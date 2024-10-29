//! Module containing the definition of the parser for instruction arguments
//!
//! The main entry point is the [`Instruction`] type

use chumsky::{prelude::*, stream::Stream};

use once_cell::sync::Lazy;
use regex::Regex;

use super::{expression, lexer, ParseError, Spanned, Token};
use crate::architecture::{BitRange, FieldType, InstructionField};

/// Instruction argument value
#[derive(Debug, Clone, PartialEq)]
pub enum Argument {
    /// Identifier
    Identifier(String),
    /// Expression that can be evaluated to a number
    Number(expression::Expr),
}

/// Output type of parsing the arguments of an instruction
type Output = Vec<(Spanned<Argument>, usize)>;

/// Instruction parser wrapper
#[derive(Clone)]
pub struct Instruction<'a>(BoxedParser<'a, Token, Output, Simple<Token>>);

impl<'a> Instruction<'a> {
    /// Creates a new `Instruction` parser
    ///
    /// # Parameters
    ///
    /// * `fmt`: syntax specification of the arguments
    /// * `fields`: definition of each field
    ///
    /// # Errors
    ///
    /// Errors if the syntax specification is invalid
    pub fn build(fmt: &str, fields: &[InstructionField<BitRange>]) -> Result<Self, &'static str> {
        // Regex for a instruction argument placeholder
        static FIELD: Lazy<Regex> =
            Lazy::new(|| Regex::new(r"^[fF][0-9]+$").expect("This shouldn't fail"));

        // Gets the field number the placeholder points to and validates that it has a correct type
        let field = |ident: String, no_co: bool| -> Result<usize, _> {
            let i: usize = ident[1..].parse().expect("this already matched a number");
            fields
                .get(i)
                .ok_or("reference to undefined field")
                .and_then(|field| match field.r#type {
                    FieldType::Cop { .. } => Err("unallowed reference to cop field"),
                    FieldType::Co if no_co => Err("unallowed reference to co field"),
                    _ => Ok(i),
                })
        };

        // Lexes the syntax definition with the same lexer as the code
        let mut tokens = lexer::lexer()
            .parse(fmt)
            .map_err(|_| "incorrect signature definition")?
            .into_iter()
            .map(|(tok, _)| tok); // We don't need the token spans

        // Creates an initial dummy parser that consumes no input
        let parser = any().ignored().or(end()).rewind();
        // Validate the first token is a field placeholder pointing to the opcode
        let mut parser = parser
            .to(match tokens.next() {
                Some(Token::Identifier(ident)) if FIELD.is_match(&ident) => {
                    let i = field(ident, false)?;
                    match fields[i].r#type {
                        FieldType::Co => {
                            // This value should never be read, we only need it to point to the
                            // opcode instruction field
                            vec![((Argument::Identifier(String::new()), 0..0), i)]
                        }
                        _ => return Err("the first field should have type `co`"),
                    }
                }
                _ => return Err("unexpected first token of signature definition"),
            })
            .boxed();

        // Iterate through the remaining tokens
        for token in tokens {
            // Append the current token parser to the parser being created
            parser = match token {
                // The current token is an argument placeholder => parse an expression/identifier
                Token::Identifier(ident) if FIELD.is_match(&ident) => {
                    let i = field(ident, true)?; // Validate the field pointed to
                    parser
                        .chain(
                            expression::parser()
                                .map(Argument::Number)
                                .or(select! {Token::Identifier(ident) => Argument::Identifier(ident)})
                                .map_with_span(move |arg, span| ((arg, span), i)),
                        )
                        .boxed()
                }
                // The current token isn't an argument placeholder => parse it literally, ignoring
                // its output
                _ => parser.then_ignore(just(token)).boxed(),
            }
        }
        // Check that there is no remaining input in the syntax and create the final parser
        Ok(Self(parser.then_ignore(end()).boxed()))
    }

    /// Parses the arguments of an instruction according to the syntax
    ///
    /// # Parameters
    ///
    /// * `code`: code to parse
    ///
    /// # Errors
    ///
    /// Errors if the code doesn't follow the syntax defined
    pub fn parse(&self, code: &Spanned<Vec<Spanned<Token>>>) -> Result<Output, ParseError> {
        let end = code.1.end;
        #[allow(clippy::range_plus_one)] // Chumsky requires an inclusive range to avoid type errors
        let stream = Stream::from_iter(end..end + 1, code.0.iter().cloned());
        Ok(self.0.parse(stream)?)
    }
}

// Boxed parsers don't implement `Debug`, so we need to implement it manually as an opaque box
impl<'a> std::fmt::Debug for Instruction<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("InstructionParser").finish()
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod test {
    use super::*;
    use crate::architecture::NonEmptyRangeInclusiveU8;
    use crate::parser::{expression::BinaryOp, Expr};

    fn fields() -> [InstructionField<'static, BitRange>; 3] {
        let field = |co| InstructionField {
            name: "",
            r#type: if co {
                FieldType::Co
            } else {
                FieldType::ImmSigned
            },
            range: BitRange::build(vec![NonEmptyRangeInclusiveU8::build(0, 0).unwrap()]).unwrap(),
        };
        [field(true), field(false), field(false)]
    }

    fn parse(parser: &Instruction, src: &str) -> Result<Output, ()> {
        let ast = (lexer::lexer().parse(src).unwrap(), 0..src.chars().count());
        parser.parse(&ast).map_err(|e| eprintln!("{e:?}"))
    }

    const fn co_arg() -> (Spanned<Argument>, usize) {
        ((Argument::Identifier(String::new()), 0..0), 0)
    }

    fn ident(name: &str) -> Argument {
        Argument::Identifier(name.into())
    }

    const fn number(x: u32) -> Argument {
        Argument::Number(Expr::Integer(x))
    }

    #[test]
    fn no_args() {
        let parser = Instruction::build("F0", &fields()).unwrap();
        assert_eq!(parse(&parser, ""), Ok(vec![co_arg()]));
        assert_eq!(parse(&parser, "a"), Err(()));
    }

    #[test]
    fn one_arg() {
        let parser = Instruction::build("F0 F1", &fields()).unwrap();
        assert_eq!(parse(&parser, ""), Err(()));
        assert_eq!(parse(&parser, ","), Err(()));
        assert_eq!(parse(&parser, "$"), Err(()));
        assert_eq!(
            parse(&parser, "a"),
            Ok(vec![co_arg(), ((ident("a"), 0..1), 1)])
        );
        assert_eq!(
            parse(&parser, "1"),
            Ok(vec![co_arg(), ((number(1), 0..1), 1)])
        );
        assert_eq!(
            parse(&parser, "1 + 1"),
            Ok(vec![
                co_arg(),
                (
                    (
                        Argument::Number(Expr::BinaryOp {
                            op: (BinaryOp::Add, 2..3),
                            lhs: Box::new((Expr::Integer(1), 0..1)),
                            rhs: Box::new((Expr::Integer(1), 4..5))
                        }),
                        0..5
                    ),
                    1
                )
            ])
        );
    }

    #[test]
    fn multiple_arg() {
        let parser = Instruction::build("F0 F2 F1", &fields()).unwrap();
        assert_eq!(parse(&parser, ""), Err(()));
        assert_eq!(parse(&parser, ","), Err(()));
        assert_eq!(parse(&parser, "a"), Err(()));
        assert_eq!(parse(&parser, "a, b"), Err(()));
        assert_eq!(
            parse(&parser, "a 1"),
            Ok(vec![
                co_arg(),
                ((ident("a"), 0..1), 2),
                ((number(1), 2..3), 1)
            ])
        );
        assert_eq!(
            parse(&parser, "b 2"),
            Ok(vec![
                co_arg(),
                ((ident("b"), 0..1), 2),
                ((number(2), 2..3), 1)
            ])
        );
    }

    #[test]
    fn comma_separator() {
        let parser = Instruction::build("F0 F1, F2", &fields()).unwrap();
        assert_eq!(parse(&parser, "1 2"), Err(()));
        assert_eq!(
            parse(&parser, "1, 2"),
            Ok(vec![
                co_arg(),
                ((number(1), 0..1), 1),
                ((number(2), 3..4), 2)
            ])
        );
    }

    #[test]
    fn literals() {
        let parser = Instruction::build("F0 ,1 F1 $(F2)", &fields()).unwrap();
        assert_eq!(parse(&parser, "2 5"), Err(()));
        assert_eq!(parse(&parser, ",1 2 5"), Err(()));
        assert_eq!(parse(&parser, ",1 2 (5)"), Err(()));
        assert_eq!(parse(&parser, ",1 2 $5"), Err(()));
        assert_eq!(parse(&parser, ",3 2 $(5)"), Err(()));
        assert_eq!(
            parse(&parser, ",1 2 $(5)"),
            Ok(vec![
                co_arg(),
                ((number(2), 3..4), 1),
                ((number(5), 7..8), 2)
            ])
        );
        let parser = Instruction::build("F0 1 * -F1", &fields()).unwrap();
        assert_eq!(parse(&parser, "2"), Err(()));
        assert_eq!(parse(&parser, "-2"), Err(()));
        assert_eq!(parse(&parser, "* -2"), Err(()));
        assert_eq!(parse(&parser, "1 * 2"), Err(()));
        assert_eq!(parse(&parser, "1 -2"), Err(()));
        assert_eq!(
            parse(&parser, "1 * -2"),
            Ok(vec![co_arg(), ((number(2), 5..6), 1)])
        );
    }
}
