/*
 * Copyright 2018-2024 Felix Garcia Carballeira, Alejandro Calderon Mateos, Diego Camarmas Alonso,
 * Álvaro Guerrero Espinosa
 *
 * This file is part of CREATOR.
 *
 * CREATOR is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * CREATOR is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with CREATOR.  If not, see <http://www.gnu.org/licenses/>.
 */

//! Module containing the definition of the parser for instruction arguments
//!
//! The main entry point is the [`Instruction`] type

use chumsky::{prelude::*, input::MappedInput};
use regex::Regex;

use std::sync::LazyLock;

use super::{expression, expression::Expr, lexer, ParseError, Span, Spanned, Token};
use crate::architecture::{FieldType, InstructionField};

/// Value of a parsed argument
#[derive(Debug, Clone, PartialEq)]
pub struct ParsedArgument {
    /// Parsed argument value
    pub value: Spanned<Expr>,
    /// Index of the field corresponding to this value in the instruction fields definition
    pub field_idx: usize,
}

/// Arguments parsed by the instruction
pub type ParsedArgs = Vec<ParsedArgument>;

/// Input type to be used with instruction argument parsers
// NOTE: we need to name this input type to be able to box the parsers, which is required to store
// them on a struct
// TODO: replace with `chumsky::input::IterInput` on chumsky 0.10.2 (on 0.10.1 it doesn't implement
// the correct traits)
type TokenInput<'src> =
    MappedInput<Token, Span, &'src [Spanned<Token>], fn(&Spanned<Token>) -> (&Token, &Span)>;

/// Parser type used internally by instruction argument parsers
type BoxedParser<'src> = super::Parser!(boxed: 'src, TokenInput<'src>, ParsedArgs);

/// Instruction parser wrapper
#[derive(Clone)]
pub struct Instruction(BoxedParser<'static>);

/// Parses an identifier in the form `[fF]\d+` into a number
///
/// # Parameters
///
/// * `identifier`: identifier to parse
///
/// # Panics
///
/// Panics if the identifier doesn't follow the regex `[fF]\d+`
#[must_use]
fn number(identifier: &str) -> usize {
    static MSG: &str = "This should have already matched a number";
    identifier[1..].parse().expect(MSG)
}

impl Instruction {
    /// Creates a new [`Instruction`] parser
    ///
    /// # Parameters
    ///
    /// * `fmt`: syntax specification of the arguments
    /// * `fields`: definition of each field
    ///
    /// # Errors
    ///
    /// Errors if the syntax specification is invalid
    pub fn build<T>(fmt: &str, fields: &[InstructionField<T>]) -> Result<Self, &'static str> {
        // Regex for a instruction argument placeholder
        static FIELD: LazyLock<Regex> = crate::regex!(r"^[fF][0-9]+$");

        // Gets the field number the placeholder points to and validates that it has a correct type
        let field = |ident: String, no_co: bool| -> Result<usize, _> {
            let i: usize = number(&ident);
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
        // NOTE: we use a null character as the comment prefix because we don't know what prefix
        // the architecture specifies here. Null characters can't appear in the input, so this
        // disallows line comments
        let mut tokens = lexer::lexer("\0")
            .parse(fmt)
            .into_result()
            .map_err(|_| "incorrect signature definition")?
            .into_iter()
            .map(|(tok, _)| tok); // We don't need the token spans

        // Creates an initial dummy parser that consumes no input
        let parser = any().ignored().or(end()).rewind();
        // Validate the first token is a field placeholder pointing to the opcode/instruction name
        let mut parser = parser
            .to(match tokens.next() {
                // First token is a placeholder => check that it points to the opcode field
                Some(Token::Identifier(ident)) if FIELD.is_match(&ident) => {
                    let i = field(ident, false)?;
                    match fields[i].r#type {
                        FieldType::Co => {
                            // NOTE: This value should never be read, we only need it to point to the
                            // opcode instruction field
                            vec![ParsedArgument {
                                value: (Expr::Integer(0u8.into()), (0..0).into()),
                                field_idx: i,
                            }]
                        }
                        _ => return Err("the first field should have type `co`"),
                    }
                }
                // First token is an identifier => assume it's the instruction name
                // There is no opcode field specification => assume it shouldn't be included in the
                // output
                Some(Token::Identifier(_)) => vec![],
                _ => return Err("unexpected first token of signature definition"),
            })
            .boxed();

        // Iterate through the remaining tokens
        for token in tokens {
            // Append the current token parser to the parser being created
            parser = match token {
                // The current token is an argument placeholder => parse an expression/identifier
                Token::Identifier(ident) if FIELD.is_match(&ident) => {
                    let field_idx = field(ident, true)?; // Validate the field pointed to
                    parser
                        .then(expression::parser().map_with(|expr, e| (expr, e.span())))
                        .map(move |(mut args, value)| {
                            args.push(ParsedArgument { value, field_idx });
                            args
                        })
                        .boxed()
                }
                // The current token isn't an argument placeholder => parse it literally, ignoring
                // its output
                _ => parser.then_ignore(just(token)).boxed(),
            }
        }
        // Check that there is no remaining input in the syntax and create the final parser
        Ok(Self(parser))
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
    pub fn parse(&self, code: &Spanned<Vec<Spanned<Token>>>) -> Result<ParsedArgs, ParseError> {
        let end = code.1.end;
        Ok(self
            .get()
            .parse(code.0.map((end..end).into(), |(x, s)| (x, s)))
            .into_result()?)
    }

    /// Get a reference to the parser. Because this function is generic over an input lifetime, the
    /// returned parser can be used in many different contexts
    //
    // NOTE: implementation adapted from [`chumsky::cache::Cache`]. Since creating the parser can
    // fail, we can't directly use that API
    fn get<'src>(&self) -> &BoxedParser<'src> {
        // SAFETY: This is safe because the stored parser has a lifetime of `'static`, so we will
        // only ever reduce its lifetime. Since lifetimes are removed during monomorphisation, the
        // parser must be valid for arbitrary lifetimes.
        unsafe { &*(&raw const self.0).cast() }
    }

    /// Lexes an instruction represented as a string
    ///
    /// # Parameters
    ///
    /// * `code`: code to lex
    ///
    /// # Errors
    ///
    /// Errors if there is an error lexing the code
    pub fn lex(code: &str) -> Result<(&str, Vec<Spanned<Token>>), ParseError> {
        let (name, args) = code.trim().split_once(' ').unwrap_or((code, ""));
        // NOTE: we use a null character as the comment prefix because we don't know what prefix
        // the architecture specifies here. Null characters can't appear in the input, so this
        // disallows line comments
        let tokens = super::lexer::lexer("\0").parse(args).into_result()?;
        Ok((name, tokens))
    }
}

// Boxed parsers don't implement `Debug`, so we need to implement it manually as an opaque box
impl std::fmt::Debug for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("InstructionParser").finish()
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod test {
    use super::*;
    use crate::parser::expression::BinaryOp;
    use crate::span::Span;

    type Range = std::ops::Range<usize>;
    type Ranged<T> = (T, Range);

    #[must_use]
    fn fields() -> [InstructionField<'static, ()>; 3] {
        let field = |co| InstructionField {
            name: "",
            r#type: if co {
                FieldType::Co
            } else {
                FieldType::ImmSigned
            },
            range: (),
        };
        [field(true), field(false), field(false)]
    }

    fn parse(parser: &Instruction, src: &str) -> Result<ParsedArgs, ()> {
        let ast = (lexer::lexer("#").parse(src).unwrap(), (0..src.len()).into());
        parser.parse(&ast).map_err(|e| eprintln!("{e:?}"))
    }

    #[must_use]
    fn arg(value: (Expr, impl Into<Span>), field_idx: usize) -> ParsedArgument {
        ParsedArgument {
            value: (value.0, value.1.into()),
            field_idx,
        }
    }

    #[must_use]
    fn co_arg() -> ParsedArgument {
        arg((Expr::Integer(0u8.into()), 0..0), 0)
    }

    #[must_use]
    fn ident(name: Ranged<&str>) -> Spanned<Expr> {
        let s = name.1.into();
        (Expr::Identifier((name.0.into(), s)), s)
    }

    #[must_use]
    fn number(x: u32) -> Expr {
        Expr::Integer(x.into())
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
            Ok(vec![co_arg(), arg(ident(("a", 0..1)), 1)])
        );
        assert_eq!(
            parse(&parser, "1"),
            Ok(vec![co_arg(), arg((number(1), 0..1), 1)])
        );
        assert_eq!(
            parse(&parser, "1 + 1"),
            Ok(vec![
                co_arg(),
                arg(
                    (
                        Expr::BinaryOp {
                            op: (BinaryOp::Add, (2..3).into()),
                            lhs: Box::new((Expr::Integer(1u8.into()), (0..1).into())),
                            rhs: Box::new((Expr::Integer(1u8.into()), (4..5).into()))
                        },
                        0..5
                    ),
                    1
                )
            ])
        );
        assert_eq!(
            parse(&parser, "c - a"),
            Ok(vec![
                co_arg(),
                arg(
                    (
                        Expr::BinaryOp {
                            op: (BinaryOp::Sub, (2..3).into()),
                            lhs: Box::new(ident(("c", 0..1))),
                            rhs: Box::new(ident(("a", 4..5)))
                        },
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
                arg(ident(("a", 0..1)), 2),
                arg((number(1), 2..3), 1)
            ])
        );
        assert_eq!(
            parse(&parser, "b 2"),
            Ok(vec![
                co_arg(),
                arg(ident(("b", 0..1)), 2),
                arg((number(2), 2..3), 1)
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
                arg((number(1), 0..1), 1),
                arg((number(2), 3..4), 2)
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
                arg((number(2), 3..4), 1),
                arg((number(5), 7..8), 2)
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
            Ok(vec![co_arg(), arg((number(2), 5..6), 1)])
        );
        let parser = Instruction::build("F0 aF1 F1a F2", &fields()).unwrap();
        assert_eq!(parse(&parser, "1 1 2"), Err(()));
        assert_eq!(parse(&parser, "a1 1a 2"), Err(()));
        assert_eq!(parse(&parser, "aF1 f1a 2"), Err(()));
        assert_eq!(
            parse(&parser, "aF1 F1a 2"),
            Ok(vec![co_arg(), arg((number(2), 8..9), 2)])
        );
    }
}
