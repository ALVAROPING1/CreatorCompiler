//! Module containing the definition of the parser for instruction arguments
//!
//! The main entry point is the [`Instruction`] type

use chumsky::{prelude::*, stream::Stream};

use once_cell::sync::Lazy;
use regex::Regex;

use super::{expression, lexer, ParseError, Spanned, Token};
use crate::architecture::{BitRange, InstructionField, InstructionFieldType};

/// Instruction argument value
#[derive(Debug, Clone)]
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
                    InstructionFieldType::Cop { .. } => Err("unallowed reference to cop field"),
                    InstructionFieldType::Co if no_co => Err("unallowed reference to co field"),
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
                        InstructionFieldType::Co => {
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
