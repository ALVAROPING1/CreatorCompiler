use chumsky::{prelude::*, stream::Stream};

use once_cell::sync::Lazy;
use regex::Regex;

use super::{expression, lexer, Argument, ParseError, Spanned, Token};
use crate::architecture::{BitRange, InstructionField, InstructionFieldType};

type Output = Vec<(Spanned<Argument>, usize)>;

#[derive(Clone)]
pub struct Instruction<'a>(BoxedParser<'a, Token, Output, Simple<Token>>);

impl<'a> Instruction<'a> {
    pub fn build(fmt: &str, fields: &[InstructionField<BitRange>]) -> Result<Self, &'static str> {
        static FIELD: Lazy<Regex> =
            Lazy::new(|| Regex::new(r"^[fF][0-9]+$").expect("This shouldn't fail"));

        let mut tokens = lexer::lexer()
            .parse(fmt)
            .map_err(|_| "incorrect signature definition")?
            .into_iter();
        let field = |ident: String, no_co: bool| -> Result<(usize, &InstructionField<_>), _> {
            let i: usize = ident[1..].parse().expect("this already matched a number");
            fields
                .get(i)
                .ok_or("reference to undefined field")
                .and_then(|field| match field.r#type {
                    InstructionFieldType::Cop { .. } => Err("unallowed reference to cop field"),
                    InstructionFieldType::Co if no_co => Err("unallowed reference to co field"),
                    _ => Ok(field),
                })
                .map(|x| (i, x))
        };
        let parser = any().ignored().or(end()).rewind();
        // Validate opcode
        let mut parser = parser
            .to(match tokens.next() {
                Some((Token::Identifier(ident), _)) if FIELD.is_match(&ident) => {
                    let (i, field) = field(ident, false)?;
                    match field.r#type {
                        InstructionFieldType::Co => {
                            vec![((Argument::Identifier(String::new()), 0..0), i)]
                        }
                        _ => return Err("the first field should have type `co`"),
                    }
                }
                _ => return Err("unexpected first token of signature definition"),
            })
            .boxed();

        for (token, _) in tokens {
            parser = match token {
                Token::Identifier(ident) if FIELD.is_match(&ident) => {
                    let (i, _) = field(ident, true)?;
                    parser
                        .chain(
                            expression::parser()
                                .map(Argument::Number)
                                .or(select! {Token::Identifier(i) => Argument::Identifier(i)})
                                .map_with_span(move |arg, span| ((arg, span), i)),
                        )
                        .boxed()
                }
                _ => parser.then_ignore(just(token)).boxed(),
            }
        }
        Ok(Self(parser.then_ignore(end()).boxed()))
    }

    pub fn parse(&self, code: Spanned<Vec<Spanned<Token>>>) -> Result<Output, ParseError> {
        let end = code.1.end;
        #[allow(clippy::range_plus_one)] // Chumsky requires an inclusive range to avoid type errors
        let stream = Stream::from_iter(end..end + 1, code.0.into_iter());
        Ok(self.0.parse(stream)?)
    }
}

impl<'a> std::fmt::Debug for Instruction<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("InstructionParser").finish()
    }
}
