use chumsky::{prelude::*, stream::Stream};

use once_cell::sync::Lazy;
use regex::Regex;

use super::{expression, lexer, Argument, ParseError, Spanned, Token};

#[derive(Clone)]
pub struct Instruction<'a>(BoxedParser<'a, Token, Vec<Spanned<Argument>>, Simple<Token>>);

impl<'a> Instruction<'a> {
    pub fn build(fmt: &str) -> Result<Self, ParseError> {
        static FIELD: Lazy<Regex> =
            Lazy::new(|| Regex::new(r"^[fF][0-9]+$").expect("This shouldn't fail"));

        let mut parser = any()
            .ignored()
            .or(end())
            .rewind()
            .to(vec![(Argument::Identifier(String::new()), 0..0)])
            .boxed();
        let tokens = lexer::lexer().parse(fmt)?;
        for (token, _) in tokens {
            parser = match token {
                Token::Identifier(ident) if FIELD.is_match(&ident) => parser
                    .chain(
                        expression::parser()
                            .map(Argument::Number)
                            .or(select! {Token::Identifier(i) => Argument::Identifier(i)})
                            .map_with_span(|arg, span| (arg, span)),
                    )
                    .boxed(),
                _ => parser.then_ignore(just(token)).boxed(),
            }
        }
        Ok(Self(parser.then_ignore(end()).boxed()))
    }

    pub fn parse(
        &self,
        code: Spanned<Vec<Spanned<Token>>>,
    ) -> Result<Vec<Spanned<Argument>>, ParseError> {
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
