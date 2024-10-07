use ariadne::{Color, Label, Report, ReportKind, Source};
use chumsky::error::{Simple, SimpleReason};

use super::Token;

/// Error representing a syntax error during parsing
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Error {
    /// The error happened during the lexing stage
    Lexer(Vec<Simple<char>>),
    /// The error happened during the parsing stage
    Parser(Vec<Simple<Token>>),
}

impl From<Vec<Simple<char>>> for Error {
    fn from(value: Vec<Simple<char>>) -> Self {
        Self::Lexer(value)
    }
}

impl From<Vec<Simple<Token>>> for Error {
    fn from(value: Vec<Simple<Token>>) -> Self {
        Self::Parser(value)
    }
}

impl Error {
    /// Prints the error to `stdout`
    ///
    /// # Parameters
    ///
    /// * `filename`: name of the file with the code
    /// * `src`: original source code parsed
    pub fn print(self, filename: &str, src: &str) {
        let (lex, parse) = match self {
            Self::Lexer(errs) => (errs, vec![]),
            Self::Parser(errs) => (vec![], errs),
        };
        lex.into_iter()
            .map(|e| e.map(|c| c.to_string()))
            .chain(parse.into_iter().map(|e| e.map(|tok| tok.to_string())))
            .for_each(|e| {
                Report::build(ReportKind::Error, filename, e.span().start)
                    .with_message(match e.reason() {
                        SimpleReason::Custom(msg) => msg.clone(),
                        _ => e.to_string(),
                    })
                    .with_label(
                        Label::new((filename, e.span()))
                            .with_message(match e.reason() {
                                SimpleReason::Unexpected => "Unexpected input",
                                SimpleReason::Custom(_) => "Caused by this",
                                SimpleReason::Unclosed { .. } => {
                                    unreachable!("We don't use this error")
                                }
                            })
                            .with_color(Color::Red),
                    )
                    .with_labels(e.label().map_or_else(Vec::new, |label| {
                        vec![Label::new((filename, e.span()))
                            .with_message(format!("while parsing this {label}"))
                            .with_color(Color::Yellow)]
                    }))
                    .finish()
                    .print((filename, Source::from(src)))
                    .expect("we should be able to print to stdout");
            });
    }
}
