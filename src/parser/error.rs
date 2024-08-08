use ariadne::{sources, Color, Label, Report, ReportKind};
use chumsky::error::Simple;

use super::Token;

#[derive(Debug)]
pub enum Error {
    Lexer(Vec<Simple<char>>),
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
    pub fn print(self, filename: &String, src: &str) {
        let (lex, parse) = match self {
            Self::Lexer(errs) => (errs, vec![]),
            Self::Parser(errs) => (vec![], errs),
        };
        lex.into_iter()
            .map(|e| e.map(|c| c.to_string()))
            .chain(parse.into_iter().map(|e| e.map(|tok| tok.to_string())))
            .for_each(|e| {
                Report::build(ReportKind::Error, filename, e.span().start)
                    .with_message(e.to_string())
                    .with_label(
                        Label::new((
                            filename.clone(),
                            std::convert::Into::<std::ops::Range<_>>::into(e.span()),
                        ))
                        .with_message(format!("{:?}", e.reason()))
                        .with_color(Color::Red),
                    )
                    .with_labels(e.label().map_or_else(Vec::new, |label| {
                        vec![Label::new((
                            filename.clone(),
                            std::convert::Into::<std::ops::Range<_>>::into(e.span()),
                        ))
                        .with_message(format!("while parsing this {label}"))
                        .with_color(Color::Yellow)]
                    }))
                    .finish()
                    .print(sources([(filename.clone(), src)]))
                    .expect("we should be able to print to stdout");
            });
    }
}
