use chumsky::prelude::*;
use std::fmt;

use super::Spanned;

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum Token {
    Number(String),
    String(String),
    Character(char),
    Identifier(String),
    Label(String),
    Directive(String),
    Operator(char),
    Ctrl(char),
    Literal(char),
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Number(n) => write!(f, "{n}"),
            Self::String(s) => write!(f, "\"{s}\""),
            Self::Character(s) => write!(f, "'{s}'"),
            Self::Identifier(i) | Self::Label(i) | Self::Directive(i) => write!(f, "{i}"),
            Self::Ctrl(c) | Self::Operator(c) | Self::Literal(c) => {
                write!(f, "{c}")
            }
        }
    }
}

#[must_use]
pub fn lexer() -> impl Parser<char, Vec<Spanned<Token>>, Error = Simple<char>> {
    let newline = text::newline().to('\n');

    // Numbers
    let num = text::int(10).map(Token::Number).labelled("number");

    // Expression operators
    let op = one_of("+-*/%|&^~")
        .map(Token::Operator)
        .labelled("operator");

    // Control characters used in the grammar
    let ctrl = one_of(",()")
        .or(newline)
        .map(Token::Ctrl)
        .labelled("control character");

    // Other literal punctuation characters. This should be the last option if all other patterns
    // fail, so we don't need to be too specific to avoid ambiguities with other patterns
    let literal = filter(|c: &char| c.is_ascii_punctuation())
        .map(Token::Literal)
        .labelled("literal");

    // Generic identifiers
    let ident = filter(|c: &char| c.is_ascii_alphabetic())
        .chain(filter(|c: &char| c.is_ascii_alphanumeric() || *c == '_' || *c == '.').repeated())
        .labelled("identifier");

    // Name identifiers
    let identifier = ident.collect::<String>().map(Token::Identifier);

    // Label names
    let label = just('.')
        .or_not()
        .chain::<char, _, _>(ident)
        .collect::<String>()
        .then_ignore(just(':'))
        .map(Token::Label)
        .labelled("label");

    // Directive names
    let directive = just('.')
        .chain(ident)
        .collect::<String>()
        .map(Token::Directive)
        .labelled("directive name");

    // Escape sequences in strings
    let escape = just('\\').ignore_then(choice((
        just('\\'),
        just('/'),
        just('"'),
        just('\''),
        just('a').to('\x07'),
        just('b').to('\x08'),
        just('e').to('\x1B'),
        just('f').to('\x0C'),
        just('n').to('\n'),
        just('r').to('\r'),
        just('t').to('\t'),
        just('0').to('\0'),
    )));

    // Characters allowed inside string/character literals
    let char = |delimiter| filter(move |c| *c != '\\' && *c != delimiter).or(escape);

    // Literal strings (`"..."`)
    let string = char('"')
        .repeated()
        .delimited_by(just('"'), just('"'))
        .collect::<String>()
        .map(Token::String);

    // Literal characters (`'c'`)
    let character = char('\'')
        .delimited_by(just('\''), just('\''))
        .map(Token::Character);

    // Any of the previous patterns can be a token
    let token = choice((
        num, op, ctrl, label, directive, identifier, string, character, literal,
    ))
    .labelled("token");

    // Single line comments
    let comment = just("#").then(newline.not().repeated()).labelled("comment");

    token
        .map_with_span(|tok, span| (tok, span))
        .padded_by(comment.repeated())
        .padded_by(
            filter(|c: &char| c.is_whitespace() && *c != '\n')
                .ignored()
                .repeated(),
        )
        .repeated()
        .then_ignore(end())
}
