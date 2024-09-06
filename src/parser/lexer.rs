use chumsky::prelude::*;
use std::{fmt, num::IntErrorKind, str::FromStr};

use super::{Parser, Spanned};

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum Token {
    Integer(u32),
    Float(u64),
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
            Self::Integer(n) => write!(f, "{n}"),
            Self::Float(n) => write!(f, "{}", f64::from_bits(*n)),
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
fn int_lexer() -> Parser!(char, Token) {
    let try_to_int = |res: Result<u32, <u32 as FromStr>::Err>, span| {
        res.map_err(|err| {
            Simple::custom(
                span,
                match err.kind() {
                    IntErrorKind::PosOverflow => "integer literal too big",
                    _ => unreachable!("We already parsed the string as an integer, and don't allow negative literals")
                },
            )
        })
    };

    // Decimal
    let decimal = text::int(10)
        // Disambiguate integer literals from the integer part of a floating point literal
        .then_ignore(none_of(".eE").rewind().to(()).or(end()))
        .from_str()
        .try_map(try_to_int);

    // Generic base N literals
    let base_n = |n| {
        text::digits(n)
            .map(move |x: String| u32::from_str_radix(&x, n))
            .try_map(try_to_int)
    };
    let hex = just("0x").or(just("0X")).ignore_then(base_n(16));
    let bin = just("0b").or(just("0B")).ignore_then(base_n(2));
    let octal = just("0").ignore_then(base_n(8));

    // Integer token
    choice((hex, bin, octal, decimal))
        .map(Token::Integer)
        .labelled("integer")
}

#[must_use]
fn float_lexer() -> Parser!(char, Token) {
    let int = text::int(10);
    let frac = just('.').then(text::digits(10));
    let sign = one_of("+-").or_not().map(|sign| sign.unwrap_or('+'));
    let exp = just('e').or(just('E')).then(sign.clone()).then(int);
    let float = int
        .then(frac.or_not())
        .then(exp.or_not())
        .map(|((int, frac), exp)| {
            format!(
                "{int}{}{}",
                frac.map_or(String::new(), |(_, frac)| format!(".{frac}")),
                exp.map_or(String::new(), |((_, sign), exp)| format!("e{sign}{exp}"))
            )
        })
        .from_str()
        .map(|res: Result<f64, _>| res.expect("We already parsed it as a float literal"));

    let named_constant = text::ident().try_map(|ident: String, span| {
        Ok(match ident.to_lowercase().as_str() {
            "inf" | "infinity" => f64::INFINITY,
            "nan" => f64::NAN,
            _ => return Err(Simple::custom(span, "Unallowed float literal")),
        })
    });

    choice((float, named_constant))
        .map(|x| Token::Float(x.to_bits()))
        .labelled("float")
}

#[must_use]
fn str_lexer() -> (Parser!(char, Token), Parser!(char, Token)) {
    // Escape sequences in strings
    let escape = just('\\').ignore_then(choice((
        just('\\'),
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
    (string, character)
}

#[must_use]
pub fn lexer() -> Parser!(char, Vec<Spanned<Token>>) {
    let newline = text::newline().to('\n');

    // Integer literals
    let int = int_lexer();
    // Float literals
    let float = float_lexer();

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

    // String/character literals
    let (string, character) = str_lexer();

    // Any of the previous patterns can be a token
    let token = choice((
        int, float, op, ctrl, label, directive, identifier, string, character, literal,
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
