use chumsky::prelude::*;
use std::{fmt, num::IntErrorKind, str::FromStr};

use super::{Parser, Spanned};

/// Tokens created by the lexer
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum Token {
    /// Integer literal
    Integer(u32),
    /// Floating point literal
    Float(u64),
    /// String literal
    String(String),
    /// Character literal
    Character(char),
    /// Identifier name
    Identifier(String),
    /// Label name
    Label(String),
    /// Directive name
    Directive(String),
    /// Numeric expression operators
    Operator(char),
    /// Control characters
    Ctrl(char),
    /// Other literal characters
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

/// Creates a lexer for integer literals
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

    // Decimal: integer not followed by a decimal part/exponent
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
    let hex = one_of("xX").ignore_then(base_n(16));
    let bin = one_of("bB").ignore_then(base_n(2));
    let octal = base_n(8);
    let base_n = just("0").ignore_then(choice((hex, bin, octal)));

    // Integer token
    base_n.or(decimal).map(Token::Integer).labelled("integer")
}

/// Creates a lexer for floating point literals
#[must_use]
fn float_lexer() -> Parser!(char, Token) {
    let int = text::int(10); // Integer part
    let frac = just('.').then(text::digits(10)); // Fractional part
    let sign = one_of("+-").or_not().map(|sign| sign.unwrap_or('+')); // Optional sign
    let exp = one_of("eE").then(sign).then(int); // Exponent part

    // Float literal: `float -> int [frac] [exp]`
    let float = int
        // Disambiguate integer literals from the integer part of a floating point literal
        .then_ignore(one_of(".eE").rewind())
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

    // named constants: `inf`, `infinity`, and `nan`
    let named_constant = text::ident().try_map(|ident: String, span| {
        Ok(match ident.to_lowercase().as_str() {
            "inf" | "infinity" => f64::INFINITY,
            "nan" => f64::NAN,
            _ => return Err(Simple::custom(span, "Unallowed float literal")),
        })
    });

    // Float token
    choice((float, named_constant))
        .map(|x| Token::Float(x.to_bits()))
        .labelled("float")
}

/// Creates a lexer for string and character literals
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

    // Characters allowed inside string/character literals: anything that isn't their delimiter or
    // a backslash
    let char = |delimiter| filter(move |c| *c != '\\' && *c != delimiter).or(escape);

    // Literal strings: `string -> " char* "`
    let string = char('"')
        .repeated()
        .delimited_by(just('"'), just('"'))
        .collect::<String>()
        .map(Token::String);

    // Literal characters: `character -> ' char '`
    let character = char('\'')
        .delimited_by(just('\''), just('\''))
        .map(Token::Character);

    (string, character)
}

/// Creates a lexer for the input
#[must_use]
pub fn lexer() -> Parser!(char, Vec<Spanned<Token>>) {
    let newline = text::newline().to('\n');

    // Integer literals
    let int = int_lexer();
    // Float literals
    let float = float_lexer();
    // Number literals can be either integers or floats
    let num = int.or(float);

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
        num, op, ctrl, label, directive, identifier, string, character, literal,
    ))
    .labelled("token");

    // Comments
    let line_comment = just("#").then(newline.not().repeated()).ignored();
    let multiline_comment = just("/*").then(take_until(just("*/"))).ignored();
    let comment = line_comment
        .or(multiline_comment)
        .ignored()
        .labelled("comment");

    let whitespace = filter(|c: &char| c.is_whitespace() && *c != '\n').ignored();

    token
        .map_with_span(|tok, span| (tok, span))
        .padded_by(comment.or(whitespace).repeated())
        .repeated()
        .then_ignore(end())
}

#[cfg(test)]
#[allow(clippy::unwrap_used)]
mod test {
    use super::{lexer, Parser as _, Spanned, Token};
    fn lex(code: &str) -> Result<Vec<Spanned<Token>>, ()> {
        lexer().parse(code).map_err(|_| ())
    }

    #[test]
    #[allow(clippy::unreadable_literal)]
    fn int() {
        let test_cases = [
            // decimal
            ("0", 0),
            ("1", 1),
            ("1234", 1234),
            ("4294967295", u32::MAX),
            // octal
            ("00", 0),
            ("01", 1),
            ("010", 8),
            // hex
            ("0x0", 0),
            ("0x1", 1),
            ("0xf", 15),
            ("0x10", 16),
            ("0X10", 16),
            ("0xFf", 255),
            // binary
            ("0b0", 0),
            ("0b1", 1),
            ("0b10", 2),
            ("0B10", 2),
        ];
        for (s, v) in test_cases {
            assert_eq!(lex(s), Ok(vec![(Token::Integer(v), 0..s.len())]), "`{s}`");
        }
        assert_eq!(lex(&(u64::from(u32::MAX) + 1).to_string()), Err(()));
    }

    #[test]
    fn float() {
        let float_tok = |x: &str| Token::Float(x.parse::<f64>().unwrap().to_bits());
        let test_cases = [
            "0.0", "1.0", "0.1", "100.0", "100.01", "100e1", "100E1", "0.5e1", "0.5e1", "0.5e+1",
            "0.5e-1", "0.5e0", "0.5e+0", "0.5e-0", "1e300", "1e400", "1e-30", "inf", "INF", "Inf",
            "nan", "NAN", "NaN",
        ];
        for s in test_cases {
            assert_eq!(lex(s), Ok(vec![(float_tok(s), 0..s.len())]), "`{s}`");
        }
    }

    // escape sequences
    const ESCAPE_SEQUENCES: [(&str, char); 11] = [
        ("\"", '\"'),
        ("\'", '\''),
        ("\\", '\\'),
        ("n", '\n'),
        ("r", '\r'),
        ("t", '\t'),
        ("0", '\0'),
        ("a", '\x07'),
        ("b", '\x08'),
        ("e", '\x1B'),
        ("f", '\x0C'),
    ];

    #[test]
    fn string() {
        // normal strings
        for s in ["", "a", "test", "TEST", "0a"] {
            assert_eq!(
                lex(&format!("\"{s}\"")),
                Ok(vec![(Token::String(s.into()), 0..s.len() + 2)])
            );
        }
        // escape sequences
        for (s, res) in ESCAPE_SEQUENCES {
            assert_eq!(
                lex(&format!("\"\\{s}\"")),
                Ok(vec![(Token::String(res.to_string()), 0..s.len() + 3)])
            );
        }
        let msg = "\"a string with escape sequences like newline `\\n` or tabs `\\t`, also quotes `\\\"` and literal backslashes `\\\\`\"";
        assert_eq!(lex(msg), Ok(vec![(Token::String("a string with escape sequences like newline `\n` or tabs `\t`, also quotes `\"` and literal backslashes `\\`".into()), 0..msg.len())]));
    }

    #[test]
    fn char() {
        // normal characters
        for c in ('!'..='~').filter(|c| !['\\', '\''].contains(c)) {
            assert_eq!(
                lex(&format!("'{c}'")),
                Ok(vec![(Token::Character(c), 0..3)])
            );
        }
        for (s, res) in ESCAPE_SEQUENCES {
            assert_eq!(
                lex(&format!("'\\{s}'")),
                Ok(vec![(Token::Character(res), 0..s.len() + 3)])
            );
        }
    }

    #[test]
    fn ident() {
        let test_cases = [
            "addi",
            "fclass.s",
            "fmul.d",
            "addi0",
            "addi1",
            "addi2",
            "ident_with_underscores_and.dots.",
            "a._123",
            "z....___1",
        ];
        for s in test_cases {
            assert_eq!(lex(s), Ok(vec![(Token::Identifier(s.into()), 0..s.len())]));
        }
    }

    #[test]
    fn label() {
        let test_cases = [
            "label:",
            ".label:",
            "label_with_underscores_and.dots.:",
            "label3:",
            ".L3:",
            "L0_:",
            "L_1:",
            ".a...___12:",
            "z....___1:",
            "z....___1..:",
            "z....___1__:",
        ];
        for s in test_cases {
            let l = s.len();
            assert_eq!(lex(s), Ok(vec![(Token::Label(s[..l - 1].into()), 0..l)]));
        }
    }

    #[test]
    fn directive() {
        let test_cases = [
            ".directive",
            ".dir_with_underscores_and.dots.",
            ".string",
            ".data",
            ".L3",
            ".L_1",
            ".z....___1",
            ".z....___1__",
            ".z....___1..",
        ];
        for s in test_cases {
            assert_eq!(lex(s), Ok(vec![(Token::Directive(s.into()), 0..s.len())]));
        }
    }

    #[test]
    fn operator() {
        for c in "+-*/%|&^~".chars() {
            assert_eq!(lex(&c.to_string()), Ok(vec![(Token::Operator(c), 0..1)]));
        }
    }

    #[test]
    fn ctrl() {
        for c in ",()\n".chars() {
            assert_eq!(lex(&c.to_string()), Ok(vec![(Token::Ctrl(c), 0..1)]));
        }
    }

    #[test]
    fn literal() {
        for c in ".!?=:_;${}[]\\<>".chars() {
            assert_eq!(lex(&c.to_string()), Ok(vec![(Token::Literal(c), 0..1)]));
        }
    }

    #[test]
    fn padding() {
        let test_cases = [
            ("  a", 2..3),
            ("a  ", 0..1),
            ("  abc    ", 2..5),
            ("  \ta\t\t", 3..4),
            ("\t\t\ta", 3..4),
            ("a\t\r\t", 0..1),
            ("\ta\t\t", 1..2),
            (" \t\ttest  \r \t \t", 3..7),
            ("/* inline comment */ test", 21..25),
            ("test /* inline comment */", 0..4),
            ("/* inline comment */ test  /* inline comment */", 21..25),
            ("test # asd", 0..4),
            ("test #asd", 0..4),
        ];
        for (s, v) in test_cases {
            assert_eq!(
                lex(s),
                Ok(vec![(Token::Identifier(s[v.clone()].into()), v)]),
                "`{s}`"
            );
        }
        assert_eq!(
            lex("#comment\ntest"),
            Ok(vec![
                (Token::Ctrl('\n'), 8..9),
                (Token::Identifier("test".into()), 9..13)
            ])
        );
    }

    #[test]
    fn sequence() {
        let src = "a 1 .z +- test:  ]\t='x'\"string\"";
        let tokens = vec![
            (Token::Identifier("a".into()), 0..1),
            (Token::Integer(1), 2..3),
            (Token::Directive(".z".into()), 4..6),
            (Token::Operator('+'), 7..8),
            (Token::Operator('-'), 8..9),
            (Token::Label("test".into()), 10..15),
            (Token::Literal(']'), 17..18),
            (Token::Literal('='), 19..20),
            (Token::Character('x'), 20..23),
            (Token::String("string".into()), 23..31),
        ];
        assert_eq!(lex(src), Ok(tokens));
    }
}
