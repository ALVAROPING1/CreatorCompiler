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

//! Module containing the definition of the lexer
//!
//! The main entry point for creating the parser is the [`lexer()`] function

use chumsky::prelude::*;
use num_bigint::BigUint;
use num_traits::Num as _;
use std::fmt;

use super::{Parser, Span, Spanned};

/// Thin wrapper for a hasheable [`f64`] value
// NOTE: this has to be stored as an `u64` to be able to derive `Hash`. The `Hash` trait is required
// by token types used for parsing by `chumsky`
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct HashableFloat(u64);

impl From<HashableFloat> for f64 {
    fn from(value: HashableFloat) -> Self {
        Self::from_bits(value.0)
    }
}

impl From<f64> for HashableFloat {
    fn from(value: f64) -> Self {
        Self(value.to_bits())
    }
}

/// Tokens created by the lexer
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum Token {
    /// Integer literal
    Integer(BigUint),
    /// Floating point literal
    Float(HashableFloat),
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
            Self::Float(n) => write!(f, "{}", f64::from(*n)),
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
    static EXPECT_MSG: &str = "The parsed string should always correspond with a valid number";

    // Decimal: integer not followed by a decimal part/exponent
    let decimal = text::int(10)
        // Disambiguate integer literals from the integer part of a floating point literal
        .then_ignore(none_of(".eE").rewind().ignored().or(end()))
        .from_str()
        .map(|x| x.expect(EXPECT_MSG));

    // Generic base N literals
    let base_n =
        |n| text::digits(n).map(move |x: String| BigUint::from_str_radix(&x, n).expect(EXPECT_MSG));
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
        .map(|x| Token::Float(x.into()))
        .labelled("float")
}

/// Creates a lexer for string and character literals
#[must_use]
fn str_lexer() -> (Parser!(char, Token), Parser!(char, Token)) {
    // Escape sequences in strings
    let escape = just('\\')
        .ignore_then(choice((
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
        )))
        .map_err_with_span(|_, s: Span| {
            #[allow(clippy::range_plus_one)]
            Simple::custom(s.start..s.end + 1, "Invalid escape sequence")
        });

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
///
/// # Parameters
///
/// * `comment_prefix`: string to use as line comment prefix
#[must_use]
pub fn lexer(comment_prefix: &str) -> Parser!(char, Vec<Spanned<Token>>, '_) {
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
    let literal = filter(|c: &char| !(c.is_ascii_alphanumeric() || "\"'_.".contains(*c)))
        .map(Token::Literal)
        .labelled("literal");

    // Generic identifiers
    let ident = filter(|c: &char| c.is_ascii_alphabetic() || "_.".contains(*c))
        .chain(filter(|c: &char| c.is_ascii_alphanumeric() || "_.".contains(*c)).repeated())
        .collect::<String>()
        .labelled("identifier");

    // Identifiers (names/labels/directives)
    let identifier = ident
        .then(just(':').or_not().map(|x| x.is_some()))
        .map(|(ident, label)| {
            if label {
                Token::Label(ident)
            } else if ident.starts_with('.') && ident != "." {
                Token::Directive(ident)
            } else {
                Token::Identifier(ident)
            }
        });

    // String/character literals
    let (string, character) = str_lexer();

    // Any of the previous patterns can be a token
    let token = choice((num, op, ctrl, identifier, string, character, literal)).labelled("token");

    // Comments
    let line_comment = just(comment_prefix)
        .then(newline.not().repeated())
        .ignored();
    let multiline_comment = just("/*").then(take_until(just("*/"))).ignored();
    let comment = line_comment
        .or(multiline_comment)
        .ignored()
        .labelled("comment");

    let whitespace = filter(|c: &char| c.is_whitespace() && *c != '\n')
        .ignored()
        .labelled("whitespace");
    let padding = comment.or(whitespace).repeated();

    token
        .map_with_span(|tok, span| (tok, span))
        .padded_by(padding)
        .repeated()
        .padded_by(padding)
        .then_ignore(end())
}

#[cfg(test)]
#[allow(clippy::unwrap_used)]
mod test {
    use super::*;

    fn lex(code: &str) -> Result<Vec<Spanned<Token>>, ()> {
        let len = code.len();
        let code_iter = code.char_indices().map(|(i, c)| (c, i..i + c.len_utf8()));
        #[allow(clippy::range_plus_one)] // Chumsky requires an inclusive range to avoid type errors
        let stream = chumsky::stream::Stream::from_iter(len..len + 1, code_iter);
        lexer("#").parse(stream).map_err(|e| eprintln!("{e:?}"))
    }

    #[test]
    #[allow(clippy::unreadable_literal)]
    fn int() {
        let test_cases = [
            // decimal
            ("0", 0),
            ("1", 1),
            ("1234", 1234),
            (&u32::MAX.to_string(), u64::from(u32::MAX)),
            (&u64::MAX.to_string(), u64::MAX),
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
            let v = v.into();
            assert_eq!(lex(s), Ok(vec![(Token::Integer(v), 0..s.len())]), "`{s}`");
        }
    }

    #[test]
    fn float() {
        let float_tok = |x: &str| Token::Float(x.parse::<f64>().unwrap().into());
        let test_cases = [
            "0.0", "1.0", "0.1", "100.0", "100.01", "100e1", "100E1", "0.5e1", "0.5e1", "0.5e+1",
            "0.5e-1", "0.5e0", "0.5e+0", "0.5e-0", "1e300", "1e400", "1e-30", "inf", "INF", "Inf",
            "infinity", "Infinity", "INFINITY", "nan", "NAN", "NaN",
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
        for s in ["", "a", "test", "TEST", "0a", "π √  🅐 󰸞"] {
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
        let err = Simple::custom(8..10, "Invalid escape sequence").with_label("token");
        assert_eq!(lexer("#").parse("\"invalid\\z\""), Err(vec![err]));
    }

    #[test]
    fn char() {
        // normal characters
        let ascii = ('!'..='~').filter(|c| !"\\\'".contains(*c));
        let chars = ascii
            .chain('¡'..='±')
            .chain('Σ'..='ω')
            .chain('ᴀ'..='ᴊ')
            .chain('←'..='↙')
            .chain('⎛'..='⎿')
            .chain('─'..='⎮')
            .chain('龱'..='龺')
            .chain('Ꭓ'..='ꞷ')
            .chain(''..='')
            .chain('𐝈'..='𐝌')
            .chain('𛰙'..='𛰜')
            .chain('🮤'..='🮧')
            .chain('󰀁'..='󰀘');
        for c in chars {
            assert_eq!(
                lex(&format!("'{c}'")),
                Ok(vec![(Token::Character(c), 0..c.len_utf8() + 2)])
            );
        }
        for (s, res) in ESCAPE_SEQUENCES {
            assert_eq!(
                lex(&format!("'\\{s}'")),
                Ok(vec![(Token::Character(res), 0..s.len() + 3)])
            );
        }
        let err = Simple::custom(1..3, "Invalid escape sequence").with_label("token");
        assert_eq!(lexer("#").parse("'\\z'"), Err(vec![err]));
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
            "_start_underscore",
            "a._123",
            "z....___1",
            "_1_",
            "_",
            ".",
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
            ".1_:",
            "_.1_a:",
            ".:",
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
            ".1_",
            "._1_a",
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
        for c in "@!?=:;${}[]\\<>".chars() {
            assert_eq!(lex(&c.to_string()), Ok(vec![(Token::Literal(c), 0..1)]));
        }
    }

    #[test]
    fn padding() {
        let utf8_len = "/* π √  🅐 󰸞 */".len();
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
            (
                "/* π √  🅐 󰸞 */ test  /* inline comment */",
                utf8_len + 1..utf8_len + 5,
            ),
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
        for (s, v) in [("test // asd", 0..4), ("test //asd", 0..4)] {
            assert_eq!(
                lexer("//").parse(s).map_err(|e| eprintln!("{e:?}")),
                Ok(vec![(Token::Identifier(s[v.clone()].into()), v)]),
                "`{s}`"
            );
        }
    }

    #[test]
    fn sequence() {
        let src = "a 1 .z +- test:  ]\t='x'\"string\"";
        let tokens = vec![
            (Token::Identifier("a".into()), 0..1),
            (Token::Integer(1u8.into()), 2..3),
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

    #[test]
    fn empty() {
        let test_cases = [
            "",
            " ",
            "    ",
            "  \t  ",
            "#a",
            "/*a*/",
            " \t #a",
            " /*a*/ \t /*b*/ #c",
        ];
        for s in test_cases {
            assert_eq!(lex(s), Ok(vec![]), "`{s}`");
        }
    }
}
