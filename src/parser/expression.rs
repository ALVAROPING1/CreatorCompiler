//! Module containing the definition of the expressions sub-parser as well as their evaluation
//!
//! The main entry point for creating the parser is the [`parser()`] function, with the evaluation
//! of methods being defined in the methods of the [`Expr`] type

use chumsky::prelude::*;

use super::{Parser, Span, Spanned, Token};
use crate::compiler::{error::OperationKind, CompileError, ErrorKind};

/// Allowed unary operations
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Plus,
    Minus,
    Complement,
}

/// Allowed binary operations
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    BitwiseOR,
    BitwiseAND,
    BitwiseXOR,
}

/// Mathematical expression on constant values
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    /// Integer literal
    Integer(u32),
    /// Float literal
    Float(Spanned<f64>),
    /// Character literal
    Character(char),
    /// Unary operation on other expressions
    UnaryOp {
        op: Spanned<UnaryOp>,
        operand: Box<Spanned<Expr>>,
    },
    /// Binary operation on other expressions
    BinaryOp {
        op: Spanned<BinaryOp>,
        lhs: Box<Spanned<Expr>>,
        rhs: Box<Spanned<Expr>>,
    },
}

impl Expr {
    /// Evaluates the expression as an integer
    ///
    /// # Errors
    ///
    /// Returns a [`ErrorKind::UnallowedFloat`] if a float literal is used, and a
    /// [`ErrorKind::DivisionBy0`] if a division by 0 is attempted
    pub fn int(&self) -> Result<i32, CompileError> {
        #[allow(clippy::cast_possible_wrap)]
        Ok(match self {
            Self::Integer(value) => *value as i32,
            Self::Float((_, span)) => return Err(ErrorKind::UnallowedFloat.add_span(span)),
            Self::Character(c) => *c as i32,
            Self::UnaryOp { op, operand } => match op.0 {
                UnaryOp::Plus => operand.0.int()?,
                UnaryOp::Minus => -operand.0.int()?,
                UnaryOp::Complement => !operand.0.int()?,
            },
            Self::BinaryOp { op, lhs, rhs } => {
                let lhs = lhs.0.int()?;
                let span = &rhs.1;
                let rhs = rhs.0.int()?;
                match op.0 {
                    BinaryOp::Add => lhs.overflowing_add(rhs).0,
                    BinaryOp::Sub => lhs.overflowing_sub(rhs).0,
                    BinaryOp::Mul => lhs.overflowing_mul(rhs).0,
                    BinaryOp::Div => lhs
                        .checked_div(rhs)
                        .ok_or_else(|| ErrorKind::DivisionBy0.add_span(span))?,
                    BinaryOp::Rem => lhs % rhs,
                    BinaryOp::BitwiseOR => lhs | rhs,
                    BinaryOp::BitwiseAND => lhs & rhs,
                    BinaryOp::BitwiseXOR => lhs ^ rhs,
                }
            }
        })
    }

    /// Evaluates the expression as a float
    ///
    /// # Errors
    ///
    /// Returns a [`ErrorKind::UnallowedFloatOperation`] if an operation that's undefined with
    /// floats is attempted
    pub fn float(&self) -> Result<f64, CompileError> {
        let err = |op, s| ErrorKind::UnallowedFloatOperation(op).add_span(s);
        Ok(match self {
            Self::Integer(value) => f64::from(*value),
            Self::Float((value, _)) => *value,
            Self::Character(c) => f64::from(*c as u32),
            Self::UnaryOp { op, operand } => match op.0 {
                UnaryOp::Plus => operand.0.float()?,
                UnaryOp::Minus => -operand.0.float()?,
                UnaryOp::Complement => return Err(err(OperationKind::UnaryNegation, &op.1)),
            },
            Self::BinaryOp { op, lhs, rhs } => {
                let lhs = lhs.0.float()?;
                let rhs = rhs.0.float()?;
                match op.0 {
                    BinaryOp::Add => lhs + rhs,
                    BinaryOp::Sub => lhs - rhs,
                    BinaryOp::Mul => lhs * rhs,
                    BinaryOp::Div => lhs / rhs,
                    BinaryOp::Rem => lhs % rhs,
                    BinaryOp::BitwiseOR => return Err(err(OperationKind::BitwiseOR, &op.1)),
                    BinaryOp::BitwiseAND => return Err(err(OperationKind::BitwiseAND, &op.1)),
                    BinaryOp::BitwiseXOR => return Err(err(OperationKind::BitwiseXOR, &op.1)),
                }
            }
        })
    }
}

/// Creates a new parser for a sequence of binary expressions
///
/// # Parameters
///
/// * `elem`: parser for each atomic value of the new expression
/// * `op`: parser for the operation symbols in the expression
#[must_use]
fn binary_parser(
    elem: Parser!(Token, Spanned<Expr>),
    op: Parser!(Token, BinaryOp),
) -> Parser!(Token, Spanned<Expr>) {
    // Expression: `expression -> element [operator element]*`
    elem.clone()
        .then(
            // Allow operators to be prefixed by newlines
            just(Token::Ctrl('\n'))
                .repeated()
                .ignore_then(op.map_with_span(|op, span| (op, span)))
                .then(elem)
                .repeated(),
        )
        .foldl(|lhs, (op, rhs)| {
            // Calculate the span of the new expression from the spans of its operands, since they
            // are on the start/end of the expression
            let span = lhs.1.start..rhs.1.end;
            (
                Expr::BinaryOp {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
                span,
            )
        })
}

/// Creates a parser for expressions
#[must_use]
pub fn parser() -> Parser!(Token, Expr) {
    // Newline tokens
    let newline = || just(Token::Ctrl('\n')).repeated();
    // Literal values
    let literal_num = select! { |span|
        Token::Integer(x) => Expr::Integer(x),
        Token::Float(x) => Expr::Float((f64::from_bits(x), span)),
        Token::Character(c) => Expr::Character(c)
    };
    recursive(|expr| {
        // NOTE: newlines before atoms (literal numbers/parenthesized expressions) and operators
        // are allowed so that expressions may span multiple lines. Newlines aren't allowed after
        // them to prevent them from consuming new lines required to end statements

        // atom: `atom -> \n* (literal_num | ( expression ))`
        let atom = newline().ignore_then(
            literal_num
                .or(expr.delimited_by(
                    just(Token::Ctrl('(')),
                    newline().ignore_then(just(Token::Ctrl(')'))),
                ))
                .map_with_span(|atom, span: Span| (atom, span)),
        );

        // Unary expressions have the highest precedence
        // Unary expression: `unary -> (\n* [+-~])* atom`
        let op = newline().ignore_then(
            select! {
                Token::Operator('+') => UnaryOp::Plus,
                Token::Operator('-') => UnaryOp::Minus,
                Token::Operator('~') => UnaryOp::Complement,
            }
            .map_with_span(|op, span: Span| (op, span)),
        );
        let unary = op.repeated().then(atom).foldr(|op, rhs| {
            let span = op.1.start..rhs.1.end;
            (
                Expr::UnaryOp {
                    op,
                    operand: Box::new(rhs),
                },
                span,
            )
        });

        // Product expressions have the second highest precedence
        // product expression: `product -> unary ([*/%] unary)*`
        let product = binary_parser(
            unary,
            select! {
                Token::Operator('*') => BinaryOp::Mul,
                Token::Operator('/') => BinaryOp::Div,
                Token::Operator('%') => BinaryOp::Rem,
            },
        );

        // Bitwise expressions have the third highest precedence
        // bitwise expression: `bitwise -> product ([*/%] product)*`
        let bitwise = binary_parser(
            product,
            select! {
                Token::Operator('|') => BinaryOp::BitwiseOR,
                Token::Operator('&') => BinaryOp::BitwiseAND,
                Token::Operator('^') => BinaryOp::BitwiseXOR,
            },
        );

        // Addition expressions have the lowest precedence
        // addition expression: `addition -> bitwise ([+-] bitwise)*`
        binary_parser(
            bitwise,
            select! {
                Token::Operator('+') => BinaryOp::Add,
                Token::Operator('-') => BinaryOp::Sub,
            },
        )
        .map(|(expr, _)| expr) // Remove the span from the output since we don't need it
        .labelled("expression")
    })
}

#[cfg(test)]
mod test {
    use super::{BinaryOp, CompileError, ErrorKind, Expr, OperationKind, Span, Spanned, UnaryOp};

    fn parse(code: &str) -> Result<Expr, ()> {
        super::super::parse_with(super::parser(), code).map_err(|_| ())
    }

    type ExprResult = (Result<i32, CompileError>, Result<f64, CompileError>);

    fn test(test_cases: &[(&str, Expr, ExprResult)]) {
        for (src, expr, (res1, res2)) in test_cases {
            assert_eq!(parse(src), Ok(expr.clone()), "`{src}`");
            assert_eq!(expr.int(), *res1, "`{src}` as int\n{expr:?}");
            assert_eq!(expr.float(), *res2, "`{src}` as float\n{expr:?}");
        }
    }

    const fn float_op(op: OperationKind, s: Span) -> CompileError {
        ErrorKind::UnallowedFloatOperation(op).add_span(&s)
    }

    #[test]
    fn literal() {
        test(&[
            ("16", Expr::Integer(16), (Ok(16), Ok(16.0))),
            ("\n\n16", Expr::Integer(16), (Ok(16), Ok(16.0))),
            ("'a'", Expr::Character('a'), (Ok(97), Ok(97.0))),
            (
                "1.0",
                Expr::Float((1.0, 0..3)),
                (Err(ErrorKind::UnallowedFloat.add_span(&(0..3))), Ok(1.0)),
            ),
        ]);
    }

    const fn int(x: u32, s: Span) -> Spanned<Expr> {
        (Expr::Integer(x), s)
    }
    fn float(x: f64, s: Span) -> Spanned<Expr> {
        (Expr::Float((x, s.clone())), s)
    }

    fn un_op(op: Spanned<UnaryOp>, operand: Spanned<Expr>) -> Expr {
        Expr::UnaryOp {
            op,
            operand: Box::new(operand),
        }
    }

    fn bin_op(op: Spanned<BinaryOp>, lhs: Spanned<Expr>, rhs: Spanned<Expr>) -> Expr {
        Expr::BinaryOp {
            op,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        }
    }

    #[test]
    fn unary() {
        test(&[
            (
                "+2",
                un_op((UnaryOp::Plus, 0..1), int(2, 1..2)),
                (Ok(2), Ok(2.0)),
            ),
            (
                "\n\n+\n2",
                un_op((UnaryOp::Plus, 2..3), int(2, 4..5)),
                (Ok(2), Ok(2.0)),
            ),
            (
                "-2",
                un_op((UnaryOp::Minus, 0..1), int(2, 1..2)),
                (Ok(-2), Ok(-2.0)),
            ),
            (
                "~2",
                un_op((UnaryOp::Complement, 0..1), int(2, 1..2)),
                (Ok(!2), Err(float_op(OperationKind::UnaryNegation, 0..1))),
            ),
        ]);
    }

    #[test]
    fn binary_add() {
        test(&[
            (
                "5 + 7",
                bin_op((BinaryOp::Add, 2..3), int(5, 0..1), int(7, 4..5)),
                (Ok(12), Ok(12.0)),
            ),
            (
                "\n5 \n\n+ \n7",
                bin_op((BinaryOp::Add, 5..6), int(5, 1..2), int(7, 8..9)),
                (Ok(12), Ok(12.0)),
            ),
            (
                "2147483647 + 1",
                bin_op(
                    (BinaryOp::Add, 11..12),
                    int(i32::MAX as u32, 0..10),
                    int(1, 13..14),
                ),
                (Ok(i32::MIN), Ok(f64::from(i32::MAX) + 1.0)),
            ),
            (
                "2.5 + 7",
                bin_op((BinaryOp::Add, 4..5), float(2.5, 0..3), int(7, 6..7)),
                (Err(ErrorKind::UnallowedFloat.add_span(&(0..3))), Ok(9.5)),
            ),
            (
                "2.5 + 7.25",
                bin_op((BinaryOp::Add, 4..5), float(2.5, 0..3), float(7.25, 6..10)),
                (Err(ErrorKind::UnallowedFloat.add_span(&(0..3))), Ok(9.75)),
            ),
        ]);
    }

    #[test]
    fn binary_sub() {
        test(&[(
            "4294967295 - 4294967295",
            bin_op(
                (BinaryOp::Sub, 11..12),
                int(u32::MAX, 0..10),
                int(u32::MAX, 13..23),
            ),
            (Ok(0), Ok(0.0)),
        )]);
    }

    #[test]
    fn binary_mul() {
        test(&[
            (
                "5 * 7",
                bin_op((BinaryOp::Mul, 2..3), int(5, 0..1), int(7, 4..5)),
                (Ok(35), Ok(35.0)),
            ),
            (
                "\n5 \n\n* \n7",
                bin_op((BinaryOp::Mul, 5..6), int(5, 1..2), int(7, 8..9)),
                (Ok(35), Ok(35.0)),
            ),
            (
                "2147483647 * 2147483648",
                bin_op(
                    (BinaryOp::Mul, 11..12),
                    int(i32::MAX as u32, 0..10),
                    int(1 << 31, 13..23),
                ),
                (Ok(i32::MIN), Ok(4_611_686_016_279_904_256.0)),
            ),
        ]);
    }

    #[test]
    fn binary_div() {
        test(&[
            (
                "8 / 2",
                bin_op((BinaryOp::Div, 2..3), int(8, 0..1), int(2, 4..5)),
                (Ok(4), Ok(4.0)),
            ),
            (
                "10 / 0",
                bin_op((BinaryOp::Div, 3..4), int(10, 0..2), int(0, 5..6)),
                (
                    Err(ErrorKind::DivisionBy0.add_span(&(5..6))),
                    Ok(f64::INFINITY),
                ),
            ),
        ]);
    }

    #[test]
    fn binary_rem() {
        test(&[(
            "7 % 5",
            bin_op((BinaryOp::Rem, 2..3), int(7, 0..1), int(5, 4..5)),
            (Ok(2), Ok(2.0)),
        )]);
    }

    #[test]
    fn binary_bitwise() {
        test(&[
            (
                "0b0101 | 0b0011",
                bin_op(
                    (BinaryOp::BitwiseOR, 7..8),
                    int(0b0101, 0..6),
                    int(0b0011, 9..15),
                ),
                (Ok(0b0111), Err(float_op(OperationKind::BitwiseOR, 7..8))),
            ),
            (
                "0b0101 & 0b0011",
                bin_op(
                    (BinaryOp::BitwiseAND, 7..8),
                    int(0b0101, 0..6),
                    int(0b0011, 9..15),
                ),
                (Ok(0b0001), Err(float_op(OperationKind::BitwiseAND, 7..8))),
            ),
            (
                "0b0101 ^ 0b0011",
                bin_op(
                    (BinaryOp::BitwiseXOR, 7..8),
                    int(0b0101, 0..6),
                    int(0b0011, 9..15),
                ),
                (Ok(0b0110), Err(float_op(OperationKind::BitwiseXOR, 7..8))),
            ),
            (
                "\n0b0101 \n\n^ \n0b0011",
                bin_op(
                    (BinaryOp::BitwiseXOR, 10..11),
                    int(0b0101, 1..7),
                    int(0b0011, 13..19),
                ),
                (Ok(0b0110), Err(float_op(OperationKind::BitwiseXOR, 10..11))),
            ),
        ]);
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn precedence() {
        test(&[
            (
                "1 + 2 - 3",
                bin_op(
                    (BinaryOp::Sub, 6..7),
                    (
                        bin_op((BinaryOp::Add, 2..3), int(1, 0..1), int(2, 4..5)),
                        0..5,
                    ),
                    int(3, 8..9),
                ),
                (Ok(0), Ok(0.0)),
            ),
            (
                "1 + \n(\n2 - 3\n)",
                bin_op(
                    (BinaryOp::Add, 2..3),
                    int(1, 0..1),
                    (
                        bin_op((BinaryOp::Sub, 9..10), int(2, 7..8), int(3, 11..12)),
                        5..14,
                    ),
                ),
                (Ok(0), Ok(0.0)),
            ),
            (
                "1 | 6 & 3 ^ 9",
                bin_op(
                    (BinaryOp::BitwiseXOR, 10..11),
                    (
                        bin_op(
                            (BinaryOp::BitwiseAND, 6..7),
                            (
                                bin_op((BinaryOp::BitwiseOR, 2..3), int(1, 0..1), int(6, 4..5)),
                                0..5,
                            ),
                            int(3, 8..9),
                        ),
                        0..9,
                    ),
                    int(9, 12..13),
                ),
                (Ok(10), Err(float_op(OperationKind::BitwiseOR, 2..3))),
            ),
            (
                "1 * 6 / 3 % 2",
                bin_op(
                    (BinaryOp::Rem, 10..11),
                    (
                        bin_op(
                            (BinaryOp::Div, 6..7),
                            (
                                bin_op((BinaryOp::Mul, 2..3), int(1, 0..1), int(6, 4..5)),
                                0..5,
                            ),
                            int(3, 8..9),
                        ),
                        0..9,
                    ),
                    int(2, 12..13),
                ),
                (Ok(0), Ok(0.0)),
            ),
            (
                "\n- \n\n+ \n1",
                un_op(
                    (UnaryOp::Minus, 1..2),
                    (un_op((UnaryOp::Plus, 5..6), int(1, 8..9)), 5..9),
                ),
                (Ok(-1), Ok(-1.0)),
            ),
            (
                "~-+1",
                un_op(
                    (UnaryOp::Complement, 0..1),
                    (
                        un_op(
                            (UnaryOp::Minus, 1..2),
                            (un_op((UnaryOp::Plus, 2..3), int(1, 3..4)), 2..4),
                        ),
                        1..4,
                    ),
                ),
                (Ok(0), Err(float_op(OperationKind::UnaryNegation, 0..1))),
            ),
            (
                "1 + 6 | 3 * +9",
                bin_op(
                    (BinaryOp::Add, 2..3),
                    int(1, 0..1),
                    (
                        bin_op(
                            (BinaryOp::BitwiseOR, 6..7),
                            int(6, 4..5),
                            (
                                bin_op(
                                    (BinaryOp::Mul, 10..11),
                                    int(3, 8..9),
                                    (un_op((UnaryOp::Plus, 12..13), int(9, 13..14)), 12..14),
                                ),
                                8..14,
                            ),
                        ),
                        4..14,
                    ),
                ),
                (Ok(32), Err(float_op(OperationKind::BitwiseOR, 6..7))),
            ),
        ]);
    }
}
