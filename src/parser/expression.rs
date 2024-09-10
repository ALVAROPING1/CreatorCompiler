use chumsky::prelude::*;

use super::{Parser, Span, Spanned, Token};
use crate::compiler::{CompileError, ErrorKind, OperationKind};

#[derive(Debug, Clone, Copy)]
pub enum UnaryOp {
    Plus,
    Minus,
    Complement,
}

#[derive(Debug, Clone, Copy)]
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

#[derive(Debug)]
pub enum Expr {
    Integer(u32),
    Float(Spanned<f64>),
    Character(char),
    UnaryOp {
        op: Spanned<UnaryOp>,
        operand: Box<Spanned<Expr>>,
    },
    BinaryOp {
        op: Spanned<BinaryOp>,
        lhs: Box<Spanned<Expr>>,
        rhs: Box<Spanned<Expr>>,
    },
}

impl Expr {
    pub fn int(&self) -> Result<i32, CompileError> {
        #[allow(clippy::cast_possible_wrap)]
        Ok(match self {
            Self::Integer(value) => *value as i32,
            Self::Float((_, span)) => return Err(ErrorKind::UnallowedFloat.add_span(span.clone())),
            Self::Character(c) => *c as i32,
            Self::UnaryOp { op, operand } => match op.0 {
                UnaryOp::Plus => operand.0.int()?,
                UnaryOp::Minus => -operand.0.int()?,
                UnaryOp::Complement => !operand.0.int()?,
            },
            Self::BinaryOp { op, lhs, rhs } => {
                let lhs = lhs.0.int()?;
                let span = rhs.1.clone();
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

    pub fn float(&self) -> Result<f64, CompileError> {
        Ok(match self {
            Self::Integer(value) => f64::from(*value),
            Self::Float((value, _)) => *value,
            Self::Character(c) => f64::from(*c as u32),
            Self::UnaryOp { op, operand } => match op.0 {
                UnaryOp::Plus => operand.0.float()?,
                UnaryOp::Minus => -operand.0.float()?,
                UnaryOp::Complement => Err(ErrorKind::UnallowedFloatOperation(
                    OperationKind::UnaryNegation,
                )
                .add_span(op.1.clone()))?,
            },
            Self::BinaryOp { op, lhs, rhs } => {
                let lhs = lhs.0.float()?;
                // let span = rhs.1.clone();
                let rhs = rhs.0.float()?;
                match op.0 {
                    BinaryOp::Add => lhs + rhs,
                    BinaryOp::Sub => lhs - rhs,
                    BinaryOp::Mul => lhs * rhs,
                    BinaryOp::Div => lhs / rhs,
                    BinaryOp::Rem => lhs % rhs,
                    BinaryOp::BitwiseOR => {
                        return Err(ErrorKind::UnallowedFloatOperation(OperationKind::BitwiseOR)
                            .add_span(op.1.clone()))
                    }
                    BinaryOp::BitwiseAND => {
                        return Err(
                            ErrorKind::UnallowedFloatOperation(OperationKind::BitwiseAND)
                                .add_span(op.1.clone()),
                        )
                    }
                    BinaryOp::BitwiseXOR => {
                        return Err(
                            ErrorKind::UnallowedFloatOperation(OperationKind::BitwiseXOR)
                                .add_span(op.1.clone()),
                        )
                    }
                }
            }
        })
    }
}

#[must_use]
fn binary_parser(
    elem: Parser!(Token, Spanned<Expr>),
    op: Parser!(Token, BinaryOp),
) -> Parser!(Token, Spanned<Expr>) {
    elem.clone()
        .then(
            op.map_with_span(|op, span| (op, span))
                .then(elem)
                .repeated(),
        )
        .foldl(|lhs, (op, rhs)| {
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

#[must_use]
pub fn parser() -> Parser!(Token, Expr) {
    recursive(|expr| {
        let literal_num = select! { |span|
            Token::Integer(x) => Expr::Integer(x),
            Token::Float(x) => Expr::Float((f64::from_bits(x), span)),
            Token::Character(c) => Expr::Character(c)
        };
        let atom = literal_num
            .or(expr.delimited_by(just(Token::Ctrl('(')), just(Token::Ctrl(')'))))
            .map_with_span(|atom, span: Span| (atom, span));

        let op = select! {
            Token::Operator('+') => UnaryOp::Plus,
            Token::Operator('-') => UnaryOp::Minus,
            Token::Operator('~') => UnaryOp::Complement,
        }
        .map_with_span(|op, span: Span| (op, span));
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

        let product = binary_parser(
            unary,
            select! {
                Token::Operator('*') => BinaryOp::Mul,
                Token::Operator('/') => BinaryOp::Div,
                Token::Operator('%') => BinaryOp::Rem,
            },
        );

        let bitwise = binary_parser(
            product,
            select! {
                Token::Operator('|') => BinaryOp::BitwiseOR,
                Token::Operator('&') => BinaryOp::BitwiseAND,
                Token::Operator('^') => BinaryOp::BitwiseXOR,
            },
        );

        binary_parser(
            bitwise,
            select! {
                Token::Operator('+') => BinaryOp::Add,
                Token::Operator('-') => BinaryOp::Sub,
            },
        )
        .map(|(expr, _)| expr)
        .labelled("expression")
    })
}

#[cfg(test)]
mod expr_eval_tests {
    use super::{BinaryOp, ErrorKind, Expr, Spanned, UnaryOp};

    #[allow(clippy::unnecessary_box_returns)]
    fn span<T>(x: T) -> Box<Spanned<T>> {
        Box::new((x, 0..0))
    }

    #[allow(clippy::unnecessary_box_returns)]
    fn num(x: u32) -> Box<Spanned<Expr>> {
        span(Expr::Integer(x))
    }

    #[test]
    fn number() {
        let expr = Expr::Integer(16);
        assert_eq!(expr.int(), Ok(16));
    }

    #[test]
    fn character() {
        let expr = Expr::Character('a');
        assert_eq!(expr.int(), Ok(97));
    }

    fn bin_op(op: BinaryOp, lhs: u32, rhs: u32) -> Expr {
        Expr::BinaryOp {
            op: (op, 0..0),
            lhs: num(lhs),
            rhs: num(rhs),
        }
    }

    #[test]
    fn unary_plus() {
        let expr = Expr::UnaryOp {
            op: (UnaryOp::Plus, 0..0),
            operand: num(2),
        };
        assert_eq!(expr.int(), Ok(2));
    }

    #[test]
    fn unary_minus() {
        let expr = Expr::UnaryOp {
            op: (UnaryOp::Minus, 0..0),
            operand: num(2),
        };
        assert_eq!(expr.int(), Ok(-2));
    }

    #[test]
    fn binary_add() {
        assert_eq!(bin_op(BinaryOp::Add, 5, 7).int(), Ok(12));
        assert_eq!(
            bin_op(BinaryOp::Add, i32::MAX as u32, 1).int(),
            Ok(i32::MIN)
        );
    }

    #[test]
    fn binary_sub() {
        assert_eq!(bin_op(BinaryOp::Sub, 5, 7).int(), Ok(-2));
        assert_eq!(
            bin_op(BinaryOp::Sub, i32::MAX as u32, i32::MAX as u32).int(),
            Ok(0)
        );
    }

    #[test]
    fn binary_mul() {
        assert_eq!(bin_op(BinaryOp::Mul, 5, 7).int(), Ok(35));
        assert_eq!(
            bin_op(BinaryOp::Mul, i32::MAX as u32, 1 << 31).int(),
            Ok(i32::MIN)
        );
    }

    #[test]
    fn binary_div() {
        assert_eq!(bin_op(BinaryOp::Div, 8, 2).int(), Ok(4));
    }

    #[test]
    fn div_by_0() {
        assert_eq!(
            bin_op(BinaryOp::Div, 10, 0).int(),
            Err(ErrorKind::DivisionBy0.add_span(0..0))
        );
    }

    #[test]
    fn binary_rem() {
        assert_eq!(bin_op(BinaryOp::Rem, 7, 5).int(), Ok(2));
    }

    #[test]
    fn binary_or() {
        assert_eq!(
            bin_op(BinaryOp::BitwiseOR, 0b0100, 0b1100).int(),
            Ok(0b1100)
        );
    }

    #[test]
    fn binary_and() {
        assert_eq!(
            bin_op(BinaryOp::BitwiseAND, 0b0110, 0b1100).int(),
            Ok(0b0100)
        );
    }

    #[test]
    fn binary_xor() {
        assert_eq!(
            bin_op(BinaryOp::BitwiseXOR, 0b0101, 0b1100).int(),
            Ok(0b1001)
        );
    }

    #[test]
    fn combined() {
        let expr = Expr::UnaryOp {
            op: (UnaryOp::Minus, 0..0),
            operand: span(Expr::BinaryOp {
                op: (BinaryOp::Add, 0..0),
                // -4
                lhs: span(Expr::BinaryOp {
                    op: (BinaryOp::Mul, 0..0),
                    // -2
                    lhs: span(Expr::UnaryOp {
                        op: (UnaryOp::Minus, 0..0),
                        // 2
                        operand: span(Expr::BinaryOp {
                            op: (BinaryOp::Div, 0..0),
                            // 6
                            lhs: span(bin_op(BinaryOp::Rem, 13, 7)),
                            rhs: num(3),
                        }),
                    }),
                    rhs: num(2),
                }),
                // 0b0101 = 5
                rhs: span(Expr::BinaryOp {
                    op: (BinaryOp::BitwiseOR, 0..0),
                    // 0b0001
                    lhs: span(Expr::UnaryOp {
                        op: (UnaryOp::Plus, 0..0),
                        operand: num(0b0001),
                    }),
                    // 0b0100
                    rhs: span(Expr::BinaryOp {
                        op: (BinaryOp::BitwiseAND, 0..0),
                        // 0b0101
                        lhs: span(Expr::BinaryOp {
                            op: (BinaryOp::BitwiseXOR, 0..0),
                            lhs: num(0b0011),
                            rhs: num(0b0110),
                        }),
                        rhs: num(0b1110),
                    }),
                }),
            }),
        };
        assert_eq!(expr.int(), Ok(-1));
    }
}
