use chumsky::prelude::*;

use super::{Parser, Token};

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
    Number(i32),
    Character(char),
    UnaryOp {
        op: UnaryOp,
        operand: Box<Expr>,
    },
    BinaryOp {
        op: BinaryOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
}

impl Expr {
    #[must_use]
    pub const fn value(&self) -> i32 {
        match self {
            Self::Number(value) => *value,
            Self::Character(c) => *c as i32,
            Self::UnaryOp { op, operand } => match op {
                UnaryOp::Plus => operand.value(),
                UnaryOp::Minus => -operand.value(),
                UnaryOp::Complement => !operand.value(),
            },
            Self::BinaryOp { op, lhs, rhs } => {
                let lhs = lhs.value();
                let rhs = rhs.value();
                match op {
                    BinaryOp::Add => lhs + rhs,
                    BinaryOp::Sub => lhs - rhs,
                    BinaryOp::Mul => lhs * rhs,
                    BinaryOp::Div => lhs / rhs,
                    BinaryOp::Rem => lhs % rhs,
                    BinaryOp::BitwiseOR => lhs | rhs,
                    BinaryOp::BitwiseAND => lhs & rhs,
                    BinaryOp::BitwiseXOR => lhs ^ rhs,
                }
            }
        }
    }
}

fn binary_parser(elem: Parser!(Token, Expr), op: Parser!(Token, BinaryOp)) -> Parser!(Token, Expr) {
    elem.clone()
        .then(op.then(elem).repeated())
        .foldl(|lhs, (op, rhs)| Expr::BinaryOp {
            op,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        })
}

#[must_use]
pub fn parser() -> impl Parser<Token, Expr, Error = Simple<Token>> + Clone {
    recursive(|expr| {
        let int = select! {
            Token::Number(x) => Expr::Number(x.parse().expect("We already parsed it as a number")),
            Token::Character(c) => Expr::Character(c)
        };
        let atom = int.or(expr.delimited_by(just(Token::Ctrl('(')), just(Token::Ctrl(')'))));

        let op = select! {
            Token::Operator('+') => UnaryOp::Plus,
            Token::Operator('-') => UnaryOp::Minus,
            Token::Operator('~') => UnaryOp::Complement,
        };
        let unary = op.repeated().then(atom).foldr(|op, rhs| Expr::UnaryOp {
            op,
            operand: Box::new(rhs),
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
        .labelled("expression")
    })
}

#[cfg(test)]
mod expr_eval_tests {
    use super::{BinaryOp, Expr, UnaryOp};

    #[allow(clippy::unnecessary_box_returns)]
    fn num(x: i32) -> Box<super::Expr> {
        Box::new(Expr::Number(x))
    }

    #[test]
    fn number() {
        let expr = Expr::Number(16);
        assert_eq!(expr.value(), 16);
    }

    #[test]
    fn character() {
        let expr = Expr::Character('a');
        assert_eq!(expr.value(), 97);
    }

    fn bin_op(op: BinaryOp, lhs: i32, rhs: i32) -> Expr {
        Expr::BinaryOp {
            op,
            lhs: num(lhs),
            rhs: num(rhs),
        }
    }

    #[test]
    fn unary_plus() {
        let expr = Expr::UnaryOp {
            op: UnaryOp::Plus,
            operand: num(2),
        };
        assert_eq!(expr.value(), 2);
    }

    #[test]
    fn unary_minus() {
        let expr = Expr::UnaryOp {
            op: UnaryOp::Minus,
            operand: Box::new(Expr::Number(2)),
        };
        assert_eq!(expr.value(), -2);
    }

    #[test]
    fn binary_add() {
        assert_eq!(bin_op(BinaryOp::Add, 5, 7).value(), 12);
    }

    #[test]
    fn binary_sub() {
        assert_eq!(bin_op(BinaryOp::Sub, 5, 7).value(), -2);
    }

    #[test]
    fn binary_mul() {
        assert_eq!(bin_op(BinaryOp::Mul, 5, 7).value(), 35);
    }

    #[test]
    fn binary_div() {
        assert_eq!(bin_op(BinaryOp::Div, 8, 2).value(), 4);
    }

    #[test]
    fn binary_rem() {
        assert_eq!(bin_op(BinaryOp::Rem, 7, 5).value(), 2);
    }

    #[test]
    fn binary_or() {
        assert_eq!(bin_op(BinaryOp::BitwiseOR, 0b0100, 0b1100).value(), 0b1100);
    }

    #[test]
    fn binary_and() {
        assert_eq!(bin_op(BinaryOp::BitwiseAND, 0b0110, 0b1100).value(), 0b0100);
    }

    #[test]
    fn binary_xor() {
        assert_eq!(bin_op(BinaryOp::BitwiseXOR, 0b0101, 0b1100).value(), 0b1001);
    }

    #[test]
    fn combined() {
        let expr = Expr::UnaryOp {
            op: UnaryOp::Minus,
            operand: Box::new(Expr::BinaryOp {
                op: BinaryOp::Add,
                // -4
                lhs: Box::new(Expr::BinaryOp {
                    op: BinaryOp::Mul,
                    // -2
                    lhs: Box::new(Expr::UnaryOp {
                        op: UnaryOp::Minus,
                        // 2
                        operand: Box::new(Expr::BinaryOp {
                            op: BinaryOp::Div,
                            // 6
                            lhs: Box::new(bin_op(BinaryOp::Rem, 13, 7)),
                            rhs: num(3),
                        }),
                    }),
                    rhs: num(2),
                }),
                // 0b0101 = 5
                rhs: Box::new(Expr::BinaryOp {
                    op: BinaryOp::BitwiseOR,
                    // 0b0001
                    lhs: Box::new(Expr::UnaryOp {
                        op: UnaryOp::Plus,
                        operand: num(0b0001),
                    }),
                    // 0b0100
                    rhs: Box::new(Expr::BinaryOp {
                        op: BinaryOp::BitwiseAND,
                        // 0b0101
                        lhs: Box::new(Expr::BinaryOp {
                            op: BinaryOp::BitwiseXOR,
                            lhs: num(0b0011),
                            rhs: num(0b0110),
                        }),
                        rhs: num(0b1110),
                    }),
                }),
            }),
        };
        assert_eq!(expr.value(), -1);
    }
}
