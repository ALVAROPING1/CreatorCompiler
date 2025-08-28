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

//! Module containing the definition of the expressions sub-parser as well as their evaluation
//!
//! The main entry point for creating the parser is the [`parser()`] function, with the evaluation
//! of methods being defined in the methods of the [`Expr`] type

use chumsky::pratt::{infix, left, prefix};
use chumsky::{input::ValueInput, prelude::*};
use num_bigint::{BigInt, BigUint};

use super::{lexer::Operator, Parser, Span, Spanned, Token};
use crate::architecture::ModifierDefinitions;
use crate::compiler::error::SpannedErr;
use crate::compiler::{ErrorData, ErrorKind};
use crate::number::Number;

/// Allowed unary operations
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnaryOp {
    /// Unary plus, essentially a no-op
    Plus,
    /// Unary negation
    Minus,
    /// Unary binary complement
    Complement,
    /// Unary Modifier
    Modifier(String),
}

/// Allowed binary operations
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
    /// Addition
    Add,
    /// Subtraction
    Sub,
    /// Multiplication
    Mul,
    /// Division
    Div,
    /// Remainder, with the same sign as the left operand
    Rem,
    /// Bitwise OR
    BitwiseOR,
    /// Bitwise AND
    BitwiseAND,
    /// Bitwise XOR
    BitwiseXOR,
}

/// Mathematical expression on constant values
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    /// Integer literal
    Integer(BigUint),
    /// Float literal
    Float(Spanned<f64>),
    /// Character literal
    Character(char),
    /// Identifier
    Identifier(Spanned<String>),
    /// Unary operation on other expressions
    UnaryOp {
        /// Operation to perform
        op: Spanned<UnaryOp>,
        /// Operand to perform the operation on
        operand: Box<Spanned<Expr>>,
    },
    /// Binary operation on other expressions
    BinaryOp {
        /// Operation to perform
        op: Spanned<BinaryOp>,
        /// Left operand of the operation
        lhs: Box<Spanned<Expr>>,
        /// Right operand of the operation
        rhs: Box<Spanned<Expr>>,
    },
}

impl Expr {
    /// Evaluates the expression
    ///
    /// # Parameters
    ///
    /// * `ident_eval`: callback function to evaluate identifiers
    /// * `modifiers`: definitions of the modifiers allowed
    ///
    /// # Errors
    ///
    /// Returns a [`ErrorKind::UnallowedFloatOperation`] if an operation that's undefined with
    /// floats is attempted, a [`ErrorKind::DivisionBy0`] if a division by 0 is attempted, or any
    /// [`ErrorKind`] returned by the callback function
    pub fn eval(
        &self,
        ident_eval: impl Copy + Fn(&str) -> Result<BigInt, ErrorKind>,
        modifiers: &ModifierDefinitions,
    ) -> Result<Number, ErrorData> {
        match self {
            Self::Integer(value) => Ok(value.clone().into()),
            Self::Float((value, span)) => Ok(Number::from((*value, *span))),
            Self::Character(c) => Ok((*c as u32).into()),
            Self::Identifier((ident, span)) => Ok(ident_eval(ident).add_span(*span)?.into()),
            Self::UnaryOp { op, operand } => match &op.0 {
                UnaryOp::Plus => operand.0.eval(ident_eval, modifiers),
                UnaryOp::Minus => Ok(-(operand.0.eval(ident_eval, modifiers)?)),
                UnaryOp::Complement => (!(operand.0.eval(ident_eval, modifiers)?)).add_span(op.1),
                UnaryOp::Modifier(name) => {
                    let x = operand.0.eval(ident_eval, modifiers)?;
                    let modifier = modifiers
                        .get(name.as_str())
                        .ok_or_else(|| ErrorKind::UnknownModifier(name.clone()).add_span(op.1))?;
                    Ok(x.modify(*modifier))
                }
            },
            Self::BinaryOp { op, lhs, rhs } => {
                let lhs = lhs.0.eval(ident_eval, modifiers)?;
                let span = rhs.1;
                let rhs = rhs.0.eval(ident_eval, modifiers)?;
                match op.0 {
                    BinaryOp::Add => Ok(lhs + rhs),
                    BinaryOp::Sub => Ok(lhs - rhs),
                    BinaryOp::Mul => Ok(lhs * rhs),
                    BinaryOp::Div => (lhs / rhs).ok_or(ErrorKind::DivisionBy0(span)),
                    BinaryOp::Rem => (lhs % rhs).ok_or(ErrorKind::RemainderWith0(span)),
                    BinaryOp::BitwiseOR => lhs | rhs,
                    BinaryOp::BitwiseAND => lhs & rhs,
                    BinaryOp::BitwiseXOR => lhs ^ rhs,
                }
                .add_span(op.1)
            }
        }
    }

    /// Identifier evaluator utility function that doesn't allow any identifier in the expression
    ///
    /// # Errors
    ///
    /// Always errors with a [`ErrorKind::UnallowedLabel`]
    pub const fn unallowed_ident<T>(_: &str) -> Result<T, ErrorKind> {
        Err(ErrorKind::UnallowedLabel)
    }

    /// Utility function to evaluate an expression without allowing identifiers
    ///
    /// # Errors
    ///
    /// Errors in the same cases as [`Expr::eval`], but any identifier usage results in a
    /// [`ErrorKind::UnallowedLabel`]
    pub fn eval_no_ident(&self, modifiers: &ModifierDefinitions) -> Result<Number, ErrorData> {
        self.eval(Self::unallowed_ident, modifiers)
    }
}

/// Creates a parser for expressions
#[must_use]
pub fn parser<'tokens, I>() -> Parser!('tokens, I, Spanned<Expr>)
where
    I: ValueInput<'tokens, Token = Token, Span = Span>,
{
    // Newline tokens
    let newline = || just(Token::Ctrl('\n')).repeated();
    // Literal values
    let literal = select! {
        Token::Integer(x) => Expr::Integer(x),
        Token::Float(x) = e => Expr::Float((x.into(), e.span())),
        Token::Character(c) => Expr::Character(c),
        Token::Identifier(ident) = e => Expr::Identifier((ident, e.span())),
        Token::Directive(ident) = e => Expr::Identifier((ident, e.span())),
    }
    .labelled("literal");

    // Operator parser
    macro_rules! op {
        (:$name:literal: $($i:ident => $o:expr),+$(,)?) => {
            newline().ignore_then(
                select! { $(Token::Operator(Operator::$i) => $o,)+ }
                    .map_with(|x, e| (x, e.span()))
                    .labelled(concat!($name, " operator"))
            )
        };
        ($($i:ident => $o:expr),+) => { op!(:"binary": $($i => $o,)+) };
    }

    // Folding function for binary operations. We need to define it with a macro because the
    // closure doesn't use the generic lifetime bounds required when stored in a variable
    macro_rules! fold {
        () => {
            |lhs: Spanned<Expr>, op: Spanned<BinaryOp>, rhs: Spanned<Expr>, _| {
                let span = lhs.1.start..rhs.1.end;
                (
                    Expr::BinaryOp {
                        op,
                        lhs: Box::new(lhs),
                        rhs: Box::new(rhs),
                    },
                    Span::new(op.1.context, span),
                )
            }
        };
    }

    recursive(|expr| {
        // NOTE: newlines before atoms (literal numbers/parenthesized expressions) and operators
        // are allowed so that expressions may span multiple lines. Newlines aren't allowed after
        // them to prevent them from consuming new lines required to end statements

        // paren_expr: `paren_expr -> ( expression )`
        let paren_expr = expr.delimited_by(
            just(Token::Ctrl('(')),
            newline().ignore_then(just(Token::Ctrl(')'))),
        );
        // modifier: `modifier -> % ident paren_expr`
        let modifier = just(Token::Operator(Operator::Percent))
            .ignore_then(select! {Token::Identifier(name) => name }.labelled("identifier"))
            .map_with(|name, e| (UnaryOp::Modifier(name), e.span()))
            .then(paren_expr.clone())
            .map(|(op, expr)| Expr::UnaryOp {
                op,
                operand: Box::new(expr),
            });
        // Remove span to replace it with one including the parenthesis
        let paren_expr = paren_expr.map(|(x, _)| x);

        // atom: `atom -> \n* (literal | modifier | paren_expr)`
        let atom = choice((literal, modifier, paren_expr)).map_with(|atom, e| (atom, e.span()));
        let atom = newline().ignore_then(atom);
        let atom = atom.labelled("expression").as_context();

        let expr = atom.pratt((
            prefix(
                4,
                op!(:"unary": Plus => UnaryOp::Plus, Minus => UnaryOp::Minus, Tilde => UnaryOp::Complement),
                |op: Spanned<UnaryOp>, rhs: Spanned<Expr>, _| {
                    let span = op.1.start..rhs.1.end;
                    let ctx = op.1.context;
                    (
                        Expr::UnaryOp {
                            op,
                            operand: Box::new(rhs),
                        },
                        Span::new(ctx, span),
                    )
                },
            ),
            infix(left(3), op!(Star => BinaryOp::Mul, Slash => BinaryOp::Div, Percent => BinaryOp::Rem), fold!()),
            infix(left(2), op!(Or => BinaryOp::BitwiseOR, And => BinaryOp::BitwiseAND, Caret => BinaryOp::BitwiseXOR), fold!()),
            infix(left(1), op!(Plus => BinaryOp::Add, Minus => BinaryOp::Sub), fold!())
        ));
        expr.labelled("expression").as_context()
    })
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::architecture::Modifier;
    use crate::compiler::error::OperationKind;
    use crate::span::test::*;

    fn parse(code: &str) -> Result<Spanned<Expr>, ()> {
        super::super::parse_with!(super::parser(), "#", code).map_err(|_| ())
    }

    type ExprResult = Result<Number, ErrorData>;

    fn test(test_cases: impl IntoIterator<Item = (&'static str, Expr, ExprResult)>) {
        let ident_eval = |ident: &str| {
            if ident.len() == 1 {
                Ok(BigInt::from(ident.as_bytes()[0] - b'a' + 5))
            } else {
                Err(ErrorKind::UnknownLabel(ident.to_owned()))
            }
        };
        #[allow(clippy::unwrap_used)]
        let modifier = |range: (u64, Option<u64>), lower_signed, output_signed| Modifier {
            range: range.try_into().unwrap(),
            lower_signed,
            output_signed,
        };
        let modifiers = ModifierDefinitions::from([
            ("hi", modifier((12, Some(32)), true, false)),
            ("low", modifier((0, Some(12)), false, true)),
        ]);
        for (src, expr, expected) in test_cases {
            let start = (src.trim_start().as_ptr() as usize) - (src.as_ptr() as usize);
            let span = (start..src.len()).span();
            assert_eq!(parse(src), Ok((expr.clone(), span)), "`{src:?}`");
            let res = expr.eval(ident_eval, &modifiers);
            assert_eq!(res, expected, "`{src:?}`\n{expr:?}");
        }
    }

    #[must_use]
    fn float_op<S: IntoSpan>(op: OperationKind, float_span: S, op_span: S) -> ErrorData {
        ErrorKind::UnallowedFloatOperation(op, float_span.span()).add_span(op_span.span())
    }

    #[test]
    fn unallowed_ident() {
        for i in &["a", "b", "test", "identifier"] {
            assert_eq!(
                Expr::unallowed_ident::<i32>(i),
                Err(ErrorKind::UnallowedLabel)
            );
        }
    }

    #[test]
    fn literal() {
        let int = BigUint::from(2u8).pow(128) - 1u8;
        test([
            ("16", Expr::Integer(16u8.into()), Ok(16.into())),
            ("\n\n16", Expr::Integer(16u8.into()), Ok(16.into())),
            ("'a'", Expr::Character('a'), Ok(('a' as u32).into())),
            (
                "a",
                Expr::Identifier(("a".into(), (0..1).span())),
                Ok(5.into()),
            ),
            (
                "test",
                Expr::Identifier(("test".into(), (0..4).span())),
                Err(ErrorKind::UnknownLabel("test".into()).add_span((0..4).span())),
            ),
            (
                ".test",
                Expr::Identifier((".test".into(), (0..5).span())),
                Err(ErrorKind::UnknownLabel(".test".into()).add_span((0..5).span())),
            ),
            (
                "1.0",
                Expr::Float((1.0, (0..3).span())),
                Ok((1.0, 0..3).into()),
            ),
            (
                "340282366920938463463374607431768211455",
                Expr::Integer(int.clone()),
                Ok(int.into()),
            ),
        ]);
    }

    #[must_use]
    fn int(x: u32, s: impl IntoSpan) -> Spanned<Expr> {
        (Expr::Integer(x.into()), s.span())
    }

    #[must_use]
    fn float(x: f64, s: impl IntoSpan) -> Spanned<Expr> {
        let s = s.span();
        (Expr::Float((x, s)), s)
    }

    #[must_use]
    fn un_op(op: (UnaryOp, impl IntoSpan), operand: (Expr, impl IntoSpan)) -> Expr {
        Expr::UnaryOp {
            op: (op.0, op.1.span()),
            operand: Box::new((operand.0, operand.1.span())),
        }
    }

    #[must_use]
    fn bin_op<S1, S2, S3>(op: (BinaryOp, S1), lhs: (Expr, S2), rhs: (Expr, S3)) -> Expr
    where
        S1: IntoSpan,
        S2: IntoSpan,
        S3: IntoSpan,
    {
        Expr::BinaryOp {
            op: (op.0, op.1.span()),
            lhs: Box::new((lhs.0, lhs.1.span())),
            rhs: Box::new((rhs.0, rhs.1.span())),
        }
    }

    #[test]
    fn unary() {
        let modifier = |n: &str, s| (UnaryOp::Modifier(n.into()), s);
        test([
            (
                "+2",
                un_op((UnaryOp::Plus, 0..1), int(2, 1..2)),
                Ok(2.into()),
            ),
            (
                "+2.2",
                un_op((UnaryOp::Plus, 0..1), float(2.2, 1..4)),
                Ok((2.2, 1..4).into()),
            ),
            (
                "\n\n+\n2",
                un_op((UnaryOp::Plus, 2..3), int(2, 4..5)),
                Ok(2.into()),
            ),
            (
                "\n\n+\n2.2",
                un_op((UnaryOp::Plus, 2..3), float(2.2, 4..7)),
                Ok((2.2, 4..7).into()),
            ),
            (
                "-2",
                un_op((UnaryOp::Minus, 0..1), int(2, 1..2)),
                Ok((-2).into()),
            ),
            (
                "~2",
                un_op((UnaryOp::Complement, 0..1), int(2, 1..2)),
                Ok((!2).into()),
            ),
            (
                "~2.75",
                un_op((UnaryOp::Complement, 0..1), float(2.75, 1..5)),
                Err(float_op(OperationKind::Complement, 1..5, 0..1)),
            ),
            (
                "%hi(0xABCDE701)",
                un_op(modifier("hi", 0..3), int(0xABCD_E701, 4..14)),
                Ok((0xABCDE).into()),
            ),
            (
                "%low(0xABCDE701)",
                un_op(modifier("low", 0..4), int(0xABCD_E701, 5..15)),
                Ok((0x701).into()),
            ),
            (
                "%mod(0xABCDE701)",
                un_op(modifier("mod", 0..4), int(0xABCD_E701, 5..15)),
                Err(ErrorKind::UnknownModifier("mod".into()).add_span((0..4).span())),
            ),
        ]);
    }

    #[test]
    fn binary_add() {
        test([
            (
                "5 + 7",
                bin_op((BinaryOp::Add, 2..3), int(5, 0..1), int(7, 4..5)),
                Ok(12.into()),
            ),
            (
                "\n5 \n\n+ \n7",
                bin_op((BinaryOp::Add, 5..6), int(5, 1..2), int(7, 8..9)),
                Ok(12.into()),
            ),
            (
                "2147483647 + 1",
                bin_op(
                    (BinaryOp::Add, 11..12),
                    int(i32::MAX as u32, 0..10),
                    int(1, 13..14),
                ),
                Ok(2_147_483_648_u32.into()),
            ),
            (
                "2.5 + 7",
                bin_op((BinaryOp::Add, 4..5), float(2.5, 0..3), int(7, 6..7)),
                Ok((9.5, 0..3).into()),
            ),
            (
                "2.5 + 7.25",
                bin_op((BinaryOp::Add, 4..5), float(2.5, 0..3), float(7.25, 6..10)),
                Ok((9.75, 0..3).into()),
            ),
        ]);
    }

    #[test]
    fn binary_sub() {
        test([
            (
                "4294967295 - 4294967295",
                bin_op(
                    (BinaryOp::Sub, 11..12),
                    int(u32::MAX, 0..10),
                    int(u32::MAX, 13..23),
                ),
                Ok(0.into()),
            ),
            (
                "d - a",
                bin_op(
                    (BinaryOp::Sub, 2..3),
                    (Expr::Identifier(("d".into(), (0..1).span())), 0..1),
                    (Expr::Identifier(("a".into(), (4..5).span())), 4..5),
                ),
                Ok(3.into()),
            ),
        ]);
    }

    #[test]
    fn binary_mul() {
        test([
            (
                "5 * 7",
                bin_op((BinaryOp::Mul, 2..3), int(5, 0..1), int(7, 4..5)),
                Ok(35.into()),
            ),
            (
                "\n5 \n\n* \n7",
                bin_op((BinaryOp::Mul, 5..6), int(5, 1..2), int(7, 8..9)),
                Ok(35.into()),
            ),
            (
                "2147483647 * 2147483648",
                bin_op(
                    (BinaryOp::Mul, 11..12),
                    int(i32::MAX as u32, 0..10),
                    int(1 << 31, 13..23),
                ),
                Ok((BigInt::from(2_147_483_647) * BigInt::from(2_147_483_648_u32)).into()),
            ),
        ]);
    }

    #[test]
    fn binary_div() {
        test([
            (
                "8 / 2",
                bin_op((BinaryOp::Div, 2..3), int(8, 0..1), int(2, 4..5)),
                Ok(4.into()),
            ),
            (
                "10 / 0",
                bin_op((BinaryOp::Div, 3..4), int(10, 0..2), int(0, 5..6)),
                Err(ErrorKind::DivisionBy0((5..6).span()).add_span((3..4).span())),
            ),
            (
                "10 / 0.0",
                bin_op((BinaryOp::Div, 3..4), int(10, 0..2), float(0.0, 5..8)),
                Ok((f64::INFINITY, 5..8).into()),
            ),
        ]);
    }

    #[test]
    fn binary_rem() {
        test([
            (
                "7 % 5",
                bin_op((BinaryOp::Rem, 2..3), int(7, 0..1), int(5, 4..5)),
                Ok(2.into()),
            ),
            (
                "7 % 0",
                bin_op((BinaryOp::Rem, 2..3), int(7, 0..1), int(0, 4..5)),
                Err(ErrorKind::RemainderWith0((4..5).span()).add_span((2..3).span())),
            ),
            (
                "7.2 % 5",
                bin_op((BinaryOp::Rem, 4..5), float(7.2, 0..3), int(5, 6..7)),
                Ok((2.2, 0..3).into()),
            ),
        ]);
    }

    #[test]
    fn binary_bitwise() {
        test([
            (
                "0b0101 | 0b0011",
                bin_op(
                    (BinaryOp::BitwiseOR, 7..8),
                    int(0b0101, 0..6),
                    int(0b0011, 9..15),
                ),
                Ok(0b0111.into()),
            ),
            (
                "0b0101 & 0b0011",
                bin_op(
                    (BinaryOp::BitwiseAND, 7..8),
                    int(0b0101, 0..6),
                    int(0b0011, 9..15),
                ),
                Ok(0b0001.into()),
            ),
            (
                "0b0101 ^ 0b0011",
                bin_op(
                    (BinaryOp::BitwiseXOR, 7..8),
                    int(0b0101, 0..6),
                    int(0b0011, 9..15),
                ),
                Ok(0b0110.into()),
            ),
            (
                "\n0b0101 \n\n^ \n0b0011",
                bin_op(
                    (BinaryOp::BitwiseXOR, 10..11),
                    int(0b0101, 1..7),
                    int(0b0011, 13..19),
                ),
                Ok(0b0110.into()),
            ),
            (
                "\n0b0101 \n\n^ \n1.1",
                bin_op(
                    (BinaryOp::BitwiseXOR, 10..11),
                    int(0b0101, 1..7),
                    float(1.1, 13..16),
                ),
                Err(float_op(OperationKind::BitwiseXOR, 13..16, 10..11)),
            ),
        ]);
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn precedence() {
        test([
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
                Ok(0.into()),
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
                Ok(0.into()),
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
                Ok(10.into()),
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
                Ok(0.into()),
            ),
            (
                "\n- \n\n+ \n1",
                un_op(
                    (UnaryOp::Minus, 1..2),
                    (un_op((UnaryOp::Plus, 5..6), int(1, 8..9)), 5..9),
                ),
                Ok((-1).into()),
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
                Ok(0.into()),
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
                Ok(32.into()),
            ),
            (
                "1 + %low(0x1234) * 3",
                bin_op(
                    (BinaryOp::Add, 2..3),
                    int(1, 0..1),
                    (
                        bin_op(
                            (BinaryOp::Mul, 17..18),
                            (
                                un_op((UnaryOp::Modifier("low".into()), 4..8), int(0x1234, 9..15)),
                                4..16,
                            ),
                            int(3, 19..20),
                        ),
                        4..20,
                    ),
                ),
                Ok((1 + 0x234 * 3).into()),
            ),
        ]);
    }
}
