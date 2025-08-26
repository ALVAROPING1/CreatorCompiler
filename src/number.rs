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

//! Module containing the definition of [`Number`]

use std::ops;

use num_bigint::{BigInt, BigUint};
use num_traits::cast::ToPrimitive;

use crate::compiler::error::OperationKind;
use crate::compiler::ErrorKind;
use crate::span::{Span, Spanned};

/// Generic number type, either an integer or a floating-point number
#[derive(Debug, Clone, PartialEq)]
pub enum Number {
    Int(BigInt),
    Float {
        // Value of the number
        value: f64,
        // Span that caused the number to be casted to a float
        origin: Span,
    },
}

impl Number {
    /// Convines the origin spans of 2 numbers, assuming either one or both of them are floats
    ///
    /// # Panics
    ///
    /// Panics if both numbers are integers
    fn combine_origin(&self, rhs: &Self) -> Span {
        match (self, rhs) {
            (Self::Float { origin, .. }, _) | (_, Self::Float { origin, .. }) => *origin,
            _ => unreachable!("We shouldn't try to combine the origin spans of 2 integers"),
        }
    }
}

impl From<Number> for f64 {
    fn from(value: Number) -> Self {
        match value {
            Number::Int(x) => x.to_f64().expect("Converting a bigint to f64 can't fail"),
            Number::Float { value, .. } => value,
        }
    }
}

impl From<Number> for f32 {
    fn from(value: Number) -> Self {
        match value {
            Number::Int(x) => x.to_f32().expect("Converting a bigint to f32 can't fail"),
            #[allow(clippy::cast_possible_truncation)]
            Number::Float { value, .. } => value as Self,
        }
    }
}

/// Generates implementations of <code>[From]\<int></code> for [`Number`]
macro_rules! impl_from_int {
    ($($ty:ty),+) => {
        $(
            impl From<$ty> for Number {
                fn from(value: $ty) -> Self {
                    Self::Int(value.into())
                }
            }
        )+
    };
}
impl_from_int!(BigUint, BigInt, u32, i32);

impl From<Spanned<f64>> for Number {
    fn from(value: Spanned<f64>) -> Self {
        Self::Float {
            value: value.0,
            origin: value.1,
        }
    }
}

impl TryFrom<Number> for BigInt {
    type Error = ErrorKind;
    fn try_from(value: Number) -> Result<Self, Self::Error> {
        match value {
            Number::Int(x) => Ok(x),
            Number::Float { origin, .. } => Err(ErrorKind::UnallowedFloat(origin)),
        }
    }
}

impl TryFrom<Number> for BigUint {
    type Error = ErrorKind;
    fn try_from(value: Number) -> Result<Self, Self::Error> {
        match value {
            Number::Int(x) => {
                Self::try_from(x).map_err(|e| ErrorKind::UnallowedNegativeValue(e.into_original()))
            }
            Number::Float { origin, .. } => Err(ErrorKind::UnallowedFloat(origin)),
        }
    }
}

impl ops::Neg for Number {
    type Output = Self;

    fn neg(self) -> Self::Output {
        match self {
            Self::Int(value) => Self::Int(-value),
            Self::Float { value, origin } => Self::Float {
                origin,
                value: -value,
            },
        }
    }
}

impl ops::Not for Number {
    type Output = Result<Self, ErrorKind>;

    fn not(self) -> Self::Output {
        match self {
            Self::Int(value) => Ok(Self::Int(!value)),
            Self::Float { origin, .. } => Err(ErrorKind::UnallowedFloatOperation(
                OperationKind::Complement,
                origin,
            )),
        }
    }
}

/// Generates an implementation of a binary operation for [`Number`]
macro_rules! impl_bin_op {
    // Generic interface
    ($trait:path, $name:ident, ($lhs:ident, $rhs:ident), $int:expr, |$orig:ident| $float:expr, $out:ty$(: $wrap:ident)?) => {
        impl $trait for Number {
            type Output = $out;

            fn $name(self, rhs: Self) -> Self::Output {
                $($wrap)?(match (self, rhs) {
                    (Self::Int($lhs), Self::Int($rhs)) => Self::Int($int),
                    (lhs, rhs) => {
                        let $orig = lhs.combine_origin(&rhs);
                        let _value = match (f64::from(lhs), f64::from(rhs)) {
                            ($lhs, $rhs) => $float
                        };
                        #[allow(unreachable_code)]
                        Self::Float { origin: $orig, value: _value }
                    },
                })
            }
        }
    };
    // Convenience shorthands that forward the arguments to the generic interface
    // No possible errors, just forwards the numbers to the operator
    ($trait:path, $name:ident, $op:tt) => {
        impl_bin_op!($trait, $name, (lhs, rhs), lhs $op rhs, |origin| lhs $op rhs, Self);
    };
    // Integer implementation that can fail in a single way, result wrapped in an `Option`
    ($trait:path, $name:ident, ($lhs:ident, $rhs:ident), $int:expr, $float:expr) => {
        impl_bin_op!($trait, $name, ($lhs, $rhs), $int, |origin| $float, Option<Self>: Some);
    };
    // Implementation for bitwise operators that aren't allowed with floats, result wrapped in
    // `Result`
    ($trait:path, $name:ident, $int:tt, $float:expr) => {
        impl_bin_op!(
            $trait,
            $name,
            (_lhs, _rhs),
            _lhs $int _rhs,
            |origin| return Err(ErrorKind::UnallowedFloatOperation($float, origin)),
            Result<Self, ErrorKind>: Ok
        );
    };
}

impl_bin_op!(ops::Add, add, +);
impl_bin_op!(ops::Sub, sub, -);
impl_bin_op!(ops::Mul, mul, *);
impl_bin_op!(ops::Div, div, (lhs, rhs), lhs.checked_div(&rhs)?, lhs / rhs);
impl_bin_op!(
    ops::Rem,
    rem,
    (lhs, rhs),
    (rhs != BigInt::ZERO).then(|| lhs % rhs)?,
    lhs % rhs
);
impl_bin_op!(ops::BitOr, bitor, |, OperationKind::BitwiseOR);
impl_bin_op!(ops::BitAnd, bitand, &, OperationKind::BitwiseAND);
impl_bin_op!(ops::BitXor, bitxor, ^, OperationKind::BitwiseXOR);

#[cfg(test)]
mod test {
    use super::*;
    use crate::span::test::*;

    impl From<Ranged<f64>> for Number {
        fn from(value: Ranged<f64>) -> Self {
            Self::Float {
                value: value.0,
                origin: value.1.span(),
            }
        }
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn to_float() {
        assert_eq!(f64::from(Number::Int(123.into())), 123.0);
        assert_eq!(
            f64::from(Number::Float {
                value: 101.5,
                origin: (0..0).span()
            }),
            101.5
        );
        assert_eq!(f32::from(Number::Int(123.into())), 123.0);
        assert_eq!(
            f32::from(Number::Float {
                value: 101.5,
                origin: (0..0).span()
            }),
            101.5
        );
    }

    #[test]
    fn to_int() {
        assert_eq!(BigInt::try_from(Number::Int(123.into())), Ok(123.into()));
        assert_eq!(
            BigInt::try_from(Number::Float {
                value: 101.5,
                origin: (1..3).span()
            }),
            Err(ErrorKind::UnallowedFloat((1..3).span()))
        );
    }

    #[test]
    fn to_uint() {
        assert_eq!(BigUint::try_from(Number::Int(123.into())), Ok(123u8.into()));
        assert_eq!(
            BigUint::try_from(Number::Int((-123).into())),
            Err(ErrorKind::UnallowedNegativeValue((-123).into()))
        );
        assert_eq!(
            BigUint::try_from(Number::Float {
                value: 101.5,
                origin: (1..3).span()
            }),
            Err(ErrorKind::UnallowedFloat((1..3).span()))
        );
    }

    #[test]
    fn from_f64() {
        assert_eq!(
            Number::from((12.5, 1..4)),
            Number::Float {
                value: 12.5,
                origin: (1..4).span()
            }
        );
    }

    fn int() -> BigInt {
        BigInt::from(2u8).pow(128) - 1u8
    }

    #[test]
    fn neg() {
        assert_eq!(-Number::from(123), Number::from(-123));
        assert_eq!(-Number::from((1.5, 1..2)), Number::from((-1.5, 1..2)));
        assert_eq!(
            -Number::from(BigInt::from(2).pow(200)),
            Number::from(-BigInt::from(2).pow(200))
        );
    }

    #[test]
    fn not() {
        assert_eq!(!Number::from(123), Ok(Number::from(!123)));
        assert_eq!(!Number::from(-1), Ok(Number::from(0)));
        assert_eq!(!Number::from(0), Ok(Number::from(-1)));
        assert_eq!(
            !Number::from((1.5, 1..2)),
            Err(ErrorKind::UnallowedFloatOperation(
                OperationKind::Complement,
                (1..2).span()
            ))
        );
    }

    #[test]
    fn add() {
        let op = |a: &Number, b: &Number| a.clone() + b.clone();
        let opint = |a: BigInt, b: BigInt| op(&Number::from(a), &Number::from(b));
        let i1 = Number::from(123);
        let i2 = Number::from(-2);
        let f1 = Number::from((1.2, 1..3));
        let f2 = Number::from((2.5, 5..6));
        assert_eq!(op(&i1, &i2), Number::from(121));
        assert_eq!(op(&i1, &f2), Number::from((125.5, 5..6)));
        assert_eq!(op(&f1, &i2), Number::from((-0.8, 1..3)));
        assert_eq!(op(&f1, &f2), Number::from((3.7, 1..3)));
        assert_eq!(opint(int(), int() + 1), Number::from(2 * int() + 1));
    }

    #[test]
    fn sub() {
        let op = |a: &Number, b: &Number| a.clone() - b.clone();
        let opint = |a: BigInt, b: BigInt| op(&Number::from(a), &Number::from(b));
        let i1 = Number::from(123);
        let i2 = Number::from(-2);
        let f1 = Number::from((1.2, 1..3));
        let f2 = Number::from((2.5, 5..6));
        assert_eq!(op(&i1, &i2), Number::from(125));
        assert_eq!(op(&i1, &f2), Number::from((120.5, 5..6)));
        assert_eq!(op(&f1, &i2), Number::from((3.2, 1..3)));
        assert_eq!(op(&f1, &f2), Number::from((-1.3, 1..3)));
        assert_eq!(opint(int() + 10, int() - 2), Number::from(12));
        assert_eq!(opint(int(), int() + 10), Number::from(-10));
    }

    #[test]
    fn mul() {
        let op = |a: &Number, b: &Number| a.clone() * b.clone();
        let opint = |a: BigInt, b: BigInt| op(&Number::from(a), &Number::from(b));
        let i1 = Number::from(12);
        let i2 = Number::from(-2);
        let f1 = Number::from((1.2, 1..3));
        let f2 = Number::from((2.5, 5..6));
        assert_eq!(op(&i1, &i2), Number::from(-24));
        assert_eq!(op(&i1, &f2), Number::from((30.0, 5..6)));
        assert_eq!(op(&f1, &i2), Number::from((-2.4, 1..3)));
        assert_eq!(op(&f1, &f2), Number::from((3.0, 1..3)));
        assert_eq!(opint(int(), int()), Number::from(int() * int()));
    }

    #[test]
    fn div() {
        const INF: f64 = f64::INFINITY;
        let op = |a: &Number, b: &Number| a.clone() / b.clone();
        let opint = |a: BigInt, b: BigInt| op(&Number::from(a), &Number::from(b));
        let i1 = Number::from(9);
        let i2 = Number::from(-5);
        let i3 = Number::from(0);
        let f1 = Number::from((1.2, 1..3));
        let f2 = Number::from((-2.5, 5..6));
        let f3 = Number::from((0.0, 5..6));
        let f4 = Number::from((-0.0, 5..6));
        assert_eq!(op(&i1, &i2), Some(Number::from(-1)));
        assert_eq!(op(&i1, &f2), Some(Number::from((9.0 / -2.5, 5..6))));
        assert_eq!(op(&f1, &i2), Some(Number::from((1.2 / -5.0, 1..3))));
        assert_eq!(op(&f1, &f2), Some(Number::from((1.2 / -2.5, 1..3))));
        assert_eq!(opint(int(), int()), Some(Number::from(1)));

        assert_eq!(op(&i1, &i3), None);
        assert_eq!(op(&i1, &f3), Some(Number::from((INF, 5..6))));
        assert_eq!(op(&f1, &i3), Some(Number::from((INF, 1..3))));
        assert_eq!(op(&f1, &f3), Some(Number::from((INF, 1..3))));
        assert_eq!(op(&f2, &f4), Some(Number::from((INF, 5..6))));
        assert_eq!(op(&i2, &f3), Some(Number::from((-INF, 5..6))));
        assert_eq!(op(&f2, &i3), Some(Number::from((-INF, 5..6))));
        assert_eq!(op(&f1, &f4), Some(Number::from((-INF, 1..3))));
    }

    #[test]
    fn rem() {
        let op = |a: &Number, b: &Number| a.clone() % b.clone();
        let opint = |a: BigInt, b: BigInt| op(&Number::from(a), &Number::from(b));
        let i1 = Number::from(9);
        let i2 = Number::from(5);
        let i3 = Number::from(-5);
        let i4 = Number::from(0);
        let f1 = Number::from((1.2, 1..3));
        let f2 = Number::from((2.5, 5..6));
        let f3 = Number::from((-2.5, 5..6));
        let f4 = Number::from((0.0, 5..6));
        assert_eq!(op(&i1, &i2), Some(Number::from(4)));
        assert_eq!(op(&i1, &f2), Some(Number::from((9.0 % 2.5, 5..6))));
        assert_eq!(op(&f1, &i2), Some(Number::from((1.2 % 5.0, 1..3))));
        assert_eq!(op(&f1, &f2), Some(Number::from((1.2 % 2.5, 1..3))));
        assert_eq!(opint(2 * int() + 10, int() - 2), Some(Number::from(14)));

        assert_eq!(op(&i1, &i3), Some(Number::from(4)));
        assert_eq!(op(&i3, &i1), Some(Number::from(-5)));
        assert_eq!(op(&f1, &f3), Some(Number::from((1.2, 1..3))));
        assert_eq!(op(&f3, &f1), Some(Number::from((-2.5 % 1.2, 5..6))));

        assert_eq!(i1.clone() % i4.clone(), None);
        let test = |a: &Number, b: &Number| {
            op(a, b).is_some_and(|x| match x {
                Number::Float { value, .. } => value.is_nan(),
                Number::Int(_) => false,
            })
        };
        assert!(test(&i1, &f4));
        assert!(test(&f1, &i4));
        assert!(test(&f1, &f4));
    }

    #[test]
    fn bitor() {
        let op = |a: &Number, b: &Number| a.clone() | b.clone();
        let opint = |a: BigInt, b: BigInt| op(&Number::from(a), &Number::from(b));
        let i1 = Number::from(12);
        let i2 = Number::from(-2);
        let f1 = Number::from((1.2, 1..3));
        let f2 = Number::from((2.5, 5..6));
        let err = |s: Range| ErrorKind::UnallowedFloatOperation(OperationKind::BitwiseOR, s.span());
        assert_eq!(op(&i1, &i2), Ok(Number::from(12 | -2)));
        assert_eq!(op(&i1, &f2), Err(err(5..6)));
        assert_eq!(op(&f1, &i2), Err(err(1..3)));
        assert_eq!(op(&f1, &f2), Err(err(1..3)));
        assert_eq!(
            opint(
                BigInt::from(0xAAAA_AAAA_AAAA_AAAA_AAAB_u128),
                BigInt::from(0x5555_5555_5555_5555_5555_u128)
            ),
            Ok(Number::from(BigInt::from(0xFFFF_FFFF_FFFF_FFFF_FFFF_u128)))
        );
        assert_eq!(
            op(&Number::from(-1), &Number::from(123)),
            Ok(Number::from(-1))
        );
    }

    #[test]
    fn bitand() {
        let op = |a: &Number, b: &Number| a.clone() & b.clone();
        let opint = |a: BigInt, b: BigInt| op(&Number::from(a), &Number::from(b));
        let i1 = Number::from(12);
        let i2 = Number::from(-2);
        let f1 = Number::from((1.2, 1..3));
        let f2 = Number::from((2.5, 5..6));
        let err =
            |s: Range| ErrorKind::UnallowedFloatOperation(OperationKind::BitwiseAND, s.span());
        assert_eq!(op(&i1, &i2), Ok(Number::from(12 & -2)));
        assert_eq!(op(&i1, &f2), Err(err(5..6)));
        assert_eq!(op(&f1, &i2), Err(err(1..3)));
        assert_eq!(op(&f1, &f2), Err(err(1..3)));
        assert_eq!(
            opint(
                BigInt::from(0xAAAA_AAAA_AAAA_AAAA_AAAB_u128),
                BigInt::from(0x5555_5555_5555_5555_5555_u128)
            ),
            Ok(Number::from(1))
        );
        assert_eq!(
            opint(
                BigInt::from(0xAAAA_AAAA_AAAA_AAAA_AAAB_u128),
                BigInt::from(-1)
            ),
            Ok(Number::from(BigInt::from(0xAAAA_AAAA_AAAA_AAAA_AAAB_u128)))
        );
        assert_eq!(
            op(&Number::from(-1), &Number::from(-1)),
            Ok(Number::from(-1))
        );
    }

    #[test]
    fn bitxor() {
        let op = |a: &Number, b: &Number| a.clone() ^ b.clone();
        let opint = |a: BigInt, b: BigInt| op(&Number::from(a), &Number::from(b));
        let i1 = Number::from(12);
        let i2 = Number::from(-2);
        let f1 = Number::from((1.2, 1..3));
        let f2 = Number::from((2.5, 5..6));
        let err =
            |s: Range| ErrorKind::UnallowedFloatOperation(OperationKind::BitwiseXOR, s.span());
        assert_eq!(op(&i1, &i2), Ok(Number::from(12 ^ -2)));
        assert_eq!(op(&i1, &f2), Err(err(5..6)));
        assert_eq!(op(&f1, &i2), Err(err(1..3)));
        assert_eq!(op(&f1, &f2), Err(err(1..3)));
        assert_eq!(
            opint(
                BigInt::from(0xAAAA_AAAA_AAAA_AAAA_AAAB_u128),
                BigInt::from(0x5555_5555_5555_5555_5555_u128)
            ),
            Ok(Number::from(BigInt::from(0xFFFF_FFFF_FFFF_FFFF_FFFE_u128)))
        );
    }
}
