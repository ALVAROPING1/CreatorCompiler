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

//! Module containing general utilities for deserialization of different types of values

use num_bigint::BigUint;
use num_traits::{Num as _, One as _};
use schemars::JsonSchema;
use serde::{de::Error, Deserialize, Deserializer};

use core::{fmt::Display, str::FromStr};

/// Thin wrapper for big integers that can be deserialized from JSON, either from a JSON integer or
/// a string representing an integer
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct Integer(pub BigUint);

impl JsonSchema for Integer {
    fn is_referenceable() -> bool {
        false
    }
    fn schema_name() -> String {
        "Integer".to_owned()
    }
    fn schema_id() -> std::borrow::Cow<'static, str> {
        std::borrow::Cow::Borrowed("Integer")
    }
    fn json_schema(_: &mut schemars::gen::SchemaGenerator) -> schemars::schema::Schema {
        schemars::schema::SchemaObject {
            instance_type: Some(schemars::schema::InstanceType::Integer.into()),
            ..Default::default()
        }
        .into()
    }
}

impl FromStr for Integer {
    type Err = <BigUint as FromStr>::Err;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self(s.parse()?))
    }
}

/// Wrapper for integers that can be deserialized from a string representing an integer in base N
#[derive(Debug, PartialEq, Eq, Clone, PartialOrd, Ord, JsonSchema)]
pub struct BaseN<const N: u8>(#[schemars(with = "String")] pub BigUint);

/// A key-value pair
#[derive(Deserialize, JsonSchema, Debug, PartialEq, Eq, Clone, Copy)]
pub struct Pair<Keys, Value> {
    pub name: Keys,
    pub value: Value,
}

/// A value optionally stored as a string
#[derive(Deserialize, JsonSchema)]
#[serde(untagged)]
pub enum StringOrT<'a, T> {
    String(&'a str),
    T(T),
}

impl<'de> Deserialize<'de> for Integer {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let s = serde_json::Number::deserialize(deserializer)?;
        Ok(Self(s.as_str().parse().map_err(Error::custom)?))
    }
}

impl<'de, const N: u8> Deserialize<'de> for BaseN<N> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let s: &str = Deserialize::deserialize(deserializer)?;
        BigUint::from_str_radix(s.trim_start_matches("0x"), N.into())
            .map(Self)
            .map_err(Error::custom)
    }
}

/// Deserialization function for a value serialized either as a string or as the value itself
pub fn from_str<'de, T, D>(deserializer: D) -> Result<T, D::Error>
where
    D: Deserializer<'de>,
    T: FromStr + Deserialize<'de>,
    <T as FromStr>::Err: Display,
{
    match Deserialize::deserialize(deserializer)? {
        StringOrT::T(i) => Ok(i),
        StringOrT::String(s) => s.parse::<T>().map_err(Error::custom),
    }
}

/// Deserialization function for an optional value serialized either as a string or as the value
/// itself
pub fn optional_from_str<'de, T, D>(deserializer: D) -> Result<Option<T>, D::Error>
where
    D: Deserializer<'de>,
    T: FromStr + Deserialize<'de>,
    <T as FromStr>::Err: Display,
{
    match Deserialize::deserialize(deserializer)? {
        None => Ok(None),
        Some(StringOrT::T(i)) => Ok(Some(i)),
        Some(StringOrT::String(s)) => s.parse::<T>().map(Some).map_err(serde::de::Error::custom),
    }
}

/// A boolean value serialized as a string of a 0/1
#[derive(Deserialize, JsonSchema, Debug, PartialEq, Eq, Clone, Copy)]
pub enum Bool {
    #[serde(rename = "1")]
    True,
    #[serde(rename = "0")]
    False,
}

impl From<Bool> for bool {
    fn from(value: Bool) -> Self {
        match value {
            Bool::True => true,
            Bool::False => false,
        }
    }
}

/// Inclusive range guaranteed to be non-empty
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct NonEmptyRangeInclusive<Idx> {
    /// Start of the range
    start: Idx,
    /// Size of the range
    size: Idx,
}

/// Macro to generate methods for non-empty ranges, taking as input the list of concrete types to
/// be used as the generic type parameter
macro_rules! impl_NonEmptyRangeInclusive {
    ($($ty:ty),+) => {
        $(
            impl NonEmptyRangeInclusive<$ty> {
                /// Creates a new [`NonEmptyRangeInclusive`]
                ///
                /// # Parameters
                ///
                /// * `start`: starting value of the range (inclusive)
                /// * `end`: ending value of the range (inclusive)
                #[must_use]
                pub fn build(start: $ty, end: $ty) -> Option<Self> {
                    if start > end {
                        return None;
                    }
                    let size = end - (&start) + <$ty>::one();
                    Some(Self { start, size })
                }

                /// Get the starting value of the range
                #[must_use]
                pub const fn start(&self) -> &$ty {
                    &self.start
                }

                /// Get the size of the range
                #[must_use]
                pub const fn size(&self) -> &$ty {
                    &self.size
                }

                /// Get the ending value of the range
                #[must_use]
                pub fn end(&self) -> $ty {
                    &self.start + &self.size - <$ty>::one()
                }

                /// Check if a value is contained in this range
                #[must_use]
                pub fn contains(&self, x: &$ty) -> bool {
                    *x >= self.start && x - (&self.start) < self.size
                }
            }
        )+
    };
}

impl_NonEmptyRangeInclusive!(BigUint, usize);

/// Exclusive non-empty range with a possibly unbound end
#[derive(Deserialize, Debug, PartialEq, Eq, Clone, Copy)]
#[serde(try_from = "(u64, Option<u64>)")]
pub struct RangeFrom {
    /// Start of the range
    pub start: u64,
    /// End of the range
    pub size: Option<u64>,
}
schema_from!(RangeFrom, (u64, Option<u64>));

impl TryFrom<(u64, Option<u64>)> for RangeFrom {
    type Error = &'static str;

    fn try_from((start, end): (u64, Option<u64>)) -> Result<Self, Self::Error> {
        let size = match end.map(|end| end.checked_sub(start)) {
            Some(None) => return Err("the range end must be bigger than the start"),
            Some(Some(x)) => Some(x),
            None => None,
        };
        Ok(Self { start, size })
    }
}

/// Derive implementation of [`JsonSchema`] from the implementation of a different type
macro_rules! schema_from {
    ($dst:ident$(<$($lt:lifetime)? $($(,)? $t:ident)?>)?, $src:ty) => {
        impl $(<$($lt)? $(, $t: JsonSchema)?>)? JsonSchema for $dst$(<$($lt)? $(, $t)?>)? {
            fn schema_name() -> String {
                <$src as JsonSchema>::schema_name()
            }

            fn schema_id() -> std::borrow::Cow<'static, str> {
                <$src as JsonSchema>::schema_id()
            }

            fn json_schema(gen: &mut schemars::gen::SchemaGenerator) -> schemars::schema::Schema {
                <$src as JsonSchema>::json_schema(gen)
            }

            fn is_referenceable() -> bool {
                <$src as JsonSchema>::is_referenceable()
            }
        }
    };
}
pub(super) use schema_from;
