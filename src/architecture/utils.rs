use schemars::JsonSchema;
use serde::{Deserialize, Deserializer};

use core::{fmt::Display, str::FromStr};

pub type Integer = i64;

#[derive(Deserialize, JsonSchema, Debug, PartialEq, Clone, Copy, PartialOrd)]
#[serde(untagged)]
pub enum Number {
    Int(Integer),
    Float(f64),
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, PartialOrd, Ord)]
pub struct BaseN<const N: u8>(pub u64);

#[derive(Deserialize, JsonSchema)]
#[serde(untagged)]
pub enum StringOrT<'a, T> {
    String(&'a str),
    T(T),
}

#[derive(Deserialize, JsonSchema, Debug, PartialEq, Eq, Clone, Copy)]
pub struct Pair<Keys, Value> {
    pub name: Keys,
    pub value: Value,
}

impl<'de, const N: u8> Deserialize<'de> for BaseN<N> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let s: &str = Deserialize::deserialize(deserializer)?;
        u64::from_str_radix(s.trim_start_matches("0x"), N.into())
            .map(Self)
            .map_err(serde::de::Error::custom)
    }
}

pub fn from_str<'de, T, D>(deserializer: D) -> Result<T, D::Error>
where
    D: Deserializer<'de>,
    T: FromStr + Deserialize<'de>,
    <T as FromStr>::Err: Display,
{
    match Deserialize::deserialize(deserializer)? {
        StringOrT::T(i) => Ok(i),
        StringOrT::String(s) => s.parse::<T>().map_err(serde::de::Error::custom),
    }
}

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
pub struct NonEmptyRangeInclusive<Idx, NonZeroIdx> {
    start: Idx,
    size: NonZeroIdx,
}

macro_rules! impl_NonEmptyRangeInclusive {
    ($(($ty:ty, $name:ident)),+) => {
        $(
            impl NonEmptyRangeInclusive<$ty, std::num::NonZero<$ty>> {
                pub fn build(start: $ty, end: $ty) -> Option<Self> {
                    let size = end.checked_sub(start)? + 1;
                    Some(Self { start, size: std::num::NonZero::new(size)? })
                }

                pub const fn start(&self) -> $ty {
                    self.start
                }

                pub const fn size(&self) -> std::num::NonZero<$ty> {
                    self.size
                }

                pub const fn end(&self) -> $ty {
                    self.start + self.size.get() - 1
                }

                pub const fn contains(&self, x: $ty) -> bool {
                    if let Some(x) = x.checked_sub(self.start) {
                        x < self.size.get()
                    } else {
                        false
                    }
                }
            }

            pub type $name = NonEmptyRangeInclusive<$ty, std::num::NonZero<$ty>>;
        )+
    };
}

impl_NonEmptyRangeInclusive!(
    (u64, NonEmptyRangeInclusiveU64),
    (u8, NonEmptyRangeInclusiveU8)
);
