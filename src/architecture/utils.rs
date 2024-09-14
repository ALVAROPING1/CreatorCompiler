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

#[derive(JsonSchema, Debug, PartialEq, Eq, Clone, Copy, PartialOrd, Ord)]
pub struct Hex(pub u64);

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

impl<'de> Deserialize<'de> for Hex {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let s: &str = Deserialize::deserialize(deserializer)?;
        u64::from_str_radix(s.trim_start_matches("0x"), 16)
            .map(Self)
            .map_err(serde::de::Error::custom)
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
