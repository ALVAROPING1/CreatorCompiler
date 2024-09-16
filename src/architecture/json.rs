use schemars::JsonSchema;
use serde::Deserialize;

use super::{utils, utils::StringOrT, DirectiveAction};
use super::{FloatType, IntegerType, StringType};

/// Directive specification
#[derive(Deserialize, JsonSchema, Debug, PartialEq, Eq, Clone, Copy)]
pub struct Directive<'a> {
    /// Name of the directive
    pub name: &'a str,
    /// Action of the directive
    pub action: DirectiveAction<DirectiveData>,
    /// Size in bytes of values associated with this directive
    #[serde(deserialize_with = "utils::optional_from_str")]
    #[schemars(with = "Option<StringOrT<u8>>")]
    pub size: Option<u8>,
}

/// Data segment types
#[derive(Deserialize, JsonSchema, Debug, PartialEq, Eq, Clone, Copy)]
#[serde(untagged)]
pub enum DirectiveData {
    /// Store n * size null bytes in the data segment
    Space(Space),
    /// Store string
    String(StringType),
    /// Store integer
    Int(IntegerType),
    /// Store floating point value
    Float(FloatType),
}

/// Store n * size null bytes in the data segment
#[derive(Deserialize, JsonSchema, Debug, PartialEq, Eq, Clone, Copy)]
#[serde(rename_all = "snake_case")]
pub enum Space {
    Space,
}

impl<'a> TryFrom<Directive<'a>> for super::Directive<'a> {
    type Error = &'static str;

    fn try_from(value: Directive<'a>) -> Result<Self, Self::Error> {
        use super::DirectiveData as SDD;
        use DirectiveData as DD;

        let size = value.size.ok_or("missing required size field value");
        Ok(Self {
            name: value.name,
            action: match value.action {
                DirectiveAction::Data(data_type) => DirectiveAction::Data(match data_type {
                    DD::Space(_) => SDD::Space(size?),
                    DD::Int(x) => SDD::Int(size?, x),
                    DD::Float(x) => SDD::Float(x),
                    DD::String(x) => SDD::String(x),
                }),
                DirectiveAction::Alignment(x) => DirectiveAction::Alignment(x),
                DirectiveAction::Segment(x) => DirectiveAction::Segment(x),
                DirectiveAction::GlobalSymbol(x) => DirectiveAction::GlobalSymbol(x),
            },
        })
    }
}

/// Range of bits of a field in a binary instruction
#[derive(Deserialize, JsonSchema, Debug, PartialEq, Eq, Clone)]
pub struct BitRange {
    /// Starting position of the field. Ignored for pseudoinstructions
    pub startbit: BitPosition,
    /// End position of the field. Ignored for pseudoinstructions
    pub stopbit: BitPosition,
}

/// Position of the start/end bit of a field in a binary instruction
#[derive(Deserialize, JsonSchema, Debug, PartialEq, Eq, Clone)]
#[serde(untagged)]
pub enum BitPosition {
    // Field uses a single, contiguous bit range
    Single(u8),
    // Field uses multiple, discontiguous bit ranges
    Multiple(Vec<u8>),
}

impl TryFrom<BitRange> for super::BitRange {
    type Error = &'static str;

    fn try_from(value: BitRange) -> Result<Self, Self::Error> {
        Ok(Self::new(match (value.startbit, value.stopbit) {
            (BitPosition::Single(start), BitPosition::Single(end)) => vec![(start, end)],
            (BitPosition::Multiple(start), BitPosition::Multiple(end)) => {
                if start.len() != end.len() {
                    return Err("the startbit and endbit fields must have the same length if they are vectors");
                }
                if start.is_empty() {
                    return Err(
                        "the startbit and endbit fields must not be empty if they are vectors",
                    );
                }
                std::iter::zip(start, end).collect()
            }
            _ => return Err("the type of the startbit and endbit fields should be the same"),
        }))
    }
}
