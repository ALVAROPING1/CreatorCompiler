use schemars::JsonSchema;
use serde::Deserialize;

use once_cell::sync::Lazy;
use regex::Regex;

use super::{utils, utils::StringOrT, DirectiveAction, InstructionFieldType};
use super::{FloatType, IntegerType, StringType};
use crate::parser::InstructionParser;

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

/// Instruction syntax specification
#[derive(Deserialize, JsonSchema, Debug, PartialEq, Eq, Clone)]
pub struct InstructionSyntax<'a> {
    /// Order of the fields/literal characters in the instruction text. `[fF]\d+` is interpreted as
    /// the field with index i of the instruction. Other characters are interpreted literally
    /// Ex: `F0 F3 F1 (F2)`
    pub signature_definition: &'a str,
    /// `signature_definition` in which `[fF]\d+` has been replaced with the type of each field in
    /// the instruction. Valid values are those in `InstructionFieldType`, except `Co` and `Cop`.
    /// The instruction opcode is replaced with its name. Spaces must also be replaced with `,`
    pub signature: &'a str,
    /// Same as `signature`, but replacing `[fF]\d+` with the field names
    #[serde(rename = "signatureRaw")]
    pub signature_raw: &'a str,
    /// Parameters of the instruction
    #[schemars(with = "Vec<super::InstructionField<BitRange>>")]
    pub fields: Vec<super::InstructionField<'a, super::BitRange>>,
}

impl<'a> TryFrom<InstructionSyntax<'a>> for super::InstructionSyntax<'a> {
    type Error = &'static str;

    fn try_from(value: InstructionSyntax<'a>) -> Result<Self, Self::Error> {
        static RE: Lazy<Regex> =
            Lazy::new(|| Regex::new(r"[fF][0-9]+").expect("This shouldn't fail"));
        let format = |fmt: &str| fmt.replace(" (", "(").replace(' ', ",");
        let parser = InstructionParser::build(&format(
            value
                .signature_definition
                // Remove opcode field
                .trim_start_matches(|c| c != ' ')
                .trim_start_matches(' '),
        ))
        .map_err(|_| "incorrect `signature_definition` field specification")?;
        let fields = RE
            .find_iter(value.signature_definition)
            .map(|res| {
                let i: usize = res.as_str()[1..]
                    .parse()
                    .expect("This shouldn't fail because we already matched a sequence of digits");
                value
                    .fields
                    .get(i)
                    .cloned()
                    .ok_or("`signature_definition` referenced an undefined field")
            })
            .chain(
                value
                    .fields
                    .iter()
                    .filter(|field| matches!(field.r#type, InstructionFieldType::Cop { .. }))
                    .cloned()
                    .map(Ok),
            )
            .collect::<Result<Vec<_>, _>>()?;

        Ok(Self {
            parser,
            output_syntax: value.signature_definition,
            user_syntax: format(value.signature_raw),
            fields,
        })
    }
}
