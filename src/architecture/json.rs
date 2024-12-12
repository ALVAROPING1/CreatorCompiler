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

//! Module containing conversion methods between the format used by the architecture JSON
//! specification and our internal representation

use schemars::JsonSchema;
use serde::Deserialize;

use super::{utils, DataFormat, DirectiveAction};
use super::{AlignmentType, FloatType, IntegerType, StringType};
use utils::{BaseN, Bool, NonEmptyRangeInclusiveU64, NonEmptyRangeInclusiveU8, Pair, StringOrT};

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
    /// Align the next data value to a given size
    Alignment(AlignmentType),
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
                    DD::Alignment(x) => SDD::Alignment(x),
                }),
                DirectiveAction::Segment(x) => DirectiveAction::Segment(x),
                DirectiveAction::GlobalSymbol(x) => DirectiveAction::GlobalSymbol(x),
                DirectiveAction::Nop(x) => DirectiveAction::Nop(x),
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
        let range =
            |(msb, lsb)| NonEmptyRangeInclusiveU8::build(lsb, msb).ok_or("invalid empty range");
        Self::build(match (value.startbit, value.stopbit) {
            (BitPosition::Single(msb), BitPosition::Single(lsb)) => vec![range((msb, lsb))?],
            (BitPosition::Multiple(msb), BitPosition::Multiple(lsb)) => {
                if msb.len() != lsb.len() {
                    return Err("the startbit and endbit fields must have the same length if they are vectors");
                }
                std::iter::zip(msb, lsb)
                    .map(range)
                    .collect::<Result<_, _>>()?
            }
            _ => return Err("the type of the startbit and endbit fields should be the same"),
        }).ok_or("the startbit and endbit fields must not be empty if they are vectors")
    }
}

/// Instruction syntax specification
#[derive(Deserialize, JsonSchema, Debug, PartialEq, Eq, Clone)]
pub struct InstructionSyntax<'a, BitRange> {
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
    pub fields: Vec<super::InstructionField<'a, BitRange>>,
}

impl<'a, T> TryFrom<InstructionSyntax<'a, T>> for super::InstructionSyntax<'a, T> {
    type Error = &'static str;

    fn try_from(value: InstructionSyntax<'a, T>) -> Result<Self, Self::Error> {
        let format = |fmt: &str| {
            let fmt = fmt.replace(" (", "(");
            fmt.split_once(' ')
                .map(|(opcode, syntax)| format!("{opcode} {}", syntax.replace(' ', ",")))
                .unwrap_or(fmt)
        };
        let parser =
            crate::parser::Instruction::build(&format(value.signature_definition), &value.fields)?;
        Ok(Self {
            parser,
            output_syntax: value.signature_definition,
            user_syntax: format(value.signature_raw),
            fields: value.fields,
        })
    }
}

/// Architecture metadata attributes
#[derive(Deserialize, JsonSchema, Debug, PartialEq, Eq, Clone, Copy)]
#[serde(tag = "name", content = "value")]
pub enum Config<'a> {
    /// Name of the architecture
    Name(&'a str),
    /// Word size
    Bits(
        #[serde(deserialize_with = "utils::from_str")]
        #[schemars(with = "utils::StringOrT<u8>")]
        u8,
    ),
    /// Description of the architecture
    Description(&'a str),
    /// Storage format of the architecture (big/little endian)
    #[serde(rename = "Data Format")]
    DataFormat(DataFormat),
    /// Whether to enable memory alignment
    #[serde(rename = "Memory Alignment")]
    MemoryAlignment(Bool),
    /// Name of the `main` function of the program
    #[serde(rename = "Main Function")]
    MainFunction(&'a str),
    /// Whether to enable function parameter passing convention checks
    #[serde(rename = "Passing Convention")]
    PassingConvention(Bool),
    /// TODO: what does this represent? is this used currently?
    #[serde(rename = "Sensitive Register Name")]
    SensitiveRegisterName(Bool),
}

macro_rules! key_error {
    ($i:expr, $name:ident) => {
        return Err(concat!(
            "unexpected key at index ",
            stringify!($i),
            ", expected key `",
            stringify!($name),
            "`"
        ))
    };
}

impl<'a> TryFrom<[Config<'a>; 8]> for super::Config<'a> {
    type Error = &'static str;
    fn try_from(value: [Config<'a>; 8]) -> Result<Self, Self::Error> {
        macro_rules! unwrap_field {
            ($i:expr, $name:ident) => {
                match value[$i] {
                    Config::$name(x) => x.into(),
                    _ => key_error!($i, $name),
                }
            };
        }
        Ok(Self {
            name: unwrap_field!(0, Name),
            word_size: unwrap_field!(1, Bits),
            description: unwrap_field!(2, Description),
            data_format: unwrap_field!(3, DataFormat),
            memory_alignment: unwrap_field!(4, MemoryAlignment),
            main_function: unwrap_field!(5, MainFunction),
            passing_convention: unwrap_field!(6, PassingConvention),
            sensitive_register_name: unwrap_field!(7, SensitiveRegisterName),
        })
    }
}

/// Memory layout attribute keys
#[derive(Deserialize, JsonSchema, Debug, PartialEq, Eq, Clone, Copy)]
pub enum MemoryLayoutKeys {
    #[serde(rename = "text start")]
    TextStart,
    #[serde(rename = "text end")]
    TextEnd,
    #[serde(rename = "data start")]
    DataStart,
    #[serde(rename = "data end")]
    DataEnd,
    #[serde(rename = "stack start")]
    StackStart,
    #[serde(rename = "stack end")]
    StackEnd,
}

impl TryFrom<[Pair<MemoryLayoutKeys, BaseN<16>>; 6]> for super::MemoryLayout {
    type Error = &'static str;
    fn try_from(value: [Pair<MemoryLayoutKeys, BaseN<16>>; 6]) -> Result<Self, Self::Error> {
        macro_rules! unwrap_field {
            ($i:expr, $name:ident) => {
                match value[$i].name {
                    MemoryLayoutKeys::$name => value[$i].value.0,
                    _ => key_error!($i, $name),
                }
            };
        }
        macro_rules! check_overlap {
            ($a:ident, $b:ident) => {
                if ($a.contains($b.start()) || $b.contains($a.start())) {
                    return Err(concat!(
                        "section `",
                        stringify!($a),
                        "` overlaps with section `",
                        stringify!($b),
                        "`"
                    ));
                }
            };
        }
        let text = (unwrap_field!(0, TextStart), unwrap_field!(1, TextEnd));
        let data = (unwrap_field!(2, DataStart), unwrap_field!(3, DataEnd));
        let stack = (unwrap_field!(4, StackStart), unwrap_field!(5, StackEnd));
        let text =
            NonEmptyRangeInclusiveU64::build(text.0, text.1).ok_or("section `text` is empty")?;
        let data =
            NonEmptyRangeInclusiveU64::build(data.0, data.1).ok_or("section `data` is empty")?;
        let stack =
            NonEmptyRangeInclusiveU64::build(stack.0, stack.1).ok_or("section `stack` is empty")?;
        check_overlap!(text, data);
        check_overlap!(text, stack);
        check_overlap!(data, stack);
        Ok(Self { text, data, stack })
    }
}
