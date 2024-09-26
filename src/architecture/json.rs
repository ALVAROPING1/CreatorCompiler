use schemars::JsonSchema;
use serde::Deserialize;

use super::{utils, DataFormat, DirectiveAction};
use super::{FloatType, IntegerType, StringType};
use utils::{Bool, StringOrT};

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
        #[schemars(with = "utils::StringOrT<u8>")]
        #[serde(deserialize_with = "utils::from_str")]
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

impl<'a> TryFrom<[Config<'a>; 8]> for super::Config<'a> {
    type Error = &'static str;
    fn try_from(value: [Config<'a>; 8]) -> Result<Self, Self::Error> {
        macro_rules! unwrap_field {
            ($i:expr, $name:ident) => {
                match value[$i] {
                    Config::$name(x) => x.into(),
                    _ => {
                        return Err(concat!(
                            "unexpected key at index ",
                            stringify!($i),
                            ", expected key `",
                            stringify!($name),
                            "`"
                        ))
                    }
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
