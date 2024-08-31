use std::ops::Range;

use crate::architecture::ComponentType;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DirectiveArgumentType {
    String,
    Number,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    UnknownDirective(String),
    UnknownInstruction(String),
    UnknownLabel(String),
    UnknownRegisterBank(ComponentType),
    UnknownRegister {
        name: String,
        bank: ComponentType,
    },
    IncorrectInstructionSyntax(Vec<String>),
    DuplicateLabel(String),
    MissingMainLabel(String),
    IntegerTooBig(i64, Range<i64>),
    MemorySectionFull(&'static str),
    DataUnaligned {
        address: u64,
        alignment: u64,
    },
    UnallowedNegativeValue(i32),
    IncorrectDirectiveArgumentNumber {
        expected: u8,
        found: usize,
    },
    IncorrectDirectiveArgumentType {
        expected: DirectiveArgumentType,
        found: DirectiveArgumentType,
    },
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::UnknownDirective(s) => write!(f, "Directive \"{s}\" isn't defined"),
            Self::UnknownInstruction(s) => write!(f, "Instruction \"{s}\" isn't defined"),
            Self::UnknownLabel(s) => write!(f, "Label \"{s}\" isn't defined"),
            Self::UnknownRegisterBank(s) => write!(f, "Register bank \"{s:?}\" isn't defined"),
            Self::UnknownRegister { name, bank } => {
                write!(f, "Register \"{name}\" isn't defined in bank type {bank:?}")
            }
            Self::IncorrectInstructionSyntax(syntaxes) => {
                write!(f, "Incorrect instruction syntax. Allowed formats:")?;
                for syntax in syntaxes {
                    write!(f, "\n{syntax}")?;
                }
                Ok(())
            }
            Self::DuplicateLabel(s) => write!(f, "Label \"{s}\" is already defined"),
            Self::MissingMainLabel(s) => write!(f, "Label \"{s}\" not found"),
            Self::IntegerTooBig(val, bounds) => write!(
                f,
                "Field is too small to contain value \"{val}\" (Allowed range: [{}, {}])",
                bounds.start,
                bounds.end - 1
            ),
            Self::MemorySectionFull(name) => write!(f, "{name} memory segment is full"),
            Self::DataUnaligned { address, alignment } => write!(
                f,
                "Data at address {address:#X} isn't aligned to size {alignment}"
            ),
            Self::UnallowedNegativeValue(x) => {
                write!(f, "Negative values aren't allowed (Found: {x})")
            }
            Self::IncorrectDirectiveArgumentNumber { expected, found } => write!(
                f,
                "Incorrect amount of arguments, expected {expected} but found {found}"
            ),
            Self::IncorrectDirectiveArgumentType { expected, found } => write!(
                f,
                "Incorrect argument type, expected \"{expected:?}\" but found \"{found:?}\""
            ),
        }
    }
}
