use once_cell::sync::Lazy;
use regex::{NoExpand, Regex};

use crate::architecture::{
    Architecture, ComponentType, DirectiveAction, Instruction as InstructionDefinition,
    InstructionFieldType,
};
use crate::parser::{
    parse_expr, parse_identifier, ASTNode, Argument, Data as DataToken, Spanned, Token,
};

mod label;
use label::{Label, Table as LabelTable};

mod error;
pub use error::{DirectiveArgumentType, Error as CompileError};

mod bit_field;
use bit_field::BitField;

mod section;
use section::Section;

mod integer;
pub use integer::{Integer, Type as IntegerType};

macro_rules! iter_captures {
    ($var:ident) => {
        $var.iter().skip(1).map(|cap| {
            cap.expect("This shouldn't fail because none of the captures are optional")
                .as_str()
        })
    };
}

/* TODO:
*  - Refactor code
*  - Remove uses of unwrap, propagating errors accordingly
*  - Combine `crate::parser::Error` with `crate::compiler::Error`
*  - Implement pseudoinstructions
*  - Add code spans to compile errors
*  - Rework argument number types
**/

static RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"[fF][0-9]+").expect("This shouldn't fail"));

fn parse_instruction<'a>(
    arch: &'a Architecture,
    name: &str,
    args: &Spanned<Vec<Token>>,
) -> Result<(&'a InstructionDefinition<'a>, Vec<Argument>), CompileError> {
    // TODO: reimplement with an actual parser for better errors

    // Format code as a string
    let mut code = format!("{name} ");
    let mut iter = args.0.iter().peekable();
    while let Some(token) = iter.next() {
        match (token, iter.peek()) {
            (Token::Ctrl(','), _) => continue,
            (tok, Some(&&Token::Ctrl(')') | &&Token::Literal('}' | ']')) | None)
            | (tok @ (Token::Ctrl('(') | Token::Literal('{' | '[')), _) => {
                code.push_str(&tok.to_string());
            }
            (tok, Some(_)) => code.push_str(&format!("{tok} ")),
        };
    }

    let mut found = false;
    for inst in arch.find_instructions(name) {
        found = true;
        let signature_definition = Regex::new(&format!(
            "^{}$",
            RE.replace_all(&regex::escape(inst.signature_definition), "(.*?)")
        ))
        .unwrap();
        let field_names = signature_definition.captures(inst.signature_raw).unwrap();
        let fields = signature_definition.captures(&code);
        if let Some(fields) = fields {
            let mut parsed_args = Vec::new();
            for (field_name, code) in iter_captures!(field_names).zip(iter_captures!(fields)) {
                let field = inst
                    .fields
                    .iter()
                    .find(|field| field.name == field_name)
                    .unwrap();
                // TODO: actually parse the arguments
                parsed_args.push(match field.r#type {
                    InstructionFieldType::Cop => {
                        panic!("This field type shouldn't be used for arguments")
                    }
                    InstructionFieldType::Co => Argument::Identifier(name.to_string()),
                    InstructionFieldType::Address
                    | InstructionFieldType::InmSigned
                    | InstructionFieldType::InmUnsigned
                    | InstructionFieldType::OffsetBytes
                    | InstructionFieldType::OffsetWords => parse_expr(code).unwrap(),
                    InstructionFieldType::IntReg
                    | InstructionFieldType::CtrlReg
                    | InstructionFieldType::SingleFPReg
                    | InstructionFieldType::DoubleFPReg => parse_identifier(code).unwrap(),
                });
            }
            return Ok((inst, parsed_args));
        }
    }
    Err(if found {
        CompileError::IncorrectInstructionSyntax(
            arch.find_instructions(name)
                .map(|inst| inst.signature_raw.to_string())
                .collect(),
        )
    } else {
        CompileError::UnknownInstruction(name.to_string())
    })
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Instruction {
    /// Address of the instruction
    pub address: u64,
    /// Labels pointing to this instruction
    pub labels: Vec<String>,
    /// Translated instruction to a simplified syntax
    pub loaded: String,
    /// Instruction encoded in binary
    pub binary: BitField,
    // /// Span of the instruction in the code
    // user: Span,
}

#[derive(Debug, PartialEq, Clone)]
pub enum Value {
    Integer(Integer),
    Space(u64),
    Padding(u64),
    Float(f32),
    Double(f64),
    String { data: String, null_terminated: bool },
}

#[derive(Debug, PartialEq, Clone)]
pub struct Data {
    /// Address of the value
    pub address: u64,
    /// Labels pointing to this data value
    pub labels: Vec<String>,
    /// Data value
    pub value: Value,
}

impl DataToken {
    fn into_string(self) -> Result<String, CompileError> {
        match self {
            Self::String(s) => Ok(s),
            Self::Number(_) => Err(CompileError::IncorrectDirectiveArgumentType {
                expected: DirectiveArgumentType::String,
                found: DirectiveArgumentType::Number,
            }),
        }
    }

    fn to_number(&self) -> Result<i32, CompileError> {
        match self {
            Self::Number(expr) => Ok(expr.value()),
            Self::String(_) => Err(CompileError::IncorrectDirectiveArgumentType {
                expected: DirectiveArgumentType::Number,
                found: DirectiveArgumentType::String,
            }),
        }
    }
}

#[allow(clippy::too_many_lines)]
pub fn compile(
    arch: &Architecture,
    ast: Vec<ASTNode>,
) -> Result<(LabelTable, Vec<Instruction>, Vec<Data>), CompileError> {
    // TODO: get spans for errors from parser
    let mut label_table = LabelTable::default();
    let mut code_section = Section::new("Instructions", arch.code_section_limits());
    let mut data_section = Section::new("Data", arch.data_section_limits());
    let word_size = arch.word_size() / 8;
    let mut parsed_instructions = Vec::new();
    let mut data_memory = Vec::new();
    let mut alignment: u32 = 1;

    for node in ast {
        match node {
            ASTNode::DataSegment(data) => {
                for mut data_node in data {
                    let directive = arch
                        .get_directive(&data_node.name)
                        .ok_or(CompileError::UnknownDirective(data_node.name))?;
                    match directive.action {
                        DirectiveAction::DataSegment
                        | DirectiveAction::CodeSegment
                        | DirectiveAction::GlobalSymbol => unreachable!(),
                        DirectiveAction::Balign | DirectiveAction::Align => {
                            if data_node.args.len() != 1 {
                                return Err(CompileError::IncorrectDirectiveArgumentNumber {
                                    expected: 1,
                                    found: data_node.args.len(),
                                });
                            };
                            let value = data_node.args[0].to_number()?;
                            let value = u32::try_from(value)
                                .map_err(|_| CompileError::UnallowedNegativeValue(value))?;
                            alignment = if directive.action == DirectiveAction::Align {
                                2_u32.pow(value)
                            } else {
                                value
                            };
                            continue;
                        }
                        _ => {}
                    }
                    if let Some((start, size)) = data_section.try_align(alignment.into())? {
                        data_memory.push(Data {
                            address: start,
                            labels: Vec::new(),
                            value: Value::Padding(size),
                        });
                    }
                    for label in &data_node.labels {
                        label_table.insert(label.to_owned(), Label::new(data_section.get()))?;
                    }
                    match directive.action {
                        DirectiveAction::DataSegment
                        | DirectiveAction::CodeSegment
                        | DirectiveAction::GlobalSymbol
                        | DirectiveAction::Balign
                        | DirectiveAction::Align => unreachable!(),
                        DirectiveAction::Space => {
                            if data_node.args.len() != 1 {
                                return Err(CompileError::IncorrectDirectiveArgumentNumber {
                                    expected: 1,
                                    found: data_node.args.len(),
                                });
                            };
                            let value = data_node.args[0].to_number()?;
                            let size = u64::try_from(value)
                                .map_err(|_| CompileError::UnallowedNegativeValue(value))?
                                * directive.size.unwrap().parse::<u64>().unwrap();
                            data_memory.push(Data {
                                address: data_section.try_reserve(size)?,
                                labels: data_node.labels,
                                value: Value::Space(size),
                            });
                        }
                        DirectiveAction::Byte
                        | DirectiveAction::HalfWord
                        | DirectiveAction::Word
                        | DirectiveAction::DoubleWord => {
                            #[allow(clippy::cast_sign_loss)]
                            let variant = match directive.action {
                                DirectiveAction::Byte => IntegerType::Byte,
                                DirectiveAction::HalfWord => IntegerType::HalfWord,
                                DirectiveAction::Word => IntegerType::Word,
                                DirectiveAction::DoubleWord => IntegerType::DoubleWord,
                                _ => unreachable!(),
                            };
                            let size = directive.size.unwrap().parse().unwrap();
                            for value in data_node.args {
                                let value = value.to_number()?;
                                data_memory.push(Data {
                                    address: data_section.try_reserve_aligned(size)?,
                                    labels: data_node.labels,
                                    value: Value::Integer(Integer::build(
                                        value.into(),
                                        (size * 8).try_into().unwrap(),
                                        Some(variant),
                                        None,
                                    )?),
                                });
                                data_node.labels = Vec::new();
                            }
                        }
                        DirectiveAction::Float | DirectiveAction::Double => {
                            todo!("Complete after float support is added")
                        }
                        DirectiveAction::AsciiNullEnd | DirectiveAction::AsciiNotNullEnd => {
                            for value in data_node.args {
                                let data = value.into_string()?;
                                let null_terminated =
                                    directive.action == DirectiveAction::AsciiNullEnd;

                                data_memory.push(Data {
                                    address: data_section.try_reserve(
                                        data.len() as u64 + u64::from(null_terminated),
                                    )?,
                                    labels: data_node.labels,
                                    value: Value::String {
                                        data,
                                        null_terminated,
                                    },
                                });
                                data_node.labels = Vec::new();
                            }
                        }
                    }
                    alignment = 1;
                }
            }
            ASTNode::CodeSegment(instructions) => {
                for instruction_node in instructions {
                    let (def, args) =
                        parse_instruction(arch, &instruction_node.name, &instruction_node.args)?;
                    let addr =
                        code_section.try_reserve(u64::from(word_size) * u64::from(def.nwords))?;
                    for label in &instruction_node.labels {
                        label_table.insert(label.clone(), Label::new(addr))?;
                    }
                    parsed_instructions.push((instruction_node.labels, addr, (def, args)));
                }
            }
        }
    }
    if label_table.get(arch.main_label()).is_none() {
        return Err(CompileError::MissingMainLabel(arch.main_label().to_owned()));
    }
    parsed_instructions
        .into_iter()
        .map(|(labels, address, (def, args))| {
            let mut binary_instruction =
                BitField::new(usize::from(word_size) * usize::from(def.nwords) * 8);
            let mut translated_instruction = def.signature_definition.to_string();
            let signature_definition = Regex::new(&format!(
                "^{}$",
                RE.replace_all(&regex::escape(def.signature_definition), "(.*?)")
            ))
            .unwrap();
            let field_names = signature_definition.captures(def.signature_raw).unwrap();
            for (field_name, value) in iter_captures!(field_names).zip(args.into_iter()) {
                let field = def
                    .fields
                    .iter()
                    .find(|field| field.name == field_name)
                    .unwrap();
                #[allow(clippy::cast_sign_loss)]
                let (value, value_str) = match field.r#type {
                    InstructionFieldType::Cop => {
                        panic!("This field type shouldn't be used for instruction arguments")
                    }
                    InstructionFieldType::Co => (
                        i64::from_str_radix(def.co, 2).unwrap(),
                        field_name.to_string(),
                    ),
                    val_type @ (InstructionFieldType::Address
                    | InstructionFieldType::InmSigned
                    | InstructionFieldType::InmUnsigned
                    | InstructionFieldType::OffsetBytes
                    | InstructionFieldType::OffsetWords) => {
                        let value = match value {
                            Argument::Number(expr) => expr.value(),
                            Argument::Identifier(label) => label_table
                                .get(&label)
                                .ok_or(CompileError::UnknownLabel(label))?
                                .address()
                                .try_into()
                                .unwrap(),
                        };
                        let value = match val_type {
                            InstructionFieldType::OffsetWords => {
                                (i64::from(value) - i64::try_from(address).unwrap())
                                    / (i64::from(word_size))
                                    - 1
                            }
                            InstructionFieldType::OffsetBytes => {
                                i64::from(value) - i64::try_from(address).unwrap()
                            }
                            _ => value.into(),
                        };
                        (value, value.to_string())
                    }
                    val_type @ (InstructionFieldType::IntReg
                    | InstructionFieldType::CtrlReg
                    | InstructionFieldType::SingleFPReg
                    | InstructionFieldType::DoubleFPReg) => {
                        let name = match value {
                            Argument::Number(_) => {
                                unreachable!("Register names are always parsed as identifiers")
                            }
                            Argument::Identifier(name) => name,
                        };
                        let bank_type = match val_type {
                            InstructionFieldType::IntReg => ComponentType::Int,
                            InstructionFieldType::CtrlReg => ComponentType::Ctrl,
                            InstructionFieldType::SingleFPReg
                            | InstructionFieldType::DoubleFPReg => ComponentType::Float,
                            _ => unreachable!("We already matched one of these variants"),
                        };
                        let bank = arch
                            .find_bank(bank_type, val_type == InstructionFieldType::DoubleFPReg)
                            .ok_or(CompileError::UnknownRegisterBank(bank_type))?;
                        let (i, _) = bank.find_register(&name).ok_or_else(|| {
                            CompileError::UnknownRegister {
                                name: name.clone(),
                                bank: bank_type,
                            }
                        })?;
                        (i64::try_from(i).unwrap(), name)
                    }
                };
                binary_instruction.replace(
                    &field.startbit,
                    &field.stopbit,
                    value,
                    matches!(
                        field.r#type,
                        InstructionFieldType::InmSigned
                            | InstructionFieldType::OffsetBytes
                            | InstructionFieldType::OffsetWords
                    ),
                )?;
                translated_instruction = RE
                    .replace(&translated_instruction, NoExpand(&value_str))
                    .to_string();
                for field in def
                    .fields
                    .iter()
                    .filter(|field| field.r#type == InstructionFieldType::Cop)
                {
                    binary_instruction.replace(
                        &field.startbit,
                        &field.stopbit,
                        i64::from_str_radix(field.value_field.unwrap(), 2).unwrap(),
                        false,
                    )?;
                }
            }
            Ok(Instruction {
                labels,
                address,
                binary: binary_instruction,
                loaded: translated_instruction,
            })
        })
        .collect::<Result<Vec<_>, _>>()
        .map(|instructions| (label_table, instructions, data_memory))
}
