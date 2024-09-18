use once_cell::sync::Lazy;
use regex::{NoExpand, Regex};

use crate::architecture::{
    Architecture, ComponentType, DirectiveAction, DirectiveAlignment, DirectiveData, FloatType,
    Instruction as InstructionDefinition, InstructionFieldType, StringType,
};
use crate::parser::{
    parse_inst_args, ASTNode, Argument, Data as DataToken, Expr, Span, Spanned, Token,
};

mod label;
use label::{Label, Table as LabelTable};

mod error;
pub use error::{ArgumentType, Error as CompileError, Kind as ErrorKind, OperationKind};

mod bit_field;
use bit_field::BitField;

mod section;
use section::Section;

mod integer;
pub use integer::Integer;

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
*  - Rework argument number types
**/

static RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"[fF][0-9]+").expect("This shouldn't fail"));

fn parse_instruction<'a>(
    arch: &'a Architecture,
    (name, name_span): Spanned<&str>,
    args: Spanned<Vec<Spanned<Token>>>,
) -> Result<(&'a InstructionDefinition<'a>, Vec<Spanned<Argument>>), CompileError> {
    let mut errs = Vec::new();
    for inst in arch.find_instructions(name) {
        let result = parse_inst_args(
            inst.signature_definition
                .trim_start_matches(|c| c != ' ')
                .trim_start_matches(' '),
            args.clone(),
        );
        match result {
            Ok(parsed_args) => return Ok((inst, parsed_args)),
            Err(e) => errs.push((inst.signature_raw.to_string(), e)),
        }
    }
    Err(if errs.is_empty() {
        ErrorKind::UnknownInstruction(name.to_string()).add_span(name_span)
    } else {
        ErrorKind::IncorrectInstructionSyntax(errs).add_span(args.1)
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
    fn into_string(self, span: Span) -> Result<String, CompileError> {
        match self {
            Self::String(s) => Ok(s),
            Self::Number(_) => Err(ErrorKind::IncorrectArgumentType {
                expected: ArgumentType::String,
                found: ArgumentType::Expression,
            }
            .add_span(span)),
        }
    }

    const fn to_expr(&self, span: Span) -> Result<&Expr, CompileError> {
        match self {
            Self::Number(expr) => Ok(expr),
            Self::String(_) => Err(ErrorKind::IncorrectArgumentType {
                expected: ArgumentType::Expression,
                found: ArgumentType::String,
            }
            .add_span(span)),
        }
    }
}

#[allow(clippy::too_many_lines)]
pub fn compile(
    arch: &Architecture,
    ast: Vec<ASTNode>,
) -> Result<(LabelTable, Vec<Instruction>, Vec<Data>), CompileError> {
    let mut label_table = LabelTable::default();
    let mut code_section = Section::new("Instructions", arch.code_section_limits());
    let mut data_section = Section::new("Data", arch.data_section_limits());
    let word_size = arch.word_size() / 8;
    let mut parsed_instructions = Vec::new();
    let mut data_memory = Vec::new();
    let mut alignment: Option<Spanned<u64>> = None;

    for node in ast {
        match node {
            ASTNode::DataSegment(data) => {
                for mut data_node in data {
                    let action = arch.find_directive(&data_node.name.0).ok_or_else(|| {
                        ErrorKind::UnknownDirective(data_node.name.0)
                            .add_span(data_node.name.1.clone())
                    })?;
                    match action {
                        DirectiveAction::Segment(_) | DirectiveAction::GlobalSymbol(_) => {
                            unreachable!()
                        }
                        DirectiveAction::Alignment(align_type) => {
                            let (args, span) = data_node.args;
                            if args.len() != 1 {
                                return Err(ErrorKind::IncorrectDirectiveArgumentNumber {
                                    expected: 1,
                                    found: args.len(),
                                }
                                .add_span(span));
                            };
                            let (value, span) = &args[0];
                            let value = value.to_expr(span.clone())?.int()?;
                            let value = u32::try_from(value).map_err(|_| {
                                ErrorKind::UnallowedNegativeValue(value.into())
                                    .add_span(span.clone())
                            })?;
                            alignment = Some((
                                match align_type {
                                    DirectiveAlignment::Exponential => 2_u64.pow(value),
                                    DirectiveAlignment::Byte => value.into(),
                                },
                                data_node.name.1,
                            ));
                            continue;
                        }
                        _ => {}
                    }
                    if let Some((alignment, span)) = alignment.take() {
                        if let Some((start, size)) = data_section
                            .try_align(alignment)
                            .map_err(|e| e.add_span(span))?
                        {
                            data_memory.push(Data {
                                address: start,
                                labels: Vec::new(),
                                value: Value::Padding(size),
                            });
                        }
                    }
                    for (label, span) in &data_node.labels {
                        label_table.insert(
                            label.to_owned(),
                            Label::new(data_section.get(), span.clone()),
                        )?;
                    }
                    match action {
                        DirectiveAction::Segment(_)
                        | DirectiveAction::GlobalSymbol(_)
                        | DirectiveAction::Alignment(_) => unreachable!(),
                        DirectiveAction::Data(DirectiveData::Space(size)) => {
                            let (args, span) = data_node.args;
                            if args.len() != 1 {
                                return Err(ErrorKind::IncorrectDirectiveArgumentNumber {
                                    expected: 1,
                                    found: args.len(),
                                }
                                .add_span(span));
                            };
                            let (value, span) = &args[0];
                            let value = value.to_expr(span.clone())?.int()?;
                            let size = u64::try_from(value).map_err(|_| {
                                ErrorKind::UnallowedNegativeValue(value.into())
                                    .add_span(span.clone())
                            })? * u64::from(size);
                            data_memory.push(Data {
                                address: data_section
                                    .try_reserve(size)
                                    .map_err(|e| e.add_span(span.clone()))?,
                                labels: data_node.labels.into_iter().map(|x| x.0).collect(),
                                value: Value::Space(size),
                            });
                        }
                        DirectiveAction::Data(DirectiveData::Int(size, int_type)) => {
                            for (value, span) in data_node.args.0 {
                                let value = value.to_expr(span.clone())?.int()?;
                                data_memory.push(Data {
                                    address: data_section
                                        .try_reserve_aligned(size.into())
                                        .map_err(|e| e.add_span(span.clone()))?,
                                    labels: data_node.labels.into_iter().map(|x| x.0).collect(),
                                    value: Value::Integer(
                                        Integer::build(
                                            value.into(),
                                            (size * 8).into(),
                                            Some(int_type),
                                            None,
                                        )
                                        .map_err(|e| e.add_span(span))?,
                                    ),
                                });
                                data_node.labels = Vec::new();
                            }
                        }
                        DirectiveAction::Data(DirectiveData::Float(float_type)) => {
                            for (value, span) in data_node.args.0 {
                                let value = value.to_expr(span.clone())?.float()?;
                                #[allow(clippy::cast_possible_truncation)]
                                let (value, size) = match float_type {
                                    FloatType::Float => (Value::Float(value as f32), 4),
                                    FloatType::Double => (Value::Double(value), 8),
                                };
                                data_memory.push(Data {
                                    address: data_section
                                        .try_reserve_aligned(size)
                                        .map_err(|e| e.add_span(span.clone()))?,
                                    labels: data_node.labels.into_iter().map(|x| x.0).collect(),
                                    value,
                                });
                                data_node.labels = Vec::new();
                            }
                        }
                        DirectiveAction::Data(DirectiveData::String(str_type)) => {
                            for (value, span) in data_node.args.0 {
                                let data = value.into_string(span.clone())?;
                                let null_terminated = str_type == StringType::AsciiNullEnd;
                                data_memory.push(Data {
                                    address: data_section
                                        .try_reserve(data.len() as u64 + u64::from(null_terminated))
                                        .map_err(|e| e.add_span(span.clone()))?,
                                    labels: data_node.labels.into_iter().map(|x| x.0).collect(),
                                    value: Value::String {
                                        data,
                                        null_terminated,
                                    },
                                });
                                data_node.labels = Vec::new();
                            }
                        }
                    }
                }
            }
            ASTNode::CodeSegment(instructions) => {
                for instruction_node in instructions {
                    let (name, span) = instruction_node.name;
                    let (def, args) =
                        parse_instruction(arch, (&name, span.clone()), instruction_node.args)?;
                    let addr = code_section
                        .try_reserve(u64::from(word_size) * u64::from(def.nwords))
                        .map_err(|e| e.add_span(span.clone()))?;
                    for (label, span) in &instruction_node.labels {
                        label_table.insert(label.clone(), Label::new(addr, span.clone()))?;
                    }
                    parsed_instructions.push((
                        instruction_node.labels.into_iter().map(|x| x.0).collect(),
                        addr,
                        (def, args),
                    ));
                }
            }
        }
    }
    match label_table.get(arch.main_label()) {
        None => {
            // TODO: what span should this use?
            return Err(ErrorKind::MissingMainLabel(arch.main_label().to_owned()).add_span(0..0));
        }
        Some(main) => {
            let (start, end) = arch.code_section_limits();
            if !(start..=end).contains(&main.address()) {
                return Err(ErrorKind::MainOutsideCode(arch.main_label().to_owned())
                    .add_span(main.span().clone()));
            }
        }
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
            for (field_name, (value, span)) in iter_captures!(field_names).zip(args.into_iter()) {
                let field = def
                    .fields
                    .iter()
                    .find(|field| field.name == field_name)
                    .unwrap();
                #[allow(clippy::cast_sign_loss)]
                let (value, value_str) = match field.r#type {
                    InstructionFieldType::Cop { .. } => {
                        unreachable!("This field type shouldn't be used for instruction arguments")
                    }
                    InstructionFieldType::Co => (def.co.0 as i64, field_name.to_string()),
                    val_type @ (InstructionFieldType::Address
                    | InstructionFieldType::InmSigned
                    | InstructionFieldType::InmUnsigned
                    | InstructionFieldType::OffsetBytes
                    | InstructionFieldType::OffsetWords) => {
                        let value = match value {
                            Argument::Number(expr) => expr.int()?,
                            Argument::Identifier(label) => label_table
                                .get(&label)
                                .ok_or_else(|| {
                                    ErrorKind::UnknownLabel(label).add_span(span.clone())
                                })?
                                .address()
                                .try_into()
                                .unwrap(),
                        };
                        let offset = i64::from(value) - i64::try_from(address).unwrap();
                        let value = match val_type {
                            InstructionFieldType::OffsetWords => {
                                offset / (i64::from(word_size)) - 1
                            }
                            InstructionFieldType::OffsetBytes => offset,
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
                                return Err(ErrorKind::IncorrectArgumentType {
                                    expected: ArgumentType::RegisterName,
                                    found: ArgumentType::Expression,
                                }
                                .add_span(span))
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
                            .ok_or_else(|| {
                                ErrorKind::UnknownRegisterBank(bank_type).add_span(span.clone())
                            })?;
                        let (i, _) = bank.find_register(&name).ok_or_else(|| {
                            ErrorKind::UnknownRegister {
                                name: name.clone(),
                                bank: bank_type,
                            }
                            .add_span(span.clone())
                        })?;
                        (i64::try_from(i).unwrap(), name)
                    }
                };
                binary_instruction
                    .replace(
                        &field.range,
                        value,
                        matches!(
                            field.r#type,
                            InstructionFieldType::InmSigned
                                | InstructionFieldType::OffsetBytes
                                | InstructionFieldType::OffsetWords
                        ),
                    )
                    .map_err(|e| e.add_span(span))?;
                translated_instruction = RE
                    .replace(&translated_instruction, NoExpand(&value_str))
                    .to_string();
                for (range, value) in def.fields.iter().filter_map(|field| match field.r#type {
                    InstructionFieldType::Cop { value } => Some((&field.range, value)),
                    _ => None,
                }) {
                    #[allow(clippy::cast_possible_wrap)]
                    binary_instruction
                        .replace(range, value.0 as i64, false)
                        .unwrap();
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
