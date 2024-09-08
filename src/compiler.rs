use once_cell::sync::Lazy;
use regex::{NoExpand, Regex};

use crate::architecture::{
    Architecture, ComponentType, DirectiveAction, Instruction as InstructionDefinition,
    InstructionFieldType,
};
use crate::parser::{
    parse_expr, parse_identifier, ASTNode, Argument, Data as DataToken, Span, Spanned, Token,
};

mod label;
use label::{Label, Table as LabelTable};

mod error;
pub use error::{DirectiveArgumentType, Error as CompileError, Kind as ErrorKind};

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

macro_rules! iter_captures_spanned {
    ($var:ident) => {
        $var.iter().skip(1).map(|cap| {
            let cap = cap.expect("This shouldn't fail because none of the captures are optional");
            (cap.as_str(), cap.range())
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
    args: &Spanned<Vec<Token>>,
) -> Result<(&'a InstructionDefinition<'a>, Vec<Spanned<Argument>>), CompileError> {
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
            // FIXME: get correct span offset
            for (field_name, (code, span)) in
                iter_captures!(field_names).zip(iter_captures_spanned!(fields))
            {
                let field = inst
                    .fields
                    .iter()
                    .find(|field| field.name == field_name)
                    .unwrap();
                // TODO: actually parse the arguments
                parsed_args.push((
                    match field.r#type {
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
                    },
                    (name_span.start + span.start)..(name_span.start + span.end),
                ));
            }
            return Ok((inst, parsed_args));
        }
    }
    Err(if found {
        ErrorKind::IncorrectInstructionSyntax(
            arch.find_instructions(name)
                .map(|inst| inst.signature_raw.to_string())
                .collect(),
        )
        .add_span(args.1.clone())
    } else {
        ErrorKind::UnknownInstruction(name.to_string()).add_span(name_span)
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
    fn into_string(self) -> Result<String, ErrorKind> {
        match self {
            Self::String(s) => Ok(s),
            Self::Number(_) => Err(ErrorKind::IncorrectDirectiveArgumentType {
                expected: DirectiveArgumentType::String,
                found: DirectiveArgumentType::Number,
            }),
        }
    }

    fn to_number(&self, span: Span) -> Result<i32, CompileError> {
        match self {
            Self::Number(expr) => expr
                .value()
                .map_err(|span| ErrorKind::DivisionBy0.add_span(span)),
            Self::String(_) => Err(ErrorKind::IncorrectDirectiveArgumentType {
                expected: DirectiveArgumentType::Number,
                found: DirectiveArgumentType::String,
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
                    let directive = arch.get_directive(&data_node.name.0).ok_or(
                        ErrorKind::UnknownDirective(data_node.name.0)
                            .add_span(data_node.name.1.clone()),
                    )?;
                    match directive.action {
                        DirectiveAction::DataSegment
                        | DirectiveAction::CodeSegment
                        | DirectiveAction::GlobalSymbol => unreachable!(),
                        DirectiveAction::ByteAlign | DirectiveAction::Align => {
                            let (args, span) = data_node.args;
                            if args.len() != 1 {
                                return Err(ErrorKind::IncorrectDirectiveArgumentNumber {
                                    expected: 1,
                                    found: args.len(),
                                }
                                .add_span(span));
                            };
                            let (value, span) = &args[0];
                            let value = value.to_number(span.clone())?;
                            let value = u32::try_from(value).map_err(|_| {
                                ErrorKind::UnallowedNegativeValue(value.into())
                                    .add_span(span.clone())
                            })?;
                            alignment = Some((
                                if directive.action == DirectiveAction::Align {
                                    2_u64.pow(value)
                                } else {
                                    value.into()
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
                    match directive.action {
                        DirectiveAction::DataSegment
                        | DirectiveAction::CodeSegment
                        | DirectiveAction::GlobalSymbol
                        | DirectiveAction::ByteAlign
                        | DirectiveAction::Align => unreachable!(),
                        DirectiveAction::Space => {
                            let (args, span) = data_node.args;
                            if args.len() != 1 {
                                return Err(ErrorKind::IncorrectDirectiveArgumentNumber {
                                    expected: 1,
                                    found: args.len(),
                                }
                                .add_span(span));
                            };
                            let (value, span) = &args[0];
                            let value = value.to_number(span.clone())?;
                            let size = u64::try_from(value).map_err(|_| {
                                ErrorKind::UnallowedNegativeValue(value.into())
                                    .add_span(span.clone())
                            })? * directive.size.unwrap().parse::<u64>().unwrap();
                            data_memory.push(Data {
                                address: data_section
                                    .try_reserve(size)
                                    .map_err(|e| e.add_span(span.clone()))?,
                                labels: data_node.labels.into_iter().map(|x| x.0).collect(),
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
                            for (value, span) in data_node.args.0 {
                                let value = value.to_number(span.clone())?;
                                data_memory.push(Data {
                                    address: data_section
                                        .try_reserve_aligned(size)
                                        .map_err(|e| e.add_span(span.clone()))?,
                                    labels: data_node.labels.into_iter().map(|x| x.0).collect(),
                                    value: Value::Integer(
                                        Integer::build(
                                            value.into(),
                                            (size * 8).try_into().unwrap(),
                                            Some(variant),
                                            None,
                                        )
                                        .map_err(|e| e.add_span(span))?,
                                    ),
                                });
                                data_node.labels = Vec::new();
                            }
                        }
                        DirectiveAction::Float | DirectiveAction::Double => {
                            todo!("Complete after float support is added")
                        }
                        DirectiveAction::AsciiNullEnd | DirectiveAction::AsciiNotNullEnd => {
                            for (value, span) in data_node.args.0 {
                                let data =
                                    value.into_string().map_err(|e| e.add_span(span.clone()))?;
                                let null_terminated =
                                    directive.action == DirectiveAction::AsciiNullEnd;

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
                        parse_instruction(arch, (&name, span.clone()), &instruction_node.args)?;
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
    if label_table.get(arch.main_label()).is_none() {
        return Err(ErrorKind::MissingMainLabel(arch.main_label().to_owned()).add_span(0..0));
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
                            Argument::Number(expr) => expr
                                .value()
                                .map_err(|span| ErrorKind::DivisionBy0.add_span(span))?,
                            Argument::Identifier(label) => label_table
                                .get(&label)
                                .ok_or(ErrorKind::UnknownLabel(label).add_span(span.clone()))?
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
                            .ok_or(
                                ErrorKind::UnknownRegisterBank(bank_type).add_span(span.clone()),
                            )?;
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
                        &field.startbit,
                        &field.stopbit,
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
                for field in def
                    .fields
                    .iter()
                    .filter(|field| field.r#type == InstructionFieldType::Cop)
                {
                    binary_instruction
                        .replace(
                            &field.startbit,
                            &field.stopbit,
                            i64::from_str_radix(field.value_field.unwrap(), 2).unwrap(),
                            false,
                        )
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
