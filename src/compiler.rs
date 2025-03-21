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

//! Module containing the definition of the assembly compiler
//!
//! The entry point for compiler code is the [`compile()`] function. Users are expected to parse
//! the code first to an AST with [`crate::parser::parse()`]

use num_bigint::{BigInt, BigUint};
use once_cell::sync::Lazy;
use regex::{NoExpand, Regex};

use std::collections::{HashMap, HashSet};

use crate::architecture::{
    AlignmentType, Architecture, DirectiveAction, DirectiveData, DirectiveSegment, FieldType,
    FloatType, IntegerType, RegisterType, StringType,
};
use crate::parser::instruction::ParsedArgs;
use crate::parser::{
    ASTNode, Data as DataToken, Expr, InstructionNode, Statement as StatementNode, Token,
};
use crate::span::{Source, Span, SpanList, Spanned};

mod label;
pub use label::{Label, Table as LabelTable};

pub mod error;
use error::{ArgumentType, SpannedErr as _};
pub use error::{Data as ErrorData, Error as CompileError, Kind as ErrorKind};

mod bit_field;
use bit_field::BitField;

mod section;
use section::Section;

mod integer;
pub use integer::Integer;

mod pseudoinstruction;
pub use pseudoinstruction::{Error as PseudoinstructionError, Kind as PseudoinstructionErrorKind};

/* TODO:
*  - Refactor code
*  - Combine `crate::parser::Error` with `crate::compiler::Error`
**/

#[derive(Debug)]
enum InstructionDefinition<'arch> {
    Real(&'arch crate::architecture::Instruction<'arch>),
    Pseudo(&'arch crate::architecture::Pseudoinstruction<'arch>),
}

/// Parse the arguments of an instruction according to any of its definitions. If the arguments
/// match the syntax of multiple definitions, one of them is selected according to the following
/// criteria:
///
/// * If there are multiple definitions in which the arguments fit, the first one is used. For
///   arguments whose size can't be known, it's assumed that they will fit
/// * If there are no definitions in which the arguments fit, the last one that parsed correctly is
///   used
///
/// # Parameters
///
/// * `arch`: architecture definition
/// * `name`: name of the instruction
/// * `args`: vector of tokens that form the instruction arguments
///
/// # Errors
///
/// Errors if the instruction name doesn't exist, or if the arguments doesn't match the syntax of
/// any of the instruction definitions for this instruction name
fn parse_instruction<'a>(
    arch: &'a Architecture,
    name: Spanned<String>,
    args: &Spanned<Vec<Spanned<Token>>>,
) -> Result<(InstructionDefinition<'a>, ParsedArgs), ErrorData> {
    let mut possible_def = None;
    // Errors produced on each of the attempted parses
    let mut errs = Vec::new();
    // Get all instruction definitions with the given name
    for inst in arch.find_instructions(&name.0) {
        // Try to parse the given arguments according to the syntax of the current definition
        match inst.syntax.parser.parse(args) {
            // If parsing is successful, assume this definition is the correct one and return it
            Ok(parsed_args) => {
                // Check if all the arguments fit in the current instruction definition
                let ok = parsed_args.iter().all(|arg| {
                    // Get the current field
                    let field = &inst.syntax.fields[arg.field_idx];
                    // Get the value
                    let value = match field.r#type {
                        // If the field expects a number and the argument value is a number,
                        // evaluate the number
                        FieldType::Address
                        | FieldType::ImmSigned
                        | FieldType::ImmUnsigned
                        | FieldType::OffsetBytes
                        | FieldType::OffsetWords => match arg.value.0.int(Expr::unallowed_ident) {
                            Ok(val) => val,
                            // If there was any error, assume the argument fits. This should be
                            // properly handled later when the arguments are fully evaluated
                            Err(_) => return true,
                        },
                        // Otherwise, assume the argument fits to avoid circular dependencies
                        _ => return true,
                    };
                    // Check if it fits by trying to build an integer with the required size
                    Integer::build(
                        value,
                        field.range.size(),
                        None,
                        Some(matches!(
                            field.r#type,
                            FieldType::ImmSigned | FieldType::OffsetBytes | FieldType::OffsetWords
                        )),
                    )
                    .is_ok()
                });
                // If all arguments fit the current definition, use it as the correct one
                if ok {
                    return Ok((InstructionDefinition::Real(inst), parsed_args));
                }
                // Otherwise, store it in case this is the only matching definition
                possible_def = Some((inst, parsed_args));
            }
            // Otherwise, append the produced error to the error vector and try the next definition
            Err(e) => errs.push((inst.syntax.user_syntax.to_string(), e)),
        }
    }
    // Get all pseudoinstruction definitions with the given name
    for inst in arch.find_pseudoinstructions(&name.0) {
        // Try to parse the given arguments according to the syntax of the current definition
        match inst.syntax.parser.parse(args) {
            // If parsing is successful, assume this definition is the correct one and return it
            Ok(parsed_args) => return Ok((InstructionDefinition::Pseudo(inst), parsed_args)),
            // Otherwise, append the produced error to the error vector and try the next definition
            Err(e) => errs.push((inst.syntax.user_syntax.to_string(), e)),
        }
    }
    // None of the definitions matched perfectly
    // If there is a matching definition that failed due to argument sizes, use it
    if let Some((def, args)) = possible_def {
        return Ok((InstructionDefinition::Real(def), args));
    }
    // Otherwise, return the appropriate error
    // If we didn't get any errors, we didn't find any definitions for the instruction
    Err(if errs.is_empty() {
        ErrorKind::UnknownInstruction(name.0).add_span(&name.1)
    } else {
        ErrorKind::IncorrectInstructionSyntax(errs).add_span(&args.1)
    })
}

/// Processed instruction pending argument evaluation
#[derive(Debug, Clone)]
pub struct PendingInstruction<'arch> {
    /// Address of the instruction
    address: BigUint,
    /// Labels pointing to this instruction
    labels: Vec<String>,
    /// Span of the instruction in the user's assembly code
    user_span: Span,
    /// Span of the instruction in pseudoinstruction expansions
    span: SpanList,
    /// Instruction definition selected
    definition: &'arch crate::architecture::Instruction<'arch>,
    /// Arguments parsed for this instruction
    args: ParsedArgs,
}

fn process_instruction<'arch>(
    arch: &'arch Architecture,
    section: &mut Section,
    label_table: &mut LabelTable,
    pending_instructions: &mut Vec<PendingInstruction<'arch>>,
    instruction: (InstructionDefinition<'arch>, ParsedArgs),
    span: (Span, SpanList),
) -> Result<(), ErrorData> {
    let (user_span, span) = span;
    match instruction.0 {
        // Base case: we have a real instruction => push it to the parsed instructions normally
        InstructionDefinition::Real(definition) => {
            let word_size = BigUint::from(arch.word_size().div_ceil(8));
            let address = section
                .try_reserve(&(word_size * definition.nwords))
                .add_span(span.clone())?;
            pending_instructions.push(PendingInstruction {
                labels: Vec::new(),
                args: instruction.1,
                address,
                user_span,
                span,
                definition,
            });
        }
        // Recursive case: we have a pseudoinstruction => expand it into multiple instructions and
        // process each of them recursively
        InstructionDefinition::Pseudo(def) => {
            let instructions = pseudoinstruction::expand(
                arch,
                label_table,
                section.get(),
                (def, span),
                &instruction.1,
            )?;
            for (instruction, span) in instructions {
                process_instruction(
                    arch,
                    section,
                    label_table,
                    pending_instructions,
                    instruction,
                    (user_span.clone(), span),
                )?;
            }
        }
    }
    Ok(())
}

/// Compiled instruction
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Instruction {
    /// Address of the instruction
    pub address: BigUint,
    /// Labels pointing to this instruction
    pub labels: Vec<String>,
    /// Translated instruction to a simplified syntax
    pub loaded: String,
    /// Instruction encoded in binary
    pub binary: BitField,
    /// Span of the instruction in the assembly code
    pub user: Span,
}

/// Value to add to the data segment pending argument evaluation
#[derive(Debug, PartialEq, Clone)]
pub enum PendingValue {
    /// Integer value
    Integer(Spanned<Expr>, usize, IntegerType),
    /// Reserved space initialized to 0
    Space(BigUint),
    /// Padding added to align elements
    Padding(BigUint),
    /// Single precision floating point value
    Float(f32),
    /// Double precision floating point value
    Double(f64),
    /// UTF-8 string
    String {
        /// Byte sequence of the string, encoded in UTF-8
        data: String,
        /// Whether the string is terminated by a null byte
        null_terminated: bool,
    },
}

/// Value to add to the data segment
#[derive(Debug, PartialEq, Clone)]
pub enum Value {
    /// Integer value
    Integer(Integer),
    /// Reserved space initialized to 0
    Space(BigUint),
    /// Padding added to align elements
    Padding(BigUint),
    /// Single precision floating point value
    Float(f32),
    /// Double precision floating point value
    Double(f64),
    /// UTF-8 string
    String {
        /// Byte sequence of the string, encoded in UTF-8
        data: String,
        /// Whether the string is terminated by a null byte
        null_terminated: bool,
    },
}

/// Compiled data segment element
#[derive(Debug, PartialEq, Clone)]
pub struct PendingData {
    /// Address of the element
    pub address: BigUint,
    /// Labels pointing to this data element
    pub labels: Vec<String>,
    /// Value of the data element
    pub value: PendingValue,
}

/// Compiled data segment element
#[derive(Debug, PartialEq, Clone)]
pub struct Data {
    /// Address of the element
    pub address: BigUint,
    /// Labels pointing to this data element
    pub labels: Vec<String>,
    /// Value of the data element
    pub value: Value,
}

impl DataToken {
    /// Convert the value to a string
    ///
    /// # Parameters
    ///
    /// * `span`: span of the value in the assembly code
    fn into_string(self, span: &Span) -> Result<String, ErrorData> {
        match self {
            Self::String(s) => Ok(s),
            Self::Number(_) => Err(ErrorKind::IncorrectArgumentType {
                expected: ArgumentType::String,
                found: ArgumentType::Expression,
            }),
        }
        .add_span(span)
    }

    /// Convert the value to an expression
    ///
    /// # Parameters
    ///
    /// * `span`: span of the value in the assembly code
    fn to_expr(&self, span: &Span) -> Result<&Expr, ErrorData> {
        match self {
            Self::Number(expr) => Ok(expr),
            Self::String(_) => Err(ErrorKind::IncorrectArgumentType {
                expected: ArgumentType::Expression,
                found: ArgumentType::String,
            }),
        }
        .add_span(span)
    }
}

/// Compilation result
#[derive(Debug, PartialEq, Clone)]
pub struct CompiledCode {
    /// Symbol table for labels
    pub label_table: LabelTable,
    /// Table indicating which labels are global
    pub global_symbols: GlobalSymbols,
    /// Compiled instructions
    pub instructions: Vec<Instruction>,
    /// Compiled data elements
    pub data_memory: Vec<Data>,
}

/// Convert a vector of spanned elements to a vector of elements, leaving an empty vector
///
/// # Parameters
///
/// * `src`: source vector to take the data from
fn take_spanned_vec<T>(src: &mut Vec<Spanned<T>>) -> Vec<T> {
    std::mem::take(src).into_iter().map(|x| x.0).collect()
}

/// Statement extracted from the AST
#[derive(Debug, PartialEq, Clone)]
struct Statement<T> {
    /// Labels attached to the node
    labels: Vec<Spanned<String>>,
    /// Whether the statement is in a kernel section (`true`) or not (`false`)
    kernel: bool,
    /// Statement of the node
    value: Spanned<T>,
}

/// Data values to add to the data segment
struct DataValue {
    /// Expected type of the values
    data_type: DirectiveData,
    /// Values to be added to the data segment
    values: Spanned<Vec<Spanned<DataToken>>>,
}

type Instructions = Vec<Statement<InstructionNode>>;
type DataDirectives = Vec<Statement<DataValue>>;
pub type GlobalSymbols = HashSet<String>;

fn split_statements(
    arch: &Architecture,
    ast: Vec<ASTNode>,
) -> Result<(Instructions, DataDirectives, GlobalSymbols), ErrorData> {
    let mut current_section: Option<Spanned<DirectiveSegment>> = None;
    let mut data_directives = Vec::new();
    let mut instructions = Vec::new();
    let mut global_symbols = HashSet::new();

    for node in ast {
        match node.statement.0 {
            StatementNode::Directive(directive) => {
                let action = arch.find_directive(&directive.name.0).ok_or_else(|| {
                    ErrorKind::UnknownDirective(directive.name.0).add_span(&directive.name.1)
                })?;
                match (action, &current_section) {
                    (DirectiveAction::Segment(new_section), _) => {
                        ArgumentNumber::new(0, false).check(&directive.args)?;
                        current_section = Some((new_section, node.statement.1));
                    }
                    (DirectiveAction::GlobalSymbol(_), _) => {
                        ArgumentNumber::new(1, true).check(&directive.args)?;
                        for (label, span) in directive.args.0 {
                            let label = match label {
                                DataToken::Number(Expr::Identifier(label)) => label,
                                DataToken::Number(_) => Err(ErrorKind::IncorrectArgumentType {
                                    expected: ArgumentType::Identifier,
                                    found: ArgumentType::Expression,
                                }
                                .add_span(&span))?,
                                DataToken::String(_) => Err(ErrorKind::IncorrectArgumentType {
                                    expected: ArgumentType::Identifier,
                                    found: ArgumentType::String,
                                }
                                .add_span(&span))?,
                            };
                            global_symbols.insert(label.0);
                        }
                    }
                    (DirectiveAction::Nop(_), _) => {}
                    (DirectiveAction::Data(data_type), Some((section, _)))
                        if !section.is_code() =>
                    {
                        let span = node.statement.1;
                        data_directives.push(Statement {
                            labels: node.labels,
                            value: (
                                DataValue {
                                    data_type,
                                    values: directive.args,
                                },
                                span,
                            ),
                            kernel: *section == DirectiveSegment::KernelData,
                        });
                    }
                    (DirectiveAction::Data(_), _) => {
                        return Err(ErrorKind::UnallowedStatementType {
                            section: current_section,
                            found: DirectiveSegment::Data,
                        }
                        .add_span(&node.statement.1));
                    }
                }
            }
            StatementNode::Instruction(instruction) => match &current_section {
                Some((section, _)) if section.is_code() => instructions.push(Statement {
                    labels: node.labels,
                    value: (instruction, node.statement.1),
                    kernel: *section == DirectiveSegment::KernelCode,
                }),
                _ => {
                    return Err(ErrorKind::UnallowedStatementType {
                        section: current_section,
                        found: DirectiveSegment::Code,
                    }
                    .add_span(&node.statement.1));
                }
            },
        }
    }
    Ok((instructions, data_directives, global_symbols))
}

/// Amount of arguments expected by a directive
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ArgumentNumber {
    /// Minimum expected amount
    pub amount: usize,
    /// Whether it's allowed to use more arguments
    pub at_least: bool,
}

impl ArgumentNumber {
    /// Creates a new [`ArgumentNumber`]
    #[must_use]
    pub const fn new(amount: usize, at_least: bool) -> Self {
        Self { amount, at_least }
    }

    /// Check if the argument number matches the amount specified
    ///
    /// # Parameters
    ///
    /// * `args`: arguments found
    ///
    /// # Errors
    ///
    /// Errors if the amount of arguments doesn't match the specified amount
    fn check<T>(self, args: &Spanned<Vec<T>>) -> Result<(), ErrorData> {
        let len = args.0.len();
        if len < self.amount || (!self.at_least && len != self.amount) {
            return Err(ErrorKind::IncorrectDirectiveArgumentNumber {
                expected: self,
                found: args.0.len(),
            }
            .add_span(&args.1));
        };
        Ok(())
    }
}

/// Combines a kernel section with a user section into a single memory vector. The sections
/// shouldn't overlap
fn combine_sections<T>(kernel: (Section, Vec<T>), user: (Section, Vec<T>)) -> Vec<T> {
    // Sort the sections
    let (mem1, mem2) = if kernel.0.get() <= user.0.get() {
        (kernel.1, user.1)
    } else {
        (user.1, kernel.1)
    };
    // Chain the elements
    mem1.into_iter().chain(mem2).collect()
}

#[allow(clippy::too_many_lines)]
fn compile_data(
    arch: &Architecture,
    label_table: &mut LabelTable,
    elements: Vec<Statement<DataValue>>,
) -> Result<Vec<PendingData>, ErrorData> {
    let size = elements.len();
    let mut user = (
        Section::new("Data", Some(arch.data_section())),
        Vec::with_capacity(size),
    );
    let mut kernel = (
        Section::new("KernelData", arch.kernel_data_section()),
        Vec::with_capacity(size),
    );
    let word_size_bytes = arch.word_size().div_ceil(8);

    for data_directive in elements {
        let mut labels = data_directive.labels;
        let (section, memory) = if data_directive.kernel {
            &mut kernel
        } else {
            &mut user
        };
        for (label, span) in &labels {
            label_table.insert(
                label.to_owned(),
                Label::new(section.get().clone(), span.clone()),
            )?;
        }
        let (statement, statement_span) = data_directive.value;
        let args = statement.values;
        match statement.data_type {
            DirectiveData::Alignment(align_type) => {
                ArgumentNumber::new(1, false).check(&args)?;
                let (value, span) = &args.0[0];
                let value = value.to_expr(span)?.int(Expr::unallowed_ident)?;
                let value = BigUint::try_from(value).map_err(|e| {
                    ErrorKind::UnallowedNegativeValue(e.into_original()).add_span(span)
                })?;
                let align = match align_type {
                    AlignmentType::Exponential => {
                        let value = u128::try_from(value).map_err(|e| {
                            ErrorKind::IntegerOutOfRange(
                                e.into_original().into(),
                                0.into()..=u128::MAX.into(),
                            )
                            .add_span(span)
                        })?;
                        BigUint::from(1u8) << value
                    }
                    AlignmentType::Byte => value,
                };
                let (start, size) = section.try_align(&align).add_span(&statement_span)?;
                if size != BigUint::ZERO {
                    memory.push(PendingData {
                        address: start,
                        labels: take_spanned_vec(&mut labels),
                        value: PendingValue::Padding(size),
                    });
                }
            }
            DirectiveData::Space(size) => {
                ArgumentNumber::new(1, false).check(&args)?;
                let (value, span) = &args.0[0];
                let value = value.to_expr(span)?.int(Expr::unallowed_ident)?;
                let size = BigUint::try_from(value).map_err(|e| {
                    ErrorKind::UnallowedNegativeValue(e.into_original()).add_span(span)
                })? * size;
                memory.push(PendingData {
                    address: section.try_reserve(&size).add_span(span)?,
                    labels: take_spanned_vec(&mut labels),
                    value: PendingValue::Space(size),
                });
            }
            DirectiveData::Int(size, int_type) => {
                ArgumentNumber::new(1, true).check(&args)?;
                for (value, span) in args.0 {
                    let value = match value {
                        DataToken::Number(expr) => expr,
                        DataToken::String(_) => {
                            return Err(ErrorKind::IncorrectArgumentType {
                                expected: ArgumentType::Expression,
                                found: ArgumentType::String,
                            }
                            .add_span(&span))
                        }
                    };
                    memory.push(PendingData {
                        address: section
                            .try_reserve_aligned(&size.into(), word_size_bytes)
                            .add_span(&span)?,
                        labels: take_spanned_vec(&mut labels),
                        value: PendingValue::Integer((value, span), size, int_type),
                    });
                }
            }
            DirectiveData::Float(float_type) => {
                ArgumentNumber::new(1, true).check(&args)?;
                for (value, span) in args.0 {
                    let value = value.to_expr(&span)?.float()?;
                    #[allow(clippy::cast_possible_truncation)]
                    let (value, size) = match float_type {
                        FloatType::Float => (PendingValue::Float(value as f32), 4u8),
                        FloatType::Double => (PendingValue::Double(value), 8),
                    };
                    memory.push(PendingData {
                        address: section
                            .try_reserve_aligned(&size.into(), word_size_bytes)
                            .add_span(&span)?,
                        labels: take_spanned_vec(&mut labels),
                        value,
                    });
                }
            }
            DirectiveData::String(str_type) => {
                ArgumentNumber::new(1, true).check(&args)?;
                for (value, span) in args.0 {
                    let data = value.into_string(&span)?;
                    let null_terminated = str_type == StringType::AsciiNullEnd;
                    memory.push(PendingData {
                        address: section
                            .try_reserve(&(BigUint::from(data.len()) + u8::from(null_terminated)))
                            .add_span(&span)?,
                        labels: take_spanned_vec(&mut labels),
                        value: PendingValue::String {
                            data,
                            null_terminated,
                        },
                    });
                }
            }
        }
    }
    Ok(combine_sections(kernel, user))
}

fn compile_instructions<'a>(
    arch: &'a Architecture,
    label_table: &mut LabelTable,
    instructions: Vec<Statement<InstructionNode>>,
    reserved_offset: &BigUint,
) -> Result<Vec<PendingInstruction<'a>>, ErrorData> {
    let size = instructions.len();
    let mut user = (
        Section::new("Instructions", Some(arch.code_section())),
        Vec::with_capacity(size),
    );
    let mut kernel = (
        Section::new("KernelInstructions", arch.kernel_code_section()),
        Vec::with_capacity(size),
    );
    user.0.try_reserve(reserved_offset).add_span(0..0)?;

    for mut instruction in instructions {
        let (name, span) = instruction.value.0.name;
        let (section, pending_instructions) = if instruction.kernel {
            &mut kernel
        } else {
            &mut user
        };
        let parsed_instruction =
            parse_instruction(arch, (name, span.clone()), &instruction.value.0.args)?;
        for (label, span) in &instruction.labels {
            label_table.insert(
                label.clone(),
                Label::new(section.get().clone(), span.clone()),
            )?;
        }
        let first_idx = pending_instructions.len();
        process_instruction(
            arch,
            section,
            label_table,
            pending_instructions,
            parsed_instruction,
            (instruction.value.1.clone(), instruction.value.1.into()),
        )?;
        if let Some(inst) = pending_instructions.get_mut(first_idx) {
            inst.labels = take_spanned_vec(&mut instruction.labels);
        }
        for inst in &mut pending_instructions[first_idx + 1..] {
            inst.user_span = 0..0;
        }
    }
    Ok(combine_sections(kernel, user))
}

#[allow(clippy::too_many_lines)]
fn compile_inner(
    arch: &Architecture,
    ast: Vec<ASTNode>,
    label_table: &mut LabelTable,
    reserved_offset: &BigUint,
    library: bool,
) -> Result<(GlobalSymbols, Vec<Instruction>, Vec<Data>), ErrorData> {
    let word_size_bits = arch.word_size();
    let word_size_bytes = arch.word_size().div_ceil(8);

    let (instructions, data_directives, global_symbols) = split_statements(arch, ast)?;

    let instruction_eof = instructions.last().map_or(0, |inst| inst.value.1.end);
    let pending_data = compile_data(arch, label_table, data_directives)?;
    let pending_instructions =
        compile_instructions(arch, label_table, instructions, reserved_offset)?;

    let add_main_span = |e: ErrorKind, main: &Label| e.add_span(main.span().unwrap_or(&(0..0)));
    match (label_table.get(arch.main_label()), library) {
        (None, false) => {
            #[allow(clippy::range_plus_one)] // Ariadne works with exclusive ranges
            return Err(
                ErrorKind::MissingMainLabel.add_span(&(instruction_eof..instruction_eof + 1))
            );
        }
        (Some(main), true) => return Err(add_main_span(ErrorKind::MainInLibrary, main)),
        (Some(main), false) if !arch.code_section().contains(main.address()) => {
            return Err(add_main_span(ErrorKind::MainOutsideCode, main));
        }
        _ => {}
    }

    let instructions = pending_instructions
        .into_iter()
        .map(|inst| {
            // Regex for replacement templates in the translation spec of instructions
            static RE: Lazy<Regex> = crate::regex!(r"[fF]([0-9]+)");
            static FIELD: Lazy<Regex> = crate::regex!("\0([0-9]+)");
            let def = inst.definition;
            let mut binary_instruction = BitField::new(word_size_bits.saturating_mul(def.nwords));
            let mut translated_instruction =
                RE.replace_all(def.syntax.output_syntax, "\0$1").to_string();
            for arg in inst.args {
                let field = &def.syntax.fields[arg.field_idx];
                #[allow(clippy::cast_sign_loss)]
                let (value, value_str) = match &field.r#type {
                    FieldType::Cop { .. } => {
                        unreachable!("This field type shouldn't be used for instruction arguments")
                    }
                    FieldType::Co => (def.co.0.clone().into(), def.name.to_string()),
                    val_type @ (FieldType::Address
                    | FieldType::ImmSigned
                    | FieldType::ImmUnsigned
                    | FieldType::OffsetBytes
                    | FieldType::OffsetWords) => {
                        let ident_eval = |label: &str| {
                            let value = if label == "." {
                                BigInt::from(inst.address.clone())
                            } else {
                                label_table
                                    .get(label)
                                    .ok_or_else(|| ErrorKind::UnknownLabel(label.to_owned()))?
                                    .address()
                                    .clone()
                                    .into()
                            };
                            let offset = |x| x - BigInt::from(inst.address.clone());
                            Ok(match val_type {
                                FieldType::OffsetWords => offset(value) / word_size_bytes,
                                FieldType::OffsetBytes => offset(value),
                                _ => value,
                            })
                        };
                        let value = arg.value.0.int(ident_eval)?;
                        let padding = field.range.padding();
                        let value = (value >> padding) << padding;
                        let value_str = value.to_string();
                        (value, value_str)
                    }
                    val_type @ (FieldType::IntReg
                    | FieldType::CtrlReg
                    | FieldType::SingleFPReg
                    | FieldType::DoubleFPReg) => {
                        let name = match arg.value.0 {
                            Expr::Identifier((name, _)) => name,
                            Expr::Integer(x) => x.to_string(),
                            _ => {
                                return Err(ErrorKind::IncorrectArgumentType {
                                    expected: ArgumentType::RegisterName,
                                    found: ArgumentType::Expression,
                                }
                                .add_span((&arg.value.1, &inst.span)))
                            }
                        };
                        let file_type = match val_type {
                            FieldType::IntReg => RegisterType::Int,
                            FieldType::CtrlReg => RegisterType::Ctrl,
                            FieldType::SingleFPReg => RegisterType::Float(FloatType::Float),
                            FieldType::DoubleFPReg => RegisterType::Float(FloatType::Double),
                            _ => unreachable!("We already matched one of these variants"),
                        };
                        let mut files = arch.find_reg_files(file_type).peekable();
                        files.peek().ok_or_else(|| {
                            ErrorKind::UnknownRegisterFile(file_type)
                                .add_span((&arg.value.1, &inst.span))
                        })?;
                        let (i, _) = files
                            .find_map(|file| file.find_register(&name))
                            .ok_or_else(|| {
                                ErrorKind::UnknownRegister {
                                    name: name.clone(),
                                    file: file_type,
                                }
                                .add_span((&arg.value.1, &inst.span))
                            })?;
                        (i.into(), name)
                    }
                    FieldType::Enum { enum_name } => {
                        let span = (&arg.value.1, &inst.span);
                        let enum_definition = arch
                            .enums
                            .get(enum_name)
                            .ok_or_else(|| ErrorKind::UnknownEnumType((*enum_name).to_string()))
                            .add_span(span)?;
                        let Expr::Identifier((name, _)) = arg.value.0 else {
                            return Err(ErrorKind::IncorrectArgumentType {
                                expected: ArgumentType::Identifier,
                                found: ArgumentType::Expression,
                            }
                            .add_span(span));
                        };
                        let Some(value) = enum_definition.get(name.as_str()) else {
                            return Err(ErrorKind::UnknownEnumValue {
                                value: name,
                                enum_name: (*enum_name).to_string(),
                            })
                            .add_span(span);
                        };
                        (value.0.clone().into(), name)
                    }
                };
                binary_instruction
                    .replace(
                        &field.range,
                        value,
                        matches!(
                            field.r#type,
                            FieldType::ImmSigned | FieldType::OffsetBytes | FieldType::OffsetWords
                        ),
                    )
                    .add_span((&arg.value.1, &inst.span))?;
                translated_instruction = FIELD
                    .replace(&translated_instruction, NoExpand(&value_str))
                    .to_string();
            }
            let fields = def.syntax.fields.iter();
            for (range, value) in fields.filter_map(|field| match &field.r#type {
                FieldType::Cop { value } => Some((&field.range, value)),
                _ => None,
            }) {
                #[allow(clippy::cast_possible_wrap)]
                binary_instruction
                    .replace(range, value.0.clone().into(), false)
                    .add_span(inst.span.clone())?;
            }
            Ok(Instruction {
                labels: inst.labels,
                address: inst.address,
                binary: binary_instruction,
                loaded: translated_instruction,
                user: inst.user_span,
            })
        })
        .collect::<Result<Vec<_>, _>>()?;

    let data_memory = pending_data
        .into_iter()
        .map(|data| {
            Ok(Data {
                labels: data.labels,
                value: match data.value {
                    PendingValue::Integer((value, span), size, int_type) => {
                        let ident_eval = |label: &str| {
                            Ok(if label == "." {
                                BigInt::from(data.address.clone())
                            } else {
                                label_table
                                    .get(label)
                                    .ok_or_else(|| ErrorKind::UnknownLabel(label.to_owned()))?
                                    .address()
                                    .clone()
                                    .into()
                            })
                        };
                        let value = value.int(ident_eval)?;
                        Value::Integer(
                            Integer::build(value, size.saturating_mul(8), Some(int_type), None)
                                .add_span(&span)?,
                        )
                    }
                    PendingValue::Space(x) => Value::Space(x),
                    PendingValue::Padding(x) => Value::Padding(x),
                    PendingValue::Float(x) => Value::Float(x),
                    PendingValue::Double(x) => Value::Double(x),
                    PendingValue::String {
                        data,
                        null_terminated,
                    } => Value::String {
                        data,
                        null_terminated,
                    },
                },
                address: data.address,
            })
        })
        .collect::<Result<Vec<_>, _>>()?;

    Ok((global_symbols, instructions, data_memory))
}

pub fn compile<'arch, S: std::hash::BuildHasher>(
    arch: &'arch Architecture,
    ast: Vec<ASTNode>,
    reserved_offset: &BigUint,
    labels: HashMap<String, BigUint, S>,
    library: bool,
) -> Result<CompiledCode, CompileError<'arch>> {
    let mut label_table = LabelTable::from(labels);
    match compile_inner(arch, ast, &mut label_table, reserved_offset, library) {
        Ok((global_symbols, instructions, data_memory)) => Ok(CompiledCode {
            label_table,
            global_symbols,
            instructions,
            data_memory,
        }),
        Err(error) => Err(CompileError {
            arch,
            label_table,
            error,
        }),
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod test {
    use super::*;
    use crate::architecture::{Architecture, BitRange, IntegerType, NonEmptyRangeInclusive};

    fn compile_with(
        src: &str,
        reserved_offset: &BigUint,
        labels: HashMap<String, BigUint>,
        library: bool,
    ) -> Result<CompiledCode, ErrorData> {
        let arch = Architecture::from_json(include_str!("../tests/architecture.json")).unwrap();
        let ast = crate::parser::parse(arch.comment_prefix(), src).unwrap();
        super::compile(&arch, ast, reserved_offset, labels, library).map_err(|e| e.error)
    }

    fn compile_arch(src: &str, arch: &str) -> Result<CompiledCode, ErrorData> {
        let arch = Architecture::from_json(arch).unwrap();
        let ast = crate::parser::parse(arch.comment_prefix(), src).unwrap();
        super::compile(&arch, ast, &BigUint::ZERO, HashMap::new(), false).map_err(|e| e.error)
    }

    fn compile(src: &str) -> Result<CompiledCode, ErrorData> {
        compile_with(src, &BigUint::ZERO, HashMap::new(), false)
    }

    fn label_table(labels: impl IntoIterator<Item = (&'static str, u64, Span)>) -> LabelTable {
        let mut tbl = LabelTable::default();
        for v in labels {
            tbl.insert(v.0.into(), Label::new(v.1.into(), v.2)).unwrap();
        }
        tbl
    }

    fn bitfield(bits: &str) -> BitField {
        let mut field = BitField::new(bits.len());
        for (i, c) in bits.chars().enumerate() {
            if c == '1' {
                let i = bits.len() - i - 1;
                let ranges = vec![NonEmptyRangeInclusive::<usize>::build(i, i).unwrap()];
                field
                    .replace(&BitRange::build(ranges, 0).unwrap(), 1.into(), false)
                    .unwrap();
            }
        }
        field
    }

    fn inst(address: u64, labels: &[&str], loaded: &str, binary: &str, user: Span) -> Instruction {
        Instruction {
            address: address.into(),
            labels: labels.iter().map(|&x| x.to_owned()).collect(),
            loaded: loaded.into(),
            binary: bitfield(binary),
            user,
        }
    }

    static NOP_BINARY: &str = "11110000000000000000000001111111";

    fn main_nop(span: Span) -> Instruction {
        inst(0, &["main"], "nop", NOP_BINARY, span)
    }

    fn data(address: u64, labels: &[&str], value: Value) -> Data {
        Data {
            address: address.into(),
            value,
            labels: labels.iter().map(|&x| x.to_owned()).collect(),
        }
    }

    fn int_val(x: i64, size: usize, ty: IntegerType) -> Value {
        Value::Integer(Integer::build(x.into(), size, Some(ty), None).unwrap())
    }

    #[test]
    fn nop() {
        // Minimal
        let x = compile(".text\nmain: nop").unwrap();
        assert_eq!(x.label_table, label_table([("main", 0, 6..11)]));
        assert_eq!(x.instructions, vec![main_nop(12..15)]);
        assert_eq!(x.data_memory, vec![]);
        assert_eq!(x.global_symbols, HashSet::new());
        // 2 instructions
        let x = compile(".text\nmain: nop\nnop").unwrap();
        assert_eq!(x.label_table, label_table([("main", 0, 6..11)]));
        assert_eq!(
            x.instructions,
            vec![
                main_nop(12..15),
                inst(4, &[], "nop", "11110000000000000000000001111111", 16..19)
            ]
        );
        assert_eq!(x.data_memory, vec![]);
        assert_eq!(x.global_symbols, HashSet::new());
    }

    #[test]
    fn instruction_multiword() {
        let x = compile(".text\nmain: nop2\nnop").unwrap();
        let binary = "1001000000000000000000000000000000000000000000000000000001000001";
        assert_eq!(x.label_table, label_table([("main", 0, 6..11)]));
        assert_eq!(
            x.instructions,
            vec![
                inst(0, &["main"], "nop2", binary, 12..16),
                inst(8, &[], "nop", "11110000000000000000000001111111", 17..20),
            ]
        );
        assert_eq!(x.data_memory, vec![]);
        assert_eq!(x.global_symbols, HashSet::new());
    }

    #[test]
    fn instruction_multiple_defs() {
        // Definition 1
        let x = compile(".text\nmain: multi 15").unwrap();
        let binary = "11110000000000000000000001110011";
        assert_eq!(x.label_table, label_table([("main", 0, 6..11)]));
        assert_eq!(
            x.instructions,
            vec![inst(0, &["main"], "multi 15", binary, 12..20)]
        );
        assert_eq!(x.data_memory, vec![]);
        assert_eq!(x.global_symbols, HashSet::new());
        // Definition 2
        let x = compile(".text\nmain: multi $").unwrap();
        let binary = "00000000000000000000000001011101";
        assert_eq!(x.label_table, label_table([("main", 0, 6..11)]));
        assert_eq!(
            x.instructions,
            vec![inst(0, &["main"], "multi $", binary, 12..19)]
        );
        assert_eq!(x.data_memory, vec![]);
        assert_eq!(x.global_symbols, HashSet::new());
        // Definition 3
        let x = compile(".text\nmain: multi 17").unwrap();
        let binary = "10001000000000000000000001000001";
        assert_eq!(x.label_table, label_table([("main", 0, 6..11)]));
        assert_eq!(
            x.instructions,
            vec![inst(0, &["main"], "multi 17", binary, 12..20)]
        );
        assert_eq!(x.data_memory, vec![]);
        assert_eq!(x.global_symbols, HashSet::new());
    }

    #[test]
    fn instruction_fields_regs() {
        // Simple
        let x = compile(".text\nmain: reg ctrl1, x2, ft1, ft2").unwrap();
        let binary = "01001000000000000000000000010010";
        let tbl = label_table([("main", 0, 6..11)]);
        assert_eq!(x.label_table, tbl);
        assert_eq!(
            x.instructions,
            vec![inst(0, &["main"], "reg ctrl1 x2 ft1 ft2", binary, 12..35)]
        );
        assert_eq!(x.data_memory, vec![]);
        assert_eq!(x.global_symbols, HashSet::new());
        // Aliases
        let x = compile(".text\nmain: reg ctrl1, two, F1, Field2").unwrap();
        assert_eq!(x.label_table, tbl);
        let instruction = "reg ctrl1 two F1 Field2";
        assert_eq!(
            x.instructions,
            vec![inst(0, &["main"], instruction, binary, 12..38)]
        );
        assert_eq!(x.data_memory, vec![]);
        assert_eq!(x.global_symbols, HashSet::new());
        // Number aliases
        let x = compile(".text\nmain: reg ctrl1, 2, ft1, ft2").unwrap();
        assert_eq!(x.label_table, tbl);
        assert_eq!(
            x.instructions,
            vec![inst(0, &["main"], "reg ctrl1 2 ft1 ft2", binary, 12..34)]
        );
        assert_eq!(x.data_memory, vec![]);
        assert_eq!(x.global_symbols, HashSet::new());
        // Linked floating point registers
        let x = compile(".text\nmain: reg ctrl1, x2, fs1, FD2").unwrap();
        assert_eq!(x.label_table, tbl);
        assert_eq!(
            x.instructions,
            vec![inst(0, &["main"], "reg ctrl1 x2 fs1 FD2", binary, 12..35)]
        );
        assert_eq!(x.data_memory, vec![]);
        assert_eq!(x.global_symbols, HashSet::new());
    }

    #[test]
    fn instruction_fields_immediate() {
        let x = compile(".text\nmain: imm -7, 255, 11").unwrap();
        let binary = "00100100000000000010110111111110";
        assert_eq!(x.label_table, label_table([("main", 0, 6..11)]));
        assert_eq!(
            x.instructions,
            vec![inst(0, &["main"], "imm -7 255 11", binary, 12..27)]
        );
        assert_eq!(x.data_memory, vec![]);
        assert_eq!(x.global_symbols, HashSet::new());
    }

    #[test]
    fn instruction_fields_immediate_labels() {
        let x = compile(".text\nmain: nop\na: imm a, c, b\nb: nop\n.data\nc: .zero 1").unwrap();
        let binary = "00010000000000000010000000100000";
        assert_eq!(
            x.label_table,
            label_table([
                ("main", 0, 6..11),
                ("a", 4, 16..18),
                ("b", 8, 31..33),
                ("c", 16, 44..46)
            ])
        );
        assert_eq!(
            x.instructions,
            vec![
                main_nop(12..15),
                inst(4, &["a"], "imm 4 16 8", binary, 19..30),
                inst(8, &["b"], "nop", NOP_BINARY, 34..37),
            ]
        );
        assert_eq!(
            x.data_memory,
            vec![data(16, &["c"], Value::Space(1u8.into()))]
        );
        assert_eq!(x.global_symbols, HashSet::new());
    }

    #[test]
    fn instruction_fields_offsets_aligned() {
        let x = compile(".text\nmain: off 7, -8").unwrap();
        let binary = "01110000000000000000000000001000";
        assert_eq!(x.label_table, label_table([("main", 0, 6..11)]));
        assert_eq!(
            x.instructions,
            vec![inst(0, &["main"], "off 7 -8", binary, 12..21)]
        );
        assert_eq!(x.data_memory, vec![]);
        assert_eq!(x.global_symbols, HashSet::new());
    }

    #[test]
    fn instruction_fields_offsets_aligned_labels() {
        let x = compile(".text\nmain: nop\noff main, main").unwrap();
        let binary = "11000000000000000000000000001111";
        assert_eq!(x.label_table, label_table([("main", 0, 6..11)]));
        assert_eq!(
            x.instructions,
            vec![main_nop(12..15), inst(4, &[], "off -4 -1", binary, 16..30),]
        );
        assert_eq!(x.data_memory, vec![]);
        assert_eq!(x.global_symbols, HashSet::new());

        let x = compile(".text\na: nop\noff main, main\nmain: nop").unwrap();
        let binary = "01000000000000000000000000000001";
        assert_eq!(
            x.label_table,
            label_table([("a", 0, 6..8), ("main", 8, 28..33)])
        );
        assert_eq!(
            x.instructions,
            vec![
                inst(0, &["a"], "nop", NOP_BINARY, 9..12),
                inst(4, &[], "off 4 1", binary, 13..27),
                inst(8, &["main"], "nop", NOP_BINARY, 34..37),
            ]
        );
        assert_eq!(x.data_memory, vec![]);
        assert_eq!(x.global_symbols, HashSet::new());
    }

    #[test]
    fn instruction_fields_offsets_unaligned() {
        let x = compile(".text\nmain: off 6, 7").unwrap();
        let binary = "01100000000000000000000000000111";
        assert_eq!(x.label_table, label_table([("main", 0, 6..11)]));
        assert_eq!(
            x.instructions,
            vec![inst(0, &["main"], "off 6 7", binary, 12..20)]
        );
        assert_eq!(x.data_memory, vec![]);
        assert_eq!(x.global_symbols, HashSet::new());
    }

    #[test]
    fn instruction_fields_offsets_unaligned_labels() {
        let x = compile(".text\nmain: off 1, a\n.data\n.zero 1\na: .zero 1").unwrap();
        let binary = "00010000000000000000000000000100";
        assert_eq!(
            x.label_table,
            label_table([("main", 0, 6..11), ("a", 17, 35..37)])
        );
        assert_eq!(
            x.instructions,
            vec![inst(0, &["main"], "off 1 4", binary, 12..20)]
        );
        assert_eq!(
            x.data_memory,
            vec![
                data(16, &[], Value::Space(1u8.into())),
                data(17, &["a"], Value::Space(1u8.into()))
            ]
        );
        assert_eq!(x.global_symbols, HashSet::new());
    }

    #[test]
    fn instruction_fields_enums() {
        let x = compile(".text\nmain: enum a, b, value, last").unwrap();
        let binary = "01010000000000011111110110000101";
        assert_eq!(x.label_table, label_table([("main", 0, 6..11)]));
        assert_eq!(
            x.instructions,
            vec![inst(0, &["main"], "enum a b value last", binary, 12..34)]
        );
        assert_eq!(x.data_memory, vec![]);
        assert_eq!(x.global_symbols, HashSet::new());
    }

    #[test]
    fn instruction_fields_padding() {
        let x = compile(".text\nmain: pad 15, 4").unwrap();
        let binary = "01100000000000011111010000000100";
        assert_eq!(x.label_table, label_table([("main", 0, 6..11)]));
        assert_eq!(
            x.instructions,
            vec![inst(0, &["main"], "pad 12 4", binary, 12..21)]
        );
        assert_eq!(x.data_memory, vec![]);
        assert_eq!(x.global_symbols, HashSet::new());

        let x = compile(".text\nmain: pad -15, -1").unwrap();
        let binary = "10000000000000011111010000111100";
        assert_eq!(x.label_table, label_table([("main", 0, 6..11)]));
        assert_eq!(
            x.instructions,
            vec![inst(0, &["main"], "pad -16 -4", binary, 12..23)]
        );
        assert_eq!(x.data_memory, vec![]);
        assert_eq!(x.global_symbols, HashSet::new());
    }

    #[test]
    fn kernel_text() {
        let x = compile(".text\nmain: nop\n.ktext\nfoo: nop").unwrap();
        assert_eq!(
            x.label_table,
            label_table([("main", 0, 6..11), ("foo", 32, 23..27)])
        );
        assert_eq!(
            x.instructions,
            vec![
                main_nop(12..15),
                inst(32, &["foo"], "nop", NOP_BINARY, 28..31),
            ]
        );
        assert_eq!(x.data_memory, vec![]);
        assert_eq!(x.global_symbols, HashSet::new());

        let x = compile(".ktext\nfoo: nop\n.text\nmain: nop").unwrap();
        assert_eq!(
            x.label_table,
            label_table([("main", 0, 22..27), ("foo", 32, 7..11)])
        );
        assert_eq!(
            x.instructions,
            vec![
                main_nop(28..31),
                inst(32, &["foo"], "nop", NOP_BINARY, 12..15),
            ]
        );
        assert_eq!(x.data_memory, vec![]);
        assert_eq!(x.global_symbols, HashSet::new());

        let x = compile_arch(
            ".text\nmain: nop\n.ktext\nfoo: nop",
            include_str!("../tests/architecture2.json"),
        )
        .unwrap();
        assert_eq!(
            x.label_table,
            label_table([("main", 32, 6..11), ("foo", 0, 23..27)])
        );
        assert_eq!(
            x.instructions,
            vec![
                inst(0, &["foo"], "nop", NOP_BINARY, 28..31),
                inst(32, &["main"], "nop", NOP_BINARY, 12..15),
            ]
        );
        assert_eq!(x.data_memory, vec![]);
        assert_eq!(x.global_symbols, HashSet::new());
    }

    #[test]
    fn space() {
        let x = compile(".data\n.zero 3\n.zero 1\n.text\nmain: nop").unwrap();
        assert_eq!(x.label_table, label_table([("main", 0, 28..33)]));
        assert_eq!(x.instructions, vec![main_nop(34..37)]);
        assert_eq!(
            x.data_memory,
            vec![
                data(16, &[], Value::Space(3u8.into())),
                data(19, &[], Value::Space(1u8.into())),
            ]
        );
        assert_eq!(x.global_symbols, HashSet::new());
    }

    #[test]
    fn int() {
        let test_cases = [
            ("byte ", 1u8, IntegerType::Byte, 2u64.pow(8) - 128),
            ("half ", 2, IntegerType::HalfWord, 2u64.pow(16) - 128),
            ("word ", 4, IntegerType::Word, 2u64.pow(32) - 128),
            ("dword", 8, IntegerType::DoubleWord, u64::MAX - 127),
        ];
        #[allow(clippy::cast_possible_wrap)]
        for (name, size, r#type, val) in test_cases {
            let bits = usize::from(size * 8);
            // 1 argument
            let x = compile(&format!(".data\na: .{name} 1\n.text\nmain: nop")).unwrap();
            assert_eq!(
                x.label_table,
                label_table([("main", 0, 24..29), ("a", 16, 6..8)])
            );
            assert_eq!(x.instructions, vec![main_nop(30..33)]);
            assert_eq!(
                x.data_memory,
                vec![data(16, &["a"], int_val(1, bits, r#type))]
            );
            assert_eq!(x.global_symbols, HashSet::new());
            // Multiple arguments
            let x = compile(&format!(".data\nb: .{name} -128, 255\n.text\nmain: nop")).unwrap();
            assert_eq!(
                x.label_table,
                label_table([("main", 0, 32..37), ("b", 16, 6..8)])
            );
            assert_eq!(x.instructions, vec![main_nop(38..41)]);
            assert_eq!(
                x.data_memory,
                vec![
                    data(16, &["b"], int_val(val as i64, bits, r#type)),
                    data((16 + size).into(), &[], int_val(255, bits, r#type))
                ]
            );
            assert_eq!(x.global_symbols, HashSet::new());
        }
    }

    #[test]
    fn int_label() {
        let x = compile(".data\na: .byte a, b\nb: .byte main\n.text\nmain: nop").unwrap();
        assert_eq!(
            x.label_table,
            label_table([("main", 0, 40..45), ("a", 16, 6..8), ("b", 18, 20..22)])
        );
        assert_eq!(x.instructions, vec![main_nop(46..49)]);
        assert_eq!(
            x.data_memory,
            vec![
                data(16, &["a"], int_val(16, 8, IntegerType::Byte)),
                data(17, &[], int_val(18, 8, IntegerType::Byte)),
                data(18, &["b"], int_val(0, 8, IntegerType::Byte)),
            ]
        );
        assert_eq!(x.global_symbols, HashSet::new());
    }

    #[test]
    fn calc_reserved_space() {
        let code = ".data\nsize: .byte end-begin\nbegin: .zero 14\nend: .byte 0\n.text\nmain: nop";
        let x = compile(code).unwrap();
        assert_eq!(
            x.label_table,
            label_table([
                ("main", 0, 63..68),
                ("size", 16, 6..11),
                ("begin", 17, 28..34),
                ("end", 31, 44..48),
            ])
        );
        assert_eq!(x.instructions, vec![main_nop(69..72)]);
        assert_eq!(
            x.data_memory,
            vec![
                data(16, &["size"], int_val(14, 8, IntegerType::Byte)),
                data(17, &["begin"], Value::Space(14u8.into())),
                data(31, &["end"], int_val(0, 8, IntegerType::Byte)),
            ]
        );
        assert_eq!(x.global_symbols, HashSet::new());
    }

    #[test]
    fn float() {
        let test_cases = [
            ("float ", 4, FloatType::Float),
            ("double", 8, FloatType::Double),
        ];
        let value = |x, ty| match ty {
            FloatType::Float => Value::Float(x),
            FloatType::Double => Value::Double(x.into()),
        };
        for (name, size, r#type) in test_cases {
            // 1 argument
            let x = compile(&format!(".data\na: .{name} 1\n.text\nmain: nop")).unwrap();
            assert_eq!(
                x.label_table,
                label_table([("main", 0, 25..30), ("a", 16, 6..8)])
            );
            assert_eq!(x.instructions, vec![main_nop(31..34)]);
            assert_eq!(x.data_memory, vec![data(16, &["a"], value(1.0, r#type))]);
            assert_eq!(x.global_symbols, HashSet::new());
            // Multiple arguments
            let x = compile(&format!(".data\nb: .{name} 1, 2\n.text\nmain: nop")).unwrap();
            assert_eq!(
                x.label_table,
                label_table([("main", 0, 28..33), ("b", 16, 6..8)])
            );
            assert_eq!(x.instructions, vec![main_nop(34..37)]);
            assert_eq!(
                x.data_memory,
                vec![
                    data(16, &["b"], value(1.0, r#type)),
                    data((16 + size).try_into().unwrap(), &[], value(2.0, r#type)),
                ]
            );
            assert_eq!(x.global_symbols, HashSet::new());
        }
    }

    #[test]
    fn string() {
        let test_cases = [("string ", true), ("stringn", false)];
        for (name, null_terminated) in test_cases {
            // 1 argument
            let x = compile(&format!(".data\na: .{name} \"a\"\n.text\nmain: nop")).unwrap();
            assert_eq!(
                x.label_table,
                label_table([("main", 0, 28..33), ("a", 16, 6..8)])
            );
            assert_eq!(x.instructions, vec![main_nop(34..37)]);
            let str = |x: &str| Value::String {
                data: x.into(),
                null_terminated,
            };
            assert_eq!(x.data_memory, vec![data(16, &["a"], str("a"))]);
            assert_eq!(x.global_symbols, HashSet::new());
            // Multiple arguments
            let x = compile(&format!(".data\nb: .{name} \"b\", \"0\"\n.text\nmain: nop")).unwrap();
            assert_eq!(
                x.label_table,
                label_table([("main", 0, 33..38), ("b", 16, 6..8)])
            );
            assert_eq!(x.instructions, vec![main_nop(39..42)]);
            assert_eq!(
                x.data_memory,
                vec![
                    data(16, &["b"], str("b")),
                    data(17 + u64::from(null_terminated), &[], str("0")),
                ]
            );
            assert_eq!(x.global_symbols, HashSet::new());
        }
    }

    #[test]
    fn global() {
        // Before definition
        let x = compile(".global main\n.text\nmain: nop").unwrap();
        assert_eq!(x.label_table, label_table([("main", 0, 19..24)]));
        assert_eq!(x.instructions, vec![main_nop(25..28)]);
        assert_eq!(x.data_memory, vec![]);
        assert_eq!(x.global_symbols, HashSet::from(["main".into()]));
        // After definition
        let x = compile(".text\nmain: nop\n.global main").unwrap();
        assert_eq!(x.label_table, label_table([("main", 0, 6..11)]));
        assert_eq!(x.instructions, vec![main_nop(12..15)]);
        assert_eq!(x.data_memory, vec![]);
        assert_eq!(x.global_symbols, HashSet::from(["main".into()]));
        // Multiple arguments
        let x = compile(".text\nmain: nop\ntest: nop\n.global main, test").unwrap();
        assert_eq!(
            x.label_table,
            label_table([("main", 0, 6..11), ("test", 4, 16..21)])
        );
        let nop = inst(4, &["test"], "nop", NOP_BINARY, 22..25);
        assert_eq!(x.instructions, vec![main_nop(12..15), nop]);
        assert_eq!(x.data_memory, vec![]);
        assert_eq!(
            x.global_symbols,
            HashSet::from(["main".into(), "test".into()])
        );
    }

    #[test]
    fn exp_align() {
        for size in [1, 3] {
            let x = compile(&format!(
                ".data\n.zero 1\na: b: .align {size}\n.zero 1\n.text\nmain: nop"
            ))
            .unwrap();
            assert_eq!(
                x.label_table,
                label_table([("main", 0, 43..48), ("a", 17, 14..16), ("b", 17, 17..19)])
            );
            assert_eq!(x.instructions, vec![main_nop(49..52)]);
            let alignment = 2u64.pow(size) - 1;
            assert_eq!(
                x.data_memory,
                vec![
                    data(16, &[], Value::Space(1u8.into())),
                    data(17, &["a", "b"], Value::Padding(alignment.into())),
                    data(17 + alignment, &[], Value::Space(1u8.into()))
                ]
            );
            assert_eq!(x.global_symbols, HashSet::new());
        }
    }

    #[test]
    fn byte_align() {
        for size in [2, 8] {
            let x = compile(&format!(
                ".data\n.zero 1\na: .balign {size}\n.zero 1\n.text\nmain: nop"
            ))
            .unwrap();
            assert_eq!(
                x.label_table,
                label_table([("main", 0, 41..46), ("a", 17, 14..16)])
            );
            assert_eq!(x.instructions, vec![main_nop(47..50)]);
            let alignment = size - 1;
            assert_eq!(
                x.data_memory,
                vec![
                    data(16, &[], Value::Space(1u8.into())),
                    data(17, &["a"], Value::Padding(alignment.into())),
                    data(17 + alignment, &[], Value::Space(1u8.into()))
                ]
            );
            assert_eq!(x.global_symbols, HashSet::new());
        }
    }

    #[test]
    fn align_end() {
        for s in [1, 3] {
            let x = compile(&format!(".data\n.zero 1\n.align {s}\n.text\nmain: nop")).unwrap();
            assert_eq!(x.label_table, label_table([("main", 0, 29..34)]));
            assert_eq!(x.instructions, vec![main_nop(35..38)]);
            let alignment = 2u64.pow(s) - 1;
            assert_eq!(
                x.data_memory,
                vec![
                    data(16, &[], Value::Space(1u8.into())),
                    data(17, &[], Value::Padding(alignment.into())),
                ]
            );
            assert_eq!(x.global_symbols, HashSet::new());
        }
    }

    #[test]
    fn already_aligned() {
        for size in [0, 1, 2] {
            let x = compile(&format!(
                ".data\n.zero 4\na: .align {size}\n.zero 1\n.text\nmain: nop"
            ))
            .unwrap();
            assert_eq!(
                x.label_table,
                label_table([("main", 0, 40..45), ("a", 20, 14..16)])
            );
            assert_eq!(x.instructions, vec![main_nop(46..49)]);
            assert_eq!(
                x.data_memory,
                vec![
                    data(16, &[], Value::Space(4u8.into())),
                    data(20, &[], Value::Space(1u8.into()))
                ]
            );
            assert_eq!(x.global_symbols, HashSet::new());
        }
    }

    #[test]
    fn align_decrease() {
        let x =
            compile(".data\n.zero 4\na: .align 3\nb: .align 2\n.zero 1\n.text\nmain: nop").unwrap();
        assert_eq!(
            x.label_table,
            label_table([("main", 0, 52..57), ("a", 20, 14..16), ("b", 24, 26..28)])
        );
        assert_eq!(x.instructions, vec![main_nop(58..61)]);
        assert_eq!(
            x.data_memory,
            vec![
                data(16, &[], Value::Space(4u8.into())),
                data(20, &["a"], Value::Padding(4u8.into())),
                data(24, &[], Value::Space(1u8.into()))
            ]
        );
        assert_eq!(x.global_symbols, HashSet::new());
    }

    #[test]
    fn kernel_data() {
        let x = compile(".text\nmain: nop\n.kdata\n.zero 1\n.data\n.zero 2").unwrap();
        let data_mem = vec![
            data(16, &[], Value::Space(2u8.into())),
            data(48, &[], Value::Space(1u8.into())),
        ];
        assert_eq!(x.label_table, label_table([("main", 0, 6..11)]));
        assert_eq!(x.instructions, vec![main_nop(12..15)]);
        assert_eq!(x.data_memory, data_mem);
        assert_eq!(x.global_symbols, HashSet::new());

        let x = compile(".text\nmain: nop\n.data\n.zero 2\n.kdata\n.zero 1").unwrap();
        assert_eq!(x.label_table, label_table([("main", 0, 6..11)]));
        assert_eq!(x.instructions, vec![main_nop(12..15)]);
        assert_eq!(x.data_memory, data_mem);
        assert_eq!(x.global_symbols, HashSet::new());

        let x = compile_arch(
            ".text\nmain: nop\n.data\n.zero 2\n.kdata\n.zero 1",
            include_str!("../tests/architecture2.json"),
        )
        .unwrap();
        assert_eq!(x.label_table, label_table([("main", 32, 6..11)]));
        assert_eq!(
            x.instructions,
            vec![inst(32, &["main"], "nop", NOP_BINARY, 12..15)]
        );
        assert_eq!(
            x.data_memory,
            vec![
                data(16, &[], Value::Space(1u8.into())),
                data(48, &[], Value::Space(2u8.into()))
            ]
        );
        assert_eq!(x.global_symbols, HashSet::new());
    }

    #[test]
    fn read_pc() {
        let x = compile(".text\nmain: nop\nimm ., 0, 0\n.data\n.word .").unwrap();
        assert_eq!(x.label_table, label_table([("main", 0, 6..11)]));
        let binary = "00010000000000000000000000000000";
        assert_eq!(
            x.instructions,
            vec![main_nop(12..15), inst(4, &[], "imm 4 0 0", binary, 16..27)]
        );
        assert_eq!(
            x.data_memory,
            vec![data(16, &[], int_val(16, 32, IntegerType::Word)),]
        );
        assert_eq!(x.global_symbols, HashSet::new());
    }

    #[test]
    fn unallowed_statement() {
        assert_eq!(
            compile(".data\nnop\n.text\nmain: nop"),
            Err(ErrorKind::UnallowedStatementType {
                section: Some((DirectiveSegment::Data, 0..5)),
                found: DirectiveSegment::Code,
            }
            .add_span(6..9)),
        );
        assert_eq!(
            compile(".kdata\nnop\n.text\nmain: nop"),
            Err(ErrorKind::UnallowedStatementType {
                section: Some((DirectiveSegment::KernelData, 0..6)),
                found: DirectiveSegment::Code,
            }
            .add_span(7..10)),
        );
        assert_eq!(
            compile(".text\nmain: nop\n.byte 1"),
            Err(ErrorKind::UnallowedStatementType {
                section: Some((DirectiveSegment::Code, 0..5)),
                found: DirectiveSegment::Data,
            }
            .add_span(16..23)),
        );
        assert_eq!(
            compile(".ktext\nmain: nop\n.byte 1"),
            Err(ErrorKind::UnallowedStatementType {
                section: Some((DirectiveSegment::KernelCode, 0..6)),
                found: DirectiveSegment::Data,
            }
            .add_span(17..24)),
        );
        assert_eq!(
            compile("nop\n.text\nmain: nop"),
            Err(ErrorKind::UnallowedStatementType {
                section: None,
                found: DirectiveSegment::Code,
            }
            .add_span(0..3)),
        );
        assert_eq!(
            compile(".byte 1\n.text\nmain: nop"),
            Err(ErrorKind::UnallowedStatementType {
                section: None,
                found: DirectiveSegment::Data,
            }
            .add_span(0..7)),
        );
    }

    #[test]
    fn unknown_directive() {
        assert_eq!(
            compile(".test\n.text\nmain: nop"),
            Err(ErrorKind::UnknownDirective(".test".into()).add_span(0..5)),
        );
    }

    #[test]
    fn unknown_instruction() {
        assert_eq!(
            compile(".text\nmain: test"),
            Err(ErrorKind::UnknownInstruction("test".into()).add_span(12..16)),
        );
    }

    #[test]
    fn unknown_label() {
        assert_eq!(
            compile(".text\nmain: imm 0, 0, test"),
            Err(ErrorKind::UnknownLabel("test".into()).add_span(22..26)),
        );
    }

    #[test]
    fn unknown_register_file() {
        let arch = include_str!("../tests/architecture2.json");
        assert_eq!(
            compile_arch(".text\nmain: ctrl pc", arch),
            Err(ErrorKind::UnknownRegisterFile(RegisterType::Ctrl).add_span(17..19)),
        );
        assert_eq!(
            compile_arch(".text\nmain: float ft0", arch),
            Err(
                ErrorKind::UnknownRegisterFile(RegisterType::Float(FloatType::Float))
                    .add_span(18..21)
            ),
        );
        assert_eq!(
            compile_arch(".text\nmain: double ft0", arch),
            Err(
                ErrorKind::UnknownRegisterFile(RegisterType::Float(FloatType::Double))
                    .add_span(19..22)
            ),
        );
    }

    #[test]
    fn unknown_register() {
        assert_eq!(
            compile(".text\nmain: reg x0, x0, ft1, ft2"),
            Err(ErrorKind::UnknownRegister {
                name: "x0".into(),
                file: RegisterType::Ctrl,
            }
            .add_span(16..18)),
        );
        assert_eq!(
            compile(".text\nmain: reg 2, x0, ft1, ft2"),
            Err(ErrorKind::UnknownRegister {
                name: "2".into(),
                file: RegisterType::Ctrl,
            }
            .add_span(16..17)),
        );
        // Register names should be case sensitive
        assert_eq!(
            compile(".text\nmain: reg pc, x0, ft1, ft2"),
            Err(ErrorKind::UnknownRegister {
                name: "pc".into(),
                file: RegisterType::Ctrl,
            }
            .add_span(16..18)),
        );
        assert_eq!(
            compile(".text\nmain: reg PC, PC, ft1, ft2"),
            Err(ErrorKind::UnknownRegister {
                name: "PC".into(),
                file: RegisterType::Int,
            }
            .add_span(20..22)),
        );
        assert_eq!(
            compile(".text\nmain: reg PC, x0, x0, ft2"),
            Err(ErrorKind::UnknownRegister {
                name: "x0".into(),
                file: RegisterType::Float(FloatType::Float),
            }
            .add_span(24..26)),
        );
        assert_eq!(
            compile(".text\nmain: reg PC, x0, FD1, ft2"),
            Err(ErrorKind::UnknownRegister {
                name: "FD1".into(),
                file: RegisterType::Float(FloatType::Float),
            }
            .add_span(24..27)),
        );
        assert_eq!(
            compile(".text\nmain: reg PC, x0, ft1, fs2"),
            Err(ErrorKind::UnknownRegister {
                name: "fs2".into(),
                file: RegisterType::Float(FloatType::Double),
            }
            .add_span(29..32)),
        );
    }

    #[test]
    fn unknown_enum_value() {
        assert_eq!(
            compile(".text\nmain: enum a, b, value, wrong"),
            Err(ErrorKind::UnknownEnumValue {
                value: "wrong".into(),
                enum_name: "test".into(),
            }
            .add_span(30..35)),
        );
        assert_eq!(
            compile(".text\nmain: enum a, b, value, a"),
            Err(ErrorKind::UnknownEnumValue {
                value: "a".into(),
                enum_name: "test".into(),
            }
            .add_span(30..31)),
        );
        assert_eq!(
            compile(".text\nmain: enum a, c, value, last"),
            Err(ErrorKind::UnknownEnumValue {
                value: "c".into(),
                enum_name: "enum1".into(),
            }
            .add_span(20..21)),
        );
        // Enum names should be case sensitive
        assert_eq!(
            compile(".text\nmain: enum a, b, value, OTHER"),
            Err(ErrorKind::UnknownEnumValue {
                value: "OTHER".into(),
                enum_name: "test".into(),
            }
            .add_span(30..35)),
        );
    }

    #[test]
    fn section_args() {
        assert_eq!(
            compile(".data 1\n.text\nmain: nop"),
            Err(ErrorKind::IncorrectDirectiveArgumentNumber {
                expected: ArgumentNumber::new(0, false),
                found: 1
            }
            .add_span(6..7)),
        );
    }

    #[test]
    fn padding_args_number() {
        for directive in ["zero  ", "align ", "balign"] {
            assert_eq!(
                compile(&format!(".data\n.{directive}\n.text\nmain: nop")),
                Err(ErrorKind::IncorrectDirectiveArgumentNumber {
                    expected: ArgumentNumber::new(1, false),
                    found: 0
                }
                .add_span(13..14)),
                "{directive}"
            );
            assert_eq!(
                compile(&format!(".data\n.{directive} 1, 2\n.text\nmain: nop")),
                Err(ErrorKind::IncorrectDirectiveArgumentNumber {
                    expected: ArgumentNumber::new(1, false),
                    found: 2
                }
                .add_span(14..18)),
                "{directive}"
            );
        }
    }

    #[test]
    fn padding_negative() {
        for directive in ["zero  ", "align ", "balign"] {
            assert_eq!(
                compile(&format!(".data\n.{directive} -1\n.text\nmain: nop")),
                Err(ErrorKind::UnallowedNegativeValue((-1).into()).add_span(14..16)),
                "{directive}"
            );
        }
    }

    #[test]
    fn int_args_type() {
        for directive in [
            "zero  ", "align ", "balign", "byte  ", "half  ", "word  ", "dword ",
        ] {
            assert_eq!(
                compile(&format!(".data\n.{directive} \"a\"\n.text\nmain: nop")),
                Err(ErrorKind::IncorrectArgumentType {
                    expected: ArgumentType::Expression,
                    found: ArgumentType::String
                }
                .add_span(14..17)),
                "{directive}"
            );
            assert_eq!(
                compile(&format!(".data\n.{directive} 1.0\n.text\nmain: nop")),
                Err(ErrorKind::UnallowedFloat.add_span(14..17)),
                "{directive}"
            );
        }
        assert_eq!(
            compile(".text\nmain: imm 0, 0, 1.0"),
            Err(ErrorKind::UnallowedFloat.add_span(22..25)),
        );
        assert_eq!(
            compile(".text\nmain: reg PC, 0+2, ft1, ft2"),
            Err(ErrorKind::IncorrectArgumentType {
                expected: ArgumentType::RegisterName,
                found: ArgumentType::Expression,
            }
            .add_span(20..23)),
        );
        assert_eq!(
            compile(".text\nmain: enum a, b, value, 0"),
            Err(ErrorKind::IncorrectArgumentType {
                expected: ArgumentType::Identifier,
                found: ArgumentType::Expression,
            }
            .add_span(30..31)),
        );
    }

    #[test]
    fn data_no_args() {
        for directive in ["byte  ", "float ", "string"] {
            assert_eq!(
                compile(&format!(".data\n.{directive}\n.text\nmain: nop")),
                Err(ErrorKind::IncorrectDirectiveArgumentNumber {
                    expected: ArgumentNumber::new(1, true),
                    found: 0
                }
                .add_span(13..14)),
                "{directive}"
            );
        }
    }

    #[test]
    fn data_unaligned() {
        for (directive, size) in [
            ("half  ", 2u8),
            ("word  ", 4),
            ("dword ", 8),
            ("float ", 4),
            ("double", 8),
        ] {
            assert_eq!(
                compile(&format!(".data\n.byte 0\n.{directive} 1\n.text\nmain: nop")),
                Err(ErrorKind::DataUnaligned {
                    address: 17u8.into(),
                    alignment: size.into(),
                }
                .add_span(22..23)),
                "{directive}",
            );
        }
    }

    #[test]
    fn int_args_size() {
        let range = |x: std::ops::Range<i32>| x.start.into()..=(x.end - 1).into();

        // Data directives
        assert_eq!(
            compile(".data\n.byte 256\n.text\nmain: nop"),
            Err(ErrorKind::IntegerOutOfRange(256.into(), range(-128..256)).add_span(12..15)),
        );
        assert_eq!(
            compile(".data\n.byte -129\n.text\nmain: nop"),
            Err(ErrorKind::IntegerOutOfRange((-129).into(), range(-128..256)).add_span(12..16)),
        );
        assert_eq!(
            compile(".data\n.half 65536\n.text\nmain: nop"),
            Err(ErrorKind::IntegerOutOfRange(65536.into(), range(-32768..65536)).add_span(12..17)),
        );
        // Instruction arguments
        assert_eq!(
            compile(".text\nmain: imm 8, 0, 0"),
            Err(ErrorKind::IntegerOutOfRange(8.into(), range(-8..8)).add_span(16..17)),
        );
        assert_eq!(
            compile(".text\nmain: imm -9, 0, 0"),
            Err(ErrorKind::IntegerOutOfRange((-9).into(), range(-8..8)).add_span(16..18)),
        );
        assert_eq!(
            compile(".text\nmain: imm 0, 256, 0"),
            Err(ErrorKind::IntegerOutOfRange(256.into(), range(0..256)).add_span(19..22)),
        );
        assert_eq!(
            compile(".text\nmain: imm 0, -1, 0"),
            Err(ErrorKind::IntegerOutOfRange((-1).into(), range(0..256)).add_span(19..21)),
        );
        assert_eq!(
            compile(".text\nmain: imm 0, 0, 20"),
            Err(ErrorKind::IntegerOutOfRange(20.into(), range(0..16)).add_span(22..24)),
        );
    }

    #[test]
    fn float_args_type() {
        assert_eq!(
            compile(".data\n.float \"a\"\n.text\nmain: nop"),
            Err(ErrorKind::IncorrectArgumentType {
                expected: ArgumentType::Expression,
                found: ArgumentType::String
            }
            .add_span(13..16)),
        );
    }

    #[test]
    fn string_args_type() {
        assert_eq!(
            compile(".data\n.string 1\n.text\nmain: nop"),
            Err(ErrorKind::IncorrectArgumentType {
                expected: ArgumentType::String,
                found: ArgumentType::Expression
            }
            .add_span(14..15)),
        );
    }

    #[test]
    fn global_args_type() {
        assert_eq!(
            compile(".global \"test\"\n.text\nmain: nop"),
            Err(ErrorKind::IncorrectArgumentType {
                expected: ArgumentType::Identifier,
                found: ArgumentType::String
            }
            .add_span(8..14)),
        );
        assert_eq!(
            compile(".global 123\n.text\nmain: nop"),
            Err(ErrorKind::IncorrectArgumentType {
                expected: ArgumentType::Identifier,
                found: ArgumentType::Expression
            }
            .add_span(8..11)),
        );
    }

    #[test]
    fn incorrect_instruction_syntax() {
        let assert = |err, syntaxes: &[&str], expected_span: Span| match err {
            Err(ErrorData { span, kind }) => match *kind {
                ErrorKind::IncorrectInstructionSyntax(s) => {
                    assert_eq!(span, expected_span.into());
                    assert_eq!(s.into_iter().map(|x| x.0).collect::<Vec<_>>(), syntaxes);
                }
                x => panic!(
                    "Incorrect result, expected ErrorKind::IncorrectInstructionSyntax: {x:?}"
                ),
            },
            x => panic!("Incorrect result, expected Err variant: {x:?}"),
        };
        assert(compile(".text\nmain: nop 1"), &["nop"], 16..17);
        assert(
            compile(".text\nmain: multi &, 1"),
            &["multi imm4", "multi $", "multi imm5"],
            18..22,
        );
    }

    #[test]
    fn expr_eval() {
        assert_eq!(
            compile(".data\n.byte 1/0\n.text\nmain: nop"),
            Err(ErrorKind::DivisionBy0.add_span(14..15)),
        );
        assert_eq!(
            compile(".text\nmain: imm 0, 0, 1/0"),
            Err(ErrorKind::DivisionBy0.add_span(24..25)),
        );
        assert_eq!(
            compile(".data\n.float ~1.0\n.text\nmain: nop"),
            Err(
                ErrorKind::UnallowedFloatOperation(error::OperationKind::Complement)
                    .add_span(13..14)
            ),
        );
        for (op, c) in [
            (error::OperationKind::BitwiseOR, '|'),
            (error::OperationKind::BitwiseAND, '&'),
            (error::OperationKind::BitwiseXOR, '^'),
        ] {
            assert_eq!(
                compile(&format!(".data\n.float 1.0 {c} 2.0\n.text\nmain: nop")),
                Err(ErrorKind::UnallowedFloatOperation(op).add_span(17..18)),
            );
        }
    }

    #[test]
    fn missing_main() {
        assert_eq!(
            compile(".text\nnop"),
            Err(ErrorKind::MissingMainLabel.add_span(9..10)),
        );
        assert_eq!(
            compile(".text\nnop\n.data"),
            Err(ErrorKind::MissingMainLabel.add_span(9..10)),
        );
    }

    #[test]
    fn main_outside_code() {
        assert_eq!(
            compile(".data\nmain: .byte 1\n.text\nnop"),
            Err(ErrorKind::MainOutsideCode.add_span(6..11)),
        );
        assert_eq!(
            compile(".kdata\nmain: .byte 1\n.text\nnop"),
            Err(ErrorKind::MainOutsideCode.add_span(7..12)),
        );
        assert_eq!(
            compile(".ktext\nmain: nop\n.text\nnop"),
            Err(ErrorKind::MainOutsideCode.add_span(7..12)),
        );
    }

    #[test]
    fn duplicate_label() {
        assert_eq!(
            compile(".text\nmain: nop\nmain: nop"),
            Err(ErrorKind::DuplicateLabel("main".into(), Some(6..11)).add_span(16..21)),
        );
        assert_eq!(
            compile(".text\nmain: nop\nlabel:\nlabel: nop"),
            Err(ErrorKind::DuplicateLabel("label".into(), Some(16..22)).add_span(23..29)),
        );
    }

    #[test]
    fn section_full() {
        // Instructions
        assert_eq!(
            compile(".text\nmain: nop\nnop\nnop\nnop\nimm 0, 0, 0"),
            Err(ErrorKind::MemorySectionFull("Instructions").add_span(28..39)),
        );
        assert_eq!(
            compile(".text\nmain: nop\nnop\nnop\nnop2"),
            Err(ErrorKind::MemorySectionFull("Instructions").add_span(24..28)),
        );
        // Data directives
        for (directive, span) in [
            ("zero 5", 21..22),
            ("word 0\n.byte 0", 29..30),
            ("dword 0", 22..23),
            ("double 0", 23..24),
            ("string \"1234\"", 23..29),
            ("stringn \"1234\"\n.stringn \"5\"", 40..43),
            ("balign 64\n.byte 0", 15..25),
        ] {
            assert_eq!(
                compile(&format!(".data\n.zero 12\n.{directive}\n.text\nmain: nop")),
                Err(ErrorKind::MemorySectionFull("Data").add_span(&span)),
                "{directive}",
            );
        }
    }

    #[test]
    fn no_kernel() {
        let compile = |src| compile_arch(src, include_str!("../tests/architecture_no_kernel.json"));
        assert_eq!(
            compile(".ktext\nfoo: nop\n.text\nmain: nop"),
            Err(ErrorKind::MemorySectionFull("KernelInstructions").add_span(12..15)),
        );
        assert_eq!(
            compile(".kdata\n.zero 1\n.text\nmain: nop"),
            Err(ErrorKind::MemorySectionFull("KernelData").add_span(13..14)),
        );
    }

    #[test]
    fn library_labels() {
        let src = ".data\n.word test\n.text\nmain: nop";
        for val in [3u8, 11, 27] {
            let labels = HashMap::from([("test".into(), val.into())]);
            let x = compile_with(src, &BigUint::ZERO, labels.clone(), false).unwrap();
            let mut labels = LabelTable::from(labels);
            labels
                .insert("main".into(), Label::new(BigUint::ZERO, 23..28))
                .unwrap();
            assert_eq!(x.label_table, labels);
            assert_eq!(x.instructions, vec![main_nop(29..32)]);
            let val = val.into();
            assert_eq!(
                x.data_memory,
                vec![data(16, &[], int_val(val, 32, IntegerType::Word))]
            );
            assert_eq!(x.global_symbols, HashSet::new());
        }
    }

    #[test]
    fn library_offset() {
        let src = ".text\nmain: nop";
        for val in [5u64, 8, 11] {
            let x = compile_with(src, &val.into(), HashMap::new(), false).unwrap();
            assert_eq!(x.label_table, label_table([("main", val, 6..11)]));
            let nop = inst(val, &["main"], "nop", NOP_BINARY, 12..15);
            assert_eq!(x.instructions, vec![nop]);
            assert_eq!(x.data_memory, vec![]);
            assert_eq!(x.global_symbols, HashSet::new());
        }
    }

    #[test]
    fn compile_library() {
        let x = compile_with(".text\ntest: nop", &BigUint::ZERO, HashMap::new(), true).unwrap();
        assert_eq!(x.label_table, label_table([("test", 0, 6..11)]));
        let nop = inst(0, &["test"], "nop", NOP_BINARY, 12..15);
        assert_eq!(x.instructions, vec![nop]);
        assert_eq!(x.data_memory, vec![]);
        assert_eq!(x.global_symbols, HashSet::new());
    }

    #[test]
    fn main_in_library() {
        assert_eq!(
            compile_with(".text\nmain: nop", &BigUint::ZERO, HashMap::new(), true),
            Err(ErrorKind::MainInLibrary.add_span(6..11))
        );
        let labels = HashMap::from([("main".into(), 4u8.into())]);
        assert_eq!(
            compile_with(".text\ntest: nop", &BigUint::ZERO, labels, true),
            Err(ErrorKind::MainInLibrary.add_span(0..0))
        );
    }
}
