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

//! Module containing the definition of the compiler errors
//!
//! The main type is [`Error`]

use ariadne::{Color, Config, Fmt, IndexType, Label, Report, ReportKind, Source};
use num_bigint::{BigInt, BigUint};

use std::collections::HashMap;
use std::fmt;
use std::ops::RangeInclusive;
use std::{fmt::Write as _, io::Write as _};

use crate::architecture::{
    Architecture, DirectiveAction, DirectiveSegment, FloatType, RegisterType,
};
use crate::error_rendering as utils;
use crate::error_rendering::{ArgNum, Colored, DisplayList};
use crate::parser::ParseError;
use crate::span::{Span, SpanList, Spanned};

use super::{ArgumentNumber, LabelTable, PseudoinstructionError, PseudoinstructionErrorKind};

/// Type of arguments for directives/instructions
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArgumentType {
    String,
    Expression,
    RegisterName,
    Identifier,
}

/// Unsupported operations for floating point numbers
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OperationKind {
    Complement,
    BitwiseOR,
    BitwiseAND,
    BitwiseXOR,
}

/// Error type
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Kind {
    UnknownDirective(String),
    UnknownInstruction(String),
    UnknownLabel(String),
    UnknownRegisterFile(RegisterType),
    UnknownRegister {
        name: String,
        file: RegisterType,
    },
    UnknownEnumType(String),
    UnknownEnumValue {
        value: String,
        enum_name: String,
    },
    IncorrectInstructionSyntax(Vec<(String, ParseError)>),
    IncorrectDirectiveArgumentNumber {
        expected: ArgumentNumber,
        found: usize,
    },
    IncorrectArgumentType {
        expected: ArgumentType,
        found: ArgumentType,
    },
    DuplicateLabel(String, Option<Span>),
    MissingMainLabel,
    MainInLibrary,
    MainOutsideCode,
    MemorySectionFull(&'static str),
    DataUnaligned {
        address: BigUint,
        alignment: BigUint,
    },
    UnallowedStatementType {
        section: Option<Spanned<DirectiveSegment>>,
        found: DirectiveSegment,
    },
    UnallowedLabel,
    UnallowedFloat(Span),
    UnallowedFloatOperation(OperationKind, Span),
    UnallowedNegativeValue(BigInt),
    IntegerOutOfRange(BigInt, RangeInclusive<BigInt>),
    DivisionBy0,
    RemainderWith0,
    PseudoinstructionError {
        name: String,
        error: Box<PseudoinstructionError>,
    },
}

/// Information about the error
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Data {
    /// Location in the assembly that produced the error
    pub span: SpanList,
    /// Type of the error
    pub kind: Box<Kind>,
}

/// Compiler error type
#[derive(Debug, Clone)]
pub struct Error<'arch> {
    /// Architecture used during the compilation
    pub arch: &'arch Architecture<'arch>,
    /// Labels defined
    pub label_table: LabelTable,
    /// Information about the error
    pub error: Data,
}

impl fmt::Display for ArgumentType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Self as fmt::Debug>::fmt(self, f)
    }
}

impl fmt::Display for OperationKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Complement => write!(f, "complement"),
            Self::BitwiseOR => write!(f, "bitwise OR"),
            Self::BitwiseAND => write!(f, "bitwise AND"),
            Self::BitwiseXOR => write!(f, "bitwise XOR"),
        }
    }
}

impl fmt::Display for RegisterType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Ctrl => write!(f, "Control"),
            Self::Int => write!(f, "Integer"),
            Self::Float(FloatType::Float) => write!(f, "SingleFloatingPoint"),
            Self::Float(FloatType::Double) => write!(f, "DoubleFloatingPoint"),
        }
    }
}

impl fmt::Display for DirectiveSegment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", if self.is_code() { "Text" } else { "Data" })
    }
}

impl Kind {
    /// Adds a span to the error kind, promoting it to a [`Data`]
    ///
    /// # Parameters
    ///
    /// * `span`: location in the assembly code that caused the error
    #[must_use]
    pub(crate) fn add_span(self, span: impl Into<SpanList>) -> Data {
        Data {
            span: span.into(),
            kind: Box::new(self),
        }
    }
}

/// Trait to get different types of data from an error, such as the error message, label message,
/// error code, or notes/hints
#[allow(unused_variables)]
pub trait Info {
    /// Gets the numeric error code of the error
    #[must_use]
    fn code(&self) -> u32 {
        0
    }

    /// Gets a note with extra information about the error if available
    ///
    /// # Parameters
    ///
    /// * `color`: whether the message should be formatted (`true`) or plain text (`false`)
    #[must_use]
    fn note(&self, color: bool) -> Option<String> {
        None
    }

    /// Gets a hint about how to fix the error if available
    ///
    /// # Parameters
    ///
    /// * `color`: whether the message should be formatted (`true`) or plain text (`false`)
    #[must_use]
    fn hint(&self, color: bool) -> Option<String> {
        None
    }

    /// Gets a list of extra context labels related to the error
    ///
    /// # Parameters
    ///
    /// * `color`: whether the message should be formatted (`true`) or plain text (`false`)
    #[must_use]
    fn context(&self, color: bool) -> Vec<(&Span, &'static str)> {
        vec![]
    }

    /// Gets the label text describing the error
    ///
    /// # Parameters
    ///
    /// * `color`: whether the message should be formatted (`true`) or plain text (`false`)
    #[must_use]
    fn label(&self, color: bool) -> String;

    /// Gets the error message of the error
    ///
    /// # Parameters
    ///
    /// * `color`: whether the message should be formatted (`true`) or plain text (`false`)
    #[must_use]
    fn msg(&self, color: bool) -> String;
}

impl Info for Error<'_> {
    fn code(&self) -> u32 {
        match self.error.kind.as_ref() {
            Kind::UnknownDirective(..) => 1,
            Kind::UnknownInstruction(..) => 2,
            Kind::UnknownLabel(..) => 3,
            Kind::UnknownRegisterFile(..) => 4,
            Kind::UnknownRegister { .. } => 5,
            Kind::UnknownEnumType { .. } => 6,
            Kind::UnknownEnumValue { .. } => 7,
            Kind::IncorrectInstructionSyntax(..) => 8,
            Kind::IncorrectDirectiveArgumentNumber { .. } => 9,
            Kind::IncorrectArgumentType { .. } => 10,
            Kind::DuplicateLabel(..) => 11,
            Kind::MissingMainLabel => 12,
            Kind::MainInLibrary => 13,
            Kind::MainOutsideCode => 14,
            Kind::MemorySectionFull(..) => 15,
            Kind::DataUnaligned { .. } => 16,
            Kind::UnallowedStatementType { .. } => 17,
            Kind::UnallowedLabel => 18,
            Kind::UnallowedFloat(..) => 19,
            Kind::UnallowedFloatOperation(..) => 20,
            Kind::UnallowedNegativeValue(..) => 21,
            Kind::IntegerOutOfRange(..) => 22,
            Kind::DivisionBy0 => 23,
            Kind::RemainderWith0 => 24,
            Kind::PseudoinstructionError { .. } => 25,
        }
    }

    fn note(&self, _: bool) -> Option<String> {
        Some(match self.error.kind.as_ref() {
            Kind::IntegerOutOfRange(_, bounds) => {
                format!("Allowed range is [{}, {}]", bounds.start(), bounds.end())
            }
            Kind::IncorrectInstructionSyntax(errs) => {
                let mut res = "Allowed formats:".to_string();
                for (syntax, _) in errs {
                    write!(res, "\n{syntax}").expect("The write macro can't fail for `String`s");
                }
                res
            }
            Kind::DuplicateLabel(_, None) => "Label also defined in library".into(),
            Kind::UnallowedStatementType { section: None, .. } => {
                "No section previously started".into()
            }
            _ => return None,
        })
    }

    fn hint(&self, color: bool) -> Option<String> {
        Some(match self.error.kind.as_ref() {
            Kind::UnknownDirective(s) => {
                let names = utils::get_similar(s, self.arch.directives.iter().map(|d| d.name));
                format!("Did you mean {}?", DisplayList::non_empty(names, color)?)
            }
            Kind::UnknownInstruction(s) => {
                let inst_names = self.arch.instructions.iter().map(|i| i.name);
                let pseudo_names = self.arch.pseudoinstructions.iter().map(|i| i.name);
                let names = utils::get_similar(s, inst_names.chain(pseudo_names));
                format!("Did you mean {}?", DisplayList::non_empty(names, color)?)
            }
            Kind::UnknownLabel(s) => {
                let names = utils::get_similar(s, self.label_table.iter().map(|(n, _)| n.as_str()));
                format!("Did you mean {}?", DisplayList::non_empty(names, color)?)
            }
            Kind::UnknownRegister { name, file } => {
                let files = self.arch.find_reg_files(*file);
                let registers = files.flat_map(|file| {
                    file.elements
                        .iter()
                        .flat_map(|reg| reg.name.iter().copied())
                });
                let names = utils::get_similar(name, registers);
                format!("Did you mean {}?", DisplayList::non_empty(names, color)?)
            }
            Kind::UnknownEnumValue { value, enum_name } => {
                let enums = &self.arch.enums;
                let default = HashMap::default();
                let enum_def = enums.get(enum_name.as_str()).unwrap_or(&default);
                let names = utils::get_similar(value, enum_def.keys().copied());
                format!("Did you mean {}?", DisplayList::non_empty(names, color)?)
            }
            Kind::DuplicateLabel(.., Some(_)) => "Consider renaming either of the labels".into(),
            Kind::DuplicateLabel(.., None) | Kind::MainInLibrary => {
                "Consider renaming the label".into()
            }
            Kind::MainOutsideCode => "Consider moving the label to a user instruction".into(),
            Kind::IncorrectDirectiveArgumentNumber { expected, found } => {
                let expected = expected.amount;
                let (msg, n) = if expected > *found {
                    ("adding the missing", expected - found)
                } else {
                    ("removing the extra", found - expected)
                };
                let color = color.then_some(Color::Green);
                format!("Consider {msg} {}", ArgNum(n, color))
            }
            Kind::UnallowedStatementType { found, .. } => {
                let names: Vec<_> = self.arch.directives.iter()
                    .filter(|dir| matches!(dir.action, DirectiveAction::Segment(s) if s.is_code() == found.is_code()))
                    .map(|dir| dir.name)
                    .collect();
                let section_type = Colored(found, color.then_some(Color::BrightBlue));
                format!(
                    "Consider changing the section to {}{}{}",
                    section_type,
                    if names.is_empty() { "" } else { ", using " },
                    DisplayList::new(names, color)
                )
            }
            _ => return None,
        })
    }

    fn context(&self, _: bool) -> Vec<(&Span, &'static str)> {
        match self.error.kind.as_ref() {
            Kind::DuplicateLabel(_, Some(span)) => {
                vec![(span, "Label also defined here")]
            }
            Kind::UnallowedStatementType {
                section: Some(section),
                ..
            } => {
                vec![(&section.1, "Section previously started here")]
            }
            Kind::UnallowedFloat(span) if *span != self.error.span.span => {
                vec![(span, "Expression evaluates to a float due to this")]
            }
            Kind::UnallowedFloatOperation(_, span) => {
                vec![(span, "Operands are converted to floats due to this")]
            }
            _ => Vec::new(),
        }
    }

    fn label(&self, color: bool) -> String {
        let red = color.then_some(Color::Red);
        match self.error.kind.as_ref() {
            Kind::UnknownDirective(..) => "Unknown directive".into(),
            Kind::UnknownInstruction(..) => "Unknown instruction".into(),
            Kind::UnknownLabel(..) => "Unknown label".into(),
            Kind::UnknownRegisterFile(..) => "Unknown register file".into(),
            Kind::UnknownRegister { .. } => "Unknown register".into(),
            Kind::UnknownEnumType { .. } => "Unknown enum type".into(),
            Kind::UnknownEnumValue { .. } => "Unknown enum value".into(),
            Kind::IncorrectInstructionSyntax(..) => "Incorrect syntax".into(),
            Kind::IncorrectDirectiveArgumentNumber { found, .. } => {
                format!("This directive has {}", ArgNum(*found, red))
            }
            Kind::IncorrectArgumentType { found, .. } => {
                format!("This argument has type {}", Colored(found, red))
            }
            Kind::DuplicateLabel(..) => "Duplicate label".into(),
            Kind::MissingMainLabel => {
                let main = Colored(self.arch.main_label(), color.then_some(Color::Green));
                format!("Consider adding a label called {main} to an instruction")
            }
            Kind::MainInLibrary | Kind::MainOutsideCode => "Label defined here".into(),
            Kind::MemorySectionFull(..) => "This element doesn't fit in the available space".into(),
            Kind::DataUnaligned { .. } => "This value isn't aligned".into(),
            Kind::UnallowedStatementType { .. } => {
                "This statement can't be used in the current section".into()
            }
            Kind::UnallowedLabel | Kind::UnallowedFloat(..) => "This value can't be used".into(),
            Kind::UnallowedFloatOperation(..) => "This operation can't be performed".into(),
            Kind::UnallowedNegativeValue(val) | Kind::IntegerOutOfRange(val, _) => {
                format!("This expression has value {}", Colored(val, red))
            }
            Kind::DivisionBy0 | Kind::RemainderWith0 => format!("This expression has value {}", Colored(0, red)),
            Kind::PseudoinstructionError { .. } => "While expanding this pseudoinstruction".into(),
        }
    }

    fn msg(&self, color: bool) -> String {
        let red = color.then_some(Color::Red);
        let blue = color.then_some(Color::BrightBlue);
        let main = Colored(self.arch.main_label(), red);
        match self.error.kind.as_ref() {
            Kind::UnknownDirective(s) => {
                format!("Directive {} isn't defined", Colored(s, red))
            }
            Kind::UnknownInstruction(s) => {
                format!("Instruction {} isn't defined", Colored(s, red))
            }
            Kind::UnknownLabel(s) => format!("Label {} isn't defined", Colored(s, red)),
            Kind::UnknownRegisterFile(s) => {
                format!("Register file of type {} isn't defined", Colored(s, red))
            }
            Kind::UnknownRegister { name, file } => format!(
                "Register {} isn't defined in file type {}",
                Colored(name, red),
                Colored(file, blue)
            ),
            Kind::UnknownEnumType(t) => format!("Enum type {} isn't defined", Colored(t, red)),
            Kind::UnknownEnumValue { value, enum_name } => format!(
                "Value {} isn't defined in enum type {}",
                Colored(value, red),
                Colored(enum_name, blue)
            ),
            Kind::IncorrectInstructionSyntax(..) => "Incorrect instruction syntax".into(),
            Kind::IncorrectDirectiveArgumentNumber { expected, found } => format!(
                "Incorrect amount of arguments, expected {}{} but found {}",
                if expected.at_least { "at least " } else { "" },
                Colored(expected.amount, blue),
                Colored(found, red),
            ),
            Kind::IncorrectArgumentType { expected, found } => format!(
                "Incorrect argument type, expected {} but found {}",
                Colored(expected, blue),
                Colored(found, red),
            ),
            Kind::DuplicateLabel(s, _) => {
                format!("Label {} is already defined", Colored(s, red))
            }
            Kind::MissingMainLabel => format!("Main label {main} not found"),
            Kind::MainInLibrary => format!("Main label {main} can't be used in libraries"),
            Kind::MainOutsideCode => {
                format!("Main label {main} defined outside of the text segment")
            }
            Kind::MemorySectionFull(name) => {
                format!("{name} memory segment is full")
            }
            Kind::DataUnaligned { address, alignment } => format!(
                "Data at address {} isn't aligned to size {} nor word size {}",
                Colored(format!("{address:#X}"), red),
                Colored(alignment, blue),
                Colored(self.arch.word_size().div_ceil(8), blue),
            ),
            Kind::UnallowedStatementType { section, found } => {
                let found = if found.is_code() {
                    "instruction"
                } else {
                    "data directive"
                };
                let found = Colored(found, red);
                let section = section
                    .as_ref()
                    .map_or_else(|| "None".into(), |(s, _)| s.to_string());
                let section = Colored(section, blue);
                format!("Can't use {found} statements while in section {section}",)
            }
            Kind::UnallowedLabel => "Can't use labels in literal expressions".into(),
            Kind::UnallowedFloat(..) => {
                "Can't use floating point values in integer expressions".into()
            }
            Kind::UnallowedFloatOperation(op, ..) => format!(
                "Can't perform the {} operation with floating point numbers",
                Colored(op, red),
            ),
            Kind::UnallowedNegativeValue(_) => "Negative values aren't allowed here".into(),
            Kind::IntegerOutOfRange(val, _) => format!(
                "Value {} is outside of the valid range of the field",
                Colored(val, red)
            ),
            Kind::DivisionBy0 => "Can't divide by 0".into(),
            Kind::RemainderWith0 => "Can't take the remainder of a division by 0".into(),
            Kind::PseudoinstructionError { name, .. } => {
                let name = Colored(name, red);
                format!("Error while expanding pseudoinstruction {name}")
            }
        }
    }
}

impl crate::RenderError for SpanList {
    fn format(&self, filename: &str, src: &str, mut buffer: &mut Vec<u8>, color: bool) {
        let (filename, src) = self.source.as_ref().map_or((filename, src), |origin| {
            origin.span.format(filename, src, buffer, color);
            ("<pseudoinstruction expansion>", origin.code.as_str())
        });
        writeln!(&mut buffer).expect("Writing to an in-memory vector can't fail");
        let kind_color = if color {
            Color::BrightBlue
        } else {
            Color::Primary
        };
        let kind = ReportKind::Custom("Note", kind_color);
        let config = Config::default()
            .with_color(color)
            .with_index_type(IndexType::Byte);
        Report::build(kind, (filename, self.span.clone()))
            .with_config(config)
            .with_message("Instruction generated from this pseudoinstruction")
            .with_label(
                Label::new((filename, self.span.clone()))
                    .with_message("Generated by this pseudoinstruction")
                    .with_color(Color::BrightBlue),
            )
            .finish()
            .write((filename, Source::from(src)), &mut buffer)
            .expect("Writing to an in-memory vector shouldn't fail");
    }
}

impl crate::RenderError for Error<'_> {
    fn format(&self, filename: &str, src: &str, mut buffer: &mut Vec<u8>, color: bool) {
        let (filename_user, src_user) = (filename, src);
        let source = self.error.span.source.as_ref();
        let (filename, src) = source.map_or((filename, src), |origin| {
            ("<pseudoinstruction expansion>", origin.code.as_str())
        });
        let blue = color.then_some(Color::BrightBlue);
        let config = Config::default()
            .with_color(color)
            .with_index_type(IndexType::Byte);
        let mut report = Report::build(ReportKind::Error, (filename, self.error.span.span.clone()))
            .with_config(config)
            .with_code(format!("E{:02}", self.code()))
            .with_message(self.msg(color))
            .with_label(
                Label::new((filename, self.error.span.span.clone()))
                    .with_message(self.label(color))
                    .with_color(Color::Red),
            )
            .with_labels(self.context(color).into_iter().map(|label| {
                Label::new((filename, label.0.clone()))
                    .with_message(format!("{} {}", "Note:".fg(blue), label.1))
                    .with_color(Color::BrightBlue)
                    .with_order(10)
            }));
        if let Some(note) = self.note(color) {
            report.set_note(note);
        }
        if let Some(hint) = self.hint(color) {
            report.set_help(hint);
        }

        report
            .finish()
            .write((filename, Source::from(src)), &mut buffer)
            .expect("Writing to an in-memory vector shouldn't fail");

        match self.error.kind.as_ref() {
            Kind::IncorrectInstructionSyntax(errs) => {
                for (syntax, err) in errs {
                    writeln!(
                        &mut buffer,
                        "\nThe syntax {} failed with the following reason:",
                        Colored(syntax, blue)
                    )
                    .expect("Writing to an in-memory vector can't fail");
                    err.format(filename, src, buffer, color);
                }
            }
            Kind::PseudoinstructionError { error, .. } => {
                writeln!(&mut buffer).expect("Writing to an in-memory vector can't fail");
                error.format(filename, src, buffer, color);
            }
            _ => {}
        }

        if let Some(origin) = &self.error.span.source {
            origin.span.format(filename_user, src_user, buffer, color);
        }
    }
}

impl Info for PseudoinstructionError {
    fn note(&self, color: bool) -> Option<String> {
        use PseudoinstructionErrorKind as Kind;
        Some(match &self.kind {
            Kind::UnknownFieldNumber { size, .. } => {
                format!(
                    "The pseudoinstruction has {}",
                    ArgNum(*size, color.then_some(Color::BrightBlue))
                )
            }
            _ => return None,
        })
    }

    fn label(&self, _: bool) -> String {
        use PseudoinstructionErrorKind as Kind;
        match &self.kind {
            Kind::UnknownFieldName(..) => "Unknown field name",
            Kind::UnknownFieldNumber { .. } => "Field index out of bounds",
            Kind::UnknownFieldType(..) => "Unknown field type",
            Kind::EmptyBitRange => "Empty bit range",
            Kind::BitRangeOutOfBounds { .. } => "Bit range out of bounds",
            Kind::EvaluationError(..) => "While evaluating this code",
            Kind::ParseError { .. } => "While parsing this instruction",
        }
        .into()
    }

    fn msg(&self, color: bool) -> String {
        use PseudoinstructionErrorKind as Kind;
        let red = color.then_some(Color::Red);
        match &self.kind {
            Kind::UnknownFieldName(s) => format!("Field {} isn't defined", Colored(s, red)),
            Kind::UnknownFieldNumber { idx, .. } => {
                format!("Field index {} is out of bounds", Colored(idx, red))
            }
            Kind::UnknownFieldType(s) => format!("Unknown field type {}", Colored(s, red)),
            Kind::EmptyBitRange => "Bit range is empty".into(),
            Kind::BitRangeOutOfBounds { upper_bound, msb } => format!(
                "Bit range is of bounds, upper bound is {} but the MSB is {}",
                Colored(upper_bound, red),
                Colored(msb, color.then_some(Color::BrightBlue)),
            ),
            Kind::EvaluationError(s) => format!("Error evaluating JS code:\n{s}"),
            Kind::ParseError(_) => "Error parsing instruction".into(),
        }
    }
}

impl crate::RenderError for PseudoinstructionError {
    fn format(&self, _: &str, _: &str, mut buffer: &mut Vec<u8>, color: bool) {
        static FILENAME: &str = "<pseudoinstruction expansion>";
        let src = &self.definition;
        let config = Config::default()
            .with_color(color)
            .with_index_type(IndexType::Byte);
        let mut report = Report::build(ReportKind::Error, (FILENAME, self.span.clone()))
            .with_config(config)
            .with_message(self.msg(color))
            .with_label(
                Label::new((FILENAME, self.span.clone()))
                    .with_message(self.label(color))
                    .with_color(Color::Red),
            );
        if let Some(note) = self.note(color) {
            report.set_note(note);
        }
        report
            .finish()
            .write((FILENAME, Source::from(src)), &mut buffer)
            .expect("Writing to an in-memory vector shouldn't fail");
        writeln!(&mut buffer).expect("Writing to an in-memory vector can't fail");
        if let PseudoinstructionErrorKind::ParseError(err) = &self.kind {
            err.format(FILENAME, &src[self.span.clone()], buffer, color);
        }
    }
}

/// Trait for promoting an error [`Kind`] wrapped in a [`Result`] to an [`Data`]
pub(crate) trait SpannedErr {
    /// Type wrapped in the Ok variant
    type T;

    /// Adds a span to the error kind, promoting it to an [`Data`]
    ///
    /// # Parameters
    ///
    /// * `span`: location in the assembly code that caused the error
    fn add_span(self, span: impl Into<SpanList>) -> Result<Self::T, Data>;
}

impl<T> SpannedErr for Result<T, Kind> {
    type T = T;
    fn add_span(self, span: impl Into<SpanList>) -> Result<T, Data> {
        self.map_err(|e| e.add_span(span))
    }
}
