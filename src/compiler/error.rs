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

use ariadne::{Color, Config, Fmt, Label, Report, ReportKind, Source};
use num_bigint::{BigInt, BigUint};

use std::fmt;
use std::ops::RangeInclusive;
use std::{fmt::Write as _, io::Write as _};

use crate::architecture::{
    Architecture, DirectiveAction, DirectiveSegment, FloatType, RegisterType,
};
use crate::parser::ParseError;
use crate::span::{Span, SpanList, Spanned};

use super::{ArgumentNumber, LabelTable, PseudoinstructionError, PseudoinstructionErrorKind};

mod utils;
use utils::{ArgNum, Colored, DisplayList};

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
    IncorrectInstructionSyntax(Vec<(String, ParseError)>),
    DuplicateLabel(String, Option<Span>),
    MissingMainLabel,
    MainInLibrary,
    MainOutsideCode,
    IntegerOutOfRange(BigInt, RangeInclusive<BigInt>),
    MemorySectionFull(&'static str),
    DataUnaligned {
        address: BigUint,
        alignment: BigUint,
    },
    UnallowedNegativeValue(BigInt),
    IncorrectDirectiveArgumentNumber {
        expected: ArgumentNumber,
        found: usize,
    },
    IncorrectArgumentType {
        expected: ArgumentType,
        found: ArgumentType,
    },
    DivisionBy0,
    UnallowedFloat,
    UnallowedLabel,
    UnallowedFloatOperation(OperationKind),
    UnallowedStatementType {
        section: Option<Spanned<DirectiveSegment>>,
        found: DirectiveSegment,
    },
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
    /// Adds a span to the error kind, promoting it to an [`Data`]
    ///
    /// # Parameters
    ///
    /// * `span`: location in the assembly code that caused the error
    #[must_use]
    pub fn add_span(self, span: impl Into<SpanList>) -> Data {
        Data {
            span: span.into(),
            kind: Box::new(self),
        }
    }

    /// Gets the numeric error code of this error
    const fn error_code(&self) -> u32 {
        match self {
            Self::UnknownDirective(..) => 1,
            Self::UnknownInstruction(..) => 2,
            Self::UnknownLabel(..) => 3,
            Self::UnknownRegisterFile(..) => 4,
            Self::UnknownRegister { .. } => 5,
            Self::IncorrectInstructionSyntax(..) => 6,
            Self::DuplicateLabel(..) => 7,
            Self::MissingMainLabel => 8,
            Self::MainInLibrary => 22,
            Self::MainOutsideCode => 9,
            Self::IntegerOutOfRange(..) => 10,
            Self::MemorySectionFull(..) => 11,
            Self::DataUnaligned { .. } => 12,
            Self::UnallowedNegativeValue(..) => 13,
            Self::IncorrectDirectiveArgumentNumber { .. } => 14,
            Self::IncorrectArgumentType { .. } => 15,
            Self::DivisionBy0 => 16,
            Self::UnallowedFloat => 17,
            Self::UnallowedLabel => 21,
            Self::UnallowedFloatOperation(..) => 18,
            Self::UnallowedStatementType { .. } => 19,
            Self::PseudoinstructionError { .. } => 20,
        }
    }

    /// Gets a note with extra information about the error if available
    fn note(&self) -> Option<String> {
        Some(match self {
            Self::IntegerOutOfRange(_, bounds) => {
                format!("Allowed range is [{}, {}]", bounds.start(), bounds.end())
            }
            Self::IncorrectInstructionSyntax(errs) => {
                let mut res = "Allowed formats:".to_string();
                for (syntax, _) in errs {
                    write!(res, "\n{syntax}").expect("The write macro can't fail for `String`s");
                }
                res
            }
            Self::DuplicateLabel(_, None) => "Label also defined in library".into(),
            Self::UnallowedStatementType { section: None, .. } => {
                "No section previously started".into()
            }
            _ => return None,
        })
    }

    /// Gets a hint about how to fix the error if available
    fn hint(&self, arch: &Architecture, labels: &LabelTable, color: bool) -> Option<String> {
        Some(match self {
            Self::UnknownDirective(s) => {
                let names = utils::get_similar(s, arch.directives.iter().map(|d| d.name));
                format!("Did you mean {}?", DisplayList::non_empty(names, color)?)
            }
            Self::UnknownInstruction(s) => {
                let inst_names = arch.instructions.iter().map(|i| i.name);
                let pseudo_names = arch.pseudoinstructions.iter().map(|i| i.name);
                let names = utils::get_similar(s, inst_names.chain(pseudo_names));
                format!("Did you mean {}?", DisplayList::non_empty(names, color)?)
            }
            Self::UnknownLabel(s) => {
                let names = utils::get_similar(s, labels.iter().map(|(n, _)| n.as_str()));
                format!("Did you mean {}?", DisplayList::non_empty(names, color)?)
            }
            Self::UnknownRegister { name, file } => {
                let files = arch.find_reg_files(*file);
                let registers = files.flat_map(|file| {
                    file.elements
                        .iter()
                        .flat_map(|reg| reg.name.iter().copied())
                });
                let names = utils::get_similar(name, registers);
                format!("Did you mean {}?", DisplayList::non_empty(names, color)?)
            }
            Self::DuplicateLabel(.., Some(_)) => "Consider renaming either of the labels".into(),
            Self::DuplicateLabel(.., None) | Self::MainInLibrary => {
                "Consider renaming the label".into()
            }
            Self::MainOutsideCode => "Consider moving the label to a user instruction".into(),
            Self::IncorrectDirectiveArgumentNumber { expected, found } => {
                let expected = expected.amount;
                let (msg, n) = if expected > *found {
                    ("adding the missing", expected - found)
                } else {
                    ("removing the extra", found - expected)
                };
                let color = color.then_some(Color::Green);
                format!("Consider {msg} {}", ArgNum(n, color))
            }
            Self::UnallowedStatementType { found, .. } => {
                let names: Vec<_> = arch.directives.iter()
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

    /// Gets the label text describing the error
    fn label(&self, arch: &Architecture, color: bool) -> String {
        let red = color.then_some(Color::Red);
        match self {
            Self::UnknownDirective(..) => "Unknown directive".into(),
            Self::UnknownInstruction(..) => "Unknown instruction".into(),
            Self::UnknownLabel(..) => "Unknown label".into(),
            Self::UnknownRegisterFile(..) => "Unknown register file".into(),
            Self::UnknownRegister { .. } => "Unknown register".into(),
            Self::IncorrectInstructionSyntax(..) => "Incorrect syntax".into(),
            Self::DuplicateLabel(..) => "Duplicate label".into(),
            Self::MissingMainLabel => {
                let main = Colored(arch.main_label(), color.then_some(Color::Green));
                format!("Consider adding a label called {main} to an instruction")
            }
            Self::MainOutsideCode | Self::MainInLibrary => "Label defined here".into(),
            Self::IntegerOutOfRange(val, _) | Self::UnallowedNegativeValue(val) => {
                format!("This expression has value {}", Colored(val, red))
            }
            Self::MemorySectionFull(..) => "This element doesn't fit in the available space".into(),
            Self::DataUnaligned { .. } => "This value isn't aligned".into(),
            Self::IncorrectDirectiveArgumentNumber { found, .. } => {
                format!("This directive has {}", ArgNum(*found, red))
            }
            Self::IncorrectArgumentType { found, .. } => {
                format!("This argument has type {}", Colored(found, red))
            }
            Self::DivisionBy0 => format!("This expression has value {}", Colored(0, red)),
            Self::UnallowedFloat | Self::UnallowedLabel => "This value can't be used".into(),
            Self::UnallowedFloatOperation(..) => "This operation can't be performed".into(),
            Self::UnallowedStatementType { .. } => {
                "This statement can't be used in the current section".into()
            }
            Self::PseudoinstructionError { .. } => "While expanding this pseudoinstruction".into(),
        }
    }

    /// Gets a list of extra context labels related to the error
    fn context(&self) -> Vec<(&Span, &'static str)> {
        match self {
            Self::DuplicateLabel(_, Some(span)) => {
                vec![(span, "Label also defined here")]
            }
            Self::UnallowedStatementType {
                section: Some(section),
                ..
            } => {
                vec![(&section.1, "Section previously started here")]
            }
            _ => Vec::new(),
        }
    }

    /// Gets the error message of this error
    fn msg(&self, arch: &Architecture, color: bool) -> String {
        let red = color.then_some(Color::Red);
        let blue = color.then_some(Color::BrightBlue);
        let main = Colored(arch.main_label(), red);
        match self {
            Self::UnknownDirective(s) => {
                format!("Directive {} isn't defined", Colored(s, red))
            }
            Self::UnknownInstruction(s) => {
                format!("Instruction {} isn't defined", Colored(s, red))
            }
            Self::UnknownLabel(s) => format!("Label {} isn't defined", Colored(s, red)),
            Self::UnknownRegisterFile(s) => {
                format!("Register file of type {} isn't defined", Colored(s, red))
            }
            Self::UnknownRegister { name, file } => format!(
                "Register {} isn't defined in file type {}",
                Colored(name, red),
                Colored(file, blue)
            ),
            Self::IncorrectInstructionSyntax(..) => "Incorrect instruction syntax".into(),
            Self::DuplicateLabel(s, _) => {
                format!("Label {} is already defined", Colored(s, red))
            }
            Self::MissingMainLabel => format!("Main label {main} not found"),
            Self::MainInLibrary => format!("Main label {main} can't be used in libraries"),
            Self::MainOutsideCode => {
                format!("Main label {main} defined outside of the text segment")
            }
            Self::IntegerOutOfRange(val, _) => format!(
                "Value {} is outside of the valid range of the field",
                Colored(val, red)
            ),
            Self::MemorySectionFull(name) => {
                format!("{name} memory segment is full")
            }
            Self::DataUnaligned { address, alignment } => format!(
                "Data at address {} isn't aligned to size {} nor word size {}",
                Colored(format!("{address:#X}"), red),
                Colored(alignment, blue),
                Colored(arch.word_size().div_ceil(8), blue),
            ),
            Self::UnallowedNegativeValue(_) => "Negative values aren't allowed here".into(),
            Self::IncorrectDirectiveArgumentNumber { expected, found } => format!(
                "Incorrect amount of arguments, expected {}{} but found {}",
                if expected.at_least { "at least " } else { "" },
                Colored(expected.amount, blue),
                Colored(found, red),
            ),
            Self::IncorrectArgumentType { expected, found } => format!(
                "Incorrect argument type, expected {} but found {}",
                Colored(expected, blue),
                Colored(found, red),
            ),
            Self::DivisionBy0 => "Can't divide by 0".into(),
            Self::UnallowedFloat => "Can't use floating point values in integer expressions".into(),
            Self::UnallowedLabel => "Can't use labels in literal expressions".into(),
            Self::UnallowedFloatOperation(op) => format!(
                "Can't perform the {} operation with floating point numbers",
                Colored(op, red),
            ),
            Self::UnallowedStatementType { section, found } => {
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
            Self::PseudoinstructionError { name, .. } => {
                let name = Colored(name, red);
                format!("Error while expanding pseudoinstruction {name}")
            }
        }
    }
}

impl SpanList {
    fn format(&self, filename: &str, src: &str, mut buffer: &mut Vec<u8>, color: bool) {
        let (filename, src) = self.source.as_ref().map_or((filename, src), |origin| {
            origin.span.format(filename, src, buffer, color);
            ("<pseudoinstruction expansion>", origin.code.as_str())
        });
        writeln!(&mut buffer).expect("Writing to an in-memory vector can't fail");
        let kind = ReportKind::Custom("Note", Color::BrightBlue);
        Report::build(kind, (filename, self.span.clone()))
            .with_config(Config::default().with_color(color))
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

impl<'arch> crate::RenderError for Error<'arch> {
    fn format(self, filename: &str, src: &str, mut buffer: &mut Vec<u8>, color: bool) {
        let (filename_user, src_user) = (filename, src);
        let source = self.error.span.source.as_ref();
        let (filename, src) = source.map_or((filename, src), |origin| {
            ("<pseudoinstruction expansion>", origin.code.as_str())
        });
        let note_color = color.then_some(Color::BrightBlue);
        let mut report = Report::build(ReportKind::Error, (filename, self.error.span.span.clone()))
            .with_config(Config::default().with_color(color))
            .with_code(format!("E{:02}", self.error.kind.error_code()))
            .with_message(self.error.kind.msg(self.arch, color))
            .with_label(
                Label::new((filename, self.error.span.span.clone()))
                    .with_message(self.error.kind.label(self.arch, color))
                    .with_color(Color::Red),
            )
            .with_labels(self.error.kind.context().into_iter().map(|label| {
                Label::new((filename, label.0.clone()))
                    .with_message(format!("{} {}", "Note:".fg(note_color), label.1))
                    .with_color(Color::BrightBlue)
                    .with_order(10)
            }));
        if let Some(note) = self.error.kind.note() {
            report.set_note(note);
        }
        if let Some(hint) = self.error.kind.hint(self.arch, &self.label_table, color) {
            report.set_help(hint);
        }

        report
            .finish()
            .write((filename, Source::from(src)), &mut buffer)
            .expect("Writing to an in-memory vector shouldn't fail");

        match *self.error.kind {
            Kind::IncorrectInstructionSyntax(errs) => {
                for (syntax, err) in errs {
                    writeln!(
                        &mut buffer,
                        "\nThe syntax `{syntax}` failed with the following reason:"
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

        if let Some(origin) = self.error.span.source {
            origin.span.format(filename_user, src_user, buffer, color);
        }
    }
}

impl PseudoinstructionErrorKind {
    /// Gets the label text describing the error
    const fn label(&self) -> &'static str {
        match self {
            Self::UnknownFieldName(..) => "Unknown field name",
            Self::UnknownFieldNumber { .. } => "Field index out of bounds",
            Self::UnknownFieldType(..) => "Unknown field type",
            Self::EmptyBitRange => "Empty bit range",
            Self::BitRangeOutOfBounds { .. } => "Bit range out of bounds",
            Self::EvaluationError(..) => "While evaluating this code",
            Self::ParseError { .. } => "While parsing this instruction",
        }
    }

    /// Gets a note with extra information about the error if available
    fn note(&self, color: bool) -> Option<String> {
        Some(match self {
            Self::UnknownFieldNumber { size, .. } => {
                format!(
                    "The pseudoinstruction has {}",
                    ArgNum(*size, color.then_some(Color::BrightBlue))
                )
            }
            _ => return None,
        })
    }

    /// Gets the error message of this error
    fn msg(&self, color: bool) -> String {
        let red = color.then_some(Color::Red);
        match self {
            Self::UnknownFieldName(s) => format!("Field {} isn't defined", Colored(s, red)),
            Self::UnknownFieldNumber { idx, .. } => {
                format!("Field index {} is out of bounds", Colored(idx, red))
            }
            Self::UnknownFieldType(s) => format!("Unknown field type {}", Colored(s, red)),
            Self::EmptyBitRange => "Bit range is empty".into(),
            Self::BitRangeOutOfBounds { upper_bound, msb } => format!(
                "Bit range is of bounds, upper bound is {} but the MSB is {}",
                Colored(upper_bound, red),
                Colored(msb, color.then_some(Color::BrightBlue)),
            ),
            Self::EvaluationError(s) => format!("Error evaluating JS code:\n{s}"),
            Self::ParseError(_) => "Error parsing instruction".into(),
        }
    }
}

impl crate::RenderError for PseudoinstructionError {
    fn format(self, _: &str, _: &str, mut buffer: &mut Vec<u8>, color: bool) {
        static FILENAME: &str = "<pseudoinstruction expansion>";
        let src = &self.definition;
        let mut report = Report::build(ReportKind::Error, (FILENAME, self.span.clone()))
            .with_config(Config::default().with_color(color))
            .with_message(self.kind.msg(color))
            .with_label(
                Label::new((FILENAME, self.span.clone()))
                    .with_message(self.kind.label())
                    .with_color(Color::Red),
            );
        if let Some(note) = self.kind.note(color) {
            report.set_note(note);
        }
        report
            .finish()
            .write((FILENAME, Source::from(src)), &mut buffer)
            .expect("Writing to an in-memory vector shouldn't fail");
        writeln!(&mut buffer).expect("Writing to an in-memory vector can't fail");
        if let PseudoinstructionErrorKind::ParseError(err) = self.kind {
            err.format(FILENAME, &src[self.span], buffer, color);
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
