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

use crate::architecture::{DirectiveSegment, FloatType, RegisterType};
use crate::parser::ParseError;
use crate::span::{Span, Spanned};

use super::{ArgumentNumber, PseudoinstructionError, PseudoinstructionErrorKind};

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
    UnknownRegisterBank(RegisterType),
    UnknownRegister {
        name: String,
        bank: RegisterType,
    },
    IncorrectInstructionSyntax(Vec<(String, ParseError)>),
    DuplicateLabel(String, Option<Span>),
    MissingMainLabel(String),
    MainInLibrary(String),
    MainOutsideCode(String),
    IntegerOutOfRange(BigInt, RangeInclusive<BigInt>),
    MemorySectionFull(&'static str),
    DataUnaligned {
        address: BigUint,
        alignment: BigUint,
        word_size: usize,
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

/// Compiler error type
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Error {
    /// Location in the assembly that produced the error
    pub span: Span,
    /// Type of the error
    pub kind: Box<Kind>,
}

macro_rules! plural {
    ($x:expr) => {
        if $x != 1 {
            "s"
        } else {
            ""
        }
    };
}

impl Kind {
    /// Adds a span to the error kind, promoting it to an [`Error`]
    ///
    /// # Parameters
    ///
    /// * `span`: location in the assembly code that caused the error
    #[must_use]
    pub fn add_span(self, span: &Span) -> Error {
        let span = span.start..span.end;
        Error {
            span,
            kind: Box::new(self),
        }
    }

    /// Gets the numeric error code of this error
    const fn error_code(&self) -> u32 {
        match self {
            Self::UnknownDirective(..) => 1,
            Self::UnknownInstruction(..) => 2,
            Self::UnknownLabel(..) => 3,
            Self::UnknownRegisterBank(..) => 4,
            Self::UnknownRegister { .. } => 5,
            Self::IncorrectInstructionSyntax(..) => 6,
            Self::DuplicateLabel(..) => 7,
            Self::MissingMainLabel(..) => 8,
            Self::MainInLibrary(..) => 22,
            Self::MainOutsideCode(..) => 9,
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
            _ => return None,
        })
    }

    /// Gets a hint about how to fix the error if available
    fn hint(&self) -> Option<String> {
        Some(match self {
            Self::DuplicateLabel(.., Some(_)) => "Consider renaming either of the labels".into(),
            Self::DuplicateLabel(.., None) | Self::MainInLibrary(..) => {
                "Consider renaming the label".into()
            }
            Self::MainOutsideCode(..) => "Consider moving the label to a user instruction".into(),
            Self::IncorrectDirectiveArgumentNumber { expected, found } => {
                let expected = expected.amount;
                let (msg, n) = if expected > *found {
                    ("adding the missing", expected - found)
                } else {
                    ("removing the extra", found - expected)
                };
                let n_str = if n == 1 {
                    String::new()
                } else {
                    format!(" {n}")
                };
                format!("Consider {msg}{n_str} argument{}", plural!(n))
            }
            // TODO: Maybe add hint for required directive name?
            Self::UnallowedStatementType { found, .. } => {
                format!(
                    "Consider changing the section to `{}`",
                    if found.is_code() { "code" } else { "data" }
                )
            }
            _ => return None,
        })
    }

    /// Gets the label text describing the error
    fn label(&self) -> String {
        match self {
            Self::UnknownDirective(..) => "Unknown directive".into(),
            Self::UnknownInstruction(..) => "Unknown instruction".into(),
            Self::UnknownLabel(..) => "Unknown label".into(),
            // TODO: this error should be detected at architecture creattion
            Self::UnknownRegisterBank(..) => "TODO: unknown register bank".into(),
            Self::UnknownRegister { .. } => "Unknown register".into(),
            Self::IncorrectInstructionSyntax(..) => "Incorrect syntax".into(),
            Self::DuplicateLabel(..) => "Duplicate label".into(),
            Self::MissingMainLabel(main) => {
                format!("Consider adding a label called `{main}` to an instruction")
            }
            Self::MainOutsideCode(..) | Self::MainInLibrary(..) => "Label defined here".into(),
            Self::IntegerOutOfRange(val, _) | Self::UnallowedNegativeValue(val) => {
                format!("This expression has value {val}")
            }
            Self::MemorySectionFull(..) => "This element doesn't fit in the available space".into(),
            Self::DataUnaligned { .. } => "This value isn't aligned".into(),
            Self::IncorrectDirectiveArgumentNumber { found, .. } => {
                format!("This directive has {found} argument{}", plural!(*found))
            }
            Self::IncorrectArgumentType { found, .. } => {
                format!("This argument has type `{found:?}`")
            }
            Self::DivisionBy0 => "This expression has value 0".into(),
            Self::UnallowedFloat | Self::UnallowedLabel => "This value can't be used".into(),
            Self::UnallowedFloatOperation(..) => "This operation can't be performed".into(),
            Self::UnallowedStatementType { .. } => {
                "This statement can't be used in the current section".into()
            }
            Self::PseudoinstructionError { .. } => "While evaluating this pseudoinstruction".into(),
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
}

impl fmt::Display for OperationKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Complement => write!(f, "complement (`~`)"),
            Self::BitwiseOR => write!(f, "bitwise OR (`|`)"),
            Self::BitwiseAND => write!(f, "bitwise AND (`&`)"),
            Self::BitwiseXOR => write!(f, "bitwise XOR (`^`)"),
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

impl fmt::Display for Kind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::UnknownDirective(s) => write!(f, "Directive `{s}` isn't defined"),
            Self::UnknownInstruction(s) => write!(f, "Instruction `{s}` isn't defined"),
            Self::UnknownLabel(s) => write!(f, "Label `{s}` isn't defined"),
            Self::UnknownRegisterBank(s) => write!(f, "Register bank of type {s} isn't defined"),
            Self::UnknownRegister { name, bank } => {
                write!(f, "Register `{name}` isn't defined in bank type {bank}")
            }
            Self::IncorrectInstructionSyntax(..) => write!(f, "Incorrect instruction syntax"),
            Self::DuplicateLabel(s, _) => write!(f, "Label `{s}` is already defined"),
            Self::MissingMainLabel(s) => write!(f, "Main label `{s}` not found"),
            Self::MainInLibrary(s) => write!(f, "Main label `{s}` can't be used in libraries"),
            Self::MainOutsideCode(s) => {
                write!(f, "Main label `{s}` defined outside of the text segment")
            }
            Self::IntegerOutOfRange(val, _) => {
                write!(f, "Value `{val}` is outside of the valid range of the field")
            }
            Self::MemorySectionFull(name) => write!(f, "{name} memory segment is full"),
            Self::DataUnaligned { address, alignment, word_size } => write!(
                f,
                "Data at address {address:#X} isn't aligned to size {alignment} nor word size {word_size}"
            ),
            Self::UnallowedNegativeValue(_) => write!(f, "Negative values aren't allowed"),
            Self::IncorrectDirectiveArgumentNumber { expected, found } => write!(
                f,
                "Incorrect amount of arguments, expected {}{} but found {found}",
                if expected.at_least { "at least " } else { "" },
                expected.amount
            ),
            Self::IncorrectArgumentType { expected, found } => write!(
                f,
                "Incorrect argument type, expected `{expected:?}` but found `{found:?}`"
            ),
            Self::DivisionBy0 => write!(f, "Can't divide by 0"),
            Self::UnallowedFloat => {
                write!(f, "Can't use floating point values in integer expressions")
            }
            Self::UnallowedLabel => {
                write!(f, "Can't use labels in literal expressions")
            }
            Self::UnallowedFloatOperation(op) => write!(
                f,
                "Can't perform the {op} operation with floating point numbers"
            ),
            Self::UnallowedStatementType { section, found } => {
                write!(
                    f,
                    "Can't use `{}` statements while in section `{}`",
                    if found.is_code() {"instruction"} else {"data directive"},
                    match section.as_ref().map(|(s, _)| s.is_code()) {
                        Some(false) => "data",
                        Some(true) => "code",
                        None => "none",
                    }
                )
            }
            Self::PseudoinstructionError {name, ..} => write!(f, "Error while evaluating pseudoinstruction `{name}`"),
        }
    }
}

impl crate::RenderError for Error {
    fn format(self, filename: &str, src: &str, mut buffer: &mut Vec<u8>, color: bool) {
        let note_color = color.then_some(Color::BrightBlue);
        let mut report = Report::build(ReportKind::Error, (filename, self.span.clone()))
            .with_config(Config::default().with_color(color))
            .with_code(format!("E{:02}", self.kind.error_code()))
            .with_message(self.kind.to_string())
            .with_label(
                Label::new((filename, self.span))
                    .with_message(self.kind.label())
                    .with_color(Color::Red),
            )
            .with_labels(self.kind.context().into_iter().map(|label| {
                Label::new((filename, label.0.clone()))
                    .with_message(format!("{} {}", "Note:".fg(note_color), label.1))
                    .with_color(Color::BrightBlue)
                    .with_order(10)
            }));
        if let Some(note) = self.kind.note() {
            report.set_note(note);
        }
        if let Some(hint) = self.kind.hint() {
            report.set_help(hint);
        }

        report
            .finish()
            .write((filename, Source::from(src)), &mut buffer)
            .expect("Writing to an in-memory vector shouldn't fail");

        match *self.kind {
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
    }
}

impl PseudoinstructionErrorKind {
    /// Gets the label text describing the error
    fn label(&self) -> &'static str {
        match self {
            Self::UnknownFieldName(..) => "Unknown field name",
            Self::UnknownFieldNumber(..) => "Field index out of bounds",
            Self::UnknownFieldType(..) => "Unknown field type",
            Self::EmptyBitRange => "Empty bit range",
            Self::BitRangeOutOfBounds { .. } => "Bit range out of bounds",
            Self::EvaluationError(..) => "While evaluating this code",
            Self::ParseError { .. } => todo!(),
        }
    }
}

impl fmt::Display for PseudoinstructionErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::UnknownFieldName(s) => write!(f, "Field `{s}` isn't defined"),
            Self::UnknownFieldNumber(x) => write!(f, "Field index `{x}` is out of bounds"),
            Self::UnknownFieldType(s) => write!(f, "Unknown field type `{s}`"),
            Self::EmptyBitRange => write!(f, "Bit range is empty"),
            Self::BitRangeOutOfBounds { upper_bound, msb } => write!(
                f,
                "Bit range is of bounds, upper bound is {upper_bound} but the MSB is {msb}"
            ),
            Self::EvaluationError(s) => write!(f, "Error evaluating JS code:\n{s}"),
            Self::ParseError { .. } => todo!(),
        }
    }
}

impl crate::RenderError for PseudoinstructionError {
    fn format(self, _: &str, _: &str, mut buffer: &mut Vec<u8>, color: bool) {
        static FILENAME: &str = "<pseudoinstruction expansion>";
        let src = &self.definition;
        Report::build(ReportKind::Error, (FILENAME, self.span.clone()))
            .with_config(Config::default().with_color(color))
            .with_message(self.kind.to_string())
            .with_label(
                Label::new((FILENAME, self.span))
                    .with_message(self.kind.label())
                    .with_color(Color::Red),
            )
            .finish()
            .write((FILENAME, Source::from(src)), &mut buffer)
            .expect("Writing to an in-memory vector shouldn't fail");
    }
}

/// Trait for promoting an error [`Kind`] wrapped in a [`Result`] to an [`Error`]
pub(crate) trait SpannedErr {
    /// Type wrapped in the Ok variant
    type T;

    /// Adds a span to the error kind, promoting it to an [`Error`]
    ///
    /// # Parameters
    ///
    /// * `span`: location in the assembly code that caused the error
    fn add_span(self, span: &Span) -> Result<Self::T, Error>;
}

impl<T> SpannedErr for Result<T, Kind> {
    type T = T;
    fn add_span(self, span: &Span) -> Result<T, Error> {
        self.map_err(|e| e.add_span(span))
    }
}
