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

/// Wrapper for a vector to display it as a list of names
struct NameList<T>(pub Vec<T>);

impl<T: std::cmp::Ord> NameList<T> {
    /// Creates a new [`NameList`], checking that it isn't empty
    fn non_empty(vals: Vec<T>) -> Option<Self> {
        (!vals.is_empty()).then_some(Self::new(vals))
    }

    /// Creates a new [`NameList`]
    fn new(mut vals: Vec<T>) -> Self {
        vals.sort_unstable();
        Self(vals)
    }
}

impl<T: fmt::Display> fmt::Display for NameList<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Some(last) = self.0.last() else {
            return Ok(());
        };
        let fmt_elem = |f: &mut fmt::Formatter, val| write!(f, "`{val}`");
        for i in 0..self.0.len() - 1 {
            fmt_elem(f, &self.0[i])?;
            write!(f, "{} ", if self.0.len() > 2 { "," } else { "" })?;
        }
        if self.0.len() > 1 {
            write!(f, "or ")?;
        }
        fmt_elem(f, last)?;
        Ok(())
    }
}

/// Gets the names from a list that are the most similar to the given name
///
/// # Parameters
///
/// * `target`: target name to match against
/// * `names`: iterator of possible names
fn get_similar<'a>(target: &str, names: impl Iterator<Item = &'a str>) -> Vec<&'a str> {
    let mut distances = std::collections::HashMap::new();
    for name in names {
        distances
            .entry(name)
            .or_insert_with(|| edit_distance::edit_distance(name, target));
    }
    let Some(min) = distances.iter().min_by_key(|(_, &d)| d).map(|(_, x)| *x) else {
        return vec![];
    };
    if min > std::cmp::max(target.len() / 3, 1) {
        return vec![];
    }
    distances
        .into_iter()
        .filter(|(_, d)| *d == min)
        .map(|(name, _)| name)
        .collect()
}

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
    fn hint(&self, arch: &Architecture, labels: &LabelTable) -> Option<String> {
        Some(match self {
            Self::UnknownDirective(s) => {
                let names = get_similar(s, arch.directives.iter().map(|d| d.name));
                format!("Did you mean {}?", NameList::non_empty(names)?)
            }
            Self::UnknownInstruction(s) => {
                let inst_names = arch.instructions.iter().map(|i| i.name);
                let pseudo_names = arch.pseudoinstructions.iter().map(|i| i.name);
                let names = get_similar(s, inst_names.chain(pseudo_names));
                format!("Did you mean {}?", NameList::non_empty(names)?)
            }
            Self::UnknownLabel(s) => {
                let names = get_similar(s, labels.iter().map(|(n, _)| n.as_str()));
                format!("Did you mean {}?", NameList::non_empty(names)?)
            }
            Self::UnknownRegister { name, file } => {
                let files = arch.find_reg_files(*file);
                let registers = files.flat_map(|file| {
                    file.elements
                        .iter()
                        .flat_map(|reg| reg.name.iter().copied())
                });
                let names = get_similar(name, registers);
                format!("Did you mean {}?", NameList::non_empty(names)?)
            }
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
            Self::UnallowedStatementType { found, .. } => {
                let names: Vec<_> = arch.directives.iter()
                    .filter(|dir| matches!(dir.action, DirectiveAction::Segment(s) if s.is_code() == found.is_code()))
                    .map(|dir| dir.name)
                    .collect();
                format!(
                    "Consider changing the section to `{}`{}{}",
                    if found.is_code() { "code" } else { "data" },
                    if names.is_empty() { "" } else { ", using " },
                    NameList::new(names)
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
            Self::UnknownRegisterFile(..) => "Unknown register file".into(),
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
            Self::UnknownRegisterFile(s) => write!(f, "Register file of type `{s}` isn't defined"),
            Self::UnknownRegister { name, file } => {
                write!(f, "Register `{name}` isn't defined in file type {file}")
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
        let data = self.error;
        let (filename_user, src_user) = (filename, src);
        let (filename, src) = data.span.source.as_ref().map_or((filename, src), |origin| {
            ("<pseudoinstruction expansion>", origin.code.as_str())
        });
        let note_color = color.then_some(Color::BrightBlue);
        let mut report = Report::build(ReportKind::Error, (filename, data.span.span.clone()))
            .with_config(Config::default().with_color(color))
            .with_code(format!("E{:02}", data.kind.error_code()))
            .with_message(data.kind.to_string())
            .with_label(
                Label::new((filename, data.span.span))
                    .with_message(data.kind.label())
                    .with_color(Color::Red),
            )
            .with_labels(data.kind.context().into_iter().map(|label| {
                Label::new((filename, label.0.clone()))
                    .with_message(format!("{} {}", "Note:".fg(note_color), label.1))
                    .with_color(Color::BrightBlue)
                    .with_order(10)
            }));
        if let Some(note) = data.kind.note() {
            report.set_note(note);
        }
        if let Some(hint) = data.kind.hint(self.arch, &self.label_table) {
            report.set_help(hint);
        }

        report
            .finish()
            .write((filename, Source::from(src)), &mut buffer)
            .expect("Writing to an in-memory vector shouldn't fail");

        match *data.kind {
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

        if let Some(origin) = &data.span.source {
            origin.span.format(filename_user, src_user, buffer, color);
        }
    }
}

impl PseudoinstructionErrorKind {
    /// Gets the label text describing the error
    const fn label(&self) -> &'static str {
        match self {
            Self::UnknownFieldName(..) => "Unknown field name",
            Self::UnknownFieldNumber(..) => "Field index out of bounds",
            Self::UnknownFieldType(..) => "Unknown field type",
            Self::EmptyBitRange => "Empty bit range",
            Self::BitRangeOutOfBounds { .. } => "Bit range out of bounds",
            Self::EvaluationError(..) => "While evaluating this code",
            Self::ParseError { .. } => "While parsing this instruction",
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
            Self::ParseError(_) => write!(f, "Error parsing instruction"),
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
                Label::new((FILENAME, self.span.clone()))
                    .with_message(self.kind.label())
                    .with_color(Color::Red),
            )
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
