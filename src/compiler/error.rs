//! Module containing the definition of the compiler errors
//!
//! The main type is [`Error`]

use ariadne::{Color, Fmt, Label, Report, ReportKind, Source};

use std::fmt;
use std::ops::Range;
use std::{fmt::Write as _, io::Write as _};

use crate::architecture::{DirectiveSegment, FloatType, RegisterType};
use crate::parser::{ParseError, Span, Spanned};

use super::{ArgumentNumber, PseudoinstructionError, PseudoinstructionErrorKind};

/// Type of arguments for directives/instructions
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArgumentType {
    String,
    Expression,
    RegisterName,
}

/// Unsupported operations for floating point numbers
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OperationKind {
    UnaryNegation,
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
    DuplicateLabel(String, Span),
    MissingMainLabel(String),
    MainOutsideCode(String),
    IntegerTooBig(i64, Range<i64>),
    MemorySectionFull(&'static str),
    DataUnaligned {
        address: u64,
        alignment: u64,
        word_size: u64,
    },
    UnallowedNegativeValue(i64),
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
    pub kind: Kind,
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
    pub const fn add_span(self, span: &Span) -> Error {
        let span = span.start..span.end;
        Error { span, kind: self }
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
            Self::MainOutsideCode(..) => 9,
            Self::IntegerTooBig(..) => 10,
            Self::MemorySectionFull(..) => 11,
            Self::DataUnaligned { .. } => 12,
            Self::UnallowedNegativeValue(..) => 13,
            Self::IncorrectDirectiveArgumentNumber { .. } => 14,
            Self::IncorrectArgumentType { .. } => 15,
            Self::DivisionBy0 => 16,
            Self::UnallowedFloat => 17,
            Self::UnallowedFloatOperation(..) => 18,
            Self::UnallowedStatementType { .. } => 19,
            Self::PseudoinstructionError { .. } => 20,
        }
    }

    /// Gets a note with extra information about the error if available
    fn note(&self) -> Option<String> {
        Some(match self {
            Self::IntegerTooBig(_, bounds) => {
                format!("Allowed range is [{}, {}]", bounds.start, bounds.end - 1)
            }
            Self::IncorrectInstructionSyntax(errs) => {
                let mut res = "Allowed formats:".to_string();
                for (syntax, _) in errs {
                    write!(res, "\n{syntax}").expect("The write macro can't fail for `String`s");
                }
                res
            }
            _ => return None,
        })
    }

    /// Gets a hint about how to fix the error if available
    fn hint(&self) -> Option<String> {
        Some(match self {
            Self::DuplicateLabel(..) => "Consider renaming either of the labels".into(),
            Self::MainOutsideCode(..) => "Consider moving the label to an instruction".into(),
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
            // TODO: Maybe add hint for required directive?
            // Self::UnallowedStatementSection { expected, _ } => { ... }
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
                format!("Consider adding a label called \"{main}\" to an instruction")
            }
            Self::MainOutsideCode(..) => "Label defined here".into(),
            Self::IntegerTooBig(val, _) | Self::UnallowedNegativeValue(val) => {
                format!("This expression has value {val}")
            }
            Self::MemorySectionFull(..) => "This element doesn't fit in the available space".into(),
            Self::DataUnaligned { .. } => "This value isn't aligned".into(),
            Self::IncorrectDirectiveArgumentNumber { found, .. } => {
                format!("This directive has {found} argument{}", plural!(*found))
            }
            Self::IncorrectArgumentType { found, .. } => {
                format!("This argument has type \"{found:?}\"")
            }
            Self::DivisionBy0 => "This expression has value 0".into(),
            Self::UnallowedFloat => "This value can't be used".into(),
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
            Self::DuplicateLabel(_, span) => {
                vec![(span, "Label previously defined here")]
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
            Self::UnaryNegation => write!(f, "unary negation (`~`)"),
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
            Self::UnknownDirective(s) => write!(f, "Directive \"{s}\" isn't defined"),
            Self::UnknownInstruction(s) => write!(f, "Instruction \"{s}\" isn't defined"),
            Self::UnknownLabel(s) => write!(f, "Label \"{s}\" isn't defined"),
            Self::UnknownRegisterBank(s) => write!(f, "Register bank of type {s} isn't defined"),
            Self::UnknownRegister { name, bank } => {
                write!(f, "Register \"{name}\" isn't defined in bank type {bank}")
            }
            Self::IncorrectInstructionSyntax(..) => write!(f, "Incorrect instruction syntax"),
            Self::DuplicateLabel(s, _) => write!(f, "Label \"{s}\" is already defined"),
            Self::MissingMainLabel(s) => write!(f, "Main label \"{s}\" not found"),
            Self::MainOutsideCode(s) => {
                write!(f, "Main label \"{s}\" defined outside of the text segment")
            }
            Self::IntegerTooBig(val, _) => {
                write!(f, "Field is too small to contain value \"{val}\"")
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
                "Incorrect argument type, expected \"{expected:?}\" but found \"{found:?}\""
            ),
            Self::DivisionBy0 => write!(f, "Can't divide by 0"),
            Self::UnallowedFloat => {
                write!(f, "Can't use floating point values in integer expressions")
            }
            Self::UnallowedFloatOperation(op) => write!(
                f,
                "Can't perform the {op} operation with floating point numbers"
            ),
            Self::UnallowedStatementType { section, found } => {
                write!(
                    f,
                    "Can't use \"{}\" statements while in section \"{}\"",
                    match found {
                        DirectiveSegment::Code => "instruction",
                        DirectiveSegment::Data => "data directive",
                    },
                    match section {
                        Some((DirectiveSegment::Data, _)) => "data",
                        Some((DirectiveSegment::Code, _)) => "code",
                        None => "none",
                    }
                )
            }
            Self::PseudoinstructionError {name, ..} => write!(f, "Error while evaluating pseudoinstruction \"{name}\""),
        }
    }
}

impl crate::RenderError for Error {
    fn format(self, filename: &str, src: &str, mut buffer: &mut Vec<u8>) {
        let mut report = Report::build(ReportKind::Error, (filename, self.span.clone()))
            .with_code(format!("E{:02}", self.kind.error_code()))
            .with_message(self.kind.to_string())
            .with_label(
                Label::new((filename, self.span))
                    .with_message(self.kind.label())
                    .with_color(Color::Red),
            )
            .with_labels(self.kind.context().into_iter().map(|label| {
                Label::new((filename, label.0.clone()))
                    .with_message(format!("{} {}", "Note:".fg(Color::BrightBlue), label.1))
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

        match self.kind {
            Kind::IncorrectInstructionSyntax(errs) => {
                for (syntax, err) in errs {
                    writeln!(
                        &mut buffer,
                        "\nThe syntax `{syntax}` failed with the following reason:"
                    )
                    .expect("Writing to an in-memory vector can't fail");
                    err.format(filename, src, buffer);
                }
            }
            Kind::PseudoinstructionError { error, .. } => {
                writeln!(&mut buffer).expect("Writing to an in-memory vector can't fail");
                error.format(filename, src, buffer);
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
            Self::UnknownFieldNumber(..) => "Unknown field number",
            Self::EvaluationError(..) => "While evaluating this code",
            Self::ParseError { .. } => todo!(),
        }
    }
}

impl fmt::Display for PseudoinstructionErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::UnknownFieldName(s) => write!(f, "Field \"{s}\" isn't defined"),
            Self::UnknownFieldNumber(s) => write!(f, "Field number \"{s}\" isn't defined"),
            Self::EvaluationError(s) => write!(f, "Error evaluating JS code:\n{s}"),
            Self::ParseError { .. } => todo!(),
        }
    }
}

impl crate::RenderError for PseudoinstructionError {
    fn format(self, _: &str, _: &str, mut buffer: &mut Vec<u8>) {
        static FILENAME: &str = "<pseudoinstruction expansion>";
        let src = &self.definition;
        Report::build(ReportKind::Error, (FILENAME, self.span.clone()))
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

/// Trait for promoting an error `Kind` wrapped in a `Result` to an `Error`
pub trait SpannedErr {
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
