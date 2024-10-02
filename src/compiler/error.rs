use ariadne::{Color, Fmt, Label, Report, ReportKind, Source};

use std::fmt;
use std::fmt::Write as _;
use std::ops::Range;

use crate::architecture::{ComponentType, DirectiveSegment};
use crate::parser::{ParseError, Span, Spanned};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArgumentType {
    String,
    Expression,
    RegisterName,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OperationKind {
    UnaryNegation,
    BitwiseOR,
    BitwiseAND,
    BitwiseXOR,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Kind {
    UnknownDirective(String),
    UnknownInstruction(String),
    UnknownLabel(String),
    UnknownRegisterBank(ComponentType),
    UnknownRegister {
        name: String,
        bank: ComponentType,
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
    },
    UnallowedNegativeValue(i64),
    IncorrectDirectiveArgumentNumber {
        expected: u8,
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
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Error {
    span: Span,
    kind: Kind,
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
    #[must_use]
    pub const fn add_span(self, span: &Span) -> Error {
        let span = span.start..span.end;
        Error { span, kind: self }
    }

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
        }
    }

    fn note(&self) -> Option<String> {
        Some(match self {
            Self::IntegerTooBig(_, bounds) => {
                format!("Allowed range is [{}, {}]", bounds.start, bounds.end - 1)
            }
            Self::IncorrectInstructionSyntax(errs) => {
                let mut res = "Allowed formats:".to_string();
                for (syntax, _) in errs {
                    // NOTE: using line jumps messes ariadne's formatting of notes, so we have to
                    // replicate the margin manually for each new line
                    write!(res, "\n   {} {syntax}", "│".fg(Color::Fixed(240)))
                        .expect("The write macro can't fail for `String`s");
                }
                res
            }
            _ => return None,
        })
    }

    fn hint(&self) -> Option<String> {
        Some(match self {
            Self::DuplicateLabel(..) => "Consider renaming either of the labels".into(),
            Self::MainOutsideCode(..) => "Consider moving the label to an instruction".into(),
            Self::IncorrectDirectiveArgumentNumber { expected, found } => {
                let expected = usize::from(*expected);
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
            Self::MemorySectionFull(..) => "This value doesn't fit in the available space".into(),
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
        }
    }

    fn context(&self) -> Vec<(Span, &'static str)> {
        match self {
            Self::DuplicateLabel(_, span) => {
                vec![(span.clone(), "Label previously defined here")]
            }
            Self::UnallowedStatementType {
                section: Some(section),
                ..
            } => {
                vec![(section.1.clone(), "Section previously started here")]
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

impl fmt::Display for Kind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::UnknownDirective(s) => write!(f, "Directive \"{s}\" isn't defined"),
            Self::UnknownInstruction(s) => write!(f, "Instruction \"{s}\" isn't defined"),
            Self::UnknownLabel(s) => write!(f, "Label \"{s}\" isn't defined"),
            Self::UnknownRegisterBank(s) => write!(f, "Register bank \"{s:?}\" isn't defined"),
            Self::UnknownRegister { name, bank } => {
                write!(f, "Register \"{name}\" isn't defined in bank type {bank:?}")
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
            Self::DataUnaligned { address, alignment } => write!(
                f,
                "Data at address {address:#X} isn't aligned to size {alignment}"
            ),
            Self::UnallowedNegativeValue(_) => write!(f, "Negative values aren't allowed"),
            Self::IncorrectDirectiveArgumentNumber { expected, found } => write!(
                f,
                "Incorrect amount of arguments, expected {expected} but found {found}"
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
        }
    }
}

impl Error {
    pub fn print(self, filename: &str, src: &str) {
        let mut report = Report::build(ReportKind::Error, filename, self.span.start)
            .with_code(format!("E{:02}", self.kind.error_code()))
            .with_message(self.kind.to_string())
            .with_label(
                Label::new((filename, self.span))
                    .with_message(self.kind.label())
                    .with_color(Color::Red),
            )
            .with_labels(self.kind.context().into_iter().map(|label| {
                Label::new((filename, label.0))
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
            .print((filename, Source::from(src)))
            .expect("we should be able to print to stdout");

        if let Kind::IncorrectInstructionSyntax(errs) = self.kind {
            for (syntax, err) in errs {
                println!("\nThe syntax `{syntax}` failed with the following reason:\n");
                err.print(filename, src);
            }
        }
    }
}

pub trait SpannedErr {
    type T;
    fn add_span(self, span: &Span) -> Result<Self::T, Error>;
}

impl<T> SpannedErr for Result<T, Kind> {
    type T = T;
    fn add_span(self, span: &Span) -> Result<T, Error> {
        self.map_err(|e| e.add_span(span))
    }
}
