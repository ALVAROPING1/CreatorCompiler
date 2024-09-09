use ariadne::{Color, Fmt, Label, Report, ReportKind, Source};

use std::fmt;
use std::fmt::Write as _;
use std::ops::Range;

use crate::architecture::ComponentType;
use crate::parser::Span;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DirectiveArgumentType {
    String,
    Number,
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
    IncorrectInstructionSyntax(Vec<String>),
    DuplicateLabel(String, Span),
    MissingMainLabel(String),
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
    IncorrectDirectiveArgumentType {
        expected: DirectiveArgumentType,
        found: DirectiveArgumentType,
    },
    DivisionBy0,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Error {
    span: Span,
    kind: Kind,
}

impl Kind {
    #[must_use]
    pub const fn add_span(self, span: Span) -> Error {
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
            Self::IntegerTooBig(..) => 9,
            Self::MemorySectionFull(..) => 10,
            Self::DataUnaligned { .. } => 11,
            Self::UnallowedNegativeValue(..) => 12,
            Self::IncorrectDirectiveArgumentNumber { .. } => 13,
            Self::IncorrectDirectiveArgumentType { .. } => 14,
            Self::DivisionBy0 => 15,
        }
    }

    fn note(&self) -> Option<String> {
        Some(match self {
            Self::IntegerTooBig(_, bounds) => {
                format!("Allowed range is [{}, {}]", bounds.start, bounds.end - 1)
            }
            Self::IncorrectInstructionSyntax(syntaxes) => {
                let mut res = "Allowed formats:".to_string();
                for syntax in syntaxes {
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
            Self::MissingMainLabel(main) => {
                format!("Consider adding a label called {main} to an instruction")
            }
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
            Self::MissingMainLabel(..) => "TODO: missing main label".into(),
            Self::IntegerTooBig(val, _) | Self::UnallowedNegativeValue(val) => {
                format!("This expression has value {val}")
            }
            Self::MemorySectionFull(..) => "This value doesn't fit in the available space".into(),
            Self::DataUnaligned { .. } => "This value isn't aligned".into(),
            Self::IncorrectDirectiveArgumentNumber { found, .. } => {
                format!("This directive has {found} arguments")
            }
            Self::IncorrectDirectiveArgumentType { found, .. } => {
                format!("This argument has type \"{found:?}\"")
            }
            Self::DivisionBy0 => "This expression has value 0".into(),
        }
    }

    fn context(&self) -> Vec<(Span, &'static str)> {
        match self {
            Self::DuplicateLabel(_, span) => {
                vec![(span.clone(), "Label previously defined here")]
            }
            _ => Vec::new(),
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
            Self::IncorrectInstructionSyntax(_) => write!(f, "Incorrect instruction syntax"),
            Self::DuplicateLabel(s, _) => write!(f, "Label \"{s}\" is already defined"),
            Self::MissingMainLabel(s) => write!(f, "Label \"{s}\" not found"),
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
            Self::IncorrectDirectiveArgumentType { expected, found } => write!(
                f,
                "Incorrect argument type, expected \"{expected:?}\" but found \"{found:?}\""
            ),
            Self::DivisionBy0 => write!(f, "Can't divide by 0"),
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
    }
}
