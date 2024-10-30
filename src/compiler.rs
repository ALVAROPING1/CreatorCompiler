//! Module containing the definition of the assembly compiler
//!
//! The entry point for compiler code is the [`compile()`] function. Users are expected to parse
//! the code first to an AST with [`crate::parser::parse()`]

use once_cell::sync::Lazy;
use regex::{NoExpand, Regex};

use crate::architecture::{
    Architecture, DirectiveAction, DirectiveAlignment, DirectiveData, DirectiveSegment, FieldType,
    FloatType, Instruction as InstructionDefinition, RegisterType, StringType,
};
use crate::parser::{ASTNode, Argument, Data as DataToken, Expr, Span, Spanned, Statement, Token};

mod label;
use label::{Label, Table as LabelTable};

mod error;
use error::SpannedErr as _;
pub use error::{ArgumentType, Error as CompileError, Kind as ErrorKind, OperationKind};

mod bit_field;
use bit_field::BitField;

mod section;
use section::Section;

mod integer;
pub use integer::Integer;

/* TODO:
*  - Refactor code
*  - Remove uses of unwrap, propagating errors accordingly
*  - Combine `crate::parser::Error` with `crate::compiler::Error`
*  - Implement pseudoinstructions
*  - Rework argument number types
**/

// Regex for replacement templates in the translation spec of instructions
static RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"[fF][0-9]+").expect("This shouldn't fail"));

// Parsed instruction arguments type
type Output = Vec<(Spanned<Argument>, usize)>;

/// Parse the arguments of an instruction according to any of its definitions. If the arguments
/// match the syntax of multiple definitions, the first definition is always used
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
) -> Result<(&'a InstructionDefinition<'a>, Output), CompileError> {
    // Errors produced on each of the attempted parses
    let mut errs = Vec::new();
    // Get all instruction definitions with the given name
    for inst in arch.find_instructions(&name.0) {
        // Try to parse the given arguments according to the syntax of the current definition
        match inst.syntax.parser.parse(args) {
            // If parsing is successful, assume this definition is the correct one and return it
            Ok(parsed_args) => return Ok((inst, parsed_args)),
            // Otherwise, append the produced error to the error vector and try the next definition
            Err(e) => errs.push((inst.syntax.user_syntax.to_string(), e)),
        }
    }
    // If we didn't get any errors, we didn't find any definitions for the instruction
    Err(if errs.is_empty() {
        ErrorKind::UnknownInstruction(name.0).add_span(&name.1)
    } else {
        ErrorKind::IncorrectInstructionSyntax(errs).add_span(&args.1)
    })
}

/// Compiled instruction
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
    /// Span of the instruction in the assembly code
    pub user: Span,
}

/// Value to add to the data segment
#[derive(Debug, PartialEq, Clone)]
pub enum Value {
    /// Integer value
    Integer(Integer),
    /// Reserved space initialized to 0
    Space(u64),
    /// Padding added to align elements
    Padding(u64),
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
pub struct Data {
    /// Address of the element
    pub address: u64,
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
    fn into_string(self, span: &Span) -> Result<String, CompileError> {
        match self {
            Self::String(s) => Ok(s),
            Self::Number(_) => Err(ErrorKind::IncorrectArgumentType {
                expected: ArgumentType::String,
                found: ArgumentType::Expression,
            }
            .add_span(span)),
        }
    }

    /// Convert the value to an expression
    ///
    /// # Parameters
    ///
    /// * `span`: span of the value in the assembly code
    const fn to_expr(&self, span: &Span) -> Result<&Expr, CompileError> {
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

/// Compilation result
#[derive(Debug, PartialEq, Clone)]
pub struct CompiledCode {
    /// Symbol table for labels
    pub label_table: LabelTable,
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

/// Amount of arguments expected by a directive
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ArgumentNumber {
    /// Minimum expected amount
    pub amount: usize,
    /// Whether it's allowed to use more arguments
    pub at_least: bool,
}

impl ArgumentNumber {
    /// Create a new `ArgumentNumber`
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
    fn check<T>(self, args: &Spanned<Vec<T>>) -> Result<(), CompileError> {
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

fn compile_data(
    label_table: &mut LabelTable,
    section: &mut Section,
    memory: &mut Vec<Data>,
    alignment: &mut Option<Spanned<u64>>,
    word_size: u64,
    data_type: DirectiveData,
    mut labels: Vec<Spanned<String>>,
    args: Spanned<Vec<Spanned<DataToken>>>,
) -> Result<(), CompileError> {
    if let Some((align, span)) = alignment.take() {
        if let Some((start, size)) = section.try_align(align).add_span(&span)? {
            memory.push(Data {
                address: start,
                labels: Vec::new(),
                value: Value::Padding(size),
            });
        }
    }
    for (label, span) in &labels {
        label_table.insert(label.to_owned(), Label::new(section.get(), span.clone()))?;
    }
    match data_type {
        DirectiveData::Space(size) => {
            ArgumentNumber::new(1, false).check(&args)?;
            let (args, _) = args;
            let (value, span) = &args[0];
            let value = value.to_expr(span)?.int()?;
            let size = u64::try_from(value)
                .map_err(|_| ErrorKind::UnallowedNegativeValue(value.into()).add_span(span))?
                * u64::from(size);
            memory.push(Data {
                address: section.try_reserve(size).add_span(span)?,
                labels: take_spanned_vec(&mut labels),
                value: Value::Space(size),
            });
        }
        DirectiveData::Int(size, int_type) => {
            ArgumentNumber::new(1, true).check(&args)?;
            for (value, span) in args.0 {
                let value = value.to_expr(&span)?.int()?;
                memory.push(Data {
                    address: section
                        .try_reserve_aligned(size.into(), word_size)
                        .add_span(&span)?,
                    labels: take_spanned_vec(&mut labels),
                    value: Value::Integer(
                        Integer::build(value.into(), (size * 8).into(), Some(int_type), None)
                            .add_span(&span)?,
                    ),
                });
            }
        }
        DirectiveData::Float(float_type) => {
            ArgumentNumber::new(1, true).check(&args)?;
            for (value, span) in args.0 {
                let value = value.to_expr(&span)?.float()?;
                #[allow(clippy::cast_possible_truncation)]
                let (value, size) = match float_type {
                    FloatType::Float => (Value::Float(value as f32), 4),
                    FloatType::Double => (Value::Double(value), 8),
                };
                memory.push(Data {
                    address: section
                        .try_reserve_aligned(size, word_size)
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
                memory.push(Data {
                    address: section
                        .try_reserve(data.len() as u64 + u64::from(null_terminated))
                        .add_span(&span)?,
                    labels: take_spanned_vec(&mut labels),
                    value: Value::String {
                        data,
                        null_terminated,
                    },
                });
            }
        }
    }
    Ok(())
}

#[allow(clippy::too_many_lines)]
pub fn compile(arch: &Architecture, ast: Vec<ASTNode>) -> Result<CompiledCode, CompileError> {
    let mut label_table = LabelTable::default();
    let mut code_section = Section::new("Instructions", arch.code_section());
    let mut data_section = Section::new("Data", arch.data_section());
    let word_size = arch.word_size() / 8;
    let mut parsed_instructions = Vec::new();
    let mut data_memory = Vec::new();
    let mut alignment: Option<Spanned<u64>> = None;
    let mut instruction_eof = 0;
    let mut current_section: Option<Spanned<DirectiveSegment>> = None;

    for node in ast {
        match node.statement.0 {
            Statement::Directive(directive) => {
                let action = arch.find_directive(&directive.name.0).ok_or_else(|| {
                    ErrorKind::UnknownDirective(directive.name.0).add_span(&directive.name.1)
                })?;
                match (action, &current_section) {
                    (DirectiveAction::Segment(new_section), _) => {
                        ArgumentNumber::new(0, false).check(&directive.args)?;
                        current_section = Some((new_section, node.statement.1));
                    }
                    (DirectiveAction::GlobalSymbol(_), _) => todo!(),
                    (DirectiveAction::Alignment(align_type), Some((DirectiveSegment::Data, _))) => {
                        ArgumentNumber::new(1, false).check(&directive.args)?;
                        let (args, _) = directive.args;
                        let (value, span) = &args[0];
                        let value = value.to_expr(span)?.int()?;
                        let value = u32::try_from(value).map_err(|_| {
                            ErrorKind::UnallowedNegativeValue(value.into()).add_span(span)
                        })?;
                        alignment = Some((
                            match align_type {
                                DirectiveAlignment::Exponential => 2_u64.pow(value),
                                DirectiveAlignment::Byte => value.into(),
                            },
                            directive.name.1.start..directive.args.1.end,
                        ));
                        continue;
                    }
                    (DirectiveAction::Data(data_type), Some((DirectiveSegment::Data, _))) => {
                        compile_data(
                            &mut label_table,
                            &mut data_section,
                            &mut data_memory,
                            &mut alignment,
                            word_size.into(),
                            data_type,
                            node.labels,
                            directive.args,
                        )?;
                    }
                    _ => {
                        return Err(ErrorKind::UnallowedStatementType {
                            section: current_section,
                            found: DirectiveSegment::Data,
                        }
                        .add_span(&node.statement.1));
                    }
                }
            }
            Statement::Instruction(instruction) => {
                if !matches!(current_section, Some((DirectiveSegment::Code, _))) {
                    return Err(ErrorKind::UnallowedStatementType {
                        section: current_section,
                        found: DirectiveSegment::Code,
                    }
                    .add_span(&node.statement.1));
                }
                let (name, span) = instruction.name;
                instruction_eof = node.statement.1.end;
                let (def, args) = parse_instruction(arch, (name, span.clone()), &instruction.args)?;
                let addr = code_section
                    .try_reserve(u64::from(word_size) * u64::from(def.nwords))
                    .add_span(&span)?;
                for (label, span) in &node.labels {
                    label_table.insert(label.clone(), Label::new(addr, span.clone()))?;
                }
                parsed_instructions.push((
                    node.labels.into_iter().map(|x| x.0).collect(),
                    addr,
                    node.statement.1,
                    (def, args),
                ));
            }
        }
    }
    match label_table.get(arch.main_label()) {
        None => {
            #[allow(clippy::range_plus_one)] // Ariadne works with exclusive ranges
            return Err(ErrorKind::MissingMainLabel(arch.main_label().to_owned())
                .add_span(&(instruction_eof..instruction_eof + 1)));
        }
        Some(main) => {
            let text = arch.code_section();
            if !text.contains(main.address()) {
                return Err(
                    ErrorKind::MainOutsideCode(arch.main_label().to_owned()).add_span(main.span())
                );
            }
        }
    }
    parsed_instructions
        .into_iter()
        .map(|(labels, address, inst_span, (def, args))| {
            let mut binary_instruction =
                BitField::new(usize::from(word_size) * usize::from(def.nwords) * 8);
            let mut translated_instruction = def.syntax.output_syntax.to_string();
            for ((value, span), i) in args {
                let field = &def.syntax.fields[i];
                #[allow(clippy::cast_sign_loss)]
                let (value, value_str) = match field.r#type {
                    FieldType::Cop { .. } => {
                        unreachable!("This field type shouldn't be used for instruction arguments")
                    }
                    #[allow(clippy::cast_possible_wrap)]
                    FieldType::Co => (def.co.0 as i64, def.name.to_string()),
                    val_type @ (FieldType::Address
                    | FieldType::ImmSigned
                    | FieldType::ImmUnsigned
                    | FieldType::OffsetBytes
                    | FieldType::OffsetWords) => {
                        let value = match value {
                            Argument::Number(expr) => expr.int()?,
                            Argument::Identifier(label) => label_table
                                .get(&label)
                                .ok_or_else(|| ErrorKind::UnknownLabel(label).add_span(&span))?
                                .address()
                                .try_into()
                                .unwrap(),
                        };
                        let next_address = i64::try_from(address).unwrap()
                            + i64::from(word_size) * i64::from(def.nwords);
                        let offset = i64::from(value) - next_address;
                        let value = match val_type {
                            FieldType::OffsetWords => offset / i64::from(word_size),
                            FieldType::OffsetBytes => offset,
                            _ => value.into(),
                        };
                        (value, value.to_string())
                    }
                    val_type @ (FieldType::IntReg
                    | FieldType::CtrlReg
                    | FieldType::SingleFPReg
                    | FieldType::DoubleFPReg) => {
                        let name = match value {
                            Argument::Number(_) => {
                                return Err(ErrorKind::IncorrectArgumentType {
                                    expected: ArgumentType::RegisterName,
                                    found: ArgumentType::Expression,
                                }
                                .add_span(&span))
                            }
                            Argument::Identifier(name) => name,
                        };
                        let bank_type = match val_type {
                            FieldType::IntReg => RegisterType::Int,
                            FieldType::CtrlReg => RegisterType::Ctrl,
                            FieldType::SingleFPReg => RegisterType::Float(FloatType::Float),
                            FieldType::DoubleFPReg => RegisterType::Float(FloatType::Double),
                            _ => unreachable!("We already matched one of these variants"),
                        };
                        let mut banks = arch.find_banks(bank_type).peekable();
                        banks.peek().ok_or_else(|| {
                            ErrorKind::UnknownRegisterBank(bank_type).add_span(&span)
                        })?;
                        let (i, _) = banks
                            .find_map(|bank| bank.find_register(&name))
                            .ok_or_else(|| {
                                ErrorKind::UnknownRegister {
                                    name: name.clone(),
                                    bank: bank_type,
                                }
                                .add_span(&span)
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
                            FieldType::ImmSigned | FieldType::OffsetBytes | FieldType::OffsetWords
                        ),
                    )
                    .add_span(&span)?;
                // FIXME: if a register is defined in the architecture with a name that uses the
                // same pattern we replace here, and it is used in the code, further replacements
                // will replace the name of the register, leading to an incorrect output. We have
                // no way to delimit replaced arguments that can't be messed up by a user, so this
                // method of translation is doomed to fail
                translated_instruction = RE
                    .replace(&translated_instruction, NoExpand(&value_str))
                    .to_string();
            }
            let fields = def.syntax.fields.iter();
            for (range, value) in fields.filter_map(|field| match field.r#type {
                FieldType::Cop { value } => Some((&field.range, value)),
                _ => None,
            }) {
                #[allow(clippy::cast_possible_wrap)]
                binary_instruction
                    .replace(range, value.0 as i64, false)
                    .unwrap();
            }
            Ok(Instruction {
                labels,
                address,
                binary: binary_instruction,
                loaded: translated_instruction,
                user: inst_span,
            })
        })
        .collect::<Result<Vec<_>, _>>()
        .map(|instructions| CompiledCode {
            label_table,
            instructions,
            data_memory,
        })
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod test {
    use super::*;
    use crate::architecture::{Architecture, BitRange, IntegerType, NonEmptyRangeInclusiveU8};

    fn compile(src: &str) -> Result<CompiledCode, CompileError> {
        let arch = Architecture::from_json(include_str!("../tests/architecture.json")).unwrap();
        let ast = crate::parser::parse(src).unwrap();
        super::compile(&arch, ast)
    }

    fn label_table(labels: impl IntoIterator<Item = (&'static str, u64, Span)>) -> LabelTable {
        let mut tbl = LabelTable::default();
        for v in labels {
            tbl.insert(v.0.into(), super::Label::new(v.1, v.2)).unwrap();
        }
        tbl
    }

    fn bitfield(bits: &str) -> BitField {
        let mut field = BitField::new(bits.len());
        for (i, c) in bits.chars().enumerate() {
            if c == '1' {
                let i = u8::try_from(bits.len() - i - 1).unwrap();
                field
                    .replace(
                        &BitRange::build(vec![NonEmptyRangeInclusiveU8::build(i, i).unwrap()])
                            .unwrap(),
                        1,
                        false,
                    )
                    .unwrap();
            }
        }
        field
    }

    fn inst(address: u64, labels: &[&str], loaded: &str, binary: &str, user: Span) -> Instruction {
        Instruction {
            address,
            labels: labels.iter().map(|&x| x.to_owned()).collect(),
            loaded: loaded.into(),
            binary: bitfield(binary),
            user,
        }
    }

    fn main_nop(span: Span) -> Instruction {
        let binary = "11110000000000000000000001111111";
        inst(0, &["main"], "nop", binary, span)
    }

    fn data(address: u64, labels: &[&str], value: Value) -> Data {
        Data {
            address,
            value,
            labels: labels.iter().map(|&x| x.to_owned()).collect(),
        }
    }

    #[test]
    fn nop() {
        // Minimal
        let x = compile(".text\nmain: nop").unwrap();
        assert_eq!(x.label_table, label_table([("main", 0, 6..11)]));
        assert_eq!(x.instructions, vec![main_nop(12..15)]);
        assert_eq!(x.data_memory, vec![]);
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
    }

    #[test]
    fn instruction_multiple_defs() {
        let x = compile(".text\nmain: multi").unwrap();
        let binary = "00000000000000000000000001110011";
        assert_eq!(x.label_table, label_table([("main", 0, 6..11)]));
        assert_eq!(
            x.instructions,
            vec![inst(0, &["main"], "multi", binary, 12..17)]
        );
        assert_eq!(x.data_memory, vec![]);
        let x = compile(".text\nmain: multi $").unwrap();
        let binary = "00000000000000000000000001011101";
        assert_eq!(x.label_table, label_table([("main", 0, 6..11)]));
        assert_eq!(
            x.instructions,
            vec![inst(0, &["main"], "multi $", binary, 12..19)]
        );
        assert_eq!(x.data_memory, vec![]);
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
        // Aliases
        let x = compile(".text\nmain: reg ctrl1, two, ft1, ft2").unwrap();
        assert_eq!(x.label_table, tbl);
        assert_eq!(
            x.instructions,
            vec![inst(0, &["main"], "reg ctrl1 two ft1 ft2", binary, 12..36)]
        );
        assert_eq!(x.data_memory, vec![]);
        // Linked floating point registers
        let x = compile(".text\nmain: reg ctrl1, x2, fs1, FD2").unwrap();
        assert_eq!(x.label_table, tbl);
        assert_eq!(
            x.instructions,
            vec![inst(0, &["main"], "reg ctrl1 x2 fs1 FD2", binary, 12..35)]
        );
        assert_eq!(x.data_memory, vec![]);
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
    }

    #[test]
    fn instruction_fields_offsets_aligned() {
        let x = compile(".text\nmain: off 7, 12").unwrap();
        let binary = "00110000000000000000000000000010";
        assert_eq!(x.label_table, label_table([("main", 0, 6..11)]));
        assert_eq!(
            x.instructions,
            vec![inst(0, &["main"], "off 3 2", binary, 12..21)]
        );
        assert_eq!(x.data_memory, vec![]);
    }

    #[test]
    fn instruction_fields_offsets_unaligned() {
        let x = compile(".text\nmain: off 6, 11").unwrap();
        let binary = "00100000000000000000000000000001";
        assert_eq!(x.label_table, label_table([("main", 0, 6..11)]));
        assert_eq!(
            x.instructions,
            vec![inst(0, &["main"], "off 2 1", binary, 12..21)]
        );
        assert_eq!(x.data_memory, vec![]);
    }

    #[test]
    fn space() {
        let x = compile(".data\n.zero 3\n.zero 1\n.text\nmain: nop").unwrap();
        assert_eq!(x.label_table, label_table([("main", 0, 28..33)]));
        assert_eq!(x.instructions, vec![main_nop(34..37)]);
        assert_eq!(
            x.data_memory,
            vec![
                data(16, &[], Value::Space(3)),
                data(19, &[], Value::Space(1)),
            ]
        );
    }

    #[test]
    fn int() {
        // 1 argument
        let x = compile(".data\na: .byte 1\n.text\nmain: nop").unwrap();
        assert_eq!(
            x.label_table,
            label_table([("main", 0, 23..28), ("a", 16, 6..8)])
        );
        assert_eq!(x.instructions, vec![main_nop(29..32)]);
        assert_eq!(
            x.data_memory,
            vec![data(
                16,
                &["a"],
                Value::Integer(Integer::build(1, 8, Some(IntegerType::Byte), None).unwrap(),)
            )]
        );
        // Multiple arguments
        let x = compile(".data\nb: .byte -128, 255\n.text\nmain: nop").unwrap();
        assert_eq!(
            x.label_table,
            label_table([("main", 0, 31..36), ("b", 16, 6..8)])
        );
        assert_eq!(x.instructions, vec![main_nop(37..40)]);
        assert_eq!(
            x.data_memory,
            vec![
                data(
                    16,
                    &["b"],
                    Value::Integer(Integer::build(128, 8, Some(IntegerType::Byte), None).unwrap())
                ),
                data(
                    17,
                    &[],
                    Value::Integer(Integer::build(255, 8, Some(IntegerType::Byte), None).unwrap())
                )
            ]
        );
        let test_cases = [
            ("half ", 2, IntegerType::HalfWord),
            ("word ", 4, IntegerType::Word),
            ("dword", 8, IntegerType::DoubleWord),
        ];
        for (name, size, r#type) in test_cases {
            let x = compile(&format!(".data\n.{name} 1, 2\n.text\nmain: nop")).unwrap();
            assert_eq!(x.label_table, label_table([("main", 0, 24..29)]));
            assert_eq!(x.instructions, vec![main_nop(30..33)]);
            assert_eq!(
                x.data_memory,
                vec![
                    data(
                        16,
                        &[],
                        Value::Integer(Integer::build(1, size * 8, Some(r#type), None).unwrap())
                    ),
                    data(
                        (16 + size).try_into().unwrap(),
                        &[],
                        Value::Integer(Integer::build(2, size * 8, Some(r#type), None).unwrap())
                    )
                ]
            );
        }
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
            assert_eq!(
                x.data_memory,
                vec![data(
                    16,
                    &["a"],
                    Value::String {
                        data: "a".into(),
                        null_terminated
                    }
                )]
            );
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
                    data(
                        16,
                        &["b"],
                        Value::String {
                            data: "b".into(),
                            null_terminated
                        }
                    ),
                    data(
                        17 + u64::from(null_terminated),
                        &[],
                        Value::String {
                            data: "0".into(),
                            null_terminated
                        }
                    ),
                ]
            );
        }
    }

    #[test]
    fn exp_align() {
        for size in [1, 3] {
            let x = compile(&format!(
                ".data\n.zero 1\n.align {size}\n.zero 1\n.text\nmain: nop"
            ))
            .unwrap();
            assert_eq!(x.label_table, label_table([("main", 0, 37..42)]));
            assert_eq!(x.instructions, vec![main_nop(43..46)]);
            let alignment = 2u64.pow(size) - 1;
            assert_eq!(
                x.data_memory,
                vec![
                    data(16, &[], Value::Space(1)),
                    data(17, &[], Value::Padding(alignment)),
                    data(17 + alignment, &[], Value::Space(1))
                ]
            );
        }
    }

    #[test]
    fn byte_align() {
        for size in [2, 8] {
            let x = compile(&format!(
                ".data\n.zero 1\n.balign {size}\n.zero 1\n.text\nmain: nop"
            ))
            .unwrap();
            assert_eq!(x.label_table, label_table([("main", 0, 38..43)]));
            assert_eq!(x.instructions, vec![main_nop(44..47)]);
            assert_eq!(
                x.data_memory,
                vec![
                    data(16, &[], Value::Space(1)),
                    data(17, &[], Value::Padding(size - 1)),
                    data(17 + size - 1, &[], Value::Space(1))
                ]
            );
        }
    }

    #[test]
    fn unallowed_statement() {
        assert_eq!(
            compile(".data\nnop\n.text\nmain: nop"),
            Err(ErrorKind::UnallowedStatementType {
                section: Some((DirectiveSegment::Data, 0..5)),
                found: DirectiveSegment::Code,
            }
            .add_span(&(6..9))),
        );
        assert_eq!(
            compile(".text\nmain: nop\n.byte 1"),
            Err(ErrorKind::UnallowedStatementType {
                section: Some((DirectiveSegment::Code, 0..5)),
                found: DirectiveSegment::Data,
            }
            .add_span(&(16..23))),
        );
        assert_eq!(
            compile("nop\n.text\nmain: nop"),
            Err(ErrorKind::UnallowedStatementType {
                section: None,
                found: DirectiveSegment::Code,
            }
            .add_span(&(0..3))),
        );
        assert_eq!(
            compile(".byte 1\n.text\nmain: nop"),
            Err(ErrorKind::UnallowedStatementType {
                section: None,
                found: DirectiveSegment::Data,
            }
            .add_span(&(0..7))),
        );
    }

    #[test]
    fn unknown_directive() {
        assert_eq!(
            compile(".test\n.text\nmain: nop"),
            Err(ErrorKind::UnknownDirective(".test".into()).add_span(&(0..5))),
        );
    }

    #[test]
    fn unknown_instruction() {
        assert_eq!(
            compile(".text\nmain: test"),
            Err(ErrorKind::UnknownInstruction("test".into()).add_span(&(12..16))),
        );
    }

    #[test]
    fn unknown_label() {
        assert_eq!(
            compile(".text\nmain: imm 0, 0, test"),
            Err(ErrorKind::UnknownLabel("test".into()).add_span(&(22..26))),
        );
    }

    #[test]
    fn unknown_register() {
        assert_eq!(
            compile(".text\nmain: reg x0, x0, ft1, ft2"),
            Err(ErrorKind::UnknownRegister {
                name: "x0".into(),
                bank: RegisterType::Ctrl,
            }
            .add_span(&(16..18))),
        );
        // Register names should be case sensitive
        assert_eq!(
            compile(".text\nmain: reg pc, x0, ft1, ft2"),
            Err(ErrorKind::UnknownRegister {
                name: "pc".into(),
                bank: RegisterType::Ctrl,
            }
            .add_span(&(16..18))),
        );
        assert_eq!(
            compile(".text\nmain: reg PC, PC, ft1, ft2"),
            Err(ErrorKind::UnknownRegister {
                name: "PC".into(),
                bank: RegisterType::Int,
            }
            .add_span(&(20..22))),
        );
        assert_eq!(
            compile(".text\nmain: reg PC, x0, x0, ft2"),
            Err(ErrorKind::UnknownRegister {
                name: "x0".into(),
                bank: RegisterType::Float(FloatType::Float),
            }
            .add_span(&(24..26))),
        );
        assert_eq!(
            compile(".text\nmain: reg PC, x0, FD1, ft2"),
            Err(ErrorKind::UnknownRegister {
                name: "FD1".into(),
                bank: RegisterType::Float(FloatType::Float),
            }
            .add_span(&(24..27))),
        );
        assert_eq!(
            compile(".text\nmain: reg PC, x0, ft1, fs2"),
            Err(ErrorKind::UnknownRegister {
                name: "fs2".into(),
                bank: RegisterType::Float(FloatType::Double),
            }
            .add_span(&(29..32))),
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
            .add_span(&(6..7))),
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
                .add_span(&(13..14))),
                "{directive}"
            );
            assert_eq!(
                compile(&format!(".data\n.{directive} 1, 2\n.text\nmain: nop")),
                Err(ErrorKind::IncorrectDirectiveArgumentNumber {
                    expected: ArgumentNumber::new(1, false),
                    found: 2
                }
                .add_span(&(14..18))),
                "{directive}"
            );
        }
    }

    #[test]
    fn padding_negative() {
        for directive in ["zero  ", "align ", "balign"] {
            assert_eq!(
                compile(&format!(".data\n.{directive} -1\n.text\nmain: nop")),
                Err(ErrorKind::UnallowedNegativeValue(-1).add_span(&(14..16))),
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
                .add_span(&(14..17))),
                "{directive}"
            );
            assert_eq!(
                compile(&format!(".data\n.{directive} 1.0\n.text\nmain: nop")),
                Err(ErrorKind::UnallowedFloat.add_span(&(14..17))),
                "{directive}"
            );
        }
        assert_eq!(
            compile(".text\nmain: imm 0, 0, 1.0"),
            Err(ErrorKind::UnallowedFloat.add_span(&(22..25))),
        );
        assert_eq!(
            compile(".text\nmain: reg PC, 0, ft1, ft2"),
            Err(ErrorKind::IncorrectArgumentType {
                expected: ArgumentType::RegisterName,
                found: ArgumentType::Expression,
            }
            .add_span(&(20..21))),
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
                .add_span(&(13..14))),
                "{directive}"
            );
        }
    }

    #[test]
    fn data_unaligned() {
        for (directive, size) in [
            ("half  ", 2),
            ("word  ", 4),
            ("dword ", 8),
            ("float ", 4),
            ("double", 8),
        ] {
            assert_eq!(
                compile(&format!(".data\n.byte 0\n.{directive} 1\n.text\nmain: nop")),
                Err(ErrorKind::DataUnaligned {
                    address: 17,
                    word_size: 4,
                    alignment: size,
                }
                .add_span(&(22..23))),
                "{directive}",
            );
        }
    }

    #[test]
    fn int_args_size() {
        // Data directives
        assert_eq!(
            compile(".data\n.byte 256\n.text\nmain: nop"),
            Err(ErrorKind::IntegerTooBig(256, -128..256).add_span(&(12..15))),
        );
        assert_eq!(
            compile(".data\n.byte -129\n.text\nmain: nop"),
            Err(ErrorKind::IntegerTooBig(-129, -128..256).add_span(&(12..16))),
        );
        assert_eq!(
            compile(".data\n.half 65536\n.text\nmain: nop"),
            Err(ErrorKind::IntegerTooBig(65536, -32768..65536).add_span(&(12..17))),
        );
        // Instruction arguments
        assert_eq!(
            compile(".text\nmain: imm 8, 0, 0"),
            Err(ErrorKind::IntegerTooBig(8, -8..8).add_span(&(16..17))),
        );
        assert_eq!(
            compile(".text\nmain: imm -9, 0, 0"),
            Err(ErrorKind::IntegerTooBig(-9, -8..8).add_span(&(16..18))),
        );
        assert_eq!(
            compile(".text\nmain: imm 0, 256, 0"),
            Err(ErrorKind::IntegerTooBig(256, 0..256).add_span(&(19..22))),
        );
        assert_eq!(
            compile(".text\nmain: imm 0, -1, 0"),
            Err(ErrorKind::IntegerTooBig(-1, 0..256).add_span(&(19..21))),
        );
        assert_eq!(
            compile(".text\nmain: imm 0, 0, 20"),
            Err(ErrorKind::IntegerTooBig(20, 0..16).add_span(&(22..24))),
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
            .add_span(&(13..16))),
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
            .add_span(&(14..15))),
        );
    }

    #[test]
    fn incorrect_instruction_syntax() {
        let assert = |err, syntaxes: &[&str], expected_span| match err {
            Err(CompileError {
                span,
                kind: ErrorKind::IncorrectInstructionSyntax(s),
            }) => {
                assert_eq!(span, expected_span);
                assert_eq!(s.into_iter().map(|x| x.0).collect::<Vec<_>>(), syntaxes);
            }
            x => panic!("Incorrect result, expected ErrorKind::IncorrectInstructionSyntax: {x:?}"),
        };
        assert(compile(".text\nmain: nop 1"), &["nop"], 16..17);
        assert(
            compile(".text\nmain: multi &, 1"),
            &["multi", "multi $"],
            18..22,
        );
    }

    #[test]
    fn expr_eval() {
        assert_eq!(
            compile(".data\n.byte 1/0\n.text\nmain: nop"),
            Err(ErrorKind::DivisionBy0.add_span(&(14..15))),
        );
        assert_eq!(
            compile(".text\nmain: imm 0, 0, 1/0"),
            Err(ErrorKind::DivisionBy0.add_span(&(24..25))),
        );
        assert_eq!(
            compile(".data\n.float ~1.0\n.text\nmain: nop"),
            Err(
                ErrorKind::UnallowedFloatOperation(OperationKind::UnaryNegation)
                    .add_span(&(13..14))
            ),
        );
        for (op, c) in [
            (OperationKind::BitwiseOR, '|'),
            (OperationKind::BitwiseAND, '&'),
            (OperationKind::BitwiseXOR, '^'),
        ] {
            assert_eq!(
                compile(&format!(".data\n.float 1.0 {c} 2.0\n.text\nmain: nop")),
                Err(ErrorKind::UnallowedFloatOperation(op).add_span(&(17..18))),
            );
        }
    }

    #[test]
    fn missing_main() {
        assert_eq!(
            compile(".text\nnop"),
            Err(ErrorKind::MissingMainLabel("main".into()).add_span(&(9..10))),
        );
        assert_eq!(
            compile(".text\nnop\n.data"),
            Err(ErrorKind::MissingMainLabel("main".into()).add_span(&(9..10))),
        );
    }

    #[test]
    fn main_in_data() {
        assert_eq!(
            compile(".data\nmain: .byte 1\n.text\nnop"),
            Err(ErrorKind::MainOutsideCode("main".into()).add_span(&(6..11))),
        );
    }

    #[test]
    fn duplicate_label() {
        assert_eq!(
            compile(".text\nmain: nop\nmain: nop"),
            Err(ErrorKind::DuplicateLabel("main".into(), 6..11).add_span(&(16..21))),
        );
        assert_eq!(
            compile(".text\nmain: nop\nlabel:\nlabel: nop"),
            Err(ErrorKind::DuplicateLabel("label".into(), 16..22).add_span(&(23..29))),
        );
    }

    #[test]
    fn section_full() {
        // Instructions
        assert_eq!(
            compile(".text\nmain: nop\nnop\nnop\nnop\nnop"),
            Err(ErrorKind::MemorySectionFull("Instructions").add_span(&(28..31))),
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
}
