use once_cell::sync::Lazy;
use regex::{NoExpand, Regex};

use crate::architecture::{
    Architecture, ComponentType, DirectiveAction, DirectiveAlignment, DirectiveData,
    DirectiveSegment, FloatType, Instruction as InstructionDefinition, InstructionFieldType,
    StringType,
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

static RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"[fF][0-9]+").expect("This shouldn't fail"));

type Output = Vec<(Spanned<Argument>, usize)>;

fn parse_instruction<'a>(
    arch: &'a Architecture,
    (name, name_span): Spanned<&str>,
    args: &Spanned<Vec<Spanned<Token>>>,
) -> Result<(&'a InstructionDefinition<'a>, Output), CompileError> {
    let mut errs = Vec::new();
    for inst in arch.find_instructions(name) {
        let result = inst.syntax.parser.parse(args);
        match result {
            Ok(parsed_args) => return Ok((inst, parsed_args)),
            Err(e) => errs.push((inst.syntax.user_syntax.to_string(), e)),
        }
    }
    Err(if errs.is_empty() {
        ErrorKind::UnknownInstruction(name.to_string()).add_span(&name_span)
    } else {
        ErrorKind::IncorrectInstructionSyntax(errs).add_span(&args.1)
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
    /// Span of the instruction in the code
    pub user: Span,
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

#[derive(Debug, PartialEq, Clone)]
pub struct CompiledCode {
    pub label_table: LabelTable,
    pub instructions: Vec<Instruction>,
    pub data_memory: Vec<Data>,
}

fn take_spanned_vec<T>(dest: &mut Vec<Spanned<T>>) -> Vec<T> {
    std::mem::take(dest).into_iter().map(|x| x.0).collect()
}

/// Amount of arguments expected by a directive
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArgumentNumber {
    /// Minimum expected amount
    pub amount: usize,
    /// Whether it's allowed to use more arguments
    pub at_least: bool,
}

impl ArgumentNumber {
    #[must_use]
    pub const fn new(amount: usize, at_least: bool) -> Self {
        Self { amount, at_least }
    }
}

fn check_arg_num<T>(expected: ArgumentNumber, args: &Spanned<Vec<T>>) -> Result<(), CompileError> {
    let len = args.0.len();
    if len < expected.amount || (!expected.at_least && len != expected.amount) {
        return Err(ErrorKind::IncorrectDirectiveArgumentNumber {
            expected,
            found: args.0.len(),
        }
        .add_span(&args.1));
    };
    Ok(())
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
    if let Some((alignment, span)) = alignment.take() {
        if let Some((start, size)) = section.try_align(alignment).add_span(&span)? {
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
            check_arg_num(ArgumentNumber::new(1, false), &args)?;
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
            check_arg_num(ArgumentNumber::new(1, true), &args)?;
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
            check_arg_num(ArgumentNumber::new(1, true), &args)?;
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
            check_arg_num(ArgumentNumber::new(1, true), &args)?;
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
                        check_arg_num(ArgumentNumber::new(0, false), &directive.args)?;
                        current_section = Some((new_section, node.statement.1));
                    }
                    (DirectiveAction::GlobalSymbol(_), _) => todo!(),
                    (DirectiveAction::Alignment(align_type), Some((DirectiveSegment::Data, _))) => {
                        check_arg_num(ArgumentNumber::new(1, false), &directive.args)?;
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
                            directive.name.1,
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
                let (def, args) =
                    parse_instruction(arch, (&name, span.clone()), &instruction.args)?;
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
                    InstructionFieldType::Cop { .. } => {
                        unreachable!("This field type shouldn't be used for instruction arguments")
                    }
                    #[allow(clippy::cast_possible_wrap)]
                    InstructionFieldType::Co => (def.co.0 as i64, def.name.to_string()),
                    val_type @ (InstructionFieldType::Address
                    | InstructionFieldType::ImmSigned
                    | InstructionFieldType::ImmUnsigned
                    | InstructionFieldType::OffsetBytes
                    | InstructionFieldType::OffsetWords) => {
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
                            InstructionFieldType::OffsetWords => offset / i64::from(word_size),
                            InstructionFieldType::OffsetBytes => offset,
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
                                return Err(ErrorKind::IncorrectArgumentType {
                                    expected: ArgumentType::RegisterName,
                                    found: ArgumentType::Expression,
                                }
                                .add_span(&span))
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
                            .ok_or_else(|| {
                                ErrorKind::UnknownRegisterBank(bank_type).add_span(&span)
                            })?;
                        let (i, _) = bank.find_register(&name).ok_or_else(|| {
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
                            InstructionFieldType::ImmSigned
                                | InstructionFieldType::OffsetBytes
                                | InstructionFieldType::OffsetWords
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
                InstructionFieldType::Cop { value } => Some((&field.range, value)),
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
    use super::{BitField, Integer, Value};
    use super::{CompileError, CompiledCode, Data, Instruction, LabelTable, Span};
    use crate::architecture::{BitRange, FloatType, IntegerType, NonEmptyRangeInclusiveU8};

    fn compile(src: &str) -> Result<CompiledCode, CompileError> {
        use crate::architecture::Architecture;
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
        let x = compile(".text\nmain: reg ctrl1, x2, ft1, ft2").unwrap();
        let binary = "01001000000000000000000000010010";
        let tbl = label_table([("main", 0, 6..11)]);
        assert_eq!(x.label_table, tbl);
        assert_eq!(
            x.instructions,
            vec![inst(0, &["main"], "reg ctrl1 x2 ft1 ft2", binary, 12..35)]
        );
        assert_eq!(x.data_memory, vec![]);
        let x = compile(".text\nmain: reg ctrl1, two, ft1, ft2").unwrap();
        assert_eq!(x.label_table, tbl);
        assert_eq!(
            x.instructions,
            vec![inst(0, &["main"], "reg ctrl1 two ft1 ft2", binary, 12..36)]
        );
        assert_eq!(x.data_memory, vec![]);
    }

    #[test]
    fn instruction_fields_immediate() {
        let x = compile(".text\nmain: imm -7, 11, 15").unwrap();
        let binary = "00100100000000000011110000010110";
        assert_eq!(x.label_table, label_table([("main", 0, 6..11)]));
        assert_eq!(
            x.instructions,
            vec![inst(0, &["main"], "imm -7 11 15", binary, 12..26)]
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
}
