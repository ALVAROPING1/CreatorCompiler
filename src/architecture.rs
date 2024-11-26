//! Module containing the specification of the architecture definition structure
//!
//! The entry point for the specification is the [`Architecture`] struct

use schemars::{schema_for, JsonSchema};
use serde::Deserialize;

mod utils;
use utils::{BaseN, Integer, Number, Pair};
pub use utils::{NonEmptyRangeInclusiveU64, NonEmptyRangeInclusiveU8};

mod json;

/// Architecture description
#[derive(Deserialize, JsonSchema, Debug, Clone)]
pub struct Architecture<'a> {
    /// Metadata about the architecture
    /// Order of elements is assumed to be name, bits, description, data format,
    /// memory alignment, main function, passing convention, and sensitive register
    /// name
    #[serde(borrow)]
    arch_conf: Config<'a>,
    /// Components (register banks) of the architecture. It's assumed that the first register of
    /// the first bank will contain the program counter
    components: Vec<Component<'a>>,
    /// Instructions allowed
    instructions: Vec<Instruction<'a>>,
    /// Pseudoinstructions allowed
    pseudoinstructions: Vec<Pseudoinstruction<'a>>,
    /// Directives allowed
    directives: Vec<Directive<'a>>,
    /// Memory layout of the architecture
    /// Order of elements is assumed to be text start/end, data start/end, and stack start/end
    memory_layout: MemoryLayout,
}

/// Architecture metadata attributes
#[derive(Deserialize, Debug, PartialEq, Eq, Clone, Copy)]
#[serde(try_from = "[json::Config<'a>; 8]")]
pub struct Config<'a> {
    /// Name of the architecture
    name: &'a str,
    /// Word size
    word_size: u8,
    /// Description of the architecture
    description: &'a str,
    /// Storage format of the architecture (big/little endian)
    data_format: DataFormat,
    /// Whether to enable memory alignment
    memory_alignment: bool,
    /// Name of the `main` function of the program
    main_function: &'a str,
    /// Whether to enable function parameter passing convention checks
    passing_convention: bool,
    /// TODO: what does this represent? is this used currently?
    sensitive_register_name: bool,
}
utils::schema_from!(Config<'a>, [json::Config<'a>; 8]);

/// Endianness of data in the architecture
#[derive(Deserialize, JsonSchema, Debug, PartialEq, Eq, Clone, Copy)]
#[serde(rename_all = "snake_case")]
pub enum DataFormat {
    BigEndian,
    LittleEndian,
}

/// Register bank
#[derive(Deserialize, JsonSchema, Debug, PartialEq, Clone)]
pub struct Component<'a> {
    /// Name of the register bank
    name: &'a str,
    /// Type of the registers
    r#type: ComponentType,
    /// Whether the registers have double the word size
    pub double_precision: bool,
    /// If the registers have double the word size, how this size is achieved
    pub double_precision_type: Option<PrecisionType>,
    /// Registers in this bank
    elements: Vec<Register<'a>>,
}

/// Types of register banks allowed
#[derive(Deserialize, JsonSchema, Debug, PartialEq, Eq, Clone, Copy)]
pub enum ComponentType {
    /// Control registers
    #[serde(rename = "ctrl_registers")]
    Ctrl,
    /// Integer registers
    #[serde(rename = "int_registers")]
    Int,
    /// Floating point registers
    #[serde(rename = "fp_registers")]
    Float,
}

/// Type of registers allowed
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum RegisterType {
    /// Control registers
    Ctrl,
    /// Integer registers
    Int,
    /// Floating point registers
    Float(FloatType),
}

/// Type of registers bigger than a single word
#[derive(Deserialize, JsonSchema, Debug, PartialEq, Eq, Clone, Copy)]
#[serde(rename_all = "snake_case")]
pub enum PrecisionType {
    /// Register has a bigger size
    Extended,
    /// Register is made up of 2 word size registers
    Linked,
}

/// Register specification
#[derive(Deserialize, JsonSchema, Debug, PartialEq, Clone)]
pub struct Register<'a> {
    /// List of aliases
    #[serde(borrow)]
    name: Vec<&'a str>,
    /// Size
    #[serde(deserialize_with = "utils::from_str")]
    #[schemars(with = "utils::StringOrT<u8>")]
    nbits: u8,
    /// Current value of the register
    value: Number,
    /// Default value of the register
    default_value: Option<Number>,
    /// Properties of this register
    properties: Vec<RegisterProperty>,
    /// Smaller registers that make up this register when the double precision mode is `Linked`
    pub simple_reg: Option<[&'a str; 2]>,
}

/// Properties of a register
#[derive(Deserialize, JsonSchema, Debug, PartialEq, Eq, Clone, Copy)]
#[serde(rename_all = "snake_case")]
pub enum RegisterProperty {
    /// Register can be read
    Read,
    /// Register can be written
    Write,
    /// Register should be preserved across routine calls
    Saved,
    /// Register contains the program counter
    ProgramCounter,
    /// Register to save PC in during interruptions
    ExceptionProgramCounter,
    /// Interruption ID register
    EventCause,
    /// TODO: is this ever used?
    StatusRegister,
    /// Writes to this register are ignored. Ignored if `Write` is set
    IgnoreWrite,
    /// Register contains the stack pointer
    StackPointer,
    /// Register contains the global pointer. Only used in the UI
    GlobalPointer,
    /// Register contains the stack frame pointer. Only used in the UI
    FramePointer,
}

/// Instruction specification
#[derive(Deserialize, JsonSchema, Debug, Clone)]
pub struct Instruction<'a> {
    /// Name of the instruction
    pub name: &'a str,
    /// Type of the instruction
    r#type: InstructionType,
    /// Syntax of the instruction
    #[serde(flatten)]
    pub syntax: InstructionSyntax<'a, BitRange>,
    /// Binary op code
    pub co: BaseN<2>,
    /// Size of the instruction
    pub nwords: u8,
    /// Execution time of the instruction
    clk_cycles: Option<Integer>,
    /// Code to execute for the instruction
    // Can't be a reference because there might be escape sequences, which require
    // modifying the data on deserialization
    pub definition: String,
    /// Determines whether the field `i` is separated in the resulting binary instruction. Ignored
    #[deprecated = "Values are obtained from the variant used in BitPosition in each field"]
    separated: Option<Vec<bool>>,
    /// Help information of the instruction
    help: &'a str,
    /// Properties of the instruction
    properties: Option<Vec<InstructionProperties>>,
}

/// Allowed instruction types
#[derive(Deserialize, JsonSchema, Debug, PartialEq, Eq, Clone, Copy)]
pub enum InstructionType {
    #[serde(rename = "Arithmetic integer")]
    ArithmeticInteger,
    #[serde(rename = "Arithmetic floating point")]
    ArithmeticFloat,
    Logic,
    Comparison,
    Control,
    #[serde(rename = "I/O")]
    IO,
    #[serde(rename = "Conditional bifurcation")]
    ConditionalBifurcation,
    #[serde(rename = "Unconditional bifurcation")]
    UnconditionalBifurcation,
    Syscall,
    #[serde(rename = "Function call")]
    FunctionCall,
    #[serde(rename = "Transfer between registers")]
    TransferRegister,
    #[serde(rename = "Memory access")]
    MemoryAccess,
    Other,
}

/// Instruction syntax specification
#[derive(Deserialize, Debug, Clone)]
#[serde(try_from = "json::InstructionSyntax<BitRange>")]
pub struct InstructionSyntax<'a, BitRange> {
    /// Parser for the syntax of the instruction
    pub parser: crate::parser::Instruction<'a>,
    /// Translated instruction's syntax
    pub output_syntax: &'a str,
    /// User representation of the instruction's syntax
    pub user_syntax: String,
    /// Parameters of the instruction
    pub fields: Vec<InstructionField<'a, BitRange>>,
}
utils::schema_from!(InstructionSyntax<'a, T>, json::InstructionSyntax<T>);

/// Allowed instruction properties
#[derive(Deserialize, JsonSchema, Debug, PartialEq, Eq, Clone, Copy)]
pub enum InstructionProperties {
    #[serde(rename = "exit_subrutine")]
    ExitSubrutine,
    #[serde(rename = "enter_subrutine")]
    EnterSubrutine,
}

/// Instruction field specification
#[derive(Deserialize, JsonSchema, Debug, PartialEq, Eq, Clone, Copy)]
pub struct InstructionField<'a, BitRange> {
    /// Name of the field
    pub name: &'a str,
    /// Type of the field
    #[serde(flatten)]
    pub r#type: FieldType,
    /// Range of bits of the field. Ignored for pseudoinstructions
    #[serde(flatten)]
    pub range: BitRange,
}

/// Range of bits of a field in a binary instruction
#[derive(Deserialize, Debug, PartialEq, Eq, Clone)]
#[serde(try_from = "json::BitRange")]
pub struct BitRange(Vec<NonEmptyRangeInclusiveU8>);
utils::schema_from!(BitRange, json::BitRange);

/// Allowed instruction field types
#[derive(Deserialize, JsonSchema, Debug, PartialEq, Eq, Clone, Copy)]
#[serde(rename_all = "snake_case")]
#[serde(tag = "type")]
pub enum FieldType {
    /// Opcode of the instruction
    Co,
    /// Extended operation code
    Cop {
        /// Fixed value of this field in the binary instruction (specified as a binary string)
        #[serde(rename = "valueField")]
        value: BaseN<2>,
    },
    /// Immediate signed integer
    #[serde(rename = "inm-signed")]
    ImmSigned,
    /// Immediate unsigned integer
    #[serde(rename = "inm-unsigned")]
    ImmUnsigned,
    /// Offset from the next instruction's address in bytes
    #[serde(rename = "offset_bytes")]
    OffsetBytes,
    /// Offset from the next instruction's address in words
    #[serde(rename = "offset_words")]
    OffsetWords,
    /// Control register
    #[serde(rename = "Ctrl-Reg")]
    CtrlReg,
    /// Integer register
    #[serde(rename = "INT-Reg")]
    IntReg,
    /// Double precision floating point register
    #[serde(rename = "DFP-Reg")]
    DoubleFPReg,
    /// Single precision floating point register
    #[serde(rename = "SFP-Reg")]
    SingleFPReg,
    /// Immediate address, equivalent to `ImmUnsigned`
    Address,
}

/// Pseudoinstruction specification
#[derive(Deserialize, JsonSchema, Debug, Clone)]
pub struct Pseudoinstruction<'a> {
    /// Name of the pseudoinstruction
    pub name: &'a str,
    /// Syntax of the instruction
    #[serde(flatten)]
    pub syntax: InstructionSyntax<'a, ()>,
    /// Code to execute for the instruction
    // Can't be a reference because there might be escape sequences, which require
    // modifying the data on deserialization
    pub definition: String,
    /// Help information of the instruction
    help: &'a str,
    /// Properties of the instruction
    properties: Option<Vec<InstructionProperties>>,
}

/// Directive specification
#[derive(Deserialize, Debug, PartialEq, Eq, Clone, Copy)]
#[serde(try_from = "json::Directive")]
pub struct Directive<'a> {
    /// Name of the directive
    pub name: &'a str,
    /// Action of the directive
    pub action: DirectiveAction<DirectiveData>,
}
utils::schema_from!(Directive<'a>, json::Directive);

/// Allowed actions for directives
#[derive(Deserialize, JsonSchema, Debug, PartialEq, Eq, Clone, Copy)]
#[serde(untagged)]
#[serde(rename_all = "snake_case")]
pub enum DirectiveAction<DirectiveData> {
    /// Switch to the given segment
    Segment(DirectiveSegment),
    /// Store symbols in an external symbols table
    GlobalSymbol(GlobalSymbol),
    /// Align the next data value to a given size
    Alignment(DirectiveAlignment),
    /// Add data to the data segment
    Data(DirectiveData),
}

/// Store symbols in an external symbols table
#[derive(Deserialize, JsonSchema, Debug, PartialEq, Eq, Clone, Copy)]
#[serde(rename_all = "snake_case")]
pub enum GlobalSymbol {
    GlobalSymbol,
}

/// Memory segment to switch to
#[derive(Deserialize, JsonSchema, Debug, PartialEq, Eq, Clone, Copy)]
pub enum DirectiveSegment {
    #[serde(rename = "code_segment")]
    Code,
    #[serde(rename = "data_segment")]
    Data,
}

/// Data alignment modes
#[derive(Deserialize, JsonSchema, Debug, PartialEq, Eq, Clone, Copy)]
pub enum DirectiveAlignment {
    /// Align next element to n bytes
    #[serde(rename = "balign")]
    Byte,
    /// Align next element to 2^n bytes
    #[serde(rename = "align")]
    Exponential,
}

/// Data segment types
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum DirectiveData {
    /// Store n * size null bytes in the data segment
    Space(u8),
    /// Store string
    String(StringType),
    /// Store integer
    Int(u8, IntegerType),
    /// Store floating point value
    Float(FloatType),
}

/// Types of strings allowed
#[derive(Deserialize, JsonSchema, Debug, PartialEq, Eq, Clone, Copy)]
#[serde(rename_all = "snake_case")]
pub enum StringType {
    /// Ascii string with a terminating null byte (`\0`)
    AsciiNullEnd,
    /// Ascii string without a terminating null byte (`\0`)
    AsciiNotNullEnd,
}

/// Types of integers allowed
#[derive(Deserialize, JsonSchema, Debug, Clone, Copy, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum IntegerType {
    Byte,
    HalfWord,
    Word,
    DoubleWord,
}

/// Types of floats allowed
#[derive(Deserialize, JsonSchema, Debug, PartialEq, Eq, Clone, Copy)]
#[serde(rename_all = "snake_case")]
pub enum FloatType {
    /// 32 bit float
    Float,
    /// 64 bit double
    Double,
}

/// Memory layout of the architecture
#[derive(Deserialize, Debug, PartialEq, Eq, Clone)]
#[serde(try_from = "[Pair<json::MemoryLayoutKeys, BaseN<16>>; 6]")]
pub struct MemoryLayout {
    /// Addresses reserved for the text segment
    text: NonEmptyRangeInclusiveU64,
    /// Addresses reserved for the data segment
    data: NonEmptyRangeInclusiveU64,
    /// Addresses reserved for the stack segment
    stack: NonEmptyRangeInclusiveU64,
}
utils::schema_from!(MemoryLayout, [Pair<json::MemoryLayoutKeys, BaseN<16>>; 6]);

impl<'a> Architecture<'a> {
    /// Generate a `JSON` schema
    ///
    /// # Panics
    ///
    /// Panics if the data can't be serialized. This should never happen
    #[must_use]
    pub fn schema() -> String {
        let schema = schema_for!(Architecture);
        serde_json::to_string_pretty(&schema)
            .expect("Input is known and fixed, so it shouldn't error out")
    }

    /// Load architecture data from `JSON`
    ///
    /// # Parameters
    ///
    /// * `src`: `JSON` data to deserialize
    ///
    /// # Errors
    ///
    /// Errors if the input `JSON` data is invalid, either because it's ill-formatted or because it
    /// doesn't conform to the specification
    pub fn from_json(src: &str) -> serde_json::Result<Architecture> {
        serde_json::from_str(src)
    }

    /// Find the directive name that switches to the given segment
    ///
    /// # Parameters
    ///
    /// * `segment`: action to search for
    #[must_use]
    pub fn get_directive_segment(&self, segment: DirectiveSegment) -> &str {
        self.directives
            .iter()
            .find(|&directive| directive.action == DirectiveAction::Segment(segment))
            .expect("There should be a directive defined for all segment types")
            .name
    }

    /// Finds the action associated with the directive with the given name
    ///
    /// # Parameters
    ///
    /// * `name`: name to search for
    #[must_use]
    pub fn find_directive(&self, name: &str) -> Option<DirectiveAction<DirectiveData>> {
        self.directives
            .iter()
            .find(|directive| directive.name == name)
            .map(|directive| directive.action)
    }

    /// Gets the word size of the architecture
    #[must_use]
    pub const fn word_size(&self) -> u8 {
        self.arch_conf.word_size
    }

    /// Gets the name of the label used as the entry point of the code
    #[must_use]
    pub const fn main_label(&self) -> &str {
        self.arch_conf.main_function
    }

    /// Gets the code section's start/end addresses
    #[must_use]
    pub const fn code_section(&self) -> &NonEmptyRangeInclusiveU64 {
        &self.memory_layout.text
    }

    /// Gets the data section's start/end addresses
    #[must_use]
    pub const fn data_section(&self) -> &NonEmptyRangeInclusiveU64 {
        &self.memory_layout.data
    }

    /// Gets the instructions with the given name
    ///
    /// # Parameters
    ///
    /// * `name`: name to search for
    pub fn find_instructions<'b: 'c, 'c>(
        &'b self,
        name: &'c str,
    ) -> impl Iterator<Item = &'b Instruction> + 'c {
        self.instructions
            .iter()
            .filter(move |instruction| instruction.name == name)
    }

    /// Gets the pseudoinstructions with the given name
    ///
    /// # Parameters
    ///
    /// * `name`: name to search for
    pub fn find_pseudoinstructions<'b: 'c, 'c>(
        &'b self,
        name: &'c str,
    ) -> impl Iterator<Item = &'b Pseudoinstruction> + 'c {
        self.pseudoinstructions
            .iter()
            .filter(move |instruction| instruction.name == name)
    }

    /// Gets the register banks with registers of the given type
    ///
    /// # Parameters
    ///
    /// * `type`: type of the bank wanted
    pub fn find_banks(&self, r#type: RegisterType) -> impl Iterator<Item = &Component> {
        let eq = move |bank: &&Component| match r#type {
            RegisterType::Int => matches!(bank.r#type, ComponentType::Int),
            RegisterType::Ctrl => matches!(bank.r#type, ComponentType::Ctrl),
            RegisterType::Float(FloatType::Float) => matches!(
                (bank.r#type, bank.double_precision_type),
                (ComponentType::Float, None | Some(PrecisionType::Extended))
            ),
            RegisterType::Float(FloatType::Double) => {
                matches!(bank.r#type, ComponentType::Float) && bank.double_precision_type.is_some()
            }
        };
        self.components.iter().filter(eq)
    }
}

impl<'a> Component<'a> {
    /// Finds the register with the given name
    ///
    /// # Parameters
    ///
    /// * `name`: name of the register to search for
    #[must_use]
    pub fn find_register(&self, name: &str) -> Option<(usize, &Register)> {
        self.elements
            .iter()
            .enumerate()
            .find(|(_, reg)| reg.name.contains(&name))
    }
}

impl BitRange {
    /// Calculates the size of this range in bits
    #[must_use]
    pub fn size(&self) -> usize {
        // We need a closure because there are multiple methods for different types
        #[allow(clippy::redundant_closure_for_method_calls)]
        self.iter()
            .map(|x| x.size())
            .reduce(|acc, val| acc.saturating_add(val.into()))
            .expect("There should always be at least 1 field")
            .get()
            .into()
    }

    /// Gets an iterator of the ranges of bits specified
    pub fn iter(&self) -> impl Iterator<Item = &NonEmptyRangeInclusiveU8> {
        self.0.iter()
    }

    /// Creates a new `BitRange`
    #[must_use]
    pub fn build(ranges: Vec<NonEmptyRangeInclusiveU8>) -> Option<Self> {
        if ranges.is_empty() {
            return None;
        }
        Some(Self(ranges))
    }
}
