use schemars::{schema_for, JsonSchema};
use serde::Deserialize;

mod utils;
use utils::{Hex, Integer, Number, Pair};

mod json;

/// Architecture description
#[derive(Deserialize, JsonSchema, Debug, PartialEq, Clone)]
pub struct Architecture<'a> {
    /// Metadata about the architecture
    /// Order of elements is assumed to be name, bits, description, data format,
    /// memory alignment, main function, passing convention, and sensitive register
    /// name
    #[serde(borrow)]
    arch_conf: [Pair<MetadataKeys, &'a str>; 8],
    /// Components (register banks) of the architecture. It's assumed that the first register of
    /// the first bank will contain the program counter
    components: Vec<Component<'a>>,
    /// Instructions allowed
    instructions: Vec<Instruction<'a>>,
    /// Pseudoinstructions allowed
    pseudoinstructions: Vec<Pseudoinstruction<'a>>,
    /// Directives allowed
    #[schemars(with = "Vec<json::Directive>")]
    directives: Vec<Directive<'a>>,
    /// Memory layout of the architecture
    /// Order of elements is assumed to be text start/end, data start/end, and stack start/end
    #[schemars(with = "[Pair<MemoryLayoutKeys, String>; 6]")]
    memory_layout: [Pair<MemoryLayoutKeys, Hex>; 6],
}

/// Architecture metadata attribute types
#[derive(Deserialize, JsonSchema, Debug, PartialEq, Eq, Clone, Copy)]
pub enum MetadataKeys {
    /// Name of the architecture
    Name,
    /// Word size
    Bits,
    /// Description of the architecture
    Description,
    /// Storage format of the architecture (big/little endian)
    #[serde(rename = "Data Format")]
    DataFormat,
    /// Whether to enable memory alignment
    #[serde(rename = "Memory Alignment")]
    MemoryAlignment,
    /// Name of the `main` function of the program
    #[serde(rename = "Main Function")]
    MainFunction,
    /// Whether to enable function parameter passing convention checks
    #[serde(rename = "Passing Convention")]
    PassingConvention,
    /// TODO: what does this represent? is this used currently?
    #[serde(rename = "Sensitive Register Name")]
    SensitiveRegisterName,
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
    name: Vec<&'a str>,
    /// Size
    nbits: &'a str,
    /// Current value of the register
    value: Number,
    /// Default value of the register
    default_value: Number,
    /// Properties of this register
    properties: Vec<RegisterProperty>,
    /// Smaller registers that make up this register when the double precision mode is `Linked`
    simple_reg: Option<[&'a str; 2]>,
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
#[derive(Deserialize, JsonSchema, Debug, PartialEq, Eq, Clone)]
pub struct Instruction<'a> {
    /// Name of the instruction
    name: &'a str,
    /// Type of the instruction
    r#type: InstructionType,
    /// Order of the fields/literal characters in the instruction text. `[fF]\d+` is interpreted as
    /// the field with index i of the instruction, although the number is ignored and `signature_raw`
    /// is used instead. Other characters are interpreted literally
    /// Ex: `F0 F3 F1 (F2)`
    pub signature_definition: &'a str,
    /// Comma-separated list of the type of each field in the instruction, in the order in which
    /// they appear in the instruction. Valid values are those in `InstructionFieldType`, except
    /// `Co` and `Cop`. Instruction opcode is specified literally, other characters are interpreted
    /// literally so that `signature_definition` can capture the value corresponding to each field
    /// when used as a regex
    pub signature: &'a str,
    /// Same as `signature`, but with a space-separated list of field names
    #[serde(rename = "signatureRaw")]
    pub signature_raw: &'a str,
    /// Binary op code
    pub co: &'a str,
    /// Binary extended op code
    cop: &'a str,
    /// Size of the instruction
    pub nwords: u8,
    /// Execution time of the instruction
    clk_cycles: Option<Integer>,
    /// Parameters of the instruction
    #[schemars(with = "Vec<InstructionField<json::BitRange>>")]
    pub fields: Vec<InstructionField<'a, BitRange>>,
    /// Code to execute for the instruction
    // Can't be a reference because there might be escape sequences, which require
    // modifying the data on deserialization
    definition: String,
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
    #[serde(rename = "Transfer between registers")]
    TransferRegister,
    #[serde(rename = "Memory access")]
    MemoryAccess,
    Other,
}

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
    pub r#type: InstructionFieldType,
    /// Range of bits of the field. Ignored for pseudoinstructions
    #[serde(flatten)]
    pub range: BitRange,
    /// Fixed value of this field in the binary instruction (specified as a binary string). Only
    /// used for `Cop` fields
    #[serde(rename = "valueField")]
    pub value_field: Option<&'a str>,
}

/// Range of bits of a field in a binary instruction
#[derive(Deserialize, Debug, PartialEq, Eq, Clone)]
#[serde(try_from = "json::BitRange")]
pub struct BitRange(Vec<(u8, u8)>);

/// Allowed instruction field types
#[derive(Deserialize, JsonSchema, Debug, PartialEq, Eq, Clone, Copy)]
#[serde(rename_all = "snake_case")]
pub enum InstructionFieldType {
    /// Opcode of the instruction
    Co,
    /// Extended operation code
    Cop,
    /// Inmediatte signed integer
    #[serde(rename = "inm-signed")]
    InmSigned,
    /// Inmediatte unsigned integer
    #[serde(rename = "inm-unsigned")]
    InmUnsigned,
    /// Offset from the instruction address in bytes
    #[serde(rename = "offset_bytes")]
    OffsetBytes,
    /// Offset from the instruction address in words
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
    /// Inmediatte address, equivalent to `InmUnsigned`
    Address,
}

/// Pseudoinstruction specification
#[derive(Deserialize, JsonSchema, Debug, PartialEq, Eq, Clone)]
struct Pseudoinstruction<'a> {
    /// Name of the pseudoinstruction
    name: &'a str,
    /// Order of the fields/literal characters in the instruction text. `[fF]\d+` is interpreted as
    /// the field with index i of the instruction, although the number is ignored and `signature_raw`
    /// is used instead. Other characters are interpreted literally
    /// Ex: `F0 F3 F1 (F2)`
    signature_definition: &'a str,
    /// Comma-separated list of the type of each field in the instruction, in the order in which
    /// they appear in the instruction. Valid values are those in `InstructionFieldType`, except
    /// `Co` and `Cop`. Instruction opcode is specified literally, other characters are interpreted
    /// literally so that `signature_definition` can capture the value corresponding to each field
    /// when used as a regex
    signature: &'a str,
    /// Same as `signature`, but with a space-separated list of field names
    #[serde(rename = "signatureRaw")]
    signature_raw: &'a str,
    /// Size of the pseudoinstruction. Ignored since some pseudoinstructions can have different sizes
    /// depending on the instructions they are replaced with
    nwords: Integer,
    /// Parameters of the pseudoinstruction. Bit positions of fields are ignored
    fields: Vec<InstructionField<'a, ()>>,
    /// Code to execute for the instruction
    // Can't be a reference because there might be escape sequences, which require
    // modifying the data on deserialization
    definition: String,
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

/// Memory layout attribute keys
#[derive(Deserialize, JsonSchema, Debug, PartialEq, Eq, Clone, Copy)]
pub enum MemoryLayoutKeys {
    #[serde(rename = "text start")]
    TextStart,
    #[serde(rename = "text end")]
    TextEnd,
    #[serde(rename = "data start")]
    DataStart,
    #[serde(rename = "data end")]
    DataEnd,
    #[serde(rename = "stack start")]
    StackStart,
    #[serde(rename = "stack end")]
    StackEnd,
}

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
    pub fn word_size(&self) -> u8 {
        self.arch_conf[1].value.parse().unwrap()
    }

    #[must_use]
    pub const fn main_label(&self) -> &str {
        self.arch_conf[5].value
    }

    /// Gets the section start/end addresses
    ///
    /// # Parameters
    ///
    /// * `i`: index of the section to get (text, data, stack)
    #[must_use]
    const fn section_limits(&self, i: usize) -> (u64, u64) {
        (
            self.memory_layout[2 * i].value.0,
            self.memory_layout[2 * i + 1].value.0,
        )
    }

    /// Gets the code section's start/end addresses
    #[must_use]
    pub const fn code_section_limits(&self) -> (u64, u64) {
        self.section_limits(0)
    }

    /// Gets the data section's start/end addresses
    #[must_use]
    pub const fn data_section_limits(&self) -> (u64, u64) {
        self.section_limits(1)
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

    /// Gets the register bank with the given type and precision
    ///
    /// # Parameters
    ///
    /// * `type`: type of the bank wanted
    /// * `double_precision`: whether the registers should have single (`false`) or double (`true`)
    ///   precision
    #[must_use]
    pub fn find_bank(&self, r#type: ComponentType, double_precision: bool) -> Option<&Component> {
        self.components.iter().find(|bank| {
            bank.r#type == r#type
                && if double_precision {
                    bank.double_precision_type.is_none()
                } else {
                    matches!(
                        bank.double_precision_type,
                        Some(PrecisionType::Extended) | None
                    )
                }
        })
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
    /// Calculates the size of this field in bits
    #[must_use]
    pub fn size(&self) -> usize {
        self.iter()
            .map(|(start, end)| usize::try_from(i32::from(*start) - i32::from(*end) + 1).unwrap())
            .reduce(|acc, val| acc + val)
            .expect("There should always be at least 1 field")
    }

    pub fn iter(&self) -> impl Iterator<Item = &(u8, u8)> {
        self.0.iter()
    }

    #[must_use]
    pub fn new(ranges: Vec<(u8, u8)>) -> Self {
        Self(ranges)
    }
}
