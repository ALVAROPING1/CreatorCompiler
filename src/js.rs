//! Module containing the definition of wrappers for the compiler and generattion of `JS` bindings
//! for interoperability

use self_cell::self_cell;
use wasm_bindgen::prelude::*;

use crate::architecture::Architecture;
use crate::RenderError;

mod utils;

self_cell!(
    /// Architecture definition
    #[wasm_bindgen]
    pub struct ArchitectureJS {
        owner: String,
        #[covariant]
        dependent: Architecture,
    }
);

/// Converts a given string with ANSI escape codes to HTML
fn to_html(str: &str) -> String {
    let opts = ansi_to_html::Opts::default().four_bit_var_prefix(Some("err-".into()));
    ansi_to_html::convert_with_opts(str, &opts).expect("we should only generate valid ANSI escapes")
}

#[wasm_bindgen]
#[allow(clippy::use_self)] // wasm_bindgen doesn't support using `Self` on nested types
impl ArchitectureJS {
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
    pub fn from_json(json: String) -> Result<ArchitectureJS, String> {
        utils::set_panic_hook();
        Self::try_new(json, |json| Architecture::from_json(json)).map_err(|e| e.to_string())
    }

    /// Converts the architecture to a pretty printed string for debugging
    #[wasm_bindgen(js_name = toString)]
    #[must_use]
    pub fn debug(&self) -> String {
        format!("{:#?}", self.borrow_dependent())
    }

    /// Compiles an assembly source according to the architecture description
    ///
    /// # Parameters
    ///
    /// * `src`: assembly code to compile
    /// * `html_error`: whether to format error messages in HTML (`true`) or ANSI (`false`)
    ///
    /// # Errors
    ///
    /// Errors if the assembly code has a syntactical or semantical error
    pub fn compile(&self, src: &str, html_error: bool) -> Result<CompiledCodeJS, String> {
        const FILENAME: &str = "assembly";
        let format_err = |e: String| if html_error { to_html(&e) } else { e };
        // Parse the source to an AST
        let ast = crate::parser::parse(src).map_err(|e| format_err(e.render(FILENAME, src)))?;
        // Compile the AST
        let compiled = crate::compiler::compile(self.borrow_dependent(), ast)
            .map_err(|e| format_err(e.render(FILENAME, src)))?;
        // Wrap the instructions in a type that can be returned to `JS`
        let instructions = compiled
            .instructions
            .into_iter()
            .map(|x| InstructionJS {
                address: format!("0x{:X}", x.address),
                labels: x.labels,
                loaded: x.loaded,
                binary: x.binary.into(),
                user: src[x.user].to_owned(),
            })
            .collect();
        // Wrap the data elements in a type that can be returned to `JS`
        let data = compiled.data_memory.into_iter().map(DataJS).collect();
        Ok(CompiledCodeJS { instructions, data })
    }
}

/// Assembly compilation output
#[wasm_bindgen(getter_with_clone)]
#[derive(Debug, Clone, PartialEq)]
pub struct CompiledCodeJS {
    /// Compiled instructions to execute
    #[wasm_bindgen(readonly)]
    pub instructions: Vec<InstructionJS>,
    /// Compiled data to add to the data segment
    #[wasm_bindgen(readonly)]
    pub data: Vec<DataJS>,
}

#[wasm_bindgen]
impl CompiledCodeJS {
    /// Converts the compiled code to a pretty printed string for debugging
    #[wasm_bindgen(js_name = toString)]
    #[must_use]
    pub fn debug(&self) -> String {
        format!("{self:#?}")
    }
}

/// Compiled instruction wrapper
#[wasm_bindgen(getter_with_clone)]
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct InstructionJS {
    /// Address of the instruction in hexadecimal (`0xABCD`)
    pub address: String,
    /// Labels pointing to this instruction
    pub labels: Vec<String>,
    /// Translated instruction to a simplified syntax
    pub loaded: String,
    /// Instruction encoded in binary
    pub binary: String,
    /// Instruction in the code
    pub user: String,
}

/// Compiled data wrapper
#[wasm_bindgen]
#[derive(Debug, Clone, PartialEq)]
pub struct DataJS(crate::compiler::Data);

/// General category of a compiled data element
#[wasm_bindgen]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DataCategoryJS {
    Number,
    String,
    Space,
    Padding,
}

#[wasm_bindgen]
#[allow(clippy::missing_const_for_fn)] // wasm_bindgen doesn't support const functions
impl DataJS {
    /// Address of the data element
    #[must_use]
    pub fn address(&self) -> u64 {
        self.0.address
    }

    /// Labels pointing to this data element
    #[must_use]
    pub fn labels(&self) -> Vec<String> {
        self.0.labels.clone()
    }

    /// Value of the data element:
    ///
    /// * For integers/floating point values, it's their value either in hexadecimal without the
    ///   `0x` prefix or as a number, depending on the `human` parameter
    /// * For strings, it's their contents
    /// * For empty spaces/padding, it's their size as a string
    ///
    /// # Parameters
    ///
    /// * `human`: whether to return the value as a human-readable representation or in bynary
    #[must_use]
    pub fn value(&self, human: bool) -> String {
        use crate::compiler::Value;
        match (&self.0.value, human) {
            (Value::Integer(int), true) => format!("{}", int.value()),
            (Value::Integer(int), false) => format!("{:X}", int.value()),
            (Value::Float(float), true) => format!("{float}"),
            (Value::Float(float), false) => format!("{:X}", float.to_bits()),
            (Value::Double(double), true) => format!("{double}"),
            (Value::Double(double), false) => format!("{:X}", double.to_bits()),
            (Value::String { data, .. }, _) => data.clone(),
            (Value::Space(n) | Value::Padding(n), _) => n.to_string(),
        }
    }

    /// Precise type of the data element
    #[must_use]
    pub fn r#type(&self) -> String {
        use crate::architecture::IntegerType;
        use crate::compiler::Value;
        match &self.0.value {
            Value::Integer(int) => match int.r#type() {
                None => "bits",
                Some(IntegerType::Byte) => "byte",
                Some(IntegerType::HalfWord) => "half",
                Some(IntegerType::Word) => "word",
                Some(IntegerType::DoubleWord) => "double_word",
            },
            Value::Float(_) => "float",
            Value::Double(_) => "double",
            Value::String {
                null_terminated, ..
            } => match null_terminated {
                true => "asciiz",
                false => "ascii",
            },
            Value::Space(_) => "space",
            Value::Padding(_) => "padding",
        }
        .into()
    }

    /// General category of the data element
    #[must_use]
    pub fn data_category(&self) -> DataCategoryJS {
        use crate::compiler::Value;
        match self.0.value {
            Value::Integer(_) | Value::Float(_) | Value::Double(_) => DataCategoryJS::Number,
            Value::String { .. } => DataCategoryJS::String,
            Value::Space(_) => DataCategoryJS::Space,
            Value::Padding(_) => DataCategoryJS::Padding,
        }
    }

    /// Size of the data element in bytes
    ///
    /// # Panics
    ///
    /// Panics if an integer bigger than 2^64 bits or a string longer than 2^64 bytes was compiled
    #[must_use]
    pub fn size(&self) -> u64 {
        use crate::compiler::Value;
        match &self.0.value {
            Value::Integer(int) => {
                let x = u64::try_from(int.size())
                    .expect("we should never have integers bigger than 2^64 bits");
                (x + 7) / 8
            }
            Value::Float(_) => 4,
            Value::Double(_) => 8,
            Value::String { data, .. } => u64::try_from(data.len())
                .expect("we should never have strings bigger than 2^64 bytes"),
            Value::Space(x) | Value::Padding(x) => *x,
        }
    }
}
