use once_cell::sync::Lazy;
use regex::{Captures, Regex};

use crate::architecture::{Architecture, FloatType, Pseudoinstruction, RegisterType};
use crate::parser::ParseError;

use super::{Argument, ParsedArgs};
use super::{ArgumentType, CompileError, ErrorKind, InstructionDefinition, LabelTable};
use super::{Span, Spanned};

/// Pseudoinstruction evaluation error
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Kind {
    UnknownFieldName(String),
    UnknownFieldNumber(usize),
    EvaluationError(String),
    ParseError {
        instruction: String,
        error: ParseError,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Error {
    pub definition: String,
    pub span: Span,
    pub kind: Kind,
}

impl Error {
    fn compile_error(self, def: &Pseudoinstruction, span: &Span) -> CompileError {
        ErrorKind::PseudoinstructionError {
            name: def.name.to_owned(),
            error: Box::new(self),
        }
        .add_span(span)
    }
}

#[cfg(not(feature = "pseudoinstructions"))]
mod js {
    pub enum Never {}
    pub type Value = String;

    pub fn eval_expr(_: &str) -> Option<Never> {
        unimplemented!("Evaluating js code during pseudoinstruction expansion requires the `pseudoinstruction` feature flag");
    }

    pub fn eval_fn(_: &str) -> Option<Never> {
        unimplemented!("Evaluating js code during pseudoinstruction expansion requires the `pseudoinstruction` feature flag");
    }

    pub fn to_string<T>(_: T) -> String {
        unimplemented!("Evaluating js code during pseudoinstruction expansion requires the `pseudoinstruction` feature flag");
    }
}

#[cfg(feature = "pseudoinstructions")]
mod js {
    use js_sys::wasm_bindgen::JsValue;
    use wasm_bindgen::prelude::*;

    #[wasm_bindgen]
    extern "C" {
        #[wasm_bindgen(js_name = String)]
        fn string(x: JsValue) -> js_sys::JsString;
    }

    pub fn eval_expr(src: &str) -> Result<JsValue, String> {
        js_sys::eval(src).map_err(to_string)
    }

    pub fn eval_fn(src: &str) -> Result<JsValue, String> {
        js_sys::Function::new_no_args(src)
            .call0(&JsValue::TRUE)
            .map_err(to_string)
    }

    pub fn to_string(x: JsValue) -> String {
        String::from(string(x))
    }
}

fn reg_name(arg: &Spanned<Argument>) -> Result<&str, CompileError> {
    match &arg.0 {
        Argument::Number(_) => Err(ErrorKind::IncorrectArgumentType {
            expected: ArgumentType::RegisterName,
            found: ArgumentType::Expression,
        }
        .add_span(&arg.1)),
        Argument::Identifier(name) => Ok(name),
    }
}

fn capture_span(captures: &Captures, i: usize) -> Span {
    captures
        .get(i)
        .expect("The capture group number given should exist")
        .range()
}

#[allow(clippy::too_many_lines)]
pub fn expand<'b, 'a: 'b>(
    arch: &'a Architecture,
    label_table: &LabelTable,
    address: u64,
    instruction: Spanned<&'b Pseudoinstruction>,
    args: &ParsedArgs,
) -> Result<Vec<(InstructionDefinition<'a>, ParsedArgs)>, CompileError> {
    // Regex used
    static ALIAS_DOUBLE: Lazy<Regex> = crate::regex!(r"aliasDouble\(([^;]+);(\d+)\)");
    static FIELD_VALUE: Lazy<Regex> = crate::regex!(r"Field\.(\d+)\.\((\d+),(\d+)\)\.(\w+)");
    static FIELD_SIZE: Lazy<Regex> = crate::regex!(r"Field\.(\d+)\.SIZE");
    static NO_RET_OP: Lazy<Regex> = crate::regex!(r"no_ret_op\{([^}]*?)\};");
    static OP: Lazy<Regex> = crate::regex!(r"op\{([^}]*?)\}");
    static INSTRUCTIONS: Lazy<Regex> = crate::regex!(r"\{(.*?)\}");

    let num = |x: &str| {
        x.parse()
            .expect("This should have already matched a number")
    };
    let (instruction, span) = instruction;

    // Get the argument corresponding to the field with the given name
    let get_arg = |name: &str| {
        args.iter()
            .find(|arg| instruction.syntax.fields[arg.field_idx].name == name)
    };

    // Expansion
    let mut def = instruction.definition.replace('\n', "");

    // Replace occurrences of `AliasDouble()`
    while let Some(x) = ALIAS_DOUBLE.captures(&def) {
        let (_, [name, i]) = x.extract();
        let name = get_arg(name).ok_or_else(|| {
            Error {
                definition: def.clone(),
                span: capture_span(&x, 1),
                kind: Kind::UnknownFieldName(name.to_owned()),
            }
            .compile_error(instruction, &span)
        })?;
        let name = reg_name(&name.value)?;
        let i: usize = num(i);
        for bank in arch.find_banks(RegisterType::Float(FloatType::Double)) {
            if let Some((_, reg)) = bank.find_register(name) {
                let name = reg
                    .simple_reg
                    .and_then(|regs| regs.get(i).copied())
                    .unwrap_or(name);
                def.replace_range(capture_span(&x, 0), name);
                break;
            }
        }
    }

    // Replace occurrences of `Field.number`
    while let Some(x) = FIELD_VALUE.captures(&def) {
        let (_, [arg, start_bit, end_bit, ty]) = x.extract();
        let arg_num = num(arg) - 1;
        let (value, span) = &args
            .get(arg_num)
            .ok_or_else(|| {
                Error {
                    definition: def.clone(),
                    span: capture_span(&x, 1),
                    kind: Kind::UnknownFieldNumber(arg_num + 1),
                }
                .compile_error(instruction, &span)
            })?
            .value;
        let start_bit = num(start_bit);
        let end_bit = num(end_bit);
        #[allow(clippy::cast_possible_truncation)]
        let field = match value {
            Argument::Number(expr) => match ty {
                "int" => format!("{:032b}", expr.int()?),
                "float" => format!("{:032b}", (expr.float()? as f32).to_bits()),
                "double" => format!("{:064b}", expr.float()?.to_bits()),
                _ => panic!(),
            },
            Argument::Identifier(label) => {
                let val: u32 = label_table
                    .get(label)
                    .ok_or_else(|| ErrorKind::UnknownLabel(label.clone()).add_span(span))?
                    .address()
                    .try_into()
                    .unwrap();
                match ty {
                    "int" => format!("{val:032b}"),
                    "float" => format!("{:032b}", (f64::from(val) as f32).to_bits()),
                    "double" => format!("{:064b}", f64::from(val).to_bits()),
                    _ => panic!(),
                }
            }
        };
        let len = field.len() - 1;
        assert!(start_bit <= len, "{start_bit} <= {len}");
        assert!(end_bit <= len, "{end_bit} <= {len}");
        let field = format!("0b{}", &field[len - start_bit..=len - end_bit]);
        def.replace_range(capture_span(&x, 0), &field);
    }

    // Replace occurrences of `Field.size`
    while let Some(x) = FIELD_SIZE.captures(&def) {
        let (_, [arg]) = x.extract();
        let arg_num = num(arg) - 1;
        let (value, span) = &args
            .get(arg_num)
            .ok_or_else(|| {
                Error {
                    definition: def.clone(),
                    span: capture_span(&x, 1),
                    kind: Kind::UnknownFieldNumber(arg_num + 1),
                }
                .compile_error(instruction, &span)
            })?
            .value;
        #[allow(clippy::cast_possible_truncation)]
        let size = match value {
            Argument::Number(expr) => match expr.int() {
                Ok(x) => 32 - x.leading_zeros(),
                Err(err) => match err.kind {
                    ErrorKind::UnallowedFloat => 32,
                    _ => return Err(err),
                },
            },
            Argument::Identifier(label) => {
                let val = label_table
                    .get(label)
                    .ok_or_else(|| ErrorKind::UnknownLabel(label.clone()).add_span(span))?
                    .address();
                64 - val.leading_zeros()
            }
        };
        def.replace_range(capture_span(&x, 0), &size.to_string());
    }

    // Replace occurrences of `reg.pc` and update its value on the JS side
    if def.contains("reg.pc") {
        let code = format!("pc = {address} + 4");
        js::eval_fn(&code).expect("The code we are running should never fail");
        def = def.replace("reg.pc", "pc");
    }

    // Evaluate occurrences of `no_ret_op{}`
    while let Some(x) = NO_RET_OP.captures(&def) {
        let (_, [code]) = x.extract();
        js::eval_fn(code).map_err(|error| {
            Error {
                definition: def.clone(),
                span: capture_span(&x, 1),
                kind: Kind::EvaluationError(error),
            }
            .compile_error(instruction, &span)
        })?;
        def.replace_range(capture_span(&x, 0), "");
    }

    // Evaluate and replace occurrences of `op{}`
    while let Some(x) = OP.captures(&def) {
        let (_, [code]) = x.extract();
        let result = js::eval_expr(code).map_err(|error| {
            Error {
                definition: def.clone(),
                span: capture_span(&x, 1),
                kind: Kind::EvaluationError(error),
            }
            .compile_error(instruction, &span)
        })?;
        def.replace_range(capture_span(&x, 0), &js::to_string(result));
    }

    // Wrap instruction sequences in quotes and with a return statement
    let mut start = 0;
    while let Some(x) = INSTRUCTIONS.captures_at(&def, start) {
        let (_, [instructions]) = x.extract();
        let replacement = format!("{{return \"{instructions}\"}}");
        let range = capture_span(&x, 0);
        start = range.start + replacement.len();
        def.replace_range(range, &replacement);
    }
    // If start isn't 0, there has been at least 1 replacement, meaning that the definition uses
    // code we must execute to get the replacement instruction sequence. Otherwise, the entire
    // string is the instruction sequence
    if start != 0 {
        let result = js::eval_fn(&def).map_err(|error| {
            Error {
                definition: def.clone(),
                span: 0..def.len(),
                kind: Kind::EvaluationError(error),
            }
            .compile_error(instruction, &span)
        })?;
        def = js::to_string(result);
    };

    def.split(';')
        .map(|inst| {
            let (name, args) = crate::parser::Instruction::lex(inst).map_err(|error| {
                let addr_of = |str: &str| str.as_ptr() as usize;
                let span_start = addr_of(inst) - addr_of(&def);
                Error {
                    definition: def.to_string(),
                    // Calculate the span in the original `instructions` as the difference between the
                    // pointers and the size
                    span: span_start..(span_start + inst.len()),
                    kind: Kind::ParseError {
                        instruction: inst.to_string(),
                        error,
                    },
                }
                .compile_error(instruction, &span)
            })?;
            let (def, mut args) =
                super::parse_instruction(arch, (name.to_owned(), 0..0), &(args, 0..0))?;
            for arg in &mut args {
                arg.value.1 = span.clone();
                let value = &arg.value;
                match &value.0 {
                    Argument::Number(_) => continue,
                    Argument::Identifier(ident) => {
                        if let Some(pseudoinstruction_arg) = get_arg(ident) {
                            arg.value = pseudoinstruction_arg.value.clone();
                        }
                    }
                }
            }
            Ok((def, args))
        })
        .collect::<Result<Vec<_>, _>>()
}
