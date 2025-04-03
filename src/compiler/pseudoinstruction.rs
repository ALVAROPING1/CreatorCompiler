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

//! Module containing the interpreter engine used to expand pseudoinstructions
//!
//! The entry point for expanding pseudoinstructions is the [`expand()`] function

// NOTE: for compatibility with pseudoinstruction definitions written for the old compiler, this
// module reimplements the same functionality used by the old compiler with minimal changes. This
// should be completely redesigned from scratch once we are ready to make a breaking change in the
// definition of the architecture

use num_bigint::BigUint;
use once_cell::sync::Lazy;
use regex::{Captures, Regex};

use std::fmt::Write as _;
use std::rc::Rc;

use crate::architecture::{Architecture, FloatType, Pseudoinstruction, RegisterType};
use crate::parser::ParseError;

use super::{ArgumentType, ErrorData, ErrorKind, InstructionDefinition, LabelTable};
use super::{Expr, ParsedArgs};
use super::{Source, Span, SpanList, Spanned};

/// Pseudoinstruction evaluation error kind
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Kind {
    UnknownFieldName(String),
    UnknownFieldNumber { idx: usize, size: usize },
    UnknownFieldType(String),
    EmptyBitRange,
    BitRangeOutOfBounds { upper_bound: usize, msb: usize },
    EvaluationError(String),
    ParseError(ParseError),
}

/// Pseudoinstruction evaluation error
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Error {
    /// Definition of the string at the point of the error
    pub definition: String,
    /// Location in the definition that caused the error
    pub span: Span,
    /// Type of the error
    pub kind: Kind,
}

impl Error {
    /// Adds a span and a pseudoinstruction name to the error, promoting it to a [`ErrorData`]
    ///
    /// # Parameters
    ///
    /// * `def`: definition of the pseudoinstruction
    /// * `span`: location in the assembly code that caused the error
    #[must_use]
    fn compile_error(self, def: &Pseudoinstruction, span: impl Into<SpanList>) -> ErrorData {
        ErrorKind::PseudoinstructionError {
            name: def.name.to_owned(),
            error: Box::new(self),
        }
        .add_span(span)
    }
}

#[cfg(not(feature = "pseudoinstructions"))]
mod js {
    #[derive(Debug)]
    pub enum Never {}

    pub fn eval_expr(_: &str) -> Result<Never, String> {
        unimplemented!("Evaluating js code during pseudoinstruction expansion requires the `pseudoinstruction` feature flag");
    }

    pub fn eval_fn(_: &str) -> Result<Never, String> {
        unimplemented!("Evaluating js code during pseudoinstruction expansion requires the `pseudoinstruction` feature flag");
    }

    #[must_use]
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
        /// Converts a `JS` value to a `JS` string
        #[wasm_bindgen(js_name = String)]
        fn string(x: JsValue) -> js_sys::JsString;
    }

    // Function
    // NOTE: Modification of [`js_sys::Function`] to add `catch` to the constructor
    #[wasm_bindgen]
    extern "C" {
        #[wasm_bindgen(extends = js_sys::Object, is_type_of = JsValue::is_function, typescript_type = "Function")]
        #[derive(Clone, Debug, PartialEq, Eq)]
        type Function;

        /// The `Function` constructor creates a new `Function` object. Calling the
        /// constructor directly can create functions dynamically, but suffers from
        /// security and similar (but far less significant) performance issues
        /// similar to `eval`. However, unlike `eval`, the `Function` constructor
        /// allows executing code in the global scope, prompting better programming
        /// habits and allowing for more efficient code minification.
        ///
        /// [MDN documentation](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Function)
        #[wasm_bindgen(constructor, catch)]
        fn new_no_args(body: &str) -> Result<Function, JsValue>;

        /// The `call()` method calls a function with a given this value and
        /// arguments provided individually.
        ///
        /// [MDN documentation](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Function/call)
        #[wasm_bindgen(method, catch, js_name = call)]
        fn call0(this: &Function, context: &JsValue) -> Result<JsValue, JsValue>;
    }

    /// Evaluates code corresponding to a `JS` expression
    ///
    /// # Errors
    ///
    /// Errors if there is any exception during the execution of the code
    pub fn eval_expr(src: &str) -> Result<JsValue, String> {
        js_sys::eval(src).map_err(to_string)
    }

    /// Evaluates code corresponding to the body of a `JS` function
    ///
    /// # Errors
    ///
    /// Errors if there is any exception during the execution of the code
    pub fn eval_fn(src: &str) -> Result<JsValue, String> {
        Function::new_no_args(src)
            .map_err(to_string)?
            .call0(&JsValue::TRUE)
            .map_err(to_string)
    }

    /// Converts a `JS` value to a string
    #[must_use]
    pub fn to_string(x: JsValue) -> String {
        String::from(string(x))
    }
}

/// Unwraps an expression containing a register name
///
/// # Errors
///
/// Errors if the expression doesn't contain a register name
fn reg_name(arg: &Spanned<Expr>) -> Result<String, ErrorData> {
    match &arg.0 {
        Expr::Identifier((name, _)) => Ok(name.clone()),
        Expr::Integer(i) => Ok(i.to_string()),
        _ => Err(ErrorKind::IncorrectArgumentType {
            expected: ArgumentType::RegisterName,
            found: ArgumentType::Expression,
        }
        .add_span(&arg.1)),
    }
}

/// Gets the [`Span`] of a capture group
///
/// # Parameters
///
/// * `captures`: list of capture groups
/// * `i`: index of the capture group to get
///
/// # Panics
///
/// Panics if the index is out of bounds
#[must_use]
fn capture_span(captures: &Captures, i: usize) -> Span {
    captures
        .get(i)
        .expect("The capture group number given should exist")
        .range()
}

/// Result of expanding a pseudoinstruction
type ExpandedInstructions<'a> = Vec<((InstructionDefinition<'a>, ParsedArgs), SpanList)>;

/// Expands a pseudoinstruction to a sequence of instructions, which might be real or another
/// pseudoinstruction
///
/// # Parameters
///
/// * `arch`: architecture definition
/// * `label_table`: symbol table for labels
/// * `address`: address in which the instruction is being compiled into
/// * `instruction`: pseudoinstruction definition to use
/// * `args`: arguments of the instruction being expanded
///
/// # Errors
///
/// Errors if there is any problem expanding the pseudoinstruction
#[allow(clippy::too_many_lines)]
pub fn expand<'b, 'a: 'b>(
    arch: &'a Architecture,
    label_table: &LabelTable,
    address: &BigUint,
    instruction: (&'b Pseudoinstruction, SpanList),
    args: &ParsedArgs,
) -> Result<ExpandedInstructions<'a>, ErrorData> {
    // Regex used
    // Register name should be replaced with the register name of the i-th register forming this
    // double precision register
    static ALIAS_DOUBLE: Lazy<Regex> = crate::regex!(r"aliasDouble\(([^;]+);(\d+)\)");
    // Gets the value of the i-th argument from bits j to k, evaluating the argument as the given
    // type
    static FIELD_VALUE: Lazy<Regex> = crate::regex!(r"Field\.(\d+)\.\((\d+),(\d+)\)\.(\w+)");
    // Gets the size of the i-th argument
    static FIELD_SIZE: Lazy<Regex> = crate::regex!(r"Field\.(\d+)\.SIZE");
    // Evaluates a `JS` expression that doesn't return a value
    static NO_RET_OP: Lazy<Regex> = crate::regex!(r"no_ret_op\{([^}]*?)\};");
    // Evaluates a `JS` expression should be replaced with its return value
    static OP: Lazy<Regex> = crate::regex!(r"op\{([^}]*?)\}");
    // Block of code containing a list of instructions
    static INSTRUCTIONS: Lazy<Regex> = crate::regex!(r"\{(.*?)\}");

    // Function to evaluate a label within an expression
    let ident_eval = |label: &str| super::label_eval(label_table, address, label);

    // Parse a number from a string that already matched a number regex
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
    let case = arch.arch_conf.sensitive_register_name;

    // Replace occurrences of `AliasDouble()`
    while let Some(x) = ALIAS_DOUBLE.captures(&def) {
        let (_, [name, i]) = x.extract();
        // Get the user's register name
        let name = get_arg(name).ok_or_else(|| {
            Error {
                definition: def.clone(),
                span: capture_span(&x, 1),
                kind: Kind::UnknownFieldName(name.to_owned()),
            }
            .compile_error(instruction, span.clone())
        })?;
        let name = &reg_name(&name.value)?;
        let i: usize = num(i);
        // Find the register name and replace it
        for file in arch.find_reg_files(RegisterType::Float(FloatType::Double)) {
            if let Some((_, reg, _)) = file.find_register(name, case) {
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
        // Get the user's argument expression
        let (value, _) = &args
            .get(arg_num)
            .ok_or_else(|| {
                Error {
                    definition: def.clone(),
                    span: capture_span(&x, 1),
                    kind: Kind::UnknownFieldNumber {
                        idx: arg_num + 1,
                        size: args.len(),
                    },
                }
                .compile_error(instruction, span.clone())
            })?
            .value;
        // Evaluate the expression according to the requested type
        #[allow(clippy::cast_possible_truncation)]
        let field = match ty {
            "int" => {
                // Convert the number to binary using two's complement
                let s = value.int(ident_eval)?.to_signed_bytes_be().iter().fold(
                    String::new(),
                    |mut s, byte| {
                        write!(s, "{byte:08b}").expect("Writing to a string shouldn't fail");
                        s
                    },
                );
                if s.len() >= 32 {
                    s
                } else {
                    // Pad the number to 32 bits, using sign extension
                    let pad = s
                        .chars()
                        .next()
                        .expect("There should always be at least 1 character");
                    let mut pad = std::iter::repeat(pad)
                        .take(32 - s.len())
                        .collect::<String>();
                    pad.push_str(&s);
                    pad
                }
            }
            "float" => format!("{:032b}", (value.float()? as f32).to_bits()),
            "double" => format!("{:064b}", value.float()?.to_bits()),
            ty => {
                return Err(Error {
                    definition: def.clone(),
                    span: capture_span(&x, 4),
                    kind: Kind::UnknownFieldType(ty.to_owned()),
                }
                .compile_error(instruction, span))
            }
        };
        // Get the range of bits requested
        let start_bit = num(start_bit);
        let end_bit = num(end_bit);
        let msb = field.len() - 1;
        if start_bit < end_bit {
            return Err(Error {
                definition: def.clone(),
                span: capture_span(&x, 2).start..capture_span(&x, 3).end,
                kind: Kind::EmptyBitRange,
            }
            .compile_error(instruction, span));
        }
        if start_bit > msb {
            return Err(Error {
                definition: def.clone(),
                span: capture_span(&x, 2).start..capture_span(&x, 3).end,
                kind: Kind::BitRangeOutOfBounds {
                    upper_bound: start_bit,
                    msb,
                },
            }
            .compile_error(instruction, span));
        }
        // Replace the matched string with the corresponding bits
        let field = format!("0b{}", &field[msb - start_bit..=msb - end_bit]);
        def.replace_range(capture_span(&x, 0), &field);
    }

    // Replace occurrences of `Field.size`
    while let Some(x) = FIELD_SIZE.captures(&def) {
        let (_, [arg]) = x.extract();
        let arg_num = num(arg) - 1;
        // Get the user's argument expression
        let (value, _) = &args
            .get(arg_num)
            .ok_or_else(|| {
                Error {
                    definition: def.clone(),
                    span: capture_span(&x, 1),
                    kind: Kind::UnknownFieldNumber {
                        idx: arg_num + 1,
                        size: args.len(),
                    },
                }
                .compile_error(instruction, span.clone())
            })?
            .value;
        // Calculate the size of the expression
        #[allow(clippy::cast_possible_truncation)]
        let size = match value.int(ident_eval) {
            Ok(x) => x.bits() + 1,
            Err(err) => match *err.kind {
                // If the expression had any floating-point numbers, assume the result is in
                // single precision
                ErrorKind::UnallowedFloat => 32,
                _ => return Err(err),
            },
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
            .compile_error(instruction, span.clone())
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
            .compile_error(instruction, span.clone())
        })?;
        def.replace_range(capture_span(&x, 0), &js::to_string(result));
    }

    // Wrap instruction sequences in quotes and with a return statement, so we can treat the
    // definition code as the body of a function
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
            .compile_error(instruction, span.clone())
        })?;
        def = js::to_string(result);
    };

    // Process the resulting instruction sequence
    let source = Rc::new(Source { code: def, span });
    let def = &source.code;
    def.split_terminator(';')
        .map(|inst| {
            // Gets the address of the start of a string
            let addr_of = |str: &str| str.as_ptr() as usize;
            // Calculate the span in the original `instructions`
            let span_start = addr_of(inst) - addr_of(def);
            let span = span_start..(span_start + inst.len());
            // Lex the instruction
            let (name, mut args) = crate::parser::Instruction::lex(inst).map_err(|error| {
                Error {
                    definition: def.clone(),
                    span: span.clone(),
                    kind: Kind::ParseError(error),
                }
                .compile_error(instruction, source.span.clone())
            })?;
            // Update the spans on the tokens to be relative to the start of the definition rather
            // than relative to the start of the instruction
            for tok in &mut args {
                tok.1.start += span_start;
                tok.1.end += span_start;
            }
            let name_span = span_start..span_start + name.len();
            let args_span = name_span.end + 1..span_start + inst.len();
            // Parse the instruction
            let (inst_def, mut args) =
                super::parse_instruction(arch, (name.to_owned(), name_span), &(args, args_span))?;
            // Replace the argument names that match those of the pseudoinstruction being expanded
            // with the values provided by the user
            for arg in &mut args {
                let value = &arg.value;
                match &value.0 {
                    Expr::Identifier((ident, _)) => {
                        if let Some(pseudoinstruction_arg) = get_arg(ident) {
                            arg.value.0 = pseudoinstruction_arg.value.0.clone();
                        }
                    }
                    _ => continue,
                }
            }
            let span = SpanList {
                span,
                source: Some(source.clone()),
            };
            Ok(((inst_def, args), span))
        })
        .collect::<Result<Vec<_>, _>>()
}
