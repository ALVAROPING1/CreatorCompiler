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

use num_bigint::BigUint;
use once_cell::sync::Lazy;
use regex::{Captures, Regex};

use std::fmt::Write as _;

use crate::architecture::{Architecture, FloatType, Pseudoinstruction, RegisterType};
use crate::parser::ParseError;

use super::{ArgumentType, CompileError, ErrorKind, InstructionDefinition, LabelTable};
use super::{Expr, ParsedArgs};
use super::{Span, Spanned};

/// Pseudoinstruction evaluation error
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Kind {
    UnknownFieldName(String),
    UnknownFieldNumber(usize),
    UnknownFieldType(String),
    EmptyBitRange,
    BitRangeOutOfBounds {
        upper_bound: usize,
        msb: usize,
    },
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

fn reg_name(arg: &Spanned<Expr>) -> Result<&str, CompileError> {
    match &arg.0 {
        Expr::Identifier((name, _)) => Ok(name),
        _ => Err(ErrorKind::IncorrectArgumentType {
            expected: ArgumentType::RegisterName,
            found: ArgumentType::Expression,
        }
        .add_span(&arg.1)),
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
    address: &BigUint,
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

    let ident_eval = |label: &str| {
        Ok(label_table
            .get(label)
            .ok_or_else(|| ErrorKind::UnknownLabel(label.to_owned()))?
            .address()
            .clone()
            .into())
    };

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
        let (value, _) = &args
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
        let field = match ty {
            "int" => {
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
                .compile_error(instruction, &span))
            }
        };
        let start_bit = num(start_bit);
        let end_bit = num(end_bit);
        let msb = field.len() - 1;
        if start_bit < end_bit {
            return Err(Error {
                definition: def.clone(),
                span: capture_span(&x, 2).start..capture_span(&x, 3).end,
                kind: Kind::EmptyBitRange,
            }
            .compile_error(instruction, &span));
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
            .compile_error(instruction, &span));
        }
        let field = format!("0b{}", &field[msb - start_bit..=msb - end_bit]);
        def.replace_range(capture_span(&x, 0), &field);
    }

    // Replace occurrences of `Field.size`
    while let Some(x) = FIELD_SIZE.captures(&def) {
        let (_, [arg]) = x.extract();
        let arg_num = num(arg) - 1;
        let (value, _) = &args
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
        let size = match value.int(ident_eval) {
            Ok(x) => x.bits() + 1,
            Err(err) => match *err.kind {
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

    def.split_terminator(';')
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
                    Expr::Identifier((ident, _)) => {
                        if let Some(pseudoinstruction_arg) = get_arg(ident) {
                            arg.value = pseudoinstruction_arg.value.clone();
                        }
                    }
                    _ => continue,
                }
            }
            Ok((def, args))
        })
        .collect::<Result<Vec<_>, _>>()
}
