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

//! Module containing the definition of the error type used by syntax errors

use ariadne::{Color, Config, IndexType, Label, Report, ReportKind, Source};
use chumsky::error::{Simple, SimpleReason};

use crate::error_rendering::{Colored, DisplayList};

use super::Token;

/// Error representing a syntax error during parsing
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Error {
    /// The error happened during the lexing stage
    Lexer(Vec<Simple<char>>),
    /// The error happened during the parsing stage
    Parser(Vec<Simple<Token>>),
}

impl From<Vec<Simple<char>>> for Error {
    fn from(value: Vec<Simple<char>>) -> Self {
        Self::Lexer(value)
    }
}

impl From<Vec<Simple<Token>>> for Error {
    fn from(value: Vec<Simple<Token>>) -> Self {
        Self::Parser(value)
    }
}

impl<T: ToString + std::hash::Hash + std::cmp::Eq> crate::RenderError for Vec<Simple<T>> {
    fn format(&self, filename: &str, src: &str, mut buffer: &mut Vec<u8>, color: bool) {
        // Configure the error reports
        let config = Config::default()
            .with_color(color)
            .with_index_type(IndexType::Byte);
        // Generate a report for each error
        for e in self {
            Report::build(ReportKind::Error, (filename, e.span()))
                .with_config(config)
                .with_message(match e.reason() {
                    SimpleReason::Custom(msg) => msg.clone(),
                    SimpleReason::Unexpected => {
                        let fmt = |x: Option<&T>| {
                            x.map_or_else(|| "end of input".into(), ToString::to_string)
                        };
                        format!(
                            "found {} but expected {}",
                            Colored(fmt(e.found()), color.then_some(Color::Red)),
                            DisplayList::new(
                                e.expected().map(|x| fmt(x.as_ref())).collect(),
                                color
                            )
                        )
                    }
                    SimpleReason::Unclosed { .. } => unreachable!("We don't use this error"),
                })
                .with_label(
                    Label::new((filename, e.span()))
                        .with_message(match e.reason() {
                            SimpleReason::Unexpected => "Unexpected input",
                            SimpleReason::Custom(_) => "Caused by this",
                            SimpleReason::Unclosed { .. } => {
                                unreachable!("We don't use this error")
                            }
                        })
                        .with_color(Color::Red),
                )
                .with_labels(e.label().map_or_else(Vec::new, |label| {
                    vec![Label::new((filename, e.span()))
                        .with_message(format!("while parsing this {label}"))
                        .with_color(Color::Yellow)]
                }))
                .finish()
                .write((filename, Source::from(src)), &mut buffer)
                .expect("Writing to an in-memory vector can't fail");
        }
    }
}

impl crate::RenderError for Error {
    fn format(&self, filename: &str, src: &str, buffer: &mut Vec<u8>, color: bool) {
        match self {
            Self::Lexer(errs) => errs.format(filename, src, buffer, color),
            Self::Parser(errs) => errs.format(filename, src, buffer, color),
        }
    }
}
