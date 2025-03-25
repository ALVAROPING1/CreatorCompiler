#![doc = include_str!("../README.md")]

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

pub mod architecture;
pub mod compiler;
pub mod error_rendering;
#[cfg(feature = "js")]
mod js;
pub mod parser;
pub mod span;
pub use error_rendering::RenderError;

/// Builds a new lazily-initialized regex with a given literal string
///
/// # Panics
///
/// Panics if the literal string isn't a valid regex
macro_rules! build_regex {
    ($re:expr) => {
        Lazy::new(|| Regex::new($re).expect("All regexes should compile"))
    };
}
use build_regex as regex;
