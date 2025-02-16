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
#[cfg(feature = "js")]
mod js;
pub mod parser;
pub mod span;

/// Trait representing an error that can be rendered for display
pub trait RenderError {
    /// Write the formatted error to a buffer. The written bytes should correspond to valid UTF-8
    ///
    /// # Parameters
    ///
    /// * `filename`: name of the file with the code
    /// * `src`: original source code parsed
    /// * `buffer`: writer in which to write the formatted error
    /// * `color`: whether to enable colors or not
    fn format(self, filename: &str, src: &str, buffer: &mut Vec<u8>, color: bool)
    where
        Self: Sized;

    /// Render the error to a string
    ///
    /// # Parameters
    ///
    /// * `filename`: name of the file with the code
    /// * `src`: original source code parsed
    /// * `color`: whether to enable colors or not
    #[must_use]
    fn render(self, filename: &str, src: &str, color: bool) -> String
    where
        Self: Sized,
    {
        let mut buffer = Vec::new();
        self.format(filename, src, &mut buffer, color);
        String::from_utf8(buffer).expect("the rendered error should be valid UTF-8")
    }
}

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
