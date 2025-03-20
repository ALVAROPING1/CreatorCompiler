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

//! Module containing utilities for rendering compiler errors

use ariadne::{Color, Fmt};

use std::fmt;

/// Wrapper to display elements with an optional color
pub struct Colored<T>(pub T, pub Option<Color>);

impl<T: fmt::Display> fmt::Display for Colored<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(color) = self.1 {
            write!(f, "{}", (&self.0).fg(color))
        } else {
            write!(f, "`{}`", self.0)
        }
    }
}

/// Wrapper for a vector to display it as a list of names
pub struct DisplayList<T> {
    /// List of names to display
    pub values: Vec<T>,
    /// Whether to display the names with colors or not
    pub color: bool,
}

impl<T: std::cmp::Ord> DisplayList<T> {
    /// Creates a new [`DisplayList`], checking that it isn't empty
    pub fn non_empty(names: Vec<T>, color: bool) -> Option<Self> {
        (!names.is_empty()).then_some(Self::new(names, color))
    }

    /// Creates a new [`DisplayList`]
    pub fn new(mut values: Vec<T>, color: bool) -> Self {
        values.sort_unstable();
        Self { values, color }
    }
}

impl<T: fmt::Display> fmt::Display for DisplayList<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Some(last) = self.values.last() else {
            return Ok(());
        };
        let color = self.color.then_some(Color::Green);
        let comma = if self.values.len() > 2 { "," } else { "" };
        for x in &self.values[..self.values.len() - 1] {
            write!(f, "{}{comma} ", Colored(x, color))?;
        }
        if self.values.len() > 1 {
            write!(f, "or ")?;
        }
        write!(f, "{}", Colored(last, color))
    }
}

/// Wrapper to display an amount of arguments
pub struct ArgNum(pub usize, pub Option<Color>);

impl fmt::Display for ArgNum {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = if self.0 == 1 { "" } else { "s" };
        write!(f, "{} argument{}", Colored(self.0, self.1), s)
    }
}

/// Gets the names from a list that are the most similar to the given name
///
/// # Parameters
///
/// * `target`: target name to match against
/// * `names`: iterator of possible names
pub fn get_similar<'a>(target: &str, names: impl Iterator<Item = &'a str>) -> Vec<&'a str> {
    let mut distances = std::collections::HashMap::new();
    for name in names {
        distances
            .entry(name)
            .or_insert_with(|| edit_distance::edit_distance(name, target));
    }
    distances
        .iter()
        .map(|(_, &d)| d)
        .min()
        .filter(|&min| min <= std::cmp::max(target.len() / 3, 1))
        .map(|min| {
            distances
                .iter()
                .filter(|(_, &d)| d == min)
                .map(|(&name, _)| name)
                .collect()
        })
        .unwrap_or_default()
}
