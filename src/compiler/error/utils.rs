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
#[derive(Debug, PartialEq, Eq)]
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
#[derive(Debug, PartialEq, Eq)]
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
#[derive(Debug, PartialEq, Eq)]
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
pub fn get_similar<'a>(target: &str, names: impl IntoIterator<Item = &'a str>) -> Vec<&'a str> {
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

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn display_colored() {
        assert_eq!(&Colored(1, None).to_string(), "`1`");
        assert_eq!(
            &Colored("test", Some(Color::Red)).to_string(),
            &"test".fg(Color::Red).to_string()
        );
        assert_eq!(
            &Colored(10, Some(Color::Blue)).to_string(),
            &"10".fg(Color::Blue).to_string()
        );
    }

    #[test]
    fn display_name_list() {
        let list = |vals: Vec<i32>, color| DisplayList::new(vals, color).to_string();
        let green = |x: &'static str| x.fg(Color::Green);
        assert_eq!(&list(vec![], false), "");
        assert_eq!(&list(vec![], true), "");
        assert_eq!(&list(vec![1], false), "`1`");
        assert_eq!(&list(vec![1, 2], false), "`1` or `2`");
        assert_eq!(&list(vec![1, 3, 2], false), "`1`, `2`, or `3`");
        assert_eq!(&list(vec![4, 3, 2, 1], false), "`1`, `2`, `3`, or `4`");
        assert_eq!(&list(vec![1], true), &1.fg(Color::Green).to_string());
        assert_eq!(
            &DisplayList::new(vec!["foo", "bar"], true).to_string(),
            &format!("{} or {}", green("bar"), green("foo"))
        );
        assert_eq!(
            &DisplayList::new(vec!["c", "a", "b"], true).to_string(),
            &format!("{}, {}, or {}", green("a"), green("b"), green("c"))
        );
    }

    #[test]
    fn display_list_new() {
        assert_eq!(
            DisplayList::<i8>::new(vec![], false),
            DisplayList {
                values: vec![],
                color: false
            }
        );
        assert_eq!(
            DisplayList::new(vec!["a"], true),
            DisplayList {
                values: vec!["a"],
                color: true
            }
        );
        assert_eq!(
            DisplayList::new(vec![1, 2, 3], false),
            DisplayList {
                values: vec![1, 2, 3],
                color: false
            }
        );
    }

    #[test]
    fn display_list_non_empty() {
        assert_eq!(DisplayList::<u8>::non_empty(vec![], false), None);
        assert_eq!(DisplayList::<u8>::non_empty(vec![], true), None);
        assert_eq!(
            DisplayList::non_empty(vec!["a"], true),
            Some(DisplayList::new(vec!["a"], true))
        );
        assert_eq!(
            DisplayList::non_empty(vec![1, 2, 3], false),
            Some(DisplayList::new(vec![1, 2, 3], false))
        );
    }

    #[test]
    fn display_arg_num() {
        assert_eq!(&ArgNum(0, None).to_string(), "`0` arguments");
        assert_eq!(&ArgNum(1, None).to_string(), "`1` argument");
        assert_eq!(&ArgNum(2, None).to_string(), "`2` arguments");
        assert_eq!(&ArgNum(10, None).to_string(), "`10` arguments");

        assert_eq!(
            &ArgNum(0, Some(Color::Red)).to_string(),
            &format!("{} arguments", 0.fg(Color::Red))
        );
        assert_eq!(
            &ArgNum(1, Some(Color::Green)).to_string(),
            &format!("{} argument", 1.fg(Color::Green))
        );
        assert_eq!(
            &ArgNum(2, Some(Color::Blue)).to_string(),
            &format!("{} arguments", 2.fg(Color::Blue))
        );
    }

    #[test]
    fn similar_names() {
        let sim = |target, values| {
            let mut res = get_similar(target, values);
            res.sort_unstable();
            res
        };
        assert_eq!(sim("test", vec!["testtest"]), Vec::<&str>::new());
        assert_eq!(sim("tests0", vec!["test"]), vec!["test"]);
        assert_eq!(sim("tes", vec!["te", "te", "te"]), vec!["te"]);
        assert_eq!(sim("x2", vec!["x0", "x1"]), vec!["x0", "x1"]);
        assert_eq!(sim("x20", vec!["x0", "x1"]), vec!["x0"]);
        assert_eq!(
            sim("test", vec!["aest", "tst", "tests", "tsts", "aa"]),
            vec!["aest", "tests", "tst"]
        );
    }
}
