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

//! Module containing the definition of assembly labels and their symbol table

use num_bigint::BigUint;
use std::collections::{hash_map::Entry, HashMap};

use super::{CompileError, ErrorKind};
use crate::span::Span;

/// Assembly label semantic data
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Label {
    /// Address to which the label points
    address: BigUint,
    /// Location of the definition of the label in the assembly. [`None`] if the label comes from a
    /// library
    definition: Option<Span>,
}

impl Label {
    /// Creates a new [`Label`] with the given data
    ///
    /// # Parameters
    ///
    /// * `address`: memory address the label points at
    /// * `definition`: [`Span`] where the label was defined
    pub const fn new(address: BigUint, definition: Span) -> Self {
        Self {
            address,
            definition: Some(definition),
        }
    }

    /// Gets the address this label is pointing in
    pub const fn address(&self) -> &BigUint {
        &self.address
    }

    /// Gets the [`Span`] where the label was defined
    pub const fn span(&self) -> Option<&Span> {
        self.definition.as_ref()
    }
}

/// Symbol table for labels
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Table(HashMap<String, Label>);

impl<S: std::hash::BuildHasher> From<HashMap<String, BigUint, S>> for Table {
    fn from(value: HashMap<String, BigUint, S>) -> Self {
        Self(
            value
                .into_iter()
                .map(|(name, address)| {
                    (
                        name,
                        Label {
                            address,
                            definition: None,
                        },
                    )
                })
                .collect(),
        )
    }
}

impl IntoIterator for Table {
    type Item = (String, Label);
    type IntoIter = <HashMap<String, Label> as IntoIterator>::IntoIter;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl Table {
    /// Inserts a new label
    ///
    /// # Parameters
    ///
    /// * `label`: Label name to insert
    /// * `data`: Data associated with the label
    ///
    /// # Errors
    ///
    /// Errors with [`ErrorKind::DuplicateLabel`] if the label has already been inserted
    pub fn insert(&mut self, label: String, data: Label) -> Result<(), CompileError> {
        match self.0.entry(label) {
            Entry::Vacant(e) => {
                e.insert(data);
                Ok(())
            }
            Entry::Occupied(e) => Err(ErrorKind::DuplicateLabel(
                e.key().clone(),
                e.get().definition.clone(),
            )
            .add_span(
                &data
                    .definition
                    .expect("New labels should always have a definition"),
            )),
        }
    }

    /// Returns a reference to the label data corresponding to the given label name
    ///
    /// # Parameters
    ///
    /// * `label`: name of the label to search
    pub fn get(&self, label: &str) -> Option<&Label> {
        self.0.get(label)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn from_library() {
        let label = |s: &str, x: usize| {
            (
                s.into(),
                Label {
                    address: x.into(),
                    definition: None,
                },
            )
        };
        let value = |s: &str, x: usize| (s.into(), x.into());
        let labels = HashMap::from([value("test", 10), value("func", 17), value("obj", 101)]);
        let correct = HashMap::from([label("test", 10), label("func", 17), label("obj", 101)]);
        let table = Table::from(labels);
        assert_eq!(table, Table(correct));
    }

    #[test]
    fn insert() {
        let mut table = Table::default();
        assert_eq!(
            table.insert("test".to_string(), Label::new(12u8.into(), 0..2)),
            Ok(())
        );
        assert_eq!(
            table.insert("test2".to_string(), Label::new(0u8.into(), 6..10)),
            Ok(())
        );
        assert_eq!(
            table.insert("test".to_string(), Label::new(4u8.into(), 13..17)),
            Err(ErrorKind::DuplicateLabel("test".to_string(), Some(0..2)).add_span(&(13..17)))
        );
        assert_eq!(
            table.insert("test2".to_string(), Label::new(128u8.into(), 20..22)),
            Err(ErrorKind::DuplicateLabel("test2".to_string(), Some(6..10)).add_span(&(20..22)))
        );
    }

    #[test]
    fn get() {
        let mut table = Table::default();
        assert_eq!(
            table.insert("test".to_string(), Label::new(12u8.into(), 2..4)),
            Ok(())
        );
        assert_eq!(
            table.insert("test2".to_string(), Label::new(0u8.into(), 5..10)),
            Ok(())
        );
        assert_eq!(table.get("test"), Some(&Label::new(12u8.into(), 2..4)));
        assert_eq!(table.get("test2"), Some(&Label::new(0u8.into(), 5..10)));
        assert_eq!(table.get("none"), None);
    }
}
