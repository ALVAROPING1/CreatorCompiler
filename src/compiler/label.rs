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
    /// Location of the definition of the label in the assembly
    definition: Span,
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
            definition,
        }
    }

    /// Gets the address this label is pointing in
    pub const fn address(&self) -> &BigUint {
        &self.address
    }

    /// Gets the [`Span`] where the label was defined
    pub const fn span(&self) -> &Span {
        &self.definition
    }
}

/// Symbol table for labels
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Table(HashMap<String, Label>);

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
            .add_span(&data.definition)),
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
    use super::{ErrorKind, Label, Table};

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
            Err(ErrorKind::DuplicateLabel("test".to_string(), 0..2).add_span(&(13..17)))
        );
        assert_eq!(
            table.insert("test2".to_string(), Label::new(128u8.into(), 20..22)),
            Err(ErrorKind::DuplicateLabel("test2".to_string(), 6..10).add_span(&(20..22)))
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
