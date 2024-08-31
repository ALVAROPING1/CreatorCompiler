use std::collections::HashMap;

use super::error::Error as CompileError;

/// Label semantic data
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Label {
    address: u64,
    // definition: Span, // Maybe this is good for error reporting?
}

impl Label {
    /// Constructs a new `Label` with the given data
    ///
    /// # Parameters
    ///
    /// * `address`: memory address the label points at
    pub const fn new(address: u64) -> Self {
        Self { address }
    }

    /// Gets the address this label is pointing in
    pub const fn address(&self) -> u64 {
        self.address
    }
}

/// Symbol table for labels
#[derive(Debug, Clone, Default)]
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
    /// Errors if the label has already been inserted
    pub fn insert(&mut self, label: String, data: Label) -> Result<(), CompileError> {
        match self.0.entry(label) {
            std::collections::hash_map::Entry::Vacant(e) => {
                e.insert(data);
                Ok(())
            }
            std::collections::hash_map::Entry::Occupied(e) => {
                Err(CompileError::DuplicateLabel(e.key().clone()))
            }
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
    use super::{CompileError, Label, Table};

    #[test]
    fn insert() {
        let mut table = Table::default();
        assert_eq!(table.insert("test".to_string(), Label::new(12)), Ok(()));
        assert_eq!(table.insert("test2".to_string(), Label::new(0)), Ok(()));
        assert_eq!(
            table.insert("test".to_string(), Label::new(4)),
            Err(CompileError::DuplicateLabel("test".to_string()))
        );
        assert_eq!(
            table.insert("test2".to_string(), Label::new(128)),
            Err(CompileError::DuplicateLabel("test2".to_string()))
        );
    }

    #[test]
    fn get() {
        let mut table = Table::default();
        assert_eq!(table.insert("test".to_string(), Label::new(12)), Ok(()));
        assert_eq!(table.insert("test2".to_string(), Label::new(0)), Ok(()));
        assert_eq!(table.get("test"), Some(&Label::new(12)));
        assert_eq!(table.get("test2"), Some(&Label::new(0)));
        assert_eq!(table.get("none"), None);
    }
}
