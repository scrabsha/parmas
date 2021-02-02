//! Allows to handle labels in the assembly input.

use std::collections::HashMap;

use crate::Result;

/// Allows to store and retrieve the labels in the program source.
///
/// The values are stored as instruction-count.
pub(crate) struct LabelTable<'a> {
    labels: HashMap<&'a str, usize>,
}

impl<'a> LabelTable<'a> {
    /// Creates a new, empty `LabelTable`.
    pub(crate) fn new() -> LabelTable<'a> {
        LabelTable {
            labels: HashMap::new(),
        }
    }

    /// Adds a new symbol at a given position in the table..
    ///
    /// Returns an error if the symbol is defined somewhere else.
    pub(crate) fn add(&mut self, s: &'a str, p: usize) -> Result<()> {
        let already_existing = self.labels.insert(s, p);

        if let Some(_) = already_existing {
            Err("Redefinition of symbol")
        } else {
            Ok(())
        }
    }

    /// Adds any type containing labels to table.
    pub(crate) fn extend<T>(&mut self, ls: T) -> Result<()>
    where
        T: IntoIterator<Item = (&'a str, usize)>,
    {
        ls.into_iter().try_for_each(|(l, p)| self.add(l, p))
    }

    /// Resolves a label. Returns an error if the label does not exist.
    pub(crate) fn resolve(&self, l: &'a str) -> Result<usize> {
        self.labels.get(l).copied().ok_or("Label resolution failed")
    }
}
