// Copyright 2019 Robin Freyler
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Utilities for parsing routines and data structures.

use crate::parse::{Identifier, ParseError};
use core::marker::PhantomData;

/// Contains imported and internal entities and provides them
/// in the same index space but with a separation between them.
#[derive(Debug)]
pub struct ImportedOrInternal<T, I> {
    /// The number of imported entities.
    len_imported: usize,
    /// Imported entities followed by internal ones.
    entities: Vec<T>,
    /// Import names of imported entities.
    namespaces: Vec<ImportName>,
    /// Marker to trick Rust into `I` being used.
    id_marker: PhantomData<fn() -> I>,
}

/// A module and field name for an imported entity.
#[derive(Debug)]
pub struct ImportName {
    module_name: String,
    field_name: String,
}

impl ImportName {
    /// Creates a new import name from the given module and field names.
    pub fn new(module_name: &str, field_name: &str) -> Self {
        Self {
            module_name: module_name.to_string(),
            field_name: field_name.to_string(),
        }
    }

    /// Returns the module name of the import.
    pub fn module_name(&self) -> &str {
        &self.module_name
    }

    /// Returns the field name of the import.
    pub fn field_name(&self) -> &str {
        &self.field_name
    }
}

impl<T, I> Default for ImportedOrInternal<T, I> {
    fn default() -> Self {
        ImportedOrInternal::new()
    }
}

impl<T, I> ImportedOrInternal<T, I> {
    /// Creates a new empty merged entities container.
    pub fn new() -> Self {
        Self {
            len_imported: 0,
            entities: Vec::new(),
            namespaces: Vec::new(),
            id_marker: Default::default(),
        }
    }

    /// Reserves the given number of additional elements.
    ///
    /// # Example
    ///
    /// For function signatures this is used for the internal
    /// function definition signatures.
    pub fn reserve(&mut self, additional: usize) {
        self.entities.reserve(additional);
    }

    /// Returns the number of imported and internal entities.
    pub fn len(&self) -> usize {
        self.entities.len()
    }

    /// Returns the number of imported entities.
    pub fn len_imported(&self) -> usize {
        self.len_imported
    }

    /// Returns the number of internal entities.
    pub fn len_internal(&self) -> usize {
        self.len() - self.len_imported
    }

    /// Pushes a new internal entity.
    pub fn push_internal(&mut self, entity: T) {
        self.entities.push(entity);
    }

    /// Returns a slice over the imported entities.
    pub fn imported_entities_slice(&self) -> &[T] {
        &self.entities[0..self.len_imported()]
    }

    /// Returns a slice over the internal entities.
    pub fn internal_entities_slice(&self) -> &[T] {
        &self.entities[self.len_imported()..]
    }

    /// Returns a slice over all entities.
    pub fn entities_slice(&self) -> &[T] {
        &self.entities[..]
    }
}

impl<T, I> ImportedOrInternal<T, I>
where
    I: Identifier,
{
    /// Returns `true` if `id` refers to an imported entity.
    pub fn is_imported(&self, id: I) -> bool {
        id.get() < self.len_imported
    }

    /// Returns `true` if `id` refers to an internal entity.
    pub fn is_internal(&self, id: I) -> bool {
        !self.is_imported(id)
    }
}

impl<'a, T, I> ImportedOrInternal<T, I> {
    /// Pushes a new imported entitiy.
    ///
    /// # Errors
    ///
    /// Returns an error if internal entities have already been pushed before.
    pub fn push_imported(
        &mut self,
        module_name: &'a str,
        field_name: &'a str,
        entity: T,
    ) -> Result<(), ParseError> {
        if self.len_internal() != 0 {
            return Err(ParseError::ImportedEntityAfterInternal)
        }
        self.entities.push(entity);
        self.namespaces
            .push(ImportName::new(module_name, field_name));
        self.len_imported += 1;
        Ok(())
    }
}

impl<'a, T, I> core::ops::Index<I> for ImportedOrInternal<T, I>
where
    I: Identifier,
{
    type Output = T;

    fn index(&self, id: I) -> &Self::Output {
        &self.entities[id.get()]
    }
}
