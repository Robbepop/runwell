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

use crate::parse::{Identifier, ParseError};
use core::marker::PhantomData;

/// Contains imported and internal entities and provides them
/// in the same index space but with a separation between them.
#[derive(Debug)]
pub struct UnifiedImportedInternal<'a, T, I> {
    /// The number of imported entities.
    len_imported: usize,
    /// Imported entities followed by internal ones.
    entities: Vec<T>,
    /// Namespace of imported entities.
    namespaces: Vec<Namespace<'a>>,
    /// Marker to trick Rust into `I` being used.
    id_marker: PhantomData<fn() -> &'a I>,
}

/// The namespace of an imported entity.
#[derive(Debug)]
pub struct Namespace<'a> {
    /// The imported module name.
    module_name: &'a str,
    /// The imported field name.
    field_name: &'a str,
}

impl<T, I> Default for UnifiedImportedInternal<'_, T, I> {
    fn default() -> Self {
        UnifiedImportedInternal::new()
    }
}

impl<T, I> UnifiedImportedInternal<'_, T, I> {
    /// Creates a new empty merged entities container.
    pub fn new() -> Self {
        Self {
            len_imported: 0,
            entities: Vec::new(),
            namespaces: Vec::new(),
            id_marker: Default::default(),
        }
    }

    /// Returns the number of imported entities.
    pub fn len_imported(&self) -> usize {
        self.len_imported
    }

    /// Returns the number of internal entities.
    pub fn len_internal(&self) -> usize {
        self.entities.len() - self.len_imported
    }

    /// Pushes a new internal entity.
    pub fn push_internal(&mut self, entity: T) {
        self.entities.push(entity);
    }
}

impl<T, I> UnifiedImportedInternal<'_, T, I>
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

impl<'a, T, I> UnifiedImportedInternal<'a, T, I> {
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
        self.namespaces.push(Namespace {
            module_name,
            field_name,
        });
        self.len_imported += 1;
        Ok(())
    }
}
