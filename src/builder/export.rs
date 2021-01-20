// Copyright 2020 Robin Freyler
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

use crate::parse::{FunctionId, GlobalVariableId, LinearMemoryId, TableId};
use core::slice::Iter as SliceIter;

/// An exported item with its field name and unique ID.
#[derive(Debug)]
pub struct Exported<Id> {
    field: String,
    id: Id,
}

impl<Id> Exported<Id> {
    /// Creates a new exported items with the field name and unique ID.
    fn new(field: &str, id: Id) -> Self {
        Self {
            field: field.to_string(),
            id,
        }
    }
}

/// Container listing all the exported items.
#[derive(Debug, Default)]
pub struct Exports {
    functions: Vec<Exported<FunctionId>>,
    tables: Vec<Exported<TableId>>,
    memories: Vec<Exported<LinearMemoryId>>,
    globals: Vec<Exported<GlobalVariableId>>,
}

impl Exports {
    /// Pushes a new function export.
    pub fn export_function(&mut self, field: &str, id: FunctionId) {
        self.functions.push(Exported::new(field, id));
    }

    /// Pushes a new table export.
    pub fn export_table(&mut self, field: &str, id: TableId) {
        self.tables.push(Exported::new(field, id));
    }

    /// Pushes a new linear memory export.
    pub fn export_memory(&mut self, field: &str, id: LinearMemoryId) {
        self.memories.push(Exported::new(field, id));
    }

    /// Pushes a new global variable export.
    pub fn export_global(&mut self, field: &str, id: GlobalVariableId) {
        self.globals.push(Exported::new(field, id));
    }

    /// Returns an iterator over the unique IDs of all exported functions.
    pub fn iter_functions(&self) -> SliceIter<Exported<FunctionId>> {
        self.functions.iter()
    }

    /// Returns an iterator over the unique IDs of all exported tables.
    pub fn iter_tables(&self) -> SliceIter<Exported<TableId>> {
        self.tables.iter()
    }

    /// Returns an iterator over the unique IDs of all exported linear memories.
    pub fn iter_memories(&self) -> SliceIter<Exported<LinearMemoryId>> {
        self.memories.iter()
    }

    /// Returns an iterator over the unique IDs of all exported global variables.
    pub fn iter_globals(&self) -> SliceIter<Exported<GlobalVariableId>> {
        self.globals.iter()
    }
}
