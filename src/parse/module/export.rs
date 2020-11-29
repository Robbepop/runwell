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
use core::convert::TryFrom;
use core::slice::Iter as SliceIter;
use derive_more::Display;

#[derive(Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ExportError {
    #[display(fmt = "encountered unsupported export kind: {}", kind)]
    UnsupportedExportKind { kind: UnsupportedExportKind },
}

#[derive(Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum UnsupportedExportKind {
    Event,
    Module,
    Instance,
    Type,
}

/// Supported kinds of exports.
pub enum ExportKind {
    /// An exported function.
    Function,
    /// An exported table.
    Table,
    /// An exported linear memory.
    Memory,
    /// An exported global variable.
    Global,
}

impl TryFrom<wasmparser::ExternalKind> for ExportKind {
    type Error = ExportError;

    fn try_from(kind: wasmparser::ExternalKind) -> Result<Self, Self::Error> {
        match kind {
            wasmparser::ExternalKind::Function => Ok(ExportKind::Function),
            wasmparser::ExternalKind::Table => Ok(ExportKind::Table),
            wasmparser::ExternalKind::Memory => Ok(ExportKind::Memory),
            wasmparser::ExternalKind::Global => Ok(ExportKind::Global),
            wasmparser::ExternalKind::Event => {
                Err(ExportError::UnsupportedExportKind {
                    kind: UnsupportedExportKind::Event,
                })
            }
            wasmparser::ExternalKind::Module => {
                Err(ExportError::UnsupportedExportKind {
                    kind: UnsupportedExportKind::Module,
                })
            }
            wasmparser::ExternalKind::Instance => {
                Err(ExportError::UnsupportedExportKind {
                    kind: UnsupportedExportKind::Instance,
                })
            }
            wasmparser::ExternalKind::Type => {
                Err(ExportError::UnsupportedExportKind {
                    kind: UnsupportedExportKind::Type,
                })
            }
        }
    }
}

/// An export kind with the associated ID.
#[derive(Debug)]
pub enum Export {
    /// An exported function.
    Function(FunctionId),
    /// An exported table.
    Table(TableId),
    /// An exported linear memory.
    Memory(LinearMemoryId),
    /// An exported global variable.
    Global(GlobalVariableId),
}

/// An export item from a Wasm export section.
pub struct ExportItem<'a> {
    field: &'a str,
    kind: ExportKind,
    raw_index: u32,
}

impl<'a> ExportItem<'a> {
    /// Returns the export item's field name.
    pub fn field(&self) -> &'a str {
        &self.field
    }

    /// Returns the export item's kind and unique ID.
    pub fn item(&self) -> Export {
        match self.kind {
            ExportKind::Function => {
                Export::Function(FunctionId::from_u32(self.raw_index))
            }
            ExportKind::Table => {
                Export::Table(TableId::from_u32(self.raw_index))
            }
            ExportKind::Memory => {
                Export::Memory(LinearMemoryId::from_u32(self.raw_index))
            }
            ExportKind::Global => {
                Export::Global(GlobalVariableId::from_u32(self.raw_index))
            }
        }
    }
}

impl<'a> TryFrom<wasmparser::Export<'a>> for ExportItem<'a> {
    type Error = ExportError;

    fn try_from(export: wasmparser::Export<'a>) -> Result<Self, Self::Error> {
        let field = export.field;
        let raw_index = export.index;
        let kind = ExportKind::try_from(export.kind)?;
        Ok(Self {
            field,
            kind,
            raw_index,
        })
    }
}

/// An exported item with its field name and unique ID.
#[derive(Debug)]
pub struct Exported<Id> {
    field: String,
    id: Id,
}

impl<Id> Exported<Id> {
    /// Creates a new exported items with the field name and unique ID.
    fn new(field: &str, id: Id) -> Self {
        Self { field: field.to_string(), id }
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
