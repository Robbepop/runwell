// Copyright 2021 Robin Freyler
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

use core::convert::TryFrom;
use derive_more::{Display, Error};
use entity::RawIdx;
use ir::primitive::{Func, Mem, Table};
use module::Global;

/// An error upon parsing, validating or operating on Wasm exports.
#[derive(Debug, Display, Error, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ExportError {
    #[display(fmt = "encountered unsupported export kind: {}", kind)]
    UnsupportedExportKind { kind: UnsupportedExportKind },
}

#[derive(Debug, Display, Error, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

/// An export kind and a reference to the entity it exports.
#[derive(Debug)]
pub enum ExportItem {
    /// An exported function.
    Function(Func),
    /// An exported table.
    Table(Table),
    /// An exported linear memory.
    Memory(Mem),
    /// An exported global variable.
    Global(Global),
}

/// An export item from a Wasm export section.
pub struct Export<'a> {
    field: &'a str,
    kind: ExportKind,
    raw_index: RawIdx,
}

impl<'a> Export<'a> {
    /// Returns the export item's field name.
    pub fn field(&self) -> &'a str {
        &self.field
    }

    /// Returns the export item's kind and unique ID.
    pub fn item(&self) -> ExportItem {
        match self.kind {
            ExportKind::Function => {
                ExportItem::Function(Func::from_raw(self.raw_index))
            }
            ExportKind::Table => {
                ExportItem::Table(Table::from_raw(self.raw_index))
            }
            ExportKind::Memory => {
                ExportItem::Memory(Mem::from_raw(self.raw_index))
            }
            ExportKind::Global => {
                ExportItem::Global(Global::from_raw(self.raw_index))
            }
        }
    }
}

impl<'a> TryFrom<wasmparser::Export<'a>> for Export<'a> {
    type Error = ExportError;

    fn try_from(export: wasmparser::Export<'a>) -> Result<Self, Self::Error> {
        let field = export.field;
        let raw_index = RawIdx::from_u32(export.index);
        let kind = ExportKind::try_from(export.kind)?;
        Ok(Self {
            field,
            kind,
            raw_index,
        })
    }
}
