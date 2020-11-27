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
use wasmparser::ExternalKind;

/// An export definition of a Wasm module.
#[derive(Debug)]
pub struct Export {
    /// The export field name.
    field: String,
    /// The export kind.
    kind: ExportKind,
}

impl Export {
    /// Returns the export kind.
    ///
    /// # Note
    ///
    /// Use this to extract further information about the exported entity.
    pub fn kind(&self) -> &ExportKind {
        &self.kind
    }
}

/// An export kind of an export definition.
#[derive(Debug)]
pub enum ExportKind {
    /// An exported function.
    Function(FunctionId),
    /// An exported global variable.
    Global(GlobalVariableId),
    /// An exported linear memory.
    Memory(LinearMemoryId),
    /// An exported table.
    Table(TableId),
}

impl<'a> From<wasmparser::Export<'a>> for Export {
    fn from(wasm_export: wasmparser::Export<'a>) -> Self {
        let id = wasm_export.index;
        Self {
            field: wasm_export.field.to_string(),
            kind: match wasm_export.kind {
                ExternalKind::Function => {
                    ExportKind::Function(FunctionId::from_u32(id))
                }
                ExternalKind::Global => {
                    ExportKind::Global(GlobalVariableId::from_u32(id))
                }
                ExternalKind::Memory => {
                    ExportKind::Memory(LinearMemoryId::from_u32(id))
                }
                ExternalKind::Table => ExportKind::Table(TableId::from_u32(id)),
                ExternalKind::Event => {
                    unimplemented!(
                        "event exports are not supported by the Runwell JIT"
                    )
                }
                ExternalKind::Module => {
                    unimplemented!(
                        "module exports are not supported by the Runwell JIT"
                    )
                }
                ExternalKind::Instance => {
                    unimplemented!(
                        "instance exports are not supported by the Runwell JIT"
                    )
                }
                ExternalKind::Type => {
                    unimplemented!(
                        "type exports are not supported by the Runwell JIT"
                    )
                }
            },
        }
    }
}
