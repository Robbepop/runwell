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

use crate::parse::{
    module::Data,
    Element,
    Export,
    FunctionBody,
    FunctionId,
    FunctionSig,
    FunctionSigId,
    GlobalVariableDecl,
    Initializer,
    Module,
    ParseError,
};
use derive_more::Display;
use wasmparser::{MemoryType, TableType};

/// A builder interface for a Wasm module.
///
/// Allows to mutate a module through some dedicated interfaces.
/// Used by the internal Wasm parser.
#[derive(Debug)]
pub struct ModuleBuilder {
    /// The Wasm module that is being build.
    module: Module,
    /// Count of expected function bodies.
    expected_fn_bodies: Option<usize>,
    /// Count of expected data elements.
    expected_data_elems: Option<usize>,
    /// Count reserved function signatures.
    expected_signatures: Option<usize>,
    /// Count reserved function definitions.
    expected_fn_defs: Option<usize>,
    /// Count reserved tables.
    expected_tables: Option<usize>,
    /// Count reserved elements.
    expected_elements: Option<usize>,
}

#[derive(Debug, Display, Copy, Clone, PartialEq, Eq)]
pub enum WasmSection {
    Types,
    Imports,
    Exports,
    Elements,
    Globals,
    DataCount,
    FnBodiesStart,
    FnBodies,
    StartFn,
    Data,
}

#[derive(Debug, Display, Copy, Clone, PartialEq, Eq)]
pub enum WasmSectionEntry {
    Type,
    FnSigs,
    Import,
    Table,
    Export,
    Element,
    Global,
    FnBody,
    Data,
}

#[derive(Debug, Display, PartialEq, Eq)]
pub enum BuildError {
    #[display(fmt = "encountered unexpected duplicate section: {}", self.section)]
    DuplicateSection { section: WasmSection },
    #[display(fmt = "encountered missing section: {}", self.section)]
    MissingSection { section: WasmSection },
    #[display(
        fmt = "registered fewer entries than expected for {}. expected: {}, actual: {}",
        entry,
        expected,
        actual
    )]
    MissingElements {
        entry: WasmSectionEntry,
        expected: usize,
        actual: usize,
    },
    #[display(
        fmt = "registered more entries than reserved (= {}) for: {}",
        reserved,
        entry
    )]
    TooManyElements {
        entry: WasmSectionEntry,
        reserved: usize,
    },
    #[display(
        fmt = "duplicate reservation of {} section entries for section {}. previous reservation: {}",
        reserved,
        entry,
        previous
    )]
    DuplicateReservation {
        entry: WasmSectionEntry,
        reserved: usize,
        previous: usize,
    },
    #[display(fmt = "missing reservation for section {}", entry)]
    MissingReservation { entry: WasmSectionEntry },
}

impl<'a> ModuleBuilder {
    /// Creates a new module builder for the given module.
    pub(super) fn new(module: Module) -> Self {
        Self {
            module,
            expected_fn_bodies: None,
            expected_data_elems: None,
            expected_signatures: None,
            expected_fn_defs: None,
            expected_tables: None,
            expected_elements: None,
        }
    }

    /// Reserves an amount of total expected function signatures to be registered.
    pub fn reserve_fn_signatures(
        &mut self,
        total_count: usize,
    ) -> Result<(), BuildError> {
        if let Some(previous) = self.expected_signatures {
            return Err(BuildError::DuplicateReservation {
                entry: WasmSectionEntry::Type,
                reserved: total_count,
                previous,
            })
        }
        self.module.signatures.reserve(total_count);
        self.expected_signatures = Some(total_count);
        Ok(())
    }

    /// Pushes the signature to the Wasm module.
    pub fn register_fn_signature(
        &mut self,
        sig: FunctionSig,
    ) -> Result<(), BuildError> {
        match self.expected_signatures {
            Some(total) => {
                let actual = self.module.signatures.len();
                if total - actual == 0 {
                    return Err(BuildError::TooManyElements {
                        entry: WasmSectionEntry::Type,
                        reserved: total,
                    })
                }
                self.module.signatures.push(sig);
            }
            None => {
                return Err(BuildError::MissingReservation {
                    entry: WasmSectionEntry::Type,
                })
            }
        }
        Ok(())
    }

    /// Pushes a new imported function to the Wasm module.
    ///
    /// # Errors
    ///
    /// Errors if an imported function is pushed after an internal
    /// function has already been pushed to the same Wasm module.
    pub fn push_imported_fn(
        &mut self,
        module_name: &'a str,
        field_name: &'a str,
        fn_sig_id: FunctionSigId,
    ) -> Result<(), ParseError> {
        self.module
            .fn_sigs
            .push_imported(module_name, field_name, fn_sig_id)
    }

    /// Reserves an amount of total expected function definitions to be registered.
    pub fn reserve_fn_defs(
        &mut self,
        total_count: usize,
    ) -> Result<(), BuildError> {
        if let Some(previous) = self.expected_fn_defs {
            return Err(BuildError::DuplicateReservation {
                entry: WasmSectionEntry::FnSigs,
                reserved: total_count,
                previous,
            })
        }
        self.module.fn_sigs.reserve(total_count);
        self.expected_fn_defs = Some(total_count);
        Ok(())
    }

    /// Pushes a new function definition to the Wasm module.
    pub fn push_fn_def(
        &mut self,
        fn_sig_id: FunctionSigId,
    ) -> Result<(), BuildError> {
        match self.expected_fn_defs {
            Some(total) => {
                let actual = self.module.fn_sigs.len_internal();
                if total - actual == 0 {
                    return Err(BuildError::TooManyElements {
                        entry: WasmSectionEntry::FnSigs,
                        reserved: total,
                    })
                }
                self.module.fn_sigs.push_internal(fn_sig_id);
            }
            None => {
                return Err(BuildError::MissingReservation {
                    entry: WasmSectionEntry::FnSigs,
                })
            }
        }
        Ok(())
    }

    /// Pushes a new imported global variable to the Wasm module.
    ///
    /// # Errors
    ///
    /// Errors if an imported global variable is pushed after an internal
    /// global variable has already been pushed to the same Wasm module.
    pub fn push_imported_global(
        &mut self,
        module_name: &'a str,
        field_name: &'a str,
        global: GlobalVariableDecl,
    ) -> Result<(), ParseError> {
        self.module
            .globals
            .push_imported(module_name, field_name, global)
    }

    /// Pushes a new internal global variable to the Wasm module.
    pub fn push_internal_global(&mut self, global: GlobalVariableDecl) {
        self.module.globals.push_internal(global)
    }

    /// Pushes a new imported linear memory to the Wasm module.
    ///
    /// # Errors
    ///
    /// Errors if an imported linear memory is pushed after an internal
    /// linear memory has already been pushed to the same Wasm module.
    pub fn push_imported_linear_memory(
        &mut self,
        module_name: &'a str,
        field_name: &'a str,
        memory: MemoryType,
    ) -> Result<(), ParseError> {
        self.module.linear_memories.push_imported(
            module_name,
            field_name,
            memory,
        )
    }

    /// Pushes a new internal linear memory to the Wasm module.
    pub fn push_internal_linear_memory(&mut self, memory: MemoryType) {
        self.module.linear_memories.push_internal(memory)
    }

    /// Pushes a new imported table to the Wasm module.
    ///
    /// # Errors
    ///
    /// Errors if an imported table is pushed after an internal
    /// table has already been pushed to the same Wasm module.
    pub fn push_imported_table(
        &mut self,
        module_name: &'a str,
        field_name: &'a str,
        table: TableType,
    ) -> Result<(), ParseError> {
        self.module
            .tables
            .push_imported(module_name, field_name, table)
    }

    /// Reserves an amount of total expected table definitions to be registered.
    pub fn reserve_tables(
        &mut self,
        total_count: usize,
    ) -> Result<(), BuildError> {
        if let Some(previous) = self.expected_tables {
            return Err(BuildError::DuplicateReservation {
                entry: WasmSectionEntry::Table,
                reserved: total_count,
                previous,
            })
        }
        self.module.tables.reserve(total_count);
        self.expected_tables = Some(total_count);
        Ok(())
    }

    /// Pushes a new internal linear memory to the Wasm module.
    pub fn push_internal_table(&mut self, table: TableType) {
        self.module.tables.push_internal(table)
    }

    /// Pushes a new export to the Wasm module.
    pub fn push_export(&mut self, export: Export) {
        self.module.exports.push(export)
    }

    /// Sets the start function to the given function ID.
    pub fn set_start_fn(&mut self, id: FunctionId) {
        assert!(self.module.start_fn.is_none());
        self.module.start_fn = Some(id);
    }

    /// Reserves an amount of total expected element definitions to be registered.
    pub fn reserve_elements(&mut self, total_count: usize) -> Result<(), BuildError> {
        if let Some(previous) = self.expected_elements {
            return Err(BuildError::DuplicateReservation {
                entry: WasmSectionEntry::Element,
                reserved: total_count,
                previous,
            })
        }
        self.module.elements.reserve(total_count);
        self.expected_elements = Some(total_count);
        Ok(())
    }

    /// Pushes a new element of the element section to the Wasm module.
    pub fn push_element(&mut self, element: Element) -> Result<(), BuildError> {
        match self.expected_elements {
            Some(total) => {
                let actual = self.module.elements.len();
                if total - actual == 0 {
                    return Err(BuildError::TooManyElements {
                        entry: WasmSectionEntry::Element,
                        reserved: total,
                    })
                }
                self.module.elements.push(element);
            }
            None => {
                return Err(BuildError::MissingReservation {
                    entry: WasmSectionEntry::Element,
                })
            }
        }
        Ok(())
    }

    /// Reserves space for `count` expected function bodies.
    pub fn reserve_fn_bodies(
        &mut self,
        total_count: usize,
    ) -> Result<(), BuildError> {
        match self.expected_fn_bodies {
            None => {
                self.module.fn_bodies.reserve(total_count);
                self.expected_fn_bodies = Some(total_count);
            }
            Some(_) => {
                return Err(BuildError::DuplicateSection {
                    section: WasmSection::FnBodiesStart,
                })
            }
        }
        Ok(())
    }

    /// Pushes a new function body of an internal function to the Wasm module.
    pub fn push_fn_body(
        &mut self,
        fn_body: FunctionBody,
    ) -> Result<(), BuildError> {
        match self.expected_fn_bodies {
            Some(total) => {
                let actual = self.module.fn_bodies.len();
                if total - actual == 0 {
                    return Err(BuildError::TooManyElements {
                        entry: WasmSectionEntry::FnBody,
                        reserved: total,
                    })
                }
                self.module.fn_bodies.push(fn_body);
            }
            None => {
                return Err(BuildError::MissingReservation {
                    entry: WasmSectionEntry::FnBody,
                })
            }
        }
        Ok(())
    }

    /// Pushes a new internal global variable initializer expression
    /// to the Wasm module.
    pub fn push_global_initializer(&mut self, initializer: Initializer) {
        self.module.globals_initializers.push(initializer)
    }

    /// Pushes a new internal table initializer expression
    /// to the Wasm module.
    pub fn push_table_initializer(&mut self, initializer: Initializer) {
        self.module.table_initializers.push(initializer)
    }

    /// Reserves space for `count` expected data elements.
    pub fn reserve_data_elements(
        &mut self,
        total_count: usize,
    ) -> Result<(), BuildError> {
        match self.expected_data_elems {
            None => {
                self.module.data.reserve(total_count);
                self.expected_data_elems = Some(total_count);
            }
            Some(_) => {
                // The `DataCount` section has been introduced with the
                // bulk-memory Wasm extension and is only optional.
                // Therefore we do not return an error for this case.
            }
        }
        Ok(())
    }

    /// Pushes a new data definition to the Wasm module.
    pub fn push_data(&mut self, data: Data) -> Result<(), BuildError> {
        match self.expected_data_elems {
            Some(total) => {
                let actual = self.module.data.len();
                if total - actual == 0 {
                    return Err(BuildError::TooManyElements {
                        entry: WasmSectionEntry::Data,
                        reserved: total,
                    })
                }
                self.module.data.push(data);
            }
            None => {
                return Err(BuildError::MissingReservation {
                    entry: WasmSectionEntry::Data,
                })
            }
        }
        Ok(())
    }

    /// Finalizes building of the Wasm module.
    pub fn finalize(self) -> Result<Module, BuildError> {
        if let Some(expected) = self.expected_data_elems {
            let actual = self.module.data.len();
            if actual != expected {
                return Err(BuildError::MissingElements {
                    entry: WasmSectionEntry::Data,
                    expected,
                    actual,
                })
            }
        }
        if let Some(expected) = self.expected_tables {
            let actual = self.module.tables.len_internal();
            if actual != expected {
                return Err(BuildError::MissingElements {
                    entry: WasmSectionEntry::Table,
                    expected,
                    actual,
                })
            }
        }
        if let Some(expected) = self.expected_fn_defs {
            let actual = self.module.fn_sigs.len_internal();
            if actual != expected {
                return Err(BuildError::MissingElements {
                    entry: WasmSectionEntry::FnSigs,
                    expected,
                    actual,
                })
            }
        }
        if let Some(expected) = self.expected_fn_bodies {
            let actual = self.module.fn_bodies.len();
            if actual != expected {
                return Err(BuildError::MissingElements {
                    entry: WasmSectionEntry::FnBody,
                    expected,
                    actual,
                })
            }
        }
        if let Some(expected) = self.expected_elements {
            let actual = self.module.elements.len();
            if actual != expected {
                return Err(BuildError::MissingElements {
                    entry: WasmSectionEntry::Element,
                    expected,
                    actual,
                })
            }
        }
        Ok(self.module)
    }
}
