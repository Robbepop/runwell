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

use super::ImportName;
use crate::parse::{
    module::Data,
    Element,
    Export,
    FunctionBody,
    FunctionId,
    FunctionSig,
    FunctionSigId,
    GlobalInitExpr,
    GlobalVariableDecl,
    GlobalVariableId,
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
    /// Count of expected data elements.
    expected_data_elems: Option<usize>,
    /// Count reserved function signatures.
    expected_types: Option<usize>,
    /// Count reserved function definitions.
    expected_fn_defs: Option<usize>,
    /// Count of expected function bodies.
    expected_fn_bodies: Option<usize>,
    /// Count reserved tables.
    expected_tables: Option<usize>,
    /// Count reserved elements.
    expected_elements: Option<usize>,
    /// Count remaining expected element definitions.
    remaining_elements: usize,
    /// Count reserved linear memories.
    expected_linear_memories: Option<usize>,
    /// Count reserved global variables.
    expected_globals: Option<usize>,
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
    LinearMemory,
    Global,
    FnBody,
    Data,
}

#[derive(Debug, Display, PartialEq, Eq)]
pub enum BuildError {
    #[display(fmt = "unable to resolve table element offset value")]
    CouldNotResolveTableElementOffset,
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
            expected_types: None,
            expected_fn_defs: None,
            expected_tables: None,
            expected_elements: None,
            remaining_elements: 0,
            expected_linear_memories: None,
            expected_globals: None,
        }
    }

    /// Reserves an amount of total expected function signatures to be registered.
    pub fn reserve_types(
        &mut self,
        total_count: usize,
    ) -> Result<(), BuildError> {
        if let Some(previous) = self.expected_types {
            return Err(BuildError::DuplicateReservation {
                entry: WasmSectionEntry::Type,
                reserved: total_count,
                previous,
            })
        }
        self.module.types.reserve(total_count);
        self.expected_types = Some(total_count);
        Ok(())
    }

    /// Pushes the signature to the Wasm module.
    pub fn register_type(
        &mut self,
        sig: FunctionSig,
    ) -> Result<(), BuildError> {
        match self.expected_types {
            Some(total) => {
                let actual = self.module.types.len();
                if total - actual == 0 {
                    return Err(BuildError::TooManyElements {
                        entry: WasmSectionEntry::Type,
                        reserved: total,
                    })
                }
                self.module.types.push(sig);
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
    pub fn import_fn_declaration(
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
    pub fn reserve_fn_decls(
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

    /// Declares a new function with its signature.
    ///
    /// Every function declaration requires a definition later on in the parsing process.
    pub fn declare_fn(
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
    pub fn import_global_variable(
        &mut self,
        module_name: &'a str,
        field_name: &'a str,
        global: GlobalVariableDecl,
    ) -> Result<(), ParseError> {
        self.module
            .globals
            .push_imported(ImportName::new(module_name, field_name), global)?;
        Ok(())
    }

    /// Pushes a new imported linear memory to the Wasm module.
    ///
    /// # Errors
    ///
    /// Errors if an imported linear memory is pushed after an internal
    /// linear memory has already been pushed to the same Wasm module.
    pub fn import_linear_memory(
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

    /// Reserves an amount of total expected linear memory definitions to be registered.
    pub fn reserve_linear_memories(
        &mut self,
        total_count: usize,
    ) -> Result<(), BuildError> {
        if let Some(previous) = self.expected_linear_memories {
            return Err(BuildError::DuplicateReservation {
                entry: WasmSectionEntry::LinearMemory,
                reserved: total_count,
                previous,
            })
        }
        self.module.linear_memories.reserve(total_count);
        self.expected_linear_memories = Some(total_count);
        Ok(())
    }

    /// Pushes a new internal linear memory to the Wasm module.
    pub fn declare_linear_memory(
        &mut self,
        memory: MemoryType,
    ) -> Result<(), BuildError> {
        match self.expected_linear_memories {
            Some(total) => {
                let actual = self.module.linear_memories.len_internal();
                if total - actual == 0 {
                    return Err(BuildError::TooManyElements {
                        entry: WasmSectionEntry::LinearMemory,
                        reserved: total,
                    })
                }
                self.module.linear_memories.push_internal(memory);
            }
            None => {
                return Err(BuildError::MissingReservation {
                    entry: WasmSectionEntry::LinearMemory,
                })
            }
        }
        Ok(())
    }

    /// Pushes a new imported table to the Wasm module.
    ///
    /// # Errors
    ///
    /// Errors if an imported table is pushed after an internal
    /// table has already been pushed to the same Wasm module.
    pub fn import_table(
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
    ) -> Result<(), ParseError> {
        if let Some(previous) = self.expected_tables {
            return Err(BuildError::DuplicateReservation {
                entry: WasmSectionEntry::Table,
                reserved: total_count,
                previous,
            })?
        }
        self.module.tables.reserve(total_count);
        self.module.elements.reserve_total_tables(total_count)?;
        self.expected_tables = Some(total_count);
        Ok(())
    }

    /// Pushes a new internal linear memory to the Wasm module.
    pub fn declare_table(
        &mut self,
        table: TableType,
    ) -> Result<(), BuildError> {
        match self.expected_tables {
            Some(total) => {
                let actual = self.module.tables.len_internal();
                if total - actual == 0 {
                    return Err(BuildError::TooManyElements {
                        entry: WasmSectionEntry::Table,
                        reserved: total,
                    })
                }
                self.module.tables.push_internal(table);
            }
            None => {
                return Err(BuildError::MissingReservation {
                    entry: WasmSectionEntry::Table,
                })
            }
        }
        Ok(())
    }

    /// Pushes a new export to the Wasm module.
    pub fn register_export(&mut self, export: Export) {
        self.module.exports.push(export)
    }

    /// Sets the start function to the given function ID.
    pub fn set_start_fn(&mut self, id: FunctionId) {
        assert!(self.module.start_fn.is_none());
        self.module.start_fn = Some(id);
    }

    /// Reserves an amount of total expected element definitions to be registered.
    pub fn reserve_elements(
        &mut self,
        total_count: usize,
    ) -> Result<(), BuildError> {
        if let Some(previous) = self.expected_elements {
            return Err(BuildError::DuplicateReservation {
                entry: WasmSectionEntry::Element,
                reserved: total_count,
                previous,
            })
        }
        self.expected_elements = Some(total_count);
        self.remaining_elements = total_count;
        Ok(())
    }

    /// Resolves the value of the given global variable.
    ///
    /// This resolves chains of global variable references if any.
    /// Returns `None` if the global variable currently has no defined value.
    fn resolve_global_variable(
        &self,
        id: GlobalVariableId,
    ) -> Option<GlobalInitExpr> {
        match self.module.get_global_initializer(id)? {
            value @ GlobalInitExpr::I32Const(_)
            | value @ GlobalInitExpr::I64Const(_) => Some(value.clone()),
            GlobalInitExpr::GetGlobal(id) => self.resolve_global_variable(*id),
        }
    }

    /// Pushes a new element of the element section to the Wasm module.
    pub fn define_element(
        &mut self,
        element: Element,
    ) -> Result<(), ParseError> {
        let table_id = element.table_id;
        match self.expected_elements {
            Some(total) => {
                let actual = total - self.remaining_elements;
                self.remaining_elements -= 1;
                if total - actual == 0 {
                    return Err(BuildError::TooManyElements {
                        entry: WasmSectionEntry::Element,
                        reserved: total,
                    })?
                }
                let offset = match element.offset {
                    GlobalInitExpr::I32Const(value) => Ok(value as usize),
                    GlobalInitExpr::I64Const(value) => Ok(value as usize),
                    GlobalInitExpr::GetGlobal(id) => {
                        // Recursively fetch value of global variable if any.
                        let resolved = self.resolve_global_variable(id).ok_or(
                            BuildError::CouldNotResolveTableElementOffset,
                        )?;
                        match resolved {
                            GlobalInitExpr::I32Const(value) => {
                                Ok(value as usize)
                            }
                            GlobalInitExpr::I64Const(value) => {
                                Ok(value as usize)
                            }
                            GlobalInitExpr::GetGlobal(_) => Err(
                                BuildError::CouldNotResolveTableElementOffset,
                            ),
                        }
                    }
                }?;
                for (n, item) in element.items().enumerate() {
                    let func_ref =
                        item.map_err(|_| ParseError::InvalidElementItem)?;
                    let index = offset + n;
                    self.module
                        .elements
                        .table_mut(table_id)
                        .set_func_ref(index, func_ref)?;
                }
            }
            None => {
                return Err(BuildError::MissingReservation {
                    entry: WasmSectionEntry::Element,
                })?
            }
        }
        Ok(())
    }

    /// Reserves space for `count` expected function bodies.
    pub fn reserve_fn_defs(
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
    pub fn define_fn(
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

    /// Reserves space for `count` expected global variables.
    pub fn reserve_global_variables(
        &mut self,
        total_count: usize,
    ) -> Result<(), ParseError> {
        match self.expected_globals {
            None => {
                self.module.globals.reserve_definitions(total_count)?;
                self.expected_globals = Some(total_count);
            }
            Some(_) => {
                return Err(BuildError::DuplicateSection {
                    section: WasmSection::Globals,
                })
                .map_err(Into::into)
            }
        }
        Ok(())
    }

    /// Defines yet another global variable, returning its unique ID.
    pub fn define_global_variable(
        &mut self,
        decl: GlobalVariableDecl,
        init_value: GlobalInitExpr,
    ) -> Result<GlobalVariableId, ParseError> {
        self.module.globals.push_defined(decl, init_value)
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
    pub fn define_data(&mut self, data: Data) -> Result<(), BuildError> {
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
            let actual = expected - self.remaining_elements;
            if actual != expected {
                return Err(BuildError::MissingElements {
                    entry: WasmSectionEntry::Element,
                    expected,
                    actual,
                })
            }
        }
        if let Some(expected) = self.expected_linear_memories {
            let actual = self.module.linear_memories.len_internal();
            if actual != expected {
                return Err(BuildError::MissingElements {
                    entry: WasmSectionEntry::LinearMemory,
                    expected,
                    actual,
                })
            }
        }
        if let Some(expected) = self.expected_globals {
            let actual = self.module.globals.len_defined();
            if actual != expected {
                return Err(BuildError::MissingElements {
                    entry: WasmSectionEntry::Global,
                    expected,
                    actual,
                })
            }
        }
        Ok(self.module)
    }
}
