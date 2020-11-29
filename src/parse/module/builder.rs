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

use super::{
    linear_memory::{Data, LinearMemoryDecl},
    table::TableDecl,
    EvaluationContext,
    ImportName,
    TableItems,
    ExportItem,
    Export,
};
use crate::parse::{
    Element,
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
use std::convert::TryFrom;
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
    /// Count remaining expected element segments.
    remaining_elements: usize,
    /// Count remaining expected data segments.
    remaining_data: usize,
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
            remaining_data: 0,
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
        let memory_decl = LinearMemoryDecl::try_from(memory)?;
        self.module.linear_memories.push_imported(
            ImportName::new(module_name, field_name),
            memory_decl,
        )?;
        Ok(())
    }

    /// Reserves an amount of total expected linear memory definitions to be registered.
    pub fn reserve_linear_memories(
        &mut self,
        total_count: usize,
    ) -> Result<(), ParseError> {
        if let Some(previous) = self.expected_linear_memories {
            return Err(BuildError::DuplicateReservation {
                entry: WasmSectionEntry::LinearMemory,
                reserved: total_count,
                previous,
            })
            .map_err(Into::into)
        }
        self.module
            .linear_memories
            .reserve_definitions(total_count)?;
        self.expected_linear_memories = Some(total_count);
        Ok(())
    }

    /// Pushes a new internal linear memory to the Wasm module.
    pub fn declare_linear_memory(
        &mut self,
        memory: MemoryType,
    ) -> Result<(), ParseError> {
        match self.expected_linear_memories {
            Some(total) => {
                let actual = self.module.linear_memories.len_defined();
                if total - actual == 0 {
                    return Err(BuildError::TooManyElements {
                        entry: WasmSectionEntry::LinearMemory,
                        reserved: total,
                    })
                    .map_err(Into::into)
                }
                let memory_decl = LinearMemoryDecl::try_from(memory)?;
                self.module
                    .linear_memories
                    .push_defined(memory_decl, Default::default())?;
            }
            None => {
                return Err(BuildError::MissingReservation {
                    entry: WasmSectionEntry::LinearMemory,
                })
                .map_err(Into::into)
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
        let table_decl = TableDecl::try_from(table)?;
        self.module.tables.push_imported(
            ImportName::new(module_name, field_name),
            table_decl,
        )?;
        Ok(())
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
            })
            .map_err(Into::into)
        }
        self.module.tables.reserve_definitions(total_count)?;
        self.expected_tables = Some(total_count);
        Ok(())
    }

    /// Pushes a new internal linear memory to the Wasm module.
    pub fn declare_table(
        &mut self,
        table: TableType,
    ) -> Result<(), ParseError> {
        match self.expected_tables {
            Some(total) => {
                let actual = self.module.tables.len_defined();
                if total - actual == 0 {
                    return Err(BuildError::TooManyElements {
                        entry: WasmSectionEntry::Table,
                        reserved: total,
                    })
                    .map_err(Into::into)
                }
                let table_decl = TableDecl::try_from(table)?;
                self.module
                    .tables
                    .push_defined(table_decl, TableItems::default())?;
            }
            None => {
                return Err(BuildError::MissingReservation {
                    entry: WasmSectionEntry::Table,
                })
                .map_err(Into::into)
            }
        }
        Ok(())
    }

    /// Declares a new exported item.
    pub fn declare_export(&mut self, export: ExportItem) {
        let field = export.field();
        match export.item() {
            Export::Function(id) => self.module.exports.export_function(field, id),
            Export::Table(id) => self.module.exports.export_table(field, id),
            Export::Memory(id) => self.module.exports.export_memory(field, id),
            Export::Global(id) => self.module.exports.export_global(field, id),
        }
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
        let global = self.module.globals.get_defined(id)?;
        Some(global.def.clone())
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
                    })
                    .map_err(Into::into)
                }
                let mut context = EvaluationContext::from(&self.module.globals);
                let offset = context.eval_const_i32(&element.offset)? as usize;
                let table = self
                    .module
                    .tables
                    .get_mut(table_id)
                    .expect("encountered unexpected invalid table ID")
                    .filter_map_defined()
                    .expect("encountered unexpected non-defined table");
                table.def.set_items(
                    offset,
                    element.items().map(|item| {
                        item.expect("encountered invalid element item")
                    }),
                )?;
            }
            None => {
                return Err(BuildError::MissingReservation {
                    entry: WasmSectionEntry::Element,
                })
                .map_err(Into::into)
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
    ) -> Result<(), ParseError> {
        match self.expected_data_elems {
            None => {
                self.module.linear_memories.reserve_definitions(total_count)?;
                self.expected_data_elems = Some(total_count);
                self.remaining_data = total_count;
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
    pub fn define_data(&mut self, data: Data) -> Result<(), ParseError> {
        match self.expected_data_elems {
            Some(total) => {
                let actual = total - self.remaining_data;
                self.remaining_data -= 1;
                if total - actual == 0 {
                    return Err(BuildError::TooManyElements {
                        entry: WasmSectionEntry::Data,
                        reserved: total,
                    })
                    .map_err(Into::into)
                }
                let id = data.id();
                let mut context = EvaluationContext::from(&self.module.globals);
                let offset = context.eval_const_i32(&data.offset())? as u32;
                let init = data.init();
                self
                    .module
                    .linear_memories
                    .get_mut(id)
                    .expect("encountered unexpected invalid linear memory ID")
                    .decl()
                    .contents()
                    .init_region(offset, init)?;
            }
            None => {
                return Err(BuildError::MissingReservation {
                    entry: WasmSectionEntry::Data,
                })
                .map_err(Into::into)
            }
        }
        Ok(())
    }

    /// Finalizes building of the Wasm module.
    pub fn finalize(self) -> Result<Module, BuildError> {
        if let Some(expected) = self.expected_data_elems {
            let actual = expected - self.remaining_data;
            if actual != expected {
                return Err(BuildError::MissingElements {
                    entry: WasmSectionEntry::Data,
                    expected,
                    actual,
                })
            }
        }
        if let Some(expected) = self.expected_tables {
            let actual = self.module.tables.len_defined();
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
            let actual = self.module.linear_memories.len_defined();
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
