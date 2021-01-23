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

#![allow(unused_variables)]

use super::{
    entity::Entities,
    BuilderError,
    Exports,
    LinearMemory,
    Table,
    Types,
};
use crate::parse::{
    self,
    Export,
    ExportItem,
    FunctionBody,
    FunctionId,
    FunctionType,
    FunctionTypeId,
    GlobalVariable,
    GlobalVariableId,
    ImportName,
    InitializerExpr,
    LinearMemoryId,
    ParseError,
    TableId,
};
use derive_more::From;

/// A parsed and validated Wasm module.
///
/// Used to create Wasm module instances for code execution.
#[derive(Debug)]
pub struct Module {}

/// The resources of a parsed and validated Wasm module.
#[derive(Debug, Default)]
pub struct ModuleResource {
    /// Function signature table.
    ///
    /// # Note
    ///
    /// Represents the Wasm `type` section.
    pub types: Types,
    /// Imported and internal function signatures.
    ///
    /// # Note
    ///
    /// Represents both the Wasm `function` and `code` sections.
    /// Also holds information about imported function declarations.
    pub function_types: Entities<FunctionId, FunctionTypeId, ()>,
    /// Imported and internal global variables.
    ///
    /// # Note
    ///
    /// Represents the Wasm `global` section.
    /// Also holds information about imported global variables.
    pub globals: Entities<GlobalVariableId, GlobalVariable, InitializerExpr>,
    /// Imported and internal linear memory sections.
    ///
    /// # Note
    ///
    /// Represents both the Wasm `memory` and `data` sections.
    /// Also holds information about imported linear memories.
    pub memories: Entities<LinearMemoryId, LinearMemory, ()>,
    /// Imported and internal tables.
    ///
    /// # Note
    ///
    /// Represents both the Wasm `table` and `data` element.
    /// Also holds information about imported tables.
    pub tables: Entities<TableId, Table, ()>,
    /// Export definitions.
    ///
    /// # Note
    ///
    /// Represents the Wasm `export` section.
    pub exports: Exports,
    /// Optional start function.
    ///
    /// # Note
    ///
    /// The start function is executed before the actually executed code upon instantiating
    /// a Wasm module if a start function has been defined.
    pub start_function: Option<FunctionId>,
}

/// Builds Wasm modules from binary Wasm inputs.
///
/// Implements the [`ModuleBuilder`] trait.
#[derive(Debug, Default)]
pub struct ModuleBuilder {
    resources: ModuleResource,
}

impl ModuleBuilder {
    /// Returns a gate to push new type definitions to the build module upon success.
    ///
    /// # Note
    ///
    /// Guaranteed to be called at most once and before any call to [`ModuleBuilder::import_section`].
    pub fn type_section(
        &mut self,
        count_types: u32,
    ) -> Result<DefineType, BuilderError> {
        self.resources.types.reserve(count_types)?;
        Ok(self.into())
    }

    /// Returns a gate to push new imports to the build module upon success.
    ///
    /// # Note
    ///
    /// Guaranteed to be called at most once and before any call to [`ModuleBuilder::function_section`].
    pub fn import_section(
        &mut self,
        count_imports: u32,
    ) -> Result<ImportEntity, BuilderError> {
        Ok(self.into())
    }

    /// Returns a gate to push new function declarations to the build module upon success.
    ///
    /// # Note
    ///
    /// Guaranteed to be called at most once and before any call to [`ModuleBuilder::table_section`].
    pub fn function_section(
        &mut self,
        count_functions: u32,
    ) -> Result<DeclareFunction, BuilderError> {
        self.resources
            .function_types
            .reserve_internals(count_functions)?;
        Ok(self.into())
    }

    /// Returns a gate to push new table declarations to the build module upon success.
    ///
    /// # Note
    ///
    /// Guaranteed to be called at most once and before any call to [`ModuleBuilder::memory_section`].
    pub fn table_section(
        &mut self,
        count_tables: u32,
    ) -> Result<DeclareTable, BuilderError> {
        self.resources.tables.reserve_internals(count_tables)?;
        Ok(self.into())
    }

    /// Returns a gate to push new linear memory declarations to the build module upon success.
    ///
    /// # Note
    ///
    /// Guaranteed to be called at most once and before any call to [`ModuleBuilder::global_section`].
    pub fn memory_section(
        &mut self,
        count_memories: u32,
    ) -> Result<DeclareMemory, BuilderError> {
        self.resources.memories.reserve_internals(count_memories)?;
        Ok(self.into())
    }

    /// Returns a gate to push new global variable definition to the build module upon success.
    ///
    /// # Note
    ///
    /// Guaranteed to be called at most once and before any call to [`ModuleBuilder::export_section`].
    pub fn global_section(
        &mut self,
        count_globals: u32,
    ) -> Result<DefineGlobal, BuilderError> {
        self.resources.globals.reserve_internals(count_globals)?;
        Ok(self.into())
    }

    /// Returns a gate to push new export declarations to the build module upon success.
    ///
    /// # Note
    ///
    /// Guaranteed to be called at most once and before any call to [`ModuleBuilder::start_function`].
    pub fn export_section(
        &mut self,
        count_exports: u32,
    ) -> Result<DeclareExport, BuilderError> {
        Ok(self.into())
    }

    /// Sets the start function to be executed for module instantiation.
    ///
    /// # Note
    ///
    /// Guaranteed to be called at most once and before any call to [`ModuleBuilder::element_section`].
    pub fn start_function(&mut self, id: crate::parse::FunctionId) {
        self.resources.start_function = Some(id);
    }

    /// Returns a gate to push new element items to the build module upon success.
    ///
    /// # Note
    ///
    /// Guaranteed to be called at most once and before any call to [`ModuleBuilder::code_section`].
    pub fn element_section(
        &mut self,
        count_elements: u32,
    ) -> Result<PushElement, BuilderError> {
        Ok(self.into())
    }

    /// Returns a gate to push new function bodies to the build module upon success.
    ///
    /// # Note
    ///
    /// Guaranteed to be called at most once and before any call to [`ModuleBuilder::data_section`].
    pub fn code_section(
        &mut self,
        count_function_bodies: u32,
    ) -> Result<DefineFunctionBody, BuilderError> {
        Ok(self.into())
    }

    /// Returns a gate to push new data items to the build module upon success.
    ///
    /// # Note
    ///
    /// Guaranteed to be called at most once and before any call to [`ModuleBuilder::finish`].
    pub fn data_section(
        &mut self,
        count_datas: u32,
    ) -> Result<PushData, BuilderError> {
        Ok(self.into())
    }

    /// Finishes building the module by returning the built Wasm module.
    pub fn finish(self) -> Result<Module, BuilderError> {
        Ok(Module {})
    }
}

#[derive(Debug, From)]
pub struct DefineType<'a> {
    builder: &'a mut ModuleBuilder,
}

impl<'a> DefineType<'a> {
    /// Defines a new type definition.
    ///
    /// # Note
    ///
    /// This is called once for every unique function type in the Wasm module.
    pub fn define_type(
        &mut self,
        function_type: FunctionType,
    ) -> Result<(), BuilderError> {
        self.builder.resources.types.push(function_type)?;
        Ok(())
    }
}

#[derive(Debug, From)]
pub struct ImportEntity<'a> {
    builder: &'a mut ModuleBuilder,
}

impl<'a> ImportEntity<'a> {
    /// Imports a new function with the given name.
    pub fn import_function(
        &mut self,
        import_name: ImportName,
        function_type_id: FunctionTypeId,
    ) -> Result<(), BuilderError> {
        self.builder
            .resources
            .function_types
            .push_imported(import_name.into(), function_type_id)?;
        Ok(())
    }

    /// Imports a new global variable with the given name.
    pub fn import_global(
        &mut self,
        import_name: ImportName,
        global: GlobalVariable,
    ) -> Result<(), BuilderError> {
        self.builder
            .resources
            .globals
            .push_imported(import_name.into(), global)?;
        Ok(())
    }

    /// Imports a new linear memory with the given name.
    pub fn import_memory(
        &mut self,
        import_name: ImportName,
        memory: parse::LinearMemory,
    ) -> Result<(), BuilderError> {
        self.builder
            .resources
            .memories
            .push_imported(import_name.into(), memory.into())?;
        Ok(())
    }

    /// Imports a new table with the given name.
    pub fn import_table(
        &mut self,
        import_name: ImportName,
        table: parse::Table,
    ) -> Result<(), BuilderError> {
        self.builder
            .resources
            .tables
            .push_imported(import_name.into(), table.into())?;
        Ok(())
    }
}

#[derive(Debug, From)]
pub struct DeclareFunction<'a> {
    builder: &'a mut ModuleBuilder,
}

impl<'a> DeclareFunction<'a> {
    /// Pushes another function declaration to the Wasm module.
    ///
    /// # Note
    ///
    /// Guaranteed to be called once per internal function in the built Wasm module.
    pub fn declare_function(
        &mut self,
        function_type_id: FunctionTypeId,
    ) -> Result<(), BuilderError> {
        self.builder
            .resources
            .function_types
            .push_internal(function_type_id, ())?;
        Ok(())
    }
}

#[derive(Debug, From)]
pub struct DeclareTable<'a> {
    builder: &'a mut ModuleBuilder,
}

impl<'a> DeclareTable<'a> {
    /// Pushes another table declaration to the Wasm module.
    ///
    /// # Note
    ///
    /// Guaranteed to be called once per internal table in the built Wasm module.
    pub fn declare_table(
        &mut self,
        table: parse::Table,
    ) -> Result<(), BuilderError> {
        self.builder
            .resources
            .tables
            .push_internal(table.into(), ())?;
        Ok(())
    }
}

#[derive(Debug, From)]
pub struct DeclareMemory<'a> {
    builder: &'a mut ModuleBuilder,
}

impl<'a> DeclareMemory<'a> {
    /// Pushes another linear memory declaration to the Wasm module.
    ///
    /// # Note
    ///
    /// Guaranteed to be called once per internal linear memory in the built Wasm module.
    pub fn declare_memory(
        &mut self,
        memory: parse::LinearMemory,
    ) -> Result<(), BuilderError> {
        self.builder
            .resources
            .memories
            .push_internal(memory.into(), ())?;
        Ok(())
    }
}

#[derive(Debug, From)]
pub struct DefineGlobal<'a> {
    builder: &'a mut ModuleBuilder,
}

impl<'a> DefineGlobal<'a> {
    /// Pushes another global variable definition to the Wasm module.
    ///
    /// # Note
    ///
    /// Guaranteed to be called once per internal global variable in the built Wasm module.
    pub fn define_global(
        &mut self,
        variable: GlobalVariable,
        init_value: parse::InitializerExpr,
    ) -> Result<(), BuilderError> {
        self.builder
            .resources
            .globals
            .push_internal(variable, init_value)?;
        Ok(())
    }
}

#[derive(Debug, From)]
pub struct DeclareExport<'a> {
    builder: &'a mut ModuleBuilder,
}

impl<'a> DeclareExport<'a> {
    /// Pushes another export declaration to the Wasm module.
    ///
    /// # Note
    ///
    /// Guaranteed to be called once per export declaration in the built Wasm module.
    pub fn declare_export(
        &mut self,
        export: Export,
    ) -> Result<(), BuilderError> {
        let field = export.field();
        match export.item() {
            ExportItem::Function(id) => {
                self.builder.resources.exports.export_function(field, id);
            }
            ExportItem::Table(id) => {
                self.builder.resources.exports.export_table(field, id);
            }
            ExportItem::Memory(id) => {
                self.builder.resources.exports.export_memory(field, id);
            }
            ExportItem::Global(id) => {
                self.builder.resources.exports.export_global(field, id);
            }
        }
        Ok(())
    }
}

#[derive(Debug, From)]
pub struct PushElement<'a> {
    builder: &'a mut ModuleBuilder,
}

impl<'a> PushElement<'a> {
    /// Pushes another element for initialization of a table of the Wasm module.
    ///
    /// # Note
    ///
    /// Guaranteed to be called once per element item in the built Wasm module.
    pub fn push_element(
        &mut self,
        element: parse::Element,
    ) -> Result<(), ParseError> {
        let id = element.table_id();
        let offset = element.offset().clone();
        let items = element.items();
        self.builder
            .resources
            .tables
            .get_mut(id)
            .expect("unexpected missing table for element")
            .shared()
            .elements
            .push_element(offset, items)?;
        Ok(())
    }
}

#[derive(Debug, From)]
pub struct PushData<'a> {
    builder: &'a mut ModuleBuilder,
}

impl<'a> PushData<'a> {
    /// Pushes another element for initialization of a linear memory of the Wasm module.
    ///
    /// # Note
    ///
    /// Guaranteed to be called once per data item in the built Wasm module.
    pub fn push_data(&mut self, data: parse::Data) -> Result<(), ParseError> {
        let id = data.memory_id();
        let offset = data.offset().clone();
        let items = data.init();
        self.builder
            .resources
            .memories
            .get_mut(id)
            .expect("unexpected missing linear memory for data item")
            .shared()
            .data
            .init_region(offset, items)?;
        Ok(())
    }
}

#[derive(Debug, From)]
pub struct DefineFunctionBody<'a> {
    builder: &'a mut ModuleBuilder,
}

impl<'a> DefineFunctionBody<'a> {
    /// Pushes another function body definition to the Wasm module.
    ///
    /// # Note
    ///
    /// Guaranteed to be called once per function body in the built Wasm module.
    pub fn define_function_body(
        &mut self,
        function_body: FunctionBody,
    ) -> Result<(), BuilderError> {
        Ok(())
    }
}
