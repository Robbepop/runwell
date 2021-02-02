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

use std::collections::HashSet;

use crate::{
    function::Function,
    FunctionType,
    Global,
    GlobalVariable,
    GlobalVariableEntity,
    ImportName,
    InitExpr,
    LinearMemoryDecl,
    LinearMemoryInit,
    TableDecl,
    TableInit,
};
use entity::{ComponentMap, ComponentVec, DefaultComponentVec, EntityArena};
use ir::primitive::{
    Func,
    FuncType,
    FuncTypeEntity,
    FunctionEntity,
    LinearMemoryEntity,
    Mem,
    Table,
    TableEntity,
};

/// A module builder to incrementally build up a Runwell module.
#[derive(Debug)]
pub struct ModuleBuilder {
    /// The last section that has been processed.
    section: Option<ModuleSection>,
    /// The internal resources of the constructed module.
    res: ModuleResources,
    /// The bodies (implementations) of the internal functions.
    bodies: ComponentVec<Func, Function>,
}

/// Module builder resource to incrementally build up a Runwell module.
#[derive(Debug, Default)]
struct ModuleResources {
    /// Function type entities.
    type_entities: EntityArena<FuncTypeEntity>,
    /// Function entities.
    function_entities: EntityArena<FunctionEntity>,
    /// Global variable entities.
    global_entities: EntityArena<GlobalVariableEntity>,
    /// Linear memory (heap) entities.
    memory_entities: EntityArena<LinearMemoryEntity>,
    /// Table entities.
    table_entities: EntityArena<TableEntity>,

    /// Registered function types.
    types: DefaultComponentVec<FuncType, FunctionType>,
    /// Function declarations.
    ///
    /// # Note
    ///
    /// In their basic form they just declare the function type or signature.
    /// Note that function bodies (implementations) are stored elsewhere.
    function_decls: ComponentVec<Func, FuncType>,
    /// Stores the import name in case the function is imported.
    ///
    /// # Note
    ///
    /// A function cannot be imported and exported at the same time.
    function_import: ComponentMap<Func, ImportName>,
    /// Stores the export name in case the function is exported.
    ///
    /// # Note
    ///
    /// A function cannot be imported and exported at the same time.
    function_export: ComponentMap<Func, String>,
    /// Global variable declarations.
    global_decls: ComponentVec<Global, GlobalVariable>,
    /// The initializer of a global variable.
    ///
    /// # Note
    ///
    /// Only internal global variables have initializers.
    /// Imported global variables take the initializer externally.
    global_inits: ComponentVec<Global, GlobalInit>,
    /// Stores the export name in case the global variable is exported.
    global_export: ComponentMap<Global, String>,
    /// Linear memory declarations.
    memory_decls: ComponentVec<Mem, LinearMemoryDecl>,
    /// Initializers of the linear memories.
    ///
    /// # Note
    ///
    /// These are the region of bytes that are initialized upon module instantiation time.
    memory_inits: DefaultComponentVec<Mem, LinearMemoryInit>,
    /// Stores the import name in case the linear memory is imported.
    ///
    /// # Note
    ///
    /// A linear memory cannot be imported and exported at the same time.
    memory_import: ComponentMap<Mem, ImportName>,
    /// Stores the export name in case the linear memory is exported.
    ///
    /// # Note
    ///
    /// A linear memory cannot be imported and exported at the same time.
    memory_export: ComponentMap<Mem, String>,
    /// Table declarations.
    table_decls: ComponentVec<Table, TableDecl>,
    /// Initializers of the tables.
    ///
    /// # Note
    ///
    /// These are the regions of function pointers that are initialized
    /// upon module instantiation time.
    table_inits: DefaultComponentVec<Table, TableInit>,
    /// Stores the import name in case the table is imported.
    ///
    /// # Note
    ///
    /// A table cannot be imported and exported at the same time.
    table_import: ComponentMap<Table, ImportName>,
    /// Stores the export name in case the table is exported.
    ///
    /// # Note
    ///
    /// A table cannot be imported and exported at the same time.
    table_export: ComponentMap<Table, String>,
}

impl ModuleResources {
    /// Ensures that the given function type exists in the module resources.
    fn ensure_func_type_exists(
        &self,
        func_type: FuncType,
    ) -> Result<(), String> {
        if !self.type_entities.contains_key(func_type) {
            return Err(format!(
                "tried to declare or import function with invalid function type: {:?}",
                func_type
            ))
        }
        Ok(())
    }
}

/// A global variable initialization.
///
/// This either represents an imported global variable with its value
/// or an internal global variable with its definition.
#[derive(Debug)]
pub enum GlobalInit {
    Import(ImportName),
    Define(InitExpr),
}

impl ModuleBuilder {
    /// Creates a new module builder.
    pub(crate) fn new() -> Self {
        Self {
            section: None,
            res: Default::default(),
            bodies: Default::default(),
        }
    }

    /// Ensures that the module sections are constructed in the correct order.
    ///
    /// Updates the current module section if in order.
    fn ensure_section_in_order(
        &mut self,
        next: ModuleSection,
    ) -> Result<(), String> {
        let current = self.section.unwrap_or(ModuleSection::Types);
        if current > next {
            return Err(format!(
                "tried to construct module in incorrect order: {:?} followed after {:?}",
                next, current,
            ))
        }
        self.section = Some(next);
        Ok(())
    }

    /// Returns a module types builder.
    pub fn types(&mut self) -> Result<ModuleTypesBuilder, String> {
        self.ensure_section_in_order(ModuleSection::Types)?;
        Ok(ModuleTypesBuilder { res: &mut self.res })
    }

    /// Returns a module imports builder.
    pub fn imports(&mut self) -> Result<ModuleImportsBuilder, String> {
        self.ensure_section_in_order(ModuleSection::Imports)?;
        Ok(ModuleImportsBuilder { res: &mut self.res })
    }

    /// Returns a module function declaration builder.
    pub fn functions(&mut self) -> Result<ModuleFunctionsBuilder, String> {
        self.ensure_section_in_order(ModuleSection::Functions)?;
        Ok(ModuleFunctionsBuilder { res: &mut self.res })
    }

    /// Returns a module table declaration builder.
    pub fn tables(&mut self) -> Result<ModuleTablesBuilder, String> {
        self.ensure_section_in_order(ModuleSection::Tables)?;
        Ok(ModuleTablesBuilder { res: &mut self.res })
    }

    /// Returns a module linear memory declaration builder.
    pub fn memories(&mut self) -> Result<ModuleMemoriesBuilder, String> {
        self.ensure_section_in_order(ModuleSection::Memories)?;
        Ok(ModuleMemoriesBuilder { res: &mut self.res })
    }

    /// Returns a module global variable builder.
    pub fn globals(&mut self) -> Result<ModuleGlobalsBuilder, String> {
        self.ensure_section_in_order(ModuleSection::Globals)?;
        Ok(ModuleGlobalsBuilder { res: &mut self.res })
    }

    /// Returns a module export builder.
    pub fn exports(&mut self) -> Result<ModuleExportsBuilder, String> {
        self.ensure_section_in_order(ModuleSection::Exports)?;
        Ok(ModuleExportsBuilder {
            res: &mut self.res,
            used_names: Default::default(),
        })
    }

    /// Returns a module table elements builder.
    pub fn table_elements(
        &mut self,
    ) -> Result<ModuleTableElementsBuilder, String> {
        self.ensure_section_in_order(ModuleSection::TableElements)?;
        Ok(ModuleTableElementsBuilder { res: &mut self.res })
    }

    /// Returns a module memory data builder.
    pub fn memory_data(&mut self) -> Result<ModuleMemoryDataBuilder, String> {
        self.ensure_section_in_order(ModuleSection::MemoryData)?;
        Ok(ModuleMemoryDataBuilder { res: &mut self.res })
    }

    /// Returns a module function bodies builder.
    pub fn function_bodies(
        &mut self,
    ) -> Result<(ModuleView, ModuleFunctionBodiesBuilder), String> {
        self.ensure_section_in_order(ModuleSection::FunctionBodies)?;
        let Self { res, bodies, .. } = self;
        let res = &*res;
        let module_view = ModuleView { res };
        let builder = ModuleFunctionBodiesBuilder { res, bodies };
        Ok((module_view, builder))
    }
}

/// The Runwell module sections.
///
/// A Runwell module has to be constructed in the order of the
/// module sections listed with their discriminants below.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum ModuleSection {
    Types = 1,
    Imports = 2,
    Functions = 3,
    Tables = 4,
    Memories = 5,
    Globals = 6,
    Exports = 7,
    TableElements = 8,
    FunctionBodies = 9,
    MemoryData = 10,
}

/// Constructs module function types.
pub struct ModuleTypesBuilder<'a> {
    res: &'a mut ModuleResources,
}

impl<'a> ModuleTypesBuilder<'a> {
    /// Reserves space for `additional` function types.
    pub fn reserve(&mut self, additional: u32) {
        self.res.types.reserve_exact(additional);
    }

    /// Pushes a new function type to the module and returns an index to it.
    pub fn push_type(&mut self, func_type: FunctionType) -> FuncType {
        let idx = self.res.type_entities.alloc(Default::default());
        self.res.types[idx] = func_type;
        idx
    }
}

/// Constructs module imports.
pub struct ModuleImportsBuilder<'a> {
    res: &'a mut ModuleResources,
}

impl<'a> ModuleImportsBuilder<'a> {
    /// Registers a function import to the module and returns an index to it.
    pub fn import_function(
        &mut self,
        name: ImportName,
        func_type: FuncType,
    ) -> Result<Func, String> {
        self.res.ensure_func_type_exists(func_type)?;
        let idx = self.res.function_entities.alloc(Default::default());
        self.res.function_decls.insert(idx, func_type);
        self.res.function_import.insert(idx, name);
        Ok(idx)
    }

    /// Registers a linear memory import to the module and returns an index to it.
    pub fn import_memory(
        &mut self,
        name: ImportName,
        decl: LinearMemoryDecl,
    ) -> Mem {
        let idx = self.res.memory_entities.alloc(Default::default());
        self.res.memory_decls.insert(idx, decl);
        self.res.memory_import.insert(idx, name);
        idx
    }

    /// Registers a table import to the module and returns an index to it.
    pub fn import_table(&mut self, name: ImportName, decl: TableDecl) -> Table {
        let idx = self.res.table_entities.alloc(Default::default());
        self.res.table_decls.insert(idx, decl);
        self.res.table_import.insert(idx, name);
        idx
    }

    /// Registers a table import to the module and returns an index to it.
    pub fn import_global(
        &mut self,
        name: ImportName,
        decl: GlobalVariable,
    ) -> Global {
        let idx = self.res.global_entities.alloc(Default::default());
        self.res.global_decls.insert(idx, decl);
        self.res.global_inits.insert(idx, GlobalInit::Import(name));
        idx
    }
}

/// Constructs module function declarations for internally defined functions.
#[derive(Debug)]
pub struct ModuleFunctionsBuilder<'a> {
    res: &'a mut ModuleResources,
}

impl<'a> ModuleFunctionsBuilder<'a> {
    /// Reserves space for `additional` function declarations.
    pub fn reserve(&mut self, additional: u32) {
        self.res.function_decls.reserve_exact(additional);
    }

    /// Pushes a new function declaration to the module and returns an index to it.
    pub fn push_function(
        &mut self,
        func_type: FuncType,
    ) -> Result<Func, String> {
        self.res.ensure_func_type_exists(func_type)?;
        let idx = self.res.function_entities.alloc(Default::default());
        self.res.function_decls.insert(idx, func_type);
        Ok(idx)
    }
}

/// Constructs module table declarations for internally defined tables.
#[derive(Debug)]
pub struct ModuleTablesBuilder<'a> {
    res: &'a mut ModuleResources,
}

impl<'a> ModuleTablesBuilder<'a> {
    /// Reserves space for `additional` table declarations.
    pub fn reserve(&mut self, additional: u32) {
        self.res.table_decls.reserve_exact(additional);
    }

    /// Pushes a new table declaration to the module and returns an index to it.
    pub fn push_table(
        &mut self,
        table_decl: TableDecl,
    ) -> Result<Table, String> {
        let idx = self.res.table_entities.alloc(Default::default());
        self.res.table_decls.insert(idx, table_decl);
        Ok(idx)
    }
}

/// Constructs module memory declarations for internally defined tables.
#[derive(Debug)]
pub struct ModuleMemoriesBuilder<'a> {
    res: &'a mut ModuleResources,
}

impl<'a> ModuleMemoriesBuilder<'a> {
    /// Reserves space for `additional` memory declarations.
    pub fn reserve(&mut self, additional: u32) {
        self.res.memory_decls.reserve_exact(additional);
    }

    /// Pushes a new memory declaration to the module and returns an index to it.
    pub fn push_memory(
        &mut self,
        memory_decl: LinearMemoryDecl,
    ) -> Result<Mem, String> {
        let idx = self.res.memory_entities.alloc(Default::default());
        self.res.memory_decls.insert(idx, memory_decl);
        Ok(idx)
    }
}

/// Constructs internal module global variables.
#[derive(Debug)]
pub struct ModuleGlobalsBuilder<'a> {
    res: &'a mut ModuleResources,
}

impl<'a> ModuleGlobalsBuilder<'a> {
    /// Reserves space for `additional` global variable.
    pub fn reserve(&mut self, additional: u32) {
        self.res.global_decls.reserve_exact(additional);
    }

    /// Pushes a new global variable to the module and returns an index to it.
    pub fn push_global(
        &mut self,
        decl: GlobalVariable,
        init: InitExpr,
    ) -> Result<Global, String> {
        let idx = self.res.global_entities.alloc(Default::default());
        self.res.global_decls.insert(idx, decl);
        self.res.global_inits.insert(idx, GlobalInit::Define(init));
        Ok(idx)
    }
}

/// Constructs module exports.
#[derive(Debug)]
pub struct ModuleExportsBuilder<'a> {
    res: &'a mut ModuleResources,
    /// Used to check for conflicting exported items.
    used_names: HashSet<ExportName>,
}

/// The name and kind of an exported item.
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct ExportName {
    name: String,
    kind: ExportKind,
}

/// The kind of an exported item.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum ExportKind {
    Function,
    Table,
    Memory,
    Global,
}

impl<'a> ModuleExportsBuilder<'a> {
    /// Ensures that there are no conflicting export items.
    fn ensure_conflict_free(
        &mut self,
        kind: ExportKind,
        name: &str,
    ) -> Result<(), String> {
        if self.used_names.contains(&ExportName {
            kind,
            name: name.to_string(),
        }) {
            return Err(format!(
                "encountered conflicting export names: {} for kind {:?}",
                name, kind
            ))
        }
        Ok(())
    }

    /// Pushes a new function export.
    pub fn export_function(
        &mut self,
        idx: Func,
        name: &str,
    ) -> Result<(), String> {
        self.ensure_conflict_free(ExportKind::Function, name)?;
        self.res.function_export.insert(idx, name.to_string());
        Ok(())
    }

    /// Pushes a new table export.
    pub fn export_table(
        &mut self,
        idx: Table,
        name: &str,
    ) -> Result<(), String> {
        self.ensure_conflict_free(ExportKind::Table, name)?;
        self.res.table_export.insert(idx, name.to_string());
        Ok(())
    }

    /// Pushes a new linear memory export.
    pub fn export_memory(
        &mut self,
        idx: Mem,
        name: &str,
    ) -> Result<(), String> {
        self.ensure_conflict_free(ExportKind::Memory, name)?;
        self.res.memory_export.insert(idx, name.to_string());
        Ok(())
    }

    /// Pushes a new global variable export.
    pub fn export_global(
        &mut self,
        idx: Global,
        name: &str,
    ) -> Result<(), String> {
        self.ensure_conflict_free(ExportKind::Global, name)?;
        self.res.global_export.insert(idx, name.to_string());
        Ok(())
    }
}

/// Constructs module table initializers.
#[derive(Debug)]
pub struct ModuleTableElementsBuilder<'a> {
    res: &'a mut ModuleResources,
}

impl<'a> ModuleTableElementsBuilder<'a> {
    /// Pushes a new table initializer to the module.
    pub fn push_element<T>(
        &mut self,
        idx: Table,
        offset: InitExpr,
        funcs: T,
    ) -> Result<(), String>
    where
        T: IntoIterator<Item = Func>,
    {
        if !self.res.table_entities.contains_key(idx) {
            return Err(format!(
                "encountered invalid table index {} to push a table element",
                idx,
            ))
        }
        self.res.table_inits[idx].push_element(offset, funcs);
        Ok(())
    }
}

/// Constructs module linear memory initializers.
#[derive(Debug)]
pub struct ModuleMemoryDataBuilder<'a> {
    res: &'a mut ModuleResources,
}

impl<'a> ModuleMemoryDataBuilder<'a> {
    /// Pushes a new table initializer to the module.
    pub fn push_data<T>(
        &mut self,
        idx: Mem,
        offset: InitExpr,
        bytes: T,
    ) -> Result<(), String>
    where
        T: IntoIterator<Item = u8>,
    {
        if !self.res.memory_entities.contains_key(idx) {
            return Err(format!(
                "encountered invalid memory index {} to push a memory data",
                idx,
            ))
        }
        self.res.memory_inits[idx].push_data(offset, bytes);
        Ok(())
    }
}

/// Allow safe access to a partially constructed module.
///
/// Contains all of a module but the memory data and function bodies.
/// Used to inspect module state upon constructing function bodies.
///
/// Defines a clean API to access the module resources.
/// Can be duplicated to allow for parallel function construction.
#[derive(Debug, Copy, Clone)]
pub struct ModuleView<'a> {
    res: &'a ModuleResources,
}

/// Constructs module function bodies.
#[derive(Debug)]
pub struct ModuleFunctionBodiesBuilder<'a> {
    res: &'a ModuleResources,
    bodies: &'a mut ComponentVec<Func, Function>,
}

impl<'a> ModuleFunctionBodiesBuilder<'a> {
    /// Registers the function body for the given function.
    pub fn push_body(
        &mut self,
        func: Func,
        body: Function,
    ) -> Result<(), String> {
        if !self.res.function_entities.contains_key(func) {
            return Err(format!(
                "tried to register function body for invalid function {:?}",
                func
            ))
        }
        if self.bodies.get(func).is_some() {
            return Err(format!(
                "encountered conflict with function bodies for function {:?}",
                func
            ))
        }
        self.bodies.insert(func, body);
        Ok(())
    }
}
