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

use super::builder::GlobalInit;
use crate::{
    func_type::FunctionType,
    global_var::{Global, GlobalVariable, GlobalVariableEntity},
    linear_memory::{LinearMemoryDecl, LinearMemoryInit},
    primitive::ImportName,
    table::{TableDecl, TableInit},
};
use entity::{ComponentMap, ComponentVec, DefaultComponentVec, PhantomEntityArena};
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

/// Module builder resource to incrementally build up a Runwell module.
#[derive(Debug, Default)]
pub struct ModuleResources {
    /// The module's start function, if any.
    pub(super) start_func: Option<Func>,
    /// Function type entities.
    pub(super) type_entities: PhantomEntityArena<FuncTypeEntity>,
    /// Function entities.
    pub(super) function_entities: PhantomEntityArena<FunctionEntity>,
    /// Global variable entities.
    pub(super) global_entities: PhantomEntityArena<GlobalVariableEntity>,
    /// Linear memory (heap) entities.
    pub(super) memory_entities: PhantomEntityArena<LinearMemoryEntity>,
    /// Table entities.
    pub(super) table_entities: PhantomEntityArena<TableEntity>,

    /// Registered function types.
    pub(super) types: DefaultComponentVec<FuncType, FunctionType>,
    /// Function declarations.
    ///
    /// # Note
    ///
    /// In their basic form they just declare the function type or signature.
    /// Note that function bodies (implementations) are stored elsewhere.
    pub(super) function_decls: ComponentVec<Func, FuncType>,
    /// Stores the import name in case the function is imported.
    ///
    /// # Note
    ///
    /// A function cannot be imported and exported at the same time.
    pub(super) function_import: ComponentMap<Func, ImportName>,
    /// Stores the export name in case the function is exported.
    ///
    /// # Note
    ///
    /// A function cannot be imported and exported at the same time.
    pub(super) function_export: ComponentMap<Func, String>,
    /// Global variable declarations.
    pub(super) global_decls: ComponentVec<Global, GlobalVariable>,
    /// The initializer of a global variable.
    ///
    /// # Note
    ///
    /// Only internal global variables have initializers.
    /// Imported global variables take the initializer externally.
    pub(super) global_inits: ComponentVec<Global, GlobalInit>,
    /// Stores the export name in case the global variable is exported.
    pub(super) global_export: ComponentMap<Global, String>,
    /// Linear memory declarations.
    pub(super) memory_decls: ComponentVec<Mem, LinearMemoryDecl>,
    /// Initializers of the linear memories.
    ///
    /// # Note
    ///
    /// These are the region of bytes that are initialized upon module instantiation time.
    pub(super) memory_inits: DefaultComponentVec<Mem, LinearMemoryInit>,
    /// Stores the import name in case the linear memory is imported.
    ///
    /// # Note
    ///
    /// A linear memory cannot be imported and exported at the same time.
    pub(super) memory_import: ComponentMap<Mem, ImportName>,
    /// Stores the export name in case the linear memory is exported.
    ///
    /// # Note
    ///
    /// A linear memory cannot be imported and exported at the same time.
    pub(super) memory_export: ComponentMap<Mem, String>,
    /// Table declarations.
    pub(super) table_decls: ComponentVec<Table, TableDecl>,
    /// Initializers of the tables.
    ///
    /// # Note
    ///
    /// These are the regions of function pointers that are initialized
    /// upon module instantiation time.
    pub(super) table_inits: DefaultComponentVec<Table, TableInit>,
    /// Stores the import name in case the table is imported.
    ///
    /// # Note
    ///
    /// A table cannot be imported and exported at the same time.
    pub(super) table_import: ComponentMap<Table, ImportName>,
    /// Stores the export name in case the table is exported.
    ///
    /// # Note
    ///
    /// A table cannot be imported and exported at the same time.
    pub(super) table_export: ComponentMap<Table, String>,
}

impl ModuleResources {
    /// Ensures that the given function type exists in the module resources.
    pub(super) fn ensure_func_type_exists(
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

    /// Returns the function type at the given index if any.
    pub fn get_type(&self, func_type: FuncType) -> Option<&FunctionType> {
        if !self.type_entities.contains_key(func_type) {
            return None
        }
        Some(&self.types[func_type])
    }

    /// Returns the function type of the function if the function exists in the module.
    pub fn get_func_type(&self, func: Func) -> Option<&FunctionType> {
        self.function_decls
            .get(func)
            .map(|&func_type| &self.types[func_type])
    }

    /// Returns the function type of the function if the function exists in the module.
    pub fn get_raw_func_type(&self, func: Func) -> Option<FuncType> {
        self.function_decls.get(func).copied()
    }

    /// Shrinks all data structures to fit their minimum space needed.
    ///
    /// This may costly reallocate some of the data structures.
    pub(super) fn shrink_to_fit(&mut self) {
        self.types.shrink_to_fit();
        self.function_decls.shrink_to_fit();
        self.function_import.shrink_to_fit();
        self.function_export.shrink_to_fit();
        self.global_decls.shrink_to_fit();
        self.global_inits.shrink_to_fit();
        self.global_export.shrink_to_fit();
        self.memory_decls.shrink_to_fit();
        self.memory_inits.shrink_to_fit();
        self.memory_import.shrink_to_fit();
        self.memory_export.shrink_to_fit();
        self.table_decls.shrink_to_fit();
        self.table_inits.shrink_to_fit();
        self.table_import.shrink_to_fit();
        self.table_export.shrink_to_fit();
    }
}
