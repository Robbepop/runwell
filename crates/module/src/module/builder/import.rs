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

use super::global::GlobalInit;
use crate::{
    global_var::{Global, GlobalVariable},
    linear_memory::LinearMemoryDecl,
    module::res::ModuleResources,
    primitive::ImportName,
    table::TableDecl,
};
use ir::primitive::{Func, FuncType, Mem, Table};

/// Constructs module imports.
pub struct ModuleImportsBuilder<'a> {
    res: &'a mut ModuleResources,
}

impl<'a> ModuleImportsBuilder<'a> {
    /// Creates a new module imports builder.
    pub(super) fn new(res: &'a mut ModuleResources) -> Self {
        Self { res }
    }

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
