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

use crate::{
    module::res::ModuleResources,
    primitive::InitExpr,
    table::TableDecl,
};
use ir::primitive::{Func, Table};

/// Constructs module table declarations for internally defined tables.
#[derive(Debug)]
pub struct ModuleTablesBuilder<'a> {
    res: &'a mut ModuleResources,
}

impl<'a> ModuleTablesBuilder<'a> {
    /// Creates a new module table builder.
    pub(super) fn new(res: &'a mut ModuleResources) -> Self {
        Self { res }
    }

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

/// Constructs module table initializers.
#[derive(Debug)]
pub struct ModuleTableElementsBuilder<'a> {
    res: &'a mut ModuleResources,
}

impl<'a> ModuleTableElementsBuilder<'a> {
    /// Creates a new module table element builder.
    pub(super) fn new(res: &'a mut ModuleResources) -> Self {
        Self { res }
    }

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
