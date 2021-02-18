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
    linear_memory::LinearMemoryDecl,
    module::res::ModuleResources,
    primitive::InitExpr,
};
use ir::primitive::Mem;

/// Constructs module memory declarations for internally defined tables.
#[derive(Debug)]
pub struct ModuleMemoriesBuilder<'a> {
    res: &'a mut ModuleResources,
}

impl<'a> ModuleMemoriesBuilder<'a> {
    /// Creates a new module linear memory builder.
    pub(super) fn new(res: &'a mut ModuleResources) -> Self {
        Self { res }
    }

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

/// Constructs module linear memory initializers.
#[derive(Debug)]
pub struct ModuleMemoryDataBuilder<'a> {
    res: &'a mut ModuleResources,
}

impl<'a> ModuleMemoryDataBuilder<'a> {
    /// Creates a new module linear memory data builder.
    pub(super) fn new(res: &'a mut ModuleResources) -> Self {
        Self { res }
    }

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
