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

use crate::{module::res::ModuleResources, FunctionBody};
use entity::ComponentVec;
use ir::primitive::{Func, FuncType};

/// Constructs module function declarations for internally defined functions.
#[derive(Debug)]
pub struct ModuleFunctionsBuilder<'a> {
    res: &'a mut ModuleResources,
}

impl<'a> ModuleFunctionsBuilder<'a> {
    /// Creates a new module function builder.
    pub(super) fn new(res: &'a mut ModuleResources) -> Self {
        Self { res }
    }

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
        let idx = self.res.function_entities.alloc_some(1);
        self.res.function_decls.insert(idx, func_type);
        Ok(idx)
    }
}

/// Constructs module function bodies.
#[derive(Debug)]
pub struct ModuleFunctionBodiesBuilder<'a> {
    res: &'a ModuleResources,
    bodies: &'a mut ComponentVec<Func, FunctionBody>,
}

impl<'a> ModuleFunctionBodiesBuilder<'a> {
    /// Creates a new module function body builder.
    pub(super) fn new(
        res: &'a ModuleResources,
        bodies: &'a mut ComponentVec<Func, FunctionBody>,
    ) -> Self {
        Self { res, bodies }
    }

    /// Reserves space for `additional` function bodies.
    pub fn reserve(&mut self, additional: u32) {
        self.bodies.reserve_exact(additional);
    }

    /// Registers the function body for the given function.
    pub fn push_body(
        &mut self,
        func: Func,
        body: FunctionBody,
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
