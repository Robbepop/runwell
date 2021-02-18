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

use crate::{func_type::FunctionType, module::res::ModuleResources};
use ir::primitive::FuncType;

/// Constructs module function types.
pub struct ModuleTypesBuilder<'a> {
    res: &'a mut ModuleResources,
}

impl<'a> ModuleTypesBuilder<'a> {
    /// Creates a new module types builder.
    pub(super) fn new(res: &'a mut ModuleResources) -> Self {
        Self { res }
    }

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
