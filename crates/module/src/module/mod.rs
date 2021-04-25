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

mod builder;
mod instance;
mod res;

pub use self::{
    builder::{
        ExportKind,
        ExportName,
        GlobalInit,
        ModuleBuilder,
        ModuleExportsBuilder,
        ModuleFunctionBodiesBuilder,
        ModuleFunctionsBuilder,
        ModuleGlobalsBuilder,
        ModuleImportsBuilder,
        ModuleMemoriesBuilder,
        ModuleMemoryDataBuilder,
        ModuleTableElementsBuilder,
        ModuleTablesBuilder,
        ModuleTypesBuilder,
    },
    instance::{
        Bytes,
        GlobalError,
        GlobalRef,
        MemoryError,
        MemoryRef,
        MemoryView,
        Mutability,
        Pages,
        RuntimeValue,
        Store,
        StoreError,
        Trap,
        TrapCode,
    },
    res::ModuleResources,
};
use crate::{Function, FunctionBody};
use core::fmt;
use entity::ComponentVec;
use ir::{primitive::Func, Indent};

/// A constructed and validated Runwell module.
#[derive(Debug)]
pub struct Module {
    /// The internal resources of the constructed module.
    pub(crate) res: ModuleResources,
    /// The bodies (implementations) of the internal functions.
    pub(crate) bodies: ComponentVec<Func, FunctionBody>,
}

impl Module {
    /// Creates a new module builder.
    pub fn build() -> ModuleBuilder {
        ModuleBuilder::new()
    }

    /// Returns the function signature and body for the given function index if any.
    pub fn get_function(&self, func: Func) -> Option<Function> {
        self.res.get_func_type(func).map(|func_type| {
            let func_body = &self.bodies[func];
            Function::new(func, func_type, func_body)
        })
    }
}

impl fmt::Display for Module {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "mod {{")?;
        for func in self.res.function_entities.indices() {
            let function = self
                .get_function(func)
                .expect("encountered missing function");
            function.display_with_indent(f, Indent::single())?;
        }
        writeln!(f, "}}")?;
        Ok(())
    }
}
