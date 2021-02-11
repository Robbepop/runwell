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

#![forbid(unsafe_code)]

mod builder;
mod error;
mod func_body;
mod func_type;
mod function;
mod global_var;
mod import_name;
mod init_expr;
mod linear_memory;
mod table;

pub use self::{
    builder::{ModuleBuilder, ModuleResources},
    error::{IrError, IrErrorKind},
    func_body::{
        FunctionBody,
        FunctionBuilder,
        FunctionBuilderError,
        Instr,
        InstructionBuilder,
        Variable,
    },
    func_type::{FunctionType, FunctionTypeBuilder},
    function::Function,
    global_var::{Global, GlobalVariable, GlobalVariableEntity},
    import_name::ImportName,
    init_expr::InitExpr,
    linear_memory::{DataSegmentIter, LinearMemoryDecl, LinearMemoryInit},
    table::{ElementSegmentIter, TableDecl, TableInit},
};
use entity::ComponentVec;
use ir::primitive::Func;

/// Module section builder types.
pub mod builders {
    pub use super::builder::{
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
    };
}

/// A constructed and validated Runwell module.
#[derive(Debug)]
pub struct Module {
    /// The internal resources of the constructed module.
    res: ModuleResources,
    /// The bodies (implementations) of the internal functions.
    bodies: ComponentVec<Func, FunctionBody>,
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
