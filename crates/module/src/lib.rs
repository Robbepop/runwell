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
mod error;
mod func_type;
mod function;
mod global_var;
mod import_name;
mod init_expr;
mod linear_memory;
mod store;
mod table;

pub use self::{
    builder::ModuleBuilder,
    error::{IrError, IrErrorKind},
    func_type::{FunctionType, FunctionTypeBuilder},
    function::{
        Function,
        FunctionBuilder,
        FunctionBuilderError,
        InstructionBuilder,
        Variable,
    },
    global_var::{Global, GlobalVariable, GlobalVariableEntity},
    import_name::ImportName,
    init_expr::InitExpr,
    linear_memory::{DataSegmentIter, LinearMemoryDecl, LinearMemoryInit},
    store::Store,
    table::{ElementSegmentIter, TableDecl, TableInit},
};

/// A constructed and validated Runwell module.
#[derive(Debug)]
pub struct Module {}

impl Module {
    /// Creates a new module builder.
    pub fn build() -> ModuleBuilder {
        ModuleBuilder::new()
    }
}
