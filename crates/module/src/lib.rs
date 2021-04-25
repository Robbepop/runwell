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

pub mod error;
mod func_body;
mod func_type;
mod function;
mod global_var;
mod import_name;
mod init_expr;
mod linear_memory;
mod module;
pub mod primitive;
mod store;
mod table;

#[doc(inline)]
pub use self::{
    error::Error,
    func_body::FunctionBody,
    module::{Module, ModuleResources},
    store::{GlobalRef, MemoryRef, Mutability, RuntimeValue, Store},
};

/// Module section builder types.
pub mod builder {
    pub use super::{
        func_body::{
            FunctionBuilder,
            InstructionBuilder,
            MatchBranchBuilder,
            MatchSelectInstructionBuilder,
        },
        func_type::FunctionTypeBuilder,
        module::{
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
    };
}

/// Utility and auxiliary types and definitions.
pub mod utils {
    pub use super::{
        func_type::PrimitiveList,
        function::Function,
        store::{Bytes, MemoryView, Pages},
    };
}
