// Copyright 2019 Robin Freyler
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

mod error;
mod function;
mod global_variable;
mod id;
mod module;
pub mod utils;
mod parser;

pub use self::{
    error::ParseError,
    function::{Function, FunctionBody, FunctionSig},
    global_variable::{
        GlobalVariable,
        GlobalVariableDecl,
        GlobalVariableInitializer,
    },
    id::{
        FunctionId,
        FunctionSigId,
        GlobalVariableId,
        Identifier,
        LinearMemoryId,
        TableId,
    },
    module::Module,
    parser::parse,
};
