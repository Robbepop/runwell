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

mod error;
mod function;
mod instruction;
mod variable;

#[cfg(test)]
mod tests;

use self::function::state;
pub use self::{
    error::{FunctionBuilderError, VariableAccess},
    function::{Function, FunctionBuilder, FunctionBuilderContext, ValueAssoc},
    instruction::{FunctionInstrBuilder, Instr},
    variable::{Variable, VariableTranslator},
};
