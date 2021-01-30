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

use crate::{function::Function, primitive::Func};
use entity::EntityArena;

/// Holds all data that is immutable during a function evaluation.
///
/// This includes but is not limited to definitions of functions,
/// linear memories, tables, global variables etc.
#[derive(Debug, Default)]
pub struct Store {
    functions: EntityArena<Function>,
}

impl Store {
    /// Pushes a function to the store and returns its key.
    pub fn push_function(&mut self, function: Function) -> Func {
        self.functions.alloc(function)
    }

    /// Returns a shared reference to the function associated to the given index.
    pub fn get_fn(&self, func: Func) -> &Function {
        &self.functions[func]
    }
}
