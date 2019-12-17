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

use wasmparser::Operator;
use core::iter::FromIterator;

/// A Wasm initializer expression.
#[derive(Debug)]
pub struct Initializer<'a> {
    /// The operators of the initializer expression.
    ops: Vec<Operator<'a>>,
}

impl<'a> Initializer<'a> {
    /// Returns the operations of the initializer routine.
    pub fn ops(&self) -> &[Operator<'a>] {
        &self.ops
    }
}

impl<'a> FromIterator<Operator<'a>> for Initializer<'a> {
    fn from_iter<T: IntoIterator<Item = Operator<'a>>>(iter: T) -> Self {
        Self {
            ops: iter.into_iter().collect(),
        }
    }
}
