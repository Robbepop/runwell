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

use crate::parse::Identifier;

/// A block identifier within a function that allows to jump to.
#[derive(Debug, Copy, Clone)]
pub struct BlockId(usize);

impl Identifier for BlockId {
    /// Returns the underlying `usize` value.
    fn get(self) -> usize {
        self.0
    }
}

/// An SSA value identifier within a function or basic block.
#[derive(Debug, Copy, Clone, PartialOrd, Ord, PartialEq, Eq)]
pub struct ValueId(usize);

impl Identifier for ValueId {
    /// Returns the underlying `usize` value.
    fn get(self) -> usize {
        self.0
    }
}
