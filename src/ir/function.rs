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

use crate::{ir::BasicBlock, maybe_std::prelude::*};

/// A `runwell` IR function.
#[derive(Debug)]
pub struct Function {
    /// The non-empty set of basic blocks that form the operations
    /// performance by the function seen as a whole.
    /// The first basic block (entry block) is special in that it is executed
    /// directly upon executing the function itself.
    /// Also it must not have precedessors which implies
    /// that it cannot contain PHI operations.
    blocks: Vec<BasicBlock>,
}

impl Function {
    /// Creates a new function from the given id, signature id and blocks.
    pub fn new<B>(blocks: B) -> Self
    where
        B: IntoIterator<Item = BasicBlock>,
    {
        Self {
            blocks: blocks.into_iter().collect::<Vec<_>>(),
        }
    }

    /// Returns the entry block of the function.
    pub fn entry_block(&self) -> &BasicBlock {
        // This can never fail since `blocks` is guaranteed to be non-empty.
        &self.blocks[0]
    }
}
