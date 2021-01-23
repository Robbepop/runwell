// Copyright 2020 Robin Freyler
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

use crate::ir::primitive::{Block, Value};
use core::fmt::Display;
use std::collections::BTreeMap;

/// A ϕ-instruction in the Runwell IR.
#[derive(Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PhiInstr {
    sources: BTreeMap<Block, Value>,
}

impl PhiInstr {
    /// Appends another ϕ-operand to the ϕ-instruction.
    ///
    /// Returns `Some` value if the ϕ-operand already existed for the ϕ-instruction.
    pub fn append_operand(
        &mut self,
        block: Block,
        value: Value,
    ) -> Option<Value> {
        self.sources.insert(block, value)
    }

    /// Creates a new ϕ-instruction from the given ϕ-sources.
    pub fn new<I>(sources: I) -> Self
    where
        I: IntoIterator<Item = (Block, Value)>,
    {
        Self {
            sources: sources.into_iter().collect::<BTreeMap<_, _>>(),
        }
    }
}

impl Display for PhiInstr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "ϕ [")?;
        let mut iter = self.sources.iter();
        if let Some((basic_block, value)) = iter.next() {
            write!(f, " {} -> {}", basic_block, value)?;
            for (basic_block, value) in iter {
                write!(f, ", {} -> {}", basic_block, value)?;
            }
        }
        write!(f, "]")?;
        Ok(())
    }
}
