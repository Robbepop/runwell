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
use std::{
    collections::{btree_map::Iter as BTreeMapIter, BTreeMap},
    iter::FusedIterator,
};

/// A ϕ-instruction in the Runwell IR.
#[derive(Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PhiInstr {
    operands: BTreeMap<Block, Value>,
}

impl PhiInstr {
    /// Creates a new ϕ-instruction from the given ϕ-sources.
    pub fn new<I>(sources: I) -> Self
    where
        I: IntoIterator<Item = (Block, Value)>,
    {
        Self {
            operands: sources.into_iter().collect::<BTreeMap<_, _>>(),
        }
    }

    /// Appends another ϕ-operand to the ϕ-instruction.
    ///
    /// Returns `Some` value if the ϕ-operand already existed for the ϕ-instruction.
    pub fn append_operand(
        &mut self,
        block: Block,
        value: Value,
    ) -> Option<Value> {
        self.operands.insert(block, value)
    }

    /// Returns the number of operands of the ϕ-instruction.
    pub fn len(&self) -> usize {
        self.operands.len()
    }

    /// Returns `true` if the ϕ-instruction has no operands.
    pub fn is_empty(&self) -> bool {
        self.operands.is_empty()
    }

    /// Returns an iterator over the operands of the ϕ-instruction.
    pub fn iter(&self) -> Iter {
        Iter {
            iter: self.operands.iter(),
        }
    }

    /// Replaces all values in the instruction using the replacer.
    ///
    /// Returns `true` if a value has been replaced in the instruction.
    ///
    /// # Note
    ///
    /// By contract the replacer returns `true` if replacement happened.
    pub fn replace_value<F>(&mut self, mut replace: F) -> bool
    where
        F: FnMut(&mut Value) -> bool,
    {
        self.operands
            .iter_mut()
            .map(|(_block, op)| replace(op))
            .fold(false, |l, r| l || r)
    }
}

/// Iterator over the operands of a ϕ-instruction.
#[derive(Debug)]
pub struct Iter<'a> {
    iter: BTreeMapIter<'a, Block, Value>,
}

impl<'a> Iterator for Iter<'a> {
    type Item = (Block, Value);

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(block, op)| (*block, *op))
    }
}

impl<'a> FusedIterator for Iter<'a> {}
impl<'a> ExactSizeIterator for Iter<'a> {}

impl Display for PhiInstr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "ϕ [")?;
        let mut iter = self.operands.iter();
        if let Some((basic_block, value)) = iter.next() {
            write!(f, " {} -> {}", basic_block, value)?;
            for (basic_block, value) in iter {
                write!(f, ", {} -> {}", basic_block, value)?;
            }
        }
        write!(f, " ]")?;
        Ok(())
    }
}
