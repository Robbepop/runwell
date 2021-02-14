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

use crate::{
    primitive::{Block, Value},
    VisitValues,
    VisitValuesMut,
};
use core::{fmt::Display, iter::FusedIterator};
use std::collections::{btree_map::Iter as BTreeMapIter, BTreeMap};

/// A ϕ-instruction in the Runwell IR.
#[derive(Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct PhiInstr {
    operands: BTreeMap<Block, Value>,
}

impl PhiInstr {
    /// Creates a new ϕ-instruction from the given ϕ-sources.
    ///
    /// It is asserted that the given blocks appear in ascending order.
    /// This is important to be able to search through the list of blocks
    /// using fast binary search.
    ///
    /// # Panics
    ///
    /// - If the given blocks are not already sorted.
    pub fn new<I>(sources: I) -> Self
    where
        I: IntoIterator<Item = (Block, Value)>,
    {
        Self {
            operands: sources.into_iter().collect(),
        }
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
    pub fn operands(&self) -> Iter {
        Iter {
            iter: self.operands.iter(),
        }
    }

    /// Returns the operand for the given block if any.
    #[inline]
    pub fn operand_for(&self, block: Block) -> Option<Value> {
        self.operands.get(&block).copied()
    }
}

impl VisitValues for PhiInstr {
    fn visit_values<V>(&self, mut visitor: V)
    where
        V: FnMut(Value) -> bool,
    {
        for value in self.operands.values().copied() {
            if !visitor(value) {
                break
            }
        }
    }
}

impl VisitValuesMut for PhiInstr {
    fn visit_values_mut<V>(&mut self, mut visitor: V)
    where
        V: FnMut(&mut Value) -> bool,
    {
        for value in &mut self.operands.values_mut() {
            if !visitor(value) {
                break
            }
        }
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
        self.iter.next().map(|(block, value)| (*block, *value))
    }
}

impl<'a> FusedIterator for Iter<'a> {}
impl<'a> ExactSizeIterator for Iter<'a> {}

impl Display for PhiInstr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "ϕ [")?;
        let mut iter = self.operands();
        if let Some((block, value)) = iter.next() {
            write!(f, " {} -> {}", block, value)?;
            for (block, value) in iter {
                write!(f, ", {} -> {}", block, value)?;
            }
        }
        write!(f, " ]")?;
        Ok(())
    }
}
