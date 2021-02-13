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

use crate::{FunctionBuilderError, IrError};
use core::iter::FusedIterator;
use ir::primitive::{Block, Value};
use std::collections::{hash_map::Iter as HashMapIter, HashMap};

/// An incomplete phi instruction.
///
/// This helper type is used only during function body construction.
/// Upon finalization all remaining incomplete phi instructions are
/// converted into proper phi instructions.
#[derive(Debug, Default)]
pub struct IncompletePhi {
    operands: HashMap<Block, Value, ahash::RandomState>,
}

impl IncompletePhi {
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

    /// Returns an iterator over the operands of the incomplete ϕ-instruction.
    pub fn operands(&self) -> Iter {
        Iter {
            iter: self.operands.iter(),
        }
    }

    /// Checks if the incomplete phi instruction is trivial.
    ///
    /// - If trivial the `Value` to which the incomplete phi instruction is
    ///   equivalent is returned.
    /// - If the incomplete phi instruction is yet deemed non-trivial
    ///   `None` is returned.
    ///
    /// # Errors
    ///
    /// If the incomplete phi instruction is unreachable or in the entry block.
    pub fn is_trivial(
        &self,
        phi_value: Value,
    ) -> Result<Option<Value>, IrError> {
        let mut same: Option<Value> = None;
        for (_block, op) in self.operands() {
            if Some(op) == same || op == phi_value {
                // Unique value or self reference.
                continue
            }
            if same.is_some() {
                // The phi merges at least two values: not trivial
                return Ok(None)
            }
            same = Some(op);
        }
        if same.is_none() {
            // The phi is unreachable or in the start block.
            // The paper replaces it with an undefined instruction.
            return Err(FunctionBuilderError::UnreachablePhi {
                value: phi_value,
            })
            .map_err(Into::into)
        }
        let same = same.expect("just asserted that same is Some");
        // Phi was determined to be trivial and can be removed.
        // Insert a default into its phi users to replace the current users with an empty set.
        // Additionally this allows us to iterate over users without borrow checker issues.
        //
        // Remove phi from its own users in case it was using itself.
        Ok(Some(same))
    }
}

/// Iterator over the operands of a ϕ-instruction.
#[derive(Debug)]
pub struct Iter<'a> {
    iter: HashMapIter<'a, Block, Value>,
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

#[cfg(test)]
mod tests {
    use entity::RawIdx;

    use super::*;

    #[test]
    fn is_trivial_works() {
        let op = (0..3)
            .into_iter()
            .map(|raw| {
                let raw = RawIdx::from_u32(raw);
                (Block::from_raw(raw), Value::from_raw(raw))
            })
            .collect::<Vec<_>>();

        // First create a non-trivial phi-instruction.
        let mut non_trivial_phi = IncompletePhi::default();
        non_trivial_phi.append_operand(op[0].0, op[0].1);
        non_trivial_phi.append_operand(op[1].0, op[1].1);
        assert_eq!(non_trivial_phi.is_trivial(op[2].1), Ok(None));

        // Assert triviality of simple trivial phi-instruction.
        let mut trivial_phi_1 = IncompletePhi::default();
        let v = op[0].1;
        trivial_phi_1.append_operand(op[0].0, v);
        trivial_phi_1.append_operand(op[1].0, v);
        assert_eq!(trivial_phi_1.is_trivial(op[2].1), Ok(Some(v)));

        // Assert triviality of trivial phi-instruction that has itself as operand.
        let mut trivial_phi_2 = IncompletePhi::default();
        let v = op[0].1;
        let phi = op[2].1;
        trivial_phi_2.append_operand(op[0].0, v);
        trivial_phi_2.append_operand(op[1].0, v);
        trivial_phi_2.append_operand(op[2].0, phi);
        assert_eq!(trivial_phi_2.is_trivial(phi), Ok(Some(v)));
    }
}
