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

use super::instructions::Instructions;
use crate::{
    ir::{BasicBlockId, FunctionBuilderError, Instr, IrError},
    Index32,
};
use core::ops::{Index, IndexMut};
use std::collections::{hash_set, HashSet};

/// Holds all data about basic blocks during function construction.
#[derive(Debug, Default)]
pub struct BasicBlocks {
    blocks: Vec<BasicBlockData>,
}

impl BasicBlocks {
    /// Creates a new basic block.
    pub fn create_block(&mut self) -> BasicBlockId {
        let id = BasicBlockId::from_u32(self.blocks.len() as u32);
        self.blocks.push(BasicBlockData::default());
        id
    }

    /// Returns a shared reference to the basic block at the index if any.
    pub fn get(&self, index: BasicBlockId) -> Result<&BasicBlockData, IrError> {
        self.blocks
            .get(index.into_u32() as usize)
            .ok_or(FunctionBuilderError::InvalidBasicBlock { block: index })
            .map_err(Into::into)
    }

    /// Returns an exclusive reference to the basic block at the index if any.
    pub fn get_mut(
        &mut self,
        index: BasicBlockId,
    ) -> Result<&mut BasicBlockData, IrError> {
        self.blocks
            .get_mut(index.into_u32() as usize)
            .ok_or(FunctionBuilderError::InvalidBasicBlock { block: index })
            .map_err(Into::into)
    }

    /// Registers the basic block `new_pred` as a predecessor of the basic block `block`.
    ///
    /// # Errors
    ///
    /// - If either `block` or `new_pred` are invalid basic block references.
    /// - If the basic block is already a predecessor.
    /// - If the new predecessor is not filled.
    /// - If this basic block is already sealed.
    pub fn add_predecessor(
        &mut self,
        block: BasicBlockId,
        new_pred: BasicBlockId,
    ) -> Result<(), IrError> {
        if !self.get(new_pred)?.filled {
            return Err(FunctionBuilderError::UnfilledPredecessor {
                unfilled_pred: new_pred,
                block,
            })
            .map_err(Into::into)
        }
        if self.get(block)?.sealed {
            return Err(FunctionBuilderError::PredecessorForSealedBlock {
                sealed_block: block,
                new_pred,
            })
            .map_err(Into::into)
        }
        let preds = self.get_mut(block).map(|data| &mut data.preds)?;
        let exists_already = preds.insert(new_pred);
        if exists_already {
            return Err(FunctionBuilderError::BranchAlreadyExists {
                from: new_pred,
                to: block,
            })
            .map_err(Into::into)
        }
        Ok(())
    }
}

impl Index<BasicBlockId> for BasicBlocks {
    type Output = BasicBlockData;

    fn index(&self, index: BasicBlockId) -> &Self::Output {
        self.get(index).expect("invalid index for basic block")
    }
}

impl IndexMut<BasicBlockId> for BasicBlocks {
    fn index_mut(&mut self, index: BasicBlockId) -> &mut Self::Output {
        self.get_mut(index).expect("invalid index for basic block")
    }
}

/// All data that is necessary to store for each basic block during function construction.
#[derive(Debug, Default)]
pub struct BasicBlockData {
    /// The direct predecessor basic blocks of the basic block.
    preds: HashSet<BasicBlockId>,
    /// All instructions of the basic blocks in the order in which they appear in the basic block.
    ///
    /// The same instruction technically can appear multiple times in the same basic block for
    /// example an instruction that has global side effects such as manipulating the linear memory.
    insts: Vec<Instr>,
    /// A filled basic block knows all of its instructions.
    pub filled: bool,
    /// A sealed basic block knows all of its predecessors.
    pub sealed: bool,
}

impl BasicBlockData {
    /// Appends the instruction to the basic block.
    pub fn append(&mut self, instr: Instr) {
        self.insts.push(instr);
    }

    /// Returns an iterator over the predecessors of the basic block.
    ///
    /// # Note
    ///
    /// The predecessors are yielded with no particular order.
    pub fn preds(&self) -> hash_set::Iter<BasicBlockId> {
        self.preds.iter()
    }

    /// Returns the last instruction of the basic block.
    pub fn last_instr(&self) -> Option<Instr> {
        self.insts.last().copied()
    }

    /// Returns `true` if the basic block has been filled.
    ///
    /// A basic block is filled if it has a terminator instruction.
    /// An empty basic block is never filled.
    pub fn is_filled(&self, instructions: &Instructions) -> bool {
        self.last_instr()
            .map(|instr| instructions[instr].instr.is_terminal())
            .unwrap_or(false)
    }

    /// Returns the number of instruction in the basic block.
    pub fn len(&self) -> usize {
        self.insts.len()
    }

    /// Returns `true` if the basic block is empty.
    pub fn is_empty(&self) -> bool {
        self.insts.is_empty()
    }
}
