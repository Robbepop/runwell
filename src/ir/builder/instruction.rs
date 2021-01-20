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

use super::{state, FunctionBuilder};
use crate::{
    entity::Idx,
    ir::{instruction::Instruction, IrError},
};

/// The unique index of a basic block entity of the Runwell IR.
pub type Instr = Idx<Instruction>;

#[derive(Debug)]
pub struct FunctionInstrBuilder<'a> {
    builder: &'a mut FunctionBuilder<state::Body>,
}

impl<'a> FunctionInstrBuilder<'a> {
    /// Creates a new function instruction builder.
    pub(super) fn new(builder: &'a mut FunctionBuilder<state::Body>) -> Self {
        Self { builder }
    }

    /// Appends the instruction to the current basic block if possible.
    ///
    /// # Note
    ///
    /// - Flags the basic block as filled if the instruction terminates the basic block.
    /// - Eventually updates the predecessors and successors of basic blocks.
    ///
    /// # Errors
    ///
    /// - If used SSA values do not exist for the function.
    /// - If values do not match required type constraints.
    /// - Upon trying to branch to a basic block that has already been sealed.
    fn append(self, _instr: Instruction) -> Result<(), IrError> {
        todo!()
    }
}
