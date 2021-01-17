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

use crate::{
    ir::{instruction::Instruction, Instr, Value},
    Index32,
};
use core::ops::{Index, IndexMut};

/// Holds all data about Runwell IR instructions during function construction.
#[derive(Debug, Default)]
pub struct Instructions {
    instrs: Vec<InstructionData>,
}

/// The data for a single Runwell IR instruction.
#[derive(Debug)]
pub struct InstructionData {
    /// The Runwell IR instruction.
    pub instr: Instruction,
    /// The value that is associated with the instruction.
    ///
    /// This is optional since some instructions such as `load` do not have
    /// an associated value since they are technically not in pure SSA form.
    pub value: Option<Value>,
}

impl Instructions {
    /// Creates a new instruction.
    pub fn create_instr<V>(&mut self, value: V, instr: Instruction) -> Instr
    where
        V: Into<Option<Value>>,
    {
        let id = Instr::from_u32(self.instrs.len() as u32);
        let value = value.into();
        self.instrs.push(InstructionData { instr, value });
        id
    }

    /// Returns a shared reference to the basic block at the index if any.
    pub fn get(&self, index: Instr) -> Option<&InstructionData> {
        self.instrs.get(index.into_u32() as usize)
    }

    /// Returns an exclusive reference to the basic block at the index if any.
    pub fn get_mut(&mut self, index: Instr) -> Option<&mut InstructionData> {
        self.instrs.get_mut(index.into_u32() as usize)
    }
}

impl Index<Instr> for Instructions {
    type Output = InstructionData;

    fn index(&self, index: Instr) -> &Self::Output {
        self.get(index).expect("invalid index for instruction")
    }
}

impl IndexMut<Instr> for Instructions {
    fn index_mut(&mut self, index: Instr) -> &mut Self::Output {
        self.get_mut(index).expect("invalid index for instruction")
    }
}
