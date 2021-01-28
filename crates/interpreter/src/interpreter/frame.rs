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

use super::InterpretationError;
use crate::{
    builder::Function,
    primitive::{Block, Value},
};
use core::mem::replace;
use entity::{DefaultComponentVec, RawIdx};

/// The evaluation context for a single function call.
///
/// Stores values required during evaluation of a function.
#[derive(Debug)]
pub struct FunctionFrame {
    /// The registers used by the function evaluation.
    ///
    /// Registers are also used for the return value.
    /// For every return value `i` the `i`-th register is set
    /// to its respective returned value right before the function
    /// returns control back to the caller.
    registers: DefaultComponentVec<Value, u64>,
    /// The index of the currently executed instruction
    /// of the currently executed basic block.
    instruction_counter: usize,
    /// The currently executed basic block.
    ///
    /// # Note
    ///
    /// Must be initialized with the functions entry block.
    current_block: Block,
    /// The last visited block.
    ///
    /// Used to resolve phi instruction operands.
    ///
    /// # Note
    ///
    /// Is initialized as `None` before function evaluation.
    last_block: Option<Block>,
}

impl Default for FunctionFrame {
    fn default() -> Self {
        Self {
            registers: Default::default(),
            current_block: Block::from_raw(RawIdx::from_u32(0)),
            last_block: None,
            instruction_counter: 0,
        }
    }
}

impl FunctionFrame {
    /// Resets the function frame and initializes the first registers to the inputs.
    ///
    /// # Errors
    ///
    /// If too many or too few function inputs have been given.
    pub fn initialize<I>(
        &mut self,
        fun: &Function,
        inputs: I,
    ) -> Result<(), InterpretationError>
    where
        I: IntoIterator<Item = u64>,
    {
        self.reset();
        self.current_block = fun.entry_block();
        let mut len_inputs = 0;
        for input in inputs.into_iter() {
            debug_assert!(len_inputs < u32::MAX as usize);
            let input_value =
                Value::from_raw(RawIdx::from_u32(len_inputs as u32));
            self.write_register(input_value, input);
            len_inputs += 1;
        }
        let given_inputs = len_inputs as usize;
        let required_inputs = fun.inputs().len();
        if given_inputs != required_inputs {
            return Err(InterpretationError::UnmatchingInputValues {
                given_inputs,
                required_inputs,
            })
        }
        Ok(())
    }

    /// Resets the interpretation context so that it can evaluate a new function.
    pub fn reset(&mut self) {
        self.registers.clear();
        self.last_block = None;
        self.instruction_counter = 0;
    }

    /// Switches the currently executed basic block.
    pub fn switch_to_block(&mut self, block: Block) {
        let last_block = replace(&mut self.current_block, block);
        self.last_block = Some(last_block);
        self.instruction_counter = 0;
    }

    /// Writes the given bits into the register for the given value.
    pub fn write_register(&mut self, value: Value, bits: u64) {
        self.registers[value] = bits;
    }

    /// Returns the bits in the register for the given value.
    pub fn read_register(&self, value: Value) -> u64 {
        self.registers[value]
    }

    /// Returns the currently executed basic block.
    pub fn current_block(&self) -> Block {
        self.current_block
    }

    /// Returns the last executed basic block if any.
    pub fn last_block(&self) -> Option<Block> {
        self.last_block
    }

    /// Bumps the instruction counter by one and returns its value before the bump.
    pub fn bump_instruction_counter(&mut self) -> usize {
        let ic = self.instruction_counter;
        self.instruction_counter += 1;
        ic
    }
}
