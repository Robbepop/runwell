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

use super::{
    frame::Frame,
    stack::{Ptr, Register, Stack},
};
use ir::primitive::{Block, Value};
use module::Module;

/// A temporary activation frame used for instruction interpretation.
#[derive(Debug)]
pub struct ActivationFrame<'a> {
    pub module: &'a Module,
    stack: &'a mut Stack,
    frame: &'a mut Frame,
    scratch: &'a mut Vec<Register>,
}

impl<'a> ActivationFrame<'a> {
    /// Creates a new activation frame.
    pub(super) fn new(
        module: &'a Module,
        stack: &'a mut Stack,
        frame: &'a mut Frame,
        scratch: &'a mut Vec<Register>,
    ) -> Self {
        Self {
            module,
            stack,
            frame,
            scratch,
        }
    }

    /// Writes the given bits into the register for the given value.
    pub fn write_register(&mut self, value: Value, bits: u64) {
        let ptr = self.stack_pointer() + value;
        self.stack.write_register(ptr, bits)
    }

    /// Returns the bits in the register for the given value.
    pub fn read_register(&self, value: Value) -> u64 {
        let ptr = self.stack_pointer() + value;
        self.stack.read_register(ptr)
    }

    /// Switches the currently executed basic block.
    pub fn switch_to_block(&mut self, block: Block) {
        self.frame.switch_to_block(block);
    }

    /// Returns the currently executed basic block.
    pub fn current_block(&self) -> Block {
        self.frame.current_block()
    }

    /// Returns the last executed basic block if any.
    pub fn last_block(&self) -> Option<Block> {
        self.frame.last_block()
    }

    /// Bumps the instruction counter by one and returns its value before the bump.
    pub fn bump_instruction_counter(&mut self) -> usize {
        self.frame.bump_instruction_counter()
    }

    /// Returns the stack pointer of the function frame.
    pub fn stack_pointer(&self) -> Ptr {
        self.frame.stack_pointer()
    }

    pub fn clear_scratch(&mut self) {
        self.scratch.clear();
    }

    pub fn push_scratch(&mut self, bits: u64) {
        self.scratch.push(Register::from_u64(bits))
    }
}
