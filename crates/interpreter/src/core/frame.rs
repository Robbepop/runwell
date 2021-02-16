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

use super::stack::Ptr;
use core::mem::replace;
use ir::primitive::{Block, Func};

/// A function's stack frame.
#[derive(Debug)]
pub struct Frame {
    func: Func,
    /// The currently executing basic block.
    current_block: Block,
    /// The last executing basic block of none.
    last_block: Option<Block>,
    /// The currently executing instruction of the currently executing basic block.
    instruction_counter: usize,
    /// The stack pointer on the global stack for the frame.
    stack_pointer: Ptr,
}

impl Frame {
    /// Returns a new function frame.
    pub fn new(func: Func, stack_pointer: Ptr, entry_block: Block) -> Self {
        Self {
            func,
            current_block: entry_block,
            last_block: None,
            instruction_counter: 0,
            stack_pointer,
        }
    }

    /// Returns the function associated to this function frame.
    pub fn func(&self) -> Func {
        self.func
    }

    /// Switches the currently executed basic block.
    pub fn switch_to_block(&mut self, block: Block) {
        let last_block = replace(&mut self.current_block, block);
        self.last_block = Some(last_block);
        self.instruction_counter = 0;
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

    /// Returns the last instruction counter.
    pub fn last_instruction_counter(&mut self) -> usize {
        self.instruction_counter.saturating_sub(1)
    }

    /// Returns the stack pointer of the function frame.
    pub fn stack_pointer(&self) -> Ptr {
        self.stack_pointer
    }
}
