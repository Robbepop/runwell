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
use ir::primitive::{Block, Edge, Value};
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

    /// Continue execution by using the given edge.
    pub fn continue_along_edge(&mut self, edge: Edge) {
        let function = self.module.get_function(self.frame.func()).unwrap();
        let destination = function.body().edge_destination(edge);
        let args = function.body().edge_args(edge);
        let params = function.body().block_params(destination);
        assert_eq!(args.len(), params.len());
        for (param, arg) in params.iter().copied().zip(args.iter().copied()) {
            let value = self.read_register(arg);
            self.write_register(param, value);
        }
        self.frame.switch_to_block(destination);
    }

    /// Returns the currently executed basic block.
    pub fn current_block(&self) -> Block {
        self.frame.current_block()
    }

    /// Bumps the instruction counter by one and returns its value before the bump.
    pub fn bump_instruction_counter(&mut self) -> usize {
        self.frame.bump_instruction_counter()
    }

    /// Returns the stack pointer of the function frame.
    pub fn stack_pointer(&self) -> Ptr {
        self.frame.stack_pointer()
    }

    /// Clears the scratch buffer.
    ///
    /// Use this before populating the scratch buffer with function call
    /// parameters or return values.
    pub fn clear_scratch(&mut self) {
        self.scratch.clear();
    }

    /// Populates the scratch buffer with another value.
    ///
    /// Use this to temporarily store function call parameters or return values.
    pub fn push_scratch(&mut self, bits: u64) {
        self.scratch.push(Register::from_u64(bits))
    }
}
