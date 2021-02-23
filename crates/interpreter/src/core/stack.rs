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

use derive_more::From;
use entity::RawIdx;
use ir::primitive::Value;

/// The stack.
#[derive(Debug, Default)]
pub struct Stack {
    registers: Vec<Register>,
}

impl Stack {
    /// Pushes a `size` new registers onto the stack and returns a pointer to its start.
    pub fn push(&mut self, size: u32) -> Ptr {
        assert!(self.registers.len() <= u32::MAX as usize);
        let len = self.registers.len() as u32;
        self.registers
            .resize_with(len as usize + size as usize, Default::default);
        len.into()
    }

    /// Pops the stack to the state before pushing the registers that formed `ptr`.
    pub fn pop(&mut self, ptr: Ptr) {
        self.registers.truncate(ptr.into_usize());
    }

    /// Initializes the first `n` values of the stack frame starting at `ptr`.
    ///
    /// Returns the number of inputs initialized through this procedure.
    pub fn initialize<I>(&mut self, ptr: Ptr, inputs: I) -> usize
    where
        I: IntoIterator<Item = u64>,
    {
        let mut len_inputs = 0;
        for input in inputs.into_iter() {
            debug_assert!(len_inputs < u32::MAX as usize);
            let input_value =
                Value::from_raw(RawIdx::from_u32(len_inputs as u32));
            self.write_register(ptr + input_value, input);
            len_inputs += 1;
        }
        len_inputs
    }

    /// Writes `new_value` to the register at the given `ptr`.
    pub fn write_register(&mut self, ptr: Ptr, new_value: u64) {
        self.registers[ptr.into_usize()].bits = new_value;
    }

    /// Returns the bits from the register at the given `ptr`.
    pub fn read_register(&self, ptr: Ptr) -> u64 {
        self.registers[ptr.into_usize()].bits
    }
}

use derive_more::Display;

/// A pointer to the start of a frame on the stack.
#[derive(Debug, From, Copy, Clone, Display)]
#[display(fmt = "ptr({})", value)]
pub struct Ptr {
    value: u32,
}

impl core::ops::Add<Value> for Ptr {
    type Output = Ptr;

    fn add(self, value: Value) -> Self::Output {
        Ptr::from(self.value + value.into_raw().into_u32())
    }
}

impl Ptr {
    /// Returns an `usize` representation of the stack pointer.
    pub fn into_usize(self) -> usize {
        self.value as usize
    }
}

/// A single cell or register on the stack.
#[derive(Debug, Default, Copy, Clone)]
pub struct Register {
    bits: u64,
}

impl Register {
    pub fn from_u64(bits: u64) -> Self {
        Self { bits }
    }

    /// Returns the `u64` representation of the register.
    pub fn into_u64(self) -> u64 {
        self.bits
    }
}
