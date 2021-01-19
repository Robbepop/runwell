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

use super::{IrError, WasmError};
use crate::ir::primitive::Value;

/// Stack of values used for the Wasm emulation stack.
#[derive(Debug, Default, PartialEq, Eq)]
pub struct ValueStack {
    stack: Vec<Value>,
}

impl ValueStack {
    /// Pushes another value onto the stack.
    pub fn push(&mut self, value: Value) {
        self.stack.push(value);
    }

    /// Pops a value from the stack or returns an error if not possible.
    fn pop_impl(
        &mut self,
        expected: u32,
        found: u32,
    ) -> Result<Value, IrError> {
        self.stack
            .pop()
            .ok_or(WasmError::MissingStackValue { expected, found })
            .map_err(Into::into)
    }

    /// Pops the last inserted value from the stack.
    pub fn pop1(&mut self) -> Result<Value, IrError> {
        self.pop_impl(1, 0)
    }

    /// Pops the last two inserted value from the stack.
    ///
    /// Returns the values in reversed order in which they have been popped.
    pub fn pop2(&mut self) -> Result<(Value, Value), IrError> {
        let rhs = self.pop_impl(2, 0)?;
        let lhs = self.pop_impl(2, 1)?;
        Ok((lhs, rhs))
    }

    /// Pops the last three inserted value from the stack.
    ///
    /// Returns the values in reversed order in which they have been popped.
    pub fn pop3(&mut self) -> Result<(Value, Value, Value), IrError> {
        let trd = self.pop_impl(3, 0)?;
        let snd = self.pop_impl(3, 1)?;
        let fst = self.pop_impl(3, 2)?;
        Ok((fst, snd, trd))
    }

    /// Peeks the last inserted value on the stack.
    pub fn peek1(&self) -> Result<Value, IrError> {
        self.stack
            .last()
            .copied()
            .ok_or(WasmError::MissingStackValue {
                expected: 1,
                found: 0,
            })
            .map_err(Into::into)
    }
}
