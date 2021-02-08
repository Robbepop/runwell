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

use crate::TranslateError;
use ir::primitive::{Type, Value};
use std::vec::Drain;

/// Stack of values used for the Wasm emulation stack.
#[derive(Debug, Default, PartialEq, Eq)]
pub struct ValueStack {
    stack: Vec<ValueEntry>,
}

/// A Runwell value on the stack and its associated type.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct ValueEntry {
    pub value: Value,
    pub ty: Type,
}

impl ValueStack {
    /// Pushes another value onto the stack.
    pub fn push(&mut self, value: Value, ty: Type) {
        self.stack.push(ValueEntry { value, ty });
    }

    /// Pops a value from the stack or returns an error if not possible.
    fn pop_impl(
        &mut self,
        expected: u32,
        found: u32,
    ) -> Result<ValueEntry, TranslateError> {
        self.stack
            .pop()
            .ok_or(TranslateError::MissingStackValue { expected, found })
    }

    /// Pops the last inserted value from the stack.
    pub fn pop1(&mut self) -> Result<ValueEntry, TranslateError> {
        self.pop_impl(1, 0)
    }

    /// Pops the last two inserted value from the stack.
    ///
    /// Returns the values in reversed order in which they have been popped.
    pub fn pop2(&mut self) -> Result<(ValueEntry, ValueEntry), TranslateError> {
        let rhs = self.pop_impl(2, 0)?;
        let lhs = self.pop_impl(2, 1)?;
        Ok((lhs, rhs))
    }

    /// Pops the last three inserted value from the stack.
    ///
    /// Returns the values in reversed order in which they have been popped.
    pub fn pop3(
        &mut self,
    ) -> Result<(ValueEntry, ValueEntry, ValueEntry), TranslateError> {
        let trd = self.pop_impl(3, 0)?;
        let snd = self.pop_impl(3, 1)?;
        let fst = self.pop_impl(3, 2)?;
        Ok((fst, snd, trd))
    }

    /// Pops the last `n` inserted values from the stack.
    ///
    /// The values are popped in the order in which they have been pushed.
    pub fn pop_n(
        &mut self,
        n: usize,
    ) -> Result<Drain<ValueEntry>, TranslateError> {
        let len_stack = self.stack.len();
        if len_stack < n {
            return Err(TranslateError::MissingStackValue {
                expected: n as u32,
                found: len_stack as u32,
            })
        }
        Ok(self.stack.drain((len_stack - n)..))
    }

    /// Peeks the last `n` inserted values from the stack.
    ///
    /// The values are peeked in the order in which they have been pushed.
    pub fn peek_n(
        &self,
        n: usize,
    ) -> Result<impl Iterator<Item = ValueEntry> + Clone + '_, TranslateError>
    {
        let len_stack = self.stack.len();
        if len_stack < n {
            return Err(TranslateError::MissingStackValue {
                expected: n as u32,
                found: len_stack as u32,
            })
        }
        Ok(self.stack[(len_stack - n)..].iter().copied())
    }

    /// Peeks the last inserted value on the stack.
    pub fn peek1(&self) -> Result<ValueEntry, TranslateError> {
        self.stack
            .last()
            .copied()
            .ok_or(TranslateError::MissingStackValue {
                expected: 1,
                found: 0,
            })
    }
}
