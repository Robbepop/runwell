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

use super::control::ControlFlowFrame;
use crate::{Error, TranslateError};
use core::slice;
use ir::primitive::{Type, Value};
use module::ModuleResources;
use std::{iter::FusedIterator, vec::Drain};

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

    /// Extends the value stack by the given iterator of pairs of values and types.
    pub fn extend<T>(&mut self, iter: T)
    where
        T: IntoIterator<Item = (Value, Type)>,
    {
        self.stack.extend(
            iter.into_iter().map(|(value, ty)| ValueEntry { value, ty }),
        )
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
        if n > len_stack {
            return Err(TranslateError::MissingStackValue {
                expected: n as u32,
                found: len_stack as u32,
            })
        }
        Ok(self.stack.drain((len_stack - n)..))
    }

    /// Returns the nth last value from the stack.
    ///
    /// The 0th last value is equal to the last value.
    #[allow(dead_code)]
    pub fn last_n(&self, n: usize) -> Result<ValueEntry, TranslateError> {
        let len_stack = self.stack.len();
        if n >= len_stack {
            return Err(TranslateError::MissingStackValue {
                expected: n as u32,
                found: len_stack as u32,
            })
        }
        Ok(self.stack[len_stack - n - 1])
    }

    /// Peeks the last `n` inserted values from the stack.
    ///
    /// The values are peeked in the order in which they have been pushed.
    pub fn peek_n(&self, n: usize) -> Result<PeekIter, TranslateError> {
        let len_stack = self.stack.len();
        if n > len_stack {
            return Err(TranslateError::MissingStackValue {
                expected: n as u32,
                found: len_stack as u32,
            })
        }
        Ok(PeekIter::new(&self.stack[(len_stack - n)..]))
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

    /// Returns the length of the value stack.
    pub fn len(&self) -> usize {
        self.stack.len()
    }

    /// Returns `true` if the value stack is empty.
    #[allow(dead_code)]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Truncates the value stack to the given length.
    ///
    /// # Errors
    ///
    /// If the given length is greater than the current length of the value stack.
    #[allow(dead_code)]
    pub fn truncate(&mut self, len: usize) -> Result<(), TranslateError> {
        if self.len() < len {
            return Err(TranslateError::InvalidValueStackLength {
                actual_len: self.len(),
                requested_len: len,
            })
        }
        self.stack.truncate(len);
        Ok(())
    }

    /// Pop values from the value stack so that it is left at the state it was
    /// before this control-flow frame.
    pub fn truncate_to_original_size(
        &mut self,
        frame: &ControlFlowFrame,
        res: &ModuleResources,
    ) -> Result<(), Error> {
        // The "If" frame pushes its parameters twice, so they're available to the else block
        // (see also `FuncTranslationState::push_if`).
        // Yet, the original_stack_size member accounts for them only once, so that the else
        // block can see the same number of parameters as the consequent block. As a matter of
        // fact, we need to substract an extra number of parameter values for if blocks.
        let len_dupe_args = if let ControlFlowFrame::If(if_frame) = frame {
            if_frame.block_type.inputs(res).len()
        } else {
            0
        };
        self.truncate(frame.original_stack_size() - len_dupe_args)?;
        Ok(())
    }
}

/// Iterator yielding some amount of the top most stack values.
#[derive(Debug, Clone)]
pub struct PeekIter<'a> {
    iter: slice::Iter<'a, ValueEntry>,
}

impl<'a> PeekIter<'a> {
    /// Creates a new peek iterator.
    fn new(slice: &'a [ValueEntry]) -> Self {
        Self { iter: slice.iter() }
    }

    /// Views the underlying data as a sub-slice of the original data.
    ///
    /// This has the same lifetime as the original slice, and so the iterator
    /// can continue to be used while this exists.
    #[allow(dead_code)]
    pub fn as_slice(&self) -> &'a [ValueEntry] {
        self.iter.as_slice()
    }
}

impl<'a> Iterator for PeekIter<'a> {
    type Item = ValueEntry;

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().copied()
    }
}

impl<'a> DoubleEndedIterator for PeekIter<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back().copied()
    }
}

impl<'a> FusedIterator for PeekIter<'a> {}
impl<'a> ExactSizeIterator for PeekIter<'a> {}
