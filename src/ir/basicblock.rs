// Copyright 2019 Robin Freyler
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
    ir::{Operator, TerminalOp},
    maybe_std::prelude::*,
};

/// A basic block within a function.
///
/// Every basic block has a parent function which is refers to through its ID.
/// They contain the ordered list of operations that they perform wholefully
/// upon being executed and are guaranteed to have an ending terminal operation
/// at the end.
#[derive(Debug)]
pub struct BasicBlock {
    /// The non-empty ordered list of operations
    /// with a terminal operation at the end.
    ops: Vec<Operator>,
}

impl BasicBlock {
    /// Creates a new empty basic block.
    ///
    /// # Note
    ///
    /// This basic block is not valid after construction
    /// since valid basic blocks must have a terminal final
    /// instruction.
    pub fn new() -> Self {
        Self { ops: Vec::new() }
    }

    /// Returns the first operator of the basic block.
    pub fn first_op(&self) -> &Operator {
        self.ops
            .first()
            .expect("basic blocks have at least one operator")
    }

    /// Returns the first operator of the basic block.
    pub fn first_op_mut(&mut self) -> &mut Operator {
        self.ops
            .first_mut()
            .expect("basic blocks have at least one operator")
    }

    /// Returns the last operator of the basic block.
    ///
    /// # Note
    ///
    /// If the basic block is valid the last operator can be assumed to be a
    /// terminal operator.
    pub fn last_op(&self) -> &Operator {
        self.ops
            .last()
            .expect("basic blocks have at least one operator")
    }

    /// Returns the last operator of the basic block.
    ///
    /// # Note
    ///
    /// If the basic block is valid the last operator can be assumed to be a
    /// terminal operator.
    pub fn last_op_mut(&mut self) -> &mut Operator {
        self.ops
            .last_mut()
            .expect("basic blocks have at least one operator")
    }

    /// Pushes an operator to the end of the basic block.
    pub fn push_op<O>(&mut self, op: O)
    where
        O: Into<Operator>,
    {
        self.ops.push(op.into())
    }

    /// Returns an iterator over the operations of the basic block.
    pub fn ops(&self) -> core::slice::Iter<Operator> {
        self.ops.iter()
    }

    /// Returns a mutable iterator over the operations of the basic block.
    pub fn ops_mut(&mut self) -> core::slice::IterMut<Operator> {
        self.ops.iter_mut()
    }

    /// Returns a shared reference to the terminal operation.
    pub fn terminal(&self) -> &TerminalOp {
        let term = self
            .ops
            .last()
            .expect("unexpected empty list of operations in basic block");
        match term {
            Operator::Terminal(terminal) => terminal,
            _ => {
                panic!(
                "unexpected non-terminal operation at the end of a basic block"
            )
            }
        }
    }

    /// Returns an exclusive reference to the terminal operation.
    pub fn terminal_mut(&mut self) -> &mut TerminalOp {
        let term = self
            .ops
            .last_mut()
            .expect("unexpected empty list of operations in basic block");
        match term {
            Operator::Terminal(terminal) => terminal,
            _ => {
                panic!(
                "unexpected non-terminal operation at the end of a basic block"
            )
            }
        }
    }
}
