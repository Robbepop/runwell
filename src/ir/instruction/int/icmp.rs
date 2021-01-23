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

use crate::ir::primitive::{IntType, Value};
use core::fmt::Display;
use derive_more::Display;

/// Compares two integers by the associated operand.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CompareIntOp {
    /// Equals operator.
    Eq,
    /// Not equals operator.
    Ne,
    /// Unsigned less-equals operator.
    Ule,
    /// Unsigned less-then operator.
    Ult,
    /// Unsigned greater-equals operator.
    Uge,
    /// Unsigned greater-than operator.
    Ugt,
    /// Signed less-equals operator.
    Sle,
    /// Signed less-then operator.
    Slt,
    /// Signed greater-equals operator.
    Sge,
    /// Signed greater-than operator.
    Sgt,
}

impl CompareIntOp {
    fn prefix(&self) -> &str {
        match self {
            Self::Eq | Self::Ne => "i",
            Self::Ule | Self::Ult | Self::Uge | Self::Ugt => "u",
            Self::Sle | Self::Slt | Self::Sge | Self::Sgt => "s",
        }
    }
}

impl Display for CompareIntOp {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let repr = match self {
            Self::Eq => "eq",
            Self::Ne => "ne",
            Self::Ule => "ule",
            Self::Ult => "ult",
            Self::Uge => "uge",
            Self::Ugt => "ugt",
            Self::Sle => "sle",
            Self::Slt => "slt",
            Self::Sge => "sge",
            Self::Sgt => "sgt",
        };
        write!(f, "{}", repr)?;
        Ok(())
    }
}

/// Instruction to compare two integer values with respect to some comparison operator.
#[derive(Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[display(fmt = "{}cmp {} {} {}", "op.prefix()", ty, lhs, rhs)]
pub struct CompareIntInstr {
    op: CompareIntOp,
    ty: IntType,
    lhs: Value,
    rhs: Value,
}

impl CompareIntInstr {
    /// Creates a new integer comparison instruction.
    pub fn new(op: CompareIntOp, ty: IntType, lhs: Value, rhs: Value) -> Self {
        Self { op, ty, lhs, rhs }
    }

    /// Returns the compare operand of the instruction.
    pub fn op(&self) -> CompareIntOp {
        self.op
    }

    /// Returns the left-hand side value.
    pub fn lhs(&self) -> Value {
        self.lhs
    }

    /// Returns the right-hand side value.
    pub fn rhs(&self) -> Value {
        self.rhs
    }

    /// Returns the integer type of the instruction.
    pub fn ty(&self) -> IntType {
        self.ty
    }

    /// Replaces all values in the instruction using the replacer.
    ///
    /// Returns `true` if a value has been replaced in the instruction.
    ///
    /// # Note
    ///
    /// By contract the replacer returns `true` if replacement happened.
    pub fn replace_value<F>(&mut self, mut replace: F) -> bool
    where
        F: FnMut(&mut Value) -> bool,
    {
        replace(&mut self.lhs) || replace(&mut self.rhs)
    }
}
