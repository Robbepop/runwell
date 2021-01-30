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

use crate::{
    primitive::{IntType, Value},
    ReplaceValue,
};
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
#[display(fmt = "icmp {} {} {} {}", ty, op, lhs, rhs)]
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
    #[inline]
    pub fn op(&self) -> CompareIntOp {
        self.op
    }

    /// Returns the left-hand side value.
    #[inline]
    pub fn lhs(&self) -> Value {
        self.lhs
    }

    /// Returns the right-hand side value.
    #[inline]
    pub fn rhs(&self) -> Value {
        self.rhs
    }

    /// Returns the integer type of the instruction.
    #[inline]
    pub fn ty(&self) -> IntType {
        self.ty
    }
}

impl ReplaceValue for CompareIntInstr {
    fn replace_value<F>(&mut self, mut replace: F) -> bool
    where
        F: FnMut(&mut Value) -> bool,
    {
        replace(&mut self.lhs) || replace(&mut self.rhs)
    }
}
