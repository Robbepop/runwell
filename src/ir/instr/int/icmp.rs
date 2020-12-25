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

use crate::ir::{IntType, Value};
use core::fmt::Display;
use derive_more::Display;

/// Compares two integers by the associated operand.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum IntCompareOp {
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

impl Display for IntCompareOp {
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

#[derive(Debug, Display, PartialEq, Eq)]
#[display(fmt = "icmp.{} type {}, lhs {}, rhs {}", op, ty, lhs, rhs)]
pub struct IntCompareInstr {
    op: IntCompareOp,
    ty: IntType,
    lhs: Value,
    rhs: Value,
}

impl IntCompareInstr {
    /// Creates a new integer comparison instruction.
    pub fn new(op: IntCompareOp, ty: IntType, lhs: Value, rhs: Value) -> Self {
        Self { op, ty, lhs, rhs }
    }
}
