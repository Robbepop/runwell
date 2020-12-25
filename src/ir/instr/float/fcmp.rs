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

use crate::ir::{FloatType, Value};
use core::fmt::Display;
use derive_more::Display;

/// Compares two floating point numbers by the associated operand.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum FcompareOp {
    /// Equals operator.
    Eq,
    /// Not equals operator.
    Ne,
    /// Unsigned less-equals operator.
    Le,
    /// Unsigned less-then operator.
    Lt,
    /// Unsigned greater-equals operator.
    Ge,
    /// Unsigned greater-than operator.
    Gt,
}

impl Display for FcompareOp {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let repr = match self {
            Self::Eq => "eq",
            Self::Ne => "ne",
            Self::Le => "le",
            Self::Lt => "lt",
            Self::Ge => "ge",
            Self::Gt => "gt",
        };
        write!(f, "{}", repr)?;
        Ok(())
    }
}

/// A comparison instruction for comparing floating point number with respect to some operand.
#[derive(Debug, Display, PartialEq, Eq)]
#[display(fmt = "fcmp.{} type {}, lhs {}, rhs {}", op, ty, lhs, rhs)]
pub struct FcompareInstr {
    op: FcompareOp,
    ty: FloatType,
    lhs: Value,
    rhs: Value,
}

impl FcompareInstr {
    /// Creates a new comparison instruction for floating point numbers.
    pub fn new(
        op: FcompareOp,
        ty: FloatType,
        lhs: Value,
        rhs: Value,
    ) -> Self {
        Self { op, ty, lhs, rhs }
    }
}
