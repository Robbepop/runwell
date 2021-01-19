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

/// Operand for unary integer instructions.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum UnaryIntOp {
    /// Counts the number of leading zero bits in the source integer value.
    IleadingZerosInstr,
    /// Counts the number of trailing zero bits in the source integer value.
    ItrailingZerosInstr,
    /// Counts the number of set `1` bits in the source integer value.
    IpopCountInstr,
}

impl Display for UnaryIntOp {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let repr = match self {
            Self::IleadingZerosInstr => "ileading_zeros",
            Self::ItrailingZerosInstr => "itrailing_zeros",
            Self::IpopCountInstr => "ipopcount",
        };
        write!(f, "{}", repr)?;
        Ok(())
    }
}

/// The base of all unary integer instructions.
///
/// Generic over a concrete unary integer operand.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UnaryIntInstr {
    op: UnaryIntOp,
    ty: IntType,
    src: Value,
}

impl Display for UnaryIntInstr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{} type {}, source {}", self.op, self.ty, self.src)?;
        Ok(())
    }
}

impl UnaryIntInstr {
    /// Creates a new unary integer instruction of the given type operating on the given value.
    fn new(op: UnaryIntOp, ty: IntType, src: Value) -> Self {
        Self { op, ty, src }
    }

    /// Returns the unary operand of the instruction.
    pub fn op(&self) -> UnaryIntOp {
        self.op
    }

    /// Returns the integer type of the return value.
    pub fn ty(&self) -> &IntType {
        &self.ty
    }

    /// Returns the source value of the instruction.
    pub fn src(&self) -> &Value {
        &self.src
    }
}
