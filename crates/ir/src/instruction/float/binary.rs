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
    primitive::{FloatType, Value},
    VisitValues,
    VisitValuesMut,
};
use core::fmt::Display;

/// Binary floating point instruction operand.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BinaryFloatOp {
    /// Adds two floating point numbers.
    Add,
    /// Subtracts the left-hand side floating point number from the right-hand side.
    Sub,
    /// Multiplies two floating point numbers.
    Mul,
    /// Divides the right-hand side floating point number by the left-hand side.
    Div,
    /// Evaluates the minimum of two floating point numbers.
    Min,
    /// Evaluates the maximum of two floating point numbers.
    Max,
    /// Takes the sign of the right-hand side floating point number
    /// and the exponent as well as the mantissa of the left-hand side
    /// floating point number and returns the result.
    CopySign,
}

impl Display for BinaryFloatOp {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let repr = match self {
            Self::Add => "fadd",
            Self::Sub => "fsub",
            Self::Mul => "fmul",
            Self::Div => "fdiv",
            Self::Min => "fmin",
            Self::Max => "fmax",
            Self::CopySign => "fcopysign",
        };
        write!(f, "{}", repr)?;
        Ok(())
    }
}

/// The base of all binary floating point number instructions.
///
/// Generic over a concrete binary floating point number operand.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct BinaryFloatInstr {
    op: BinaryFloatOp,
    ty: FloatType,
    lhs: Value,
    rhs: Value,
}

impl Display for BinaryFloatInstr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}<{}> {} {}", self.op, self.ty, self.lhs, self.rhs)?;
        Ok(())
    }
}

impl BinaryFloatInstr {
    /// Creates a new binary floating point number instruction.
    pub fn new(
        op: BinaryFloatOp,
        ty: FloatType,
        lhs: Value,
        rhs: Value,
    ) -> Self {
        Self { op, ty, lhs, rhs }
    }

    /// Returns the floating point comparison operand of the instruction.
    pub fn op(&self) -> BinaryFloatOp {
        self.op
    }

    /// Returns the left-hand side value of the compare instruction.
    pub fn lhs(&self) -> Value {
        self.lhs
    }

    /// Returns the right-hand side value of the compare instruction.
    pub fn rhs(&self) -> Value {
        self.rhs
    }

    /// Returns the type of the compare instruction.
    pub fn ty(&self) -> FloatType {
        self.ty
    }
}

impl VisitValues for BinaryFloatInstr {
    fn visit_values<V>(&self, mut visitor: V)
    where
        V: FnMut(Value) -> bool,
    {
        let _ = visitor(self.lhs) && visitor(self.rhs);
    }
}

impl VisitValuesMut for BinaryFloatInstr {
    fn visit_values_mut<V>(&mut self, mut visitor: V)
    where
        V: FnMut(&mut Value) -> bool,
    {
        let _ = visitor(&mut self.lhs) && visitor(&mut self.rhs);
    }
}
