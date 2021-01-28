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

use crate::ir::primitive::{FloatType, Value};
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
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BinaryFloatInstr {
    op: BinaryFloatOp,
    ty: FloatType,
    lhs: Value,
    rhs: Value,
}

impl Display for BinaryFloatInstr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "{} type {}, lhs {}, rhs {}",
            self.op, self.ty, self.lhs, self.rhs
        )?;
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