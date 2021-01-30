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

/// The base of all binary integer instructions.
///
/// Generic over a concrete binary integer operand.
///
/// # Note
///
/// - Both input values as well as the output value of the instruction are
///   equal to the type `ty`.
/// - In case of shift and rotate operands the `lhs` value is the source
///   and the `rhs` value is the shift or rotate amount.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BinaryIntInstr {
    op: BinaryIntOp,
    ty: IntType,
    lhs: Value,
    rhs: Value,
}

/// Binary integer operand codes.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BinaryIntOp {
    /// Evalutes integer addition of two integer values.
    Add,
    /// Subtracts the right-hand side integer from the left-hand side integer.
    Sub,
    /// Evalutes integer multiplication of two integer values.
    Mul,
    /// Divides the right-hand side signed integer from the left-hand side signed integer.
    Sdiv,
    /// Divides the right-hand side unsigned integer from the left-hand side unsigned integer.
    Udiv,
    /// Computes the remainder of the left-hand side signed integer divided by the right-hand side signed integer.
    Srem,
    /// Computes the remainder of the left-hand side unsigned integer divided by the right-hand side unsigned integer.
    Urem,
    /// Computes the bitwise and for two integer value.
    And,
    /// Computes the bitwise or for two integer value.
    Or,
    /// Computes the bitwise xor for two integer value.
    Xor,
    /// Shifts the bits of the left-hand side integer to the left by the amount of the right-hand side integer value.
    Shl,
    /// Shifts the bits of the left-hand side integer to the right by the amount of the right-hand side integer value.
    ///
    /// # Note
    ///
    /// The operation is preserving the sign of the left-hand side integer.
    Sshr,
    /// Shifts the bits of the left-hand side integer to the right by the amount of the right-hand side integer value.
    ///
    /// # Note
    ///
    /// The operation is not preserving the sign of the left-hand side integer.
    Ushr,
    /// Rotates the bits of the left-hand side integer to the left by the amount of the right-hand side integer value.
    Rotl,
    /// Rotates the bits of the left-hand side integer to the right by the amount of the right-hand side integer value.
    Rotr,
}

impl Display for BinaryIntOp {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let repr = match self {
            Self::Add => "iadd",
            Self::Sub => "isub",
            Self::Mul => "imul",
            Self::Sdiv => "sdiv",
            Self::Udiv => "udiv",
            Self::Srem => "srem",
            Self::Urem => "urem",
            Self::And => "iand",
            Self::Or => "ior",
            Self::Xor => "ixor",
            Self::Shl => "ishl",
            Self::Sshr => "sshr",
            Self::Ushr => "ushr",
            Self::Rotl => "irotl",
            Self::Rotr => "irotr",
        };
        write!(f, "{}", repr)?;
        Ok(())
    }
}

impl BinaryIntInstr {
    /// Creates a new binary integer instruction.
    pub fn new(op: BinaryIntOp, ty: IntType, lhs: Value, rhs: Value) -> Self {
        Self { op, ty, lhs, rhs }
    }

    /// Returns the binary operand of the instruction.
    #[inline]
    pub fn op(&self) -> BinaryIntOp {
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

impl ReplaceValue for BinaryIntInstr {
    fn replace_value<F>(&mut self, mut replace: F) -> bool
    where
        F: FnMut(&mut Value) -> bool,
    {
        replace(&mut self.lhs) || replace(&mut self.rhs)
    }
}

impl Display for BinaryIntInstr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{} {} {} {}", self.op, self.ty, self.lhs, self.rhs)?;
        Ok(())
    }
}
