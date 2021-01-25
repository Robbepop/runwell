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

use crate::ir::{
    interpreter::{InterpretationContext, InterpretationError},
    primitive::{Const, IntConst, IntType, Value},
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
    Sshlr,
    /// Shifts the bits of the left-hand side integer to the right by the amount of the right-hand side integer value.
    ///
    /// # Note
    ///
    /// The operation is not preserving the sign of the left-hand side integer.
    Ushlr,
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
            Self::Sshlr => "sshlr",
            Self::Ushlr => "ushlr",
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
    pub fn op(&self) -> BinaryIntOp {
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

    /// Evaluates the function given the interpretation context.
    pub fn interpret(
        &self,
        value: Option<Value>,
        ctx: &mut InterpretationContext,
    ) -> Result<(), InterpretationError> {
        let result_value = value.expect("missing value for instruction");
        let lhs_value = ctx.value_results[self.lhs()];
        let rhs_value = ctx.value_results[self.rhs()];
        let lhs_value = match lhs_value {
            Const::Int(int_const) => int_const,
            _ => unreachable!(),
        };
        let rhs_value = match rhs_value {
            Const::Int(int_const) => int_const,
            _ => unreachable!(),
        };
        let result = match self.op {
            BinaryIntOp::Add => {
                match (lhs_value, rhs_value) {
                    (IntConst::I8(lhs), IntConst::I8(rhs)) => {
                        IntConst::I8(lhs.wrapping_add(rhs))
                    }
                    (IntConst::I16(lhs), IntConst::I16(rhs)) => {
                        IntConst::I16(lhs.wrapping_add(rhs))
                    }
                    (IntConst::I32(lhs), IntConst::I32(rhs)) => {
                        IntConst::I32(lhs.wrapping_add(rhs))
                    }
                    (IntConst::I64(lhs), IntConst::I64(rhs)) => {
                        IntConst::I64(lhs.wrapping_add(rhs))
                    }
                    _ => unreachable!(),
                }
            }
            BinaryIntOp::Mul => {
                match (lhs_value, rhs_value) {
                    (IntConst::I8(lhs), IntConst::I8(rhs)) => {
                        IntConst::I8(lhs.wrapping_mul(rhs))
                    }
                    (IntConst::I16(lhs), IntConst::I16(rhs)) => {
                        IntConst::I16(lhs.wrapping_mul(rhs))
                    }
                    (IntConst::I32(lhs), IntConst::I32(rhs)) => {
                        IntConst::I32(lhs.wrapping_mul(rhs))
                    }
                    (IntConst::I64(lhs), IntConst::I64(rhs)) => {
                        IntConst::I64(lhs.wrapping_mul(rhs))
                    }
                    _ => unreachable!(),
                }
            }
            _ => unimplemented!(),
        };
        ctx.value_results.insert(result_value, result.into());
        Ok(())
    }
}

impl Display for BinaryIntInstr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{} {} {} {}", self.op, self.ty, self.lhs, self.rhs)?;
        Ok(())
    }
}
