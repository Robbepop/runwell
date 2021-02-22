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

/// Unary floating point instruction operand.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum UnaryFloatOp {
    /// Evaluates the absolute value of the floating point number.
    Abs,
    /// Negatives the floating point number.
    Neg,
    /// Evaluates the square root of the floating point number.
    Sqrt,
    /// Rounds to ceil for the floating point number.
    Ceil,
    /// Rounds to floor for the floating point number.
    Floor,
    /// Truncates the floating point number to ne next smaller integer.
    ///
    /// # Note
    ///
    /// The result remains a floating point number type.
    Truncate,
    /// Rounds the floating point number to the nearest integer value.
    ///
    /// # Note
    ///
    /// The result remains a floating point number type.
    Nearest,
}

impl Display for UnaryFloatOp {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let repr = match self {
            Self::Abs => "fabs",
            Self::Neg => "fneg",
            Self::Sqrt => "fsqrt",
            Self::Ceil => "fceil",
            Self::Floor => "ffloor",
            Self::Truncate => "ftrunc",
            Self::Nearest => "fnearest",
        };
        write!(f, "{}", repr)?;
        Ok(())
    }
}

/// The base of all unary floating point number instructions.
///
/// Generic over a concrete unary floating point number operand.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct UnaryFloatInstr {
    op: UnaryFloatOp,
    ty: FloatType,
    src: Value,
}

impl Display for UnaryFloatInstr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}<{}> {}", self.op, self.ty, self.src)?;
        Ok(())
    }
}

impl UnaryFloatInstr {
    /// Creates a new unary integer instruction of the given type operating on the given value.
    pub fn new(op: UnaryFloatOp, ty: FloatType, src: Value) -> Self {
        Self { op, ty, src }
    }

    /// Returns the unary floating point number operand of the instruction.
    pub fn op(&self) -> UnaryFloatOp {
        self.op
    }

    /// Returns the integer type of the return value.
    pub fn ty(&self) -> FloatType {
        self.ty
    }

    /// Returns the source value of the instruction.
    pub fn src(&self) -> Value {
        self.src
    }
}

impl VisitValues for UnaryFloatInstr {
    fn visit_values<V>(&self, mut visitor: V)
    where
        V: FnMut(Value) -> bool,
    {
        visitor(self.src);
    }
}

impl VisitValuesMut for UnaryFloatInstr {
    fn visit_values_mut<V>(&mut self, mut visitor: V)
    where
        V: FnMut(&mut Value) -> bool,
    {
        visitor(&mut self.src);
    }
}
