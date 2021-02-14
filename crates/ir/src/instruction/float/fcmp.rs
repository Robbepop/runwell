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
use derive_more::Display;

/// Compares two floating point numbers by the associated operand.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CompareFloatOp {
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

impl Display for CompareFloatOp {
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
#[derive(Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
#[display(fmt = "fcmp -{} {} {} {}", op, ty, lhs, rhs)]
pub struct CompareFloatInstr {
    op: CompareFloatOp,
    ty: FloatType,
    lhs: Value,
    rhs: Value,
}

impl CompareFloatInstr {
    /// Creates a new comparison instruction for floating point numbers.
    pub fn new(
        op: CompareFloatOp,
        ty: FloatType,
        lhs: Value,
        rhs: Value,
    ) -> Self {
        Self { op, ty, lhs, rhs }
    }

    /// Returns the floating point comparison operand of the instruction.
    pub fn op(&self) -> CompareFloatOp {
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

impl VisitValues for CompareFloatInstr {
    fn visit_values<V>(&self, mut visitor: V)
    where
        V: FnMut(Value) -> bool,
    {
        let _ = visitor(self.lhs) && visitor(self.rhs);
    }
}

impl VisitValuesMut for CompareFloatInstr {
    fn visit_values_mut<V>(&mut self, mut visitor: V)
    where
        V: FnMut(&mut Value) -> bool,
    {
        let _ = visitor(&mut self.lhs) && visitor(&mut self.rhs);
    }
}
