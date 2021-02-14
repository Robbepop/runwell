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
    VisitValues,
    VisitValuesMut,
};
use core::fmt::Display;

/// The base of all integer shift instructions.
///
/// Generic over a concrete integer shift operand.
///
/// # Note
///
/// - The source and result values are of integer type `ty` whereas
///   the shift amount is always of type `I32`.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct ShiftIntInstr {
    op: ShiftIntOp,
    int_type: IntType,
    source: Value,
    shift_amount: Value,
}

/// Integer shift and rotate operand codes.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ShiftIntOp {
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

impl Display for ShiftIntOp {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let repr = match self {
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

impl ShiftIntInstr {
    /// Creates a new shift or rotate integer instruction.
    pub fn new(
        op: ShiftIntOp,
        int_type: IntType,
        source: Value,
        shift_amount: Value,
    ) -> Self {
        Self {
            op,
            int_type,
            source,
            shift_amount,
        }
    }

    /// Returns the shift operand of the instruction.
    #[inline]
    pub fn op(&self) -> ShiftIntOp {
        self.op
    }

    /// Returns the left-hand side value.
    #[inline]
    pub fn source(&self) -> Value {
        self.source
    }

    /// Returns the right-hand side value.
    #[inline]
    pub fn shift_amount(&self) -> Value {
        self.shift_amount
    }

    /// Returns the integer type of the instruction.
    #[inline]
    pub fn ty(&self) -> IntType {
        self.int_type
    }
}

impl VisitValues for ShiftIntInstr {
    fn visit_values<V>(&self, mut visitor: V)
    where
        V: FnMut(Value) -> bool,
    {
        let _ = visitor(self.source) && visitor(self.shift_amount);
    }
}

impl VisitValuesMut for ShiftIntInstr {
    fn visit_values_mut<V>(&mut self, mut visitor: V)
    where
        V: FnMut(&mut Value) -> bool,
    {
        let _ = visitor(&mut self.source) && visitor(&mut self.shift_amount);
    }
}

impl ReplaceValue for ShiftIntInstr {
    fn replace_value<F>(&mut self, mut replace: F) -> bool
    where
        F: FnMut(&mut Value) -> bool,
    {
        replace(&mut self.source) || replace(&mut self.shift_amount)
    }
}

impl Display for ShiftIntInstr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "{} {} {} {}",
            self.op, self.int_type, self.source, self.shift_amount
        )?;
        Ok(())
    }
}
