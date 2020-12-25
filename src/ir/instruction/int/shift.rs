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
use core::{fmt::Display, marker::PhantomData};

/// The base of all shift or rotate instructions.
///
/// Generic over a concrete shift or rotate integer operand.
#[derive(Debug, PartialEq, Eq)]
pub struct ShiftInstr<T>
where
    T: ShiftOperand,
{
    ty: IntType,
    src: Value,
    amount: Value,
    marker: PhantomData<fn() -> T>,
}

impl<T> ShiftInstr<T>
where
    T: ShiftOperand,
{
    /// Creates a new shift instruction.
    pub fn new(ty: IntType, src: Value, amount: Value) -> Self {
        Self {
            ty,
            src,
            amount,
            marker: Default::default(),
        }
    }

    /// Returns the integer type of the shift or rotate instruction.
    pub fn ty(&self) -> &IntType {
        &self.ty
    }

    /// Returns the source value of the shift or rotate instruction.
    pub fn src(&self) -> &Value {
        &self.src
    }

    /// Returns the shift or rotate amount value of the shift or rotate instruction.
    pub fn shift_amount(&self) -> &Value {
        &self.amount
    }
}

impl<T> Display for ShiftInstr<T>
where
    T: ShiftOperand,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "{} type {}, src {}, amount {}",
            <T as ShiftOperand>::DISPLAY_REPR,
            self.ty,
            self.src,
            self.amount,
        )?;
        Ok(())
    }
}

mod operands {
    /// Types implementing this trait are shift instruction operands.
    pub trait ShiftOperand: Sealed {
        /// A string representation for `Display` trait implementations.
        const DISPLAY_REPR: &'static str;
    }
    pub trait Sealed {}

    macro_rules! impl_shift_operand {
        (
            $( #[$attr:meta] )*
            struct $name:ident {
                display_repr: $display_repr:literal
            }
        ) => {
            $( #[$attr] )*
            #[derive(Debug, Copy, Clone, PartialEq, Eq)]
            pub enum $name {}

            impl ShiftOperand for $name {
                const DISPLAY_REPR: &'static str = $display_repr;
            }
            impl Sealed for $name {}
        };
    }

    impl_shift_operand! {
        /// Operand for integer shift left.
        ///
        /// The `lhs` operand is the source and the `rhs` operand is the shift amount.
        struct Shl {
            display_repr: "shl"
        }
    }

    impl_shift_operand! {
        /// Operand for integer signed shift right.
        ///
        /// The `lhs` operand is the source and the `rhs` operand is the shift amount.
        struct Sshlr {
            display_repr: "sshr"
        }
    }

    impl_shift_operand! {
        /// Operand for integer unsigned shift right.
        ///
        /// The `lhs` operand is the source and the `rhs` operand is the shift amount.
        struct Ushlr {
            display_repr: "ushr"
        }
    }

    impl_shift_operand! {
        /// Operand for integer rotate left.
        ///
        /// The `lhs` operand is the source and the `rhs` operand is the rotate amount.
        struct Rotl {
            display_repr: "rotl"
        }
    }

    impl_shift_operand! {
        /// Operand for integer rotate right.
        ///
        /// The `lhs` operand is the source and the `rhs` operand is the rotate amount.
        struct Rotr {
            display_repr: "rotr"
        }
    }
}
use self::operands::ShiftOperand;

pub type ShlInstr = ShiftInstr<operands::Shl>;
pub type SshlrInstr = ShiftInstr<operands::Sshlr>;
pub type UshlrInstr = ShiftInstr<operands::Ushlr>;
pub type IrotlInstr = ShiftInstr<operands::Rotl>;
pub type IrotrInstr = ShiftInstr<operands::Rotr>;
