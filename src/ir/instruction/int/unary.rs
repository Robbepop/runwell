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

/// The base of all unary integer instructions.
///
/// Generic over a concrete unary integer operand.
#[derive(Debug, PartialEq, Eq)]
pub struct UnaryIntInstr<T>
where
    T: UnaryIntOperand,
{
    ty: IntType,
    src: Value,
    marker: PhantomData<fn() -> T>,
}

impl<T> Display for UnaryIntInstr<T>
where
    T: UnaryIntOperand,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "{} type {}, source {}",
            <T as UnaryIntOperand>::DISPLAY_REPR,
            self.ty,
            self.src
        )?;
        Ok(())
    }
}

impl<T> UnaryIntInstr<T>
where
    T: UnaryIntOperand,
{
    /// Creates a new unary integer instruction of the given type operating on the given value.
    fn new(ty: IntType, src: Value) -> Self {
        Self {
            ty,
            src,
            marker: Default::default(),
        }
    }

    /// Returns the integer type of the return value.
    fn ty(&self) -> &IntType {
        &self.ty
    }

    /// Returns the source value of the instruction.
    fn src(&self) -> &Value {
        &self.src
    }
}

mod operands {
    /// Types implementing this trait are unary integer instruction operands.
    pub trait UnaryIntOperand: Sealed {
        /// A string representation for `Display` trait implementations.
        const DISPLAY_REPR: &'static str;
    }
    pub trait Sealed {}

    macro_rules! impl_unary_int_operand {
        ( $( #[$attr:meta] )* struct $name:ident($display_repr:literal); ) => {
            $( #[$attr] )*
            #[derive(Debug, Copy, Clone, PartialEq, Eq)]
            pub enum $name {}

            impl UnaryIntOperand for $name {
                const DISPLAY_REPR: &'static str = $display_repr;
            }
            impl Sealed for $name {}
        };
    }

    impl_unary_int_operand! {
        /// Unary operand for counting the leading zeros in an integer.
        struct LeadingZeros("ileading_zeros");
    }

    impl_unary_int_operand! {
        /// Unary operand for counting the trailing zeros in an integer.
        struct TrailingZeros("itrailing_zeros");
    }

    impl_unary_int_operand! {
        /// Unary operand for counting the number of `1` bits in an integer.
        struct PopCount("ipopcount");
    }
}
use self::operands::UnaryIntOperand;

/// Counts the number of leading zero bits in the source integer value.
pub type IleadingZerosInstr = UnaryIntInstr<operands::LeadingZeros>;

/// Counts the number of trailing zero bits in the source integer value.
pub type ItrailingZerosInstr = UnaryIntInstr<operands::TrailingZeros>;

/// Counts the number of set `1` bits in the source integer value.
pub type IpopCountInstr = UnaryIntInstr<operands::PopCount>;
