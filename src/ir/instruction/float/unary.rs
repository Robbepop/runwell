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

use crate::ir::{FloatType, Value};
use core::{fmt::Display, marker::PhantomData};

/// The base of all unary floating point number instructions.
///
/// Generic over a concrete unary floating point number operand.
#[derive(Debug, PartialEq, Eq)]
pub struct UnaryFloatInstr<T>
where
    T: UnaryFloatOperand,
{
    ty: FloatType,
    src: Value,
    marker: PhantomData<fn() -> T>,
}

impl<T> Display for UnaryFloatInstr<T>
where
    T: UnaryFloatOperand,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "{} type {}, source {}",
            <T as UnaryFloatOperand>::DISPLAY_REPR,
            self.ty,
            self.src
        )?;
        Ok(())
    }
}

impl<T> UnaryFloatInstr<T>
where
    T: UnaryFloatOperand,
{
    /// Creates a new unary integer instruction of the given type operating on the given value.
    fn new(ty: FloatType, src: Value) -> Self {
        Self {
            ty,
            src,
            marker: Default::default(),
        }
    }

    /// Returns the integer type of the return value.
    fn ty(&self) -> &FloatType {
        &self.ty
    }

    /// Returns the source value of the instruction.
    fn src(&self) -> &Value {
        &self.src
    }
}

mod operands {
    /// Types implementing this trait are unary floating point number instruction operands.
    pub trait UnaryFloatOperand: Sealed {
        /// A string representation for `Display` trait implementations.
        const DISPLAY_REPR: &'static str;
    }
    pub trait Sealed {}

    macro_rules! impl_unary_float_operand {
        ( $( #[$attr:meta] )* struct $name:ident($display_repr:literal); ) => {
            $( #[$attr] )*
            #[derive(Debug, Copy, Clone, PartialEq, Eq)]
            pub enum $name {}

            impl UnaryFloatOperand for $name {
                const DISPLAY_REPR: &'static str = $display_repr;
            }
            impl Sealed for $name {}
        };
    }

    impl_unary_float_operand! {
        /// Unary operand for evaluating the absolute value of a floating point number.
        struct Abs("fabs");
    }
    impl_unary_float_operand! {
        /// Unary operand for negating value of a floating point number.
        struct Neg("fneg");
    }
    impl_unary_float_operand! {
        /// Unary operand for evaluating the square root of a floating point number.
        struct Sqrt("fsqrt");
    }
    impl_unary_float_operand! {
        /// Unary operand for evaluating the ceil of a floating point number.
        struct Ceil("fceil");
    }
    impl_unary_float_operand! {
        /// Unary operand for evaluating the floor of a floating point number.
        struct Floor("ffloor");
    }
    impl_unary_float_operand! {
        /// Unary operand for rounding to nearest integer towards zero of a floating point number.
        struct Truncate("ftrunc");
    }
    impl_unary_float_operand! {
        /// Unary operand for rounding to nearest integer, ties to even, of a floating point number.
        struct Nearest("fnearest");
    }
}
use self::operands::UnaryFloatOperand;

/// Evaluates the absolute value of the floating point number.
pub type FabsInstr = UnaryFloatInstr<operands::Abs>;
/// Negatives the floating point number.
pub type FnegInstr = UnaryFloatInstr<operands::Neg>;
/// Evaluates the square root of the floating point number.
pub type FsqrtInstr = UnaryFloatInstr<operands::Sqrt>;
/// Rounds to ceil for the floating point number.
pub type FceilInstr = UnaryFloatInstr<operands::Ceil>;
/// Rounds to floor for the floating point number.
pub type FfloorInstr = UnaryFloatInstr<operands::Floor>;
/// Truncates the floating point number to ne next smaller integer.
///
/// # Note
///
/// The result remains a floating point number type.
pub type FtruncateInstr = UnaryFloatInstr<operands::Truncate>;
/// Rounds the floating point number to the nearest integer value.
///
/// # Note
///
/// The result remains a floating point number type.
pub type FnearestInstr = UnaryFloatInstr<operands::Nearest>;
