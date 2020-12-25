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

/// The base of all binary integer instructions.
///
/// Generic over a concrete binary integer operand.
#[derive(Debug, PartialEq, Eq)]
pub struct BinaryIntInstr<T>
where
    T: BinaryIntOperand,
{
    ty: IntType,
    lhs: Value,
    rhs: Value,
    marker: PhantomData<fn() -> T>,
}

impl<T> Display for BinaryIntInstr<T>
where
    T: BinaryIntOperand,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "{} type {}, lhs {}, rhs {}",
            <T as BinaryIntOperand>::DISPLAY_REPR,
            self.ty,
            self.lhs,
            self.rhs
        )?;
        Ok(())
    }
}

mod operands {
    /// Types implementing this trait are binary integer instruction operands.
    pub trait BinaryIntOperand: Sealed {
        /// A string representation for `Display` trait implementations.
        const DISPLAY_REPR: &'static str;
        /// Is `true` if the operation is commutative, i.e. identical upon swapping `lhs` and `rhs`.
        const COMMUTATIVE: bool;
    }
    pub trait Sealed {}

    macro_rules! impl_binary_int_operand {
        (
            $( #[$attr:meta] )*
            struct $name:ident {
                commutative: $commutative:literal,
                display_repr: $display_repr:literal
            }
        ) => {
            $( #[$attr] )*
            #[derive(Debug, Copy, Clone, PartialEq, Eq)]
            pub enum $name {}

            impl BinaryIntOperand for $name {
                const DISPLAY_REPR: &'static str = $display_repr;
                const COMMUTATIVE: bool = $commutative;
            }
            impl Sealed for $name {}
        };
    }

    impl_binary_int_operand! {
        /// Binary operand for integer addition.
        struct Add {
            commutative: true,
            display_repr: "iadd"
        }
    }

    impl_binary_int_operand! {
        /// Binary operand for integer substraction.
        struct Sub {
            commutative: false,
            display_repr: "isub"
        }
    }

    impl_binary_int_operand! {
        /// Binary operand for integer multiplication.
        struct Mul {
            commutative: true,
            display_repr: "imul"
        }
    }

    impl_binary_int_operand! {
        /// Binary operand for signed integer division.
        struct Sdiv {
            commutative: false,
            display_repr: "sdiv"
        }
    }

    impl_binary_int_operand! {
        /// Binary operand for unsigned integer division.
        struct Udiv {
            commutative: false,
            display_repr: "udiv"
        }
    }

    impl_binary_int_operand! {
        /// Binary operand for signed integer remainder.
        struct Srem {
            commutative: false,
            display_repr: "srem"
        }
    }

    impl_binary_int_operand! {
        /// Binary operand for unsigned integer remainder.
        struct Urem {
            commutative: false,
            display_repr: "urem"
        }
    }

    impl_binary_int_operand! {
        /// Binary operand for bitwise integer and.
        struct And {
            commutative: true,
            display_repr: "and"
        }
    }

    impl_binary_int_operand! {
        /// Binary operand for bitwise integer or.
        struct Or {
            commutative: true,
            display_repr: "or"
        }
    }

    impl_binary_int_operand! {
        /// Binary operand for bitwise integer xor.
        struct Xor {
            commutative: true,
            display_repr: "xor"
        }
    }
}
use self::operands::BinaryIntOperand;

pub type IaddInstr = BinaryIntInstr<operands::Add>;
pub type IsubInstr = BinaryIntInstr<operands::Sub>;
pub type ImulInstr = BinaryIntInstr<operands::Mul>;
pub type SdivInstr = BinaryIntInstr<operands::Sdiv>;
pub type UdivInstr = BinaryIntInstr<operands::Udiv>;
pub type SremInstr = BinaryIntInstr<operands::Srem>;
pub type UremInstr = BinaryIntInstr<operands::Urem>;
pub type IandInstr = BinaryIntInstr<operands::And>;
pub type IorInstr = BinaryIntInstr<operands::Or>;
pub type IxorInstr = BinaryIntInstr<operands::Xor>;