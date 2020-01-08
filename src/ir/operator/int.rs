// Copyright 2019 Robin Freyler
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

//! Integer type operations.

use crate::{
    ir::{operator::DestinationId, ValueId},
    parse::operator::IntType as Type,
};
use derive_more::From;

/// Any integer operation.
#[derive(From, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum IntOp {
    LeadingZeros(LeadingZerosOp),
    TrailingZeros(TrailingZerosOp),
    Popcount(PopcountOp),
    Add(AddOp),
    Mul(MulOp),
    Sub(SubOp),
    Sdiv(SdivOp),
    Udiv(UdivOp),
    Srem(SremOp),
    Urem(UremOp),
    Compare(CompareOp),
    And(AndOp),
    Or(OrOp),
    Xor(XorOp),
    Shl(ShlOp),
    Sshr(SshrOp),
    Ushr(UshrOp),
    Rotl(RotlOp),
    Rotr(RotrOp),
}

mod seal {
    pub trait Sealed {}
}
use self::seal::Sealed;

mod kinds {
    use super::Sealed;

    macro_rules! simple_marker {
        ( $( $(#[$doc:meta])* $name:ident),* $(,)? ) => {
            $(
                $( #[$doc] )*
                #[derive(Debug, Copy, Clone, PartialEq, Eq)]
                pub enum $name {}
                impl Sealed for $name {}
            )*
        }
    }

    simple_marker!(
        /// Computes the number of leading zeros in an integer.
        LeadingZerosOpKind,
        /// Computes the number of trailing zeros in an integer.
        TrailingZerosOpKind,
        /// Computes the number of `1` bits in an integer.
        PopcountOpKind,
        /// Computes the twos-complement addition of two integers.
        AddOpKind,
        /// Computes the twos-complement multiplication of two integers.
        MulOpKind,
        /// Computes the twos-complement substration of two integers.
        SubOpKind,
        /// Computes the signed integer division.
        SdivOpKind,
        /// Computes the unsigned integer division.
        UdivOpKind,
        /// Computes the signed integer remainder.
        SremOpKind,
        /// Computes the unsigned integer remainder.
        UremOpKind,
        /// Computes the bitwise-and between two integers.
        AndOpKind,
        /// Computes the bitwise-or between two integers.
        OrOpKind,
        /// Computes the bitwise-xor between two integers.
        XorOpKind,
        /// Left-shifts the integer.
        ShlOpKind,
        /// Right-shifts the signed integer.
        SshrOpKind,
        /// Right-shifts the unsigned integer.
        UshrOpKind,
        /// Left-rotates the integer.
        RotlOpKind,
        /// Right-rotates the integer.
        RotrOpKind,
    );

    /// Compares two integers by the associated operand.
    #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
    pub enum CompareOpKind {
        /// Equals
        Eq,
        /// Not equals
        Ne,
        /// Unsigned less-equals
        Ule,
        /// Unsigned less-then
        Ult,
        /// Unsigned greater-equals
        Uge,
        /// Unsigned greater-than
        Ugt,
        /// Signed less-equals
        Sle,
        /// Signed less-then
        Slt,
        /// Signed greater-equals
        Sge,
        /// Signed greater-than
        Sgt,
    }
    impl Sealed for CompareOpKind {}
}
pub use self::kinds::CompareOpKind;

/// A generic unary integer operation.
///
/// # Example
///
/// Performs the operation `<op>` on `%2` of type `i32` and stores the
/// result into `%1`.
///
/// ```no_compile
/// %1 <- i32.<op> %2
/// ```
///
/// Where `<op>` is one of
///
/// - `popcnt`
/// - `leadingzeros`
/// - `trailingzeros`
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct GenericUnaryIntOp<Kind>
where
    Kind: Sealed,
{
    /// The source binding or value of the operation.
    src: ValueId,
    /// The integer type of the resulting operation.
    ty: Type,
    /// The kind of the operation.
    kind: Kind,
}

/// Returns the leading zeros of the integer operand.
pub type LeadingZerosOp = GenericUnaryIntOp<kinds::LeadingZerosOpKind>;

/// Returns the trailing zeros of the integer operand.
pub type TrailingZerosOp = GenericUnaryIntOp<kinds::TrailingZerosOpKind>;

/// Returns the number of ones in the integer operand.
pub type PopcountOp = GenericUnaryIntOp<kinds::PopcountOpKind>;

/// A generic binary integer operation.
///
/// # Example
///
/// Performs the operation `<op>` on `%2` and `%3` of type `i32` and stores the
/// result into `%1`.
///
/// ```no_compile
/// %1 <- i32.<op> %2 %3
/// ```
///
/// Where `<op>` is one of
///
/// - `add`: addition
/// - `mul`: multiplication
/// - `sub`: subtraction
/// - `sdiv`: signed-division
/// - `udiv`: unsigned-division
/// - `srem`: signed-remainder
/// - `urem`: unsigned-remainder
/// - `and`: bitwise-and
/// - `or`: bitwise-or
/// - `xor`: bitwise-xor
/// - `shl`: shift-left
/// - `sshr`: signed shift-right
/// - `ushr`: unsigned shift-right
/// - `rotl`: rotate-left
/// - `rotr`: rotate-right
///
/// Or represents a `cmp` (compare) operation:
///
/// Compares `%2` and `%3` of type `i64` using `<op>` relation and stores the
/// result of type `i32` into `%1`.
///
/// ```no_compile
/// %1 <- i64.cmp <op> %2 %3
/// ```
///
/// Where `<op>` is one of the following:
///
/// - `eq`: Equals
/// - `ne`: Not-equals
/// - `ule`: Unsigned less-equals
/// - `ult`: Unsigned less-than
/// - `uge`: Unsigned greater-equals
/// - `ugt`: Unsigned greater-than
/// - `sle`: Signed less-equals
/// - `slt`: Signed less-than
/// - `sge`: Signed greater-equals
/// - `sgt`: Signed greater-than
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct GenericBinaryIntOp<Kind> {
    /// The left-hand side integer source.
    lhs: ValueId,
    /// The right-hand side integer source.
    rhs: ValueId,
    /// The resulting integer type of the operation.
    ty: Type,
    /// The underlying kind of the binary operation.
    kind: Kind,
}

where
{
    }
}

/// A simple integer addition. Stores the result into `dst`.
///
/// # Note
///
/// Since Wasm expects twos-complement integers the operation
/// is the same for signed and unsigned integers.
pub type AddOp = GenericBinaryIntOp<kinds::AddOpKind>;

/// An integer multiplication. Stores the result into `dst`.
///
/// # Note
///
/// Since Wasm expects twos-complement integers the operation
/// is the same for signed and unsigned integers.
pub type MulOp = GenericBinaryIntOp<kinds::MulOpKind>;

/// An integer subtraction. Stores the result into `dst`.
///
/// # Note
///
/// Since Wasm expects twos-complement integers the operation
/// is the same for signed and unsigned integers.
pub type SubOp = GenericBinaryIntOp<kinds::SubOpKind>;

/// A signed integer division. Stores the result into `dst`.
pub type SdivOp = GenericBinaryIntOp<kinds::SdivOpKind>;

/// An unsigned integer division. Stores the result into `dst`.
pub type UdivOp = GenericBinaryIntOp<kinds::UdivOpKind>;

/// A signed integer remainder. Stores the result into `dst`.
pub type SremOp = GenericBinaryIntOp<kinds::SremOpKind>;

/// An unsigned integer remainder. Stores the result into `dst`.
pub type UremOp = GenericBinaryIntOp<kinds::UremOpKind>;

/// Integer compare operation.
///
/// `dst := lhs op rhs`
pub type CompareOp = GenericBinaryIntOp<kinds::CompareOpKind>;

/// Bitwise and operation.
pub type AndOp = GenericBinaryIntOp<kinds::AndOpKind>;

/// Bitwise or operation.
pub type OrOp = GenericBinaryIntOp<kinds::OrOpKind>;

/// Bitwise xor operation.
pub type XorOp = GenericBinaryIntOp<kinds::XorOpKind>;

/// Shift-left operation.
pub type ShlOp = GenericBinaryIntOp<kinds::ShlOpKind>;

/// Arithmetic shift-right (a.k.a. signed shift-right) operation.
pub type SshrOp = GenericBinaryIntOp<kinds::SshrOpKind>;

/// Logical shift-right (a.k.a. unsigned shift-right) operation.
pub type UshrOp = GenericBinaryIntOp<kinds::UshrOpKind>;

/// Rotate-left operation.
pub type RotlOp = GenericBinaryIntOp<kinds::RotlOpKind>;

/// Rotate-right operation.
pub type RotrOp = GenericBinaryIntOp<kinds::RotrOpKind>;
