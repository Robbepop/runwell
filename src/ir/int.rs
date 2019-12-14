use crate::ir::{
    sealed::Sealed,
    source::{IntSource, Value},
    IntType,
    LocalVar,
};
use derive_more::From;

/// Any integer operation.
#[derive(From)]
pub enum IntOp {
    LeadingZeros(LeadingZerosOp),
    TrailingZeros(TrailingZerosOp),
    Popcount(PopcountOp),
    Add(IntAddOp),
    Mul(IntMulOp),
    Sub(IntSubOp),
    Sdiv(IntSdivOp),
    Udiv(IntUdivOp),
    Srem(IntSremOp),
    Urem(IntUremOp),
    Compare(IntCompareOp),
    Truncate(IntTruncateOp),
    SignExtend(SignExtendOp),
    ZeroExtend(ZeroExtendOp),
}

/// A generic unary integer operation.
pub struct GenericIntUnaryOp<Kind>
where
    Kind: Sealed,
{
    /// The local variable binding to store the result.
    dst: LocalVar,
    /// The source binding or value of the operation.
    src: IntSource,
    /// The integer type of the resulting operation.
    ty: IntType,
    /// The kind of the operation.
    kind: Kind,
}

/// Returns the leading zeros of the integer operand.
pub type LeadingZerosOp = GenericIntUnaryOp<kinds::LeadingZerosOpKind>;

/// Returns the trailing zeros of the integer operand.
pub type TrailingZerosOp = GenericIntUnaryOp<kinds::TrailingZerosOpKind>;

/// Returns the number of ones in the integer operand.
pub type PopcountOp = GenericIntUnaryOp<kinds::PopcountOpKind>;

/// Integer truncate operation.
pub type IntTruncateOp = GenericIntUnaryOp<kinds::IntTruncateKind>;

/// Integer zero-extension operation.
pub type ZeroExtendOp = GenericIntUnaryOp<kinds::ZeroExtendKind>;

/// Integer sign-extension operation.
pub type SignExtendOp = GenericIntUnaryOp<kinds::SignExtendKind>;

pub(super) mod kinds {
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
        IntAddOpKind,
        /// Computes the twos-complement multiplication of two integers.
        IntMulOpKind,
        /// Computes the twos-complement substration of two integers.
        IntSubOpKind,
        /// Computes the signed integer division.
        IntSdivOpKind,
        /// Computes the unsigned integer division.
        IntUdivOpKind,
        /// Computes the signed integer remainder.
        IntSremOpKind,
        /// Computes the unsigned integer remainder.
        IntUremOpKind,
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
        /// Truncates the integer value to a smaller integer type.
        IntTruncateKind,
        /// Zero-extends the integer value to a larger integer type.
        ZeroExtendKind,
        /// Sign-extends the integer value to a larger integer type.
        SignExtendKind,
    );

    /// Compares two integers by the associated operand.
    #[derive(Debug, Copy, Clone, PartialEq, Eq)]
    pub enum IntCompareOpKind {
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
    impl Sealed for IntCompareOpKind {}
}

/// A generic binary integer operation.
pub struct GenericIntBinaryOp<Kind> {
    /// The local variable binding to store the result.
    dst: LocalVar,
    /// The left-hand side integer source.
    lhs: IntSource,
    /// The right-hand side integer source.
    rhs: IntSource,
    /// The resulting integer type of the operation.
    ty: IntType,
    /// The underlying kind of the binary operation.
    kind: Kind,
}

/// A simple integer addition. Stores the result into `dst`.
///
/// # Note
///
/// Since Wasm expects twos-complement integers the operation
/// is the same for signed and unsigned integers.
pub type IntAddOp = GenericIntBinaryOp<kinds::IntAddOpKind>;

/// An integer multiplication. Stores the result into `dst`.
///
/// # Note
///
/// Since Wasm expects twos-complement integers the operation
/// is the same for signed and unsigned integers.
pub type IntMulOp = GenericIntBinaryOp<kinds::IntMulOpKind>;

/// An integer subtraction. Stores the result into `dst`.
///
/// # Note
///
/// Since Wasm expects twos-complement integers the operation
/// is the same for signed and unsigned integers.
pub type IntSubOp = GenericIntBinaryOp<kinds::IntSubOpKind>;

/// A signed integer division. Stores the result into `dst`.
pub type IntSdivOp = GenericIntBinaryOp<kinds::IntSdivOpKind>;

/// An unsigned integer division. Stores the result into `dst`.
pub type IntUdivOp = GenericIntBinaryOp<kinds::IntUdivOpKind>;

/// A signed integer remainder. Stores the result into `dst`.
pub type IntSremOp = GenericIntBinaryOp<kinds::IntSremOpKind>;

/// An unsigned integer remainder. Stores the result into `dst`.
pub type IntUremOp = GenericIntBinaryOp<kinds::IntUremOpKind>;

/// Integer compare operation.
///
/// `dst := lhs op rhs`
pub type IntCompareOp = GenericIntBinaryOp<kinds::IntCompareOpKind>;

/// Bitwise and operation.
pub type AndOp = GenericIntBinaryOp<kinds::AndOpKind>;

/// Bitwise or operation.
pub type OrOp = GenericIntBinaryOp<kinds::OrOpKind>;

/// Bitwise xor operation.
pub type XorOp = GenericIntBinaryOp<kinds::XorOpKind>;

/// Shift-left operation.
pub type ShlOp = GenericIntBinaryOp<kinds::ShlOpKind>;

/// Arithmetic shift-right (a.k.a. signed shift-right) operation.
pub type SshrOp = GenericIntBinaryOp<kinds::SshrOpKind>;

/// Logical shift-right (a.k.a. unsigned shift-right) operation.
pub type UshrOp = GenericIntBinaryOp<kinds::UshrOpKind>;

/// Rotate-left operation.
pub type RotlOp = GenericIntBinaryOp<kinds::RotlOpKind>;

/// Rotate-right operation.
pub type RotrOp = GenericIntBinaryOp<kinds::RotrOpKind>;
