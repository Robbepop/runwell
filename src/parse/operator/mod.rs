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

//! Parsed Wasm operators.
//!
//! This module contains the `runwell` Wasm operators.
//! They are very similar to their original Wasm operators,
//! provide the same semantics, but in a more compact fashion.
//!
//! Does not contain Wasm operators that are unsupported in the `runwell` JIT.

mod convert;
mod display;
mod utils;

use crate::parse::{
    FunctionId,
    FunctionSigId,
    GlobalVariableId,
    LinearMemoryId,
    ParseError,
    TableId,
};
use derive_more::From;
use wasmparser::TypeOrFuncType;

pub use self::utils::{
    ExtIntType,
    IntType,
    LocalVariableId,
    LocalVariableIdGen,
    MemoryImmediate,
};

/// A Wasm block operator.
#[derive(Debug)]
pub struct BlockOp {
    /// The type of the block.
    ty: TypeOrFuncType,
}

/// A Wasm loop operator.
#[derive(Debug)]
pub struct LoopOp {
    /// The type of the loop.
    ty: TypeOrFuncType,
}

/// A Wasm if-then-else operator.
#[derive(Debug)]
pub struct IfOp {
    /// The type of the if-then-else.
    ty: TypeOrFuncType,
}

/// A Wasm unconditional branch operator.
#[derive(Debug)]
pub struct BrOp {
    /// The relative branching depth.
    pub relative_depth: usize,
}

/// A Wasm branch-if operator.
#[derive(Debug)]
pub struct BrIfOp {
    /// The relative branching depth.
    pub relative_depth: usize,
}

/// A Wasm branch-table (a.k.a. switch) operator.
#[derive(Debug)]
pub struct BrTableOp {
    /// The relative branching depths.
    ///
    /// Does not contain the default branching depth.
    relative_depths: Vec<usize>,
    /// The default branching depth.
    pub default: usize,
}

/// Calls the function with the given `id`.
#[derive(Debug)]
pub struct CallOp {
    /// The called function `id`.
    pub id: FunctionId,
}

/// Calls the function indirectly given the table `id` and the
/// `offset` into the table.
#[derive(Debug)]
pub struct CallIndirectOp {
    /// The table where the called function pointers are stored.
    pub table_id: TableId,
    /// The offset into the indirect call table.
    pub fn_sig_id: FunctionSigId,
}

/// Gets the identified local variable.
#[derive(Debug)]
pub struct LocalGetOp {
    /// The local variable identifier.
    pub id: LocalVariableId,
}

/// Sets the identified local variable.
#[derive(Debug)]
pub struct LocalSetOp {
    /// The local variable identifier.
    pub id: LocalVariableId,
}

/// Sets and returns back the value of the identified local variable.
#[derive(Debug)]
pub struct LocalTeeOp {
    /// The local variable identifier.
    pub id: LocalVariableId,
}

/// Gets the identified global variable.
#[derive(Debug)]
pub struct GlobalGetOp {
    /// The global variable identifier.
    pub id: GlobalVariableId,
}

/// Sets the identified global variable.
#[derive(Debug)]
pub struct GlobalSetOp {
    /// The global variable identifier.
    pub id: GlobalVariableId,
}

/// A Wasm store operation.
///
/// # Note
///
/// - This operation unifies all the different Wasm `store` operations.
/// - The `conversion` field stores the kind of conversion if any.
#[derive(Debug)]
pub struct LoadOp {
    /// The memory parameter.
    pub memarg: MemoryImmediate,
    /// The kind of the load conversion if any.
    pub conversion: LoadConversion,
}

impl LoadOp {
    /// Creates a simple load operation without conversion.
    fn simple(memarg: MemoryImmediate, ty: IntType) -> Self {
        Self {
            memarg,
            conversion: LoadConversion::NoConversion { ty },
        }
    }

    /// Creates a coupled load and zero-extend operation.
    ///
    /// # Errors
    ///
    /// If the width of the result type is equal to or greater
    /// than the width of the source type.
    fn load_zext(
        memarg: MemoryImmediate,
        result_ty: IntType,
        source_ty: ExtIntType,
    ) -> Result<Self, ParseError> {
        if !source_ty.is_extendable_to(result_ty) {
            return Err(ParseError::ExtensionToSmallerInt)
        }
        Ok(Self {
            memarg,
            conversion: LoadConversion::ZeroExt {
                result_ty,
                source_ty,
            },
        })
    }

    /// Creates a coupled load and sign-extend operation.
    ///
    /// # Errors
    ///
    /// If the width of the result type is equal to or greater
    /// than the width of the source type.
    fn load_sext(
        memarg: MemoryImmediate,
        result_ty: IntType,
        source_ty: ExtIntType,
    ) -> Result<Self, ParseError> {
        if !source_ty.is_extendable_to(result_ty) {
            return Err(ParseError::ExtensionToSmallerInt)
        }
        Ok(Self {
            memarg,
            conversion: LoadConversion::SignExt {
                result_ty,
                source_ty,
            },
        })
    }
}

/// The kind of the load conversion.
#[derive(Debug)]
pub enum LoadConversion {
    /// No conversion is taking place.
    ///
    /// The operation simply load the integer with type `ty`.
    NoConversion { ty: IntType },
    /// Sign-extend conversion is taking place.
    SignExt {
        /// The resulting integer type after the load operation.
        result_ty: IntType,
        /// The integer type of the loaded value.
        source_ty: ExtIntType,
    },
    /// Sign-extend conversion is taking place.
    ZeroExt {
        /// The resulting integer type after the load operation.
        result_ty: IntType,
        /// The integer type of the loaded value.
        source_ty: ExtIntType,
    },
}

/// A Wasm store operation.
///
/// # Note
///
/// - This operation unifies all the different Wasm `store` operations.
/// - If `src_ty` and `dst_ty` are equal there is no conversion.
#[derive(Debug)]
pub struct StoreOp {
    /// The memory parameter.
    pub memarg: MemoryImmediate,
    /// The source type of the stored value.
    ///
    /// This is the type before the eventual truncation.
    pub src_ty: IntType,
    /// The dstination type of the stored value.
    ///
    /// This is the type after the eventual truncation.
    pub dst_ty: ExtIntType,
}

impl StoreOp {
    /// Creates a simple store operation without conversion.
    fn simple(memarg: MemoryImmediate, ty: IntType) -> Self {
        Self {
            memarg,
            src_ty: ty,
            dst_ty: ty.into(),
        }
    }

    /// Returns `true` if the load operation implies a conversion.
    pub fn has_conversion(&self) -> bool {
        self.src_ty.width() != self.dst_ty.width()
    }

    /// Creates a coupled store and truncate operation.
    ///
    /// # Errors
    ///
    /// If the width of the source type is equal to or less than
    /// the width of the destination type.
    fn store_truncate(
        memarg: MemoryImmediate,
        src_ty: IntType,
        dst_ty: ExtIntType,
    ) -> Result<Self, ParseError> {
        if !src_ty.is_truncatable_to(dst_ty) {
            return Err(ParseError::TruncationToBiggerInt)
        }
        Ok(Self {
            memarg,
            src_ty,
            dst_ty,
        })
    }
}

/// An integer constant value.
#[derive(Debug)]
pub enum ConstOp {
    I32(i32),
    I64(i64),
}

/// An integer comparison.
#[derive(Debug)]
pub struct IntCmpOp {
    /// The kind of the integer comparison.
    pub kind: IntCmpOpKind,
    /// The expected input integer types.
    ///
    /// # Dev Note (TODO)
    ///
    /// We might be able to throw away `ty` because in Wasm
    /// a comparison operation is always performed on a `i32`.
    pub ty: IntType,
}

impl IntCmpOp {
    /// Creates a new integer compare operator.
    fn new(ty: IntType, kind: IntCmpOpKind) -> Self {
        Self { kind, ty }
    }
}

/// The kind of the integer comparison.
#[derive(Debug)]
pub enum IntCmpOpKind {
    /// Equality to zero (0)
    Eqz,
    /// Equality
    Eq,
    /// Not-equality
    Ne,
    /// Less-equals (unsigned)
    Ule,
    /// Less-than (unsigned)
    Ult,
    /// Greater-equals (unsigned)
    Uge,
    /// Greater-than (unsigned)
    Ugt,
    /// Less-equals (signed)
    Sle,
    /// Less-than (signed)
    Slt,
    /// Greater-equals (signed)
    Sge,
    /// Greater-than (signed)
    Sgt,
}

macro_rules! gen_simple_int_op {
    (
        $(
            $( #[$docs:meta] )*
            struct $name:ident;
        )*
    ) => {
        $(
            $( #[$docs] )*
            #[derive(Debug)]
            pub struct $name {
                /// The integer type of the operation.
                ///
                /// This is the type that this operation expects its inputs
                /// to be in as well as the type that it itself outputs.
                pub ty: IntType,
            }

            impl $name {
                /// Creates a new operator from the given type.
                fn new(ty: IntType) -> Self {
                    Self { ty }
                }
            }
        )*
    }
}
gen_simple_int_op! {
    /// Count leading zeros of an integer.
    struct CountLeadingZerosOp;
    /// Count trailing zeros of an integer.
    struct CountTrailingZerosOp;
    /// Counts the number of `1` bits in the integer.
    struct PopcountOp;
    /// Integer addition.
    struct AddOp;
    /// Integer subtraction.
    struct SubOp;
    /// Integer multiplication.
    struct MulOp;
    /// Signed integer division.
    struct SdivOp;
    /// Unsigned integer division.
    struct UdivOp;
    /// Signed integer remainder.
    struct SremOp;
    /// Unsigned integer remainder.
    struct UremOp;
    /// Bitwise-and
    struct AndOp;
    /// Bitwise-or
    struct OrOp;
    /// Bitwise-xor
    struct XorOp;
    /// Shift-left
    struct ShlOp;
    /// Signed shift-right propagating sign bit.
    struct SshrOp;
    /// Unsigned shift-right propagating zeros.
    struct UshrOp;
    /// Rotate-left
    struct RotLeftOp;
    /// Rotate-right
    struct RotRightOp;
}

/// Integer truncate operation.
#[derive(Debug)]
pub struct TruncateOp {
    /// The resulting integer type after the truncation.
    pub result_ty: IntType,
    /// The input integer type before the truncation.
    pub source_ty: IntType,
}

impl TruncateOp {
    /// Creates a new truncate operation.
    ///
    /// # Errors
    ///
    /// If the operation would truncate the source type to a bigger width.
    fn new(result_ty: IntType, source_ty: IntType) -> Result<Self, ParseError> {
        if !source_ty.is_truncatable_to(result_ty.into()) {
            return Err(ParseError::TruncationToBiggerInt)
        }
        Ok(Self {
            result_ty,
            source_ty,
        })
    }
}

/// Zero-extend integer operation.
#[derive(Debug)]
pub struct ZeroExtendOp {
    /// The resulting integer type after the extension.
    pub result_ty: IntType,
    /// The input integer type before the extension.
    pub source_ty: IntType,
}

impl ZeroExtendOp {
    /// Creates a new zero-extend operation.
    ///
    /// # Errors
    ///
    /// If the operation would extend the source type to a smaller width.
    fn new(result_ty: IntType, source_ty: IntType) -> Result<Self, ParseError> {
        if !ExtIntType::is_extendable_to(source_ty.into(), result_ty) {
            return Err(ParseError::ExtensionToSmallerInt)
        }
        Ok(Self {
            result_ty,
            source_ty,
        })
    }
}

/// Sign-extend integer operation.
#[derive(Debug)]
pub struct SignExtendOp {
    /// The resulting integer type after the extension.
    pub result_ty: IntType,
    /// The input integer type before the extension.
    pub source_ty: IntType,
}

impl SignExtendOp {
    /// Creates a new sign-extend operation.
    ///
    /// # Errors
    ///
    /// If the operation would extend the source type to a smaller width.
    fn new(result_ty: IntType, source_ty: IntType) -> Result<Self, ParseError> {
        if !ExtIntType::is_extendable_to(source_ty.into(), result_ty) {
            return Err(ParseError::ExtensionToSmallerInt)
        }
        Ok(Self {
            result_ty,
            source_ty,
        })
    }
}

/// The Wasm `memory.grow` operation.
#[derive(Debug)]
pub struct MemoryGrowOp {
    /// The identifier of the operated on linear memory.
    pub id: LinearMemoryId,
}

impl MemoryGrowOp {
    /// Creates a new `memory.grow` operation.
    fn new(id: LinearMemoryId) -> Self {
        Self { id }
    }
}

/// The Wasm `memory.size` operation.
#[derive(Debug)]
pub struct MemorySizeOp {
    /// The identifier of the operated on linear memory.
    pub id: LinearMemoryId,
}

impl MemorySizeOp {
    /// Creates a new `memory.size` operation.
    fn new(id: LinearMemoryId) -> Self {
        Self { id }
    }
}

/// Runwell-Wasm operators.
///
/// # Note
///
/// - These are very close to the original Wasm input operators.
/// - Indices have been converted from raw and being untyped into their
///   typed `runwell` representation, e.g. `FunctionId` instead of `u32`.
/// - Some of the original Wasm operators have been unified, such as all the
///   `load` and `store` operators.
/// - The conversion to this operator format has the advantage of finalizing
///   the parsing procedure so that later passes can simply work on the
///   operator data without parsing anything.
/// - Unsupported Wasm operators such as floating point operators have been
///   filtered out in this set compared to the operators provided by the
///   `wasmparser` crate.
#[derive(Debug, From)]
pub enum Operator {
    Unreachable,
    Nop,
    Block(BlockOp),
    Loop(LoopOp),
    If(IfOp),
    Else,
    End,
    Br(BrOp),
    BrIf(BrIfOp),
    BrTable(BrTableOp),
    Return,
    Call(CallOp),
    CallIndirect(CallIndirectOp),
    Drop,
    Select,
    LocalGet(LocalGetOp),
    LocalSet(LocalSetOp),
    LocalTee(LocalTeeOp),
    GlobalGet(GlobalGetOp),
    GlobalSet(GlobalSetOp),
    Load(LoadOp),
    Store(StoreOp),
    Const(ConstOp),
    IntCmp(IntCmpOp),
    CountLeadingZeros(CountLeadingZerosOp),
    CountTrailingZeros(CountTrailingZerosOp),
    Popcount(PopcountOp),
    Add(AddOp),
    Sub(SubOp),
    Mul(MulOp),
    Sdiv(SdivOp),
    Udiv(UdivOp),
    Srem(SremOp),
    Urem(UremOp),
    And(AndOp),
    Or(OrOp),
    Xor(XorOp),
    Shl(ShlOp),
    Sshr(SshrOp),
    Ushr(UshrOp),
    RotLeft(RotLeftOp),
    RotRight(RotRightOp),
    ZeroExtend(ZeroExtendOp),
    SignExtend(SignExtendOp),
    Truncate(TruncateOp),
    MemoryGrow(MemoryGrowOp),
    MemorySize(MemorySizeOp),
}
