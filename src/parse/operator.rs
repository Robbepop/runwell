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

use crate::parse::{FunctionId, GlobalVariableId, ParseError, TableId};
use derive_more::From;
use wasmparser::{MemoryImmediate, TypeOrFuncType};

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
    relative_depths: Box<[usize]>,
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
    pub offset: usize,
}

/// A local variable ID.
///
/// Used to access local variables of Wasm functions.
#[derive(Debug)]
pub struct LocalId(pub(super) usize);

/// Gets the identified local variable.
#[derive(Debug)]
pub struct LocalGetOp {
    /// The local variable identifier.
    pub id: LocalId,
}

/// Sets the identified local variable.
#[derive(Debug)]
pub struct LocalSetOp {
    /// The local variable identifier.
    pub id: LocalId,
}

/// Sets and returns back the value of the identified local variable.
#[derive(Debug)]
pub struct LocalTeeOp {
    /// The local variable identifier.
    pub id: LocalId,
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

/// The extended set of integer types.
///
/// # Note
///
/// Required for generic `load` and `store` as well as for
/// conversion routines.
#[derive(Debug, Copy, Clone)]
pub enum ExtIntType {
    /// 8-bit integer type.
    I8,
    /// 16-bit integer type.
    I16,
    /// 32-bit integer type.
    I32,
    /// 64-bit integer type.
    I64,
}

impl ExtIntType {
    /// Returns the number of bytes used to represent a value of the type.
    fn width(self) -> usize {
        match self {
            ExtIntType::I8 => 1,
            ExtIntType::I16 => 2,
            ExtIntType::I32 => 3,
            ExtIntType::I64 => 4,
        }
    }
}

impl From<IntType> for ExtIntType {
    fn from(int_ty: IntType) -> Self {
        match int_ty {
            IntType::I32 => ExtIntType::I32,
            IntType::I64 => ExtIntType::I64,
        }
    }
}

/// A Wasm integer type.
#[derive(Debug, Copy, Clone)]
pub enum IntType {
    /// 32-bit integer type.
    I32,
    /// 64-bit integer type.
    I64,
}

impl IntType {
    /// Returns the number of bytes used to represent a value of the type.
    fn width(self) -> usize {
        match self {
            IntType::I32 => 2,
            IntType::I64 => 4,
        }
    }
}

/// Either signed or unsigned.
#[derive(Debug, Copy, Clone)]
pub enum Signedness {
    Unsigned,
    Signed,
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
        if result_ty.width() <= source_ty.width() {
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
        if result_ty.width() <= source_ty.width() {
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
        if src_ty.width() <= dst_ty.width() {
            return Err(ParseError::ExtensionToSmallerInt)
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

/// Zero-extend integer operation.
#[derive(Debug)]
pub struct ZeroExtendOp {
    /// The resulting integer type after the extension.
    pub result_ty: IntType,
    /// The input integer type before the extension.
    pub source_ty: IntType,
}

/// Sign-extend integer operation.
#[derive(Debug)]
pub struct SignExtendOp {
    /// The resulting integer type after the extension.
    pub result_ty: IntType,
    /// The input integer type before the extension.
    pub source_ty: IntType,
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
}

impl<'a> core::convert::TryFrom<wasmparser::Operator<'a>> for Operator {
    type Error = ParseError;

    fn try_from(op: wasmparser::Operator<'a>) -> Result<Self, Self::Error> {
        use wasmparser::Operator as WasmOperator;
        let result_op = match op {
            WasmOperator::Unreachable => Operator::Unreachable,
            WasmOperator::Nop => Operator::Nop,

            WasmOperator::Block { ty } => BlockOp { ty }.into(),
            WasmOperator::Loop { ty } => LoopOp { ty }.into(),
            WasmOperator::If { ty } => IfOp { ty }.into(),
            WasmOperator::Else => Operator::Else,
            WasmOperator::End => Operator::End,

            WasmOperator::Br { relative_depth } => {
                BrOp {
                    relative_depth: relative_depth as usize,
                }
                .into()
            }
            WasmOperator::BrIf { relative_depth } => {
                BrIfOp {
                    relative_depth: relative_depth as usize,
                }
                .into()
            }
            WasmOperator::BrTable { table } => {
                BrTableOp::try_from(table)?.into()
            }

            WasmOperator::Return => Operator::Return,

            WasmOperator::Call { function_index } => {
                CallOp {
                    id: FunctionId(function_index as usize),
                }
                .into()
            }
            WasmOperator::CallIndirect { index, table_index } => {
                CallIndirectOp {
                    table_id: TableId(table_index as usize),
                    offset: index as usize,
                }
                .into()
            }

            WasmOperator::Drop => Operator::Drop,
            WasmOperator::Select => Operator::Select,

            WasmOperator::LocalGet { local_index } => {
                LocalGetOp {
                    id: LocalId(local_index as usize),
                }
                .into()
            }
            WasmOperator::LocalSet { local_index } => {
                LocalSetOp {
                    id: LocalId(local_index as usize),
                }
                .into()
            }
            WasmOperator::LocalTee { local_index } => {
                LocalTeeOp {
                    id: LocalId(local_index as usize),
                }
                .into()
            }

            WasmOperator::GlobalGet { global_index } => {
                GlobalGetOp {
                    id: GlobalVariableId(global_index as usize),
                }
                .into()
            }
            WasmOperator::GlobalSet { global_index } => {
                GlobalSetOp {
                    id: GlobalVariableId(global_index as usize),
                }
                .into()
            }

            WasmOperator::I32Load { memarg } => {
                LoadOp::simple(memarg, IntType::I32).into()
            }
            WasmOperator::I64Load { memarg } => {
                LoadOp::simple(memarg, IntType::I64).into()
            }
            WasmOperator::I32Load8S { memarg } => {
                LoadOp::load_sext(memarg, IntType::I32, ExtIntType::I8)?.into()
            }
            WasmOperator::I32Load8U { memarg } => {
                LoadOp::load_zext(memarg, IntType::I32, ExtIntType::I8)?.into()
            }
            WasmOperator::I32Load16S { memarg } => {
                LoadOp::load_sext(memarg, IntType::I32, ExtIntType::I16)?.into()
            }
            WasmOperator::I32Load16U { memarg } => {
                LoadOp::load_zext(memarg, IntType::I32, ExtIntType::I16)?.into()
            }
            WasmOperator::I64Load8S { memarg } => {
                LoadOp::load_sext(memarg, IntType::I64, ExtIntType::I8)?.into()
            }
            WasmOperator::I64Load8U { memarg } => {
                LoadOp::load_zext(memarg, IntType::I64, ExtIntType::I8)?.into()
            }
            WasmOperator::I64Load16S { memarg } => {
                LoadOp::load_sext(memarg, IntType::I64, ExtIntType::I16)?.into()
            }
            WasmOperator::I64Load16U { memarg } => {
                LoadOp::load_zext(memarg, IntType::I64, ExtIntType::I16)?.into()
            }
            WasmOperator::I64Load32S { memarg } => {
                LoadOp::load_sext(memarg, IntType::I64, ExtIntType::I32)?.into()
            }
            WasmOperator::I64Load32U { memarg } => {
                LoadOp::load_zext(memarg, IntType::I64, ExtIntType::I32)?.into()
            }

            WasmOperator::I32Store { memarg } => {
                StoreOp::simple(memarg, IntType::I32).into()
            }
            WasmOperator::I64Store { memarg } => {
                StoreOp::simple(memarg, IntType::I64).into()
            }
            WasmOperator::I32Store8 { memarg } => {
                StoreOp::store_truncate(memarg, IntType::I32, ExtIntType::I8)?
                    .into()
            }
            WasmOperator::I32Store16 { memarg } => {
                StoreOp::store_truncate(memarg, IntType::I32, ExtIntType::I16)?
                    .into()
            }
            WasmOperator::I64Store8 { memarg } => {
                StoreOp::store_truncate(memarg, IntType::I64, ExtIntType::I8)?
                    .into()
            }
            WasmOperator::I64Store16 { memarg } => {
                StoreOp::store_truncate(memarg, IntType::I64, ExtIntType::I16)?
                    .into()
            }
            WasmOperator::I64Store32 { memarg } => {
                StoreOp::store_truncate(memarg, IntType::I64, ExtIntType::I32)?
                    .into()
            }

            WasmOperator::I32Const { value } => ConstOp::I32(value).into(),
            WasmOperator::I64Const { value } => ConstOp::I64(value).into(),

            WasmOperator::I32Eqz => {
                IntCmpOp::new(IntType::I32, IntCmpOpKind::Eqz).into()
            }
            WasmOperator::I32Eq => {
                IntCmpOp::new(IntType::I32, IntCmpOpKind::Eq).into()
            }
            WasmOperator::I32Ne => {
                IntCmpOp::new(IntType::I32, IntCmpOpKind::Ne).into()
            }
            WasmOperator::I32LtS => {
                IntCmpOp::new(IntType::I32, IntCmpOpKind::Slt).into()
            }
            WasmOperator::I32LtU => {
                IntCmpOp::new(IntType::I32, IntCmpOpKind::Ult).into()
            }
            WasmOperator::I32GtS => {
                IntCmpOp::new(IntType::I32, IntCmpOpKind::Sgt).into()
            }
            WasmOperator::I32GtU => {
                IntCmpOp::new(IntType::I32, IntCmpOpKind::Ugt).into()
            }
            WasmOperator::I32LeS => {
                IntCmpOp::new(IntType::I32, IntCmpOpKind::Sle).into()
            }
            WasmOperator::I32LeU => {
                IntCmpOp::new(IntType::I32, IntCmpOpKind::Ule).into()
            }
            WasmOperator::I32GeS => {
                IntCmpOp::new(IntType::I32, IntCmpOpKind::Sge).into()
            }
            WasmOperator::I32GeU => {
                IntCmpOp::new(IntType::I32, IntCmpOpKind::Uge).into()
            }
            WasmOperator::I64Eqz => {
                IntCmpOp::new(IntType::I64, IntCmpOpKind::Eqz).into()
            }
            WasmOperator::I64Eq => {
                IntCmpOp::new(IntType::I64, IntCmpOpKind::Eq).into()
            }
            WasmOperator::I64Ne => {
                IntCmpOp::new(IntType::I64, IntCmpOpKind::Ne).into()
            }
            WasmOperator::I64LtS => {
                IntCmpOp::new(IntType::I64, IntCmpOpKind::Slt).into()
            }
            WasmOperator::I64LtU => {
                IntCmpOp::new(IntType::I64, IntCmpOpKind::Ult).into()
            }
            WasmOperator::I64GtS => {
                IntCmpOp::new(IntType::I64, IntCmpOpKind::Sgt).into()
            }
            WasmOperator::I64GtU => {
                IntCmpOp::new(IntType::I64, IntCmpOpKind::Ugt).into()
            }
            WasmOperator::I64LeS => {
                IntCmpOp::new(IntType::I64, IntCmpOpKind::Sle).into()
            }
            WasmOperator::I64LeU => {
                IntCmpOp::new(IntType::I64, IntCmpOpKind::Ule).into()
            }
            WasmOperator::I64GeS => {
                IntCmpOp::new(IntType::I64, IntCmpOpKind::Sge).into()
            }
            WasmOperator::I64GeU => {
                IntCmpOp::new(IntType::I64, IntCmpOpKind::Uge).into()
            }

            WasmOperator::I32Clz => {
                CountLeadingZerosOp::new(IntType::I32).into()
            }
            WasmOperator::I32Ctz => {
                CountTrailingZerosOp::new(IntType::I32).into()
            }
            WasmOperator::I32Popcnt => {
                PopcountOp::new(IntType::I32).into()
            }

            WasmOperator::I64Clz => {
                CountLeadingZerosOp::new(IntType::I64).into()
            }
            WasmOperator::I64Ctz => {
                CountTrailingZerosOp::new(IntType::I64).into()
            }
            WasmOperator::I64Popcnt => {
                PopcountOp::new(IntType::I64).into()
            }

            WasmOperator::I32Add => AddOp::new(IntType::I32).into(),
            WasmOperator::I32Sub => SubOp::new(IntType::I32).into(),
            WasmOperator::I32Mul => MulOp::new(IntType::I32).into(),
            WasmOperator::I32DivS => SdivOp::new(IntType::I32).into(),
            WasmOperator::I32DivU => UdivOp::new(IntType::I32).into(),
            WasmOperator::I32RemS => SremOp::new(IntType::I32).into(),
            WasmOperator::I32RemU => UremOp::new(IntType::I32).into(),
            WasmOperator::I32And => AndOp::new(IntType::I32).into(),
            WasmOperator::I32Or => OrOp::new(IntType::I32).into(),
            WasmOperator::I32Xor => XorOp::new(IntType::I32).into(),
            WasmOperator::I32Shl => ShlOp::new(IntType::I32).into(),
            WasmOperator::I32ShrS => SshrOp::new(IntType::I32).into(),
            WasmOperator::I32ShrU => UshrOp::new(IntType::I32).into(),
            WasmOperator::I32Rotl => RotLeftOp::new(IntType::I32).into(),
            WasmOperator::I32Rotr => RotRightOp::new(IntType::I32).into(),

            WasmOperator::I64Add => AddOp::new(IntType::I64).into(),
            WasmOperator::I64Sub => SubOp::new(IntType::I64).into(),
            WasmOperator::I64Mul => MulOp::new(IntType::I64).into(),
            WasmOperator::I64DivS => SdivOp::new(IntType::I64).into(),
            WasmOperator::I64DivU => UdivOp::new(IntType::I64).into(),
            WasmOperator::I64RemS => SremOp::new(IntType::I64).into(),
            WasmOperator::I64RemU => UremOp::new(IntType::I64).into(),
            WasmOperator::I64And => AndOp::new(IntType::I64).into(),
            WasmOperator::I64Or => OrOp::new(IntType::I64).into(),
            WasmOperator::I64Xor => XorOp::new(IntType::I64).into(),
            WasmOperator::I64Shl => ShlOp::new(IntType::I64).into(),
            WasmOperator::I64ShrS => SshrOp::new(IntType::I64).into(),
            WasmOperator::I64ShrU => UshrOp::new(IntType::I64).into(),
            WasmOperator::I64Rotl => RotLeftOp::new(IntType::I64).into(),
            WasmOperator::I64Rotr => RotRightOp::new(IntType::I64).into(),

            unsupported => {
                println!(
                    "encountered unsupported Wasm operator: {:?}",
                    unsupported
                );
                return Err(ParseError::UnsupportedOperator)
            }
        };
        Ok(result_op)
    }
}

impl<'a> core::convert::TryFrom<wasmparser::BrTable<'a>> for BrTableOp {
    type Error = ParseError;

    fn try_from(table: wasmparser::BrTable<'a>) -> Result<Self, Self::Error> {
        let (relative_depths, default) = table.read_table()?;
        let relative_depths = relative_depths
            .into_iter()
            .map(|&relative_depth| relative_depth as usize)
            .collect::<Vec<_>>()
            .into_boxed_slice();
        let default = default as usize;
        Ok(Self {
            relative_depths,
            default,
        })
    }
}
