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

//! Runwell primitive types and constant values.
//!
//! Unlike Wasm the Runwell JIT supports 8-bit and 16-bit integer types.
//! This is to generalize certain compound Wasm operations such as `i32.load8_u`
//! that first load an 8-bit integer from the given address and then zero-extends it
//! to a 32-bit integer value.

use crate::instr::Instruction;
use core::fmt;
use derive_more::{Display, From};
use entity::{DisplayHook, Idx};

impl DisplayHook for Instruction {
    fn fmt(
        idx: Idx<Self>,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        write!(f, "instr({})", idx.into_raw())
    }
}

/// A branching edge entity.
///
/// An entity of this kind represents a single edge between a pair
/// of two basic blocks with a branch between them. There can be
/// multiple such edges between the same pair of basic blocks.
#[derive(Debug)]
pub enum EdgeEntity {}

/// A unique edge entity reference.
pub type Edge = Idx<EdgeEntity>;

impl DisplayHook for EdgeEntity {
    fn fmt(idx: Edge, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "edge{}", idx.into_raw())
    }
}

/// A function entity of the Runwell IR.
#[derive(Debug, Default)]
pub struct FunctionEntity;

/// A function index.
pub type Func = Idx<FunctionEntity>;

impl DisplayHook for FunctionEntity {
    fn fmt(idx: Func, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "func{}", idx.into_raw())
    }
}

/// A function type entity of the Runwell IR.
#[derive(Debug, Default)]
pub struct FuncTypeEntity;

/// The unique index of a function type entity of the Runwell IR.
pub type FuncType = Idx<FuncTypeEntity>;

impl DisplayHook for FuncTypeEntity {
    fn fmt(idx: FuncType, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "func_type({})", idx.into_raw())
    }
}

/// A linear memory entity of the Runwell IR.
#[derive(Debug, Default)]
pub struct LinearMemoryEntity;

/// The unique index of a linear memory entity of the Runwell IR.
pub type Mem = Idx<LinearMemoryEntity>;

impl DisplayHook for LinearMemoryEntity {
    fn fmt(idx: Mem, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "mem({})", idx.into_raw())
    }
}

/// A table entity of the Runwell IR.
#[derive(Debug, Default)]
pub struct TableEntity;

/// The unique index of a table entity of the Runwell IR.
pub type Table = Idx<TableEntity>;

impl DisplayHook for TableEntity {
    fn fmt(idx: Table, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "table({})", idx.into_raw())
    }
}

/// A basic block entity of the Runwell IR.
#[derive(Debug, Default, Copy, Clone)]
pub struct BlockEntity;

/// The unique index of a basic block entity of the Runwell IR.
pub type Block = Idx<BlockEntity>;

impl DisplayHook for BlockEntity {
    fn fmt(idx: Block, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "bb{}", idx.into_raw())
    }
}

/// An SSA value entity of the Runwell IR.
#[derive(Debug, Default, Copy, Clone)]
pub struct ValueEntity;

/// The unique index of a value entity of the Runwell IR.
pub type Value = Idx<ValueEntity>;

impl DisplayHook for ValueEntity {
    fn fmt(idx: Value, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "v{}", idx.into_raw())
    }
}

/// Any Runwell supported primitive type.
#[derive(
    Debug, Display, From, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash,
)]
pub enum Type {
    #[display(fmt = "ptr")]
    Ptr,
    Int(IntType),
    Float(FloatType),
}

impl Type {
    /// Returns the bit width of the type.
    pub fn bit_width(&self) -> u32 {
        match self {
            Self::Ptr => 32,
            Self::Int(int_type) => int_type.bit_width(),
            Self::Float(float_type) => float_type.bit_width(),
        }
    }

    /// Returns the alignment exponent, `N` in `2^N`.
    pub fn alignment(&self) -> u8 {
        match self {
            Self::Ptr => 2,
            Self::Int(int_type) => int_type.alignment(),
            Self::Float(float_type) => float_type.alignment(),
        }
    }

    /// Returns `Some` if the type is an integer type, otherwise returns `None`.
    pub fn filter_map_int(self) -> Option<IntType> {
        if let Self::Int(int_type) = self {
            return Some(int_type)
        }
        None
    }

    /// Returns `Some` if the type is a float type, otherwise returns `None`.
    pub fn filter_map_float(self) -> Option<FloatType> {
        if let Self::Float(float_type) = self {
            return Some(float_type)
        }
        None
    }
}

/// Any fixed-size integer type.
#[derive(Debug, Display, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IntType {
    #[display(fmt = "i1")]
    I1,
    #[display(fmt = "i8")]
    I8,
    #[display(fmt = "i16")]
    I16,
    #[display(fmt = "i32")]
    I32,
    #[display(fmt = "i64")]
    I64,
}

impl IntType {
    /// Returns the bit width of the fixed-size integer type.
    pub fn bit_width(&self) -> u32 {
        match self {
            Self::I1 => 1,
            Self::I8 => 8,
            Self::I16 => 16,
            Self::I32 => 32,
            Self::I64 => 64,
        }
    }

    /// Returns the alignment exponent, `N` in `2^N`.
    pub fn alignment(&self) -> u8 {
        match self {
            Self::I1 => 0,
            Self::I8 => 0,
            Self::I16 => 1,
            Self::I32 => 2,
            Self::I64 => 3,
        }
    }

    /// Returns the maximum unsigned value representable by the integer type.
    pub fn max_unsigned_value(&self) -> u64 {
        match self {
            Self::I1 => 1,
            Self::I8 => u8::MAX as u64,
            Self::I16 => u16::MAX as u64,
            Self::I32 => u32::MAX as u64,
            Self::I64 => u64::MAX as u64,
        }
    }
}

/// Any floating point number type.
#[derive(Debug, Display, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FloatType {
    #[display(fmt = "f32")]
    F32,
    #[display(fmt = "f64")]
    F64,
}

impl FloatType {
    /// Returns the bit width of the floating point number type.
    pub fn bit_width(&self) -> u32 {
        match self {
            Self::F32 => 32,
            Self::F64 => 64,
        }
    }

    /// Returns the alignment exponent, `N` in `2^N`.
    pub fn alignment(&self) -> u8 {
        match self {
            Self::F32 => 2,
            Self::F64 => 3,
        }
    }
}

/// A Runwell constant value.
#[derive(
    Debug, Display, From, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash,
)]
pub enum Const {
    Ptr(u32),
    Int(IntConst),
    Float(FloatConst),
}

impl Const {
    /// Returns a zero-constant for the given type.
    pub fn zero(ty: Type) -> Const {
        match ty {
            Type::Ptr => Const::Ptr(0),
            Type::Int(int_type) => IntConst::zero(int_type).into(),
            Type::Float(float_type) => FloatConst::zero(float_type).into(),
        }
    }

    /// Returns the type of the constant value.
    pub fn ty(&self) -> Type {
        match self {
            Self::Ptr(_) => Type::Ptr,
            Self::Int(int_const) => int_const.ty(),
            Self::Float(float_const) => float_const.ty(),
        }
    }

    /// Returns the underlying 64-bits of the constant.
    pub fn into_bits64(self) -> u64 {
        match self {
            Self::Ptr(ptr_value) => ptr_value as u64,
            Self::Int(int_const) => int_const.into_bits64(),
            Self::Float(float_const) => float_const.into_bits64(),
        }
    }
}

/// A constant fixed-size integer value.
#[derive(Debug, Display, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IntConst {
    I1(bool),
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
}

impl IntConst {
    /// Returns a zero-constant integer for the given type.
    pub fn zero(int_ty: IntType) -> IntConst {
        match int_ty {
            IntType::I1 => Self::I1(false),
            IntType::I8 => Self::I8(0),
            IntType::I16 => Self::I16(0),
            IntType::I32 => Self::I32(0),
            IntType::I64 => Self::I64(0),
        }
    }

    /// Returns the type of the constant fixed-size integer.
    pub fn ty(&self) -> Type {
        self.int_ty().into()
    }

    /// Returns the type of the constant fixed-size integer.
    pub fn int_ty(&self) -> IntType {
        match self {
            Self::I1(_) => IntType::I1,
            Self::I8(_) => IntType::I8,
            Self::I16(_) => IntType::I16,
            Self::I32(_) => IntType::I32,
            Self::I64(_) => IntType::I64,
        }
    }

    /// Returns the underlying 64-bits of the constant.
    pub fn into_bits64(self) -> u64 {
        match self {
            Self::I1(value) => value as u64,
            Self::I8(value) => value as u8 as u64,
            Self::I16(value) => value as u16 as u64,
            Self::I32(value) => value as u32 as u64,
            Self::I64(value) => value as u64,
        }
    }
}

/// A constant floating point number value.
#[derive(Debug, Display, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FloatConst {
    F32(F32),
    F64(F64),
}

impl FloatConst {
    /// Returns a zero-constant integer for the given type.
    pub fn zero(float_ty: FloatType) -> FloatConst {
        match float_ty {
            FloatType::F32 => Self::F32(F32::from(0.0)),
            FloatType::F64 => Self::F64(F64::from(0.0)),
        }
    }

    /// Returns the type of the constant floating point number.
    pub fn ty(&self) -> Type {
        match self {
            Self::F32(_) => FloatType::F32.into(),
            Self::F64(_) => FloatType::F64.into(),
        }
    }

    /// Returns the underlying 64-bits of the constant.
    pub fn into_bits64(self) -> u64 {
        match self {
            Self::F32(value) => value.bits() as u64,
            Self::F64(value) => value.bits(),
        }
    }
}

/// A `f32` (32-bit floating point) value.
#[derive(Debug, Display, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[display(fmt = "{:?}", "f32::from_le_bytes(bits.to_le_bytes())")]
pub struct F32 {
    bits: u32,
}

impl F32 {
    /// Returns a 32-bit floating point number from the given bits.
    pub fn from_bits(bits: u32) -> Self {
        Self { bits }
    }

    /// Returns the underlying bits of the 32-bit float.
    pub fn bits(self) -> u32 {
        self.bits
    }
}

impl From<f32> for F32 {
    fn from(value: f32) -> Self {
        Self {
            bits: u32::from_le_bytes(value.to_le_bytes()),
        }
    }
}

impl From<F32> for Const {
    fn from(value: F32) -> Self {
        Const::Float(FloatConst::F32(value))
    }
}

/// A `f64` (64-bit floating point) value.
#[derive(Debug, Display, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[display(fmt = "{:?}", "f64::from_le_bytes(bits.to_le_bytes())")]
pub struct F64 {
    bits: u64,
}

impl F64 {
    /// Returns a 64-bit floating point number from the given bits.
    pub fn from_bits(bits: u64) -> Self {
        Self { bits }
    }

    /// Returns the underlying bits of the 64-bit float.
    pub fn bits(self) -> u64 {
        self.bits
    }
}

impl From<f64> for F64 {
    fn from(value: f64) -> Self {
        Self {
            bits: u64::from_le_bytes(value.to_le_bytes()),
        }
    }
}

impl From<F64> for Const {
    fn from(value: F64) -> Self {
        Const::Float(FloatConst::F64(value))
    }
}
