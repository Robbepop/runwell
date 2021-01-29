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

use super::{
    EvaluationContext,
    FunctionFrame,
    InterpretInstr,
    InterpretationError,
    InterpretationFlow,
    MISSING_RETURN_VALUE_ERRSTR,
};
use ir::{
    instr::{
        operands::{BinaryIntOp, CompareIntOp, UnaryIntOp},
        BinaryIntInstr,
        CompareIntInstr,
        ExtendIntInstr,
        IntInstr,
        IntToFloatInstr,
        TruncateIntInstr,
        UnaryIntInstr,
    },
    primitive::{FloatType, IntType, Value},
};

impl InterpretInstr for IntInstr {
    fn interpret_instr(
        &self,
        return_value: Option<Value>,
        ctx: &mut EvaluationContext,
        frame: &mut FunctionFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        match self {
            Self::Binary(instr) => {
                instr.interpret_instr(return_value, ctx, frame)
            }
            Self::Unary(instr) => {
                instr.interpret_instr(return_value, ctx, frame)
            }
            Self::Compare(instr) => {
                instr.interpret_instr(return_value, ctx, frame)
            }
            Self::Extend(instr) => {
                instr.interpret_instr(return_value, ctx, frame)
            }
            Self::IntToFloat(instr) => {
                instr.interpret_instr(return_value, ctx, frame)
            }
            Self::Truncate(instr) => {
                instr.interpret_instr(return_value, ctx, frame)
            }
        }
    }
}

impl InterpretInstr for UnaryIntInstr {
    fn interpret_instr(
        &self,
        return_value: Option<Value>,
        _ctx: &mut EvaluationContext,
        frame: &mut FunctionFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let return_value = return_value.expect(MISSING_RETURN_VALUE_ERRSTR);
        let source = frame.read_register(self.src());
        let result = match self.op() {
            UnaryIntOp::LeadingZeros => source.leading_zeros(),
            UnaryIntOp::TrailingZeros => source.trailing_zeros(),
            UnaryIntOp::PopCount => source.count_ones(),
        };
        frame.write_register(return_value, result as u64);
        Ok(InterpretationFlow::Continue)
    }
}

impl InterpretInstr for TruncateIntInstr {
    fn interpret_instr(
        &self,
        return_value: Option<Value>,
        _ctx: &mut EvaluationContext,
        frame: &mut FunctionFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let return_value = return_value.expect(MISSING_RETURN_VALUE_ERRSTR);
        let source = frame.read_register(self.src());
        debug_assert!(
            self.dst_type().bit_width() <= self.src_type().bit_width()
        );
        fn mask(bits: u32) -> u64 {
            (0x1 << bits) - 1
        }
        let result = match self.dst_type() {
            IntType::I8 => source & mask(8),
            IntType::I16 => source & mask(16),
            IntType::I32 => source & mask(32),
            IntType::I64 => source,
        };
        frame.write_register(return_value, result as u64);
        Ok(InterpretationFlow::Continue)
    }
}

impl InterpretInstr for ExtendIntInstr {
    fn interpret_instr(
        &self,
        return_value: Option<Value>,
        _ctx: &mut EvaluationContext,
        frame: &mut FunctionFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let return_value = return_value.expect(MISSING_RETURN_VALUE_ERRSTR);
        let source = frame.read_register(self.src());
        debug_assert!(
            self.src_type().bit_width() <= self.dst_type().bit_width()
        );
        let result = if self.is_signed() {
            match (self.src_type(), self.dst_type()) {
                (IntType::I8, IntType::I16) => {
                    source as u8 as i8 as i16 as u16 as u64
                }
                (IntType::I8, IntType::I32) => {
                    source as u8 as i8 as i32 as u32 as u64
                }
                (IntType::I8, IntType::I64) => source as u8 as i8 as i64 as u64,
                (IntType::I16, IntType::I32) => {
                    source as u16 as i16 as i32 as u32 as u64
                }
                (IntType::I32, IntType::I64) => {
                    source as u32 as i32 as i64 as u64
                }
                (x, y) if x == y => source,
                _ => unreachable!(),
            }
        } else {
            // Nothing to do since interpreter registers are `u64`.
            source
        };
        frame.write_register(return_value, result as u64);
        Ok(InterpretationFlow::Continue)
    }
}

impl InterpretInstr for IntToFloatInstr {
    /// WebAssembly instructions that map to IntToFloatInstr:
    ///
    /// `i32` conversion to `f32` and `f64`:
    ///  - `i32.trunc_f32_s`
    ///  - `i32.trunc_f32_u`
    ///  - `i32.trunc_f64_s`
    ///  - `i32.trunc_f64_u`
    ///
    /// `i64` conversion to `f32` and `f64`:
    ///  - `i64.trunc_f32_s`
    ///  - `i64.trunc_f32_u`
    ///  - `i64.trunc_f64_s`
    ///  - `i64.trunc_f64_u`
    fn interpret_instr(
        &self,
        return_value: Option<Value>,
        _ctx: &mut EvaluationContext,
        frame: &mut FunctionFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let return_value = return_value.expect(MISSING_RETURN_VALUE_ERRSTR);
        let source = frame.read_register(self.src());
        use FloatType::{F32, F64};
        use IntType::{I16, I32, I64, I8};
        let result = match (self.is_signed(), self.src_type(), self.dst_type())
        {
            // uN -> f32
            (false, I8, F32) => (source as u8 as f32).to_bits() as u64,
            (false, I16, F32) => (source as u16 as f32).to_bits() as u64,
            (false, I32, F32) => (source as u32 as f32).to_bits() as u64,
            (false, I64, F32) => (source as u64 as f32).to_bits() as u64,
            // uN -> f64
            (false, I8, F64) => (source as u8 as f64).to_bits(),
            (false, I16, F64) => (source as u16 as f64).to_bits(),
            (false, I32, F64) => (source as u32 as f64).to_bits(),
            (false, I64, F64) => (source as u64 as f64).to_bits(),
            // iN -> f32
            (true, I8, F32) => (source as u8 as i8 as f32).to_bits() as u64,
            (true, I16, F32) => (source as u16 as i16 as f32).to_bits() as u64,
            (true, I32, F32) => (source as u32 as i32 as f32).to_bits() as u64,
            (true, I64, F32) => (source as u64 as i64 as f32).to_bits() as u64,
            // iN -> f64
            (true, I8, F64) => (source as u8 as i8 as f64).to_bits(),
            (true, I16, F64) => (source as u16 as i16 as f64).to_bits(),
            (true, I32, F64) => (source as u32 as i32 as f64).to_bits(),
            (true, I64, F64) => (source as u64 as i64 as f64).to_bits(),
        };
        frame.write_register(return_value, result as u64);
        Ok(InterpretationFlow::Continue)
    }
}

impl InterpretInstr for CompareIntInstr {
    fn interpret_instr(
        &self,
        return_value: Option<Value>,
        _ctx: &mut EvaluationContext,
        frame: &mut FunctionFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let return_value = return_value.expect(MISSING_RETURN_VALUE_ERRSTR);
        let lhs = frame.read_register(self.lhs());
        let rhs = frame.read_register(self.rhs());
        use CompareIntOp as Op;
        /// Compares `lhs` and `rhs` given the comparator `op` using `f` to convert to signed.
        fn cmp<U, S, F>(op: CompareIntOp, lhs: U, rhs: U, mut f: F) -> u64
        where
            U: Eq + Ord,
            S: Ord,
            F: FnMut(U) -> S,
        {
            let result = match op {
                Op::Eq => lhs == rhs,
                Op::Ne => lhs != rhs,
                Op::Slt => f(lhs) < f(rhs),
                Op::Sle => f(lhs) <= f(rhs),
                Op::Sgt => f(lhs) > f(rhs),
                Op::Sge => f(lhs) >= f(rhs),
                Op::Ult => lhs < rhs,
                Op::Ule => lhs <= rhs,
                Op::Ugt => lhs > rhs,
                Op::Uge => lhs >= rhs,
            };
            result as u64
        }
        let result = match self.ty() {
            IntType::I8 => {
                let lhs = lhs as u8;
                let rhs = rhs as u8;
                cmp(self.op(), lhs, rhs, |lhs| lhs as i8)
            }
            IntType::I16 => {
                let lhs = lhs as u16;
                let rhs = rhs as u16;
                cmp(self.op(), lhs, rhs, |lhs| lhs as i16)
            }
            IntType::I32 => {
                let lhs = lhs as u32;
                let rhs = rhs as u32;
                cmp(self.op(), lhs, rhs, |lhs| lhs as i32)
            }
            IntType::I64 => cmp(self.op(), lhs, rhs, |lhs| lhs as i64),
        };
        frame.write_register(return_value, result);
        Ok(InterpretationFlow::Continue)
    }
}

#[rustfmt::skip]
mod conv {
    pub fn reg_to_i8(reg: u64) -> i8 { reg as u8 as i8 }
    pub fn reg_to_i16(reg: u64) -> i16 { reg as u16 as i16 }
    pub fn reg_to_i32(reg: u64) -> i32 { reg as u32 as i32 }
    pub fn reg_to_i64(reg: u64) -> i64 { reg as u64 as i64 }
    pub fn reg_to_u8(reg: u64) -> u8 { reg as u8 }
    pub fn reg_to_u16(reg: u64) -> u16 { reg as u16 }
    pub fn reg_to_u32(reg: u64) -> u32 { reg as u32 }
    pub fn reg_to_u64(reg: u64) -> u64 { reg }
    pub fn i8_to_reg(val: i8) -> u64 { val as u8 as u64 }
    pub fn i16_to_reg(val: i16) -> u64 { val as u16 as u64 }
    pub fn i32_to_reg(val: i32) -> u64 { val as u32 as u64 }
    pub fn i64_to_reg(val: i64) -> u64 { val as u64 }
    pub fn u8_to_reg(val: u8) -> u64 { val as u64 }
    pub fn u16_to_reg(val: u16) -> u64 { val as u64 }
    pub fn u32_to_reg(val: u32) -> u64 { val as u64 }
    pub fn u64_to_reg(val: u64) -> u64 { val }
}

/// Trait used to streamline operations on primitive types.
pub trait PrimitiveInteger: Copy {
    fn from_reg(reg: u64) -> Self;
    fn into_reg(self) -> u64;

    fn checked_div(self, rhs: Self) -> Result<Self, InterpretationError>;
    fn checked_rem(self, rhs: Self) -> Result<Self, InterpretationError>;
}
macro_rules! impl_primitive_integer_for {
    ( $( ($type:ty, $reg_to_val:ident, $val_to_reg:ident) ),* $(,)? ) => {
        $(
            impl PrimitiveInteger for $type {
                fn from_reg(reg: u64) -> Self { conv::$reg_to_val(reg) }
                fn into_reg(self) -> u64 { conv::$val_to_reg(self) }

                fn checked_div(self, rhs: Self) -> Result<Self, InterpretationError> {
                    self.checked_div(rhs).ok_or(InterpretationError::DivisionByZero)
                }
                fn checked_rem(self, rhs: Self) -> Result<Self, InterpretationError> {
                    self.checked_div(rhs).ok_or(InterpretationError::DivisionByZero)
                }
            }
        )*
    };
}
impl_primitive_integer_for! {
    ( i8, reg_to_i8 , i8_to_reg ),
    (i16, reg_to_i16, i16_to_reg),
    (i32, reg_to_i32, i32_to_reg),
    (i64, reg_to_i64, i64_to_reg),
    ( u8, reg_to_u8 , u8_to_reg ),
    (u16, reg_to_u16, u16_to_reg),
    (u32, reg_to_u32, u32_to_reg),
    (u64, reg_to_u64, u64_to_reg),
}

impl InterpretInstr for BinaryIntInstr {
    fn interpret_instr(
        &self,
        return_value: Option<Value>,
        _ctx: &mut EvaluationContext,
        frame: &mut FunctionFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let return_value = return_value.expect(MISSING_RETURN_VALUE_ERRSTR);
        let lhs = frame.read_register(self.lhs());
        let rhs = frame.read_register(self.rhs());
        use core::ops::{BitAnd, BitOr, BitXor};
        use BinaryIntOp as Op;
        use IntType::{I16, I32, I64, I8};
        fn compute<T, F>(lhs: u64, rhs: u64, f: F) -> u64
        where
            T: PrimitiveInteger,
            F: FnOnce(T, T) -> T,
        {
            f(T::from_reg(lhs), T::from_reg(rhs)).into_reg()
        }
        fn compute_checked<T, F>(
            lhs: u64,
            rhs: u64,
            f: F,
        ) -> Result<u64, InterpretationError>
        where
            T: PrimitiveInteger,
            F: FnOnce(T, T) -> Result<T, InterpretationError>,
        {
            Ok(f(T::from_reg(lhs), T::from_reg(rhs))?.into_reg())
        }
        fn compute_shift<T, F>(lhs: u64, rhs: u64, f: F) -> u64
        where
            T: PrimitiveInteger,
            F: FnOnce(T, u32) -> T,
        {
            f(T::from_reg(lhs), rhs as u32).into_reg()
        }
        let result = match (self.op(), self.ty()) {
            (Op::Add, I8) => compute(lhs, rhs, u8::wrapping_add),
            (Op::Add, I16) => compute(lhs, rhs, u16::wrapping_add),
            (Op::Add, I32) => compute(lhs, rhs, u32::wrapping_add),
            (Op::Add, I64) => compute(lhs, rhs, u64::wrapping_add),
            (Op::Sub, I8) => compute(lhs, rhs, u8::wrapping_sub),
            (Op::Sub, I16) => compute(lhs, rhs, u16::wrapping_sub),
            (Op::Sub, I32) => compute(lhs, rhs, u32::wrapping_sub),
            (Op::Sub, I64) => compute(lhs, rhs, u64::wrapping_sub),
            (Op::Mul, I8) => compute(lhs, rhs, u8::wrapping_mul),
            (Op::Mul, I16) => compute(lhs, rhs, u16::wrapping_mul),
            (Op::Mul, I32) => compute(lhs, rhs, u32::wrapping_mul),
            (Op::Mul, I64) => compute(lhs, rhs, u64::wrapping_mul),
            (Op::Sdiv, I8) => {
                compute_checked(
                    lhs,
                    rhs,
                    <i8 as PrimitiveInteger>::checked_div,
                )?
            }
            (Op::Sdiv, I16) => {
                compute_checked(
                    lhs,
                    rhs,
                    <i16 as PrimitiveInteger>::checked_div,
                )?
            }
            (Op::Sdiv, I32) => {
                compute_checked(
                    lhs,
                    rhs,
                    <i32 as PrimitiveInteger>::checked_div,
                )?
            }
            (Op::Sdiv, I64) => {
                compute_checked(
                    lhs,
                    rhs,
                    <i64 as PrimitiveInteger>::checked_div,
                )?
            }
            (Op::Udiv, I8) => {
                compute_checked(
                    lhs,
                    rhs,
                    <u8 as PrimitiveInteger>::checked_div,
                )?
            }
            (Op::Udiv, I16) => {
                compute_checked(
                    lhs,
                    rhs,
                    <u16 as PrimitiveInteger>::checked_div,
                )?
            }
            (Op::Udiv, I32) => {
                compute_checked(
                    lhs,
                    rhs,
                    <u32 as PrimitiveInteger>::checked_div,
                )?
            }
            (Op::Udiv, I64) => {
                compute_checked(
                    lhs,
                    rhs,
                    <u64 as PrimitiveInteger>::checked_div,
                )?
            }
            (Op::Srem, I8) => {
                compute_checked(
                    lhs,
                    rhs,
                    <i8 as PrimitiveInteger>::checked_rem,
                )?
            }
            (Op::Srem, I16) => {
                compute_checked(
                    lhs,
                    rhs,
                    <i16 as PrimitiveInteger>::checked_rem,
                )?
            }
            (Op::Srem, I32) => {
                compute_checked(
                    lhs,
                    rhs,
                    <i32 as PrimitiveInteger>::checked_rem,
                )?
            }
            (Op::Srem, I64) => {
                compute_checked(
                    lhs,
                    rhs,
                    <i64 as PrimitiveInteger>::checked_rem,
                )?
            }
            (Op::Urem, I8) => {
                compute_checked(
                    lhs,
                    rhs,
                    <u8 as PrimitiveInteger>::checked_rem,
                )?
            }
            (Op::Urem, I16) => {
                compute_checked(
                    lhs,
                    rhs,
                    <u16 as PrimitiveInteger>::checked_rem,
                )?
            }
            (Op::Urem, I32) => {
                compute_checked(
                    lhs,
                    rhs,
                    <u32 as PrimitiveInteger>::checked_rem,
                )?
            }
            (Op::Urem, I64) => {
                compute_checked(
                    lhs,
                    rhs,
                    <u64 as PrimitiveInteger>::checked_rem,
                )?
            }
            (Op::And, I8) => compute(lhs, rhs, u8::bitand),
            (Op::And, I16) => compute(lhs, rhs, u16::bitand),
            (Op::And, I32) => compute(lhs, rhs, u32::bitand),
            (Op::And, I64) => compute(lhs, rhs, u64::bitand),
            (Op::Or, I8) => compute(lhs, rhs, u8::bitor),
            (Op::Or, I16) => compute(lhs, rhs, u16::bitor),
            (Op::Or, I32) => compute(lhs, rhs, u32::bitor),
            (Op::Or, I64) => compute(lhs, rhs, u64::bitor),
            (Op::Xor, I8) => compute(lhs, rhs, u8::bitxor),
            (Op::Xor, I16) => compute(lhs, rhs, u16::bitxor),
            (Op::Xor, I32) => compute(lhs, rhs, u32::bitxor),
            (Op::Xor, I64) => compute(lhs, rhs, u64::bitxor),
            (Op::Shl, I8) => compute_shift(lhs, rhs, u8::wrapping_shl),
            (Op::Shl, I16) => compute_shift(lhs, rhs, u16::wrapping_shl),
            (Op::Shl, I32) => compute_shift(lhs, rhs, u32::wrapping_shl),
            (Op::Shl, I64) => compute_shift(lhs, rhs, u64::wrapping_shl),
            (Op::Sshr, I8) => compute_shift(lhs, rhs, i8::wrapping_shr),
            (Op::Sshr, I16) => compute_shift(lhs, rhs, i16::wrapping_shr),
            (Op::Sshr, I32) => compute_shift(lhs, rhs, i32::wrapping_shr),
            (Op::Sshr, I64) => compute_shift(lhs, rhs, i64::wrapping_shr),
            (Op::Ushr, I8) => compute_shift(lhs, rhs, u8::wrapping_shr),
            (Op::Ushr, I16) => compute_shift(lhs, rhs, u16::wrapping_shr),
            (Op::Ushr, I32) => compute_shift(lhs, rhs, u32::wrapping_shr),
            (Op::Ushr, I64) => compute_shift(lhs, rhs, u64::wrapping_shr),
            (Op::Rotl, I8) => compute_shift(lhs, rhs, u8::rotate_left),
            (Op::Rotl, I16) => compute_shift(lhs, rhs, u16::rotate_left),
            (Op::Rotl, I32) => compute_shift(lhs, rhs, u32::rotate_left),
            (Op::Rotl, I64) => compute_shift(lhs, rhs, u64::rotate_left),
            (Op::Rotr, I8) => compute_shift(lhs, rhs, u8::rotate_right),
            (Op::Rotr, I16) => compute_shift(lhs, rhs, u16::rotate_right),
            (Op::Rotr, I32) => compute_shift(lhs, rhs, u32::rotate_right),
            (Op::Rotr, I64) => compute_shift(lhs, rhs, u64::rotate_right),
        };
        frame.write_register(return_value, result);
        Ok(InterpretationFlow::Continue)
    }
}
