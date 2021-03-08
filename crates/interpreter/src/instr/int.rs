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
    extract_single_output,
    InterpretInstr,
    InterpretationError,
    InterpretationFlow,
    PrimitiveInteger,
    PrimitiveIntegerDivision,
    I1,
};
use crate::core::ActivationFrame;
use ir::{
    instr::{
        operands::{BinaryIntOp, CompareIntOp, ShiftIntOp, UnaryIntOp},
        BinaryIntInstr,
        CompareIntInstr,
        ExtendIntInstr,
        IntInstr,
        IntToFloatInstr,
        ShiftIntInstr,
        TruncateIntInstr,
        UnaryIntInstr,
    },
    primitive::{FloatType, IntType, Value},
};

impl InterpretInstr for IntInstr {
    fn interpret_instr(
        &self,
        outputs: &[Option<Value>],
        frame: ActivationFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        match self {
            Self::Binary(instr) => instr.interpret_instr(outputs, frame),
            Self::Unary(instr) => instr.interpret_instr(outputs, frame),
            Self::Compare(instr) => instr.interpret_instr(outputs, frame),
            Self::Extend(instr) => instr.interpret_instr(outputs, frame),
            Self::IntToFloat(instr) => instr.interpret_instr(outputs, frame),
            Self::Truncate(instr) => instr.interpret_instr(outputs, frame),
            Self::Shift(instr) => instr.interpret_instr(outputs, frame),
        }
    }
}

impl InterpretInstr for UnaryIntInstr {
    fn interpret_instr(
        &self,
        outputs: &[Option<Value>],
        mut frame: ActivationFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let return_value = extract_single_output(outputs);
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
        outputs: &[Option<Value>],
        mut frame: ActivationFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let return_value = extract_single_output(outputs);
        let source = frame.read_register(self.src());
        debug_assert!(
            self.dst_type().bit_width() <= self.src_type().bit_width()
        );
        fn mask(bits: u32) -> u64 {
            (0x1 << bits) - 1
        }
        let result = match self.dst_type() {
            IntType::I64 => source,
            int_ty => source & mask(int_ty.bit_width()),
        };
        frame.write_register(return_value, result as u64);
        Ok(InterpretationFlow::Continue)
    }
}

impl InterpretInstr for ExtendIntInstr {
    fn interpret_instr(
        &self,
        outputs: &[Option<Value>],
        mut frame: ActivationFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let return_value = extract_single_output(outputs);
        let source = frame.read_register(self.src());
        debug_assert!(
            self.src_type().bit_width() <= self.dst_type().bit_width()
        );
        use IntType::{I1, I16, I32, I64, I8};
        let result = if self.is_signed() {
            match (self.src_type(), self.dst_type()) {
                (I1, I8) => self::I1::from_reg(source).extend_to_i8() as u64,
                (I1, I16) => self::I1::from_reg(source).extend_to_i16() as u64,
                (I1, I32) => self::I1::from_reg(source).extend_to_i32() as u64,
                (I1, I64) => self::I1::from_reg(source).extend_to_i64() as u64,
                (I8, I16) => source as u8 as i8 as i16 as u16 as u64,
                (I8, I32) => source as u8 as i8 as i32 as u32 as u64,
                (I8, I64) => source as u8 as i8 as i64 as u64,
                (I16, I32) => source as u16 as i16 as i32 as u32 as u64,
                (I16, I64) => source as u16 as i16 as i64 as u64,
                (I32, I64) => source as u32 as i32 as i64 as u64,
                (x, y) if x == y => source,
                _ => unreachable!("encountered invalid integer extension"),
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
    /// WebAssembly instructions that map to `IntToFloatInstr`:
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
        outputs: &[Option<Value>],
        mut frame: ActivationFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let return_value = extract_single_output(outputs);
        let source = frame.read_register(self.src());
        use FloatType::{F32, F64};
        use IntType::{I1, I16, I32, I64, I8};
        let result = match (self.is_signed(), self.src_type(), self.dst_type())
        {
            // uN -> f32
            (false, I1, F32) => ((source != 0) as u8 as f32).to_bits() as u64,
            (false, I8, F32) => (source as u8 as f32).to_bits() as u64,
            (false, I16, F32) => (source as u16 as f32).to_bits() as u64,
            (false, I32, F32) => (source as u32 as f32).to_bits() as u64,
            (false, I64, F32) => (source as u64 as f32).to_bits() as u64,
            // uN -> f64
            (false, I1, F64) => ((source != 0) as u8 as f64).to_bits() as u64,
            (false, I8, F64) => (source as u8 as f64).to_bits(),
            (false, I16, F64) => (source as u16 as f64).to_bits(),
            (false, I32, F64) => (source as u32 as f64).to_bits(),
            (false, I64, F64) => (source as u64 as f64).to_bits(),
            // iN -> f32
            (true, I1, F32) => {
                (self::I1::from_reg(source).extend_to_i8() as f32).to_bits()
                    as u64
            }
            (true, I8, F32) => (source as u8 as i8 as f32).to_bits() as u64,
            (true, I16, F32) => (source as u16 as i16 as f32).to_bits() as u64,
            (true, I32, F32) => (source as u32 as i32 as f32).to_bits() as u64,
            (true, I64, F32) => (source as u64 as i64 as f32).to_bits() as u64,
            // iN -> f64
            (true, I1, F64) => {
                (self::I1::from_reg(source).extend_to_i8() as f64).to_bits()
            }
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
        outputs: &[Option<Value>],
        mut frame: ActivationFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let return_value = extract_single_output(outputs);
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
            IntType::I1 => {
                let lhs = I1::from_reg(lhs);
                let rhs = I1::from_reg(rhs);
                match self.op() {
                    Op::Eq => I1::new(lhs == rhs).into_reg(),
                    Op::Ne => I1::new(lhs != rhs).into_reg(),
                    undefined => {
                        unimplemented!(
                            "{} comparison between I1 values is undefined",
                            undefined,
                        )
                    }
                }
            }
            IntType::I8 => {
                let lhs = u8::from_reg(lhs);
                let rhs = u8::from_reg(rhs);
                cmp(self.op(), lhs, rhs, |lhs| lhs as i8)
            }
            IntType::I16 => {
                let lhs = u16::from_reg(lhs);
                let rhs = u16::from_reg(rhs);
                cmp(self.op(), lhs, rhs, |lhs| lhs as i16)
            }
            IntType::I32 => {
                let lhs = u32::from_reg(lhs);
                let rhs = u32::from_reg(rhs);
                cmp(self.op(), lhs, rhs, |lhs| lhs as i32)
            }
            IntType::I64 => cmp(self.op(), lhs, rhs, |lhs| lhs as i64),
        };
        frame.write_register(return_value, result);
        Ok(InterpretationFlow::Continue)
    }
}

impl InterpretInstr for ShiftIntInstr {
    fn interpret_instr(
        &self,
        outputs: &[Option<Value>],
        mut frame: ActivationFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let return_value = extract_single_output(outputs);
        let src = frame.read_register(self.source());
        let shamt = frame.read_register(self.shift_amount());
        fn eval_shift<T, F>(lhs: u64, rhs: u64, f: F) -> u64
        where
            T: PrimitiveInteger,
            F: FnOnce(T, u32) -> T,
        {
            f(T::from_reg(lhs), rhs as u32).into_reg()
        }
        use IntType::{I1, I16, I32, I64, I8};
        use ShiftIntOp::*;
        let result = match (self.op(), self.ty()) {
            (_, I1) => {
                unimplemented!("shift operations are undefined for I1 types")
            }
            (Shl, I8) => eval_shift(src, shamt, u8::wrapping_shl),
            (Shl, I16) => eval_shift(src, shamt, u16::wrapping_shl),
            (Shl, I32) => eval_shift(src, shamt, u32::wrapping_shl),
            (Shl, I64) => eval_shift(src, shamt, u64::wrapping_shl),
            (Sshr, I8) => eval_shift(src, shamt, i8::wrapping_shr),
            (Sshr, I16) => eval_shift(src, shamt, i16::wrapping_shr),
            (Sshr, I32) => eval_shift(src, shamt, i32::wrapping_shr),
            (Sshr, I64) => eval_shift(src, shamt, i64::wrapping_shr),
            (Ushr, I8) => eval_shift(src, shamt, u8::wrapping_shr),
            (Ushr, I16) => eval_shift(src, shamt, u16::wrapping_shr),
            (Ushr, I32) => eval_shift(src, shamt, u32::wrapping_shr),
            (Ushr, I64) => eval_shift(src, shamt, u64::wrapping_shr),
            (Rotl, I8) => eval_shift(src, shamt, u8::rotate_left),
            (Rotl, I16) => eval_shift(src, shamt, u16::rotate_left),
            (Rotl, I32) => eval_shift(src, shamt, u32::rotate_left),
            (Rotl, I64) => eval_shift(src, shamt, u64::rotate_left),
            (Rotr, I8) => eval_shift(src, shamt, u8::rotate_right),
            (Rotr, I16) => eval_shift(src, shamt, u16::rotate_right),
            (Rotr, I32) => eval_shift(src, shamt, u32::rotate_right),
            (Rotr, I64) => eval_shift(src, shamt, u64::rotate_right),
        };
        frame.write_register(return_value, result);
        Ok(InterpretationFlow::Continue)
    }
}

impl InterpretInstr for BinaryIntInstr {
    fn interpret_instr(
        &self,
        outputs: &[Option<Value>],
        mut frame: ActivationFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let return_value = extract_single_output(outputs);
        let lhs = frame.read_register(self.lhs());
        let rhs = frame.read_register(self.rhs());
        use core::ops::{BitAnd, BitOr, BitXor};
        use BinaryIntOp::*;
        use IntType::{I1, I16, I32, I64, I8};
        use PrimitiveIntegerDivision as PrimDiv;
        fn eval<T, F>(lhs: u64, rhs: u64, f: F) -> u64
        where
            T: PrimitiveInteger,
            F: FnOnce(T, T) -> T,
        {
            f(T::from_reg(lhs), T::from_reg(rhs)).into_reg()
        }
        fn eval_div<T, F>(
            lhs: u64,
            rhs: u64,
            f: F,
        ) -> Result<u64, InterpretationError>
        where
            T: PrimitiveIntegerDivision,
            F: FnOnce(T, T) -> Result<T, InterpretationError>,
        {
            Ok(f(T::from_reg(lhs), T::from_reg(rhs))?.into_reg())
        }
        let result = match (self.op(), self.ty()) {
            (And, I1) => eval(lhs, rhs, self::I1::bitand),
            (And, I8) => eval(lhs, rhs, u8::bitand),
            (And, I16) => eval(lhs, rhs, u16::bitand),
            (And, I32) => eval(lhs, rhs, u32::bitand),
            (And, I64) => eval(lhs, rhs, u64::bitand),
            (Or, I1) => eval(lhs, rhs, self::I1::bitor),
            (Or, I8) => eval(lhs, rhs, u8::bitor),
            (Or, I16) => eval(lhs, rhs, u16::bitor),
            (Or, I32) => eval(lhs, rhs, u32::bitor),
            (Or, I64) => eval(lhs, rhs, u64::bitor),
            (Xor, I1) => eval(lhs, rhs, self::I1::bitxor),
            (Xor, I8) => eval(lhs, rhs, u8::bitxor),
            (Xor, I16) => eval(lhs, rhs, u16::bitxor),
            (Xor, I32) => eval(lhs, rhs, u32::bitxor),
            (Xor, I64) => eval(lhs, rhs, u64::bitxor),
            (op, I1) => {
                unimplemented!(
                    "binary integer operator {} is not defined on I1 types",
                    op
                )
            }
            (Add, I8) => eval(lhs, rhs, u8::wrapping_add),
            (Add, I16) => eval(lhs, rhs, u16::wrapping_add),
            (Add, I32) => eval(lhs, rhs, u32::wrapping_add),
            (Add, I64) => eval(lhs, rhs, u64::wrapping_add),
            (Sub, I8) => eval(lhs, rhs, u8::wrapping_sub),
            (Sub, I16) => eval(lhs, rhs, u16::wrapping_sub),
            (Sub, I32) => eval(lhs, rhs, u32::wrapping_sub),
            (Sub, I64) => eval(lhs, rhs, u64::wrapping_sub),
            (Mul, I8) => eval(lhs, rhs, u8::wrapping_mul),
            (Mul, I16) => eval(lhs, rhs, u16::wrapping_mul),
            (Mul, I32) => eval(lhs, rhs, u32::wrapping_mul),
            (Mul, I64) => eval(lhs, rhs, u64::wrapping_mul),
            (Sdiv, I8) => eval_div(lhs, rhs, <i8 as PrimDiv>::checked_div)?,
            (Sdiv, I16) => eval_div(lhs, rhs, <i16 as PrimDiv>::checked_div)?,
            (Sdiv, I32) => eval_div(lhs, rhs, <i32 as PrimDiv>::checked_div)?,
            (Sdiv, I64) => eval_div(lhs, rhs, <i64 as PrimDiv>::checked_div)?,
            (Udiv, I8) => eval_div(lhs, rhs, <u8 as PrimDiv>::checked_div)?,
            (Udiv, I16) => eval_div(lhs, rhs, <u16 as PrimDiv>::checked_div)?,
            (Udiv, I32) => eval_div(lhs, rhs, <u32 as PrimDiv>::checked_div)?,
            (Udiv, I64) => eval_div(lhs, rhs, <u64 as PrimDiv>::checked_div)?,
            (Srem, I8) => eval_div(lhs, rhs, <i8 as PrimDiv>::checked_rem)?,
            (Srem, I16) => eval_div(lhs, rhs, <i16 as PrimDiv>::checked_rem)?,
            (Srem, I32) => eval_div(lhs, rhs, <i32 as PrimDiv>::checked_rem)?,
            (Srem, I64) => eval_div(lhs, rhs, <i64 as PrimDiv>::checked_rem)?,
            (Urem, I8) => eval_div(lhs, rhs, <u8 as PrimDiv>::checked_rem)?,
            (Urem, I16) => eval_div(lhs, rhs, <u16 as PrimDiv>::checked_rem)?,
            (Urem, I32) => eval_div(lhs, rhs, <u32 as PrimDiv>::checked_rem)?,
            (Urem, I64) => eval_div(lhs, rhs, <u64 as PrimDiv>::checked_rem)?,
        };
        frame.write_register(return_value, result);
        Ok(InterpretationFlow::Continue)
    }
}
