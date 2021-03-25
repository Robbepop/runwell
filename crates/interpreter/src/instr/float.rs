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
    InterpretInstr,
    InterpretationError,
    InterpretationFlow,
    PrimitiveInteger,
    I1,
};
use crate::core::ActivationFrame;
use ir::{
    instr::{
        operands::{BinaryFloatOp, CompareFloatOp, UnaryFloatOp},
        BinaryFloatInstr,
        CompareFloatInstr,
        DemoteFloatInstr,
        FloatInstr,
        FloatToIntInstr,
        PromoteFloatInstr,
        UnaryFloatInstr,
    },
    primitive::{FloatType, IntType, Value},
};

impl InterpretInstr for FloatInstr {
    fn interpret_instr(
        &self,
        outputs: &[Option<Value>],
        frame: ActivationFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        match self {
            FloatInstr::Binary(instr) => instr.interpret_instr(outputs, frame),
            FloatInstr::Compare(instr) => instr.interpret_instr(outputs, frame),
            FloatInstr::Demote(instr) => instr.interpret_instr(outputs, frame),
            FloatInstr::FloatToInt(instr) => {
                instr.interpret_instr(outputs, frame)
            }
            FloatInstr::Promote(instr) => instr.interpret_instr(outputs, frame),
            FloatInstr::Unary(instr) => instr.interpret_instr(outputs, frame),
        }
    }
}

/// Converts the register `u64` bits into a `f32` float.
fn reg_f32(reg: u64) -> f32 {
    f32::from_bits(reg as u32)
}

/// Converts the `f32` into a `u64` bits register.
fn f32_reg(float: f32) -> u64 {
    float.to_bits() as u64
}

/// Converts the register `u64` bits into a `f64` float.
fn reg_f64(reg: u64) -> f64 {
    f64::from_bits(reg)
}

/// Converts the `f64` into a `u64` bits register.
fn f64_reg(float: f64) -> u64 {
    float.to_bits()
}

impl InterpretInstr for DemoteFloatInstr {
    fn interpret_instr(
        &self,
        outputs: &[Option<Value>],
        mut frame: ActivationFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let return_value = extract_single_output_or_skip!(outputs);
        let source = frame.read_register(self.src());
        assert!(self.dst_type().bit_width() <= self.src_type().bit_width());
        let result = match (self.src_type(), self.dst_type()) {
            (FloatType::F64, FloatType::F32) => f32_reg(reg_f64(source) as f32),
            _ => source,
        };
        frame.write_register(return_value, result);
        Ok(InterpretationFlow::Continue)
    }
}

impl InterpretInstr for PromoteFloatInstr {
    fn interpret_instr(
        &self,
        outputs: &[Option<Value>],
        mut frame: ActivationFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let return_value = extract_single_output_or_skip!(outputs);
        let source = frame.read_register(self.src());
        assert!(self.src_type().bit_width() <= self.dst_type().bit_width());
        let result = match (self.src_type(), self.dst_type()) {
            (FloatType::F32, FloatType::F64) => f64_reg(reg_f32(source) as f64),
            _ => source,
        };
        frame.write_register(return_value, result);
        Ok(InterpretationFlow::Continue)
    }
}

impl InterpretInstr for CompareFloatInstr {
    fn interpret_instr(
        &self,
        outputs: &[Option<Value>],
        mut frame: ActivationFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let return_value = extract_single_output_or_skip!(outputs);
        let lhs = frame.read_register(self.lhs());
        let rhs = frame.read_register(self.rhs());
        use CompareFloatOp as Op;
        use FloatType::{F32, F64};
        fn operate_f32<F>(lhs: u64, rhs: u64, op: F) -> u64
        where
            F: FnOnce(&f32, &f32) -> bool,
        {
            let lhs = reg_f32(lhs);
            let rhs = reg_f32(rhs);
            op(&lhs, &rhs) as u64
        }
        fn operate_f64<F>(lhs: u64, rhs: u64, op: F) -> u64
        where
            F: FnOnce(&f64, &f64) -> bool,
        {
            let lhs = reg_f64(lhs);
            let rhs = reg_f64(rhs);
            op(&lhs, &rhs) as u64
        }
        let result = match (self.ty(), self.op()) {
            (F32, Op::Eq) => operate_f32(lhs, rhs, f32::eq),
            (F64, Op::Eq) => operate_f64(lhs, rhs, f64::eq),
            (F32, Op::Ne) => operate_f32(lhs, rhs, f32::ne),
            (F64, Op::Ne) => operate_f64(lhs, rhs, f64::ne),
            (F32, Op::Le) => operate_f32(lhs, rhs, f32::le),
            (F64, Op::Le) => operate_f64(lhs, rhs, f64::le),
            (F32, Op::Lt) => operate_f32(lhs, rhs, f32::lt),
            (F64, Op::Lt) => operate_f64(lhs, rhs, f64::lt),
            (F32, Op::Ge) => operate_f32(lhs, rhs, f32::ge),
            (F64, Op::Ge) => operate_f64(lhs, rhs, f64::ge),
            (F32, Op::Gt) => operate_f32(lhs, rhs, f32::gt),
            (F64, Op::Gt) => operate_f64(lhs, rhs, f64::gt),
        };
        frame.write_register(return_value, result);
        Ok(InterpretationFlow::Continue)
    }
}

impl InterpretInstr for BinaryFloatInstr {
    fn interpret_instr(
        &self,
        outputs: &[Option<Value>],
        mut frame: ActivationFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let return_value = extract_single_output_or_skip!(outputs);
        let lhs = frame.read_register(self.lhs());
        let rhs = frame.read_register(self.rhs());
        use core::ops::{Add, Div, Mul, Sub};
        use BinaryFloatOp as Op;
        use FloatType::{F32, F64};
        fn operate_f32<F>(lhs: u64, rhs: u64, op: F) -> u64
        where
            F: FnOnce(f32, f32) -> f32,
        {
            let lhs = reg_f32(lhs);
            let rhs = reg_f32(rhs);
            f32_reg(op(lhs, rhs))
        }
        fn operate_f64<F>(lhs: u64, rhs: u64, op: F) -> u64
        where
            F: FnOnce(f64, f64) -> f64,
        {
            let lhs = reg_f64(lhs);
            let rhs = reg_f64(rhs);
            f64_reg(op(lhs, rhs))
        }
        let result = match (self.ty(), self.op()) {
            (F32, Op::Add) => operate_f32(lhs, rhs, f32::add),
            (F64, Op::Add) => operate_f64(lhs, rhs, f64::add),
            (F32, Op::Sub) => operate_f32(lhs, rhs, f32::sub),
            (F64, Op::Sub) => operate_f64(lhs, rhs, f64::sub),
            (F32, Op::Mul) => operate_f32(lhs, rhs, f32::mul),
            (F64, Op::Mul) => operate_f64(lhs, rhs, f64::mul),
            (F32, Op::Div) => {
                let lhs = reg_f32(lhs);
                let rhs = reg_f32(rhs);
                if rhs.abs() == 0.0 {
                    return Err(InterpretationError::DivisionByZero)
                }
                f32_reg(f32::div(lhs, rhs))
            }
            (F64, Op::Div) => {
                let lhs = reg_f64(lhs);
                let rhs = reg_f64(rhs);
                if rhs.abs() == 0.0 {
                    return Err(InterpretationError::DivisionByZero)
                }
                f64_reg(f64::div(lhs, rhs))
            }
            (F32, Op::Min) => operate_f32(lhs, rhs, f32::min),
            (F64, Op::Min) => operate_f64(lhs, rhs, f64::min),
            (F32, Op::Max) => operate_f32(lhs, rhs, f32::max),
            (F64, Op::Max) => operate_f64(lhs, rhs, f64::max),
            (F32, Op::CopySign) => operate_f32(lhs, rhs, f32::copysign),
            (F64, Op::CopySign) => operate_f64(lhs, rhs, f64::copysign),
        };
        frame.write_register(return_value, result);
        Ok(InterpretationFlow::Continue)
    }
}

impl InterpretInstr for UnaryFloatInstr {
    fn interpret_instr(
        &self,
        outputs: &[Option<Value>],
        mut frame: ActivationFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let return_value = extract_single_output_or_skip!(outputs);
        let source = frame.read_register(self.src());
        use FloatType::{F32, F64};
        use UnaryFloatOp as Op;
        fn operate_f32<F>(reg: u64, op: F) -> u64
        where
            F: FnOnce(f32) -> f32,
        {
            f32_reg(op(reg_f32(reg)))
        }
        fn operate_f64<F>(reg: u64, op: F) -> u64
        where
            F: FnOnce(f64) -> f64,
        {
            f64_reg(op(reg_f64(reg)))
        }
        use core::ops::Neg;
        let result = match (self.ty(), self.op()) {
            (F32, Op::Abs) => operate_f32(source, f32::abs),
            (F64, Op::Abs) => operate_f64(source, f64::abs),
            (F32, Op::Neg) => operate_f32(source, f32::neg),
            (F64, Op::Neg) => operate_f64(source, f64::neg),
            (F32, Op::Sqrt) => operate_f32(source, f32::sqrt),
            (F64, Op::Sqrt) => operate_f64(source, f64::sqrt),
            (F32, Op::Ceil) => operate_f32(source, f32::ceil),
            (F64, Op::Ceil) => operate_f64(source, f64::ceil),
            (F32, Op::Floor) => operate_f32(source, f32::floor),
            (F64, Op::Floor) => operate_f64(source, f64::floor),
            (F32, Op::Truncate) => operate_f32(source, f32::trunc),
            (F64, Op::Truncate) => operate_f64(source, f64::trunc),
            (F32, Op::Nearest) => operate_f32(source, f32::round),
            (F64, Op::Nearest) => operate_f64(source, f64::round),
        };
        frame.write_register(return_value, result);
        Ok(InterpretationFlow::Continue)
    }
}

impl InterpretInstr for FloatToIntInstr {
    /// WebAssembly instructions that map to `FloatTotIntInstr`:
    ///
    /// `f32` conversion to `i32` and `i64`:
    ///  - `f32.convert_i32_s`
    ///  - `f32.convert_i32_u`
    ///  - `f32.convert_i64_s`
    ///  - `f32.convert_i64_u`
    ///
    /// `f64` conversion to `i32` and `i64`:
    ///  - `f64.convert_i32_s`
    ///  - `f64.convert_i32_u`
    ///  - `f64.convert_i64_s`
    ///  - `f64.convert_i64_u`
    fn interpret_instr(
        &self,
        outputs: &[Option<Value>],
        mut frame: ActivationFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let return_value = extract_single_output_or_skip!(outputs);
        let source = frame.read_register(self.src());
        use FloatType::{F32, F64};
        use IntType::{I1, I16, I32, I64, I8};
        let result = match (self.is_signed(), self.src_type(), self.dst_type())
        {
            // f32 -> uN
            (false, F32, I1) => {
                self::I1::from_reg(reg_f32(source) as u64).into_reg()
            }
            (false, F32, I8) => reg_f32(source) as u8 as u64,
            (false, F32, I16) => reg_f32(source) as u16 as u64,
            (false, F32, I32) => reg_f32(source) as u32 as u64,
            (false, F32, I64) => reg_f32(source) as u64,
            // f64 -> uN
            (false, F64, I1) => {
                self::I1::from_reg(reg_f64(source) as u64).into_reg()
            }
            (false, F64, I8) => reg_f64(source) as u8 as u64,
            (false, F64, I16) => reg_f64(source) as u16 as u64,
            (false, F64, I32) => reg_f64(source) as u32 as u64,
            (false, F64, I64) => reg_f64(source) as u64,
            // f32 -> iN
            (true, F32, I1) => {
                self::I1::new((reg_f32(source) as i64).is_negative()).into_reg()
            }
            (true, F32, I8) => reg_f32(source) as i8 as u8 as u64,
            (true, F32, I16) => reg_f32(source) as i16 as u16 as u64,
            (true, F32, I32) => reg_f32(source) as i32 as u32 as u64,
            (true, F32, I64) => reg_f32(source) as i64 as u64,
            // f64 -> iN
            (true, F64, I1) => {
                self::I1::new((reg_f64(source) as i64).is_negative()).into_reg()
            }
            (true, F64, I8) => reg_f64(source) as i8 as u8 as u64,
            (true, F64, I16) => reg_f64(source) as i16 as u16 as u64,
            (true, F64, I32) => reg_f64(source) as i32 as u32 as u64,
            (true, F64, I64) => reg_f64(source) as i64 as u64,
        };
        frame.write_register(return_value, result as u64);
        Ok(InterpretationFlow::Continue)
    }
}
