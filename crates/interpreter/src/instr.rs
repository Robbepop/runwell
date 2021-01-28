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

use super::{EvaluationContext, Func, FunctionFrame, InterpretationError};
use core::mem::replace;
use entity::RawIdx;
use ir::{
    builder::Function,
    instr::{
        operands::{
            BinaryFloatOp,
            BinaryIntOp,
            CompareIntOp,
            UnaryFloatOp,
            UnaryIntOp,
        },
        BinaryFloatInstr,
        BinaryIntInstr,
        BranchInstr,
        CallInstr,
        CompareIntInstr,
        ConstInstr,
        ExtendIntInstr,
        FloatInstr,
        FloatToIntInstr,
        IfThenElseInstr,
        Instruction,
        IntInstr,
        IntToFloatInstr,
        PhiInstr,
        ReinterpretInstr,
        ReturnInstr,
        SelectInstr,
        TailCallInstr,
        TerminalInstr,
        TruncateIntInstr,
        UnaryFloatInstr,
        UnaryIntInstr,
    },
    primitive::{FloatType, IntType, Value},
};

/// Implemented by Runwell IR instructions to make them interpretable.
pub trait InterpretInstr {
    /// Evaluates the function given the interpretation context.
    fn interpret_instr(
        &self,
        return_value: Option<Value>,
        ctx: &mut EvaluationContext,
        frame: &mut FunctionFrame,
    ) -> Result<InterpretationFlow, InterpretationError>;
}

impl InterpretInstr for Function {
    fn interpret_instr(
        &self,
        _return_value: Option<Value>,
        ctx: &mut EvaluationContext,
        frame: &mut FunctionFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let block = frame.current_block();
        let ic = frame.bump_instruction_counter();
        let (instr_value, instruction) = self
            .instruction_and_value(block, ic)
            .expect("missing instruction in function");
        instruction.interpret_instr(instr_value, ctx, frame)
    }
}

/// Return the status of evaluating a Runwell IR instruction.
///
/// Guides the evaluation context into what to do next.
#[derive(Debug, Copy, Clone)]
pub enum InterpretationFlow {
    /// Continues evaluation of instructions.
    Continue,
    /// The function has returned.
    Return,
    /// The function returns a call to another function.
    ///
    /// In this case the registers are assumed to be prefilled
    /// with the functions inputs. The outer evaluation context
    /// then has to check the aquired inputs against the called
    /// function signature.
    TailCall(Func),
}

const MISSING_RETURN_VALUE_ERRSTR: &str =
    "missing return value for returning instruction";

impl InterpretInstr for Instruction {
    fn interpret_instr(
        &self,
        return_value: Option<Value>,
        ctx: &mut EvaluationContext,
        frame: &mut FunctionFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        match self {
            Self::Call(instr) => {
                instr.interpret_instr(return_value, ctx, frame)
            }
            Self::CallIndirect(_instr) => unimplemented!(),
            Self::Const(instr) => {
                instr.interpret_instr(return_value, ctx, frame)
            }
            Self::MemoryGrow(_instr) => unimplemented!(),
            Self::MemorySize(_instr) => unimplemented!(),
            Self::Phi(instr) => instr.interpret_instr(return_value, ctx, frame),
            Self::Load(_instr) => unimplemented!(),
            Self::Store(_instr) => unimplemented!(),
            Self::Select(instr) => {
                instr.interpret_instr(return_value, ctx, frame)
            }
            Self::Reinterpret(instr) => {
                instr.interpret_instr(return_value, ctx, frame)
            }
            Self::Terminal(instr) => {
                instr.interpret_instr(return_value, ctx, frame)
            }
            Self::Int(instr) => instr.interpret_instr(return_value, ctx, frame),
            Self::Float(instr) => instr.interpret_instr(return_value, ctx, frame),
        }
    }
}

impl InterpretInstr for PhiInstr {
    fn interpret_instr(
        &self,
        return_value: Option<Value>,
        _ctx: &mut EvaluationContext,
        frame: &mut FunctionFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let return_value = return_value.expect(MISSING_RETURN_VALUE_ERRSTR);
        let last_block = frame
            .last_block()
            .expect("phi instruction is missing predecessor");
        let result = self
            .operand_for(last_block)
            .expect("phi instruction missing value for predecessor");
        let result = frame.read_register(result);
        frame.write_register(return_value, result);
        Ok(InterpretationFlow::Continue)
    }
}

impl InterpretInstr for ConstInstr {
    fn interpret_instr(
        &self,
        return_value: Option<Value>,
        _ctx: &mut EvaluationContext,
        frame: &mut FunctionFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let return_value = return_value.expect(MISSING_RETURN_VALUE_ERRSTR);
        frame.write_register(return_value, self.const_value().into_bits64());
        Ok(InterpretationFlow::Continue)
    }
}

impl InterpretInstr for SelectInstr {
    fn interpret_instr(
        &self,
        return_value: Option<Value>,
        _ctx: &mut EvaluationContext,
        frame: &mut FunctionFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let return_value = return_value.expect(MISSING_RETURN_VALUE_ERRSTR);
        let condition = frame.read_register(self.condition());
        let result_value = if condition != 0 {
            self.true_value()
        } else {
            self.false_value()
        };
        let result = frame.read_register(result_value);
        frame.write_register(return_value, result);
        Ok(InterpretationFlow::Continue)
    }
}

impl InterpretInstr for TerminalInstr {
    fn interpret_instr(
        &self,
        return_value: Option<Value>,
        ctx: &mut EvaluationContext,
        frame: &mut FunctionFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        match self {
            Self::Trap => Err(InterpretationError::EvaluationHasTrapped),
            Self::Return(instr) => {
                instr.interpret_instr(return_value, ctx, frame)
            }
            Self::Br(instr) => instr.interpret_instr(return_value, ctx, frame),
            Self::Ite(instr) => instr.interpret_instr(return_value, ctx, frame),
            Self::TailCall(instr) => {
                instr.interpret_instr(return_value, ctx, frame)
            }
            Self::BranchTable(_instr) => unimplemented!(),
        }
    }
}

impl InterpretInstr for ReturnInstr {
    fn interpret_instr(
        &self,
        _return_value: Option<Value>,
        _ctx: &mut EvaluationContext,
        frame: &mut FunctionFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let return_value = frame.read_register(self.return_value());
        let r0 = Value::from_raw(RawIdx::from_u32(0));
        frame.write_register(r0, return_value);
        Ok(InterpretationFlow::Return)
    }
}

impl InterpretInstr for BranchInstr {
    fn interpret_instr(
        &self,
        _return_value: Option<Value>,
        _ctx: &mut EvaluationContext,
        frame: &mut FunctionFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        frame.switch_to_block(self.target());
        Ok(InterpretationFlow::Continue)
    }
}

impl InterpretInstr for IfThenElseInstr {
    fn interpret_instr(
        &self,
        _return_value: Option<Value>,
        _ctx: &mut EvaluationContext,
        frame: &mut FunctionFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let condition = frame.read_register(self.condition());
        let target = if condition != 0 {
            self.true_target()
        } else {
            self.false_target()
        };
        frame.switch_to_block(target);
        Ok(InterpretationFlow::Continue)
    }
}

impl InterpretInstr for CallInstr {
    fn interpret_instr(
        &self,
        return_value: Option<Value>,
        ctx: &mut EvaluationContext,
        frame: &mut FunctionFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let mut new_frame = ctx.create_frame();
        let function = ctx.store.get_fn(self.func());
        new_frame.initialize(
            function,
            self.params()
                .iter()
                .copied()
                .map(|param| frame.read_register(param)),
        )?;
        ctx.evaluate_function_frame(function, &mut new_frame, |result| {
            // Actually this is wrong and we ideally should write
            // the return value into `return_value` parameter.
            // However, there is only one `return_value` parameter
            // while there is an arbitrary amount of actual results.
            //
            // We need to adjust `interpret_instr` interace in order
            // to take multiple return values into account.
            let return_value = return_value.expect(MISSING_RETURN_VALUE_ERRSTR);
            frame.write_register(return_value, result)
        })?;
        Ok(InterpretationFlow::Continue)
    }
}

impl InterpretInstr for TailCallInstr {
    fn interpret_instr(
        &self,
        _return_value: Option<Value>,
        ctx: &mut EvaluationContext,
        frame: &mut FunctionFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        // Create a new function frame and load input parameters into it.
        // We cannot do this within the current frame since we might risk
        // overriding inputs with each other.
        // The old frame is released before continuing execution to have
        // efficient tail calls without exploding the frame stack.
        // In a tail call recursion this caching would result in similar
        // behavior as using two ping-pong buffers.
        //
        // Since function frames are cached reusing them is very cheap.
        let mut new_frame = ctx.create_frame();
        let function = ctx.store.get_fn(self.func());
        new_frame.initialize(
            function,
            self.params()
                .iter()
                .copied()
                .map(|param| frame.read_register(param)),
        )?;
        let old_frame = replace(frame, new_frame);
        ctx.release_frame(old_frame);
        Ok(InterpretationFlow::TailCall(self.func()))
    }
}

impl InterpretInstr for ReinterpretInstr {
    fn interpret_instr(
        &self,
        return_value: Option<Value>,
        _ctx: &mut EvaluationContext,
        frame: &mut FunctionFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let return_value = return_value.expect(MISSING_RETURN_VALUE_ERRSTR);
        let source = frame.read_register(self.src());
        debug_assert_eq!(
            self.src_type().bit_width(),
            self.dst_type().bit_width()
        );
        // Reinterpretation just moves from one register to the other.
        frame.write_register(return_value, source);
        Ok(InterpretationFlow::Continue)
    }
}

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

/// Trait used to streamline operations on primitive types.
pub trait PrimitiveInteger: Copy {
    fn wrapping_add(self, rhs: Self) -> Self;
    fn wrapping_sub(self, rhs: Self) -> Self;
    fn wrapping_mul(self, rhs: Self) -> Self;
    fn wrapping_div(self, rhs: Self) -> Self;
    fn wrapping_rem(self, rhs: Self) -> Self;
}
macro_rules! impl_primitive_integer_for {
    ( $( $type:ty ),* $(,)? ) => {
        $(
            impl PrimitiveInteger for $type {
                fn wrapping_add(self, rhs: Self) -> Self { self.wrapping_add(rhs) }
                fn wrapping_sub(self, rhs: Self) -> Self { self.wrapping_sub(rhs) }
                fn wrapping_mul(self, rhs: Self) -> Self { self.wrapping_mul(rhs) }
                fn wrapping_div(self, rhs: Self) -> Self { self.wrapping_div(rhs) }
                fn wrapping_rem(self, rhs: Self) -> Self { self.wrapping_rem(rhs) }
            }
        )*
    };
}
impl_primitive_integer_for! {
    i8, i16, i32, i64,
    u8, u16, u32, u64,
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
        /// Computes `op` on `lhs` and `rhs` using `f` to convert from unsigned to signed.
        fn compute<U, S, F, V>(
            op: BinaryIntOp,
            lhs: U,
            rhs: U,
            mut u2s: F,
            mut s2u: V,
        ) -> U
        where
            U: PrimitiveInteger
                + BitAnd<Output = U>
                + BitOr<Output = U>
                + BitXor<Output = U>,
            S: PrimitiveInteger
                + BitAnd<Output = S>
                + BitOr<Output = S>
                + BitXor<Output = S>,
            F: FnMut(U) -> S,
            V: FnMut(S) -> U,
        {
            match op {
                Op::Add => lhs.wrapping_add(rhs),
                Op::Sub => lhs.wrapping_sub(rhs),
                Op::Mul => lhs.wrapping_mul(rhs),
                Op::Sdiv => s2u(u2s(lhs).wrapping_div(u2s(rhs))),
                Op::Srem => s2u(u2s(lhs).wrapping_rem(u2s(rhs))),
                Op::Udiv => lhs.wrapping_div(rhs),
                Op::Urem => lhs.wrapping_rem(rhs),
                Op::And => lhs & rhs,
                Op::Or => lhs | rhs,
                Op::Xor => lhs ^ rhs,
                _ => unimplemented!(),
            }
        }
        let result = match self.ty() {
            IntType::I8 => {
                let lhs = lhs as u8;
                let rhs = rhs as u8;
                let result =
                    compute(self.op(), lhs, rhs, |u| u as i8, |s| s as u8);
                result as u64
            }
            IntType::I16 => {
                let lhs = lhs as u16;
                let rhs = rhs as u16;
                let result =
                    compute(self.op(), lhs, rhs, |u| u as i16, |s| s as u16);
                result as u64
            }
            IntType::I32 => {
                let lhs = lhs as u32;
                let rhs = rhs as u32;
                let result =
                    compute(self.op(), lhs, rhs, |u| u as i32, |s| s as u32);
                result as u64
            }
            IntType::I64 => {
                let result =
                    compute(self.op(), lhs, rhs, |u| u as i64, |s| s as u64);
                result as u64
            }
        };
        frame.write_register(return_value, result);
        Ok(InterpretationFlow::Continue)
    }
}

impl InterpretInstr for FloatInstr {
    fn interpret_instr(
        &self,
        return_value: Option<Value>,
        ctx: &mut EvaluationContext,
        frame: &mut FunctionFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        match self {
            FloatInstr::Binary(instr) => instr.interpret_instr(return_value, ctx, frame),
            FloatInstr::Compare(_instr) => unimplemented!(),
            FloatInstr::Demote(_instr) => unimplemented!(),
            FloatInstr::FloatToInt(instr) => {
                instr.interpret_instr(return_value, ctx, frame)
            }
            FloatInstr::Promote(_instr) => unimplemented!(),
            FloatInstr::Unary(instr) => {
                instr.interpret_instr(return_value, ctx, frame)
            }
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

impl InterpretInstr for BinaryFloatInstr {
    fn interpret_instr(
        &self,
        return_value: Option<Value>,
        _ctx: &mut EvaluationContext,
        frame: &mut FunctionFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let return_value = return_value.expect(MISSING_RETURN_VALUE_ERRSTR);
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
            (F32, Op::Div) => operate_f32(lhs, rhs, f32::div),
            (F64, Op::Div) => operate_f64(lhs, rhs, f64::div),
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
        return_value: Option<Value>,
        _ctx: &mut EvaluationContext,
        frame: &mut FunctionFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let return_value = return_value.expect(MISSING_RETURN_VALUE_ERRSTR);
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
            // f32 -> uN
            (false, F32, I8) => reg_f32(source) as u8 as u64,
            (false, F32, I16) => reg_f32(source) as u16 as u64,
            (false, F32, I32) => reg_f32(source) as u32 as u64,
            (false, F32, I64) => reg_f32(source) as u64,
            // f64 -> uN
            (false, F64, I8) => reg_f64(source) as u8 as u64,
            (false, F64, I16) => reg_f64(source) as u16 as u64,
            (false, F64, I32) => reg_f64(source) as u32 as u64,
            (false, F64, I64) => reg_f64(source) as u64,
            // f32 -> iN
            (true, F32, I8) => reg_f32(source) as i8 as u8 as u64,
            (true, F32, I16) => reg_f32(source) as i16 as u16 as u64,
            (true, F32, I32) => reg_f32(source) as i32 as u32 as u64,
            (true, F32, I64) => reg_f32(source) as i64 as u64,
            // f64 -> iN
            (true, F64, I8) => reg_f64(source) as i8 as u8 as u64,
            (true, F64, I16) => reg_f64(source) as i16 as u16 as u64,
            (true, F64, I32) => reg_f64(source) as i32 as u32 as u64,
            (true, F64, I64) => reg_f64(source) as i64 as u64,
        };
        frame.write_register(return_value, result as u64);
        Ok(InterpretationFlow::Continue)
    }
}
