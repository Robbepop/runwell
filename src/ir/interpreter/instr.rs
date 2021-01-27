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

use super::{FunctionEvaluationContext, InterpretationError};
use crate::{entity::RawIdx, ir::{
    instr::{
        BinaryIntInstr,
        BranchInstr,
        CompareIntInstr,
        ConstInstr,
        ExtendIntInstr,
        IfThenElseInstr,
        Instruction,
        IntInstr,
        IntToFloatInstr,
        PhiInstr,
        ReinterpretInstr,
        ReturnInstr,
        SelectInstr,
        TerminalInstr,
        TruncateIntInstr,
        UnaryIntInstr,
    },
    instruction::{BinaryIntOp, CompareIntOp, UnaryIntOp},
    primitive::{IntType, Value},
}};
use crate::parse::FunctionId;

/// Implemented by Runwell IR instructions to make them interpretable.
pub trait InterpretInstr {
    /// Evaluates the function given the interpretation context.
    fn interpret_instr(
        &self,
        return_return_value: Option<Value>,
        ctx: &mut FunctionEvaluationContext,
    ) -> Result<InterpretationFlow, InterpretationError>;
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
    TailCall(FunctionId),
}

impl InterpretInstr for Instruction {
    fn interpret_instr(
        &self,
        return_value: Option<Value>,
        ctx: &mut FunctionEvaluationContext,
    ) -> Result<InterpretationFlow, InterpretationError> {
        match self {
            Self::Call(_instr) => unimplemented!(),
            Self::CallIndirect(_instr) => unimplemented!(),
            Self::Const(instr) => instr.interpret_instr(return_value, ctx),
            Self::MemoryGrow(_instr) => unimplemented!(),
            Self::MemorySize(_instr) => unimplemented!(),
            Self::Phi(instr) => instr.interpret_instr(return_value, ctx),
            Self::Load(_instr) => unimplemented!(),
            Self::Store(_instr) => unimplemented!(),
            Self::Select(instr) => instr.interpret_instr(return_value, ctx),
            Self::Reinterpret(instr) => {
                instr.interpret_instr(return_value, ctx)
            }
            Self::Terminal(instr) => instr.interpret_instr(return_value, ctx),
            Self::Int(instr) => instr.interpret_instr(return_value, ctx),
            Self::Float(_instr) => unimplemented!(),
        }
    }
}

impl InterpretInstr for PhiInstr {
    fn interpret_instr(
        &self,
        return_value: Option<Value>,
        ctx: &mut FunctionEvaluationContext,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let return_value = return_value.expect("missing value for instruction");
        let last_block = ctx
            .frame
            .last_block()
            .expect("phi instruction is missing predecessor");
        let result = self
            .operand_for(last_block)
            .expect("phi instruction missing value for predecessor");
        let result = ctx.frame.read_register(result);
        ctx.frame.write_register(return_value, result);
        Ok(InterpretationFlow::Continue)
    }
}

impl InterpretInstr for ConstInstr {
    fn interpret_instr(
        &self,
        return_value: Option<Value>,
        ctx: &mut FunctionEvaluationContext,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let return_value = return_value.expect("missing value for instruction");
        ctx.frame.write_register(return_value, self.const_value().into_bits64());
        Ok(InterpretationFlow::Continue)
    }
}

impl InterpretInstr for SelectInstr {
    fn interpret_instr(
        &self,
        return_value: Option<Value>,
        ctx: &mut FunctionEvaluationContext,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let return_value = return_value.expect("missing value for instruction");
        let condition = ctx.frame.read_register(self.condition());
        let result_value = if condition != 0 {
            self.true_value()
        } else {
            self.false_value()
        };
        let result = ctx.frame.read_register(result_value);
        ctx.frame.write_register(return_value, result);
        Ok(InterpretationFlow::Continue)
    }
}

impl InterpretInstr for TerminalInstr {
    fn interpret_instr(
        &self,
        return_value: Option<Value>,
        ctx: &mut FunctionEvaluationContext,
    ) -> Result<InterpretationFlow, InterpretationError> {
        match self {
            Self::Trap => {
                Err(InterpretationError::EvaluationHasTrapped)
            }
            Self::Return(instr) => instr.interpret_instr(return_value, ctx),
            Self::Br(instr) => instr.interpret_instr(return_value, ctx),
            Self::Ite(instr) => instr.interpret_instr(return_value, ctx),
            Self::BranchTable(_instr) => unimplemented!(),
        }
    }
}

impl InterpretInstr for ReturnInstr {
    fn interpret_instr(
        &self,
        _return_value: Option<Value>,
        ctx: &mut FunctionEvaluationContext,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let return_value = ctx.frame.read_register(self.return_value());
        let r0 = Value::from_raw(RawIdx::from_u32(0));
        ctx.frame.write_register(r0, return_value);
        Ok(InterpretationFlow::Return)
    }
}

impl InterpretInstr for BranchInstr {
    fn interpret_instr(
        &self,
        _return_value: Option<Value>,
        ctx: &mut FunctionEvaluationContext,
    ) -> Result<InterpretationFlow, InterpretationError> {
        ctx.frame.switch_to_block(self.target());
        Ok(InterpretationFlow::Continue)
    }
}

impl InterpretInstr for IfThenElseInstr {
    fn interpret_instr(
        &self,
        _return_value: Option<Value>,
        ctx: &mut FunctionEvaluationContext,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let condition = ctx.frame.read_register(self.condition());
        let target = if condition != 0 {
            self.true_target()
        } else {
            self.false_target()
        };
        ctx.frame.switch_to_block(target);
        Ok(InterpretationFlow::Continue)
    }
}

impl InterpretInstr for ReinterpretInstr {
    fn interpret_instr(
        &self,
        return_value: Option<Value>,
        ctx: &mut FunctionEvaluationContext,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let return_value = return_value.expect("missing value for instruction");
        let source = ctx.frame.read_register(self.src());
        debug_assert_eq!(
            self.src_type().bit_width(),
            self.dst_type().bit_width()
        );
        // Reinterpretation just moves from one register to the other.
        ctx.frame.write_register(return_value, source);
        Ok(InterpretationFlow::Continue)
    }
}

impl InterpretInstr for IntInstr {
    fn interpret_instr(
        &self,
        return_value: Option<Value>,
        ctx: &mut FunctionEvaluationContext,
    ) -> Result<InterpretationFlow, InterpretationError> {
        match self {
            Self::Binary(instr) => instr.interpret_instr(return_value, ctx),
            Self::Unary(instr) => instr.interpret_instr(return_value, ctx),
            Self::Compare(instr) => instr.interpret_instr(return_value, ctx),
            Self::Extend(instr) => instr.interpret_instr(return_value, ctx),
            Self::IntToFloat(instr) => instr.interpret_instr(return_value, ctx),
            Self::Truncate(instr) => instr.interpret_instr(return_value, ctx),
        }
    }
}

impl InterpretInstr for UnaryIntInstr {
    fn interpret_instr(
        &self,
        return_value: Option<Value>,
        ctx: &mut FunctionEvaluationContext,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let return_value = return_value.expect("missing value for instruction");
        let source = ctx.frame.read_register(self.src());
        let result = match self.op() {
            UnaryIntOp::LeadingZeros => source.leading_zeros(),
            UnaryIntOp::TrailingZeros => source.trailing_zeros(),
            UnaryIntOp::PopCount => source.count_ones(),
        };
        ctx.frame.write_register(return_value, result as u64);
        Ok(InterpretationFlow::Continue)
    }
}

impl InterpretInstr for TruncateIntInstr {
    fn interpret_instr(
        &self,
        return_value: Option<Value>,
        ctx: &mut FunctionEvaluationContext,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let return_value = return_value.expect("missing value for instruction");
        let source = ctx.frame.read_register(self.src());
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
        ctx.frame.write_register(return_value, result as u64);
        Ok(InterpretationFlow::Continue)
    }
}

impl InterpretInstr for ExtendIntInstr {
    fn interpret_instr(
        &self,
        return_value: Option<Value>,
        ctx: &mut FunctionEvaluationContext,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let return_value = return_value.expect("missing value for instruction");
        let source = ctx.frame.read_register(self.src());
        debug_assert!(
            self.src_type().bit_width() <= self.dst_type().bit_width()
        );
        let result = if self.is_signed() {
            match (self.src_type(), self.dst_type()) {
                (IntType::I8, IntType::I16) => source as u8 as i8 as i16 as u16 as u64,
                (IntType::I8, IntType::I32) => source as u8 as i8 as i32 as u32 as u64,
                (IntType::I8, IntType::I64) => source as u8 as i8 as i64 as u64,
                (IntType::I16, IntType::I32) => source as u16 as i16 as i32 as u32 as u64,
                (IntType::I32, IntType::I64) => source as u32 as i32 as i64 as u64,
                (x, y) if x == y => source,
                _ => unreachable!(),
            }
        } else {
            // Nothing to do since interpreter registers are `u64`.
            source
        };
        ctx.frame.write_register(return_value, result as u64);
        Ok(InterpretationFlow::Continue)
    }
}

impl InterpretInstr for IntToFloatInstr {
    fn interpret_instr(
        &self,
        _return_value: Option<Value>,
        _ctx: &mut FunctionEvaluationContext,
    ) -> Result<InterpretationFlow, InterpretationError> {
        // WebAssembly instructions that map to IntToFloatInstr:
        //
        // i32 conversion to f32 and f64:
        //  - i32.trunc_f32_s
        //  - i32.trunc_f32_u
        //  - i32.trunc_f64_s
        //  - i32.trunc_f64_u
        //
        // i64 conversion to f32 and f64:
        //  - i64.trunc_f32_s
        //  - i64.trunc_f32_u
        //  - i64.trunc_f64_s
        //  - i64.trunc_f64_u
        //
        // WebAssembly instructions that map to FloatTotIntInstr:
        //
        // f32 conversion to i32 and i64:
        //  - f32.convert_i32_s
        //  - f32.convert_i32_u
        //  - f32.convert_i64_s
        //  - f32.convert_i64_u
        //
        // f64 conversion to i32 and i64:
        //  - f64.convert_i32_s
        //  - f64.convert_i32_u
        //  - f64.convert_i64_s
        //  - f64.convert_i64_u
        unimplemented!()
    }
}

impl InterpretInstr for CompareIntInstr {
    fn interpret_instr(
        &self,
        return_value: Option<Value>,
        ctx: &mut FunctionEvaluationContext,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let return_value = return_value.expect("missing value for instruction");
        let lhs = ctx.frame.read_register(self.lhs());
        let rhs = ctx.frame.read_register(self.rhs());
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
        ctx.frame.write_register(return_value, result);
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
        ctx: &mut FunctionEvaluationContext,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let return_value = return_value.expect("missing value for instruction");
        let lhs = ctx.frame.read_register(self.lhs());
        let rhs = ctx.frame.read_register(self.rhs());
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
        ctx.frame.write_register(return_value, result);
        Ok(InterpretationFlow::Continue)
    }
}
