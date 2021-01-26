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

use super::{InterpretationContext, InterpretationError};
use crate::{ir::{instr::{
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
        }, instruction::{BinaryIntOp, CompareIntOp, UnaryIntOp}, primitive::{
            Const,
            FloatConst,
            FloatType,
            IntConst,
            IntType,
            Type,
            Value,
        }}, parse::{F32, F64}};

/// Implemented by Runwell IR instructions to make them interpretable.
pub trait InterpretInstr {
    /// Evaluates the function given the interpretation context.
    fn interpret(
        &self,
        value: Option<Value>,
        ctx: &mut InterpretationContext,
    ) -> Result<(), InterpretationError>;
}

impl InterpretInstr for Instruction {
    fn interpret(
        &self,
        value: Option<Value>,
        ctx: &mut InterpretationContext,
    ) -> Result<(), InterpretationError> {
        match self {
            Self::Call(_instr) => unimplemented!(),
            Self::CallIndirect(_instr) => unimplemented!(),
            Self::Const(instr) => instr.interpret(value, ctx),
            Self::MemoryGrow(_instr) => unimplemented!(),
            Self::MemorySize(_instr) => unimplemented!(),
            Self::Phi(instr) => instr.interpret(value, ctx),
            Self::Load(_instr) => unimplemented!(),
            Self::Store(_instr) => unimplemented!(),
            Self::Select(instr) => instr.interpret(value, ctx),
            Self::Reinterpret(instr) => instr.interpret(value, ctx),
            Self::Terminal(instr) => instr.interpret(value, ctx),
            Self::Int(instr) => instr.interpret(value, ctx),
            Self::Float(_instr) => unimplemented!(),
        }
    }
}

impl InterpretInstr for PhiInstr {
    fn interpret(
        &self,
        value: Option<Value>,
        ctx: &mut InterpretationContext,
    ) -> Result<(), InterpretationError> {
        let value = value.expect("missing value for instruction");
        let last_block = ctx
            .last_block()
            .expect("phi instruction is missing predecessor");
        let result = self
            .operand_for(last_block)
            .expect("phi instruction missing value for predecessor");
        let result_value = ctx.value_results[result];
        ctx.value_results.insert(value, result_value);
        Ok(())
    }
}

impl InterpretInstr for ConstInstr {
    fn interpret(
        &self,
        value: Option<Value>,
        ctx: &mut InterpretationContext,
    ) -> Result<(), InterpretationError> {
        let value = value.expect("missing value for instruction");
        ctx.value_results.insert(value, self.const_value());
        Ok(())
    }
}

impl InterpretInstr for SelectInstr {
    fn interpret(
        &self,
        value: Option<Value>,
        ctx: &mut InterpretationContext,
    ) -> Result<(), InterpretationError> {
        let value = value.expect("missing value for instruction");
        let condition = ctx.value_results[self.condition()];
        let result_value = match condition {
            Const::Bool(true) => self.true_value(),
            Const::Bool(false) => self.false_value(),
            _ => unreachable!(),
        };
        let result = ctx.value_results[result_value];
        ctx.value_results.insert(value, result);
        Ok(())
    }
}

impl InterpretInstr for TerminalInstr {
    fn interpret(
        &self,
        value: Option<Value>,
        ctx: &mut InterpretationContext,
    ) -> Result<(), InterpretationError> {
        match self {
            Self::Trap => {
                ctx.set_trapped();
                Ok(())
            }
            Self::Return(instr) => instr.interpret(value, ctx),
            Self::Br(instr) => instr.interpret(value, ctx),
            Self::Ite(instr) => instr.interpret(value, ctx),
            Self::BranchTable(_instr) => unimplemented!(),
        }
    }
}

impl InterpretInstr for ReturnInstr {
    fn interpret(
        &self,
        _value: Option<Value>,
        ctx: &mut InterpretationContext,
    ) -> Result<(), InterpretationError> {
        let return_value = ctx.value_results[self.return_value()];
        ctx.set_output(return_value)?;
        ctx.set_returned();
        Ok(())
    }
}

impl InterpretInstr for BranchInstr {
    fn interpret(
        &self,
        _value: Option<Value>,
        ctx: &mut InterpretationContext,
    ) -> Result<(), InterpretationError> {
        ctx.switch_to_block(self.target());
        Ok(())
    }
}

impl InterpretInstr for IfThenElseInstr {
    fn interpret(
        &self,
        _value: Option<Value>,
        ctx: &mut InterpretationContext,
    ) -> Result<(), InterpretationError> {
        let condition = ctx.value_results[self.condition()];
        match condition {
            Const::Bool(true) => ctx.switch_to_block(self.true_target()),
            Const::Bool(false) => ctx.switch_to_block(self.false_target()),
            _ => unreachable!(),
        }
        Ok(())
    }
}

impl InterpretInstr for ReinterpretInstr {
    fn interpret(
        &self,
        value: Option<Value>,
        ctx: &mut InterpretationContext,
    ) -> Result<(), InterpretationError> {
        let value = value.expect("missing value for instruction");
        let source = ctx.value_results[self.src()];
        debug_assert_eq!(source.ty(), self.src_type());
        debug_assert_eq!(
            self.src_type().bit_width(),
            self.dst_type().bit_width()
        );
        let bits = match source {
            Const::Int(IntConst::I8(src)) => src as u8 as u64,
            Const::Int(IntConst::I16(src)) => src as u16 as u64,
            Const::Int(IntConst::I32(src)) => src as u32 as u64,
            Const::Int(IntConst::I64(src)) => src as u64,
            Const::Bool(src) => src as u64,
            Const::Float(FloatConst::F32(src)) => src.bits() as u64,
            Const::Float(FloatConst::F64(src)) => src.bits(),
        };
        let result = match self.dst_type() {
            Type::Int(IntType::I8) => {
                Const::Int(IntConst::I8(bits as u8 as i8))
            }
            Type::Int(IntType::I16) => {
                Const::Int(IntConst::I16(bits as u16 as i16))
            }
            Type::Int(IntType::I32) => {
                Const::Int(IntConst::I32(bits as u32 as i32))
            }
            Type::Int(IntType::I64) => Const::Int(IntConst::I64(bits as i64)),
            Type::Bool => Const::Bool(bits != 0),
            Type::Float(FloatType::F32) => {
                Const::Float(FloatConst::F32(F32::from_bits(bits as u32)))
            }
            Type::Float(FloatType::F64) => {
                Const::Float(FloatConst::F64(F64::from_bits(bits)))
            }
        };
        ctx.value_results.insert(value, result);
        Ok(())
    }
}

impl InterpretInstr for IntInstr {
    fn interpret(
        &self,
        value: Option<Value>,
        ctx: &mut InterpretationContext,
    ) -> Result<(), InterpretationError> {
        match self {
            Self::Binary(instr) => instr.interpret(value, ctx),
            Self::Unary(instr) => instr.interpret(value, ctx),
            Self::Compare(instr) => instr.interpret(value, ctx),
            Self::Extend(instr) => instr.interpret(value, ctx),
            Self::IntToFloat(instr) => instr.interpret(value, ctx),
            Self::Truncate(instr) => instr.interpret(value, ctx),
        }
    }
}

impl InterpretInstr for UnaryIntInstr {
    fn interpret(
        &self,
        value: Option<Value>,
        ctx: &mut InterpretationContext,
    ) -> Result<(), InterpretationError> {
        let result_value = value.expect("missing value for instruction");
        let source = ctx.value_results[self.src()];
        let source_int = match source {
            Const::Int(int_const) => int_const,
            _ => unreachable!(),
        };
        use IntConst::{I8, I16, I32, I64};
        let result = match (self.op(), source_int) {
            (UnaryIntOp::LeadingZeros, I8(src)) => src.leading_zeros(),
            (UnaryIntOp::LeadingZeros, I16(src)) => src.leading_zeros(),
            (UnaryIntOp::LeadingZeros, I32(src)) => src.leading_zeros(),
            (UnaryIntOp::LeadingZeros, I64(src)) => src.leading_zeros(),
            (UnaryIntOp::TrailingZeros, I8(src)) => src.trailing_zeros(),
            (UnaryIntOp::TrailingZeros, I16(src)) => src.trailing_zeros(),
            (UnaryIntOp::TrailingZeros, I32(src)) => src.trailing_zeros(),
            (UnaryIntOp::TrailingZeros, I64(src)) => src.trailing_zeros(),
            (UnaryIntOp::PopCount, I8(src)) => src.count_ones(),
            (UnaryIntOp::PopCount, I16(src)) => src.count_ones(),
            (UnaryIntOp::PopCount, I32(src)) => src.count_ones(),
            (UnaryIntOp::PopCount, I64(src)) => src.count_ones(),
            _ => unimplemented!(),
        };
        ctx.value_results.insert(result_value, Const::Int(I32(result as i32)));
        Ok(())
    }
}

impl InterpretInstr for TruncateIntInstr {
    fn interpret(
        &self,
        _value: Option<Value>,
        _ctx: &mut InterpretationContext,
    ) -> Result<(), InterpretationError> {
        unimplemented!()
    }
}

impl InterpretInstr for ExtendIntInstr {
    fn interpret(
        &self,
        _value: Option<Value>,
        _ctx: &mut InterpretationContext,
    ) -> Result<(), InterpretationError> {
        unimplemented!()
    }
}

impl InterpretInstr for IntToFloatInstr {
    fn interpret(
        &self,
        _value: Option<Value>,
        _ctx: &mut InterpretationContext,
    ) -> Result<(), InterpretationError> {
        unimplemented!()
    }
}

impl InterpretInstr for CompareIntInstr {
    fn interpret(
        &self,
        value: Option<Value>,
        ctx: &mut InterpretationContext,
    ) -> Result<(), InterpretationError> {
        let result_value = value.expect("missing value for instruction");
        let lhs_value = ctx.value_results[self.lhs()];
        let rhs_value = ctx.value_results[self.rhs()];
        let lhs_int = match lhs_value {
            Const::Int(int_const) => int_const,
            _ => unreachable!(),
        };
        let rhs_int = match rhs_value {
            Const::Int(int_const) => int_const,
            _ => unreachable!(),
        };
        debug_assert_eq!(lhs_value.ty(), rhs_value.ty());
        use CompareIntOp as Op;
        use IntConst::{I16, I32, I64, I8};
        let result = match (self.op(), lhs_int, rhs_int) {
            // Equals
            (Op::Eq, I8(lhs), I8(rhs)) => lhs == rhs,
            (Op::Eq, I16(lhs), I16(rhs)) => lhs == rhs,
            (Op::Eq, I32(lhs), I32(rhs)) => lhs == rhs,
            (Op::Eq, I64(lhs), I64(rhs)) => lhs == rhs,
            // Signed less-than
            (Op::Slt, I8(lhs), I8(rhs)) => lhs < rhs,
            (Op::Slt, I16(lhs), I16(rhs)) => lhs < rhs,
            (Op::Slt, I32(lhs), I32(rhs)) => lhs < rhs,
            (Op::Slt, I64(lhs), I64(rhs)) => lhs < rhs,
            // Signed less-equals
            (Op::Sle, I8(lhs), I8(rhs)) => lhs <= rhs,
            (Op::Sle, I16(lhs), I16(rhs)) => lhs <= rhs,
            (Op::Sle, I32(lhs), I32(rhs)) => lhs <= rhs,
            (Op::Sle, I64(lhs), I64(rhs)) => lhs <= rhs,
            // Signed greater-than
            (Op::Sgt, I8(lhs), I8(rhs)) => lhs > rhs,
            (Op::Sgt, I16(lhs), I16(rhs)) => lhs > rhs,
            (Op::Sgt, I32(lhs), I32(rhs)) => lhs > rhs,
            (Op::Sgt, I64(lhs), I64(rhs)) => lhs > rhs,
            // Signed greater-equals
            (Op::Sge, I8(lhs), I8(rhs)) => lhs >= rhs,
            (Op::Sge, I16(lhs), I16(rhs)) => lhs >= rhs,
            (Op::Sge, I32(lhs), I32(rhs)) => lhs >= rhs,
            (Op::Sge, I64(lhs), I64(rhs)) => lhs >= rhs,
            // Unsigned less-than
            (Op::Ult, I8(lhs), I8(rhs)) => (lhs as u8) < (rhs as u8),
            (Op::Ult, I16(lhs), I16(rhs)) => (lhs as u16) < (rhs as u16),
            (Op::Ult, I32(lhs), I32(rhs)) => (lhs as u32) < (rhs as u32),
            (Op::Ult, I64(lhs), I64(rhs)) => (lhs as u64) < (rhs as u64),
            // Unsigned less-equals
            (Op::Ule, I8(lhs), I8(rhs)) => (lhs as u8) <= (rhs as u8),
            (Op::Ule, I16(lhs), I16(rhs)) => (lhs as u16) <= (rhs as u16),
            (Op::Ule, I32(lhs), I32(rhs)) => (lhs as u32) <= (rhs as u32),
            (Op::Ule, I64(lhs), I64(rhs)) => (lhs as u64) <= (rhs as u64),
            // Unsigned greater-than
            (Op::Ugt, I8(lhs), I8(rhs)) => (lhs as u8) > (rhs as u8),
            (Op::Ugt, I16(lhs), I16(rhs)) => (lhs as u16) > (rhs as u16),
            (Op::Ugt, I32(lhs), I32(rhs)) => (lhs as u32) > (rhs as u32),
            (Op::Ugt, I64(lhs), I64(rhs)) => (lhs as u64) > (rhs as u64),
            // Unsigned greater-equals
            (Op::Uge, I8(lhs), I8(rhs)) => (lhs as u8) >= (rhs as u8),
            (Op::Uge, I16(lhs), I16(rhs)) => (lhs as u16) >= (rhs as u16),
            (Op::Uge, I32(lhs), I32(rhs)) => (lhs as u32) >= (rhs as u32),
            (Op::Uge, I64(lhs), I64(rhs)) => (lhs as u64) >= (rhs as u64),
            _ => unimplemented!(),
        };
        let result = Const::Bool(result);
        ctx.value_results.insert(result_value, result);
        Ok(())
    }
}

impl InterpretInstr for BinaryIntInstr {
    fn interpret(
        &self,
        value: Option<Value>,
        ctx: &mut InterpretationContext,
    ) -> Result<(), InterpretationError> {
        let result_value = value.expect("missing value for instruction");
        let lhs_value = ctx.value_results[self.lhs()];
        let rhs_value = ctx.value_results[self.rhs()];
        let lhs_int = match lhs_value {
            Const::Int(int_const) => int_const,
            _ => unreachable!(),
        };
        let rhs_int = match rhs_value {
            Const::Int(int_const) => int_const,
            _ => unreachable!(),
        };
        use BinaryIntOp as Op;
        use IntConst::{I16, I32, I64, I8};
        #[rustfmt::skip]
        let result = match (self.op(), lhs_int, rhs_int) {
            // Shift and rotate operations are currently unimplemented since
            // their semantics are not yet clear. Binary instructions typically
            // require their left-hand and right-hand side values to be of the
            // same type. The problem with shift and rotate instructions is that
            // at least in Rust the right-hand side is expected to always be of
            // type `u32` instead of having the same type as the left-hand side.
            //
            // Integer Addition
            (Op::Add, I8(lhs), I8(rhs)) => I8(lhs.wrapping_add(rhs)),
            (Op::Add, I16(lhs), I16(rhs)) => I16(lhs.wrapping_add(rhs)),
            (Op::Add, I32(lhs), I32(rhs)) => I32(lhs.wrapping_add(rhs)),
            (Op::Add, I64(lhs), I64(rhs)) => I64(lhs.wrapping_add(rhs)),
            // Integer Subtraction
            (Op::Sub, I8(lhs), I8(rhs)) => I8(lhs.wrapping_sub(rhs)),
            (Op::Sub, I16(lhs), I16(rhs)) => I16(lhs.wrapping_sub(rhs)),
            (Op::Sub, I32(lhs), I32(rhs)) => I32(lhs.wrapping_sub(rhs)),
            (Op::Sub, I64(lhs), I64(rhs)) => I64(lhs.wrapping_sub(rhs)),
            // Integer Multiplication
            (Op::Mul, I8(lhs), I8(rhs)) => I8(lhs.wrapping_mul(rhs)),
            (Op::Mul, I16(lhs), I16(rhs)) => I16(lhs.wrapping_mul(rhs)),
            (Op::Mul, I32(lhs), I32(rhs)) => I32(lhs.wrapping_mul(rhs)),
            (Op::Mul, I64(lhs), I64(rhs)) => I64(lhs.wrapping_mul(rhs)),
            // Signed Integer Division
            (Op::Sdiv, I8(lhs), I8(rhs)) => I8(lhs.wrapping_div(rhs)),
            (Op::Sdiv, I16(lhs), I16(rhs)) => I16(lhs.wrapping_div(rhs)),
            (Op::Sdiv, I32(lhs), I32(rhs)) => I32(lhs.wrapping_div(rhs)),
            (Op::Sdiv, I64(lhs), I64(rhs)) => I64(lhs.wrapping_div(rhs)),
            // Signed Integer Remainder
            (Op::Srem, I8(lhs), I8(rhs)) => I8(lhs.wrapping_rem(rhs)),
            (Op::Srem, I16(lhs), I16(rhs)) => I16(lhs.wrapping_rem(rhs)),
            (Op::Srem, I32(lhs), I32(rhs)) => I32(lhs.wrapping_rem(rhs)),
            (Op::Srem, I64(lhs), I64(rhs)) => I64(lhs.wrapping_rem(rhs)),
            // Unsigned Integer Division
            (Op::Udiv, I8(l), I8(r)) => I8((l as u8).wrapping_div(r as u8) as i8),
            (Op::Udiv, I16(l), I16(r)) => I16((l as u16).wrapping_div(r as u16) as i16),
            (Op::Udiv, I32(l), I32(r)) => I32((l as u32).wrapping_div(r as u32) as i32),
            (Op::Udiv, I64(l), I64(r)) => I64((l as u64).wrapping_div(r as u64) as i64),
            // Unsigned Integer Remainder
            (Op::Urem, I8(l), I8(r)) => I8((l as u8).wrapping_rem(r as u8) as i8),
            (Op::Urem, I16(l), I16(r)) => I16((l as u16).wrapping_rem(r as u16) as i16),
            (Op::Urem, I32(l), I32(r)) => I32((l as u32).wrapping_rem(r as u32) as i32),
            (Op::Urem, I64(l), I64(r)) => I64((l as u64).wrapping_rem(r as u64) as i64),
            // Bitwise-AND
            (Op::And, I8(lhs), I8(rhs)) => I8(lhs & rhs),
            (Op::And, I16(lhs), I16(rhs)) => I16(lhs & rhs),
            (Op::And, I32(lhs), I32(rhs)) => I32(lhs & rhs),
            (Op::And, I64(lhs), I64(rhs)) => I64(lhs & rhs),
            // Bitwise-OR
            (Op::Or, I8(lhs), I8(rhs)) => I8(lhs | rhs),
            (Op::Or, I16(lhs), I16(rhs)) => I16(lhs | rhs),
            (Op::Or, I32(lhs), I32(rhs)) => I32(lhs | rhs),
            (Op::Or, I64(lhs), I64(rhs)) => I64(lhs | rhs),
            // Bitwise-XOR
            (Op::Xor, I8(lhs), I8(rhs)) => I8(lhs ^ rhs),
            (Op::Xor, I16(lhs), I16(rhs)) => I16(lhs ^ rhs),
            (Op::Xor, I32(lhs), I32(rhs)) => I32(lhs ^ rhs),
            (Op::Xor, I64(lhs), I64(rhs)) => I64(lhs ^ rhs),
            _ => unimplemented!(),
        };
        ctx.value_results.insert(result_value, result.into());
        Ok(())
    }
}
