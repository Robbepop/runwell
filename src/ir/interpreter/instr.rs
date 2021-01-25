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
use crate::{
    ir::{
        instr::{
            BinaryIntInstr,
            CompareIntInstr,
            ConstInstr,
            ExtendIntInstr,
            Instruction,
            IntInstr,
            IntToFloatInstr,
            PhiInstr,
            ReinterpretInstr,
            SelectInstr,
            TerminalInstr,
            TruncateIntInstr,
            UnaryIntInstr,
        },
        instruction::{BinaryIntOp, CompareIntOp},
        primitive::{
            Const,
            FloatConst,
            FloatType,
            IntConst,
            IntType,
            Type,
            Value,
        },
    },
    parse::{F32, F64},
};

impl Instruction {
    /// Evaluates the function given the interpretation context.
    pub fn interpret(
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
            Self::Reinterpret(_instr) => unimplemented!(),
            Self::Terminal(instr) => instr.interpret(value, ctx),
            Self::Int(instr) => instr.interpret(value, ctx),
            Self::Float(_instr) => unimplemented!(),
        }
    }
}

impl PhiInstr {
    /// Evaluates the function given the interpretation context.
    pub fn interpret(
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

impl ConstInstr {
    /// Evaluates the function given the interpretation context.
    pub fn interpret(
        &self,
        value: Option<Value>,
        ctx: &mut InterpretationContext,
    ) -> Result<(), InterpretationError> {
        let value = value.expect("missing value for instruction");
        ctx.value_results.insert(value, self.const_value());
        Ok(())
    }
}

impl SelectInstr {
    /// Evaluates the function given the interpretation context.
    pub fn interpret(
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

impl TerminalInstr {
    /// Evaluates the function given the interpretation context.
    pub fn interpret(
        &self,
        _value: Option<Value>,
        ctx: &mut InterpretationContext,
    ) -> Result<(), InterpretationError> {
        match self {
            Self::Trap => {
                ctx.set_trapped();
                Ok(())
            }
            Self::Return(instr) => {
                let return_value = ctx.value_results[instr.return_value()];
                ctx.set_output(return_value)?;
                ctx.set_returned();
                Ok(())
            }
            Self::Br(instr) => {
                ctx.switch_to_block(instr.target());
                Ok(())
            }
            Self::Ite(instr) => {
                let condition = ctx.value_results[instr.condition()];
                match condition {
                    Const::Bool(true) => {
                        ctx.switch_to_block(instr.true_target())
                    }
                    Const::Bool(false) => {
                        ctx.switch_to_block(instr.false_target())
                    }
                    _ => unreachable!(),
                }
                Ok(())
            }
            Self::BranchTable(_instr) => unimplemented!(),
        }
    }
}

impl ReinterpretInstr {
    /// Evaluates the function given the interpretation context.
    pub fn interpret(
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

impl IntInstr {
    /// Evaluates the function given the interpretation context.
    pub fn interpret(
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

impl UnaryIntInstr {
    /// Evaluates the function given the interpretation context.
    pub fn interpret(
        &self,
        _value: Option<Value>,
        _ctx: &mut InterpretationContext,
    ) -> Result<(), InterpretationError> {
        unimplemented!()
    }
}

impl TruncateIntInstr {
    /// Evaluates the function given the interpretation context.
    pub fn interpret(
        &self,
        _value: Option<Value>,
        _ctx: &mut InterpretationContext,
    ) -> Result<(), InterpretationError> {
        unimplemented!()
    }
}

impl ExtendIntInstr {
    /// Evaluates the function given the interpretation context.
    pub fn interpret(
        &self,
        _value: Option<Value>,
        _ctx: &mut InterpretationContext,
    ) -> Result<(), InterpretationError> {
        unimplemented!()
    }
}

impl IntToFloatInstr {
    /// Evaluates the function given the interpretation context.
    pub fn interpret(
        &self,
        _value: Option<Value>,
        _ctx: &mut InterpretationContext,
    ) -> Result<(), InterpretationError> {
        unimplemented!()
    }
}

impl CompareIntInstr {
    /// Evaluates the function given the interpretation context.
    pub fn interpret(
        &self,
        value: Option<Value>,
        ctx: &mut InterpretationContext,
    ) -> Result<(), InterpretationError> {
        let result_value = value.expect("missing value for instruction");
        let lhs_value = ctx.value_results[self.lhs()];
        let rhs_value = ctx.value_results[self.rhs()];
        let lhs_value = match lhs_value {
            Const::Int(int_const) => int_const,
            _ => unreachable!(),
        };
        let rhs_value = match rhs_value {
            Const::Int(int_const) => int_const,
            _ => unreachable!(),
        };
        let result = match self.op() {
            CompareIntOp::Eq => {
                match (lhs_value, rhs_value) {
                    (IntConst::I8(lhs), IntConst::I8(rhs)) => {
                        Const::Bool(lhs == rhs)
                    }
                    (IntConst::I16(lhs), IntConst::I16(rhs)) => {
                        Const::Bool(lhs == rhs)
                    }
                    (IntConst::I32(lhs), IntConst::I32(rhs)) => {
                        Const::Bool(lhs == rhs)
                    }
                    (IntConst::I64(lhs), IntConst::I64(rhs)) => {
                        Const::Bool(lhs == rhs)
                    }
                    _ => unreachable!(),
                }
            }
            CompareIntOp::Slt => {
                match (lhs_value, rhs_value) {
                    (IntConst::I8(lhs), IntConst::I8(rhs)) => {
                        Const::Bool(lhs < rhs)
                    }
                    (IntConst::I16(lhs), IntConst::I16(rhs)) => {
                        Const::Bool(lhs < rhs)
                    }
                    (IntConst::I32(lhs), IntConst::I32(rhs)) => {
                        Const::Bool(lhs < rhs)
                    }
                    (IntConst::I64(lhs), IntConst::I64(rhs)) => {
                        Const::Bool(lhs < rhs)
                    }
                    _ => unreachable!(),
                }
            }
            CompareIntOp::Ule => {
                match (lhs_value, rhs_value) {
                    (IntConst::I8(lhs), IntConst::I8(rhs)) => {
                        Const::Bool(lhs as u8 <= rhs as u8)
                    }
                    (IntConst::I16(lhs), IntConst::I16(rhs)) => {
                        Const::Bool(lhs as u16 <= rhs as u16)
                    }
                    (IntConst::I32(lhs), IntConst::I32(rhs)) => {
                        Const::Bool(lhs as u32 <= rhs as u32)
                    }
                    (IntConst::I64(lhs), IntConst::I64(rhs)) => {
                        Const::Bool(lhs as u64 <= rhs as u64)
                    }
                    _ => unreachable!(),
                }
            }
            _ => unimplemented!(),
        };
        ctx.value_results.insert(result_value, result);
        Ok(())
    }
}

impl BinaryIntInstr {
    /// Evaluates the function given the interpretation context.
    pub fn interpret(
        &self,
        value: Option<Value>,
        ctx: &mut InterpretationContext,
    ) -> Result<(), InterpretationError> {
        let result_value = value.expect("missing value for instruction");
        let lhs_value = ctx.value_results[self.lhs()];
        let rhs_value = ctx.value_results[self.rhs()];
        let lhs_value = match lhs_value {
            Const::Int(int_const) => int_const,
            _ => unreachable!(),
        };
        let rhs_value = match rhs_value {
            Const::Int(int_const) => int_const,
            _ => unreachable!(),
        };
        let result = match self.op() {
            BinaryIntOp::Add => {
                match (lhs_value, rhs_value) {
                    (IntConst::I8(lhs), IntConst::I8(rhs)) => {
                        IntConst::I8(lhs.wrapping_add(rhs))
                    }
                    (IntConst::I16(lhs), IntConst::I16(rhs)) => {
                        IntConst::I16(lhs.wrapping_add(rhs))
                    }
                    (IntConst::I32(lhs), IntConst::I32(rhs)) => {
                        IntConst::I32(lhs.wrapping_add(rhs))
                    }
                    (IntConst::I64(lhs), IntConst::I64(rhs)) => {
                        IntConst::I64(lhs.wrapping_add(rhs))
                    }
                    _ => unreachable!(),
                }
            }
            BinaryIntOp::Mul => {
                match (lhs_value, rhs_value) {
                    (IntConst::I8(lhs), IntConst::I8(rhs)) => {
                        IntConst::I8(lhs.wrapping_mul(rhs))
                    }
                    (IntConst::I16(lhs), IntConst::I16(rhs)) => {
                        IntConst::I16(lhs.wrapping_mul(rhs))
                    }
                    (IntConst::I32(lhs), IntConst::I32(rhs)) => {
                        IntConst::I32(lhs.wrapping_mul(rhs))
                    }
                    (IntConst::I64(lhs), IntConst::I64(rhs)) => {
                        IntConst::I64(lhs.wrapping_mul(rhs))
                    }
                    _ => unreachable!(),
                }
            }
            _ => unimplemented!(),
        };
        ctx.value_results.insert(result_value, result.into());
        Ok(())
    }
}
