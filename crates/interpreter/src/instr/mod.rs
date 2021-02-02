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

mod float;
mod int;
mod terminal;

use super::{EvaluationContext, Func, FunctionFrame, InterpretationError};
use ir::{
    instr::{
        CallInstr,
        ConstInstr,
        Instruction,
        PhiInstr,
        ReinterpretInstr,
        SelectInstr,
    },
    primitive::Value,
};
use module::Function;

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

pub const MISSING_RETURN_VALUE_ERRSTR: &str =
    "missing return value for returning instruction";

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
            Self::HeapAddr(_instr) => unimplemented!(),
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
            Self::Float(instr) => {
                instr.interpret_instr(return_value, ctx, frame)
            }
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
