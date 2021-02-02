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
};
use core::mem::replace;
use entity::RawIdx;
use ir::{
    instr::{
        BranchInstr,
        BranchTableInstr,
        IfThenElseInstr,
        ReturnInstr,
        TailCallInstr,
        TerminalInstr,
    },
    primitive::Value,
};

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
            Self::BranchTable(instr) => {
                instr.interpret_instr(return_value, ctx, frame)
            }
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
        let (_function_type, function) = ctx
            .module
            .get_function(self.func())
            .expect("encountered invalid function index");
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

impl InterpretInstr for BranchTableInstr {
    fn interpret_instr(
        &self,
        _return_value: Option<Value>,
        _ctx: &mut EvaluationContext,
        frame: &mut FunctionFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let case = frame.read_register(self.case());
        let target = self
            .targets()
            .get(case as usize)
            .copied()
            .unwrap_or_else(|| self.default_target());
        frame.switch_to_block(target);
        Ok(InterpretationFlow::Continue)
    }
}
