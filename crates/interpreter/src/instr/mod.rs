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

use super::InterpretationError;
use crate::core::ActivationFrame;
use ir::{
    instr::{
        CallInstr,
        ConstInstr,
        Instruction,
        PhiInstr,
        ReinterpretInstr,
        SelectInstr,
    },
    primitive::{Func, Value},
};
use module::FunctionBody;

/// Implemented by Runwell IR instructions to make them interpretable.
pub trait InterpretInstr {
    /// Evaluates the function given the interpretation context.
    fn interpret_instr(
        &self,
        outputs: &[Option<Value>],
        frame: ActivationFrame,
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
    /// In this case the registers are assumed to be initialized
    /// with the functions inputs. The outer evaluation context
    /// then has to check the acquired inputs against the called
    /// function signature.
    TailCall(Func),
    /// The function calls another function.
    Call(Func),
}

fn extract_single_output(outputs: &[Option<Value>]) -> Value {
    debug_assert_eq!(outputs.len(), 1);
    outputs[0].expect("encountered missing single output SSA value")
}

impl InterpretInstr for FunctionBody {
    fn interpret_instr(
        &self,
        outputs: &[Option<Value>],
        mut frame: ActivationFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        debug_assert!(outputs.is_empty());
        let block = frame.current_block();
        let ic = frame.bump_instruction_counter();
        let (instr_values, instruction) = self
            .instruction_and_value(block, ic)
            .expect("missing instruction in function");
        instruction.interpret_instr(instr_values, frame)
    }
}

impl InterpretInstr for Instruction {
    fn interpret_instr(
        &self,
        outputs: &[Option<Value>],
        frame: ActivationFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        match self {
            Self::Call(instr) => instr.interpret_instr(outputs, frame),
            Self::CallIndirect(_instr) => unimplemented!(),
            Self::Const(instr) => instr.interpret_instr(outputs, frame),
            Self::MemoryGrow(_instr) => unimplemented!(),
            Self::MemorySize(_instr) => unimplemented!(),
            Self::Phi(instr) => instr.interpret_instr(outputs, frame),
            Self::HeapAddr(_instr) => unimplemented!(),
            Self::Load(_instr) => unimplemented!(),
            Self::Store(_instr) => unimplemented!(),
            Self::Select(instr) => instr.interpret_instr(outputs, frame),
            Self::Reinterpret(instr) => instr.interpret_instr(outputs, frame),
            Self::Terminal(instr) => instr.interpret_instr(outputs, frame),
            Self::Terminal2(_instr) => unimplemented!(),
            Self::Int(instr) => instr.interpret_instr(outputs, frame),
            Self::Float(instr) => instr.interpret_instr(outputs, frame),
        }
    }
}

impl InterpretInstr for PhiInstr {
    fn interpret_instr(
        &self,
        outputs: &[Option<Value>],
        mut frame: ActivationFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let return_value = extract_single_output(outputs);
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
        outputs: &[Option<Value>],
        mut frame: ActivationFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let return_value = extract_single_output(outputs);
        frame.write_register(return_value, self.const_value().into_bits64());
        Ok(InterpretationFlow::Continue)
    }
}

impl InterpretInstr for SelectInstr {
    fn interpret_instr(
        &self,
        outputs: &[Option<Value>],
        mut frame: ActivationFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let return_value = extract_single_output(outputs);
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
        _outputs: &[Option<Value>],
        mut frame: ActivationFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        frame.clear_scratch();
        for param in self.params().iter().copied() {
            let bits = frame.read_register(param);
            frame.push_scratch(bits);
        }
        Ok(InterpretationFlow::Call(self.func()))
    }
}

impl InterpretInstr for ReinterpretInstr {
    fn interpret_instr(
        &self,
        outputs: &[Option<Value>],
        mut frame: ActivationFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let return_value = extract_single_output(outputs);
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
