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

/// Extracts the single output value from the outputs slice or skips execution.
macro_rules! extract_single_output_or_skip {
    ($outputs:expr) => {{
        debug_assert!(
            $outputs.len() == 1,
            "expected 1 static output value but found {}",
            $outputs.len(),
        );
        match $outputs[0] {
            Some(output) => output,
            None => return Ok(InterpretationFlow::Continue),
        }
    }};
}

mod float;
mod int;
mod primitive;
mod terminal;

use self::primitive::{PrimitiveInteger, PrimitiveIntegerDivision, I1};
use super::InterpretationError;
use crate::core::ActivationFrame;
use ir::{
    instr::{
        CallInstr,
        ConstInstr,
        Instruction,
        MatchSelectInstr,
        ReinterpretInstr,
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
            Self::HeapAddr(_instr) => unimplemented!(),
            Self::Load(_instr) => unimplemented!(),
            Self::Store(_instr) => unimplemented!(),
            Self::Select(instr) => instr.interpret_instr(outputs, frame),
            Self::Reinterpret(instr) => instr.interpret_instr(outputs, frame),
            Self::Terminal(instr) => instr.interpret_instr(outputs, frame),
            Self::Int(instr) => instr.interpret_instr(outputs, frame),
            Self::Float(instr) => instr.interpret_instr(outputs, frame),
        }
    }
}

impl InterpretInstr for ConstInstr {
    fn interpret_instr(
        &self,
        outputs: &[Option<Value>],
        mut frame: ActivationFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let return_value = extract_single_output_or_skip!(outputs);
        frame.write_register(return_value, self.const_value().into_bits64());
        Ok(InterpretationFlow::Continue)
    }
}

impl InterpretInstr for MatchSelectInstr {
    fn interpret_instr(
        &self,
        outputs: &[Option<Value>],
        mut frame: ActivationFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let selected = frame.read_register(self.selector());
        let target_results = self
            .target_results(selected as usize)
            .unwrap_or_else(|| self.default_results());
        for (&target_result, output) in target_results.iter().zip(outputs) {
            if let Some(output) = output {
                // Only write a result value if the result value is going to be read.
                let result = frame.read_register(target_result);
                frame.write_register(*output, result);
            }
        }
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
        let return_value = extract_single_output_or_skip!(outputs);
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
