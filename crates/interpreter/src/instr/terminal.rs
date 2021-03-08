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

use crate::core::ActivationFrame;

use super::{InterpretInstr, InterpretationError, InterpretationFlow};
use ir::{
    instr::{
        BranchInstr,
        BranchTableInstr,
        IfThenElseInstr,
        ReturnInstr,
        TailCallIndirectInstr,
        TailCallInstr,
        TerminalInstr,
    },
    primitive::Value,
};

impl InterpretInstr for TerminalInstr {
    fn interpret_instr(
        &self,
        outputs: &[Option<Value>],
        frame: ActivationFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        match self {
            Self::Trap => Err(InterpretationError::EvaluationHasTrapped),
            Self::Return(instr) => instr.interpret_instr(outputs, frame),
            Self::Br(instr) => instr.interpret_instr(outputs, frame),
            Self::Ite(instr) => instr.interpret_instr(outputs, frame),
            Self::TailCall(instr) => instr.interpret_instr(outputs, frame),
            Self::TailCallIndirect(instr) => {
                instr.interpret_instr(outputs, frame)
            }
            Self::BranchTable(instr) => instr.interpret_instr(outputs, frame),
        }
    }
}

impl InterpretInstr for ReturnInstr {
    fn interpret_instr(
        &self,
        _outputs: &[Option<Value>],
        mut frame: ActivationFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        frame.clear_scratch();
        for param in self.return_values().iter().copied() {
            let bits = frame.read_register(param);
            frame.push_scratch(bits);
        }
        Ok(InterpretationFlow::Return)
    }
}

impl InterpretInstr for BranchInstr {
    fn interpret_instr(
        &self,
        _outputs: &[Option<Value>],
        mut frame: ActivationFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        frame.continue_along_edge(self.edge());
        Ok(InterpretationFlow::Continue)
    }
}

impl InterpretInstr for IfThenElseInstr {
    fn interpret_instr(
        &self,
        _outputs: &[Option<Value>],
        mut frame: ActivationFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let condition = frame.read_register(self.condition());
        let edge = if condition != 0 {
            self.then_edge()
        } else {
            self.else_edge()
        };
        frame.continue_along_edge(edge);
        Ok(InterpretationFlow::Continue)
    }
}

impl InterpretInstr for TailCallInstr {
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
        Ok(InterpretationFlow::TailCall(self.func()))
    }
}

impl InterpretInstr for TailCallIndirectInstr {
    fn interpret_instr(
        &self,
        _outputs: &[Option<Value>],
        _frame: ActivationFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        unimplemented!()
    }
}

impl InterpretInstr for BranchTableInstr {
    fn interpret_instr(
        &self,
        _outputs: &[Option<Value>],
        mut frame: ActivationFrame,
    ) -> Result<InterpretationFlow, InterpretationError> {
        let selected = frame.read_register(self.selector());
        let target_edge = self
            .target_edges()
            .get(selected as usize)
            .copied()
            .unwrap_or_else(|| self.default_target());
        frame.continue_along_edge(target_edge);
        Ok(InterpretationFlow::Continue)
    }
}
