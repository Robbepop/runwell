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

mod instr;

pub use self::instr::InterpretInstr;
use super::builder::{Function, ValueAssoc};
use crate::{
    entity::{ComponentMap, RawIdx},
    ir::primitive::{Block, Const, Type, Value},
};
use core::mem::replace;
use derive_more::{Display, Error};

/// The interpretation context.
///
/// Stores values required during interpretation of a function.
#[derive(Debug)]
pub struct InterpretationContext {
    /// The latest results of all values involved in the evaluation.
    ///
    /// # Note
    ///
    /// This is initialized with the inputs of the function evaluation.
    pub(in crate::ir) value_results: ComponentMap<Value, Const>,
    /// The currently executed basic block.
    ///
    /// # Note
    ///
    /// Must be initialized with the functions entry block.
    current_block: Block,
    /// The last visited block.
    ///
    /// Used to resolve phi instruction operands.
    ///
    /// # Note
    ///
    /// Is initialized as `None` before function evaluation.
    last_block: Option<Block>,
    /// The index of the currently executed instruction
    /// of the currently executed basic block.
    instruction_counter: usize,
    /// The result returned by the evaluation if any.
    ///
    /// # Note
    ///
    /// Is initialized as `None` before function evaluation.
    output: Option<Const>,
    /// Is `true` if the evaluation of the function has trapped.
    ///
    /// # Note
    ///
    /// Initialized to `false` before function evaluation.
    has_trapped: bool,
    /// Is `true` if the evaluation of the function is finished.
    ///
    /// # Note
    ///
    /// Initialized to `false` before function evaluation.
    has_returned: bool,
    /// The current state of function evaluation.
    state: EvaluationState,
}

impl Default for InterpretationContext {
    fn default() -> Self {
        Self {
            value_results: Default::default(),
            current_block: Block::from_raw(RawIdx::from_u32(0)),
            last_block: None,
            instruction_counter: 0,
            output: None,
            has_trapped: false,
            has_returned: false,
            state: EvaluationState::Initialization,
        }
    }
}

/// The state of the function evaluation.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum EvaluationState {
    /// The function evaluation is initializing.
    Initialization,
    /// The function is currently evaluating.
    Evaluation,
    /// The function evaluation has finished.
    Finished,
}

impl Default for EvaluationState {
    fn default() -> Self {
        Self::Initialization
    }
}

/// An error that may occure while evaluating a function.
#[derive(Debug, Display, Error, PartialEq, Eq, Hash)]
pub enum InterpretationError {
    #[display(fmt = "the function evaluation has not yet finished")]
    UnfinishedEvaluation,
    #[display(fmt = "the function evaluation has trapped")]
    EvaluationHasTrapped,
    #[display(
        fmt = "tried to initialize the non-input {} to {}",
        non_input,
        init
    )]
    TriedToInitializeNonInput { non_input: Value, init: Const },
    #[display(
        fmt = "tried to initialize input {} with type {} that requires type {}",
        value,
        given_type,
        expected_type
    )]
    UnmatchingInputTypes {
        value: Value,
        given_type: Type,
        expected_type: Type,
    },
    #[display(fmt = "tried to read uninitialized input {}", input)]
    UninitializedInput { input: Value },
    #[display(
        fmt = "encountered duplicate output values. first: {}, second: {}",
        prev_output,
        output
    )]
    AlreadySetOutput { output: Const, prev_output: Const },
}

impl InterpretationContext {
    /// Initializes the interpretation context for the function with the given inputs.
    ///
    /// # Errors
    ///
    /// - If the given inputs do not match the input signature of the function.
    /// - If the function evaluation traps.
    pub fn interpret(
        &mut self,
        function: &Function,
        inputs: &[Const],
    ) -> Result<Option<Const>, InterpretationError> {
        self.reset();
        self.current_block = function.entry_block();
        for (n, &input) in inputs.iter().enumerate() {
            let value = Value::from_raw(RawIdx::from_u32(n as u32));
            match function.value_assoc[value] {
                ValueAssoc::Input(pos) => {
                    assert_eq!(pos, n as u32);
                    let value_type = input.ty();
                    let expected_type = function.value_type[value];
                    if value_type != expected_type {
                        return Err(InterpretationError::UnmatchingInputTypes {
                            value,
                            given_type: value_type,
                            expected_type,
                        })
                    }
                    self.value_results.insert(value, input);
                }
                ValueAssoc::Instr(_) => {
                    return Err(InterpretationError::TriedToInitializeNonInput {
                        non_input: value,
                        init: input,
                    })
                }
            }
        }
        self.state = EvaluationState::Evaluation;
        function.interpret(self)?;
        self.state = EvaluationState::Finished;
        Ok(self.output)
    }

    /// Resets the interpretation context so that it can evaluate a new function.
    fn reset(&mut self) {
        self.value_results.clear();
        self.last_block = None;
        self.output = None;
        self.has_trapped = false;
        self.has_returned = false;
        self.instruction_counter = 0;
        self.state = EvaluationState::Initialization;
    }

    /// Returns `true` if the function evaluation has trapped.
    pub fn has_trapped(&self) -> bool {
        self.has_trapped
    }

    /// Returns `true` if the function evaluation has finished.
    pub fn has_returned(&self) -> bool {
        self.has_returned
    }

    /// Returns the output of the function evaluation if any.
    ///
    /// # Errors
    ///
    /// - If the function evaluation has trapped.
    /// - If the evaluation has not yet finished or started.
    pub fn output(&self) -> Result<Option<Const>, InterpretationError> {
        if self.has_trapped() {
            return Err(InterpretationError::EvaluationHasTrapped)
        }
        if self.state != EvaluationState::Finished {
            return Err(InterpretationError::UnfinishedEvaluation)
        }
        Ok(self.output)
    }

    /// Switches the currently executed basic block.
    fn switch_to_block(&mut self, block: Block) {
        let last_block = replace(&mut self.current_block, block);
        self.last_block = Some(last_block);
        self.instruction_counter = 0;
    }

    /// Returns the currently executed basic block.
    pub(in crate::ir) fn current_block(&self) -> Block {
        self.current_block
    }

    /// Returns the last executed basic block if any.
    fn last_block(&self) -> Option<Block> {
        self.last_block
    }

    /// Tells the interpretation context that the function evaluation has trapped.
    fn set_trapped(&mut self) {
        assert!(!self.has_returned);
        self.has_trapped = true;
    }

    /// Tells the interpretation context that the function evaluation has finished.
    fn set_returned(&mut self) {
        assert!(!self.has_trapped);
        self.has_returned = true;
    }

    /// Bumps the instruction counter by one and returns its value before the bump.
    pub(in crate::ir) fn bump_instruction_counter(&mut self) -> usize {
        let ic = self.instruction_counter;
        self.instruction_counter += 1;
        ic
    }

    /// Sets the output to the given value.
    ///
    /// # Errors
    ///
    /// If an output has already been set.
    fn set_output(&mut self, output: Const) -> Result<(), InterpretationError> {
        if let Some(prev_output) = self.output {
            return Err(InterpretationError::AlreadySetOutput {
                prev_output,
                output,
            })
        }
        self.output = Some(output);
        Ok(())
    }
}
