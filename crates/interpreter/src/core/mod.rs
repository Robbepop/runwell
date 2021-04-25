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

//! Allows to interpret the Runwell IR.

mod act_frame;
mod frame;
mod stack;

pub use self::act_frame::ActivationFrame;
use self::{
    frame::Frame,
    stack::{Register, Stack},
};
pub use crate::error::InterpretationError;
use crate::instr::{InterpretInstr, InterpretationFlow};
use ir::primitive::Func;
use module::{utils::Function, Module};

/// The evaluation context for the entire virtual machine.
///
/// This holds all the mutable data such as the actual linear memory.
#[derive(Debug)]
pub struct EvaluationContext<'a> {
    /// The module that holds immutable data.
    module: &'a Module,
    /// The stack and function frames.
    frames: Frames<'a>,
    /// A scratch buffer to store intermediate state between function executions.
    scratch: Vec<Register>,
}

/// The value stack and the function frames.
#[derive(Debug)]
pub struct Frames<'a> {
    /// The module that holds immutable data.
    module: &'a Module,
    /// The stack on which functions are operating.
    stack: Stack,
    /// The currently active frames.
    frames: Vec<Frame>,
}

impl<'a> Frames<'a> {
    /// Creates a new value stack and function frame.
    fn new(module: &'a Module) -> Self {
        Self {
            module,
            stack: Default::default(),
            frames: Default::default(),
        }
    }

    /// Pushes a stack frame onto the stack for the given function.
    pub fn push_frame<I>(
        &mut self,
        func: Func,
        inputs: I,
    ) -> Result<(), InterpretationError>
    where
        I: IntoIterator<Item = u64>,
    {
        let function = self
            .module
            .get_function(func)
            .expect("encountered invalid function index");
        let frame_size = function.body().max_value().into_raw().into_u32() + 1;
        let sp = self.stack.push(frame_size);
        let given_inputs = self.stack.initialize(sp, inputs);
        let required_inputs = function.inputs().len();
        if given_inputs != required_inputs {
            return Err(InterpretationError::UnmatchingInputValues {
                given_inputs,
                required_inputs,
            })
        }
        self.frames
            .push(Frame::new(func, sp, function.body().entry_block()));
        Ok(())
    }

    /// Pops the last stack frame from the stack.
    pub fn pop_frame(&mut self) {
        let frame = self.frames.pop().expect("encountered missing stack frame");
        self.stack.pop(frame.stack_pointer());
    }

    /// Returns a mutable reference to the stack and to the last function frame.
    fn last_frame_mut(&mut self) -> Option<(&mut Stack, &mut Frame)> {
        let frame = self.frames.last_mut()?;
        Some((&mut self.stack, frame))
    }
}

impl<'a> EvaluationContext<'a> {
    /// Creates a new evaluation context from the given shared reference to the store.
    pub fn new(module: &'a Module) -> Self {
        Self {
            module,
            frames: Frames::new(module),
            scratch: Default::default(),
        }
    }

    /// Evaluates the given function.
    ///
    /// This creates a new call frame for the function which can be costly.
    /// The outputs are returned in order of their function definition appearance.
    ///
    /// # Note
    ///
    /// This API is for use externally to the interpreter.
    /// Users call it in order to invoke the entry level function.
    pub fn evaluate_function<I, O>(
        &mut self,
        func: Func,
        inputs: I,
        outputs: O,
    ) -> Result<(), InterpretationError>
    where
        I: IntoIterator<Item = u64>,
        O: FnMut(u64),
    {
        self.frames.push_frame(func, inputs)?;
        let function = self
            .module
            .get_function(func)
            .expect("encountered invalid function index");
        self.evaluate_function_frame(function, outputs)?;
        Ok(())
    }

    /// Evaluates the given function using the function frame.
    ///
    /// The function frame is expected to already be setup with the input parameters.
    /// The outputs are returned in order of their function definition appearance.
    ///
    /// # Note
    ///
    /// This API is for use internally to the interpreter.
    fn evaluate_function_frame<O>(
        &mut self,
        mut function: Function<'a>,
        mut outputs: O,
    ) -> Result<(), InterpretationError>
    where
        O: FnMut(u64),
    {
        loop {
            let Self {
                module,
                frames,
                scratch,
            } = self;
            let (stack, frame) = match frames.last_frame_mut() {
                Some(last) => last,
                None => panic!("cannot execute without an activation frame"),
            };
            let act = ActivationFrame::new(module, stack, frame, scratch);
            match function.body().interpret_instr(&[], act)? {
                InterpretationFlow::Continue => continue,
                InterpretationFlow::Return => {
                    self.frames.pop_frame();
                    if self.evaluate_return_flow(&mut function) {
                        break
                    }
                }
                InterpretationFlow::TailCall(func) => {
                    self.frames.pop_frame();
                    self.update_and_push_frame(func, &mut function);
                }
                InterpretationFlow::Call(func) => {
                    self.update_and_push_frame(func, &mut function);
                }
            }
        }
        for return_value in self.scratch.drain(..) {
            outputs(return_value.into_u64())
        }
        Ok(())
    }

    /// Pushes another function frame onto the stack of frames.
    ///
    /// Initializes the new function frame with the values found in the scratch buffer.
    /// Updates the function pointer to point to the new function frame.
    fn update_and_push_frame(
        &mut self,
        func: Func,
        function: &mut Function<'a>,
    ) {
        let called_function = self
            .module
            .get_function(func)
            .expect("encountered invalid function index");
        *function = called_function;
        self.frames
            .push_frame(func, self.scratch.drain(..).map(Register::into_u64))
            .expect("encountered invalid function for call");
    }

    /// Evaluates the control flow when an interpreted function returns to its caller.
    ///
    /// Handles propagation of the returned results into the callers registers.
    /// Updates the current `function` to the caller's function if any.
    ///
    /// Returns `true` if there was no caller so that the interpreter returns entirely
    /// to the interpreter's own caller.
    fn evaluate_return_flow(&mut self, function: &mut Function<'a>) -> bool {
        match self.frames.last_frame_mut() {
            Some((stack, next_frame)) => {
                let func = next_frame.func();
                let next_function = self
                    .module
                    .get_function(func)
                    .expect("encountered invalid function index");
                let (output_values, _) = next_function
                    .body()
                    .instruction_and_value(
                        next_frame.current_block(),
                        next_frame.last_instruction_counter(),
                    )
                    .expect("missing instruction in function");
                let ptr = next_frame.stack_pointer();
                for (output_value, output_result) in output_values
                    .iter()
                    .copied()
                    .zip(self.scratch.iter().copied().map(Register::into_u64))
                {
                    if let Some(output_value) = output_value {
                        stack.write_register(ptr + output_value, output_result);
                    }
                }
                *function = next_function;
                false
            }
            None => true,
        }
    }
}
