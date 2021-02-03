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

mod error;
mod frame;
mod instr;

#[cfg(test)]
mod tests;

pub use self::error::InterpretationError;
use self::{
    frame::FunctionFrame,
    instr::{InterpretInstr, InterpretationFlow},
};
use entity::RawIdx;
use ir::primitive::{Func, Value};
use module::{Function, FunctionType, Module};

/// The evaluation context for the entire virtual machine.
///
/// This holds all the mutable data such as the actual linear memory.
#[derive(Debug)]
pub struct EvaluationContext<'a> {
    /// The module that holds immutable data.
    pub module: &'a Module,
    /// Cached function frames to reuse memory allocations.
    cached_frames: Vec<FunctionFrame>,
}

impl<'a> EvaluationContext<'a> {
    /// Creates a new evaluation context from the given shared reference to the store.
    pub fn new(module: &'a Module) -> Self {
        Self {
            module,
            cached_frames: Vec::new(),
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
        let mut frame = self.create_frame();
        let (function_type, function) = self
            .module
            .get_function(func)
            .expect("encountered invalid function index");
        frame.initialize(function_type, function, inputs)?;
        self.evaluate_function_frame(
            function_type,
            function,
            &mut frame,
            outputs,
        )?;
        self.release_frame(frame);
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
        function_type: &'a FunctionType,
        mut function: &'a Function,
        frame: &mut FunctionFrame,
        mut outputs: O,
    ) -> Result<(), InterpretationError>
    where
        O: FnMut(u64),
    {
        loop {
            match function.interpret_instr(None, self, frame)? {
                InterpretationFlow::Continue => continue,
                InterpretationFlow::Return => break,
                InterpretationFlow::TailCall(func) => {
                    let (_function_type, called_function) = &self
                        .module
                        .get_function(func)
                        .expect("encountered invalid function index");
                    function = called_function;
                }
            }
        }
        for (n, _) in function_type.outputs().iter().enumerate() {
            let result_value = Value::from_raw(RawIdx::from_u32(n as u32));
            let result = frame.read_register(result_value);
            outputs(result)
        }
        Ok(())
    }

    /// Creates a new function evaluation frame.
    ///
    /// This might reuse function evaluation frames used in past evaluations.
    fn create_frame(&mut self) -> FunctionFrame {
        if let Some(frame) = self.cached_frames.pop() {
            return frame
        }
        Default::default()
    }

    /// Releases the function evaluation frame back to its evaluation context for caching.
    fn release_frame(&mut self, frame: FunctionFrame) {
        self.cached_frames.push(frame);
    }
}
