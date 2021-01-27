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

pub(in crate::ir) use self::frame::FunctionFrame;
pub use self::{
    error::InterpretationError,
    instr::{InterpretInstr, InterpretationFlow},
};
use super::{builder::Function, primitive::Value};
use crate::entity::{EntityArena, Idx, RawIdx};

/// A function index.
pub type Func = Idx<Function>;

/// Holds all data that is immutable during a function evaluation.
///
/// This includes but is not limited to definitions of functions,
/// linear memories, tables, global variables etc.
#[derive(Debug, Default)]
pub struct Store {
    functions: EntityArena<Function>,
}

impl Store {
    /// Pushes a function to the store and returns its key.
    pub fn push_function(&mut self, function: Function) -> Func {
        self.functions.alloc(function)
    }

    /// Returns a shared reference to the function associated to the given index.
    pub fn get_fn(&self, func: Func) -> &Function {
        &self.functions[func]
    }
}

/// The evaluation context for the entire virtual machine.
///
/// This holds all the mutable data such as the actual linear memory.
#[derive(Debug)]
pub struct EvaluationContext<'a> {
    pub store: &'a Store,
    cached_frames: Vec<FunctionFrame>,
}

impl<'a> EvaluationContext<'a> {
    /// Creates a new evaluation context from the given shared reference to the store.
    pub fn new(store: &'a Store) -> Self {
        Self {
            store,
            cached_frames: Vec::new(),
        }
    }

    /// Evaluates the given function.
    ///
    /// This creates a new call frame for the function which can be costly.
    /// For tail calls this function should not be used.
    pub fn evaluate_function<I, O>(
        &mut self,
        func: Func,
        inputs: I,
        mut outputs: O,
    ) -> Result<(), InterpretationError>
    where
        I: IntoIterator<Item = u64>,
        O: FnMut(Value, u64),
    {
        let mut frame = self.create_frame();
        let function = self.store.get_fn(func);
        frame.initialize(function, inputs)?;
        loop {
            match function.interpret_instr(None, self, &mut frame)? {
                InterpretationFlow::Continue => continue,
                InterpretationFlow::Return => break,
                InterpretationFlow::TailCall(_id) => {
                    // TODO:
                    //  - replace `fun` with the function associated to the ID
                    //  - check if the inputs in the first N registers of `frame` match
                    //    the new `fun` signature.
                    unimplemented!()
                }
            }
        }
        for (n, _) in function.outputs().iter().enumerate() {
            let result_value = Value::from_raw(RawIdx::from_u32(n as u32));
            let result = frame.read_register(result_value);
            outputs(result_value, result)
        }
        self.release_frame(frame);
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
