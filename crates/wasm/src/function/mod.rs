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

//! Utilities to translate a Wasm function body into a Runwell function body.

#![allow(unused_variables)]

mod control;
mod error;
mod operator;
mod stack;

use self::control::{
    BlockControlFrame,
    ControlFlowFrame,
    ControlFrameKind,
    FunctionBodyFrame,
    IfControlFrame,
    LoopControlFrame,
    UnreachableControlFrame,
    WasmBlockType,
};
pub use self::error::TranslateError;
pub(self) use self::{
    control::{ControlFlowStack, ElseData},
    stack::ValueStack,
};
use crate::{Error, Type};
use core::{convert::TryFrom as _, fmt};
use ir::primitive::{Block, Func};
use module::{builder::FunctionBuilder, FunctionBody, ModuleResources};
use wasmparser::{BinaryReader, FuncValidator, Range, ValidatorResources};

/// Translate a Wasm function body into a Runwell function body.
///
/// # Note
///
/// - The `buffer` contains the binary encoded Wasm function body.
/// - The Wasm function body is parsed and validated during construction.
pub fn translate_function_body(
    range: Range,
    buffer: Vec<u8>,
    validator: FuncValidator<ValidatorResources>,
    func: Func,
    res: &ModuleResources,
) -> Result<FunctionBody, Error> {
    let wasm_body = wasmparser::FunctionBody::new(range.start, &buffer[..]);
    let function_body =
        FunctionBodyTranslator::new(wasm_body, validator, func, res)
            .translate()?;
    Ok(function_body)
}

/// Translates Wasm function bodies into Runwell function bodies.
struct FunctionBodyTranslator<'a, 'b> {
    // The Wasm function body.
    reader: BinaryReader<'a>,
    /// Used to validate a function on the fly during translation.
    validator: FuncValidator<ValidatorResources>,
    /// The unique function index associated to the translated function body.
    func: Func,
    /// The immutable module resources required to translate the function body.
    res: &'b ModuleResources,
    /// The Runwell function body builder.
    builder: FunctionBuilder<'b>,
    /// The emulated Wasm stack to translate the Wasm stack machine.
    value_stack: ValueStack,
    /// The stack of control flow frames.
    control_stack: ControlFlowStack,
    /// Determines if the current control flow is reachable.
    reachable: bool,
}

impl<'a, 'b> fmt::Debug for FunctionBodyTranslator<'a, 'b> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("FunctionBodyTranslator")
            .field("reader", &self.reader)
            .field("func", &self.func)
            .field("res", &self.res)
            .field("builder", &self.builder)
            .field("value_stack", &self.value_stack)
            .field("control_stack", &self.control_stack)
            .finish()
    }
}

impl<'a, 'b> FunctionBodyTranslator<'a, 'b> {
    /// Creates a new Wasm to Runwell function body translator.
    fn new(
        wasm_body: wasmparser::FunctionBody<'a>,
        validator: FuncValidator<ValidatorResources>,
        func: Func,
        res: &'b ModuleResources,
    ) -> Self {
        let mut reader = wasm_body.get_binary_reader();
        let _body_size = reader
            .read_var_u32()
            .expect("expect function size in bytes");
        Self {
            reader,
            validator,
            func,
            res,
            builder: FunctionBody::build(func, res),
            value_stack: Default::default(),
            control_stack: Default::default(),
            reachable: true,
        }
    }

    /// Translates the Wasm function body into an equivalent Runwell function body.
    fn translate(mut self) -> Result<FunctionBody, Error> {
        self.translate_local_variables()?;
        self.initialize_entry_block()?;
        self.translate_operators()?;
        let body = self.builder.finalize()?;
        Ok(body)
    }

    /// Parses, validates and translates the Wasm local variables into
    /// Runwell variable declarations.
    fn translate_local_variables(&mut self) -> Result<(), Error> {
        let count_locals = self.reader.read_var_u32()?;
        for _ in 0..count_locals {
            let offset = self.reader.original_position();
            let count = self.reader.read_var_u32()?;
            let ty = self.reader.read_type()?;
            self.validator.define_locals(offset, count, ty)?;
            let ty = Type::try_from(ty)?.into_inner();
            self.builder.declare_variables(count, ty)?;
        }
        Ok(())
    }

    /// Initializes the control flow frames to contain the function body frame.
    fn initialize_entry_block(&mut self) -> Result<(), Error> {
        let entry_block_type =
            self.res.get_raw_func_type(self.func).unwrap_or_else(|| {
                panic!(
                    "expected function type for {} due to validation",
                    self.func
                )
            });
        // The `exit_block` is the block that is to be branched to
        // when encountering a branch instruction to the function body
        // control frame. At the end of the Wasm translation if the
        // block was branched to it is going to contain the function's
        // final return instruction.
        let exit_block = self.builder.create_block()?;
        let block_type = WasmBlockType::from(entry_block_type);
        for &return_value in block_type.outputs(&self.res) {
            self.builder
                .create_block_parameter(exit_block, return_value)?;
        }
        self.control_stack.push_frame(ControlFlowFrame::Body(
            FunctionBodyFrame::new(
                WasmBlockType::from(entry_block_type),
                exit_block,
            ),
        ));
        Ok(())
    }

    /// Parses, validates and translates the Wasm operands into Runwell
    /// function body instructions and basic blocks.
    fn translate_operators(&mut self) -> Result<(), Error> {
        while !self.reader.eof() {
            let offset = self.reader.original_position();
            let op = self.reader.read_operator()?;
            self.validator.op(offset, &op)?;
            self.translate_operator(offset, op)?;
        }
        let offset = self.reader.original_position();
        self.validator.finish(offset)?;
        self.finalize_exit_block()?;
        Ok(())
    }

    /// Finalizes the `exit_block` of the function body control frame.
    ///
    /// This adds the final `return` instruction to the `exit_block`.
    ///
    /// After translating all Wasm operators and encountering the final
    /// `End` operator we should be left in a state where the current
    /// basic block refers to the `exit_block`.
    fn finalize_exit_block(&mut self) -> Result<(), Error> {
        let current = self.builder.current_block()?;
        if !self.reachable || !self.builder.is_block_reachable(current) {
            return Ok(())
        }
        let entry_block_type =
            self.res.get_raw_func_type(self.func).unwrap_or_else(|| {
                panic!(
                    "expected function type for {} due to validation",
                    self.func
                )
            });
        let block_type = WasmBlockType::from(entry_block_type);
        let len_outputs = block_type.outputs(&self.res).len();
        let outputs = self
            .value_stack
            .pop_n(len_outputs)?
            .map(|entry| entry.value);
        self.builder.ins()?.return_values(outputs)?;
        Ok(())
    }

    /// Push a Wasm `block` on the control flow stack.
    fn push_control_block(&mut self, block: Block, block_type: WasmBlockType) {
        let block_inputs = block_type.inputs(&self.res);
        debug_assert!(block_inputs.len() <= self.value_stack.len());
        self.control_stack.push_frame(ControlFlowFrame::Block(
            BlockControlFrame::new(
                block_type,
                self.value_stack.len() - block_inputs.len(),
                block,
            ),
        ));
    }

    /// Push a Wasm `loop` on the control flow stack.
    fn push_control_loop(
        &mut self,
        loop_header: Block,
        loop_exit: Block,
        block_type: WasmBlockType,
    ) {
        let block_inputs = block_type.inputs(&self.res);
        debug_assert!(block_inputs.len() <= self.value_stack.len());
        self.control_stack.push_frame(ControlFlowFrame::Loop(
            LoopControlFrame::new(
                block_type,
                self.value_stack.len() - block_inputs.len(),
                loop_header,
                loop_exit,
            ),
        ));
    }

    /// Pushes a Wasm `if` on the control flow stack.
    fn push_control_if(
        &mut self,
        if_exit: Block,
        else_data: ElseData,
        block_type: WasmBlockType,
    ) -> Result<(), Error> {
        let block_inputs = block_type.inputs(&self.res);
        debug_assert!(block_inputs.len() <= self.value_stack.len());
        // Push a second copy of our `if`'s parameters on the stack. This lets
        // us avoid saving them on the side in the `ControlFrameStack` for our
        // `else` block (if it exists), which would require a second heap
        // allocation. See also the comment in `translate_operator` for
        // `Operator::Else`.
        // for i in (self.stack.len() - len_inputs)..self.stack.len() {
        for n in (0..block_inputs.len()).rev() {
            let entry = self.value_stack.last_n(n)?;
            self.value_stack.push(entry.value, entry.ty);
        }
        self.control_stack.push_frame(ControlFlowFrame::If(
            IfControlFrame::new(
                block_type,
                self.value_stack.len() - block_inputs.len(),
                if_exit,
                else_data,
                self.reachable,
            ),
        ));
        Ok(())
    }

    /// Pushes an unreachable Wasm control flow frame to the control flow stack.
    fn push_unreachable_control_frame(
        &mut self,
        kind: ControlFrameKind,
        block_type: WasmBlockType,
    ) -> Result<(), Error> {
        let block_inputs = block_type.inputs(&self.res);
        self.control_stack.push_frame(ControlFlowFrame::Unreachable(
            UnreachableControlFrame::new(
                block_type,
                self.value_stack.len() - block_inputs.len(),
                kind,
            ),
        ));
        Ok(())
    }
}
