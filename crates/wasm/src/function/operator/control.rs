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

use super::super::{ElseData, FunctionBodyTranslator};
use crate::{
    function::control::{ControlFlowFrame, WasmBlockType},
    Error,
    TranslateError,
};
use core::convert::TryFrom;
use ir::{
    instr::operands::CompareIntOp,
    primitive::{Block, Const, IntConst, IntType, Type, Value},
};
use module::{builder::FunctionBuilder, primitive::Instr};

impl<'a, 'b> FunctionBodyTranslator<'a, 'b> {
    /// Creates a new basic block with the given parameters.
    fn block_with_params<I>(&mut self, inputs: I) -> Result<Block, Error>
    where
        I: IntoIterator<Item = Type>,
    {
        Self::block_with_params_explicit(&mut self.builder, inputs)
    }

    /// Creates a new basic block with the given parameters without `self` receiver.
    fn block_with_params_explicit<I>(
        func_builder: &mut FunctionBuilder,
        inputs: I,
    ) -> Result<Block, Error>
    where
        I: IntoIterator<Item = Type>,
    {
        let block = func_builder.create_block()?;
        for input in inputs {
            func_builder.create_block_parameter(block, input)?;
        }
        Ok(block)
    }

    /// Pop values from the value stack so that it is left at the state it was
    /// before this control-flow frame.
    pub fn truncate_value_stack_to_original_size(
        &mut self,
        frame: &ControlFlowFrame,
    ) -> Result<(), Error> {
        // The "If" frame pushes its parameters twice, so they're available to the else block
        // (see also `FuncTranslationState::push_if`).
        // Yet, the original_stack_size member accounts for them only once, so that the else
        // block can see the same number of parameters as the consequent block. As a matter of
        // fact, we need to substract an extra number of parameter values for if blocks.
        let len_dupe_args = if let ControlFlowFrame::If(if_frame) = frame {
            if_frame.block_type.inputs(&self.res).len()
        } else {
            0
        };
        self.value_stack
            .truncate(frame.original_stack_size() - len_dupe_args)?;
        Ok(())
    }
}

impl<'a, 'b> FunctionBodyTranslator<'a, 'b> {
    /// Translate a Wasm `Block` control operator.
    ///
    /// # Note
    ///
    /// Implementation ideas copied over from Cranelift: [*source*][1]
    ///
    /// [1]: https://github.com/bytecodealliance/wasmtime/blob/main/cranelift/wasm/src/code_translator.rs
    pub(super) fn translate_block(
        &mut self,
        ty: wasmparser::TypeOrFuncType,
    ) -> Result<(), Error> {
        let block_type = WasmBlockType::try_from(ty)?;
        let inputs = block_type.inputs(&self.res);
        let block = self.block_with_params(inputs.iter().copied())?;
        self.push_control_block(block, block_type);
        Ok(())
    }

    /// Translate a Wasm `Loop` control operator.
    ///
    /// # Note
    ///
    /// Implementation ideas copied over from Cranelift: [*source*][1]
    ///
    /// [1]: https://github.com/bytecodealliance/wasmtime/blob/main/cranelift/wasm/src/code_translator.rs
    pub(super) fn translate_loop(
        &mut self,
        ty: wasmparser::TypeOrFuncType,
    ) -> Result<(), Error> {
        let block_type = WasmBlockType::try_from(ty)?;
        let inputs = block_type.inputs(&self.res);
        let outputs = block_type.outputs(&self.res);
        let loop_head = self.block_with_params(inputs.iter().copied())?;
        let loop_exit = self.block_with_params(outputs.iter().copied())?;
        let args = self.value_stack.peek_n(inputs.len())?;
        self.builder
            .ins()?
            .br(loop_head, args.map(|entry| entry.value))?;
        self.push_control_loop(loop_head, loop_exit, block_type);

        // Pop the initial `Block` actuals and replace them with the `Block`'s
        // params since control flow joins at the top of the loop.
        self.value_stack.pop_n(inputs.len())?;
        self.value_stack.extend(
            self.builder
                .block_parameters(loop_head)
                .iter()
                .copied()
                .zip(inputs.iter().copied()),
        );

        self.builder.switch_to_block(loop_head)?;
        Ok(())
    }

    /// Constructs an if that compares the top most value for unequality with zero.
    fn construct_if_nez(
        &mut self,
        condition: Value,
        then_block: Block,
        else_block: Block,
        len_then_args: usize,
        len_else_args: usize,
    ) -> Result<Instr, Error> {
        let zero =
            self.builder.ins()?.constant(Const::Int(IntConst::I32(0)))?;
        debug_assert_eq!(
            self.builder.value_type(condition),
            IntType::I32.into()
        );
        let eq = self.builder.ins()?.icmp(
            IntType::I32,
            CompareIntOp::Ne,
            condition,
            zero,
        )?;
        let instr = self.builder.ins()?.if_then_else(
            eq,
            then_block,
            else_block,
            self.value_stack
                .peek_n(len_then_args)?
                .map(|entry| entry.value),
            self.value_stack
                .peek_n(len_else_args)?
                .map(|entry| entry.value),
        )?;
        Ok(instr)
    }

    /// Translate a Wasm `If` control operator.
    ///
    /// # Note
    ///
    /// Implementation ideas copied over from Cranelift: [*source*][1]
    ///
    /// [1]: https://github.com/bytecodealliance/wasmtime/blob/main/cranelift/wasm/src/code_translator.rs
    pub(super) fn translate_if(
        &mut self,
        ty: wasmparser::TypeOrFuncType,
    ) -> Result<(), Error> {
        let condition = self.value_stack.pop1()?;
        debug_assert_eq!(condition.ty, IntType::I32.into());

        let block_type = WasmBlockType::try_from(ty)?;
        let inputs = block_type.inputs(&self.res);
        let outputs = block_type.outputs(&self.res);

        let then_block = self.builder.create_block()?;
        let exit_block = self.block_with_params(outputs.iter().copied())?;
        let else_data = if inputs == outputs {
            // It is possible there is no `else` block, so we will only
            // allocate a block for it when we find the `else`. For now,
            // if the condition isn't true we jump directly to the
            // exit block following the whole `if...end`. If we do end
            // up discovering an `else`, then we will allocate a block for it
            // and go back and patch the jump.
            let branch_instr = self.construct_if_nez(
                condition.value,
                then_block,
                exit_block,
                0,
                inputs.len(),
            )?;
            ElseData::NoElse { branch_instr }
        } else {
            // The `if` type signature is not valid without an `else` block,
            // so we eagerly allocate the `else` block here.
            let else_block = self.block_with_params(inputs.iter().copied())?;
            let branch_instr = self.construct_if_nez(
                condition.value,
                then_block,
                else_block,
                0,
                inputs.len(),
            )?;
            self.builder.seal_block(else_block)?;
            ElseData::WithElse { else_block }
        };
        self.builder.seal_block(then_block)?;
        self.builder.switch_to_block(then_block)?;

        // Here we append an argument to a Block targeted by an argumentless jump instruction
        // But in fact there are two cases:
        // - either the If does not have a Else clause, in that case ty = EmptyBlock
        //   and we add nothing;
        // - either the If have an Else clause, in that case the destination of this jump
        //   instruction will be changed later when we translate the Else operator.
        self.push_control_if(exit_block, else_data, block_type)?;
        Ok(())
    }

    /// Translate a Wasm `Else` control operator.
    pub(super) fn translate_else(&mut self) -> Result<(), Error> {
        let frame = match self.control_stack.last_mut() {
            ControlFlowFrame::If(frame) => frame,
            _ => unreachable!("missing `if` frame upon encountering `else`"),
        };
        // We just finished the `then_block` (consequent), so record
        // its final reachability state.
        debug_assert!(frame.consequent_ends_reachable.is_none());
        frame.consequent_ends_reachable = Some(self.reachable);
        if !frame.head_is_reachable {
            // If the `if` was not reachable we have nothing to do
            // in the `else_block` either.
            return Ok(())
        }
        // We have a branch from the head of the `if` to the `else`.
        self.reachable = true;
        // Ensure we have a block for the `else` block (it may have
        // already been pre-allocated, see `ElseData` for details).
        let else_block = match frame.else_data {
            ElseData::WithElse { else_block } => {
                let outputs = frame.block_type.outputs(&self.res);
                let exit_block = frame.exit_block;
                self.builder.ins()?.br(
                    exit_block,
                    self.value_stack
                        .pop_n(outputs.len())?
                        .map(|entry| entry.value),
                )?;
                else_block
            }
            ElseData::NoElse { branch_instr } => {
                let block_type = frame.block_type;
                let inputs = block_type.inputs(&self.res);
                let outputs = block_type.outputs(&self.res);
                debug_assert_eq!(inputs.len(), outputs.len());
                let else_block = Self::block_with_params_explicit(
                    &mut self.builder,
                    inputs.iter().copied(),
                )?;
                let exit_block = frame.exit_block;
                self.builder.ins()?.br(
                    exit_block,
                    self.value_stack
                        .pop_n(inputs.len())?
                        .map(|entry| entry.value),
                )?;
                self.builder.relink_edge_destination(
                    branch_instr,
                    exit_block,
                    else_block,
                )?;
                self.builder.seal_block(else_block)?;
                else_block
            }
        };
        // Now switch to the if's `else_block` to continue translation there.
        //
        // You might be expecting that we push the parameters for this
        // `else` block here, something like this:
        //
        //     state.pushn(&control_stack_frame.params);
        //
        // We don't do that because they are already on the top of the stack
        // for us: we pushed the parameters twice when we saw the initial
        // `if` so that we wouldn't have to save the parameters in the
        // `ControlStackFrame` as another vector allocation.
        self.builder.switch_to_block(else_block)?;
        // We don't bother updating the control frame's `ElseData`
        // to `WithElse` because nothing else will read it.
        Ok(())
    }

    /// Translate a Wasm `End` control operator.
    pub(super) fn translate_end(&mut self) -> Result<(), Error> {
        let frame = self.control_stack.pop_frame()?;
        if let ControlFlowFrame::Body(body_frame) = frame {
            let current = self.builder.current_block()?;
            if !self.reachable || !self.builder.is_block_reachable(current) {
                // We won't generate a return instruction if the code at
                // this point is unreachable since the value stack could
                // be different from our expectations.
                return Ok(())
            }
            // We just encountered the final `End` operator.
            // So we put a return instruction at the end of the function body.
            let len_stack = self.value_stack.len();
            // debug_assert_eq!(
            //     len_stack,
            //     body_frame.block_type.outputs(&self.res).len()
            // );
            let return_values =
                self.value_stack.pop_n(len_stack)?.map(|entry| entry.value);
            self.builder.ins()?.return_values(return_values)?;
            return Ok(())
        }
        let next_block = frame.following_code();
        let current = self.builder.current_block()?;
        if self.builder.is_block_reachable(current)
        // || !builder.is_pristine()
        {
            let len_outputs = frame.outputs(&self.res).len();
            let output_args = self.value_stack.peek_n(len_outputs)?;
            self.builder
                .ins()?
                .br(next_block, output_args.map(|entry| entry.value))?;
            // You might expect that if we just finished an `if` block that
            // didn't have a corresponding `else` block, then we would clean
            // up our duplicate set of parameters that we pushed earlier
            // right here. However, we don't have to explicitly do that,
            // since we truncate the stack back to the original height
            // below.
        }
        self.builder.switch_to_block(next_block)?;
        self.builder.seal_block(next_block)?;

        // If it is a loop we also have to seal the body loop block
        if let ControlFlowFrame::Loop(loop_frame) = &frame {
            self.builder.seal_block(loop_frame.loop_header)?;
        }

        self.truncate_value_stack_to_original_size(&frame)?;
        let Self {
            value_stack,
            ref builder,
            ..
        } = self;
        let next_block_params = builder
            .block_parameters(next_block)
            .iter()
            .map(|&value| (value, builder.value_type(value)));
        value_stack.extend(next_block_params);
        Ok(())
    }

    /// Translate a Wasm `Br` control operator.
    pub(super) fn translate_br(
        &mut self,
        relative_depth: u32,
    ) -> Result<(), Error> {
        let frame = self.control_stack.nth_back_mut(relative_depth)?;
        if frame.is_func_body() {
            // Branching to the implicit function body label is equal to a return.
            return self.translate_return()
        }
        // We signal that all the code that follows until the next `End` is unreachable.
        frame.set_branched_to_exit();
        let len_return_values = frame.len_branch_args(&self.res);
        let destination_args = self
            .value_stack
            .pop_n(len_return_values)?
            .map(|entry| entry.value);
        self.builder
            .ins()?
            .br(frame.branch_destination(), destination_args)?;
        self.reachable = false;
        Ok(())
    }

    /// Translate a Wasm `BrIf` control operator.
    pub(super) fn translate_br_if(
        &mut self,
        relative_depth: u32,
    ) -> Result<(), Error> {
        Err(TranslateError::unimplemented_operator(
            wasmparser::Operator::BrIf { relative_depth },
        ))
        .map_err(Into::into)
    }

    /// Translate a Wasm `BrTable` control operator.
    pub(super) fn translate_br_table(
        &mut self,
        table: wasmparser::BrTable,
    ) -> Result<(), Error> {
        Err(TranslateError::unimplemented_operator(
            wasmparser::Operator::BrTable { table },
        ))
        .map_err(Into::into)
    }

    /// Translate a Wasm `Return` control operator.
    pub(super) fn translate_return(&mut self) -> Result<(), Error> {
        let frame = &mut self.control_stack.first();
        let outputs = frame.outputs(&self.res);
        let return_args = self
            .value_stack
            .pop_n(outputs.len())?
            .map(|entry| entry.value);
        self.builder.ins()?.return_values(return_args)?;
        self.reachable = false;
        Ok(())
    }
}
