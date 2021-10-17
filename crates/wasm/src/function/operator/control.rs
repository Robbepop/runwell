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

use super::super::{ControlFrameKind, ElseData, FunctionBodyTranslator};
use crate::{
    function::control::{ControlFlowFrame, WasmBlockType},
    Error,
};
use core::convert::TryFrom;
use ir::{
    instr::operands::CompareIntOp,
    primitive::{Block, Const, IntConst, IntType, Type, Value},
};
use module::{builder::FunctionBuilder, primitive::Instr};
use wasmparser::Operator;

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
        self.value_stack.truncate_to_original_size(frame, self.res)
    }
}

impl<'a, 'b> FunctionBodyTranslator<'a, 'b> {
    /// Translates a Wasm operator in an unreachable code section.
    ///
    /// This requires special treatment in order to track unreachable
    /// control flow frames so that we are able to resolve them correctly.
    /// Some control flow operators such as `Else` and `End` also might
    /// might end the unreachable code section.
    ///
    /// All other Wasm operators are silently dropped.
    pub(super) fn translate_unreachable_operator(
        &mut self,
        op: &Operator,
    ) -> Result<(), Error> {
        debug_assert!(!self.reachable);
        match op {
            Operator::If { ty } => {
                let block_type = WasmBlockType::try_from(*ty)?;
                self.push_unreachable_control_frame(
                    ControlFrameKind::If,
                    block_type,
                );
            }
            Operator::Block { ty } => {
                let block_type = WasmBlockType::try_from(*ty)?;
                self.push_unreachable_control_frame(
                    ControlFrameKind::Block,
                    block_type,
                );
            }
            Operator::Loop { ty } => {
                let block_type = WasmBlockType::try_from(*ty)?;
                self.push_unreachable_control_frame(
                    ControlFrameKind::Loop,
                    block_type,
                );
            }
            Operator::Else => {
                let any_frame = self.control_stack.last_mut();
                assert_eq!(
                    any_frame.kind(),
                    ControlFrameKind::If,
                    "missing parent `If` frame upon encountering `Else`"
                );
                let frame = match any_frame {
                    ControlFlowFrame::If(frame) => frame,
                    ControlFlowFrame::Unreachable(_) => {
                        // The parent `If` frame was already unreachable so
                        // we do nothing here.
                        return Ok(())
                    }
                    _ => unreachable!(),
                };
                // At this point we know that `frame` refers to a reachable `If`.
                //
                // We just finished the `then_block` (consequent), so record
                // its final reachability state.
                debug_assert!(frame.then_end_is_reachable.is_none());
                frame.then_end_is_reachable = Some(self.reachable);
                // We have a branch from the head of the `if` to the `else`.
                self.reachable = true;

                let else_block = match frame.else_data {
                    ElseData::WithElse { else_block } => {
                        self.value_stack
                            .truncate_to_original_size(any_frame, self.res)?;
                        else_block
                    }
                    ElseData::NoElse { branch_instr } => {
                        let inputs = frame.block_type.inputs(self.res);
                        let outputs = frame.block_type.outputs(self.res);
                        debug_assert_eq!(inputs.len(), outputs.len());
                        let else_block = Self::block_with_params_explicit(
                            &mut self.builder,
                            inputs.iter().copied(),
                        )?;
                        self.value_stack
                            .truncate_to_original_size(any_frame, self.res)?;
                        self.builder.seal_block(else_block)?;
                        else_block
                    }
                };
                self.builder.switch_to_block(else_block)?;
                // Again, no need to push the parameters for the `else`,
                // since we already did when we saw the original `if`. See
                // the comment for translating `Operator::Else` in
                // `translate_operator` for details.
            }
            Operator::End => {
                let frame = self.control_stack.pop_frame()?;
                self.truncate_value_stack_to_original_size(&frame)?;

                let reachable_anyway = match &frame {
                    ControlFlowFrame::Loop(frame) => {
                        // If it is a loop we also have to seal the body loop block.
                        self.builder.seal_block(frame.loop_header)?;
                        // And loops can't have branches to the end.
                        false
                    }
                    ControlFlowFrame::If(frame) => {
                        // There are two cases:
                        //
                        // - If `then_end_is_reachable` is `None` it means that we
                        //   are in the unreachable `Then` part of the `If` and there
                        //   is no `Else` block. In this case the code after the `End`
                        //   is always reachable again.
                        // - If `then_end_is_reachable` is `Some(flag)` it means that
                        //   we are in the unreachable `Else` part of the `If`. In this
                        //   case the code after the `End` is always reachable if the
                        //   end of the consequent (`Then`) was reachable.
                        frame.then_end_is_reachable.unwrap_or(true)
                    }
                    _ => {
                        // All other control constructs are already handled.
                        false
                    }
                };
                if frame.exit_is_branched_to() || reachable_anyway {
                    let following_code = frame.following_code();
                    self.builder.switch_to_block(following_code)?;
                    self.builder.seal_block(following_code)?;

                    // And add the return values of the block but only if the next block is reachable
                    // (which corresponds to testing if the stack depth is 1)
                    let Self {
                        value_stack,
                        builder,
                        ..
                    } = self;
                    let block_parameters = builder
                        .block_parameters(following_code)
                        .iter()
                        .copied();
                    value_stack.extend(block_parameters);
                    self.reachable = true;
                }
            }
            _ => {
                // We don't translate because this is unreachable code.
            }
        }
        Ok(())
    }

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
        let outputs = block_type.outputs(self.res);
        let block = self.block_with_params(outputs.iter().copied())?;
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
        let inputs = block_type.inputs(self.res);
        let outputs = block_type.outputs(self.res);
        let loop_head = self.block_with_params(inputs.iter().copied())?;
        let loop_exit = self.block_with_params(outputs.iter().copied())?;
        let args = self.value_stack.peek_n(inputs.len())?;
        self.builder.ins()?.br(loop_head, args)?;
        self.push_control_loop(loop_head, loop_exit, block_type);

        // Pop the initial `Block` actuals and replace them with the `Block`'s
        // params since control flow joins at the top of the loop.
        self.value_stack.pop_n(inputs.len())?;
        self.value_stack
            .extend(self.builder.block_parameters(loop_head).iter().copied());

        self.builder.switch_to_block(loop_head)?;
        Ok(())
    }

    /// Constructs an if that compares the top most value for inequality with zero.
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
            self.value_stack.peek_n(len_then_args)?,
            self.value_stack.peek_n(len_else_args)?,
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
        let condition_type = self.builder.value_type(condition);
        debug_assert_eq!(condition_type, IntType::I32.into());

        let block_type = WasmBlockType::try_from(ty)?;
        let inputs = block_type.inputs(self.res);
        let outputs = block_type.outputs(self.res);

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
                condition,
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
                condition,
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
        let frame = self.control_stack.last_mut();
        assert_eq!(
            frame.kind(),
            ControlFrameKind::If,
            "missing `If` frame upon encountering reachable `Else`"
        );
        let frame = match frame {
            ControlFlowFrame::If(frame) => frame,
            _ => {
                unreachable!(
                    "encountered invalid unreachable `If` for reachable `Else`"
                )
            }
        };
        // We just finished the `then_block` (consequent), so record
        // its final reachability state.
        debug_assert!(frame.then_end_is_reachable.is_none());
        frame.then_end_is_reachable = Some(self.reachable);
        // Ensure we have a block for the `else` block (it may have
        // already been pre-allocated, see `ElseData` for details).
        let else_block = match frame.else_data {
            ElseData::WithElse { else_block } => {
                let outputs = frame.block_type.outputs(self.res);
                let exit_block = frame.exit_block;
                self.builder
                    .ins()?
                    .br(exit_block, self.value_stack.pop_n(outputs.len())?)?;
                else_block
            }
            ElseData::NoElse { branch_instr } => {
                let block_type = frame.block_type;
                let inputs = block_type.inputs(self.res);
                let outputs = block_type.outputs(self.res);
                debug_assert_eq!(inputs.len(), outputs.len());
                let else_block = Self::block_with_params_explicit(
                    &mut self.builder,
                    inputs.iter().copied(),
                )?;
                let exit_block = frame.exit_block;
                self.builder
                    .ins()?
                    .br(exit_block, self.value_stack.pop_n(inputs.len())?)?;
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
        Ok(())
    }

    /// Translate a Wasm `End` control operator.
    pub(super) fn translate_end(&mut self) -> Result<(), Error> {
        let frame = self.control_stack.pop_frame()?;
        let next_block = frame.following_code();
        let current = self.builder.current_block()?;
        if self.builder.is_block_reachable(current)
        // || !builder.is_pristine()
        {
            let outputs = frame.outputs(self.res);
            let len_outputs = frame.outputs(self.res).len();
            let output_args = self.value_stack.peek_n(len_outputs)?;
            if frame.is_func_body() {
                // Ending the function body label is equal to a return.
                self.builder.ins()?.return_values(output_args)?;
            } else {
                self.builder.ins()?.br(next_block, output_args)?;
            }
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
        let next_block_params =
            self.builder.block_parameters(next_block).iter().copied();
        self.value_stack.extend(next_block_params);
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
        let len_return_values = frame.len_branch_args(self.res);
        let destination_args = self.value_stack.pop_n(len_return_values)?;
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
        let condition = self.value_stack.pop1()?;
        let condition_type = self.builder.value_type(condition);
        assert_eq!(condition_type, IntType::I32.into());
        let frame = self.control_stack.nth_back_mut(relative_depth)?;
        // The values returned by the branch are still available for the reachable
        // code that comes after it.
        frame.set_branched_to_exit();
        let len_return_values = frame.len_branch_args(self.res);
        let then_block = frame.branch_destination();
        let next_block = self.builder.create_block()?;
        self.construct_if_nez(
            condition,
            then_block,
            next_block,
            len_return_values,
            0,
        )?;
        self.builder.seal_block(next_block)?;
        self.builder.switch_to_block(next_block)?;
        Ok(())
    }

    /// Translate a Wasm `BrTable` control operator.
    pub(super) fn translate_br_table(
        &mut self,
        table: wasmparser::BrTable,
    ) -> Result<(), Error> {
        let selector = self.value_stack.pop1()?;
        let selector_type = self
            .builder
            .value_type(selector)
            .filter_map_int()
            .unwrap_or_else(|| panic!(
                "expected an integer type for the `br_table` selector but found {}: {}",
                selector,
                self.builder.value_type(selector),
            ));
        let mut instr =
            self.builder.ins()?.match_branch(selector_type, selector)?;

        // Translate `br_table` targets:
        for relative_depth in table.targets() {
            let relative_depth = relative_depth?;
            let frame = self.control_stack.nth_back_mut(relative_depth)?;
            let branch_destination = frame.branch_destination();
            let len_branch_args = frame.len_branch_args(self.res);
            let branch_args = self.value_stack.peek_n(len_branch_args)?;
            instr.push_edge(branch_destination, branch_args)?;
            frame.set_branched_to_exit();
        }

        // Translate `br_table` default target:
        let default_depth = table.default();
        let frame = self.control_stack.nth_back_mut(default_depth)?;
        let default_destination = frame.branch_destination();
        let len_default_args = frame.len_branch_args(self.res);
        let default_args = self.value_stack.pop_n(len_default_args)?;
        frame.set_branched_to_exit();
        instr.finish(default_destination, default_args)?;
        self.reachable = false;
        Ok(())
    }

    /// Translate a Wasm `Return` control operator.
    pub(super) fn translate_return(&mut self) -> Result<(), Error> {
        let frame = &mut self.control_stack.first();
        let outputs = frame.outputs(self.res);
        let return_args = self.value_stack.pop_n(outputs.len())?;
        self.builder.ins()?.return_values(return_args)?;
        self.reachable = false;
        Ok(())
    }

    /// Translate a Wasm `Unreachable` control operator.
    pub(super) fn translate_unreachable(&mut self) -> Result<(), Error> {
        self.builder.ins()?.unreachable()?;
        self.reachable = false;
        Ok(())
    }
}
