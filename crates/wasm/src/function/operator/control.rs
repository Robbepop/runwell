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

use super::super::ElseData;
use ir::{
    instr::operands::CompareIntOp,
    primitive::{Block, IntType, Value},
};
use module::primitive::Instr;

use super::super::FunctionBodyTranslator;
use crate::{
    function::control::{ControlFlowFrame, WasmBlockType},
    Error,
    TranslateError,
};
use std::convert::TryFrom;

impl<'a, 'b> FunctionBodyTranslator<'a, 'b> {
    /// Translate a Wasm `Block` control operator.
    pub(super) fn translate_block(
        &mut self,
        ty: wasmparser::TypeOrFuncType,
    ) -> Result<(), Error> {
        let block_type = WasmBlockType::try_from(ty)?;
        let inputs = block_type.inputs(&self.res);
        let outputs = block_type.outputs(&self.res);
        self.push_control_block(inputs.len(), outputs.len());
        Ok(())
    }

    /// Translate a Wasm `Loop` control operator.
    pub(super) fn translate_loop(
        &mut self,
        ty: wasmparser::TypeOrFuncType,
    ) -> Result<(), Error> {
        let loop_header = self.builder.create_block()?;
        let block_type = WasmBlockType::try_from(ty)?;
        let inputs = block_type.inputs(&self.res);
        let outputs = block_type.outputs(&self.res);
        self.builder.ins()?.br(loop_header)?;
        self.push_control_loop(loop_header, inputs.len(), outputs.len());
        self.builder.switch_to_block(loop_header)?;
        Ok(())
    }

    /// Constructs an if that compares the top most value with zero.
    fn construct_if_eqz(
        &mut self,
        condition: Value,
        then_block: Block,
        else_block: Block,
    ) -> Result<Instr, Error> {
        let zero = self.builder.ins()?.constant(0)?;
        let eq = self.builder.ins()?.icmp(
            IntType::I32,
            CompareIntOp::Eq,
            condition,
            zero,
        )?;
        let instr = self
            .builder
            .ins()?
            .if_then_else(eq, then_block, else_block)?;
        Ok(instr)
    }

    /// Translate a Wasm `If` control operator.
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
        let exit_block = self.builder.create_block()?;
        let else_data = if inputs == outputs {
            // It is possible there is no `else` block, so we will only
            // allocate a block for it when we find the `else`. For now,
            // if the condition isn't true we jump directly to the
            // exit block following the whole `if...end`. If we do end
            // up discovering an `else`, then we will allocate a block for it
            // and go back and patch the jump.
            let branch_instr =
                self.construct_if_eqz(condition.value, then_block, exit_block)?;
            ElseData::NoElse { branch_instr }
        } else {
            // The `if` type signature is not valid without an `else` block,
            // so we eagerly allocate the `else` block here and make use of it.
            let else_block = self.builder.create_block()?;
            let instr =
                self.construct_if_eqz(condition.value, then_block, else_block)?;
            self.builder.seal_block(else_block)?;
            ElseData::WithElse { else_block }
        };
        self.builder.seal_block(then_block)?;
        self.builder.switch_to_block(then_block)?;
        // Here we append an argument to a block targeted by an argumentless jump instruction.
        // There are two cases:
        // - either the If does not have a else clause, in that case: `ty == EmptyBlock`
        //   and we add nothing;
        // - or the If has an else clause, in that case the destination of this jump
        //   instruction will be changed later when we translate the else operator.
        self.push_control_if(
            exit_block,
            else_data,
            inputs.len(),
            outputs.len(),
            block_type,
        )?;
        Ok(())
    }

    /// Translate a Wasm `Else` control operator.
    pub(super) fn translate_else(&mut self) -> Result<(), Error> {
        let parent_if = match self.control_stack.last_mut() {
            Some(ControlFlowFrame::If(if_frame)) => if_frame,
            _ => {
                unreachable!(
                    "expect to encounter an `if` before encountering an `else`"
                )
            }
        };
        // We finished the consequent, so record its final
        // reachability state.
        debug_assert!(parent_if.consequent_ends_reachable.is_none());
        parent_if.consequent_ends_reachable = Some(self.reachable);
        if !parent_if.head_is_reachable {
            return Ok(())
        }
        // We have a branch from the head of the `if` to the `else`.
        self.reachable = true;
        // Ensure we have a block for the `else` block (it may have
        // already been pre-allocated, see `ElseData` for details).
        let else_block = match parent_if.else_data {
            ElseData::WithElse { else_block } => else_block,
            ElseData::NoElse { branch_instr } => {
                let block_type = parent_if.block_type;
                let inputs = block_type.inputs(&self.res);
                let outputs = block_type.outputs(&self.res);
                debug_assert_eq!(inputs.len(), parent_if.len_outputs);
                let else_block = self.builder.create_block()?;
                self.builder.change_jump_of_else(branch_instr, else_block);
                self.builder.seal_block(else_block)?;
                else_block
            }
        };
        // Finalize the if's `then_block` by branching to the if's exit block.
        self.builder.ins()?.br(parent_if.exit_block)?;
        self.value_stack.pop_n(parent_if.len_outputs)?;
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
        let next_block = match frame.following_code() {
            Some(next_block) => next_block,
            None => {
                // The `following_code` is only `None` if there was never
                // a branch to it or if it is the entry block. Therefore
                // we can continue staying in the current basic block and
                // continue translation; OR in case of entry block insert
                // a final return instruction.
                if self.control_stack.is_empty() {
                    // Since the control stack is empty the popped block
                    // was in fact the entry block.
                    let outputs = self
                        .res
                        .get_func_type(self.func)
                        .unwrap_or_else(|| {
                            panic!(
                            "expected function type for {} due to validation",
                            self.func
                        )
                        })
                        .outputs();
                    let output_values =
                        self.value_stack.peek_n(outputs.len())?.as_slice();
                    assert!(outputs
                        .iter()
                        .copied()
                        .zip(output_values)
                        .all(|(lhs, rhs)| lhs == rhs.ty));
                    self.builder.ins()?.return_values(
                        output_values.iter().map(|entry| entry.value),
                    )?;
                    let original_size = frame.original_stack_size();
                    self.value_stack.truncate(original_size)?;
                }
                return Ok(())
            }
        };
        let current = self.builder.current_block()?;
        if self.builder.is_block_reachable(current)
        // || self.builder.is_block_touched(current) // same as `!pristine`
        {
            self.builder.ins()?.br(next_block)?;
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
        let original_size = frame.original_stack_size();
        self.value_stack.truncate(original_size)?;
        // TODO: Push block inputs to value stack.
        //
        // Problem: Phi instructions of a block are unordered in comparison
        //          with block parameters from Cranelift.

        Ok(())
    }

    /// Translate a Wasm `Br` control operator.
    pub(super) fn translate_br(
        &mut self,
        relative_depth: u32,
    ) -> Result<(), Error> {
        Err(TranslateError::unimplemented_operator(
            wasmparser::Operator::Br { relative_depth },
        ))
        .map_err(Into::into)
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
        Err(TranslateError::unimplemented_operator(
            wasmparser::Operator::Return,
        ))
        .map_err(Into::into)
    }
}
