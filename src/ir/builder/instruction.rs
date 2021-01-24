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

use super::{
    function::ValueAssoc,
    state,
    FunctionBuilder,
    FunctionBuilderError,
};
use crate::{
    entity::Idx,
    ir::{
        instr::{
            BinaryIntInstr,
            BranchInstr,
            CompareIntInstr,
            ConstInstr,
            IfThenElseInstr,
            ReturnInstr,
            TerminalInstr,
        },
        instruction::{BinaryIntOp, CompareIntOp, Instruction},
        primitive::{Block, Const, IntType, Type, Value},
        IrError,
    },
};

/// The unique index of a basic block entity of the Runwell IR.
pub type Instr = Idx<Instruction>;

#[derive(Debug)]
pub struct FunctionInstrBuilder<'a> {
    builder: &'a mut FunctionBuilder<state::Body>,
}

impl<'a> FunctionInstrBuilder<'a> {
    /// Creates a new function instruction builder.
    pub(super) fn new(builder: &'a mut FunctionBuilder<state::Body>) -> Self {
        Self { builder }
    }

    /// Appends the instruction to the current basic block if possible.
    ///
    /// # Note
    ///
    /// - Flags the basic block as filled if the instruction terminates the basic block.
    /// - Eventually updates the predecessors and successors of basic blocks.
    ///
    /// # Errors
    ///
    /// - If used SSA values do not exist for the function.
    /// - If values do not match required type constraints.
    /// - Upon trying to branch to a basic block that has already been sealed.
    fn append_value_instr(
        &mut self,
        instruction: Instruction,
        ty: Type,
    ) -> Result<(Value, Instr), IrError> {
        let block = self.builder.current_block()?;
        let instr = self.builder.ctx.instrs.alloc(instruction.into());
        let value = self.builder.ctx.values.alloc(Default::default());
        self.builder.ctx.block_instrs[block].push(instr);
        self.builder.ctx.instr_value.insert(instr, value);
        self.builder.ctx.value_type.insert(value, ty);
        self.builder
            .ctx
            .value_users
            .insert(value, Default::default());
        self.builder
            .ctx
            .value_assoc
            .insert(value, ValueAssoc::Instr(instr));
        Ok((value, instr))
    }

    pub fn constant<C>(mut self, constant: C) -> Result<Value, IrError>
    where
        C: Into<Const>,
    {
        let constant = constant.into();
        let instruction = ConstInstr::new(constant);
        let (value, _) =
            self.append_value_instr(instruction.into(), constant.ty())?;
        Ok(value)
    }

    /// Registers that the instruction uses the given values.
    ///
    /// This information is later used to remove trivial phi nodes
    /// recursively and can later be used to down propagate other simplifications.
    fn register_uses(&mut self, instr: Instr, uses: &[Value]) {
        for &value in uses {
            self.builder.ctx.value_users[value].insert(instr);
        }
    }

    fn expect_type(
        &self,
        value: Value,
        expected_type: Type,
    ) -> Result<(), IrError> {
        let value_type = self.builder.ctx.value_type[value];
        if value_type != expected_type {
            return Err(FunctionBuilderError::UnmatchingValueType {
                value,
                value_type,
                expected_type,
            })
            .map_err(Into::into)
        }
        Ok(())
    }

    fn ibinary(
        mut self,
        op: BinaryIntOp,
        ty: IntType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, IrError> {
        self.expect_type(lhs, ty.into())?;
        self.expect_type(rhs, ty.into())?;
        let instruction = BinaryIntInstr::new(op, ty, lhs, rhs);
        let (value, instr) =
            self.append_value_instr(instruction.into(), ty.into())?;
        self.register_uses(instr, &[lhs, rhs]);
        Ok(value)
    }

    pub fn iadd(
        self,
        ty: IntType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, IrError> {
        self.ibinary(BinaryIntOp::Add, ty, lhs, rhs)
    }

    pub fn isub(
        self,
        ty: IntType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, IrError> {
        self.ibinary(BinaryIntOp::Sub, ty, lhs, rhs)
    }

    pub fn imul(
        self,
        ty: IntType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, IrError> {
        self.ibinary(BinaryIntOp::Mul, ty, lhs, rhs)
    }

    pub fn sdiv(
        self,
        ty: IntType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, IrError> {
        self.ibinary(BinaryIntOp::Sdiv, ty, lhs, rhs)
    }

    pub fn udiv(
        self,
        ty: IntType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, IrError> {
        self.ibinary(BinaryIntOp::Udiv, ty, lhs, rhs)
    }

    pub fn icmp(
        mut self,
        ty: IntType,
        op: CompareIntOp,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, IrError> {
        self.expect_type(lhs, ty.into())?;
        self.expect_type(rhs, ty.into())?;
        let instruction = CompareIntInstr::new(op, ty, lhs, rhs);
        let (value, instr) =
            self.append_value_instr(instruction.into(), ty.into())?;
        self.register_uses(instr, &[lhs, rhs]);
        Ok(value)
    }

    fn append_instr<I>(&mut self, instruction: I) -> Result<Instr, IrError>
    where
        I: Into<Instruction>,
    {
        let instruction = instruction.into();
        let block = self.builder.current_block()?;
        let is_terminal = instruction.is_terminal();
        let instr = self.builder.ctx.instrs.alloc(instruction);
        self.builder.ctx.block_instrs[block].push(instr);
        if is_terminal {
            self.builder.ctx.block_filled[block] = true;
        }
        Ok(instr)
    }

    pub fn return_value(
        mut self,
        return_value: Value,
    ) -> Result<Instr, IrError> {
        let instr = self.append_instr(ReturnInstr::new(return_value))?;
        self.register_uses(instr, &[return_value]);
        Ok(instr)
    }

    pub fn br(mut self, target: Block) -> Result<Instr, IrError> {
        let block = self.builder.current_block()?;
        let instr = self.append_instr(BranchInstr::new(target))?;
        self.add_predecessor(target, block)?;
        Ok(instr)
    }

    pub fn trap(mut self) -> Result<Instr, IrError> {
        self.append_instr(TerminalInstr::Trap)
    }

    pub fn if_then_else(
        mut self,
        condition: Value,
        then_target: Block,
        else_target: Block,
    ) -> Result<Instr, IrError> {
        let block = self.builder.current_block()?;
        let instr = self.append_instr(IfThenElseInstr::new(
            condition,
            then_target,
            else_target,
        ))?;
        self.add_predecessor(then_target, block)?;
        self.add_predecessor(else_target, block)?;
        self.register_uses(instr, &[condition]);
        Ok(instr)
    }

    /// Adds a new predecessor basic block to the block.
    ///
    /// # Errors
    ///
    /// - If the new predecessor is not yet filled.
    /// - If the block that gains a new predessor has already been sealed.
    /// - If the new predecessor is already a predecessor of the block.
    fn add_predecessor(
        &mut self,
        block: Block,
        new_pred: Block,
    ) -> Result<(), IrError> {
        if !self.builder.ctx.block_filled[new_pred] {
            return Err(IrError::FunctionBuilder(
                FunctionBuilderError::UnfilledPredecessor {
                    block,
                    unfilled_pred: new_pred,
                },
            ))
        }
        if self.builder.ctx.block_sealed[block] {
            return Err(IrError::FunctionBuilder(
                FunctionBuilderError::PredecessorForSealedBlock {
                    sealed_block: block,
                    new_pred,
                },
            ))
        }
        if !self.builder.ctx.block_preds[block].insert(new_pred) {
            return Err(IrError::FunctionBuilder(
                FunctionBuilderError::BranchAlreadyExists {
                    from: new_pred,
                    to: block,
                },
            ))
        }
        Ok(())
    }
}
