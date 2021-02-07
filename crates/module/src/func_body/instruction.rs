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

use super::{builder::ValueAssoc, FunctionBuilder, FunctionBuilderError};
use crate::IrError;
use entity::Idx;
use ir::{
    instr::{
        operands::{
            BinaryFloatOp,
            BinaryIntOp,
            CompareFloatOp,
            CompareIntOp,
            ShiftIntOp,
            UnaryFloatOp,
            UnaryIntOp,
        },
        BinaryFloatInstr,
        BinaryIntInstr,
        BranchInstr,
        CallInstr,
        CompareFloatInstr,
        CompareIntInstr,
        ConstInstr,
        IfThenElseInstr,
        Instruction,
        ReinterpretInstr,
        ReturnInstr,
        SelectInstr,
        ShiftIntInstr,
        TailCallInstr,
        TerminalInstr,
        UnaryFloatInstr,
        UnaryIntInstr,
    },
    primitive::{Block, Const, FloatType, Func, IntType, Type, Value},
};

/// The unique index of a basic block entity of the Runwell IR.
pub type Instr = Idx<Instruction>;

/// Builder guiding the construction of Runwell IR instructions.
#[derive(Debug)]
pub struct InstructionBuilder<'a> {
    builder: &'a mut FunctionBuilder,
}

impl<'a> InstructionBuilder<'a> {
    /// Creates a new function instruction builder.
    pub(super) fn new(builder: &'a mut FunctionBuilder) -> Self {
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
        let instr = self.builder.ctx.instrs.alloc(instruction);
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

    pub fn call<P>(mut self, func: Func, params: P) -> Result<Value, IrError>
    where
        P: IntoIterator<Item = Value>,
    {
        let instruction = CallInstr::new(func, params);
        // We have to query the type of the function `func` in the store.
        // Currently we simply use `bool` as return type for all functions.
        let (value, _) =
            self.append_value_instr(instruction.into(), Type::Bool)?;
        Ok(value)
    }

    pub fn tail_call<P>(
        mut self,
        func: Func,
        params: P,
    ) -> Result<Value, IrError>
    where
        P: IntoIterator<Item = Value>,
    {
        let instruction = TailCallInstr::new(func, params);
        // We have to query the type of the function `func` in the store.
        // Currently we simply use `bool` as return type for all functions.
        let (value, _) =
            self.append_value_instr(instruction.into(), Type::Bool)?;
        Ok(value)
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

    /// Returns `Ok` if the type of the value matches the expected type.
    ///
    /// # Errors
    ///
    /// If the types do not match.
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

    /// Convenience function to construct unary integer instructions.
    fn iunary(
        mut self,
        op: UnaryIntOp,
        int_type: IntType,
        source: Value,
    ) -> Result<Value, IrError> {
        self.expect_type(source, int_type.into())?;
        let instruction = UnaryIntInstr::new(op, int_type, source);
        let (value, instr) =
            self.append_value_instr(instruction.into(), int_type.into())?;
        self.register_uses(instr, &[source]);
        Ok(value)
    }

    /// Integer count leading zeros.
    pub fn iclz(
        self,
        int_type: IntType,
        source: Value,
    ) -> Result<Value, IrError> {
        self.iunary(UnaryIntOp::LeadingZeros, int_type, source)
    }

    /// Integer count trailing zeros.
    pub fn ictz(
        self,
        int_type: IntType,
        source: Value,
    ) -> Result<Value, IrError> {
        self.iunary(UnaryIntOp::TrailingZeros, int_type, source)
    }

    /// Integer count ones.
    pub fn ipopcnt(
        self,
        int_type: IntType,
        source: Value,
    ) -> Result<Value, IrError> {
        self.iunary(UnaryIntOp::PopCount, int_type, source)
    }

    /// Convenience function to construct integer shift and rotate instructions.
    fn ishift(
        mut self,
        op: ShiftIntOp,
        int_type: IntType,
        source: Value,
        shift_amount: Value,
    ) -> Result<Value, IrError> {
        self.expect_type(source, int_type.into())?;
        self.expect_type(shift_amount, IntType::I32.into())?;
        let instruction =
            ShiftIntInstr::new(op, int_type, source, shift_amount);
        let (value, instr) =
            self.append_value_instr(instruction.into(), int_type.into())?;
        self.register_uses(instr, &[source, shift_amount]);
        Ok(value)
    }

    /// Integer left shift.
    pub fn ishl(
        self,
        int_type: IntType,
        source: Value,
        shift_amount: Value,
    ) -> Result<Value, IrError> {
        self.ishift(ShiftIntOp::Shl, int_type, source, shift_amount)
    }

    /// Integer unsigned right shift.
    pub fn iushr(
        self,
        int_type: IntType,
        source: Value,
        shift_amount: Value,
    ) -> Result<Value, IrError> {
        self.ishift(ShiftIntOp::Ushr, int_type, source, shift_amount)
    }

    /// Integer signed right shift.
    pub fn isshr(
        self,
        int_type: IntType,
        source: Value,
        shift_amount: Value,
    ) -> Result<Value, IrError> {
        self.ishift(ShiftIntOp::Sshr, int_type, source, shift_amount)
    }

    /// Integer rotate left.
    pub fn irotl(
        self,
        int_type: IntType,
        source: Value,
        shift_amount: Value,
    ) -> Result<Value, IrError> {
        self.ishift(ShiftIntOp::Rotl, int_type, source, shift_amount)
    }

    /// Integer rotate right.
    pub fn irotr(
        self,
        int_type: IntType,
        source: Value,
        shift_amount: Value,
    ) -> Result<Value, IrError> {
        self.ishift(ShiftIntOp::Rotr, int_type, source, shift_amount)
    }

    /// Convenience function to construct binary integer instructions.
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

    /// Integer addition.
    pub fn iadd(
        self,
        ty: IntType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, IrError> {
        self.ibinary(BinaryIntOp::Add, ty, lhs, rhs)
    }

    /// Integer subtraction.
    pub fn isub(
        self,
        ty: IntType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, IrError> {
        self.ibinary(BinaryIntOp::Sub, ty, lhs, rhs)
    }

    /// Integer multiplication.
    pub fn imul(
        self,
        ty: IntType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, IrError> {
        self.ibinary(BinaryIntOp::Mul, ty, lhs, rhs)
    }

    /// Signed integer division.
    pub fn sdiv(
        self,
        ty: IntType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, IrError> {
        self.ibinary(BinaryIntOp::Sdiv, ty, lhs, rhs)
    }

    /// Unsigned integer division.
    pub fn udiv(
        self,
        ty: IntType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, IrError> {
        self.ibinary(BinaryIntOp::Udiv, ty, lhs, rhs)
    }

    /// Signed integer remainder.
    pub fn srem(
        self,
        ty: IntType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, IrError> {
        self.ibinary(BinaryIntOp::Srem, ty, lhs, rhs)
    }

    /// Unsigned integer remainder.
    pub fn urem(
        self,
        ty: IntType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, IrError> {
        self.ibinary(BinaryIntOp::Urem, ty, lhs, rhs)
    }

    /// Integer bitwise AND.
    pub fn iand(
        self,
        ty: IntType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, IrError> {
        self.ibinary(BinaryIntOp::And, ty, lhs, rhs)
    }

    /// Integer bitwise OR.
    pub fn ior(
        self,
        ty: IntType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, IrError> {
        self.ibinary(BinaryIntOp::Or, ty, lhs, rhs)
    }

    /// Integer bitwise XOR.
    pub fn ixor(
        self,
        ty: IntType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, IrError> {
        self.ibinary(BinaryIntOp::Xor, ty, lhs, rhs)
    }

    /// Integer comparison given a comparator.
    ///
    /// # Comparator Kinds
    ///
    /// - There is a sign agnostic equals (`==`) comparator.
    /// - There are four signed integer comparators:
    ///     - `slt`: Signed less-than
    ///     - `sle`: Signed less-equals
    ///     - `sgt`: Signed greater-than
    ///     - `sge`: Signed greater-equals
    /// - There are four unsigned integer comparators:
    ///     - `ult`: Unsigned less-than
    ///     - `ule`: Unsigned less-equals
    ///     - `ugt`: Unsigned greater-than
    ///     - `uge`: Unsigned greater-equals
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
            self.append_value_instr(instruction.into(), Type::Bool)?;
        self.register_uses(instr, &[lhs, rhs]);
        Ok(value)
    }

    /// Convenience function to construct unary float instructions.
    fn funary(
        mut self,
        op: UnaryFloatOp,
        ty: FloatType,
        source: Value,
    ) -> Result<Value, IrError> {
        self.expect_type(source, ty.into())?;
        let instruction = UnaryFloatInstr::new(op, ty, source);
        let (value, instr) =
            self.append_value_instr(instruction.into(), ty.into())?;
        self.register_uses(instr, &[source]);
        Ok(value)
    }

    /// Float absolute value.
    pub fn fabs(self, ty: FloatType, source: Value) -> Result<Value, IrError> {
        self.funary(UnaryFloatOp::Abs, ty, source)
    }

    /// Float negate.
    pub fn fneg(self, ty: FloatType, source: Value) -> Result<Value, IrError> {
        self.funary(UnaryFloatOp::Neg, ty, source)
    }

    /// Float square root.
    pub fn fsqrt(self, ty: FloatType, source: Value) -> Result<Value, IrError> {
        self.funary(UnaryFloatOp::Sqrt, ty, source)
    }

    /// Float round to ceil.
    pub fn fceil(self, ty: FloatType, source: Value) -> Result<Value, IrError> {
        self.funary(UnaryFloatOp::Ceil, ty, source)
    }

    /// Float round to floor.
    pub fn ffloor(
        self,
        ty: FloatType,
        source: Value,
    ) -> Result<Value, IrError> {
        self.funary(UnaryFloatOp::Floor, ty, source)
    }

    /// Float round to next smaller integer.
    pub fn ftruncate(
        self,
        ty: FloatType,
        source: Value,
    ) -> Result<Value, IrError> {
        self.funary(UnaryFloatOp::Truncate, ty, source)
    }

    /// Float round to nearest integer.
    pub fn fnearest(
        self,
        ty: FloatType,
        source: Value,
    ) -> Result<Value, IrError> {
        self.funary(UnaryFloatOp::Nearest, ty, source)
    }

    /// Convenience function to construct binary float instructions.
    fn fbinary(
        mut self,
        op: BinaryFloatOp,
        ty: FloatType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, IrError> {
        self.expect_type(lhs, ty.into())?;
        self.expect_type(rhs, ty.into())?;
        let instruction = BinaryFloatInstr::new(op, ty, lhs, rhs);
        let (value, instr) =
            self.append_value_instr(instruction.into(), ty.into())?;
        self.register_uses(instr, &[lhs, rhs]);
        Ok(value)
    }

    /// Float addition.
    pub fn fadd(
        self,
        ty: FloatType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, IrError> {
        self.fbinary(BinaryFloatOp::Add, ty, lhs, rhs)
    }

    /// Float subtraction.
    pub fn fsub(
        self,
        ty: FloatType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, IrError> {
        self.fbinary(BinaryFloatOp::Sub, ty, lhs, rhs)
    }

    /// Float multiplication.
    pub fn fmul(
        self,
        ty: FloatType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, IrError> {
        self.fbinary(BinaryFloatOp::Mul, ty, lhs, rhs)
    }

    /// Float division.
    pub fn fdiv(
        self,
        ty: FloatType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, IrError> {
        self.fbinary(BinaryFloatOp::Div, ty, lhs, rhs)
    }

    /// Float minimum element.
    pub fn fmin(
        self,
        ty: FloatType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, IrError> {
        self.fbinary(BinaryFloatOp::Min, ty, lhs, rhs)
    }

    /// Float maximum element.
    pub fn fmax(
        self,
        ty: FloatType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, IrError> {
        self.fbinary(BinaryFloatOp::Max, ty, lhs, rhs)
    }

    /// Float copysign operation.
    pub fn fcopysign(
        self,
        ty: FloatType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, IrError> {
        self.fbinary(BinaryFloatOp::CopySign, ty, lhs, rhs)
    }

    /// Float comparison given a comparator.
    ///
    /// # Comparator Kinds
    ///
    /// - `eq`: Tests for bitwise equality.
    /// - `ne`: Tests for bitwise inequality.
    /// - `le`: Less-than or equals.
    /// - `lt`: Less-than.
    /// - `ge`: Greater-than or equals.
    /// - `gt`: Greater-than.
    pub fn fcmp(
        mut self,
        ty: FloatType,
        op: CompareFloatOp,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, IrError> {
        self.expect_type(lhs, ty.into())?;
        self.expect_type(rhs, ty.into())?;
        let instruction = CompareFloatInstr::new(op, ty, lhs, rhs);
        let (value, instr) =
            self.append_value_instr(instruction.into(), Type::Bool)?;
        self.register_uses(instr, &[lhs, rhs]);
        Ok(value)
    }

    /// Selects either `if_true` or `if_false` depending on the value of `condition`.
    ///
    /// # Note
    ///
    /// This is very similar to an if-then-else instruction that does not require jumps.
    pub fn select(
        mut self,
        ty: Type,
        condition: Value,
        if_true: Value,
        if_false: Value,
    ) -> Result<Value, IrError> {
        self.expect_type(if_true, ty)?;
        self.expect_type(if_false, ty)?;
        let instruction = SelectInstr::new(condition, ty, if_true, if_false);
        let (value, instr) = self.append_value_instr(instruction.into(), ty)?;
        self.register_uses(instr, &[condition, if_true, if_false]);
        Ok(value)
    }

    /// Reinterprets the source value from its source type into its new destination type.
    ///
    /// # Note
    ///
    /// This allows casting between integer and float without conversion.
    ///
    /// # Errors
    ///
    /// If source and destination types have different bit widths.
    pub fn reinterpret(
        mut self,
        from_type: Type,
        to_type: Type,
        src: Value,
    ) -> Result<Value, IrError> {
        let from_bitwidth = from_type.bit_width();
        let to_bitwidth = to_type.bit_width();
        if from_bitwidth != to_bitwidth {
            return Err(FunctionBuilderError::UnmatchingReinterpretBitwidths {
                from_bitwidth,
                to_bitwidth,
                src,
            })
            .map_err(Into::into)
        }
        let instruction = ReinterpretInstr::new(from_type, to_type, src);
        let (value, instr) =
            self.append_value_instr(instruction.into(), to_type)?;
        self.register_uses(instr, &[src]);
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

    /// Returns the given value to the caller of the function.
    pub fn return_value(
        mut self,
        return_value: Value,
    ) -> Result<Instr, IrError> {
        let expected_output = &self.builder.ctx.output_types;
        let return_type = self.builder.ctx.value_type[return_value];
        if &[return_type][..] != expected_output {
            return Err(FunctionBuilderError::UnmatchingFunctionReturnType {
                returned_types: vec![return_type],
                expected_types: expected_output.to_vec(),
            })
            .map_err(Into::into)
        }
        let instr = self.append_instr(ReturnInstr::new(return_value))?;
        self.register_uses(instr, &[return_value]);
        Ok(instr)
    }

    /// Unconditionally jumps to the target basic block.
    pub fn br(mut self, target: Block) -> Result<Instr, IrError> {
        let block = self.builder.current_block()?;
        let instr = self.append_instr(BranchInstr::new(target))?;
        self.add_predecessor(target, block)?;
        Ok(instr)
    }

    /// Immediately traps or aborts execution.
    pub fn trap(mut self) -> Result<Instr, IrError> {
        self.append_instr(TerminalInstr::Trap)
    }

    /// Conditionally jumps to either `then_target` or `else_target` depending on
    /// the value of `condition`.
    pub fn if_then_else(
        mut self,
        condition: Value,
        then_target: Block,
        else_target: Block,
    ) -> Result<Instr, IrError> {
        self.expect_type(condition, Type::Bool)?;
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
            return Err(FunctionBuilderError::UnfilledPredecessor {
                block,
                unfilled_pred: new_pred,
            })
            .map_err(Into::into)
        }
        if self.builder.ctx.block_sealed[block] {
            return Err(FunctionBuilderError::PredecessorForSealedBlock {
                sealed_block: block,
                new_pred,
            })
            .map_err(Into::into)
        }
        if !self.builder.ctx.block_preds[block].insert(new_pred) {
            return Err(FunctionBuilderError::BranchAlreadyExists {
                from: new_pred,
                to: block,
            })
            .map_err(Into::into)
        }
        Ok(())
    }
}
