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
    builder::FunctionBuilderContext,
    FunctionBuilder,
    FunctionBuilderError,
    ValueDefinition,
    ValueUser,
};
use crate::Error;
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
        utils::{MatchBranchInstrBuilder, MatchSelectInstrBuilder},
        BinaryFloatInstr,
        BinaryIntInstr,
        BranchInstr,
        CallInstr,
        CompareFloatInstr,
        CompareIntInstr,
        ConstInstr,
        DemoteFloatInstr,
        ExtendIntInstr,
        FloatToIntInstr,
        HeapAddrInstr,
        Instruction,
        IntToFloatInstr,
        LoadInstr,
        MatchBranchInstr,
        MatchSelectInstr,
        PromoteFloatInstr,
        ReinterpretInstr,
        ReturnInstr,
        ShiftIntInstr,
        StoreInstr,
        TailCallInstr,
        TerminalInstr,
        TruncateIntInstr,
        UnaryFloatInstr,
        UnaryIntInstr,
    },
    primitive::{
        Block,
        Const,
        Edge,
        FloatType,
        Func,
        IntType,
        Mem,
        Type,
        Value,
    },
    ImmU32,
    VisitValues,
};
use smallvec::SmallVec;

/// The unique index of a basic block entity of the Runwell IR.
pub type Instr = Idx<Instruction>;

/// Builder guiding the construction of Runwell IR instructions.
#[derive(Debug)]
pub struct InstructionBuilder<'a, 'b: 'a> {
    builder: &'a mut FunctionBuilder<'b>,
}

impl<'a, 'b: 'a> InstructionBuilder<'a, 'b> {
    /// Creates a new function instruction builder.
    pub(super) fn new(builder: &'a mut FunctionBuilder<'b>) -> Self {
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
        output_type: Type,
    ) -> Result<(Value, Instr), Error> {
        let block = self.builder.current_block()?;
        if self.builder.ctx.block_filled.get(block) {
            return Err(FunctionBuilderError::BasicBlockIsAlreadyFilled {
                block,
            })
            .map_err(Into::into)
        }
        let instr =
            self.append_multi_value_instr(instruction, &[output_type])?;
        self.register_uses(instr);
        let value = self.builder.ctx.instr_values[instr][0];
        Ok((value, instr))
    }

    /// Appends the instruction to the current basic block if possible.
    ///
    /// The instruction is associated to `n` output SSA values where
    /// `n` is equal to the length of the `output_types` slice.
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
    fn append_multi_value_instr(
        &mut self,
        instruction: Instruction,
        output_types: &[Type],
    ) -> Result<Instr, Error> {
        let is_terminal = instruction.is_terminal();
        if is_terminal {
            assert!(
                output_types.is_empty(),
                "a terminal instruction must not have output values but found {:?} for {:?}",
                output_types,
                instruction,
            );
        }
        let block = self.builder.current_block()?;
        let instr = self.builder.ctx.instrs.alloc(instruction);
        self.builder.ctx.block_instrs[block].push(instr);
        for (n, output_type) in output_types.iter().copied().enumerate() {
            let value = self.builder.ctx.values.alloc_some(1);
            self.builder.ctx.instr_values[instr].push(value);
            self.builder.ctx.value_type.insert(value, output_type);
            assert!(n <= u32::MAX as usize);
            self.builder
                .ctx
                .value_definition
                .insert(value, ValueDefinition::Instr(instr, n as u32));
        }
        if is_terminal {
            self.builder.ctx.block_filled.set(block, true);
        }
        self.register_uses(instr);
        Ok(instr)
    }

    pub fn call<P>(mut self, func: Func, params: P) -> Result<Instr, Error>
    where
        P: IntoIterator<Item = Value>,
    {
        let instruction = CallInstr::new(func, params);
        let func_type =
            self.builder.res.get_func_type(func).unwrap_or_else(|| {
                panic!(
                "encountered missing function type while building function {}",
                func
            )
            });
        let param_types = instruction
            .params()
            .iter()
            .copied()
            .map(|val| self.builder.ctx.value_type[val]);
        assert!(
            // We might want to turn this into an error instead of panicking.
            param_types.eq(func_type.inputs().iter().copied()),
            "encountered mismatch between function parameter types and declaration types",
        );
        let instr = self.append_multi_value_instr(
            instruction.into(),
            func_type.outputs(),
        )?;
        let call_instruction = match &self.builder.ctx.instrs[instr] {
            Instruction::Call(call_instruction) => call_instruction,
            _ => panic!("encountered unexpected instruction kind"),
        };
        for param in call_instruction.params().iter().copied() {
            self.builder.ctx.value_users[param].insert(ValueUser::Instr(instr));
        }
        Ok(instr)
    }

    pub fn tail_call<P>(mut self, func: Func, params: P) -> Result<Instr, Error>
    where
        P: IntoIterator<Item = Value>,
    {
        let instruction = TailCallInstr::new(func, params);
        let func_type =
            self.builder.res.get_func_type(func).unwrap_or_else(|| {
                panic!(
                "encountered missing function type while building function {}",
                func
            )
            });
        let param_types = instruction
            .params()
            .iter()
            .copied()
            .map(|val| self.builder.ctx.value_type[val]);
        assert!(
            param_types.eq(func_type.inputs().iter().copied()),
            "encountered mismatch between function parameter types and declaration types",
        );
        // We have to query the type of the function `func` in the store.
        // Currently we simply use `bool` as return type for all functions.
        let instr = self.append_instr(instruction)?;
        let call_instruction = match &self.builder.ctx.instrs[instr] {
            Instruction::Terminal(TerminalInstr::TailCall(
                call_instruction,
            )) => call_instruction,
            _ => panic!("encountered unexpected instruction kind"),
        };
        for param in call_instruction.params().iter().copied() {
            self.builder.ctx.value_users[param].insert(ValueUser::Instr(instr));
        }
        Ok(instr)
    }

    pub fn constant<C>(mut self, constant: C) -> Result<Value, Error>
    where
        C: Into<Const>,
    {
        let constant = constant.into();
        let instruction = ConstInstr::new(constant);
        let (value, _) =
            self.append_value_instr(instruction.into(), constant.ty())?;
        Ok(value)
    }

    /// Registers all values that are used by the instruction.
    ///
    /// This is automated by the value visitor implementation of all instructions.
    fn register_uses(&mut self, instr: Instr) {
        let FunctionBuilderContext {
            instrs,
            value_users,
            ..
        } = &mut self.builder.ctx;
        let instruction = &instrs[instr];
        instruction.visit_values(|value| {
            value_users[value].insert(ValueUser::Instr(instr));
            true
        })
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
    ) -> Result<(), Error> {
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
    ) -> Result<Value, Error> {
        self.expect_type(source, int_type.into())?;
        let instruction = UnaryIntInstr::new(op, int_type, source);
        let (value, _instr) =
            self.append_value_instr(instruction.into(), int_type.into())?;
        Ok(value)
    }

    /// Integer count leading zeros.
    pub fn iclz(
        self,
        int_type: IntType,
        source: Value,
    ) -> Result<Value, Error> {
        self.iunary(UnaryIntOp::LeadingZeros, int_type, source)
    }

    /// Integer count trailing zeros.
    pub fn ictz(
        self,
        int_type: IntType,
        source: Value,
    ) -> Result<Value, Error> {
        self.iunary(UnaryIntOp::TrailingZeros, int_type, source)
    }

    /// Integer count ones.
    pub fn ipopcnt(
        self,
        int_type: IntType,
        source: Value,
    ) -> Result<Value, Error> {
        self.iunary(UnaryIntOp::PopCount, int_type, source)
    }

    /// Convenience function to construct integer shift and rotate instructions.
    fn ishift(
        mut self,
        op: ShiftIntOp,
        int_type: IntType,
        source: Value,
        shift_amount: Value,
    ) -> Result<Value, Error> {
        self.expect_type(source, int_type.into())?;
        self.expect_type(shift_amount, IntType::I32.into())?;
        let instruction =
            ShiftIntInstr::new(op, int_type, source, shift_amount);
        let (value, _instr) =
            self.append_value_instr(instruction.into(), int_type.into())?;
        Ok(value)
    }

    /// Integer left shift.
    pub fn ishl(
        self,
        int_type: IntType,
        source: Value,
        shift_amount: Value,
    ) -> Result<Value, Error> {
        self.ishift(ShiftIntOp::Shl, int_type, source, shift_amount)
    }

    /// Integer unsigned right shift.
    pub fn iushr(
        self,
        int_type: IntType,
        source: Value,
        shift_amount: Value,
    ) -> Result<Value, Error> {
        self.ishift(ShiftIntOp::Ushr, int_type, source, shift_amount)
    }

    /// Integer signed right shift.
    pub fn isshr(
        self,
        int_type: IntType,
        source: Value,
        shift_amount: Value,
    ) -> Result<Value, Error> {
        self.ishift(ShiftIntOp::Sshr, int_type, source, shift_amount)
    }

    /// Integer rotate left.
    pub fn irotl(
        self,
        int_type: IntType,
        source: Value,
        shift_amount: Value,
    ) -> Result<Value, Error> {
        self.ishift(ShiftIntOp::Rotl, int_type, source, shift_amount)
    }

    /// Integer rotate right.
    pub fn irotr(
        self,
        int_type: IntType,
        source: Value,
        shift_amount: Value,
    ) -> Result<Value, Error> {
        self.ishift(ShiftIntOp::Rotr, int_type, source, shift_amount)
    }

    /// Convenience function to construct binary integer instructions.
    fn ibinary(
        mut self,
        op: BinaryIntOp,
        ty: IntType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, Error> {
        self.expect_type(lhs, ty.into())?;
        self.expect_type(rhs, ty.into())?;
        let instruction = BinaryIntInstr::new(op, ty, lhs, rhs);
        let (value, _instr) =
            self.append_value_instr(instruction.into(), ty.into())?;
        Ok(value)
    }

    /// Integer addition.
    pub fn iadd(
        self,
        ty: IntType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, Error> {
        self.ibinary(BinaryIntOp::Add, ty, lhs, rhs)
    }

    /// Integer subtraction.
    pub fn isub(
        self,
        ty: IntType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, Error> {
        self.ibinary(BinaryIntOp::Sub, ty, lhs, rhs)
    }

    /// Integer multiplication.
    pub fn imul(
        self,
        ty: IntType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, Error> {
        self.ibinary(BinaryIntOp::Mul, ty, lhs, rhs)
    }

    /// Signed integer division.
    pub fn sdiv(
        self,
        ty: IntType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, Error> {
        self.ibinary(BinaryIntOp::Sdiv, ty, lhs, rhs)
    }

    /// Unsigned integer division.
    pub fn udiv(
        self,
        ty: IntType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, Error> {
        self.ibinary(BinaryIntOp::Udiv, ty, lhs, rhs)
    }

    /// Signed integer remainder.
    pub fn srem(
        self,
        ty: IntType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, Error> {
        self.ibinary(BinaryIntOp::Srem, ty, lhs, rhs)
    }

    /// Unsigned integer remainder.
    pub fn urem(
        self,
        ty: IntType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, Error> {
        self.ibinary(BinaryIntOp::Urem, ty, lhs, rhs)
    }

    /// Integer bit-wise AND.
    pub fn iand(
        self,
        ty: IntType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, Error> {
        self.ibinary(BinaryIntOp::And, ty, lhs, rhs)
    }

    /// Integer bit-wise OR.
    pub fn ior(
        self,
        ty: IntType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, Error> {
        self.ibinary(BinaryIntOp::Or, ty, lhs, rhs)
    }

    /// Integer bit-wise XOR.
    pub fn ixor(
        self,
        ty: IntType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, Error> {
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
    ) -> Result<Value, Error> {
        self.expect_type(lhs, ty.into())?;
        self.expect_type(rhs, ty.into())?;
        let instruction = CompareIntInstr::new(op, ty, lhs, rhs);
        let (value, _instr) =
            self.append_value_instr(instruction.into(), IntType::I1.into())?;
        Ok(value)
    }

    /// Convenience function to construct unary float instructions.
    fn funary(
        mut self,
        op: UnaryFloatOp,
        ty: FloatType,
        source: Value,
    ) -> Result<Value, Error> {
        self.expect_type(source, ty.into())?;
        let instruction = UnaryFloatInstr::new(op, ty, source);
        let (value, _instr) =
            self.append_value_instr(instruction.into(), ty.into())?;
        Ok(value)
    }

    /// Float absolute value.
    pub fn fabs(self, ty: FloatType, source: Value) -> Result<Value, Error> {
        self.funary(UnaryFloatOp::Abs, ty, source)
    }

    /// Float negate.
    pub fn fneg(self, ty: FloatType, source: Value) -> Result<Value, Error> {
        self.funary(UnaryFloatOp::Neg, ty, source)
    }

    /// Float square root.
    pub fn fsqrt(self, ty: FloatType, source: Value) -> Result<Value, Error> {
        self.funary(UnaryFloatOp::Sqrt, ty, source)
    }

    /// Float round to ceil.
    pub fn fceil(self, ty: FloatType, source: Value) -> Result<Value, Error> {
        self.funary(UnaryFloatOp::Ceil, ty, source)
    }

    /// Float round to floor.
    pub fn ffloor(self, ty: FloatType, source: Value) -> Result<Value, Error> {
        self.funary(UnaryFloatOp::Floor, ty, source)
    }

    /// Float round to next smaller integer.
    pub fn ftruncate(
        self,
        ty: FloatType,
        source: Value,
    ) -> Result<Value, Error> {
        self.funary(UnaryFloatOp::Truncate, ty, source)
    }

    /// Float round to the nearest integer.
    pub fn fnearest(
        self,
        ty: FloatType,
        source: Value,
    ) -> Result<Value, Error> {
        self.funary(UnaryFloatOp::Nearest, ty, source)
    }

    /// Convenience function to construct binary float instructions.
    fn fbinary(
        mut self,
        op: BinaryFloatOp,
        ty: FloatType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, Error> {
        self.expect_type(lhs, ty.into())?;
        self.expect_type(rhs, ty.into())?;
        let instruction = BinaryFloatInstr::new(op, ty, lhs, rhs);
        let (value, _instr) =
            self.append_value_instr(instruction.into(), ty.into())?;
        Ok(value)
    }

    /// Float addition.
    pub fn fadd(
        self,
        ty: FloatType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, Error> {
        self.fbinary(BinaryFloatOp::Add, ty, lhs, rhs)
    }

    /// Float subtraction.
    pub fn fsub(
        self,
        ty: FloatType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, Error> {
        self.fbinary(BinaryFloatOp::Sub, ty, lhs, rhs)
    }

    /// Float multiplication.
    pub fn fmul(
        self,
        ty: FloatType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, Error> {
        self.fbinary(BinaryFloatOp::Mul, ty, lhs, rhs)
    }

    /// Float division.
    pub fn fdiv(
        self,
        ty: FloatType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, Error> {
        self.fbinary(BinaryFloatOp::Div, ty, lhs, rhs)
    }

    /// Float minimum element.
    pub fn fmin(
        self,
        ty: FloatType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, Error> {
        self.fbinary(BinaryFloatOp::Min, ty, lhs, rhs)
    }

    /// Float maximum element.
    pub fn fmax(
        self,
        ty: FloatType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, Error> {
        self.fbinary(BinaryFloatOp::Max, ty, lhs, rhs)
    }

    /// Float copy-sign operation.
    pub fn fcopysign(
        self,
        ty: FloatType,
        lhs: Value,
        rhs: Value,
    ) -> Result<Value, Error> {
        self.fbinary(BinaryFloatOp::CopySign, ty, lhs, rhs)
    }

    /// Float comparison given a comparator.
    ///
    /// # Comparator Kinds
    ///
    /// - `eq`: Tests for bit-wise equality.
    /// - `ne`: Tests for bit-wise inequality.
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
    ) -> Result<Value, Error> {
        self.expect_type(lhs, ty.into())?;
        self.expect_type(rhs, ty.into())?;
        let instruction = CompareFloatInstr::new(op, ty, lhs, rhs);
        let (value, _instr) =
            self.append_value_instr(instruction.into(), IntType::I1.into())?;
        Ok(value)
    }

    /// Selects either `if_true` or `if_false` depending on the value of `condition`.
    ///
    /// # Note
    ///
    /// This is very similar to an if-then-else instruction that does not require jumps.
    pub fn bool_select(
        self,
        ty: Type,
        condition: Value,
        if_true: Value,
        if_false: Value,
    ) -> Result<Value, Error> {
        self.match_select(
            IntType::I1,
            ty,
            condition,
            if_true,
            [if_false].iter().copied(),
        )
    }
}

/// Builder to construct a match select instruction returning multiple values per arm.
#[derive(Debug)]
pub struct MatchSelectInstructionBuilder<'a, 'b: 'a> {
    /// The underlying instruction builder for the function body.
    instr_builder: InstructionBuilder<'a, 'b>,
    /// The underlying builder for the multi-select instruction.
    match_builder: MatchSelectInstrBuilder,
}

impl<'a, 'b: 'a> MatchSelectInstructionBuilder<'a, 'b> {
    /// Pushes another results tuple match arm to the constructed `MatchSelectInstr`.
    ///
    /// # Panics
    ///
    /// If the `results` tuple iterator does not yield exactly as many values as there
    /// are expected return types for the constructed `MatchSelectInstr`.
    ///
    /// # Errors
    ///
    /// If the `results` tuple value types do not match the expected results types.
    pub fn push_results<T>(&mut self, results: T) -> Result<(), Error>
    where
        T: IntoIterator<Item = Value>,
    {
        self.match_builder.push_results(results);
        let pushed_values = self.match_builder.last_pushed_values();
        let result_types = self.match_builder.result_types();
        for (default_result, expected_type) in pushed_values
            .iter()
            .copied()
            .zip(result_types.iter().copied())
        {
            self.instr_builder
                .expect_type(default_result, expected_type)?;
        }
        Ok(())
    }

    /// Pushes another results tuple match arm to the constructed `MatchSelectInstr`.
    ///
    /// # Panics
    ///
    /// If the `results` tuple iterator does not yield exactly as many values as there
    /// are expected return types for the constructed `MatchSelectInstr`.
    ///
    /// # Errors
    ///
    /// If the `results` tuple value types do not match the expected results types.
    pub fn with_results<T>(mut self, results: T) -> Result<Self, Error>
    where
        T: IntoIterator<Item = Value>,
    {
        self.push_results(results)?;
        Ok(self)
    }

    /// Pushes the default results tuple to the constructed `MatchSelectInstr`.
    ///
    /// # Panics
    ///
    /// If the `default_results` tuple iterator does not yield exactly as many values as there
    /// are expected return types for the constructed `MatchSelectInstr`.
    ///
    /// # Errors
    ///
    /// If the `default_results` tuple value types do not match the expected results types.
    pub fn finish<T>(self, default_results: T) -> Result<Instr, Error>
    where
        T: IntoIterator<Item = Value>,
    {
        let Self {
            mut instr_builder,
            match_builder,
        } = self;
        let instruction = match_builder.finish(default_results);
        for (default_result, expected_type) in instruction
            .default_results()
            .iter()
            .copied()
            .zip(instruction.result_types().iter().copied())
        {
            instr_builder.expect_type(default_result, expected_type)?;
        }
        // Having to allocate heap memory for more than 8 returned types
        // per match arm is not ideal, however, having 8 return types per
        // match arm is by far a common case either.
        //
        // We choose `[Type; 8]` because up to this point the `SmallVec`
        // yields the same `size_of`.
        let result_types = instruction
            .result_types()
            .iter()
            .copied()
            .collect::<SmallVec<[Type; 8]>>();
        let instr = instr_builder
            .append_multi_value_instr(instruction.into(), &result_types)?;
        Ok(instr)
    }
}

impl<'a, 'b: 'a> InstructionBuilder<'a, 'b> {
    /// Selects from the given target result values or the default given a selector.
    ///
    /// # Note
    ///
    /// This can be used in order to construct `MatchSelectInstr` instructions where
    /// match arms are required to return more than just a single value. Since the
    /// construction is more complex than with just a single returned value per match
    /// arm users are free to use the simpler [`match_select`][1] or [`bool_select`][2]
    /// constructors.
    ///
    /// [1]: `InstructionBuilder::match_select`
    /// [2]: `InstructionBuilder::bool_select`
    ///
    /// # Note
    ///
    /// This mirrors the branching table construct but using value semantics instead
    /// of taking branches.
    pub fn match_select_multi<T>(
        self,
        selector_type: IntType,
        selector: Value,
        result_types: T,
    ) -> Result<MatchSelectInstructionBuilder<'a, 'b>, Error>
    where
        T: IntoIterator<Item = Type>,
    {
        self.expect_type(selector, selector_type.into())?;
        let match_builder =
            MatchSelectInstr::new_multi(selector, selector_type, result_types);
        Ok(MatchSelectInstructionBuilder {
            instr_builder: self,
            match_builder,
        })
    }

    /// Selects from the given target result values or the default given a selector.
    ///
    /// # Note
    ///
    /// This mirrors the branching table construct but using value semantics instead
    /// of taking branches.
    pub fn match_select<T>(
        mut self,
        selector_type: IntType,
        result_type: Type,
        selector: Value,
        default_result: Value,
        target_results: T,
    ) -> Result<Value, Error>
    where
        T: IntoIterator<Item = Value>,
    {
        self.expect_type(selector, selector_type.into())?;
        self.expect_type(default_result, result_type)?;
        let instruction = MatchSelectInstr::new(
            selector,
            selector_type,
            result_type,
            default_result,
            target_results,
        );
        let mut at = 0;
        while let Some(results) = instruction.target_results(at) {
            assert_eq!(results.len(), 1);
            self.expect_type(results[0], result_type)?;
            at += 1;
        }
        let (value, _instr) =
            self.append_value_instr(instruction.into(), result_type)?;
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
    ) -> Result<Value, Error> {
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
        let (value, _instr) =
            self.append_value_instr(instruction.into(), to_type)?;
        Ok(value)
    }

    /// Extends the source integer to the destination integer type.
    ///
    /// # Errors
    ///
    /// If the destination integer type does not have a bit-width greater than or equal
    /// to the source type.
    pub fn iextend(
        mut self,
        from_type: IntType,
        to_type: IntType,
        src: Value,
        signed: bool,
    ) -> Result<Value, Error> {
        if from_type.bit_width() > to_type.bit_width() {
            return Err(FunctionBuilderError::InvalidExtension {
                from_type,
                to_type,
            })
            .map_err(Into::into)
        }
        let instruction = ExtendIntInstr::new(signed, from_type, to_type, src);
        let (value, _instr) =
            self.append_value_instr(instruction.into(), to_type.into())?;
        Ok(value)
    }

    /// Truncates the source integer to the destination integer type.
    ///
    /// # Errors
    ///
    /// If the destination integer type does not have a bit-width greater than or equal
    /// to the source type.
    pub fn itruncate(
        mut self,
        from_type: IntType,
        to_type: IntType,
        src: Value,
    ) -> Result<Value, Error> {
        if to_type.bit_width() > from_type.bit_width() {
            return Err(FunctionBuilderError::InvalidTruncation {
                from_type,
                to_type,
            })
            .map_err(Into::into)
        }
        let instruction = TruncateIntInstr::new(from_type, to_type, src);
        let (value, _instr) =
            self.append_value_instr(instruction.into(), to_type.into())?;
        Ok(value)
    }

    /// Promotes the source float to the other (bigger) float type.
    ///
    /// # Errors
    ///
    /// If the source type is bigger than the promoted-to type.
    pub fn promote(
        mut self,
        from_type: FloatType,
        to_type: FloatType,
        src: Value,
    ) -> Result<Value, Error> {
        if from_type.bit_width() > to_type.bit_width() {
            return Err(FunctionBuilderError::InvalidPromotion {
                from_type,
                to_type,
            })
            .map_err(Into::into)
        }
        let instruction = PromoteFloatInstr::new(from_type, to_type, src);
        let (value, _instr) =
            self.append_value_instr(instruction.into(), to_type.into())?;
        Ok(value)
    }

    /// Demotes the source float to the other (bigger) float type.
    ///
    /// # Errors
    ///
    /// If the source type is smaller than the demoted-to type.
    pub fn demote(
        mut self,
        from_type: FloatType,
        to_type: FloatType,
        src: Value,
    ) -> Result<Value, Error> {
        if from_type.bit_width() < to_type.bit_width() {
            return Err(FunctionBuilderError::InvalidPromotion {
                from_type,
                to_type,
            })
            .map_err(Into::into)
        }
        let instruction = DemoteFloatInstr::new(from_type, to_type, src);
        let (value, _instr) =
            self.append_value_instr(instruction.into(), to_type.into())?;
        Ok(value)
    }

    /// Converts the float value into an integer value.
    ///
    /// - The `dst_signed` flag determines if the resulting integer
    ///   value shall be treated as if the integer is signed.
    /// - The `saturating` flag determines if the conversion may
    ///   trap upon failure or simply saturates to integer boundaries.
    pub fn float_to_int(
        mut self,
        src_type: FloatType,
        dst_type: IntType,
        dst_signed: bool,
        src: Value,
        saturating: bool,
    ) -> Result<Value, Error> {
        let instruction = FloatToIntInstr::new(
            src_type, dst_type, dst_signed, src, saturating,
        );
        let (value, _instr) =
            self.append_value_instr(instruction.into(), dst_type.into())?;
        Ok(value)
    }

    /// Converts the integer value into an floating point value.
    ///
    /// - The `signed` flag determines if the source integer
    ///   value shall be treated as if the integer is signed.
    pub fn int_to_float(
        mut self,
        signed: bool,
        src_type: IntType,
        dst_type: FloatType,
        src: Value,
    ) -> Result<Value, Error> {
        let instruction = IntToFloatInstr::new(signed, src_type, dst_type, src);
        let (value, _instr) =
            self.append_value_instr(instruction.into(), dst_type.into())?;
        Ok(value)
    }

    /// Retrieves the heap address at the byte position for the given linear memory of given size.
    ///
    /// The returned value can be used to load and store values from and to linear memory
    /// with an offset that is valid for the given size.
    pub fn heap_addr(
        mut self,
        mem: Mem,
        pos: Value,
        size: ImmU32,
    ) -> Result<Value, Error> {
        self.expect_type(pos, IntType::I32.into())?;
        let instruction = HeapAddrInstr::new(mem, pos, size);
        let (value, _instr) =
            self.append_value_instr(instruction.into(), Type::Ptr)?;
        Ok(value)
    }

    /// Loads a value of the given type from the pointer with given offset.
    pub fn load(
        mut self,
        ptr: Value,
        offset: ImmU32,
        ty: Type,
    ) -> Result<Value, Error> {
        self.expect_type(ptr, Type::Ptr)?;
        let instruction = LoadInstr::new(ty, ptr, offset);
        let (value, _instr) =
            self.append_value_instr(instruction.into(), ty)?;
        Ok(value)
    }

    /// Stores the given value of the given type to the pointer with given offset.
    pub fn store(
        mut self,
        ptr: Value,
        offset: ImmU32,
        stored_value: Value,
        ty: Type,
    ) -> Result<Instr, Error> {
        self.expect_type(ptr, Type::Ptr)?;
        let instruction = StoreInstr::new(ptr, offset, stored_value, ty);
        let instr = self.append_instr(instruction)?;
        Ok(instr)
    }

    /// Appends the instruction onto the current basic block.
    ///
    /// Fills the block in case the instruction is a terminal instruction.
    fn append_instr<I>(&mut self, instruction: I) -> Result<Instr, Error>
    where
        I: Into<Instruction>,
    {
        let block = self.builder.current_block()?;
        if self.builder.ctx.block_filled.get(block) {
            return Err(FunctionBuilderError::BasicBlockIsAlreadyFilled {
                block,
            })
            .map_err(Into::into)
        }
        let instruction = instruction.into();
        let is_terminal = instruction.is_terminal();
        let instr = self.builder.ctx.instrs.alloc(instruction);
        self.builder.ctx.block_instrs[block].push(instr);
        if is_terminal {
            self.builder.ctx.block_filled.set(block, true);
        }
        self.register_uses(instr);
        Ok(instr)
    }

    /// Returns the given value to the caller of the function.
    pub fn return_values<T>(mut self, return_values: T) -> Result<Instr, Error>
    where
        T: IntoIterator<Item = Value>,
    {
        let return_values = return_values.into_iter();
        let func_type = self
            .builder
            .res
            .get_func_type(self.builder.func)
            .unwrap_or_else(|| {
                panic!(
                    "encountered missing function type while building function {}",
                    self.builder.func
                )
            });
        let return_instr = ReturnInstr::new(return_values);
        let returned_types = return_instr
            .return_values()
            .iter()
            .map(|&value| self.builder.ctx.value_type[value]);
        let expected_return_types = func_type.outputs().iter().copied();
        if !expected_return_types.clone().eq(returned_types.clone()) {
            return Err(FunctionBuilderError::UnmatchingFunctionReturnType {
                returned_types: returned_types.collect(),
                expected_types: expected_return_types.collect(),
            })
            .map_err(Into::into)
        }
        let instr = self.append_instr(return_instr)?;
        Ok(instr)
    }

    /// Unconditionally jumps to the target basic block.
    pub fn br<A>(mut self, target: Block, args: A) -> Result<Instr, Error>
    where
        A: IntoIterator<Item = Value>,
    {
        let block = self.builder.current_block()?;
        let edge = self.add_branching_edge(target, block, args)?;
        let instr = self.append_instr(BranchInstr::new(edge))?;
        Ok(instr)
    }

    /// Immediately aborts execution when reached.
    pub fn unreachable(mut self) -> Result<Instr, Error> {
        self.append_instr(TerminalInstr::Unreachable)
    }

    /// Conditionally jumps to either `then_target` or `else_target` depending on
    /// the value of `condition`.
    pub fn if_then_else<A1, A2>(
        self,
        condition: Value,
        then_target: Block,
        else_target: Block,
        then_args: A1,
        else_args: A2,
    ) -> Result<Instr, Error>
    where
        A1: IntoIterator<Item = Value>,
        A2: IntoIterator<Item = Value>,
    {
        let instr = self
            .match_branch(IntType::I1, condition)?
            .with_edge(else_target, else_args)?
            .finish(then_target, then_args)?;
        Ok(instr)
    }
}

/// Builder used in order to construct `MatchBranchInstr` instructions.
#[derive(Debug)]
pub struct MatchBranchBuilder<'a, 'b: 'a> {
    /// The underlying instruction builder for the function body.
    instr_builder: InstructionBuilder<'a, 'b>,
    /// The instruction under construction.
    match_instr: MatchBranchInstrBuilder,
}

impl<'a, 'b: 'a> MatchBranchBuilder<'a, 'b> {
    /// Pushes another edge to the `MatchBranchInstr` under construction.
    pub fn push_edge<A>(
        &mut self,
        destination: Block,
        args: A,
    ) -> Result<(), Error>
    where
        A: IntoIterator<Item = Value>,
    {
        let current = self.instr_builder.builder.current_block()?;
        let edge = self.instr_builder.add_branching_edge(
            destination,
            current,
            args,
        )?;
        self.match_instr.push_edge(edge);
        Ok(())
    }

    /// Pushes another edge to the `MatchBranchInstr` under construction.
    pub fn with_edge<A>(
        mut self,
        destination: Block,
        args: A,
    ) -> Result<Self, Error>
    where
        A: IntoIterator<Item = Value>,
    {
        self.push_edge(destination, args)?;
        Ok(self)
    }

    /// Finishes construction of the `MatchBranchInstr`.
    pub fn finish<A>(
        mut self,
        default_destination: Block,
        default_args: A,
    ) -> Result<Instr, Error>
    where
        A: IntoIterator<Item = Value>,
    {
        let default_edge = self.instr_builder.add_branching_edge_from_current(
            default_destination,
            default_args,
        )?;
        let instr = self
            .instr_builder
            .append_instr(self.match_instr.finish(default_edge))?;
        Ok(instr)
    }
}

impl<'a, 'b: 'a> InstructionBuilder<'a, 'b> {
    /// Constructs a match-branch instruction.
    ///
    /// This is the conditional jump that selects one of a set of match arms
    /// with different branching edges.
    pub fn match_branch(
        self,
        selector_type: IntType,
        selector: Value,
    ) -> Result<MatchBranchBuilder<'a, 'b>, Error> {
        self.expect_type(selector, selector_type.into())?;
        let builder = MatchBranchBuilder {
            instr_builder: self,
            match_instr: MatchBranchInstr::build(selector_type, selector),
        };
        Ok(builder)
    }

    /// Adds a new branching edge between the current block and the
    /// destination using the given arguments.
    ///
    /// # Errors
    ///
    /// - If the new predecessor is not yet filled.
    /// - If the block that gains a new predecessor has already been sealed.
    /// - If the new predecessor is already a predecessor of the block.
    /// - If the given arguments cannot be applied to the destination block.
    fn add_branching_edge_from_current<A>(
        &mut self,
        destination: Block,
        args: A,
    ) -> Result<Edge, Error>
    where
        A: IntoIterator<Item = Value>,
    {
        let current = self.builder.current_block()?;
        let edge = self.add_branching_edge(destination, current, args)?;
        Ok(edge)
    }

    /// Adds a new branching edge between the basic blocks with the given arguments.
    ///
    /// # Errors
    ///
    /// - If the new predecessor is not yet filled.
    /// - If the block that gains a new predecessor has already been sealed.
    /// - If the new predecessor is already a predecessor of the block.
    /// - If the given arguments cannot be applied to the destination block.
    fn add_branching_edge<A>(
        &mut self,
        destination: Block,
        source: Block,
        args: A,
    ) -> Result<Edge, Error>
    where
        A: IntoIterator<Item = Value>,
    {
        if self.builder.ctx.block_sealed.get(destination) {
            return Err(FunctionBuilderError::PredecessorForSealedBlock {
                sealed_block: destination,
                new_pred: source,
            })
            .map_err(Into::into)
        }
        let edge = self.builder.ctx.edges.alloc_some(1);
        self.builder.ctx.edge_src.insert(edge, source);
        self.builder.ctx.edge_dst.insert(edge, destination);
        debug_assert!(self.builder.ctx.edge_args[edge].is_empty());
        self.builder.ctx.edge_args[edge].extend(args);
        self.builder.ctx.block_edges[destination].push(edge);
        for &arg in &self.builder.ctx.edge_args[edge] {
            self.builder.ctx.value_users[arg].insert(ValueUser::Edge(edge));
        }
        Ok(edge)
    }
}
