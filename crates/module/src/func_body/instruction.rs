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
        DemoteFloatInstr,
        ExtendIntInstr,
        FloatToIntInstr,
        HeapAddrInstr,
        IfThenElseInstr,
        Instruction,
        IntToFloatInstr,
        LoadInstr,
        PromoteFloatInstr,
        ReinterpretInstr,
        ReturnInstr,
        SelectInstr,
        ShiftIntInstr,
        StoreInstr,
        TailCallInstr,
        TerminalInstr,
        TruncateIntInstr,
        UnaryFloatInstr,
        UnaryIntInstr,
    },
    primitive::{Block, Const, FloatType, Func, IntType, Mem, Type, Value},
    ImmU32,
};

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

    pub fn call<P>(
        mut self,
        func: Func,
        params: P,
    ) -> Result<(Option<Value>, Instr), IrError>
    where
        P: IntoIterator<Item = Value>,
    {
        let instruction = CallInstr::new(func, params);
        let func_type = self
            .builder
            .res
            .get_func_type(func)
            .unwrap_or_else(|| {
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
        if let Some(output) = func_type.outputs().first() {
            let (value, instr) =
                self.append_value_instr(instruction.into(), *output)?;
            Ok((Some(value), instr))
        } else {
            let instr = self.append_instr(instruction)?;
            Ok((None, instr))
        }
    }

    pub fn tail_call<P>(
        mut self,
        func: Func,
        params: P,
    ) -> Result<Instr, IrError>
    where
        P: IntoIterator<Item = Value>,
    {
        let instruction = TailCallInstr::new(func, params);
        let func_type = self
            .builder
            .res
            .get_func_type(func)
            .unwrap_or_else(|| {
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
        Ok(instr)
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
    fn register_uses<T>(&mut self, instr: Instr, uses: T)
    where
        T: IntoIterator<Item = Value>,
    {
        for value in uses {
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
        self.register_uses(instr, [source].iter().copied());
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
        self.register_uses(instr, [source, shift_amount].iter().copied());
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
        self.register_uses(instr, [lhs, rhs].iter().copied());
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
        self.register_uses(instr, [lhs, rhs].iter().copied());
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
        self.register_uses(instr, [source].iter().copied());
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
        self.register_uses(instr, [lhs, rhs].iter().copied());
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
        self.register_uses(instr, [lhs, rhs].iter().copied());
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
        self.register_uses(
            instr,
            [condition, if_true, if_false].iter().copied(),
        );
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
        self.register_uses(instr, [src].iter().copied());
        Ok(value)
    }

    /// Extends the source integer to the destination integer type.
    ///
    /// # Errors
    ///
    /// If the destination integer type does not have a bitwidth greater than or equal
    /// to the source type.
    pub fn iextend(
        mut self,
        from_type: IntType,
        to_type: IntType,
        src: Value,
        signed: bool,
    ) -> Result<Value, IrError> {
        if from_type.bit_width() > to_type.bit_width() {
            return Err(FunctionBuilderError::InvalidExtension {
                from_type,
                to_type,
            })
            .map_err(Into::into)
        }
        let instruction = ExtendIntInstr::new(signed, from_type, to_type, src);
        let (value, instr) =
            self.append_value_instr(instruction.into(), to_type.into())?;
        self.register_uses(instr, [src].iter().copied());
        Ok(value)
    }

    /// Truncates the source integer to the destination integer type.
    ///
    /// # Errors
    ///
    /// If the destination integer type does not have a bitwidth greater than or equal
    /// to the source type.
    pub fn itruncate(
        mut self,
        from_type: IntType,
        to_type: IntType,
        src: Value,
    ) -> Result<Value, IrError> {
        if to_type.bit_width() > from_type.bit_width() {
            return Err(FunctionBuilderError::InvalidTruncation {
                from_type,
                to_type,
            })
            .map_err(Into::into)
        }
        let instruction = TruncateIntInstr::new(from_type, to_type, src);
        let (value, instr) =
            self.append_value_instr(instruction.into(), to_type.into())?;
        self.register_uses(instr, [src].iter().copied());
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
    ) -> Result<Value, IrError> {
        if from_type.bit_width() > to_type.bit_width() {
            return Err(FunctionBuilderError::InvalidPromotion {
                from_type,
                to_type,
            })
            .map_err(Into::into)
        }
        let instruction = PromoteFloatInstr::new(from_type, to_type, src);
        let (value, instr) =
            self.append_value_instr(instruction.into(), to_type.into())?;
        self.register_uses(instr, [src].iter().copied());
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
    ) -> Result<Value, IrError> {
        if from_type.bit_width() < to_type.bit_width() {
            return Err(FunctionBuilderError::InvalidPromotion {
                from_type,
                to_type,
            })
            .map_err(Into::into)
        }
        let instruction = DemoteFloatInstr::new(from_type, to_type, src);
        let (value, instr) =
            self.append_value_instr(instruction.into(), to_type.into())?;
        self.register_uses(instr, [src].iter().copied());
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
    ) -> Result<Value, IrError> {
        let instruction = FloatToIntInstr::new(
            src_type, dst_type, dst_signed, src, saturating,
        );
        let (value, instr) =
            self.append_value_instr(instruction.into(), dst_type.into())?;
        self.register_uses(instr, [src].iter().copied());
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
    ) -> Result<Value, IrError> {
        let instruction = IntToFloatInstr::new(signed, src_type, dst_type, src);
        let (value, instr) =
            self.append_value_instr(instruction.into(), dst_type.into())?;
        self.register_uses(instr, [src].iter().copied());
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
    ) -> Result<Value, IrError> {
        self.expect_type(pos, IntType::I32.into())?;
        let instruction = HeapAddrInstr::new(mem, pos, size);
        let (value, instr) =
            self.append_value_instr(instruction.into(), Type::Ptr)?;
        self.register_uses(instr, [pos].iter().copied());
        Ok(value)
    }

    /// Loads a value of the given type from the pointer with given offset.
    pub fn load(
        mut self,
        ptr: Value,
        offset: ImmU32,
        ty: Type,
    ) -> Result<Value, IrError> {
        self.expect_type(ptr, Type::Ptr)?;
        let instruction = LoadInstr::new(ty, ptr, offset);
        let (value, instr) = self.append_value_instr(instruction.into(), ty)?;
        self.register_uses(instr, [ptr].iter().copied());
        Ok(value)
    }

    /// Stores the given value of the given type to the pointer with given offset.
    pub fn store(
        mut self,
        ptr: Value,
        offset: ImmU32,
        stored_value: Value,
        ty: Type,
    ) -> Result<Instr, IrError> {
        self.expect_type(ptr, Type::Ptr)?;
        let instruction = StoreInstr::new(ptr, offset, stored_value, ty);
        let instr = self.append_instr(instruction)?;
        self.register_uses(instr, [ptr, stored_value].iter().copied());
        Ok(instr)
    }

    /// Appends the instruction onto the current basic block.
    ///
    /// Fills the block in case the instruction is a terminal instruction.
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
    pub fn return_values<T>(
        mut self,
        return_values: T,
    ) -> Result<Instr, IrError>
    where
        T: IntoIterator<Item = Value>,
        <T as IntoIterator>::IntoIter: Clone,
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
        let expected_outputs = func_type.outputs().iter().copied();
        let return_types = return_values
            .clone()
            .map(|val| self.builder.ctx.value_type[val]);
        if !return_types.clone().eq(expected_outputs.clone()) {
            return Err(FunctionBuilderError::UnmatchingFunctionReturnType {
                returned_types: return_types.collect(),
                expected_types: expected_outputs.collect(),
            })
            .map_err(Into::into)
        }
        let ret_instr = ReturnInstr::new(return_values.clone());
        let instr = self.append_instr(ret_instr)?;
        self.register_uses(instr, return_values);
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
        self.register_uses(instr, [condition].iter().copied());
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
