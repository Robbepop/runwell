// Copyright 2020 Robin Freyler
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
    instr::Instruction,
    instruction::{IaddInstr, ImulInstr, SdivInstr, SelectInstr, UdivInstr},
    BasicBlockId,
    IntType,
    IrError,
    Type,
    Value,
    ValueGen,
};
use crate::{
    builder::ModuleResource,
    ir::instr::ConstInstr,
    parse2::{
        FunctionBody,
        FunctionType,
        LocalVariableEntry,
        LocalsIter,
        OperatorsIter,
    },
    Index32,
};
use std::collections::HashMap;
use wasmparser::Operator;

pub struct FunctionTranslator<'a, 'b> {
    resource: &'a ModuleResource,
    ops: OperatorsIter<'b>,
    value_numbering: ValueNumbering,
}

impl<'a, 'b> FunctionTranslator<'a, 'b> {
    pub fn new(
        resource: &'a ModuleResource,
        func_body: FunctionBody<'b>,
    ) -> Self {
        let func_type_id = resource
            .function_types
            .get(func_body.id())
            .expect("unexpected missing function for ID")
            .shared();
        let func_type = resource.types.get(*func_type_id);
        Self {
            resource,
            ops: func_body.ops(),
            value_numbering: ValueNumbering::new(func_type, func_body.locals()),
        }
    }
}

#[derive(Debug)]
pub struct BasicBlocks {
    len_blocks: u32,
    current_block: BasicBlockId,
    entry_block: BasicBlockId,
    blocks: HashMap<BasicBlockId, BasicBlock>,
}

impl Default for BasicBlocks {
    fn default() -> Self {
        let mut blocks = HashMap::new();
        let entry_block = BasicBlockId::from_u32(0);
        blocks.insert(entry_block, BasicBlock::default());
        Self {
            len_blocks: 1,
            current_block: entry_block,
            entry_block,
            blocks,
        }
    }
}

#[derive(Debug, Default)]
pub struct BasicBlock {
    predecessors: Vec<BasicBlockId>,
}

/// The value numbering for translating Wasm operators to Runwell IR.
///
/// The numbering is sorted in the following way:
///
/// 1. All function inputs are assigned a unique value each in order
///    of their appearence.
/// 2. All declared local variables are assigned a unique value each
///    in order of their appearence.
/// 3. Then newly find unique instructions are assigned a unique value
///    and put into the value numbering table alongside their block.
/// 4. When querying for the value of such an instruction iteratively
///    look for occurences in the predessecors until reaching the
///    entry block.
#[derive(Debug)]
pub struct ValueNumbering {
    /// The types of all input parameters in order.
    inputs: Vec<Type>,
    /// The amount of type of all local variables.
    ///
    /// Stores as amount per type in order simply following the Wasm spec.
    /// If we stored a vector of one entry per local variable we would risk
    /// inefficiency for Wasm binaries with tons of local variables per function.
    locals: Vec<LocalVariableEntry>,
    /// The number of total local variables.
    len_locals: u32,
    /// The number of additionally generated non-input and non-local values.
    len_values: u32,
    /// Determines the shift of value index between predetermined
    /// inputs and locals and newly generated values.
    value_offset: u32,
    /// Generator to create new unique value IDs.
    value_gen: ValueGen,
    /// Basic blocks.
    blocks: BasicBlocks,
    /// Mapping from instruction and basic block to value.
    ///
    /// Used to deduplicate instructions and associate them with a unique value.
    instr_to_value: HashMap<(BasicBlockId, Instruction), Value>,
    /// All value entries.
    value_entries: Vec<ValueEntry>,
    /// The emulated Wasm stack using Runwell IR instruction instead of Wasm operators.
    stack: Vec<Value>,
}

impl ValueNumbering {
    /// Creates a new value numbering for the given function type and its local variables.
    pub fn new(func_type: &FunctionType, locals: LocalsIter) -> Self {
        let len_inputs = func_type.inputs().len() as u32;
        let inputs = func_type
            .inputs()
            .iter()
            .copied()
            .map(Type::from)
            .collect::<Vec<_>>();
        let locals = locals.map(|(_, entry)| entry).collect::<Vec<_>>();
        let len_locals = locals.iter().map(|entry| entry.count()).sum();
        let value_offset = len_inputs + len_locals;
        let value_gen = ValueGen::from(value_offset);
        Self {
            inputs,
            locals,
            len_locals,
            len_values: 0,
            value_offset,
            value_gen,
            blocks: BasicBlocks::default(),
            instr_to_value: HashMap::new(),
            value_entries: Vec::new(),
            stack: Vec::new(),
        }
    }

    /// Tries to pop 2 values from the emulation stack.
    ///
    /// Returns the second popped value followed by the first.
    fn pop_2(&mut self) -> Result<(Value, Value), IrError> {
        let rhs = self.stack.pop().ok_or(IrError::MissingStackValue {
            expected: 2,
            found: 0,
        })?;
        let lhs = self.stack.pop().ok_or(IrError::MissingStackValue {
            expected: 2,
            found: 1,
        })?;
        Ok((lhs, rhs))
    }

    /// Tries to pop 3 values from the emulation stack.
    ///
    /// Returns the values in reverse order in which they have been popped.
    fn pop_3(&mut self) -> Result<(Value, Value, Value), IrError> {
        let (snd, trd) = self.pop_2()?;
        let fst = self.stack.pop().ok_or(IrError::MissingStackValue {
            expected: 3,
            found: 2,
        })?;
        Ok((fst, snd, trd))
    }

    /// Tries to pop 2 values from the emulation stack
    /// and feeds them into the constructed instruction.
    fn process_binary_instruction<F, I>(
        &mut self,
        resource: &ModuleResource,
        f: F,
    ) -> Result<(), IrError>
    where
        F: FnOnce(Value, Value) -> I,
        I: Into<Instruction>,
    {
        let (lhs, rhs) = self.pop_2()?;
        self.push_instruction(resource, f(lhs, rhs))?;
        Ok(())
    }

    /// Pushes another Wasm operator to the IR translator.
    ///
    /// The pushed Wasm operators must be pushed in the same order in which
    /// they appear in the Wasm function body.
    pub fn push_operator(
        &mut self,
        resource: &ModuleResource,
        operator: Operator,
    ) -> Result<(), IrError> {
        match operator {
            Operator::LocalGet { local_index: _ } => {
                todo!()
            }
            Operator::LocalSet { local_index: _ } => {
                todo!()
            }
            Operator::LocalTee { local_index: _ } => {
                todo!()
            }
            Operator::I32Const { value } => {
                self.push_instruction(resource, ConstInstr::i32(value))?;
            }
            Operator::I64Const { value } => {
                self.push_instruction(resource, ConstInstr::i64(value))?;
            }
            Operator::F32Const { value } => {
                self.push_instruction(resource, ConstInstr::f32(value.into()))?;
            }
            Operator::F64Const { value } => {
                self.push_instruction(resource, ConstInstr::f64(value.into()))?;
            }
            Operator::I32Add => {
                self.process_binary_instruction(resource, |lhs, rhs| {
                    IaddInstr::new(IntType::I32, lhs, rhs)
                })
                .expect("i32.add: missing stack values");
            }
            Operator::I32Mul => {
                self.process_binary_instruction(resource, |lhs, rhs| {
                    ImulInstr::new(IntType::I32, lhs, rhs)
                })
                .expect("i32.mul: missing stack values");
            }
            Operator::I32DivS => {
                self.process_binary_instruction(resource, |lhs, rhs| {
                    SdivInstr::new(IntType::I32, lhs, rhs)
                })
                .expect("i32.divs: missing stack values");
            }
            Operator::I32DivU => {
                self.process_binary_instruction(resource, |lhs, rhs| {
                    UdivInstr::new(IntType::I32, lhs, rhs)
                })
                .expect("i32.divu: missing stack values");
            }
            Operator::Select => {
                let (condition, val1, val2) =
                    self.pop_3().expect("select: missing stack values");
                self.push_instruction(
                    resource,
                    SelectInstr::new(
                        condition,
                        Type::Int(IntType::I32),
                        val1,
                        val2,
                    ),
                )?;
            }
            Operator::Drop => {
                self.stack
                    .pop()
                    .expect("drop: emulation stack is unexpectedly empty");
            }
            Operator::Nop => (),
            _unsupported => return Err(IrError::UnsupportedOperator),
        }
        Ok(())
    }

    /// Pushes another Runwell IR instruction.
    ///
    /// Returns its associated value.
    fn push_instruction<I>(
        &mut self,
        _resource: &ModuleResource,
        instr: I,
    ) -> Result<Value, IrError>
    where
        I: Into<Instruction>,
    {
        // let mut block = self.blocks.current_block;
        // let block_instr = (block, instr);
        // match self.instr_to_value.get(&block_instr) {
        //     Some(value) => {

        //     }
        //     None => {

        //     }
        // }
        let value = self.value_gen.next();
        Ok(value)
    }
}

/// An entry in the value numbering table.
#[derive(Debug)]
pub struct ValueEntry {
    value: Value,
    instr: Instruction,
}
