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

mod operator;

use super::{instr::Instruction, BasicBlockId, Type, Value, ValueGen};
use crate::{
    builder::ModuleResource,
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

pub struct FunctionTranslator<'a, 'b> {
    resource: &'a ModuleResource,
    ops: OperatorsIter<'b>,
    blocks: BasicBlocks,
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
            blocks: BasicBlocks::default(),
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
    /// Mapping from instruction to value entry.
    ///
    /// Used to deduplicate instructions and associate them with a unique value.
    instr_to_entry: HashMap<Instruction, ValueEntryId>,
    /// All value entries.
    value_entries: Vec<ValueEntry>,
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
            instr_to_entry: HashMap::new(),
            value_entries: Vec::new(),
        }
    }
}

define_id_type! {
    /// Unique index used to access the value entries.
    pub struct ValueEntryId;
}

#[derive(Debug)]
pub struct ValueEntry {
    value: Value,
    instr: Instruction,
}
