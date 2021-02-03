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

mod builder;
mod error;
mod instruction;
mod variable;

use self::builder::state;
pub use self::{
    builder::{FunctionBuilder, FunctionBuilderContext, ValueAssoc},
    error::{FunctionBuilderError, VariableAccess},
    instruction::{Instr, InstructionBuilder},
    variable::{Variable, VariableTranslator},
};
use core::fmt;
use entity::{ComponentMap, ComponentVec, EntityArena, RawIdx};
use ir::{
    instr::Instruction,
    primitive::{Block, BlockEntity, Type, Value, ValueEntity},
};

/// A virtual, verified Runwell IR function.
#[derive(Debug)]
pub struct Function {
    /// Arena for all block entities.
    blocks: EntityArena<BlockEntity>,
    /// Arena for all SSA value entities.
    values: EntityArena<ValueEntity>,
    /// Arena for all IR instructions.
    instrs: EntityArena<Instruction>,
    /// Block instructions.
    ///
    /// # Note
    ///
    /// Also contains all the phi instructions at the block start.
    block_instrs: ComponentVec<Block, Vec<Instr>>,
    /// Optional associated values for instructions.
    ///
    /// Not all instructions can be associated with an SSA value.
    /// For example `store` is not in pure SSA form and therefore
    /// has no SSA value association.
    instr_value: ComponentMap<Instr, Value>,
    /// Types for all values.
    value_type: ComponentVec<Value, Type>,
    /// The association of the SSA value.
    ///
    /// Every SSA value has an association to either an IR instruction
    /// or to an input parameter of the IR function under construction.
    value_assoc: ComponentVec<Value, ValueAssoc>,
    /// The types of the input values of the constructed function.
    ///
    /// Used in order to check upon evaluating the function.
    input_types: Vec<Type>,
    /// The types of the output values of the constructed function.
    output_types: Vec<Type>,
}

impl Function {
    /// Returns the entry block of the function.
    pub fn entry_block(&self) -> Block {
        Block::from_raw(RawIdx::from_u32(0))
    }

    /// Returns the n-th instruction of the block and its assoc value if any.
    pub fn instruction_and_value(
        &self,
        block: Block,
        n: usize,
    ) -> Option<(Option<Value>, &Instruction)> {
        let instr = self
            .block_instrs
            .get(block)
            .and_then(|instrs| instrs.get(n))
            .copied()?;
        let instruction = &self.instrs[instr];
        let instr_value = self.instr_value.get(instr).copied();
        Some((instr_value, instruction))
    }
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut inputs = self
            .value_assoc
            .iter()
            .filter_map(|(value, assoc)| {
                if let ValueAssoc::Input(idx) = *assoc {
                    Some((idx, value))
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();
        inputs.sort_by(|(lpos, _), (rpos, _)| lpos.cmp(rpos));
        write!(f, "fn (")?;
        if let Some(((_, first_input), rest_input)) = inputs.split_first() {
            let value_type = self.value_type[*first_input];
            write!(f, "{}: {}", first_input, value_type)?;
            for (_, rest_input) in rest_input {
                let value_type = self.value_type[*rest_input];
                write!(f, ", {}: {}", rest_input, value_type)?;
            }
        }
        write!(f, ")")?;
        if let Some((first_output, rest_outputs)) =
            self.output_types.split_first()
        {
            write!(f, " -> ")?;
            if !rest_outputs.is_empty() {
                write!(f, "[")?;
            }
            write!(f, "{}", first_output)?;
            for rest_output in rest_outputs {
                write!(f, ", {}", rest_output)?;
            }
            if !rest_outputs.is_empty() {
                write!(f, "]")?;
            }
        }
        writeln!(f)?;
        for block in self.blocks.indices() {
            writeln!(f, "{}:", block)?;
            for &instr in &self.block_instrs[block] {
                let instr_data = &self.instrs[instr];
                let instr_value = self.instr_value.get(instr).copied();
                match instr_value {
                    Some(value) => {
                        let value_type = self.value_type[value];
                        writeln!(
                            f,
                            "    {}: {} = {}",
                            value, value_type, instr_data
                        )?;
                    }
                    None => {
                        writeln!(f, "    {}", instr_data)?;
                    }
                }
            }
        }
        writeln!(f)?;
        Ok(())
    }
}
