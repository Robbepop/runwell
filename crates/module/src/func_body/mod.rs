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
mod incomplete_phi;
mod instruction;
mod variable;

pub use self::{
    builder::{
        FunctionBuilder,
        FunctionBuilderContext,
        FunctionBuilderState,
        ValueAssoc,
    },
    error::{FunctionBuilderError, VariableAccess},
    instruction::{Instr, InstructionBuilder},
    variable::{Variable, VariableTranslator},
};
use crate::module::Indent;
use core::fmt;
use entity::{
    ComponentVec,
    DefaultComponentMap,
    DefaultComponentVec,
    EntityArena,
    PhantomEntityArena,
    RawIdx,
};
use ir::{
    instr::Instruction,
    primitive::{Block, BlockEntity, Type, Value, ValueEntity},
};
use smallvec::SmallVec;

/// A virtual, verified Runwell IR function.
#[derive(Debug)]
pub struct FunctionBody {
    /// Arena for all block entities.
    blocks: PhantomEntityArena<BlockEntity>,
    /// Arena for all SSA value entities.
    values: PhantomEntityArena<ValueEntity>,
    /// Arena for all IR instructions.
    instrs: EntityArena<Instruction>,
    /// Block instructions.
    ///
    /// # Note
    ///
    /// Also contains all the phi instructions at the block start.
    block_instrs: DefaultComponentVec<Block, SmallVec<[Instr; 4]>>,
    /// Optional associated values for instructions.
    ///
    /// Not all instructions can be associated with an SSA value.
    /// For example `store` is not in pure SSA form and therefore
    /// has no SSA value association.
    instr_values: DefaultComponentMap<Instr, SmallVec<[Option<Value>; 4]>>,
    /// Types for all values.
    value_type: ComponentVec<Value, Type>,
    /// The association of the SSA value.
    ///
    /// Every SSA value has an association to either an IR instruction
    /// or to an input parameter of the IR function under construction.
    value_assoc: ComponentVec<Value, ValueAssoc>,
}

impl FunctionBody {
    /// Returns the entry block of the function.
    pub fn entry_block(&self) -> Block {
        Block::from_raw(RawIdx::from_u32(0))
    }

    /// Returns the maximum SSA value used by the function.
    pub fn max_value(&self) -> Value {
        self.values
            .indices()
            .last()
            .unwrap_or_else(|| Value::from_raw(RawIdx::from_u32(0)))
    }

    /// Returns the slice over the output values of the instruction.
    fn instr_values(&self, instr: Instr) -> &[Option<Value>] {
        self.instr_values[instr].as_slice()
    }

    /// Returns the nth instruction of the block and its assoc value if any.
    pub fn instruction_and_value(
        &self,
        block: Block,
        n: usize,
    ) -> Option<(&[Option<Value>], &Instruction)> {
        let instr = self.block_instrs[block].get(n).copied()?;
        let instruction = &self.instrs[instr];
        let instr_values = self.instr_values(instr);
        Some((instr_values, instruction))
    }

    /// Display the function body with the given indentation.
    ///
    /// # Note
    ///
    /// Indentation is important to properly indent the printed function body
    /// in case the output is part of an entire function with signature.
    pub(crate) fn display_with_indent(
        &self,
        f: &mut fmt::Formatter<'_>,
        ident: Indent,
    ) -> fmt::Result {
        let block_ident = ident;
        let instr_ident = ident + Indent::single();
        let mut passed_entry = false;
        for block in self.blocks.indices() {
            if !passed_entry {
                passed_entry = true;
                writeln!(f, "{}block {{", block_ident)?;
            } else {
                writeln!(f, "{}block {} {{", block_ident, block)?;
            }
            for &instr in &self.block_instrs[block] {
                let instr_data = &self.instrs[instr];
                let instr_values = self.instr_values(instr);
                let instr_values_tuples = instr_values.len() >= 2;
                write!(f, "{}", instr_ident)?;
                match instr_values.split_first() {
                    None => {
                        writeln!(f, "{}", instr_data)?;
                    }
                    Some((&first, rest)) => {
                        write!(f, "let ")?;
                        if instr_values_tuples {
                            write!(f, "(")?;
                        }
                        if let Some(first) = first {
                            let value_type = self.value_type[first];
                            write!(f, "{}: {}", first, value_type)?;
                        } else {
                            write!(f, "_")?;
                        }
                        for &value in rest {
                            if let Some(value) = value {
                                let value_type = self.value_type[value];
                                write!(f, ", {}: {}", value, value_type)?;
                            } else {
                                write!(f, ", _")?;
                            }
                        }
                        if instr_values_tuples {
                            write!(f, ")")?;
                        }
                        writeln!(f, " = {}", instr_data)?;
                    }
                }
            }
            writeln!(f, "{}}}", block_ident)?;
        }
        Ok(())
    }
}

impl fmt::Display for FunctionBody {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.display_with_indent(f, Default::default())
    }
}
