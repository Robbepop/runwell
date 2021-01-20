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
    instruction::{FunctionInstrBuilder, Instr},
    variable::Variable,
};
use crate::{
    entity::{ComponentMap, ComponentVec, EntityArena, RawIdx},
    ir::{
        instruction::Instruction,
        primitive::{Block, BlockEntity, Type, Value, ValueEntity},
        IrError,
    },
};
use core::marker::PhantomData;
use std::collections::HashSet;

#[derive(Debug)]
pub struct Function {}

impl Function {
    /// Creates a function builder to incrementally construct the function.
    pub fn build() -> FunctionBuilder<state::Inputs> {
        FunctionBuilder {
            ctx: Default::default(),
            state: Default::default(),
        }
    }
}

/// Incrementally guides the construction process to build a Runwell IR function.
#[derive(Debug, Default)]
pub struct FunctionBuilder<S> {
    pub(super) ctx: FunctionBuilderContext,
    state: PhantomData<fn() -> S>,
}

/// The context that is built during IR function construction.
#[derive(Debug)]
pub struct FunctionBuilderContext {
    /// Arena for all block entities.
    blocks: EntityArena<BlockEntity>,
    /// Arena for all SSA value entities.
    values: EntityArena<ValueEntity>,
    /// Arena for all IR instructions.
    instrs: EntityArena<Instruction>,
    /// Block predecessors.
    block_preds: ComponentVec<Block, HashSet<Block>>,
    /// Is `true` if block is sealed.
    ///
    /// A sealed block knows all its predecessors.
    block_sealed: ComponentVec<Block, bool>,
    /// Is `true` if block is filled.
    ///
    /// A filled block knows all its instructions and has
    /// a terminal instruction as its last instruction.
    block_filled: ComponentVec<Block, bool>,
    /// Block instructions.
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
    /// The current basic block that is being operated on.
    current: Block,
}

impl Default for FunctionBuilderContext {
    fn default() -> Self {
        Self {
            blocks: Default::default(),
            values: Default::default(),
            instrs: Default::default(),
            block_preds: Default::default(),
            block_sealed: Default::default(),
            block_filled: Default::default(),
            block_instrs: Default::default(),
            instr_value: Default::default(),
            value_type: Default::default(),
            value_assoc: Default::default(),
            current: Block::from_raw(RawIdx::from_u32(0)),
        }
    }
}

/// The association of the SSA value.
///
/// Every SSA value has an association to either an IR instruction
/// or to an input parameter of the IR function under construction.
#[derive(Debug)]
pub enum ValueAssoc {
    Input(u32),
    Instr(Instr),
}

pub(crate) mod state {
    /// State to declare the inputs to the function.
    #[derive(Debug, Copy, Clone, PartialEq, Eq)]
    pub enum Inputs {}
    /// State to declare the output of the function.
    #[derive(Debug, Copy, Clone, PartialEq, Eq)]
    pub enum Outputs {}
    /// State to declare all the function local variables of the function.
    #[derive(Debug, Copy, Clone, PartialEq, Eq)]
    pub enum DeclareVariables {}
    /// State to declare all the function local variables of the function.
    #[derive(Debug, Copy, Clone, PartialEq, Eq)]
    pub enum Body {}

    /// Type states for the function builder.
    pub trait State {}

    impl State for Inputs {}
    impl State for Outputs {}
    impl State for DeclareVariables {}
    impl State for Body {}
}

impl FunctionBuilder<state::Inputs> {
    /// Declares the inputs parameters and their types for the function.
    pub fn with_inputs(
        self,
        _inputs: &[Type],
    ) -> Result<FunctionBuilder<state::Outputs>, IrError> {
        todo!()
    }
}

impl FunctionBuilder<state::Outputs> {
    /// Declares the output types of the function.
    ///
    /// # Note
    ///
    /// The function is required to return the same amount and type as declared here.
    pub fn with_outputs(
        self,
        _outputs: &[Type],
    ) -> Result<FunctionBuilder<state::DeclareVariables>, IrError> {
        todo!()
    }
}

impl FunctionBuilder<state::DeclareVariables> {
    /// Declares all function local variables that the function is going to require for execution.
    ///
    /// # Note
    ///
    /// This includes variables that are artifacts of translation from the original source
    /// language to whatever input source is fed into Runwell IR.
    pub fn declare_variables(
        self,
        _amount: u32,
        _ty: Type,
    ) -> Result<Self, IrError> {
        todo!()
    }

    /// Start defining the body of the function with its basic blocks and instructions.
    pub fn body(self) -> FunctionBuilder<state::Body> {
        todo!()
    }
}

impl FunctionBuilder<state::Body> {
    /// Creates a new basic block for the function and returns a reference to it.
    ///
    /// # Note
    ///
    /// After this operation the current block will reference the new basic block.
    pub fn create_block(&mut self) -> Block {
        todo!()
    }

    /// Returns a reference to the current basic block if any.
    ///
    /// # Errors
    ///
    /// If no basic blocks exist.
    pub fn current_block(&self) -> Result<Block, IrError> {
        todo!()
    }

    /// Switches the current block to the given basic block.
    ///
    /// # Errors
    ///
    /// If the basic block does not exist in this function.
    pub fn switch_to_block(&mut self, _block: Block) -> Result<(), IrError> {
        todo!()
    }

    /// Seals the current basic block.
    ///
    /// A sealed basic block knows all of its predecessors.
    ///
    /// # Errors
    ///
    /// If the current basic block has already been sealed.
    pub fn seal_block(&mut self) -> Result<(), IrError> {
        todo!()
    }

    /// Returns an instruction builder to appends instructions to the current basic block.
    ///
    /// # Errors
    ///
    /// If the current block is already filled.
    pub fn ins(&mut self) -> Result<FunctionInstrBuilder, IrError> {
        todo!()
    }

    /// Assignes the value to the variable for the current basic block.
    ///
    /// # Errors
    ///
    /// - If the variable has not beed declared.
    /// - If the type of the assigned value does not match the variable's type declaration.
    pub fn write_var(
        &mut self,
        _var: Variable,
        _value: Value,
    ) -> Result<(), IrError> {
        todo!()
    }

    /// Reads the last assigned value of the variable within the scope of the current basic block.
    ///
    /// # Errors
    ///
    /// - If the variable has not beed declared.
    /// - If the variable has not been assigned before for the scope of the current basic block.
    pub fn read_var(&self, _var: Variable) -> Result<Value, IrError> {
        todo!()
    }

    /// Finalizes construction of the built function.
    ///
    /// Returns the built function.
    ///
    /// # Errors
    ///
    /// If not all basic blocks in the function are sealed and filled.
    pub fn finalize(self) -> Result<Function, IrError> {
        todo!()
    }
}
