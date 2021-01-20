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

//! From the paper "Simple and Efficient SSA Construction" by Buchwald et. al.:
//!
//! We call a basic block sealed if no further predecessors will be added to the block.
//! As only filled blocks may have successors, predecessors are always filled.
//! Note that a sealed block is not necessarily filled. Intuitively,
//! a filled block contains all its instructions and can provide variable definitions for its successors.
//! Conversely, a sealed block may look up variable definitions in
//! its predecessors as all predecessors are known.

use super::{
    instruction::{FunctionInstrBuilder, Instr},
    variable::Variable,
    FunctionBuilderError,
    VariableTranslator,
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
    ///
    /// Only filled blocks may have successors, predecessors are always filled.
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
    /// The variable translator.
    ///
    /// This translates local variables from the source language that
    /// are not in SSA form into SSA form values.
    vars: VariableTranslator,
    /// The types of the output values of the constructed function.
    output_types: Vec<Type>,
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
            vars: Default::default(),
            output_types: Default::default(),
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

/// Type states for the function builder.
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
        mut self,
        inputs: &[Type],
    ) -> Result<FunctionBuilder<state::Outputs>, IrError> {
        for (n, input_type) in inputs.iter().copied().enumerate() {
            let val = self.ctx.values.alloc(Default::default());
            let prev_type = self.ctx.value_type.insert(val, input_type);
            debug_assert!(prev_type.is_none());
            let prev_assoc = self
                .ctx
                .value_assoc
                .insert(val, ValueAssoc::Input(n as u32));
            debug_assert!(prev_assoc.is_none());
        }
        Ok(FunctionBuilder {
            ctx: self.ctx,
            state: Default::default(),
        })
    }
}

impl FunctionBuilder<state::Outputs> {
    /// Declares the output types of the function.
    ///
    /// # Note
    ///
    /// The function is required to return the same amount and type as declared here.
    pub fn with_outputs(
        mut self,
        outputs: &[Type],
    ) -> Result<FunctionBuilder<state::DeclareVariables>, IrError> {
        self.ctx.output_types.extend_from_slice(outputs);
        Ok(FunctionBuilder {
            ctx: self.ctx,
            state: Default::default(),
        })
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
        mut self,
        amount: u32,
        ty: Type,
    ) -> Result<Self, IrError> {
        self.ctx.vars.declare_vars(amount, ty)?;
        Ok(FunctionBuilder {
            ctx: self.ctx,
            state: Default::default(),
        })
    }

    /// Start defining the body of the function with its basic blocks and instructions.
    pub fn body(mut self) -> FunctionBuilder<state::Body> {
        let entry_block = self.ctx.blocks.alloc(Default::default());
        self.ctx.block_preds.insert(entry_block, Default::default());
        self.ctx.block_sealed.insert(entry_block, true);
        self.ctx.block_filled.insert(entry_block, false);
        self.ctx
            .block_instrs
            .insert(entry_block, Default::default());
        self.ctx.current = entry_block;
        FunctionBuilder {
            ctx: self.ctx,
            state: Default::default(),
        }
    }
}

impl FunctionBuilder<state::Body> {
    /// Creates a new basic block for the function and returns a reference to it.
    ///
    /// # Note
    ///
    /// After this operation the current block will reference the new basic block.
    pub fn create_block(&mut self) -> Block {
        let new_block = self.ctx.blocks.alloc(Default::default());
        let prev_preds =
            self.ctx.block_preds.insert(new_block, Default::default());
        let prev_sealed = self.ctx.block_sealed.insert(new_block, false);
        let prev_filled = self.ctx.block_filled.insert(new_block, false);
        let prev_instrs =
            self.ctx.block_instrs.insert(new_block, Default::default());
        debug_assert!(prev_preds.is_none());
        debug_assert!(prev_sealed.is_none());
        debug_assert!(prev_filled.is_none());
        debug_assert!(prev_instrs.is_none());
        self.ctx.current = new_block;
        new_block
    }

    /// Returns a reference to the current basic block if any.
    ///
    /// # Errors
    ///
    /// If no basic blocks exist.
    pub fn current_block(&self) -> Result<Block, IrError> {
        Ok(self.ctx.current)
    }

    /// Switches the current block to the given basic block.
    ///
    /// # Errors
    ///
    /// If the basic block does not exist in this function.
    pub fn switch_to_block(&mut self, block: Block) -> Result<(), IrError> {
        if !self.ctx.blocks.contains_key(block) {
            return Err(IrError::FunctionBuilder(
                FunctionBuilderError::InvalidBasicBlock { block },
            ))
        }
        self.ctx.current = block;
        Ok(())
    }

    /// Seals the current basic block.
    ///
    /// A sealed basic block knows all of its predecessors.
    ///
    /// # Errors
    ///
    /// If the current basic block has already been sealed.
    pub fn seal_block(&mut self) -> Result<(), IrError> {
        let block = self.current_block()?;
        let already_sealed = self
            .ctx
            .block_sealed
            .insert(block, true)
            .expect("encountered invalid current basic block");
        if already_sealed {
            return Err(IrError::FunctionBuilder(
                FunctionBuilderError::BasicBlockIsAlreadySealed { block },
            ))
        }
        Ok(())
    }

    /// Returns an instruction builder to appends instructions to the current basic block.
    ///
    /// # Errors
    ///
    /// If the current block is already filled.
    pub fn ins(&mut self) -> Result<FunctionInstrBuilder, IrError> {
        let block = self.current_block()?;
        let already_filled = self.ctx.block_sealed[block];
        if already_filled {
            return Err(IrError::FunctionBuilder(
                FunctionBuilderError::BasicBlockIsAlreadyFilled { block },
            ))
        }
        Ok(FunctionInstrBuilder::new(self))
    }

    /// Assignes the value to the variable for the current basic block.
    ///
    /// # Errors
    ///
    /// - If the variable has not beed declared.
    /// - If the type of the assigned value does not match the variable's type declaration.
    pub fn write_var(
        &mut self,
        var: Variable,
        value: Value,
    ) -> Result<(), IrError> {
        let block = self.current_block()?;
        let FunctionBuilderContext { vars, value_type, ..} = &mut self.ctx;
        vars
            .write_var(var, value, block, || value_type[value])?;
        Ok(())
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
