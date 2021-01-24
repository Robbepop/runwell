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
        instr::PhiInstr,
        instruction::Instruction,
        primitive::{Block, BlockEntity, Type, Value, ValueEntity},
        IrError,
    },
};
use core::{fmt, marker::PhantomData};
use std::collections::HashSet;

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
    /// The types of the output values of the constructed function.
    output_types: Vec<Type>,
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
    pub blocks: EntityArena<BlockEntity>,
    /// Arena for all SSA value entities.
    pub values: EntityArena<ValueEntity>,
    /// Arena for all IR instructions.
    pub instrs: EntityArena<Instruction>,
    /// Block predecessors.
    ///
    /// Only filled blocks may have successors, predecessors are always filled.
    pub block_preds: ComponentVec<Block, HashSet<Block>>,
    /// The phi functions of every basic block.
    ///
    /// Every basic block can have up to one phi instruction per variable in use.
    pub block_phis: ComponentMap<Block, ComponentMap<Variable, Instr>>,
    /// Is `true` if block is sealed.
    ///
    /// A sealed block knows all its predecessors.
    pub block_sealed: ComponentVec<Block, bool>,
    /// Is `true` if block is filled.
    ///
    /// A filled block knows all its instructions and has
    /// a terminal instruction as its last instruction.
    pub block_filled: ComponentVec<Block, bool>,
    /// Block instructions.
    pub block_instrs: ComponentVec<Block, Vec<Instr>>,
    /// Marker to indicate if a block has already been visited
    /// when querying the latest value of a variable upon reading it.
    pub block_marker: ComponentMap<Block, ()>,
    /// Required information to remove phi from its block if it becomes trivial.
    pub phi_block: ComponentMap<Value, Block>,
    /// Required information to remove phi from its block if it becomes trivial.
    pub phi_var: ComponentMap<Value, Variable>,
    /// Incomplete phi nodes for all blocks.
    ///
    /// This stores a mapping from each variable in a basic block to
    /// some value that must be associated to the phi instruction in
    /// the same block representing bindings for the variable.
    pub incomplete_phis: ComponentMap<Block, ComponentMap<Variable, Value>>,
    /// Optional associated values for instructions.
    ///
    /// Not all instructions can be associated with an SSA value.
    /// For example `store` is not in pure SSA form and therefore
    /// has no SSA value association.
    pub instr_value: ComponentMap<Instr, Value>,
    /// Types for all values.
    pub value_type: ComponentVec<Value, Type>,
    /// The association of the SSA value.
    ///
    /// Every SSA value has an association to either an IR instruction
    /// or to an input parameter of the IR function under construction.
    pub value_assoc: ComponentVec<Value, ValueAssoc>,
    /// Stores all users of all values.
    ///
    /// This information is required to replace an unnecessary phi
    /// phi instruction with its single operand. Users of the unnecessary
    /// phi instruction are updated accordingly and phi instruction
    /// users are checked for triviality.
    ///
    /// Also this information can be used for optimizations when replacing
    /// one instruction with another.
    pub value_users: ComponentMap<Value, HashSet<Instr>>,
    /// The current basic block that is being operated on.
    pub current: Block,
    /// The variable translator.
    ///
    /// This translates local variables from the source language that
    /// are not in SSA form into SSA form values.
    pub vars: VariableTranslator,
    /// The types of the output values of the constructed function.
    pub output_types: Vec<Type>,
}

impl Default for FunctionBuilderContext {
    fn default() -> Self {
        Self {
            blocks: Default::default(),
            values: Default::default(),
            instrs: Default::default(),
            block_preds: Default::default(),
            block_phis: Default::default(),
            block_sealed: Default::default(),
            block_filled: Default::default(),
            block_instrs: Default::default(),
            block_marker: Default::default(),
            phi_block: Default::default(),
            phi_var: Default::default(),
            incomplete_phis: Default::default(),
            instr_value: Default::default(),
            value_type: Default::default(),
            value_assoc: Default::default(),
            value_users: Default::default(),
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
    /// Creates the entry block of the constructed function.
    fn create_entry_block(&mut self) -> Block {
        let entry_block = self.ctx.blocks.alloc(Default::default());
        self.ctx.block_preds.insert(entry_block, Default::default());
        self.ctx.block_sealed.insert(entry_block, true);
        self.ctx.block_filled.insert(entry_block, false);
        self.ctx
            .block_instrs
            .insert(entry_block, Default::default());
        self.ctx.block_phis.insert(entry_block, Default::default());
        self.ctx
            .incomplete_phis
            .insert(entry_block, Default::default());
        self.ctx.current = entry_block;
        entry_block
    }

    /// Declares the inputs parameters and their types for the function.
    pub fn with_inputs(
        mut self,
        inputs: &[Type],
    ) -> Result<FunctionBuilder<state::Outputs>, IrError> {
        let entry_block = self.create_entry_block();
        for (n, input_type) in inputs.iter().copied().enumerate() {
            let val = self.ctx.values.alloc(Default::default());
            self.ctx.value_type.insert(val, input_type);
            self.ctx
                .value_assoc
                .insert(val, ValueAssoc::Input(n as u32));
            self.ctx.value_users.insert(val, Default::default());
            self.ctx.vars.declare_vars(1, input_type)?;
            let input_var = Variable::from_raw(RawIdx::from_u32(n as u32));
            self.ctx
                .vars
                .write_var(input_var, val, entry_block, || input_type)?;
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
    pub fn body(self) -> FunctionBuilder<state::Body> {
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
        self.ctx.block_preds.insert(new_block, Default::default());
        self.ctx.block_sealed.insert(new_block, false);
        self.ctx.block_filled.insert(new_block, false);
        self.ctx.block_instrs.insert(new_block, Default::default());
        self.ctx.block_phis.insert(new_block, Default::default());
        self.ctx
            .incomplete_phis
            .insert(new_block, Default::default());
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
        // Popping incomplete phis by inserting a new empty component map.
        let incomplete_phis = self
            .ctx
            .incomplete_phis
            .insert(block, Default::default())
            .expect("encountered missing incomplete phis component");
        for (variable, &value) in incomplete_phis.iter() {
            self.add_phi_operands(block, variable, value)?;
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
        let already_filled = self.ctx.block_filled[block];
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
        let FunctionBuilderContext {
            vars, value_type, ..
        } = &mut self.ctx;
        vars.write_var(var, value, block, || value_type[value])?;
        Ok(())
    }

    /// Creates a new phi instruction.
    fn create_phi_instruction(
        &mut self,
        var: Variable,
        var_type: Type,
        block: Block,
    ) -> Result<Value, IrError> {
        let instr = self.ctx.instrs.alloc(PhiInstr::default().into());
        let value = self.ctx.values.alloc(ValueEntity);
        self.ctx.value_assoc.insert(value, ValueAssoc::Instr(instr));
        self.ctx.value_type.insert(value, var_type);
        self.ctx.value_users.insert(value, Default::default());
        self.ctx.phi_var.insert(value, var);
        self.ctx.phi_block.insert(value, block);
        self.ctx.block_phis[block].insert(var, instr);
        self.ctx.vars.write_var(var, value, block, || var_type)?;
        self.ctx.instr_value.insert(instr, value);
        return Ok(value)
    }

    /// Reads the given variable starting from the given block.
    fn read_var_in_block(
        &mut self,
        var: Variable,
        block: Block,
    ) -> Result<Value, IrError> {
        let var_info = self.ctx.vars.get(var)?;
        if let Some(value) = var_info.definitions().for_block(block) {
            // Local Value Numbering
            return Ok(value)
        }
        // Global Value Numbering
        let var_type = var_info.ty();
        if !self.ctx.block_sealed[block] {
            // Incomplete phi node required.
            let value = self.create_phi_instruction(var, var_type, block)?;
            self.ctx.vars.write_var(var, value, block, || var_type)?;
            self.ctx.incomplete_phis[block].insert(var, value);
            return Ok(value)
        }
        let value = if self.ctx.block_preds[block].len() == 1 {
            // Optimize the common case of one predecessor: No phi needed.
            let pred = self.ctx.block_preds[block]
                .iter()
                .next()
                .copied()
                .expect("missing expected predecessor for basic block");
            self.read_var_in_block(var, pred)?
        } else {
            // Break potential cycles with operandless phi instruction.
            let value = self.create_phi_instruction(var, var_type, block)?;
            value
        };
        self.ctx.vars.write_var(var, value, block, || var_type)?;
        Ok(value)
    }

    /// Add operands to the phi instruction.
    ///
    /// Note that this procedure can only run once a basic block has been sealed.
    fn add_phi_operands(
        &mut self,
        block: Block,
        var: Variable,
        phi: Value,
    ) -> Result<Value, IrError> {
        let preds = self.ctx.block_preds[block]
            .iter()
            .copied()
            .collect::<Vec<_>>();
        let instr = match self.ctx.value_assoc[phi] {
            ValueAssoc::Instr(instr) => instr,
            _ => panic!("unexpected non-instruction value"),
        };
        for pred in preds {
            let value = self.read_var_in_block(var, pred)?;
            let phi = match &mut self.ctx.instrs[instr] {
                Instruction::Phi(phi) => phi,
                _ => panic!("unexpected non-phi instruction"),
            };
            phi.append_operand(pred, value);
        }
        self.try_remove_trivial_phi(phi)
    }

    /// Checks if the given phi instruction is trivial replacing it if true.
    ///
    /// Replacement is a recursive operation that replaces all uses of the
    /// phi instruction with its only non-phi operand. During this process
    /// other phi instruction users might become trivial and cascade the effect.
    fn try_remove_trivial_phi(
        &mut self,
        phi_value: Value,
    ) -> Result<Value, IrError> {
        let phi_instr = match self.ctx.value_assoc[phi_value] {
            ValueAssoc::Instr(instr) => instr,
            _ => panic!("unexpected non-instruction value"),
        };
        let instruction = match &mut self.ctx.instrs[phi_instr] {
            Instruction::Phi(phi) => phi,
            _ => panic!("unexpected non-phi instruction"),
        };
        let mut same: Option<Value> = None;
        for (_block, op) in instruction.iter() {
            if Some(op) == same || op == phi_value {
                // Unique value or self reference.
                continue
            }
            if same.is_some() {
                // The phi merges at least two values: not trivial
                return Ok(phi_value)
            }
            same = Some(op);
        }
        if same.is_none() {
            // The phi is unreachable or in the start block.
            // The paper replaces it with an undefined instruction.
            return Err(IrError::FunctionBuilder(
                FunctionBuilderError::UnreachablePhi { value: phi_value },
            ))
        }
        let same = same.expect("just asserted that same is Some");
        // Phi was determined to be trivial and can be removed.
        // Insert a default into its phi users to replace the current users with an empty set.
        // Additionally this allows us to iterate over users without borrow checker issues.
        //
        // Remove phi from its own users in case it was using itself.
        self.ctx.value_users[phi_value].remove(&phi_instr);
        let users = self
            .ctx
            .value_users
            .insert(phi_value, Default::default())
            .unwrap_or_default();
        let phi_block = self.ctx.phi_block[phi_value];
        let phi_var = self.ctx.phi_var[phi_value];
        self.ctx.block_phis[phi_block].remove(phi_var);
        for user in users {
            let user_instr = &mut self.ctx.instrs[user];
            user_instr.replace_value(|value| {
                if *value == phi_value {
                    *value = same;
                    return true
                }
                false
            });
            if user_instr.is_phi() {
                let phi_value = self.ctx.instr_value[user];
                self.try_remove_trivial_phi(phi_value)?;
            }
        }
        Ok(same)
    }

    /// Reads the last assigned value of the variable within the scope of the current basic block.
    ///
    /// # Errors
    ///
    /// - If the variable has not beed declared.
    pub fn read_var(&mut self, var: Variable) -> Result<Value, IrError> {
        let current = self.current_block()?;
        self.read_var_in_block(var, current)
    }

    /// Finalizes construction of the built function.
    ///
    /// Returns the built function.
    ///
    /// # Errors
    ///
    /// If not all basic blocks in the function are sealed and filled.
    pub fn finalize(mut self) -> Result<Function, IrError> {
        let unsealed_blocks = self
            .ctx
            .block_sealed
            .iter()
            .filter_map(|(idx, &sealed)| if !sealed { Some(idx) } else { None })
            .collect::<Vec<_>>();
        if !unsealed_blocks.is_empty() {
            return Err(IrError::FunctionBuilder(
                FunctionBuilderError::UnsealedBlocksUponFinalize {
                    unsealed: unsealed_blocks,
                },
            ))
        }
        let unfilled_blocks = self
            .ctx
            .block_filled
            .iter()
            .filter_map(|(idx, &filled)| if !filled { Some(idx) } else { None })
            .collect::<Vec<_>>();
        if !unfilled_blocks.is_empty() {
            return Err(IrError::FunctionBuilder(
                FunctionBuilderError::UnfilledBlocksUponFinalize {
                    unfilled: unfilled_blocks,
                },
            ))
        }
        self.ctx.blocks.shrink_to_fit();
        self.ctx.values.shrink_to_fit();
        self.ctx.instrs.shrink_to_fit();
        self.ctx.block_instrs.shrink_to_fit();
        self.ctx.instr_value.shrink_to_fit();
        self.ctx.value_type.shrink_to_fit();
        self.ctx.value_assoc.shrink_to_fit();
        self.ctx.output_types.shrink_to_fit();
        let mut block_instrs = ComponentVec::default();
        for (block, var_phis) in self.ctx.block_phis.iter() {
            // First add all phi instructions of a basic block and then
            // append the rest of the instructions of the same basic block.
            let mut instructions = var_phis
                .iter()
                .map(|(_var, &phi_instr)| phi_instr)
                .collect::<Vec<_>>();
            instructions.extend_from_slice(&self.ctx.block_instrs[block]);
            block_instrs.insert(block, instructions);
        }
        block_instrs.shrink_to_fit();
        Ok(Function {
            blocks: self.ctx.blocks,
            values: self.ctx.values,
            instrs: self.ctx.instrs,
            block_instrs,
            instr_value: self.ctx.instr_value,
            value_type: self.ctx.value_type,
            value_assoc: self.ctx.value_assoc,
            output_types: self.ctx.output_types,
        })
    }
}
