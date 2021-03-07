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

//! From the paper "Simple and Efficient SSA Construction" by Buchwald and others:
//!
//! We call a basic block sealed if no further predecessors will be added to the block.
//! As only filled blocks may have successors, predecessors are always filled.
//! Note that a sealed block is not necessarily filled. Intuitively,
//! a filled block contains all its instructions and can provide variable definitions for its successors.
//! Conversely, a sealed block may look up variable definitions in
//! its predecessors as all predecessors are known.

use super::{
    incomplete_phi::IncompletePhi,
    instruction::{Instr, InstructionBuilder},
    variable::Variable,
    FunctionBody,
    FunctionBuilderError,
    VariableTranslator,
};
use crate::{Error, ModuleResources};
use core::{
    fmt::Debug,
    hash::Hash,
    mem::{replace, take},
};
use derive_more::Display;
use entity::{
    ComponentMap,
    ComponentVec,
    DefaultComponentBitVec,
    DefaultComponentMap,
    DefaultComponentVec,
    EntityArena,
    PhantomEntityArena,
    RawIdx,
};
use ir::{
    instr::{Instruction, PhiInstr},
    primitive::{Block, BlockEntity, Func, Type, Value, ValueEntity},
    VisitValuesMut,
};
use smallvec::SmallVec;
use std::collections::HashMap;

/// Type alias to Rust's `HashSet` but using `ahash` as hasher which is more efficient.
type HashSet<T> = std::collections::HashSet<T, ahash::RandomState>;

impl FunctionBody {
    /// Creates a function builder to incrementally construct the function.
    pub fn build(func: Func, res: &ModuleResources) -> FunctionBuilder {
        let mut ctx = Default::default();
        let func_type = res.get_func_type(func).unwrap_or_else(|| {
            panic!(
                "tried to build function {} that is missing from module resources",
                func
            )
        });
        FunctionBuilder::initialize_inputs(&mut ctx, func_type.inputs());
        FunctionBuilder {
            ctx,
            func,
            res,
            state: FunctionBuilderState::LocalVariables,
        }
    }
}

/// Incrementally guides the construction process to build a Runwell IR function.
#[derive(Debug)]
pub struct FunctionBuilder<'a> {
    pub(super) ctx: FunctionBuilderContext,
    pub(super) func: Func,
    pub(super) res: &'a ModuleResources,
    state: FunctionBuilderState,
}

/// The context that is built during IR function construction.
#[derive(Debug)]
pub struct FunctionBuilderContext {
    /// Arena for all block entities.
    pub blocks: PhantomEntityArena<BlockEntity>,
    /// Arena for all SSA value entities.
    pub values: PhantomEntityArena<ValueEntity>,
    /// Arena for all IR instructions.
    pub instrs: EntityArena<Instruction>,
    /// Block predecessors.
    ///
    /// Only filled blocks may have successors, predecessors are always filled.
    pub block_preds: DefaultComponentVec<Block, HashSet<Block>>,
    /// The phi functions of every basic block.
    ///
    /// Every basic block can have up to one phi instruction per variable in use.
    pub block_phis: DefaultComponentMap<Block, ComponentMap<Variable, Instr>>,
    /// Is `true` if block is sealed.
    ///
    /// A sealed block knows all its predecessors.
    pub block_sealed: DefaultComponentBitVec<Block>,
    /// Is `true` if block is filled.
    ///
    /// A filled block knows all its instructions and has
    /// a terminal instruction as its last instruction.
    pub block_filled: DefaultComponentBitVec<Block>,
    /// Block instructions.
    pub block_instrs: DefaultComponentVec<Block, SmallVec<[Instr; 4]>>,
    /// Required information to remove phi from its block if it becomes trivial.
    pub phi_block: ComponentMap<Value, Block>,
    /// Required information to remove phi from its block if it becomes trivial.
    pub phi_var: ComponentMap<Value, Variable>,
    /// Incomplete phi nodes for all blocks.
    ///
    /// This stores a mapping from each variable in a basic block to
    /// some value that must be associated to the phi instruction in
    /// the same block representing bindings for the variable.
    pub block_incomplete_phis:
        DefaultComponentMap<Block, ComponentMap<Variable, Value>>,
    /// Optional associated values for instructions.
    ///
    /// Not all instructions can be associated with an SSA value.
    /// For example `store` is not in pure SSA form and therefore
    /// has no SSA value association.
    pub instr_values: DefaultComponentMap<Instr, SmallVec<[Value; 4]>>,
    /// The incomplete phi instruction in case the value represents one.
    ///
    /// Incomplete phis are use throughout the function body construction
    /// instead of actually creating phi instructions. Phi instructions are
    /// first created upon finalization of the function body.
    ///
    /// The construction algorithm works solely on incomplete phis, even
    /// though a phi instruction might be deemed complete during function
    /// body construction.
    pub value_incomplete_phi: ComponentMap<Value, IncompletePhi>,
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
    pub value_users: DefaultComponentMap<Value, HashSet<Instr>>,
    /// The current basic block that is being operated on.
    pub current: Block,
    /// The variable translator.
    ///
    /// This translates local variables from the source language that
    /// are not in SSA form into SSA form values.
    pub vars: VariableTranslator,
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
            block_incomplete_phis: Default::default(),
            phi_block: Default::default(),
            phi_var: Default::default(),
            instr_values: Default::default(),
            value_incomplete_phi: Default::default(),
            value_type: Default::default(),
            value_assoc: Default::default(),
            value_users: Default::default(),
            current: Block::from_raw(RawIdx::from_u32(0)),
            vars: Default::default(),
        }
    }
}

/// The association of the SSA value.
///
/// Every SSA value has an association to either an IR instruction
/// or to an input parameter of the IR function under construction.
#[derive(Debug, Copy, Clone)]
pub enum ValueAssoc {
    /// The value is associated to the nth input of the function.
    Input(u32),
    /// The value is associated to the nth output of the instruction.
    Instr(Instr, u32),
}

impl ValueAssoc {
    /// Returns `true` if the value is associated to a function input parameter.
    pub fn is_input(self) -> bool {
        matches!(self, Self::Input(_))
    }
}

/// The current state of the function body construction.
#[derive(Debug, Display, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum FunctionBuilderState {
    /// Declare local variables used in the function body.
    #[display(fmt = "local variables")]
    LocalVariables = 1,
    /// Define the function body.
    #[display(fmt = "function body")]
    Body = 2,
}

impl<'a> FunctionBuilder<'a> {
    /// Ensures that the function body construction happens in the correct order.
    ///
    /// Updates the current function body construction state if in order.
    fn ensure_construction_in_order(
        &mut self,
        next: FunctionBuilderState,
    ) -> Result<(), FunctionBuilderError> {
        let current = self.state;
        if current > next {
            return Err(FunctionBuilderError::IncorrectOrder {
                last_state: current,
                fail_state: next,
            })
        }
        self.state = next;
        Ok(())
    }

    /// Creates the entry block of the constructed function.
    fn create_entry_block(ctx: &mut FunctionBuilderContext) -> Block {
        if !ctx.blocks.is_empty() {
            // Do not create an entry block if there is already one.
            return ctx.current
        }
        let entry_block = ctx.blocks.alloc_some(1);
        ctx.block_sealed.set(entry_block, true);
        ctx.current = entry_block;
        entry_block
    }

    /// Initializes the input parameters and their types for the function.
    pub fn initialize_inputs(
        ctx: &mut FunctionBuilderContext,
        inputs: &[Type],
    ) {
        let entry_block = Self::create_entry_block(ctx);
        for (n, input_type) in inputs.iter().copied().enumerate() {
            let val = ctx.values.alloc_some(1);
            ctx.value_type.insert(val, input_type);
            ctx.value_assoc.insert(val, ValueAssoc::Input(n as u32));
            ctx.vars.declare_vars(1, input_type).expect(
                "unexpected failure to declare function input variable",
            );
            let input_var = Variable::from_raw(RawIdx::from_u32(n as u32));
            ctx.vars
                .write_var(input_var, val, entry_block, input_type)
                .expect("unexpected failure to write just declared variable");
        }
    }

    /// Declares all function local variables that the function is going to require for execution.
    ///
    /// # Note
    ///
    /// This includes variables that are artifacts of translation from the original source
    /// language to whatever input source is fed into Runwell IR.
    pub fn declare_variables(
        &mut self,
        amount: u32,
        ty: Type,
    ) -> Result<(), Error> {
        self.ensure_construction_in_order(
            FunctionBuilderState::LocalVariables,
        )?;
        self.ctx.vars.declare_vars(amount, ty)?;
        Ok(())
    }

    /// Start defining the body of the function with its basic blocks and instructions.
    pub fn body(&mut self) -> Result<(), Error> {
        self.ensure_construction_in_order(FunctionBuilderState::Body)?;
        Ok(())
    }

    /// Creates a new basic block for the function and returns a reference to it.
    pub fn create_block(&mut self) -> Result<Block, Error> {
        self.ensure_construction_in_order(FunctionBuilderState::Body)?;
        let new_block = self.ctx.blocks.alloc_some(1);
        Ok(new_block)
    }

    /// Returns a reference to the current basic block if any.
    ///
    /// # Errors
    ///
    /// If no basic blocks exist.
    pub fn current_block(&mut self) -> Result<Block, Error> {
        self.ensure_construction_in_order(FunctionBuilderState::Body)?;
        Ok(self.ctx.current)
    }

    /// Switches the current block to the given basic block.
    ///
    /// # Errors
    ///
    /// If the basic block does not exist in this function.
    pub fn switch_to_block(&mut self, block: Block) -> Result<(), Error> {
        self.ensure_construction_in_order(FunctionBuilderState::Body)?;
        if !self.ctx.blocks.contains_key(block) {
            return Err(FunctionBuilderError::InvalidBasicBlock { block })
                .map_err(Into::into)
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
    pub fn seal_block(&mut self, block: Block) -> Result<(), Error> {
        self.ensure_construction_in_order(FunctionBuilderState::Body)?;
        let already_sealed = self.ctx.block_sealed.replace(block, true);
        if already_sealed {
            return Err(FunctionBuilderError::BasicBlockIsAlreadySealed {
                block,
            })
            .map_err(Into::into)
        }
        // Popping incomplete phis by replacing with new empty component map.
        let incomplete_phis = take(&mut self.ctx.block_incomplete_phis[block]);
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
    pub fn ins<'b>(&'b mut self) -> Result<InstructionBuilder<'b, 'a>, Error> {
        self.ensure_construction_in_order(FunctionBuilderState::Body)?;
        let block = self.current_block()?;
        let already_filled = self.ctx.block_filled.get(block);
        if already_filled {
            return Err(FunctionBuilderError::BasicBlockIsAlreadyFilled {
                block,
            })
            .map_err(Into::into)
        }
        Ok(InstructionBuilder::new(self))
    }

    /// Assigns the value to the variable for the current basic block.
    ///
    /// # Errors
    ///
    /// - If the variable has not been declared.
    /// - If the type of the assigned value does not match the variable's type declaration.
    pub fn write_var(
        &mut self,
        var: Variable,
        value: Value,
    ) -> Result<(), Error> {
        self.ensure_construction_in_order(FunctionBuilderState::Body)?;
        let block = self.current_block()?;
        let FunctionBuilderContext {
            vars, value_type, ..
        } = &mut self.ctx;
        vars.write_var(var, value, block, value_type[value])?;
        Ok(())
    }

    /// Creates a new phi instruction.
    fn create_phi_instruction(
        &mut self,
        var: Variable,
        var_type: Type,
        block: Block,
    ) -> Result<Value, Error> {
        let instr = self.ctx.instrs.alloc(PhiInstr::default().into());
        let value = self.ctx.values.alloc_some(1);
        self.ctx
            .value_incomplete_phi
            .insert(value, Default::default());
        self.ctx
            .value_assoc
            .insert(value, ValueAssoc::Instr(instr, 0));
        self.ctx.value_type.insert(value, var_type);
        self.ctx.phi_var.insert(value, var);
        self.ctx.phi_block.insert(value, block);
        self.ctx.block_phis[block].insert(var, instr);
        self.ctx.block_incomplete_phis[block].insert(var, value);
        self.ctx.vars.write_var(var, value, block, var_type)?;
        self.ctx.instr_values[instr].push(value);
        Ok(value)
    }

    /// Reads the given variable starting from the given block.
    fn read_var_in_block(
        &mut self,
        var: Variable,
        block: Block,
    ) -> Result<Value, Error> {
        let var_info = self.ctx.vars.get(var)?;
        if let Some(value) = var_info.definitions().for_block(block) {
            // Local Value Numbering
            return Ok(value)
        }
        // Global Value Numbering
        let var_type = var_info.ty();
        if !self.ctx.block_sealed.get(block) {
            // Incomplete phi node required.
            let value = self.create_phi_instruction(var, var_type, block)?;
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
            let phi_value =
                self.create_phi_instruction(var, var_type, block)?;
            self.add_phi_operands(block, var, phi_value)?
        };
        self.ctx.vars.write_var(var, value, block, var_type)?;
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
    ) -> Result<Value, Error> {
        let preds = self.ctx.block_preds[block].clone();
        for pred in preds {
            let value = self.read_var_in_block(var, pred)?;
            let incomplete_phi = &mut self.ctx.value_incomplete_phi[phi];
            incomplete_phi.append_operand(pred, value);
            let phi_instr = self.phi_value_to_instr(phi);
            self.ctx.value_users[value].insert(phi_instr);
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
    ) -> Result<Value, Error> {
        let incomplete_phi = &self.ctx.value_incomplete_phi[phi_value];
        let equivalent = match incomplete_phi.is_trivial(phi_value)? {
            Some(equivalent) => {
                // The phi instruction is trivial and the returned value
                // is equivalent and shall replace it from now on.
                equivalent
            }
            None => {
                // The phi instruction is non-trivial, return it.
                return Ok(phi_value)
            }
        };
        // Phi was determined to be trivial and can be removed.
        // Insert a default into its phi users to replace the current users with an empty set.
        // Additionally this allows us to iterate over users without borrow checker issues.
        //
        // Remove phi from its own users in case it was using itself.
        let phi_instr = self.phi_value_to_instr(phi_value);
        let mut users = take(&mut self.ctx.value_users[phi_value]);
        users.remove(&phi_instr);
        let phi_block = self.ctx.phi_block[phi_value];
        let phi_var = self.ctx.phi_var[phi_value];
        let phi_type = self.ctx.value_type[phi_value];
        self.ctx.block_phis[phi_block].remove(phi_var);
        self.ctx
            .vars
            .replace_var(phi_var, phi_block, phi_value, equivalent, phi_type)?;
        for user in users {
            let got_replaced = self.replace_user_values(user, phi_value, equivalent);
            if got_replaced && self.ctx.instrs[user].is_phi() {
                // If the user was an incomplete phi and there was an actual replacement
                // we have to check if the phi is now trivial as well.
                self.try_remove_trivial_phi(phi_value)?;
            }
        }
        Ok(equivalent)
    }

    /// Replaces occurrences of `replace_value` with `with_value` for the given user instruction.
    ///
    /// # Note
    ///
    /// - This also updates value users on the fly if replacements took place.
    /// - Returns `true` if an actual replacement took place.
    fn replace_user_values(
        &mut self,
        user: Instr,
        replace_value: Value,
        with_value: Value,
    ) -> bool {
        let user_instr = &mut self.ctx.instrs[user];
        let got_replaced = match user_instr.is_phi() {
            false => {
                // Returns `true` if a value actually got replaced.
                let mut replaced = false;
                user_instr.visit_values_mut(|value| {
                    if *value == replace_value {
                        *value = with_value;
                        replaced = true;
                    }
                    true
                });
                replaced
            }
            true => {
                // Due to incomplete phi instruction we need to treat them differently.
                let phi_value = self.phi_instr_to_value(user);
                let inc_phi = &mut self.ctx.value_incomplete_phi[phi_value];
                // Returns `true` if a value actually got replaced.
                inc_phi.replace_value(replace_value, with_value)
            }
        };
        if got_replaced {
            // Register the instruction as user if there was an actual replacement.
            self.ctx.value_users[with_value].insert(user);
        }
        got_replaced
    }

    /// Returns the associated value of the phi instruction.
    ///
    /// # Panics
    ///
    /// If the given `Instr` is not a phi instruction.
    fn phi_instr_to_value(&self, phi_instr: Instr) -> Value {
        assert!(self.ctx.instrs[phi_instr].is_phi());
        assert_eq!(
            self.ctx.instr_values[phi_instr].len(),
            1,
            "phi instructions must have exactly one output value"
        );
        self.ctx.instr_values[phi_instr][0]
    }

    /// Returns the associated `Instr` for the phi value.
    ///
    /// # Panics
    ///
    /// If the given phi value is not associated to a phi instruction.
    fn phi_value_to_instr(&self, phi_value: Value) -> Instr {
        match self.ctx.value_assoc[phi_value] {
            ValueAssoc::Instr(instr, 0) => {
                assert!(self.ctx.instrs[instr].is_phi());
                instr
            }
            ValueAssoc::Instr(instr, n) => {
                panic!(
                    "found {} to be the {}-th output of a phi instruction {} which is illegal",
                    phi_value, n, instr,
                )
            }
            _ => panic!("unexpected non-instruction value"),
        }
    }

    /// Reads the last assigned value of the variable within the scope of the current basic block.
    ///
    /// # Errors
    ///
    /// - If the variable has not been declared.
    pub fn read_var(&mut self, var: Variable) -> Result<Value, Error> {
        self.ensure_construction_in_order(FunctionBuilderState::Body)?;
        let current = self.current_block()?;
        self.read_var_in_block(var, current)
    }

    /// Returns the type of the variable.
    ///
    /// # Errors
    ///
    /// - If the variable has not been declared.
    pub fn var_type(&mut self, var: Variable) -> Result<Type, Error> {
        Ok(self.ctx.vars.get(var)?.ty())
    }

    /// Changes the else block of the given if instruction `instr` to `new_else`.
    ///
    /// # Panics
    ///
    /// If `instr` does not refer to an if instruction.
    /// If `new_else` does not refer to a valid basic block.
    pub fn change_jump_of_else(&mut self, instr: Instr, new_else: Block) {
        let if_instruction = match &mut self.ctx.instrs[instr] {
            Instruction::Terminal(ir::instr::TerminalInstr::Ite(if_instruction)) => if_instruction,
            _ => panic!("tried to change jump of else destination for a non-if instruction"),
        };
        let old_else = if_instruction.else_block();
        let if_block = self.ctx.block_preds[old_else]
            .iter()
            .copied()
            .find(|block| self.ctx.block_instrs[*block].contains(&instr))
            .expect("one of the predecessors must contain the if-instruction");
        self.ctx.block_preds[old_else].remove(&if_block);
        self.ctx.block_preds[new_else].insert(if_block);
    }

    /// Returns `true` if the block is reachable.
    ///
    /// A block is unreachable if it has no predecessors and is sealed.
    /// A block counts as reachable if it is not (yet) unreachable.
    ///
    /// # Panics
    ///
    /// If the given `block` is invalid for the function builder.
    pub fn is_block_reachable(&self, block: Block) -> bool {
        let unreachable = self.ctx.block_sealed.get(block)
            && self.ctx.block_preds[block].is_empty();
        !unreachable
    }

    /// Returns the SSA output values of the instruction if any.
    pub fn instr_values(&self, instr: Instr) -> Result<&[Value], Error> {
        if !self.ctx.instrs.contains_key(instr) {
            return Err(Error::from(FunctionBuilderError::InvalidInstr {
                instr,
            })
            .with_context("tried to query instruction values"))
        }
        let values = self.ctx.instr_values[instr].as_slice();
        Ok(values)
    }

    /// Finalizes construction of the built function.
    ///
    /// Returns the built function.
    ///
    /// # Errors
    ///
    /// If not all basic blocks in the function are sealed and filled.
    pub fn finalize(mut self) -> Result<FunctionBody, Error> {
        self.ensure_construction_in_order(FunctionBuilderState::Body)?;
        self.ensure_all_blocks_sealed()?;
        self.ensure_all_blocks_filled()?;

        let mut body = FunctionBody {
            blocks: Default::default(),
            block_instrs: Default::default(),
            values: Default::default(),
            value_type: Default::default(),
            value_assoc: Default::default(),
            instrs: Default::default(),
            instr_values: Default::default(),
        };
        let (replace_values, incomplete_phis) =
            self.initialize_values(&mut body);
        self.initialize_instrs(&replace_values, incomplete_phis, &mut body);
        Ok(body)
    }

    /// Ensures that all basic blocks are sealed and returns an `Error` if not.
    fn ensure_all_blocks_sealed(&self) -> Result<(), Error> {
        let is_block_unsealed =
            |block: &Block| -> bool { !self.ctx.block_sealed.get(*block) };
        let len_unsealed_blocks =
            self.ctx.blocks.indices().filter(is_block_unsealed).count();
        if len_unsealed_blocks > 0 {
            return Err(FunctionBuilderError::UnsealedBlocksUponFinalize {
                unsealed: {
                    self.ctx
                        .blocks
                        .indices()
                        .filter(is_block_unsealed)
                        .collect::<Vec<_>>()
                },
            })
            .map_err(Into::into)
        }
        Ok(())
    }

    /// Ensures that all basic blocks are filled and returns an `Error` if not.
    fn ensure_all_blocks_filled(&self) -> Result<(), Error> {
        let is_block_unfilled =
            |block: &Block| -> bool { !self.ctx.block_filled.get(*block) };
        let len_unfilled_blocks =
            self.ctx.blocks.indices().filter(is_block_unfilled).count();
        if len_unfilled_blocks > 0 {
            return Err(FunctionBuilderError::UnfilledBlocksUponFinalize {
                unfilled: {
                    self.ctx
                        .blocks
                        .indices()
                        .filter(is_block_unfilled)
                        .collect::<Vec<_>>()
                },
            })
            .map_err(Into::into)
        }
        Ok(())
    }

    /// Initializes all values of the finalized constructed function body.
    ///
    /// This eliminates all dead SSA values that are no longer in use at the end of construction.
    /// This also updates all data that is associated to the remaining alive SSA values in order
    /// to compact their representation in memory.
    ///
    /// Returns a mapping that stores all the SSA value replacements for all alive SSA values.
    /// Also returns all incomplete phi instructions with their values updated.
    /// These two return values are going to be used in the `initialize_instrs` procedure.
    fn initialize_values(
        &mut self,
        body: &mut FunctionBody,
    ) -> (Replacer<Value>, ComponentMap<Value, IncompletePhi>) {
        let mut value_replace = <Replacer<Value>>::default();
        let mut value_incomplete_phi =
            <ComponentMap<Value, IncompletePhi>>::default();
        // Replace all values and update references for all their associated data.
        for old_value in self.ctx.values.indices() {
            if !self.ctx.value_users[old_value].is_empty()
                || self.ctx.value_assoc[old_value].is_input()
            {
                let new_value = body.values.alloc_some(1);
                body.value_type
                    .insert(new_value, self.ctx.value_type[old_value]);
                body.value_assoc
                    .insert(new_value, self.ctx.value_assoc[old_value]);
                if let Some(incomplete_phi) =
                    self.ctx.value_incomplete_phi.get_mut(old_value)
                {
                    value_incomplete_phi
                        .insert(new_value, take(incomplete_phi));
                }
                value_replace.insert(old_value, new_value);
            }
        }
        // Replace all old value operands of all incomplete phi instructions.
        for value in body.values.indices() {
            if let Some(incomplete_phi) = value_incomplete_phi.get_mut(value) {
                incomplete_phi.visit_values_mut(|old_value| {
                    let new_value = value_replace.get(*old_value);
                    *old_value = new_value;
                    true
                });
            }
        }
        (value_replace, value_incomplete_phi)
    }

    /// For every instruction returns a `bool` indicating if it is alive within the function body.
    ///
    /// Is only called and used from the `initialize_instrs` procedure.
    ///
    /// # Note
    ///
    /// - This information can later be used to remove dead instructions from the function body.
    /// - An instruction is said to be alive if it is used at least once in any of the basic blocks.
    /// - Since phi instructions are not part of the block instructions during function body construction
    ///   we need to treat them specially.
    fn get_alive_instrs(&self) -> DefaultComponentBitVec<Instr> {
        let mut is_alive = <DefaultComponentBitVec<Instr>>::default();
        for block in self.ctx.blocks.indices() {
            for instr in self.ctx.block_instrs[block].iter().copied() {
                is_alive.set(instr, true);
            }
            for (_phi_var, &phi_instr) in &self.ctx.block_phis[block] {
                let phi_value = self.phi_instr_to_value(phi_instr);
                if !self.ctx.value_users[phi_value].is_empty() {
                    is_alive.set(phi_instr, true);
                }
            }
        }
        is_alive
    }

    /// Initializes all instructions of the finalized constructed function body.
    ///
    /// This eliminates all dead instructions that are no longer in use at the end of construction.
    /// This also updates all the data that is associated to the remaining alive instructions in order
    /// to compact their representation in memory.
    fn initialize_instrs(
        &mut self,
        value_replace: &Replacer<Value>,
        value_incomplete_phi: ComponentMap<Value, IncompletePhi>,
        body: &mut FunctionBody,
    ) {
        let is_instr_alive = self.get_alive_instrs();
        let mut instr_replace = <Replacer<Instr>>::default();
        // Fetch all alive instructions.
        for (old_instr, instruction) in &mut self.ctx.instrs {
            if is_instr_alive.get(old_instr) {
                // Replace all old values in the instruction with new values.
                instruction.visit_values_mut(|old_value| {
                    let new_value = value_replace.get(*old_value);
                    *old_value = new_value;
                    true
                });
                // Swap out updated instruction with a placeholder phi instruction.
                // The old instructions will be dropped so whatever we put in there does not matter.
                let instruction =
                    replace(instruction, Instruction::Phi(PhiInstr::default()));
                let new_instr = body.instrs.alloc(instruction);
                instr_replace.insert(old_instr, new_instr);
                // Replace all values associated to the output of all instructions.
                for old_value in &self.ctx.instr_values[old_instr] {
                    let maybe_new_value = value_replace.try_get(*old_value);
                    body.instr_values[new_instr].push(maybe_new_value);
                }
            }
        }
        // Simply copy over the same basic block structure.
        // We do not yet eliminate trivial or dead basic blocks.
        body.blocks = self.ctx.blocks.clone();
        // Convert all incomplete phis into complete phis and add them to the
        // start of each of their associated basic blocks.
        for block in self.ctx.blocks.indices() {
            for &phi_instr in self.ctx.block_phis[block].components() {
                let phi_value = self.phi_instr_to_value(phi_instr);
                let incomplete_phi = &value_incomplete_phi[phi_value];
                let _ = replace(
                    &mut body.instrs[phi_instr],
                    PhiInstr::new(incomplete_phi.operands()).into(),
                );
                body.block_instrs[block].push(phi_instr);
            }
        }
        // Replace instruction references of block instructions.
        for block in self.ctx.blocks.indices() {
            for old_instr in self.ctx.block_instrs[block].iter().copied() {
                let new_instr = instr_replace.get(old_instr);
                body.block_instrs[block].push(new_instr);
            }
        }
        // Replace value association of all alive values.
        for value in body.values.indices() {
            if let ValueAssoc::Instr(old_instr, _) =
                &mut body.value_assoc[value]
            {
                let new_instr = instr_replace.get(*old_instr);
                *old_instr = new_instr;
            }
        }
    }
}

/// A replacement mapping.
#[derive(Debug)]
pub struct Replacer<T> {
    replace: HashMap<T, T, ahash::RandomState>,
}

impl<T> Default for Replacer<T> {
    fn default() -> Self {
        Self {
            replace: Default::default(),
        }
    }
}

impl<T> Replacer<T>
where
    T: Debug + Hash + Eq + Copy,
{
    /// Inserts a replacement for `old_value` to `new_value`.
    ///
    /// # Panics
    ///
    /// If this replacement has already been inserted.
    pub fn insert(&mut self, old_value: T, new_value: T) {
        if self.replace.insert(old_value, new_value).is_some() {
            panic!(
                "encountered duplicate replacement insert of {:?} -> {:?}",
                old_value, new_value,
            )
        }
    }

    /// Returns the replacement of `old_value` or returns `old_value` back.
    pub fn get(&self, old_value: T) -> T {
        self.replace.get(&old_value).copied().unwrap_or(old_value)
    }

    /// Returns the replacement of `old_value` or returns `None`.
    pub fn try_get(&self, old_value: T) -> Option<T> {
        self.replace.get(&old_value).copied()
    }
}
