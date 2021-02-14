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
    incomplete_phi::IncompletePhi,
    instruction::{Instr, InstructionBuilder},
    variable::Variable,
    FunctionBody,
    FunctionBuilderError,
    VariableTranslator,
};
use crate::{IrError, ModuleResources};
use core::mem::replace;
use derive_more::Display;
use entity::{
    ComponentMap,
    ComponentVec,
    DefaultComponentVec,
    EntityArena,
    RawIdx,
};
use ir::{
    instr::{Instruction, PhiInstr},
    primitive::{Block, BlockEntity, Func, Type, Value, ValueEntity},
    ReplaceValue,
};
use smallvec::{smallvec, SmallVec};

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
    pub block_sealed: DefaultComponentVec<Block, bool>,
    /// Is `true` if block is filled.
    ///
    /// A filled block knows all its instructions and has
    /// a terminal instruction as its last instruction.
    pub block_filled: DefaultComponentVec<Block, bool>,
    /// Block instructions.
    pub block_instrs: ComponentVec<Block, Vec<Instr>>,
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
        ComponentMap<Block, ComponentMap<Variable, Value>>,
    /// Optional associated values for instructions.
    ///
    /// Not all instructions can be associated with an SSA value.
    /// For example `store` is not in pure SSA form and therefore
    /// has no SSA value association.
    pub instr_values: ComponentMap<Instr, SmallVec<[Value; 4]>>,
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
    pub value_users: ComponentMap<Value, HashSet<Instr>>,
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
#[derive(Debug)]
pub enum ValueAssoc {
    /// The value is associated to the `n`-th input of the function.
    Input(u32),
    /// The value is associated to the `n`-th output of the instruction.
    Instr(Instr, u32),
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
        let entry_block = ctx.blocks.alloc(Default::default());
        ctx.block_preds.insert(entry_block, Default::default());
        ctx.block_sealed[entry_block] = true;
        ctx.block_instrs.insert(entry_block, Default::default());
        ctx.block_phis.insert(entry_block, Default::default());
        ctx.block_incomplete_phis
            .insert(entry_block, Default::default());
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
            let val = ctx.values.alloc(Default::default());
            ctx.value_type.insert(val, input_type);
            ctx.value_assoc.insert(val, ValueAssoc::Input(n as u32));
            ctx.value_users.insert(val, Default::default());
            ctx.vars.declare_vars(1, input_type).expect(
                "unexpected failure to declare function input variable",
            );
            let input_var = Variable::from_raw(RawIdx::from_u32(n as u32));
            ctx.vars
                .write_var(input_var, val, entry_block, || input_type, None)
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
    ) -> Result<(), IrError> {
        self.ensure_construction_in_order(
            FunctionBuilderState::LocalVariables,
        )?;
        self.ctx.vars.declare_vars(amount, ty)?;
        Ok(())
    }

    /// Start defining the body of the function with its basic blocks and instructions.
    pub fn body(&mut self) -> Result<(), IrError> {
        self.ensure_construction_in_order(FunctionBuilderState::Body)?;
        Ok(())
    }

    /// Creates a new basic block for the function and returns a reference to it.
    pub fn create_block(&mut self) -> Result<Block, IrError> {
        self.ensure_construction_in_order(FunctionBuilderState::Body)?;
        let new_block = self.ctx.blocks.alloc(Default::default());
        self.ctx.block_preds.insert(new_block, Default::default());
        self.ctx.block_instrs.insert(new_block, Default::default());
        self.ctx.block_phis.insert(new_block, Default::default());
        self.ctx
            .block_incomplete_phis
            .insert(new_block, Default::default());
        Ok(new_block)
    }

    /// Returns a reference to the current basic block if any.
    ///
    /// # Errors
    ///
    /// If no basic blocks exist.
    pub fn current_block(&mut self) -> Result<Block, IrError> {
        self.ensure_construction_in_order(FunctionBuilderState::Body)?;
        Ok(self.ctx.current)
    }

    /// Switches the current block to the given basic block.
    ///
    /// # Errors
    ///
    /// If the basic block does not exist in this function.
    pub fn switch_to_block(&mut self, block: Block) -> Result<(), IrError> {
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
    pub fn seal_block(&mut self) -> Result<(), IrError> {
        self.ensure_construction_in_order(FunctionBuilderState::Body)?;
        let block = self.current_block()?;
        let already_sealed = replace(&mut self.ctx.block_sealed[block], true);
        if already_sealed {
            return Err(FunctionBuilderError::BasicBlockIsAlreadySealed {
                block,
            })
            .map_err(Into::into)
        }
        // Popping incomplete phis by inserting a new empty component map.
        let incomplete_phis = self
            .ctx
            .block_incomplete_phis
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
    pub fn ins<'b>(
        &'b mut self,
    ) -> Result<InstructionBuilder<'b, 'a>, IrError> {
        self.ensure_construction_in_order(FunctionBuilderState::Body)?;
        let block = self.current_block()?;
        let already_filled = self.ctx.block_filled[block];
        if already_filled {
            return Err(FunctionBuilderError::BasicBlockIsAlreadyFilled {
                block,
            })
            .map_err(Into::into)
        }
        Ok(InstructionBuilder::new(self))
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
        self.ensure_construction_in_order(FunctionBuilderState::Body)?;
        let block = self.current_block()?;
        let FunctionBuilderContext {
            vars, value_type, ..
        } = &mut self.ctx;
        vars.write_var(var, value, block, || value_type[value], None)?;
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
        self.ctx
            .value_incomplete_phi
            .insert(value, Default::default());
        self.ctx
            .value_assoc
            .insert(value, ValueAssoc::Instr(instr, 0));
        self.ctx.value_type.insert(value, var_type);
        self.ctx.value_users.insert(value, Default::default());
        self.ctx.phi_var.insert(value, var);
        self.ctx.phi_block.insert(value, block);
        self.ctx.block_phis[block].insert(var, instr);
        self.ctx.block_incomplete_phis[block].insert(var, value);
        self.ctx
            .vars
            .write_var(var, value, block, || var_type, None)?;
        self.ctx.instr_values.insert(instr, smallvec![value]);
        Ok(value)
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
        self.ctx
            .vars
            .write_var(var, value, block, || var_type, None)?;
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
    ) -> Result<Value, IrError> {
        let incomplete_phi = &self.ctx.value_incomplete_phi[phi_value];
        let equivalent_value = match incomplete_phi.is_trivial(phi_value)? {
            Some(equivalent_value) => {
                // The phi instruction is trivial and the returned value
                // is equivalent and shall replace it from now on.
                equivalent_value
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
        let same = equivalent_value;
        let phi_instr = self.phi_value_to_instr(phi_value);
        self.ctx.value_users[phi_value].remove(&phi_instr);
        let users = self
            .ctx
            .value_users
            .insert(phi_value, Default::default())
            .unwrap_or_default();
        let phi_block = self.ctx.phi_block[phi_value];
        let phi_var = self.ctx.phi_var[phi_value];
        let phi_value = self.phi_instr_to_value(phi_instr);
        let phi_type = self.ctx.value_type[phi_value];
        self.ctx.block_phis[phi_block].remove(phi_var);
        self.ctx.vars.write_var(
            phi_var,
            same,
            phi_block,
            || phi_type,
            Some(phi_value),
        )?;
        for user in users {
            let got_replaced = self.replace_user_values(user, phi_value, same);
            if got_replaced && self.ctx.instrs[user].is_phi() {
                // If the user was an incomplete phi and there was an actual replacement
                // we have to check if the phi is now trivial as well.
                self.try_remove_trivial_phi(phi_value)?;
            }
        }
        Ok(same)
    }

    /// Replaces occurrences of `replace_value` with `with_value` for the given user instruction.
    ///
    /// # Note
    ///
    /// - This also updates value users on the fly if replacments took place.
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
                user_instr.replace_value(|value| {
                    if *value == replace_value {
                        *value = with_value;
                        return true
                    }
                    false
                })
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
    /// - If the variable has not beed declared.
    pub fn read_var(&mut self, var: Variable) -> Result<Value, IrError> {
        self.ensure_construction_in_order(FunctionBuilderState::Body)?;
        let current = self.current_block()?;
        self.read_var_in_block(var, current)
    }

    /// Returns the type of the variable.
    ///
    /// # Errors
    ///
    /// - If the variable has not beed declared.
    pub fn var_type(&mut self, var: Variable) -> Result<Type, IrError> {
        Ok(self.ctx.vars.get(var)?.ty())
    }

    /// Returns the SSA output values of the instruction if any.
    pub fn instr_values(&self, instr: Instr) -> Result<&[Value], IrError> {
        if !self.ctx.instrs.contains_key(instr) {
            return Err(IrError::from(FunctionBuilderError::InvalidInstr {
                instr,
            })
            .with_context("tried to query instruction values"))
        }
        let values = self
            .ctx
            .instr_values
            .get(instr)
            .map(SmallVec::as_slice)
            .unwrap_or_default();
        Ok(values)
    }

    /// Finalizes construction of the built function.
    ///
    /// Returns the built function.
    ///
    /// # Errors
    ///
    /// If not all basic blocks in the function are sealed and filled.
    pub fn finalize(mut self) -> Result<FunctionBody, IrError> {
        self.ensure_construction_in_order(FunctionBuilderState::Body)?;
        let unsealed_blocks = self
            .ctx
            .blocks
            .indices()
            .filter(|&block| !self.ctx.block_sealed[block])
            .collect::<Vec<_>>();
        if !unsealed_blocks.is_empty() {
            return Err(FunctionBuilderError::UnsealedBlocksUponFinalize {
                unsealed: unsealed_blocks,
            })
            .map_err(Into::into)
        }
        let unfilled_blocks = self
            .ctx
            .blocks
            .indices()
            .filter(|&block| !self.ctx.block_filled[block])
            .collect::<Vec<_>>();
        if !unfilled_blocks.is_empty() {
            return Err(FunctionBuilderError::UnfilledBlocksUponFinalize {
                unfilled: unfilled_blocks,
            })
            .map_err(Into::into)
        }
        self.ctx.blocks.shrink_to_fit();
        self.ctx.values.shrink_to_fit();
        self.ctx.instrs.shrink_to_fit();
        self.ctx.block_instrs.shrink_to_fit();
        self.ctx.instr_values.shrink_to_fit();
        self.ctx.value_type.shrink_to_fit();
        self.ctx.value_assoc.shrink_to_fit();
        let mut block_instrs = ComponentVec::default();
        for (block, var_phis) in self.ctx.block_phis.iter() {
            for (_var, &phi_instr) in var_phis {
                let phi_value = self.phi_instr_to_value(phi_instr);
                let incomplete_phi = &self.ctx.value_incomplete_phi[phi_value];
                let _empty_old_phi = core::mem::replace(
                    &mut self.ctx.instrs[phi_instr],
                    PhiInstr::new(incomplete_phi.operands()).into(),
                );
            }
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
        Ok(FunctionBody {
            blocks: self.ctx.blocks,
            values: self.ctx.values,
            instrs: self.ctx.instrs,
            block_instrs,
            instr_values: self.ctx.instr_values,
            value_type: self.ctx.value_type,
            value_assoc: self.ctx.value_assoc,
        })
    }
}
