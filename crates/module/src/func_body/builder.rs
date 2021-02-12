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
    instruction::{Instr, InstructionBuilder},
    variable::Variable,
    FunctionBody,
    FunctionBuilderError,
    VariableTranslator,
};
use crate::{IrError, ModuleResources};
use derive_more::Display;
use entity::{ComponentMap, ComponentVec, EntityArena, RawIdx};
use ir::{
    instr::{Instruction, PhiInstr},
    primitive::{Block, BlockEntity, Func, Type, Value, ValueEntity},
    ReplaceValue,
};

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
    pub block_sealed: ComponentVec<Block, bool>,
    /// Is `true` if block is filled.
    ///
    /// A filled block knows all its instructions and has
    /// a terminal instruction as its last instruction.
    pub block_filled: ComponentVec<Block, bool>,
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
            phi_block: Default::default(),
            phi_var: Default::default(),
            incomplete_phis: Default::default(),
            instr_value: Default::default(),
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
    Input(u32),
    Instr(Instr),
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
        ctx.block_sealed.insert(entry_block, true);
        ctx.block_filled.insert(entry_block, false);
        ctx.block_instrs.insert(entry_block, Default::default());
        ctx.block_phis.insert(entry_block, Default::default());
        ctx.incomplete_phis.insert(entry_block, Default::default());
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
                .write_var(input_var, val, entry_block, || input_type)
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
        self.ctx.block_sealed.insert(new_block, false);
        self.ctx.block_filled.insert(new_block, false);
        self.ctx.block_instrs.insert(new_block, Default::default());
        self.ctx.block_phis.insert(new_block, Default::default());
        self.ctx
            .incomplete_phis
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
        let already_sealed = self
            .ctx
            .block_sealed
            .insert(block, true)
            .expect("encountered invalid current basic block");
        if already_sealed {
            return Err(FunctionBuilderError::BasicBlockIsAlreadySealed {
                block,
            })
            .map_err(Into::into)
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
            self.create_phi_instruction(var, var_type, block)?
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
        for (_block, op) in instruction.operands() {
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
            return Err(FunctionBuilderError::UnreachablePhi {
                value: phi_value,
            })
            .map_err(Into::into)
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
            .block_sealed
            .iter()
            .filter_map(|(idx, &sealed)| if !sealed { Some(idx) } else { None })
            .collect::<Vec<_>>();
        if !unsealed_blocks.is_empty() {
            return Err(FunctionBuilderError::UnsealedBlocksUponFinalize {
                unsealed: unsealed_blocks,
            })
            .map_err(Into::into)
        }
        let unfilled_blocks = self
            .ctx
            .block_filled
            .iter()
            .filter_map(|(idx, &filled)| if !filled { Some(idx) } else { None })
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
        self.ctx.instr_value.shrink_to_fit();
        self.ctx.value_type.shrink_to_fit();
        self.ctx.value_assoc.shrink_to_fit();
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
        Ok(FunctionBody {
            blocks: self.ctx.blocks,
            values: self.ctx.values,
            instrs: self.ctx.instrs,
            block_instrs,
            instr_value: self.ctx.instr_value,
            value_type: self.ctx.value_type,
            value_assoc: self.ctx.value_assoc,
        })
    }
}
