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

use super::{
    FunctionBody,
    FunctionBuilderError,
    InstructionBuilder,
    ValueDefinition,
    ValueUser,
    Variable,
    VariableTranslator,
};
use crate::{primitive::Instr, Error, ModuleResources};
use core::mem::take;
use derive_more::Display;
use entity::{
    ComponentMap,
    ComponentVec,
    DefaultComponentBitVec,
    DefaultComponentMap,
    DefaultComponentVec,
    EntityArena,
    Idx,
    PhantomEntityArena,
    RawIdx,
};
use ir::{
    instr::Instruction,
    primitive::{Block, BlockEntity, Func, Type, Value, ValueEntity},
    VisitValuesMut,
};
use smallvec::SmallVec;

/// Type alias to Rust's `HashSet` but using `ahash` as hasher which is more efficient.
type HashSet<T> = std::collections::HashSet<T, ahash::RandomState>;

/// Incrementally guides the construction process to build a Runwell IR function.
#[derive(Debug)]
pub struct FunctionBuilder<'a> {
    pub(super) ctx: FunctionBuilderContext,
    pub(super) func: Func,
    pub(super) res: &'a ModuleResources,
    state: FunctionBuilderState,
}

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

/// A branching edge entity.
///
/// An entity of this kind represents a single edge between a pair
/// of two basic blocks with a branch between them. There can be
/// multiple such edges between the same pair of basic blocks.
#[derive(Debug)]
pub enum EdgeEntity {}

/// A unique edge entity reference.
pub type Edge = Idx<EdgeEntity>;

/// The context that is built during IR function construction.
#[derive(Debug)]
pub struct FunctionBuilderContext {
    /// The current basic block that is being operated on.
    pub current: Block,
    /// Arena for all block entities.
    pub blocks: PhantomEntityArena<BlockEntity>,
    /// Arena for all branching edges.
    pub edges: PhantomEntityArena<EdgeEntity>,
    /// Arena for all SSA value entities.
    pub values: PhantomEntityArena<ValueEntity>,
    /// Arena for all IR instructions.
    pub instrs: EntityArena<Instruction>,
    /// All incoming edges for the block.
    ///
    /// # Note
    ///
    /// Due to conditional branch instructions and branching tables is is
    /// possible to have multiple edges between the same pair of blocks.
    ///
    /// The outer `Block` represents the destination basic block that stores
    /// a mapping for every of its predecessor blocks and their edges.
    ///
    /// So this mapping stores both the predecessors of a basic block as well
    /// as all the edges between the two.
    ///
    /// We optimize for the case of a single branching edge between a pair of
    /// two basic blocks because this is a very common case.
    pub block_edges: DefaultComponentVec<Block, SmallVec<[Edge; 4]>>,
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
    /// Block parameters.
    pub block_params: DefaultComponentVec<Block, SmallVec<[Value; 4]>>,
    /// The incomplete parameters of a block for each variable used in the block.
    pub block_incomplete_params:
        DefaultComponentMap<Block, ComponentMap<Variable, Value>>,
    /// Required information to remove block parameter if it becomes trivial.
    pub param_var: ComponentMap<Value, Variable>,
    /// The arguments for the block parameters of the branching edge.
    pub edge_args: DefaultComponentVec<Edge, SmallVec<[Value; 4]>>,
    /// The source basic block for the edge.
    pub edge_src: ComponentVec<Edge, Block>,
    /// The destination basic block for the edge.
    pub edge_dst: ComponentVec<Edge, Block>,
    /// Optional associated values for instructions.
    ///
    /// Not all instructions can be associated with an SSA value.
    /// For example `store` is not in pure SSA form and therefore
    /// has no SSA value association.
    pub instr_values: DefaultComponentMap<Instr, SmallVec<[Value; 4]>>,
    /// Types for all values.
    pub value_type: ComponentVec<Value, Type>,
    /// The association of the SSA value.
    ///
    /// Every SSA value has an association to either an IR instruction
    /// or to an input parameter of the IR function under construction.
    pub value_definition: ComponentVec<Value, ValueDefinition>,
    /// Stores all users of all values.
    ///
    /// This information is required to replace an unnecessary phi
    /// phi instruction with its single operand. Users of the unnecessary
    /// phi instruction are updated accordingly and phi instruction
    /// users are checked for triviality.
    ///
    /// Also this information can be used for optimizations when replacing
    /// one instruction with another.
    pub value_users: DefaultComponentMap<Value, HashSet<ValueUser>>,
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
            edges: Default::default(),
            values: Default::default(),
            instrs: Default::default(),
            block_params: Default::default(),
            block_edges: Default::default(),
            block_sealed: Default::default(),
            block_filled: Default::default(),
            block_instrs: Default::default(),
            block_incomplete_params: Default::default(),
            param_var: Default::default(),
            edge_args: Default::default(),
            edge_src: Default::default(),
            edge_dst: Default::default(),
            instr_values: Default::default(),
            value_type: Default::default(),
            value_definition: Default::default(),
            value_users: Default::default(),
            current: Block::from_raw(RawIdx::from_u32(0)),
            vars: Default::default(),
        }
    }
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
        assert!(
            ctx.blocks.is_empty(),
            "function body unexpectedly already has basic blocks: {:?}",
            ctx.blocks,
        );
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
            debug_assert!(
                n < u16::MAX as usize,
                "encountered too many function input parameters. \
                found {} but cannot handle more than {}.",
                n,
                u16::MAX,
            );
            let n = n as u32;
            let val = ctx.values.alloc_some(1);
            ctx.value_type.insert(val, input_type);
            ctx.value_definition
                .insert(val, ValueDefinition::Param(entry_block, n));
            ctx.vars.declare_vars(1, input_type)
                .unwrap_or_else(|err| {
                    panic!(
                        "unexpected failure to declare the function input variable \
                        at position {} of type {}: {:?}",
                        n,
                        input_type,
                        err,
                    )
                });
            let input_var = Variable::from_raw(RawIdx::from_u32(n));
            ctx.vars
                .write_var(input_var, val, entry_block, input_type)
                .unwrap_or_else(|err| {
                    panic!(
                        "unexpected failure to assign variable {} of type {} to {}. \
                        The variable has just been declared as function input {} in \
                        entry block {}: {:?}",
                        input_var,
                        val,
                        input_type,
                        n,
                        entry_block,
                        err,
                    )
                })
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
        let incomplete_params =
            take(&mut self.ctx.block_incomplete_params[block]);
        for (_, &param) in incomplete_params.iter() {
            self.add_incomplete_param_args(param)?;
        }
        Ok(())
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

    /// Creates a new incomplete block parameter.
    ///
    /// These block parameters are driven by the SSA value construction
    /// and can be placed during basic block construction unlike the user
    /// provided block parameters.
    fn create_incomplete_block_parameter(
        &mut self,
        var: Variable,
        var_type: Type,
        block: Block,
    ) -> Result<Value, Error> {
        debug_assert!(
            !self.ctx.block_sealed.get(block),
            "cannot create incomplete block parameter for sealed block {}",
            block
        );
        debug_assert!(
            !self.ctx.block_filled.get(block),
            "cannot create incomplete block parameter for filled block {}",
            block
        );
        let value = self.ctx.values.alloc_some(1);
        let pos = self.ctx.block_params[block].len();
        assert!(
            pos < u16::MAX as usize,
            "there are {} block parameters for block {} \
            while the maximum amount of block parameters is {}",
            pos,
            block,
            u16::MAX,
        );
        self.ctx
            .value_definition
            .insert(value, ValueDefinition::Param(block, pos as u32));
        self.ctx.value_type.insert(value, var_type);
        self.ctx.block_params[block].push(value);
        self.ctx.block_incomplete_params[block].insert(var, value);
        self.ctx.param_var.insert(value, var);
        self.ctx.vars.write_var(var, value, block, var_type)?;
        Ok(value)
    }

    /// Returns the associated block and index for the block parameter value.
    ///
    /// # Panics
    ///
    /// If the given value is not defined as a block parameter.
    fn expect_block_param(&self, param: Value) -> (Block, u32) {
        match self.ctx.value_definition[param] {
            ValueDefinition::Param(block, index) => (block, index),
            ValueDefinition::Instr(instr, index) => {
                panic!(
                "encountered a block parameter that is falsely defined as the \
                return value at index {} of instruction {}",
                index,
                instr,
            )
            }
        }
    }

    /// Add arguments to the incomplete block parameter.
    ///
    /// # Note
    ///
    /// After this procedure the incomplete block parameter will be completed.
    /// This procedure can only run once a basic block has been sealed.
    fn add_incomplete_param_args(
        &mut self,
        param: Value,
    ) -> Result<Value, Error> {
        let param_var = self.ctx.param_var[param];
        let (param_block, index) = self.expect_block_param(param);
        let incoming_edges = self.ctx.block_edges[param_block].clone();
        for edge in incoming_edges {
            let edge_dst = self.ctx.edge_dst[edge];
            let value = self.read_var_in_block(param_var, edge_dst)?;
            let edge_args = &mut self.ctx.edge_args[edge];
            debug_assert_eq!(edge_args.len(), index as usize);
            edge_args.push(value);
            self.ctx.value_users[value].insert(ValueUser::Param(param));
        }
        self.try_remove_trivial_param(param)
    }

    /// Returns `true` if all incoming edges of the block have the same source block.
    ///
    /// Returns `false` otherwise or if there are no incoming edges for the block.
    fn get_unique_predecessor_block(&self, block: Block) -> Option<Block> {
        let mut same = None;
        for edge in &self.ctx.block_edges[block] {
            let block = self.ctx.edge_src[*edge];
            if let Some(same) = same {
                if block != same {
                    return None
                }
            }
            same = Some(block);
        }
        same
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
            let value =
                self.create_incomplete_block_parameter(var, var_type, block)?;
            return Ok(value)
        }
        let value = match self.get_unique_predecessor_block(block) {
            Some(pred) => {
                // Optimize the common case where all incoming edges have the same
                // source basic block. No incomplete block parameter required in this case.
                self.read_var_in_block(var, pred)?
            }
            None => {
                // Break potential cycles with incomplete block parameter.
                let param = self
                    .create_incomplete_block_parameter(var, var_type, block)?;
                self.add_incomplete_param_args(param)?
            }
        };
        self.ctx.vars.write_var(var, value, block, var_type)?;
        Ok(value)
    }

    /// Checks if the given phi instruction is trivial replacing it if true.
    ///
    /// Replacement is a recursive operation that replaces all uses of the
    /// phi instruction with its only non-phi operand. During this process
    /// other phi instruction users might become trivial and cascade the effect.
    fn try_remove_trivial_param(
        &mut self,
        param: Value,
    ) -> Result<Value, Error> {
        let equivalent = match self.is_param_trivial(param)? {
            Some(equivalent) => {
                // The block parameter is trivial and the returned value
                // is found to be equivalent to it and shall replace all
                // uses of the block parameter from now on.
                equivalent
            }
            None => {
                // The block parameter was found to be non-trivial.
                return Ok(param)
            }
        };
        // The block parameter was determined to be trivial and must be replaced with
        // the `equivalent` for all of its users.
        //
        // We `take` all users of the block parameter. This allows us to iterate over
        // all users without borrow checker problems while at the same time clearing the
        // set of users which is exactly what we want to happen.
        let (block, _index) = self.expect_block_param(param);
        let param_var = self.ctx.param_var[param];
        let param_type = self.ctx.value_type[param];
        self.ctx.block_incomplete_params[block].remove(param_var);
        self.ctx
            .vars
            .replace_var(param_var, block, param, equivalent, param_type)?;
        let mut param_users = take(&mut self.ctx.value_users[param]);
        // Remove the trivial block parameter from its own set of users before iteration.
        param_users.remove(&ValueUser::Param(param));
        for user in param_users {
            match user {
                ValueUser::Instr(i) => {
                    self.replace_value_for_instr(i, param, equivalent);
                }
                ValueUser::Param(p) => {
                    self.replace_value_for_param(p, param, equivalent);
                    // If the user is another block parameter and there was an actual replacement
                    // we have to check if the block parameter user is now trivial as well.
                    self.try_remove_trivial_param(p)?;
                }
            };
        }
        Ok(equivalent)
    }

    /// Checks if the incomplete block parameter is trivial.
    ///
    /// A block parameter is trivial if all edges provide the same value
    /// or the value of the block parameter itself as the argument.
    ///
    /// - If trivial the `Value` to which the incomplete block parameter is
    ///   equivalent is returned.
    /// - If the incomplete block parameter is yet deemed non-trivial
    ///   `None` is returned.
    ///
    /// # Errors
    ///
    /// If the incomplete block parameter is unreachable or in the entry block.
    pub fn is_param_trivial(
        &self,
        param: Value,
    ) -> Result<Option<Value>, Error> {
        let (block, index) = self.expect_block_param(param);
        let mut same: Option<Value> = None;
        for edge in &self.ctx.block_edges[block] {
            let arg = self.ctx.edge_args[*edge][index as usize];
            if Some(arg) == same || arg == param {
                // Unique value or self reference.
                continue
            }
            if same.is_some() {
                // The block parameter has at least two distinct arguments: non-trivial
                return Ok(None)
            }
            same = Some(arg);
        }
        match same {
            None => {
                // The block parameter is unreachable or in the entry block.
                // The paper we implement replaces it with an undefined instruction
                // but we simply bail out with an error.
                Err(FunctionBuilderError::UnreachablePhi { value: param })
                    .map_err(Into::into)
            }
            Some(same) => {
                // The block parameter was determined to be trivial and should
                // be replaced by the `same` value in all of its users.
                Ok(Some(same))
            }
        }
    }

    /// Replaces all occurrences of `replace_value` with `with_value` for the block parameter.
    ///
    /// The block parameter is meant to be a user of `replace_value` if any of its
    /// incoming edges uses `replace_value` as an argument to the block parameter.
    /// After this procedure this branching edge will no longer be a user of
    /// `replace_value` and instead be a user of `with_value`.
    ///
    /// Naturally `replace_user` and `with_value` must be distinct values.
    ///
    /// # Note
    ///
    /// - This also updates value users on the fly if replacements took place.
    /// - Returns `true` if an actual replacement took place.
    ///
    /// # Panics
    ///
    /// If the given `param` is not defined as a block parameter.
    fn replace_value_for_param(
        &mut self,
        param: Value,
        replace_value: Value,
        with_value: Value,
    ) -> bool {
        debug_assert_ne!(replace_value, with_value);
        let (block, index) = self.expect_block_param(param);
        let incoming_edges = &mut self.ctx.block_edges[block];
        let mut is_user = false;
        for edge in incoming_edges {
            let edge_args = &mut self.ctx.edge_args[*edge];
            let param_arg = &mut edge_args[index as usize];
            if *param_arg == replace_value {
                *param_arg = with_value;
                is_user = true;
            }
        }
        let value_user = ValueUser::Param(param);
        if is_user {
            // Register the block parameter as user of the
            // new value if it was a user of the old one.
            self.ctx.value_users[with_value].insert(value_user);
            debug_assert!(
                self.ctx.value_users[with_value].contains(&value_user)
            );
        }
        debug_assert!(
            !self.ctx.value_users[replace_value].contains(&value_user)
        );
        is_user
    }

    /// Replaces all occurrences of `replace_value` with `with_value` for the instruction.
    ///
    /// The instruction is meant to be a user of `replace_value` if it refers to it
    /// in some way. After this procedure that instruction will no longer be a user
    /// of `replace_value` and instead be a user of `with_value`.
    ///
    /// Naturally `replace_user` and `with_value` must be distinct values.
    ///
    /// # Note
    ///
    /// - This also updates value users on the fly if replacements took place.
    /// - Returns `true` if an actual replacement took place.
    fn replace_value_for_instr(
        &mut self,
        instr: Instr,
        replace_value: Value,
        with_value: Value,
    ) -> bool {
        debug_assert_ne!(replace_value, with_value);
        let user_instr = &mut self.ctx.instrs[instr];
        debug_assert!(!user_instr.is_phi());
        let mut is_user = false;
        user_instr.visit_values_mut(|value| {
            if *value == replace_value {
                *value = with_value;
                is_user = true;
            }
            true
        });
        let value_user = ValueUser::Instr(instr);
        if is_user {
            // Register the instruction as user of the
            // new value if it was a user of the old one.
            self.ctx.value_users[with_value].insert(value_user);
            debug_assert!(
                self.ctx.value_users[with_value].contains(&value_user)
            );
        }
        debug_assert!(
            !self.ctx.value_users[replace_value].contains(&value_user)
        );
        is_user
    }

    /// Returns the type of the variable.
    ///
    /// # Errors
    ///
    /// - If the variable has not been declared.
    pub fn var_type(&mut self, var: Variable) -> Result<Type, Error> {
        Ok(self.ctx.vars.get(var)?.ty())
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
            && self.ctx.block_edges[block].is_empty();
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
}
