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
    Replacer,
    ValueDefinition,
    ValueUser,
    Variable,
    VariableTranslator,
};
use crate::{primitive::Instr, Error, ModuleResources};
use core::mem::{replace, take};
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
    instr::{Instruction, TerminalInstr},
    primitive::{
        Block,
        BlockEntity,
        Const,
        Edge,
        EdgeEntity,
        Func,
        Type,
        Value,
        ValueEntity,
    },
    VisitEdges,
    VisitValuesMut,
};
use smallvec::SmallVec;

/// Type alias to Rust's `HashSet` but using `ahash` as hasher which is more efficient.
type HashSet<T> = std::collections::HashSet<T, ahash::RandomState>;

/// Type alias to Rust's `HashMap` but using `ahash` as hasher which is more efficient.
type HashMap<K, V> = std::collections::HashMap<K, V, ahash::RandomState>;

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

/// The context that is built during IR function construction.
#[derive(Debug)]
pub struct FunctionBuilderContext {
    /// The current basic block that is being operated on.
    pub current: Block,
    /// The unique entry basic block of the function.
    pub entry_block: Block,
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
    /// Contains the indices of all incomplete parameters per block.
    pub block_incomplete_params: DefaultComponentMap<Block, HashSet<u32>>,
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
    /// Zero-constant initializers to emulate default initialization of
    /// Wasm local variables. Every type has its own zero initializer.
    pub zero_init: HashMap<Type, Value>,
}

impl Default for FunctionBuilderContext {
    fn default() -> Self {
        let dummy_block = Block::from_raw(RawIdx::from_u32(0));
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
            current: dummy_block,
            entry_block: dummy_block,
            vars: Default::default(),
            zero_init: Default::default(),
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
        ctx.entry_block = entry_block;
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
            ctx.block_params[entry_block].push(val);
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
        self.implicit_zero_init(ty)?;
        Ok(())
    }

    /// Creates the zero-initializer for the `ty` and stores it for later reuse.
    ///
    /// # Note
    ///
    /// We eagerly create these zero-initializers, one per Runwell type.
    /// However, they only end up in the final constructed function if they
    /// are actually used since otherwise they will be eliminated in the
    /// dead code elimination phase.
    fn implicit_zero_init(&mut self, ty: Type) -> Result<(), Error> {
        self.ensure_construction_in_order(
            FunctionBuilderState::LocalVariables,
        )?;
        debug_assert_eq!(self.ctx.current, self.ctx.entry_block);
        if let Some(_cached) = self.ctx.zero_init.get(&ty) {
            return Ok(())
        }
        let value = self.ins_impl()?.constant(Const::zero(ty))?;
        self.ctx.zero_init.insert(ty, value);
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
        // The list of block parameters start with user provided block parameters
        // followed by the block parameters generated through SSA construction.
        // Only block parameters generated by the SSA construction may be incomplete.
        let len_params = self.ctx.block_incomplete_params[block].len();
        for index in 0..len_params {
            debug_assert!(index < u16::MAX as usize);
            if !self.ctx.block_incomplete_params[block]
                .contains(&(index as u32))
            {
                // The incomplete block parameter has already been resolved.
                continue
            }
            let param = self.ctx.block_params[block][index];
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

    /// Creates a user provided block parameter with the given type.
    ///
    /// Returns the value that is defined as the new block parameter.
    ///
    /// # Errors
    ///
    /// If the block already contains non-user provided parameters or
    /// instructions. Basically this operation can only be used directly
    /// after creating a new basic block.
    pub fn create_block_parameter(
        &mut self,
        block: Block,
        param_type: Type,
    ) -> Result<Value, Error> {
        assert!(
            self.ctx.block_instrs[block].is_empty(),
            "cannot add a user provided block parameter to a basic block that has instructions already",
        );
        assert!(
            self.ctx.block_incomplete_params[block].is_empty(),
            "cannot add a user provided block parameter to a basic block that already has SSA parameters",
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
        self.ctx.value_type.insert(value, param_type);
        self.ctx.block_params[block].push(value);
        Ok(value)
    }

    /// Returns the block parameters of the given block.
    pub fn block_parameters(&self, block: Block) -> &[Value] {
        &self.ctx.block_params[block]
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
        self.ctx.block_incomplete_params[block].insert(pos as u32);
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
        let len_incoming_edges = self.ctx.block_edges[param_block].len();
        for edge_idx in 0..len_incoming_edges {
            debug_assert_eq!(
                self.ctx.block_edges[param_block].len(),
                len_incoming_edges,
                "the number of incoming edges has changed while adding \
                another incomplete block parameter {} to {} at index {} \
                representing {}.",
                param,
                param_block,
                index,
                param_var,
            );
            let edge = self.ctx.block_edges[param_block][edge_idx];
            let edge_src = self.ctx.edge_src[edge];
            let value = self.read_var_in_block(param_var, edge_src)?;
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
        let (block, index) = self.expect_block_param(param);
        let param_var = self.ctx.param_var[param];
        let param_type = self.ctx.value_type[param];
        self.ctx.block_incomplete_params[block].remove(&index);
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
                ValueUser::Edge(e) => {
                    self.replace_value_for_edge(e, param, equivalent);
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
        for &edge in &self.ctx.block_edges[block] {
            let arg = self.ctx.edge_args[edge][index as usize];
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
                // The paper we implement replaces it with an undefined instruction.
                // However, we try to mimic WebAssembly semantics instead.
                //
                // # Note
                //
                // This can happen if a local variable is accesses before it has
                // ever been assigned to some value. We zero-initialize the values
                // in this cases since variables in WebAssembly are zero-initialized.
                let ty = self.ctx.value_type[param];
                let zero_init = self.ctx.zero_init[&ty];
                Ok(Some(zero_init))
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

    /// Replaces all occurrences of `replace_value` with `with_value` for the edge.
    ///
    /// The edge is meant to be a user of `replace_value` if it refers to it
    /// via its arguments. After this procedure the edge will no longer be a user
    /// of `replace_value` and instead be a user of `with_value`.
    ///
    /// Naturally `replace_user` and `with_value` must be distinct values.
    ///
    /// # Note
    ///
    /// - This also updates value users on the fly if replacements took place.
    /// - Returns `true` if an actual replacement took place.
    fn replace_value_for_edge(
        &mut self,
        edge: Edge,
        replace_value: Value,
        with_value: Value,
    ) -> bool {
        debug_assert_ne!(replace_value, with_value);
        let mut is_user = false;
        for arg in &mut self.ctx.edge_args[edge] {
            if *arg == replace_value {
                *arg = with_value;
                is_user = true;
            }
        }
        let value_user = ValueUser::Edge(edge);
        if is_user {
            // Register the edge as user of the
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

    /// Returns the type of the given value.
    ///
    /// # Panics
    ///
    /// If the given value is invalid.
    pub fn value_type(&self, value: Value) -> Type {
        self.ctx.value_type[value]
    }

    /// Changes the destination of all edges with a destination equal to
    /// `old_destination` to `new_destination`.
    ///
    /// # Panics
    ///
    /// If `old_destination` or `new_destination` do not refer to a valid block.
    ///
    /// # Errors
    ///
    /// - If the block parameters of `old_destination` and `new_destination`
    /// do not match.
    /// - If either `old_destination` or `new_destination` are already sealed.
    pub fn relink_edge_destination(
        &mut self,
        instr: Instr,
        old_destination: Block,
        new_destination: Block,
    ) -> Result<(), Error> {
        let FunctionBuilderContext {
            instrs,
            block_params,
            block_edges,
            block_sealed,
            edge_dst,
            ..
        } = &mut self.ctx;
        if block_params[old_destination] != block_params[new_destination] {
            return Err(FunctionBuilderError::UnmatchingBlockParameters {
                block_a: old_destination,
                block_b: new_destination,
            })
            .map_err(Into::into)
        }
        if block_sealed.get(old_destination) {
            return Err(FunctionBuilderError::BasicBlockIsAlreadySealed {
                block: old_destination,
            })
            .map_err(Into::into)
        }
        if block_sealed.get(new_destination) {
            return Err(FunctionBuilderError::BasicBlockIsAlreadySealed {
                block: new_destination,
            })
            .map_err(Into::into)
        }
        let instruction = &mut instrs[instr];
        instruction.visit_edges(|edge| {
            let destination = edge_dst[edge];
            if destination != old_destination {
                // Skip and visit next edge in case source does not match.
                return true
            }
            edge_dst.insert(edge, new_destination);
            let edge_index = block_edges[old_destination]
            .iter()
            .copied()
            .position(|e| e == edge)
            .unwrap_or_else(|| panic!(
                "unexpected missing edge in block upon changing else destination. \
                else_edge = {}, old_destination = {}, new_destination = {}",
                edge,
                old_destination,
                new_destination,
            ));
            block_edges[old_destination].swap_remove(edge_index);
            block_edges[new_destination].push(edge);
            true
        });
        Ok(())
    }

    /// Returns `true` if the block is reachable.
    ///
    /// # Note
    ///
    /// - A block is unreachable if it has no predecessors and is sealed.
    /// - A block counts as reachable if it is not (yet) unreachable.
    /// - The entry block is always reachable.
    ///
    /// # Panics
    ///
    /// If the given `block` is invalid for the function builder.
    pub fn is_block_reachable(&self, block: Block) -> bool {
        if block == self.ctx.entry_block {
            return true
        }
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

    /// Returns an instruction builder to appends instructions to the current basic block.
    ///
    /// # Note
    ///
    /// This is an internal implementation that can be called out-of-order.
    /// This is required for it to be called in the local variable declaration
    /// phase to set-up zero-initializers.
    fn ins_impl<'b>(&'b mut self) -> Result<InstructionBuilder<'b, 'a>, Error> {
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

    /// Returns an instruction builder to appends instructions to the current basic block.
    ///
    /// # Errors
    ///
    /// If the current block is already filled.
    pub fn ins<'b>(&'b mut self) -> Result<InstructionBuilder<'b, 'a>, Error> {
        self.ensure_construction_in_order(FunctionBuilderState::Body)?;
        self.ins_impl()
    }

    /// Seals all remaining unsealed blocks.
    fn seal_all_blocks(&mut self) -> Result<(), Error> {
        // Cloning `self.ctx.blocks` is very cheap since the type
        // is nothing but a glorified counter.
        let blocks = self.ctx.blocks.clone();
        for block in blocks.indices() {
            if !self.ctx.block_sealed.get(block) {
                // The block has not yet been sealed.
                self.seal_block(block)?;
            }
        }
        Ok(())
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
        self.seal_all_blocks()?;
        self.ensure_all_blocks_sealed()?;
        self.ensure_all_blocks_filled()?;

        let mut body = FunctionBody {
            blocks: Default::default(),
            block_instrs: Default::default(),
            block_params: Default::default(),
            values: Default::default(),
            value_type: Default::default(),
            value_definition: Default::default(),
            instrs: Default::default(),
            instr_values: Default::default(),
            edges: Default::default(),
            edge_args: Default::default(),
            edge_destination: Default::default(),
        };
        let replace_values = self.initialize_values(&mut body);
        self.initialize_instrs(&replace_values, &mut body);
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
        let is_block_unfilled = |block: &Block| -> bool {
            self.is_block_reachable(*block)
                && !self.ctx.block_filled.get(*block)
        };
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
    fn initialize_values(
        &mut self,
        body: &mut FunctionBody,
    ) -> Replacer<Value> {
        let mut value_replace = <Replacer<Value>>::default();
        let mut dead_params =
            <DefaultComponentMap<Block, HashSet<u32>>>::default();
        // Replace all values and update references for all their associated data.
        for old_value in self.ctx.values.indices() {
            let is_alive = !self.ctx.value_users[old_value].is_empty();
            match is_alive {
                true => {
                    let new_value = body.values.alloc_some(1);
                    body.value_type
                        .insert(new_value, self.ctx.value_type[old_value]);
                    body.value_definition.insert(
                        new_value,
                        self.ctx.value_definition[old_value],
                    );
                    value_replace.insert(old_value, new_value);
                }
                false => {
                    if let ValueDefinition::Param(block, n) =
                        self.ctx.value_definition[old_value]
                    {
                        // The dead value is a block parameter.
                        //
                        // We need to remove the dead block parameter and the arguments
                        // of all incoming edges for it.
                        dead_params[block].insert(n);
                    }
                }
            }
        }
        // Replace all block parameter arguments of all edges.
        body.edges = self.ctx.edges.clone();
        for edge in self.ctx.edges.indices() {
            let edge_destination = self.ctx.edge_dst[edge];
            body.edge_destination.insert(edge, edge_destination);
            for (index, old_arg) in self.ctx.edge_args[edge].iter().enumerate()
            {
                debug_assert!(index < u16::MAX as usize);
                let index = index as u32;
                if dead_params[edge_destination].contains(&index) {
                    continue
                }
                let new_arg = value_replace.get(*old_arg);
                body.edge_args[edge].push(new_arg);
            }
        }
        // Cut away dead block parameters.
        for block in self.ctx.blocks.indices() {
            let dead_params = &dead_params[block];
            for (index, &old_param) in
                self.ctx.block_params[block].iter().enumerate()
            {
                debug_assert!(index < u16::MAX as usize);
                let index = index as u32;
                if dead_params.contains(&index) {
                    continue
                }
                let new_param = value_replace.get(old_param);
                body.block_params[block].push(new_param);
            }
        }
        value_replace
    }

    /// For every instruction returns a `bool` indicating if it is alive within the function body.
    ///
    /// Is only called and used from the `initialize_instrs` procedure.
    ///
    /// # Note
    ///
    /// - This information can later be used to remove dead instructions from the function body.
    /// - An instruction is said to be alive if it is used at least once in any of the basic blocks.
    fn get_alive_instrs(
        &self,
        value_replace: &Replacer<Value>,
    ) -> DefaultComponentBitVec<Instr> {
        let mut is_alive = <DefaultComponentBitVec<Instr>>::default();
        for block in self.ctx.blocks.indices() {
            for instr in self.ctx.block_instrs[block].iter().copied() {
                let actual_outputs = self.ctx.instr_values[instr]
                    .iter()
                    .filter(|&&value| value_replace.try_get(value).is_some())
                    .count();
                let expected_outputs = self.instr_expected_returns(instr);
                is_alive
                    .set(instr, expected_outputs == 0 || actual_outputs > 0);
            }
        }
        is_alive
    }

    /// Returns the number of expected return values for the given instruction.
    fn instr_expected_returns(&self, instr: Instr) -> usize {
        let instruction = &self.ctx.instrs[instr];
        match instruction {
            Instruction::Call(instr) => {
                self.res
                    .get_func_type(instr.func())
                    .expect("missing function type for call")
                    .outputs()
                    .len()
            }
            Instruction::CallIndirect(instr) => {
                self.res
                    .get_type(instr.func_type())
                    .expect("missing function type for call_indirect")
                    .outputs()
                    .len()
            }
            Instruction::Const(_) => 1,
            Instruction::MemoryGrow(_) => 1,
            Instruction::MemorySize(_) => 1,
            Instruction::HeapAddr(_) => 1,
            Instruction::Load(_) => 1,
            Instruction::Store(_) => 0,
            Instruction::Select(instr) => instr.result_types().len(),
            Instruction::Reinterpret(_) => 1,
            Instruction::Terminal(_) => 0,
            Instruction::Int(_) => 1,
            Instruction::Float(_) => 1,
        }
    }

    /// Initializes all instructions of the finalized constructed function body.
    ///
    /// This eliminates all dead instructions that are no longer in use at the end of construction.
    /// This also updates all the data that is associated to the remaining alive instructions in order
    /// to compact their representation in memory.
    fn initialize_instrs(
        &mut self,
        value_replace: &Replacer<Value>,
        body: &mut FunctionBody,
    ) {
        let is_instr_alive = self.get_alive_instrs(value_replace);
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
                // Swap out updated instruction with a placeholder trap instruction.
                // The old instructions will be dropped so whatever we put in there does not matter.
                let instruction = replace(
                    instruction,
                    Instruction::Terminal(TerminalInstr::Unreachable),
                );
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
        // Replace instruction references of block instructions.
        for block in self.ctx.blocks.indices() {
            for old_instr in self.ctx.block_instrs[block].iter().copied() {
                if let Some(new_instr) = instr_replace.try_get(old_instr) {
                    body.block_instrs[block].push(new_instr);
                }
            }
        }
        // Replace value association of all alive values.
        for value in body.values.indices() {
            if let ValueDefinition::Instr(old_instr, _) =
                &mut body.value_definition[value]
            {
                let new_instr = instr_replace.get(*old_instr);
                *old_instr = new_instr;
            }
        }
    }
}
