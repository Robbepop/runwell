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

use super::VariableAccess;
use crate::{FunctionBuilderError, IrError};
use core::fmt;
use derive_more::From;
use entity::{
    secondary::map::Entry,
    ComponentMap,
    DisplayHook,
    EntityArena,
    Idx,
    RawIdx,
};
use ir::primitive::{Block, Type, Value};

/// A variable entity of the Runwell IR.
///
/// Represents a unique variable from the input language.
/// Used to translate a foreign language into SSA form.
///
/// # Note
///
/// In the context of Wasm such variables are local variables that can
/// be operated on using `local.set`, `local.get` and `local.tee`. Those
/// operations are not in SSA form and we use the `Variable` index type
/// in order to translate them to their SSA forms.
///
/// # Example
///
/// Since in Wasm all local variables in a function are uniquely identified
/// by their local index we can simply take this local index and map it
/// onto the `Variable` index space.
#[derive(Debug, Default)]
pub struct VariableEntity;

/// The unique index of a basic block entity of the Runwell IR.
pub type Variable = Idx<VariableEntity>;

impl DisplayHook for VariableEntity {
    fn fmt(idx: Variable, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "var({})", idx.into_raw())
    }
}

/// Used to translate variables of some source language into Runwell IR SSA values.
///
/// All variables are required to be declared before their first use and they
/// are also required to be assigned to some value before they are read.
///
///
/// Upon first variable write the declarations array is traversed using binary
/// search and the associated declaration is inserted into the variable definitions
/// map for faster query upon the next time the same variable is written to again.
///
/// # Execution Time
///
/// ## Variable Declarations
///
/// All variable declarations have a constant execution time of O(1).
///
/// ## Variable Writes
///
/// The first time a variable is assigned that has been declared with a shared
/// declaration the `var_to_type` array is traversed using binary search taking
/// roughly O(log(D)) where D is the number of shared variable declarations.
/// Due to caching this occures only once per unique variable assignment.
/// Therefore the worst-case is triggered only whenever a shared declared variable
/// is only ever assigned to a new value once in the entire function.
/// The total worst-case execution time is O(A * log(D)) where A is the number of
/// unique variable assignments and D is the number of shared variable declarations.
///
/// ## Variable Reads
///
/// Both `read_var` as well as `VariableDefinitions::for_block` have a constant
/// execution time of O(1). However, reading the value of a variable during translation
/// might call `VariableDefinitions::for_block` multiple times for each recursive
/// predecessor of the current basic block. Therefore the execution time of reading
/// a variable is in O(P) where P is the set of predecessors of the current basic block
/// in the worst case.
///
/// # Dev. Note
///
/// As stated above the total worst-case execution time for variable assignments is in
/// O(A * log(D)) where A is the number of unique variable assignments and D is the number
/// of shared variable declarations.
/// In typical Wasm binaries D is very small leading to linear translation time.
/// Due to caching if A and D are equal the execution time is only O(A).
/// The worst case is if D is equal to A/2 with a worst-case execution time of
/// O(A * log(A/2)). The worst-case can be easily eliminated by requiring that types of variable
/// declarations in a function are required to be unique. As stated above this is already
/// true for typical generated Wasm binaries, e.g. in case of LLVM translations.
#[derive(Debug, Default)]
pub struct VariableTranslator {
    /// The amount of declared variables.
    vars: EntityArena<VariableEntity>,
    /// For every declaration of multiple variables their shared declaration is appended
    /// to this vector.
    ///
    /// # Note
    ///
    /// Upon first variable write the declarations array is traversed using binary
    /// search and the associated declaration is inserted into the variable definitions
    /// map for faster query upon the next time the same variable is written to again.
    var_to_type: VariableDeclarations,
    /// Entries for variables definitions and their declared types.
    ///
    /// # Note
    ///
    /// This map is initialized lazily during the first assignment of each variable.
    var_to_defs: ComponentMap<Variable, VariableDefinitions>,
}

/// The lazily declared list of variable declarations.
#[derive(Debug, Default)]
struct VariableDeclarations {
    /// For every declaration of multiple variables their shared declaration is appended
    /// to this vector.
    ///
    /// # Note
    ///
    /// Upon first variable write the declarations array is traversed using binary
    /// search and the associated declaration is inserted into the variable definitions
    /// map for faster query upon the next time the same variable is written to again.
    var_to_type: Vec<VariableDecl>,
}

impl VariableDeclarations {
    /// Registers another lazily declared variable declaration.
    pub fn push(&mut self, decl: VariableDecl) {
        self.var_to_type.push(decl);
    }

    /// Returns the declared type of the variable.
    ///
    /// # Note
    ///
    /// Returns the type of the last declared variable in case the variable is out of bounds.
    /// It is the callers responsibility to never call this function with an invalid variable.
    pub fn get_var_type(&self, var: Variable) -> Type {
        let target = var.into_raw();
        match self
            .var_to_type
            .binary_search_by(|decl| target.cmp(&decl.first_idx))
        {
            Ok(index) => self.var_to_type[index].ty,
            Err(index) => self.var_to_type[index - 1].ty,
        }
    }
}

/// Space efficient storage for variable declarations and their declared types.
///
/// Used for storing shared information about variables that have been declared
/// together using [`VariableTranslator::declare_variables`] for more than just
/// a single variable.
#[derive(Debug)]
struct VariableDecl {
    /// Denotes the first variable index of the variable declarations that share
    /// the same type. All those declared variables have adjacent indices.
    first_idx: RawIdx,
    /// The shared type of the variable declaration.
    ty: Type,
}

/// The entry for the definitions and the type of a declared variable.
///
/// Stores all definitions for all basic blocks for the variable
/// as well as the type of the variable's declaration.
#[derive(Debug)]
pub struct VariableDefinitions {
    /// All definitions for the variable per basic block.
    block_defs: ComponentMap<Block, Value>,
    /// The type of the variable given upon its declaration.
    ty: Type,
}

impl VariableDefinitions {
    /// Create a new entry for variable definitions.
    fn new(ty: Type) -> Self {
        Self {
            block_defs: ComponentMap::default(),
            ty,
        }
    }

    /// Returns the type of the variable definition.
    pub fn ty(&self) -> Type {
        self.ty
    }

    /// Returns the variable's definitions for every basic block.
    pub fn definitions(&self) -> VariableDefinitionPerBlock {
        VariableDefinitionPerBlock {
            defs: &self.block_defs,
        }
    }
}

/// The value definitions of a variable for every basic block.
#[derive(Debug, Copy, Clone, From)]
pub struct VariableDefinitionPerBlock<'a> {
    defs: &'a ComponentMap<Block, Value>,
}

impl<'a> VariableDefinitionPerBlock<'a> {
    /// Returns the value written to the variable for the given block if any.
    pub fn for_block(self, block: Block) -> Option<Value> {
        self.defs.get(block).copied()
    }
}

impl VariableTranslator {
    /// Ensures that the variable has been declared.
    ///
    /// # Errors
    ///
    /// If the variable has not been declared.
    fn ensure_declared(
        &self,
        var: Variable,
        access: VariableAccess,
    ) -> Result<(), IrError> {
        if !self.vars.contains_key(var) {
            return Err(FunctionBuilderError::MissingDeclarationForVariable {
                variable: var,
                access,
            })
            .map_err(Into::into)
        }
        Ok(())
    }

    /// Ensures that the type of the variable declaration matches the type of the new value.
    ///
    /// # Errors
    ///
    /// If the type of the new value does not match the type of the variable declaration.
    fn ensure_types_match<F>(
        var: Variable,
        new_value: Value,
        declared_type: Type,
        value_to_type: F,
    ) -> Result<(), IrError>
    where
        F: FnOnce() -> Type,
    {
        let value_type = value_to_type();
        if declared_type != value_type {
            return Err(FunctionBuilderError::UnmatchingVariableType {
                variable: var,
                value: new_value,
                declared_type,
                value_type,
            })
            .map_err(Into::into)
        }
        Ok(())
    }

    /// Declares an amount of variables that share the same type.
    ///
    /// A variable is required to be declared before reading or writing to it
    /// using `VariableTranslator::read_var` and `VariableTranslator::write_var`.
    ///
    /// # Errors
    ///
    /// If there are more than 2^31 variable declarations.
    pub fn declare_vars(
        &mut self,
        amount: u32,
        ty: Type,
    ) -> Result<(), IrError> {
        let first_idx = self.vars.alloc_default(amount as usize);
        if self.vars.len() >= u32::MAX as usize {
            return Err(FunctionBuilderError::TooManyVariableDeclarations)
                .map_err(Into::into)
        }
        // Future task: We should be able to get rid of the push if `amount == 1` while preserving correctness.
        self.var_to_type.push(VariableDecl {
            first_idx: first_idx.into_raw(),
            ty,
        });
        if amount == 1 {
            // As an optimization we directly initialize the definition of the
            // variable to avoid the binary search for it upon its first assignmnet.
            let old_def = self
                .var_to_defs
                .insert(first_idx, VariableDefinitions::new(ty));
            debug_assert!(old_def.is_none());
        }
        Ok(())
    }

    /// Assigns a new value to the variable.
    ///
    /// - The variable assignment is with respect to the given basic block.
    /// - The `value_to_type` closure is used to check whether the type of the new value
    ///   matches the type given at variable declaration.
    ///
    /// # Note
    ///
    /// Initializes the variable entry if it has never been read or written before.
    ///
    /// # Errors
    ///
    /// - If the variable has not been declared before.
    /// - If the type of the new value does not match the type of the variable declaration.
    pub fn write_var<F>(
        &mut self,
        var: Variable,
        new_value: Value,
        block: Block,
        value_to_type: F,
    ) -> Result<(), IrError>
    where
        F: FnOnce() -> Type,
    {
        self.ensure_declared(var, VariableAccess::Write(new_value))?;
        let Self {
            var_to_type,
            var_to_defs,
            ..
        } = self;
        match var_to_defs.entry(var) {
            Entry::Occupied(occupied) => {
                let declared_type = occupied.get().ty;
                Self::ensure_types_match(
                    var,
                    new_value,
                    declared_type,
                    value_to_type,
                )?;
                occupied.into_mut().block_defs.insert(block, new_value);
            }
            Entry::Vacant(vacant) => {
                let declared_type = var_to_type.get_var_type(var);
                Self::ensure_types_match(
                    var,
                    new_value,
                    declared_type,
                    value_to_type,
                )?;
                vacant.insert(VariableDefinitions::new(declared_type));
            }
        }
        Ok(())
    }

    /// Returns all definitions per basic block of the variable.
    ///
    /// # Note
    ///
    /// Initializes the variable entry if it has never been read or written before.
    ///
    /// # Errors
    ///
    /// - If the variable has not been declared, yet.
    pub fn get(
        &mut self,
        var: Variable,
    ) -> Result<&VariableDefinitions, IrError> {
        self.ensure_declared(var, VariableAccess::Read)?;
        let Self {
            var_to_type,
            var_to_defs,
            ..
        } = self;
        let definition = var_to_defs.entry(var).or_insert_with(|| {
            let declared_type = var_to_type.get_var_type(var);
            VariableDefinitions::new(declared_type)
        });
        Ok(definition)
    }
}
