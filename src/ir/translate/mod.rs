// Copyright 2019 Robin Freyler
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

mod operator;

#[cfg(test)]
mod tests;

use crate::{
    ir,
    ir::{
        operator::*,
        translate::operator::TranslateOperator,
        BasicBlock,
        Binding,
        BindingGen,
    },
    maybe_std::vec::Vec,
    parse,
    parse::{
        FunctionBody,
        FunctionId,
        FunctionSig,
        LocalVariableId,
        Module,
        Type,
    },
};
use core::num::NonZeroUsize;

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct OperatorId(NonZeroUsize);

/// A translator to encapsulate state used to translate Wasm into `runwell` IR
/// on a function by function level.
#[derive(Debug)]
pub struct FunctionTranslator<'a> {
    /// The underlying Wasm module.
    module: &'a parse::Module,
    /// The blocks used in the already translated parts of the `runwell`
    /// IR function.
    blocks: Vec<BasicBlock>,
    /// The number of already finalized blocks.
    finalized_blocks: usize,
    /// The Wasm execution stack emulated for translation.
    stack: Vec<(Binding, Type)>,
    /// The local stack.
    locals: Vec<LocalBindingEntry>,
    /// The number of function parameters.
    len_parameters: usize,
    /// The binding generator.
    binding_gen: BindingGen,
}

/// A local variable or function parameter SSA binding.
#[derive(Debug, Clone)]
pub struct LocalBindingEntry {
    /// The SSA stack frame binding that refers to the local variable.
    pub binding: Binding,
    /// The type of the local variable.
    pub ty: Type,
}

impl LocalBindingEntry {
    /// Creates a new single local binding entry.
    pub fn new(binding: Binding, ty: Type) -> Self {
        Self { binding, ty }
    }
}

impl<'a> FunctionTranslator<'a> {
    /// Creates a new function translator.
    pub fn new(module: &'a Module) -> Self {
        Self {
            module,
            blocks: Vec::new(),
            finalized_blocks: 0,
            stack: Vec::new(),
            locals: Vec::new(),
            len_parameters: 0,
            binding_gen: BindingGen::new(),
        }
    }

    /// Translate the given function into `runwell` IR.
    pub fn translate(&mut self, fn_id: FunctionId) -> ir::Function {
        let fun = self.module.get_fn(fn_id);
        let sig = fun.sig();
        let body = self
            .module
            .get_fn_body(fn_id)
            .expect("expect internal functions only");
        self.reset();
        self.blocks.push(BasicBlock::new());
        self.initialize_local_bindings(sig, body);
        for op in body.ops() {
            op.translate_operator(self);
        }
        ir::Function::new(core::mem::replace(&mut self.blocks, Vec::new()))
    }

    /// Resets the state of the function translator.
    ///
    /// Required before translating another function.
    fn reset(&mut self) {
        self.blocks.clear();
        self.finalized_blocks = 0;
        self.stack.clear();
        self.binding_gen.reset();
    }

    /// Returns the current block to push operators.
    fn current_block(&self) -> &BasicBlock {
        assert!(self.finalized_blocks < self.blocks.len());
        &self.blocks[self.finalized_blocks]
    }

    /// Returns the current block to push operators.
    fn current_block_mut(&mut self) -> &mut BasicBlock {
        assert!(self.finalized_blocks < self.blocks.len());
        &mut self.blocks[self.finalized_blocks]
    }

    /// Initializes the local bindings for the function parameters and
    /// the local variables of the function.
    ///
    /// # Note
    ///
    /// For every function the first `n` SSA bindings always refer to the
    /// `n` function parameters, the next `m` SSA bindings always refer to the
    /// local variables of the function's stack frame.
    ///
    /// For simplicity reasons we always store and load instead of using the
    /// direct bindings because Wasm allows to mutate all local variables
    /// and function parameters inplace.
    ///
    /// In later optimization passes we can then optimize those superflous
    /// store and load operations and replace them with direct accesses ands
    /// phi operators.
    ///
    /// # Example
    ///
    /// For a function with 2 i32 parameters and 2 i64 local variables we
    /// generate the following sequence of operators.
    /// Note that `%0` and `%1` refer to function parameters 0 and 1
    /// respectively.
    ///
    /// ```no_compile
    /// ;; %0 is given and refers to function parameter 0
    /// ;; %1 is given and refers to function parameter 1
    /// %2 <- local i32 1 ;; function parameter 0 (local_id 0)
    /// %3 <- local i32 1 ;; function parameter 1 (local_id 1)
    /// %4 <- local i64 1 ;; local variable 0 (local_id 2)
    /// %5 <- local i64 1 ;; local variable 1 (local_id 3)
    /// store local i32 %0 at %2 align 2 ;; initialize function parameter 0
    /// store local i32 %1 at %3 align 2 ;; initialize function parameter 1
    /// ```
    ///
    /// Note that we directly initialize the function parameter stack frame
    /// bindings, however, we do not initialize the pure local variables of
    /// the function.
    fn initialize_local_bindings(
        &mut self,
        sig: &FunctionSig,
        body: &FunctionBody,
    ) {
        self.len_parameters = sig.inputs().len();
        let mut srcs = Vec::new();
        let mut locals = Vec::new();
        // Initialize function parameter bindings.
        for _ in sig.inputs() {
            srcs.push(self.binding_gen.gen());
        }
        // Initialize function parameter stack frame placeholders.
        for ty in sig.inputs() {
            let binding = self.push_op(LocalOp::single(ty.clone()), ty.clone());
            locals.push(LocalBindingEntry::new(binding, ty.clone()));
        }
        // Initialize function local variable bindings.
        for (n, ty) in body.locals() {
            core::iter::repeat(ty)
                .take(*n)
                .for_each(|ty| self.push_local_binding(ty.clone()));
        }
        // Store function parameters into their respective stack frame.
        for (local, src) in locals.iter().zip(srcs.iter()) {
            self.push_unbinded_op(StoreOp::store_local(
                local.ty.clone(),
                local.binding,
                *src,
            ));
        }
        self.locals = locals;
    }

    /// Returns the local entry of the local variable or function parameter.
    pub fn get_local_binding(&self, id: LocalVariableId) -> &LocalBindingEntry {
        use crate::parse::Identifier as _;
        &self.locals[id.get()]
    }

    /// Pushes a new basic block to the block stack.
    fn push_block(&mut self) {
        self.blocks.push(BasicBlock::new());
    }

    /// Finalizes the current block.
    fn finalize_block(&mut self) {
        self.finalized_blocks += 1;
    }

    /// Pushes the binding to the given operator of given type to the table.
    ///
    /// Does not push the binding to the emulation stack.
    /// This is mainly used to initialize locals and function parameters.
    pub fn push_local_binding(&mut self, ty: Type) {
        let binding = self.push_op(LocalOp::single(ty.clone()), ty.clone());
        self.locals.push(LocalBindingEntry::new(binding, ty));
    }

    /// Pushes the operator to the current block and returns its binding.
    ///
    /// # Note
    ///
    /// - Requires an additional type parameter in order to push to typed
    ///   emulation stack.
    /// - Use [`push_unbinded_op`] to avoid generating bindings for example
    ///   for terminal operators.
    pub fn push_op<O>(&mut self, op: O, ty: Type) -> Binding
    where
        O: Into<ir::Operator>,
    {
        self.push_unbinded_op(op);
        let binding = self.binding_gen.gen();
        self.stack_push(binding, ty);
        binding
    }

    /// Pushes the operator to the current block.
    ///
    /// # Note
    ///
    /// Does not create a binding.
    /// Use this for terminal operators, store operator, etc.
    pub fn push_unbinded_op<O>(&mut self, op: O)
    where
        O: Into<ir::Operator>,
    {
        self.current_block_mut().push_op(op);
    }

    /// Pops the top binding and type from the emulation stack.
    pub fn stack_pop(&mut self) -> (Binding, Type) {
        self.stack.pop().expect("cannot be empty if Wasm is valid")
    }

    /// Returns the top element on the emulation stack.
    pub fn stack_last(&self) -> &(Binding, Type) {
        self.stack.last().expect("cannot be empty if Wasm is valid")
    }

    /// Pushes the binding with the associated type to the emulation stack.
    pub fn stack_push(&mut self, binding: Binding, ty: Type) {
        self.stack.push((binding, ty))
    }
}
