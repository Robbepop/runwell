
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct TypeId(usize);

pub struct Function {
    /// The globally unique identifier of the function.
    id: FunctionId,
    /// The signature of the function.
    signature: FunctionSig,
    /// The used local variable declarations of the function.
    locals: FunctionLocals,
    /// The non-empty set of basic blocks that form the operations
    /// performance by the function seen as a whole.
    /// The first basic block (entry block) is special in that it is executed
    /// directly upon executing the function itself.
    /// Also it must not have precedessors which implies
    /// that it cannot contain PHI operations.
    blocks: Vec<BasicBlock>,
}

impl Function {
    /// Returns the entry block of the function.
    pub fn entry_block(&self) -> &BasicBlock {
        // This can never fail since `blocks` is guaranteed to be non-empty.
        &self.blocks[0]
    }
}
