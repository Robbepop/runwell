use crate::ir::{Op, TerminalOp};

/// The unique identifier of a function.
///
/// The underlying definition (data) of a function can be accessed
/// through its function ID and the associated Wasm module.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct FunctionId(usize);

/// A basic block within a function.
///
/// Every basic block has a parent function which is refers to through its ID.
/// They contain the ordered list of operations that they perform wholefully
/// upon being executed and are guaranteed to have an ending terminal operation
/// at the end.
pub struct BasicBlock {
    /// The parent function ID that encloses this basic block.
    parent: FunctionId,
    /// The non-empty ordered list of operations
    /// with a terminal operation at the end.
    ops: Vec<Op>,
}

impl BasicBlock {
    /// Returns the ID of the parent function of `self`.
    pub fn parent(&self) -> FunctionId {
        self.parent
    }

    /// Returns an iterator over the operations of the basic block.
    pub fn ops(&self) -> impl Iterator<Item = &Op> {
        self.ops.iter()
    }

    /// Returns a mutable iterator over the operations of the basic block.
    pub fn ops_mut(&mut self) -> impl Iterator<Item = &mut Op> {
        self.ops.iter_mut()
    }

    /// Returns a shared reference to the terminal operation.
    pub fn terminal(&self) -> &TerminalOp {
        let term = self
            .ops
            .last()
            .expect("unexpected empty list of operations in basic block");
        match term {
            Op::Terminal(terminal_op) => terminal_op,
            _ => {
                panic!(
                "unexpected non-terminal operation at the end of a basic block"
            )
            }
        }
    }

    /// Returns an exclusive reference to the terminal operation.
    pub fn terminal_mut(&mut self) -> &mut TerminalOp {
        let term = self
            .ops
            .last_mut()
            .expect("unexpected empty list of operations in basic block");
        match term {
            Op::Terminal(terminal_op) => terminal_op,
            _ => {
                panic!(
                "unexpected non-terminal operation at the end of a basic block"
            )
            }
        }
    }
}
