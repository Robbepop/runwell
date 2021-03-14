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

use super::block::WasmBlockType;
use ir::primitive::{Block, Type};
use module::{primitive::Instr, ModuleResources};

/// A control flow frame can be a `Block` a `Loop` or an `If` Wasm control instruction.
#[derive(Debug, Clone)]
pub enum ControlFlowFrame {
    Body(FunctionBodyFrame),
    If(IfControlFrame),
    Block(BlockControlFrame),
    Loop(LoopControlFrame),
}

/// Control flow frame to guard the entire function body.
///
/// # Note
///
/// This is mainly used to provide a proper stop guard for
/// the expected `End` operator at the end of each Wasm
/// function body.
///
/// This control frame must not occur elsewhere on the
/// control stack but once at the beginning.
#[derive(Debug, Copy, Clone)]
pub struct FunctionBodyFrame {
    pub block_type: WasmBlockType,
}

/// Control flow frame for a Wasm `Block`.
#[derive(Debug, Clone)]
pub struct BlockControlFrame {
    /// The non-SSA input and output types of the control frame.
    pub block_type: WasmBlockType,
    /// The value stack size upon entering the control frame.
    pub original_stack_size: usize,
    /// The block that is branched to upon encountering `End` operator.
    pub following_block: Block,
    /// Is `true` if there is at least one branch to this control frame.
    pub is_branched_to: bool,
}

impl BlockControlFrame {
    /// Creates a new `Block` Wasm control frame.
    pub fn new(
        block_type: WasmBlockType,
        original_stack_size: usize,
        following_block: Block,
    ) -> Self {
        Self {
            block_type,
            original_stack_size,
            following_block,
            is_branched_to: false,
        }
    }
}

/// Control flow frame for a Wasm `Loop` construct.
#[derive(Debug, Clone)]
pub struct LoopControlFrame {
    /// The non-SSA input and output types of the control frame.
    pub block_type: WasmBlockType,
    /// The value stack size upon entering the control frame.
    pub original_stack_size: usize,
    /// The loop's exit block.
    pub loop_exit: Block,
    /// The loop's header block.
    pub loop_header: Block,
}

impl LoopControlFrame {
    /// Creates a new `Loop` Wasm control frame.
    pub fn new(
        block_type: WasmBlockType,
        original_stack_size: usize,
        loop_header: Block,
        loop_exit: Block,
    ) -> Self {
        Self {
            block_type,
            original_stack_size,
            loop_header,
            loop_exit,
        }
    }
}

/// Control flow frame for a Wasm `If`, `Else`, `End` construct.
#[derive(Debug, Clone)]
pub struct IfControlFrame {
    /// The non-SSA input and output types of the control frame.
    pub block_type: WasmBlockType,
    /// The value stack size upon entering the control frame.
    pub original_stack_size: usize,
    /// Is `true` if there is at least one branch to this control frame.
    pub exit_is_branched_to: bool,
    /// The block that contains the code after the if-then-else instructions.
    pub exit_block: Block,
    /// Used to establish the else block when `Else` operator is encountered.
    pub else_data: ElseData,
    /// Was the head of the `if` reachable?
    pub head_is_reachable: bool,
    /// What was the reachability at the end of the consequent?
    ///
    /// This is `None` until we're finished translating the consequent, and
    /// is set to `Some` either by hitting an `else` when we will begin
    /// translating the alternative, or by hitting an `end` in which case
    /// there is no alternative.
    pub consequent_ends_reachable: Option<bool>,
    /* Note: no need for `alternative_ends_reachable` because that is just
     * `state.reachable` when we hit the `end` in the `if .. else .. end`. */
}

impl IfControlFrame {
    /// Creates a new `If` Wasm control frame.
    pub fn new(
        block_type: WasmBlockType,
        original_stack_size: usize,
        exit_block: Block,
        else_data: ElseData,
        head_is_reachable: bool,
    ) -> Self {
        Self {
            block_type,
            original_stack_size,
            exit_block,
            else_data,
            head_is_reachable,
            exit_is_branched_to: false,
            consequent_ends_reachable: None,
        }
    }
}

/// The optional `else` part of an `if` control flow frame.
///
/// An `if` control flow frame starts with `NoElse` and eventually updates
/// to `WithElse` when encountering the optional `else` branch.
/// Sometimes it is possible to infer that an `if` control flow frame requires
/// an `else` block by inspecting the `if` signature. In these cases,
/// we preallocate the `else` block.
#[derive(Debug, Copy, Clone)]
pub enum ElseData {
    /// The `if` does not already have an `else` block.
    ///
    /// This doesn't mean that it will never have an `else`, just that we
    /// haven't seen it yet.
    NoElse {
        /// If we discover that we need an `else` block, this is the jump
        /// instruction that needs to be fixed up to point to the new `else`
        /// block rather than the destination block after the `if...end`.
        branch_instr: Instr,
    },
    /// We have already allocated an `else` block.
    ///
    /// Usually we don't know whether we will hit an `if .. end` or an `if
    /// .. else .. end`, but sometimes we can tell based on the block's type
    /// signature that the signature is not valid if there isn't an `else`.
    /// In these cases, we preallocate the `else` block.
    WithElse {
        /// This is the `else` block.
        else_block: Block,
    },
}

/// Helper methods for the control stack objects.
impl ControlFlowFrame {
    /// Returns the number of input values of the control flow frame.
    pub fn inputs<'a, 'b, 'c>(&'a self, res: &'b ModuleResources) -> &'c [Type]
    where
        'a: 'c,
        'b: 'c,
    {
        let block_type = match self {
            Self::If(frame) => &frame.block_type,
            Self::Block(frame) => &frame.block_type,
            Self::Loop(frame) => &frame.block_type,
            Self::Body(frame) => &frame.block_type,
        };
        block_type.inputs(res)
    }

    /// Returns the number of output values of the control flow frame.
    pub fn outputs<'a, 'b, 'c>(&'a self, res: &'b ModuleResources) -> &'c [Type]
    where
        'a: 'c,
        'b: 'c,
    {
        let block_type = match self {
            Self::If(frame) => &frame.block_type,
            Self::Block(frame) => &frame.block_type,
            Self::Loop(frame) => &frame.block_type,
            Self::Body(frame) => &frame.block_type,
        };
        block_type.outputs(res)
    }

    /// Returns the block that follows the control flow frame if any.
    ///
    /// # Note
    ///
    /// This returns `None` in case of `Block` control flow frames that
    /// have not yet seen branches to them.
    pub fn following_code(&self) -> Block {
        match self {
            Self::If(frame) => frame.exit_block,
            Self::Block(frame) => frame.following_block,
            Self::Loop(frame) => frame.loop_exit,
            Self::Body(_) => {
                unreachable!(
                    "a function body control frame cannot have following code"
                )
            }
        }
    }

    /// Returns the destination block for branches for the control flow frame if any.
    ///
    /// # Note
    ///
    /// This returns `None` in case of `Block` control flow frames that
    /// have not yet seen branches to them.
    pub fn branch_destination(&self) -> Block {
        match self {
            Self::If(frame) => frame.exit_block,
            Self::Block(frame) => frame.following_block,
            Self::Loop(frame) => frame.loop_header,
            Self::Body(_) => {
                unreachable!(
                    "a function body control frame cannot have a branch destination"
                )
            }
        }
    }

    /// Returns the original value stack size before the control flow frame.
    ///
    /// # Note
    ///
    /// This is a private helper method. Use `truncate_value_stack_to_else_params()`
    /// or `truncate_value_stack_to_original_size()` to restore value-stack state.
    pub fn original_stack_size(&self) -> usize {
        match self {
            Self::If(frame) => frame.original_stack_size,
            Self::Block(frame) => frame.original_stack_size,
            Self::Loop(frame) => frame.original_stack_size,
            Self::Body(_) => 0,
        }
    }

    /// Returns `true` if the control frame is a Wasm `Loop`.
    pub fn is_loop(&self) -> bool {
        matches!(self, Self::Loop(_))
    }

    /// Returns the number of arguments required for a branch to the frame.
    pub fn len_branch_args(&self, res: &ModuleResources) -> usize {
        if self.is_loop() {
            self.inputs(res).len()
        } else {
            self.outputs(res).len()
        }
    }

    /// Returns `true` if the control frame is the implicit function body label.
    ///
    /// # Note
    ///
    /// Branching to this label has the same effect as returning from the function.
    pub fn is_func_body(&self) -> bool {
        matches!(self, Self::Body(_))
    }

    /// Returns `true` if there have been branches to the exit block of the control frame.
    ///
    /// # Note
    ///
    /// This flag could be used in some cases to prevent creating of superfluous blocks.
    #[allow(dead_code)]
    pub fn exit_is_branched_to(&self) -> bool {
        match self {
            Self::If(frame) => frame.exit_is_branched_to,
            Self::Block(frame) => frame.is_branched_to,
            Self::Loop(frame) => {
                // A branch to a loop control frame will always branch
                // to the loop header and never to the loop exit.
                // Therefore this is always `false`.
                false
            }
            Self::Body(_) => false,
        }
    }

    /// Tells the frame that it has been branched to if possible.
    pub fn set_branched_to_exit(&mut self) {
        match self {
            Self::If(frame) => frame.exit_is_branched_to = true,
            Self::Block(frame) => frame.is_branched_to = true,
            Self::Loop(frame) => {
                // A loop exit block is always branched to so we don't store state.
            }
            Self::Body(_) => {
                // Branching to the outermost implicit label (function body)
                // is similar to a return statement.
            }
        }
    }
}
