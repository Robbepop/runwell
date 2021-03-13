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
use ir::primitive::Block;
use module::primitive::Instr;

/// A control flow frame can be a `Block` a `Loop` or an `If` Wasm control instruction.
#[derive(Debug, Clone)]
pub enum ControlFlowFrame {
    If(IfControlFrame),
    Block(BlockControlFrame),
    Loop(LoopControlFrame),
}

/// Control flow frame for a Wasm `Block`.
#[derive(Debug, Clone)]
pub struct BlockControlFrame {
    pub len_inputs: usize,
    pub len_outputs: usize,
    pub original_stack_size: usize,
    pub destination: Option<Block>,
}

/// Control flow frame for a Wasm `Loop` construct.
#[derive(Debug, Clone)]
pub struct LoopControlFrame {
    pub len_inputs: usize,
    pub len_outputs: usize,
    pub original_stack_size: usize,
    pub loop_exit: Option<Block>,
    pub loop_header: Block,
}

/// Control flow frame for a Wasm `If`, `Else`, `End` construct.
#[derive(Debug, Clone)]
pub struct IfControlFrame {
    pub len_inputs: usize,
    pub len_outputs: usize,
    pub original_stack_size: usize,
    pub exit_is_branched_to: bool,
    pub exit_block: Block,
    pub else_data: ElseData,
    pub block_type: WasmBlockType,
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

/// The optional `else` part of an `if` control flow frame.
///
/// An `if` control flow frame starts with `NoElse` and eventually updates
/// to `WithElse` when encountering the optional `else` branch.
/// Sometimes it is possible to infer that an `if` control flow frame requires
/// an `else` block by inspecting the `if` signature. In these cases,
/// we pre-allocate the `else` block.
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
    /// In these cases, we pre-allocate the `else` block.
    WithElse {
        /// This is the `else` block.
        else_block: Block,
    },
}

/// Helper methods for the control stack objects.
impl ControlFlowFrame {
    /// Returns the number of output values of the control flow frame.
    pub fn len_outputs(&self) -> usize {
        match self {
            Self::If(frame) => frame.len_outputs,
            Self::Block(frame) => frame.len_outputs,
            Self::Loop(frame) => frame.len_outputs,
        }
    }

    /// Returns the number of input values of the control flow frame.
    pub fn len_inputs(&self) -> usize {
        match self {
            Self::If(frame) => frame.len_inputs,
            Self::Block(frame) => frame.len_inputs,
            Self::Loop(frame) => frame.len_inputs,
        }
    }

    /// Returns the block that follows the control flow frame if any.
    ///
    /// # Note
    ///
    /// This returns `None` in case of `Block` control flow frames that
    /// have not yet seen branches to them.
    pub fn following_code(&self) -> Option<Block> {
        match self {
            Self::If(frame) => Some(frame.exit_block),
            Self::Block(frame) => frame.destination,
            Self::Loop(frame) => frame.loop_exit,
        }
    }

    /// Returns the destination block for branches for the control flow frame if any.
    ///
    /// # Note
    ///
    /// This returns `None` in case of `Block` control flow frames that
    /// have not yet seen branches to them.
    ///
    /// TODO: Decide if we need this API.
    pub fn br_destination(&self) -> Option<Block> {
        match self {
            Self::If(frame) => Some(frame.exit_block),
            Self::Block(frame) => frame.destination,
            Self::Loop(frame) => Some(frame.loop_header),
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
        }
    }

    /// Returns `true` if the control frame is a Wasm `Loop`.
    pub fn is_loop(&self) -> bool {
        matches!(self, Self::Loop(_))
    }

    /// Returns `true` if there have been branches to the exit block of the control frame.
    pub fn exit_is_branched_to(&self) -> bool {
        match self {
            Self::If(frame) => frame.exit_is_branched_to,
            Self::Block(frame) => frame.destination.is_some(),
            Self::Loop(frame) => false,
        }
    }
}
