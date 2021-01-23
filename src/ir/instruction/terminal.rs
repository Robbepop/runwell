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

use crate::ir::primitive::{Block, Value};
use core::fmt::Display;
use derive_more::{Display, From};

/// A terminal SSA instruction.
///
/// Every basic block is required to have a terminal instruction
/// as its last instruction.
#[derive(Debug, Display, From, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TerminalInstr {
    #[display(fmt = "trap")]
    Trap,
    Return(ReturnInstr),
    Br(BranchInstr),
    Ite(IfThenElseInstr),
    BranchTable(BranchTableInstr),
}

impl TerminalInstr {
    /// Replaces all values in the instruction using the replacer.
    ///
    /// Returns `true` if a value has been replaced in the instruction.
    ///
    /// # Note
    ///
    /// By contract the replacer returns `true` if replacement happened.
    pub fn replace_value<F>(&mut self, replace: F) -> bool
    where
        F: FnMut(&mut Value) -> bool,
    {
        match self {
            Self::Trap => false,
            Self::Return(instr) => instr.replace_value(replace),
            Self::Br(_instr) => false,
            Self::Ite(instr) => instr.replace_value(replace),
            Self::BranchTable(instr) => instr.replace_value(replace),
        }
    }
}

/// Returns the returned value from to the function's caller.
#[derive(Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[display(fmt = "ret {}", return_value)]
pub struct ReturnInstr {
    return_value: Value,
}

impl ReturnInstr {
    /// Creates a new return instruction returning the given value.
    pub fn new(return_value: Value) -> Self {
        Self { return_value }
    }

    /// Returns the value that is returned by the instruction.
    pub fn return_value(&self) -> Value {
        self.return_value
    }

    /// Replaces all values in the instruction using the replacer.
    ///
    /// Returns `true` if a value has been replaced in the instruction.
    ///
    /// # Note
    ///
    /// By contract the replacer returns `true` if replacement happened.
    pub fn replace_value<F>(&mut self, mut replace: F) -> bool
    where
        F: FnMut(&mut Value) -> bool,
    {
        replace(&mut self.return_value)
    }
}

/// Unconditionally branches to another basic block.
#[derive(Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[display(fmt = "br {}", target)]
pub struct BranchInstr {
    target: Block,
}

impl BranchInstr {
    /// Creates a new branch instruction branching to the given basic block.
    pub fn new(target: Block) -> Self {
        Self { target }
    }

    /// Returns the target block to jump to.
    pub fn target(&self) -> Block {
        self.target
    }
}

/// Conditionally either branches to `then` or `else` branch depending on `condition`.
#[derive(Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[display(fmt = "if {} then {} else {}", condition, br_then, br_else)]
pub struct IfThenElseInstr {
    condition: Value,
    br_then: Block,
    br_else: Block,
}

impl IfThenElseInstr {
    /// Creates a new if-then-else instruction branching to either `then` or `else` depending on `condition`.
    pub fn new(condition: Value, br_then: Block, br_else: Block) -> Self {
        Self {
            condition,
            br_then,
            br_else,
        }
    }

    /// Returns the condition value of the if-then-else instruction.
    pub fn condition(&self) -> Value {
        self.condition
    }

    /// Returns the block to jump to in case the condition evaluates to `true`.
    pub fn true_target(&self) -> Block {
        self.br_then
    }

    /// Returns the block to jump to in case the condition evaluates to `false`.
    pub fn false_target(&self) -> Block {
        self.br_else
    }

    /// Replaces all values in the instruction using the replacer.
    ///
    /// Returns `true` if a value has been replaced in the instruction.
    ///
    /// # Note
    ///
    /// By contract the replacer returns `true` if replacement happened.
    pub fn replace_value<F>(&mut self, mut replace: F) -> bool
    where
        F: FnMut(&mut Value) -> bool,
    {
        replace(&mut self.condition)
    }
}

/// A branching table mapping indices to branching targets.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BranchTableInstr {
    source: Value,
    default: Block,
    targets: Vec<Block>,
}

impl BranchTableInstr {
    /// Creates a new branching table with the given source, default target and targets.
    pub fn new<I>(source: Value, default: Block, targets: I) -> Self
    where
        I: IntoIterator<Item = Block>,
    {
        Self {
            source,
            default,
            targets: targets.into_iter().collect::<Vec<_>>(),
        }
    }

    /// Replaces all values in the instruction using the replacer.
    ///
    /// Returns `true` if a value has been replaced in the instruction.
    ///
    /// # Note
    ///
    /// By contract the replacer returns `true` if replacement happened.
    pub fn replace_value<F>(&mut self, mut replace: F) -> bool
    where
        F: FnMut(&mut Value) -> bool,
    {
        replace(&mut self.source)
    }
}

impl Display for BranchTableInstr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "br_table source {}, default {}, targets [",
            self.source, self.default
        )?;
        for target in &self.targets {
            write!(f, "{}", target)?;
        }
        write!(f, "]")?;
        Ok(())
    }
}

macro_rules! impl_from_terminal_instr_for_instr {
    ( $( $name:ident ),* $(,)? ) => {
        $(
            impl ::core::convert::From<$name> for crate::ir::instr::Instruction {
                fn from(instr: $name) -> Self {
                    Self::Terminal(crate::ir::instr::TerminalInstr::from(instr))
                }
            }
        )*
    };
}
impl_from_terminal_instr_for_instr! {
    ReturnInstr,
    BranchInstr,
    IfThenElseInstr,
    BranchTableInstr,
}
