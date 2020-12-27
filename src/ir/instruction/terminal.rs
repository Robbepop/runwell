// Copyright 2020 Robin Freyler
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

use crate::ir::{BasicBlockId, Value};
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
}

/// Unconditionally branches to another basic block.
#[derive(Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[display(fmt = "br {}", target)]
pub struct BranchInstr {
    target: BasicBlockId,
}

impl BranchInstr {
    /// Creates a new branch instruction branching to the given basic block.
    pub fn new(target: BasicBlockId) -> Self {
        Self { target }
    }
}

/// Conditionally either branches to `then` or `else` branch depending on `condition`.
#[derive(Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[display(
    fmt = "ite condition {}, then {}, else {}",
    condition,
    br_then,
    br_else
)]
pub struct IfThenElseInstr {
    condition: Value,
    br_then: BasicBlockId,
    br_else: BasicBlockId,
}

impl IfThenElseInstr {
    /// Creates a new if-then-else instruction branching to either `then` or `else` depending on `condition`.
    pub fn new(
        condition: Value,
        br_then: BasicBlockId,
        br_else: BasicBlockId,
    ) -> Self {
        Self {
            condition,
            br_then,
            br_else,
        }
    }
}

/// A branching table mapping indices to branching targets.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BranchTableInstr {
    source: Value,
    default: BasicBlockId,
    targets: Vec<BasicBlockId>,
}

impl BranchTableInstr {
    /// Creates a new branching table with the given source, default target and targets.
    pub fn new<I>(source: Value, default: BasicBlockId, targets: I) -> Self
    where
        I: IntoIterator<Item = BasicBlockId>,
    {
        Self {
            source,
            default,
            targets: targets.into_iter().collect::<Vec<_>>(),
        }
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
