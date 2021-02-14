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

use super::{CallInstr, SmallBlockVec};
use crate::{
    primitive::{Block, Func, Value},
    VisitValues,
    VisitValuesMut,
};
use core::fmt::{self, Display};
use derive_more::{Display, From};

/// A tail call instruction.
#[derive(Debug, From, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct TailCallInstr {
    /// The underlying call instruction.
    instr: CallInstr,
}

impl Display for TailCallInstr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "tail{}", self.instr)
    }
}

impl TailCallInstr {
    /// Creates a new tail call instruction to call the indexed function using the given parameters.
    pub fn new<I>(func: Func, call_params: I) -> Self
    where
        I: IntoIterator<Item = Value>,
    {
        Self {
            instr: CallInstr::new(func, call_params),
        }
    }

    /// Returns the called function index.
    pub fn func(&self) -> Func {
        self.instr.func()
    }

    /// Returns the function call parameters.
    pub fn params(&self) -> &[Value] {
        self.instr.params()
    }
}

impl VisitValues for TailCallInstr {
    fn visit_values<V>(&self, visitor: V)
    where
        V: FnMut(Value) -> bool,
    {
        self.instr.visit_values(visitor)
    }
}

impl VisitValuesMut for TailCallInstr {
    fn visit_values_mut<V>(&mut self, visitor: V)
    where
        V: FnMut(&mut Value) -> bool,
    {
        self.instr.visit_values_mut(visitor)
    }
}

/// A terminal SSA instruction.
///
/// Every basic block is required to have a terminal instruction
/// as its last instruction.
#[derive(Debug, Display, From, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum TerminalInstr {
    #[display(fmt = "trap")]
    Trap,
    Return(ReturnInstr),
    Br(BranchInstr),
    Ite(IfThenElseInstr),
    TailCall(TailCallInstr),
    BranchTable(BranchTableInstr),
}

impl VisitValues for TerminalInstr {
    fn visit_values<V>(&self, visitor: V)
    where
        V: FnMut(Value) -> bool,
    {
        match self {
            Self::Trap => (),
            Self::Return(instr) => instr.visit_values(visitor),
            Self::Br(_instr) => (),
            Self::Ite(instr) => instr.visit_values(visitor),
            Self::TailCall(instr) => instr.visit_values(visitor),
            Self::BranchTable(instr) => instr.visit_values(visitor),
        }
    }
}

impl VisitValuesMut for TerminalInstr {
    fn visit_values_mut<V>(&mut self, visitor: V)
    where
        V: FnMut(&mut Value) -> bool,
    {
        match self {
            Self::Trap => (),
            Self::Return(instr) => instr.visit_values_mut(visitor),
            Self::Br(_instr) => (),
            Self::Ite(instr) => instr.visit_values_mut(visitor),
            Self::TailCall(instr) => instr.visit_values_mut(visitor),
            Self::BranchTable(instr) => instr.visit_values_mut(visitor),
        }
    }
}

/// Returns the returned value from to the function's caller.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct ReturnInstr {
    return_values: Vec<Value>,
}

impl fmt::Display for ReturnInstr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ret [")?;
        if let Some((first, rest)) = self.return_values().split_first() {
            write!(f, "{}", first)?;
            for return_value in rest {
                write!(f, ", {}", return_value)?;
            }
        }
        write!(f, "]")?;
        Ok(())
    }
}

impl ReturnInstr {
    /// Creates a new return instruction returning the given value.
    pub fn new<T>(return_values: T) -> Self
    where
        T: IntoIterator<Item = Value>,
    {
        Self {
            return_values: return_values.into_iter().collect::<Vec<_>>(),
        }
    }

    /// Returns the value that is returned by the instruction.
    #[inline]
    pub fn return_values(&self) -> &[Value] {
        &self.return_values
    }
}

impl VisitValues for ReturnInstr {
    fn visit_values<V>(&self, mut visitor: V)
    where
        V: FnMut(Value) -> bool,
    {
        for &value in &self.return_values {
            if !visitor(value) {
                break
            }
        }
    }
}

impl VisitValuesMut for ReturnInstr {
    fn visit_values_mut<V>(&mut self, mut visitor: V)
    where
        V: FnMut(&mut Value) -> bool,
    {
        for value in &mut self.return_values {
            if !visitor(value) {
                break
            }
        }
    }
}

/// Unconditionally branches to another basic block.
#[derive(Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
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
    #[inline]
    pub fn target(&self) -> Block {
        self.target
    }
}

/// Conditionally either branches to `then` or `else` branch depending on `condition`.
#[derive(Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
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
    #[inline]
    pub fn condition(&self) -> Value {
        self.condition
    }

    /// Returns the block to jump to in case the condition evaluates to `true`.
    #[inline]
    pub fn true_target(&self) -> Block {
        self.br_then
    }

    /// Returns the block to jump to in case the condition evaluates to `false`.
    #[inline]
    pub fn false_target(&self) -> Block {
        self.br_else
    }
}

impl VisitValues for IfThenElseInstr {
    fn visit_values<V>(&self, mut visitor: V)
    where
        V: FnMut(Value) -> bool,
    {
        visitor(self.condition);
    }
}

impl VisitValuesMut for IfThenElseInstr {
    fn visit_values_mut<V>(&mut self, mut visitor: V)
    where
        V: FnMut(&mut Value) -> bool,
    {
        visitor(&mut self.condition);
    }
}

/// A branching table mapping indices to branching targets.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct BranchTableInstr {
    case: Value,
    default: Block,
    targets: SmallBlockVec,
}

impl BranchTableInstr {
    /// Creates a new branching table with the given case, default target and targets.
    pub fn new<I>(case: Value, default: Block, targets: I) -> Self
    where
        I: IntoIterator<Item = Block>,
    {
        Self {
            case,
            default,
            targets: targets.into_iter().collect(),
        }
    }

    /// Returns the case value determining where to jump to.
    pub fn case(&self) -> Value {
        self.case
    }

    /// Returns a slice over all target jumps.
    pub fn targets(&self) -> &[Block] {
        &self.targets
    }

    /// Returns the default target to jump to.
    pub fn default_target(&self) -> Block {
        self.default
    }
}

impl VisitValues for BranchTableInstr {
    fn visit_values<V>(&self, mut visitor: V)
    where
        V: FnMut(Value) -> bool,
    {
        visitor(self.case);
    }
}

impl VisitValuesMut for BranchTableInstr {
    fn visit_values_mut<V>(&mut self, mut visitor: V)
    where
        V: FnMut(&mut Value) -> bool,
    {
        visitor(&mut self.case);
    }
}

impl Display for BranchTableInstr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "br_table {} [ ", self.case)?;
        if let Some((first, rest)) = self.targets.split_first() {
            write!(f, "0 🠖 {}", first)?;
            for (n, target) in rest.iter().enumerate() {
                write!(f, ", {} 🠖 {}", n + 1, target)?;
            }
        }
        write!(f, "_ 🠖 {}", self.default_target())?;
        write!(f, " ]")?;
        Ok(())
    }
}

macro_rules! impl_from_terminal_instr_for_instr {
    ( $( $name:ident ),* $(,)? ) => {
        $(
            impl ::core::convert::From<$name> for crate::instr::Instruction {
                fn from(instr: $name) -> Self {
                    Self::Terminal(crate::instr::TerminalInstr::from(instr))
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
    TailCallInstr,
}
