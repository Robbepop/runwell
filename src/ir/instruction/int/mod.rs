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

mod binary;
mod icmp;
mod iconv;
mod unary;

use crate::ir::{
    interpreter::{InterpretationContext, InterpretationError},
    primitive::Value,
};

pub use self::{
    binary::{BinaryIntInstr, BinaryIntOp},
    icmp::{CompareIntInstr, CompareIntOp},
    iconv::{ExtendIntInstr, IntToFloatInstr, TruncateIntInstr},
    unary::{UnaryIntInstr, UnaryIntOp},
};
use derive_more::{Display, From};

/// An SSA integer instruction from the Runwell IR.
#[derive(Debug, Display, From, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IntInstr {
    Binary(BinaryIntInstr),
    Unary(UnaryIntInstr),
    Compare(CompareIntInstr),
    Extend(ExtendIntInstr),
    IntToFloat(IntToFloatInstr),
    Truncate(TruncateIntInstr),
}

impl IntInstr {
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
            Self::Binary(instr) => instr.replace_value(replace),
            Self::Unary(instr) => instr.replace_value(replace),
            Self::Compare(instr) => instr.replace_value(replace),
            Self::Extend(instr) => instr.replace_value(replace),
            Self::IntToFloat(instr) => instr.replace_value(replace),
            Self::Truncate(instr) => instr.replace_value(replace),
        }
    }

    /// Evaluates the function given the interpretation context.
    pub fn interpret(
        &self,
        value: Option<Value>,
        ctx: &mut InterpretationContext,
    ) -> Result<(), InterpretationError> {
        match self {
            Self::Binary(instr) => instr.interpret(value, ctx),
            Self::Unary(instr) => instr.interpret(value, ctx),
            Self::Compare(instr) => instr.interpret(value, ctx),
            Self::Extend(instr) => instr.interpret(value, ctx),
            Self::IntToFloat(instr) => instr.interpret(value, ctx),
            Self::Truncate(instr) => instr.interpret(value, ctx),
        }
    }
}

macro_rules! impl_from_int_instr_for_instr {
    ( $( $name:ident ),* $(,)? ) => {
        $(
            impl ::core::convert::From<$name> for crate::ir::instr::Instruction {
                fn from(instr: $name) -> Self {
                    Self::Int(crate::ir::instr::IntInstr::from(instr))
                }
            }
        )*
    };
}
impl_from_int_instr_for_instr! {
    BinaryIntInstr,
    UnaryIntInstr,
    CompareIntInstr,
    TruncateIntInstr,
    IntToFloatInstr,
    ExtendIntInstr,
}
