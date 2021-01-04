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

use crate::ir::{BasicBlockId, Type, Value, Variable};
use derive_more::{Display, Error};

/// Errors that might occure upon building up a Runwell IR function.
#[derive(Debug, Display, Error, PartialEq, Eq)]
pub enum FunctionBuilderError {
    #[display(
        fmt = "tried to add new predecessor {} to sealed basic block {}",
        new_pred,
        sealed_block
    )]
    PredecessorForSealedBlock {
        sealed_block: BasicBlockId,
        new_pred: BasicBlockId,
    },
    #[display(
        fmt = "tried to add unfilled predecessor {} to basic block {}",
        unfilled_pred,
        block
    )]
    UnfilledPredecessor {
        unfilled_pred: BasicBlockId,
        block: BasicBlockId,
    },
    #[display(
        fmt = "tried to query current basic block while there is no basic block, yet."
    )]
    NoCurrentBasicBlock,
    #[display(fmt = "missing basic block at {}", block)]
    MissingBasicBlock { block: BasicBlockId },
    #[display(
        fmt = "tried to seal basic block {} that is already sealed",
        block
    )]
    BasicBlockIsAlreadySealed { block: BasicBlockId },
    #[display(
        fmt = "tried to append instructions to basic block {} that is already filled",
        block
    )]
    BasicBlockIsAlreadyFilled { block: BasicBlockId },
    #[display(fmt = "tried to declare too many function local variables")]
    TooManyVariableDeclarations,
    #[display(fmt = "tried {} undeclared variable {}.", variable, access)]
    MissingDeclarationForVariable {
        variable: Variable,
        access: VariableAccess,
    },
    #[display(
        fmt = "tried to assign {} with declared type {} to value {} of unmatching type {}",
        variable,
        declared_type,
        value,
        value_type
    )]
    UnmatchingVariableType {
        variable: Variable,
        value: Value,
        declared_type: Type,
        value_type: Type,
    },
    #[display(
        fmt = "tried to read variable {} before writing to it",
        variable
    )]
    ReadBeforeWriteVariable { variable: Variable },
    #[display(
        fmt = "there are still {} unsealed basic blocks upon finalizing construction",
        amount
    )]
    UnsealedBlocksUponFinalize { amount: usize },
    #[display(
        fmt = "branch from basic block {} to basic block {} already exists",
        from,
        to
    )]
    BranchAlreadyExists {
        from: BasicBlockId,
        to: BasicBlockId,
    },
    #[display(fmt = "encountered invalid basic block index at {}.", block)]
    InvalidBasicBlock { block: BasicBlockId },
}

/// A variable access for better error information.
#[derive(Debug, Display, PartialEq, Eq)]
pub enum VariableAccess {
    /// Read the value of the variable.
    #[display(fmt = "read")]
    Read,
    /// Write the value to variable.
    #[display(fmt = "write {} to", _0)]
    Write(Value),
}
