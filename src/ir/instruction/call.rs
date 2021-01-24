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

use crate::{
    ir::primitive::Value,
    parse::{FunctionId, FunctionTypeId, TableId},
};
use core::{convert::identity, fmt::Display};

/// Calls a function statically.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CallInstr {
    /// The identified of the called function.
    function_id: FunctionId,
    /// The parameters of the function call.
    call_params: Vec<Value>,
}

impl CallInstr {
    /// Creates a new call instruction to call the indexed function using the given parameters.
    pub fn new<I>(function_id: FunctionId, call_params: I) -> Self
    where
        I: IntoIterator<Item = Value>,
    {
        Self {
            function_id,
            call_params: call_params.into_iter().collect::<Vec<_>>(),
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
        self.call_params
            .iter_mut()
            .map(|param| replace(param))
            .any(identity)
    }
}

impl Display for CallInstr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "call {}, params: [", self.function_id)?;
        if let Some((fst, rest)) = self.call_params.split_first() {
            write!(f, "{}", fst)?;
            for param in rest {
                write!(f, ", {}", param)?;
            }
        }
        write!(f, "]")?;
        Ok(())
    }
}

/// Calls a function indirectly through a table with a dynamic offset into the table.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CallIndirectInstr {
    /// The unique ID of the table holding the indirectly called functions.
    table_id: TableId,
    /// The type of the indirectly called function that is expected by this instruction.
    ///
    /// If the dynamically chosen function does not match this function type the
    /// call will trap at execution time.
    func_type: FunctionTypeId,
    /// The index of the function in the table that is indirectly called.
    index: Value,
    /// The parameters given to the indirectly called function.
    call_params: Vec<Value>,
}

impl CallIndirectInstr {
    /// Creates a new call instruction to call the indexed function using the given parameters.
    pub fn new<I>(
        table_id: TableId,
        func_type: FunctionTypeId,
        index: Value,
        call_params: I,
    ) -> Self
    where
        I: IntoIterator<Item = Value>,
    {
        Self {
            table_id,
            func_type,
            index,
            call_params: call_params.into_iter().collect::<Vec<_>>(),
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
        replace(&mut self.index)
            && self
                .call_params
                .iter_mut()
                .map(|param| replace(param))
                .any(identity)
    }
}

impl Display for CallIndirectInstr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "call.indirect table {}, func_type {}, index {}, params: [",
            self.table_id, self.func_type, self.index
        )?;
        if let Some((fst, rest)) = self.call_params.split_first() {
            write!(f, "{}", fst)?;
            for param in rest {
                write!(f, ", {}", param)?;
            }
        }
        write!(f, "]")?;
        Ok(())
    }
}
