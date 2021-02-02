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
    primitive::{Func, FuncType, Table, Value},
    ReplaceValue,
};
use core::{convert::identity, fmt::Display};

/// Calls a function statically.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CallInstr {
    /// The index of the called function.
    func: Func,
    /// The parameters of the function call.
    params: Vec<Value>,
}

impl CallInstr {
    /// Creates a new call instruction to call the indexed function using the given parameters.
    pub fn new<I>(func: Func, params: I) -> Self
    where
        I: IntoIterator<Item = Value>,
    {
        Self {
            func,
            params: params.into_iter().collect::<Vec<_>>(),
        }
    }

    /// Returns the called function index.
    pub fn func(&self) -> Func {
        self.func
    }

    /// Returns the function call parameters.
    pub fn params(&self) -> &[Value] {
        &self.params
    }
}

impl ReplaceValue for CallInstr {
    fn replace_value<F>(&mut self, mut replace: F) -> bool
    where
        F: FnMut(&mut Value) -> bool,
    {
        self.params
            .iter_mut()
            .map(|param| replace(param))
            .any(identity)
    }
}

impl Display for CallInstr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "call {} [ ", self.func())?;
        if let Some((fst, rest)) = self.params().split_first() {
            write!(f, "{}", fst)?;
            for param in rest {
                write!(f, ", {}", param)?;
            }
        }
        write!(f, " ]")?;
        Ok(())
    }
}

/// Calls a function indirectly through a table with a dynamic offset into the table.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CallIndirectInstr {
    /// The unique ID of the table holding the indirectly called functions.
    table: Table,
    /// The type of the indirectly called function that is expected by this instruction.
    ///
    /// If the dynamically chosen function does not match this function type the
    /// call will trap at execution time.
    func_type: FuncType,
    /// The index of the function in the table that is indirectly called.
    index: Value,
    /// The parameters given to the indirectly called function.
    params: Vec<Value>,
}

impl CallIndirectInstr {
    /// Creates a new call instruction to call the indexed function using the given parameters.
    pub fn new<I>(
        table: Table,
        func_type: FuncType,
        index: Value,
        params: I,
    ) -> Self
    where
        I: IntoIterator<Item = Value>,
    {
        Self {
            table,
            func_type,
            index,
            params: params.into_iter().collect::<Vec<_>>(),
        }
    }
}

impl ReplaceValue for CallIndirectInstr {
    fn replace_value<F>(&mut self, mut replace: F) -> bool
    where
        F: FnMut(&mut Value) -> bool,
    {
        replace(&mut self.index)
            && self
                .params
                .iter_mut()
                .map(|param| replace(param))
                .any(identity)
    }
}

impl Display for CallIndirectInstr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "call_indirect {}[{}] [ ", self.table, self.index)?;
        if let Some((first, rest)) = self.params.split_first() {
            write!(f, "{}", first)?;
            for param in rest {
                write!(f, ", {}", param)?;
            }
        }
        write!(f, " ]: ")?;
        write!(f, "{}", self.func_type)?;
        Ok(())
    }
}
