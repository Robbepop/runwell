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

use super::SmallValueVec;
use crate::{
    primitive::{Func, FuncType, Table, Value},
    VisitValues,
    VisitValuesMut,
};
use core::fmt::Display;
use smallvec::smallvec;

/// Calls a function statically.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct CallInstr {
    /// The index of the called function.
    func: Func,
    /// The parameters of the function call.
    params: SmallValueVec,
}

impl CallInstr {
    /// Creates a new call instruction to call the indexed function using the given parameters.
    pub fn new<I>(func: Func, params: I) -> Self
    where
        I: IntoIterator<Item = Value>,
    {
        Self {
            func,
            params: params.into_iter().collect::<SmallValueVec>(),
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

impl VisitValues for CallInstr {
    fn visit_values<V>(&self, mut visitor: V)
    where
        V: FnMut(Value) -> bool,
    {
        for &value in &self.params {
            if !visitor(value) {
                break
            }
        }
    }
}

impl VisitValuesMut for CallInstr {
    fn visit_values_mut<V>(&mut self, mut visitor: V)
    where
        V: FnMut(&mut Value) -> bool,
    {
        for value in &mut self.params {
            if !visitor(value) {
                break
            }
        }
    }
}

impl Display for CallInstr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "call {}(", self.func())?;
        if let Some((fst, rest)) = self.params().split_first() {
            write!(f, "{}", fst)?;
            for param in rest {
                write!(f, ", {}", param)?;
            }
        }
        write!(f, ")")?;
        Ok(())
    }
}

/// Calls a function indirectly through a table with a dynamic offset into the table.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct CallIndirectInstr {
    /// The unique ID of the table holding the indirectly called functions.
    table: Table,
    /// The type of the indirectly called function that is expected by this instruction.
    ///
    /// If the dynamically chosen function does not match this function type the
    /// call will trap at execution time.
    func_type: FuncType,
    /// Vector containing
    ///
    /// - the index of the function in the table that is indirectly called.
    /// - followd by the parameters given to the indirectly called function.
    ///
    /// # Note
    ///
    /// This design was chosen in order to slightly decrease the size of the
    /// instruction.
    index_and_params: SmallValueVec,
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
        let mut index_and_params = smallvec![index];
        index_and_params.extend(params.into_iter());
        Self {
            table,
            func_type,
            index_and_params,
        }
    }

    /// Returns the table for the indirect function call.
    pub fn table(&self) -> Table {
        self.table
    }

    /// Returns the table index for the indirect call.
    pub fn index(&self) -> Value {
        self.index_and_params[0]
    }

    /// Returns the expected func type of the indirectly called function.
    pub fn func_type(&self) -> FuncType {
        self.func_type
    }

    /// Returns the SSA function input values for the indirect call.
    pub fn params(&self) -> &[Value] {
        &self.index_and_params[1..]
    }
}

impl VisitValues for CallIndirectInstr {
    fn visit_values<V>(&self, mut visitor: V)
    where
        V: FnMut(Value) -> bool,
    {
        for &value in &self.index_and_params {
            if !visitor(value) {
                break
            }
        }
    }
}

impl VisitValuesMut for CallIndirectInstr {
    fn visit_values_mut<V>(&mut self, mut visitor: V)
    where
        V: FnMut(&mut Value) -> bool,
    {
        for value in &mut self.index_and_params {
            if !visitor(value) {
                break
            }
        }
    }
}

impl Display for CallIndirectInstr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "call_indirect {}[{}](", self.table, self.index())?;
        if let Some((first, rest)) = self.params().split_first() {
            write!(f, "{}", first)?;
            for param in rest {
                write!(f, ", {}", param)?;
            }
        }
        write!(f, "): ")?;
        write!(f, "{}", self.func_type)?;
        Ok(())
    }
}
