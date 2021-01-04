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

use crate::{
    ir::{Instr, Type, Value},
    Index32,
};
use core::ops::{Index, IndexMut};

/// Holds all data about Runwell IR SSA values during function construction.
#[derive(Debug, Default)]
pub struct Values {
    values: Vec<ValueData>,
}

/// Data associated to a single Runwell IR SSA value.
#[derive(Debug)]
pub enum ValueData {
    /// A value associated to a function input parameter.
    Input {
        /// The output type of the input value.
        ty: Type,
        /// The position of the input parameter associated to the value.
        pos: u32,
    },
    /// A value associated to an instruction of the function.
    Instr {
        /// The output type of the instruction value.
        ty: Type,
        /// The instruction associated to the value.
        instr: Instr,
    },
}

impl ValueData {
    /// Returns the type of the value.
    pub fn ty(&self) -> &Type {
        match self {
            Self::Input { ty, .. } => ty,
            Self::Instr { ty, .. } => ty,
        }
    }

    /// Returns the instruction if the value data refers to an instruction value.
    ///
    /// Otherwise returns `None`.
    pub fn instr(&self) -> Option<Instr> {
        match self {
            Self::Instr { instr, .. } => Some(*instr),
            _ => None,
        }
    }

    /// Returns the input position if the value data refers to an input parameter value.
    ///
    /// Otherwise returns `None`.
    pub fn pos(&self) -> Option<u32> {
        match self {
            Self::Input { pos, .. } => Some(*pos),
            _ => None,
        }
    }
}

impl Values {
    /// Returns the next value.
    ///
    /// Used only internally to incrementally generate the next value.
    fn next_value(&mut self) -> Value {
        Value::from_u32(self.values.len() as u32)
    }

    /// Create a value associated to an input parameter of a function.
    pub fn create_input_value(&mut self, ty: Type, pos: u32) -> Value {
        let value = self.next_value();
        self.values.push(ValueData::Input { ty, pos });
        value
    }

    /// Create a value associated to an instruction of a function.
    pub fn create_instr_value(&mut self, ty: Type, instr: Instr) -> Value {
        let value = self.next_value();
        self.values.push(ValueData::Instr { ty, instr });
        value
    }

    /// Returns a shared reference to the value's data if any.
    pub fn get(&self, value: Value) -> Option<&ValueData> {
        self.values.get(value.into_u32() as usize)
    }

    /// Returns an exclusive reference to the value's data if any.
    pub fn get_mut(&mut self, value: Value) -> Option<&mut ValueData> {
        self.values.get_mut(value.into_u32() as usize)
    }
}

impl Index<Value> for Values {
    type Output = ValueData;

    fn index(&self, value: Value) -> &Self::Output {
        self.get(value).expect("invalid index for value")
    }
}

impl IndexMut<Value> for Values {
    fn index_mut(&mut self, value: Value) -> &mut Self::Output {
        self.get_mut(value).expect("invalid index for value")
    }
}
