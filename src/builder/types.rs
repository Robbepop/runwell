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

use super::BuilderError;
use crate::{
    parse2::{FunctionType, FunctionTypeId},
    Index32,
};
use derive_more::{Display, Error};

#[derive(Debug, Display, Error, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypesError {
    #[display(
        fmt = "encountered duplicate reservation for types table with {}. previous reservation: {}",
        total_count,
        previous
    )]
    DuplicateReserved { total_count: u32, previous: u32 },
    #[display(
        fmt = "tried to register another type when the Wasm types table did not expect any further items. reserved: {}, last item = {:?}",
        reserved,
        last_item
    )]
    RegisteredTooManyTypes {
        reserved: u32,
        last_item: FunctionType,
    },
}

/// The Wasm types table.
///
/// Represents the contents of the Wasm type section.
#[derive(Debug, Default)]
pub struct Types {
    types: Vec<FunctionType>,
}

impl Types {
    /// Reserves space for the given amount of expected type definitions.
    ///
    /// # Errors
    ///
    /// If there already has been a reservation before.
    pub fn reserve(&mut self, total_count: u32) -> Result<(), BuilderError> {
        let capacity = self.types.capacity();
        if capacity > 0 {
            return Err(TypesError::DuplicateReserved {
                total_count,
                previous: capacity as u32,
            })
            .map_err(BuilderError::from)
            .map_err(Into::into)
        }
        self.types.reserve(total_count as usize);
        Ok(())
    }

    /// Returns the number of registered Wasm type definitions.
    pub fn len(&self) -> usize {
        self.types.len()
    }

    /// Returns `true` if there are no registered Wasm type definitions.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the function signature identified by `id`.
    ///
    /// # Panics
    ///
    /// If the given ID is invalid for this Wasm types table.
    pub fn get(&self, id: FunctionTypeId) -> &FunctionType {
        &self.types[id.into_u32() as usize]
    }

    /// Returns the function signature identifier by `id` if any.
    pub fn try_get(&self, id: FunctionTypeId) -> Option<&FunctionType> {
        self.types.get(id.into_u32() as usize)
    }

    /// Registers another function signature at the Wasm types table.
    ///
    /// Returns its unique function signature ID.
    ///
    /// # Errors
    ///
    /// If trying to register more types than reserved.
    pub fn push(
        &mut self,
        sig: FunctionType,
    ) -> Result<FunctionTypeId, BuilderError> {
        let len = self.len();
        let cap = self.types.capacity();
        assert!(len < u32::MAX as usize);
        if len == cap {
            return Err(TypesError::RegisteredTooManyTypes {
                reserved: cap as u32,
                last_item: sig,
            })
            .map_err(Into::into)
        }
        let id = FunctionTypeId::from_u32(self.len() as u32);
        self.types.push(sig);
        Ok(id)
    }
}
