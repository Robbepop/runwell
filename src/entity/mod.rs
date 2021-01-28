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

//! Data structures for entity component management.
//!
//! For efficiency purposes it is not possible to remove once created entities again.
//! Systems are not supported by this ECS system.

mod index;
pub mod primary;
pub mod secondary;

#[cfg(test)]
mod tests;

pub use self::{
    index::{
        Idx,
        RawIdx,
    },
    primary::EntityArena,
    secondary::{
        ComponentMap,
        ComponentVec,
        DefaultComponentMap,
        DefaultComponentVec,
    },
};
