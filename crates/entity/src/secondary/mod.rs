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

//! Data structures to add, remove and query components for existing entities.

pub mod default_bitvec;
pub mod default_map;
pub mod default_vec;
mod immutable;
pub mod map;
pub mod vec;

use self::immutable::Immutable;
pub use self::{
    default_bitvec::DefaultComponentBitVec,
    default_map::DefaultComponentMap,
    default_vec::DefaultComponentVec,
    map::ComponentMap,
    vec::ComponentVec,
};
