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

use core::ops::Deref;
use derive_more::{Display, From};

/// A value that cannot be mutated.
///
/// Used by default component data structures as their prototype to yield
/// references to default components in case of a missing component. This
/// way those data structures can avoid mutations in `&self` methods such
/// as access through their [`Index`][`core::ops::Index`] trait implementation.
#[derive(Debug, Default, Display, Copy, Clone, From, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Immutable<T> {
    value: T,
}

impl<T> Deref for Immutable<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}
