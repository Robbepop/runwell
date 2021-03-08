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

use core::{fmt::Debug, hash::Hash};
use std::collections::HashMap;

/// A replacement mapping.
#[derive(Debug)]
pub struct Replacer<T> {
    replace: HashMap<T, T, ahash::RandomState>,
}

impl<T> Default for Replacer<T> {
    fn default() -> Self {
        Self {
            replace: Default::default(),
        }
    }
}

impl<T> Replacer<T>
where
    T: Debug + Hash + Eq + Copy,
{
    /// Inserts a replacement for `old_value` to `new_value`.
    ///
    /// # Panics
    ///
    /// If this replacement has already been inserted.
    pub fn insert(&mut self, old_value: T, new_value: T) {
        if self.replace.insert(old_value, new_value).is_some() {
            panic!(
                "encountered duplicate replacement insert of {:?} -> {:?}",
                old_value, new_value,
            )
        }
    }

    /// Returns the replacement of `old_value` or returns `old_value` back.
    pub fn get(&self, old_value: T) -> T {
        self.replace.get(&old_value).copied().unwrap_or(old_value)
    }

    /// Returns the replacement of `old_value` or returns `None`.
    pub fn try_get(&self, old_value: T) -> Option<T> {
        self.replace.get(&old_value).copied()
    }
}
