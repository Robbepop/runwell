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

use crate::primitive::Value;

/// Implemented by all Runwell IR instructions.
///
/// Allows to replaces all values in the instruction using the replacer.
/// This is used by the SSA conversion routines in order to propagate new
/// values for switched out instructions. This is in particular useful to
/// replace temporarily introduced phi instructions.
pub trait ReplaceValue {
    /// Replaces all values in the instruction using the replacer.
    ///
    /// Returns `true` if a value has been replaced in the instruction.
    ///
    /// # Note
    ///
    /// By contract the replacer returns `true` if replacement happened.
    fn replace_value<F>(&mut self, replace: F) -> bool
    where
        F: FnMut(&mut Value) -> bool;
}
