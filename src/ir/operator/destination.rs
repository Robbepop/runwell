// Copyright 2019 Robin Freyler
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

use crate::ir::ValueId;

/// Implemented by `runwell` IR operators to return their destination value.
///
/// # Examples
///
/// - `%5 <- i32.const 42` returns `Some(%5)`
/// - `i32.store %1 %2` returns `None` since it has no destination value
pub trait DestinationId {
    /// Returns the destination value ID from the `runwell` IR operator.
    fn destination_id(&self) -> Option<ValueId>;
}
