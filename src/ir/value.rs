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

use crate::Index32;
use derive_more::Display;

define_id_type! {
    /// An SSA value binding used for local and global value numbering.
    #[derive(Display)]
    #[display(fmt = "v{}", "self.index.get()")]
    pub struct Value;
}

/// Used to generate new SSA values in ascending order.
#[derive(Debug, Default)]
pub struct ValueGen {
    current_index: u32,
}

impl From<u32> for ValueGen {
    fn from(starting_index: u32) -> Self {
        Self {
            current_index: starting_index,
        }
    }
}

impl ValueGen {
    /// Generates and returns the next SSA value.
    pub fn next(&mut self) -> Value {
        let index = Value::from_u32(self.current_index);
        self.current_index += 1;
        index
    }
}
