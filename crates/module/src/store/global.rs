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

use crate::Store;
use core::cell::Cell;
use derive_more::Display;
use ir::primitive::Type;
use super::RuntimeValue;
use std::rc::Rc;

/// Errors that can occur while operating on global values.
#[derive(Debug, Display, PartialEq, Eq)]
pub enum GlobalError {
    #[display(fmt = "found {} type but expected {} type", found, expected)]
    UnmatchingTypes { expected: Type, found: Type },
    #[display(
        fmt = "tried to set immutable global from {:?} to {:?}",
        old_value,
        new_value
    )]
    ImmutableWrite {
        old_value: RuntimeValue,
        new_value: RuntimeValue,
    },
}

/// A result encountered when operating on linear memory instances.
type Result<T> = core::result::Result<T, GlobalError>;

/// Denotes the mutability of a global variable.
#[derive(Debug, Copy, Clone)]
pub enum Mutability {
    Immutable,
    Mutable,
}

/// Holds the state of a single global variable at runtime.
///
/// # Note
///
/// Guards access to the value of the global variable.
#[derive(Debug)]
pub struct GlobalInstance {
    value: Cell<RuntimeValue>,
    mutability: Mutability,
}

impl GlobalInstance {
    /// Creates a new global value with the given initial value and mutability.
    pub fn new(initial_value: RuntimeValue, mutability: Mutability) -> Self {
        Self {
            value: Cell::new(initial_value),
            mutability,
        }
    }

    /// Returns `true` if the global value is mutable.
    pub fn is_mutable(&self) -> bool {
        matches!(self.mutability, Mutability::Mutable)
    }

    /// Returns the value type of the global value.
    pub fn value_type(&self) -> Type {
        self.value.get().value_type()
    }

    /// Updates the value of the global value to the new value.
    ///
    /// This returns a new global instance with the new value.
    ///
    /// # Errors
    ///
    /// - If the global value is immutable.
    /// - If the type of the new value does not match the type of the global value.
    pub fn set(&self, new_value: RuntimeValue) -> Result<()> {
        if new_value.value_type() != self.value_type() {
            return Err(GlobalError::UnmatchingTypes {
                expected: self.value_type(),
                found: new_value.value_type(),
            })
        }
        if !self.is_mutable() {
            return Err(GlobalError::ImmutableWrite {
                new_value,
                old_value: self.get(),
            })
        }
        self.value.set(new_value);
        Ok(())
    }

    /// Returns the value of the global value.
    pub fn get(&self) -> RuntimeValue {
        self.value.get()
    }
}

/// A shared reference to a global value.
///
/// # Note
///
/// Cloning a `GlobalRef` only performs an efficient shallow copy.
#[derive(Debug, Clone)]
pub struct GlobalRef {
    inner: Rc<GlobalInstance>,
}

impl GlobalRef {
    /// Creates a new global value in the given store.
    pub fn new(
        store: &Store,
        initial_value: RuntimeValue,
        mutability: Mutability,
    ) -> Self {
        store.alloc_global(initial_value, mutability)
    }

    /// Creates a new shared global value reference from the given global instance.
    pub(super) fn from_instance(global: GlobalInstance) -> Self {
        Self {
            inner: Rc::new(global),
        }
    }

    /// Returns `true` if the global value is mutable.
    pub fn is_mutable(&self) -> bool {
        self.inner.is_mutable()
    }

    /// Returns the value type of the global value.
    pub fn value_type(&self) -> Type {
        self.inner.value_type()
    }

    /// Sets the value of the global value to the new value.
    ///
    /// # Errors
    ///
    /// - If the global value is immutable.
    /// - If the type of the new value does not match the type of the global value.
    pub fn set(&self, new_value: RuntimeValue) -> Result<()> {
        self.inner.set(new_value)
    }

    /// Returns the value of the global value.
    pub fn get(&self) -> RuntimeValue {
        self.inner.get()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ir::primitive::IntType;

    #[test]
    fn get_set_works() {
        let store = Store::default();
        let global =
            GlobalRef::new(&store, RuntimeValue::I32(1), Mutability::Mutable);
        assert_eq!(global.get(), RuntimeValue::I32(1));
        assert!(global.is_mutable());
        assert_eq!(global.value_type(), Type::Int(IntType::I32));
        global.set(RuntimeValue::I32(2)).unwrap();
        assert_eq!(global.get(), RuntimeValue::I32(2));
    }

    #[test]
    fn unmatching_types_rejected() {
        let store = Store::default();
        let global =
            GlobalRef::new(&store, RuntimeValue::I32(1), Mutability::Mutable);
        assert_eq!(
            global.set(RuntimeValue::I64(2)),
            Err(GlobalError::UnmatchingTypes {
                expected: Type::Int(IntType::I32),
                found: Type::Int(IntType::I64),
            })
        );
    }

    #[test]
    fn immutable_set_rejected() {
        let store = Store::default();
        let global =
            GlobalRef::new(&store, RuntimeValue::I32(1), Mutability::Immutable);
        assert_eq!(
            global.set(RuntimeValue::I32(2)),
            Err(GlobalError::ImmutableWrite {
                old_value: RuntimeValue::I32(1),
                new_value: RuntimeValue::I32(2),
            })
        );
    }
}
