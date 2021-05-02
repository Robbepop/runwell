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
use ir::primitive::{FloatType, IntType, Type, F32, F64};
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

/// A typed runtime value.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum RuntimeValue {
    I1(bool),
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
    F32(F32),
    F64(F64),
}

macro_rules! impl_from_primitive {
    ( $( impl From<$variant_type:ty> for RuntimeValue::$variant_ident:ident );* $(;)? ) => {
        $(
            impl From<$variant_type> for RuntimeValue {
                fn from(value: $variant_type) -> Self {
                    Self::$variant_ident(value)
                }
            }
        )*
    };
}
impl_from_primitive! {
    impl From<bool> for RuntimeValue::I1;
    impl From<i8> for RuntimeValue::I8;
    impl From<i16> for RuntimeValue::I16;
    impl From<i32> for RuntimeValue::I32;
    impl From<i64> for RuntimeValue::I64;
    impl From<F32> for RuntimeValue::F32;
    impl From<F64> for RuntimeValue::F64;
}

macro_rules! impl_from_unsigned_primitive {
    ( $( impl From<$unsigned_type:ty> for RuntimeValue::$variant_ident:ident { _ as $variant_type:ty } )* ) => {
        $(
            impl From<$unsigned_type> for RuntimeValue {
                fn from(value: $unsigned_type) -> Self {
                    Self::$variant_ident(value as $variant_type)
                }
            }
        )*
    };
}
impl_from_unsigned_primitive! {
    impl From<u8> for RuntimeValue::I8 { _ as i8 }
    impl From<u16> for RuntimeValue::I16 { _ as i16 }
    impl From<u32> for RuntimeValue::I32 { _ as i32 }
    impl From<u64> for RuntimeValue::I64 { _ as i64 }
}

macro_rules! impl_as_primitive {
    ( $(
        $( #[$docs:meta] ),*
        fn $fn_name:ident($variant_name:ident) -> $variant_type:ty
    );* $(;)? ) => {
        impl RuntimeValue {
            $(
                $(
                    #[$docs]
                )*
                pub fn $fn_name(self) -> Option<$variant_type> {
                    if let Self::$variant_name(value) = self {
                        return Some(value)
                    }
                    None
                }
            )*
        }
    };
}
impl_as_primitive! {
    /// Returns the `bool`value or `None`if the type is not `bool`.
    fn as_bool(I1) -> bool;

    /// Returns the `i8` value or `None` if the type is not `i8`.
    fn as_i8(I8) -> i8;

    /// Returns the `i16` value or `None` if the type is not `i16`.
    fn as_i16(I16) -> i16;

    /// Returns the `i32` value or `None` if the type is not `i32`.
    fn as_i32(I32) -> i32;

    /// Returns the `i64` value or `None` if the type is not `i64`.
    fn as_i64(I64) -> i64;

    /// Returns the `f32` value or `None` if the type is not `f32`.
    fn as_f32(F32) -> F32;

    /// Returns the `f64` value or `None` if the type is not `f64`.
    fn as_f64(F64) -> F64;
}

impl RuntimeValue {
    /// Creates a default value for the given value type.
    pub fn default(value_type: Type) -> Self {
        match value_type {
            Type::Ptr => RuntimeValue::I32(Default::default()),
            Type::Int(IntType::I1) => RuntimeValue::I1(false),
            Type::Int(IntType::I8) => RuntimeValue::I8(Default::default()),
            Type::Int(IntType::I16) => RuntimeValue::I16(Default::default()),
            Type::Int(IntType::I32) => RuntimeValue::I32(Default::default()),
            Type::Int(IntType::I64) => RuntimeValue::I64(Default::default()),
            Type::Float(FloatType::F32) => {
                RuntimeValue::F32(Default::default())
            }
            Type::Float(FloatType::F64) => {
                RuntimeValue::F64(Default::default())
            }
        }
    }

    /// Returns the value type of the runtime value.
    pub fn value_type(self) -> Type {
        match self {
            RuntimeValue::I1(_) => Type::Int(IntType::I1),
            RuntimeValue::I8(_) => Type::Int(IntType::I8),
            RuntimeValue::I16(_) => Type::Int(IntType::I16),
            RuntimeValue::I32(_) => Type::Int(IntType::I32),
            RuntimeValue::I64(_) => Type::Int(IntType::I64),
            RuntimeValue::F32(_) => Type::Float(FloatType::F32),
            RuntimeValue::F64(_) => Type::Float(FloatType::F64),
        }
    }
}

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
