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

use crate::maybe_std::prelude::*;
use derive_more::From;

/// A type.
#[derive(From)]
pub enum Type {
    Int(IntType),
    Float(FloatType),
    Ptr(Box<PtrType>),
    Fn(FnType),
    BasicBlock,
}

/// A function type with inputs and outputs.
pub struct FnType {
    /// The input types.
    inputs: Vec<Type>,
    /// The output types.
    ///
    /// # Note
    ///
    /// The current version of Wasm (1.0) restricts the output
    /// to have one element at most.
    outputs: Vec<Type>,
}

/// A pointer type.
///
/// # Note
///
/// Operations like `alloca` will return pointer types.
/// Operations like `load` and `store` receive pointer types for their source
/// or destination.
pub struct PtrType {
    /// The type of the pointer.
    inner: Type,
}

/// An integer type.
pub enum IntType {
    /// 8-bit integer type.
    ///
    /// # Note
    ///
    /// Only used for truncation or extension from and to `i32` or `i64`.
    I8,
    /// 16-bit integer type.
    ///
    /// # Note
    ///
    /// Only used for truncation or extension from and to `i32` or `i64`.
    I16,
    /// 32-bit integer type.
    I32,
    /// 64-bit integer type.
    I64,
}

/// A float type.
pub enum FloatType {
    F32,
    F64,
}

/// A label within a function that allows to jump to.
pub struct Label(usize);

/// A function local variable or function parameter.
pub struct LocalVar(usize);

/// A global variable.
pub struct GlobalVar(usize);
