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

use crate::{
    ir::{operator::DestinationId, ValueId},
    parse::operator::IntType as Type,
};

/// Truncates the value to the smaller type and stores it into `dst`.
///
/// # Example
///
/// Truncates the `%2` of type `i64` into a value of type `i32` and stores
/// the result into `%1`.
///
/// ```no_compile
/// %1 <- i32.truncate i64 %2
/// ```
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct TruncateOp {
    /// The type after the truncation.
    dst_ty: Type,
    /// The source value of the truncation.
    src: ValueId,
    /// The type before the truncation.
    src_ty: Type,
}

/// Zero-extends the value to the biffer type and stores it into `dst`.
///
/// # Example
///
/// Zero-extends the `%2` of type `i32` into a value of type `i64` and stores
/// the result into `%1`.
///
/// ```no_compile
/// %1 <- i64.zero_extend i32 %2
/// ```
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ZeroExtendOp {
    /// The type after extension.
    dst_ty: Type,
    /// The source value of the extension.
    src: ValueId,
    /// The type before extension.
    src_ty: Type,
}

/// Sign-extends the value to the biffer type and stores it into `dst`.
///
/// # Example
///
/// Sign-extends the `%2` of type `i32` into a value of type `i64` and stores
/// the result into `%1`.
///
/// ```no_compile
/// %1 <- i64.sign_extend i32 %2
/// ```
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SignExtendOp {
    /// The type after extension.
    dst_ty: Type,
    /// The source value of the extension.
    src: ValueId,
    /// The type before extension.
    src_ty: Type,
}
