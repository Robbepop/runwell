//! A source of an operation.
//!
//! This can be either an immediate value, a local variable or a global variable.

use crate::ir::{GlobalVar, LocalVar};
use derive_more::From;

/// A generic constant value.
#[derive(From)]
pub enum Value {
    I32(I32Value),
    I64(I64Value),
    F32(F32Value),
    F64(F64Value),
}

/// Either an `i32` or `i64` value.
#[derive(From)]
pub enum IntValue {
    I32(I32Value),
    I64(I64Value),
}

/// Either an `f32` or `f64` value.
#[derive(From)]
pub enum FloatValue {
    F32(F32Value),
    F64(F64Value),
}

/// A constant `i32` value.
#[derive(From)]
pub struct I32Value(i32);

/// A constant `i64` value.
#[derive(From)]
pub struct I64Value(i64);

/// A constant `f32` value.
#[derive(From)]
pub struct F32Value(f32);

/// A constant `f64` value.
#[derive(From)]
pub struct F64Value(f64);

/// Source into an operation.
///
/// This can either be an immediate value, a local variable or a global variable.
pub enum GenericSource<V> {
    /// An immediate constant value.
    Value(V),
    /// A function local variable or function parameter.
    Local(LocalVar),
    /// A global variable.
    Global(GlobalVar),
}

/// A generic source.
pub type Source = GenericSource<Value>;
/// An explicitely integer (`i32` or `i64`) typed source.
pub type IntSource = GenericSource<IntValue>;
/// An explicitely float (`f32` or `f64`) typed source.
pub type FloatSource = GenericSource<FloatValue>;
/// An explicitely `i32` typed source.
pub type I32Source = GenericSource<I32Value>;
/// An explicitely `i64` typed source.
pub type I64Source = GenericSource<I64Value>;
/// An explicitely `f32` typed source.
pub type F32Source = GenericSource<F32Value>;
/// An explicitely `f64` typed source.
pub type F64Source = GenericSource<F64Value>;
