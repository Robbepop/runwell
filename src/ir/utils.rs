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
