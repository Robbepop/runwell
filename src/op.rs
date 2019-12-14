use crate::vm::{Address, Register};

/// A type.
#[repr(u8)]
pub enum Type {
    /// The `bool` type.
    Bool,
    /// The 32-bit signed or unsigned integer.
    I32,
    /// The 64-bit signed or unsigned integer.
    I64,
    /// The 32-bit IEEE float.
    F32,
    /// The 64-bit IEEE float.
    F64,
}

impl Type {
    /// Returns the size in bytes for the type.
    pub fn size_of(self) -> usize {
        match self {
            Type::Bool => 1,
            Type::I32 => 4,
            Type::I64 => 8,
            Type::F32 => 4,
            Type::F64 => 8,
        }
    }
}

#[rustfmt::skip]
pub enum Op {
    /// Signals to abort the process.
    Unreachable,
    /// Operation that does nothing.
    Nop,

    /// Stores the `bool` constant into `dst`.
    BoolConst { dst: Register, value: bool },
    /// Stores the `i32` constant into `dst`.
    I32Const { dst: Register, value: i32 },
    /// Stores the `i64` constant into `dst`.
    I64Const { dst: Register, value: i64 },
    /// Stores the `f32` constant into `dst`.
    F32Const { dst: Register, value: f32 },
    /// Stores the `f64` constant into `dst`.
    F64Const { dst: Register, value: f64 },

    /// Loads the `bool` at `src` into `dst`.
    BoolLoad { dst: Register, src: Address },
    /// Loads the `i32` at `src` into `dst`.
    I32Load { dst: Register, src: Address },
    /// Loads the `i64` at `src` into `dst`.
    I64Load { dst: Register, src: Address },
    /// Loads the `f32` at `src` into `dst`.
    F32Load { dst: Register, src: Address },
    /// Loads the `f64` at `src` into `dst`.
    F64Load { dst: Register, src: Address },

    /// Stores the `bool` at `src` into `dst`.
    BoolStore { dst: Address, src: Register },
    /// Stores the `i32` at `src` into `dst`.
    I32Store { dst: Address, src: Register },
    /// Stores the `i64` at `src` into `dst`.
    I64Store { dst: Address, src: Register },
    /// Stores the `f32` at `src` into `dst`.
    F32Store { dst: Address, src: Register },
    /// Stores the `f64` at `src` into `dst`.
    F64Store { dst: Address, src: Register },

    /// Computes `lhs == rhs` of type `bool` and stores the result into `dst`.
    BoolEq { dst: Register, lhs: Register, rhs: Register },
    /// Computes `lhs == rhs` of type `i32` and stores the result into `dst`.
    I32Eq { dst: Register, lhs: Register, rhs: Register },
    /// Computes `lhs == rhs` of type `i64` and stores the result into `dst`.
    I64Eq { dst: Register, lhs: Register, rhs: Register },
    /// Computes `lhs == rhs` of type `f32` and stores the result into `dst`.
    F32Eq { dst: Register, lhs: Register, rhs: Register },
    /// Computes `lhs == rhs` of type `f64` and stores the result into `dst`.
    F64Eq { dst: Register, lhs: Register, rhs: Register },

    /// Computes `lhs < rhs` of type `i32` and stores the result into `dst`.
    I32Lt { dst: Register, lhs: Register, rhs: Register },
    /// Computes `lhs < rhs` of type `i64` and stores the result into `dst`.
    I64Lt { dst: Register, lhs: Register, rhs: Register },
    /// Computes `lhs < rhs` of type `f32` and stores the result into `dst`.
    F32Lt { dst: Register, lhs: Register, rhs: Register },
    /// Computes `lhs < rhs` of type `f64` and stores the result into `dst`.
    F64Lt { dst: Register, lhs: Register, rhs: Register },

    /// Computes `lhs + rhs` of type `i32` and stores the result into `dst`.
    I32Add { dst: Register, lhs: Register, rhs: Register },
    /// Computes `lhs + rhs` of type `i64` and stores the result into `dst`.
    I64Add { dst: Register, lhs: Register, rhs: Register },
    /// Computes `lhs + rhs` of type `f32` and stores the result into `dst`.
    F32Add { dst: Register, lhs: Register, rhs: Register },
    /// Computes `lhs + rhs` of type `f64` and stores the result into `dst`.
    F64Add { dst: Register, lhs: Register, rhs: Register },

    /// Jumps to the given line of code if `src` is not 0.
    JumpIf { src: Register, to: u32 },

    /// Prints the value at `src` into the console log.
    Print { src: Register },
}

/// A sequence of instructions that has a termination instruction at the end.
pub struct Block {
    ops: Vec<Op>,
}

#[repr(transparent)]
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Label {
    id: u32,
}

impl From<u32> for Label {
    fn from(id: u32) -> Self {
        Self { id }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vm::Vm;

    #[test]
    fn it_works() {
        let ops = vec![
            Op::I32Const {
                dst: Register::new(0),
                value: 5,
            },
            Op::I32Const {
                dst: Register::new(1),
                value: 42,
            },
            Op::I32Add {
                dst: Register::new(2),
                lhs: Register::new(0),
                rhs: Register::new(1),
            },
            Op::Print {
                src: Register::new(2),
            },
        ];
        let mut vm = Vm::new();
        vm.execute(ops);
    }
}
