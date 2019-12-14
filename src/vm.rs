use crate::op::{Block, Label, Op};
use core::{convert::TryFrom, num::NonZeroU32};
use slice_of_array::prelude::*;
use thiserror::Error;

#[repr(transparent)]
#[derive(Debug, Copy, Clone)]
pub struct Register {
    id: u8,
}

impl Register {
    pub fn new(id: u8) -> Self {
        assert!(id < 128);
        Self { id }
    }

    pub fn id(self) -> u8 {
        self.id
    }

    pub fn get(self) -> usize {
        self.id as usize
    }
}

impl TryFrom<u8> for Register {
    type Error = InvalidRegisterId;

    fn try_from(id: u8) -> Result<Self, Self::Error> {
        if id >= 128 {
            return Err(InvalidRegisterId)
        }
        Ok(Self { id })
    }
}

#[derive(Debug, Error, Copy, Clone)]
#[error("invalid register id")]
pub struct InvalidRegisterId;

#[repr(transparent)]
#[derive(Debug, Copy, Clone)]
pub struct Address {
    location: NonZeroU32,
}

impl Address {
    pub fn new(location: u32) -> Self {
        assert_ne!(location, 0);
        Self {
            location: unsafe { NonZeroU32::new_unchecked(location) },
        }
    }

    pub fn location(self) -> u32 {
        self.location.get()
    }
}

impl TryFrom<u32> for Address {
    type Error = InvalidAddressLocation;

    fn try_from(location: u32) -> Result<Self, Self::Error> {
        Ok(Self {
            location: NonZeroU32::new(location)
                .ok_or_else(|| InvalidAddressLocation)?,
        })
    }
}

impl From<NonZeroU32> for Address {
    fn from(location: NonZeroU32) -> Self {
        Self { location }
    }
}

#[derive(Debug, Error, Copy, Clone)]
#[error("invalid register id")]
pub struct InvalidAddressLocation;

#[derive(Copy, Clone, Debug)]
pub struct Pointer(u32);

impl Pointer {
    pub fn get(self) -> usize {
        self.0 as usize
    }
}

/// A program's stack.
pub struct Stack {
    /// The current live bytes of the stack.
    bytes: Vec<u8>,
}

impl Stack {
    /// Creates a new empty stack.
    pub fn new() -> Self {
        Self { bytes: Vec::new() }
    }

    /// Returns the current size of the stack.
    pub fn len(&self) -> usize {
        self.bytes.len()
    }

    /// Pushes the stack by `amount` bytes.
    pub fn push_frame(&mut self, amount: usize) {
        self.bytes.resize(self.len() + amount, 0x00)
    }

    /// Pops the stack by `amount` bytes.
    pub fn pop_frame(&mut self, amount: usize) {
        self.bytes.truncate(self.len() - amount)
    }

    /// Returns the byte at `ptr` as `bool`.
    ///
    /// # Safety
    ///
    /// The `ptr` value is trusted at this point.
    pub fn get_bool(&self, ptr: Pointer) -> bool {
        let at = ptr.get();
        debug_assert!(at < self.len());
        let value = unsafe { *self.bytes.get_unchecked(at) };
        debug_assert!(value == 0 || value == 1);
        value != 0
    }

    /// Sets the `bool` of the byte at `ptr` to `new_value`.
    pub fn set_bool(&mut self, ptr: Pointer, new_value: bool) {
        let at = ptr.get();
        debug_assert!(at < self.len());
        unsafe { *self.bytes.get_unchecked_mut(at) = new_value as u8 };
    }

    /// Returns the bytes at `ptr..4` as `i32`.
    ///
    /// # Safety
    ///
    /// The `ptr` value is trusted at this point.
    pub fn get_i32(&self, ptr: Pointer) -> i32 {
        type Int = i32;
        const N: usize = core::mem::size_of::<Int>();
        let at = ptr.get();
        debug_assert!((at + N) <= self.len());
        Int::from_le_bytes(
            unsafe { self.bytes.get_unchecked(ptr.get()..N) }
                .to_array::<[_; N]>(),
        )
    }

    /// Sets the `i32` value at `ptr` to `new_value`.
    pub fn set_i32(&mut self, ptr: Pointer, new_value: i32) {
        const N: usize = core::mem::size_of::<i32>();
        let at = ptr.get();
        debug_assert!((at + N) <= self.len());
        let bytes = new_value.to_le_bytes();
        unsafe {
            *self
                .bytes
                .get_unchecked_mut(ptr.get()..N)
                .as_mut_array::<[_; N]>() = bytes
        };
    }
}

pub struct Vm {
    /// Program counter.
    pc: u32,
    /// Stack
    stack: Stack,
    /// Stack pointer
    stack_ptr: Pointer,
    /// A runewell VM has 128 register with each 16 bytes.
    registers: [Entry; 128],
    /// A stack of break labels.
    labels: Vec<Label>,
}

pub struct Function {
    /// The first block is the entry point.
    block: Vec<Block>,
    /// The function's stack frame size.
    ///
    /// This includes
    ///
    /// - Required stack size for all function arguments.
    /// - Required stack size for all local variables and state.
    frame_size: usize,
}

/// A register entry.
///
/// Can contain any kind of possible value.
///
/// # Safety
///
/// The register entry assumes that operations performed on it
/// occure in a type safe fashion. Type safety is asserted by
/// checks previous to the actual computation.
#[derive(Copy, Clone)]
pub union Entry {
    /// A boolean value.
    bool_value: bool,
    /// An `i32` value.
    i32_value: i32,
    /// An `i64` value.
    i64_value: i64,
    /// An `f32` value.
    f32_value: f32,
    /// An `f64` value.
    f64_value: f64,
    /// A bytes array of the same size as the biggest sub type.
    bytes: [u8; 8],
}

impl core::fmt::Debug for Entry {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        unsafe { self.bytes }.fmt(f)
    }
}

impl Entry {
    /// Initializes the register entry with zeroes.
    pub const fn zero() -> Self {
        Self { bytes: [0x00; 8] }
    }

    /// Sets the register entry to the `bool` value.
    pub fn set_to_bool(&mut self, value: bool) {
        self.bool_value = value;
    }

    /// Returns the `bool` value stored in the register entry.
    pub fn get_bool(self) -> bool {
        unsafe { self.bool_value }
    }

    /// Sets the register entry to the `i32` value.
    pub fn set_to_i32(&mut self, value: i32) {
        self.i32_value = value;
    }

    /// Returns the `i32` value stored in the register entry.
    pub fn get_i32(self) -> i32 {
        unsafe { self.i32_value }
    }
}

impl Vm {
    /// Creates a new virtual machine.
    pub fn new() -> Self {
        Self {
            pc: 0,
            stack: Stack::new(),
            stack_ptr: Pointer(0),
            registers: [Entry::zero(); 128],
            labels: Vec::new(),
        }
    }

    /// Returns a shared reference to the register entry.
    ///
    /// # Safety
    ///
    /// We can assume to only receive valid `reg` identifiers at this point.
    fn get_register(&self, reg: Register) -> &Entry {
        unsafe { self.registers.get_unchecked(reg.get()) }
    }

    /// Returns an exclusive reference to the register entry.
    ///
    /// # Safety
    ///
    /// We can assume to only receive valid `reg` identifiers at this point.
    fn get_register_mut(&mut self, reg: Register) -> &mut Entry {
        unsafe { self.registers.get_unchecked_mut(reg.get()) }
    }

    /// Loads the `bool` value into the `dst` register.
    fn bool_const_to_reg(&mut self, dst: Register, value: bool) {
        self.get_register_mut(dst).set_to_bool(value)
    }

    /// Loads the `bool` value from the `src` register.
    fn bool_load_from_reg(&self, src: Register) -> bool {
        self.get_register(src).get_bool()
    }

    /// Loads the `i32` value into the `dst` register.
    fn i32_const_to_reg(&mut self, dst: Register, value: i32) {
        self.get_register_mut(dst).set_to_i32(value)
    }

    /// Loads an `i32` value from the `src` register.
    fn i32_load_from_reg(&self, src: Register) -> i32 {
        self.get_register(src).get_i32()
    }

    /// Loads the `i32` values from the `lhs` and `rhs` registers
    /// and stores the result of the wrapping add into the `dst` register.
    fn i32_add(&mut self, dst: Register, lhs: Register, rhs: Register) {
        let rhs = self.i32_load_from_reg(rhs);
        self.i32_add_by_const(dst, lhs, rhs);
    }

    fn i32_add_by_const(&mut self, dst: Register, lhs: Register, rhs: i32) {
        let lhs = self.i32_load_from_reg(lhs);
        self.i32_const_to_reg(dst, lhs.wrapping_add(rhs));
    }

    /// Loads the `i32` values from the `lhs` and `rhs` registers
    /// and stores the `bool` result of `lhs == rhs` into the `dst` register.
    fn i32_eq(&mut self, dst: Register, lhs: Register, rhs: Register) {
        let lhs = self.i32_load_from_reg(lhs);
        let rhs = self.i32_load_from_reg(rhs);
        self.bool_const_to_reg(dst, lhs == rhs);
    }

    fn break_to_label(&mut self, label: Label) {
        while let Some(popped) = self.labels.pop() {
            if popped == label {
                break
            }
        }
    }

    fn break_if(&mut self, src: Register, label: Label) {
        let src_value = self.bool_load_from_reg(src);
        if src_value {
            self.break_to_label(label)
        }
    }

    fn execute_if(&mut self, src: Register, then_op: &Op, else_op: &Op) {
        let value = self.bool_load_from_reg(src);
        if value {
            self.execute_op(then_op)
        } else {
            self.execute_op(else_op)
        }
    }

    fn jump_if(&mut self, src: Register, to: u32) {
        let value = self.bool_load_from_reg(src);
        if !value {
            self.pc = to;
        }
    }

    pub fn execute_op(&mut self, op: &Op) {
        match *op {
            Op::BoolConst { dst, value } => self.bool_const_to_reg(dst, value),
            Op::I32Const { dst, value } => self.i32_const_to_reg(dst, value),
            Op::I32Add { dst, lhs, rhs } => self.i32_add(dst, lhs, rhs),
            Op::I32Eq { dst, lhs, rhs } => self.i32_eq(dst, lhs, rhs),
            Op::JumpIf { src, to } => self.jump_if(src, to),
            Op::Print { src } => {
                println!("console.log: {:?}", self.registers[src.get()]);
            }
            Op::Nop => {}
            _ => panic!("encountered unsupported op code"),
        }
    }

    pub fn execute<I>(&mut self, input: I)
    where
        I: IntoIterator<Item = Op>,
    {
        let input = input.into_iter();
        for op in input {
            self.execute_op(&op)
        }
    }

    pub fn execute2<'a, I>(&mut self, instructions: I)
    where
        I: Iterator<Item = &'a Op> + 'a,
    {
        let insts = instructions.collect::<Vec<_>>();
        self.execute3(insts.as_slice());
    }

    pub fn execute3(&mut self, instructions: &[&Op]) {
        loop {
            let maybe_inst = instructions.get(self.pc as usize);
            self.pc += 1;
            match maybe_inst {
                Some(inst) => self.execute_op(inst),
                None => return,
            }
        }
    }
}
