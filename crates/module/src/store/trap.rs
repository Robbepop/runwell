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

use derive_more::Display;

/// A program execution failure trap.
#[derive(Debug, Display, PartialEq, Eq)]
pub struct Trap {
    reason: TrapReason,
}

impl Trap {
    /// Constructs a new trap with the given trap reason.
    fn from_reason(reason: TrapReason) -> Self {
        Self { reason }
    }

    /// Constructs a new trap with the given custom trap message.
    pub fn message<S>(message: S) -> Self
    where
        S: Into<String>,
    {
        Self::from_reason(TrapReason::Message(message.into()))
    }

    /// Constructs a new trap from the given raw `i32` status code.
    pub fn i32_code(code: i32) -> Self {
        Self::from_reason(TrapReason::Code(code))
    }

    /// Constructs a new trap from the given Wasm specific trap reason.
    pub fn wasm_code(code: TrapCode) -> Self {
        Self::from_reason(TrapReason::Wasm(code))
    }

    /// Returns the custom trap reason message if the trap has one.
    pub fn try_into_message(&self) -> Option<&str> {
        if let TrapReason::Message(message) = &self.reason {
            return Some(message)
        }
        None
    }

    /// Returns the `i32` code of the trap if it has one.
    pub fn try_into_i32_code(&self) -> Option<i32> {
        if let TrapReason::Code(code) = &self.reason {
            return Some(*code)
        }
        None
    }

    /// Returns the Wasm specific trap code if there is one.
    pub fn try_into_wasm_code(&self) -> Option<TrapCode> {
        if let TrapReason::Wasm(code) = &self.reason {
            return Some(*code)
        }
        None
    }
}

/// Reason why a trap occurred.
#[derive(Debug, Display, PartialEq, Eq)]
pub enum TrapReason {
    /// An error message describing a trap.
    #[display(fmt = "message: {}", _0)]
    Message(String),
    /// An `i32` exit code describing an explicit program exit.
    #[display(fmt = "code: {}", _0)]
    Code(i32),
    /// A trap code that may be triggered while executing Wasm.
    #[display(fmt = "{}", _0)]
    Wasm(TrapCode),
}

/// A trap code describing the reason for a trap.
///
/// All trap instructions have an explicit trap code.
#[non_exhaustive]
#[derive(Debug, Display, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TrapCode {
    /// The current stack space was exhausted.
    ///
    /// # Note
    ///
    /// This can happen for very deep recursive executions or due to
    /// extensive inlining of function.
    #[display(fmt = "call stack exhausted")]
    StackOverflow,

    /// An out-of-bounds linear memory access.
    ///
    /// # Note
    ///
    /// Since addresses are interpreted as unsigned integers, out of bounds access
    /// can't happen with negative addresses (i.e. they will always wrap).
    #[display(fmt = "out of bounds memory access")]
    MemoryOutOfBounds,

    /// An out-of-bounds access to a table.
    ///
    /// # Note
    ///
    /// - This typically can happen when `call_indirect` is executed
    ///   with an out of bounds index.
    /// - Since indexes are interpreted as unsigned integers, out of bounds access
    ///   can't happen with negative indexes (i.e. they will always wrap).
    #[display(fmt = "undefined element: out of bounds table access")]
    TableOutOfBounds,

    /// An indirect call to an uninitialized table entry.
    ///
    /// # Note
    ///
    /// This can happen for indirect function calls where the index of the table
    /// refers to a slot that has not been initialized to a valid function reference.
    #[display(fmt = "uninitialized element")]
    IndirectCallToNull,

    /// Signature mismatch upon indirect call.
    ///
    /// # Note
    ///
    /// This can happen if a function was invoked with a mismatching [signature][`Signature`].
    ///
    /// A common source of this error is with indirect calls.
    /// `call_indirect` instruction specify the expected signature of function.
    /// If `call_indirect` is executed with an index that points on function with a
    /// signature different from what is expected by this `call_indirect`,
    /// a trap is raised.
    ///
    /// [`Signature`]: struct.Signature.html
    #[display(fmt = "indirect call signature mismatch")]
    SignatureMismatch,

    /// An integer arithmetic operation caused an overflow.
    #[display(fmt = "integer overflow")]
    IntegerOverflow,

    /// An integer division by zero.
    #[display(fmt = "integer division by zero")]
    IntegerDivisionByZero,

    /// A failed float-to-int conversion.
    ///
    /// # Note
    ///
    /// This can happen when:
    ///
    /// - trying to do signed division (or get the remainder) of the minimum value over -1.
    ///   This is because the result isn't representable as an N-bit signed integer in
    ///   twos-complement machine representation.
    /// - trying to truncate NaNs, infinity, or value for which the result is out of range into an integer.
    #[display(fmt = "invalid float to integer conversion")]
    InvalidFloatToIntegerConversion,

    /// Code that was supposed to have been unreachable was reached.
    #[display(fmt = "unreachable")]
    UnreachableCodeReached,

    /// Execution has potentially run too long and may be interrupted.
    #[display(fmt = "interrupt")]
    Interrupt,
}
