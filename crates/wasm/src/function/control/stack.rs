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

use super::frame::ControlFlowFrame;
use crate::TranslateError;

/// The stack of control flow frames.
#[derive(Debug, Default)]
pub struct ControlFlowStack {
    frames: Vec<ControlFlowFrame>,
}

impl ControlFlowStack {
    /// Returns `true` if the stack of control flow frames is empty.
    ///
    /// # Note
    ///
    /// This is usually the case after translating the last `End` Wasm operator
    /// of a Wasm function.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the current depth of the stack of control flow frames.
    pub fn len(&self) -> usize {
        self.frames.len()
    }

    /// Pushes a new frame to the stack of control flow frames.
    pub fn push_frame(&mut self, frame: ControlFlowFrame) {
        self.frames.push(frame)
    }

    /// Pops the last frame from the stack of control flow frames.
    pub fn pop_frame(&mut self) -> Result<ControlFlowFrame, TranslateError> {
        self.frames.pop().ok_or(TranslateError::MissingWasmBlock)
    }

    /// Returns the last control flow frame on the control stack.
    pub fn last(&self) -> Option<&ControlFlowFrame> {
        self.frames.last()
    }

    /// Returns the last control flow frame on the control stack.
    pub fn last_mut(&mut self) -> Option<&mut ControlFlowFrame> {
        self.frames.last_mut()
    }

    /// Returns the nth control flow frame from the back where 0th is the last.
    ///
    /// # Errors
    ///
    /// If `n` exceeds the length of the stack of control flow frames.
    pub fn nth_back(
        &self,
        n: u32,
    ) -> Result<&ControlFlowFrame, TranslateError> {
        self.frames
            .iter()
            .rev()
            .nth_back(n as usize)
            .ok_or_else(|| {
                let len = self.frames.len();
                TranslateError::RelativeDepthExceedsBlockStack { n, len }
            })
    }

    /// Returns the nth control flow frame from the back where 0th is the last.
    ///
    /// # Errors
    ///
    /// If `n` exceeds the length of the stack of control flow frames.
    pub fn nth_back_mut(
        &mut self,
        n: u32,
    ) -> Result<&mut ControlFlowFrame, TranslateError> {
        let len = self.frames.len();
        self.frames
            .iter_mut()
            .rev()
            .nth_back(n as usize)
            .ok_or(TranslateError::RelativeDepthExceedsBlockStack { n, len })
    }

    /// Returns the top most control flow frame.
    ///
    /// This is the control flow frame that was put the latest on the stack of frames.
    ///
    /// # Errors
    ///
    /// If the stack of blocks is empty.
    pub fn current(&self) -> Result<&ControlFlowFrame, TranslateError> {
        self.frames.last().ok_or(TranslateError::MissingWasmBlock)
    }
}
