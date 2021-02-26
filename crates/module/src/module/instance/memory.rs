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

/// The contents of an instantiated linear memory.
#[derive(Debug, Default)]
pub struct LinearMemoryContents {
    bytes: Vec<u8>,
}

impl LinearMemoryContents {
    /// Initializes parts of the linear memory contents.
    pub fn initialize(&mut self, offset: u32, bytes: &[u8]) {
        self.bytes.resize(offset as usize + bytes.len(), 0x00);
        self.write_from_slice(offset, bytes);
    }

    /// Returns a shared slice of bytes at the given offset and of given size.
    ///
    /// # Panics
    ///
    /// If the sum of offset and size index is out of bounds for the linear memory.
    fn bytes_at(&self, offset: u32, size: usize) -> &[u8] {
        let size = size as usize;
        let offset = offset as usize;
        &self.bytes[offset..(offset + size)]
    }

    /// Returns a mutable slice of bytes at the given offset and of given size.
    ///
    /// # Panics
    ///
    /// If the sum of offset and size index is out of bounds for the linear memory.
    fn bytes_at_mut(&mut self, offset: u32, size: usize) -> &mut [u8] {
        let size = size as usize;
        let offset = offset as usize;
        &mut self.bytes[offset..(offset + size)]
    }

    /// Reads bytes starting at the given offset into the buffer until it is full.
    ///
    /// # Note
    ///
    /// Can be used on the caller site to fill a fixed-size array as buffer
    /// and then convert the array bytes into another primitive such as a `u32`
    /// or `f64`.
    ///
    /// # Panics
    ///
    /// If the sum of offset and buffer length is out of bounds for the linear memory.
    pub fn read_into_slice(&self, offset: u32, buffer: &mut [u8]) {
        buffer.copy_from_slice(self.bytes_at(offset, buffer.len()));
    }

    /// Writes the given bytes into the linear memory at the given offset.
    ///
    /// # Panics
    ///
    /// If the sum of offset and bytes length is out of bounds for the linear memory.
    pub fn write_from_slice(&mut self, offset: u32, bytes: &[u8]) {
        let len = bytes.len();
        self.bytes_at_mut(offset, len).copy_from_slice(bytes);
    }
}
