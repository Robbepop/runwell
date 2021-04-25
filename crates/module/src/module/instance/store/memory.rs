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

use super::{RunwellPrimitive, Store};
use core::{
    cell::{RefCell, RefMut},
    ops::RangeInclusive,
};
use derive_more::Display;
use std::rc::Rc;

/// A result encountered when operating on linear memory instances.
type Result<T> = core::result::Result<T, MemoryError>;

/// An error that can occure while operating on linear memory instances.
#[derive(Debug, Display, PartialEq, Eq)]
pub enum MemoryError {
    #[display(
        fmt = "tried to access bytes at [{}..{}+{}] with only {} pages ({} bytes)",
        offset,
        offset,
        len,
        "pages.into_u16()",
        "pages.into_bytes().into_u32()"
    )]
    RangeOutOfBounds {
        offset: usize,
        len: usize,
        pages: Pages,
    },
    #[display(
        fmt = "tried to grow from {} pages to {} pages with only {} maximum pages",
        "current_pages.into_u16()",
        "target_pages.into_u16()",
        "maximum_pages.into_u16()"
    )]
    InvalidGrow {
        target_pages: Pages,
        current_pages: Pages,
        maximum_pages: Pages,
    },
}

/// Represents an amount of bytes.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Bytes {
    amount: u32,
}

impl Bytes {
    /// Creates an amount of bytes from the given `u32` amount.
    pub(super) const fn new(amount: u32) -> Bytes {
        Self { amount }
    }

    /// Returns the amount of bytes as `u32`.
    pub const fn into_u32(self) -> u32 {
        self.amount
    }
}

/// The amount of pages for a linear memory.
///
/// This might represent the minimum, maximum or current amount of memory pages.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Pages {
    /// The amount.
    amount: u16,
}

impl Pages {
    /// The maximum amount of pages for a single linear memory.
    const MAX: Self = Pages { amount: u16::MAX };

    /// The amount of bytes in a single memory page.
    const BYTES_PER_PAGE: Bytes = Bytes::new(u16::MAX as u32);

    /// Creates a new amount of pages.
    ///
    /// # Panics
    ///
    /// If the amount of pages is equal to zero.
    pub fn new(amount: u16) -> Self {
        assert_ne!(amount, 0, "cannot have zero pages");
        Self { amount }
    }

    /// Returns the amount of pages.
    pub fn into_u16(self) -> u16 {
        self.amount
    }

    /// Returns the amount of bytes that can be stored with the amount of pages.
    pub fn into_bytes(self) -> Bytes {
        Bytes::new(self.amount as u32 * Self::BYTES_PER_PAGE.into_u32())
    }
}

/// The layout of a linear memory.
#[derive(Debug, Copy, Clone)]
struct MemoryLayout {
    minimum_pages: Pages,
    maximum_pages: Pages,
    current_pages: Pages,
}

impl MemoryLayout {
    /// Create a new memory layout.
    pub fn new(minimum_pages: Pages, maximum_pages: Option<Pages>) -> Self {
        let maximum_pages = maximum_pages.unwrap_or(Pages::MAX);
        assert!(
            minimum_pages < maximum_pages,
            "tried to create a linear memory with only {} maxmimum and {} minimum pages",
            maximum_pages.into_u16(),
            minimum_pages.into_u16(),
        );
        Self {
            minimum_pages,
            maximum_pages,
            current_pages: minimum_pages,
        }
    }

    /// Grows the current pages by the additional amount.
    ///
    /// This does not immediately grow the underlying memory buffer but instead
    /// adjusts the current amount of memory pages. Only when the memory at the
    /// now available indices is actually required will the underlying buffer be
    /// grown in order to support the operation.
    ///
    /// # Errors
    ///
    /// If `new_pages` is greater than the specified maximum amount of pages for
    /// the linear memory instance.
    pub fn grow(&mut self, additional: Pages) -> Result<()> {
        let new_pages =
            Pages::new(self.current_pages.into_u16() + additional.into_u16());
        if new_pages > self.maximum_pages {
            return Err(MemoryError::InvalidGrow {
                target_pages: new_pages,
                current_pages: self.current_pages,
                maximum_pages: self.maximum_pages,
            })
        }
        self.current_pages = new_pages;
        Ok(())
    }

    /// Returns the number of currently allocated pages.
    pub fn size(&self) -> Pages {
        self.current_pages
    }

    /// Ensures that the range is within bounds for the linear memory.
    ///
    /// Returns the maximum index of the range if valid.
    ///
    /// # Errors
    ///
    /// If the index is out of bounds for the current amount of memory pages.
    fn ensure_range_within_bounds(
        &self,
        offset: usize,
        len: usize,
    ) -> Result<usize> {
        let index = offset
            .checked_add(len)
            .map(|r| r.saturating_sub(1))
            .unwrap_or_else(|| {
                panic!(
                    "offset + len index is out of valid bounds as `usize` value"
                )
            });
        let max = self.current_pages.into_bytes().into_u32() as usize;
        if index >= max {
            return Err(MemoryError::RangeOutOfBounds {
                offset,
                len,
                pages: self.current_pages,
            })
        }
        Ok(index)
    }
}

/// An instantiated linear memory with its live contents.
#[derive(Debug)]
pub struct MemoryInstance {
    layout: MemoryLayout,
    bytes: Vec<u8>,
}

impl MemoryInstance {
    /// Creates a new linear memory instance with the given amount of minimum and maximum pages.
    ///
    /// # Panics
    ///
    /// When trying to create a linear memory with fewer maxmimum pages than minimum pages.
    pub fn new(minimum_pages: Pages, maximum_pages: Option<Pages>) -> Self {
        Self {
            layout: MemoryLayout::new(minimum_pages, maximum_pages),
            bytes: Vec::new(),
        }
    }

    /// Ensures that the range is within bounds for the linear memory.
    ///
    /// Returns the range `start..end` if valid.
    ///
    /// # Note
    ///
    /// This operation lazily resizes the underlying bytes buffer in case
    /// it is not big enough to represent the bytes at the chosen range.
    ///
    /// # Errors
    ///
    /// If the index is out of bounds for the current amount of memory pages.
    fn ensure_range_within_bounds(
        &mut self,
        offset: usize,
        len: usize,
    ) -> Result<RangeInclusive<usize>> {
        let index = self.layout.ensure_range_within_bounds(offset, len)?;
        if index >= self.bytes.len() {
            self.bytes.resize(offset + len, 0x00);
        }
        Ok(offset..=index)
    }

    /// Grows the current pages by the additional amount.
    ///
    /// This does not immediately grow the underlying memory buffer but instead
    /// adjusts the current amount of memory pages. Only when the memory at the
    /// now available indices is actually required will the underlying buffer be
    /// grown in order to support the operation.
    ///
    /// # Errors
    ///
    /// If resulting pages are greater than the specified maximum amount of pages
    /// of the linear memory instance.
    pub fn grow(&mut self, additional: Pages) -> Result<()> {
        self.layout.grow(additional)
    }

    /// Returns the current number of pages of the linear memory.
    ///
    /// # Note
    ///
    /// The current amount of pages does not necessarily mean that the underlying
    /// buffer has an equivalent amount of allocated bytes. Instead buffer memory
    /// is allocated lazily only when required.
    pub fn size(&self) -> Pages {
        self.layout.size()
    }

    /// Returns a slice to the bytes within the range.
    ///
    /// # Note
    ///
    /// - This might costly resize the underlying buffer of the linear memory
    ///   in case the current amount of pages suffices for the range of bytes.
    /// - The underlying buffer is resized with zero initialized bytes.
    ///
    /// # Errors
    ///
    /// If the range of bytes is out of bounds of the current pages.
    fn access_bytes(&mut self, offset: usize, len: usize) -> Result<&mut [u8]> {
        let range = self.ensure_range_within_bounds(offset, len)?;
        Ok(&mut self.bytes[range])
    }
}

/// A shared reference to a linear memory instance.
#[derive(Debug, Clone)]
pub struct MemoryRef {
    inner: Rc<RefCell<MemoryInstance>>,
}

/// Represents a partial view into the contents of a linear memory.
///
/// # Note
///
/// This can be used to avoid recomputing bounds checks for some connected
/// memory accesses to the same region of linear memory.
#[derive(Debug)]
pub struct MemoryView<'a> {
    layout: MemoryLayout,
    offset: usize,
    view: RefMut<'a, [u8]>,
}

impl<'a> MemoryView<'a> {
    /// Ensures that the range is within bounds for the linear memory.
    ///
    /// Returns the maximum index of the range if valid.
    ///
    /// # Errors
    ///
    /// If the index is out of bounds for the current amount of memory pages.
    fn ensure_range_within_bounds(
        &self,
        offset: usize,
        len: usize,
    ) -> Result<RangeInclusive<usize>> {
        let end = self
            .layout
            .ensure_range_within_bounds(offset + self.offset, len)?
            - self.offset;
        Ok(offset..=end)
    }

    /// Reads the Wasm primitive from the given offset in the linear memory view.
    ///
    /// # Errors
    ///
    /// If the read bytes are out of bounds of the current pages or the view.
    pub fn read_primitive<T>(&self, offset: usize) -> Result<T>
    where
        T: RunwellPrimitive,
    {
        let mut bytes = <T as Default>::default().into_bytes();
        let range =
            self.ensure_range_within_bounds(offset, bytes.as_ref().len())?;
        bytes.as_mut().copy_from_slice(&self.view[range]);
        let value = <T as RunwellPrimitive>::from_bytes(bytes);
        Ok(value)
    }

    /// Writes the Wasm primitive to the given offset in the linear memory view.
    ///
    /// # Errors
    ///
    /// If the written bytes are out of bounds of the current pages or the view.
    pub fn write_primitive<T>(&mut self, offset: usize, value: T) -> Result<()>
    where
        T: RunwellPrimitive,
    {
        let bytes = value.into_bytes();
        let range =
            self.ensure_range_within_bounds(offset, bytes.as_ref().len())?;
        self.view[range].copy_from_slice(bytes.as_ref());
        Ok(())
    }
}

impl<'a> core::ops::Deref for MemoryView<'a> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        &self.view
    }
}

impl<'a> core::ops::DerefMut for MemoryView<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.view
    }
}

impl MemoryRef {
    /// Creates a new linear memory in the given store.
    ///
    /// # Panics
    ///
    /// When trying to create a linear memory with fewer maxmimum pages than minimum pages.
    pub fn new(
        store: &Store,
        minimum_pages: Pages,
        maximum_pages: Option<Pages>,
    ) -> Self {
        store.alloc_memory(minimum_pages, maximum_pages)
    }

    /// Returns a view into the bytes at `mem[offset..(offset + len)]`.
    ///
    /// # Note
    ///
    /// This might costly resize the underlying buffer of the linear memory
    /// in case the current amount of pages suffices for the range of bytes.
    ///
    /// # Errors
    ///
    /// If the range of bytes is out of bounds of the current pages.
    pub fn view(&self, offset: usize, len: usize) -> Result<MemoryView> {
        self.inner.borrow_mut().access_bytes(offset, len)?;
        let layout = self.inner.borrow().layout;
        // With `RefMap::filter_map` or `RefMap::try_map` we could provide a more efficient
        // implementation, however those APIs are not yet stabilized. Tracking issue can be
        // found here: https://github.com/rust-lang/rust/issues/81061
        let view = RefMut::map(self.inner.borrow_mut(), |mem| {
            mem.access_bytes(offset, len).unwrap_or_else(|err| {
                unreachable!(
                    "memory[{}..{}+{}] invalidly is out of valid bounds: {}",
                    offset, offset, len, err,
                )
            })
        });
        Ok(MemoryView {
            view,
            layout,
            offset,
        })
    }

    /// Creates a new shared memory reference from the given memory instance.
    pub(super) fn from_instance(memory: MemoryInstance) -> Self {
        Self {
            inner: Rc::new(RefCell::new(memory)),
        }
    }

    /// Grows the linear memory to the new amount of pages.
    ///
    /// This does not immediately grow the underlying memory buffer but instead
    /// adjusts the current amount of memory pages. Only when the memory at the
    /// now available indices is actually required will the underlying buffer be
    /// grown in order to support the operation.
    ///
    /// # Errors
    ///
    /// If `new_pages` is greater than the specified maximum amount of pages for
    /// the linear memory instance.
    pub fn grow(&self, additional: Pages) -> Result<()> {
        self.inner.borrow_mut().grow(additional)
    }

    /// Returns the current number of pages of the linear memory.
    ///
    /// # Note
    ///
    /// The current amount of pages does not necessarily mean that the underlying
    /// buffer has an equivalent amount of allocated bytes. Instead buffer memory
    /// is allocated lazily only when required.
    pub fn size(&self) -> Pages {
        self.inner.borrow().size()
    }

    /// Reads bytes starting at the given offset into the buffer until it is full.
    ///
    /// # Note
    ///
    /// - Can be used on the caller site to fill a predetermined buffer and
    ///   then convert the buffer bytes into another primitive such as a `u32`
    ///   or `f64`.
    /// - This might costly resize the underlying buffer of the linear memory
    ///   in case the current amount of pages suffices for the range of bytes.
    ///
    /// # Errors
    ///
    /// If the range of bytes is out of bounds of the current pages.
    pub fn read_bytes(&self, offset: usize, buffer: &mut [u8]) -> Result<()> {
        let view = self.view(offset, buffer.len())?;
        buffer.copy_from_slice(&view);
        Ok(())
    }

    /// Writes the given bytes into the linear memory at the given offset.
    ///
    /// # Note
    ///
    /// - Can be used on the caller site to fill a predetermined buffer with
    ///   the contents of a primitive such as a `u32` or a `f64`.
    /// - This might costly resize the underlying buffer of the linear memory
    ///   in case the current amount of pages suffices for the range of bytes.
    ///
    /// # Errors
    ///
    /// If the range of bytes is out of bounds of the current pages.
    pub fn write_bytes(&self, offset: usize, buffer: &[u8]) -> Result<()> {
        let mut view = self.view(offset, buffer.len())?;
        view.copy_from_slice(buffer);
        Ok(())
    }

    /// Reads the Wasm primitive from the given offset in the linear memory.
    ///
    /// # Note
    ///
    /// This might costly resize the underlying buffer of the linear memory
    /// in case the current amount of pages suffices for the range of bytes.
    ///
    /// # Errors
    ///
    /// If the range of bytes is out of bounds of the current pages.
    pub fn read_primitive<T>(&self, offset: usize) -> Result<T>
    where
        T: RunwellPrimitive,
    {
        let mut bytes = <T as Default>::default().into_bytes();
        self.read_bytes(offset, bytes.as_mut())?;
        let value = <T as RunwellPrimitive>::from_bytes(bytes);
        Ok(value)
    }

    /// Writes the Wasm primitive to the given offset in the linear memory.
    ///
    /// # Note
    ///
    /// This might costly resize the underlying buffer of the linear memory
    /// in case the current amount of pages suffices for the range of bytes.
    ///
    /// # Errors
    ///
    /// If the range of bytes is out of bounds of the current pages.
    pub fn write_primitive<T>(&self, offset: usize, value: T) -> Result<()>
    where
        T: RunwellPrimitive,
    {
        let bytes = value.into_bytes();
        self.write_bytes(offset, bytes.as_ref())?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Create the default store for testing purposes.
    fn store() -> Store {
        Store::default()
    }

    #[test]
    #[should_panic = "tried to create a linear memory with only 1 maxmimum and 2 minimum pages"]
    fn invalid_new_panics() {
        let store = store();
        MemoryRef::new(&store, Pages::new(2), Some(Pages::new(1)));
    }

    #[test]
    fn grow_works() -> Result<()> {
        let store = store();
        let one_page = Pages::new(1);
        let min_pages = Pages::new(1);
        let max_pages = Pages::new(2);
        let memory = MemoryRef::new(&store, min_pages, Some(max_pages));
        assert_eq!(memory.size(), min_pages);
        memory.grow(one_page)?;
        assert_eq!(memory.size(), max_pages);
        assert_eq!(
            memory.grow(one_page),
            Err(MemoryError::InvalidGrow {
                target_pages: Pages::new(3),
                current_pages: max_pages,
                maximum_pages: max_pages,
            }),
        );
        assert_eq!(memory.size(), max_pages);
        Ok(())
    }

    #[test]
    fn grow_works_without_max() -> Result<()> {
        let store = store();
        let memory = MemoryRef::new(&store, Pages::new(1), None);
        assert!(memory.grow(Pages::new(2)).is_ok());
        assert!(memory.grow(Pages::MAX).is_ok());
        Ok(())
    }

    #[test]
    fn read_write_bytes_out_of_bounds() {
        let store = store();
        let pages = Pages::new(1);
        let memory = MemoryRef::new(&store, pages, None);
        // Perform out of bounds read and check whether the operation returns an error.
        let mut bytes = [0x00; 1];
        let bytes_per_page = Pages::BYTES_PER_PAGE.into_u32() as usize;
        assert_eq!(
            memory.read_bytes(bytes_per_page, &mut bytes),
            Err(MemoryError::RangeOutOfBounds {
                offset: bytes_per_page,
                len: 1,
                pages: Pages::new(1),
            })
        );
        assert_eq!(
            memory.write_bytes(bytes_per_page, &mut bytes),
            Err(MemoryError::RangeOutOfBounds {
                offset: bytes_per_page,
                len: 1,
                pages: Pages::new(1),
            })
        );
    }

    #[test]
    fn read_write_bytes_works() -> Result<()> {
        let store = store();
        let pages = Pages::new(1);
        let memory = MemoryRef::new(&store, pages, None);
        let mut buffer = [0x00; 4];
        // Read without any write should result in zero initialized bytes.
        memory.read_bytes(0, &mut buffer)?;
        assert_eq!(buffer, [0x00; 4]);
        // Write to the same memory location and check if next read yields the same.
        memory.write_bytes(0, &[0x01, 0x02, 0x03, 0x04])?;
        memory.read_bytes(0, &mut buffer)?;
        assert_eq!(buffer, [0x01, 0x02, 0x03, 0x04]);
        // Write to the last 4 bytes of the current page.
        let last_4_offset = (u16::MAX - 4) as usize;
        memory.write_bytes(last_4_offset, &[0xC0, 0xFE, 0xBE, 0xEB])?;
        memory.read_bytes(last_4_offset, &mut buffer)?;
        assert_eq!(buffer, [0xC0, 0xFE, 0xBE, 0xEB]);
        // Grow memory to some more pages and see if reading and writing still works.
        // Access 4 bytes starting at the 100th byte of the 4th memory page check if
        // zero initialization works, then write and read out the same result.
        memory.grow(Pages::new(10))?;
        let offset = (Pages::new(4).into_bytes().into_u32() + 100) as usize;
        memory.read_bytes(offset, &mut buffer)?;
        assert_eq!(buffer, [0x00; 4]);
        memory.write_bytes(offset, &[0x10, 0x20, 0x30, 0x40])?;
        memory.read_bytes(offset, &mut buffer)?;
        assert_eq!(buffer, [0x10, 0x20, 0x30, 0x40]);
        Ok(())
    }

    #[test]
    fn read_write_primitive_out_of_bounds() {
        let store = store();
        let pages = Pages::new(1);
        let memory = MemoryRef::new(&store, pages, None);
        // Perform out of bounds read and check whether the operation returns an error.
        let bytes_per_page = Pages::BYTES_PER_PAGE.into_u32() as usize;
        assert_eq!(
            memory.read_primitive::<i8>(bytes_per_page),
            Err(MemoryError::RangeOutOfBounds {
                offset: bytes_per_page,
                len: 1,
                pages: Pages::new(1),
            })
        );
        assert_eq!(
            memory.write_primitive::<i8>(bytes_per_page, 1),
            Err(MemoryError::RangeOutOfBounds {
                offset: bytes_per_page,
                len: 1,
                pages: Pages::new(1),
            })
        );
    }

    #[test]
    fn read_write_primitive_works() -> Result<()> {
        let store = store();
        let pages = Pages::new(1);
        let size_i32 = core::mem::size_of::<i32>() as usize;
        let size_f64 = core::mem::size_of::<f64>() as usize;
        let memory = MemoryRef::new(&store, pages, None);
        // Read without any write should result in zero initialized bytes.
        let bytes_per_page = Pages::BYTES_PER_PAGE.into_u32() as usize;
        assert_eq!(memory.read_primitive::<i32>(0)?, 0);
        assert_eq!(memory.read_primitive::<f64>(0 + size_i32)?, 0.0);
        assert_eq!(memory.read_primitive::<i32>(bytes_per_page - size_i32)?, 0);
        assert_eq!(
            memory
                .read_primitive::<f64>(bytes_per_page - size_i32 - size_f64)?,
            0.0
        );
        // Write to the same offsets and see if the values successfully changed.
        macro_rules! validate_access {
            ( $base_offset:expr ) => {{
                let bytes_per_page = Pages::BYTES_PER_PAGE.into_u32() as usize;
                memory.write_primitive::<i32>($base_offset, 1)?;
                memory.write_primitive::<f64>($base_offset + size_i32, 2.0)?;
                memory.write_primitive::<i32>(
                    $base_offset + bytes_per_page - size_i32,
                    3,
                )?;
                memory.write_primitive::<f64>(
                    $base_offset + bytes_per_page - size_i32 - size_f64,
                    4.0,
                )?;
                assert_eq!(memory.read_primitive::<i32>($base_offset)?, 1);
                assert_eq!(
                    memory.read_primitive::<f64>($base_offset + size_i32)?,
                    2.0
                );
                assert_eq!(
                    memory.read_primitive::<i32>(
                        $base_offset + bytes_per_page - size_i32
                    )?,
                    3
                );
                assert_eq!(
                    memory.read_primitive::<f64>(
                        $base_offset + bytes_per_page - size_i32 - size_f64
                    )?,
                    4.0
                );
            }};
        }
        validate_access!(0);
        // Grow memory to some more pages and see if reading and writing still works.
        memory.grow(Pages::new(10))?;
        let base_offset =
            (Pages::new(4).into_bytes().into_u32() + 100) as usize;
        validate_access!(base_offset);
        Ok(())
    }
}
