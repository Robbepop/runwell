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

//! This crate provides an interface for virtual memory that is used by virtual machines.
//!
//! This provides a low-level basis for virtual memory usage in the Runwell VM.
//! The main API is provided via the `VirtualMemory` type.
//! The API itself is agnostic over Wasm constraints, e.g. allows for pages sizes
//! other than 64kB.

use core::{
    cmp::max,
    fmt,
    fmt::{Debug, Display, Formatter},
    ops::{Deref, DerefMut, Index, IndexMut},
    ptr,
    slice::{self, SliceIndex},
};

/// An error that may occur upon operating with virtual memory.
#[derive(Debug)]
pub enum Error {
    Region(region::Error),
    OutOfBounds { len: usize, index: usize },
}

impl From<region::Error> for Error {
    fn from(error: region::Error) -> Self {
        Self::Region(error)
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Region(region) => Display::fmt(region, f),
            Self::OutOfBounds { len, index } => {
                write!(
                    f,
                    "out of bounds access at index {} with region of len {}",
                    index, len
                )
            }
        }
    }
}

/// A virtually allocated memory.
///
/// # Dev. Note
///
/// - Since instances of this type are always created with a read and write protection it is safe
///   to dereference instances into slices of bytes.
/// - Cannot implement `Clone`, `Copy` because of non-trivial destructor of `region::Allocation`.
/// - Cannot implement other standard traits such as `PartialEq`, `PartialOrd` or `Hash` efficiently.
///   If a user needs this they shall convert the virtual allocation into a slice.
pub struct VirtualMemory {
    allocation: region::Allocation,
}

impl Debug for VirtualMemory {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_struct("VirtualMemory")
            .field("ptr", &self.allocation.as_ptr::<u8>())
            .field("len", &self.allocation.len())
            .finish()
    }
}

#[allow(clippy::len_without_is_empty)]
impl VirtualMemory {
    /// Creates a new virtual memory with a capacity for the given amount of bytes.
    pub fn new(size: usize) -> Result<Self, Error> {
        let allocation = region::alloc(size, region::Protection::READ_WRITE)?;
        Ok(Self { allocation })
    }

    /// Returns the length of the virtually allocated buffer.
    #[inline]
    pub fn len(&self) -> usize {
        self.allocation.len()
    }

    /// Grows the virtually allocated buffer by the additional size.
    pub fn grow(&mut self, additional_size: usize) -> Result<(), Error> {
        if additional_size == 0 {
            return Ok(())
        }
        let new_size = self.len() + additional_size;
        self.allocation = region::alloc_at::<u8>(
            self.allocation.as_ptr::<u8>(),
            new_size,
            region::Protection::READ_WRITE,
        )?;
        Ok(())
    }

    /// Copies `len` bytes from `memory[src_offset..]` to `memory[dst_offset..]`.
    ///
    /// # Note
    ///
    /// The source and destination memory regions may overlap.
    ///
    /// # Errors
    ///
    /// If `src_offset + len` or `dst_offset + len` is out of bounds.
    #[inline]
    pub fn copy(
        &mut self,
        src_offset: usize,
        dst_offset: usize,
        len: usize,
    ) -> Result<(), Error> {
        let max_index = max(src_offset + len, dst_offset + len);
        let memory_len = self.len();
        if max_index >= memory_len {
            // Bail out early since the copy operation would access out of bounds indices.
            return Err(Error::OutOfBounds {
                index: max_index,
                len: memory_len,
            })
        }
        // SAFETY: Out of bounds check has already been performed above.
        unsafe {
            let src_ptr = self.allocation.as_ptr::<u8>().add(src_offset);
            let dst_ptr = self.allocation.as_mut_ptr::<u8>().add(dst_offset);
            ptr::copy(src_ptr, dst_ptr, len);
        }
        Ok(())
    }

    /// Returns a shared slice to the virtually allocated buffer.
    #[inline]
    pub fn as_slice(&self) -> &[u8] {
        // SAFETY: The only way to create an instance of this type
        //         is via the constructor which guarantees that the
        //         below byte slice creation is valid.
        unsafe {
            slice::from_raw_parts(
                self.allocation.as_ptr::<u8>(),
                self.allocation.len(),
            )
        }
    }

    /// Returns a mutable slice to the virtually allocated buffer.
    #[inline]
    pub fn as_slice_mut(&mut self) -> &mut [u8] {
        // SAFETY: The only way to create an instance of this type
        //         is via the constructor which guarantees that the
        //         below byte slice creation is valid.
        unsafe {
            slice::from_raw_parts_mut(
                self.allocation.as_mut_ptr::<u8>(),
                self.allocation.len(),
            )
        }
    }
}

impl<Idx> Index<Idx> for VirtualMemory
where
    Idx: SliceIndex<[u8]>,
{
    type Output = <Idx as SliceIndex<[u8]>>::Output;

    #[inline]
    fn index(&self, index: Idx) -> &Self::Output {
        &self.as_slice()[index]
    }
}

impl<Idx> IndexMut<Idx> for VirtualMemory
where
    Idx: SliceIndex<[u8]>,
{
    #[inline]
    fn index_mut(&mut self, index: Idx) -> &mut Self::Output {
        &mut self.as_slice_mut()[index]
    }
}

impl Deref for VirtualMemory {
    type Target = [u8];

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl DerefMut for VirtualMemory {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_slice_mut()
    }
}
