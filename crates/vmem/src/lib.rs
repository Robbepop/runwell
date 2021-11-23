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
//! other than 64 kB.

mod error;

#[cfg(test)]
mod tests;

pub use self::error::{Error, RegionError};
use core::{
    fmt,
    fmt::{Debug, Formatter},
    ops::{Deref, DerefMut, Index, IndexMut},
    slice::{self, SliceIndex},
};

/// A virtually allocated memory.
///
/// # Developer Note
///
/// - Since instances of this type are always created with a read and write protection it is safe
///   to dereference instances into slices of bytes.
/// - Cannot implement `Clone`, `Copy` because of non-trivial destructor of `region::Allocation`.
/// - Cannot implement other standard traits such as `PartialEq`, `PartialOrd` or `Hash` efficiently.
///   If a user needs this they shall convert the virtual allocation into a slice.
/// - The Virtual memory allocation or anonymously mapped memory is initialized to zero.
pub struct VirtualMemory {
    allocation: region::Allocation,
}

impl Debug for VirtualMemory {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_struct("VirtualMemory")
            .field("capacity", &self.capacity())
            .field("bytes", &self.as_slice())
            .finish()
    }
}

#[cfg(
    // Comparing virtual memories is a very costly operation
    // due to the fact that most often virtual memory is allocated
    // with a huge capacity where most bytes are unused.
    // Therefore the equality operation should not be supported directly.
    test
)]
impl PartialEq for VirtualMemory {
    fn eq(&self, other: &Self) -> bool {
        // Comparing the slices works since virtual memories are zero initialized.
        // Two virtual memories with the same capcaity and memory contents are
        // treated as equal to each other.
        self.as_slice() == other.as_slice()
    }
}

#[allow(clippy::len_without_is_empty)]
impl VirtualMemory {
    /// Creates a new virtual memory with a capacity for at least the given amount of bytes.
    ///
    /// # Note
    ///
    /// The resulting capacity of the virtual memory might be greater than requested.
    pub fn new(capacity: usize) -> Result<Self, Error> {
        let allocation =
            region::alloc(capacity, region::Protection::READ_WRITE)?;
        Ok(Self { allocation })
    }

    /// Returns the capacity of the virtually allocated buffer.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.allocation.len()
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
                self.capacity(),
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
                self.capacity(),
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
