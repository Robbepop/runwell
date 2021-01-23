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

use derive_more::{Display, Error};

/// Errors returned by [`Read::read`].
#[derive(Debug, Display, Error, PartialEq, Eq)]
pub enum ReadError {
    /// The source has reached the end of the stream.
    #[display(fmt = "encountered unexpected end of stream")]
    EndOfStream,
    /// An unknown error occurred.
    #[display(fmt = "encountered unknown read error")]
    UnknownError,
}

/// The Read trait allows for reading bytes from a source.
///
/// # Note
///
/// Provides a subset of the interface provided by Rust's [`std::io::Read`][std_io_read] trait.
///
/// [std_io_read]: https://doc.rust-lang.org/std/io/trait.Read.html
pub trait Read {
    /// Pull some bytes from this source into the specified buffer, returning how many bytes were read.
    ///
    /// # Note
    ///
    /// Provides the same guarantees to the caller as [`std::io::Read::read`][io_read_read].
    ///
    /// [io_read_read]: https://doc.rust-lang.org/std/io/trait.Read.html#tymethod.read
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, ReadError>;
}

#[cfg(feature = "std")]
impl<T> Read for T
where
    T: ::std::io::Read,
{
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, ReadError> {
        <T as ::std::io::Read>::read(self, buf).map_err(|err| {
            match err.kind() {
                ::std::io::ErrorKind::UnexpectedEof => ReadError::EndOfStream,
                _ => ReadError::UnknownError,
            }
        })
    }
}

#[cfg(not(feature = "std"))]
impl<'a> Read for &'a [u8] {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, ReadError> {
        let len_copy = core::cmp::min(self.len(), buf.len());
        buf.copy_from_slice(&self[..len_copy]);
        *self = &self[len_copy..];
        Ok(len_copy)
    }
}
