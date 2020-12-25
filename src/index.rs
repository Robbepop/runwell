// Copyright 2020 Robin Freyler
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

/// An index in the 2^32 space.
pub trait Index32: Copy {
    /// Converts the raw `u32` index into `Self`:
    fn from_u32(index: u32) -> Self;
    /// Converts the index to the underlying `u32` representation.
    fn into_u32(self) -> u32;
}

/// Defines a new 32-bit space optimized index type.
macro_rules! define_id_type {
    ( $( #[$attr:meta] )* pub struct $name:ident ; ) => {
        $( #[ $attr ] )*
        #[derive(
            ::core::fmt::Debug,
            ::core::marker::Copy,
            ::core::clone::Clone,
            ::core::cmp::PartialEq,
            ::core::cmp::Eq,
            ::core::cmp::PartialOrd,
            ::core::cmp::Ord,
            ::core::hash::Hash,
        )]
        pub struct $name {
            index: ::core::num::NonZeroU32,
        }

        impl crate::Index32 for $name {
            /// Creates a new instance from the given `u32`.
            ///
            /// # Panics
            ///
            /// If the given `u32` is equal to `u32::MAX`.
            fn from_u32(index: ::core::primitive::u32) -> Self {
                Self {
                    index: ::core::num::NonZeroU32::new(index.wrapping_add(1))
                        .expect("encountered invalid u32::MAX value"),
                }
            }

            /// Returns the underlying raw `u32` representation.
            fn into_u32(self) -> ::core::primitive::u32 {
                self.index.get().wrapping_sub(1)
            }
        }
    };
}
