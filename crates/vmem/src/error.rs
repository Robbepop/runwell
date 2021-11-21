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

use core::{
    fmt,
    fmt::{Debug, Display, Formatter},
};

/// An error originating from the `region` crate.
#[derive(Debug)]
pub struct RegionError(region::Error);

impl Display for RegionError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

impl From<region::Error> for RegionError {
    fn from(error: region::Error) -> Self {
        Self(error)
    }
}

#[cfg(
    // Comparing virtual memories is a very costly operation
    // that should not be supported or used outside of test code.
    test
)]
impl PartialEq for RegionError {
    fn eq(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (region::Error::UnmappedRegion, region::Error::UnmappedRegion) => {
                true
            }
            (
                region::Error::InvalidParameter(lhs),
                region::Error::InvalidParameter(rhs),
            ) => lhs == rhs,
            (
                region::Error::ProcfsInput(lhs),
                region::Error::ProcfsInput(rhs),
            ) => lhs == rhs,
            (
                region::Error::SystemCall(lhs),
                region::Error::SystemCall(rhs),
            ) => lhs.kind() == rhs.kind(),
            (region::Error::MachCall(lhs), region::Error::MachCall(rhs)) => {
                lhs == rhs
            }
            _ => false,
        }
    }
}

/// An error that may occur upon operating with virtual memory.
#[derive(Debug)]
#[cfg_attr(test, derive(PartialEq))]
#[non_exhaustive]
pub enum Error {
    Region(RegionError),
}

impl From<region::Error> for Error {
    fn from(error: region::Error) -> Self {
        Self::Region(RegionError::from(error))
    }
}

impl From<RegionError> for Error {
    fn from(error: RegionError) -> Self {
        Self::Region(error)
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Region(region) => Display::fmt(region, f),
        }
    }
}
