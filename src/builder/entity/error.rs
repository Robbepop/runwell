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

use derive_more::{Display, Error};

#[derive(Debug, Display, Error)]
pub enum EntityError {
    #[display(
        fmt = "encountered duplicate reservation for internal entities. previous: {}, actual: {}",
        previous_reservation,
        actual_reservation
    )]
    DuplicateReservedInternals {
        previous_reservation: usize,
        actual_reservation: usize,
    },
    #[display(
        fmt = "tried to push more internal entities than reserved. reserved: {}",
        reserved
    )]
    TooManyDefinitions { reserved: usize },
    #[display(
        fmt = "tried to push an imported entity after pushing internal entities. count internal entities: {}",
        count_internal
    )]
    PushImportAfterInternals { count_internal: usize },
}
