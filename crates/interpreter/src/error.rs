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

use ir::primitive::{Const, Type, Value};
use derive_more::{Display, Error};

/// An error that may occure while evaluating a function.
#[derive(Debug, Display, Error, PartialEq, Eq, Hash)]
pub enum InterpretationError {
    #[display(fmt = "the function evaluation has trapped")]
    EvaluationHasTrapped,
    #[display(
        fmt = "tried to initialize the non-input {} to {}",
        non_input,
        init
    )]
    TriedToInitializeNonInput { non_input: Value, init: Const },
    #[display(
        fmt = "tried to initialize input {} with type {} that requires type {}",
        value,
        given_type,
        expected_type
    )]
    UnmatchingInputTypes {
        value: Value,
        given_type: Type,
        expected_type: Type,
    },
    #[display(fmt = "tried to read uninitialized input {}", input)]
    UninitializedInput { input: Value },
    #[display(
        fmt = "encountered duplicate output values. first: {:?}, second: {:?}",
        prev_return_value,
        return_value
    )]
    AlreadySetReturnValue {
        return_value: Vec<u64>,
        prev_return_value: Vec<u64>,
    },
    #[display(
        fmt = "provided {} inputs for a function evaluation but require {}",
        given_inputs,
        required_inputs
    )]
    UnmatchingInputValues {
        given_inputs: usize,
        required_inputs: usize,
    },
}
