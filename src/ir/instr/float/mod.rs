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

mod binary;
mod fcmp;
mod fconv;
mod unary;

pub use self::{
    binary::{
        BinaryFloatInstr,
        FaddInstr,
        FcopysignInstr,
        FdivInstr,
        FmaxInstr,
        FminInstr,
        FmulInstr,
        FsubInstr,
    },
    fcmp::{FcompareInstr, FcompareOp},
    fconv::{FdemoteInstr, FpromoteInstr},
    unary::{
        FabsInstr,
        FnegInstr,
        FsqrtInstr,
        FceilInstr,
        FfloorInstr,
        FtruncateInstr,
        FnearestInstr,
        UnaryFloatInstr,
    },
};