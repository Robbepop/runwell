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
mod icmp;
mod iconv;
mod shift;
mod unary;

pub use self::{
    binary::{
        IaddInstr,
        IandInstr,
        BinaryIntInstr,
        ImulInstr,
        IorInstr,
        SdivInstr,
        SremInstr,
        IsubInstr,
        UdivInstr,
        UremInstr,
        IxorInstr,
    },
    icmp::{IcompareInstr, IcompareOp},
    iconv::{SextendInstr, ItruncateInstr, UextendInstr},
    shift::{
        IrotlInstr,
        IrotrInstr,
        ShiftInstr,
        ShlInstr,
        SshlrInstr,
        UshlrInstr,
    },
    unary::{
        IleadingZerosInstr,
        IpopCountInstr,
        ItrailingZerosInstr,
        UnaryIntInstr,
    },
};