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

//! Implements `Display` for all operators and utility structures used by them.
//!
//! This effort exists mainly to help and support readability while analysing
//! the parsed bytecode. The displayed representation tries to be close to the
//! Wasm spec but will have a special appearance in some aspects for improved
//! readability.

use crate::parse::{operator::*, Identifier, MemoryImmediate};
use core::fmt::{Display, Formatter, Result};

impl Display for BlockOp {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "block")
    }
}

impl Display for LoopOp {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "loop")
    }
}

impl Display for IfOp {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "if")
    }
}

impl Display for BrOp {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "br {}", self.relative_depth)
    }
}

impl Display for BrIfOp {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "brif {}", self.relative_depth)
    }
}

impl Display for BrTableOp {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(
            f,
            "brtable default {}, cases {:?}",
            self.default, &self.relative_depths,
        )
    }
}

impl Display for CallOp {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "call {}", self.id.get(),)
    }
}

impl Display for CallIndirectOp {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(
            f,
            "call_indirect type {}, table {}",
            self.fn_sig_id.get(),
            self.table_id.get(),
        )
    }
}

impl Display for LocalGetOp {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "local.get {}", self.id.get(),)
    }
}

impl Display for LocalSetOp {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "local.set {}", self.id.get(),)
    }
}

impl Display for LocalTeeOp {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "local.tee {}", self.id.get(),)
    }
}

impl Display for GlobalGetOp {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "global.get {}", self.id.get(),)
    }
}

impl Display for GlobalSetOp {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "global.set {}", self.id.get(),)
    }
}

impl Display for MemoryImmediate {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(
            f,
            "offset {}, alignment {}",
            self.offset(),
            self.alignment()
        )
    }
}

impl Display for IntType {
    fn fmt(&self, f: &mut Formatter) -> Result {
        match self {
            IntType::I32 => write!(f, "i32"),
            IntType::I64 => write!(f, "i64"),
        }
    }
}

impl Display for ExtIntType {
    fn fmt(&self, f: &mut Formatter) -> Result {
        match self {
            ExtIntType::I8 => write!(f, "i8"),
            ExtIntType::I16 => write!(f, "i16"),
            ExtIntType::I32 => write!(f, "i32"),
            ExtIntType::I64 => write!(f, "i64"),
        }
    }
}

impl Display for LoadOp {
    fn fmt(&self, f: &mut Formatter) -> Result {
        match self.conversion {
            LoadConversion::NoConversion { ty } => {
                write!(f, "{}.load {}", ty, self.memarg)
            }
            LoadConversion::SignExt {
                result_ty,
                source_ty,
            } => {
                write!(
                    f,
                    "{}.load{}_s {}",
                    result_ty,
                    source_ty.width() * 8,
                    self.memarg,
                )
            }
            LoadConversion::ZeroExt {
                result_ty,
                source_ty,
            } => {
                write!(
                    f,
                    "{}.load{}_u {}",
                    result_ty,
                    source_ty.width() * 8,
                    self.memarg,
                )
            }
        }
    }
}

impl Display for StoreOp {
    fn fmt(&self, f: &mut Formatter) -> Result {
        if self.has_conversion() {
            write!(f, "{}.store{}", self.dst_ty, self.src_ty.width() * 8)
        } else {
            write!(f, "{}.store", self.dst_ty)
        }
    }
}

impl Display for ConstOp {
    fn fmt(&self, f: &mut Formatter) -> Result {
        match self {
            ConstOp::I32(value) => write!(f, "i32.const {}", value),
            ConstOp::I64(value) => write!(f, "i64.const {}", value),
        }
    }
}

impl Display for IntCmpOp {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "{}.{}", self.ty, self.kind)
    }
}

impl Display for IntCmpOpKind {
    fn fmt(&self, f: &mut Formatter) -> Result {
        match self {
            IntCmpOpKind::Eqz => write!(f, "eqz"),
            IntCmpOpKind::Eq => write!(f, "eq"),
            IntCmpOpKind::Ne => write!(f, "ne"),
            IntCmpOpKind::Ule => write!(f, "le_u"),
            IntCmpOpKind::Ult => write!(f, "lt_u"),
            IntCmpOpKind::Uge => write!(f, "gt_u"),
            IntCmpOpKind::Ugt => write!(f, "ge_u"),
            IntCmpOpKind::Sle => write!(f, "le_s"),
            IntCmpOpKind::Slt => write!(f, "lt_s"),
            IntCmpOpKind::Sge => write!(f, "gt_s"),
            IntCmpOpKind::Sgt => write!(f, "ge_s"),
        }
    }
}

macro_rules! impl_display_for_simple_op {
    (
        $(
            struct $name:ident($repr:literal);
        )*
    ) => {
        $(
            impl Display for $name {
                fn fmt(&self, f: &mut Formatter) -> Result {
                    write!(f, "{}.{}", self.ty, $repr)
                }
            }
        )*
    }
}
impl_display_for_simple_op! {
    struct CountLeadingZerosOp("clz");
    struct CountTrailingZerosOp("ctz");
    struct PopcountOp("popcnt");
    struct AddOp("add");
    struct SubOp("sub");
    struct MulOp("mul");
    struct SdivOp("div_s");
    struct UdivOp("div_u");
    struct SremOp("rem_s");
    struct UremOp("rem_u");
    struct AndOp("and");
    struct OrOp("or");
    struct XorOp("xor");
    struct ShlOp("shl");
    struct SshrOp("shr_s");
    struct UshrOp("shr_u");
    struct RotLeftOp("rotl");
    struct RotRightOp("rotr");
}

impl Display for TruncateOp {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "{}.wrap_{}", self.result_ty, self.source_ty.width() * 8)
    }
}

impl Display for ZeroExtendOp {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(
            f,
            "{}.extend_{}_u",
            self.result_ty,
            self.source_ty.width() * 8
        )
    }
}

impl Display for SignExtendOp {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(
            f,
            "{}.extend_{}_s",
            self.result_ty,
            self.source_ty.width() * 8
        )
    }
}

impl Display for MemoryGrowOp {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "memory.grow {}", self.id.get())
    }
}

impl Display for MemorySizeOp {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "memory.size {}", self.id.get())
    }
}

impl Display for Operator {
    fn fmt(&self, f: &mut Formatter) -> Result {
        match self {
            Operator::Unreachable => write!(f, "unreachable"),
            Operator::Nop => write!(f, "nop"),
            Operator::Block(block_op) => block_op.fmt(f),
            Operator::Loop(loop_op) => loop_op.fmt(f),
            Operator::If(if_op) => if_op.fmt(f),
            Operator::Else => write!(f, "else"),
            Operator::End => write!(f, "end"),
            Operator::Br(br_op) => br_op.fmt(f),
            Operator::BrIf(brif_op) => brif_op.fmt(f),
            Operator::BrTable(brtrable_op) => brtrable_op.fmt(f),
            Operator::Return => write!(f, "return"),
            Operator::Call(call_op) => call_op.fmt(f),
            Operator::CallIndirect(call_indirect_op) => call_indirect_op.fmt(f),
            Operator::Drop => write!(f, "drop"),
            Operator::Select => write!(f, "select"),
            Operator::LocalGet(local_get_op) => local_get_op.fmt(f),
            Operator::LocalSet(local_set_op) => local_set_op.fmt(f),
            Operator::LocalTee(local_tee_op) => local_tee_op.fmt(f),
            Operator::GlobalGet(global_get_op) => global_get_op.fmt(f),
            Operator::GlobalSet(global_set_op) => global_set_op.fmt(f),
            Operator::Load(load_op) => load_op.fmt(f),
            Operator::Store(store_op) => store_op.fmt(f),
            Operator::Const(const_op) => const_op.fmt(f),
            Operator::IntCmp(int_cmp_op) => int_cmp_op.fmt(f),
            Operator::CountLeadingZeros(clz_op) => clz_op.fmt(f),
            Operator::CountTrailingZeros(ctz_op) => ctz_op.fmt(f),
            Operator::Popcount(popcnt_op) => popcnt_op.fmt(f),
            Operator::Add(add_op) => add_op.fmt(f),
            Operator::Sub(sub_op) => sub_op.fmt(f),
            Operator::Mul(mul_op) => mul_op.fmt(f),
            Operator::Sdiv(sdiv_op) => sdiv_op.fmt(f),
            Operator::Udiv(udiv_op) => udiv_op.fmt(f),
            Operator::Srem(srem_op) => srem_op.fmt(f),
            Operator::Urem(urem_op) => urem_op.fmt(f),
            Operator::And(and_op) => and_op.fmt(f),
            Operator::Or(or_op) => or_op.fmt(f),
            Operator::Xor(xor_op) => xor_op.fmt(f),
            Operator::Shl(shl_op) => shl_op.fmt(f),
            Operator::Sshr(sshr_op) => sshr_op.fmt(f),
            Operator::Ushr(ushr_op) => ushr_op.fmt(f),
            Operator::RotLeft(rotl_op) => rotl_op.fmt(f),
            Operator::RotRight(rotr_op) => rotr_op.fmt(f),
            Operator::ZeroExtend(zext_op) => zext_op.fmt(f),
            Operator::SignExtend(sext_op) => sext_op.fmt(f),
            Operator::Truncate(trunc_op) => trunc_op.fmt(f),
            Operator::MemoryGrow(mem_grow_op) => mem_grow_op.fmt(f),
            Operator::MemorySize(mem_size_op) => mem_size_op.fmt(f),
        }
    }
}
