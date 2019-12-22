// Copyright 2019 Robin Freyler
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

use crate::parse::{
    operator::*,
    Operator,
    ParseError,
    LinearMemoryId,
};
use core::convert::TryFrom;

impl<'a> TryFrom<wasmparser::Operator<'a>> for Operator {
    type Error = ParseError;

    fn try_from(op: wasmparser::Operator<'a>) -> Result<Self, Self::Error> {
        use wasmparser::Operator as WasmOperator;
        let result_op = match op {
            WasmOperator::Unreachable => Operator::Unreachable,
            WasmOperator::Nop => Operator::Nop,

            WasmOperator::Block { ty } => BlockOp { ty }.into(),
            WasmOperator::Loop { ty } => LoopOp { ty }.into(),
            WasmOperator::If { ty } => IfOp { ty }.into(),
            WasmOperator::Else => Operator::Else,
            WasmOperator::End => Operator::End,

            WasmOperator::Br { relative_depth } => {
                BrOp {
                    relative_depth: relative_depth as usize,
                }
                .into()
            }
            WasmOperator::BrIf { relative_depth } => {
                BrIfOp {
                    relative_depth: relative_depth as usize,
                }
                .into()
            }
            WasmOperator::BrTable { table } => {
                BrTableOp::try_from(table)?.into()
            }

            WasmOperator::Return => Operator::Return,

            WasmOperator::Call { function_index } => {
                CallOp {
                    id: FunctionId(function_index as usize),
                }
                .into()
            }
            WasmOperator::CallIndirect { index, table_index } => {
                CallIndirectOp {
                    table_id: TableId(table_index as usize),
                    offset: index as usize,
                }
                .into()
            }

            WasmOperator::Drop => Operator::Drop,
            WasmOperator::Select => Operator::Select,

            WasmOperator::LocalGet { local_index } => {
                LocalGetOp {
                    id: LocalVariableId(local_index as usize),
                }
                .into()
            }
            WasmOperator::LocalSet { local_index } => {
                LocalSetOp {
                    id: LocalVariableId(local_index as usize),
                }
                .into()
            }
            WasmOperator::LocalTee { local_index } => {
                LocalTeeOp {
                    id: LocalVariableId(local_index as usize),
                }
                .into()
            }

            WasmOperator::GlobalGet { global_index } => {
                GlobalGetOp {
                    id: GlobalVariableId(global_index as usize),
                }
                .into()
            }
            WasmOperator::GlobalSet { global_index } => {
                GlobalSetOp {
                    id: GlobalVariableId(global_index as usize),
                }
                .into()
            }

            WasmOperator::I32Load { memarg } => {
                LoadOp::simple(memarg, IntType::I32).into()
            }
            WasmOperator::I64Load { memarg } => {
                LoadOp::simple(memarg, IntType::I64).into()
            }
            WasmOperator::I32Load8S { memarg } => {
                LoadOp::load_sext(memarg, IntType::I32, ExtIntType::I8)?.into()
            }
            WasmOperator::I32Load8U { memarg } => {
                LoadOp::load_zext(memarg, IntType::I32, ExtIntType::I8)?.into()
            }
            WasmOperator::I32Load16S { memarg } => {
                LoadOp::load_sext(memarg, IntType::I32, ExtIntType::I16)?.into()
            }
            WasmOperator::I32Load16U { memarg } => {
                LoadOp::load_zext(memarg, IntType::I32, ExtIntType::I16)?.into()
            }
            WasmOperator::I64Load8S { memarg } => {
                LoadOp::load_sext(memarg, IntType::I64, ExtIntType::I8)?.into()
            }
            WasmOperator::I64Load8U { memarg } => {
                LoadOp::load_zext(memarg, IntType::I64, ExtIntType::I8)?.into()
            }
            WasmOperator::I64Load16S { memarg } => {
                LoadOp::load_sext(memarg, IntType::I64, ExtIntType::I16)?.into()
            }
            WasmOperator::I64Load16U { memarg } => {
                LoadOp::load_zext(memarg, IntType::I64, ExtIntType::I16)?.into()
            }
            WasmOperator::I64Load32S { memarg } => {
                LoadOp::load_sext(memarg, IntType::I64, ExtIntType::I32)?.into()
            }
            WasmOperator::I64Load32U { memarg } => {
                LoadOp::load_zext(memarg, IntType::I64, ExtIntType::I32)?.into()
            }

            WasmOperator::I32Store { memarg } => {
                StoreOp::simple(memarg, IntType::I32).into()
            }
            WasmOperator::I64Store { memarg } => {
                StoreOp::simple(memarg, IntType::I64).into()
            }
            WasmOperator::I32Store8 { memarg } => {
                StoreOp::store_truncate(memarg, IntType::I32, ExtIntType::I8)?
                    .into()
            }
            WasmOperator::I32Store16 { memarg } => {
                StoreOp::store_truncate(memarg, IntType::I32, ExtIntType::I16)?
                    .into()
            }
            WasmOperator::I64Store8 { memarg } => {
                StoreOp::store_truncate(memarg, IntType::I64, ExtIntType::I8)?
                    .into()
            }
            WasmOperator::I64Store16 { memarg } => {
                StoreOp::store_truncate(memarg, IntType::I64, ExtIntType::I16)?
                    .into()
            }
            WasmOperator::I64Store32 { memarg } => {
                StoreOp::store_truncate(memarg, IntType::I64, ExtIntType::I32)?
                    .into()
            }

            WasmOperator::I32Const { value } => ConstOp::I32(value).into(),
            WasmOperator::I64Const { value } => ConstOp::I64(value).into(),

            WasmOperator::I32Eqz => {
                IntCmpOp::new(IntType::I32, IntCmpOpKind::Eqz).into()
            }
            WasmOperator::I32Eq => {
                IntCmpOp::new(IntType::I32, IntCmpOpKind::Eq).into()
            }
            WasmOperator::I32Ne => {
                IntCmpOp::new(IntType::I32, IntCmpOpKind::Ne).into()
            }
            WasmOperator::I32LtS => {
                IntCmpOp::new(IntType::I32, IntCmpOpKind::Slt).into()
            }
            WasmOperator::I32LtU => {
                IntCmpOp::new(IntType::I32, IntCmpOpKind::Ult).into()
            }
            WasmOperator::I32GtS => {
                IntCmpOp::new(IntType::I32, IntCmpOpKind::Sgt).into()
            }
            WasmOperator::I32GtU => {
                IntCmpOp::new(IntType::I32, IntCmpOpKind::Ugt).into()
            }
            WasmOperator::I32LeS => {
                IntCmpOp::new(IntType::I32, IntCmpOpKind::Sle).into()
            }
            WasmOperator::I32LeU => {
                IntCmpOp::new(IntType::I32, IntCmpOpKind::Ule).into()
            }
            WasmOperator::I32GeS => {
                IntCmpOp::new(IntType::I32, IntCmpOpKind::Sge).into()
            }
            WasmOperator::I32GeU => {
                IntCmpOp::new(IntType::I32, IntCmpOpKind::Uge).into()
            }
            WasmOperator::I64Eqz => {
                IntCmpOp::new(IntType::I64, IntCmpOpKind::Eqz).into()
            }
            WasmOperator::I64Eq => {
                IntCmpOp::new(IntType::I64, IntCmpOpKind::Eq).into()
            }
            WasmOperator::I64Ne => {
                IntCmpOp::new(IntType::I64, IntCmpOpKind::Ne).into()
            }
            WasmOperator::I64LtS => {
                IntCmpOp::new(IntType::I64, IntCmpOpKind::Slt).into()
            }
            WasmOperator::I64LtU => {
                IntCmpOp::new(IntType::I64, IntCmpOpKind::Ult).into()
            }
            WasmOperator::I64GtS => {
                IntCmpOp::new(IntType::I64, IntCmpOpKind::Sgt).into()
            }
            WasmOperator::I64GtU => {
                IntCmpOp::new(IntType::I64, IntCmpOpKind::Ugt).into()
            }
            WasmOperator::I64LeS => {
                IntCmpOp::new(IntType::I64, IntCmpOpKind::Sle).into()
            }
            WasmOperator::I64LeU => {
                IntCmpOp::new(IntType::I64, IntCmpOpKind::Ule).into()
            }
            WasmOperator::I64GeS => {
                IntCmpOp::new(IntType::I64, IntCmpOpKind::Sge).into()
            }
            WasmOperator::I64GeU => {
                IntCmpOp::new(IntType::I64, IntCmpOpKind::Uge).into()
            }

            WasmOperator::I32Clz => {
                CountLeadingZerosOp::new(IntType::I32).into()
            }
            WasmOperator::I32Ctz => {
                CountTrailingZerosOp::new(IntType::I32).into()
            }
            WasmOperator::I32Popcnt => PopcountOp::new(IntType::I32).into(),

            WasmOperator::I64Clz => {
                CountLeadingZerosOp::new(IntType::I64).into()
            }
            WasmOperator::I64Ctz => {
                CountTrailingZerosOp::new(IntType::I64).into()
            }
            WasmOperator::I64Popcnt => PopcountOp::new(IntType::I64).into(),

            WasmOperator::I32Add => AddOp::new(IntType::I32).into(),
            WasmOperator::I32Sub => SubOp::new(IntType::I32).into(),
            WasmOperator::I32Mul => MulOp::new(IntType::I32).into(),
            WasmOperator::I32DivS => SdivOp::new(IntType::I32).into(),
            WasmOperator::I32DivU => UdivOp::new(IntType::I32).into(),
            WasmOperator::I32RemS => SremOp::new(IntType::I32).into(),
            WasmOperator::I32RemU => UremOp::new(IntType::I32).into(),
            WasmOperator::I32And => AndOp::new(IntType::I32).into(),
            WasmOperator::I32Or => OrOp::new(IntType::I32).into(),
            WasmOperator::I32Xor => XorOp::new(IntType::I32).into(),
            WasmOperator::I32Shl => ShlOp::new(IntType::I32).into(),
            WasmOperator::I32ShrS => SshrOp::new(IntType::I32).into(),
            WasmOperator::I32ShrU => UshrOp::new(IntType::I32).into(),
            WasmOperator::I32Rotl => RotLeftOp::new(IntType::I32).into(),
            WasmOperator::I32Rotr => RotRightOp::new(IntType::I32).into(),

            WasmOperator::I64Add => AddOp::new(IntType::I64).into(),
            WasmOperator::I64Sub => SubOp::new(IntType::I64).into(),
            WasmOperator::I64Mul => MulOp::new(IntType::I64).into(),
            WasmOperator::I64DivS => SdivOp::new(IntType::I64).into(),
            WasmOperator::I64DivU => UdivOp::new(IntType::I64).into(),
            WasmOperator::I64RemS => SremOp::new(IntType::I64).into(),
            WasmOperator::I64RemU => UremOp::new(IntType::I64).into(),
            WasmOperator::I64And => AndOp::new(IntType::I64).into(),
            WasmOperator::I64Or => OrOp::new(IntType::I64).into(),
            WasmOperator::I64Xor => XorOp::new(IntType::I64).into(),
            WasmOperator::I64Shl => ShlOp::new(IntType::I64).into(),
            WasmOperator::I64ShrS => SshrOp::new(IntType::I64).into(),
            WasmOperator::I64ShrU => UshrOp::new(IntType::I64).into(),
            WasmOperator::I64Rotl => RotLeftOp::new(IntType::I64).into(),
            WasmOperator::I64Rotr => RotRightOp::new(IntType::I64).into(),

            WasmOperator::MemoryGrow { reserved } => {
                MemoryGrowOp::new(LinearMemoryId(reserved as usize)).into()
            }
            WasmOperator::MemorySize { reserved } => {
                MemorySizeOp::new(LinearMemoryId(reserved as usize)).into()
            }

            WasmOperator::I32WrapI64 => {
                TruncateOp::new(IntType::I32, IntType::I64)?.into()
            }
            WasmOperator::I64ExtendI32S => {
                SignExtendOp::new(IntType::I64, IntType::I32)?.into()
            }
            WasmOperator::I64ExtendI32U => {
                ZeroExtendOp::new(IntType::I64, IntType::I32)?.into()
            }

            unsupported => {
                println!(
                    "encountered unsupported Wasm operator: {:?}",
                    unsupported
                );
                return Err(ParseError::UnsupportedOperator)
            }
        };
        Ok(result_op)
    }
}

impl<'a> TryFrom<wasmparser::BrTable<'a>> for BrTableOp {
    type Error = ParseError;

    fn try_from(table: wasmparser::BrTable<'a>) -> Result<Self, Self::Error> {
        let (relative_depths, default) = table.read_table()?;
        let relative_depths = relative_depths
            .into_iter()
            .map(|&relative_depth| relative_depth as usize)
            .collect::<Vec<_>>()
            .into_boxed_slice();
        let default = default as usize;
        Ok(Self {
            relative_depths,
            default,
        })
    }
}
