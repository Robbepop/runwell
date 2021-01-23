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

use super::Function;
use crate::{
    entity::RawIdx,
    ir::{
        instruction::CompareIntOp,
        primitive::{IntConst, IntType},
        IrError,
        Variable,
    },
};

#[test]
fn ret_const_works() -> Result<(), IrError> {
    let mut b = Function::build()
        .with_inputs(&[])?
        .with_outputs(&[])?
        .body();
    let c = b.ins()?.constant(IntConst::I32(42))?;
    b.ins()?.return_value(c)?;
    let fun = b.finalize()?;
    println!("{}", fun);
    Ok(())
}

#[test]
fn simple_block_works() -> Result<(), IrError> {
    let mut b = Function::build()
        .with_inputs(&[])?
        .with_outputs(&[])?
        .body();
    let v1 = b.ins()?.constant(IntConst::I32(1))?;
    let v2 = b.ins()?.constant(IntConst::I32(2))?;
    let v3 = b.ins()?.iadd(IntType::I32, v1, v2)?;
    let v3 = b.ins()?.imul(IntType::I32, v3, v3)?;
    b.ins()?.return_value(v3)?;
    let fun = b.finalize()?;
    println!("{}", fun);
    Ok(())
}

#[test]
fn if_then_else_works() -> Result<(), IrError> {
    let mut b = Function::build()
        .with_inputs(&[])?
        .with_outputs(&[])?
        .body();
    let then_block = b.create_block();
    let else_block = b.create_block();
    let v1 = b.ins()?.constant(IntConst::I32(1))?;
    let v2 = b.ins()?.constant(IntConst::I32(2))?;
    let v3 = b.ins()?.icmp(IntType::I32, CompareIntOp::Ule, v1, v2)?;
    let _v4 = b.ins()?.if_then_else(v3, then_block, else_block)?;
    b.switch_to_block(then_block)?;
    let v5 = b.ins()?.constant(IntConst::I32(10))?;
    b.ins()?.return_value(v5)?;
    b.seal_block()?;
    b.switch_to_block(else_block)?;
    let v6 = b.ins()?.constant(IntConst::I32(20))?;
    b.ins()?.return_value(v6)?;
    b.seal_block()?;
    let fun = b.finalize()?;
    println!("{}", fun);
    Ok(())
}

#[test]
fn simple_variable() -> Result<(), IrError> {
    let mut b = Function::build()
        .with_inputs(&[])?
        .with_outputs(&[])?
        .declare_variables(1, IntType::I32.into())?
        .body();
    let var = Variable::from_raw(RawIdx::from_u32(0));
    let v1 = b.ins()?.constant(IntConst::I32(1))?;
    b.write_var(var, v1)?;
    let v2 = b.read_var(var)?;
    let v3 = b.ins()?.iadd(IntType::I32, v2, v2)?;
    b.ins()?.return_value(v3)?;
    let fun = b.finalize()?;
    println!("{}", fun);
    Ok(())
}

#[test]
fn simple_input() -> Result<(), IrError> {
    let mut b = Function::build()
        .with_inputs(&[IntType::I32.into()])?
        .with_outputs(&[IntType::I32.into()])?
        .body();
    let input = Variable::from_raw(RawIdx::from_u32(0));
    let v0 = b.read_var(input)?;
    let v1 = b.ins()?.iadd(IntType::I32, v0, v0)?;
    b.ins()?.return_value(v1)?;
    let fun = b.finalize()?;
    println!("{}", fun);
    Ok(())
}

#[test]
fn simple_gvn_var_read() -> Result<(), IrError> {
    let mut b = Function::build()
        .with_inputs(&[IntType::I32.into()])?
        .with_outputs(&[])?
        .body();
    let var = Variable::from_raw(RawIdx::from_u32(0));
    let v0 = b.ins()?.constant(IntConst::I32(1))?;
    b.write_var(var, v0)?;
    let exit_block = b.create_block();
    b.ins()?.br(exit_block)?;
    b.switch_to_block(exit_block)?;
    let v0 = b.read_var(var)?;
    b.ins()?.return_value(v0)?;
    b.seal_block()?;
    let fun = b.finalize()?;
    println!("{}", fun);
    Ok(())
}
