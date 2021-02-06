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

//! The tests build up a Runwell IR function and print an output of the function.
//!
//! Note that currently the tests do not automatically test if the constructed
//! function is equal to the tests expectation.
//! Also note that currently no optimizations are performed.
//!
//! Automated checks to verify that the constructed functions match expectations
//! are planned after an API for that has been designed.

use crate::EvaluationContext;
use entity::RawIdx;
use ir::{
    instr::operands::CompareIntOp,
    primitive::{Const, Func, IntConst, IntType, Type, Value},
};
use module::{
    FunctionBody,
    FunctionType,
    InstructionBuilder,
    IrError,
    Module,
    Variable,
};

/// Evaluates the function given the inputs and returns the results.
fn evaluate_function(function: FunctionBody, inputs: &[Const]) -> Vec<u64> {
    let mut builder = Module::build();
    let mut type_builder = builder.type_section().unwrap();
    let func_type = type_builder.push_type({
        let mut b = FunctionType::build();
        for input in inputs {
            b.push_input(input.ty());
        }
        b.push_output(IntType::I32);
        b.finalize()
    });
    let mut function_builder = builder.function_section().unwrap();
    let func = function_builder.push_function(func_type).unwrap();
    let (_view, mut body_builder) = builder.code_section().unwrap();
    body_builder.push_body(func, function).unwrap();
    let module = builder.finalize().unwrap();

    println!("{}", module.get_function(func).unwrap());

    let mut ctx = EvaluationContext::new(&module);
    let mut results = Vec::new();
    ctx.evaluate_function(
        func,
        inputs.iter().copied().map(Const::into_bits64),
        |result| results.push(result),
    )
    .unwrap();
    results
}

#[test]
fn ret_const_works() -> Result<(), IrError> {
    let mut b = FunctionBody::build();
    b.with_inputs(&[])?;
    b.with_outputs(&[IntType::I32.into()])?;
    b.body()?;
    let c = b.ins()?.constant(IntConst::I32(42))?;
    b.ins()?.return_value(c)?;
    let function = b.finalize()?;

    let results = evaluate_function(function, &[]);
    assert_eq!(results, vec![42]);

    Ok(())
}

#[test]
fn simple_block_works() -> Result<(), IrError> {
    let mut b = FunctionBody::build();
    b.with_inputs(&[])?;
    b.with_outputs(&[IntType::I32.into()])?;
    b.body()?;
    let v1 = b.ins()?.constant(IntConst::I32(1))?;
    let v2 = b.ins()?.constant(IntConst::I32(2))?;
    let v3 = b.ins()?.iadd(IntType::I32, v1, v2)?;
    let v3 = b.ins()?.imul(IntType::I32, v3, v3)?;
    b.ins()?.return_value(v3)?;
    let function = b.finalize()?;

    let results = evaluate_function(function, &[]);
    assert_eq!(results, vec![9]);

    Ok(())
}

#[test]
fn if_then_else_works() -> Result<(), IrError> {
    let mut b = FunctionBody::build();
    b.with_inputs(&[])?;
    b.with_outputs(&[IntType::I32.into()])?;
    b.body()?;
    let then_block = b.create_block()?;
    let else_block = b.create_block()?;
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
    let function = b.finalize()?;

    let results = evaluate_function(function, &[]);
    assert_eq!(results, vec![10]);

    Ok(())
}

#[test]
fn simple_variable() -> Result<(), IrError> {
    let mut b = FunctionBody::build();
    b.with_inputs(&[])?;
    b.with_outputs(&[IntType::I32.into()])?;
    b.declare_variables(1, IntType::I32.into())?;
    b.body()?;
    let var = Variable::from_raw(RawIdx::from_u32(0));
    let v1 = b.ins()?.constant(IntConst::I32(1))?;
    b.write_var(var, v1)?;
    let v2 = b.read_var(var)?;
    let v3 = b.ins()?.iadd(IntType::I32, v2, v2)?;
    b.ins()?.return_value(v3)?;
    let function = b.finalize()?;

    let results = evaluate_function(function, &[]);
    assert_eq!(results, vec![2]);

    Ok(())
}

#[test]
fn simple_input() -> Result<(), IrError> {
    let mut b = FunctionBody::build();
    b.with_inputs(&[IntType::I32.into()])?;
    b.with_outputs(&[IntType::I32.into()])?;
    b.body()?;
    let input = Variable::from_raw(RawIdx::from_u32(0));
    let v0 = b.read_var(input)?;
    let v1 = b.ins()?.iadd(IntType::I32, v0, v0)?;
    b.ins()?.return_value(v1)?;
    let function = b.finalize()?;

    let results = evaluate_function(function, &[Const::Int(IntConst::I32(11))]);
    assert_eq!(results, vec![22]);

    Ok(())
}

#[test]
fn simple_gvn_var_read() -> Result<(), IrError> {
    let mut b = FunctionBody::build();
    b.with_inputs(&[IntType::I32.into()])?;
    b.with_outputs(&[IntType::I32.into()])?;
    b.body()?;
    let var = Variable::from_raw(RawIdx::from_u32(0));
    let v0 = b.ins()?.constant(IntConst::I32(1))?;
    b.write_var(var, v0)?;
    let exit_block = b.create_block()?;
    b.ins()?.br(exit_block)?;
    b.switch_to_block(exit_block)?;
    let v0 = b.read_var(var)?;
    b.ins()?.return_value(v0)?;
    b.seal_block()?;
    let function = b.finalize()?;

    let results = evaluate_function(function, &[Const::Int(IntConst::I32(42))]);
    assert_eq!(results, vec![1]);

    Ok(())
}

#[test]
fn simple_gvn_if_works() -> Result<(), IrError> {
    // Setup module.
    let mut builder = Module::build();
    let mut type_builder = builder.type_section().unwrap();
    let func_type = type_builder.push_type({
        let mut b = FunctionType::build();
        b.push_input(IntType::I32);
        b.push_output(IntType::I32);
        b.finalize()
    });
    let mut function_builder = builder.function_section().unwrap();
    let func = function_builder.push_function(func_type).unwrap();
    let (_view, mut body_builder) = builder.code_section().unwrap();

    // Construct function body.
    let mut b = FunctionBody::build();
    b.with_inputs(&[IntType::I32.into()])?;
    b.with_outputs(&[IntType::I32.into()])?;
    b.declare_variables(1, IntType::I32.into())?;
    b.body()?;

    let then_block = b.create_block()?;
    let else_block = b.create_block()?;
    let exit_block = b.create_block()?;

    let input = Variable::from_raw(RawIdx::from_u32(0));
    let var = Variable::from_raw(RawIdx::from_u32(1));

    let v0 = b.read_var(input)?;
    let v1 = b.ins()?.constant(IntConst::I32(0))?;
    let v2 = b.ins()?.icmp(IntType::I32, CompareIntOp::Eq, v0, v1)?;
    b.ins()?.if_then_else(v2, then_block, else_block)?;

    b.switch_to_block(then_block)?;
    let v3 = b.ins()?.constant(IntConst::I32(10))?;
    b.write_var(var, v3)?;
    b.ins()?.br(exit_block)?;
    b.seal_block()?;

    b.switch_to_block(else_block)?;
    let v4 = b.ins()?.constant(IntConst::I32(20))?;
    b.write_var(var, v4)?;
    b.ins()?.br(exit_block)?;
    b.seal_block()?;

    b.switch_to_block(exit_block)?;
    let v5 = b.read_var(var)?;
    b.ins()?.return_value(v5)?;
    b.seal_block()?;

    let function = b.finalize()?;

    body_builder.push_body(func, function).unwrap();
    let module = builder.finalize().unwrap();

    println!("{}", module.get_function(func).unwrap());

    let mut ctx = EvaluationContext::new(&module);
    let mut results = Vec::new();
    ctx.evaluate_function(func, vec![0], |result| results.push(result))
        .unwrap();
    assert_eq!(results, vec![10]);
    results.clear();
    ctx.evaluate_function(func, vec![1], |result| results.push(result))
        .unwrap();
    assert_eq!(results, vec![20]);

    Ok(())
}

#[test]
fn simple_loop_works() -> Result<(), IrError> {
    let mut b = FunctionBody::build();
    b.with_inputs(&[IntType::I32.into()])?;
    b.with_outputs(&[IntType::I32.into()])?;
    b.declare_variables(1, IntType::I32.into())?;
    b.declare_variables(1, IntType::I32.into())?;
    b.body()?;

    let loop_head = b.create_block()?;
    let loop_body = b.create_block()?;
    let loop_exit = b.create_block()?;

    let input = Variable::from_raw(RawIdx::from_u32(0));
    let counter = Variable::from_raw(RawIdx::from_u32(1));
    let one = Variable::from_raw(RawIdx::from_u32(2));

    let v0 = b.ins()?.constant(IntConst::I32(0))?;
    let v0_1 = b.ins()?.constant(IntConst::I32(1))?;
    b.write_var(counter, v0)?;
    b.write_var(one, v0_1)?;
    b.ins()?.br(loop_head)?;

    b.switch_to_block(loop_head)?;
    let v1 = b.read_var(counter)?;
    let v2 = b.read_var(input)?;
    let v3 = b.ins()?.icmp(IntType::I32, CompareIntOp::Slt, v1, v2)?;
    b.ins()?.if_then_else(v3, loop_body, loop_exit)?;

    b.switch_to_block(loop_body)?;
    b.seal_block()?;
    let v4 = b.read_var(counter)?;
    let v5 = b.read_var(one)?;
    let v6 = b.ins()?.iadd(IntType::I32, v4, v5)?;
    b.write_var(counter, v6)?;
    b.ins()?.br(loop_head)?;

    b.switch_to_block(loop_head)?;
    b.seal_block()?;

    b.switch_to_block(loop_exit)?;
    b.seal_block()?;
    let v7 = b.read_var(counter)?;
    b.ins()?.return_value(v7)?;

    let function = b.finalize()?;

    let iterations = 100;
    let results =
        evaluate_function(function, &[Const::Int(IntConst::I32(iterations))]);
    assert_eq!(results, vec![iterations as u64]);

    Ok(())
}

fn construct_is_even_and_is_odd<F>(
    mut f: F,
) -> Result<(Module, Func, Func), IrError>
where
    F: FnMut(InstructionBuilder, Func, Value) -> Result<Value, IrError>,
{
    // Setup module.
    let mut builder = Module::build();
    let mut type_builder = builder.type_section().unwrap();
    let func_type = type_builder.push_type({
        let mut b = FunctionType::build();
        b.push_input(IntType::I32);
        b.push_output(Type::Bool);
        b.finalize()
    });
    // Pre declare functions used before they are defined.
    let mut function_builder = builder.function_section().unwrap();
    let is_even = function_builder.push_function(func_type).unwrap();
    let is_odd = function_builder.push_function(func_type).unwrap();

    // Create Function: is_even
    //
    // Encodes `is_even` as follows:
    //
    // is_odd(x):
    //     if x == 0:
    //         return true
    //     return is_odd(x - 1)

    let mut b = FunctionBody::build();
    b.with_inputs(&[IntType::I32.into()])?;
    b.with_outputs(&[Type::Bool])?;
    b.body()?;

    let if_zero = b.create_block()?;
    let if_not_zero = b.create_block()?;

    let input = Variable::from_raw(RawIdx::from_u32(0));

    let v0 = b.read_var(input)?;
    let v1 = b.ins()?.constant(IntConst::I32(0))?;
    let v2 = b.ins()?.icmp(IntType::I32, CompareIntOp::Eq, v0, v1)?;
    b.ins()?.if_then_else(v2, if_zero, if_not_zero)?;

    b.switch_to_block(if_zero)?;
    let v3 = b.ins()?.constant(Const::Bool(true))?;
    b.ins()?.return_value(v3)?;
    b.seal_block()?;

    b.switch_to_block(if_not_zero)?;
    let v4 = b.read_var(input)?;
    let v5 = b.ins()?.constant(IntConst::I32(1))?;
    let v6 = b.ins()?.isub(IntType::I32, v4, v5)?;
    let v7 = f(b.ins()?, is_odd, v6)?;
    b.ins()?.return_value(v7)?;
    b.seal_block()?;
    let is_even_body = b.finalize()?;

    // Create Function: is_odd
    //
    // Encodes `is_odd` as follows:
    //
    // is_odd(x):
    //     if x == 0:
    //         return false
    //     return is_even(x - 1)

    let mut b = FunctionBody::build();
    b.with_inputs(&[IntType::I32.into()])?;
    b.with_outputs(&[Type::Bool])?;
    b.body()?;

    let if_zero = b.create_block()?;
    let if_not_zero = b.create_block()?;

    let input = Variable::from_raw(RawIdx::from_u32(0));

    let v0 = b.read_var(input)?;
    let v1 = b.ins()?.constant(IntConst::I32(0))?;
    let v2 = b.ins()?.icmp(IntType::I32, CompareIntOp::Eq, v0, v1)?;
    b.ins()?.if_then_else(v2, if_zero, if_not_zero)?;

    b.switch_to_block(if_zero)?;
    let v3 = b.ins()?.constant(Const::Bool(false))?;
    b.ins()?.return_value(v3)?;
    b.seal_block()?;

    b.switch_to_block(if_not_zero)?;
    let v4 = b.read_var(input)?;
    let v5 = b.ins()?.constant(IntConst::I32(1))?;
    let v6 = b.ins()?.isub(IntType::I32, v4, v5)?;
    let v7 = f(b.ins()?, is_even, v6)?;
    b.ins()?.return_value(v7)?;
    b.seal_block()?;
    let is_odd_body = b.finalize()?;

    let (_view, mut body_builder) = builder.code_section().unwrap();
    body_builder.push_body(is_even, is_even_body).unwrap();
    body_builder.push_body(is_odd, is_odd_body).unwrap();
    let module = builder.finalize().unwrap();

    println!("{}", module.get_function(is_even).unwrap());
    println!("{}", module.get_function(is_odd).unwrap());

    Ok((module, is_even, is_odd))
}

#[test]
fn ping_pong_calls() -> Result<(), IrError> {
    let (module, is_even, is_odd) =
        construct_is_even_and_is_odd(|ins, func, v6| ins.call(func, vec![v6]))?;

    let mut ctx = EvaluationContext::new(&module);
    let mut results = Vec::new();

    let input = 100;
    ctx.evaluate_function(is_even, vec![input], |result| results.push(result))
        .unwrap();
    assert_eq!(results, vec![(input % 2 == 0) as u64]);

    results.clear();
    ctx.evaluate_function(is_odd, vec![input], |result| results.push(result))
        .unwrap();
    assert_eq!(results, vec![(input % 2 == 1) as u64]);

    Ok(())
}

#[test]
fn ping_pong_tail_calls() -> Result<(), IrError> {
    let (module, is_even, is_odd) =
        construct_is_even_and_is_odd(|ins, func, v6| {
            ins.tail_call(func, vec![v6])
        })?;

    let mut ctx = EvaluationContext::new(&module);
    let mut results = Vec::new();

    let input = 100;
    ctx.evaluate_function(is_even, vec![input], |result| results.push(result))
        .unwrap();
    assert_eq!(results, vec![(input % 2 == 0) as u64]);

    results.clear();
    ctx.evaluate_function(is_odd, vec![input], |result| results.push(result))
        .unwrap();
    assert_eq!(results, vec![(input % 2 == 1) as u64]);

    Ok(())
}
