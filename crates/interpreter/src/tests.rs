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
    primitive::{
        Const,
        FloatConst,
        FloatType,
        Func,
        IntConst,
        IntType,
        Type,
        Value,
    },
};
use module::{
    primitive::{FunctionType, Instr, Variable},
    FunctionBody,
    FunctionBuilder,
    InstructionBuilder,
    Module,
};

/// Evaluates the function given the inputs and returns the results.
fn module_with_func<F>(
    inputs: &[Type],
    outputs: &[Type],
    f: F,
) -> (Func, Module)
where
    F: FnOnce(&mut FunctionBuilder) -> Result<(), module::Error>,
{
    let mut builder = Module::build();
    let mut type_builder = builder.type_section().unwrap();
    let func_type = type_builder.push_type({
        let mut b = FunctionType::build();
        for input in inputs {
            b.push_input(*input);
        }
        for output in outputs {
            b.push_output(*output);
        }
        b.finalize()
    });
    let mut function_builder = builder.function_section().unwrap();
    let func = function_builder.push_function(func_type).unwrap();
    let (res, mut body_builder) = builder.code_section().unwrap();
    let mut func_builder = FunctionBody::build(func, res);
    f(&mut func_builder).unwrap();
    let func_body = func_builder.finalize().unwrap();
    body_builder.push_body(func, func_body).unwrap();
    let module = builder.finalize().unwrap();

    println!("{}", module.get_function(func).unwrap());

    (func, module)
}

fn evaluate_func(module: &Module, func: Func, inputs: &[Const]) -> Vec<u64> {
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

fn bits_into_const(module: &Module, func: Func, bits: Vec<u64>) -> Vec<Const> {
    let outputs = module.get_function(func).unwrap().outputs();
    bits.into_iter()
        .zip(outputs)
        .map(|(bits, ty)| {
            match ty {
                Type::Bool => {
                    assert!(bits <= 1);
                    Const::Bool(bits != 0)
                }
                Type::Ptr => {
                    assert!(bits & ((0x1 << 16) - 1) == 0);
                    Const::Ptr(bits as u32)
                }
                Type::Int(IntType::I8) => IntConst::I8(bits as i8).into(),
                Type::Int(IntType::I16) => IntConst::I16(bits as i16).into(),
                Type::Int(IntType::I32) => IntConst::I32(bits as i32).into(),
                Type::Int(IntType::I64) => IntConst::I64(bits as i64).into(),
                Type::Float(FloatType::F32) => {
                    FloatConst::F32(f32::from_bits(bits as u32).into()).into()
                }
                Type::Float(FloatType::F64) => {
                    FloatConst::F64(f64::from_bits(bits as u64).into()).into()
                }
            }
        })
        .collect::<Vec<_>>()
}

#[test]
fn ret_const_works() -> Result<(), module::Error> {
    let (func, module) = module_with_func(&[], &[IntType::I32.into()], |b| {
        b.body()?;
        let c = b.ins()?.constant(IntConst::I32(42))?;
        b.ins()?.return_values([c].iter().copied())?;
        Ok(())
    });
    let result = evaluate_func(&module, func, &[]);
    assert_eq!(result, vec![42]);
    Ok(())
}

#[test]
fn simple_block_works() -> Result<(), module::Error> {
    let (func, module) = module_with_func(&[], &[IntType::I32.into()], |b| {
        b.body()?;
        let v1 = b.ins()?.constant(IntConst::I32(1))?;
        let v2 = b.ins()?.constant(IntConst::I32(2))?;
        let v3 = b.ins()?.iadd(IntType::I32, v1, v2)?;
        let v3 = b.ins()?.imul(IntType::I32, v3, v3)?;
        b.ins()?.return_values([v3].iter().copied())?;
        Ok(())
    });
    let result = evaluate_func(&module, func, &[]);
    assert_eq!(result, vec![9]);
    Ok(())
}

#[test]
fn if_then_else_works() -> Result<(), module::Error> {
    let (func, module) = module_with_func(&[], &[IntType::I32.into()], |b| {
        b.body()?;
        let then_block = b.create_block()?;
        let else_block = b.create_block()?;
        let v1 = b.ins()?.constant(IntConst::I32(1))?;
        let v2 = b.ins()?.constant(IntConst::I32(2))?;
        let v3 = b.ins()?.icmp(IntType::I32, CompareIntOp::Ule, v1, v2)?;
        let _v4 = b.ins()?.if_then_else(v3, then_block, else_block)?;
        b.switch_to_block(then_block)?;
        let v5 = b.ins()?.constant(IntConst::I32(10))?;
        b.ins()?.return_values([v5].iter().copied())?;
        b.seal_block()?;
        b.switch_to_block(else_block)?;
        let v6 = b.ins()?.constant(IntConst::I32(20))?;
        b.ins()?.return_values([v6].iter().copied())?;
        b.seal_block()?;
        Ok(())
    });
    let result = evaluate_func(&module, func, &[]);
    assert_eq!(result, vec![10]);
    Ok(())
}

#[test]
fn simple_variable() -> Result<(), module::Error> {
    let (func, module) = module_with_func(&[], &[IntType::I32.into()], |b| {
        b.declare_variables(1, IntType::I32.into())?;
        b.body()?;
        let var = Variable::from_raw(RawIdx::from_u32(0));
        let v1 = b.ins()?.constant(IntConst::I32(1))?;
        b.write_var(var, v1)?;
        let v2 = b.read_var(var)?;
        let v3 = b.ins()?.iadd(IntType::I32, v2, v2)?;
        b.ins()?.return_values([v3].iter().copied())?;
        Ok(())
    });
    let result = evaluate_func(&module, func, &[]);
    assert_eq!(result, vec![2]);
    Ok(())
}

#[test]
fn double_input() -> Result<(), module::Error> {
    let (func, module) =
        module_with_func(&[IntType::I32.into()], &[IntType::I32.into()], |b| {
            b.body()?;
            let input = Variable::from_raw(RawIdx::from_u32(0));
            let v0 = b.read_var(input)?;
            let v1 = b.ins()?.iadd(IntType::I32, v0, v0)?;
            b.ins()?.return_values([v1].iter().copied())?;
            Ok(())
        });
    for x in -10..10 {
        let result = evaluate_func(&module, func, &[IntConst::I32(x).into()]);
        let result = bits_into_const(&module, func, result);
        assert_eq!(result, vec![IntConst::I32(x * 2).into()]);
    }
    Ok(())
}

#[test]
fn global_identity_using_local() -> Result<(), module::Error> {
    let (func, module) =
        module_with_func(&[IntType::I32.into()], &[IntType::I32.into()], |b| {
            b.declare_variables(1, IntType::I32.into())?;
            b.body()?;

            let input = Variable::from_raw(RawIdx::from_u32(0));
            let local = Variable::from_raw(RawIdx::from_u32(1));
            let v0 = b.read_var(input)?;
            b.write_var(local, v0)?;
            let exit_block = b.create_block()?;
            b.ins()?.br(exit_block)?;
            b.switch_to_block(exit_block)?;
            let v0 = b.read_var(local)?;
            b.ins()?.return_values([v0].iter().copied())?;
            b.seal_block()?;

            Ok(())
        });
    for x in -10..10 {
        let value = IntConst::I32(x).into();
        let result = evaluate_func(&module, func, &[value]);
        let result = bits_into_const(&module, func, result);
        assert_eq!(result, vec![value]);
    }
    Ok(())
}

#[test]
fn inconveniently_written_min() -> Result<(), module::Error> {
    let (func, module) = module_with_func(
        &[IntType::I32.into(); 2][..],
        &[IntType::I32.into()],
        |b| {
            b.declare_variables(1, IntType::I32.into())?;
            b.body()?;

            let then_block = b.create_block()?;
            let else_block = b.create_block()?;
            let exit_block = b.create_block()?;

            let lhs = Variable::from_raw(RawIdx::from_u32(0));
            let rhs = Variable::from_raw(RawIdx::from_u32(1));
            let result = Variable::from_raw(RawIdx::from_u32(2));

            let v0 = b.read_var(lhs)?;
            let v1 = b.read_var(rhs)?;
            let v2 = b.ins()?.icmp(IntType::I32, CompareIntOp::Slt, v0, v1)?;
            b.ins()?.if_then_else(v2, then_block, else_block)?;

            b.switch_to_block(then_block)?;
            b.seal_block()?;
            let v3 = b.read_var(lhs)?;
            b.write_var(result, v3)?;
            b.ins()?.br(exit_block)?;

            b.switch_to_block(else_block)?;
            b.seal_block()?;
            let v4 = b.read_var(rhs)?;
            b.write_var(result, v4)?;
            b.ins()?.br(exit_block)?;

            b.switch_to_block(exit_block)?;
            let v5 = b.read_var(result)?;
            b.ins()?.return_values([v5].iter().copied())?;
            b.seal_block()?;

            Ok(())
        },
    );
    for x in -10..10 {
        for y in -5..15 {
            let x = IntConst::I32(x).into();
            let y = IntConst::I32(y).into();
            let result = evaluate_func(&module, func, &[x, y]);
            let result = bits_into_const(&module, func, result);
            assert_eq!(result, vec![if x < y { x } else { y }]);
        }
    }
    Ok(())
}

#[test]
fn binary_swap_works() -> Result<(), module::Error> {
    let (func, module) = module_with_func(
        &[IntType::I32.into(); 2][..],
        &[IntType::I32.into(); 2][..],
        |b| {
            b.body()?;

            let lhs = Variable::from_raw(RawIdx::from_u32(0));
            let rhs = Variable::from_raw(RawIdx::from_u32(1));

            let v0 = b.read_var(lhs)?;
            let v1 = b.read_var(rhs)?;
            b.ins()?.return_values([v1, v0].iter().copied())?;

            Ok(())
        },
    );
    for x in -10..10 {
        for y in -10..10 {
            let x = IntConst::I32(x).into();
            let y = IntConst::I32(y).into();
            let result = evaluate_func(&module, func, &[x, y]);
            let _result = bits_into_const(&module, func, result);
            // assert_eq!(result, vec![y, x]);
        }
    }
    Ok(())
}

#[test]
fn counting_loop_works() -> Result<(), module::Error> {
    let (func, module) =
        module_with_func(&[IntType::I32.into()], &[IntType::I32.into()], |b| {
            b.declare_variables(2, IntType::I32.into())?;
            b.body()?;

            let loop_head = b.create_block()?;
            let loop_body = b.create_block()?;
            let loop_exit = b.create_block()?;

            let input = Variable::from_raw(RawIdx::from_u32(0));
            let counter = Variable::from_raw(RawIdx::from_u32(1));
            let one = Variable::from_raw(RawIdx::from_u32(2));

            let v0 = b.ins()?.constant(IntConst::I32(0))?;
            let v1 = b.ins()?.constant(IntConst::I32(1))?;
            b.write_var(counter, v0)?;
            b.write_var(one, v1)?;
            b.ins()?.br(loop_head)?;

            b.switch_to_block(loop_head)?;
            let v2 = b.read_var(counter)?;
            let v3 = b.read_var(input)?;
            let v4 = b.ins()?.icmp(IntType::I32, CompareIntOp::Slt, v2, v3)?;
            b.ins()?.if_then_else(v4, loop_body, loop_exit)?;

            b.switch_to_block(loop_body)?;
            let v5 = b.read_var(counter)?;
            let v6 = b.read_var(one)?;
            let v7 = b.ins()?.iadd(IntType::I32, v5, v6)?;
            b.write_var(counter, v7)?;
            b.ins()?.br(loop_head)?;
            b.seal_block()?;

            b.switch_to_block(loop_head)?;
            b.seal_block()?;

            b.switch_to_block(loop_exit)?;
            b.seal_block()?;
            let v8 = b.read_var(counter)?;
            b.ins()?.return_values([v8].iter().copied())?;

            Ok(())
        });
    for count_until in 0..10 {
        let count_until = IntConst::I32(count_until).into();
        let result = evaluate_func(&module, func, &[count_until]);
        let result = bits_into_const(&module, func, result);
        assert_eq!(result, vec![count_until]);
    }
    Ok(())
}

fn construct_is_even_and_is_odd<F>(
    mut f: F,
) -> Result<(Module, Func, Func), module::Error>
where
    F: FnMut(InstructionBuilder, Func, Value) -> Result<Instr, module::Error>,
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
    let (res, mut body_builder) = builder.code_section().unwrap();

    // Create Function: is_even
    //
    // Encodes `is_even` as follows:
    //
    // is_odd(x):
    //     if x == 0:
    //         return true
    //     return is_odd(x - 1)

    let mut b = FunctionBody::build(is_even, res);
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
    b.ins()?.return_values([v3].iter().copied())?;
    b.seal_block()?;

    b.switch_to_block(if_not_zero)?;
    let v4 = b.read_var(input)?;
    let v5 = b.ins()?.constant(IntConst::I32(1))?;
    let v6 = b.ins()?.isub(IntType::I32, v4, v5)?;
    let instr = f(b.ins()?, is_odd, v6)?;
    if let Some((&v7, rest)) = b.instr_values(instr)?.split_first() {
        assert!(rest.is_empty(), "is_odd only has a single output value");
        b.ins()?.return_values([v7].iter().copied())?;
    }
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

    let mut b = FunctionBody::build(is_odd, res);
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
    b.ins()?.return_values([v3].iter().copied())?;
    b.seal_block()?;

    b.switch_to_block(if_not_zero)?;
    let v4 = b.read_var(input)?;
    let v5 = b.ins()?.constant(IntConst::I32(1))?;
    let v6 = b.ins()?.isub(IntType::I32, v4, v5)?;
    let instr = f(b.ins()?, is_even, v6)?;
    if let Some((&v7, rest)) = b.instr_values(instr)?.split_first() {
        assert!(rest.is_empty(), "is_odd only has a single output value");
        b.ins()?.return_values([v7].iter().copied())?;
    }
    b.seal_block()?;
    let is_odd_body = b.finalize()?;

    body_builder.push_body(is_even, is_even_body).unwrap();
    body_builder.push_body(is_odd, is_odd_body).unwrap();
    let module = builder.finalize().unwrap();

    println!("{}", module.get_function(is_even).unwrap());
    println!("{}", module.get_function(is_odd).unwrap());

    Ok((module, is_even, is_odd))
}

#[test]
fn ping_pong_calls() -> Result<(), module::Error> {
    let (module, is_even, is_odd) =
        construct_is_even_and_is_odd(|ins, func, v6| ins.call(func, vec![v6]))?;

    for x in 0..10 {
        let input = IntConst::I32(x).into();

        let is_even_result = evaluate_func(&module, is_even, &[input]);
        let is_even_result = bits_into_const(&module, is_even, is_even_result);
        assert_eq!(is_even_result, vec![Const::Bool(x % 2 == 0)]);

        let is_odd_result = evaluate_func(&module, is_odd, &[input]);
        let is_odd_result = bits_into_const(&module, is_odd, is_odd_result);
        assert_eq!(is_odd_result, vec![Const::Bool(x % 2 == 1)]);
    }
    Ok(())
}

#[test]
fn ping_pong_tail_calls() -> Result<(), module::Error> {
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
