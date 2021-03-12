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
    builder::{FunctionBuilder, InstructionBuilder},
    primitive::{FunctionType, Instr, Variable},
    FunctionBody,
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

    println!("{}", module);

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

fn evaluate_func_in_ctx(
    ctx: &mut EvaluationContext,
    func: Func,
    inputs: &[Const],
) -> Vec<u64> {
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
                Type::Ptr => {
                    assert!(bits & ((0x1 << 16) - 1) == 0);
                    Const::Ptr(bits as u32)
                }
                Type::Int(IntType::I1) => IntConst::I1(bits != 0).into(),
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
fn ret_const_works() {
    let (func, module) = module_with_func(&[], &[IntType::I32.into()], |b| {
        b.body()?;
        let c = b.ins()?.constant(IntConst::I32(42))?;
        b.ins()?.return_values([c].iter().copied())?;
        Ok(())
    });
    let result = evaluate_func(&module, func, &[]);
    assert_eq!(result, vec![42]);
}

#[test]
fn simple_block_works() {
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
}

#[test]
fn if_then_else_works() {
    let (func, module) = module_with_func(&[], &[IntType::I32.into()], |b| {
        b.body()?;
        let then_block = b.create_block()?;
        let else_block = b.create_block()?;
        let v1 = b.ins()?.constant(IntConst::I32(1))?;
        let v2 = b.ins()?.constant(IntConst::I32(2))?;
        let v3 = b.ins()?.icmp(IntType::I32, CompareIntOp::Ule, v1, v2)?;
        let _v4 = b.ins()?.if_then_else(
            v3,
            then_block,
            else_block,
            vec![],
            vec![],
        )?;
        b.switch_to_block(then_block)?;
        let v5 = b.ins()?.constant(IntConst::I32(10))?;
        b.ins()?.return_values([v5].iter().copied())?;
        b.seal_block(then_block)?;
        b.switch_to_block(else_block)?;
        let v6 = b.ins()?.constant(IntConst::I32(20))?;
        b.ins()?.return_values([v6].iter().copied())?;
        b.seal_block(else_block)?;
        Ok(())
    });
    let result = evaluate_func(&module, func, &[]);
    assert_eq!(result, vec![10]);
}

#[test]
fn simple_variable() {
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
}

#[test]
fn double_input() {
    let (func, module) =
        module_with_func(&[IntType::I32.into()], &[IntType::I32.into()], |b| {
            b.body()?;
            let input = Variable::from_raw(RawIdx::from_u32(0));
            let v0 = b.read_var(input)?;
            let v1 = b.ins()?.iadd(IntType::I32, v0, v0)?;
            b.ins()?.return_values([v1].iter().copied())?;
            Ok(())
        });
    let mut ctx = EvaluationContext::new(&module);
    for x in -10..10 {
        let result =
            evaluate_func_in_ctx(&mut ctx, func, &[IntConst::I32(x).into()]);
        let result = bits_into_const(&module, func, result);
        assert_eq!(result, vec![IntConst::I32(x * 2).into()]);
    }
}

#[test]
fn global_identity_using_local() {
    let (func, module) =
        module_with_func(&[IntType::I32.into()], &[IntType::I32.into()], |b| {
            b.declare_variables(1, IntType::I32.into())?;
            b.body()?;

            let input = Variable::from_raw(RawIdx::from_u32(0));
            let local = Variable::from_raw(RawIdx::from_u32(1));
            let v0 = b.read_var(input)?;
            b.write_var(local, v0)?;
            let exit_block = b.create_block()?;
            b.ins()?.br(exit_block, vec![])?;
            b.switch_to_block(exit_block)?;
            let v0 = b.read_var(local)?;
            b.ins()?.return_values([v0].iter().copied())?;
            b.seal_block(exit_block)?;

            Ok(())
        });
    let mut ctx = EvaluationContext::new(&module);
    for x in -10..10 {
        let value = IntConst::I32(x).into();
        let result = evaluate_func_in_ctx(&mut ctx, func, &[value]);
        let result = bits_into_const(&module, func, result);
        assert_eq!(result, vec![value]);
    }
}

#[test]
fn inconveniently_written_min() {
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
            b.ins()?.if_then_else(
                v2,
                then_block,
                else_block,
                vec![],
                vec![],
            )?;

            b.switch_to_block(then_block)?;
            b.seal_block(then_block)?;
            let v3 = b.read_var(lhs)?;
            b.write_var(result, v3)?;
            b.ins()?.br(exit_block, vec![])?;

            b.switch_to_block(else_block)?;
            b.seal_block(else_block)?;
            let v4 = b.read_var(rhs)?;
            b.write_var(result, v4)?;
            b.ins()?.br(exit_block, vec![])?;

            b.switch_to_block(exit_block)?;
            let v5 = b.read_var(result)?;
            b.ins()?.return_values([v5].iter().copied())?;
            b.seal_block(exit_block)?;

            Ok(())
        },
    );
    let mut ctx = EvaluationContext::new(&module);
    for x in -10..10 {
        for y in -5..15 {
            let x = IntConst::I32(x).into();
            let y = IntConst::I32(y).into();
            let result = evaluate_func_in_ctx(&mut ctx, func, &[x, y]);
            let result = bits_into_const(&module, func, result);
            assert_eq!(result, vec![if x < y { x } else { y }]);
        }
    }
}

#[test]
fn inconveniently_written_min_2() {
    let (func, module) = module_with_func(
        &[IntType::I32.into(); 2][..],
        &[IntType::I32.into()],
        |b| {
            b.body()?;

            let exit_block = b.create_block()?;
            let param =
                b.create_block_parameter(exit_block, IntType::I32.into())?;

            let lhs = Variable::from_raw(RawIdx::from_u32(0));
            let rhs = Variable::from_raw(RawIdx::from_u32(1));

            let v0 = b.read_var(lhs)?;
            let v1 = b.read_var(rhs)?;
            let v2 = b.ins()?.icmp(IntType::I32, CompareIntOp::Slt, v0, v1)?;
            b.ins()?.if_then_else(
                v2,
                exit_block,
                exit_block,
                vec![v0],
                vec![v1],
            )?;

            b.switch_to_block(exit_block)?;
            b.ins()?.return_values([param].iter().copied())?;
            b.seal_block(exit_block)?;

            Ok(())
        },
    );
    let mut ctx = EvaluationContext::new(&module);
    for x in -10..10 {
        for y in -5..15 {
            let x = IntConst::I32(x).into();
            let y = IntConst::I32(y).into();
            let result = evaluate_func_in_ctx(&mut ctx, func, &[x, y]);
            let result = bits_into_const(&module, func, result);
            assert_eq!(result, vec![if x < y { x } else { y }]);
        }
    }
}

#[test]
fn swap_2() {
    let (func, module) = module_with_func(
        &[IntType::I32.into(); 2][..],
        &[IntType::I32.into(); 2][..],
        |b| {
            b.body()?;

            let lhs = Variable::from_raw(RawIdx::from_u32(0));
            let rhs = Variable::from_raw(RawIdx::from_u32(1));

            let v0 = b.read_var(lhs)?;
            let v1 = b.read_var(rhs)?;
            let v2 = b.ins()?.icmp(IntType::I32, CompareIntOp::Slt, v0, v1)?;
            let mut builder = b.ins()?.match_select_multi(
                IntType::I1,
                v2,
                [IntType::I32.into(), IntType::I32.into()].iter().copied(),
            )?;
            builder.push_results([v1, v0].iter().copied())?;
            let instr = builder.finish([v0, v1].iter().copied())?;
            let returned_values =
                b.instr_values(instr)?.iter().copied().collect::<Vec<_>>();
            b.ins()?.return_values(returned_values)?;

            Ok(())
        },
    );
    let mut ctx = EvaluationContext::new(&module);
    for x in -10..10 {
        for y in -5..15 {
            let x = IntConst::I32(x).into();
            let y = IntConst::I32(y).into();
            let result = evaluate_func_in_ctx(&mut ctx, func, &[x, y]);
            let result = bits_into_const(&module, func, result);
            use core::cmp::{max, min};
            assert_eq!(result, vec![min(x, y), max(x, y)]);
        }
    }
}

#[test]
fn conveniently_written_min() {
    let (func, module) = module_with_func(
        &[IntType::I32.into(); 2][..],
        &[IntType::I32.into()],
        |b| {
            b.body()?;

            let lhs = Variable::from_raw(RawIdx::from_u32(0));
            let rhs = Variable::from_raw(RawIdx::from_u32(1));

            let v0 = b.read_var(lhs)?;
            let v1 = b.read_var(rhs)?;
            let v2 = b.ins()?.icmp(IntType::I32, CompareIntOp::Slt, v0, v1)?;
            let v3 = b.ins()?.bool_select(IntType::I32.into(), v2, v0, v1)?;
            b.ins()?.return_values([v3].iter().copied())?;

            Ok(())
        },
    );
    let mut ctx = EvaluationContext::new(&module);
    for x in -10..10 {
        for y in -5..15 {
            let x = IntConst::I32(x).into();
            let y = IntConst::I32(y).into();
            let result = evaluate_func_in_ctx(&mut ctx, func, &[x, y]);
            let result = bits_into_const(&module, func, result);
            assert_eq!(result, vec![if x < y { x } else { y }]);
        }
    }
}

#[test]
fn binary_swap_works() {
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
    let mut ctx = EvaluationContext::new(&module);
    for x in -10..10 {
        for y in -10..10 {
            let x = IntConst::I32(x).into();
            let y = IntConst::I32(y).into();
            let result = evaluate_func_in_ctx(&mut ctx, func, &[x, y]);
            let result = bits_into_const(&module, func, result);
            assert_eq!(result, vec![y, x]);
        }
    }
}

#[test]
fn counting_loop_works() {
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
            b.ins()?.br(loop_head, vec![])?;

            b.switch_to_block(loop_head)?;
            let v2 = b.read_var(counter)?;
            let v3 = b.read_var(input)?;
            let v4 = b.ins()?.icmp(IntType::I32, CompareIntOp::Slt, v2, v3)?;
            b.ins()?
                .if_then_else(v4, loop_body, loop_exit, vec![], vec![])?;

            b.switch_to_block(loop_body)?;
            let v5 = b.read_var(counter)?;
            let v6 = b.read_var(one)?;
            let v7 = b.ins()?.iadd(IntType::I32, v5, v6)?;
            b.write_var(counter, v7)?;
            b.ins()?.br(loop_head, vec![])?;
            b.seal_block(loop_body)?;

            b.seal_block(loop_head)?;
            b.switch_to_block(loop_exit)?;
            b.seal_block(loop_exit)?;
            let v8 = b.read_var(counter)?;
            b.ins()?.return_values([v8].iter().copied())?;

            Ok(())
        });
    let mut ctx = EvaluationContext::new(&module);
    for count_until in 0..10 {
        let count_until = IntConst::I32(count_until).into();
        let result = evaluate_func_in_ctx(&mut ctx, func, &[count_until]);
        let result = bits_into_const(&module, func, result);
        assert_eq!(result, vec![count_until]);
    }
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
        b.push_output(IntType::I1);
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
    b.ins()?
        .if_then_else(v2, if_zero, if_not_zero, vec![], vec![])?;

    b.switch_to_block(if_zero)?;
    let v3 = b.ins()?.constant(IntConst::I1(true))?;
    b.ins()?.return_values([v3].iter().copied())?;
    b.seal_block(if_zero)?;

    b.switch_to_block(if_not_zero)?;
    let v4 = b.read_var(input)?;
    let v5 = b.ins()?.constant(IntConst::I32(1))?;
    let v6 = b.ins()?.isub(IntType::I32, v4, v5)?;
    let instr = f(b.ins()?, is_odd, v6)?;
    if let Some((&v7, rest)) = b.instr_values(instr)?.split_first() {
        assert!(rest.is_empty(), "is_odd only has a single output value");
        b.ins()?.return_values([v7].iter().copied())?;
    }
    b.seal_block(if_not_zero)?;
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
    b.ins()?
        .if_then_else(v2, if_zero, if_not_zero, vec![], vec![])?;

    b.switch_to_block(if_zero)?;
    let v3 = b.ins()?.constant(IntConst::I1(false))?;
    b.ins()?.return_values([v3].iter().copied())?;
    b.seal_block(if_zero)?;

    b.switch_to_block(if_not_zero)?;
    let v4 = b.read_var(input)?;
    let v5 = b.ins()?.constant(IntConst::I32(1))?;
    let v6 = b.ins()?.isub(IntType::I32, v4, v5)?;
    let instr = f(b.ins()?, is_even, v6)?;
    if let Some((&v7, rest)) = b.instr_values(instr)?.split_first() {
        assert!(rest.is_empty(), "is_odd only has a single output value");
        b.ins()?.return_values([v7].iter().copied())?;
    }
    b.seal_block(if_not_zero)?;
    let is_odd_body = b.finalize()?;

    body_builder.push_body(is_even, is_even_body).unwrap();
    body_builder.push_body(is_odd, is_odd_body).unwrap();
    let module = builder.finalize().unwrap();

    println!("{}", module);

    Ok((module, is_even, is_odd))
}

#[test]
fn ping_pong_calls() -> Result<(), module::Error> {
    let (module, is_even, is_odd) =
        construct_is_even_and_is_odd(|ins, func, v6| ins.call(func, vec![v6]))?;

    let mut ctx = EvaluationContext::new(&module);
    for x in 0..10 {
        let input = IntConst::I32(x).into();

        let is_even_result = evaluate_func_in_ctx(&mut ctx, is_even, &[input]);
        let is_even_result = bits_into_const(&module, is_even, is_even_result);
        assert_eq!(is_even_result, vec![IntConst::I1(x % 2 == 0).into()]);

        let is_odd_result = evaluate_func_in_ctx(&mut ctx, is_odd, &[input]);
        let is_odd_result = bits_into_const(&module, is_odd, is_odd_result);
        assert_eq!(is_odd_result, vec![IntConst::I1(x % 2 == 1).into()]);
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
    for x in 0..10 {
        let input = IntConst::I32(x).into();

        let is_even_result = evaluate_func_in_ctx(&mut ctx, is_even, &[input]);
        let is_even_result = bits_into_const(&module, is_even, is_even_result);
        assert_eq!(is_even_result, vec![IntConst::I1(x % 2 == 0).into()]);

        let is_odd_result = evaluate_func_in_ctx(&mut ctx, is_odd, &[input]);
        let is_odd_result = bits_into_const(&module, is_odd, is_odd_result);
        assert_eq!(is_odd_result, vec![IntConst::I1(x % 2 == 1).into()]);
    }

    Ok(())
}

#[test]
fn multi_value_div_rem_works() -> Result<(), module::Error> {
    // Setup module.
    let mut builder = Module::build();
    let mut type_builder = builder.type_section().unwrap();
    let div_rem_func_type = type_builder.push_type({
        let mut b = FunctionType::build();
        b.push_input(IntType::I32);
        b.push_input(IntType::I32);
        b.push_output(IntType::I32);
        b.push_output(IntType::I32);
        b.finalize()
    });
    let div_or_rem_func_type = type_builder.push_type({
        let mut b = FunctionType::build();
        b.push_input(IntType::I32);
        b.push_input(IntType::I32);
        b.push_output(IntType::I32);
        b.finalize()
    });

    // Pre declare functions used before they are defined.
    let mut function_builder = builder.function_section().unwrap();
    let div_rem = function_builder.push_function(div_rem_func_type).unwrap();
    let div = function_builder
        .push_function(div_or_rem_func_type)
        .unwrap();
    let rem = function_builder
        .push_function(div_or_rem_func_type)
        .unwrap();
    let (res, mut body_builder) = builder.code_section().unwrap();

    let dividend = Variable::from_raw(RawIdx::from_u32(0));
    let divisor = Variable::from_raw(RawIdx::from_u32(1));

    // Create Function: div_rem
    //
    // Encodes `div_rem` as follows:
    //
    // div_rem(x, y):
    //     return ((x / y), (x % y))

    let mut b = FunctionBody::build(div_rem, res);
    b.body()?;
    let v0 = b.read_var(dividend)?;
    let v1 = b.read_var(divisor)?;
    let v2 = b.ins()?.sdiv(IntType::I32, v0, v1)?;
    let v3 = b.ins()?.srem(IntType::I32, v0, v1)?;
    b.ins()?.return_values([v2, v3].iter().copied())?;
    let div_rem_body = b.finalize()?;

    // Create Function: div
    //
    // Encodes `div` as follows:
    //
    // div(x, y):
    //     v0, _ = div_rem(x, y)
    //     return v0

    let mut b = FunctionBody::build(div, res);
    b.body()?;
    let v0 = b.read_var(dividend)?;
    let v1 = b.read_var(divisor)?;
    let instr = b.ins()?.call(div_rem, [v0, v1].iter().copied())?;
    let v_div = b.instr_values(instr)?[0];
    b.ins()?.return_values([v_div].iter().copied())?;
    let div_body = b.finalize()?;

    // Create Function: rem
    //
    // Encodes `rem` as follows:
    //
    // rem(x, y):
    //     _, v0 = div_rem(x, y)
    //     return v0

    let mut b = FunctionBody::build(rem, res);
    b.body()?;
    let v0 = b.read_var(dividend)?;
    let v1 = b.read_var(divisor)?;
    let instr = b.ins()?.call(div_rem, [v0, v1].iter().copied())?;
    let v_rem = b.instr_values(instr)?[1];
    b.ins()?.return_values([v_rem].iter().copied())?;
    let rem_body = b.finalize()?;

    body_builder.push_body(div_rem, div_rem_body).unwrap();
    body_builder.push_body(div, div_body).unwrap();
    body_builder.push_body(rem, rem_body).unwrap();
    let module = builder.finalize().unwrap();

    println!("{}", module);

    let mut ctx = EvaluationContext::new(&module);
    for x in -10..10 {
        for y in -4..4 {
            if y == 0 {
                // Don't test division by zero here.
                continue
            }
            // Test `div_rem` function directly:
            let input_x = IntConst::I32(x).into();
            let input_y = IntConst::I32(y).into();
            let output_div = IntConst::I32(x / y).into();
            let output_rem = IntConst::I32(x % y).into();
            let div_rem_result =
                evaluate_func_in_ctx(&mut ctx, div_rem, &[input_x, input_y]);
            let div_rem_result =
                bits_into_const(&module, div_rem, div_rem_result);
            assert_eq!(div_rem_result, vec![output_div, output_rem]);

            let div_result =
                evaluate_func_in_ctx(&mut ctx, div, &[input_x, input_y]);
            let div_result = bits_into_const(&module, div, div_result);
            assert_eq!(div_result, vec![output_div]);

            let rem_result =
                evaluate_func_in_ctx(&mut ctx, rem, &[input_x, input_y]);
            let rem_result = bits_into_const(&module, rem, rem_result);
            assert_eq!(rem_result, vec![output_rem]);
        }
    }

    Ok(())
}
