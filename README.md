# The `runwell` WebAssembly JIT Compiler

A non-bombable, optimizing WebAssembly (Wasm) JIT compiler with deterministic behaviour.

> **WIP** - The `runwell` JIT is under active development. Don't expect it to be working and expect dragons instead.

## Credits

Credits go to the people behind the [Bytecode Alliance](https://bytecodealliance.org/) for their fantastic
work on the WebAssembly specification and work on WebAssembly frameworks, libraries and tooling.
This project took a lot of inspiration from projects found under their
[GitHub Organization](https://github.com/bytecodealliance).

## WebAssembly

WebAssembly (abbreviated Wasm) is a binary instruction format for a stack-based virtual machine. Wasm is designed as a portable target for compilation of high-level languages like C/C++/Rust, enabling deployment on the web for client and server applications.

Read more [here](https://webassembly.org/).

## JIT Compiler

Just-in-time (abbreviated JIT) compilers compile the bytecode on the fly to efficient machine code while running the program. Wasm is especially suited for this kind of execution. Just-in-time compilation is generally orders of magnitudes faster than interpretation of the same bytecode.

## JIT-bomb Protection & Deterministic Behaviour

> **Definition:** A JIT bomb is a program that, upon execution via a JIT compiler, has a significantly increased compile-time in proportion to its original bytecode size. Since compile-time is part of the execution-time under a JIT compiler this has severe effects of the execution itself.

For many applications it is of high importance to have a deterministic execution and that the execution cannot be attacked by malicious codes in order to freeze the compilation or execution of the Wasm program. The `runwell` JIT guarantees deterministic and non-bombable execution of Wasm programs.*

> **Note:** If sources of JIT-boms or non-deterministic behaviours are caught in the `runwell` JIT they are treated as high-priority bugs.

## Optimizing

Even though the `runwell` JIT guarantees deterministic behaviour and protection against JIT bombs it still tries its best to optimize its input bytecode as much as possible.

High-level optimizations that might be bombable are performed by the `runwell` JIT securely to protect them from JIT bombs.

## Example

The following example shows how to construct a Runwell IR function equivalent to the below
python script and evaluate it using the Runwell IR interpreter.
```python
x = 0
while x < 100:
    x = x + 1
```
Below is the Rust code necessary to construct the equivalent Runwell IR function:
```rust
use runwell::ir::*;
use runwell::ir::interpreter::*;

let mut b = Function::build()
    .with_inputs(&[IntType::I32.into()])?
    .with_outputs(&[IntType::I32.into()])?
    .declare_variables(1, IntType::I32.into())?
    .body();

let loop_head = b.create_block();
let loop_body = b.create_block();
let loop_exit = b.create_block();

let input = Variable::from_raw(RawIdx::from_u32(0));
let counter = Variable::from_raw(RawIdx::from_u32(1));

let v0 = b.ins()?.constant(IntConst::I32(0))?;
b.write_var(counter, v0)?;
b.ins()?.br(loop_head)?;

b.switch_to_block(loop_head)?;
let v1 = b.read_var(counter)?;
let v2 = b.read_var(input)?;
let v3 = b.ins()?.icmp(IntType::I32, CompareIntOp::Slt, v1, v2)?;
b.ins()?.if_then_else(v3, loop_body, loop_exit)?;

b.switch_to_block(loop_body)?;
let v4 = b.read_var(counter)?;
let v5 = b.ins()?.constant(IntConst::I32(1))?;
let v6 = b.ins()?.iadd(IntType::I32, v4, v5)?;
b.write_var(counter, v6)?;
b.ins()?.br(loop_head)?;
b.seal_block()?;

b.switch_to_block(loop_head)?;
b.seal_block()?;

b.switch_to_block(loop_exit)?;
let v7 = b.read_var(counter)?;
b.ins()?.return_value(v7)?;
b.seal_block()?;

let function = b.finalize()?;
```
Printing the Runwell IR function using `println!("{}", function)` yields the following output:
```llvm
fn (v0: i32) -> i32
bb0:
    v1: i32 = const 0
    br bb1
bb1:
    v2: i32 = ϕ [ bb0 -> v1, bb2 -> v7 ]
    v4: bool = scmp i32 slt v2 v0
    if v4 then bb2 else bb3
bb2:
    v6: i32 = const 1
    v7: i32 = iadd i32 v2 v6
    br bb1
bb3:
    ret v2
```
Evaluating `function` using Runwell's built-in interpreter is done as follows:
```rust
let mut store = Store::default();
let func = store.push_function(function);
let mut ctx = EvaluationContext::new(&store);
let mut results = Vec::new();
let iterations = 100;
ctx.evaluate_function(
    func,
    [iterations].iter().copied(),
    |_, result| results.push(result),
)
.unwrap();
assert_eq!(result[0], iterations);
```
