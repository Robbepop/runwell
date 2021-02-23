# The `runwell` WebAssembly Virtual Machine

|   Continuous Integration  |       LoC        |
|:-------------------------:|:----------------:|
| [![GHActions][A1]][A2]    | [![loc][B1]][B2] |

[A1]: https://github.com/Robbepop/runwell/workflows/Rust%20-%20Continuous%20Integration/badge.svg?branch=master&event=push
[A2]: https://github.com/Robbepop/runwell/actions?query=workflow%3A%22Rust+-+Continuous+Integration%22+branch%3Amaster+event%3Apush
[B1]: https://tokei.rs/b1/github/Robbepop/runwell?category=code
[B2]: https://github.com/Aaronepower/tokei#badges

An attempt for a non-bombable, optimizing WebAssembly (Wasm) JIT compiler with deterministic behaviour.

> **WIP** - The `runwell` virtual machine is under active development. Don't expect it to be working. Here be dragons.

## Credits

Credits go to the people behind the [Bytecode Alliance](https://bytecodealliance.org/) for their fantastic
work on the WebAssembly specification and work on WebAssembly frameworks, libraries and tooling.
This project took a lot of inspiration from projects found under their
[GitHub Organization](https://github.com/bytecodealliance).

## Architecture

The `runwell` virtual machine consists of several sub-crates:

- `runwell_entity`: Data structures to follow data oriented design architecture using entity component structures.
- `runwell_ir`: Defines the Runwell **I**ntermediate **R**epresentation (IR) on the instruction level.
- `runwell_module`: Defines the module and function structure of the Runwell IR.
- `runwell_interpreter`: Implements a simple Runwell IR interpreter.
- `runwell_wasm`: Implements routines to convert from WebAssembly (Wasm) to Runwell IR.

The crates are ordered in the way they depend on each other.
Crates below might depend on a subset of the crates above them.

## Why WebAssembly?

WebAssembly (abbreviated Wasm) is a binary instruction format for a stack-based virtual machine. Wasm is designed as a portable target for compilation of high-level languages like C/C++/Rust, enabling deployment on the web for client and server applications.

Read more [here](https://webassembly.org/).

## Why JIT Compiler?

Just-in-time (abbreviated JIT) compilers compile the bytecode on the fly to efficient machine code while running the program. Wasm is especially suited for this kind of execution. Just-in-time compilation is expected to be orders of magnitudes more efficient than interpretation of the same bytecode.

## JIT-bomb Protection

A JIT bomb is a program that, upon execution via a JIT compiler, has a significantly increased compile-time in proportion to its original bytecode size. Since compile-time is part of the execution-time under a JIT compiler this has severe effects of the execution itself.
