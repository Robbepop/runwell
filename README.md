# The `runwell` WebAssembly Virtual Machine

An attempt for a non-bombable, optimizing WebAssembly (Wasm) JIT compiler with deterministic behaviour.

> **WIP** - The `runwell` virtual machine is under active development. Don't expect it to be working. Here be dragons.

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
