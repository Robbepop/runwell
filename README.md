# The `runwell` WebAssembly Virtual Machine

|   Continuous Integration  |    Coverage      |       LoC        |
|:-------------------------:|:----------------:|:----------------:|
| [![GHActions][A1]][A2]    | [![loc][B1]][B2] | [![][C1]][C2]    |

[A1]: https://github.com/Robbepop/runwell/workflows/Rust%20-%20Continuous%20Integration/badge.svg?branch=master&event=push
[A2]: https://github.com/Robbepop/runwell/actions?query=workflow%3A%22Rust+-+Continuous+Integration%22+branch%3Amaster+event%3Apush
[B1]:  https://codecov.io/gh/Robbepop/runwell/branch/master/graph/badge.svg
[B2]:  https://codecov.io/gh/Robbepop/runwell/branch/master
[C1]: https://tokei.rs/b1/github/Robbepop/runwell?category=code
[C2]: https://github.com/Aaronepower/tokei#badges

An attempt for a non-bombable, optimizing WebAssembly (Wasm) JIT compiler with deterministic behaviour.

> **WIP** - The `runwell` virtual machine is under active development. Don't expect it to be working. Here be dragons.

## Crates & Documentation

| Crate | Docs | Description |
|:--|:--|:--|
| `runwell_entity` | [![][doc-badge]][entity-docs] | Data structures to follow data oriented design architecture using entity component structures. |
| `runwell_ir` | [![][doc-badge]][ir-docs] | Defines the Runwell **I**ntermediate **R**epresentation (IR) on the instruction level. |
| `runwell_module` | [![][doc-badge]][module-docs] | Defines the module and function structure of the Runwell IR. |
| `runwell_interpreter` | [![][doc-badge]][interpreter-docs] | Implements a simple Runwell IR interpreter. |
| `runwell_wasm` | [![][doc-badge]][wasm-docs] | Implements routines to convert from WebAssembly (Wasm) to Runwell IR. |

[doc-badge]: https://img.shields.io/badge/click-blue.svg
[entity-docs]: https://robbepop.github.io/runwell/runwell_entity/index.html
[wasm-docs]: https://robbepop.github.io/runwell/runwell_wasm/index.html
[ir-docs]: https://robbepop.github.io/runwell/runwell_ir/index.html
[module-docs]: https://robbepop.github.io/runwell/runwell_module/index.html
[interpreter-docs]: https://robbepop.github.io/runwell/runwell_interpreter/index.html

The crates are ordered in the way they depend on each other.
Crates below might depend on a subset of the crates above them.

## Why WebAssembly?

WebAssembly (abbreviated Wasm) is a binary instruction format for a stack-based virtual machine. Wasm is designed as a portable target for compilation of high-level languages like C/C++/Rust, enabling deployment on the web for client and server applications.

Read more [here](https://webassembly.org/).

### Planned & Implemented Wasm Proposals

> [x] Means that the feature is either fully implemented or that some implemented foundation already exists.

- [ ] [Import/Export of Mutable Globals][import_export_of_mutable_globals]
- [x] [Non-trapping float-to-int conversions][non-trapping_float-to-int_conversions]
- [x] [Sign-extension operators][sign-extension_operators]
- [x] [Multi-value][multi-value]
- [x] [Tail call][tail_call]
- [ ] [Multiple memories][multi-memory]

[import_export_of_mutable_globals]: https://github.com/WebAssembly/mutable-global
[non-trapping_float-to-int_conversions]: https://github.com/WebAssembly/nontrapping-float-to-int-conversions
[sign-extension_operators]: https://github.com/WebAssembly/sign-extension-ops
[multi-value]: https://github.com/WebAssembly/multi-value
[tail_call]: https://github.com/WebAssembly/tail-call
[multi-memory]: https://github.com/WebAssembly/multi-memory

## Credits

Credits go to the people behind the [Bytecode Alliance](https://bytecodealliance.org/) for their fantastic
work on the WebAssembly specification and work on WebAssembly frameworks, libraries and tooling.
This project took a lot of inspiration from projects found under their
[GitHub Organization](https://github.com/bytecodealliance).
