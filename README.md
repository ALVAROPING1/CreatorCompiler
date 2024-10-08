# Creator Compiler

Reimplementation of the compiler used by [Creator](https://creatorsim.github.io/)
to have better performance, more helpful error messages, and a more correct output.

## Running locally

The compiler currently supports 4 modes of execution:

- Print architecture specification schema: `cargo run --release -- 0 > schema.json`
- Validate architecture specification: `cargo run --release -- 1 architecture.json`
- Parse assembly input: `cargo run --release -- 2 architecture.json assembly.s`
- Compile assembly input: `cargo run --release -- 3 architecture.json assembly.s`

The `--release` flag can be omitted to generate debug binaries

## Running tests

Unit tests can be run with `cargo test`
