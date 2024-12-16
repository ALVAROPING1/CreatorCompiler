# Creator Compiler

Reimplementation of the compiler used by [Creator](https://creatorsim.github.io/)
to have better performance, more helpful error messages, and a more correct output.

## Running locally (CLI)

The compiler can be built from source using `cargo build --release`, which will
place the binary in `./target/release/creator-compiler`. The `--release` flag can
be omitted to generate debug binaries. Additionally, `cargo run --release -- [<ARGS>]`
can be used as a shortcut to build and run the binary. Running the application
without arguments provides a short description of the application and subcommands,
and using `creator-compiler help <command>` provides a description and usage
instructions for each command.

The compiler currently supports 3 modes of execution:

- Print architecture specification schema to `stdout`: `creator-compiler schema`
- Validate architecture specification file: `creator-compiler validate <architecture.json>`
- Compile assembly input and print the result to `stdout`:
  `creator-compiler compile <architecture.json> <assembly.s>`
  - The `-v`/`--verbose` flag can be used to also print the parsed AST

## Running in a browser

Running in a browser is supported through `wasm`. In order to do so, the code must
first be compiled into `wasm` package with `wasm-pack build --target web`. The flag
`--dev` can be added to generate a debug module with a shorter compile time by
omitting optimizations

After the package has been built, it can be loaded into a web page by requiring the
generated `.js` file as a module. The `js_example/` directory contains a working
example of how to use the generated package. The `index.html` file can't be directly
opened in a browser due to [CORS](https://developer.mozilla.org/en-US/docs/Web/HTTP/CORS)
limitations. Python can be used to start a development server with
`python3 -m http.server 8080` which allows to load the page at `localhost:8080/js_example`

## Running tests

Unit tests can be run with `cargo test`
