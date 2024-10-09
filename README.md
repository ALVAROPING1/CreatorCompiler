# Creator Compiler

Reimplementation of the compiler used by [Creator](https://creatorsim.github.io/)
to have better performance, more helpful error messages, and a more correct output.

## Running locally (CLI)

The compiler currently supports 4 modes of execution:

- Print architecture specification schema: `cargo run --release -- 0 > schema.json`
- Validate architecture specification: `cargo run --release -- 1 architecture.json`
- Parse assembly input: `cargo run --release -- 2 architecture.json assembly.s`
- Compile assembly input: `cargo run --release -- 3 architecture.json assembly.s`

The `--release` flag can be omitted to generate debug binaries

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
