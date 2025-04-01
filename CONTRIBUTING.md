# Contributing to the project

## Documentation

Developer documentation (including private elements) can be generated and opened
from the doc comments using `cargo doc --open --document-private-items`

## Pre-requisites

Code is formatted with `rustfmt` and linted with `clippy`. These should come by
default with an installation of rust

To format the code, use `cargo fmt`. To run the linter, use:

```sh
cargo clippy -- -W clippy::pedantic -W clippy::nursery -W clippy::unwrap_used --no-deps
```

## Pull Request

Commits messages and PR titles must follow [Conventional Commits Specification](https://www.conventionalcommits.org/).
The scope should be the path to the file with the main modification done, e.g.
`compiler` or `parser/expression`. The description should start with a lowercase
letter

## Running tests

Unit tests can be run with `cargo test`
