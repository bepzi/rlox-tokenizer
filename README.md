# rlox-tokenizer

Converts Lox source code into syntax tokens.

Lox is a toy scripting language featured in Bob Nystrom's book
[Crafting Interpreters](https://craftinginterpreters.com/). This crate
provides methods for the initial transformation of Lox source code
into abstract syntax tokens.

This implementation differs from the C reference implementation, most notably:

- Full support for UTF-8 source code
- Support for nested multiline comments
- Doesn't require a magic `EOF` syntax token
- Rust-style error handling with `Result`

## Usage

Inside `Cargo.toml`:

``` toml
# ...
[dependencies]
rlox-tokenizer = { git = "https://github.com/ben01189998819991197253/rlox-tokenizer.git" }
```

## Documentation

```bash
cargo test && cargo doc --no-deps --open
```

## Contributing

Feel free to submit a pull request or file an issue! Please run your
code through `rustfmt` first, though.

