# Parmas

PARM-Assembler.

## Compiling

First, install the `rustup` tool for your operating system (see
[rustup.rs][rustup] for detailled instructions). Then, you need to install the
`stable` rust toolchain:

```bash
$ rustup install stable
```

Then, clone the repository and `cd` to it:

```bash
$ git clone https://github.com/leopourcelot/parmas
$ cargo build --release
```

The executable is located in the `target` subdirectory.

## Testing

This project use the rust built-in testing framework. To run the test suite,
issue:

```bash
$ cargo test
```



[rustup]: https://rustup.rs