# Parmas

PARM-Assembler.

## Disclaimer

This project was created for the Computer Architecture class at Polytech Nice
Sophia. The goal was to create an assembler for a subset of the ARM-Cortex-M0
microprocessor (see [the project documentation][miaous-repo]).

I will not maintain this repository anymore. Feel free to study and borrow
anything you find interesting.

## Compiling and installing parmas

First, install the `rustup` tool for your operating system (see
[rustup.rs][rustup] for detailled instructions). Then, you need to install the
`stable` rust toolchain:

```bash
rustup install stable
```

Then, clone the repository and `cd` to it:

```bash
git clone https://github.com/scrabsha/parmas
cargo build --release
```

The executable is located in the `target` subdirectory. On Linux, it can be
installed with (requires root) :

```
install target/release/parmas /usr/bin/parmas
```

## Running parmas

To run `parmas` on an assembly file, issue:

```
parmas path/to/file.s
```

The output file will be created in the same directory, with the `raw` file
extension. If no input file is provided, then the standard input will be
processed, and the result will be printed to the standard output.

## Testing

This project use the rust built-in testing framework. To run the test suite,
issue:

```
cargo test
```

## Instrunction table

| Instruction | Parsing | Encoding |
| ----------- | ------- | -------- |
| LSL (immediate) | ✔️ | ✔️ |
| LSR (immediate) | ✔️ | ✔️ |
| ASR (immediate) | ✔️ | ✔️ |
| ADD (register) | ✔️ | ✔️ |
| SUB (register) | ✔️ | ✔️ |
| ADD (immediate) | ✔️ | ✔️ |
| SUB (immediate) | ✔️ | ✔️ |
| MOV (immediate) | ✔️ | ✔️ |
| AND (register) | ✔️ | ✔️ |
| EOR (register) | ✔️ | ✔️ |
| LSL (register) | ✔️ | ✔️ |
| LSR (register) | ✔️ | ✔️ |
| ASR (register) | ✔️ | ✔️ |
| ADC (register) | ✔️ | ✔️ |
| SBC (register) | ✔️ | ✔️ |
| ROR (register) | ✔️ | ✔️ |
| TST (register) | ✔️ | ✔️ |
| RSB (immediate) | ✔️ | ✔️ |
| CMP (register) | ✔️ | ✔️ |
| CMN (register) | ✔️ | ✔️ |
| ORR (register) | ✔️ | ✔️ |
| MUL | ✔️ | ✔️ |
| BIC (register) | ✔️ | ✔️ |
| MVN (register) | ✔️ | ✔️ |
| STR (immediate) | ✔️ | ✔️ |
| LDR (immediate) | ✔️ | ✔️ |
| ADD (SP plus immediate) | ✔️ | ✔️ |
| SUB (SP minus immediate) | ✔️ | ✔️ |
| B (conditional branche) | ✔️ | ✔️ |

[miaous-repo]: https://github.com/MIAOU-Polytech/SI3_PEP_Project
[rustup]: https://rustup.rs
