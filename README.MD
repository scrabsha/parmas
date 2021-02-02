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
| STR (immediate) | ❌ | ❌ |
| LDR (immediate) | ❌ | ❌ |
| ADD (SP plus immediate) | ❌ | ❌ |
| SUB (SP minus immediate) | ❌ | ❌ |
| B (conditional branche) | ❌ | ❌ |

Clipboard helper: `✔️❌`

[rustup]: https://rustup.rs
