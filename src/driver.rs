//! Glues toghether the parsing system and the instruction encoding system.
//!
//! This module contains the `Assembler` struct, which takes two generics
//! objects. One represents the input data stream, the other represents the
//! output data stream.

use crate::{encoder::EncodedInstruction, parser, Result};
use std::io::{self, Read, Result as IResult, Write};

/// The output file header.
static OUTPUT_HEADER: &str = "v2.0 raw\n";

/// Allows to launch parm with specific streams.
///
/// The generic types here allow us to ease integration testing.
pub(crate) struct Assembler<I, O> {
    /// Where data should be gathered.
    input: I,
    /// Where output should be written.
    output: O,
}

impl Assembler<(), ()> {
    /// Runs the assembler, with the provided input and outputs.
    ///
    /// This function should be called in the main function.
    /// It determines, with an optional input and output file, where to
    /// read and write data, and runs itself.
    pub(crate) fn run<I: Read, O: Write>(i: Option<I>, o: Option<O>) -> Result<()> {
        match (i, o) {
            (None, None) => Assembler::builder()
                .with_input(io::stdin())
                .with_output(io::stdout())
                .assemble(),

            (Some(i), Some(o)) => Assembler::builder().with_input(i).with_output(o).assemble(),

            (Some(i), None) => Assembler::builder()
                .with_input(i)
                .with_output(io::stdout())
                .assemble(),

            (None, Some(o)) => Assembler::builder()
                .with_input(io::stdin())
                .with_output(o)
                .assemble(),
        }
    }


    /// Creates an object which allows to build the assembler.
    pub(crate) fn builder() -> Assembler<(), ()> {
        Assembler {
            input: (),
            output: (),
        }
    }
}

impl<O> Assembler<(), O> {
    /// Adds an input stream to the assembler.
    pub(crate) fn with_input<I: Read>(self, input: I) -> Assembler<I, O> {
        let output = self.output;
        Assembler { input, output }
    }
}

impl<I> Assembler<I, ()> {
    /// Adds an output stream to the assembler.
    pub(crate) fn with_output<O: Write>(self, output: O) -> Assembler<I, O> {
        let input = self.input;
        Assembler { input, output }
    }
}

impl<I: Read, O: Write> Assembler<I, O> {
    /// Reads the whole input stream, converts it to binary instructions and
    /// writes it to the output stream.
    pub(crate) fn assemble(mut self) -> Result<()> {
        let input_data = self
            .read_input()
            .map_err(|_| "Failed to read input data: I/O error")?;

        let mut tail = input_data.as_str();

        let mut final_instructions = Vec::new();

        while !tail.is_empty() {
            let (op, rest) = parser::parse_op(tail)?;
            final_instructions.push(op.encode());
            tail = rest;
        }

        self.write_header()
            .map_err(|_| "Failed to write output data: I/O error")?;

        self.write_instructions(final_instructions.as_slice())
            .map_err(|_| "Failed to write output data: I/O error")?;

        Ok(())
    }

    /// Reads the whole input stream and returns it as a String.
    fn read_input(&mut self) -> IResult<String> {
        let mut buff = String::new();
        self.input.read_to_string(&mut buff).map(|_| buff)
    }

    /// Writes the output file header in the output stream.
    fn write_header(&mut self) -> IResult<usize> {
        self.output.write(OUTPUT_HEADER.as_bytes())
    }

    /// Writes instructions to the output stream.
    fn write_instructions(&mut self, instrs: &[EncodedInstruction]) -> IResult<()> {
        instrs
            .iter()
            .try_for_each(|i| self.output.write_fmt(format_args!("{} ", i)))
    }
}
