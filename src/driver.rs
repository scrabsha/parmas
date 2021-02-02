//! Glues toghether the parsing system and the instruction encoding system.
//!
//! This module contains the `Assembler` struct, which takes two generics
//! objects. One represents the input data stream, the other represents the
//! output data stream.

use crate::{encoder::EncodedInstruction, labels::LabelTable, parser, Result};
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

impl<'a> Assembler<(), ()> {
    /// Runs the assembler, with the provided input and outputs.
    ///
    /// This function should be called in the main function.
    /// It determines, with an optional input and output file, where to
    /// read and write data, and runs itself.
    pub(crate) fn run<I: Read, O: Write>(i: Option<&'a mut I>, o: Option<&'a mut O>) -> Result<()> {
        match (i, o) {
            (None, None) => {
                let mut data_in = io::stdin();
                let mut data_out = io::stdout();
                Assembler::builder()
                    .with_input(&mut data_in)
                    .with_output(&mut data_out)
                    .assemble()
            }

            (Some(i), Some(o)) => Assembler::builder().with_input(i).with_output(o).assemble(),

            (Some(i), None) => {
                let mut data_out = io::stdout();
                Assembler::builder()
                    .with_input(i)
                    .with_output(&mut data_out)
                    .assemble()
            }

            (None, Some(o)) => {
                let mut data_in = io::stdin();
                Assembler::builder()
                    .with_input(&mut data_in)
                    .with_output(o)
                    .assemble()
            }
        }
    }

    /// Creates an object which allows to build the assembler.
    pub(crate) fn builder() -> Assembler<(), ()> {
        Assembler {
            input: (),
            output: (),
        }
    }

    #[cfg(any(test, doc))]
    /// Runs an assembler on a test-situation, with a custom input string.
    pub(crate) fn run_test(input: &str) -> Result<String> {
        let mut output = Vec::new();
        Assembler::builder()
            .with_input(&mut input.as_bytes())
            .with_output(&mut output)
            .assemble()?;

        let output = String::from_utf8(output).expect("Non UTF-8 assembly generated");

        Ok(output)
    }
}

impl<O> Assembler<(), O> {
    /// Adds an input stream to the assembler.
    pub(crate) fn with_input<'a, I: Read>(self, input: &'a mut I) -> Assembler<&'a mut I, O> {
        let output = self.output;
        Assembler { input, output }
    }
}

impl<I> Assembler<I, ()> {
    /// Adds an output stream to the assembler.
    pub(crate) fn with_output<'a, O: Write>(self, output: &'a mut O) -> Assembler<I, &'a mut O> {
        let input = self.input;
        Assembler { input, output }
    }
}

impl<'a, I: Read, O: Write> Assembler<&'a mut I, &'a mut O> {
    /// Reads the whole input stream, converts it to binary instructions and
    /// writes it to the output stream.
    pub(crate) fn assemble(mut self) -> Result<()> {
        let input_data = self
            .read_input()
            .map_err(|_| "Failed to read input data: I/O error")?;

        let mut tail = input_data.as_str();
        let mut labels = LabelTable::new();

        let mut instructions = Vec::new();

        while !tail.is_empty() {
            let ((ls, op), rest) = parser::parse_op_and_labels(tail)?;

            let ls = ls.into_iter().map(|l| (l, instructions.len()));
            labels.extend(ls)?;

            instructions.push(op);

            tail = rest;
        }

        let resolved_instructions = instructions
            .into_iter()
            .enumerate()
            .map(|(pos, op)| op.resolve_labels(pos, &labels).map(|op| op.encode()))
            .collect::<Result<Vec<_>>>()?;

        self.write_header()
            .map_err(|_| "Failed to write output data: I/O error")?;

        self.write_instructions(resolved_instructions.as_slice())
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn encode_example_code() {
        // In this test, we ensure that the example provided in the class
        // documentation assembles exactly as expected.

        let input = "
        sub sp, #12 // Agrandir  la  pile de 3*4 octets d’où le  sp − 12
        movs r0, #0 //  Placer dans un  registre  la  valeur  contenue dans  la  variable a
        str r0 , [sp, #8] // Stocker cette valeur dans la pile
        movs r1, #1 // Placer dans un registre la valeur contenue dans la variable b
        str r1, [sp, #4] // Stocker cette valeur dans la pile
        ldr r1, [sp, #8] // Charger dans le registre 1 la  valeur contenue à la dernière adresse de la pile
        ldr r2, [sp, #4] // Charger dans le registre 2 la valeur contenue à l’avant dernière adresse de la pile
        adds r1, r1, r2 // Additionner les valeurs des registres 1 et 2, stocker le résultat dans le registre 1
        str r1, [sp] // Stocker le contenu du registre 1 à l’adresse pointée par le pointeur de pile
        add sp, #12 // Réduire la pile de 3*4 octets
        ";

        let output = Assembler::run_test(input);
        let expected_output = "v2.0 raw\nb08c 2000 9008 2101 9104 9908 9a04 1889 9100 b00c ";

        assert_eq!(output.unwrap(), expected_output);
    }

    #[test]
    fn encode_infinite_loop() {
        let input = "foo: beq foo";

        let output = Assembler::run_test(input).unwrap();
        let expected_output = "v2.0 raw\nd0fe ";

        assert_eq!(output, expected_output);
    }

    #[test]
    fn encode_shortest_branch() {
        let input = "
            beq foo
        foo:
            adds r1, r1, r1
        ";

        let output = Assembler::run_test(input).unwrap();
        let expected_output = "v2.0 raw\nd0ff 1849 ";

        assert_eq!(output, expected_output);
    }
}
