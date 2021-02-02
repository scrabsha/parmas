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
    pub(crate) fn with_input<I: Read>(self, input: &mut I) -> Assembler<&mut I, O> {
        let output = self.output;
        Assembler { input, output }
    }
}

impl<I> Assembler<I, ()> {
    /// Adds an output stream to the assembler.
    pub(crate) fn with_output<O: Write>(self, output: &mut O) -> Assembler<I, &mut O> {
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
        let expected_output = "v2.0 raw\nd0fd ";

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
        let expected_output = "v2.0 raw\nd0fe 1849 ";

        assert_eq!(output, expected_output);
    }

    #[test]
    fn multiple_branches() {
        let input = "
            b foo
            b foo
            b foo
            b foo
        foo:
            b foo
        ";

        let output = Assembler::run_test(input).unwrap();
        let expected_output = "v2.0 raw\nde01 de00 deff defe defd ";
        assert_eq!(output, expected_output);
    }

    #[test]
    fn calculator_example() {
        let input = "
            .text
            .syntax unified
            .eabi_attribute	67, \"2.09\"	@ Tag_conformance
            .cpu	cortex-m0
            .eabi_attribute	6, 12	@ Tag_CPU_arch
            .eabi_attribute	8, 0	@ Tag_ARM_ISA_use
            .eabi_attribute	9, 1	@ Tag_THUMB_ISA_use
            .eabi_attribute	17, 1	@ Tag_ABI_PCS_GOT_use
            .eabi_attribute	20, 1	@ Tag_ABI_FP_denormal
            .eabi_attribute	21, 1	@ Tag_ABI_FP_exceptions
            .eabi_attribute	23, 3	@ Tag_ABI_FP_number_model
            .eabi_attribute	34, 0	@ Tag_CPU_unaligned_access
            .eabi_attribute	24, 1	@ Tag_ABI_align_needed
            .eabi_attribute	25, 1	@ Tag_ABI_align_preserved
            .eabi_attribute	38, 1	@ Tag_ABI_FP_16bit_format
            .eabi_attribute	18, 4	@ Tag_ABI_PCS_wchar_t
            .eabi_attribute	26, 2	@ Tag_ABI_enum_size
            .eabi_attribute	14, 0	@ Tag_ABI_PCS_R9_use
            .file	\"demo.c\"
            .globl	main
            .p2align	1
            .type	main,%function
            .code	16                      @ @main
            .thumb_func
        main:
            .fnstart
        @ BB#0:
            .pad	#24
            sub	sp, #24
            movs	r0, #0
            str	r0, [sp, #20]
            str	r0, [sp, #16]
            str	r0, [sp, #12]
            movs	r0, #1
            str	r0, [sp, #8]
            movs	r0, #2
            str	r0, [sp, #4]
            movs	r0, #3
            str	r0, [sp]
            b	.LBB0_1
        .LBB0_1:                                @ =>This Inner Loop Header: Depth=1
            ldr	r0, [sp, #32]
            ldr	r1, [sp, #12]
            cmp	r0, r1
            bne	.LBB0_3
            b	.LBB0_2
        .LBB0_2:                                @   in Loop: Header=BB0_1 Depth=1
            ldr	r0, [sp, #24]
            ldr	r1, [sp, #28]
            adds	r0, r0, r1
            str	r0, [sp, #40]
            b	.LBB0_3
        .LBB0_3:                                @   in Loop: Header=BB0_1 Depth=1
            ldr	r0, [sp, #32]
            ldr	r1, [sp, #8]
            cmp	r0, r1
            bne	.LBB0_5
            b	.LBB0_4
        .LBB0_4:                                @   in Loop: Header=BB0_1 Depth=1
            ldr	r0, [sp, #24]
            ldr	r1, [sp, #28]
            subs	r0, r0, r1
            str	r0, [sp, #40]
            b	.LBB0_5
        .LBB0_5:                                @   in Loop: Header=BB0_1 Depth=1
            ldr	r0, [sp, #32]
            ldr	r1, [sp, #4]
            cmp	r0, r1
            bne	.LBB0_7
            b	.LBB0_6
        .LBB0_6:                                @   in Loop: Header=BB0_1 Depth=1
            ldr	r0, [sp, #24]
            ldr	r1, [sp, #28]
            muls	r1, r0, r1
            str	r1, [sp, #40]
            b	.LBB0_7
        .LBB0_7:                                @   in Loop: Header=BB0_1 Depth=1
            ldr	r0, [sp, #32]
            ldr	r1, [sp]
            cmp	r0, r1
            bne	.LBB0_9
            b	.LBB0_8
        .LBB0_8:                                @   in Loop: Header=BB0_1 Depth=1
            ldr	r0, [sp, #24]
            ldr	r1, [sp, #28]
            lsls	r0, r1
            str	r0, [sp, #40]
            b	.LBB0_9
        .LBB0_9:                                @   in Loop: Header=BB0_1 Depth=1
            b	.LBB0_1
        .Lfunc_end0:
            .size	main, .Lfunc_end0-main
            .cantunwind
            .fnend


            .ident	\"clang version 4.0.1 (tags/RELEASE_401/final)\"
            .section	\".note.GNU-stack\",\"\",%progbits
            .eabi_attribute	30, 5	@ Tag_ABI_optimization_goals
        ";

        let output = Assembler::run_test(input).unwrap();
        let expected_outptut = "v2.0 raw\nb098 2000 9014 9010 900c 2001 9008 \
        2002 9004 2003 9000 defe 9820 990c 4288 d104 defe 9818 991c 1840 9028 \
        defe 9820 9908 4288 d104 defe 9818 991c 1a40 9028 defe 9820 9904 4288 \
        d104 defe 9818 991c 4341 9128 defe 9820 9900 4288 d104 defe 9818 991c \
        4088 9028 defe ded5 0000 ";
        assert_eq!(output, expected_outptut);
    }
}
