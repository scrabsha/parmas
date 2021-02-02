use crate::encoder::{Encodable, EncodedInstruction, InstructionEncoder};

// The shift, add, sub, mov opcodes header, section 10.1.1.
#[derive(Clone, Copy, Debug, PartialEq)]
struct SasmHeader;

impl Encodable for SasmHeader {
    fn encode(self, instruct: InstructionEncoder) -> InstructionEncoder {
        instruct.then(false).then(false)
    }
}

// The data processing header, section 10.1.2.
#[derive(Clone, Copy, Debug, PartialEq)]
struct DpHeader;

impl Encodable for DpHeader {
    fn encode(self, instruct: InstructionEncoder) -> InstructionEncoder {
        instruct
            .then(false)
            .then(true)
            .then(false)
            .then(false)
            .then(false)
            .then(false)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Op {
    // Shift, add, sub, mov, section 10.1.1.
    LslI(Register, Register, Imm5),
    LsrI(Register, Register, Imm5),
    AsrI(Register, Register, Imm5),
    AddR(Register, Register, Register),
    SubR(Register, Register, Register),
    AddI(Register, Register, Imm3),
    SubI(Register, Register, Imm3),
    MovI(Register, Imm8),

    // Data processing, section 10.1.2.
    And(Register, Register),
    Eor(Register, Register),
    LslR(Register, Register),
    LsrR(Register, Register),
    AsrR(Register, Register),
    AdcR(Register, Register),
    SbcR(Register, Register),
    RorR(Register, Register),
    Tst(Register, Register),
    Rsb(Register, Register), // This is strange
    Cmp(Register, Register),
    Cmn(Register, Register),
    Orr(Register, Register),
    Mul(Register, Register, Register),
    Bic(Register, Register),
    Mvn(Register, Register),

    // Load/Store, section 10.1.3.
    Str(Register, Imm8),
    Ldr(Register, Imm8),

    // Miscellianous 16-bit instructions, section 10.1.4.
    AddSp(Imm7),
    SubSp(Imm7),

    // Branch, section 10.1.6.
    B(Condition, String),
}

impl Op {
    pub(crate) fn encode(&self) -> EncodedInstruction {
        InstructionEncoder::new()
            .then(self)
            .into_to_encoded_instruction()
    }
}

impl Encodable for &Op {
    fn encode(self, instruct: InstructionEncoder) -> InstructionEncoder {
        match self {
            Op::LslI(rd, rm, imm5) => instruct
                .then(SasmHeader)
                .then((false, false, false))
                .then(*rd)
                .then(*rm)
                .then(*imm5),

            Op::LsrI(rd, rm, imm5) => instruct
                .then(SasmHeader)
                .then((false, false, true))
                .then(*imm5)
                .then(*rm)
                .then(*rd),

            Op::AsrI(rd, rm, imm5) => instruct
                .then(SasmHeader)
                .then((false, true, false))
                .then(*imm5)
                .then(*rm)
                .then(*rd),

            Op::AddR(rd, rn, rm) => instruct
                .then(SasmHeader)
                .then((false, true, true))
                .then((false, false))
                .then(*rm)
                .then(*rn)
                .then(*rd),

            Op::SubR(rd, rn, rm) => instruct
                .then(SasmHeader)
                .then((false, true, true))
                .then((false, true))
                .then(*rm)
                .then(*rn)
                .then(*rd),

            Op::AddI(rd, rn, imm3) => instruct
                .then(SasmHeader)
                .then((false, true, true))
                .then((true, false))
                .then(*imm3)
                .then(*rn)
                .then(*rd),

            Op::SubI(rd, rn, imm3) => instruct
                .then(SasmHeader)
                .then((false, true, true))
                .then((true, true))
                .then(*imm3)
                .then(*rn)
                .then(*rd),

            Op::MovI(rd, imm8) => instruct
                .then(SasmHeader)
                .then((true, false, false))
                .then(*rd)
                .then(*imm8),

            Op::And(rdn, rm) => instruct
                .then(DpHeader)
                .then((false, false, false, false))
                .then(*rm)
                .then(*rdn),

            Op::Eor(rdn, rm) => instruct
                .then(DpHeader)
                .then((false, false, false, true))
                .then(*rm)
                .then(*rdn),

            Op::LslR(rdn, rm) => instruct
                .then(DpHeader)
                .then((false, false, true, false))
                .then(*rm)
                .then(*rdn),

            Op::LsrR(rdn, rm) => instruct
                .then(DpHeader)
                .then((false, false, true, false))
                .then(*rm)
                .then(*rdn),

            Op::AsrR(rdn, rm) => instruct
                .then(DpHeader)
                .then((false, true, false, false))
                .then(*rm)
                .then(*rdn),

            _ => todo!(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Register {
    R0,
    R1,
    R2,
    R3,
    R4,
    R5,
    R6,
    R7,
}

impl Encodable for Register {
    fn encode(self, instr: InstructionEncoder) -> InstructionEncoder {
        use Register::*;
        let bits = match self {
            R0 => (false, false, false),
            R1 => (false, false, true),
            R2 => (false, true, false),
            R3 => (false, true, true),
            R4 => (true, false, false),
            R5 => (true, false, true),
            R6 => (true, true, false),
            R7 => (true, true, true),
        };

        instr.then(bits)
    }
}

// Must be < 32
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Imm5(pub usize);

impl Encodable for Imm5 {
    fn encode(self, instruct: InstructionEncoder) -> InstructionEncoder {
        let v = self.0;
        let bits = (
            v & 0b10000 != 0,
            v & 0b01000 != 0,
            v & 0b00100 != 0,
            v & 0b00010 != 0,
            v & 0b00001 != 0,
        );

        instruct.then(bits)
    }
}

// Must be < 256
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Imm8(pub usize);

impl Encodable for Imm8 {
    fn encode(self, instruct: InstructionEncoder) -> InstructionEncoder {
        let v = self.0;
        let (hi, lo) = (
            (
                v & 0b10000000 != 0,
                v & 0b01000000 != 0,
                v & 0b00100000 != 0,
                v & 0b00010000 != 0,
            ),
            (
                v & 0b00001000 != 0,
                v & 0b00000100 != 0,
                v & 0b00000010 != 0,
                v & 0b00000001 != 0,
            ),
        );

        instruct.then(hi).then(lo)
    }
}

// Must be < 128
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Imm7(pub usize);

// Must be < 8
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Imm3(pub usize);

impl Encodable for Imm3 {
    fn encode(self, instruct: InstructionEncoder) -> InstructionEncoder {
        let v = self.0;
        let bits = (v & 0b100 != 0, v & 0b010 != 0, v & 0b001 != 0);

        instruct.then(bits)
    }
}

// Must be < 15
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Condition(pub u8);
