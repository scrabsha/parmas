//! Represents a specific ARM-Cortex M0 operation.
//!
//! This modules contains the `Op` enum as well as all its dependencies. It
//! also implements the encoding of all these types.

use crate::encoder::{
    AddBit, Encodable, EncodedInstruction, InstructionEncoder, Succ10, Succ2, Succ3, Succ4, Succ5, Succ7,
    Succ6, Succ8,
};

// The shift, add, sub, mov opcodes header.
/// Represents the Shift, Add, Sub, Mov instruction header.
///
/// See section A5.2.1 (page 130) of the ARMv7 Architecture Manual.
#[derive(Clone, Copy, Debug, PartialEq)]
struct SasmHeader;

impl<T: AddBit> Encodable<T> for SasmHeader {
    type Output = Succ2<T>;

    fn encode(self, instruct: InstructionEncoder<T>) -> InstructionEncoder<Self::Output> {
        instruct.then(false).then(false)
    }
}

// The data processing header.
/// Represents the data processing instruction header.
///
/// See section A5.2.2 (page 131) of the ARMv7 Architecture Manual.
#[derive(Clone, Copy, Debug, PartialEq)]
struct DpHeader;

impl<T: AddBit> Encodable<T> for DpHeader {
    type Output = Succ6<T>;

    fn encode(self, instruct: InstructionEncoder<T>) -> InstructionEncoder<Self::Output> {
        instruct
            .then(false)
            .then(true)
            .then(false)
            .then(false)
            .then(false)
            .then(false)
    }
}

/// Represents the Load, Store instruction header.
///
/// See section A5.2.4 (page 133) of the ARMv7 Architecture Manual.
#[derive(Clone, Copy, Debug, PartialEq)]
struct LsHeader;

impl<T: AddBit> Encodable<T> for LsHeader {
    type Output = Succ4<T>;

    fn encode(self, instruct: InstructionEncoder<T>) -> InstructionEncoder<Self::Output> {
        instruct.then(true).then(false).then(false).then(true)
    }
}

/// Represents the Miscellaneous instruction header.
///
/// See section A5.2.5 (page 134) of the ARMv7 Architecture Manual.
#[derive(Clone, Copy, Debug, PartialEq)]
struct MHeader;

impl<T: AddBit> Encodable<T> for MHeader {
    type Output = Succ4<T>;

    fn encode(self, instruct: InstructionEncoder<T>) -> InstructionEncoder<Self::Output> {
        instruct.then(true).then(false).then(true).then(true)
    }
}

// Next headers:
//   - conditional branch: A.5.2.6 (page 136).

/// Represents a specific ARM-Cortex M0 operation.
///
/// This enum is generated with the `parse_op` function from the `parser`
/// module. It can then encoded to a 16-bit value using the `Encodable` trait
/// and the `encode` method.
#[derive(Clone, Debug, PartialEq)]
pub enum Op {
    // Shift, add, sub, mov, section 10.1.1.
    /// LSL (immediate).
    LslI(Register, Register, Imm5),
    /// LSR (immediate).
    LsrI(Register, Register, Imm5),
    /// ASR (immediate).
    AsrI(Register, Register, Imm5),
    /// ADD (register).
    AddR(Register, Register, Register),
    /// SUB (register).
    SubR(Register, Register, Register),
    /// ADD (immediate).
    AddI(Register, Register, Imm3),
    /// SUB (immediate).
    SubI(Register, Register, Imm3),
    /// MOV (immediate).
    MovI(Register, Imm8),

    // Data processing, section 10.1.2.
    /// AND (register).
    And(Register, Register),
    /// EOR (register).
    Eor(Register, Register),
    /// LSR (register).
    LslR(Register, Register),
    /// LSR (register).
    LsrR(Register, Register),
    /// ASR (register).
    AsrR(Register, Register),
    /// ADC (register).
    AdcR(Register, Register),
    /// SBC (register).
    SbcR(Register, Register),
    /// ROR (register).
    RorR(Register, Register),
    /// TST (register).
    Tst(Register, Register),
    /// RSB (immediate).
    Rsb(Register, Register), // This is strange
    /// CMP (register).
    Cmp(Register, Register),
    /// CMN (register).
    Cmn(Register, Register),
    /// ORR (register).
    Orr(Register, Register),
    /// MUL.
    Mul(Register, Register),
    /// BIC (register).
    Bic(Register, Register),
    /// MVN (register).
    Mvn(Register, Register),

    // Load/Store, section 10.1.3.
    /// STR (immediate).
    Str(Register, Imm8),
    /// LDR (immediate).
    Ldr(Register, Imm8),

    // Miscellianous 16-bit instructions, section 10.1.4.
    /// ADD (SP plus immediate).
    AddSp(Imm7),
    /// SUB (SP minus immediate).
    SubSp(Imm7),

    // Branch, section 10.1.6.
    /// B (conditionnal branch).
    B(Condition, String),
}

impl Op {
    /// Creates an `EncodedInstruction` from the current instruction.
    ///
    /// # Example
    ///
    /// ```rust
    /// let v = Op::LslI(Register::R3, Register::R1, Imm5(20));
    /// assert_eq!(v.encode(), EncodedInstruction(Ox050b));
    /// ```
    pub(crate) fn encode(&self) -> EncodedInstruction {
        InstructionEncoder::new()
            .then(self)
            .into_to_encoded_instruction()
    }
}

impl<T: AddBit> Encodable<T> for &Op {
    type Output = Succ10<T>;

    fn encode(self, instruct: InstructionEncoder<T>) -> InstructionEncoder<Self::Output> {
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

            Op::AdcR(rdn, rm) => instruct
                .then(DpHeader)
                .then((false, true, false, true))
                .then(*rm)
                .then(*rdn),

            Op::SbcR(rdn, rm) => instruct
                .then(DpHeader)
                .then((false, true, true, false))
                .then(*rm)
                .then(*rdn),

            Op::RorR(rdn, rm) => instruct
                .then(DpHeader)
                .then((false, true, true, true))
                .then(*rm)
                .then(*rdn),

            Op::Tst(rdn, rm) => instruct
                .then(DpHeader)
                .then((true, false, false, false))
                .then(*rm)
                .then(*rdn),

            Op::Rsb(rdn, rm) => instruct
                .then(DpHeader)
                .then((true, false, false, true))
                .then(*rm)
                .then(*rdn),

            Op::Cmp(rdn, rm) => instruct
                .then(DpHeader)
                .then((true, false, true, false))
                .then(*rm)
                .then(*rdn),

            Op::Cmn(rn, rm) => instruct
                .then(DpHeader)
                .then((true, false, true, true))
                .then(*rm)
                .then(*rn),

            Op::Orr(rdn, rm) => instruct
                .then(DpHeader)
                .then((true, true, false, false))
                .then(*rm)
                .then(*rdn),

            Op::Mul(rdn, rn) => instruct
                .then(DpHeader)
                .then((true, true, false, true))
                .then(*rn)
                .then(*rdn),

            Op::Bic(rdn, rm) => instruct
                .then(DpHeader)
                .then((true, true, true, false))
                .then(*rm)
                .then(*rdn),

            Op::Mvn(rd, rm) => instruct
                .then(DpHeader)
                .then((true, true, true, true))
                .then(*rm)
                .then(*rd),

            Op::Str(rt, imm8) => instruct.then(LsHeader).then(false).then(*rt).then(*imm8),

            Op::Ldr(rt, imm8) => instruct.then(LsHeader).then(true).then(*rt).then(*imm8),

            Op::AddSp(imm7) => instruct
                .then(MHeader)
                .then((false,false, false, false, false))
                .then(*imm7),

            _ => todo!(),
        }
    }
}

/// Represents a valid register.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Register {
    /// Register 0.
    R0,
    /// Register 1.
    R1,
    /// Register 2.
    R2,
    /// Register 3.
    R3,
    /// Register 4.
    R4,
    /// Register 5.
    R5,
    /// Register 6.
    R6,
    /// Register 7.
    R7,
}

impl<T: AddBit> Encodable<T> for Register {
    type Output = Succ3<T>;

    fn encode(self, instr: InstructionEncoder<T>) -> InstructionEncoder<Self::Output> {
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

/// Represents an Imm5.
///
/// An imm5 is a contiguous sequence of five bits.
///
/// It is not guaranteed to be five bits long. Such constraint must be checked
/// when the structure is created.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Imm5(pub usize);

impl<T: AddBit> Encodable<T> for Imm5 {
    type Output = Succ5<T>;

    fn encode(self, instruct: InstructionEncoder<T>) -> InstructionEncoder<Self::Output> {
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
/// Represents an Imm8.
///
/// An imm8 is a contiguous sequence of eight bits.
///
/// It is not guaranteed to be eight bits long. Such constraint must be checked
/// when the structure is created.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Imm8(pub usize);

impl<T: AddBit> Encodable<T> for Imm8 {
    type Output = Succ8<T>;

    fn encode(self, instruct: InstructionEncoder<T>) -> InstructionEncoder<Self::Output> {
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

/// Represents an Imm7.
///
/// An imm7 is a contiguous sequence of seven bits.
///
/// It is not guaranteed to be seven bits long. Such constraint must be checked
/// when the structure is created.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Imm7(pub usize);

impl<T: AddBit> Encodable<T> for Imm7 {
    type Output = Succ7<T>;

    fn encode(self, instruct: InstructionEncoder<T>) -> InstructionEncoder<Self::Output> {
        let v = self.0;
        let (hi, lo) = (
            (
                v & 0b1000000 != 0,
                v & 0b0100000 != 0,
                v & 0b0010000 != 0,
            ),
            (
                v & 0b0001000 != 0,
                v & 0b0000100 != 0,
                v & 0b0000010 != 0,
                v & 0b0000001 != 0,
            )
        );

        instruct.then(hi).then(lo)
    }
}

/// Represents an Imm".
///
/// An imm3 is a contiguous sequence of three bits.
///
/// It is not guaranteed to be three bits long. Such constraint must be checked
/// when the structure is created.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Imm3(pub usize);

impl<T: AddBit> Encodable<T> for Imm3 {
    type Output = Succ3<T>;

    fn encode(self, instruct: InstructionEncoder<T>) -> InstructionEncoder<Self::Output> {
        let v = self.0;
        let bits = (v & 0b100 != 0, v & 0b010 != 0, v & 0b001 != 0);

        instruct.then(bits)
    }
}

/// Represents any condition.
///
/// The inner value must be lower than 14. It must be checked when the
/// the structure is created.
///
/// Each value maps to a specific condition, as defined in the following table.
///
/// | Value | Condition Code | Signification |
/// | ----- | -------------- | ------------- |
/// | `0000` | EQ | Equality |
/// | `0001` | NE | Non-equality |
/// | `0010` | CS | Carry set |
/// | `0011` | CC | Carry clear |
/// | `0100` | MI | Minus, negative |
/// | `0101` | PL | Plus, positive |
/// | `0110` | VS | OVerflow Set |
/// | `0111` | VC | OVerflow Clear |
/// | `1000` | HI | Unsigned higher |
/// | `1001` | LS | Unsigner lower or same |
/// | `1010` | GE | Signed greater or equal |
/// | `1011` | LT | Signed less than |
/// | `1100` | GT | Signed greater than |
/// | `1101` | LE | Signed less than or equal |
/// | `1110`, `1111` | Unused | N/A |
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Condition(pub u8);
