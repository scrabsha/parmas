//! Represents a specific ARM-Cortex M0 operation.
//!
//! This modules contains the `Op` enum as well as all its dependencies. It
//! also implements the encoding of all these types.

use crate::encoder::{
    AddBit, Encodable, EncodedInstruction, InstructionEncoder, Succ10, Succ2, Succ3, Succ4, Succ5,
    Succ6, Succ7, Succ8,
};

use crate::{labels::LabelTable, Result};

pub(crate) type RawOp<'a> = Op<&'a str>;
pub(crate) type ResolvedOp = Op<Imm8>;

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

/// Represents the Miscellaneous instruction header.
///
/// See section A5.2.6 (page 136) of the ARMv7 Architecture Manual.
#[derive(Clone, Copy, Debug, PartialEq)]
struct BHeader;

impl<T: AddBit> Encodable<T> for BHeader {
    type Output = Succ4<T>;

    fn encode(self, instruct: InstructionEncoder<T>) -> InstructionEncoder<Self::Output> {
        instruct.then(true).then(true).then(false).then(true)
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
pub(crate) enum Op<T> {
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
    B(Condition, T),

    Noop,
}

impl<'a> RawOp<'a> {
    pub(crate) fn resolve_labels(self, pos: usize, ls: &LabelTable) -> Result<ResolvedOp> {
        let translated = match self {
            Op::LslI(a, b, c) => Op::LslI(a, b, c),
            Op::LsrI(a, b, c) => Op::LsrI(a, b, c),
            Op::AsrI(a, b, c) => Op::AsrI(a, b, c),
            Op::AddR(a, b, c) => Op::AddR(a, b, c),
            Op::SubR(a, b, c) => Op::SubR(a, b, c),
            Op::AddI(a, b, c) => Op::AddI(a, b, c),
            Op::SubI(a, b, c) => Op::SubI(a, b, c),
            Op::MovI(a, b) => Op::MovI(a, b),
            Op::And(a, b) => Op::And(a, b),
            Op::Eor(a, b) => Op::Eor(a, b),
            Op::LslR(a, b) => Op::LslR(a, b),
            Op::LsrR(a, b) => Op::LsrR(a, b),
            Op::AsrR(a, b) => Op::AsrR(a, b),
            Op::AdcR(a, b) => Op::AdcR(a, b),
            Op::SbcR(a, b) => Op::SbcR(a, b),
            Op::RorR(a, b) => Op::RorR(a, b),
            Op::Tst(a, b) => Op::Tst(a, b),
            Op::Rsb(a, b) => Op::Rsb(a, b),
            Op::Cmp(a, b) => Op::Cmp(a, b),
            Op::Cmn(a, b) => Op::Cmn(a, b),
            Op::Orr(a, b) => Op::Orr(a, b),
            Op::Mul(a, b) => Op::Mul(a, b),
            Op::Bic(a, b) => Op::Bic(a, b),
            Op::Mvn(a, b) => Op::Mvn(a, b),
            Op::Str(a, b) => Op::Str(a, b),
            Op::Ldr(a, b) => Op::Ldr(a, b),
            Op::AddSp(a) => Op::AddSp(a),
            Op::SubSp(a) => Op::SubSp(a),
            Op::B(a, label) => {
                let from = pos;
                let to = ls.resolve(label)?;
                let delta = compute_branching_delta(from, to)?;
                Op::B(a, delta)
            }
            Op::Noop => Op::Noop,
        };

        Ok(translated)
    }
}

impl ResolvedOp {
    pub(crate) fn encode(&self) -> EncodedInstruction {
        InstructionEncoder::new()
            .then(self)
            .into_to_encoded_instruction()
    }
}

/// Returns how much bytes should be jumped to, returns an error if the
/// branching is impossible.
fn compute_branching_delta(from: usize, to: usize) -> Result<Imm8> {
    let (from, to) = (from as isize, to as isize);
    let delta = to - from - 3;

    if delta.abs() > 127 {
        Err("Illegal branch offset")
    } else {
        let delta = if delta >= 0 {
            delta as usize
        } else {
            0usize.wrapping_sub((-delta) as usize)
        };

        Ok(Imm8(delta))
    }
}

impl<'a, T: AddBit> Encodable<T> for &'a ResolvedOp {
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
                .then((false, false, false, false, false))
                .then(*imm7),

            Op::SubSp(imm7) => instruct
                .then(MHeader)
                .then((false, false, false, false, true))
                .then(*imm7),

            Op::B(cond, imm8) => instruct.then(BHeader).then(*cond).then(*imm8),

            Op::Noop => instruct
                .then((false, false, false, false))
                .then((false, false, false, false))
                .then((false, false, false, false))
                .then((false, false, false, false)),
        }
    }
}

/// Represents a valid register.
#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum Register {
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
pub(crate) struct Imm5(pub(crate) usize);

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
pub(crate) struct Imm8(pub(crate) usize);

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
pub(crate) struct Imm7(pub(crate) usize);

impl<T: AddBit> Encodable<T> for Imm7 {
    type Output = Succ7<T>;

    fn encode(self, instruct: InstructionEncoder<T>) -> InstructionEncoder<Self::Output> {
        let v = self.0;
        let (hi, lo) = (
            (v & 0b1000000 != 0, v & 0b0100000 != 0, v & 0b0010000 != 0),
            (
                v & 0b0001000 != 0,
                v & 0b0000100 != 0,
                v & 0b0000010 != 0,
                v & 0b0000001 != 0,
            ),
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
pub(crate) struct Imm3(pub(crate) usize);

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
/// The inner value must be lower than 15. It must be checked when the
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
/// | `1110` | AL | Always true |
/// | `1111` | Unused | N/A |
#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) struct Condition(pub(crate) u8);

impl<T: AddBit> Encodable<T> for Condition {
    type Output = Succ4<T>;

    fn encode(self, instruct: InstructionEncoder<T>) -> InstructionEncoder<Self::Output> {
        let v = self.0;

        let bits = (
            v & 0b1000 != 0,
            v & 0b0100 != 0,
            v & 0b0010 != 0,
            v & 0b0001 != 0,
        );

        instruct.then(bits)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Encodes an `Op` to an `EncodedInstruction`, and compares it against
    /// an expected value.
    macro_rules! assert_encoding {
        ($op:expr, $encoded:expr $(,)? ) => {{
            let left = $op.encode().0;
            let right = $encoded;

            assert_eq!(left, right);
        }};
    }

    /// Expands to several tests, which compare an Op to a final encoded value.
    /// See the documentation of `assert_encoding` for more.
    macro_rules! tests {
        ($(
            $name:ident :: $op:expr => $encoded:expr
        ),* $(,)?) => {
            $(
                #[test]
                fn $name() {
                    let left = $op;
                    let right = $encoded;
                    assert_encoding!(left, right);
                }
            )*
        }
    }

    tests! {
        sub_sp_12_encoding :: ResolvedOp::SubSp(Imm7(12)) => 0xb08c,
        movs_r0_0_encoding :: ResolvedOp::MovI(Register::R0, Imm8(0)) => 0x2000,
        str_r0_sp_8_encoding :: ResolvedOp::Str(Register::R0, Imm8(8)) => 0x9008,
        movs_r1_1 :: ResolvedOp::MovI(Register::R1, Imm8(1)) => 0x2101,
        str_r1_sp_4_encoding :: ResolvedOp::Str(Register::R1, Imm8(4)) => 0x9104,
    }
}
