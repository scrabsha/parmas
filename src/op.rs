#[derive(Clone, Debug, PartialEq)]
pub enum Op {
    // Shift, add, sub, mov, section 10.1.1.
    LslI(Register, Register, Imm5),
    LsrI(Register, Register, Imm5),
    AsrI(Register, Register, Imm5),
    AddR(Register, Register, Register),
    SubR(Register, Register, Register),
    AddI(Register, Register, Imm5),
    SubI(Register, Register, Imm5),
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
    R8,
}

// Must be < 32
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Imm5(pub usize);

// Must be < 256
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Imm8(pub usize);

// Must be < 128
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Imm7(pub usize);

// Must be < 15
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Condition(pub u8);