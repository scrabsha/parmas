use std::marker::PhantomData;
use std::fmt;

pub(crate) struct Succ<T>(PhantomData<T>);

pub(crate) type Succ2<T> = Succ<Succ<T>>;
pub(crate) type Succ3<T> = Succ<Succ2<T>>;
pub(crate) type Succ4<T> = Succ<Succ3<T>>;
pub(crate) type Succ5<T> = Succ<Succ4<T>>;
pub(crate) type Succ6<T> = Succ<Succ5<T>>;
pub(crate) type Succ7<T> = Succ<Succ6<T>>;
pub(crate) type Succ8<T> = Succ<Succ7<T>>;
pub(crate) type Succ9<T> = Succ<Succ8<T>>;
pub(crate) type SuccA<T> = Succ<Succ9<T>>;
pub(crate) type SuccB<T> = Succ<SuccA<T>>;
pub(crate) type SuccC<T> = Succ<SuccB<T>>;
pub(crate) type SuccD<T> = Succ<SuccC<T>>;
pub(crate) type SuccE<T> = Succ<SuccD<T>>;
pub(crate) type SuccF<T> = Succ<SuccE<T>>;
pub(crate) type Succ10<T> = Succ<SuccF<T>>;

pub struct T0;
type T10 = Succ10<T0>;

/// Allows to encode an instruction, bit by bit.
pub(crate) struct InstructionEncoder<T> {
    current_op: u16,
    bit_idx: i8,
    marker: PhantomData<T>,
}

impl InstructionEncoder<T0> {
    /// Creates a new, empty `InstructionEncoder`.
    pub(crate) fn new() -> InstructionEncoder<T0> {
        InstructionEncoder {
            current_op: 0,
            bit_idx: 15,
            marker: PhantomData,
        }
    }
}

impl<T> InstructionEncoder<T> {
    fn add_bit(mut self, bit: bool) -> InstructionEncoder<Succ<T>> {
        assert!(
            self.bit_idx >= 0,
            "Attempt to write too much bits in a single instruction"
        );

        let byte_val = match bit {
            true => 1,
            false => 0,
        };

        self.current_op |= byte_val << self.bit_idx;

        InstructionEncoder {
            bit_idx: self.bit_idx,
            current_op: self.current_op,
            marker: PhantomData,
        }
    }

    /// Adds new bits at the right of current bits.
    pub(crate) fn then<U>(self, bits: U) -> InstructionEncoder<<U as Encodable<T>>::Output>
    where
        U: Encodable<T>,
    {
        bits.encode(self)
    }
}

impl InstructionEncoder<T10> {
    /// Allows to encode the current instruction.
    ///
    /// Panics if not exactly 16 bits have been added.
    pub(crate) fn into_to_encoded_instruction(self) -> EncodedInstruction {
        EncodedInstruction(self.current_op)
    }
}

/// Represents an encoded instruction.
#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) struct EncodedInstruction(u16);

impl fmt::Display for EncodedInstruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:x?}", self.0)
    }
}

pub(crate) trait Encodable<T> {
    type Output;
    fn encode(self, instruct: InstructionEncoder<T>) -> InstructionEncoder<Self::Output>;
}

impl<T> Encodable<T> for bool {
    type Output = Succ<T>;

    fn encode(self, instruct: InstructionEncoder<T>) -> InstructionEncoder<Self::Output> {
        instruct.add_bit(self)
    }
}

impl<T> Encodable<T> for (bool, bool) {
    type Output = Succ2<T>;

    fn encode(self, instruct: InstructionEncoder<T>) -> InstructionEncoder<Self::Output> {
        let (a, b) = self;

        instruct.add_bit(a).add_bit(b)
    }
}

impl<T> Encodable<T> for (bool, bool, bool) {
    type Output = Succ3<T>;

    fn encode(self, instruct: InstructionEncoder<T>) -> InstructionEncoder<Self::Output> {
        let (a, b, c) = self;

        instruct.add_bit(a).add_bit(b).add_bit(c)
    }
}

impl<T> Encodable<T> for (bool, bool, bool, bool) {
    type Output = Succ4<T>;

    fn encode(self, instruct: InstructionEncoder<T>) -> InstructionEncoder<Self::Output> {
        let (a, b, c, d) = self;

        instruct.add_bit(a).add_bit(b).add_bit(c).add_bit(d)
    }
}

impl<T> Encodable<T> for (bool, bool, bool, bool, bool) {
    type Output = Succ5<T>;

    fn encode(self, instruct: InstructionEncoder<T>) -> InstructionEncoder<Self::Output> {
        let (a, b, c, d, e) = self;

        instruct
            .add_bit(a)
            .add_bit(b)
            .add_bit(c)
            .add_bit(d)
            .add_bit(e)
    }
}
