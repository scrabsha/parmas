use std::marker::PhantomData;
use std::fmt;

#[derive(Copy, Clone)]
pub(crate) struct Succ<T: AddBit>(PhantomData<T>);

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

pub(crate) trait AddBit {
    const OFFSET: usize;

    fn add_bit(bit: bool, instr: u16) -> u16 {
        let or_val = if bit {
            1 << Self::OFFSET
        } else {
            0
        };

        instr | or_val
    }
}

impl AddBit for T0 {
    const OFFSET: usize = 0;
}

impl<T: AddBit> AddBit for Succ<T> {
    const OFFSET: usize = <T as AddBit>::OFFSET + 1;
}

pub struct T0;
type T10 = Succ10<T0>;

/// Allows to encode an instruction, bit by bit.
pub(crate) struct InstructionEncoder<T> {
    op: u16,
    marker: PhantomData<T>,
}

impl InstructionEncoder<T0> {
    /// Creates a new, empty `InstructionEncoder`.
    pub(crate) fn new() -> InstructionEncoder<T0> {
        InstructionEncoder {
            op: 0,
            marker: PhantomData,
        }
    }
}

impl<T: AddBit> InstructionEncoder<T> {
    fn add_bit(self, bit: bool) -> InstructionEncoder<Succ<T>> {
        let op = T::add_bit(bit, self.op);

        InstructionEncoder {
            op,
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
        EncodedInstruction(self.op)
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

impl<T: AddBit> Encodable<T> for bool {
    type Output = Succ<T>;

    fn encode(self, instruct: InstructionEncoder<T>) -> InstructionEncoder<Self::Output> {
        instruct.add_bit(self)
    }
}

impl<T: AddBit> Encodable<T> for (bool, bool) {
    type Output = Succ2<T>;

    fn encode(self, instruct: InstructionEncoder<T>) -> InstructionEncoder<Self::Output> {
        let (a, b) = self;

        instruct.add_bit(a).add_bit(b)
    }
}

impl<T: AddBit> Encodable<T> for (bool, bool, bool) {
    type Output = Succ3<T>;

    fn encode(self, instruct: InstructionEncoder<T>) -> InstructionEncoder<Self::Output> {
        let (a, b, c) = self;

        instruct.add_bit(a).add_bit(b).add_bit(c)
    }
}

impl<T: AddBit> Encodable<T> for (bool, bool, bool, bool) {
    type Output = Succ4<T>;

    fn encode(self, instruct: InstructionEncoder<T>) -> InstructionEncoder<Self::Output> {
        let (a, b, c, d) = self;

        instruct.add_bit(a).add_bit(b).add_bit(c).add_bit(d)
    }
}

impl<T: AddBit> Encodable<T> for (bool, bool, bool, bool, bool) {
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
