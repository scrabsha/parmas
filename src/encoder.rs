//! Allows to encode data into 16-bit instructions.
//!
//! The `InstructionEncoder` struct represent an in-progress encoding of a
//! 16-bits word. It can then be translated to an `EncodedInstruction`. The way
//! an object is encoded is described thanks to the `Encodable` trait.
//!
//! In order to statically ensure that exactly 16 bits are written for each
//! instruction, a Peano-like arithmetic system is defined. It allows us to
//! track at compile-time how much bits have been encoded. This corresponds to
//! The `T0`, `Succ*` and `AddBit` definitions.

use std::marker::PhantomData;
use std::fmt;

/// Represents the successor of a number.
///
/// This allows us, toghether with the `T0` struct, to define a peano-like
/// numering.
#[derive(Copy, Clone)]
pub(crate) struct Succ<T: AddBit>(PhantomData<T>);

/// Represents the `Succ` operator applied two times.
pub(crate) type Succ2<T> = Succ<Succ<T>>;
/// Represents the `Succ` operator applied three times.
pub(crate) type Succ3<T> = Succ<Succ2<T>>;
/// Represents the `Succ` operator applied four times.
pub(crate) type Succ4<T> = Succ<Succ3<T>>;
/// Represents the `Succ` operator applied five times.
pub(crate) type Succ5<T> = Succ<Succ4<T>>;
/// Represents the `Succ` operator applied six times.
pub(crate) type Succ6<T> = Succ<Succ5<T>>;
/// Represents the `Succ` operator applied seven times.
pub(crate) type Succ7<T> = Succ<Succ6<T>>;
/// Represents the `Succ` operator applied eight times.
pub(crate) type Succ8<T> = Succ<Succ7<T>>;
/// Represents the `Succ` operator applied nine times.
pub(crate) type Succ9<T> = Succ<Succ8<T>>;
/// Represents the `Succ` operator applied ten times.
///
/// The value is named in hexadecimal.
pub(crate) type SuccA<T> = Succ<Succ9<T>>;
/// Represents the `Succ` operator applied eleven times.
///
/// The value is named in hexadecimal.
pub(crate) type SuccB<T> = Succ<SuccA<T>>;
/// Represents the `Succ` operator applied twelve times.
///
/// The value is named in hexadecimal.
pub(crate) type SuccC<T> = Succ<SuccB<T>>;
/// Represents the `Succ` operator applied thirteen times.
///
/// The value is named in hexadecimal.
pub(crate) type SuccD<T> = Succ<SuccC<T>>;
/// Represents the `Succ` operator applied fourteen times.
///
/// The value is named in hexadecimal.
pub(crate) type SuccE<T> = Succ<SuccD<T>>;
/// Represents the `Succ` operator applied fifteen times.
///
/// The value is named in hexadecimal.
pub(crate) type SuccF<T> = Succ<SuccE<T>>;
/// Represents the `Succ` operator applied sixteen times.
///
/// The value is named in hexadecimal.
pub(crate) type Succ10<T> = Succ<SuccF<T>>;

/// Defines how a specific bit should be set.
///
/// This allows us, once we know how much bits have been written in an
/// instruction, to properly write the next ones.
pub(crate) trait AddBit {
    /// Represents where the bit should be written in the 16-bit word.
    const OFFSET: usize;

    /// Writes a bit to a 16-bit word.
    ///
    /// This function should not be redefined when this trait is implemented
    /// a specific type.
    fn add_bit(bit: bool, instr: u16) -> u16 {
        let or_val = if bit {
            1 << (15 - Self::OFFSET)
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

/// The initial number, 0.
///
/// With the `succ*` types, we are able to define a Peano-like arithmetic
/// system.
pub struct T0;

/// Represents 16 on the Peano arithmetic system.
type T10 = Succ10<T0>;

/// Allows to encode an instruction, bit by bit.
///
/// Encoding bits is done with a continuation-passing-style, with the `then`
/// method. Once exactly 16 bits have been encoded, the
/// `into_encoded_instruction` allows to generate the final
/// `EncodedInstruction`.
///
/// The generic type parameter allows to statically track how much bits have
/// been written, and hence write the next one at the correct place.
#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) struct InstructionEncoder<T> {
    /// The bits currently written to the encoder.
    op: u16,
    /// Tracks how much bits have been written.
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
    /// Adds a single bit to the encoder.
    fn add_bit(self, bit: bool) -> InstructionEncoder<Succ<T>> {
        let op = T::add_bit(bit, self.op);

        InstructionEncoder {
            op,
            marker: PhantomData,
        }
    }

    /// Adds some bits to the encoder.
    pub(crate) fn then<U>(self, bits: U) -> InstructionEncoder<<U as Encodable<T>>::Output>
    where
        U: Encodable<T>,
    {
        bits.encode(self)
    }
}

impl InstructionEncoder<T10> {
    /// Generates final instructions.
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

/// Allows to define how data must is encoded.
pub(crate) trait Encodable<T> {
    /// Defines the offset of the resulting encoder.
    ///
    /// The `Succ*` types can be used in order to ease this definition.
    type Output;

    /// Adds data to an encoder.
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
