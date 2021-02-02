use std::fmt;

/// Allows to encode an instruction, bit by bit.
pub(crate) struct InstructionEncoder {
    current_op: u16,
    bit_idx: i8,
}

impl InstructionEncoder {
    /// Creates a new, empty `InstructionEncoder`.
    pub(crate) fn new() -> InstructionEncoder {
        InstructionEncoder {
            current_op: 0,
            bit_idx: 15,
        }
    }

    /// Adds a single byte at the right of the current bytes
    ///
    /// Panics if there is no room left in the instruction.
    fn add_bit(&mut self, b: bool) {
        assert!(
            self.bit_idx < 0,
            "Attempt to write too much bits in a single instruction"
        );

        let byte_val = match b {
            true => 1,
            false => 0,
        };

        self.current_op |= byte_val << self.bit_idx;
        self.bit_idx -= 1;
    }

    /// Adds bytes at the right of the current bytes
    pub(crate) fn with_bits<'a>(
        mut self,
        bs: impl IntoIterator<Item = &'a bool>,
    ) -> InstructionEncoder {
        bs.into_iter().for_each(|b| self.add_bit(*b));

        self
    }

    /// Allows to encode the current instruction.
    ///
    /// Panics if not exactly 16 bits have been added.
    pub(crate) fn into_to_encoded_instruction(self) -> EncodedInstruction {
        assert!(
            self.bit_idx == -1,
            "Not enough bits to create an instruction"
        );

        EncodedInstruction(self.current_op)
    }

    /// Adds new bits at the right of current bits.
    pub(crate) fn then(self, bits: impl Encodable) -> InstructionEncoder {
        bits.encode(self)
    }
}

/// Represents an encoded instruction.
#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) struct EncodedInstruction(u16);

impl fmt::Display for EncodedInstruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:x}", self.0)
    }
}

pub(crate) trait Encodable {
    fn encode(self, instruct: InstructionEncoder) -> InstructionEncoder;
}

impl Encodable for bool {
    fn encode(self, mut instruct: InstructionEncoder) -> InstructionEncoder {
        instruct.add_bit(self);
        instruct
    }
}

impl Encodable for (bool, bool) {
    fn encode(self, mut instruct: InstructionEncoder) -> InstructionEncoder {
        let (a, b) = self;
        instruct.add_bit(a);
        instruct.add_bit(b);
        instruct
    }
}


impl Encodable for (bool, bool, bool) {
    fn encode(self, mut instruct: InstructionEncoder) -> InstructionEncoder {
        let (a, b, c) = self;
        instruct.add_bit(a);
        instruct.add_bit(b);
        instruct.add_bit(c);
        instruct
    }
}

impl Encodable for (bool, bool, bool, bool) {
    fn encode(self, mut instruct: InstructionEncoder) -> InstructionEncoder {
        let (a, b, c, d) = self;
        instruct.add_bit(a);
        instruct.add_bit(b);
        instruct.add_bit(c);
        instruct.add_bit(d);
        instruct
    }
}

impl Encodable for (bool, bool, bool, bool, bool) {
    fn encode(self, mut instruct: InstructionEncoder) -> InstructionEncoder {
        let (a, b, c, d, e) = self;
        instruct.add_bit(a);
        instruct.add_bit(b);
        instruct.add_bit(c);
        instruct.add_bit(d);
        instruct.add_bit(e);

        instruct
    }
}
