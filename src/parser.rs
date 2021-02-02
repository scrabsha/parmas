use crate::{
    op::{Imm5, Imm7, Imm8, Op, Register},
    Result,
};

type ParsingResult<'a, T> = Result<(T, &'a str)>;

fn multiple2<'a, A, B, F, G>(input: &'a str, f: F, g: G) -> ParsingResult<(A, B)>
where
    A: 'a,
    B: 'a,
    F: Fn(&'a str) -> ParsingResult<A>,
    G: Fn(&'a str) -> ParsingResult<B>,
{
    let (a, tail) = f(input)?;
    let (b, tail) = g(tail)?;

    Ok(((a, b), tail))
}

fn multiple3<'a, A, B, C, F, G, H>(input: &'a str, f: F, g: G, h: H) -> ParsingResult<(A, B, C)>
where
    A: 'a,
    B: 'a,
    C: 'a,
    F: Fn(&str) -> ParsingResult<A>,
    G: Fn(&str) -> ParsingResult<B>,
    H: Fn(&str) -> ParsingResult<C>,
{
    let ((a, b), tail) = multiple2(input, f, g)?;
    let (c, tail) = h(tail)?;

    Ok(((a, b, c), tail))
}

fn multiple5<'a, A, B, C, D, E, F, G, H, I, J>(
    input: &'a str,
    f: F,
    g: G,
    h: H,
    i: I,
    j: J,
) -> ParsingResult<(A, B, C, D, E)>
where
    A: 'a,
    B: 'a,
    C: 'a,
    D: 'a,
    E: 'a,
    F: Fn(&str) -> ParsingResult<A>,
    G: Fn(&str) -> ParsingResult<B>,
    H: Fn(&str) -> ParsingResult<C>,
    I: Fn(&str) -> ParsingResult<D>,
    J: Fn(&str) -> ParsingResult<E>,
{
    let ((a, b, c), tail) = multiple3(input, f, g, h)?;
    let ((d, e), tail) = multiple2(tail, i, j)?;

    Ok(((a, b, c, d, e), tail))
}

fn whitespaces_split_idx(input: &str) -> usize {
    input
        .char_indices()
        .find(|(_, chr)| !chr.is_whitespace())
        .map(|(idx, _)| idx)
        .unwrap_or_else(|| input.len())
}

fn whitespaces(input: &str) -> ParsingResult<()> {
    let idx = whitespaces_split_idx(input);
    if idx == 0 {
        Err("Expected whitespaces")
    } else {
        Ok(((), input.split_at(idx).1))
    }
}

fn whitespaces_opt(input: &str) -> &str {
    let idx = whitespaces_split_idx(input);
    input.split_at(idx).1
}

fn symbol(input: &str) -> ParsingResult<&str> {
    let index = input
        .char_indices()
        .find(|(_, chr)| !chr.is_alphabetic())
        .map(|(idx, _)| idx)
        .unwrap_or_else(|| input.len());

    match index {
        0 => Err("Expected symbol"),
        _ => Ok(input.split_at(index)),
    }
}

fn register_id(input: char) -> Result<Register> {
    Ok(match input {
        '0' => Register::R0,
        '1' => Register::R1,
        '2' => Register::R2,
        '3' => Register::R3,
        '4' => Register::R4,
        '5' => Register::R5,
        '6' => Register::R6,
        '7' => Register::R7,
        _ => return Err("Expected register id"),
    })
}

fn register(input: &str) -> ParsingResult<Register> {
    let mut crs = input.char_indices();

    match dbg!(crs.next()) {
        Some((_, 'r')) => {}
        None => return Err("Expected register name, found EOF"),
        Some(_) => return Err("Expected register name"),
    }

    let (_, id) = crs.next().ok_or("Expected register id, found EOF")?;
    let reg = register_id(id)?;
    let tail = crs.as_str();

    Ok((reg, tail))
}

fn lit(input: &str) -> ParsingResult<usize> {
    let mut crs = input.char_indices();

    dbg!(crs.as_str());

    match crs.next() {
        Some((_, '#')) => {}
        None => return Err("Expected register name, found EOF"),
        Some(_) => return Err("Expected `#`"),
    }

    let tail = crs.as_str();
    let idx = crs
        .find(|(_, chr)| !chr.is_numeric())
        .map(|(idx, _)| idx)
        .unwrap_or_else(|| input.len() - 1);

    let (head, tail) = tail.split_at(idx);

    let val = head.parse().unwrap();

    Ok((val, tail))
}

fn imm5(input: &str) -> ParsingResult<Imm5> {
    match lit(input)? {
        (v, tail) if v < 32 => Ok((Imm5(v), tail)),
        _ => Err("Invalid imm5 value"),
    }
}

fn imm7(input: &str) -> ParsingResult<Imm7> {
    match lit(input)? {
        (v, tail) if v < 128 => Ok((Imm7(v), tail)),
        _ => Err("Invalid imm7 value"),
    }
}

fn imm8(input: &str) -> ParsingResult<Imm8> {
    match lit(input)? {
        (v, tail) if v < 256 => Ok((Imm8(v), tail)),
        _ => Err("Invalid imm7 value"),
    }
}

fn comma(input: &str) -> ParsingResult<()> {
    if input.starts_with(',') {
        Ok(((), input.split_at(1).1))
    } else {
        Err("Expected `,`")
    }
}

fn comma_and_maybe_whitespaces(input: &str) -> ParsingResult<()> {
    let (_, tail) = comma(input)?;
    Ok(((), whitespaces_opt(tail)))
}

fn parse_lsls_args(input: &str) -> ParsingResult<Op> {
    let ((rd, _, rm, _, imm5), tail) = multiple5(
        input,
        register,
        comma_and_maybe_whitespaces,
        register,
        comma_and_maybe_whitespaces,
        imm5,
    )?;

    let op = Op::LslI(rd, rm, imm5);
    Ok((op, tail))
}

fn parse_lsrs_args(input: &str) -> ParsingResult<Op> {
    let ((rd, _, rm, _, imm5), tail) = multiple5(
        input,
        register,
        comma_and_maybe_whitespaces,
        register,
        comma_and_maybe_whitespaces,
        imm5,
    )?;

    let op = Op::LsrI(rd, rm, imm5);
    Ok((op, tail))
}

fn parse_asrs_args(input: &str) -> ParsingResult<Op> {
    let ((rd, _, rm, _, imm5), tail) = multiple5(
        input,
        register,
        comma_and_maybe_whitespaces,
        register,
        comma_and_maybe_whitespaces,
        imm5,
    )?;

    let op = Op::AsrI(rd, rm, imm5);
    Ok((op, tail))
}

fn parse_adds_args(input: &str) -> ParsingResult<Op> {
    let ((rd, _, rn, _, rm), tail) = multiple5(
        input,
        register,
        comma_and_maybe_whitespaces,
        register,
        comma_and_maybe_whitespaces,
        register,
    )?;

    let op = Op::AddR(rd, rn, rm);
    Ok((op, tail))
}

pub(crate) fn parse_op(input: &str) -> ParsingResult<Op> {
    let ((opcode, _), tail) = multiple2(input, symbol, whitespaces)?;

    let opcode = opcode.to_lowercase();

    match opcode.as_str() {
        "lsls" => parse_lsls_args(tail),
        "lsrs" => parse_lsrs_args(tail),
        "asrs" => parse_asrs_args(tail),
        "adds" => parse_adds_args(tail),
        _ => todo!(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_op_lsls_immediate() {
        assert_eq!(
            parse_op("lsls r4, r2, #12").unwrap().0,
            Op::LslI(Register::R4, Register::R2, Imm5(12)),
        );
    }

    #[test]
    fn parse_op_lsrs_immediate() {
        assert_eq!(
            parse_op("lsrs r4, r2, #12").unwrap().0,
            Op::LsrI(Register::R4, Register::R2, Imm5(12)),
        );
    }

    #[test]
    fn parse_op_asr_immediate() {
        assert_eq!(
            parse_op("asrs r4, r2, #12").unwrap().0,
            Op::AsrI(Register::R4, Register::R2, Imm5(12)),
        );
    }

    #[test]
    fn parse_op_adds_register() {
        assert_eq!(
            parse_op("adds r4, r2, r0").unwrap().0,
            Op::AddR(Register::R4, Register::R2, Register::R0),
        );
    }
}
