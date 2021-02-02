use crate::{
    op::{Imm5, Imm7, Imm8, Op, Register},
    Result,
};

fn whitespaces_split_idx(input: &str) -> usize {
    input
        .char_indices()
        .find(|(_, chr)| !chr.is_whitespace())
        .map(|(idx, _)| idx)
        .unwrap_or_else(|| input.len())
}

fn whitespaces(input: &str) -> Result<&str> {
    let idx = whitespaces_split_idx(input);
    if idx == 0 {
        Err("Expected whitespaces")
    } else {
        Ok(input.split_at(idx).1)
    }
}

fn whitespaces_opt(input: &str) -> &str {
    let idx = whitespaces_split_idx(input);
    input.split_at(idx).1
}

fn symbol(input: &str) -> Result<(&str, &str)> {
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

fn register(input: &str) -> Result<(Register, &str)> {
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

fn lit(input: &str) -> Result<(usize, &str)> {
    let mut crs = input.char_indices();

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

fn imm5(input: &str) -> Result<(Imm5, &str)> {
    match lit(input)? {
        (v, tail) if v < 32 => Ok((Imm5(v), tail)),
        _ => Err("Invalid imm5 value"),
    }
}

fn imm7(input: &str) -> Result<(Imm7, &str)> {
    match lit(input)? {
        (v, tail) if v < 128 => Ok((Imm7(v), tail)),
        _ => Err("Invalid imm7 value"),
    }
}

fn imm8(input: &str) -> Result<(Imm8, &str)> {
    match lit(input)? {
        (v, tail) if v < 256 => Ok((Imm8(v), tail)),
        _ => Err("Invalid imm7 value"),
    }
}

fn comma(input: &str) -> Result<&str> {
    if input.starts_with(',') {
        Ok(input.split_at(1).1)
    } else {
        Err("Expected `,`")
    }
}

fn comma_and_maybe_whitespaces(input: &str) -> Result<&str> {
    let tail = comma(input)?;
    Ok(whitespaces_opt(tail))
}

fn parse_lsls_args(input: &str) -> Result<(Op, &str)> {
    let (rd, tail) = register(input)?;
    let tail = comma_and_maybe_whitespaces(tail)?;
    let (rm, tail) = register(tail)?;
    let tail = comma_and_maybe_whitespaces(tail)?;
    let (imm5, tail) = imm5(tail)?;
    let op = Op::LslI(rd, rm, imm5);
    Ok((op, tail))
}

fn parse_op(input: &str) -> Result<(Op, &str)> {
    let (opcode, tail) = symbol(input)?;
    let tail = whitespaces(tail)?;

    let opcode = opcode.to_lowercase();

    match opcode.as_str() {
        "lsls" => parse_lsls_args(tail),
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
}