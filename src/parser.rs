use crate::{
    op::{Imm3, Imm5, Imm7, Imm8, Op, Register},
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
    F: Fn(&'a str) -> ParsingResult<A>,
    G: Fn(&'a str) -> ParsingResult<B>,
    H: Fn(&'a str) -> ParsingResult<C>,
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
    F: Fn(&'a str) -> ParsingResult<A>,
    G: Fn(&'a str) -> ParsingResult<B>,
    H: Fn(&'a str) -> ParsingResult<C>,
    I: Fn(&'a str) -> ParsingResult<D>,
    J: Fn(&'a str) -> ParsingResult<E>,
{
    let ((a, b, c), tail) = multiple3(input, f, g, h)?;
    let ((d, e), tail) = multiple2(tail, i, j)?;

    Ok(((a, b, c, d, e), tail))
}

fn args2<'a, A, B, F, G>(input: &'a str, f: F, g: G) -> ParsingResult<(A, B)>
where
    A: 'a,
    B: 'a,
    F: Fn(&'a str) -> ParsingResult<A>,
    G: Fn(&'a str) -> ParsingResult<B>,
{
    let ((a, _, b), tail) = multiple3(input, f, arg_sep, g)?;
    Ok(((a, b), tail))
}

fn args3<'a, A, B, C, F, G, H>(input: &'a str, f: F, g: G, h: H) -> ParsingResult<(A, B, C)>
where
    A: 'a,
    B: 'a,
    C: 'a,
    F: Fn(&'a str) -> ParsingResult<A>,
    G: Fn(&'a str) -> ParsingResult<B>,
    H: Fn(&'a str) -> ParsingResult<C>,
{
    let ((a, _, b, _, c), tail) = multiple5(input, f, arg_sep, g, arg_sep, h)?;
    Ok(((a, b, c), tail))
}

fn whitespaces_split_idx(input: &str) -> usize {
    input
        .char_indices()
        .find(|(_, chr)| !chr.is_whitespace())
        .map(|(idx, _)| idx)
        .unwrap_or_else(|| input.len())
}

fn starts_with_whitespace(input: &str) -> bool {
    input
        .chars()
        .next()
        .map(char::is_whitespace)
        .unwrap_or(false)
}

fn starts_with_comment(input: &str) -> bool {
    input.starts_with("//") || input.starts_with("/*")
}

fn comment_split_idx(input: &str) -> Result<usize> {
    if input.starts_with("//") {
        Ok(input
            .char_indices()
            .find(|(_, chr)| *chr == '\n')
            .map(|(idx, _)| idx)
            .unwrap_or_else(|| input.len()))
    } else if input.starts_with("/*") {
        input
            .find("*/")
            .map(|idx| idx + 2)
            .ok_or("Unclosed multiline comment")
    } else {
        Ok(0)
    }
}

fn whitespaces(mut input: &str) -> ParsingResult<()> {
    let mut eaten_bytes = 0;

    while starts_with_comment(input) || starts_with_whitespace(input) {
        let idx = whitespaces_split_idx(input);
        eaten_bytes += idx;
        input = input.split_at(idx).1;

        let idx = comment_split_idx(input)?;
        eaten_bytes += idx;
        input = input.split_at(idx).1;
    }

    dbg!(input);

    if eaten_bytes == 0 {
        return Err("Expected whitespaces");
    } else {
        Ok(((), input))
    }
}

fn whitespaces_opt(input: &str) -> ParsingResult<()> {
    let idx = whitespaces_split_idx(input);
    Ok(((), input.split_at(idx).1))
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

    match crs.next() {
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

    match crs.next() {
        Some((_, '#')) => {}
        None => return Err("Expected register name, found EOF"),
        Some(_) => return Err("Expected `#`"),
    }

    let tail = crs.as_str();
    let idx = crs
        .find(|(_, chr)| !chr.is_numeric())
        .map(|(idx, _)| idx - 1)
        .unwrap_or_else(|| input.len() - 1);

    let (head, tail) = tail.split_at(idx);
    let val = head.parse().unwrap();

    Ok((val, tail))
}

fn imm3(input: &str) -> ParsingResult<Imm3> {
    match lit(input)? {
        (v, tail) if v < 8 => Ok((Imm3(v), tail)),
        _ => Err("Invalid imm3 value"),
    }
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

fn arg_sep(input: &str) -> ParsingResult<()> {
    let ((_, _), tail) = multiple2(input, comma, whitespaces_opt)?;
    Ok(((), tail))
}

fn parse_lsls_immediate_args(input: &str) -> ParsingResult<Op> {
    let ((rd, rm, imm5), tail) = args3(input, register, register, imm5)?;

    let op = Op::LslI(rd, rm, imm5);
    Ok((op, tail))
}

fn parse_lsls_register_args(input: &str) -> ParsingResult<Op> {
    let ((rdn, rm), tail) = args2(input, register, register)?;

    let op = Op::LslR(rdn, rm);
    Ok((op, tail))
}

fn parse_lsls_args(input: &str) -> ParsingResult<Op> {
    parse_lsls_immediate_args(input).or_else(|_| parse_lsls_register_args(input))
}

fn parse_lsrs_immediate_args(input: &str) -> ParsingResult<Op> {
    let ((rd, rm, imm5), tail) = args3(input, register, register, imm5)?;

    let op = Op::LsrI(rd, rm, imm5);
    Ok((op, tail))
}

fn parse_lsrs_register_args(input: &str) -> ParsingResult<Op> {
    let ((rdn, rm), tail) = args2(input, register, register)?;

    let op = Op::LsrR(rdn, rm);
    Ok((op, tail))
}

fn parse_lsrs_args(input: &str) -> ParsingResult<Op> {
    parse_lsrs_immediate_args(input).or_else(|_| parse_lsrs_register_args(input))
}

fn parse_asrs_args_immediate(input: &str) -> ParsingResult<Op> {
    let ((rd, rm, imm5), tail) = args3(input, register, register, imm5)?;

    let op = Op::AsrI(rd, rm, imm5);
    Ok((op, tail))
}

fn parse_asrs_args_register(input: &str) -> ParsingResult<Op> {
    let ((rdn, rm), tail) = args2(input, register, register)?;

    let op = Op::AsrR(rdn, rm);
    Ok((op, tail))
}

fn parse_asrs_args(input: &str) -> ParsingResult<Op> {
    parse_asrs_args_immediate(input).or_else(|_| parse_asrs_args_register(input))
}

fn parse_adds_register_args(input: &str) -> ParsingResult<Op> {
    let ((rd, rn, rm), tail) = args3(input, register, register, register)?;

    let op = Op::AddR(rd, rn, rm);
    Ok((op, tail))
}

fn parse_adds_immediate_args(input: &str) -> ParsingResult<Op> {
    let ((rd, rn, rm), tail) = args3(input, register, register, imm3)?;

    let op = Op::AddI(rd, rn, rm);
    Ok((op, tail))
}

fn parse_adds_args(input: &str) -> ParsingResult<Op> {
    parse_adds_register_args(input).or_else(|_| parse_adds_immediate_args(input))
}

fn parse_subs_register_args(input: &str) -> ParsingResult<Op> {
    let ((rd, rn, rm), tail) = args3(input, register, register, register)?;

    let op = Op::SubR(rd, rn, rm);
    Ok((op, tail))
}

fn parse_subs_immediate_args(input: &str) -> ParsingResult<Op> {
    let ((rd, rn, imm3), tail) = args3(input, register, register, imm3)?;

    let op = Op::SubI(rd, rn, imm3);
    Ok((op, tail))
}

fn parse_subs_args(input: &str) -> ParsingResult<Op> {
    parse_subs_register_args(input).or_else(|_| parse_subs_immediate_args(input))
}

fn parse_movs_args(input: &str) -> ParsingResult<Op> {
    let ((rd, imm8), tail) = args2(input, register, imm8)?;

    let op = Op::MovI(rd, imm8);
    Ok((op, tail))
}

fn parse_ands_args(input: &str) -> ParsingResult<Op> {
    let ((rdn, rm), tail) = args2(input, register, register)?;

    let op = Op::And(rdn, rm);
    Ok((op, tail))
}

fn parse_eors_args(input: &str) -> ParsingResult<Op> {
    let ((rdn, rm), tail) = args2(input, register, register)?;

    let op = Op::Eor(rdn, rm);
    Ok((op, tail))
}

fn parse_adcs_args(input: &str) -> ParsingResult<Op> {
    let ((rdn, rm), tail) = args2(input, register, register)?;

    let op = Op::AdcR(rdn, rm);
    Ok((op, tail))
}

fn parse_sbcs_args(input: &str) -> ParsingResult<Op> {
    let ((rdn, rm), tail) = args2(input, register, register)?;

    let op = Op::SbcR(rdn, rm);
    Ok((op, tail))
}

fn parse_rors_args(input: &str) -> ParsingResult<Op> {
    let ((rdn, rm), tail) = args2(input, register, register)?;

    let op = Op::RorR(rdn, rm);
    Ok((op, tail))
}

fn parse_tsts_args(input: &str) -> ParsingResult<Op> {
    let ((rdn, rm), tail) = args2(input, register, register)?;

    let op = Op::Tst(rdn, rm);
    Ok((op, tail))
}

fn parse_rsbs_args(input: &str) -> ParsingResult<Op> {
    let ((rdn, rm), tail) = args2(input, register, register)?;

    let op = Op::Rsb(rdn, rm);
    Ok((op, tail))
}

fn parse_cmps_args(input: &str) -> ParsingResult<Op> {
    let ((rdn, rm), tail) = args2(input, register, register)?;

    let op = Op::Cmp(rdn, rm);
    Ok((op, tail))
}

pub(crate) fn parse_op(input: &str) -> ParsingResult<Op> {
    let ((_, opcode, _), tail) = multiple3(input, whitespaces_opt, symbol, whitespaces)?;

    let opcode = opcode.to_lowercase();

    match opcode.as_str() {
        "lsls" => parse_lsls_args(tail),
        "lsrs" => parse_lsrs_args(tail),
        "asrs" => parse_asrs_args(tail),
        "adds" => parse_adds_args(tail),
        "subs" => parse_subs_args(tail),
        "movs" => parse_movs_args(tail),
        "ands" => parse_ands_args(tail),
        "eors" => parse_eors_args(tail),
        "adcs" => parse_adcs_args(tail),
        "sbcs" => parse_sbcs_args(tail),
        "rors" => parse_rors_args(tail),
        "tsts" => parse_tsts_args(tail),
        "rsbs" => parse_rsbs_args(tail),
        "cmps" => parse_cmps_args(tail),
        _ => todo!(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn whitespaces_handles_single_line_comments() {
        let input = "// foo bar\nhello";
        let tail = whitespaces(input).unwrap().1;
        assert_eq!(tail, "hello");
    }

    #[test]
    fn whitespaces_handles_multiline_comments() {
        let input = "/* foo bar baz */hello";
        let tail = whitespaces(input).unwrap().1;
        assert_eq!(tail, "hello");
    }

    #[test]
    fn parse_op_lsls_immediate() {
        assert_eq!(
            parse_op("lsls r4, r2, #12").unwrap().0,
            Op::LslI(Register::R4, Register::R2, Imm5(12)),
        );

        assert_eq!(
            parse_op("lsls r4, r2").unwrap().0,
            Op::LslR(Register::R4, Register::R2),
        );
    }

    #[test]
    fn parse_op_lsrs() {
        assert_eq!(
            parse_op("lsrs r4, r2, #12").unwrap().0,
            Op::LsrI(Register::R4, Register::R2, Imm5(12)),
        );

        assert_eq!(
            parse_op("lsrs r4, r2").unwrap().0,
            Op::LsrR(Register::R4, Register::R2),
        );
    }

    #[test]
    fn parse_op_asr() {
        assert_eq!(
            parse_op("asrs r4, r2, #12").unwrap().0,
            Op::AsrI(Register::R4, Register::R2, Imm5(12)),
        );

        assert_eq!(
            parse_op("asrs r4, r2").unwrap().0,
            Op::AsrR(Register::R4, Register::R2),
        );
    }

    #[test]
    fn parse_op_adds_register() {
        assert_eq!(
            parse_op("adds r4, r2, r0").unwrap().0,
            Op::AddR(Register::R4, Register::R2, Register::R0),
        );

        assert_eq!(
            parse_op("adds r4, r2, #6").unwrap().0,
            Op::AddI(Register::R4, Register::R2, Imm3(6)),
        );
    }

    #[test]
    fn parse_op_subs_register() {
        assert_eq!(
            parse_op("subs r4, r2, r0").unwrap().0,
            Op::SubR(Register::R4, Register::R2, Register::R0),
        );

        assert_eq!(
            parse_op("subs r4, r2, #6").unwrap().0,
            Op::SubI(Register::R4, Register::R2, Imm3(6)),
        );
    }

    #[test]
    fn parse_movs() {
        assert_eq!(
            parse_op("movs r3, #99").unwrap().0,
            Op::MovI(Register::R3, Imm8(99)),
        );
    }

    #[test]
    fn parse_ands() {
        assert_eq!(
            parse_op("ands r3, r1").unwrap().0,
            Op::And(Register::R3, Register::R1),
        );
    }

    #[test]
    fn parse_eors() {
        assert_eq!(
            parse_op("eors r3, r1").unwrap().0,
            Op::Eor(Register::R3, Register::R1),
        );
    }

    #[test]
    fn parse_adcs() {
        assert_eq!(
            parse_op("adcs r4, r1").unwrap().0,
            Op::AdcR(Register::R4, Register::R1),
        );
    }

    #[test]
    fn parse_sbcs() {
        assert_eq!(
            parse_op("sbcs r4, r1").unwrap().0,
            Op::SbcR(Register::R4, Register::R1),
        );
    }

    #[test]
    fn parse_rors() {
        assert_eq!(
            parse_op("rors r4, r1").unwrap().0,
            Op::RorR(Register::R4, Register::R1),
        );
    }

    #[test]
    fn parse_tsts() {
        assert_eq!(
            parse_op("tsts r4, r1").unwrap().0,
            Op::Tst(Register::R4, Register::R1),
        );
    }

    #[test]
    fn parse_rsbs() {
        assert_eq!(
            parse_op("rsbs r4, r1").unwrap().0,
            Op::Rsb(Register::R4, Register::R1),
        );
    }

    #[test]
    fn parse_cmps() {
        assert_eq!(
            parse_op("cmps r4, r1").unwrap().0,
            Op::Cmp(Register::R4, Register::R1),
        );
    }
}
