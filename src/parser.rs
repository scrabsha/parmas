//! A parser for the UAL language.
//!
//! This crate different kind of functions. Some allow to parse a specific
//! terminal, while other allow to combine several parsing functions.
//!
//! The parsing functions return a `ParsingResult<T>`, which is a modified
//! version of `Result`, which holds the parsed data and the remaining input.

use crate::{
    op::{Condition, Imm3, Imm5, Imm7, Imm8, RawOp, Register},
    Result,
};

/// Represents either a successfull parsing, or a failure.
///
/// The data contained in the second tuple member is the remaining input.
type ParsingResult<'a, T> = Result<(T, &'a str)>;

/// Combines two parsing functions.
///
/// An error is returned if either `f` or `g` returned an error. Otherwise,
/// the two results are returned.
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

/// Combines three parsing functions.
///
/// An error is returned if either `f`, `g` or `h` returned an error.
/// Otherwise, the three results are returned.
fn multiple3<'a, A, B, C, F, G, H>(input: &'a str, fa: F, fb: G, fc: H) -> ParsingResult<(A, B, C)>
where
    A: 'a,
    B: 'a,
    C: 'a,
    F: Fn(&'a str) -> ParsingResult<A>,
    G: Fn(&'a str) -> ParsingResult<B>,
    H: Fn(&'a str) -> ParsingResult<C>,
{
    let ((va, vb), tail) = multiple2(input, fa, fb)?;
    let (vc, tail) = fc(tail)?;

    Ok(((va, vb, vc), tail))
}

/// Combines five parsing functions.
///
/// An error is returned if either `f`, `g` `h`, `i` or `j` returned an error.
/// Otherwise, the five results are returned.
fn multiple4<'a, A, B, C, D, F, G, H, I>(
    input: &'a str,
    f1: F,
    f2: G,
    f3: H,
    f4: I,
) -> ParsingResult<(A, B, C, D)>
where
    A: 'a,
    B: 'a,
    C: 'a,
    D: 'a,
    F: Fn(&'a str) -> ParsingResult<A>,
    G: Fn(&'a str) -> ParsingResult<B>,
    H: Fn(&'a str) -> ParsingResult<C>,
    I: Fn(&'a str) -> ParsingResult<D>,
{
    let ((v1, v2), tail) = multiple2(input, f1, f2)?;
    let ((v3, v4), tail) = multiple2(tail, f3, f4)?;

    Ok(((v1, v2, v3, v4), tail))
}

/// Combines five parsing functions.
///
/// An error is returned if either `f`, `g` `h`, `i` or `j` returned an error.
/// Otherwise, the five results are returned.
fn multiple5<'a, A, B, C, D, E, F, G, H, I, J>(
    input: &'a str,
    f1: F,
    f2: G,
    f3: H,
    f4: I,
    f5: J,
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
    let ((v1, v2, v3), tail) = multiple3(input, f1, f2, f3)?;
    let ((v4, v5), tail) = multiple2(tail, f4, f5)?;

    Ok(((v1, v2, v3, v4, v5), tail))
}

/// Parses two instruction arguments.
///
/// Instruction arguments are separated by one comma and zero or more
/// whitespaces.
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

/// Parses three instruction arguments.
///
/// Instruction arguments are separated by one comma and zero or more
/// whitespaces.
fn args3<'a, A, B, C, F, G, H>(input: &'a str, f1: F, f2: G, f3: H) -> ParsingResult<(A, B, C)>
where
    A: 'a,
    B: 'a,
    C: 'a,
    F: Fn(&'a str) -> ParsingResult<A>,
    G: Fn(&'a str) -> ParsingResult<B>,
    H: Fn(&'a str) -> ParsingResult<C>,
{
    let ((v1, _, v2, _, v3), tail) = multiple5(input, f1, arg_sep, f2, arg_sep, f3)?;
    Ok(((v1, v2, v3), tail))
}

/// Returns the byte-index of the first non-whitespace of a string slice.
///
/// The definition of whitespace follows the definition given by the unicode
/// standard.
fn whitespaces_split_idx(input: &str) -> usize {
    input
        .char_indices()
        .find(|(_, chr)| !chr.is_whitespace())
        .map(|(idx, _)| idx)
        .unwrap_or_else(|| input.len())
}

/// Returns whether if a string slice starts with a whitespace or not.
///
/// The definition of whitespace follows the definition given by the unicode
/// standard.
fn starts_with_whitespace(input: &str) -> bool {
    input
        .chars()
        .next()
        .map(char::is_whitespace)
        .unwrap_or(false)
}

/// Returns whether if a string slice starts with a comment or not.
///
/// A comment starts with either `//` or `/*`.
fn starts_with_comment(input: &str) -> bool {
    input.starts_with("//") || input.starts_with("/*")
}

/// Returns the byte-index of the first non-comment character of a string
/// slice.
///
/// If `input` starts with `//`, then the first non-comment character is the
/// character following the next newline.
///
/// If `input` starts with `/*`, then the first non-comment character is the
/// character following the next `*/`.
///
/// In other situations, `Ok(0)` is returned.
///
/// Returns an error if input starts with `/*` but contains no other `*/`.
fn comment_split_idx(input: &str) -> Result<usize> {
    if input.starts_with("//") || input.starts_with('@') {
        Ok(input
            .char_indices()
            .skip_while(|(_, chr)| *chr != '\n')
            .map(|(idx, _)| idx)
            .nth(1)
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

/// Removes whitespaces at the beginning of a string.
///
/// Whitespace follows the definition of unicode whitespace.
///
/// If `input` does not start with a whitespace, then an error is returned.
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

    if eaten_bytes == 0 {
        Err("Expected whitespaces")
    } else {
        Ok(((), input))
    }
}

/// Parses an optional amount of whitespaces from a string.
///
/// See the documentation of `whitespaces` for more information.
///
/// This function is guaranteed to always succeed.
fn whitespaces_opt(input: &str) -> ParsingResult<()> {
    let v = whitespaces(input).unwrap_or(((), input));

    Ok(v)
}

/// Parses a symbol from an input string.
///
/// A symbol is a contiguous sequence of alphabetic characters, as defined in
/// the unicode standard.
///
/// Returns an error if `input` does not start with an alphabetic character.
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

/// Translates a char into a possible register id.
///
/// If `input` is one of `0`, `1`, `2`, `3`, `4`, `5`, `6`, `7`, then it gets
/// translated as a register. Otherwise, an error is returned.
///
/// A register is always represented as a single char, so this function accepts
/// a single char.
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

/// Parses a register from a string.
///
/// A register is represented by the symbol `r`, immediatly followed by a valid
/// register id.
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

/// Parses a number literal from a string.
///
/// A number literal is composed of a `#` followed by one or more decimal
/// digits.
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

/// Parses an `imm3` from an input string.
///
/// An `imm3` is a literal whose value is lower than 8.
fn imm3(input: &str) -> ParsingResult<Imm3> {
    match lit(input)? {
        (v, tail) if v < 8 => Ok((Imm3(v), tail)),
        _ => Err("Invalid imm3 value"),
    }
}

/// Parses an `imm5` from an input string.
///
/// An `imm5` is a literal whose value is lower than 32.
fn imm5(input: &str) -> ParsingResult<Imm5> {
    match lit(input)? {
        (v, tail) if v < 32 => Ok((Imm5(v), tail)),
        _ => Err("Invalid imm5 value"),
    }
}

/// Parses an `imm7` from an input string.
///
/// An `imm7` is a literal whose value is lower than 128.
fn imm7(input: &str) -> ParsingResult<Imm7> {
    match lit(input)? {
        (v, tail) if v < 128 => Ok((Imm7(v), tail)),
        _ => Err("Invalid imm7 value"),
    }
}

/// Parses an `imm8` from an input string.
///
/// An `imm8` is a literal whose value is lower than 256.
fn imm8(input: &str) -> ParsingResult<Imm8> {
    match lit(input)? {
        (v, tail) if v < 256 => Ok((Imm8(v), tail)),
        _ => Err("Invalid imm7 value"),
    }
}

/// Parses a stack adress from an input string.
///
/// A stack adress is an imm8 that is a multiple of 4, in which case, it is
/// returned divided by 4.
///
/// Note: while this is not true for regular arm processors, this is actually
/// needed for our 8-bit one.
///
/// To further increase the derpiness, if the imm8 is not a multiple of 4, then
/// it still gets divided, and an error is printed on the stack.
fn stack_adress(input: &str) -> ParsingResult<Imm8> {
    let (Imm8(i), tail) = imm8(input)?;

    if i & 0b11 != 0 {
        eprintln!("Invalid stack adress: should be multiple of 4");
    }

    Ok((Imm8(i / 4), tail))
}

/// Parses a comma `,`.
fn comma(input: &str) -> ParsingResult<()> {
    if input.starts_with(',') {
        Ok(((), input.split_at(1).1))
    } else {
        Err("Expected `,`")
    }
}

/// Parses an instruction argument separator.
///
/// An instruction argument separator is defined zero or more whitespaces, a
/// comma and zero or more whitespaces.
fn arg_sep(input: &str) -> ParsingResult<()> {
    let ((_, _, _), tail) = multiple3(input, whitespaces_opt, comma, whitespaces_opt)?;
    Ok(((), tail))
}

/// Parses the `SP` register.
///
/// Returns an error if the next symbol is not the `SP` register.
fn sp(input: &str) -> ParsingResult<()> {
    let (i, tail) = symbol(input)?;

    if i.to_lowercase() == "sp" {
        Ok(((), tail))
    } else {
        Err("Expected SP register")
    }
}

/// Eats a single expected char from an input string.
///
/// If `input` does not start with `c`, then `None` is returned. Otherwise,
/// the input tail is returned.
fn eat_char(input: &str, c: char) -> Option<&str> {
    if input.starts_with(c) {
        let (_, tail) = input.split_at(1);
        Some(tail)
    } else {
        None
    }
}

/// Parses a left bracket (`[`).
fn left_bracket(input: &str) -> ParsingResult<()> {
    eat_char(input, '[')
        .map(|tail| ((), tail))
        .ok_or("Expected `[`")
}

/// Parses a right bracket (`]`).
fn right_bracket(input: &str) -> ParsingResult<()> {
    eat_char(input, ']')
        .map(|tail| ((), tail))
        .ok_or("Expected `]`")
}

/// Parses a colon (`:`).
fn colon(input: &str) -> ParsingResult<()> {
    eat_char(input, ':')
        .map(|tail| ((), tail))
        .ok_or("Expected `:`")
}

/// Parses a label identifier.
///
/// A label idenfitier is an optional dot, followed by one or more alphanumeric
/// characters, and `_`.
fn label_identifier(input: &str) -> ParsingResult<&str> {
    let (tail, init_length) = if input.starts_with('.') {
        (input.split_at(1).1, 1)
    } else {
        (input, 0)
    };

    let rest_split_idx = tail
        .char_indices()
        .find(|(_, c)| !c.is_alphanumeric() && *c != '_')
        .map(|(idx, _)| idx)
        .unwrap_or_else(|| tail.len());

    if rest_split_idx < 1 {
        return Err("Expected label");
    }

    let (label, tail) = input.split_at(init_length + rest_split_idx);
    Ok((label, tail))
}

/// Returns the condition number corresponding to a branch instruction.
///
/// `input` is supposed to be lowercase. If `input` does not correspond to a
/// condition, then an error is returned.
fn branch_condition(input: &str) -> Result<Condition> {
    match input {
        "beq" => Ok(Condition(0)),
        "bne" => Ok(Condition(1)),
        "bcs" => Ok(Condition(2)),
        "bcc" => Ok(Condition(3)),
        "bmi" => Ok(Condition(4)),
        "bpl" => Ok(Condition(5)),
        "bvs" => Ok(Condition(6)),
        "bvc" => Ok(Condition(7)),
        "bhi" => Ok(Condition(8)),
        "bls" => Ok(Condition(9)),
        "bge" => Ok(Condition(10)),
        "blt" => Ok(Condition(11)),
        "bgt" => Ok(Condition(12)),
        "ble" => Ok(Condition(13)),
        "b" => Ok(Condition(14)),
        _ => Err("Unknown branching instruction"),
    }
}

/// Parses an optional SP symbol, followed by an `arg_sep`.
///
/// This parser is guaranteed to succeed.
fn sp_arg_opt(input: &str) -> ParsingResult<()> {
    multiple2(input, sp, arg_sep)
        .map(|((_, _), tail)| ((), tail))
        .or(Ok(((), input)))
}

/// Parses the inner part of the second argument of STR and LDR instructions.
///
/// The inner part corresonds to what is between `[` and `]`.
fn load_store_second_argument_inner(input: &str) -> ParsingResult<Imm8> {
    multiple5(input, whitespaces_opt, sp, arg_sep, stack_adress, whitespaces_opt)
        .map(|((_, _, _, imm8, _), tail)| (imm8, tail))
        .or_else(|_| {
            multiple3(input, whitespaces_opt, sp, whitespaces_opt)
                .map(|((_, _, _), tail)| (Imm8(0), tail))
        })
}

/// Parses the second argument of the STR and LDR instructions.
fn load_store_second_argument(input: &str) -> ParsingResult<Imm8> {
    multiple3(
        input,
        left_bracket,
        load_store_second_argument_inner,
        right_bracket,
    )
    .map(|((_, imm8, _), tail)| (imm8, tail))
}

/// Parses the arguments following an LSLS (immediate) instruction.
fn parse_lsls_immediate_args(input: &str) -> ParsingResult<RawOp> {
    let ((rd, rm, imm5), tail) = args3(input, register, register, imm5)?;

    let op = RawOp::LslI(rd, rm, imm5);
    Ok((op, tail))
}

/// Parses the arguments following an LSLS (register) instruction.
fn parse_lsls_register_args(input: &str) -> ParsingResult<RawOp> {
    let ((rdn, rm), tail) = args2(input, register, register)?;

    let op = RawOp::LslR(rdn, rm);
    Ok((op, tail))
}

/// Parses the arguments following an LSLS (any form) instruction.
fn parse_lsls_args(input: &str) -> ParsingResult<RawOp> {
    parse_lsls_immediate_args(input).or_else(|_| parse_lsls_register_args(input))
}

/// Parses the arguments following an LSRS (immediate) instruction.
fn parse_lsrs_immediate_args(input: &str) -> ParsingResult<RawOp> {
    let ((rd, rm, imm5), tail) = args3(input, register, register, imm5)?;

    let op = RawOp::LsrI(rd, rm, imm5);
    Ok((op, tail))
}

/// Parses the arguments following an LSRS (register) instruction.
fn parse_lsrs_register_args(input: &str) -> ParsingResult<RawOp> {
    let ((rdn, rm), tail) = args2(input, register, register)?;

    let op = RawOp::LsrR(rdn, rm);
    Ok((op, tail))
}

/// Parses the arguments following an LSRS (any form) instruction.
fn parse_lsrs_args(input: &str) -> ParsingResult<RawOp> {
    parse_lsrs_immediate_args(input).or_else(|_| parse_lsrs_register_args(input))
}

/// Parses the arguments following an ASRS (immediate) instruction.
fn parse_asrs_args_immediate(input: &str) -> ParsingResult<RawOp> {
    let ((rd, rm, imm5), tail) = args3(input, register, register, imm5)?;

    let op = RawOp::AsrI(rd, rm, imm5);
    Ok((op, tail))
}

/// Parses the arguments following an ASRS (register) instruction.
fn parse_asrs_args_register(input: &str) -> ParsingResult<RawOp> {
    let ((rdn, rm), tail) = args2(input, register, register)?;

    let op = RawOp::AsrR(rdn, rm);
    Ok((op, tail))
}

/// Parses the arguments following an ASRS (any form) instruction.
fn parse_asrs_args(input: &str) -> ParsingResult<RawOp> {
    parse_asrs_args_immediate(input).or_else(|_| parse_asrs_args_register(input))
}

/// Parses the arguments following an ADDS (register) instruction.
fn parse_adds_register_args(input: &str) -> ParsingResult<RawOp> {
    let ((rd, rn, rm), tail) = args3(input, register, register, register)?;

    let op = RawOp::AddR(rd, rn, rm);
    Ok((op, tail))
}

/// Parses the arguments following an ADDS (immediate) instruction.
fn parse_adds_immediate_args(input: &str) -> ParsingResult<RawOp> {
    let ((rd, rn, rm), tail) = args3(input, register, register, imm3)?;

    let op = RawOp::AddI(rd, rn, rm);
    Ok((op, tail))
}

/// Parses the arguments following an ADDS (any form) instruction.
fn parse_adds_args(input: &str) -> ParsingResult<RawOp> {
    parse_adds_register_args(input).or_else(|_| parse_adds_immediate_args(input))
}

/// Parses the arguments following an SUBS (register) instruction.
fn parse_subs_register_args(input: &str) -> ParsingResult<RawOp> {
    let ((rd, rn, rm), tail) = args3(input, register, register, register)?;

    let op = RawOp::SubR(rd, rn, rm);
    Ok((op, tail))
}

/// Parses the arguments following an SUBS (immediate) instruction.
fn parse_subs_immediate_args(input: &str) -> ParsingResult<RawOp> {
    let ((rd, rn, imm3), tail) = args3(input, register, register, imm3)?;

    let op = RawOp::SubI(rd, rn, imm3);
    Ok((op, tail))
}

/// Parses the arguments following an SUBS (any form) instruction.
fn parse_subs_args(input: &str) -> ParsingResult<RawOp> {
    parse_subs_register_args(input).or_else(|_| parse_subs_immediate_args(input))
}

/// Parses the arguments following an MOVS instruction.
fn parse_movs_args(input: &str) -> ParsingResult<RawOp> {
    let ((rd, imm8), tail) = args2(input, register, imm8)?;

    let op = RawOp::MovI(rd, imm8);
    Ok((op, tail))
}

/// Parses the arguments following an ANDS instruction.
fn parse_ands_args(input: &str) -> ParsingResult<RawOp> {
    let ((rdn, rm), tail) = args2(input, register, register)?;

    let op = RawOp::And(rdn, rm);
    Ok((op, tail))
}

/// Parses the arguments following an EORS instruction.
fn parse_eors_args(input: &str) -> ParsingResult<RawOp> {
    let ((rdn, rm), tail) = args2(input, register, register)?;

    let op = RawOp::Eor(rdn, rm);
    Ok((op, tail))
}

/// Parses the arguments following an ADCS instruction.
fn parse_adcs_args(input: &str) -> ParsingResult<RawOp> {
    let ((rdn, rm), tail) = args2(input, register, register)?;

    let op = RawOp::AdcR(rdn, rm);
    Ok((op, tail))
}

/// Parses the arguments following an SBCS instruction.
fn parse_sbcs_args(input: &str) -> ParsingResult<RawOp> {
    let ((rdn, rm), tail) = args2(input, register, register)?;

    let op = RawOp::SbcR(rdn, rm);
    Ok((op, tail))
}

/// Parses the arguments following an RORS instruction.
fn parse_rors_args(input: &str) -> ParsingResult<RawOp> {
    let ((rdn, rm), tail) = args2(input, register, register)?;

    let op = RawOp::RorR(rdn, rm);
    Ok((op, tail))
}

/// Parses the arguments following an TSTS instruction.
fn parse_tsts_args(input: &str) -> ParsingResult<RawOp> {
    let ((rdn, rm), tail) = args2(input, register, register)?;

    let op = RawOp::Tst(rdn, rm);
    Ok((op, tail))
}

/// Parses the arguments following an RSBS instruction.
fn parse_rsbs_args(input: &str) -> ParsingResult<RawOp> {
    let ((rdn, rm, imm), tail) = args3(input, register, register, imm8)?;

    if imm.0 != 0 {
        return Err("Incorrect immediate value");
    }

    let op = RawOp::Rsb(rdn, rm);
    Ok((op, tail))
}

/// Parses the arguments following an CMPS instruction.
fn parse_cmps_args(input: &str) -> ParsingResult<RawOp> {
    let ((rdn, rm), tail) = args2(input, register, register)?;

    let op = RawOp::Cmp(rdn, rm);
    Ok((op, tail))
}

/// Parses the arguments following an CMNS instruction.
fn parse_cmns_args(input: &str) -> ParsingResult<RawOp> {
    let ((rn, rm), tail) = args2(input, register, register)?;

    let op = RawOp::Cmn(rn, rm);
    Ok((op, tail))
}

/// Parses the arguments following an ORRS instruction.
fn parse_orrs_args(input: &str) -> ParsingResult<RawOp> {
    let ((rdn, rm), tail) = args2(input, register, register)?;

    let op = RawOp::Orr(rdn, rm);
    Ok((op, tail))
}

/// Parses the arguments following an MULS instruction.
fn parse_muls_args(input: &str) -> ParsingResult<RawOp> {
    let ((rdm, rn, rdm2), tail) = args3(input, register, register, register)?;

    if rdm != rdm2 {
        return Err("Wrong repeated register");
    }

    let op = RawOp::Mul(rdm, rn);
    Ok((op, tail))
}

/// Parses the arguments following an BICS instruction.
fn parse_bics_args(input: &str) -> ParsingResult<RawOp> {
    let ((rdn, rm), tail) = args2(input, register, register)?;

    let op = RawOp::Bic(rdn, rm);
    Ok((op, tail))
}

/// Parses the arguments following an MVNS instruction.
fn parse_mvns_args(input: &str) -> ParsingResult<RawOp> {
    let ((rdn, rm), tail) = args2(input, register, register)?;

    let op = RawOp::Mvn(rdn, rm);
    Ok((op, tail))
}

/// Parses the arguments of the load and store forms.
fn parse_load_store_args(input: &str) -> ParsingResult<(Register, Imm8)> {
    args2(input, register, load_store_second_argument)
}

/// Parses the arguments following an STR instruction.
fn parse_str_args(input: &str) -> ParsingResult<RawOp> {
    parse_load_store_args(input).map(|((rt, imm8), tail)| (RawOp::Str(rt, imm8), tail))
}

/// Parses the arguments following an LDR instruction.
fn parse_ldr_args(input: &str) -> ParsingResult<RawOp> {
    parse_load_store_args(input).map(|((rt, imm8), tail)| (RawOp::Ldr(rt, imm8), tail))
}

/// Parses the arguments following an ADD instruction.
fn parse_add_args(input: &str) -> ParsingResult<RawOp> {
    let ((_, _, _, imm7), tail) = multiple4(input, sp, arg_sep, sp_arg_opt, imm7)?;

    let op = RawOp::AddSp(imm7);
    Ok((op, tail))
}

/// Parses the arguments following an SUB instruction.
fn parse_sub_args(input: &str) -> ParsingResult<RawOp> {
    let ((_, _, _, imm7), tail) = multiple4(input, sp, arg_sep, sp_arg_opt, imm7)?;

    let op = RawOp::SubSp(imm7);
    Ok((op, tail))
}

/// Parse the arguments following a B-- instruction.
///
/// This function also takes the branch instruction in order to guess which
/// condition is branched.
fn parse_b_args<'a>(opcode: &str, tail: &'a str) -> ParsingResult<'a, RawOp<'a>> {
    let cond = branch_condition(opcode)?;
    let (label, tail) = label_identifier(tail)?;

    let op = RawOp::B(cond, label);
    Ok((op, tail))
}

/// Parses an assembler directive.
///
/// This is not returned for now, as it is not supported.
fn directive_split_idx(input: &str) -> Result<usize> {
    if !input.starts_with('.') {
        return Err("Directive starts with `.`");
    }

    let (name, tail) = label_identifier(input)?;
    if tail.starts_with(':') {
        return Err("Expected directive, found label");
    }

    // We discard input until the next \n.
    let split_idx = tail
        .char_indices()
        .find(|(_, c)| *c == '\n')
        .map(|(idx, _)| idx)
        .unwrap_or_else(|| tail.len());

    let bits_eaten = split_idx + name.len();
    Ok(bits_eaten)
}

/// Parses a collection of directives.
fn directives(input: &str) -> Result<&str> {
    let ((), mut tail) = whitespaces_opt(input)?;
    while let Ok(dsi) = directive_split_idx(tail) {
        tail = tail.split_at(dsi).1;
        tail = whitespaces_opt(tail)?.1;
    }
    Ok(tail)
}

/// Parses a label from an input string.
fn label(input: &str) -> Option<(&str, &str)> {
    let mut input = input;

    if let Ok(directive_idx) = directive_split_idx(input) {
        input = input.split_at(directive_idx).1;
    }

    multiple5(
        input,
        whitespaces_opt,
        label_identifier,
        whitespaces_opt,
        colon,
        whitespaces_opt,
    )
    .ok()
    .map(|((_, label, _, _, _), tail)| (label, tail))
}

/// Parses any number of labels from an input string.
fn labels(input: &str) -> (Vec<&str>, &str) {
    let mut labels = Vec::new();
    let mut tail = input;

    while let Some((l, t)) = label(tail) {
        labels.push(l);
        tail = t;
    }

    (labels, tail)
}

/// Parses an operation from an input string.
///
/// An operation is defined as a mnemonic and a sequence of arguments. The
/// instruction name is recognized and the corresponding function is then
/// called.
fn op(input: &str) -> ParsingResult<RawOp> {
    let ((), input) = whitespaces_opt(input)?;
    let input = directives(input)?;

    if input.is_empty() {
        return Ok((RawOp::Noop, ""));
    }

    let ((_, opcode, _), tail) = multiple3(input, whitespaces_opt, symbol, whitespaces)?;
    let opcode = opcode.to_lowercase();

    let (op, tail) = match opcode.as_str() {
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
        "tst" => parse_tsts_args(tail),
        "rsbs" => parse_rsbs_args(tail),
        "cmp" => parse_cmps_args(tail),
        "cmn" => parse_cmns_args(tail),
        "orrs" => parse_orrs_args(tail),
        "muls" => parse_muls_args(tail),
        "bics" => parse_bics_args(tail),
        "mvns" => parse_mvns_args(tail),
        "str" => parse_str_args(tail),
        "ldr" => parse_ldr_args(tail),
        "add" => parse_add_args(tail),
        "sub" => parse_sub_args(tail),
        branch if branch.starts_with('b') => parse_b_args(branch, tail),

        _ => Err("Unexpected instruction"),
    }?;

    let ((), tail) = whitespaces_opt(tail)?;
    let tail = directives(tail)?;
    let tail = whitespaces_opt(tail)?.1;
    Ok((op, tail))
}

pub(crate) fn parse_op_and_labels(input: &str) -> ParsingResult<(Vec<&str>, RawOp)> {
    let input = directives(input)?;
    let input = whitespaces_opt(input)?.1;
    let (labels, tail) = labels(input);
    let tail = directives(tail)?;
    let tail = whitespaces_opt(tail)?.1;

    let (op, tail) = op(tail)?;
    Ok(((labels, op), tail))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn comment_split_idx_handles_newlines_correctly() {
        assert_eq!(comment_split_idx("// hello\n world"), Ok(9));
        assert_eq!(comment_split_idx("@ foo bar\nbaz"), Ok(10));
    }

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
            op("lsls r4, r2, #12").unwrap().0,
            RawOp::LslI(Register::R4, Register::R2, Imm5(12)),
        );

        assert_eq!(
            op("lsls r4, r2").unwrap().0,
            RawOp::LslR(Register::R4, Register::R2),
        );
    }

    #[test]
    fn parse_op_lsrs() {
        assert_eq!(
            op("lsrs r4, r2, #12").unwrap().0,
            RawOp::LsrI(Register::R4, Register::R2, Imm5(12)),
        );

        assert_eq!(
            op("lsrs r4, r2").unwrap().0,
            RawOp::LsrR(Register::R4, Register::R2),
        );
    }

    #[test]
    fn parse_op_asr() {
        assert_eq!(
            op("asrs r4, r2, #12").unwrap().0,
            RawOp::AsrI(Register::R4, Register::R2, Imm5(12)),
        );

        assert_eq!(
            op("asrs r4, r2").unwrap().0,
            RawOp::AsrR(Register::R4, Register::R2),
        );
    }

    #[test]
    fn parse_op_adds_register() {
        assert_eq!(
            op("adds r4, r2, r0").unwrap().0,
            RawOp::AddR(Register::R4, Register::R2, Register::R0),
        );

        assert_eq!(
            op("adds r4, r2, #6").unwrap().0,
            RawOp::AddI(Register::R4, Register::R2, Imm3(6)),
        );
    }

    #[test]
    fn parse_op_subs_register() {
        assert_eq!(
            op("subs r4, r2, r0").unwrap().0,
            RawOp::SubR(Register::R4, Register::R2, Register::R0),
        );

        assert_eq!(
            op("subs r4, r2, #6").unwrap().0,
            RawOp::SubI(Register::R4, Register::R2, Imm3(6)),
        );
    }

    #[test]
    fn parse_movs() {
        assert_eq!(
            op("movs r3, #99").unwrap().0,
            RawOp::MovI(Register::R3, Imm8(99)),
        );
    }

    #[test]
    fn parse_ands() {
        assert_eq!(
            op("ands r3, r1").unwrap().0,
            RawOp::And(Register::R3, Register::R1),
        );
    }

    #[test]
    fn parse_eors() {
        assert_eq!(
            op("eors r3, r1").unwrap().0,
            RawOp::Eor(Register::R3, Register::R1),
        );
    }

    #[test]
    fn parse_adcs() {
        assert_eq!(
            op("adcs r4, r1").unwrap().0,
            RawOp::AdcR(Register::R4, Register::R1),
        );
    }

    #[test]
    fn parse_sbcs() {
        assert_eq!(
            op("sbcs r4, r1").unwrap().0,
            RawOp::SbcR(Register::R4, Register::R1),
        );
    }

    #[test]
    fn parse_rors() {
        assert_eq!(
            op("rors r4, r1").unwrap().0,
            RawOp::RorR(Register::R4, Register::R1),
        );
    }

    #[test]
    fn parse_tsts() {
        assert_eq!(
            op("tst r4, r1").unwrap().0,
            RawOp::Tst(Register::R4, Register::R1),
        );
    }

    #[test]
    fn parse_rsbs() {
        assert_eq!(
            op("rsbs r4, r1, #0").unwrap().0,
            RawOp::Rsb(Register::R4, Register::R1),
        );
    }

    #[test]
    fn parse_cmps() {
        assert_eq!(
            op("cmp r4, r1").unwrap().0,
            RawOp::Cmp(Register::R4, Register::R1),
        );
    }

    #[test]
    fn parse_cmns() {
        assert_eq!(
            op("cmn r4, r1").unwrap().0,
            RawOp::Cmn(Register::R4, Register::R1),
        );
    }

    #[test]
    fn parse_orrs() {
        assert_eq!(
            op("orrs r4, r1").unwrap().0,
            RawOp::Orr(Register::R4, Register::R1),
        );
    }

    #[test]
    fn parse_muls() {
        assert_eq!(
            op("muls r4, r1, r4").unwrap().0,
            RawOp::Mul(Register::R4, Register::R1),
        );

        assert!(op("muls r4, r1, r2").is_err());
    }

    #[test]
    fn parse_bics() {
        assert_eq!(
            op("bics r4, r1, r4").unwrap().0,
            RawOp::Bic(Register::R4, Register::R1),
        );
    }

    #[test]
    fn parse_mvns() {
        assert_eq!(
            op("mvns r4, r1, r4").unwrap().0,
            RawOp::Mvn(Register::R4, Register::R1),
        );
    }

    #[test]
    fn parse_str() {
        assert_eq!(
            op("str r4, [sp, #168]").unwrap().0,
            RawOp::Str(Register::R4, Imm8(42)),
        );

        assert_eq!(
            op("str r4, [sp]").unwrap().0,
            RawOp::Str(Register::R4, Imm8(0)),
        );
    }

    #[test]
    fn parse_ldr() {
        assert_eq!(
            op("ldr r4, [sp, #168]").unwrap().0,
            RawOp::Ldr(Register::R4, Imm8(42)),
        );

        assert_eq!(
            op("ldr r4, [sp]").unwrap().0,
            RawOp::Ldr(Register::R4, Imm8(0)),
        );
    }

    #[test]
    fn parse_add() {
        assert_eq!(op("add sp, sp, #101").unwrap().0, RawOp::AddSp(Imm7(101)),);

        assert_eq!(op("add sp, #101").unwrap().0, RawOp::AddSp(Imm7(101)),);
    }

    #[test]
    fn parse_sub() {
        assert_eq!(op("sub sp, sp, #101").unwrap().0, RawOp::SubSp(Imm7(101)),);

        assert_eq!(op("sub sp, #101").unwrap().0, RawOp::SubSp(Imm7(101)),);
    }

    #[test]
    fn parse_beq() {
        assert_eq!(op("beq foo").unwrap().0, RawOp::B(Condition(0), "foo"),);
    }

    #[test]
    fn parse_bne() {
        assert_eq!(op("bne bar").unwrap().0, RawOp::B(Condition(1), "bar"),);
    }

    #[test]
    fn parse_bcs() {
        assert_eq!(op("bcs hello").unwrap().0, RawOp::B(Condition(2), "hello"),);
    }

    #[test]
    fn parse_bcc() {
        assert_eq!(op("bcc f").unwrap().0, RawOp::B(Condition(3), "f"),);
    }

    #[test]
    fn parse_bmi() {
        assert_eq!(op("bmi main").unwrap().0, RawOp::B(Condition(4), "main"),);
    }

    #[test]
    fn parse_bpl() {
        assert_eq!(op("bpl ffff").unwrap().0, RawOp::B(Condition(5), "ffff"),);
    }

    #[test]
    fn parse_bvs() {
        assert_eq!(op("bvs end").unwrap().0, RawOp::B(Condition(6), "end"),);
    }

    #[test]
    fn parse_bvc() {
        assert_eq!(
            op("bvc while_start").unwrap().0,
            RawOp::B(Condition(7), "while_start"),
        );
    }

    #[test]
    fn parse_bhi() {
        assert_eq!(
            op("bhi .final").unwrap().0,
            RawOp::B(Condition(8), ".final"),
        );
    }

    #[test]
    fn parse_bls() {
        assert_eq!(op("bls foo").unwrap().0, RawOp::B(Condition(9), "foo"),);
    }

    #[test]
    fn parse_bge() {
        assert_eq!(op("bge h").unwrap().0, RawOp::B(Condition(10), "h"),);
    }

    #[test]
    fn parse_blt() {
        assert_eq!(op("blt p").unwrap().0, RawOp::B(Condition(11), "p"),);
    }

    #[test]
    fn parse_bgt() {
        assert_eq!(op("bgt .foo").unwrap().0, RawOp::B(Condition(12), ".foo"),);
    }

    #[test]
    fn parse_ble() {
        assert_eq!(
            op("ble foobar").unwrap().0,
            RawOp::B(Condition(13), "foobar"),
        );
    }

    #[test]
    fn labels_parses_multiple_labels() {
        let (ls, tail) = labels("foo: bar: .baz: qux: tail");
        assert_eq!(ls, ["foo", "bar", ".baz", "qux"]);
        assert_eq!(tail, "tail");

        let (ls, tail) = labels("hello, world");
        assert!(ls.is_empty());
        assert_eq!(tail, "hello, world");
    }
}
