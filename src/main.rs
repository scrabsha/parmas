use std::env;
use std::fs;

pub mod op;
pub mod parser;
mod encoder;

pub type Result<T> = std::result::Result<T, &'static str>;

fn input_data() -> Result<String> {
    let filename = env::args().nth(1).ok_or("No input file")?;
    fs::read_to_string(filename).map_err(|_| "Failed to open file: IO error")
}

fn main() -> Result<()> {
    let data = input_data()?;

    let mut tail = data.as_str();

    while !tail.is_empty() {
        let (op, rest) = parser::parse_op(tail)?;
        tail = rest;
        println!("{:?}", op);
    }

    Ok(())
}
