use std::env;
use std::fs::{File, OpenOptions};
use std::path::PathBuf;

mod driver;
mod encoder;
pub mod op;
pub mod parser;

use driver::Assembler;

pub type Result<T> = std::result::Result<T, &'static str>;

fn input_file() -> Option<Result<File>> {
    let name: PathBuf = env::args_os().nth(1).map(Into::into)?;

    let file = OpenOptions::new()
        .read(true)
        .open(name)
        .map_err(|_| "Failed to open output file: I/O error");

    Some(file)
}

fn output_file() -> Option<Result<File>> {
    let output_file_path = env::args_os()
        .nth(1)
        .map(PathBuf::from)?
        .with_extension("raw");

    let output = OpenOptions::new()
        .create(true)
        .append(false)
        .truncate(true)
        .write(true)
        .open(output_file_path)
        .map_err(|_| "Failed to open output file: IO error");

    Some(output)
}

fn main() -> Result<()> {
    let input = input_file().transpose()?;
    let output = output_file().transpose()?;
    Assembler::run(input, output)
}
