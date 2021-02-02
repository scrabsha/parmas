use std::env;
use std::fs::{self, File, OpenOptions};
use std::io::Write;
use std::path::{Path, PathBuf};

mod encoder;
pub mod op;
pub mod parser;

pub type Result<T> = std::result::Result<T, &'static str>;

fn input_file_name() -> Result<PathBuf> {
    env::args_os()
        .nth(1)
        .map(Into::into)
        .ok_or("No input file provided")
}

fn output_file(input_file_name: &Path) -> Result<File> {
    let output_file_path = input_file_name.with_extension("raw");

    OpenOptions::new()
        .create(true)
        .append(false)
        .truncate(true)
        .write(true)
        .open(output_file_path)
        .map_err(|_| "Failed to open output file: IO error")
}

static OUTPUT_HEADER: &str = "v2.0 raw\n";

fn main() -> Result<()> {
    let input_name = input_file_name()?;
    let data = fs::read_to_string(input_name.as_path())
        .map_err(|_| "Failed to open input file: IO error")?;

    let mut output_file = output_file(input_name.as_path())?;
    output_file
        .write_all(OUTPUT_HEADER.as_bytes())
        .map_err(|_| "Failed to write output file header: IO error")?;

    let mut tail = data.as_str();

    while !tail.is_empty() {
        let (op, rest) = parser::parse_op(tail)?;

        output_file
            .write_fmt(format_args!("{} ", op.encode()))
            .map_err(|_| "Write failed: IO error")?;

        tail = rest;
    }

    Ok(())
}
