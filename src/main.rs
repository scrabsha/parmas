//! The parmas (PARM-assembler) main file.
//!
//! ```none
//! ####    #   ####  #   #   #    ###
//! #   #  # #  #   # ## ##  # #  #
//! ####   ###  ####  # # #  ###   ###
//! #     #   # # #   #   # #   #     #
//! #     #   # #  #  #   # #   #  ###
//!```
//!
//! *Note:* in order to see this program's documentation, run:
//!
//! ```bash
//! cargo doc --document-private-items --open
//! ```

use std::env;
use std::fs::{File, OpenOptions};
use std::path::PathBuf;

mod driver;
mod encoder;
mod labels;
mod op;
mod parser;

use driver::Assembler;

/// A result type that is used accross the program.
///
/// This type allows us to reduce error handling as its minimal form. Once
/// an error is encountered, it is immediatly propagated with the `?` operator.
/// The error message are not spanned.
type Result<T> = std::result::Result<T, &'static str>;

/// Opens and returns the input file submitted from cli if it exists.
///
/// If no input file is provided, then `None` is returned. If, for any reason,
/// the input file could not be opened, then `Some(Err(_))` is returned.
///
/// This file is only readable.
fn input_file() -> Option<Result<File>> {
    let name: PathBuf = env::args_os().nth(1).map(Into::into)?;

    let file = OpenOptions::new()
        .read(true)
        .open(name)
        .map_err(|_| "Failed to open output file: I/O error");

    Some(file)
}

// Opens and returns the output file from cli arguments if it exists.
///
/// The output file is the same as the input file, but with the `raw` extension
/// instead.
///
/// If no input file is provided, then `None` is returned. If, for any reason,
/// the output file could not be opened, then `Some(Err(_))` is returned.
///
/// This file is writeable.
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

/// The program entry point.
fn main() -> Result<()> {
    let mut input = input_file().transpose()?;
    let mut output = output_file().transpose()?;
    Assembler::run(input.as_mut(), output.as_mut())
}
