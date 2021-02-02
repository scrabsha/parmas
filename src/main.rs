pub mod op;
pub mod parser;

pub type Result<T> = std::result::Result<T, &'static str>;

fn main() {
    println!("Hello, world!");
}
