use clap::Parser;
use crate::driver::Driver;

mod ast;
mod cli_args;
mod codegen;
mod driver;
mod error;
mod log;
mod parse;
mod validate;

fn main() {
    log::init();

    let args = cli_args::CliArgs::parse();

    if let Err(e) = Driver::run(args) {
        log::error(e).print()
    }
}
