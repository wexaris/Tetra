use std::ffi::OsStr;
use std::path::PathBuf;
use clap::Parser;
use clap_derive::Parser;

#[derive(Parser, Debug, Clone)]
#[command(version, about, long_about = None)]
pub struct CliArgs {
    /// Package root file
    #[arg(required = true)]
    pub input: PathBuf,

    /// Output file name
    #[arg(short, long)]
    pub name: Option<String>,

    #[arg(long)]
    pub print_ast: bool,

    #[arg(long)]
    pub print_ir: bool,
}

pub fn parse() -> CliArgs {
    let mut args = CliArgs::parse();

    if args.name.is_none() {
        let input_stem = args.input.file_stem().unwrap_or(OsStr::new(OUT_FILE));

        if let Some(name) = input_stem.to_str() {
            args.name = Some(name.to_string());
        }
    }

    args
}

#[cfg(unix)]
static OUT_FILE: &str = "out";
#[cfg(windows)]
static OUT_FILE: &str = "out.exe";
