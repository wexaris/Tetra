use clap_derive::Parser;
use std::path::PathBuf;

#[derive(Parser, Debug, Clone)]
#[command(version, about, long_about = None)]
pub struct CliArgs {
    /// Package root file
    #[arg(required = true)]
    pub input: PathBuf,

    /// Output name
    #[arg(short, long, default_value = "out")]
    pub name: String,

    /// Directory to store compilation objects
    #[arg(long, default_value = ".")]
    pub dir: PathBuf,

    /// Target output of the compilation
    #[arg(short, long, value_enum, default_value_t = Default::default())]
    pub output: Output,

    /// Print the AST while doing compilation
    #[arg(long)]
    pub print_ast: bool,

    /// Print the IR while doing compilation
    #[arg(long)]
    pub print_ir: bool,
}

#[derive(Default, Debug, Clone, Eq, PartialEq)]
pub enum Output {
    #[default]
    Executable,
    LibDynamic,
    LibStatic,
    Objects,
    Assembly,
    LlvmBitCode,
    LlvmIr,
}

#[allow(dead_code, unreachable_code, unused_variables, unused_braces, unused_qualifications)]
impl clap::ValueEnum for Output {
    fn value_variants<'a>() -> &'a [Self] {
        &[
            Self::Executable,
            Self::LibDynamic,
            Self::LibStatic,
            Self::Objects,
            Self::Assembly,
            Self::LlvmBitCode,
            Self::LlvmIr,
        ]
    }
    fn to_possible_value<'a>(&self) -> Option<clap::builder::PossibleValue> {
        match self {
            Self::Executable =>
                Some({ clap::builder::PossibleValue::new("exe") }),
            Self::LibDynamic =>
                Some({ clap::builder::PossibleValue::new("dynamic").aliases(["so", "dll"]) }),
            Self::LibStatic =>
                Some({ clap::builder::PossibleValue::new("static").aliases(["ar", "lib"]) }),
            Self::Objects =>
                Some({ clap::builder::PossibleValue::new("obj") }),
            Self::Assembly =>
                Some({ clap::builder::PossibleValue::new("asm") }),
            Self::LlvmBitCode =>
                Some({ clap::builder::PossibleValue::new("bc") }),
            Self::LlvmIr =>
                Some({ clap::builder::PossibleValue::new("ir") }),
        }
    }
}
