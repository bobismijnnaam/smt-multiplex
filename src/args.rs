use std::path::PathBuf;
// use clap::Parser;
use clap::clap_derive::Parser;

#[derive(Parser, Debug)]
#[command(author, version, about)]
pub struct Args {
    /// Input file. If not provided, read from stdin
    pub input: Option<PathBuf>,

    /// Log path
    #[arg(short, long, value_name = "FILE")]
    pub log_path: Option<PathBuf>,

    // z3 path
    #[arg(long, value_name = "PATH")]
    pub z3_path: Option<PathBuf>
}

