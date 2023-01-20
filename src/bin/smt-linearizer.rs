use std::fs::File;
use std::io::BufReader;
use std::path::{Path, PathBuf};
use smt_multiplex::parser::*;
use smt_multiplex::compliant_solver::CompliantSolver;
use smt_multiplex::solver::Solver;
use smt_multiplex::uninterpreted_ast::{GeneralResponse, Response, ScriptCommand};
use smt_multiplex::smt_server::*;
use clap::Parser;
use log::{Level, Metadata, Record};
use smt_multiplex::linearizing_solver::LinearizingSolver;

/// Program that linearizes an incremental SMT script such that the underlying solver only has to support non-incremental queries + reset
#[derive(Parser, Debug)]
#[command(author, version, about)]
struct Args {
    /// Log path
    #[arg(short, long, value_name = "FILE")]
    log_path: Option<PathBuf>,

    // z3 path
    #[arg(long, value_name = "PATH")]
    z3_path: Option<PathBuf>
}

static MY_LOGGER: MyLogger = MyLogger;

struct MyLogger;

impl log::Log for MyLogger {
    fn enabled(&self, metadata: &Metadata) -> bool {
        metadata.level() <= Level::Info
    }

    fn log(&self, record: &Record) {
        if self.enabled(record.metadata()) {
            println!("{} - {}", record.level(), record.args());
        }
    }
    fn flush(&self) {}
}

// https://docs.rs/log/latest/log/fn.set_logger.html
// TODO: Make this work with the bottom part

fn main() {

    let args = Args::parse();

    let mut ls = LinearizingSolver::new(CompliantSolver::z3(&args.z3_path.unwrap()).unwrap());

    let f = File::open("predicateExistsTest4.smt2").unwrap();
    let mut reader = BufReader::new(f);
    let mut stdout = std::io::stdout().lock();

    let mut smtServer = SmtServer::new(reader, stdout, ls);
    smtServer.run();
}
