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
use smt_multiplex::args::Args;
use smt_multiplex::linearizing_solver::LinearizingSolver;
use smt_multiplex::log::enable_logging;
use smt_multiplex::util::reader_from_args;

fn main() {
    let args = Args::parse();

    enable_logging(args.log_path.as_deref());

    let mut ls = LinearizingSolver::new(CompliantSolver::z3(&args.z3_path.unwrap()).unwrap());

    let mut reader = reader_from_args(&args);
    let mut stdout = std::io::stdout().lock();

    let mut smtServer = SmtServer::new(reader, stdout, ls);
    smtServer.run();
}
