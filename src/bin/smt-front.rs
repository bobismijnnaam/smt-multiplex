/*
This file is just a front for whatever smt solver we use below it. It is not meant to do anything
useful, just pass on commands, and print the result from the underlying solver to stdout.
It is intended as an exercise/reference for basic stuff.
 */

use std::fs::File;
use std::io::{BufReader, Read};
use std::path::{Path, PathBuf};
use smt_multiplex::parser::*;
use smt_multiplex::compliant_solver::CompliantSolver;
use smt_multiplex::solver::Solver;
use smt_multiplex::uninterpreted_ast::{GeneralResponse, Response, ScriptCommand};
use smt_multiplex::smt_server::*;
use log::{error, info, Level, Metadata, Record};
use utf8_read::Reader;
use smt_multiplex::args::Args;
use smt_multiplex::linearizing_solver::LinearizingSolver;
use clap::Parser;
use smt_multiplex::log::enable_logging;
use smt_multiplex::util::{reader_from_args, solver_from_args_or_env_or_exit};

fn main() {
    let args = Args::parse();

    enable_logging(args.log_path.as_deref());

    let reader = reader_from_args(&args);
    let mut stdout = std::io::stdout().lock();

    let (solver_path, solver_args) = solver_from_args_or_env_or_exit(args);
    trace!("selected solver: {}", solver_path);

    let solver = CompliantSolver::new(&solver_path, solver_args).unwrap();

    let mut smt_server = SmtServer::new(reader, stdout, solver);
    smt_server.run();
}
