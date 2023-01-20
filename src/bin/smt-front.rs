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

fn main() {
    let args = Args::parse();

    enable_logging();

    let mut reader: Box<dyn Read> = match &args.input {
        Some(p) => {
            Box::new(File::open(&p).unwrap())
        }
        None => {
            Box::new(std::io::stdin().lock())
        }
    };
    let mut stdout = std::io::stdout().lock();

    let solver = CompliantSolver::z3(&args.z3_path.unwrap()).unwrap();

    let mut smt_server = SmtServer::new(reader, stdout, solver);
    smt_server.run();
}
