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
use clap::Parser;
use log::{Level, Metadata, Record};
use utf8_read::Reader;
use smt_multiplex::linearizing_solver::LinearizingSolver;

/// Passthrough program that sits inbetween a user and an SMT solver and does nothing.
#[derive(Parser, Debug)]
#[command(author, version, about)]
struct Args {
    /// Input file. If not provided, read from stdin
    input: Option<PathBuf>,

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

    let mut reader: Box<dyn Read> = match &args.input {
        Some(p) => {
            Box::new(File::open(&p).unwrap())
        }
        None => {
            Box::new(std::io::stdin().lock())
        }
    };
    let mut stdout = std::io::stdout().lock();


    let solver = match CompliantSolver::z3(Path::new("z3")) {
        Ok(s) => {
            println!("Success");
            s
        }
        Err(err) => {
            println!("{}", err);
            return
        }
    };

    let mut smtServer = SmtServer::new(reader, stdout, solver);
    smtServer.run();
}
