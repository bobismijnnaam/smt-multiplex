/*
This file is just a front for whatever smt solver we use below it. It is not meant to do anything
useful, just pass on commands, and print the result from the underlying solver to stdout.
It is intended as an exercise/reference for basic stuff.
 */

use std::fs::File;
use std::io::BufReader;
use std::path::Path;
use smt_multiplex::parser::*;
use smt_multiplex::compliant_solver::CompliantSolver;
use smt_multiplex::solver::Solver;
use smt_multiplex::uninterpreted_ast::{GeneralResponse, Response, ScriptCommand};
use smt_multiplex::smt_server::*;

fn main() {
    let f = File::open("predicateExistsTest4.smt2").unwrap();
    let mut reader = BufReader::new(f);
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
