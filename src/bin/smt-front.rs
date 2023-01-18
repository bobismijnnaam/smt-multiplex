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
    // let mut reader = ScriptParser::new(BufReader::new(f));
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

    /*
    let mut solver = match CompliantSolver::z3(Path::new("z3")) {
        Ok(s) => {
            println!("Success");
            s
        }
        Err(err) => {
            println!("{}", err);
            return
        }
    };

    for command in reader {
        println!("Got: {}", &command);

        fn handleGeneral(response: Response<GeneralResponse>) {
            match response {
                Ok(x) => println!("Response: {}", x),
                Err(x) => {
                    println!("Error: {}", x);
                    std::process::exit(1)
                }
            }
        }

        let res = match command {
            ScriptCommand::DeclareSort(name, arity) => { handleGeneral(solver.declare_sort(&name, &arity)) }
            ScriptCommand::Assert(t) => { handleGeneral(solver.assert(&t)) }
            ScriptCommand::CheckSat => {
                match solver.check_sat(&vec![]) {

                }
            },
            ScriptCommand::CheckSatAssuming(_) => { todo!() }
            ScriptCommand::DeclareConst(name, sort) => { handleGeneral(solver.declare_const(&name, &sort)) },
            ScriptCommand::DeclareDatatype(_, _) => { todo!() }
            ScriptCommand::DeclareDatatypes(_, _) => { todo!() }
            ScriptCommand::DeclareFun { .. } => { todo!() }
            ScriptCommand::DefineConst(_, _, _) => { todo!() }
            ScriptCommand::DefineFun(_) => { todo!() }
            ScriptCommand::DefineFunRec(_) => { todo!() }
            ScriptCommand::DefineFunsRec(_, _) => { todo!() }
            ScriptCommand::DefineSort { .. } => { todo!() }
            ScriptCommand::Echo(_) => { todo!() }
            ScriptCommand::Exit => { todo!() }
            ScriptCommand::GetAssertions => { todo!() }
            ScriptCommand::GetAssignment => { todo!() }
            ScriptCommand::GetInfo(_) => { todo!() }
            ScriptCommand::GetModel => { todo!() }
            ScriptCommand::GetOption(_) => { todo!() }
            ScriptCommand::GetProof => { todo!() }
            ScriptCommand::GetUnsatAssumptions => { todo!() }
            ScriptCommand::GetUnsatCore => { todo!() }
            ScriptCommand::GetValue(_) => { todo!() }
            ScriptCommand::Pop(_) => { todo!() }
            ScriptCommand::Push(_) => { solver.push() }
            ScriptCommand::Reset => { todo!() }
            ScriptCommand::ResetAssertions => { todo!() }
            ScriptCommand::SetInfo(_) => { todo!() }
            ScriptCommand::SetLogic(_) => { todo!() }
            ScriptCommand::SetOption(attribute) => { solver.set_option(&attribute) }
        };
    }
     */
}
