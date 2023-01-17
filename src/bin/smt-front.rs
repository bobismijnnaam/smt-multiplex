/*
This file is just a front for whatever smt solver we use below it. It is not meant to do anything
useful, just pass on commands, and print the result from the underlying solver to stdout.
It is intended as an exercise/reference for basic stuff.
 */

use std::fs::File;
use std::io::BufReader;
use std::path::Path;
use bigdecimal::BigDecimal;
use smt_multiplex::lexer::*;
use smt_multiplex::parser::*;
use smt_multiplex::z3::Z3;
use smt_multiplex::solver::Solver;
use smt_multiplex::uninterpreted_ast::ScriptCommand;

fn main() {
    let f = File::open("predicateExistsTest4.smt2").unwrap();
    let mut reader = ScriptParser::new(BufReader::new(f));

    let mut solver = match Z3::new(Path::new("z3")) {
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
        let res = match command {
            ScriptCommand::DeclareSort(name, arity) => { solver.declare_sort(&name, &arity) }
            ScriptCommand::Assert(t) => { solver.assert(&t) }
            ScriptCommand::CheckSat => { todo!() }
            ScriptCommand::CheckSatAssuming(_) => { todo!() }
            ScriptCommand::DeclareConst(name, sort) => { solver.declare_const(&name, &sort) },
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
        // println!("{}", res);
        match res {
            Ok(x) => println!("Response: {}", x),
            Err(x) => { println!("Error: {}", x); return }
        }
    }

    // if let Some(e) = reader.take_err() {
    //     println!("{}", e);
    // }
}
