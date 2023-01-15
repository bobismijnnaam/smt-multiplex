use std::io::{Read, Write};
use num_bigint::BigUint;
use crate::{ScriptParser, UnrecoverableParseFailure};
use crate::uninterpreted_ast::*;

struct SmtServer<R: Read, W: Write, S: Solver> {
    reader: ScriptParser<R>,
    writer: W,
    solver: S,

    print_success: bool,
}

macro_rules! success {
    ($this: expr, $res: expr) => {
        if($this.print_success || $res.is_err()) {
            result!($this, $res.map(|_| "success"))
        } else {
            Ok(())
        }
    }
}

macro_rules! result {
    ($this: expr, $res: expr) => {
        match $res {
            Ok(res) => write!($this.writer, "{}\n", res),
            Err(res) => write!($this.writer, "{}\n", res),
        }
    }
}

impl<R: Read, W: Write, S: Solver> SmtServer<R, W, S> {
    pub fn new(read: R, write: W, solver: S) -> Self {
        Self { reader: ScriptParser::new(read), writer: write, solver, print_success: true }
    }

    pub fn run(&mut self) -> Option<UnrecoverableParseFailure> {
        for command in &mut self.reader {
            // Since we can't say Response<() union dyn Display>, some generics via macros :)
            // success! print success, or the error for Response<()>
            // result! flatly prints the Ok / Err case of Response<_ : Display>
            let result = match command {
                ScriptCommand::Assert(term) => success!(self, self.solver.assert(&term)),
                ScriptCommand::CheckSat => result!(self, self.solver.check_sat(&vec![])),
                ScriptCommand::CheckSatAssuming(lits) => result!(self, self.solver.check_sat(&lits)),
                ScriptCommand::DeclareConst(_, _) => todo!(),
                ScriptCommand::DeclareDatatype(_, _) => todo!(),
                ScriptCommand::DeclareDatatypes(_, _) => todo!(),
                ScriptCommand::DeclareFun { .. } => todo!(),
                ScriptCommand::DeclareSort(_, _) => todo!(),
                ScriptCommand::DefineConst(_, _, _) => todo!(),
                ScriptCommand::DefineFun(_) => todo!(),
                ScriptCommand::DefineFunRec(_) => todo!(),
                ScriptCommand::DefineFunsRec(_, _) => todo!(),
                ScriptCommand::DefineSort { .. } => todo!(),
                ScriptCommand::Echo(_) => todo!(),
                ScriptCommand::Exit => todo!(),
                ScriptCommand::GetAssertions => todo!(),
                ScriptCommand::GetAssignment => todo!(),
                ScriptCommand::GetInfo(_) => todo!(),
                ScriptCommand::GetModel => todo!(),
                ScriptCommand::GetOption(_) => todo!(),
                ScriptCommand::GetProof => todo!(),
                ScriptCommand::GetUnsatAssumptions => todo!(),
                ScriptCommand::GetUnsatCore => todo!(),
                ScriptCommand::GetValue(_) => todo!(),
                ScriptCommand::Pop(_) => todo!(),
                ScriptCommand::Push(_) => todo!(),
                ScriptCommand::Reset => todo!(),
                ScriptCommand::ResetAssertions => todo!(),
                ScriptCommand::SetInfo(_) => todo!(),
                ScriptCommand::SetLogic(_) => todo!(),
                ScriptCommand::SetOption(_) => todo!(),
            };
        }

        self.reader.take_err()
    }
}