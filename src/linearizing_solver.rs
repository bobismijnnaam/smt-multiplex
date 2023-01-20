use num_bigint::BigUint;
use crate::solver::Solver;
use crate::uninterpreted_ast::{Attribute, CheckSatResponse, DatatypeDec, GeneralResponse, GetAssignmentResponse, GetInfoResponse, GetModelResponse, GetOptionResponse, GetProofResponse, GetUnsatAssumptionsResponse, GetUnsatCoreResponse, GetValueResponse, PropLiteral, Response, ScriptCommand, Sort, Term};
use crate::uninterpreted_ast::GeneralFailure::NotImplemented;
use crate::uninterpreted_ast::GeneralResponse::Success;

// Optimization possibility: if we can make the user promise the commands (= args to solver functions) are all immutable, we can make them by reference in cmds. This is cheaper than cloning everything all the time
/* Optimization possibility: pass everything directly to the solver, until push/pop commands start occurring. Then need to start keeping track of command history, and resetting and replaying upon pop commands
   Essentially, this is a solver that stores up all commands, and when it encounters a check-sat it dumps the entire history to the solver for a result.
   Instead, a solver could also be made that sends commands to the solver eagerly, and which resets the solver, and possibly replays the history, only on push/pop boundaries.
   E.g. if the user never calls push you might as well dump everything to the solver eagerly. The same holds if the user only push+pops once.
 */
pub struct LinearizingSolver<S: Solver> {
    solver: S,
    cmds: Vec<Vec<ScriptCommand>>
}

pub fn applyGeneral<S: Solver>(s: &mut S, cmd: &ScriptCommand) -> Response<GeneralResponse> {
    match cmd {
        ScriptCommand::Assert(t) => s.assert(t),
        ScriptCommand::DeclareConst(name, sort) => s.declare_const(name, sort),
        ScriptCommand::DeclareFun { name, sort, args } => s.declare_fun(name, sort, args),
        ScriptCommand::DefineSort { name, args, def } => s.define_sort(name, args, def),
        ScriptCommand::DeclareSort(name, arity) => s.declare_sort(name, arity),
        ScriptCommand::SetOption(attribute) => s.set_option(attribute),
        _ => panic!("Expected general command, got: {}", cmd)
    }
}

impl <S: Solver> LinearizingSolver<S> {
    pub fn new(solver: S) -> LinearizingSolver<S> {
        LinearizingSolver {
            solver,
            cmds: vec![vec![]]
        }
    }

    pub fn record(&mut self, cmd: ScriptCommand) -> Response<GeneralResponse> {
        self.cmds.last_mut().unwrap().push(cmd);
        Ok(Success)
    }
}

impl <S: Solver> Solver for LinearizingSolver<S> {
    fn set_logic(&mut self, logic: String) -> Response<GeneralResponse> {
        self.record(ScriptCommand::SetLogic(logic));
        Ok(Success)
    }

    fn reset(&mut self) -> Response<GeneralResponse> {
        // Optimization possibility: here all the inner vecs are also thrown away. If we switch to some cursor approach we could retain them.
        self.cmds.clear();
        Ok(Success)
    }
    fn reset_assertions(&mut self) -> Response<GeneralResponse> {
        // TODO: Need to be intelligent here: only remove assertions, not global declarations, unless :global-declarations is set. Probably requires separate storage of declarations
        Err(NotImplemented)
    }
    fn exit(&mut self) -> Response<GeneralResponse> {
        self.solver.exit()
    }

    fn push(&mut self) -> Response<GeneralResponse> {
        self.cmds.push(vec![]);
        Ok(Success)
    }
    fn pop(&mut self) -> Response<GeneralResponse> {
        self.cmds.pop();
        Ok(Success)
    }

    fn declare_sort(&mut self, name: &String, arity: &BigUint) -> Response<GeneralResponse> {
        self.record(ScriptCommand::DeclareSort(name.clone(), arity.clone()))
    }
    fn define_sort(&mut self, name: &String, args: &Vec<String>, def: &Sort) -> Response<GeneralResponse> {
        self.record(ScriptCommand::DefineSort { name: name.clone(), args: args.clone(), def: def.clone() })
    }
    fn declare_fun(&mut self, name: &String, sort: &Sort, args: &Vec<Sort>) -> Response<GeneralResponse> {
        self.record(ScriptCommand::DeclareFun { name: name.clone(), sort: sort.clone(), args: args.clone() })
    }
    fn declare_const(&mut self, name: &String, sort: &Sort) -> Response<GeneralResponse> {
        self.record(ScriptCommand::DeclareConst(name.clone(), sort.clone()))
    }
    fn declare_datatypes(&mut self, datatypes: &Vec<(String, BigUint, DatatypeDec)>) -> Response<GeneralResponse> {
        // TODO: Don't understand this one
        Err(NotImplemented)
    }

    fn assert(&mut self, t: &Term) -> Response<GeneralResponse> {
        self.record(ScriptCommand::Assert(t.clone()))
    }

    fn check_sat(&mut self, assuming: &Vec<PropLiteral>) -> Response<CheckSatResponse> {
        assert!(assuming.len() == 0);

        for section in &self.cmds {
            for cmd in section {
                applyGeneral(&mut self.solver, &cmd)?;
            }
        }
        let res = self.solver.check_sat(assuming)?;
        // Optimizing opportunity: maybe use reset_assertions here?
        self.solver.reset()?;
        Ok(res)
    }
    fn get_value(&mut self, terms: &Vec<Term>) -> Response<GetValueResponse> {
        Err(NotImplemented)
    }
    fn get_assignment(&mut self) -> Response<GetAssignmentResponse> {
        Err(NotImplemented)
    }
    fn get_model(&mut self) -> Response<GetModelResponse> {
        Err(NotImplemented)
    }
    fn get_unsat_assumptions(&mut self) -> Response<GetUnsatAssumptionsResponse> {
        Err(NotImplemented)
    }
    fn get_proof(&mut self) -> Response<GetProofResponse> {
        Err(NotImplemented)
    }
    fn get_unsat_core(&mut self) -> Response<GetUnsatCoreResponse> {
        Err(NotImplemented)
    }

    fn get_info(&mut self, key: &String) -> Response<GetInfoResponse> {
        Err(NotImplemented)
    }
    fn get_option(&mut self, key: &String) -> Response<GetOptionResponse> {
        Err(NotImplemented)
    }
    fn set_option(&mut self, opt: &Attribute) -> Response<GeneralResponse> {
        self.record(ScriptCommand::SetOption(opt.clone()))
    }

    fn set_info(&mut self, info: &Attribute) -> Response<GeneralResponse> {
        self.record(ScriptCommand::SetInfo(info.clone()))
    }
}