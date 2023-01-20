use num_bigint::BigUint;
use crate::solver::Solver;
use crate::uninterpreted_ast::{Attribute, CheckSatResponse, DatatypeDec, GeneralResponse, GetAssignmentResponse, GetInfoResponse, GetModelResponse, GetOptionResponse, GetProofResponse, GetUnsatAssumptionsResponse, GetUnsatCoreResponse, GetValueResponse, PropLiteral, Response, Sort, Term};

// struct ForwardingSolver<S: Solver> {
//     solver: S,
// }

// pub trait ForwardingSolver<S: Solver> : Solver {
//     fn solver(&mut self) -> &mut S;
//
//     fn set_logic(&mut self, logic: String) -> Response<GeneralResponse> {
//         self.solver().set_logic(logic)
//     }
//     fn reset(&mut self) -> Response<GeneralResponse> {
//         self.solver().reset()
//     }
//     fn reset_assertions(&mut self) -> Response<GeneralResponse> {
//         self.solver().reset_assertions()
//     }
//     fn exit(&mut self) -> Response<GeneralResponse> {
//         self.solver().exit()
//     }
//
//     fn push(&mut self) -> Response<GeneralResponse> {
//         self.solver().push()
//     }
//     fn pop(&mut self) -> Response<GeneralResponse> {
//         self.solver().pop()
//     }
//
//     fn declare_sort(&mut self, name: &String, arity: &BigUint) -> Response<GeneralResponse> {
//         self.solver().declare_sort(name, arity)
//     }
//     fn define_sort(&mut self, name: &String, args: &Vec<String>, def: &Sort) -> Response<GeneralResponse> {
//         self.solver().define_sort(name, args, def)
//     }
//     fn declare_fun(&mut self, name: &String, sort: &Sort, args: &Vec<Sort>) -> Response<GeneralResponse> {
//         self.solver().declare_fun(name, sort, args)
//     }
//     fn declare_const(&mut self, name: &String, sort: &Sort) -> Response<GeneralResponse> {
//         self.solver().declare_const(name, sort)
//     }
//     fn declare_datatypes(&mut self, datatypes: &Vec<(String, BigUint, DatatypeDec)>) -> Response<GeneralResponse> {
//         self.solver().declare_datatypes(datatypes)
//     }
//
//     fn assert(&mut self, t: &Term) -> Response<GeneralResponse> {
//         self.solver().assert(t)
//     }
//
//     fn check_sat(&mut self, assuming: &Vec<PropLiteral>) -> Response<CheckSatResponse> {
//         self.solver().check_sat(assuming)
//     }
//     fn get_value(&mut self, terms: &Vec<Term>) -> Response<GetValueResponse> {
//         self.solver().get_value(terms)
//     }
//     fn get_assignment(&mut self) -> Response<GetAssignmentResponse> {
//         self.solver().get_assignment()
//     }
//     fn get_model(&mut self) -> Response<GetModelResponse> {
//         self.solver().get_model()
//     }
//     fn get_unsat_assumptions(&mut self) -> Response<GetUnsatAssumptionsResponse> {
//         self.solver().get_unsat_assumptions()
//     }
//     fn get_proof(&mut self) -> Response<GetProofResponse> {
//         self.solver().get_proof()
//     }
//     fn get_unsat_core(&mut self) -> Response<GetUnsatCoreResponse> {
//         self.solver().get_unsat_core()
//     }
//
//     fn get_info(&mut self, key: &String) -> Response<GetInfoResponse> {
//         self.solver().get_info(key)
//     }
//     fn get_option(&mut self, key: &String) -> Response<GetOptionResponse> {
//         self.solver().get_option(key)
//     }
//     fn set_option(&mut self, opt: &Attribute) -> Response<GeneralResponse> {
//         self.solver().set_option(opt)
//     }
//
//     fn set_info(&mut self, info: &Attribute) -> Response<GeneralResponse> {
//         self.solver().set_info(info)
//     }
// }

// pub trait ForwardingSolver {
//     type UnderlyingSolver: Solver;
//
//     fn solver(&mut self) -> &mut Self::UnderlyingSolver;
// }
//
// impl <T: ForwardingSolver> Solver for T {
//     fn set_logic(&mut self, logic: String) -> Response<GeneralResponse> {
//         self.solver().set_logic(logic)
//     }
//     fn reset(&mut self) -> Response<GeneralResponse> {
//         self.solver().reset()
//     }
//     fn reset_assertions(&mut self) -> Response<GeneralResponse> {
//         println!("In ForwardingSolver");
//         self.solver().reset_assertions()
//     }
//     fn exit(&mut self) -> Response<GeneralResponse> {
//         self.solver().exit()
//     }
//
//     fn push(&mut self) -> Response<GeneralResponse> {
//         self.solver().push()
//     }
//     fn pop(&mut self) -> Response<GeneralResponse> {
//         self.solver().pop()
//     }
//
//     fn declare_sort(&mut self, name: &String, arity: &BigUint) -> Response<GeneralResponse> {
//         self.solver().declare_sort(name, arity)
//     }
//     fn define_sort(&mut self, name: &String, args: &Vec<String>, def: &Sort) -> Response<GeneralResponse> {
//         self.solver().define_sort(name, args, def)
//     }
//     fn declare_fun(&mut self, name: &String, sort: &Sort, args: &Vec<Sort>) -> Response<GeneralResponse> {
//         self.solver().declare_fun(name, sort, args)
//     }
//     fn declare_const(&mut self, name: &String, sort: &Sort) -> Response<GeneralResponse> {
//         self.solver().declare_const(name, sort)
//     }
//     fn declare_datatypes(&mut self, datatypes: &Vec<(String, BigUint, DatatypeDec)>) -> Response<GeneralResponse> {
//         self.solver().declare_datatypes(datatypes)
//     }
//
//     fn assert(&mut self, t: &Term) -> Response<GeneralResponse> {
//         self.solver().assert(t)
//     }
//
//     fn check_sat(&mut self, assuming: &Vec<PropLiteral>) -> Response<CheckSatResponse> {
//         self.solver().check_sat(assuming)
//     }
//     fn get_value(&mut self, terms: &Vec<Term>) -> Response<GetValueResponse> {
//         self.solver().get_value(terms)
//     }
//     fn get_assignment(&mut self) -> Response<GetAssignmentResponse> {
//         self.solver().get_assignment()
//     }
//     fn get_model(&mut self) -> Response<GetModelResponse> {
//         self.solver().get_model()
//     }
//     fn get_unsat_assumptions(&mut self) -> Response<GetUnsatAssumptionsResponse> {
//         self.solver().get_unsat_assumptions()
//     }
//     fn get_proof(&mut self) -> Response<GetProofResponse> {
//         self.solver().get_proof()
//     }
//     fn get_unsat_core(&mut self) -> Response<GetUnsatCoreResponse> {
//         self.solver().get_unsat_core()
//     }
//
//     fn get_info(&mut self, key: &String) -> Response<GetInfoResponse> {
//         self.solver().get_info(key)
//     }
//     fn get_option(&mut self, key: &String) -> Response<GetOptionResponse> {
//         self.solver().get_option(key)
//     }
//     fn set_option(&mut self, opt: &Attribute) -> Response<GeneralResponse> {
//         self.solver().set_option(opt)
//     }
//
//     fn set_info(&mut self, info: &Attribute) -> Response<GeneralResponse> {
//         self.solver().set_info(info)
//     }
// }
