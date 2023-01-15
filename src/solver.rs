use num_bigint::BigUint;
use crate::uninterpreted_ast::*;
use crate::uninterpreted_ast::GeneralFailure::NotImplemented;

trait Solver {
    fn set_logic(&mut self, logic: String) -> Response<GeneralResponse> {
        Err(NotImplemented)
    }

    fn reset(&mut self) -> Response<GeneralResponse> {
        Err(NotImplemented)
    }
    fn reset_assertions(&mut self) -> Response<GeneralResponse> {
        Err(NotImplemented)
    }
    fn exit(&mut self) -> Response<GeneralResponse> {
        Err(NotImplemented)
    }

    fn push(&mut self) -> Response<GeneralResponse> {
        Err(NotImplemented)
    }
    fn pop(&mut self) -> Response<GeneralResponse> {
        Err(NotImplemented)
    }

    fn declare_sort(&mut self, name: &String, arity: &BigUint) -> Response<GeneralResponse> {
        Err(NotImplemented)
    }
    fn define_sort(&mut self, name: &String, args: &Vec<String>, def: &Sort) -> Response<GeneralResponse> {
        Err(NotImplemented)
    }
    fn declare_fun(&mut self, name: &String, sort: &Sort, args: &Vec<Sort>) -> Response<GeneralResponse> {
        Err(NotImplemented)
    }
    fn declare_datatypes(&mut self, datatypes: &Vec<(String, BigUint, DatatypeDec)>) -> Response<GeneralResponse> {
        Err(NotImplemented)
    }

    fn assert(&mut self, t: &Term) -> Response<GeneralResponse> {
        Err(NotImplemented)
    }

    fn check_sat(&mut self, assuming: &Vec<PropLiteral>) -> Response<CheckSatResponse> {
        Err(NotImplemented)
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
    fn set_option(&mut self, opt: &Attribute) -> Response<()> {
        Err(NotImplemented)
    }

    fn set_info(&mut self, info: &Attribute) -> Response<()>;
}

