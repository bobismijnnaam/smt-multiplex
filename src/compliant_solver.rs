use std::{fmt, io};
use std::io::{Read, Stdout, Write};
use std::path::Path;
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};
use bigdecimal::num_traits::AsPrimitive;
use bitvec::macros::internal::funty::Fundamental;
use log::trace;
use num_bigint::BigUint;
use crate::uninterpreted_ast::Attribute::Pair;
use crate::uninterpreted_ast::{Attribute, AttributeValue, CheckSatResponse, GeneralFailure, GeneralResponse, PropLiteral, Response, Sort, SpecConst, Term};
use crate::uninterpreted_ast::GeneralFailure::Error;
use crate::uninterpreted_ast::SExpr::Symbol;
use crate::solver::Solver;
use crate::uninterpreted_ast::GeneralResponse::Success;

/*
Implements support and constructors compliant solvers (currently only z3)
 */
pub struct CompliantSolver {
    proc: Child,
    buf: Option<char>,
}

impl CompliantSolver {
    // Currently only tested with z3, but should probably make this generic over some enum of supported solvers
    pub fn new(p: &Path, args: Vec<String>) -> Result<CompliantSolver, String> {
        let proc = Command::new(p)
            .args(args)
            .stdout(Stdio::piped())
            .stdin(Stdio::piped())
            .spawn();

        let mut proc = match proc {
            Ok(child) => child,
            Err(err) => return Err(err.to_string())
        };

        let mut z3 = CompliantSolver {
            proc,
            buf: None
        };

        trace!("started {:?}", p);

        match z3.set_option(&Pair("print-success".into(), AttributeValue::Symbol("true".into()))) {
            Ok(Success) => Ok(z3),
            Err(err) => Err(err.to_string())
        }
    }

    fn stdin_write_fmt(&mut self, fmt: fmt::Arguments<'_>) -> Response<()> {
        match &mut self.proc.stdin {
            None => Err(Error("stdin not found in inner process".into())),
            Some(stdin) => {
                trace!("writing to solver: {}", fmt.to_string().trim());
                match stdin.write_fmt(fmt) {
                    Ok(_) => Ok(()),
                    Err(err) => Err(Error(err.to_string()))
                }
            }
        }
    }

    fn peek(&mut self) -> Response<char> {
        match self.buf {
            Some(c) => { return Ok(c) }
            None => { }
        };
        let stdout = match &mut self.proc.stdout {
            None => { return Err(Error("no stdout in proc".into())) }
            Some(stdout) => stdout
        };
        let mut buffer= [0; 1];
        let someU8 = match stdout.read_exact(&mut buffer) {
            Ok(_) => buffer[0],
            Err(err) => return Err(Error(format!("could not read byte from proc stdout: {}", err)))
        };
        let c = match someU8.as_char() {
            Some(c) => c,
            None => return Err(Error("could not conver byte to char".into()))
        };
        self.buf = Some(c);
        // println!("Fresh read: {}", c);
        Ok(c)
    }

    fn read_line(&mut self) -> Response<String> {
        let mut string_buf: String = "".into();
        while self.peek()? != '\n' {
            string_buf.push(self.consume()?)
        }
        Ok(string_buf)
    }

    fn expect(&mut self, c: char) -> Response<()> {
        match self.peek()? {
            d if c == d => {
                self.consume()?;
                Ok(())
            },
            _ => {
                let line = self.read_line()?;
                Err(Error(format!("expected {}, got {}", c, line)))
            }
        }
    }

    fn consume(&mut self) -> Response<char> {
        self.peek()?;
        Ok(self.buf.take().unwrap())
    }

    fn expect_str(&mut self, v: &str) -> Response<()> {
        for c in v.chars() {
            self.expect(c)?
        }
        Ok(())
    }

    fn consume_sat_unsat(&mut self) -> Response<CheckSatResponse> {
        match self.peek()? {
            'u' => {
                self.consume()?;
                self.expect('n')?;
                match self.peek()? {
                    'k' => {
                        self.expect_str("known\n")?;
                        Ok(CheckSatResponse::Unknown)
                    }
                    's' => {
                        self.expect_str("sat\n")?;
                        Ok(CheckSatResponse::Unsat)
                    }
                    _ => {
                        Err(Error(format!("expected 'unsat', 'sat', or 'unknown', got {}", self.read_line()?)))
                    }
                }
            }
            's' => {
                self.expect_str("sat\n")?;
                Ok(CheckSatResponse::Unsat)
            }
            _ => {
                Err(Error(format!("expected 'unsat' or 'sat', got {}", self.read_line()?)))
            }
        }
    }

    fn consume_success(&mut self) -> Response<GeneralResponse> {
        self.expect_str("success\n")?;
        Ok(Success)
    }
}

impl Solver for CompliantSolver {
    fn push(&mut self) -> Response<GeneralResponse> {
        self.stdin_write_fmt(format_args!("(push)\n"))?;
        self.consume_success()
    }

    fn declare_sort(&mut self, name: &String, arity: &BigUint) -> Response<GeneralResponse> {
        self.stdin_write_fmt(format_args!("(declare-sort {} {})\n", name, arity))?;
        self.consume_success()
    }

    fn declare_const(&mut self, name: &String, sort: &Sort) -> Response<GeneralResponse> {
        self.stdin_write_fmt(format_args!("(declare-const {} {})\n", name, sort))?;
        self.consume_success()
    }

    fn assert(&mut self, t: &Term) -> Response<GeneralResponse> {
        self.stdin_write_fmt(format_args!("(assert {})\n", t))?;
        self.consume_success()
    }

    fn check_sat(&mut self, assuming: &Vec<PropLiteral>) -> Response<CheckSatResponse> {
        assert!(assuming.is_empty());
        self.stdin_write_fmt(format_args!("(check-sat)\n"))?;
        self.consume_sat_unsat()
    }

    fn set_option(&mut self, opt: &Attribute) -> Response<GeneralResponse> {
        self.stdin_write_fmt(format_args!("(set-option {})\n", opt))?;
        self.consume_success()
    }

    fn reset(&mut self) -> Response<GeneralResponse> {
        self.stdin_write_fmt(format_args!("(reset)\n"))?;
        self.consume_success()
    }
}
