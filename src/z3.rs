use std::{fmt, io};
use std::io::{Read, Stdout, Write};
use std::path::Path;
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};
use bitvec::macros::internal::funty::Fundamental;
use num_bigint::BigUint;
use crate::uninterpreted_ast::Attribute::Pair;
use crate::uninterpreted_ast::{Attribute, AttributeValue, GeneralFailure, GeneralResponse, Response, Sort, SpecConst, Term};
use crate::uninterpreted_ast::GeneralFailure::Error;
use crate::uninterpreted_ast::SExpr::Symbol;
use crate::solver::Solver;
use crate::uninterpreted_ast::GeneralResponse::Success;

// TODO: Probably rename this one to smtlib-compliant solver...
pub struct Z3 {
    proc: Child,
    stdout_buf: String,
}

impl Z3 {
    pub fn new(p: &Path) -> Result<Z3, String> {
        let proc = match Command::new(p)
            .arg("-in") // Read from stdin
            .arg("-nw") // No warnings
            .stdout(Stdio::piped())
            .stdin(Stdio::piped())
            .spawn() {
            Ok(child) => child,
            Err(err) => return Err(err.to_string())
        };

        let mut z3 = Z3 {
            proc,
            stdout_buf: "".into()
        };

        println!("started z3");

        match z3.set_option(&Pair("print-success".into(), AttributeValue::Symbol("true".into()))) {
            Ok(Success) => {
                println!("Received success");
                Ok(z3)
            },
            Err(err) => Err(err.to_string())
        }
    }

    fn stdin_write_fmt(&mut self, fmt: fmt::Arguments<'_>) -> Response<()> {
        match &mut self.proc.stdin {
            None => Err(Error("stdin not found in inner process".into())),
            Some(stdin) => {
                match stdin.write_fmt(fmt) {
                    Ok(_) => Ok(()),
                    Err(err) => Err(Error(err.to_string()))
                }
            }
        }
    }

    fn stdout_buf_trim(&mut self) {
        while (self.stdout_buf.len() > 0 && self.stdout_buf.chars().next().unwrap().is_whitespace()) {
            self.stdout_buf.remove(0);
        }
    }

    fn ensure_stdout_buf_size(&mut self, size: usize) -> Response<()> {
        self.stdout_buf_trim();

        while (self.stdout_buf.len() < size) {
            let mut read: [u8; 10] = [0; 10]; // Would like this to be flexible, or, just read as much as possible...?

            let stdout = match &mut self.proc.stdout {
                None => return Err(Error("stdout not found in inner proc".into())),
                Some(stdout) => stdout
            };

            let n = match stdout.read(&mut read) {
                Ok(n) => n,
                Err(err) => return Err(Error(err.to_string()))
            };

            for c in read.iter().take(n) {
                match c.as_char() {
                    None => return Err(Error("read byte which is not a char".into())),
                    Some(c) => self.stdout_buf.push(c)
                }
            }

            self.stdout_buf_trim();
        }

        Ok(())
    }

    fn expect_success(&mut self) -> Response<GeneralResponse> {
        self.ensure_stdout_buf_size("success".len());
        if (self.stdout_buf.starts_with("success")) {
            self.stdout_buf.replace_range(0.."success".len(), "");
            Ok(Success)
        } else {
            Err(Error(format!("expected success, got: {}", &self.stdout_buf)))
        }
    }
}

impl Solver for Z3 {
    fn set_option(&mut self, opt: &Attribute) -> Response<GeneralResponse> {
        println!("; writing to z3: (set-option {})", opt);
        self.stdin_write_fmt(format_args!("(set-option {})\n", opt))?;
        self.expect_success()
    }

    fn declare_sort(&mut self, name: &String, arity: &BigUint) -> Response<GeneralResponse> {
        println!("; writing to z3: (declare-sort {} {})", name, arity);
        self.stdin_write_fmt(format_args!("(declare-sort {} {})\n", name, arity))?;
        self.expect_success()
    }

    fn declare_const(&mut self, name: &String, sort: &Sort) -> Response<GeneralResponse> {
        self.stdin_write_fmt(format_args!("(declare-const {} {})\n", name, sort))?;
        self.expect_success()
    }

    fn push(&mut self) -> Response<GeneralResponse> {
        self.stdin_write_fmt(format_args!("(push)\n"))?;
        self.expect_success()
    }

    fn assert(&mut self, t: &Term) -> Response<GeneralResponse> {
        self.stdin_write_fmt(format_args!("(assert {})\n", t))?;
        self.expect_success()
    }
}
