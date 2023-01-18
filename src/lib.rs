// TODO remove once everything is actually used.
#![allow(dead_code)]

pub mod lexer;
pub mod parser;
pub mod uninterpreted_ast;
mod ast;

mod display;

mod smt_client;
pub mod smt_server;

pub mod solver;
pub mod compliant_solver;