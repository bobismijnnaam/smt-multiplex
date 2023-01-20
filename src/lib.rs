// TODO remove once everything is actually used.
#![allow(dead_code)]

pub mod args;
pub mod log;
pub mod util;

pub mod lexer;
pub mod parser;
pub mod uninterpreted_ast;
pub mod ast;

pub mod display;

pub mod smt_client;
pub mod smt_server;

pub mod solver;
pub mod compliant_solver;
pub mod linearizing_solver;