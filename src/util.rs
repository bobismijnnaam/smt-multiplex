use std::fs::File;
use std::io::Read;
use std::path::PathBuf;
use crate::args::Args;

/// Either gives back the path and solver args from the args object, or detects a solver + likely required arguments from context
pub fn solver_from_args_or_env_or_exit(args: Args) -> (PathBuf, Vec<String>) {
    match args.solver_path.map(|s| (s, args.solver_args)).or_else(|| detect_solver_from_env()) {
        Some((p, args)) => (p, args),
        None => {
            println!("(error \"no solver path passed as arguments, nor detected automatically\")");
            std::process::exit(1)
        }
    }
}

fn detect_solver_from_env() -> Option<(PathBuf, Vec<String>)> {
     [
        ("z3", vec!["-nw", "-in"]),
        ("cvc5", vec![]),
        ("cvc4", vec![]),
        ("mathsat", vec![]),
        ("minisat", vec![]),
        ("alt-ergo", vec![])
    ].into_iter()
        .map(|(p, args)|
            (PathBuf::from(p),
             args.iter().map(|a| a.to_string()).collect()))
        .find(|(p, _)| {
            if (p.exists() && s.0.is_file()) {
                trace!("{} exists and is a file");
                true
            } else {
                trace!("{} does not exist or is not a file");
                false
            }
        })
}

pub fn reader_from_args(args: &Args) -> Box<dyn Read> {
    match &args.input {
        Some(p) => {
            Box::new(File::open(&p).unwrap())
        }
        None => {
            Box::new(std::io::stdin().lock())
        }
    }
}