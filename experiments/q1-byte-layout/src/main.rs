#![forbid(unsafe_code)]

mod arm_f;
mod arm_p;
mod arm_s;
mod checks;
mod generator;
mod hex;
mod report;
mod run;
mod types;

use std::path::Path;
use std::process::ExitCode;

const USAGE: &str = "usage: borsuk-q1 check|hex|smoke|report DIR|run run|repeat NN DIR";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let args: Vec<&str> = args.iter().map(String::as_str).collect();
    let result = match args.as_slice() {
        ["check"] => checks::check(&generator::corpus()).map(|lines| {
            for line in lines {
                println!("{line}");
            }
        }),
        ["hex"] => hex::hex(&generator::corpus()),
        ["smoke"] => run::smoke(&generator::corpus()),
        ["report", dir] => report::report(&generator::corpus(), Path::new(dir)),
        ["run", series @ ("run" | "repeat"), nn, dir] => match nn.parse::<u32>() {
            Ok(n) if nn.len() == 2 && (1..=if *series == "run" { 12 } else { 24 }).contains(&n) => {
                run::run(&generator::corpus(), series, n, Path::new(dir))
            }
            _ => {
                eprintln!("{USAGE}");
                return ExitCode::from(2);
            }
        },
        _ => {
            eprintln!("{USAGE}");
            return ExitCode::from(2);
        }
    };
    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("error: {e}");
            ExitCode::FAILURE
        }
    }
}
