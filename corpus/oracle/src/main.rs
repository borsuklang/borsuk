#![forbid(unsafe_code)]

mod decimals;
mod enums;
mod floats;
mod fmt;
mod fp;
mod maths;
mod stream;

use std::path::Path;
use std::process::ExitCode;

fn put(dir: &Path, name: &str, text: &str) -> Result<(), String> {
    let path = dir.join(name);
    std::fs::write(&path, text).map_err(|e| format!("cannot write {}: {e}", path.display()))
}

fn run(dir: &Path) -> Result<(), String> {
    put(dir, "accept/float.brk", &floats::file()?)?;
    put(dir, "accept/math.brk", &maths::file()?)?;
    put(dir, "accept/decimal.brk", &decimals::file()?)?;
    put(dir, "accept/enum256.brk", &enums::enum256())?;
    put(dir, "reject/layout-limit.brk", &enums::layout_limit())?;
    put(
        dir,
        "reject/layout-limit-record.brk",
        &enums::layout_limit_record(),
    )
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let [dir] = args.as_slice() else {
        eprintln!("usage: borsuk-oracle CORPUS_DIR");
        return ExitCode::from(2);
    };
    match run(Path::new(dir)) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("stop: {e}");
            ExitCode::FAILURE
        }
    }
}
