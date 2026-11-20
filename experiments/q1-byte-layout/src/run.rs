use std::fs::OpenOptions;
use std::io::Write;
use std::path::Path;
use std::time::{Duration, Instant};

use crate::arm_f::ArmF;
use crate::arm_p::ArmP;
use crate::arm_s::ArmS;
use crate::types::{Arm, CSV_HEADER, Corpus, GROUPS, KINDS, N, ROTATIONS, Row};

struct Limits {
    values: usize,
    warm_passes: u64,
    warm_time: Duration,
    passes: u64,
    time: Duration,
}

const TIMED: Limits = Limits {
    values: N,
    warm_passes: 3,
    warm_time: Duration::from_secs(1),
    passes: 30,
    time: Duration::from_secs(1),
};

const SMOKE: Limits = Limits {
    values: 10,
    warm_passes: 0,
    warm_time: Duration::ZERO,
    passes: 1,
    time: Duration::ZERO,
};

struct Totals {
    passes: u64,
    time: [Duration; 4],
}

fn pass<A: Arm>(arm: &mut A, n: usize) -> [Duration; 4] {
    arm.reset();
    let start = Instant::now();
    for i in 0..n {
        arm.step_hold(i);
    }
    let hold = start.elapsed();
    let start = Instant::now();
    for i in 0..n {
        arm.step_confirm(i);
    }
    let confirm = start.elapsed();
    let start = Instant::now();
    for i in 0..n {
        arm.step_wide(i);
    }
    let wide = start.elapsed();
    let start = Instant::now();
    for i in 0..n {
        arm.step_varied(i);
    }
    let varied = start.elapsed();
    let start = Instant::now();
    for i in 0..n {
        arm.step_person(i);
    }
    let personal = start.elapsed();
    [hold + confirm, wide, varied, personal]
}

fn measure<A: Arm>(arm: &mut A, limits: &Limits) -> Totals {
    let start = Instant::now();
    let mut warm = 0;
    while warm < limits.warm_passes || start.elapsed() < limits.warm_time {
        pass(arm, limits.values);
        warm += 1;
    }
    let mut totals = Totals {
        passes: 0,
        time: [Duration::ZERO; 4],
    };
    while totals.passes < limits.passes || totals.time.iter().any(|t| *t < limits.time) {
        let time = pass(arm, limits.values);
        totals.passes += 1;
        for (sum, t) in totals.time.iter_mut().zip(time) {
            *sum += t;
        }
    }
    totals
}

fn rows<A: Arm>(arm: &mut A, nn: u32, position: u32, limits: &Limits) -> Result<Vec<Row>, String> {
    let totals = measure(arm, limits);
    GROUPS
        .iter()
        .zip(totals.time)
        .map(|(group, time)| {
            let kinds = KINDS.iter().filter(|k| k.group() == *group).count();
            let nanos = u64::try_from(time.as_nanos()).map_err(|_| {
                format!(
                    "arm {}: the time of the group {} is above the u64 range",
                    A::NAME,
                    group.name()
                )
            })?;
            Ok(Row {
                run: nn,
                position,
                arm: A::NAME.to_string(),
                group: group.name().to_string(),
                passes: totals.passes,
                steps: totals.passes * (limits.values * kinds) as u64,
                nanos,
            })
        })
        .collect()
}

fn write_run(
    corpus: &Corpus,
    series: &str,
    nn: u32,
    dir: &Path,
    limits: &Limits,
) -> Result<(), String> {
    if !dir.is_dir() {
        return Err(format!("{} is not a directory", dir.display()));
    }
    let path = dir.join(format!("{series}-{nn:02}.csv"));
    match path.try_exists() {
        Ok(false) => {}
        Ok(true) => {
            return Err(format!(
                "{} exists: measurement data is never edited",
                path.display()
            ));
        }
        Err(e) => return Err(format!("cannot examine {}: {e}", path.display())),
    }
    let mut f = ArmF::new(corpus);
    let mut p = ArmP::new(corpus);
    let mut s = ArmS::new(corpus);
    let mut all = Vec::new();
    for (position, name) in (1..).zip(ROTATIONS[((nn - 1) % 3) as usize]) {
        all.extend(match name {
            n if n == ArmF::NAME => rows(&mut f, nn, position, limits),
            n if n == ArmP::NAME => rows(&mut p, nn, position, limits),
            n if n == ArmS::NAME => rows(&mut s, nn, position, limits),
            n => Err(format!("the rotation names the unknown arm {n}")),
        }?);
    }
    let text: String = std::iter::once(format!("{CSV_HEADER}\n"))
        .chain(all.iter().map(|r| {
            format!(
                "{},{},{},{},{},{},{}\n",
                r.run, r.position, r.arm, r.group, r.passes, r.steps, r.nanos
            )
        }))
        .collect();
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&path)
        .map_err(|e| format!("cannot make {}: {e}", path.display()))?;
    file.write_all(text.as_bytes())
        .map_err(|e| format!("cannot write {}: {e}", path.display()))
}

pub fn run(corpus: &Corpus, series: &str, nn: u32, dir: &Path) -> Result<(), String> {
    crate::checks::check(corpus)?;
    write_run(corpus, series, nn, dir, &TIMED)
}

fn smoke_runs(corpus: &Corpus, dir: &Path) -> Result<(), String> {
    for nn in 1..=12 {
        write_run(corpus, "run", nn, dir, &SMOKE)?;
    }
    for nn in 1..=24 {
        write_run(corpus, "repeat", nn, dir, &SMOKE)?;
    }
    crate::report::text(corpus, dir)?;
    Ok(())
}

pub fn smoke(corpus: &Corpus) -> Result<(), String> {
    crate::checks::check(corpus)?;
    let dir = std::env::temp_dir().join(format!("borsuk-q1-smoke-{}", std::process::id()));
    std::fs::create_dir(&dir)
        .map_err(|e| format!("cannot make the directory {}: {e}", dir.display()))?;
    let result = smoke_runs(corpus, &dir);
    let removed = std::fs::remove_dir_all(&dir)
        .map_err(|e| format!("cannot remove the directory {}: {e}", dir.display()));
    result.and(removed)?;
    println!("smoke ok");
    Ok(())
}
