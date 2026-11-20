use std::collections::BTreeMap;
use std::path::Path;

use crate::arm_f::ArmF;
use crate::arm_p::ArmP;
use crate::arm_s::ArmS;
use crate::types::{ARMS, Arm, CSV_HEADER, Corpus, GROUPS, Group, KINDS, N, ROTATIONS, Row, step};

const SERIES: [(&str, usize, f64); 2] = [("run", 12, 2.201), ("repeat", 24, 2.069)];

const BASE: usize = 2;

struct Cells {
    time: [[f64; 4]; 3],
    per_pass: [[f64; 4]; 3],
}

fn sums<A: Arm>(corpus: &Corpus) -> [[u64; 5]; 2] {
    let mut arm = A::new(corpus);
    let mut wire = [0; 5];
    let mut log = [0; 5];
    arm.reset();
    for (k, kind) in KINDS.into_iter().enumerate() {
        for i in 0..N {
            wire[k] += arm.frame(kind, i).len() as u64;
            step(&mut arm, kind, i);
            log[k] += arm.log().len() as u64;
        }
    }
    [wire, log]
}

fn mean(sum: u64, count: usize) -> f64 {
    sum as f64 / count as f64
}

fn group_mean(sums: &[u64; 5], group: Group) -> f64 {
    let (sum, count) = KINDS
        .iter()
        .zip(sums)
        .filter(|(kind, _)| kind.group() == group)
        .fold((0, 0), |(sum, count), (_, s)| (sum + s, count + N));
    mean(sum, count)
}

fn geometric(ratios: &[f64]) -> f64 {
    (ratios.iter().map(|r| r.ln()).sum::<f64>() / ratios.len() as f64).exp()
}

fn arithmetic(ratios: &[f64]) -> f64 {
    ratios.iter().sum::<f64>() / ratios.len() as f64
}

fn worst(ratios: &[f64; 4]) -> &'static str {
    let w = (0..ratios.len()).fold(0, |w, g| if ratios[g] > ratios[w] { g } else { w });
    GROUPS[w].name()
}

fn byte_lines(lines: &mut Vec<String>, label: &str, sums: &[[u64; 5]; 3]) {
    for (arm, s) in ARMS.iter().zip(sums) {
        for group in GROUPS {
            lines.push(format!(
                "{label} {arm} mean {}: {:.2}",
                group.name(),
                group_mean(s, group)
            ));
        }
        for (kind, sum) in KINDS.iter().zip(s) {
            lines.push(format!(
                "{label} {arm} mean {}: {:.2}",
                kind.name(),
                mean(*sum, N)
            ));
        }
    }
    let base = &sums[BASE];
    for (arm, s) in ARMS.iter().zip(sums).take(BASE) {
        let ratios = GROUPS.map(|g| group_mean(s, g) / group_mean(base, g));
        for (group, ratio) in GROUPS.iter().zip(ratios) {
            lines.push(format!("{label} {arm} ratio {}: {ratio:.4}", group.name()));
        }
        for (k, kind) in KINDS.iter().enumerate() {
            if kind.group() == Group::Booking {
                lines.push(format!(
                    "{label} {arm} ratio {}: {:.4}",
                    kind.name(),
                    mean(s[k], N) / mean(base[k], N)
                ));
            }
        }
        lines.push(format!(
            "{label} {arm} geometric mean: {:.4}",
            geometric(&ratios)
        ));
        lines.push(format!(
            "{label} {arm} arithmetic mean: {:.4}",
            arithmetic(&ratios)
        ));
        lines.push(format!(
            "{label} {arm} ratio of totals: {:.4}",
            s.iter().sum::<u64>() as f64 / base.iter().sum::<u64>() as f64
        ));
        lines.push(format!("{label} {arm} worst group: {}", worst(&ratios)));
    }
}

fn number(name: &str, series: &str) -> Option<u32> {
    let nn = name
        .strip_prefix(series)?
        .strip_prefix('-')?
        .strip_suffix(".csv")?;
    if nn.len() == 2 && nn.bytes().all(|b| b.is_ascii_digit()) {
        nn.parse().ok()
    } else {
        None
    }
}

fn decimal<T: std::str::FromStr>(text: &str) -> Option<T> {
    if text.is_empty() || !text.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    text.parse().ok()
}

fn row(line: &str) -> Option<(usize, usize, Row)> {
    let fields: Vec<&str> = line.split(',').collect();
    let [run, position, arm, group, passes, steps, nanos] = fields.as_slice() else {
        return None;
    };
    let a = ARMS.iter().position(|x| x == arm)?;
    let g = GROUPS.iter().position(|x| x.name() == *group)?;
    let row = Row {
        run: decimal(run)?,
        position: decimal(position)?,
        arm: arm.to_string(),
        group: group.to_string(),
        passes: decimal(passes)?,
        steps: decimal(steps)?,
        nanos: decimal(nanos)?,
    };
    Some((a, g, row))
}

fn parse(path: &Path, nn: u32) -> Result<Cells, String> {
    let name = path.display();
    let text = std::fs::read_to_string(path).map_err(|e| format!("cannot read {name}: {e}"))?;
    let body = text
        .strip_suffix('\n')
        .ok_or_else(|| format!("{name}: the last line does not end with a newline"))?;
    let mut lines = body.split('\n');
    if lines.next() != Some(CSV_HEADER) {
        return Err(format!("{name}: the header is not {CSV_HEADER}"));
    }
    let rotation = ROTATIONS[((nn - 1) % 3) as usize];
    let mut cells: [[Option<(f64, f64)>; 4]; 3] = [[None; 4]; 3];
    for (number, line) in (2..).zip(lines) {
        let at = |what: String| format!("{name}: line {number}: {what}");
        let (a, g, row) = row(line).ok_or_else(|| at("the row does not parse".to_string()))?;
        if row.run != nn {
            return Err(at(format!("the run value {} is not {nn}", row.run)));
        }
        let place = row
            .position
            .checked_sub(1)
            .and_then(|p| rotation.get(p as usize));
        if place != Some(&row.arm.as_str()) {
            return Err(at(format!(
                "the position {} of arm {} does not follow the rotation {}",
                row.position,
                row.arm,
                rotation.join(" ")
            )));
        }
        if row.steps == 0 || row.passes == 0 {
            return Err(at("a steps or passes value is 0".to_string()));
        }
        if cells[a][g].is_some() {
            return Err(at(format!(
                "a second row for arm {} and group {}",
                row.arm, row.group
            )));
        }
        cells[a][g] = Some((
            row.nanos as f64 / row.steps as f64,
            row.steps as f64 / row.passes as f64,
        ));
    }
    let mut out = Cells {
        time: [[0.0; 4]; 3],
        per_pass: [[0.0; 4]; 3],
    };
    for (a, arm) in ARMS.iter().enumerate() {
        for (g, group) in GROUPS.iter().enumerate() {
            let (time, per_pass) = cells[a][g].ok_or_else(|| {
                format!("{name}: no row for arm {arm} and group {}", group.name())
            })?;
            out.time[a][g] = time;
            out.per_pass[a][g] = per_pass;
        }
    }
    Ok(out)
}

fn series(dir: &Path) -> Result<Vec<Vec<(u32, Cells)>>, String> {
    let unread = |e: std::io::Error| format!("cannot read the directory {}: {e}", dir.display());
    let mut found = [BTreeMap::new(), BTreeMap::new()];
    for entry in std::fs::read_dir(dir).map_err(unread)? {
        let entry = entry.map_err(unread)?;
        let name = entry.file_name();
        for (map, (series, _, _)) in found.iter_mut().zip(SERIES) {
            if let Some(nn) = name.to_str().and_then(|n| number(n, series)) {
                map.insert(nn, entry.path());
            }
        }
    }
    for (map, (series, count, _)) in found.iter().zip(SERIES) {
        if !map.is_empty() && map.len() != count {
            return Err(format!(
                "{} has {} {series} files, and the report needs 0 or {count}",
                dir.display(),
                map.len()
            ));
        }
        if map.keys().zip(1..).any(|(nn, want)| *nn != want) {
            return Err(format!(
                "the {series} files of {} are not {series}-01.csv to {series}-{count:02}.csv",
                dir.display()
            ));
        }
    }
    if found[0].is_empty() && !found[1].is_empty() {
        return Err(format!(
            "{} has repeat files and no run files",
            dir.display()
        ));
    }
    found
        .iter()
        .map(|map| {
            map.iter()
                .map(|(nn, path)| Ok((*nn, parse(path, *nn)?)))
                .collect()
        })
        .collect()
}

fn interval(l: &[f64], q: f64) -> [f64; 3] {
    let n = l.len() as f64;
    let m = l.iter().sum::<f64>() / n;
    let s = (l.iter().map(|x| (x - m) * (x - m)).sum::<f64>() / (n - 1.0)).sqrt();
    let half = q * s / n.sqrt();
    [m.exp(), (m - half).exp(), (m + half).exp()]
}

fn shown([ratio, low, high]: [f64; 3]) -> String {
    format!("{ratio:.4} [{low:.4}, {high:.4}]")
}

fn speed_lines(lines: &mut Vec<String>, series: &str, q: f64, runs: &[(u32, Cells)]) {
    lines.push(format!("{series} speed quantile: {q:.3}"));
    for (a, arm) in ARMS.iter().enumerate() {
        for (g, group) in GROUPS.iter().enumerate() {
            let l: Vec<f64> = runs.iter().map(|(_, c)| c.time[a][g].ln()).collect();
            lines.push(format!(
                "{series} speed {arm} nanos per step {}: {:.2}",
                group.name(),
                (l.iter().sum::<f64>() / l.len() as f64).exp()
            ));
        }
    }
    for (a, arm) in ARMS.iter().enumerate().take(BASE) {
        let logs: Vec<[f64; 4]> = runs
            .iter()
            .map(|(_, c)| std::array::from_fn(|g| (c.time[a][g] / c.time[BASE][g]).ln()))
            .collect();
        let groups: [[f64; 3]; 4] = std::array::from_fn(|g| {
            let l: Vec<f64> = logs.iter().map(|r| r[g]).collect();
            interval(&l, q)
        });
        for (group, result) in GROUPS.iter().zip(groups) {
            lines.push(format!(
                "{series} speed {arm} ratio {}: {}",
                group.name(),
                shown(result)
            ));
        }
        let l: Vec<f64> = logs
            .iter()
            .map(|r| r.iter().sum::<f64>() / r.len() as f64)
            .collect();
        lines.push(format!(
            "{series} speed {arm} geometric mean: {}",
            shown(interval(&l, q))
        ));
        lines.push(format!(
            "{series} speed {arm} worst group: {}",
            worst(&groups.map(|[ratio, _, _]| ratio))
        ));
        for (nn, c) in runs {
            let ratios: [f64; 4] = std::array::from_fn(|g| c.time[a][g] / c.time[BASE][g]);
            let total = |x: usize| (0..4).map(|g| c.time[x][g] * c.per_pass[x][g]).sum::<f64>();
            lines.push(format!(
                "{series} speed {arm} {series}-{nn:02} arithmetic mean: {:.4}",
                arithmetic(&ratios)
            ));
            lines.push(format!(
                "{series} speed {arm} {series}-{nn:02} ratio of totals: {:.4}",
                total(a) / total(BASE)
            ));
        }
    }
}

pub fn text(corpus: &Corpus, dir: &Path) -> Result<String, String> {
    let series = series(dir)?;
    let [fw, fl] = sums::<ArmF>(corpus);
    let [pw, pl] = sums::<ArmP>(corpus);
    let [sw, sl] = sums::<ArmS>(corpus);
    let mut lines = Vec::new();
    byte_lines(&mut lines, "wire bytes", &[fw, pw, sw]);
    byte_lines(&mut lines, "log bytes", &[fl, pl, sl]);
    for ((name, _, q), runs) in SERIES.iter().zip(&series) {
        if !runs.is_empty() {
            speed_lines(&mut lines, name, *q, runs);
        }
    }
    Ok(lines.into_iter().map(|line| line + "\n").collect())
}

pub fn report(corpus: &Corpus, dir: &Path) -> Result<(), String> {
    print!("{}", text(corpus, dir)?);
    Ok(())
}
