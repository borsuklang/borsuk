use crate::arm_f::ArmF;
use crate::arm_p::ArmP;
use crate::arm_s::ArmS;
use crate::types::{Arm, Corpus, InputKind, KINDS, Log, LogInput, N, State, admit, input, step};

struct Outcome {
    checksum: u64,
    log: Log,
    state: State,
}

fn round_trip<A: Arm>(corpus: &Corpus, arm: &A) -> Result<String, String> {
    let mut n = 0;
    for kind in KINDS {
        for i in 0..N {
            let value = input(corpus, kind, i);
            let frame = A::encode(&value)
                .ok_or_else(|| format!("arm {}: {} {i} has no frame", A::NAME, kind.name()))?;
            if arm.frame(kind, i) != frame.as_slice() {
                return Err(format!(
                    "arm {}: the wire frame of {} {i} differs from its encoding",
                    A::NAME,
                    kind.name()
                ));
            }
            if A::decode(kind, &frame) != Some(value) {
                return Err(format!(
                    "arm {}: the round trip of {} {i} fails",
                    A::NAME,
                    kind.name()
                ));
            }
            n += 1;
        }
    }
    Ok(format!("round trip {}: {n} values pass", A::NAME))
}

fn outcome<A: Arm>(arm: &mut A, kind: InputKind, i: usize) -> Result<Outcome, String> {
    let checksum = step(arm, kind, i);
    let log = A::decode_log(kind, arm.log()).ok_or_else(|| {
        format!(
            "arm {}: the log record of {} {i} does not decode",
            A::NAME,
            kind.name()
        )
    })?;
    let state = arm.state(kind.group(), i);
    Ok(Outcome {
        checksum,
        log,
        state,
    })
}

fn differ(kind: InputKind, i: usize, part: &str, other: &str) -> String {
    format!(
        "{} {i}: the {part} of arm F and arm {other} differ",
        kind.name()
    )
}

fn same(kind: InputKind, i: usize, a: &Outcome, b: &Outcome, other: &str) -> Result<(), String> {
    if a.checksum != b.checksum {
        return Err(differ(kind, i, "checksums", other));
    }
    if a.log.input != b.log.input {
        return Err(differ(kind, i, "decoded input parts", other));
    }
    if a.state != b.state {
        return Err(differ(kind, i, "decoded new states", other));
    }
    if a.log.change != b.log.change {
        return Err(differ(kind, i, "decoded changes", other));
    }
    if a.log.outputs != b.log.outputs {
        return Err(differ(kind, i, "decoded outputs", other));
    }
    if a.log.decision != b.log.decision {
        return Err(differ(kind, i, "decoded decisions", other));
    }
    Ok(())
}

fn compare(corpus: &Corpus, f: &mut ArmF, p: &mut ArmP, s: &mut ArmS) -> Result<String, String> {
    f.reset();
    p.reset();
    s.reset();
    let mut n = 0;
    for kind in KINDS {
        for i in 0..N {
            let a = outcome(f, kind, i)?;
            let b = outcome(p, kind, i)?;
            let c = outcome(s, kind, i)?;
            same(kind, i, &a, &b, "P")?;
            same(kind, i, &a, &c, "S")?;
            if kind == InputKind::Person
                && a.log.input != LogInput::Person(Box::new(admit(&corpus.pad, &corpus.person[i])))
            {
                return Err(format!(
                    "PersonIn {i}: a slot of the input part differs from its sealed slot"
                ));
            }
            n += 1;
        }
    }
    Ok(format!("comparison of arms F, P and S: {n} steps pass"))
}

fn refused<A: Arm>(corpus: &Corpus, arm: &mut A) -> Result<Vec<String>, String> {
    let frames = A::refused(corpus);
    let mut lines = Vec::with_capacity(frames.len() + 1);
    for r in &frames {
        if arm.admits(r.kind, &r.frame) {
            return Err(format!(
                "arm {}: admit accepts the refused frame of {} with the cause {}",
                A::NAME,
                r.kind.name(),
                r.cause
            ));
        }
        lines.push(format!(
            "refused {} {}: {}",
            A::NAME,
            r.kind.name(),
            r.cause
        ));
    }
    lines.push(format!(
        "refused frames {}: admit refuses {} frames",
        A::NAME,
        frames.len()
    ));
    Ok(lines)
}

pub fn check(corpus: &Corpus) -> Result<Vec<String>, String> {
    let mut f = ArmF::new(corpus);
    let mut p = ArmP::new(corpus);
    let mut s = ArmS::new(corpus);
    let mut lines = vec![
        round_trip(corpus, &f)?,
        round_trip(corpus, &p)?,
        round_trip(corpus, &s)?,
    ];
    lines.push(compare(corpus, &mut f, &mut p, &mut s)?);
    lines.extend(refused(corpus, &mut f)?);
    lines.extend(refused(corpus, &mut p)?);
    lines.extend(refused(corpus, &mut s)?);
    Ok(lines)
}
