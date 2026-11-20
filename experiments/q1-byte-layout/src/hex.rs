use std::iter::once;

use crate::arm_f::ArmF;
use crate::arm_p::ArmP;
use crate::arm_s::ArmS;
use crate::types::{
    Arm, BookedFields, CommandId, Corpus, Flag, Input, InputKind, KINDS, Kind, N, Person, Sealed,
    SlotState, State, StepId, Ticket, Varied, Wide, held, input, person_start, step, varied_start,
    wide_start,
};

const PROPERTIES: [&str; 13] = [
    "none",
    "some",
    "ok",
    "err",
    "Plain",
    "Tagged",
    "Scored",
    "A",
    "B",
    "C",
    "D",
    "negative Int",
    "empty Text",
];

struct Pick {
    kind: InputKind,
    i: usize,
    reasons: Vec<&'static str>,
}

fn generator_order() -> Vec<(InputKind, usize)> {
    let booking = (0..N).flat_map(|i| [(InputKind::Hold, i), (InputKind::Confirm, i)]);
    let others = [InputKind::Wide, InputKind::Varied, InputKind::Person]
        .into_iter()
        .flat_map(|kind| (0..N).map(move |i| (kind, i)));
    booking.chain(others).collect()
}

fn flag_name(flag: Flag) -> &'static str {
    match flag {
        Flag::A => "A",
        Flag::B => "B",
        Flag::C => "C",
        Flag::D => "D",
    }
}

fn properties(value: &Input) -> Vec<&'static str> {
    let mut found = Vec::new();
    let mut ints = Vec::new();
    let mut texts: Vec<&str> = Vec::new();
    match value {
        Input::Hold(h) => ints.push(h.key),
        Input::Confirm(c) => ints.extend([c.key, c.token.key, c.token.life, c.token.seq]),
        Input::Wide(w) => {
            ints.extend(w.wide.ints);
            found.extend(w.wide.flags.map(flag_name));
        }
        Input::Varied(v) => {
            let v = &v.varied;
            texts.extend(v.texts.iter().map(String::as_str));
            match &v.opt {
                None => found.push("none"),
                Some(t) => {
                    found.push("some");
                    texts.push(t);
                }
            }
            match &v.res {
                Ok(n) => {
                    found.push("ok");
                    ints.push(*n);
                }
                Err(t) => {
                    found.push("err");
                    texts.push(t);
                }
            }
            match &v.kind {
                Kind::Plain => found.push("Plain"),
                Kind::Tagged(t) => {
                    found.push("Tagged");
                    texts.push(t);
                }
                Kind::Scored(a, b) => {
                    found.push("Scored");
                    ints.extend([*a, *b]);
                }
            }
            ints.extend(v.ints);
        }
        Input::Person(p) => {
            ints.extend([p.id, p.visits, p.score]);
            texts.extend([p.name.as_str(), p.email.as_str(), p.phone.as_str()]);
        }
    }
    if ints.iter().any(|n| *n < 0) {
        found.push("negative Int");
    }
    if texts.iter().any(|t| t.is_empty()) {
        found.push("empty Text");
    }
    found
}

fn add(picks: &mut Vec<Pick>, kind: InputKind, i: usize, reason: &'static str) {
    match picks.iter_mut().find(|p| p.kind == kind && p.i == i) {
        Some(p) => p.reasons.push(reason),
        None => picks.push(Pick {
            kind,
            i,
            reasons: vec![reason],
        }),
    }
}

fn select(corpus: &Corpus) -> Result<Vec<Pick>, String> {
    let mut picks = Vec::new();
    for kind in KINDS {
        add(&mut picks, kind, 0, "value 0");
    }
    let found: Vec<(InputKind, usize, Vec<&str>)> = generator_order()
        .into_iter()
        .map(|(kind, i)| (kind, i, properties(&input(corpus, kind, i))))
        .collect();
    for property in PROPERTIES {
        let (kind, i, _) = found
            .iter()
            .find(|(_, _, has)| has.contains(&property))
            .ok_or_else(|| format!("no input value has the property {property}"))?;
        add(&mut picks, *kind, *i, property);
    }
    Ok(picks)
}

fn lower_hex(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(2 * bytes.len());
    for b in bytes {
        out.push_str(&format!("{b:02x}"));
    }
    out
}

fn form(name: &str, fields: impl IntoIterator<Item = String>) -> String {
    let mut out = format!("({name}");
    for field in fields {
        out.push(' ');
        out.push_str(&field);
    }
    out.push(')');
    out
}

fn text(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        if c == '"' || c == '\\' {
            out.push('\\');
        }
        out.push(c);
    }
    out.push('"');
    out
}

fn command(cmd: &CommandId) -> String {
    text(&lower_hex(&cmd.0))
}

fn sealed(slot: &Sealed) -> String {
    text(&lower_hex(&slot.0))
}

fn principal(name: &str) -> String {
    form("principal", [text(name)])
}

fn time(nanos: i64) -> String {
    form("time", [nanos.to_string()])
}

fn slot_id(key: i64) -> String {
    form("SlotId", [key.to_string()])
}

fn step_id(s: &StepId) -> String {
    form(
        "step",
        [
            s.machine.clone(),
            slot_id(s.key),
            s.life.to_string(),
            s.seq.to_string(),
        ],
    )
}

fn ticket(t: &Ticket) -> String {
    form(
        "ticket",
        [
            t.machine.clone(),
            slot_id(t.key),
            t.life.to_string(),
            t.seq.to_string(),
            t.idx.to_string(),
        ],
    )
}

fn hold_token(hold: &StepId) -> String {
    form("HoldToken", [step_id(hold)])
}

fn flag(f: Flag) -> String {
    form(flag_name(f), [])
}

fn float(bits: u64) -> String {
    form("f64", [f64::from_bits(bits).to_string()])
}

fn decimal(c: i128) -> String {
    let digits = format!("{:03}", c.unsigned_abs());
    let (whole, cents) = digits.split_at(digits.len() - 2);
    let sign = if c < 0 { "-" } else { "" };
    form("dec", [format!("{sign}{whole}.{cents}")])
}

fn kind(k: &Kind) -> String {
    match k {
        Kind::Plain => form("Plain", []),
        Kind::Tagged(t) => form("Tagged", [text(t)]),
        Kind::Scored(a, b) => form("Scored", [a.to_string(), b.to_string()]),
    }
}

fn wide_fields(w: &Wide) -> Vec<String> {
    let mut fields: Vec<String> = w.ints.iter().map(i64::to_string).collect();
    fields.extend(w.flags.map(flag));
    fields.extend(w.bools.iter().map(bool::to_string));
    fields.extend(w.floats.map(float));
    fields.push(decimal(w.money));
    fields
}

fn varied_fields(v: &Varied) -> Vec<String> {
    let mut fields: Vec<String> = v.texts.iter().map(|t| text(t)).collect();
    fields.push(match &v.opt {
        Some(t) => form("some", [text(t)]),
        None => form("none", []),
    });
    fields.push(match &v.res {
        Ok(n) => form("ok", [n.to_string()]),
        Err(t) => form("err", [text(t)]),
    });
    fields.push(kind(&v.kind));
    fields.extend(v.ints.iter().map(i64::to_string));
    fields
}

fn person_fields(p: &Person) -> [String; 7] {
    [
        p.id.to_string(),
        sealed(&p.name),
        sealed(&p.email),
        sealed(&p.phone),
        p.visits.to_string(),
        p.score.to_string(),
        time(p.since),
    ]
}

fn input_text(value: &Input) -> String {
    match value {
        Input::Hold(h) => form(
            "HoldIn",
            [
                command(&h.cmd),
                slot_id(h.key),
                principal(&h.sender),
                time(h.now),
            ],
        ),
        Input::Confirm(c) => form(
            "ConfirmIn",
            [
                command(&c.cmd),
                slot_id(c.key),
                principal(&c.sender),
                time(c.now),
                hold_token(&c.token),
            ],
        ),
        Input::Wide(w) => form("WideIn", once(command(&w.cmd)).chain(wide_fields(&w.wide))),
        Input::Varied(v) => form(
            "VariedIn",
            once(command(&v.cmd)).chain(varied_fields(&v.varied)),
        ),
        Input::Person(p) => form(
            "PersonIn",
            [
                command(&p.cmd),
                p.id.to_string(),
                text(&p.name),
                text(&p.email),
                text(&p.phone),
                p.visits.to_string(),
                p.score.to_string(),
                time(p.since),
            ],
        ),
    }
}

fn state_text(state: &State) -> String {
    match state {
        State::Slot(SlotState::Absent) => form("Absent", []),
        State::Slot(SlotState::Free) => form("Free", []),
        State::Slot(SlotState::Held(h)) => form(
            "Held",
            [form(
                "HeldFields",
                [principal(&h.holder), hold_token(&h.hold), ticket(&h.timer)],
            )],
        ),
        State::Slot(SlotState::Booked(b)) => form(
            "Booked",
            [form(
                "BookedFields",
                [principal(&b.owner), hold_token(&b.hold)],
            )],
        ),
        State::Wide(w) => form("Wide", wide_fields(w)),
        State::Varied(v) => form("Varied", varied_fields(v)),
        State::Person(p) => form("Person", person_fields(p)),
    }
}

fn states(corpus: &Corpus, kind: InputKind, i: usize) -> [State; 2] {
    match kind {
        InputKind::Hold => [
            State::Slot(SlotState::Free),
            State::Slot(SlotState::Held(held(corpus, i))),
        ],
        InputKind::Confirm => {
            let start = held(corpus, i);
            let new = BookedFields {
                owner: start.holder.clone(),
                hold: start.hold.clone(),
            };
            [
                State::Slot(SlotState::Held(start)),
                State::Slot(SlotState::Booked(new)),
            ]
        }
        InputKind::Wide => {
            let start = wide_start(corpus, i);
            let mut new = start.clone();
            new.ints[0] = new.ints[0].wrapping_add(1);
            [State::Wide(start), State::Wide(new)]
        }
        InputKind::Varied => {
            let start = varied_start(corpus, i);
            let mut new = start.clone();
            new.ints[0] = new.ints[0].wrapping_add(1);
            [State::Varied(start), State::Varied(new)]
        }
        InputKind::Person => {
            let start = person_start(corpus, i);
            let mut new = start.clone();
            new.visits = new.visits.wrapping_add(1);
            [State::Person(Box::new(start)), State::Person(Box::new(new))]
        }
    }
}

fn bytes<A: Arm>(corpus: &Corpus, picks: &[Pick]) -> Vec<String> {
    let mut arm = A::new(corpus);
    picks
        .iter()
        .map(|p| {
            arm.reset();
            if p.kind == InputKind::Confirm {
                arm.step_hold(p.i);
            }
            step(&mut arm, p.kind, p.i);
            format!(
                "{name} frame {}\n{name} log {}",
                lower_hex(arm.frame(p.kind, p.i)),
                lower_hex(arm.log()),
                name = A::NAME
            )
        })
        .collect()
}

pub fn hex(corpus: &Corpus) -> Result<(), String> {
    let picks = select(corpus)?;
    let f = bytes::<ArmF>(corpus, &picks);
    let p = bytes::<ArmP>(corpus, &picks);
    let s = bytes::<ArmS>(corpus, &picks);
    for (n, pick) in picks.iter().enumerate() {
        let [start, new] = states(corpus, pick.kind, pick.i);
        println!(
            "value {} {}: {}",
            pick.kind.name(),
            pick.i,
            pick.reasons.join(", ")
        );
        println!("input {}", input_text(&input(corpus, pick.kind, pick.i)));
        println!("start {}", state_text(&start));
        println!("new {}", state_text(&new));
        println!("{}", f[n]);
        println!("{}", p[n]);
        println!("{}", s[n]);
    }
    Ok(())
}
