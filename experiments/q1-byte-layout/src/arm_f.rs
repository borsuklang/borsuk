use std::hint::black_box;

use crate::types::{
    Admitted, Arm, BookedFields, Change, CommandId, ConfirmIn, Corpus, Decision, Flag, Group,
    HeldFields, HoldIn, Input, InputKind, KINDS, Kind, Log, LogInput, MACHINE, N, Output, Person,
    PersonIn, Refused, Sealed, SlotState, State, StepId, TIMER_NANOS, Ticket, Varied, VariedIn,
    Wide, WideIn, fold, fold_text, input, person_start, varied_start, wide_start,
};

const VERSION: u16 = 1;
const LIMIT: u64 = 1 << 32;
const CANONICAL_NAN: u64 = 0x7FF8_0000_0000_0000;
const INFINITY: u64 = 0x7FF0_0000_0000_0000;
const SIGN: u64 = 1 << 63;
const DECIMAL_MAX: i128 = 10i128.pow(38) - 1;
const SEAL_TEXT: usize = 86;
const SLOT: usize = 128;
const FLAGS: [Flag; 4] = [Flag::A, Flag::B, Flag::C, Flag::D];
const ABSENT: u8 = 0;
const FREE: u8 = 1;
const HELD: u8 = 2;
const BOOKED: u8 = 3;
const AFTER: u8 = 0;
const CANCEL: u8 = 1;
const NONE: u8 = 0;
const SOME: u8 = 1;
const OK: u8 = 0;
const ERR: u8 = 1;
const PLAIN: u8 = 0;
const TAGGED: u8 = 1;
const SCORED: u8 = 2;
const OUTCOME: u8 = 0;
const LIFE: i64 = 1;
const TIMER_IDX: i64 = 0;
const OFFSET: usize = 4;
const INT: usize = 8;
const COUNT: usize = 2;
const CMD_END: usize = COUNT + 34;
const ID_SIZE: usize = OFFSET + MACHINE.len() + 3 * INT;
const TICKET_SIZE: usize = ID_SIZE + INT;
const VARIANT_FIXED: usize = 1 + OFFSET;
const AFTER_FIXED: usize = 1 + INT + OFFSET;
const CHANGE_SIZE: usize = 2 + INT;
const HOLD_COUNT: u16 = 4;
const HOLD_FIXED: usize = CMD_END + INT + OFFSET + INT;
const CONFIRM_COUNT: u16 = 5;
const CONFIRM_FIXED: usize = HOLD_FIXED + OFFSET;
const KEY: usize = CMD_END;
const SENDER: usize = KEY + INT;
const NOW: usize = SENDER + OFFSET;
const TOKEN: usize = NOW + INT;
const WIDE_IN_COUNT: u16 = 25;
const WIDE_COUNT: u16 = 24;
const WIDE_FLAGS: usize = 14 * INT;
const WIDE_BOOLS: usize = WIDE_FLAGS + 4;
const WIDE_FLOATS: usize = WIDE_BOOLS + 2;
const WIDE_MONEY: usize = WIDE_FLOATS + 3 * INT;
const WIDE_SIZE: usize = WIDE_MONEY + 16;
const WIDE_INT: u16 = 0;
const VARIED_IN_COUNT: u16 = 12;
const VARIED_COUNT: u16 = 11;
const VARIED_OPT: usize = 4 * OFFSET;
const VARIED_RES: usize = VARIED_OPT + OFFSET;
const VARIED_KIND: usize = VARIED_RES + OFFSET;
const VARIED_INTS: usize = VARIED_KIND + OFFSET;
const VARIED_SIZE: usize = VARIED_INTS + 4 * INT;
const VARIED_INT: u16 = 7;
const PERSON_IN_COUNT: u16 = 8;
const PERSON_COUNT: u16 = 7;
const PERSON_TEXTS: [usize; 3] = [
    CMD_END + INT,
    CMD_END + INT + OFFSET,
    CMD_END + INT + 2 * OFFSET,
];
const PERSON_IN_REST: usize = CMD_END + INT + 3 * OFFSET;
const PERSON_IN_FIXED: usize = PERSON_IN_REST + 3 * INT;
const PERSON_VISITS: u16 = 4;
const SEALED_ID: usize = 0;
const SEALED_SLOTS: usize = INT;
const SEALED_VISITS: usize = SEALED_SLOTS + 3 * SLOT;
const SEALED_SIZE: usize = SEALED_VISITS + 3 * INT;
const PERSON_FIXED: usize = COUNT + SEALED_SIZE;
const ADMITTED_FIXED: usize = CMD_END + SEALED_SIZE;
const HELD_COUNT: u16 = 3;
const HELD_FIXED: usize = COUNT + 3 * OFFSET;
const BOOKED_COUNT: u16 = 2;
const BOOKED_FIXED: usize = COUNT + 2 * OFFSET;
const ADMITTED: &str = "each corpus frame passes admission";
const HELD_STATE: &str = "ConfirmIn i runs on the Held state of HoldIn i";
const FITS: &str = "each corpus value has a frame below 2^32 bytes";
const STATE_FRAME: &str = "each state frame of arm F decodes";

type Span = (usize, usize);

pub struct ArmF {
    pad: [u8; SLOT],
    hold_frames: Vec<Vec<u8>>,
    confirm_frames: Vec<Vec<u8>>,
    wide_frames: Vec<Vec<u8>>,
    varied_frames: Vec<Vec<u8>>,
    person_frames: Vec<Vec<u8>>,
    free: Vec<u8>,
    slots: Vec<Vec<u8>>,
    wides: Vec<Vec<u8>>,
    wide_starts: Vec<Vec<u8>>,
    varieds: Vec<Vec<u8>>,
    varied_starts: Vec<Vec<u8>>,
    persons: Vec<Vec<u8>>,
    person_starts: Vec<Vec<u8>>,
    log: Vec<u8>,
}

fn bytes<const K: usize>(b: &[u8], at: usize) -> [u8; K] {
    let mut a = [0; K];
    a.copy_from_slice(&b[at..at + K]);
    a
}

fn u16_at(b: &[u8], at: usize) -> u16 {
    u16::from_le_bytes(bytes(b, at))
}

fn u32_at(b: &[u8], at: usize) -> usize {
    u32::from_le_bytes(bytes(b, at)) as usize
}

fn i64_at(b: &[u8], at: usize) -> i64 {
    i64::from_le_bytes(bytes(b, at))
}

fn u64_at(b: &[u8], at: usize) -> u64 {
    u64::from_le_bytes(bytes(b, at))
}

fn i128_at(b: &[u8], at: usize) -> i128 {
    i128::from_le_bytes(bytes(b, at))
}

fn put_u16(b: &mut Vec<u8>, v: u16) {
    b.extend_from_slice(&v.to_le_bytes());
}

fn put_u32(b: &mut Vec<u8>, v: usize) {
    b.extend_from_slice(&(v as u32).to_le_bytes());
}

fn put_i64(b: &mut Vec<u8>, v: i64) {
    b.extend_from_slice(&v.to_le_bytes());
}

fn put_id(b: &mut Vec<u8>, machine: &str, key: i64, life: i64, seq: i64) {
    put_u32(b, machine.len());
    b.extend_from_slice(machine.as_bytes());
    put_i64(b, key);
    put_i64(b, life);
    put_i64(b, seq);
}

fn slot(b: &mut Vec<u8>) -> usize {
    let at = b.len();
    b.extend_from_slice(&[0; OFFSET]);
    at
}

fn part(b: &mut [u8], start: usize, at: usize) {
    let offset = (b.len() - start) as u32;
    b[at..at + OFFSET].copy_from_slice(&offset.to_le_bytes());
}

fn put_tail(b: &mut Vec<u8>, tag: u8, text: &str) {
    b.push(tag);
    put_u32(b, VARIANT_FIXED);
    b.extend_from_slice(text.as_bytes());
}

fn put_wide(b: &mut Vec<u8>, w: &Wide) {
    for x in w.ints {
        put_i64(b, x);
    }
    for f in w.flags {
        b.push(f as u8);
    }
    for x in w.bools {
        b.push(u8::from(x));
    }
    for x in w.floats {
        b.extend_from_slice(&x.to_le_bytes());
    }
    b.extend_from_slice(&w.money.to_le_bytes());
}

fn put_varied(b: &mut Vec<u8>, start: usize, v: &Varied) {
    let slots: [usize; 7] = std::array::from_fn(|_| slot(b));
    for x in v.ints {
        put_i64(b, x);
    }
    for (&at, t) in slots.iter().zip(&v.texts) {
        part(b, start, at);
        b.extend_from_slice(t.as_bytes());
    }
    part(b, start, slots[4]);
    match &v.opt {
        None => b.push(NONE),
        Some(t) => put_tail(b, SOME, t),
    }
    part(b, start, slots[5]);
    match &v.res {
        Ok(x) => {
            b.push(OK);
            put_i64(b, *x);
        }
        Err(t) => put_tail(b, ERR, t),
    }
    part(b, start, slots[6]);
    match &v.kind {
        Kind::Plain => b.push(PLAIN),
        Kind::Tagged(t) => put_tail(b, TAGGED, t),
        Kind::Scored(x, y) => {
            b.push(SCORED);
            put_i64(b, *x);
            put_i64(b, *y);
        }
    }
}

fn put_person(b: &mut Vec<u8>, p: &Person) {
    put_i64(b, p.id);
    for s in [&p.name, &p.email, &p.phone] {
        b.extend_from_slice(&s.0);
    }
    put_i64(b, p.visits);
    put_i64(b, p.score);
    put_i64(b, p.since);
}

fn start_frame() -> Vec<u8> {
    VERSION.to_le_bytes().to_vec()
}

fn wide_frame(w: &Wide) -> Vec<u8> {
    let mut b = start_frame();
    put_u16(&mut b, WIDE_COUNT);
    put_wide(&mut b, w);
    b
}

fn varied_frame(v: &Varied) -> Vec<u8> {
    let mut b = start_frame();
    let start = b.len();
    put_u16(&mut b, VARIED_COUNT);
    put_varied(&mut b, start, v);
    b
}

fn person_frame(p: &Person) -> Vec<u8> {
    let mut b = start_frame();
    put_u16(&mut b, PERSON_COUNT);
    put_person(&mut b, p);
    b
}

fn frame(b: &[u8]) -> Option<&[u8]> {
    ((b.len() as u64) < LIMIT && b.len() >= 2 && u16_at(b, 0) == VERSION).then(|| &b[2..])
}

fn count(c: &[u8], n: u16) -> Option<()> {
    (c.len() >= COUNT && u16_at(c, 0) == n).then_some(())
}

fn parts<const K: usize>(c: &[u8], slots: [usize; K], fixed: usize) -> Option<[Span; K]> {
    if c.len() < fixed {
        return None;
    }
    let starts = slots.map(|at| u32_at(c, at));
    let valid =
        starts[0] == fixed && starts.windows(2).all(|w| w[0] <= w[1]) && starts[K - 1] <= c.len();
    valid.then(|| {
        std::array::from_fn(|k| (starts[k], starts.get(k + 1).copied().unwrap_or(c.len())))
    })
}

fn text(c: &[u8], (a, e): Span) -> Option<&str> {
    std::str::from_utf8(&c[a..e]).ok()
}

fn string(c: &[u8], span: Span) -> Option<String> {
    text(c, span).map(str::to_string)
}

fn tail(o: &[u8]) -> Option<&str> {
    let [t] = parts(o, [1], VARIANT_FIXED)?;
    text(o, t)
}

fn id(p: &[u8], slots: usize) -> Option<usize> {
    if p.len() < OFFSET + slots * INT {
        return None;
    }
    let n = u32_at(p, 0);
    let named = n == p.len() - OFFSET - slots * INT && &p[OFFSET..OFFSET + n] == MACHINE.as_bytes();
    named.then_some(OFFSET + n)
}

fn step_id(p: &[u8]) -> Option<StepId> {
    let k = id(p, 3)?;
    Some(StepId {
        machine: MACHINE.to_string(),
        key: i64_at(p, k),
        life: i64_at(p, k + INT),
        seq: i64_at(p, k + 2 * INT),
    })
}

fn ticket(p: &[u8]) -> Option<Ticket> {
    let k = id(p, 4)?;
    Some(Ticket {
        machine: MACHINE.to_string(),
        key: i64_at(p, k),
        life: i64_at(p, k + INT),
        seq: i64_at(p, k + 2 * INT),
        idx: i64_at(p, k + 3 * INT),
    })
}

fn cmd(c: &[u8]) -> CommandId {
    CommandId(bytes(c, COUNT))
}

fn float_ok(bits: u64) -> bool {
    (bits & !SIGN) <= INFINITY || bits == CANONICAL_NAN
}

fn wide_ok(f: &[u8]) -> bool {
    f[WIDE_FLAGS..WIDE_BOOLS]
        .iter()
        .all(|&t| usize::from(t) < FLAGS.len())
        && f[WIDE_BOOLS..WIDE_FLOATS].iter().all(|&b| b <= 1)
        && (0..3).all(|k| float_ok(u64_at(f, WIDE_FLOATS + k * INT)))
        && (-DECIMAL_MAX..=DECIMAL_MAX).contains(&i128_at(f, WIDE_MONEY))
}

fn wide(f: &[u8]) -> Wide {
    Wide {
        ints: std::array::from_fn(|k| i64_at(f, k * INT)),
        flags: std::array::from_fn(|k| FLAGS[usize::from(f[WIDE_FLAGS + k])]),
        bools: std::array::from_fn(|k| f[WIDE_BOOLS + k] == 1),
        floats: std::array::from_fn(|k| u64_at(f, WIDE_FLOATS + k * INT)),
        money: i128_at(f, WIDE_MONEY),
    }
}

fn opt(o: &[u8]) -> Option<Option<&str>> {
    match *o.first()? {
        NONE if o.len() == 1 => Some(None),
        SOME => tail(o).map(Some),
        _ => None,
    }
}

fn res(o: &[u8]) -> Option<Result<i64, &str>> {
    match *o.first()? {
        OK if o.len() == 1 + INT => Some(Ok(i64_at(o, 1))),
        ERR => tail(o).map(Err),
        _ => None,
    }
}

fn kind_ok(o: &[u8]) -> bool {
    match o.first() {
        Some(&PLAIN) => o.len() == 1,
        Some(&TAGGED) => tail(o).is_some(),
        Some(&SCORED) => o.len() == 1 + 2 * INT,
        _ => false,
    }
}

fn kind(o: &[u8]) -> Option<Kind> {
    match *o.first()? {
        PLAIN if o.len() == 1 => Some(Kind::Plain),
        TAGGED => tail(o).map(|t| Kind::Tagged(t.to_string())),
        SCORED if o.len() == 1 + 2 * INT => Some(Kind::Scored(i64_at(o, 1), i64_at(o, 1 + INT))),
        _ => None,
    }
}

fn varied_parts(c: &[u8], base: usize) -> Option<[Span; 7]> {
    let p = parts(
        c,
        std::array::from_fn(|k| base + k * OFFSET),
        base + VARIED_SIZE,
    )?;
    let valid = p[..4].iter().all(|&t| text(c, t).is_some())
        && opt(&c[p[4].0..p[4].1]).is_some()
        && res(&c[p[5].0..p[5].1]).is_some()
        && kind_ok(&c[p[6].0..p[6].1]);
    valid.then_some(p)
}

fn varied(c: &[u8], base: usize, p: &[Span; 7]) -> Option<Varied> {
    Some(Varied {
        texts: [
            string(c, p[0])?,
            string(c, p[1])?,
            string(c, p[2])?,
            string(c, p[3])?,
        ],
        opt: opt(&c[p[4].0..p[4].1])?.map(str::to_string),
        res: res(&c[p[5].0..p[5].1])?.map_err(str::to_string),
        kind: kind(&c[p[6].0..p[6].1])?,
        ints: std::array::from_fn(|k| i64_at(c, base + VARIED_INTS + k * INT)),
    })
}

fn sealed(c: &[u8], at: usize) -> Person {
    Person {
        id: i64_at(c, at + SEALED_ID),
        name: Sealed(bytes(c, at + SEALED_SLOTS)),
        email: Sealed(bytes(c, at + SEALED_SLOTS + SLOT)),
        phone: Sealed(bytes(c, at + SEALED_SLOTS + 2 * SLOT)),
        visits: i64_at(c, at + SEALED_VISITS),
        score: i64_at(c, at + SEALED_VISITS + INT),
        since: i64_at(c, at + SEALED_VISITS + 2 * INT),
    }
}

fn admit_hold(b: &[u8]) -> Option<Span> {
    let c = frame(b)?;
    count(c, HOLD_COUNT)?;
    let [sender] = parts(c, [SENDER], HOLD_FIXED)?;
    text(c, sender)?;
    Some(sender)
}

fn admit_confirm(b: &[u8]) -> Option<(Span, usize)> {
    let c = frame(b)?;
    count(c, CONFIRM_COUNT)?;
    let [sender, token] = parts(c, [SENDER, TOKEN], CONFIRM_FIXED)?;
    text(c, sender)?;
    let k = id(&c[token.0..token.1], 3)?;
    Some((sender, token.0 + k))
}

fn admit_wide(b: &[u8]) -> Option<()> {
    let c = frame(b)?;
    count(c, WIDE_IN_COUNT)?;
    (c.len() == CMD_END + WIDE_SIZE && wide_ok(&c[CMD_END..])).then_some(())
}

fn admit_varied(b: &[u8]) -> Option<[Span; 7]> {
    let c = frame(b)?;
    count(c, VARIED_IN_COUNT)?;
    varied_parts(c, CMD_END)
}

fn person_parts(b: &[u8]) -> Option<(&[u8], [Span; 3])> {
    let c = frame(b)?;
    count(c, PERSON_IN_COUNT)?;
    Some((c, parts(c, PERSON_TEXTS, PERSON_IN_FIXED)?))
}

fn admit_person(b: &[u8], pad: &[u8; SLOT], log: &mut Vec<u8>) -> Option<()> {
    let (c, texts) = person_parts(b)?;
    log.clear();
    put_u16(log, VERSION);
    put_u32(log, 2 + ADMITTED_FIXED);
    put_u16(log, VERSION);
    log.extend_from_slice(&c[..CMD_END + INT]);
    for span in texts {
        let t = text(c, span)?.as_bytes();
        if t.len() > SEAL_TEXT {
            return None;
        }
        put_u16(log, t.len() as u16);
        log.extend_from_slice(t);
        log.extend_from_slice(&pad[2 + t.len()..]);
    }
    log.extend_from_slice(&c[PERSON_IN_REST..PERSON_IN_FIXED]);
    Some(())
}

fn hold_in(b: &[u8]) -> Option<HoldIn> {
    let sender = admit_hold(b)?;
    let c = &b[2..];
    Some(HoldIn {
        cmd: cmd(c),
        key: i64_at(c, KEY),
        sender: string(c, sender)?,
        now: i64_at(c, NOW),
    })
}

fn confirm_in(b: &[u8]) -> Option<ConfirmIn> {
    let (sender, _) = admit_confirm(b)?;
    let c = &b[2..];
    let at = u32_at(c, TOKEN);
    Some(ConfirmIn {
        cmd: cmd(c),
        key: i64_at(c, KEY),
        sender: string(c, sender)?,
        now: i64_at(c, NOW),
        token: step_id(&c[at..])?,
    })
}

fn wide_in(b: &[u8]) -> Option<WideIn> {
    admit_wide(b)?;
    let c = &b[2..];
    Some(WideIn {
        cmd: cmd(c),
        wide: wide(&c[CMD_END..]),
    })
}

fn varied_in(b: &[u8]) -> Option<VariedIn> {
    let p = admit_varied(b)?;
    let c = &b[2..];
    Some(VariedIn {
        cmd: cmd(c),
        varied: varied(c, CMD_END, &p)?,
    })
}

fn person_in(b: &[u8]) -> Option<PersonIn> {
    let (c, [name, email, phone]) = person_parts(b)?;
    let rest = PERSON_IN_REST;
    Some(PersonIn {
        cmd: cmd(c),
        id: i64_at(c, CMD_END),
        name: string(c, name)?,
        email: string(c, email)?,
        phone: string(c, phone)?,
        visits: i64_at(c, rest),
        score: i64_at(c, rest + INT),
        since: i64_at(c, rest + 2 * INT),
    })
}

fn admitted(b: &[u8]) -> Option<Admitted> {
    let c = frame(b)?;
    count(c, PERSON_IN_COUNT)?;
    (c.len() == ADMITTED_FIXED).then(|| Admitted {
        cmd: cmd(c),
        person: sealed(c, CMD_END),
    })
}

fn held(h: &[u8]) -> Option<HeldFields> {
    count(h, HELD_COUNT)?;
    let [holder, hold, timer] = parts(h, [2, 6, 10], HELD_FIXED)?;
    Some(HeldFields {
        holder: string(h, holder)?,
        hold: step_id(&h[hold.0..hold.1])?,
        timer: ticket(&h[timer.0..timer.1])?,
    })
}

fn booked(h: &[u8]) -> Option<BookedFields> {
    count(h, BOOKED_COUNT)?;
    let [owner, hold] = parts(h, [2, 6], BOOKED_FIXED)?;
    Some(BookedFields {
        owner: string(h, owner)?,
        hold: step_id(&h[hold.0..hold.1])?,
    })
}

fn slot_state(c: &[u8]) -> Option<SlotState> {
    match *c.first()? {
        ABSENT if c.len() == 1 => Some(SlotState::Absent),
        FREE if c.len() == 1 => Some(SlotState::Free),
        HELD => {
            let [h] = parts(c, [1], VARIANT_FIXED)?;
            held(&c[h.0..h.1]).map(SlotState::Held)
        }
        BOOKED => {
            let [h] = parts(c, [1], VARIANT_FIXED)?;
            booked(&c[h.0..h.1]).map(SlotState::Booked)
        }
        _ => None,
    }
}

fn wide_state(b: &[u8]) -> Option<Wide> {
    let c = frame(b)?;
    count(c, WIDE_COUNT)?;
    (c.len() == COUNT + WIDE_SIZE && wide_ok(&c[COUNT..])).then(|| wide(&c[COUNT..]))
}

fn varied_state(b: &[u8]) -> Option<Varied> {
    let c = frame(b)?;
    count(c, VARIED_COUNT)?;
    let p = varied_parts(c, COUNT)?;
    varied(c, COUNT, &p)
}

fn person_state(b: &[u8]) -> Option<Person> {
    let c = frame(b)?;
    count(c, PERSON_COUNT)?;
    (c.len() == PERSON_FIXED).then(|| sealed(c, COUNT))
}

fn piece(r: &[u8]) -> Option<(&[u8], &[u8])> {
    if r.len() < OFFSET {
        return None;
    }
    let n = u32_at(r, 0);
    (n <= r.len() - OFFSET).then(|| (&r[OFFSET..OFFSET + n], &r[OFFSET + n..]))
}

fn fields(mut c: &[u8], int: fn(u16) -> bool) -> Option<Vec<(u64, i64)>> {
    let mut out: Vec<(u64, i64)> = Vec::new();
    while !c.is_empty() {
        if c.len() < CHANGE_SIZE {
            return None;
        }
        let k = u16_at(c, 0);
        if !int(k) || out.last().is_some_and(|&(j, _)| j >= u64::from(k)) {
            return None;
        }
        out.push((u64::from(k), i64_at(c, 2)));
        c = &c[CHANGE_SIZE..];
    }
    Some(out)
}

fn output(o: &[u8]) -> Option<Output> {
    match *o.first()? {
        AFTER => {
            let [t] = parts(o, [1 + INT], AFTER_FIXED)?;
            Some(Output::After(i64_at(o, 1), ticket(&o[t.0..t.1])?))
        }
        CANCEL => {
            let [t] = parts(o, [1], VARIANT_FIXED)?;
            Some(Output::Cancel(ticket(&o[t.0..t.1])?))
        }
        _ => None,
    }
}

fn fold_id(sum: u64, b: &[u8], k: usize) -> u64 {
    let sum = fold(sum, u64_at(b, k));
    let sum = fold(sum, u64_at(b, k + INT));
    fold(sum, u64_at(b, k + 2 * INT))
}

fn fold_wide(sum: u64, f: &[u8]) -> u64 {
    let sum = fold(sum, u64_at(f, 0));
    let sum = fold(sum, u64::from(f[WIDE_BOOLS]));
    let sum = fold(sum, u64_at(f, WIDE_FLOATS));
    let sum = fold(sum, u64_at(f, WIDE_MONEY));
    fold(sum, u64_at(f, WIDE_MONEY + INT))
}

fn fold_varied(sum: u64, c: &[u8], (a, e): Span, res: usize, kind: usize, int: usize) -> u64 {
    let sum = fold_text(sum, &c[a..e]);
    let sum = fold(sum, u64::from(c[res]));
    let sum = fold(sum, u64::from(c[kind]));
    fold(sum, u64_at(c, int))
}

fn fold_person(sum: u64, c: &[u8], id: usize, visits: usize, since: usize) -> u64 {
    let sum = fold(sum, u64_at(c, id));
    let sum = fold(sum, u64_at(c, visits));
    fold(sum, u64_at(c, since))
}

fn put_head(log: &mut Vec<u8>, frame: &[u8]) {
    log.clear();
    put_u16(log, VERSION);
    put_u32(log, frame.len());
    log.extend_from_slice(frame);
}

fn put_field(log: &mut Vec<u8>, index: u16, value: i64) {
    put_u32(log, CHANGE_SIZE);
    put_u16(log, index);
    put_i64(log, value);
    put_u32(log, 0);
    put_u32(log, 1);
    log.push(OUTCOME);
}

fn set_i64(state: &mut [u8], at: usize, value: i64) {
    state[at..at + INT].copy_from_slice(&value.to_le_bytes());
}

fn refuse(out: &mut Vec<Refused>, kind: InputKind, cause: &'static str, frame: Vec<u8>) {
    out.push(Refused { kind, cause, frame });
}

fn with(f: &[u8], at: usize, new: &[u8]) -> Vec<u8> {
    let mut g = f.to_vec();
    g[at..at + new.len()].copy_from_slice(new);
    g
}

fn with_offset(f: &[u8], slot: usize, offset: usize) -> Vec<u8> {
    with(f, 2 + slot, &(offset as u32).to_le_bytes())
}

fn grown(f: &[u8], new: &[u8]) -> Vec<u8> {
    [f, new].concat()
}

fn refuse_frame(out: &mut Vec<Refused>, kind: InputKind, f: &[u8], n: u16, fixed: usize) {
    refuse(
        out,
        kind,
        "version",
        with(f, 0, &(VERSION + 1).to_le_bytes()),
    );
    refuse(out, kind, "short-frame", f[..1 + fixed].to_vec());
    refuse(
        out,
        kind,
        "record-count-above",
        with(f, 2, &(n + 1).to_le_bytes()),
    );
    refuse(
        out,
        kind,
        "record-count-below",
        with(f, 2, &(n - 1).to_le_bytes()),
    );
}

fn refuse_offsets(
    out: &mut Vec<Refused>,
    kind: InputKind,
    f: &[u8],
    slots: &[usize],
    fixed: usize,
) {
    refuse(
        out,
        kind,
        "first-offset",
        with_offset(f, slots[0], fixed + 1),
    );
    if let (Some(&second), Some(&last)) = (slots.get(1), slots.last()) {
        refuse(out, kind, "offset-order", with_offset(f, second, fixed - 1));
        refuse(out, kind, "offset-end", with_offset(f, last, f.len() - 1));
    }
}

impl Arm for ArmF {
    const NAME: &'static str = "F";

    fn new(corpus: &Corpus) -> Self {
        let frames = |kind| -> Vec<Vec<u8>> {
            (0..N)
                .map(|i| Self::encode(&input(corpus, kind, i)).expect(FITS))
                .collect()
        };
        let [
            hold_frames,
            confirm_frames,
            wide_frames,
            varied_frames,
            person_frames,
        ] = KINDS.map(frames);
        let mut free = start_frame();
        free.push(FREE);
        let wide_starts: Vec<Vec<u8>> =
            (0..N).map(|i| wide_frame(&wide_start(corpus, i))).collect();
        let varied_starts: Vec<Vec<u8>> = (0..N)
            .map(|i| varied_frame(&varied_start(corpus, i)))
            .collect();
        let person_starts: Vec<Vec<u8>> = (0..N)
            .map(|i| person_frame(&person_start(corpus, i)))
            .collect();
        let longest = [
            &hold_frames,
            &confirm_frames,
            &wide_frames,
            &varied_frames,
            &person_frames,
        ]
        .iter()
        .flat_map(|fs| fs.iter().map(Vec::len))
        .max()
        .unwrap_or(0);
        ArmF {
            pad: corpus.pad,
            hold_frames,
            confirm_frames,
            wide_frames,
            varied_frames,
            person_frames,
            slots: vec![free.clone(); N],
            free,
            wides: wide_starts.clone(),
            wide_starts,
            varieds: varied_starts.clone(),
            varied_starts,
            persons: person_starts.clone(),
            person_starts,
            log: Vec::with_capacity(longest),
        }
    }

    fn reset(&mut self) {
        for s in &mut self.slots {
            s.clear();
            s.extend_from_slice(&self.free);
        }
        for (s, from) in self.wides.iter_mut().zip(&self.wide_starts) {
            s.copy_from_slice(from);
        }
        for (s, from) in self.varieds.iter_mut().zip(&self.varied_starts) {
            s.copy_from_slice(from);
        }
        for (s, from) in self.persons.iter_mut().zip(&self.person_starts) {
            s.copy_from_slice(from);
        }
    }

    fn step_hold(&mut self, i: usize) -> u64 {
        let frame = self.hold_frames[i].as_slice();
        let (a, e) = admit_hold(frame).expect(ADMITTED);
        let c = &frame[2..];
        let key = i64_at(c, KEY);
        let sender = &c[a..e];
        let state = &mut self.slots[i];
        let mut sum = fold(0, key as u64);
        sum = fold_text(sum, sender);
        sum = fold(sum, u64_at(c, NOW));
        sum = fold(sum, u64::from(state[2]));
        let seq = i as i64 + 1;
        let n = sender.len();
        let log = &mut self.log;
        put_head(log, frame);
        put_u32(log, VARIANT_FIXED + HELD_FIXED + n + ID_SIZE + TICKET_SIZE);
        let change = log.len();
        log.push(HELD);
        put_u32(log, VARIANT_FIXED);
        put_u16(log, HELD_COUNT);
        put_u32(log, HELD_FIXED);
        put_u32(log, HELD_FIXED + n);
        put_u32(log, HELD_FIXED + n + ID_SIZE);
        log.extend_from_slice(sender);
        put_id(log, MACHINE, key, LIFE, seq);
        put_id(log, MACHINE, key, LIFE, seq);
        put_i64(log, TIMER_IDX);
        let end = log.len();
        put_u32(log, AFTER_FIXED + TICKET_SIZE);
        log.push(AFTER);
        put_i64(log, TIMER_NANOS);
        put_u32(log, AFTER_FIXED);
        put_id(log, MACHINE, key, LIFE, seq);
        put_i64(log, TIMER_IDX);
        put_u32(log, 1 + ID_SIZE);
        log.push(OUTCOME);
        put_id(log, MACHINE, key, LIFE, seq);
        state.clear();
        state.extend_from_slice(&log[..2]);
        state.extend_from_slice(&log[change..end]);
        black_box(&*state);
        black_box(&self.log);
        black_box(sum)
    }

    fn step_confirm(&mut self, i: usize) -> u64 {
        let frame = self.confirm_frames[i].as_slice();
        let ((a, e), token) = admit_confirm(frame).expect(ADMITTED);
        let c = &frame[2..];
        let state = &mut self.slots[i];
        assert!(state[2] == HELD, "{HELD_STATE}");
        let h = &state[2 + VARIANT_FIXED..];
        let hold_at = u32_at(h, 6);
        let timer_at = u32_at(h, 10);
        let holder = &h[HELD_FIXED..hold_at];
        let hold = &h[hold_at..timer_at];
        let timer = &h[timer_at..];
        let mut sum = fold_id(0, c, token);
        sum = fold_text(sum, &c[a..e]);
        sum = fold_text(sum, holder);
        sum = fold_id(sum, hold, OFFSET + u32_at(hold, 0));
        let n = holder.len();
        let log = &mut self.log;
        put_head(log, frame);
        put_u32(log, VARIANT_FIXED + BOOKED_FIXED + n + hold.len());
        let change = log.len();
        log.push(BOOKED);
        put_u32(log, VARIANT_FIXED);
        put_u16(log, BOOKED_COUNT);
        put_u32(log, BOOKED_FIXED);
        put_u32(log, BOOKED_FIXED + n);
        log.extend_from_slice(holder);
        log.extend_from_slice(hold);
        let end = log.len();
        put_u32(log, VARIANT_FIXED + timer.len());
        log.push(CANCEL);
        put_u32(log, VARIANT_FIXED);
        log.extend_from_slice(timer);
        put_u32(log, 1);
        log.push(OUTCOME);
        state.clear();
        state.extend_from_slice(&log[..2]);
        state.extend_from_slice(&log[change..end]);
        black_box(&*state);
        black_box(&self.log);
        black_box(sum)
    }

    fn step_wide(&mut self, i: usize) -> u64 {
        let frame = self.wide_frames[i].as_slice();
        admit_wide(frame).expect(ADMITTED);
        let state = &mut self.wides[i];
        let at = 2 + COUNT;
        let sum = fold_wide(fold_wide(0, &frame[2 + CMD_END..]), &state[at..]);
        let new = i64_at(state, at).wrapping_add(1);
        let log = &mut self.log;
        put_head(log, frame);
        put_field(log, WIDE_INT, new);
        set_i64(state, at, new);
        black_box(&*state);
        black_box(&self.log);
        black_box(sum)
    }

    fn step_varied(&mut self, i: usize) -> u64 {
        let frame = self.varied_frames[i].as_slice();
        let p = admit_varied(frame).expect(ADMITTED);
        let c = &frame[2..];
        let state = &mut self.varieds[i];
        let s = &state[2..];
        let text = (COUNT + VARIED_SIZE, u32_at(s, COUNT + OFFSET));
        let res = u32_at(s, COUNT + VARIED_RES);
        let kind = u32_at(s, COUNT + VARIED_KIND);
        let at = COUNT + VARIED_INTS;
        let mut sum = fold_varied(0, c, p[0], p[5].0, p[6].0, CMD_END + VARIED_INTS);
        sum = fold_varied(sum, s, text, res, kind, at);
        let new = i64_at(s, at).wrapping_add(1);
        let log = &mut self.log;
        put_head(log, frame);
        put_field(log, VARIED_INT, new);
        set_i64(state, 2 + at, new);
        black_box(&*state);
        black_box(&self.log);
        black_box(sum)
    }

    fn step_person(&mut self, i: usize) -> u64 {
        let frame = self.person_frames[i].as_slice();
        admit_person(frame, &self.pad, &mut self.log).expect(ADMITTED);
        let c = &frame[2..];
        let state = &mut self.persons[i];
        let s = &state[2..];
        let rest = PERSON_IN_REST;
        let visits = COUNT + SEALED_VISITS;
        let mut sum = fold_person(0, c, CMD_END, rest, rest + 2 * INT);
        sum = fold_person(sum, s, COUNT + SEALED_ID, visits, visits + 2 * INT);
        let new = i64_at(s, visits).wrapping_add(1);
        put_field(&mut self.log, PERSON_VISITS, new);
        set_i64(state, 2 + visits, new);
        black_box(&*state);
        black_box(&self.log);
        black_box(sum)
    }

    fn frame(&self, kind: InputKind, i: usize) -> &[u8] {
        match kind {
            InputKind::Hold => &self.hold_frames[i],
            InputKind::Confirm => &self.confirm_frames[i],
            InputKind::Wide => &self.wide_frames[i],
            InputKind::Varied => &self.varied_frames[i],
            InputKind::Person => &self.person_frames[i],
        }
    }

    fn log(&self) -> &[u8] {
        &self.log
    }

    fn state(&self, group: Group, i: usize) -> State {
        let state = match group {
            Group::Booking => frame(&self.slots[i]).and_then(slot_state).map(State::Slot),
            Group::Wide => wide_state(&self.wides[i]).map(State::Wide),
            Group::Varied => varied_state(&self.varieds[i]).map(State::Varied),
            Group::Personal => person_state(&self.persons[i]).map(|p| State::Person(Box::new(p))),
        };
        state.expect(STATE_FRAME)
    }

    fn admits(&mut self, kind: InputKind, frame: &[u8]) -> bool {
        match kind {
            InputKind::Hold => admit_hold(frame).is_some(),
            InputKind::Confirm => admit_confirm(frame).is_some(),
            InputKind::Wide => admit_wide(frame).is_some(),
            InputKind::Varied => admit_varied(frame).is_some(),
            InputKind::Person => admit_person(frame, &self.pad, &mut self.log).is_some(),
        }
    }

    fn encode(input: &Input) -> Option<Vec<u8>> {
        let mut b = start_frame();
        let start = b.len();
        match input {
            Input::Hold(h) => {
                put_u16(&mut b, HOLD_COUNT);
                b.extend_from_slice(&h.cmd.0);
                put_i64(&mut b, h.key);
                let sender = slot(&mut b);
                put_i64(&mut b, h.now);
                part(&mut b, start, sender);
                b.extend_from_slice(h.sender.as_bytes());
            }
            Input::Confirm(h) => {
                put_u16(&mut b, CONFIRM_COUNT);
                b.extend_from_slice(&h.cmd.0);
                put_i64(&mut b, h.key);
                let sender = slot(&mut b);
                put_i64(&mut b, h.now);
                let token = slot(&mut b);
                part(&mut b, start, sender);
                b.extend_from_slice(h.sender.as_bytes());
                part(&mut b, start, token);
                let t = &h.token;
                put_id(&mut b, &t.machine, t.key, t.life, t.seq);
            }
            Input::Wide(w) => {
                put_u16(&mut b, WIDE_IN_COUNT);
                b.extend_from_slice(&w.cmd.0);
                put_wide(&mut b, &w.wide);
            }
            Input::Varied(v) => {
                put_u16(&mut b, VARIED_IN_COUNT);
                b.extend_from_slice(&v.cmd.0);
                put_varied(&mut b, start, &v.varied);
            }
            Input::Person(p) => {
                put_u16(&mut b, PERSON_IN_COUNT);
                b.extend_from_slice(&p.cmd.0);
                put_i64(&mut b, p.id);
                let texts: [usize; 3] = std::array::from_fn(|_| slot(&mut b));
                put_i64(&mut b, p.visits);
                put_i64(&mut b, p.score);
                put_i64(&mut b, p.since);
                for (at, t) in texts.into_iter().zip([&p.name, &p.email, &p.phone]) {
                    part(&mut b, start, at);
                    b.extend_from_slice(t.as_bytes());
                }
            }
        }
        if b.len() as u64 >= LIMIT {
            return None;
        }
        Some(b)
    }

    fn decode(kind: InputKind, frame: &[u8]) -> Option<Input> {
        match kind {
            InputKind::Hold => hold_in(frame).map(Input::Hold),
            InputKind::Confirm => confirm_in(frame).map(Input::Confirm),
            InputKind::Wide => wide_in(frame).map(Input::Wide),
            InputKind::Varied => varied_in(frame).map(Input::Varied),
            InputKind::Person => person_in(frame).map(Input::Person),
        }
    }

    fn decode_log(kind: InputKind, record: &[u8]) -> Option<Log> {
        let r = frame(record)?;
        let (input, r) = piece(r)?;
        let (change, r) = piece(r)?;
        let (outputs, r) = piece(r)?;
        let (decision, r) = piece(r)?;
        if !r.is_empty() {
            return None;
        }
        let input = match kind {
            InputKind::Hold => LogInput::Hold(hold_in(input)?),
            InputKind::Confirm => LogInput::Confirm(confirm_in(input)?),
            InputKind::Wide => LogInput::Wide(wide_in(input)?),
            InputKind::Varied => LogInput::Varied(varied_in(input)?),
            InputKind::Person => LogInput::Person(Box::new(admitted(input)?)),
        };
        let change = match kind.group() {
            Group::Booking => Change::State(slot_state(change)?),
            Group::Wide => Change::Fields(fields(change, |k| matches!(k, 0..=13))?),
            Group::Varied => Change::Fields(fields(change, |k| matches!(k, 7..=10))?),
            Group::Personal => Change::Fields(fields(change, |k| matches!(k, 0 | 4..=6))?),
        };
        let outputs = if outputs.is_empty() {
            Vec::new()
        } else {
            vec![output(outputs)?]
        };
        let decision = match (decision.split_first()?, kind) {
            ((&OUTCOME, token), InputKind::Hold) => Decision::Token(step_id(token)?),
            ((&OUTCOME, []), _) => Decision::Unit,
            _ => return None,
        };
        Some(Log {
            input,
            change,
            outputs,
            decision,
        })
    }

    fn refused(corpus: &Corpus) -> Vec<Refused> {
        let mut out = Vec::new();

        let kind = InputKind::Hold;
        let f = Self::encode(&input(corpus, kind, 0)).expect(FITS);
        refuse_frame(&mut out, kind, &f, HOLD_COUNT, HOLD_FIXED);
        refuse_offsets(&mut out, kind, &f, &[SENDER], HOLD_FIXED);
        refuse(
            &mut out,
            kind,
            "text-utf8",
            with(&f, 2 + HOLD_FIXED, &[0xFF]),
        );

        let kind = InputKind::Confirm;
        let f = Self::encode(&input(corpus, kind, 0)).expect(FITS);
        refuse_frame(&mut out, kind, &f, CONFIRM_COUNT, CONFIRM_FIXED);
        refuse_offsets(&mut out, kind, &f, &[SENDER, TOKEN], CONFIRM_FIXED);
        refuse(
            &mut out,
            kind,
            "text-utf8",
            with(&f, 2 + CONFIRM_FIXED, &[0xFF]),
        );
        let name = 2 + u32_at(&f, 2 + TOKEN) + OFFSET;
        refuse(&mut out, kind, "machine-name", with(&f, name, b"s"));
        refuse(&mut out, kind, "trailing-byte", grown(&f, &[0]));

        let kind = InputKind::Wide;
        let f = Self::encode(&input(corpus, kind, 0)).expect(FITS);
        let at = 2 + CMD_END;
        refuse_frame(&mut out, kind, &f, WIDE_IN_COUNT, CMD_END + WIDE_SIZE);
        refuse(&mut out, kind, "enum-tag", with(&f, at + WIDE_FLAGS, &[4]));
        refuse(&mut out, kind, "bool-byte", with(&f, at + WIDE_BOOLS, &[2]));
        let nan = (CANONICAL_NAN | 1).to_le_bytes();
        refuse(
            &mut out,
            kind,
            "nan-pattern",
            with(&f, at + WIDE_FLOATS, &nan),
        );
        let big = (DECIMAL_MAX + 1).to_le_bytes();
        refuse(
            &mut out,
            kind,
            "decimal-range",
            with(&f, at + WIDE_MONEY, &big),
        );
        refuse(&mut out, kind, "trailing-byte", grown(&f, &[0]));

        let kind = InputKind::Varied;
        let fixed = CMD_END + VARIED_SIZE;
        let first = |test: fn(&Varied) -> bool| {
            let i = (0..N)
                .find(|&i| test(&corpus.varied[i].varied))
                .expect("a VariedIn value of the needed form");
            Self::encode(&input(corpus, kind, i)).expect(FITS)
        };
        let f = first(|v| !v.texts[0].is_empty());
        refuse_frame(&mut out, kind, &f, VARIED_IN_COUNT, fixed);
        let slots: [usize; 7] = std::array::from_fn(|k| CMD_END + k * OFFSET);
        refuse_offsets(&mut out, kind, &f, &slots, fixed);
        refuse(&mut out, kind, "text-utf8", with(&f, 2 + fixed, &[0xFF]));
        let tag = |slot: usize| 2 + u32_at(&f, 2 + CMD_END + slot);
        refuse(
            &mut out,
            kind,
            "option-tag",
            with(&f, tag(VARIED_OPT), &[2]),
        );
        refuse(
            &mut out,
            kind,
            "result-tag",
            with(&f, tag(VARIED_RES), &[2]),
        );
        refuse(&mut out, kind, "enum-tag", with(&f, tag(VARIED_KIND), &[3]));
        let f = first(|v| !matches!(v.kind, Kind::Tagged(_)));
        refuse(&mut out, kind, "trailing-byte", grown(&f, &[0]));

        let kind = InputKind::Person;
        let p = &corpus.person[0];
        let f = Self::encode(&input(corpus, kind, 0)).expect(FITS);
        refuse_frame(&mut out, kind, &f, PERSON_IN_COUNT, PERSON_IN_FIXED);
        refuse_offsets(&mut out, kind, &f, &PERSON_TEXTS, PERSON_IN_FIXED);
        refuse(
            &mut out,
            kind,
            "text-utf8",
            with(&f, 2 + PERSON_IN_FIXED, &[0xFF]),
        );
        let long = b"0".repeat(SEAL_TEXT + 1 - p.phone.len());
        refuse(&mut out, kind, "personal-text-long", grown(&f, &long));
        out
    }
}
