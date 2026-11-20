use std::hint::black_box;

use crate::types::{
    Admitted, Arm, BookedFields, Change, CommandId, ConfirmIn, Corpus, Decision, Flag, Group,
    HeldFields, HoldIn, Input, InputKind, KINDS, Kind, Log, LogInput, MACHINE, N, Output, Person,
    PersonIn, Refused, Sealed, SlotState, State, StepId, TIMER_NANOS, Ticket, Varied, VariedIn,
    Wide, WideIn, fold, fold_text, input, person_start, varied_start, wide_start,
};

const VERSION: u64 = 1;
const LIMIT: u64 = 1 << 32;
const CMD: usize = 34;
const SLOT: usize = 128;
const SEAL_TEXT: usize = 86;
const CANONICAL_NAN: u64 = 0x7FF8_0000_0000_0000;
const DECIMAL_MAX: u128 = 10u128.pow(38) - 1;
const HOLD_COUNT: u64 = 4;
const CONFIRM_COUNT: u64 = 5;
const WIDE_IN_COUNT: u64 = 25;
const VARIED_IN_COUNT: u64 = 12;
const PERSON_IN_COUNT: u64 = 8;
const HELD_COUNT: u64 = 3;
const BOOKED_COUNT: u64 = 2;
const ABSENT: u64 = 0;
const FREE: u64 = 1;
const HELD: u64 = 2;
const BOOKED: u64 = 3;
const AFTER: u64 = 0;
const CANCEL: u64 = 1;
const PLAIN: u64 = 0;
const TAGGED: u64 = 1;
const SCORED: u64 = 2;
const NONE: u8 = 0;
const SOME: u8 = 1;
const OK: u8 = 0;
const ERR: u8 = 1;
const OUTCOME: u8 = 0;
const LIFE: i64 = 1;
const TIMER_IDX: i64 = 0;
const WIDE_INT: u64 = 0;
const VARIED_INT: u64 = 7;
const PERSON_VISITS: u64 = 4;
const INT_MAX_SIZE: usize = 10;
const PERSON_INTS: usize = 4;
const PERSON_FIXED: usize = uleb_size(VERSION) + uleb_size(PERSON_IN_COUNT) + CMD + 3 * SLOT;
const PERSON_LEN_SIZE: usize = uleb_size((PERSON_FIXED + PERSON_INTS) as u64);
const PERSON_AT: usize = uleb_size(VERSION) + PERSON_LEN_SIZE;
const _: () =
    assert!(PERSON_LEN_SIZE == uleb_size((PERSON_FIXED + PERSON_INTS * INT_MAX_SIZE) as u64));
const ADMITTED: &str = "each corpus frame passes admission";
const FITS: &str = "each corpus value has a frame below 2^32 bytes";
const HELD_STATE: &str = "ConfirmIn i runs on the Held state of HoldIn i";

#[derive(Clone, Copy)]
struct Span {
    pos: usize,
    len: usize,
}

#[derive(Clone, Copy)]
struct StepS {
    machine: Span,
    key: i64,
    life: i64,
    seq: i64,
}

#[derive(Clone, Copy)]
struct TicketS {
    machine: Span,
    key: i64,
    life: i64,
    seq: i64,
    idx: i64,
}

#[derive(Clone, Copy)]
struct HeldS {
    holder: Span,
    hold: StepS,
    timer: TicketS,
}

#[derive(Clone, Copy)]
struct BookedS {
    owner: Span,
    hold: StepS,
}

#[derive(Clone, Copy)]
enum SlotS {
    Absent,
    Free,
    Held(HeldS),
    Booked(BookedS),
}

#[derive(Clone, Copy)]
enum KindS {
    Plain,
    Tagged(Span),
    Scored(i64, i64),
}

#[derive(Clone, Copy)]
struct VariedS {
    texts: [Span; 4],
    opt: Option<Span>,
    res: Result<i64, Span>,
    kind: KindS,
    ints: [i64; 4],
}

struct HoldA {
    key: i64,
    sender: Span,
    now: i64,
}

struct ConfirmA {
    key: i64,
    sender: Span,
    now: i64,
    token: StepS,
}

struct PersonA {
    id: i64,
    name: Span,
    email: Span,
    phone: Span,
    visits: i64,
    score: i64,
    since: i64,
}

#[derive(Clone)]
struct SlotInst {
    state: SlotS,
    buf: Vec<u8>,
}

#[derive(Clone)]
struct VariedInst {
    state: VariedS,
    buf: Vec<u8>,
}

pub struct ArmS {
    pad: [u8; SLOT],
    hold_frames: Vec<Vec<u8>>,
    confirm_frames: Vec<Vec<u8>>,
    wide_frames: Vec<Vec<u8>>,
    varied_frames: Vec<Vec<u8>>,
    person_frames: Vec<Vec<u8>>,
    slots: Vec<SlotInst>,
    slot_starts: Vec<SlotInst>,
    wides: Vec<Wide>,
    wide_starts: Vec<Wide>,
    varieds: Vec<VariedInst>,
    varied_starts: Vec<VariedInst>,
    persons: Vec<Person>,
    person_starts: Vec<Person>,
    log: Vec<u8>,
}

const fn uleb_size(v: u64) -> usize {
    ((64 - (v | 1).leading_zeros()).div_ceil(7)) as usize
}

fn zigzag(n: i64) -> u64 {
    ((n << 1) ^ (n >> 63)) as u64
}

fn unzigzag(v: u64) -> i64 {
    (v >> 1) as i64 ^ -((v & 1) as i64)
}

fn zigzag128(c: i128) -> u128 {
    ((c << 1) ^ (c >> 127)) as u128
}

fn unzigzag128(v: u128) -> i128 {
    (v >> 1) as i128 ^ -((v & 1) as i128)
}

fn int_size(n: i64) -> usize {
    uleb_size(zigzag(n))
}

fn text_size(len: usize) -> usize {
    uleb_size(len as u64) + len
}

fn step_size(name: &[u8], key: i64, life: i64, seq: i64) -> usize {
    text_size(name.len()) + int_size(key) + int_size(life) + int_size(seq)
}

fn put_uleb(out: &mut Vec<u8>, mut v: u64) {
    while v >= 0x80 {
        out.push(v as u8 | 0x80);
        v >>= 7;
    }
    out.push(v as u8);
}

fn put_uleb128(out: &mut Vec<u8>, mut v: u128) {
    while v >= 0x80 {
        out.push(v as u8 | 0x80);
        v >>= 7;
    }
    out.push(v as u8);
}

fn patch_uleb(out: &mut [u8], mut v: u64) {
    let last = out.len() - 1;
    for (j, b) in out.iter_mut().enumerate() {
        *b = v as u8 & 0x7f | if j < last { 0x80 } else { 0 };
        v >>= 7;
    }
}

fn put_int(out: &mut Vec<u8>, n: i64) {
    put_uleb(out, zigzag(n));
}

fn put_text(out: &mut Vec<u8>, bytes: &[u8]) {
    put_uleb(out, bytes.len() as u64);
    out.extend_from_slice(bytes);
}

fn put_step(out: &mut Vec<u8>, name: &[u8], key: i64, life: i64, seq: i64) {
    put_text(out, name);
    put_int(out, key);
    put_int(out, life);
    put_int(out, seq);
}

fn put_ticket(out: &mut Vec<u8>, name: &[u8], key: i64, life: i64, seq: i64, idx: i64) {
    put_step(out, name, key, life, seq);
    put_int(out, idx);
}

fn put_head(log: &mut Vec<u8>, frame: &[u8]) {
    log.clear();
    put_uleb(log, VERSION);
    put_uleb(log, frame.len() as u64);
    log.extend_from_slice(frame);
}

fn put_change(log: &mut Vec<u8>, index: u64, value: i64) {
    put_uleb(log, (uleb_size(index) + int_size(value)) as u64);
    put_uleb(log, index);
    put_int(log, value);
}

fn put_unit_tail(log: &mut Vec<u8>) {
    put_uleb(log, 0);
    put_uleb(log, 1);
    log.push(OUTCOME);
}

impl Span {
    fn of(self, b: &[u8]) -> &[u8] {
        &b[self.pos..self.pos + self.len]
    }
}

fn keep(buf: &mut Vec<u8>, bytes: &[u8]) -> Span {
    let span = Span {
        pos: buf.len(),
        len: bytes.len(),
    };
    buf.extend_from_slice(bytes);
    span
}

fn string(b: &[u8], span: Span) -> String {
    String::from_utf8_lossy(span.of(b)).into_owned()
}

fn step_of(b: &[u8], s: StepS) -> StepId {
    StepId {
        machine: string(b, s.machine),
        key: s.key,
        life: s.life,
        seq: s.seq,
    }
}

fn ticket_of(b: &[u8], t: TicketS) -> Ticket {
    Ticket {
        machine: string(b, t.machine),
        key: t.key,
        life: t.life,
        seq: t.seq,
        idx: t.idx,
    }
}

fn keep_step(buf: &mut Vec<u8>, s: &StepId) -> StepS {
    StepS {
        machine: keep(buf, s.machine.as_bytes()),
        key: s.key,
        life: s.life,
        seq: s.seq,
    }
}

fn keep_ticket(buf: &mut Vec<u8>, t: &Ticket) -> TicketS {
    TicketS {
        machine: keep(buf, t.machine.as_bytes()),
        key: t.key,
        life: t.life,
        seq: t.seq,
        idx: t.idx,
    }
}

impl SlotS {
    fn tag(self) -> u64 {
        match self {
            SlotS::Absent => ABSENT,
            SlotS::Free => FREE,
            SlotS::Held(_) => HELD,
            SlotS::Booked(_) => BOOKED,
        }
    }
}

impl SlotInst {
    fn load(s: &SlotState) -> SlotInst {
        let mut buf = Vec::new();
        let state = match s {
            SlotState::Absent => SlotS::Absent,
            SlotState::Free => SlotS::Free,
            SlotState::Held(h) => SlotS::Held(HeldS {
                holder: keep(&mut buf, h.holder.as_bytes()),
                hold: keep_step(&mut buf, &h.hold),
                timer: keep_ticket(&mut buf, &h.timer),
            }),
            SlotState::Booked(b) => SlotS::Booked(BookedS {
                owner: keep(&mut buf, b.owner.as_bytes()),
                hold: keep_step(&mut buf, &b.hold),
            }),
        };
        SlotInst { state, buf }
    }

    fn value(&self) -> SlotState {
        let b = &self.buf;
        match self.state {
            SlotS::Absent => SlotState::Absent,
            SlotS::Free => SlotState::Free,
            SlotS::Held(h) => SlotState::Held(HeldFields {
                holder: string(b, h.holder),
                hold: step_of(b, h.hold),
                timer: ticket_of(b, h.timer),
            }),
            SlotS::Booked(k) => SlotState::Booked(BookedFields {
                owner: string(b, k.owner),
                hold: step_of(b, k.hold),
            }),
        }
    }

    fn restore(&mut self, from: &SlotInst) {
        self.state = from.state;
        self.buf.clear();
        self.buf.extend_from_slice(&from.buf);
    }
}

impl VariedInst {
    fn load(v: &Varied) -> VariedInst {
        let mut buf = Vec::new();
        let texts = std::array::from_fn(|j| keep(&mut buf, v.texts[j].as_bytes()));
        let opt = v.opt.as_ref().map(|t| keep(&mut buf, t.as_bytes()));
        let res = match &v.res {
            Ok(n) => Ok(*n),
            Err(t) => Err(keep(&mut buf, t.as_bytes())),
        };
        let kind = match &v.kind {
            Kind::Plain => KindS::Plain,
            Kind::Tagged(t) => KindS::Tagged(keep(&mut buf, t.as_bytes())),
            Kind::Scored(a, b) => KindS::Scored(*a, *b),
        };
        VariedInst {
            state: VariedS {
                texts,
                opt,
                res,
                kind,
                ints: v.ints,
            },
            buf,
        }
    }

    fn restore(&mut self, from: &VariedInst) {
        self.state = from.state;
        self.buf.clear();
        self.buf.extend_from_slice(&from.buf);
    }
}

fn varied_of(b: &[u8], v: &VariedS) -> Varied {
    Varied {
        texts: v.texts.map(|t| string(b, t)),
        opt: v.opt.map(|t| string(b, t)),
        res: v.res.map_err(|t| string(b, t)),
        kind: match v.kind {
            KindS::Plain => Kind::Plain,
            KindS::Tagged(t) => Kind::Tagged(string(b, t)),
            KindS::Scored(x, y) => Kind::Scored(x, y),
        },
        ints: v.ints,
    }
}

struct Reader<'a> {
    b: &'a [u8],
    p: usize,
}

impl<'a> Reader<'a> {
    fn new(b: &'a [u8]) -> Option<Reader<'a>> {
        ((b.len() as u64) < LIMIT).then_some(Reader { b, p: 0 })
    }

    fn bytes(&mut self, n: usize) -> Option<&'a [u8]> {
        let end = self.p.checked_add(n)?;
        let s = self.b.get(self.p..end)?;
        self.p = end;
        Some(s)
    }

    fn byte(&mut self) -> Option<u8> {
        let v = *self.b.get(self.p)?;
        self.p += 1;
        Some(v)
    }

    fn uleb(&mut self) -> Option<u64> {
        let mut v = 0u64;
        let mut shift = 0u32;
        loop {
            let b = self.byte()?;
            let low = u64::from(b & 0x7f);
            if shift == 63 && low > 1 {
                return None;
            }
            v |= low << shift;
            if b & 0x80 == 0 {
                return (b != 0 || shift == 0).then_some(v);
            }
            shift += 7;
            if shift > 63 {
                return None;
            }
        }
    }

    fn uleb128(&mut self) -> Option<u128> {
        let mut v = 0u128;
        let mut shift = 0u32;
        loop {
            let b = self.byte()?;
            let low = u128::from(b & 0x7f);
            if shift == 126 && low > 3 {
                return None;
            }
            v |= low << shift;
            if b & 0x80 == 0 {
                return (b != 0 || shift == 0).then_some(v);
            }
            shift += 7;
            if shift > 126 {
                return None;
            }
        }
    }

    fn head(&mut self, count: u64) -> Option<()> {
        (self.uleb()? == VERSION && self.uleb()? == count).then_some(())
    }

    fn count(&mut self, count: u64) -> Option<()> {
        (self.uleb()? == count).then_some(())
    }

    fn end(&self) -> Option<()> {
        (self.p == self.b.len()).then_some(())
    }

    fn int(&mut self) -> Option<i64> {
        Some(unzigzag(self.uleb()?))
    }

    fn decimal(&mut self) -> Option<i128> {
        let c = unzigzag128(self.uleb128()?);
        (c.unsigned_abs() <= DECIMAL_MAX).then_some(c)
    }

    fn float(&mut self) -> Option<u64> {
        let v = u64::from_le_bytes(self.bytes(8)?.try_into().ok()?);
        (!f64::from_bits(v).is_nan() || v == CANONICAL_NAN).then_some(v)
    }

    fn boolean(&mut self) -> Option<bool> {
        match self.byte()? {
            0 => Some(false),
            1 => Some(true),
            _ => None,
        }
    }

    fn flag(&mut self) -> Option<Flag> {
        match self.uleb()? {
            0 => Some(Flag::A),
            1 => Some(Flag::B),
            2 => Some(Flag::C),
            3 => Some(Flag::D),
            _ => None,
        }
    }

    fn span(&mut self) -> Option<Span> {
        let len = self.uleb()?;
        if len >= LIMIT {
            return None;
        }
        let pos = self.p;
        let len = len as usize;
        self.bytes(len)?;
        Some(Span { pos, len })
    }

    fn part(&mut self) -> Option<&'a [u8]> {
        let span = self.span()?;
        Some(span.of(self.b))
    }

    fn text(&mut self) -> Option<Span> {
        let span = self.span()?;
        std::str::from_utf8(span.of(self.b)).ok()?;
        Some(span)
    }

    fn name(&mut self) -> Option<Span> {
        let span = self.span()?;
        (span.of(self.b) == MACHINE.as_bytes()).then_some(span)
    }

    fn step(&mut self) -> Option<StepS> {
        Some(StepS {
            machine: self.name()?,
            key: self.int()?,
            life: self.int()?,
            seq: self.int()?,
        })
    }

    fn ticket(&mut self) -> Option<TicketS> {
        Some(TicketS {
            machine: self.name()?,
            key: self.int()?,
            life: self.int()?,
            seq: self.int()?,
            idx: self.int()?,
        })
    }

    fn copy_int(&mut self, log: &mut Vec<u8>) -> Option<i64> {
        let at = self.p;
        let v = self.int()?;
        log.extend_from_slice(&self.b[at..self.p]);
        Some(v)
    }

    fn seal(&mut self, log: &mut Vec<u8>, pad: &[u8; SLOT]) -> Option<Span> {
        let span = self.text()?;
        if span.len > SEAL_TEXT {
            return None;
        }
        log.extend_from_slice(&(span.len as u16).to_le_bytes());
        log.extend_from_slice(span.of(self.b));
        log.extend_from_slice(&pad[2 + span.len..]);
        Some(span)
    }
}

fn admit_hold(frame: &[u8]) -> Option<HoldA> {
    let mut r = Reader::new(frame)?;
    r.head(HOLD_COUNT)?;
    r.bytes(CMD)?;
    let a = HoldA {
        key: r.int()?,
        sender: r.text()?,
        now: r.int()?,
    };
    r.end()?;
    Some(a)
}

fn admit_confirm(frame: &[u8]) -> Option<ConfirmA> {
    let mut r = Reader::new(frame)?;
    r.head(CONFIRM_COUNT)?;
    r.bytes(CMD)?;
    let a = ConfirmA {
        key: r.int()?,
        sender: r.text()?,
        now: r.int()?,
        token: r.step()?,
    };
    r.end()?;
    Some(a)
}

fn admit_wide(frame: &[u8]) -> Option<Wide> {
    let mut r = Reader::new(frame)?;
    r.head(WIDE_IN_COUNT)?;
    r.bytes(CMD)?;
    let mut ints = [0i64; 14];
    for x in &mut ints {
        *x = r.int()?;
    }
    let mut flags = [Flag::A; 4];
    for f in &mut flags {
        *f = r.flag()?;
    }
    let mut bools = [false; 2];
    for b in &mut bools {
        *b = r.boolean()?;
    }
    let mut floats = [0u64; 3];
    for f in &mut floats {
        *f = r.float()?;
    }
    let money = r.decimal()?;
    r.end()?;
    Some(Wide {
        ints,
        flags,
        bools,
        floats,
        money,
    })
}

fn admit_varied(frame: &[u8]) -> Option<VariedS> {
    let mut r = Reader::new(frame)?;
    r.head(VARIED_IN_COUNT)?;
    r.bytes(CMD)?;
    let mut texts = [Span { pos: 0, len: 0 }; 4];
    for t in &mut texts {
        *t = r.text()?;
    }
    let opt = match r.byte()? {
        NONE => None,
        SOME => Some(r.text()?),
        _ => return None,
    };
    let res = match r.byte()? {
        OK => Ok(r.int()?),
        ERR => Err(r.text()?),
        _ => return None,
    };
    let kind = match r.uleb()? {
        PLAIN => KindS::Plain,
        TAGGED => KindS::Tagged(r.text()?),
        SCORED => KindS::Scored(r.int()?, r.int()?),
        _ => return None,
    };
    let mut ints = [0i64; 4];
    for x in &mut ints {
        *x = r.int()?;
    }
    r.end()?;
    Some(VariedS {
        texts,
        opt,
        res,
        kind,
        ints,
    })
}

fn admit_person(frame: &[u8], pad: &[u8; SLOT], log: &mut Vec<u8>) -> Option<PersonA> {
    let mut r = Reader::new(frame)?;
    r.head(PERSON_IN_COUNT)?;
    log.clear();
    log.extend_from_slice(&[0; PERSON_AT]);
    put_uleb(log, VERSION);
    put_uleb(log, PERSON_IN_COUNT);
    log.extend_from_slice(r.bytes(CMD)?);
    let a = PersonA {
        id: r.copy_int(log)?,
        name: r.seal(log, pad)?,
        email: r.seal(log, pad)?,
        phone: r.seal(log, pad)?,
        visits: r.copy_int(log)?,
        score: r.copy_int(log)?,
        since: r.copy_int(log)?,
    };
    r.end()?;
    Some(a)
}

fn parse_person(frame: &[u8]) -> Option<PersonA> {
    let mut r = Reader::new(frame)?;
    r.head(PERSON_IN_COUNT)?;
    r.bytes(CMD)?;
    let a = PersonA {
        id: r.int()?,
        name: r.text()?,
        email: r.text()?,
        phone: r.text()?,
        visits: r.int()?,
        score: r.int()?,
        since: r.int()?,
    };
    r.end()?;
    Some(a)
}

fn command(frame: &[u8]) -> Option<CommandId> {
    let mut r = Reader::new(frame)?;
    r.uleb()?;
    r.uleb()?;
    Some(CommandId(r.bytes(CMD)?.try_into().ok()?))
}

fn fold_step(c: u64, key: i64, life: i64, seq: i64) -> u64 {
    fold(fold(fold(c, key as u64), life as u64), seq as u64)
}

fn fold_wide(c: u64, w: &Wide) -> u64 {
    let c = fold(c, w.ints[0] as u64);
    let c = fold(c, u64::from(w.bools[0]));
    let c = fold(c, w.floats[0]);
    let c = fold(c, w.money as u64);
    fold(c, (w.money >> 64) as u64)
}

fn fold_varied(c: u64, b: &[u8], v: &VariedS) -> u64 {
    let c = fold_text(c, v.texts[0].of(b));
    let c = fold(
        c,
        match v.res {
            Ok(_) => u64::from(OK),
            Err(_) => u64::from(ERR),
        },
    );
    let c = fold(
        c,
        match v.kind {
            KindS::Plain => PLAIN,
            KindS::Tagged(_) => TAGGED,
            KindS::Scored(_, _) => SCORED,
        },
    );
    fold(c, v.ints[0] as u64)
}

fn fold_person(c: u64, id: i64, visits: i64, since: i64) -> u64 {
    fold(fold(fold(c, id as u64), visits as u64), since as u64)
}

fn decode_slot(b: &[u8]) -> Option<SlotState> {
    let mut r = Reader::new(b)?;
    let s = match r.uleb()? {
        ABSENT => SlotState::Absent,
        FREE => SlotState::Free,
        HELD => {
            r.count(HELD_COUNT)?;
            SlotState::Held(HeldFields {
                holder: string(b, r.text()?),
                hold: step_of(b, r.step()?),
                timer: ticket_of(b, r.ticket()?),
            })
        }
        BOOKED => {
            r.count(BOOKED_COUNT)?;
            SlotState::Booked(BookedFields {
                owner: string(b, r.text()?),
                hold: step_of(b, r.step()?),
            })
        }
        _ => return None,
    };
    r.end()?;
    Some(s)
}

fn decode_fields(b: &[u8]) -> Option<Vec<(u64, i64)>> {
    let mut r = Reader::new(b)?;
    let mut fields = Vec::new();
    while r.p < b.len() {
        fields.push((r.uleb()?, r.int()?));
    }
    Some(fields)
}

fn decode_outputs(b: &[u8]) -> Option<Vec<Output>> {
    let mut r = Reader::new(b)?;
    let mut outputs = Vec::new();
    while r.p < b.len() {
        outputs.push(match r.uleb()? {
            AFTER => Output::After(r.int()?, ticket_of(b, r.ticket()?)),
            CANCEL => Output::Cancel(ticket_of(b, r.ticket()?)),
            _ => return None,
        });
    }
    Some(outputs)
}

fn decode_admitted(b: &[u8]) -> Option<Admitted> {
    let mut r = Reader::new(b)?;
    r.head(PERSON_IN_COUNT)?;
    let cmd = CommandId(r.bytes(CMD)?.try_into().ok()?);
    let a = Admitted {
        cmd,
        person: Person {
            id: r.int()?,
            name: Sealed(r.bytes(SLOT)?.try_into().ok()?),
            email: Sealed(r.bytes(SLOT)?.try_into().ok()?),
            phone: Sealed(r.bytes(SLOT)?.try_into().ok()?),
            visits: r.int()?,
            score: r.int()?,
            since: r.int()?,
        },
    };
    r.end()?;
    Some(a)
}

fn decode_decision(kind: InputKind, b: &[u8]) -> Option<Decision> {
    let mut r = Reader::new(b)?;
    if r.byte()? != OUTCOME {
        return None;
    }
    let d = match kind {
        InputKind::Hold => Decision::Token(step_of(b, r.step()?)),
        _ => Decision::Unit,
    };
    r.end()?;
    Some(d)
}

fn splice(frame: &[u8], at: usize, old: usize, new: &[u8]) -> Vec<u8> {
    let mut f = frame[..at].to_vec();
    f.extend_from_slice(new);
    f.extend_from_slice(&frame[at + old..]);
    f
}

fn refuse(out: &mut Vec<Refused>, kind: InputKind, cause: &'static str, frame: Vec<u8>) {
    out.push(Refused { kind, cause, frame });
}

fn refuse_frame(out: &mut Vec<Refused>, kind: InputKind, f: &[u8], count: u64) {
    refuse(out, kind, "version", splice(f, 0, 1, &[2]));
    refuse(out, kind, "short-frame", f[..f.len() - 1].to_vec());
    refuse(out, kind, "trailing-byte", splice(f, f.len(), 0, &[0]));
    refuse(
        out,
        kind,
        "record-count-above",
        splice(f, 1, 1, &[count as u8 + 1]),
    );
    refuse(
        out,
        kind,
        "record-count-below",
        splice(f, 1, 1, &[count as u8 - 1]),
    );
}

fn refuse_int(out: &mut Vec<Refused>, kind: InputKind, f: &[u8], at: usize, n: i64) {
    let size = int_size(n);
    let mut long = f[at..at + size].to_vec();
    long[size - 1] |= 0x80;
    long.push(0);
    refuse(out, kind, "uleb-not-shortest", splice(f, at, size, &long));
    let mut range = vec![0x80; 9];
    range.push(0x02);
    refuse(out, kind, "uleb-range", splice(f, at, size, &range));
}

fn refuse_text(out: &mut Vec<Refused>, kind: InputKind, f: &[u8], at: usize, text: &str) {
    let first = at + uleb_size(text.len() as u64);
    refuse(out, kind, "text-utf8", splice(f, first, 1, &[0xFF]));
    let mut long = Vec::new();
    put_uleb(&mut long, LIMIT);
    refuse(
        out,
        kind,
        "text-length",
        splice(f, at, uleb_size(text.len() as u64), &long),
    );
}

fn cmd_end(count: u64) -> usize {
    uleb_size(VERSION) + uleb_size(count) + CMD
}

fn ints_size(ints: &[i64]) -> usize {
    ints.iter().map(|&n| int_size(n)).sum()
}

fn texts_size(texts: &[String]) -> usize {
    texts.iter().map(|t| text_size(t.len())).sum()
}

impl Arm for ArmS {
    const NAME: &'static str = "S";

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
        let slot_starts: Vec<SlotInst> = (0..N).map(|_| SlotInst::load(&SlotState::Free)).collect();
        let wide_starts: Vec<Wide> = (0..N).map(|i| wide_start(corpus, i)).collect();
        let varied_starts: Vec<VariedInst> = (0..N)
            .map(|i| VariedInst::load(&varied_start(corpus, i)))
            .collect();
        let person_starts: Vec<Person> = (0..N).map(|i| person_start(corpus, i)).collect();
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
        ArmS {
            pad: corpus.pad,
            hold_frames,
            confirm_frames,
            wide_frames,
            varied_frames,
            person_frames,
            slots: slot_starts.clone(),
            slot_starts,
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
        for (s, from) in self.slots.iter_mut().zip(&self.slot_starts) {
            s.restore(from);
        }
        for (w, from) in self.wides.iter_mut().zip(&self.wide_starts) {
            w.clone_from(from);
        }
        for (v, from) in self.varieds.iter_mut().zip(&self.varied_starts) {
            v.restore(from);
        }
        for (p, from) in self.persons.iter_mut().zip(&self.person_starts) {
            p.clone_from(from);
        }
    }

    fn step_hold(&mut self, i: usize) -> u64 {
        let frame = self.hold_frames[i].as_slice();
        let a = admit_hold(frame).expect(ADMITTED);
        let inst = &mut self.slots[i];
        let sender = a.sender.of(frame);
        let mut c = fold(0, a.key as u64);
        c = fold_text(c, sender);
        c = fold(c, a.now as u64);
        c = fold(c, inst.state.tag());
        let name = MACHINE.as_bytes();
        let seq = i as i64 + 1;
        let hold_size = step_size(name, a.key, LIFE, seq);
        let ticket_size = hold_size + int_size(TIMER_IDX);
        let log = &mut self.log;
        put_head(log, frame);
        put_uleb(
            log,
            (uleb_size(HELD)
                + uleb_size(HELD_COUNT)
                + text_size(sender.len())
                + hold_size
                + ticket_size) as u64,
        );
        put_uleb(log, HELD);
        put_uleb(log, HELD_COUNT);
        put_text(log, sender);
        put_step(log, name, a.key, LIFE, seq);
        put_ticket(log, name, a.key, LIFE, seq, TIMER_IDX);
        put_uleb(
            log,
            (uleb_size(AFTER) + int_size(TIMER_NANOS) + ticket_size) as u64,
        );
        put_uleb(log, AFTER);
        put_int(log, TIMER_NANOS);
        put_ticket(log, name, a.key, LIFE, seq, TIMER_IDX);
        put_uleb(log, (1 + hold_size) as u64);
        log.push(OUTCOME);
        put_step(log, name, a.key, LIFE, seq);
        inst.buf.clear();
        let holder = keep(&mut inst.buf, sender);
        let hold = keep(&mut inst.buf, name);
        let timer = keep(&mut inst.buf, name);
        inst.state = SlotS::Held(HeldS {
            holder,
            hold: StepS {
                machine: hold,
                key: a.key,
                life: LIFE,
                seq,
            },
            timer: TicketS {
                machine: timer,
                key: a.key,
                life: LIFE,
                seq,
                idx: TIMER_IDX,
            },
        });
        black_box(&*inst);
        black_box(&self.log);
        black_box(c)
    }

    fn step_confirm(&mut self, i: usize) -> u64 {
        let frame = self.confirm_frames[i].as_slice();
        let a = admit_confirm(frame).expect(ADMITTED);
        let inst = &mut self.slots[i];
        let SlotS::Held(h) = inst.state else {
            panic!("{HELD_STATE}");
        };
        let b = inst.buf.as_slice();
        let holder = h.holder.of(b);
        let hold_name = h.hold.machine.of(b);
        let timer_name = h.timer.machine.of(b);
        let mut c = fold_step(0, a.token.key, a.token.life, a.token.seq);
        c = fold_text(c, a.sender.of(frame));
        c = fold_text(c, holder);
        c = fold_step(c, h.hold.key, h.hold.life, h.hold.seq);
        let hold_size = step_size(hold_name, h.hold.key, h.hold.life, h.hold.seq);
        let ticket_size =
            step_size(timer_name, h.timer.key, h.timer.life, h.timer.seq) + int_size(h.timer.idx);
        let log = &mut self.log;
        put_head(log, frame);
        put_uleb(
            log,
            (uleb_size(BOOKED) + uleb_size(BOOKED_COUNT) + text_size(holder.len()) + hold_size)
                as u64,
        );
        put_uleb(log, BOOKED);
        put_uleb(log, BOOKED_COUNT);
        put_text(log, holder);
        put_step(log, hold_name, h.hold.key, h.hold.life, h.hold.seq);
        put_uleb(log, (uleb_size(CANCEL) + ticket_size) as u64);
        put_uleb(log, CANCEL);
        let t = h.timer;
        put_ticket(log, timer_name, t.key, t.life, t.seq, t.idx);
        put_uleb(log, 1);
        log.push(OUTCOME);
        inst.state = SlotS::Booked(BookedS {
            owner: h.holder,
            hold: h.hold,
        });
        inst.buf.truncate(h.hold.machine.pos + h.hold.machine.len);
        black_box(&*inst);
        black_box(&self.log);
        black_box(c)
    }

    fn step_wide(&mut self, i: usize) -> u64 {
        let frame = self.wide_frames[i].as_slice();
        let a = admit_wide(frame).expect(ADMITTED);
        let st = &mut self.wides[i];
        let c = fold_wide(fold_wide(0, &a), st);
        let new = st.ints[0].wrapping_add(1);
        let log = &mut self.log;
        put_head(log, frame);
        put_change(log, WIDE_INT, new);
        put_unit_tail(log);
        st.ints[0] = new;
        black_box(&*st);
        black_box(&self.log);
        black_box(c)
    }

    fn step_varied(&mut self, i: usize) -> u64 {
        let frame = self.varied_frames[i].as_slice();
        let a = admit_varied(frame).expect(ADMITTED);
        let inst = &mut self.varieds[i];
        let c = fold_varied(fold_varied(0, frame, &a), &inst.buf, &inst.state);
        let new = inst.state.ints[0].wrapping_add(1);
        let log = &mut self.log;
        put_head(log, frame);
        put_change(log, VARIED_INT, new);
        put_unit_tail(log);
        inst.state.ints[0] = new;
        black_box(&*inst);
        black_box(&self.log);
        black_box(c)
    }

    fn step_person(&mut self, i: usize) -> u64 {
        let frame = self.person_frames[i].as_slice();
        let a = admit_person(frame, &self.pad, &mut self.log).expect(ADMITTED);
        let st = &mut self.persons[i];
        let c = fold_person(
            fold_person(0, a.id, a.visits, a.since),
            st.id,
            st.visits,
            st.since,
        );
        let new = st.visits.wrapping_add(1);
        let log = &mut self.log;
        let part = (log.len() - PERSON_AT) as u64;
        patch_uleb(&mut log[..uleb_size(VERSION)], VERSION);
        patch_uleb(&mut log[uleb_size(VERSION)..PERSON_AT], part);
        put_change(log, PERSON_VISITS, new);
        put_unit_tail(log);
        st.visits = new;
        black_box(&*st);
        black_box(&self.log);
        black_box(c)
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
        match group {
            Group::Booking => State::Slot(self.slots[i].value()),
            Group::Wide => State::Wide(self.wides[i].clone()),
            Group::Varied => {
                let v = &self.varieds[i];
                State::Varied(varied_of(&v.buf, &v.state))
            }
            Group::Personal => State::Person(Box::new(self.persons[i].clone())),
        }
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
        let mut f = Vec::new();
        put_uleb(&mut f, VERSION);
        match input {
            Input::Hold(h) => {
                put_uleb(&mut f, HOLD_COUNT);
                f.extend_from_slice(&h.cmd.0);
                put_int(&mut f, h.key);
                put_text(&mut f, h.sender.as_bytes());
                put_int(&mut f, h.now);
            }
            Input::Confirm(c) => {
                put_uleb(&mut f, CONFIRM_COUNT);
                f.extend_from_slice(&c.cmd.0);
                put_int(&mut f, c.key);
                put_text(&mut f, c.sender.as_bytes());
                put_int(&mut f, c.now);
                let t = &c.token;
                put_step(&mut f, t.machine.as_bytes(), t.key, t.life, t.seq);
            }
            Input::Wide(w) => {
                put_uleb(&mut f, WIDE_IN_COUNT);
                f.extend_from_slice(&w.cmd.0);
                let w = &w.wide;
                for &n in &w.ints {
                    put_int(&mut f, n);
                }
                for &flag in &w.flags {
                    put_uleb(&mut f, flag as u64);
                }
                for &b in &w.bools {
                    f.push(u8::from(b));
                }
                for &x in &w.floats {
                    f.extend_from_slice(&x.to_le_bytes());
                }
                put_uleb128(&mut f, zigzag128(w.money));
            }
            Input::Varied(v) => {
                put_uleb(&mut f, VARIED_IN_COUNT);
                f.extend_from_slice(&v.cmd.0);
                let v = &v.varied;
                for t in &v.texts {
                    put_text(&mut f, t.as_bytes());
                }
                match &v.opt {
                    None => f.push(NONE),
                    Some(t) => {
                        f.push(SOME);
                        put_text(&mut f, t.as_bytes());
                    }
                }
                match &v.res {
                    Ok(n) => {
                        f.push(OK);
                        put_int(&mut f, *n);
                    }
                    Err(t) => {
                        f.push(ERR);
                        put_text(&mut f, t.as_bytes());
                    }
                }
                match &v.kind {
                    Kind::Plain => put_uleb(&mut f, PLAIN),
                    Kind::Tagged(t) => {
                        put_uleb(&mut f, TAGGED);
                        put_text(&mut f, t.as_bytes());
                    }
                    Kind::Scored(x, y) => {
                        put_uleb(&mut f, SCORED);
                        put_int(&mut f, *x);
                        put_int(&mut f, *y);
                    }
                }
                for &n in &v.ints {
                    put_int(&mut f, n);
                }
            }
            Input::Person(p) => {
                put_uleb(&mut f, PERSON_IN_COUNT);
                f.extend_from_slice(&p.cmd.0);
                put_int(&mut f, p.id);
                put_text(&mut f, p.name.as_bytes());
                put_text(&mut f, p.email.as_bytes());
                put_text(&mut f, p.phone.as_bytes());
                put_int(&mut f, p.visits);
                put_int(&mut f, p.score);
                put_int(&mut f, p.since);
            }
        }
        if f.len() as u64 >= LIMIT {
            return None;
        }
        Some(f)
    }

    fn decode(kind: InputKind, frame: &[u8]) -> Option<Input> {
        let cmd = command(frame);
        Some(match kind {
            InputKind::Hold => {
                let a = admit_hold(frame)?;
                Input::Hold(HoldIn {
                    cmd: cmd?,
                    key: a.key,
                    sender: string(frame, a.sender),
                    now: a.now,
                })
            }
            InputKind::Confirm => {
                let a = admit_confirm(frame)?;
                Input::Confirm(ConfirmIn {
                    cmd: cmd?,
                    key: a.key,
                    sender: string(frame, a.sender),
                    now: a.now,
                    token: step_of(frame, a.token),
                })
            }
            InputKind::Wide => {
                let wide = admit_wide(frame)?;
                Input::Wide(WideIn { cmd: cmd?, wide })
            }
            InputKind::Varied => {
                let a = admit_varied(frame)?;
                Input::Varied(VariedIn {
                    cmd: cmd?,
                    varied: varied_of(frame, &a),
                })
            }
            InputKind::Person => {
                let a = parse_person(frame)?;
                Input::Person(PersonIn {
                    cmd: cmd?,
                    id: a.id,
                    name: string(frame, a.name),
                    email: string(frame, a.email),
                    phone: string(frame, a.phone),
                    visits: a.visits,
                    score: a.score,
                    since: a.since,
                })
            }
        })
    }

    fn decode_log(kind: InputKind, record: &[u8]) -> Option<Log> {
        let mut r = Reader::new(record)?;
        if r.uleb()? != VERSION {
            return None;
        }
        let input = r.part()?;
        let change = r.part()?;
        let outputs = r.part()?;
        let decision = r.part()?;
        r.end()?;
        let input = match kind {
            InputKind::Person => LogInput::Person(Box::new(decode_admitted(input)?)),
            _ => match Self::decode(kind, input)? {
                Input::Hold(h) => LogInput::Hold(h),
                Input::Confirm(c) => LogInput::Confirm(c),
                Input::Wide(w) => LogInput::Wide(w),
                Input::Varied(v) => LogInput::Varied(v),
                Input::Person(_) => return None,
            },
        };
        let change = match kind.group() {
            Group::Booking => Change::State(decode_slot(change)?),
            _ => Change::Fields(decode_fields(change)?),
        };
        Some(Log {
            input,
            change,
            outputs: decode_outputs(outputs)?,
            decision: decode_decision(kind, decision)?,
        })
    }

    fn refused(corpus: &Corpus) -> Vec<Refused> {
        let mut out = Vec::new();

        let kind = InputKind::Hold;
        let h = &corpus.hold[0];
        let f = Self::encode(&Input::Hold(h.clone())).expect(FITS);
        refuse_frame(&mut out, kind, &f, HOLD_COUNT);
        let at = cmd_end(HOLD_COUNT);
        refuse_int(&mut out, kind, &f, at, h.key);
        refuse_text(&mut out, kind, &f, at + int_size(h.key), &h.sender);

        let kind = InputKind::Confirm;
        let c = &corpus.confirm[0];
        let f = Self::encode(&Input::Confirm(c.clone())).expect(FITS);
        refuse_frame(&mut out, kind, &f, CONFIRM_COUNT);
        let at = cmd_end(CONFIRM_COUNT);
        refuse_int(&mut out, kind, &f, at, c.key);
        refuse_text(&mut out, kind, &f, at + int_size(c.key), &c.sender);
        let t = &c.token;
        let name = f.len() - step_size(t.machine.as_bytes(), t.key, t.life, t.seq)
            + uleb_size(t.machine.len() as u64);
        refuse(&mut out, kind, "machine-name", splice(&f, name, 1, b"s"));

        let kind = InputKind::Wide;
        let w = &corpus.wide[0];
        let f = Self::encode(&Input::Wide(w.clone())).expect(FITS);
        refuse_frame(&mut out, kind, &f, WIDE_IN_COUNT);
        let at = cmd_end(WIDE_IN_COUNT);
        refuse_int(&mut out, kind, &f, at, w.wide.ints[0]);
        let flags = at + ints_size(&w.wide.ints);
        let bools = flags + w.wide.flags.len();
        let floats = bools + w.wide.bools.len();
        let money = floats + 8 * w.wide.floats.len();
        refuse(&mut out, kind, "enum-tag", splice(&f, flags, 1, &[4]));
        refuse(&mut out, kind, "bool-byte", splice(&f, bools, 1, &[2]));
        let nan = (CANONICAL_NAN | 1).to_le_bytes();
        refuse(&mut out, kind, "nan-pattern", splice(&f, floats, 8, &nan));
        let mut big = Vec::new();
        put_uleb128(&mut big, zigzag128(DECIMAL_MAX as i128 + 1));
        refuse(
            &mut out,
            kind,
            "decimal-range",
            splice(&f, money, f.len() - money, &big),
        );

        let kind = InputKind::Varied;
        let v = corpus
            .varied
            .iter()
            .find(|v| !v.varied.texts[0].is_empty())
            .expect("a VariedIn value with a nonempty first text");
        let f = Self::encode(&Input::Varied(v.clone())).expect(FITS);
        let v = &v.varied;
        refuse_frame(&mut out, kind, &f, VARIED_IN_COUNT);
        let at = cmd_end(VARIED_IN_COUNT);
        refuse_text(&mut out, kind, &f, at, &v.texts[0]);
        let opt = at + texts_size(&v.texts);
        let res = opt + 1 + v.opt.as_ref().map_or(0, |t| text_size(t.len()));
        let tag = res
            + 1
            + match &v.res {
                Ok(n) => int_size(*n),
                Err(t) => text_size(t.len()),
            };
        refuse(&mut out, kind, "option-tag", splice(&f, opt, 1, &[2]));
        refuse(&mut out, kind, "result-tag", splice(&f, res, 1, &[2]));
        refuse(&mut out, kind, "enum-tag", splice(&f, tag, 1, &[3]));
        refuse_int(&mut out, kind, &f, f.len() - ints_size(&v.ints), v.ints[0]);

        let kind = InputKind::Person;
        let p = &corpus.person[0];
        let f = Self::encode(&Input::Person(p.clone())).expect(FITS);
        refuse_frame(&mut out, kind, &f, PERSON_IN_COUNT);
        let at = cmd_end(PERSON_IN_COUNT);
        refuse_int(&mut out, kind, &f, at, p.id);
        let name = at + int_size(p.id);
        refuse_text(&mut out, kind, &f, name, &p.name);
        let mut long = p.name.as_bytes().to_vec();
        long.resize(SEAL_TEXT + 1, b'a');
        let mut text = Vec::new();
        put_text(&mut text, &long);
        refuse(
            &mut out,
            kind,
            "personal-text-long",
            splice(&f, name, text_size(p.name.len()), &text),
        );
        out
    }
}
