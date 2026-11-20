pub const N: usize = 1000;

pub const MACHINE: &str = "Slot";

pub const TIMER_NANOS: i64 = 30_000_000_000;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct CommandId(pub [u8; 34]);

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Sealed(pub [u8; 128]);

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct StepId {
    pub machine: String,
    pub key: i64,
    pub life: i64,
    pub seq: i64,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Ticket {
    pub machine: String,
    pub key: i64,
    pub life: i64,
    pub seq: i64,
    pub idx: i64,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct HoldIn {
    pub cmd: CommandId,
    pub key: i64,
    pub sender: String,
    pub now: i64,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ConfirmIn {
    pub cmd: CommandId,
    pub key: i64,
    pub sender: String,
    pub now: i64,
    pub token: StepId,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct HeldFields {
    pub holder: String,
    pub hold: StepId,
    pub timer: Ticket,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct BookedFields {
    pub owner: String,
    pub hold: StepId,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum SlotState {
    Absent,
    Free,
    Held(HeldFields),
    Booked(BookedFields),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Output {
    After(i64, Ticket),
    Cancel(Ticket),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Flag {
    A,
    B,
    C,
    D,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Wide {
    pub ints: [i64; 14],
    pub flags: [Flag; 4],
    pub bools: [bool; 2],
    pub floats: [u64; 3],
    pub money: i128,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct WideIn {
    pub cmd: CommandId,
    pub wide: Wide,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Kind {
    Plain,
    Tagged(String),
    Scored(i64, i64),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Varied {
    pub texts: [String; 4],
    pub opt: Option<String>,
    pub res: Result<i64, String>,
    pub kind: Kind,
    pub ints: [i64; 4],
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct VariedIn {
    pub cmd: CommandId,
    pub varied: Varied,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct PersonIn {
    pub cmd: CommandId,
    pub id: i64,
    pub name: String,
    pub email: String,
    pub phone: String,
    pub visits: i64,
    pub score: i64,
    pub since: i64,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Person {
    pub id: i64,
    pub name: Sealed,
    pub email: Sealed,
    pub phone: Sealed,
    pub visits: i64,
    pub score: i64,
    pub since: i64,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Admitted {
    pub cmd: CommandId,
    pub person: Person,
}

pub struct Corpus {
    pub pad: [u8; 128],
    pub hold: Vec<HoldIn>,
    pub confirm: Vec<ConfirmIn>,
    pub wide: Vec<WideIn>,
    pub varied: Vec<VariedIn>,
    pub person: Vec<PersonIn>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum InputKind {
    Hold,
    Confirm,
    Wide,
    Varied,
    Person,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Group {
    Booking,
    Wide,
    Varied,
    Personal,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Input {
    Hold(HoldIn),
    Confirm(ConfirmIn),
    Wide(WideIn),
    Varied(VariedIn),
    Person(PersonIn),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum State {
    Slot(SlotState),
    Wide(Wide),
    Varied(Varied),
    Person(Box<Person>),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum LogInput {
    Hold(HoldIn),
    Confirm(ConfirmIn),
    Wide(WideIn),
    Varied(VariedIn),
    Person(Box<Admitted>),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Change {
    State(SlotState),
    Fields(Vec<(u64, i64)>),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Decision {
    Token(StepId),
    Unit,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Log {
    pub input: LogInput,
    pub change: Change,
    pub outputs: Vec<Output>,
    pub decision: Decision,
}

pub struct Refused {
    pub kind: InputKind,
    pub cause: &'static str,
    pub frame: Vec<u8>,
}

pub trait Arm {
    const NAME: &'static str;
    fn new(corpus: &Corpus) -> Self;
    fn reset(&mut self);
    fn step_hold(&mut self, i: usize) -> u64;
    fn step_confirm(&mut self, i: usize) -> u64;
    fn step_wide(&mut self, i: usize) -> u64;
    fn step_varied(&mut self, i: usize) -> u64;
    fn step_person(&mut self, i: usize) -> u64;
    fn frame(&self, kind: InputKind, i: usize) -> &[u8];
    fn log(&self) -> &[u8];
    fn state(&self, group: Group, i: usize) -> State;
    fn admits(&mut self, kind: InputKind, frame: &[u8]) -> bool;
    fn encode(input: &Input) -> Option<Vec<u8>>;
    fn decode(kind: InputKind, frame: &[u8]) -> Option<Input>;
    fn decode_log(kind: InputKind, record: &[u8]) -> Option<Log>;
    fn refused(corpus: &Corpus) -> Vec<Refused>;
}

pub fn fold(c: u64, v: u64) -> u64 {
    c.rotate_left(5) ^ v
}

pub fn fold_text(c: u64, bytes: &[u8]) -> u64 {
    let first = bytes.first().map_or(0, |b| u64::from(*b));
    let last = bytes.last().map_or(0, |b| u64::from(*b));
    fold(fold(fold(c, bytes.len() as u64), first), last)
}

pub fn seal(pad: &[u8; 128], text: &str) -> Sealed {
    let bytes = text.as_bytes();
    let mut slot = *pad;
    slot[0..2].copy_from_slice(&(bytes.len() as u16).to_le_bytes());
    slot[2..2 + bytes.len()].copy_from_slice(bytes);
    Sealed(slot)
}

pub fn admit(pad: &[u8; 128], input: &PersonIn) -> Admitted {
    Admitted {
        cmd: input.cmd,
        person: Person {
            id: input.id,
            name: seal(pad, &input.name),
            email: seal(pad, &input.email),
            phone: seal(pad, &input.phone),
            visits: input.visits,
            score: input.score,
            since: input.since,
        },
    }
}

pub fn hold_token(corpus: &Corpus, i: usize) -> StepId {
    StepId {
        machine: MACHINE.to_string(),
        key: corpus.hold[i].key,
        life: 1,
        seq: i as i64 + 1,
    }
}

pub fn held(corpus: &Corpus, i: usize) -> HeldFields {
    let hold = hold_token(corpus, i);
    HeldFields {
        holder: corpus.hold[i].sender.clone(),
        timer: Ticket {
            machine: hold.machine.clone(),
            key: hold.key,
            life: hold.life,
            seq: hold.seq,
            idx: 0,
        },
        hold,
    }
}

pub fn wide_start(corpus: &Corpus, i: usize) -> Wide {
    corpus.wide[(i + 1) % N].wide.clone()
}

pub fn varied_start(corpus: &Corpus, i: usize) -> Varied {
    corpus.varied[(i + 1) % N].varied.clone()
}

pub fn person_start(corpus: &Corpus, i: usize) -> Person {
    admit(&corpus.pad, &corpus.person[(i + 1) % N]).person
}

pub const KINDS: [InputKind; 5] = [
    InputKind::Hold,
    InputKind::Confirm,
    InputKind::Wide,
    InputKind::Varied,
    InputKind::Person,
];

pub const GROUPS: [Group; 4] = [Group::Booking, Group::Wide, Group::Varied, Group::Personal];

pub const ARMS: [&str; 3] = ["F", "P", "S"];

pub const ROTATIONS: [[&str; 3]; 3] = [["F", "P", "S"], ["P", "S", "F"], ["S", "F", "P"]];

pub const CSV_HEADER: &str = "run,position,arm,group,passes,steps,nanos";

pub struct Row {
    pub run: u32,
    pub position: u32,
    pub arm: String,
    pub group: String,
    pub passes: u64,
    pub steps: u64,
    pub nanos: u64,
}

impl Group {
    pub fn name(self) -> &'static str {
        match self {
            Group::Booking => "booking",
            Group::Wide => "wide",
            Group::Varied => "varied",
            Group::Personal => "personal",
        }
    }
}

impl InputKind {
    pub fn group(self) -> Group {
        match self {
            InputKind::Hold | InputKind::Confirm => Group::Booking,
            InputKind::Wide => Group::Wide,
            InputKind::Varied => Group::Varied,
            InputKind::Person => Group::Personal,
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            InputKind::Hold => "HoldIn",
            InputKind::Confirm => "ConfirmIn",
            InputKind::Wide => "WideIn",
            InputKind::Varied => "VariedIn",
            InputKind::Person => "PersonIn",
        }
    }
}

pub fn input(corpus: &Corpus, kind: InputKind, i: usize) -> Input {
    match kind {
        InputKind::Hold => Input::Hold(corpus.hold[i].clone()),
        InputKind::Confirm => Input::Confirm(corpus.confirm[i].clone()),
        InputKind::Wide => Input::Wide(corpus.wide[i].clone()),
        InputKind::Varied => Input::Varied(corpus.varied[i].clone()),
        InputKind::Person => Input::Person(corpus.person[i].clone()),
    }
}

pub fn step<A: Arm>(arm: &mut A, kind: InputKind, i: usize) -> u64 {
    match kind {
        InputKind::Hold => arm.step_hold(i),
        InputKind::Confirm => arm.step_confirm(i),
        InputKind::Wide => arm.step_wide(i),
        InputKind::Varied => arm.step_varied(i),
        InputKind::Person => arm.step_person(i),
    }
}
