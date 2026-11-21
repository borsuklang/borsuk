pub type Name = String;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ty {
    Unit,
    Bool,
    Int,
    Text,
    Time,
    Duration,
    Principal,
    StepId,
    Ticket,
    F64,
    F32,
    Decimal(u32),
    Option(Box<Ty>),
    Result(Box<Ty>, Box<Ty>),
    Named(Name),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Effect {
    ConsoleOut,
    Timer,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EnvField {
    Now,
    Step,
    Sender,
    Deadline,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Arith {
    Add,
    Sub,
    Mul,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fn1 {
    Exp,
    Exp2,
    Log,
    Log2,
    Log10,
    Sin,
    Cos,
    Tan,
    Asin,
    Acos,
    Atan,
    Sinh,
    Cosh,
    Tanh,
    Cbrt,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fn2 {
    Pow,
    Atan2,
    Hypot,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    Up,
    Down,
    Ceiling,
    Floor,
    HalfUp,
    HalfDown,
    HalfEven,
    Exact,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Op {
    Print,
    After,
    Cancel,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    Int(i64),
    Text(String),
    Bool(bool),
    Unit,
    Dur(i64),
    Var(Name),
    Env(EnvField),
    Call(Name, Vec<Expr>),
    New(Name, Vec<Expr>),
    Get(Box<Expr>, Name),
    Some(Box<Expr>),
    None,
    Ok(Box<Expr>),
    Err(Box<Expr>),
    Arith(Arith, Box<Expr>, Box<Expr>),
    Eq(Box<Expr>, Box<Expr>),
    Lt(Box<Expr>, Box<Expr>),
    And(Box<Expr>, Box<Expr>),
    Not(Box<Expr>),
    Op(Op, Box<Expr>),
    F64(u64),
    F32(u32),
    Dec(u32, i128),
    Div(Box<Expr>, Box<Expr>),
    Sqrt(Box<Expr>),
    Fma(Box<Expr>, Box<Expr>, Box<Expr>),
    Fn1(Fn1, Box<Expr>),
    Fn2(Fn2, Box<Expr>, Box<Expr>),
    Round(Ty, Mode, Box<Expr>),
    DivMode(Ty, Mode, Box<Expr>, Box<Expr>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Bind {
    Wild,
    Name(Name),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Pat {
    Bool(bool),
    None,
    Some(Bind),
    Ok(Bind),
    Err(Bind),
    Con(Name, Vec<Bind>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Stmt {
    Let(Name, Expr),
    Do(Expr),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub tail: Tail,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Tail {
    Value(Expr),
    Next(Name, Vec<Expr>, Option<Expr>),
    Stay(Option<Expr>),
    Reject(Name),
    Answer(Expr),
    Ignore,
    Impossible,
    Match(Expr, Vec<Arm>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Arm {
    pub pat: Pat,
    pub body: Block,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Param {
    pub name: Name,
    pub ty: Ty,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Variant {
    pub name: Name,
    pub fields: Vec<Ty>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Fn {
    pub name: Name,
    pub params: Vec<Param>,
    pub result: Ty,
    pub uses: Vec<Effect>,
    pub body: Block,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Msg {
    Command {
        name: Name,
        params: Vec<Param>,
        result: Ty,
        rejects: Vec<Name>,
        role: Option<Name>,
    },
    Query {
        name: Name,
        params: Vec<Param>,
        result: Ty,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Protocol {
    pub name: Name,
    pub msgs: Vec<Msg>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct State {
    pub name: Name,
    pub fields: Vec<Param>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Group {
    pub name: Name,
    pub members: Vec<Name>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cell {
    pub input: Name,
    pub body: Block,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct In {
    pub target: Name,
    pub cells: Vec<Cell>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Machine {
    pub name: Name,
    pub key: Ty,
    pub protocol: Name,
    pub uses: Vec<Effect>,
    pub init: Name,
    pub states: Vec<State>,
    pub groups: Vec<Group>,
    pub ins: Vec<In>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Platform {
    Cli,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Deployment {
    pub name: Name,
    pub platform: Platform,
    pub entry: Name,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum XExpr {
    Int(i64),
    Text(String),
    Bool(bool),
    Unit,
    Dur(i64),
    Var(Name),
    New(Name, Vec<XExpr>),
    Some(Box<XExpr>),
    None,
    Ok(Box<XExpr>),
    Err(Box<XExpr>),
    Step(i64),
    Ticket(i64),
    F64(u64),
    F32(u32),
    Dec(u32, i128),
    Time(i64),
    Principal(String),
    StepOf(Name, Box<XExpr>, i64, i64),
    TicketOf(Name, Box<XExpr>, i64, i64, i64),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Fact {
    Outcome(XExpr),
    Reject(Name),
    Answer(XExpr),
    Refused,
    Fault(Name),
    Ignored,
    State(Name, Vec<XExpr>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Line {
    Send {
        actor: Name,
        input: Name,
        args: Vec<XExpr>,
        facts: Vec<Fact>,
    },
    Fire {
        ticket: XExpr,
        facts: Vec<Fact>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Actor {
    pub name: Name,
    pub roles: Vec<Name>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Example {
    pub name: Name,
    pub machine: Name,
    pub key: XExpr,
    pub actors: Vec<Actor>,
    pub lines: Vec<Line>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Item {
    Newtype(Name, Ty),
    Record(Name, Vec<Param>, Vec<(Param, XExpr)>),
    Enum(Name, Vec<Variant>),
    Role(Name),
    Fn(Fn),
    Protocol(Protocol),
    Machine(Machine),
    Deployment(Deployment),
    Example(Example),
    Decode(Name, Ty, Vec<u8>, Option<XExpr>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Program {
    pub items: Vec<Item>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fault {
    Overflow,
    Impossible,
    Inexact,
    DivZero,
    Undecided,
}

impl Fault {
    pub fn text(&self) -> &'static str {
        match self {
            Fault::Overflow => "overflow",
            Fault::Impossible => "impossible",
            Fault::Inexact => "inexact",
            Fault::DivZero => "div_zero",
            Fault::Undecided => "undecided",
        }
    }
}

pub const FIRED_NAME: &str = "Fired";

impl Msg {
    pub fn name(&self) -> &Name {
        match self {
            Msg::Command { name, .. } | Msg::Query { name, .. } => name,
        }
    }

    pub fn params(&self) -> &[Param] {
        match self {
            Msg::Command { params, .. } | Msg::Query { params, .. } => params,
        }
    }

    pub fn result(&self) -> &Ty {
        match self {
            Msg::Command { result, .. } | Msg::Query { result, .. } => result,
        }
    }
}

pub fn find_protocol<'a>(p: &'a Program, name: &str) -> Option<&'a Protocol> {
    p.items.iter().find_map(|item| match item {
        Item::Protocol(q) if q.name == name => Some(q),
        _ => None,
    })
}

pub fn find_fn<'a>(p: &'a Program, name: &str) -> Option<&'a Fn> {
    p.items.iter().find_map(|item| match item {
        Item::Fn(f) if f.name == name => Some(f),
        _ => None,
    })
}

pub fn find_machine<'a>(p: &'a Program, name: &str) -> Option<&'a Machine> {
    p.items.iter().find_map(|item| match item {
        Item::Machine(m) if m.name == name => Some(m),
        _ => None,
    })
}

pub fn find_msg<'a>(p: &'a Program, m: &Machine, name: &str) -> Option<&'a Msg> {
    find_protocol(p, &m.protocol).and_then(|q| q.msgs.iter().find(|msg| msg.name() == name))
}

pub fn fired_params() -> Vec<Param> {
    vec![Param {
        name: "ticket".to_string(),
        ty: Ty::Ticket,
    }]
}

pub fn input_params(p: &Program, m: &Machine, input: &str) -> Vec<Param> {
    match find_msg(p, m, input) {
        Some(msg) => msg.params().to_vec(),
        None => fired_params(),
    }
}

pub fn find_state<'a>(m: &'a Machine, name: &str) -> Option<&'a State> {
    m.states.iter().find(|s| s.name == name)
}

pub fn input_names(p: &Program, m: &Machine) -> Vec<Name> {
    let mut names: Vec<Name> = find_protocol(p, &m.protocol)
        .map(|q| q.msgs.iter().map(|msg| msg.name().clone()).collect())
        .unwrap_or_default();
    if m.uses.contains(&Effect::Timer) {
        names.push(FIRED_NAME.to_string());
    }
    names
}

pub fn covers(m: &Machine, target: &str, state: &str) -> bool {
    target == state
        || m.groups
            .iter()
            .any(|g| g.name == target && g.members.iter().any(|x| x == state))
}

pub fn cells_for<'a>(m: &'a Machine, state: &str, input: &str) -> Vec<(&'a Name, &'a Cell)> {
    m.ins
        .iter()
        .filter(|b| covers(m, &b.target, state))
        .flat_map(|b| {
            b.cells
                .iter()
                .filter(move |c| c.input == input)
                .map(move |c| (&b.target, c))
        })
        .collect()
}

pub fn find_cell<'a>(m: &'a Machine, state: &str, input: &str) -> Option<(&'a Name, &'a Cell)> {
    cells_for(m, state, input).into_iter().next()
}
