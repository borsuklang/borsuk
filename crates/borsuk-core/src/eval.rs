use crate::ir::{
    Arith, Arm, Bind, Block, EnvField, Expr, Item, Name, Op, Pat, Program, Stmt, Tail, find_fn,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
    Int(i64),
    Bool(bool),
    Unit,
    Text(String),
    Dur(i64),
    Time(i64),
    Principal(Name),
    StepId {
        machine: Name,
        key: Box<Value>,
        life: i64,
        seq: i64,
    },
    Ticket {
        machine: Name,
        key: Box<Value>,
        life: i64,
        seq: i64,
        idx: i64,
    },
    Con(Name, Vec<Value>),
    Some(Box<Value>),
    None,
    Ok(Box<Value>),
    Err(Box<Value>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fault {
    Overflow,
    Impossible,
}

impl Fault {
    pub fn text(&self) -> &'static str {
        match self {
            Fault::Overflow => "overflow",
            Fault::Impossible => "impossible",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Stop {
    Fault(Fault),
    Stuck,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Output {
    Print(Value),
    After(Value, Value),
    Cancel(Value),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Envelope {
    pub machine: Name,
    pub key: Value,
    pub life: i64,
    pub seq: i64,
    pub now: i64,
    pub deadline: i64,
    pub sender: Name,
    pub input: Name,
    pub args: Vec<Value>,
}

impl Envelope {
    pub fn field(&self, field: EnvField) -> Value {
        match field {
            EnvField::Now => Value::Time(self.now),
            EnvField::Step => Value::StepId {
                machine: self.machine.clone(),
                key: Box::new(self.key.clone()),
                life: self.life,
                seq: self.seq,
            },
            EnvField::Sender => Value::Principal(self.sender.clone()),
            EnvField::Deadline => Value::Time(self.deadline),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ending {
    Value(Value),
    Next(Name, Vec<Value>, Option<Value>),
    Stay(Option<Value>),
    Reject(Name),
    Answer(Value),
    Ignore,
}

pub fn stuck<T>() -> Result<T, Stop> {
    Err(Stop::Stuck)
}

pub fn checked(n: Option<i64>) -> Result<Value, Stop> {
    match n {
        Some(n) => Ok(Value::Int(n)),
        None => Err(Stop::Fault(Fault::Overflow)),
    }
}

pub fn arith(op: Arith, a: i64, b: i64) -> Option<i64> {
    match op {
        Arith::Add => a.checked_add(b),
        Arith::Sub => a.checked_sub(b),
        Arith::Mul => a.checked_mul(b),
    }
}

pub fn less(a: &Value, b: &Value) -> Option<bool> {
    match (a, b) {
        (Value::Int(a), Value::Int(b)) => Some(a < b),
        (Value::Time(a), Value::Time(b)) => Some(a < b),
        (Value::Dur(a), Value::Dur(b)) => Some(a < b),
        _ => None,
    }
}

pub fn tickets(outs: &[Output]) -> i64 {
    outs.iter().fold(0, |n, o| match o {
        Output::After(..) => n + 1,
        _ => n,
    })
}

pub fn bind_value(b: &Bind, v: Value) -> Vec<(Name, Value)> {
    match b {
        Bind::Wild => Vec::new(),
        Bind::Name(x) => vec![(x.clone(), v)],
    }
}

pub fn bind_values(bs: &[Bind], vs: &[Value]) -> Vec<(Name, Value)> {
    bs.iter()
        .zip(vs)
        .flat_map(|(b, v)| bind_value(b, v.clone()))
        .collect()
}

pub fn match_pat(pat: &Pat, v: &Value) -> Option<Vec<(Name, Value)>> {
    match (pat, v) {
        (Pat::Bool(b), Value::Bool(v)) => {
            if b == v {
                Some(Vec::new())
            } else {
                None
            }
        }
        (Pat::None, Value::None) => Some(Vec::new()),
        (Pat::Some(b), Value::Some(v)) => Some(bind_value(b, (**v).clone())),
        (Pat::Ok(b), Value::Ok(v)) => Some(bind_value(b, (**v).clone())),
        (Pat::Err(b), Value::Err(v)) => Some(bind_value(b, (**v).clone())),
        (Pat::Con(c, bs), Value::Con(d, vs)) => {
            if c == d {
                Some(bind_values(bs, vs))
            } else {
                None
            }
        }
        _ => None,
    }
}

pub fn field_index(p: &Program, record: &str, field: &str) -> Option<usize> {
    p.items.iter().find_map(|item| match item {
        Item::Record(r, fields) => {
            if r == record {
                fields.iter().position(|f| f.name == field)
            } else {
                None
            }
        }
        _ => None,
    })
}

pub fn fuel_of(p: &Program) -> u64 {
    p.items.iter().fold(0, |n, item| match item {
        Item::Fn(_) => n + 1,
        _ => n,
    })
}

pub fn eval_expr(
    p: &Program,
    env: Option<&Envelope>,
    fuel: u64,
    locals: &[(Name, Value)],
    outs: &mut Vec<Output>,
    e: &Expr,
) -> Result<Value, Stop> {
    match e {
        Expr::Int(n) => Ok(Value::Int(*n)),
        Expr::Text(s) => Ok(Value::Text(s.clone())),
        Expr::Bool(b) => Ok(Value::Bool(*b)),
        Expr::Unit => Ok(Value::Unit),
        Expr::Dur(n) => Ok(Value::Dur(*n)),
        Expr::Var(x) => match locals.iter().rev().find(|l| l.0 == *x) {
            Some((_, v)) => Ok(v.clone()),
            None => stuck(),
        },
        Expr::Env(field) => match env {
            Some(e) => Ok(e.field(*field)),
            None => stuck(),
        },
        Expr::Call(callee, args) => {
            let vs = eval_args(p, env, fuel, locals, outs, args)?;
            call_fn(p, fuel, callee, vs, outs)
        }
        Expr::New(ctor, args) => {
            let vs = eval_args(p, env, fuel, locals, outs, args)?;
            Ok(Value::Con(ctor.clone(), vs))
        }
        Expr::Get(target, field) => {
            let v = eval_expr(p, env, fuel, locals, outs, target)?;
            match v {
                Value::Con(r, vs) => match field_index(p, &r, field).and_then(|i| vs.get(i)) {
                    Some(x) => Ok(x.clone()),
                    None => stuck(),
                },
                _ => stuck(),
            }
        }
        Expr::Some(inner) => {
            let v = eval_expr(p, env, fuel, locals, outs, inner)?;
            Ok(Value::Some(Box::new(v)))
        }
        Expr::None => Ok(Value::None),
        Expr::Ok(inner) => {
            let v = eval_expr(p, env, fuel, locals, outs, inner)?;
            Ok(Value::Ok(Box::new(v)))
        }
        Expr::Err(inner) => {
            let v = eval_expr(p, env, fuel, locals, outs, inner)?;
            Ok(Value::Err(Box::new(v)))
        }
        Expr::Arith(op, a, b) => {
            let va = eval_expr(p, env, fuel, locals, outs, a)?;
            let vb = eval_expr(p, env, fuel, locals, outs, b)?;
            match (va, vb) {
                (Value::Int(x), Value::Int(y)) => checked(arith(*op, x, y)),
                _ => stuck(),
            }
        }
        Expr::Eq(a, b) => {
            let va = eval_expr(p, env, fuel, locals, outs, a)?;
            let vb = eval_expr(p, env, fuel, locals, outs, b)?;
            Ok(Value::Bool(va == vb))
        }
        Expr::Lt(a, b) => {
            let va = eval_expr(p, env, fuel, locals, outs, a)?;
            let vb = eval_expr(p, env, fuel, locals, outs, b)?;
            match less(&va, &vb) {
                Some(r) => Ok(Value::Bool(r)),
                None => stuck(),
            }
        }
        Expr::And(a, b) => {
            let va = eval_expr(p, env, fuel, locals, outs, a)?;
            let vb = eval_expr(p, env, fuel, locals, outs, b)?;
            match (va, vb) {
                (Value::Bool(x), Value::Bool(y)) => Ok(Value::Bool(x && y)),
                _ => stuck(),
            }
        }
        Expr::Not(a) => {
            let va = eval_expr(p, env, fuel, locals, outs, a)?;
            match va {
                Value::Bool(x) => Ok(Value::Bool(!x)),
                _ => stuck(),
            }
        }
        Expr::Op(Op::Print, arg) => {
            let v = eval_expr(p, env, fuel, locals, outs, arg)?;
            outs.push(Output::Print(v));
            Ok(Value::Unit)
        }
        Expr::Op(Op::After, arg) => {
            let d = eval_expr(p, env, fuel, locals, outs, arg)?;
            match env {
                Some(e) => {
                    let idx = tickets(outs);
                    let t = Value::Ticket {
                        machine: e.machine.clone(),
                        key: Box::new(e.key.clone()),
                        life: e.life,
                        seq: e.seq,
                        idx,
                    };
                    outs.push(Output::After(d, t.clone()));
                    Ok(t)
                }
                None => stuck(),
            }
        }
        Expr::Op(Op::Cancel, arg) => {
            let t = eval_expr(p, env, fuel, locals, outs, arg)?;
            outs.push(Output::Cancel(t));
            Ok(Value::Unit)
        }
    }
}

pub fn eval_args(
    p: &Program,
    env: Option<&Envelope>,
    fuel: u64,
    locals: &[(Name, Value)],
    outs: &mut Vec<Output>,
    args: &[Expr],
) -> Result<Vec<Value>, Stop> {
    let mut vs = Vec::new();
    for e in args {
        vs.push(eval_expr(p, env, fuel, locals, outs, e)?);
    }
    Ok(vs)
}

pub fn eval_outcome(
    p: &Program,
    env: Option<&Envelope>,
    fuel: u64,
    locals: &[(Name, Value)],
    outs: &mut Vec<Output>,
    o: Option<&Expr>,
) -> Result<Option<Value>, Stop> {
    match o {
        Some(e) => {
            let v = eval_expr(p, env, fuel, locals, outs, e)?;
            Ok(Some(v))
        }
        None => Ok(None),
    }
}

pub fn eval_stmts(
    p: &Program,
    env: Option<&Envelope>,
    fuel: u64,
    mut locals: Vec<(Name, Value)>,
    outs: &mut Vec<Output>,
    stmts: &[Stmt],
) -> Result<Vec<(Name, Value)>, Stop> {
    for s in stmts {
        match s {
            Stmt::Let(x, e) => {
                let v = eval_expr(p, env, fuel, &locals, outs, e)?;
                locals.push((x.clone(), v));
            }
            Stmt::Do(e) => {
                eval_expr(p, env, fuel, &locals, outs, e)?;
            }
        }
    }
    Ok(locals)
}

pub fn eval_block(
    p: &Program,
    env: Option<&Envelope>,
    fuel: u64,
    locals: Vec<(Name, Value)>,
    outs: &mut Vec<Output>,
    b: &Block,
) -> Result<Ending, Stop> {
    let locals = eval_stmts(p, env, fuel, locals, outs, &b.stmts)?;
    eval_tail(p, env, fuel, locals, outs, &b.tail)
}

pub fn eval_tail(
    p: &Program,
    env: Option<&Envelope>,
    fuel: u64,
    locals: Vec<(Name, Value)>,
    outs: &mut Vec<Output>,
    t: &Tail,
) -> Result<Ending, Stop> {
    match t {
        Tail::Value(e) => {
            let v = eval_expr(p, env, fuel, &locals, outs, e)?;
            Ok(Ending::Value(v))
        }
        Tail::Next(s, args, o) => {
            let vs = eval_args(p, env, fuel, &locals, outs, args)?;
            let ov = eval_outcome(p, env, fuel, &locals, outs, o.as_ref())?;
            Ok(Ending::Next(s.clone(), vs, ov))
        }
        Tail::Stay(o) => {
            let ov = eval_outcome(p, env, fuel, &locals, outs, o.as_ref())?;
            Ok(Ending::Stay(ov))
        }
        Tail::Reject(r) => Ok(Ending::Reject(r.clone())),
        Tail::Answer(e) => {
            let v = eval_expr(p, env, fuel, &locals, outs, e)?;
            Ok(Ending::Answer(v))
        }
        Tail::Ignore => Ok(Ending::Ignore),
        Tail::Impossible => Err(Stop::Fault(Fault::Impossible)),
        Tail::Match(subject, arms) => {
            let v = eval_expr(p, env, fuel, &locals, outs, subject)?;
            eval_arms(p, env, fuel, locals, outs, &v, arms)
        }
    }
}

pub fn eval_arms(
    p: &Program,
    env: Option<&Envelope>,
    fuel: u64,
    mut locals: Vec<(Name, Value)>,
    outs: &mut Vec<Output>,
    subject: &Value,
    arms: &[Arm],
) -> Result<Ending, Stop> {
    for arm in arms {
        if let Some(binds) = match_pat(&arm.pat, subject) {
            locals.extend(binds.into_iter().rev());
            return eval_block(p, env, fuel, locals, outs, &arm.body);
        }
    }
    stuck()
}

pub fn call_fn(
    p: &Program,
    fuel: u64,
    callee: &str,
    args: Vec<Value>,
    outs: &mut Vec<Output>,
) -> Result<Value, Stop> {
    match fuel.checked_sub(1) {
        None => stuck(),
        Some(k) => match find_fn(p, callee) {
            Some(f) => {
                let mut locals: Vec<(Name, Value)> =
                    f.params.iter().map(|x| x.name.clone()).zip(args).collect();
                locals.reverse();
                let ending = eval_block(p, None, k, locals, outs, &f.body)?;
                match ending {
                    Ending::Value(v) => Ok(v),
                    _ => stuck(),
                }
            }
            None => stuck(),
        },
    }
}
