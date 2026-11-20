use crate::eval::{Ending, Envelope, Fault, Output, Stop, Value, eval_block, fuel_of};
use crate::ir::{
    Actor, Fn, Machine, Msg, Name, Program, find_cell, find_machine, find_msg, find_state,
    input_params,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Reply {
    Outcome(Value),
    Reject(Name),
    Answer(Value),
    Ignored,
    Fault(Fault),
    Next,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineState {
    pub name: Name,
    pub fields: Vec<Value>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Instance {
    pub machine: Name,
    pub key: Value,
    pub state: MachineState,
    pub seq: i64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Event {
    Step(Envelope, Reply, MachineState, Vec<Output>),
    Query(Envelope, Reply),
    Refused(Envelope),
}

impl Event {
    pub fn reply(&self) -> Option<Reply> {
        match self {
            Event::Step(_, reply, _, _) => Some(reply.clone()),
            Event::Query(_, reply) => Some(reply.clone()),
            Event::Refused(_) => None,
        }
    }
}

pub const LIFE: i64 = 1;

pub fn start(m: &Machine, key: Value) -> Instance {
    Instance {
        machine: m.name.clone(),
        key,
        state: MachineState {
            name: m.init.clone(),
            fields: Vec::new(),
        },
        seq: 0,
    }
}

pub fn cell_locals(
    p: &Program,
    m: &Machine,
    st: &MachineState,
    target: &str,
    env: &Envelope,
) -> Vec<(Name, Value)> {
    let mut locals: Vec<(Name, Value)> = if target == st.name {
        match find_state(m, &st.name) {
            Some(s) => s
                .fields
                .iter()
                .map(|f| f.name.clone())
                .zip(st.fields.iter().cloned())
                .collect(),
            None => Vec::new(),
        }
    } else {
        Vec::new()
    };
    locals.extend(
        input_params(p, m, &env.input)
            .into_iter()
            .map(|x| x.name)
            .zip(env.args.iter().cloned()),
    );
    locals.reverse();
    locals
}

pub fn run_cell(
    p: &Program,
    m: &Machine,
    inst: &Instance,
    env: &Envelope,
) -> Option<Result<(Ending, Vec<Output>), Fault>> {
    match find_cell(m, &inst.state.name, &env.input) {
        None => None,
        Some((target, cell)) => {
            let locals = cell_locals(p, m, &inst.state, target, env);
            let mut outs = Vec::new();
            match eval_block(p, Some(env), fuel_of(p), locals, &mut outs, &cell.body) {
                Ok(ending) => Some(Ok((ending, outs))),
                Err(Stop::Fault(f)) => Some(Err(f)),
                Err(Stop::Stuck) => None,
            }
        }
    }
}

pub fn settle(st: &MachineState, ending: Ending) -> Option<(Reply, MachineState)> {
    match ending {
        Ending::Next(s, vs, o) => Some((
            o.map(Reply::Outcome).unwrap_or(Reply::Next),
            MachineState {
                name: s,
                fields: vs,
            },
        )),
        Ending::Stay(o) => Some((o.map(Reply::Outcome).unwrap_or(Reply::Next), st.clone())),
        Ending::Reject(r) => Some((Reply::Reject(r), st.clone())),
        Ending::Answer(v) => Some((Reply::Answer(v), st.clone())),
        Ending::Ignore => Some((Reply::Ignored, st.clone())),
        Ending::Value(_) => None,
    }
}

pub fn step(p: &Program, m: &Machine, inst: &Instance, env: Envelope) -> Option<(Instance, Event)> {
    match run_cell(p, m, inst, &env)? {
        Err(f) => Some((
            Instance {
                seq: env.seq,
                ..inst.clone()
            },
            Event::Step(env, Reply::Fault(f), inst.state.clone(), Vec::new()),
        )),
        Ok((ending, outs)) => {
            let (reply, state) = settle(&inst.state, ending)?;
            Some((
                Instance {
                    state: state.clone(),
                    seq: env.seq,
                    ..inst.clone()
                },
                Event::Step(env, reply, state, outs),
            ))
        }
    }
}

pub fn query(
    p: &Program,
    m: &Machine,
    inst: &Instance,
    env: Envelope,
) -> Option<(Instance, Event)> {
    match run_cell(p, m, inst, &env)? {
        Err(f) => Some((inst.clone(), Event::Query(env, Reply::Fault(f)))),
        Ok((ending, _)) => {
            let (reply, _) = settle(&inst.state, ending)?;
            Some((inst.clone(), Event::Query(env, reply)))
        }
    }
}

pub fn deliver(
    p: &Program,
    inst: &Instance,
    now: i64,
    deadline: i64,
    caller: &Actor,
    input: &str,
    args: &[Value],
) -> Option<(Instance, Event)> {
    let m = find_machine(p, &inst.machine)?;
    let env = |seq: i64| Envelope {
        machine: inst.machine.clone(),
        key: inst.key.clone(),
        life: LIFE,
        seq,
        now,
        deadline,
        sender: caller.name.clone(),
        input: input.to_string(),
        args: args.to_vec(),
    };
    match find_msg(p, m, input) {
        Some(Msg::Command {
            role: Some(role), ..
        }) => {
            if caller.roles.contains(role) {
                step(p, m, inst, env(inst.seq + 1))
            } else {
                Some((inst.clone(), Event::Refused(env(inst.seq))))
            }
        }
        Some(Msg::Query { .. }) => query(p, m, inst, env(inst.seq)),
        _ => step(p, m, inst, env(inst.seq + 1)),
    }
}

pub fn run_entry(p: &Program, f: &Fn) -> Option<Result<Vec<Output>, Fault>> {
    let mut outs = Vec::new();
    match eval_block(p, None, fuel_of(p), Vec::new(), &mut outs, &f.body) {
        Ok(Ending::Value(_)) => Some(Ok(outs)),
        Ok(_) => None,
        Err(Stop::Fault(fault)) => Some(Err(fault)),
        Err(Stop::Stuck) => None,
    }
}
