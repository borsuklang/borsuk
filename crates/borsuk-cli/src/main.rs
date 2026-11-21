#![forbid(unsafe_code)]

use std::process::ExitCode;

use borsuk_core::check::{Code, Diag, check};
use borsuk_core::codec::{decode, encode, full};
use borsuk_core::eval::{Output, Value};
use borsuk_core::ir::{
    Actor, Deployment, Example, FIRED_NAME, Fact, Item, Line, Name, Program, Ty, XExpr, find_fn,
    find_machine,
};
use borsuk_core::print::{show_diag, show_event};
use borsuk_core::read::read;
use borsuk_core::runtime::{
    Event, Instance, MachineState, Reply, deliver, run_entry, start, xvalue, xvalues,
};

fn fault_is(kind: &str, reply: Option<Reply>) -> bool {
    match reply {
        Some(Reply::Fault(f)) => f.text() == kind,
        _ => false,
    }
}

fn holds(inst: Option<(&str, &Value)>, ev: &Event, state: &MachineState, fact: &Fact) -> bool {
    match fact {
        Fact::Outcome(x) => ev.reply() == xvalue(inst, x).map(Reply::Outcome),
        Fact::Reject(r) => ev.reply() == Some(Reply::Reject(r.clone())),
        Fact::Answer(x) => ev.reply() == xvalue(inst, x).map(Reply::Answer),
        Fact::Refused => matches!(ev, Event::Refused(_)),
        Fact::Fault(k) => fault_is(k, ev.reply()),
        Fact::Ignored => ev.reply() == Some(Reply::Ignored),
        Fact::State(s, args) => {
            state.name == *s && xvalues(inst, args).as_ref() == Some(&state.fields)
        }
    }
}

fn find_actor(ex: &Example, name: &str) -> Actor {
    match ex.actors.iter().find(|a| a.name == name) {
        Some(a) => a.clone(),
        None => Actor {
            name: name.to_string(),
            roles: Vec::new(),
        },
    }
}

fn line_input<'a>(
    inst: Option<(&str, &Value)>,
    ex: &Example,
    l: &'a Line,
) -> Option<(Actor, Name, Vec<Value>, &'a [Fact])> {
    match l {
        Line::Send {
            actor,
            input,
            args,
            facts,
        } => xvalues(inst, args).map(|vs| (find_actor(ex, actor), input.clone(), vs, &facts[..])),
        Line::Fire { ticket, facts } => xvalue(inst, ticket).map(|v| {
            (
                Actor {
                    name: "runtime".to_string(),
                    roles: Vec::new(),
                },
                FIRED_NAME.to_string(),
                vec![v],
                &facts[..],
            )
        }),
    }
}

fn run_lines(p: &Program, ex: &Example, mut n: u64, mut inst: Instance, lines: &[Line]) -> bool {
    for l in lines {
        let here = Some((inst.machine.as_str(), &inst.key));
        let result = line_input(here, ex, l).and_then(|(caller, input, args, facts)| {
            deliver(p, &inst, 0, 0, &caller, &input, &args).map(|r| (r, facts))
        });
        match result {
            Some(((inst2, ev), facts)) => {
                println!("{}", show_event(&ev));
                if !facts.iter().all(|f| holds(here, &ev, &inst2.state, f)) {
                    println!("fail {}: line {}", ex.name, n);
                    return false;
                }
                n += 1;
                inst = inst2;
            }
            None => {
                println!("fail {}: line {}", ex.name, n);
                return false;
            }
        }
    }
    println!("pass {}", ex.name);
    true
}

fn run_example(p: &Program, ex: &Example) -> bool {
    match (find_machine(p, &ex.machine), xvalue(None, &ex.key)) {
        (Some(m), Some(key)) => run_lines(p, ex, 1, start(m, key), &ex.lines),
        _ => {
            println!("fail {}: line 1", ex.name);
            false
        }
    }
}

fn decode_holds(p: &Program, t: &Ty, frame: &[u8], expect: Option<&XExpr>) -> bool {
    match expect {
        Some(x) => match xvalue(None, x) {
            Some(v) => {
                decode(p, t, frame).as_ref() == Some(&v)
                    && (!full(p, t, frame) || encode(p, t, &v).as_deref() == Some(frame))
            }
            None => false,
        },
        None => decode(p, t, frame).is_none(),
    }
}

fn run_decode(p: &Program, name: &str, t: &Ty, frame: &[u8], expect: Option<&XExpr>) -> bool {
    let ok = decode_holds(p, t, frame, expect);
    println!("{} {}", if ok { "pass" } else { "fail" }, name);
    ok
}

fn run_item(p: &Program, it: &Item) -> bool {
    match it {
        Item::Example(ex) => run_example(p, ex),
        Item::Decode(name, t, frame, expect) => run_decode(p, name, t, frame, expect.as_ref()),
        _ => true,
    }
}

fn test(p: &Program) -> u8 {
    let mut ok = true;
    for it in &p.items {
        if !run_item(p, it) {
            ok = false;
        }
    }
    if ok { 0 } else { 1 }
}

fn first_deployment(p: &Program) -> Option<&Deployment> {
    p.items.iter().find_map(|it| match it {
        Item::Deployment(d) => Some(d),
        _ => None,
    })
}

fn printed(o: &Output) -> Option<&str> {
    match o {
        Output::Print(Value::Text(s)) => Some(s),
        _ => None,
    }
}

fn run(p: &Program) -> u8 {
    match first_deployment(p) {
        None => {
            println!(
                "{}",
                show_diag(&Diag {
                    code: Code::BadEntry,
                    message: "no deployment".to_string(),
                })
            );
            1
        }
        Some(d) => match find_fn(p, &d.entry).and_then(|f| run_entry(p, f)) {
            Some(Ok(outs)) => {
                for o in &outs {
                    if let Some(s) = printed(o) {
                        println!("{}", s);
                    }
                }
                0
            }
            Some(Err(fault)) => {
                println!("fault {}", fault.text());
                1
            }
            None => 1,
        },
    }
}

fn usage() -> u8 {
    eprintln!("usage: brk check|run|test FILE");
    2
}

fn parse_error() -> u8 {
    println!(
        "{}",
        show_diag(&Diag {
            code: Code::Parse,
            message: "text is not a program".to_string(),
        })
    );
    1
}

fn cli() -> u8 {
    let args: Vec<String> = std::env::args_os()
        .skip(1)
        .map(|a| a.to_string_lossy().into_owned())
        .collect();
    match args.as_slice() {
        [cmd, file] => {
            if !["check", "run", "test"].contains(&cmd.as_str()) {
                usage()
            } else {
                match std::fs::read(file) {
                    Err(_) => parse_error(),
                    Ok(bytes) => match read(&bytes) {
                        None => parse_error(),
                        Some(p) => match check(&p) {
                            Err(ds) => {
                                for d in &ds {
                                    println!("{}", show_diag(d));
                                }
                                1
                            }
                            Ok(()) => match cmd.as_str() {
                                "run" => run(&p),
                                "test" => test(&p),
                                _ => 0,
                            },
                        },
                    },
                }
            }
        }
        _ => usage(),
    }
}

fn main() -> ExitCode {
    match std::thread::Builder::new().stack_size(1 << 30).spawn(cli) {
        Ok(handle) => match handle.join() {
            Ok(code) => ExitCode::from(code),
            Err(_) => ExitCode::FAILURE,
        },
        Err(_) => ExitCode::FAILURE,
    }
}
