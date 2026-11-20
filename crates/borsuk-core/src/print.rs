use crate::check::Diag;
use crate::eval::{Envelope, Output, Value};
use crate::ir::EnvField;
use crate::runtime::{Event, Reply};

pub fn form(parts: &[String]) -> String {
    let mut s = String::from("(");
    s.push_str(&parts.join(" "));
    s.push(')');
    s
}

pub fn escape_text(s: &str) -> String {
    let mut out = String::new();
    for c in s.chars() {
        if c == '"' {
            out.push_str("\\\"");
        } else if c == '\\' {
            out.push_str("\\\\");
        } else {
            out.push(c);
        }
    }
    out
}

pub fn quote(s: &str) -> String {
    let mut out = String::from("\"");
    out.push_str(&escape_text(s));
    out.push('"');
    out
}

pub fn show_value(v: &Value) -> String {
    match v {
        Value::Int(n) => n.to_string(),
        Value::Bool(b) => {
            if *b {
                String::from("true")
            } else {
                String::from("false")
            }
        }
        Value::Unit => String::from("(unit)"),
        Value::Text(s) => quote(s),
        Value::Dur(n) => form(&[String::from("dur"), n.to_string()]),
        Value::Time(n) => form(&[String::from("time"), n.to_string()]),
        Value::Principal(name) => form(&[String::from("principal"), quote(name)]),
        Value::StepId {
            machine,
            key,
            life,
            seq,
        } => form(&[
            String::from("step"),
            machine.clone(),
            show_value(key),
            life.to_string(),
            seq.to_string(),
        ]),
        Value::Ticket {
            machine,
            key,
            life,
            seq,
            idx,
        } => form(&[
            String::from("ticket"),
            machine.clone(),
            show_value(key),
            life.to_string(),
            seq.to_string(),
            idx.to_string(),
        ]),
        Value::Con(name, args) => {
            let mut parts = vec![name.clone()];
            parts.extend(show_values(args));
            form(&parts)
        }
        Value::Some(v) => form(&[String::from("some"), show_value(v)]),
        Value::None => String::from("(none)"),
        Value::Ok(v) => form(&[String::from("ok"), show_value(v)]),
        Value::Err(v) => form(&[String::from("err"), show_value(v)]),
    }
}

pub fn show_values(vs: &[Value]) -> Vec<String> {
    vs.iter().map(show_value).collect()
}

pub fn show_reply(r: &Reply) -> String {
    match r {
        Reply::Outcome(v) => form(&[String::from("outcome"), show_value(v)]),
        Reply::Reject(reason) => form(&[String::from("reject"), reason.clone()]),
        Reply::Answer(v) => form(&[String::from("answer"), show_value(v)]),
        Reply::Ignored => String::from("(ignored)"),
        Reply::Fault(f) => form(&[String::from("fault"), String::from(f.text())]),
        Reply::Next => String::from("(next)"),
    }
}

pub fn show_output(o: &Output) -> String {
    match o {
        Output::Print(v) => form(&[String::from("ConsoleOut.print"), show_value(v)]),
        Output::After(d, t) => form(&[String::from("Timer.after"), show_value(d), show_value(t)]),
        Output::Cancel(t) => form(&[String::from("Timer.cancel"), show_value(t)]),
    }
}

pub fn show_envelope(env: &Envelope) -> Vec<String> {
    let mut input = vec![env.input.clone()];
    input.extend(show_values(&env.args));
    vec![
        form(&[String::from("now"), show_value(&Value::Time(env.now))]),
        form(&[
            String::from("deadline"),
            show_value(&Value::Time(env.deadline)),
        ]),
        form(&[
            String::from("by"),
            show_value(&Value::Principal(env.sender.clone())),
        ]),
        form(&[String::from("input"), form(&input)]),
    ]
}

pub fn show_instance(env: &Envelope) -> String {
    form(&[env.machine.clone(), show_value(&env.key)])
}

pub fn show_event(e: &Event) -> String {
    match e {
        Event::Step(env, reply, state, outputs) => {
            let mut parts = vec![String::from("step"), show_value(&env.field(EnvField::Step))];
            parts.extend(show_envelope(env));
            let mut fields = vec![state.name.clone()];
            fields.extend(show_values(&state.fields));
            let mut outs = vec![String::from("outputs")];
            outs.extend(outputs.iter().map(show_output));
            parts.push(form(&[String::from("result"), show_reply(reply)]));
            parts.push(form(&[String::from("state"), form(&fields)]));
            parts.push(form(&outs));
            form(&parts)
        }
        Event::Query(env, reply) => {
            let mut parts = vec![String::from("query"), show_instance(env)];
            parts.extend(show_envelope(env));
            parts.push(form(&[String::from("result"), show_reply(reply)]));
            form(&parts)
        }
        Event::Refused(env) => {
            let mut parts = vec![String::from("refused"), show_instance(env)];
            parts.extend(show_envelope(env));
            parts.push(String::from("forbidden"));
            form(&parts)
        }
    }
}

pub fn show_diag(d: &Diag) -> String {
    let mut s = String::from("error[");
    s.push_str(d.code.text());
    s.push_str("]: ");
    s.push_str(&d.message);
    s
}
