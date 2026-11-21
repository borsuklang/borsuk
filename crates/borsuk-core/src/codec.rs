use crate::check::{find_enum, find_newtype, find_record, is_type_name, type_names};
use crate::decimal::dec_in;
use crate::eval::Value;
use crate::float::Fmt;
use crate::ir::{Item, Name, Param, Program, Ty, Variant, XExpr, find_machine};
use crate::runtime::xvalues;

pub const FRAME_LIMIT: u64 = 1 << 32;

pub fn start_fuel(p: &Program) -> usize {
    type_names(p).len() + 3
}

pub const FORMAT_VERSION: u128 = 1;

pub fn find_inits<'a>(p: &'a Program, name: &str) -> Option<&'a [(Param, XExpr)]> {
    p.items.iter().find_map(|item| match item {
        Item::Record(r, _, inits) if r == name => Some(inits.as_slice()),
        _ => None,
    })
}

pub fn find_variant<'a>(c: &str, vs: &'a [Variant]) -> Option<(usize, &'a Variant)> {
    vs.iter().enumerate().find(|(_, v)| v.name == c)
}

pub fn type_named(p: &Program, t: &Ty) -> bool {
    match t {
        Ty::Option(t) => type_named(p, t),
        Ty::Result(a, b) => type_named(p, a) && type_named(p, b),
        Ty::Named(n) => is_type_name(p, n),
        _ => true,
    }
}

pub fn all_fixed(p: &Program, fuel: usize, ts: &[&Ty]) -> Option<bool> {
    let mut all = true;
    for t in ts {
        let x = is_fixed(p, fuel, t)?;
        all = x && all;
    }
    Some(all)
}

pub fn fixed_ty(p: &Program, fuel: usize, t: &Ty) -> Option<bool> {
    match t {
        Ty::Unit
        | Ty::Bool
        | Ty::Int
        | Ty::Time
        | Ty::Duration
        | Ty::F64
        | Ty::F32
        | Ty::Decimal(_) => Some(true),
        Ty::Text | Ty::Principal | Ty::StepId | Ty::Ticket => Some(false),
        Ty::Option(t) => fixed_ty(p, fuel, t),
        Ty::Result(a, b) => {
            let x = fixed_ty(p, fuel, a)?;
            let y = fixed_ty(p, fuel, b)?;
            Some(x && y)
        }
        Ty::Named(n) => match find_record(p, n) {
            Some(_) => Some(false),
            None => match find_enum(p, n) {
                Some(vs) => {
                    let ts: Vec<&Ty> = vs.iter().flat_map(|v| v.fields.iter()).collect();
                    all_fixed(p, fuel, &ts)
                }
                None => match find_newtype(p, n) {
                    Some(t) => is_fixed(p, fuel, t),
                    None => Some(false),
                },
            },
        },
    }
}

pub fn is_fixed(p: &Program, fuel: usize, t: &Ty) -> Option<bool> {
    match fuel {
        0 => None,
        _ => fixed_ty(p, fuel - 1, t),
    }
}

pub fn sum_sizes(p: &Program, fuel: usize, ts: &[&Ty]) -> Option<u64> {
    let mut sum = 0;
    for t in ts {
        let x = ty_size(p, fuel, t)?;
        sum = (x + sum).min(FRAME_LIMIT);
    }
    Some(sum)
}

pub fn max_sizes(p: &Program, fuel: usize, vs: &[Variant]) -> Option<u64> {
    let mut most = 0;
    for v in vs {
        let x = sum_sizes(p, fuel, &v.fields.iter().collect::<Vec<_>>())?;
        most = x.max(most);
    }
    Some(most)
}

pub fn size_ty(p: &Program, fuel: usize, t: &Ty) -> Option<u64> {
    match t {
        Ty::Unit => Some(0),
        Ty::Bool => Some(1),
        Ty::Int | Ty::Time | Ty::Duration | Ty::F64 => Some(8),
        Ty::F32 => Some(4),
        Ty::Decimal(_) => Some(16),
        Ty::Text | Ty::Principal | Ty::StepId | Ty::Ticket => None,
        Ty::Option(t) => size_ty(p, fuel, t).map(|x| (1 + x).min(FRAME_LIMIT)),
        Ty::Result(a, b) => {
            let x = size_ty(p, fuel, a)?;
            let y = size_ty(p, fuel, b)?;
            Some((1 + x.max(y)).min(FRAME_LIMIT))
        }
        Ty::Named(n) => match find_record(p, n) {
            Some(_) => None,
            None => match find_enum(p, n) {
                Some(vs) => max_sizes(p, fuel, vs).map(|x| (1 + x).min(FRAME_LIMIT)),
                None => match find_newtype(p, n) {
                    Some(t) => ty_size(p, fuel, t),
                    None => None,
                },
            },
        },
    }
}

pub fn ty_size(p: &Program, fuel: usize, t: &Ty) -> Option<u64> {
    match fuel {
        0 => None,
        _ => size_ty(p, fuel - 1, t),
    }
}

pub fn slot_of(p: &Program, t: &Ty) -> Option<Option<u64>> {
    match is_fixed(p, start_fuel(p), t) {
        Some(true) => ty_size(p, start_fuel(p), t).map(Some),
        Some(false) => Some(None),
        None => None,
    }
}

pub fn slots_of(p: &Program, ts: &[&Ty]) -> Option<Vec<Option<u64>>> {
    let mut ks = Vec::new();
    for t in ts {
        ks.push(slot_of(p, t)?);
    }
    Some(ks)
}

pub fn slot_width(k: Option<u64>) -> u64 {
    k.unwrap_or(4)
}

pub fn slots_width(ks: &[Option<u64>]) -> u64 {
    ks.iter().map(|k| slot_width(*k)).sum()
}

pub fn le_bytes(n: usize, x: u128) -> Vec<u8> {
    x.to_le_bytes()[..n].to_vec()
}

pub fn le_value(bs: &[u8]) -> u128 {
    let mut all = [0u8; 16];
    all[..bs.len()].copy_from_slice(bs);
    u128::from_le_bytes(all)
}

pub fn int_bytes(n: usize, x: i128) -> Vec<u8> {
    le_bytes(n, x as u128)
}

pub fn int_of(n: usize, bs: &[u8]) -> i128 {
    let shift = 128 - 8 * n;
    ((le_value(bs) << shift) as i128) >> shift
}

pub fn utf8(s: &str) -> Vec<u8> {
    s.as_bytes().to_vec()
}

pub fn from_utf8(bs: &[u8]) -> Option<String> {
    String::from_utf8(bs.to_vec()).ok()
}

pub fn float_ok(f: Fmt, x: u64) -> bool {
    x % (1 << (f.width() - 1)) <= ((1 << (f.width() - f.prec())) - 1) * (1 << (f.prec() - 1))
        || x == f.nan()
}

pub fn take_bytes(n: u64, bs: &[u8]) -> Option<(&[u8], &[u8])> {
    if n <= bs.len() as u64 {
        Some(bs.split_at(n as usize))
    } else {
        None
    }
}

pub fn slot_bytes(pos: u64, fs: &[(Option<u64>, Vec<u8>)]) -> Vec<u8> {
    let mut out = Vec::new();
    let mut pos = pos;
    for (k, e) in fs {
        match k {
            Some(_) => out.extend_from_slice(e),
            None => {
                out.extend(le_bytes(4, u128::from(pos)));
                pos += e.len() as u64;
            }
        }
    }
    out
}

pub fn part_bytes(fs: &[(Option<u64>, Vec<u8>)]) -> Vec<u8> {
    let mut out = Vec::new();
    for (k, e) in fs {
        match k {
            Some(_) => {}
            None => out.extend_from_slice(e),
        }
    }
    out
}

pub fn compose(head: &[u8], fs: &[(Option<u64>, Vec<u8>)]) -> Vec<u8> {
    let ks: Vec<Option<u64>> = fs.iter().map(|f| f.0).collect();
    let fixed_len = head.len() as u64 + slots_width(&ks);
    [head.to_vec(), slot_bytes(fixed_len, fs), part_bytes(fs)].concat()
}

pub fn pad_to(n: u64, bs: Vec<u8>) -> Option<Vec<u8>> {
    if n < FRAME_LIMIT {
        let pad = n.saturating_sub(bs.len() as u64) as usize;
        Some([bs, vec![0; pad]].concat())
    } else {
        None
    }
}

pub fn tagged(p: &Program, t: &Ty, tag: usize, ts: &[&Ty], vs: &[Value]) -> Option<Vec<u8>> {
    if tag < 1 << 8 && type_named(p, t) {
        match is_fixed(p, start_fuel(p), t) {
            Some(true) => {
                let n = ty_size(p, start_fuel(p), t)?;
                if n < FRAME_LIMIT {
                    let es = encode_list(p, ts, vs)?;
                    pad_to(n, [vec![tag as u8], es.concat()].concat())
                } else {
                    None
                }
            }
            Some(false) => {
                let ks = slots_of(p, ts)?;
                let es = encode_list(p, ts, vs)?;
                Some(compose(
                    &[tag as u8],
                    &ks.into_iter().zip(es).collect::<Vec<_>>(),
                ))
            }
            None => None,
        }
    } else {
        None
    }
}

pub fn record_bytes(p: &Program, ts: &[&Ty], es: Vec<Vec<u8>>) -> Option<Vec<u8>> {
    if ts.len() < 1 << 16 {
        let ks = slots_of(p, ts)?;
        Some(compose(
            &le_bytes(2, ts.len() as u128),
            &ks.into_iter().zip(es).collect::<Vec<_>>(),
        ))
    } else {
        None
    }
}

pub fn int_field(n: i64) -> Option<Vec<u8>> {
    Some(int_bytes(8, i128::from(n)))
}

pub fn int_fields(ns: &[i64]) -> Option<Vec<Vec<u8>>> {
    let mut es = Vec::new();
    for n in ns {
        es.push(int_field(*n)?);
    }
    Some(es)
}

pub fn step_bytes(p: &Program, m: &str, key: &Ty, ek: Vec<u8>, ns: &[i64]) -> Option<Vec<u8>> {
    let es = int_fields(ns)?;
    let ts: Vec<&Ty> = std::iter::once(key)
        .chain(std::iter::repeat_n(&Ty::Int, ns.len()))
        .collect();
    let ks = slots_of(p, &ts)?;
    let fs: Vec<(Option<u64>, Vec<u8>)> =
        ks.into_iter().zip(std::iter::once(ek).chain(es)).collect();
    Some(
        [
            le_bytes(4, utf8(m).len() as u128),
            utf8(m),
            compose(&[], &fs),
        ]
        .concat(),
    )
}

pub fn encode_value(p: &Program, ty: &Ty, v: &Value) -> Option<Vec<u8>> {
    match (ty, v) {
        (Ty::Unit, Value::Unit) => Some(Vec::new()),
        (Ty::Bool, Value::Bool(b)) => Some(vec![if *b { 1 } else { 0 }]),
        (Ty::Int, Value::Int(n)) => int_field(*n),
        (Ty::Time, Value::Time(n)) => int_field(*n),
        (Ty::Duration, Value::Dur(n)) => int_field(*n),
        (Ty::F64, Value::F64(b)) => {
            if float_ok(Fmt::B64, *b) {
                Some(le_bytes(8, u128::from(*b)))
            } else {
                None
            }
        }
        (Ty::F32, Value::F32(b)) => {
            if float_ok(Fmt::B32, u64::from(*b)) {
                Some(le_bytes(4, u128::from(*b)))
            } else {
                None
            }
        }
        (Ty::Decimal(s), Value::Dec(s2, c)) => {
            if s2 == s && dec_in(*c) {
                Some(int_bytes(16, *c))
            } else {
                None
            }
        }
        (Ty::Text, Value::Text(s)) => Some(utf8(s)),
        (Ty::Principal, Value::Principal(n)) => Some(utf8(n)),
        (
            Ty::StepId,
            Value::StepId {
                machine,
                key,
                life,
                seq,
            },
        ) => match find_machine(p, machine) {
            Some(mach) => {
                let ek = encode_value(p, &mach.key, key)?;
                step_bytes(p, machine, &mach.key, ek, &[*life, *seq])
            }
            None => None,
        },
        (
            Ty::Ticket,
            Value::Ticket {
                machine,
                key,
                life,
                seq,
                idx,
            },
        ) => match find_machine(p, machine) {
            Some(mach) => {
                let ek = encode_value(p, &mach.key, key)?;
                step_bytes(p, machine, &mach.key, ek, &[*life, *seq, *idx])
            }
            None => None,
        },
        (Ty::Option(_), Value::None) => tagged(p, ty, 0, &[], &[]),
        (Ty::Option(t), Value::Some(w)) => tagged(p, ty, 1, &[&**t], std::slice::from_ref(w)),
        (Ty::Result(a, _), Value::Ok(w)) => tagged(p, ty, 0, &[&**a], std::slice::from_ref(w)),
        (Ty::Result(_, b), Value::Err(w)) => tagged(p, ty, 1, &[&**b], std::slice::from_ref(w)),
        (Ty::Named(n), Value::Con(c, args)) => match find_record(p, n) {
            Some(fs) => {
                if c == n {
                    let ts: Vec<&Ty> = fs.iter().map(|f| &f.ty).collect();
                    let es = encode_list(p, &ts, args)?;
                    record_bytes(p, &ts, es)
                } else {
                    None
                }
            }
            None => match find_enum(p, n) {
                Some(vs) => match find_variant(c, vs) {
                    Some((i, v)) => tagged(p, ty, i, &v.fields.iter().collect::<Vec<_>>(), args),
                    None => None,
                },
                None => match find_newtype(p, n) {
                    Some(inner) => {
                        if c == n {
                            let es = encode_list(p, &[inner], args)?;
                            match <[Vec<u8>; 1]>::try_from(es) {
                                Ok([e]) => Some(e),
                                Err(_) => None,
                            }
                        } else {
                            None
                        }
                    }
                    None => None,
                },
            },
        },
        _ => None,
    }
}

pub fn encode_list(p: &Program, ts: &[&Ty], vs: &[Value]) -> Option<Vec<Vec<u8>>> {
    if ts.len() != vs.len() {
        return None;
    }
    let mut es = Vec::new();
    for (t, v) in ts.iter().zip(vs) {
        es.push(encode_value(p, t, v)?);
    }
    Some(es)
}

pub fn encode(p: &Program, t: &Ty, v: &Value) -> Option<Vec<u8>> {
    let body = encode_value(p, t, v)?;
    if 2 + (body.len() as u64) < FRAME_LIMIT {
        let mut frame = le_bytes(2, FORMAT_VERSION);
        frame.extend_from_slice(&body);
        Some(frame)
    } else {
        None
    }
}

pub enum Slot<'a> {
    Bytes(&'a [u8]),
    Offset(u64),
}

pub fn read_slots<'a>(ks: &[Option<u64>], bs: &'a [u8]) -> Option<Vec<Slot<'a>>> {
    let mut xs = Vec::new();
    let mut bs = bs;
    for k in ks {
        match k {
            Some(n) => {
                let (s, rest) = take_bytes(*n, bs)?;
                xs.push(Slot::Bytes(s));
                bs = rest;
            }
            None => {
                let (s, rest) = take_bytes(4, bs)?;
                xs.push(Slot::Offset(le_value(s) as u64));
                bs = rest;
            }
        }
    }
    Some(xs)
}

pub fn slot_offsets(xs: &[Slot]) -> Vec<u64> {
    let mut os = Vec::new();
    for x in xs {
        match x {
            Slot::Bytes(_) => {}
            Slot::Offset(o) => os.push(*o),
        }
    }
    os
}

pub fn cut_parts<'a>(pos: u64, os: &[u64], rest: &'a [u8]) -> Option<Vec<&'a [u8]>> {
    let mut parts = Vec::new();
    let mut pos = pos;
    let mut rest = rest;
    for o in os {
        if pos <= *o && o - pos <= rest.len() as u64 {
            let (part, next) = rest.split_at((o - pos) as usize);
            parts.push(part);
            pos = *o;
            rest = next;
        } else {
            return None;
        }
    }
    parts.push(rest);
    Some(parts)
}

pub fn parts_of<'a>(fixed_len: u64, bs: &'a [u8], os: &[u64]) -> Option<Vec<&'a [u8]>> {
    match os.split_first() {
        None => {
            if bs.len() as u64 == fixed_len {
                Some(Vec::new())
            } else {
                None
            }
        }
        Some((o, os)) => {
            if *o == fixed_len {
                cut_parts(*o, os, bs.get(fixed_len as usize..).unwrap_or_default())
            } else {
                None
            }
        }
    }
}

pub fn place_parts<'a>(xs: &[Slot<'a>], ps: Vec<&'a [u8]>) -> Option<Vec<&'a [u8]>> {
    let mut out = Vec::new();
    let mut ps = ps.into_iter();
    for x in xs {
        match x {
            Slot::Bytes(s) => out.push(*s),
            Slot::Offset(_) => out.push(ps.next()?),
        }
    }
    match ps.next() {
        None => Some(out),
        Some(_) => None,
    }
}

pub fn segments<'a>(p: &Program, head: u64, ts: &[&Ty], bs: &'a [u8]) -> Option<Vec<&'a [u8]>> {
    let ks = slots_of(p, ts)?;
    let fixed_len = head + slots_width(&ks);
    if fixed_len <= bs.len() as u64 {
        let xs = read_slots(&ks, &bs[head as usize..])?;
        let ps = parts_of(fixed_len, bs, &slot_offsets(&xs))?;
        place_parts(&xs, ps)
    } else {
        None
    }
}

pub fn padded_segments<'a>(p: &Program, ts: &[&Ty], bs: &'a [u8]) -> Option<Vec<&'a [u8]>> {
    let ks = slots_of(p, ts)?;
    let xs = read_slots(&ks, bs)?;
    if bs[slots_width(&ks) as usize..].iter().all(|b| *b == 0) {
        place_parts(&xs, Vec::new())
    } else {
        None
    }
}

pub fn variant_segments<'a>(
    p: &Program,
    t: &Ty,
    ts: &[&Ty],
    bs: &'a [u8],
) -> Option<Vec<&'a [u8]>> {
    if type_named(p, t) {
        match is_fixed(p, start_fuel(p), t) {
            Some(true) => {
                let n = ty_size(p, start_fuel(p), t)?;
                if bs.len() as u64 == n {
                    padded_segments(p, ts, bs.get(1..).unwrap_or_default())
                } else {
                    None
                }
            }
            Some(false) => segments(p, 1, ts, bs),
            None => None,
        }
    } else {
        None
    }
}

pub fn decode_fields(
    p: &Program,
    fuel: usize,
    ts: &[&Ty],
    ss: &[&[u8]],
) -> Option<(Vec<Value>, bool)> {
    if ts.len() != ss.len() {
        return None;
    }
    let mut vs = Vec::new();
    let mut all = true;
    for (t, s) in ts.iter().zip(ss) {
        let (v, f) = decode_at(p, fuel, t, s)?;
        vs.push(v);
        all = f && all;
    }
    Some((vs, all))
}

pub fn decode_int(bs: &[u8]) -> Option<i64> {
    if bs.len() == 8 {
        Some(int_of(8, bs) as i64)
    } else {
        None
    }
}

pub fn decode_ints(ss: &[&[u8]]) -> Option<Vec<i64>> {
    let mut ns = Vec::new();
    for s in ss {
        ns.push(decode_int(s)?);
    }
    Some(ns)
}

pub fn decode_step(
    p: &Program,
    fuel: usize,
    count: usize,
    bs: &[u8],
) -> Option<(Name, Value, Vec<i64>, bool)> {
    let (len, rest) = take_bytes(4, bs)?;
    let (name, body) = take_bytes(le_value(len) as u64, rest)?;
    let m = from_utf8(name)?;
    let mach = find_machine(p, &m)?;
    let ts: Vec<&Ty> = std::iter::once(&mach.key)
        .chain(std::iter::repeat_n(&Ty::Int, count))
        .collect();
    let ss = segments(p, 0, &ts, body)?;
    match ss.split_first() {
        Some((sk, sn)) => {
            let (k, f) = decode_at(p, fuel, &mach.key, sk)?;
            let ns = decode_ints(sn)?;
            Some((m, k, ns, f))
        }
        None => None,
    }
}

pub fn init_values(p: &Program, n: &str, missing: usize) -> Option<Vec<Value>> {
    let inits = find_inits(p, n)?;
    if missing <= inits.len() {
        let xs: Vec<XExpr> = inits[inits.len() - missing..]
            .iter()
            .map(|(_, x)| x.clone())
            .collect();
        xvalues(None, &xs)
    } else {
        None
    }
}

pub fn decode_record(
    p: &Program,
    fuel: usize,
    n: &str,
    fs: &[&Param],
    bs: &[u8],
) -> Option<(Value, bool)> {
    let (count, _) = take_bytes(2, bs)?;
    let k = le_value(count) as usize;
    if k <= fs.len() {
        let ts: Vec<&Ty> = fs[..k].iter().map(|f| &f.ty).collect();
        let ss = segments(p, 2, &ts, bs)?;
        let (vs, f) = decode_fields(p, fuel, &ts, &ss)?;
        let rest = init_values(p, n, fs.len() - k)?;
        Some((
            Value::Con(n.to_string(), [vs, rest].concat()),
            f && k == fs.len(),
        ))
    } else {
        None
    }
}

pub fn decode_ty(p: &Program, fuel: usize, ty: &Ty, bs: &[u8]) -> Option<(Value, bool)> {
    match ty {
        Ty::Unit => {
            if bs.is_empty() {
                Some((Value::Unit, true))
            } else {
                None
            }
        }
        Ty::Bool => match bs {
            [b] => {
                if *b == 0 {
                    Some((Value::Bool(false), true))
                } else if *b == 1 {
                    Some((Value::Bool(true), true))
                } else {
                    None
                }
            }
            _ => None,
        },
        Ty::Int => decode_int(bs).map(|n| (Value::Int(n), true)),
        Ty::Time => decode_int(bs).map(|n| (Value::Time(n), true)),
        Ty::Duration => decode_int(bs).map(|n| (Value::Dur(n), true)),
        Ty::F64 => {
            if bs.len() == 8 && float_ok(Fmt::B64, le_value(bs) as u64) {
                Some((Value::F64(le_value(bs) as u64), true))
            } else {
                None
            }
        }
        Ty::F32 => {
            if bs.len() == 4 && float_ok(Fmt::B32, le_value(bs) as u64) {
                Some((Value::F32(le_value(bs) as u32), true))
            } else {
                None
            }
        }
        Ty::Decimal(s) => {
            if bs.len() == 16 && dec_in(int_of(16, bs)) {
                Some((Value::Dec(*s, int_of(16, bs)), true))
            } else {
                None
            }
        }
        Ty::Text => from_utf8(bs).map(|s| (Value::Text(s), true)),
        Ty::Principal => from_utf8(bs).map(|s| (Value::Principal(s), true)),
        Ty::StepId => {
            let (m, k, ns, f) = decode_step(p, fuel, 2, bs)?;
            match ns.as_slice() {
                [l, q] => Some((
                    Value::StepId {
                        machine: m,
                        key: Box::new(k),
                        life: *l,
                        seq: *q,
                    },
                    f,
                )),
                _ => None,
            }
        }
        Ty::Ticket => {
            let (m, k, ns, f) = decode_step(p, fuel, 3, bs)?;
            match ns.as_slice() {
                [l, q, i] => Some((
                    Value::Ticket {
                        machine: m,
                        key: Box::new(k),
                        life: *l,
                        seq: *q,
                        idx: *i,
                    },
                    f,
                )),
                _ => None,
            }
        }
        Ty::Option(t) => match bs.first() {
            Some(tag) => {
                if *tag == 0 {
                    let ss = variant_segments(p, ty, &[], bs)?;
                    if ss.is_empty() {
                        Some((Value::None, true))
                    } else {
                        None
                    }
                } else if *tag == 1 {
                    let ss = variant_segments(p, ty, &[&**t], bs)?;
                    match ss.as_slice() {
                        [s] => decode_ty(p, fuel, t, s).map(|(v, f)| (Value::Some(Box::new(v)), f)),
                        _ => None,
                    }
                } else {
                    None
                }
            }
            None => None,
        },
        Ty::Result(a, b) => match bs.first() {
            Some(tag) => {
                if *tag == 0 {
                    let ss = variant_segments(p, ty, &[&**a], bs)?;
                    match ss.as_slice() {
                        [s] => decode_ty(p, fuel, a, s).map(|(v, f)| (Value::Ok(Box::new(v)), f)),
                        _ => None,
                    }
                } else if *tag == 1 {
                    let ss = variant_segments(p, ty, &[&**b], bs)?;
                    match ss.as_slice() {
                        [s] => decode_ty(p, fuel, b, s).map(|(v, f)| (Value::Err(Box::new(v)), f)),
                        _ => None,
                    }
                } else {
                    None
                }
            }
            None => None,
        },
        Ty::Named(n) => match find_record(p, n) {
            Some(fs) => decode_record(p, fuel, n, &fs, bs),
            None => match find_enum(p, n) {
                Some(vs) => match bs.first() {
                    Some(tag) => match vs.get(usize::from(*tag)) {
                        Some(v) => {
                            if find_variant(&v.name, vs).map(|(i, _)| i) == Some(usize::from(*tag))
                            {
                                let ss = variant_segments(
                                    p,
                                    ty,
                                    &v.fields.iter().collect::<Vec<_>>(),
                                    bs,
                                )?;
                                let (vals, f) = decode_fields(
                                    p,
                                    fuel,
                                    &v.fields.iter().collect::<Vec<_>>(),
                                    &ss,
                                )?;
                                Some((Value::Con(v.name.clone(), vals), f))
                            } else {
                                None
                            }
                        }
                        None => None,
                    },
                    None => None,
                },
                None => match find_newtype(p, n) {
                    Some(inner) => decode_at(p, fuel, inner, bs)
                        .map(|(v, f)| (Value::Con(n.clone(), vec![v]), f)),
                    None => None,
                },
            },
        },
    }
}

pub fn decode_at(p: &Program, fuel: usize, t: &Ty, bs: &[u8]) -> Option<(Value, bool)> {
    match fuel {
        0 => None,
        _ => decode_ty(p, fuel - 1, t, bs),
    }
}

pub fn decode_frame(p: &Program, t: &Ty, b: &[u8]) -> Option<(Value, bool)> {
    if (b.len() as u64) < FRAME_LIMIT {
        match take_bytes(2, b) {
            Some((v, body)) => {
                if le_value(v) == FORMAT_VERSION {
                    decode_at(p, start_fuel(p), t, body)
                } else {
                    None
                }
            }
            None => None,
        }
    } else {
        None
    }
}

pub fn decode(p: &Program, t: &Ty, b: &[u8]) -> Option<Value> {
    decode_frame(p, t, b).map(|(v, _)| v)
}

pub fn full(p: &Program, t: &Ty, b: &[u8]) -> bool {
    match decode_frame(p, t, b) {
        Some((_, f)) => f,
        None => false,
    }
}
