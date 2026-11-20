use rug::ops::AssignRound;
use rug::{Float, Integer, Rational};

use crate::fmt::{FORMATS, Fmt};
use crate::fp;
use crate::stream::Stream;

const SEED: u64 = 0x0F10A7;
const DRAWS: usize = 100;
const LIT: &str = "0.1";
const SEARCH: u64 = 1 << 20;
const PARAMS: [&str; 3] = ["a", "b", "c"];

#[derive(Clone, Copy, PartialEq)]
enum Op {
    Lit,
    Add,
    Sub,
    Mul,
    Div,
    Sqrt,
    Fma,
    Eq,
    Lt,
}

const QUERIES: [Op; 9] = [
    Op::Lit,
    Op::Add,
    Op::Sub,
    Op::Mul,
    Op::Div,
    Op::Sqrt,
    Op::Fma,
    Op::Eq,
    Op::Lt,
];

const DRAWN: [Op; 6] = [Op::Add, Op::Sub, Op::Mul, Op::Div, Op::Sqrt, Op::Fma];

impl Op {
    fn name(self) -> &'static str {
        match self {
            Op::Lit => "Lit",
            Op::Add => "Add",
            Op::Sub => "Sub",
            Op::Mul => "Mul",
            Op::Div => "Div",
            Op::Sqrt => "Sqrt",
            Op::Fma => "Fma",
            Op::Eq => "Eq",
            Op::Lt => "Lt",
        }
    }

    fn head(self) -> &'static str {
        match self {
            Op::Lit => "",
            Op::Add => "+",
            Op::Sub => "-",
            Op::Mul => "*",
            Op::Div => "/",
            Op::Sqrt => "sqrt",
            Op::Fma => "fma",
            Op::Eq => "==",
            Op::Lt => "<",
        }
    }

    fn arity(self) -> usize {
        match self {
            Op::Lit => 0,
            Op::Sqrt => 1,
            Op::Fma => 3,
            Op::Add | Op::Sub | Op::Mul | Op::Div | Op::Eq | Op::Lt => 2,
        }
    }

    fn result(self, f: Fmt) -> &'static str {
        match self {
            Op::Eq | Op::Lt => "Bool",
            _ => f.ty(),
        }
    }
}

struct Query {
    f: Fmt,
    op: Op,
    form: String,
    cases: Vec<Vec<u64>>,
}

impl Query {
    fn name(&self) -> String {
        format!("{}_{}", self.op.name(), self.f.name())
    }
}

struct Edges {
    min_sub: String,
    two_sub: String,
    three_sub: String,
    max_sub: String,
    min_norm: String,
    max: String,
    below_max: String,
    two_below_max: String,
    top: String,
    half_ulp_max: String,
    quarter_ulp_max: String,
    up: String,
    up2: String,
    down: String,
    tie: String,
    half_tie: String,
}

fn pow2(f: Fmt, e: i32) -> u64 {
    fp::round(f, false, &(Rational::from(1) << e))
}

fn pow10(e: i32) -> Rational {
    let p = Integer::from(Integer::u_pow_u(10, e.unsigned_abs()));
    if e < 0 {
        Rational::from((Integer::from(1), p))
    } else {
        Rational::from(p)
    }
}

fn decimal(body: &str) -> Option<Rational> {
    let (mantissa, exp) = match body.split_once('e') {
        Some((m, e)) => (m, e.parse::<i32>().ok()?),
        None => (body, 0),
    };
    let (whole, part) = mantissa.split_once('.').unwrap_or((mantissa, ""));
    let digits = Integer::from_str_radix(&format!("{whole}{part}"), 10).ok()?;
    Some(Rational::from(digits) * pow10(exp - part.len() as i32))
}

fn parse(f: Fmt, t: &str) -> Result<u64, String> {
    let (neg, body) = match t.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, t),
    };
    let sign = if neg { f.sign() } else { 0 };
    let bits = match body {
        "nan" => Some(f.nan()),
        "inf" => Some(f.exponent_mask() | sign),
        _ => decimal(body).map(|r| fp::round(f, neg, &r)),
    };
    match bits {
        Some(b) if fp::text(f, b) == t => Ok(b),
        _ => Err(format!(
            "the case value {t} is not the canonical text of a value of the type {}",
            f.ty()
        )),
    }
}

struct Candidates {
    x: Rational,
    k: u32,
    chosen: (i32, Integer),
    all: Vec<(i32, Integer)>,
}

fn shape(t: &str) -> (u32, i32, Integer) {
    let body = t.trim_start_matches('-');
    let (mantissa, exp) = match body.split_once('e') {
        Some((m, e)) => (m, e.parse::<i32>().unwrap_or(0)),
        None => (body, 0),
    };
    let point = mantissa.find('.').unwrap_or(mantissa.len()) as i32;
    let all: String = mantissa.chars().filter(|c| *c != '.').collect();
    let lead = (all.len() - all.trim_start_matches('0').len()) as i32;
    let s = all.trim_matches('0');
    let digits = Integer::from_str_radix(s, 10).unwrap_or_default();
    (s.len() as u32, point - lead + exp, digits)
}

fn magnitude(f: Fmt, bits: u64) -> Rational {
    match fp::value(f, bits) {
        fp::Value::Finite { magnitude, .. } => magnitude,
        fp::Value::Nan | fp::Value::Inf { .. } => Rational::from(1) << (f.emax() + 1),
    }
}

fn candidates(f: Fmt, bits: u64) -> Candidates {
    let (k, n, s) = shape(&fp::text(f, bits));
    let below = magnitude(f, bits - 1);
    let above = magnitude(f, bits + 1);
    let low = Integer::from(Integer::u_pow_u(10, k - 1));
    let high = Integer::from(Integer::u_pow_u(10, k)) - 1u32;
    let mut all = Vec::new();
    for m in n - 1..=n + 1 {
        let scale = pow10(m - k as i32);
        let (_, first) = Rational::from(&below / &scale).fract_floor(Integer::new());
        let (_, last) = Rational::from(&above / &scale).fract_floor(Integer::new());
        let mut t = first.max(low.clone());
        let last = last.min(high.clone());
        while t <= last {
            if fp::round(f, false, &(Rational::from(&t) * &scale)) == bits {
                all.push((m, t.clone()));
            }
            t += 1u32;
        }
    }
    Candidates {
        x: magnitude(f, bits),
        k,
        chosen: (n, s),
        all,
    }
}

fn distance(c: &Candidates, (n, s): &(i32, Integer)) -> Rational {
    (Rational::from(s) * pow10(n - c.k as i32) - &c.x).abs()
}

fn closer_second(c: &Candidates) -> bool {
    c.all.len() == 2 && c.all[0].0 == c.all[1].0 && c.all[1] == c.chosen
}

fn tied(c: &Candidates) -> bool {
    let best = distance(c, &c.chosen);
    c.all.iter().filter(|p| distance(c, p) == best).count() == 2
}

fn spread(c: &Candidates) -> bool {
    c.all.windows(2).any(|w| w[0].0 != w[1].0)
}

fn search(f: Fmt, start: u64, what: &str, test: impl Fn(u64) -> bool) -> Result<u64, String> {
    (start..start + SEARCH)
        .find(|&b| test(b))
        .ok_or_else(|| format!("the search for {what} in {} ends with no value", f.ty()))
}

fn text_edges(f: Fmt) -> Result<Vec<String>, String> {
    let (digits, tiny) = match f {
        Fmt::F64 => (17, "-2.5e-300"),
        Fmt::F32 => (9, "-2.5e-30"),
    };
    let longest = search(f, parse(f, "0.1")?, "a text of the most digits", |b| {
        candidates(f, b).k == digits
    })?;
    let pair = search(f, pow2(f, 0), "a value with two shortest candidates", |b| {
        closer_second(&candidates(f, b))
    })?;
    let start = pow2(f, f.prec() as i32 - 4);
    let tie = search(f, start, "a value with two equally close candidates", |b| {
        tied(&candidates(f, b))
    })?;
    let wide = search(f, 1, "a value whose shortest candidates differ in n", |b| {
        spread(&candidates(f, b))
    })?;
    if f == Fmt::F64 && fp::text(f, wide) != "1e-323" {
        return Err(format!(
            "the search for a value whose shortest candidates differ in n gives {}, not 1e-323",
            fp::text(f, wide)
        ));
    }
    let mut list: Vec<String> = [
        "100000000000000000000",
        "1e+21",
        "0.000001",
        "1e-7",
        "0.0000015",
        "1.5e-7",
        "123",
        "12.3",
        "123.456",
        "2",
        tiny,
    ]
    .iter()
    .map(|t| t.to_string())
    .collect();
    list.extend([longest, pair, tie, wide].iter().map(|&b| fp::text(f, b)));
    Ok(list)
}

fn edges(f: Fmt) -> Edges {
    let m = f.prec() - 1;
    let p = f.prec() as i32;
    let one = pow2(f, 0);
    let max = f.exponent_mask() - 1;
    let t = |bits| fp::text(f, bits);
    Edges {
        min_sub: t(1),
        two_sub: t(2),
        three_sub: t(3),
        max_sub: t((1 << m) - 1),
        min_norm: t(1 << m),
        max: t(max),
        below_max: t(max - 1),
        two_below_max: t(max - 2),
        top: t(pow2(f, f.emax())),
        half_ulp_max: t(pow2(f, f.emax() - p)),
        quarter_ulp_max: t(pow2(f, f.emax() - p - 1)),
        up: t(one + 1),
        up2: t(one + 2),
        down: t(one - 1),
        tie: t(pow2(f, -p)),
        half_tie: t(pow2(f, -p - 1)),
    }
}

fn neg(t: &str) -> String {
    format!("-{t}")
}

fn rows(table: &[&[&str]]) -> Vec<Vec<String>> {
    table
        .iter()
        .map(|row| row.iter().map(|t| t.to_string()).collect())
        .collect()
}

fn add(e: &Edges, texts: &[String]) -> Vec<Vec<String>> {
    let nmin_sub = neg(&e.min_sub);
    let nmax = neg(&e.max);
    let mut list = rows(&[
        &["1", "2"],
        &["0.1", "0.2"],
        &["inf", "1"],
        &["-1", "-inf"],
        &["inf", "inf"],
        &["inf", "-inf"],
        &["-inf", "inf"],
        &["nan", "1"],
        &["1", "nan"],
        &["nan", "inf"],
        &["0", "0"],
        &["0", "-0"],
        &["-0", "0"],
        &["-0", "-0"],
        &["1.5", "-1.5"],
        &["-1.5", "1.5"],
        &[&e.min_sub, &e.min_sub],
        &[&e.max_sub, &e.min_sub],
        &[&e.min_norm, &nmin_sub],
        &[&e.min_sub, &nmin_sub],
        &[&nmin_sub, &nmin_sub],
        &[&e.max, &e.max],
        &[&nmax, &nmax],
        &[&e.max, &e.half_ulp_max],
        &[&e.max, &e.quarter_ulp_max],
        &[&nmax, &neg(&e.half_ulp_max)],
        &[&nmax, &neg(&e.quarter_ulp_max)],
        &["1", &e.tie],
        &[&e.up, &e.tie],
        &["-1", &neg(&e.tie)],
    ]);
    list.extend(texts.iter().map(|t| vec![t.clone(), "-0".to_string()]));
    list
}

fn sub(e: &Edges) -> Vec<Vec<String>> {
    let nmin_sub = neg(&e.min_sub);
    let nmax = neg(&e.max);
    rows(&[
        &["3", "1"],
        &["1", "3"],
        &["0.3", "0.1"],
        &["inf", "inf"],
        &["-inf", "-inf"],
        &["inf", "-inf"],
        &["-inf", "inf"],
        &["1", "inf"],
        &["nan", "1"],
        &["1", "nan"],
        &["0", "0"],
        &["0", "-0"],
        &["-0", "0"],
        &["-0", "-0"],
        &["1.5", "1.5"],
        &["-1.5", "-1.5"],
        &[&e.min_norm, &e.min_sub],
        &[&e.max_sub, &nmin_sub],
        &[&e.two_sub, &e.min_sub],
        &[&e.min_sub, &e.min_sub],
        &[&nmin_sub, &e.min_sub],
        &[&e.max, &nmax],
        &[&nmax, &e.max],
        &[&nmax, &e.half_ulp_max],
        &[&nmax, &e.quarter_ulp_max],
        &[&e.max, &neg(&e.half_ulp_max)],
        &["1", &e.half_tie],
        &[&e.up, &e.tie],
        &[&e.down, &e.half_tie],
    ])
}

fn mul(e: &Edges) -> Vec<Vec<String>> {
    let nmin_sub = neg(&e.min_sub);
    rows(&[
        &["1.5", "2"],
        &["-1.5", "2"],
        &["0.1", "3"],
        &["0", "inf"],
        &["inf", "0"],
        &["-0", "inf"],
        &["-inf", "-0"],
        &["inf", "inf"],
        &["inf", "-inf"],
        &["-inf", "-2"],
        &["nan", "1"],
        &["1", "nan"],
        &["nan", "0"],
        &["0", "0"],
        &["-0", "0"],
        &["0", "-0"],
        &["-0", "-0"],
        &["0", "-1"],
        &["-1", "-0"],
        &[&e.min_sub, "0.5"],
        &[&nmin_sub, "0.5"],
        &[&e.min_sub, "0.75"],
        &[&nmin_sub, "0.75"],
        &[&e.three_sub, "0.5"],
        &[&e.min_norm, "0.5"],
        &[&e.max_sub, "2"],
        &[&e.min_norm, &e.down],
        &[&e.min_sub, &e.min_sub],
        &[&nmin_sub, &e.min_sub],
        &[&e.max, "2"],
        &[&e.max, "-2"],
        &[&e.top, "2"],
        &[&e.below_max, &e.up],
        &[&e.two_below_max, &e.up],
        &[&neg(&e.two_below_max), &e.up],
    ])
}

fn div(e: &Edges) -> Vec<Vec<String>> {
    let nmin_sub = neg(&e.min_sub);
    rows(&[
        &["3", "2"],
        &["1", "3"],
        &["-1", "3"],
        &["1", "0"],
        &["1", "-0"],
        &["-1", "0"],
        &["-1", "-0"],
        &["0", "0"],
        &["-0", "0"],
        &["inf", "inf"],
        &["-inf", "inf"],
        &["nan", "1"],
        &["1", "nan"],
        &["nan", "0"],
        &["0", "1"],
        &["-0", "1"],
        &["0", "-1"],
        &["1", "inf"],
        &["-1", "inf"],
        &["1", "-inf"],
        &["inf", "2"],
        &["inf", "-0"],
        &[&e.min_norm, "2"],
        &[&e.min_sub, "2"],
        &[&e.min_sub, "1.5"],
        &[&e.three_sub, "2"],
        &[&e.min_sub, "-2"],
        &[&e.min_norm, &e.up],
        &[&e.min_norm, &e.max],
        &[&nmin_sub, &e.max],
        &[&e.max, "0.5"],
        &[&e.max, &e.down],
        &[&e.below_max, &e.down],
        &[&neg(&e.below_max), &e.down],
    ])
}

fn sqrt(e: &Edges) -> Vec<Vec<String>> {
    rows(&[
        &["4"],
        &["2"],
        &["0.01"],
        &["0"],
        &["-0"],
        &["inf"],
        &["-inf"],
        &["nan"],
        &["-1"],
        &[&neg(&e.min_sub)],
        &[&e.min_sub],
        &[&e.max_sub],
        &[&e.min_norm],
        &[&e.max],
        &[&e.down],
        &[&e.up],
    ])
}

fn fma(e: &Edges) -> Vec<Vec<String>> {
    let nmin_sub = neg(&e.min_sub);
    let nmax = neg(&e.max);
    rows(&[
        &["2", "3", "4"],
        &["inf", "0", "1"],
        &["0", "inf", "1"],
        &["inf", "0", "nan"],
        &["inf", "1", "-inf"],
        &["-inf", "1", "inf"],
        &["inf", "-1", "inf"],
        &["inf", "1", "inf"],
        &["inf", "2", "1"],
        &["1", "1", "-inf"],
        &["nan", "1", "1"],
        &["1", "nan", "1"],
        &["1", "1", "nan"],
        &["0", "0", "0"],
        &["0", "0", "-0"],
        &["-0", "0", "-0"],
        &["0", "-1", "0"],
        &["0", "-1", "-0"],
        &["1", "-1", "1"],
        &["-1", "-1", "-1"],
        &[&e.min_sub, &e.min_sub, "-0"],
        &[&e.min_sub, &nmin_sub, "0"],
        &[&e.min_sub, &nmin_sub, "-0"],
        &[&e.up, &e.up, &neg(&e.up2)],
        &["1", "1", &e.tie],
        &[&e.up, "1", &e.tie],
        &[&e.up, &e.tie, "1"],
        &[&e.min_sub, "0.5", "0"],
        &[&e.min_sub, "0.75", "0"],
        &[&e.min_sub, "0.5", &e.min_sub],
        &[&e.max_sub, "1", &e.min_sub],
        &[&e.min_norm, "1", &nmin_sub],
        &[&e.min_sub, &e.min_sub, &e.min_sub],
        &[&e.max, "2", &nmax],
        &[&e.max, "1", &e.max],
        &[&e.max, "1", &e.half_ulp_max],
        &[&e.max, "1", &e.quarter_ulp_max],
        &[&nmax, "1", &nmax],
        &[&nmax, "2", &e.max],
    ])
}

fn order(e: &Edges) -> Vec<Vec<String>> {
    let points = ["-inf", "-1", "-0", "0", "1", "inf", "nan"];
    let mut list: Vec<Vec<String>> = points
        .iter()
        .flat_map(|a| points.iter().map(|b| vec![a.to_string(), b.to_string()]))
        .collect();
    let nmin_sub = neg(&e.min_sub);
    list.extend(rows(&[
        &["-2", "-1"],
        &["-1", "-2"],
        &["1", "2"],
        &["2", "1"],
        &[&nmin_sub, "-0"],
        &["0", &e.min_sub],
        &[&e.min_sub, &nmin_sub],
        &[&e.max_sub, &e.min_norm],
        &["1", &e.up],
        &[&e.max, "inf"],
        &["-inf", &neg(&e.max)],
    ]));
    list
}

fn hand(op: Op, e: &Edges, texts: &[String]) -> Vec<Vec<String>> {
    match op {
        Op::Lit => vec![vec![]],
        Op::Add => add(e, texts),
        Op::Sub => sub(e),
        Op::Mul => mul(e),
        Op::Div => div(e),
        Op::Sqrt => sqrt(e),
        Op::Fma => fma(e),
        Op::Eq | Op::Lt => order(e),
    }
}

fn draws() -> Vec<(Op, Fmt, Vec<Vec<u64>>)> {
    let mut stream = Stream::new(SEED);
    let mut list = Vec::new();
    for op in DRAWN {
        for f in FORMATS {
            let lo = pow2(f, -10);
            let hi = pow2(f, 10);
            let mut cases = Vec::new();
            for _ in 0..DRAWS {
                let case: Vec<u64> = (0..op.arity()).map(|_| stream.whole(f)).collect();
                cases.push(case);
            }
            for _ in 0..DRAWS {
                let case: Vec<u64> = (0..op.arity())
                    .map(|_| stream.range(f, lo, hi, op != Op::Sqrt))
                    .collect();
                cases.push(case);
            }
            list.push((op, f, cases));
        }
    }
    list
}

fn key(f: Fmt, bits: u64) -> i128 {
    let magnitude = i128::from(bits & !f.sign());
    if bits & f.sign() == 0 {
        magnitude
    } else {
        -magnitude - 1
    }
}

fn answer(f: Fmt, op: Op, args: &[u64]) -> Result<String, String> {
    let x: Vec<Float> = args.iter().map(|&b| fp::to_float(f, b)).collect();
    let bits = match op {
        Op::Lit => parse(f, LIT)?,
        Op::Add => fp::eval(f, |r, rnd| r.assign_round(&x[0] + &x[1], rnd)),
        Op::Sub => fp::eval(f, |r, rnd| r.assign_round(&x[0] - &x[1], rnd)),
        Op::Mul => fp::eval(f, |r, rnd| r.assign_round(&x[0] * &x[1], rnd)),
        Op::Div => fp::eval(f, |r, rnd| r.assign_round(&x[0] / &x[1], rnd)),
        Op::Sqrt => fp::eval(f, |r, rnd| r.assign_round(x[0].sqrt_ref(), rnd)),
        Op::Fma => fp::eval(f, |r, rnd| {
            r.assign_round(x[0].mul_add_ref(&x[1], &x[2]), rnd)
        }),
        Op::Eq => return Ok((args[0] == args[1]).to_string()),
        Op::Lt => {
            let less = args[0] != args[1] && key(f, args[0]) <= key(f, args[1]);
            return Ok(less.to_string());
        }
    };
    Ok(fp::literal(f, bits))
}

fn form(f: Fmt, op: Op) -> Result<String, String> {
    match op {
        Op::Lit => Ok(fp::literal(f, parse(f, LIT)?)),
        _ => Ok(format!(
            "({} {})",
            op.head(),
            PARAMS[..op.arity()].join(" ")
        )),
    }
}

fn case(f: Fmt, op: Op, row: &[String]) -> Result<Vec<u64>, String> {
    if row.len() != op.arity() {
        return Err(format!(
            "a case of {}_{} has the wrong number of values",
            op.name(),
            f.name()
        ));
    }
    row.iter().map(|t| parse(f, t)).collect()
}

fn queries() -> Result<Vec<Query>, String> {
    let drawn = draws();
    let mut list = Vec::new();
    for f in FORMATS {
        let e = edges(f);
        let texts = text_edges(f)?;
        for op in QUERIES {
            let mut cases = hand(op, &e, &texts)
                .iter()
                .map(|row| case(f, op, row))
                .collect::<Result<Vec<Vec<u64>>, String>>()?;
            if let Some((_, _, more)) = drawn.iter().find(|(o, g, _)| *o == op && *g == f) {
                cases.extend(more.iter().cloned());
            }
            list.push(Query {
                f,
                op,
                form: form(f, op)?,
                cases,
            });
        }
    }
    Ok(list)
}

fn protocol(list: &[Query]) -> String {
    let lines: String = list
        .iter()
        .map(|q| {
            let params: Vec<String> = PARAMS[..q.op.arity()]
                .iter()
                .map(|p| format!("({p} {})", q.f.ty()))
                .collect();
            format!(
                "\n    (query {} ({}) {})",
                q.name(),
                params.join(" "),
                q.op.result(q.f)
            )
        })
        .collect();
    format!("  (protocol FloatOps{lines})")
}

fn machine(list: &[Query]) -> String {
    let cells: String = list
        .iter()
        .map(|q| format!("\n      (on {} (block (answer {})))", q.name(), q.form))
        .collect();
    format!(
        "  (machine FloatCalc (key Int) (protocol FloatOps) (uses) (init Ready)\n    (state Ready)\n    (in Ready{cells}))"
    )
}

fn example(q: &Query) -> Result<String, String> {
    let name = q.name();
    let mut lines = vec![
        format!(
            "  (example {} (machine FloatCalc) (key 1)",
            name.to_lowercase()
        ),
        "    (actor u)".to_string(),
    ];
    for case in &q.cases {
        let args: String = case
            .iter()
            .map(|&b| format!(" {}", fp::literal(q.f, b)))
            .collect();
        let value = answer(q.f, q.op, case)?;
        lines.push(format!(
            "    (send u {name}{args} (expect (answer {value})))"
        ));
    }
    Ok(lines.join("\n") + ")")
}

fn meter_protocol() -> String {
    format!(
        "  (protocol MeterOps\n    (command Set ((v {})) Unit (rejects)))",
        Fmt::F64.ty()
    )
}

fn meter_machine() -> String {
    format!(
        "  (machine Meter (key Int) (protocol MeterOps) (uses) (init Empty)\n    (state Empty)\n    (state Holding (v {}))\n    (group Any Empty Holding)\n    (in Any\n      (on Set (block (next (Holding v) (outcome (unit)))))))",
        Fmt::F64.ty()
    )
}

fn meter_example() -> Result<String, String> {
    let mut lines = vec![
        "  (example meter (machine Meter) (key 1)".to_string(),
        "    (actor u)".to_string(),
    ];
    for text in ["0.1", "-0", "nan"] {
        let v = fp::literal(Fmt::F64, parse(Fmt::F64, text)?);
        lines.push(format!(
            "    (send u Set {v} (expect (outcome (unit)) (state Holding {v})))"
        ));
    }
    Ok(lines.join("\n") + ")")
}

pub fn file() -> Result<String, String> {
    let list = queries()?;
    let mut items = vec![
        protocol(&list),
        machine(&list),
        meter_protocol(),
        meter_machine(),
    ];
    for q in &list {
        items.push(example(q)?);
    }
    items.push(meter_example()?);
    Ok(format!("(program\n{})\n", items.join("\n")))
}
