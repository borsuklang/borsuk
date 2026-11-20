use rug::{Integer, Rational};
use std::cmp::Ordering;

#[derive(Clone, Copy)]
enum Ty {
    Int,
    Bool,
    Dec(u32),
}

impl Ty {
    fn text(self) -> String {
        match self {
            Ty::Int => "Int".to_string(),
            Ty::Bool => "Bool".to_string(),
            Ty::Dec(s) => format!("(Decimal {s})"),
        }
    }

    fn scale(self) -> u32 {
        match self {
            Ty::Dec(s) => s,
            Ty::Int | Ty::Bool => 0,
        }
    }
}

#[derive(Clone, Copy)]
enum Mode {
    Up,
    Down,
    Ceiling,
    Floor,
    HalfUp,
    HalfDown,
    HalfEven,
    Exact,
}

const MODES: [Mode; 8] = [
    Mode::Up,
    Mode::Down,
    Mode::Ceiling,
    Mode::Floor,
    Mode::HalfUp,
    Mode::HalfDown,
    Mode::HalfEven,
    Mode::Exact,
];

impl Mode {
    fn name(self) -> &'static str {
        match self {
            Mode::Up => "up",
            Mode::Down => "down",
            Mode::Ceiling => "ceiling",
            Mode::Floor => "floor",
            Mode::HalfUp => "half_up",
            Mode::HalfDown => "half_down",
            Mode::HalfEven => "half_even",
            Mode::Exact => "exact",
        }
    }
}

#[derive(PartialEq)]
enum Fault {
    Overflow,
    Inexact,
    DivZero,
}

impl Fault {
    fn name(&self) -> &'static str {
        match self {
            Fault::Overflow => "overflow",
            Fault::Inexact => "inexact",
            Fault::DivZero => "div_zero",
        }
    }
}

enum Op {
    Lit(Integer),
    Add,
    Sub,
    Mul,
    Eq,
    Lt,
    Round(Mode),
    Div(Mode),
}

struct Query {
    name: String,
    params: Vec<(&'static str, Ty)>,
    result: Ty,
    op: Op,
    cases: Vec<Vec<String>>,
}

struct Num {
    c: Integer,
    scale: u32,
}

fn pow10(s: u32) -> Integer {
    Integer::from(Integer::u_pow_u(10, s))
}

fn max() -> Integer {
    pow10(38) - 1
}

fn digits(c: &Integer, s: u32) -> String {
    let s = s as usize;
    let body = format!("{:0>width$}", c.as_abs().to_string(), width = s + 1);
    let (whole, part) = body.split_at(body.len() - s);
    let sign = if c.is_negative() { "-" } else { "" };
    if s == 0 {
        format!("{sign}{whole}")
    } else {
        format!("{sign}{whole}.{part}")
    }
}

fn value(ty: Ty, k: &Integer) -> String {
    match ty {
        Ty::Int => k.to_string(),
        Ty::Bool => (*k == 1).to_string(),
        Ty::Dec(s) => format!("(dec {})", digits(k, s)),
    }
}

fn inside(ty: Ty, k: &Integer) -> bool {
    match ty {
        Ty::Int => k.to_i64().is_some(),
        Ty::Bool => *k == 0 || *k == 1,
        Ty::Dec(_) => k.cmp_abs(&max()) != Ordering::Greater,
    }
}

fn fit(ty: Ty, k: Integer) -> Result<String, Fault> {
    if inside(ty, &k) {
        Ok(value(ty, &k))
    } else {
        Err(Fault::Overflow)
    }
}

fn parse(text: &str, ty: Ty) -> Result<Num, String> {
    let point = text.find('.').map_or(0, |i| text.len() - i - 1);
    let wanted = match ty {
        Ty::Dec(_) => format!("(dec {text})"),
        Ty::Int | Ty::Bool => text.to_string(),
    };
    match Integer::from_str_radix(&text.replace('.', ""), 10) {
        Ok(c) if point == ty.scale() as usize && fit(ty, c.clone()) == Ok(wanted) => Ok(Num {
            c,
            scale: ty.scale(),
        }),
        _ => Err(format!(
            "the case value {text} is not the canonical text of a value of the type {}",
            ty.text()
        )),
    }
}

fn exact(n: &Num) -> Rational {
    Rational::from((n.c.clone(), pow10(n.scale)))
}

fn round(r: Rational, mode: Mode) -> Result<Integer, Fault> {
    let (fract, floor) = r.fract_floor(Integer::new());
    if fract.is_zero() {
        return Ok(floor);
    }
    let negative = floor.is_negative();
    let next = match (mode, fract.cmp(&Rational::from((1, 2)))) {
        (Mode::Exact, _) => return Err(Fault::Inexact),
        (Mode::Up, _) => !negative,
        (Mode::Down, _) => negative,
        (Mode::Ceiling, _) => true,
        (Mode::Floor, _) => false,
        (_, Ordering::Less) => false,
        (_, Ordering::Greater) => true,
        (Mode::HalfUp, Ordering::Equal) => !negative,
        (Mode::HalfDown, Ordering::Equal) => negative,
        (Mode::HalfEven, Ordering::Equal) => floor.is_odd(),
    };
    Ok(if next { floor + 1 } else { floor })
}

fn scaled(r: Rational, ty: Ty) -> Rational {
    r * Rational::from(pow10(ty.scale()))
}

fn eval(q: &Query, args: &[Num]) -> Result<String, Fault> {
    match &q.op {
        Op::Lit(c) => fit(q.result, c.clone()),
        Op::Add => fit(q.result, Integer::from(&args[0].c + &args[1].c)),
        Op::Sub => fit(q.result, Integer::from(&args[0].c - &args[1].c)),
        Op::Mul => fit(q.result, Integer::from(&args[0].c * &args[1].c)),
        Op::Eq => fit(q.result, Integer::from(u8::from(args[0].c == args[1].c))),
        Op::Lt => fit(q.result, Integer::from(u8::from(args[0].c < args[1].c))),
        Op::Round(mode) => fit(q.result, round(scaled(exact(&args[0]), q.result), *mode)?),
        Op::Div(mode) => {
            if args[1].c.is_zero() {
                return Err(Fault::DivZero);
            }
            let quotient = exact(&args[0]) / exact(&args[1]);
            fit(q.result, round(scaled(quotient, q.result), *mode)?)
        }
    }
}

fn expr(q: &Query) -> String {
    let names: Vec<&str> = q.params.iter().map(|p| p.0).collect();
    let operands = names.join(" ");
    match &q.op {
        Op::Lit(c) => value(q.result, c),
        Op::Add => format!("(+ {operands})"),
        Op::Sub => format!("(- {operands})"),
        Op::Mul => format!("(* {operands})"),
        Op::Eq => format!("(== {operands})"),
        Op::Lt => format!("(< {operands})"),
        Op::Round(mode) => format!("(round {} {} {operands})", q.result.text(), mode.name()),
        Op::Div(mode) => format!("(div {} {} {operands})", q.result.text(), mode.name()),
    }
}

fn rows(table: &[&[&str]]) -> Vec<Vec<String>> {
    table
        .iter()
        .map(|row| row.iter().map(|t| t.to_string()).collect())
        .collect()
}

fn nines(s: u32) -> String {
    digits(&max(), s)
}

fn neg(text: &str) -> String {
    format!("-{text}")
}

fn add_d2() -> Vec<Vec<String>> {
    let m = nines(2);
    let n = neg(&m);
    rows(&[
        &["1.25", "2.50"],
        &["0.05", "0.05"],
        &["-1.25", "1.25"],
        &["-0.05", "0.00"],
        &["0.00", "0.00"],
        &["-1.25", "-2.50"],
        &[&m, "0.00"],
        &[&m, "0.01"],
        &[&n, "-0.01"],
        &[&m, &n],
    ])
}

fn sub_d2() -> Vec<Vec<String>> {
    let m = nines(2);
    let n = neg(&m);
    rows(&[
        &["3.75", "1.25"],
        &["1.25", "3.75"],
        &["0.10", "0.05"],
        &["0.00", "0.05"],
        &["-0.05", "-0.05"],
        &[&m, "0.00"],
        &[&m, "-0.01"],
        &[&n, "0.01"],
        &[&n, "0.00"],
        &[&m, &m],
    ])
}

fn add_d0() -> Vec<Vec<String>> {
    let m = nines(0);
    let n = neg(&m);
    rows(&[
        &["7", "5"],
        &["-7", "0"],
        &["0", "0"],
        &["-7", "7"],
        &[&m, "0"],
        &[&m, "1"],
        &[&n, "-1"],
        &[&m, "-1"],
        &[&n, &m],
    ])
}

fn mul_d2_d3() -> Vec<Vec<String>> {
    let m = nines(2);
    let n = neg(&m);
    rows(&[
        &["1.25", "2.000"],
        &["0.01", "0.001"],
        &["-1.50", "2.500"],
        &["-1.50", "-2.500"],
        &["0.00", "-1.000"],
        &["12.34", "1000.000"],
        &[&m, "0.001"],
        &[&m, "0.002"],
        &[&n, "0.001"],
        &[&n, "0.002"],
    ])
}

fn mul_d20_d17() -> Vec<Vec<String>> {
    let m = nines(20);
    rows(&[
        &["0.00000000000000000001", "0.00000000000000001"],
        &["1.00000000000000000000", "1.00000000000000000"],
        &["9.99999999999999999999", "0.99999999999999999"],
        &["-9.99999999999999999999", "-0.99999999999999999"],
        &["10.00000000000000000000", "1.00000000000000000"],
        &["-10.00000000000000000000", "1.00000000000000000"],
        &["-0.50000000000000000000", "0.20000000000000000"],
        &["0.00000000000000000000", "-1.00000000000000000"],
        &[&m, "0.00000000000000001"],
        &[&m, "0.00000000000000002"],
    ])
}

fn eq_d2() -> Vec<Vec<String>> {
    let m = nines(2);
    let n = neg(&m);
    rows(&[
        &["1.25", "1.25"],
        &["1.25", "1.26"],
        &["-0.05", "0.05"],
        &["0.00", "0.00"],
        &["0.10", "0.01"],
        &[&m, &m],
        &[&n, &m],
    ])
}

fn lt_d2() -> Vec<Vec<String>> {
    let m = nines(2);
    let n = neg(&m);
    rows(&[
        &["1.25", "1.26"],
        &["1.26", "1.25"],
        &["1.25", "1.25"],
        &["-1.25", "1.25"],
        &["1.25", "-1.25"],
        &["0.10", "0.01"],
        &["-0.10", "-0.01"],
        &["0.00", "0.01"],
        &["-0.01", "0.00"],
        &[&n, &m],
        &[&m, &n],
    ])
}

fn round_d3() -> Vec<Vec<String>> {
    let m = nines(3);
    let n = neg(&m);
    rows(&[
        &["1.250"],
        &["1.350"],
        &["-1.250"],
        &["-1.350"],
        &["1.251"],
        &["-1.251"],
        &["1.249"],
        &["-1.249"],
        &["1.200"],
        &["-1.200"],
        &["0.000"],
        &["0.050"],
        &["-0.050"],
        &["0.049"],
        &["-0.049"],
        &[&m],
        &[&n],
    ])
}

fn int_edges() -> [String; 4] {
    [
        i64::MAX.to_string(),
        (Integer::from(i64::MAX) + 1u32).to_string(),
        i64::MIN.to_string(),
        (Integer::from(i64::MIN) - 1u32).to_string(),
    ]
}

fn round_int() -> Vec<Vec<String>> {
    let m = nines(2);
    let n = neg(&m);
    let [top, above, bottom, below] = int_edges();
    let top_tie = format!("{top}.50");
    let bottom_tie = format!("{bottom}.50");
    let top = format!("{top}.00");
    let above = format!("{above}.00");
    let bottom = format!("{bottom}.00");
    let below = format!("{below}.00");
    rows(&[
        &["2.50"],
        &["3.50"],
        &["-2.50"],
        &["-3.50"],
        &["2.51"],
        &["-2.51"],
        &["2.49"],
        &["-2.49"],
        &["2.00"],
        &["-2.00"],
        &["0.00"],
        &["0.50"],
        &["-0.50"],
        &["0.49"],
        &["-0.49"],
        &[&top],
        &[&top_tie],
        &[&above],
        &[&bottom],
        &[&bottom_tie],
        &[&below],
        &[&m],
        &[&n],
    ])
}

fn div_d2() -> Vec<Vec<String>> {
    let m = nines(2);
    let n = neg(&m);
    rows(&[
        &["7.50", "2.50"],
        &["1.00", "8.00"],
        &["3.00", "8.00"],
        &["-1.00", "8.00"],
        &["1.00", "-8.00"],
        &["-3.00", "-8.00"],
        &["1.00", "3.00"],
        &["2.00", "3.00"],
        &["-1.00", "3.00"],
        &["2.00", "-3.00"],
        &["0.01", "3.00"],
        &["-0.01", "3.00"],
        &["0.00", "5.00"],
        &["1.00", "0.00"],
        &["0.00", "0.00"],
        &[&m, "1.00"],
        &[&m, "0.01"],
        &[&m, "0.07"],
        &[&n, "0.07"],
        &["0.01", &m],
        &["-0.01", &m],
    ])
}

fn widen() -> Vec<Vec<String>> {
    let m = nines(1);
    let n = neg(&m);
    let fits = digits(&(pow10(36) - 1), 1);
    let fits_neg = neg(&fits);
    let over = digits(&pow10(36), 1);
    let over_neg = neg(&over);
    rows(&[
        &["1.5"],
        &["-0.1"],
        &["0.0"],
        &["12.3"],
        &[&fits],
        &[&fits_neg],
        &[&over],
        &[&over_neg],
        &[&m],
        &[&n],
    ])
}

fn from_int() -> Vec<Vec<String>> {
    let [top, _, bottom, _] = int_edges();
    rows(&[&["0"], &["5"], &["-7"], &["100"], &[&top], &[&bottom]])
}

fn to_int() -> Vec<Vec<String>> {
    let m = nines(0);
    let n = neg(&m);
    let [top, above, bottom, below] = int_edges();
    rows(&[
        &["0"],
        &["42"],
        &["-42"],
        &[&top],
        &[&above],
        &[&bottom],
        &[&below],
        &[&m],
        &[&n],
    ])
}

fn query(
    name: &str,
    params: &[(&'static str, Ty)],
    result: Ty,
    op: Op,
    cases: Vec<Vec<String>>,
) -> Query {
    Query {
        name: name.to_string(),
        params: params.to_vec(),
        result,
        op,
        cases,
    }
}

fn mul(a: u32, b: u32, cases: Vec<Vec<String>>) -> Query {
    query(
        &format!("Mul_d{a}_d{b}"),
        &[("a", Ty::Dec(a)), ("b", Ty::Dec(b))],
        Ty::Dec(a + b),
        Op::Mul,
        cases,
    )
}

fn queries() -> Result<Vec<Query>, String> {
    let d2 = Ty::Dec(2);
    let d0 = Ty::Dec(0);
    let two = [("a", d2), ("b", d2)];
    let mut list = vec![
        query(
            "Lit_d2",
            &[],
            d2,
            Op::Lit(parse("12.50", d2)?.c),
            vec![vec![]],
        ),
        query("Add_d2", &two, d2, Op::Add, add_d2()),
        query("Sub_d2", &two, d2, Op::Sub, sub_d2()),
        query("Add_d0", &[("a", d0), ("b", d0)], d0, Op::Add, add_d0()),
        mul(2, 3, mul_d2_d3()),
        mul(20, 17, mul_d20_d17()),
        query("Eq_d2", &two, Ty::Bool, Op::Eq, eq_d2()),
        query("Lt_d2", &two, Ty::Bool, Op::Lt, lt_d2()),
    ];
    for mode in MODES {
        let m = mode.name();
        list.push(query(
            &format!("Round_{m}"),
            &[("a", Ty::Dec(3))],
            Ty::Dec(1),
            Op::Round(mode),
            round_d3(),
        ));
        list.push(query(
            &format!("RoundInt_{m}"),
            &[("a", d2)],
            Ty::Int,
            Op::Round(mode),
            round_int(),
        ));
        list.push(query(
            &format!("Div_{m}"),
            &two,
            d2,
            Op::Div(mode),
            div_d2(),
        ));
    }
    list.push(query(
        "Widen",
        &[("a", Ty::Dec(1))],
        Ty::Dec(3),
        Op::Round(Mode::Exact),
        widen(),
    ));
    list.push(query(
        "FromInt",
        &[("n", Ty::Int)],
        d2,
        Op::Round(Mode::Exact),
        from_int(),
    ));
    list.push(query(
        "ToInt",
        &[("a", d0)],
        Ty::Int,
        Op::Round(Mode::Exact),
        to_int(),
    ));
    Ok(list)
}

fn protocol(list: &[Query]) -> String {
    let lines: String = list
        .iter()
        .map(|q| {
            let params: Vec<String> = q
                .params
                .iter()
                .map(|(name, ty)| format!("({name} {})", ty.text()))
                .collect();
            format!(
                "\n    (query {} ({}) {})",
                q.name,
                params.join(" "),
                q.result.text()
            )
        })
        .collect();
    format!("  (protocol DecimalOps{lines})")
}

fn machine(list: &[Query]) -> String {
    let cells: String = list
        .iter()
        .map(|q| format!("\n      (on {} (block (answer {})))", q.name, expr(q)))
        .collect();
    format!(
        "  (machine DecimalCalc (key Int) (protocol DecimalOps) (uses) (init Ready)\n    (state Ready)\n    (in Ready{cells}))"
    )
}

fn example(q: &Query) -> Result<String, String> {
    let mut lines = vec![
        format!(
            "  (example {} (machine DecimalCalc) (key 1)",
            q.name.to_lowercase()
        ),
        "    (actor u)".to_string(),
    ];
    for case in &q.cases {
        if case.len() != q.params.len() {
            return Err(format!(
                "a case of {} has the wrong number of values",
                q.name
            ));
        }
        let args = q
            .params
            .iter()
            .zip(case)
            .map(|((_, ty), text)| parse(text, *ty))
            .collect::<Result<Vec<Num>, String>>()?;
        let texts: String = q
            .params
            .iter()
            .zip(&args)
            .map(|((_, ty), n)| format!(" {}", value(*ty, &n.c)))
            .collect();
        let fact = match eval(q, &args) {
            Ok(v) => format!("(answer {v})"),
            Err(f) => format!("(fault {})", f.name()),
        };
        lines.push(format!("    (send u {}{texts} (expect {fact}))", q.name));
    }
    Ok(lines.join("\n") + ")")
}

fn till_protocol() -> String {
    format!(
        "  (protocol TillOps\n    (command Put ((v {})) Unit (rejects)))",
        Ty::Dec(2).text()
    )
}

fn till_machine() -> String {
    format!(
        "  (machine Till (key Int) (protocol TillOps) (uses) (init Empty)\n    (state Empty)\n    (state Holding (v {}))\n    (group Any Empty Holding)\n    (in Any\n      (on Put (block (next (Holding v) (outcome (unit)))))))",
        Ty::Dec(2).text()
    )
}

fn till_example() -> Result<String, String> {
    let d2 = Ty::Dec(2);
    let m = nines(2);
    let mut lines = vec![
        "  (example till (machine Till) (key 1)".to_string(),
        "    (actor u)".to_string(),
    ];
    for text in ["12.50", "-0.05", &m] {
        let v = value(d2, &parse(text, d2)?.c);
        lines.push(format!(
            "    (send u Put {v} (expect (outcome (unit)) (state Holding {v})))"
        ));
    }
    Ok(lines.join("\n") + ")")
}

pub fn file() -> Result<String, String> {
    let list = queries()?;
    let mut items = vec![
        protocol(&list),
        machine(&list),
        till_protocol(),
        till_machine(),
    ];
    for q in &list {
        items.push(example(q)?);
    }
    items.push(till_example()?);
    Ok(format!("(program\n{})\n", items.join("\n")))
}
