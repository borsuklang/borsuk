use rug::float::{Constant, Round};
use rug::ops::{AssignRound, Pow};
use rug::{Float, Integer, Rational};
use std::cmp::Ordering;

use crate::fmt::{FORMATS, Fmt};
use crate::fp;
use crate::stream::Stream;

type Mpfr = fn(&mut Float, &[Float], Round) -> Ordering;

struct Function {
    name: &'static str,
    params: &'static [&'static str],
    mpfr: Mpfr,
}

const FUNCTIONS: [Function; 18] = [
    Function {
        name: "exp",
        params: &["x"],
        mpfr: |o, a, r| o.assign_round(a[0].exp_ref(), r),
    },
    Function {
        name: "exp2",
        params: &["x"],
        mpfr: |o, a, r| o.assign_round(a[0].exp2_ref(), r),
    },
    Function {
        name: "log",
        params: &["x"],
        mpfr: |o, a, r| o.assign_round(a[0].ln_ref(), r),
    },
    Function {
        name: "log2",
        params: &["x"],
        mpfr: |o, a, r| o.assign_round(a[0].log2_ref(), r),
    },
    Function {
        name: "log10",
        params: &["x"],
        mpfr: |o, a, r| o.assign_round(a[0].log10_ref(), r),
    },
    Function {
        name: "sin",
        params: &["x"],
        mpfr: |o, a, r| o.assign_round(a[0].sin_ref(), r),
    },
    Function {
        name: "cos",
        params: &["x"],
        mpfr: |o, a, r| o.assign_round(a[0].cos_ref(), r),
    },
    Function {
        name: "tan",
        params: &["x"],
        mpfr: |o, a, r| o.assign_round(a[0].tan_ref(), r),
    },
    Function {
        name: "asin",
        params: &["x"],
        mpfr: |o, a, r| o.assign_round(a[0].asin_ref(), r),
    },
    Function {
        name: "acos",
        params: &["x"],
        mpfr: |o, a, r| o.assign_round(a[0].acos_ref(), r),
    },
    Function {
        name: "atan",
        params: &["x"],
        mpfr: |o, a, r| o.assign_round(a[0].atan_ref(), r),
    },
    Function {
        name: "sinh",
        params: &["x"],
        mpfr: |o, a, r| o.assign_round(a[0].sinh_ref(), r),
    },
    Function {
        name: "cosh",
        params: &["x"],
        mpfr: |o, a, r| o.assign_round(a[0].cosh_ref(), r),
    },
    Function {
        name: "tanh",
        params: &["x"],
        mpfr: |o, a, r| o.assign_round(a[0].tanh_ref(), r),
    },
    Function {
        name: "cbrt",
        params: &["x"],
        mpfr: |o, a, r| o.assign_round(a[0].cbrt_ref(), r),
    },
    Function {
        name: "pow",
        params: &["x", "y"],
        mpfr: |o, a, r| o.assign_round((&a[0]).pow(&a[1]), r),
    },
    Function {
        name: "atan2",
        params: &["y", "x"],
        mpfr: |o, a, r| o.assign_round(a[0].atan2_ref(&a[1]), r),
    },
    Function {
        name: "hypot",
        params: &["x", "y"],
        mpfr: |o, a, r| o.assign_round(a[0].hypot_ref(&a[1]), r),
    },
];

const APPENDIX: [(&str, &str, &str); 56] = [
    (
        "exp exp2 log log2 log10 sin cos tan asin acos atan sinh cosh tanh cbrt",
        "nan",
        "nan",
    ),
    ("pow", "nan 2; 2 nan", "nan"),
    ("atan2 hypot", "nan 1; 1 nan", "nan"),
    ("exp exp2", "0; -0", "1"),
    ("exp exp2", "-inf", "+0"),
    ("exp exp2", "inf", "+inf"),
    ("log log2 log10", "0; -0", "-inf"),
    ("log log2 log10", "1", "+0"),
    ("log log2 log10", "-1; -tiny; -inf", "nan"),
    ("log log2 log10", "inf", "+inf"),
    ("sin tan", "0; -0", "±0"),
    ("sin cos tan", "inf; -inf", "nan"),
    ("cos", "0; -0", "1"),
    ("asin", "0; -0", "±0"),
    ("asin acos", "above1; -above1; 2; -2; inf; -inf", "nan"),
    ("acos", "1", "+0"),
    ("atan", "0; -0", "±0"),
    ("atan", "inf; -inf", "±pi/2"),
    ("sinh tanh", "0; -0", "±0"),
    ("sinh", "inf; -inf", "±inf"),
    ("cosh", "0; -0", "1"),
    ("cosh", "inf; -inf", "+inf"),
    ("tanh", "inf; -inf", "±1"),
    ("cbrt", "0; -0; inf; -inf", "x"),
    ("atan2", "0 -0; -0 -0", "±pi"),
    ("atan2", "0 0; -0 0", "±0"),
    (
        "atan2",
        "0 -1; -0 -1; 0 -tiny; -0 -max; 0 -inf; -0 -inf",
        "±pi",
    ),
    ("atan2", "0 1; -0 1; 0 tiny; -0 max; 0 inf; -0 inf", "±0"),
    (
        "atan2",
        "-1 0; -1 -0; -tiny 0; -max -0; -inf 0; -inf -0",
        "-pi/2",
    ),
    ("atan2", "1 0; 1 -0; tiny 0; max -0; inf 0; inf -0", "+pi/2"),
    ("atan2", "1 -inf; -1 -inf; tiny -inf; -max -inf", "±pi"),
    ("atan2", "1 inf; -1 inf; tiny inf; -max inf", "±0"),
    (
        "atan2",
        "inf 1; -inf 1; inf -1; -inf -1; inf tiny; -inf -max",
        "±pi/2",
    ),
    ("atan2", "inf -inf; -inf -inf", "±3pi/4"),
    ("atan2", "inf inf; -inf inf", "±pi/4"),
    (
        "hypot",
        "inf 1; -inf 1; 1 inf; 1 -inf; inf nan; -inf nan; nan inf; nan -inf",
        "+inf",
    ),
    ("hypot", "3 0; -3 -0; -tiny 0; -max -0; -0 -0", "|x|"),
    ("hypot", "0 -3; -0 3; 0 -tiny; -0 max", "|y|"),
    ("pow", "1 3; 1 -1/2; 1 max; 1 inf; 1 -inf; 1 nan", "1"),
    ("pow", "3 0; -3 -0; 0 0; -inf -0; inf 0; nan 0; nan -0", "1"),
    ("pow", "0 -1; -0 -1; -0 -3; -0 -odd", "±inf"),
    (
        "pow",
        "0 -2; -0 -2; -0 -1/2; -0 -max; 0 -inf; -0 -inf",
        "+inf",
    ),
    ("pow", "0 1; -0 1; -0 3; -0 odd", "±0"),
    ("pow", "0 2; -0 2; -0 1/2; -0 max; 0 inf; -0 inf", "+0"),
    ("pow", "-1 inf; -1 -inf", "1"),
    (
        "pow",
        "-2 1/2; -1/2 -5/2; -1 1/2; -max 1/2; -tiny -1/2",
        "nan",
    ),
    (
        "pow",
        "1/2 -inf; -1/2 -inf; below1 -inf; -tiny -inf",
        "+inf",
    ),
    (
        "pow",
        "2 -inf; -2 -inf; above1 -inf; -max -inf; inf -inf; -inf -inf",
        "+0",
    ),
    ("pow", "1/2 inf; -1/2 inf; below1 inf; -tiny inf", "+0"),
    (
        "pow",
        "2 inf; -2 inf; above1 inf; -max inf; inf inf; -inf inf",
        "+inf",
    ),
    ("pow", "-inf -1; -inf -3; -inf -odd", "-0"),
    ("pow", "-inf -2; -inf -1/2; -inf -max; -inf -inf", "+0"),
    ("pow", "-inf 1; -inf 3; -inf odd", "-inf"),
    ("pow", "-inf 2; -inf 1/2; -inf max; -inf inf", "+inf"),
    ("pow", "inf -1; inf -1/2; inf -tiny; inf -inf", "+0"),
    ("pow", "inf 1; inf 1/2; inf tiny; inf inf", "+inf"),
];

const POW_DYADIC: [&str; 33] = [
    "3 2",
    "3/2 3",
    "5 3",
    "2 10",
    "2 -3",
    "1/4 -3",
    "1/2 -5",
    "9 1/2",
    "4 1/2",
    "16 3/4",
    "81/16 1/4",
    "81/16 3/4",
    "1/4 1/2",
    "4 -1/2",
    "16 -3/4",
    "1/4 -1/2",
    "-3 3",
    "-3 2",
    "-3/2 3",
    "-2 -3",
    "-2 -2",
    "-1/2 -5",
    "3 1000000",
    "-3 1000001",
    "2 max",
    "1/2 -max",
    "1/2 max",
    "3 34",
    "3 35",
    "-3 35",
    "11 7",
    "3 16",
    "-11 7",
];

const SEED: u64 = 0x0AC1E;
const DRAWS: usize = 100;
const SOURCES: [&str; 2] = ["lefevre-muller.txt", "openjdk-jdk-25-ga.txt"];
const CHECK_PREC: u32 = 200;
const CHECK_RUN: u32 = 20;

fn qmin(f: Fmt) -> i32 {
    2 - f.emax() - f.prec() as i32
}

fn pow2(e: i32) -> Rational {
    Rational::from(1) << e
}

fn exact(f: Fmt, q: &Rational) -> Result<u64, String> {
    let bits = fp::round(f, false, q);
    match fp::value(f, bits) {
        fp::Value::Finite { magnitude, .. } if magnitude == *q => Ok(bits),
        _ => Err(format!("{q} is not a value of {}", f.ty())),
    }
}

fn operand(f: Fmt, text: &str) -> Result<u64, String> {
    if text == "nan" {
        return Ok(f.nan());
    }
    let (sign, body) = match text.strip_prefix('-') {
        Some(body) => (f.sign(), body),
        None => (0, text),
    };
    let one = exact(f, &Rational::from(1))?;
    let magnitude = match body {
        "inf" => f.exponent_mask(),
        "max" => f.exponent_mask() - 1,
        "tiny" => 1,
        "above1" => one + 1,
        "below1" => one - 1,
        "odd" => exact(f, &Rational::from((Integer::from(1) << f.prec()) - 1u32))?,
        _ => {
            let q: Rational = body
                .parse()
                .map_err(|_| format!("operand `{text}` is not a number"))?;
            exact(f, &q)?
        }
    };
    Ok(magnitude | sign)
}

fn inputs<'a>(
    f: Fmt,
    g: &Function,
    list: impl Iterator<Item = &'a str>,
) -> Result<Vec<Vec<u64>>, String> {
    let mut out = Vec::new();
    for input in list.map(str::trim) {
        let args = input
            .split(' ')
            .map(|t| operand(f, t))
            .collect::<Result<Vec<u64>, String>>()?;
        if args.len() != g.params.len() {
            return Err(format!(
                "input `{input}` of {} has a wrong operand count",
                g.name
            ));
        }
        out.push(args);
    }
    Ok(out)
}

fn pi(f: Fmt, num: u32, den: u32) -> Result<u64, String> {
    let bound = |round| {
        let (p, _) = Float::with_val_round(CHECK_PREC, Constant::Pi, round);
        let scaled = Float::with_val(CHECK_PREC + 8, &p * num) / den;
        fp::eval(f, |x, r| x.assign_round(&scaled, r))
    };
    let lo = bound(Round::Down);
    if lo == bound(Round::Up) {
        Ok(lo)
    } else {
        Err(format!("{num}π/{den} is not decided at {CHECK_PREC} bits"))
    }
}

fn symbol(f: Fmt, value: &str, args: &[u64]) -> Result<u64, String> {
    let (sign, body) = if let Some(body) = value.strip_prefix('±') {
        (args[0] & f.sign(), body)
    } else if let Some(body) = value.strip_prefix('-') {
        (f.sign(), body)
    } else {
        (0, value.strip_prefix('+').unwrap_or(value))
    };
    let magnitude = match body {
        "nan" => return Ok(f.nan()),
        "x" => return Ok(args[0]),
        "|x|" => return Ok(args[0] & !f.sign()),
        "|y|" => return Ok(args[1] & !f.sign()),
        "0" => 0,
        "1" => exact(f, &Rational::from(1))?,
        "inf" => f.exponent_mask(),
        "pi" => pi(f, 1, 1)?,
        "pi/2" => pi(f, 1, 2)?,
        "pi/4" => pi(f, 1, 4)?,
        "3pi/4" => pi(f, 3, 4)?,
        _ => {
            return Err(format!(
                "value `{value}` of the copy of Appendix A is unknown"
            ));
        }
    };
    Ok(magnitude | sign)
}

fn compute(f: Fmt, g: &Function, args: &[u64]) -> u64 {
    let a: Vec<Float> = args.iter().map(|&b| fp::to_float(f, b)).collect();
    fp::eval(f, |x, r| (g.mpfr)(x, &a, r))
}

fn shown(f: Fmt, args: &[u64]) -> String {
    let texts: Vec<String> = args.iter().map(|&b| fp::text(f, b)).collect();
    texts.join(" ")
}

fn appendix(f: Fmt, g: &Function) -> Result<Vec<Vec<u64>>, String> {
    let mut out = Vec::new();
    for (names, list, value) in APPENDIX {
        if !names.split(' ').any(|n| n == g.name) {
            continue;
        }
        for args in inputs(f, g, list.split(';'))? {
            let table = symbol(f, value, &args)?;
            let mpfr = compute(f, g, &args);
            if table != mpfr {
                return Err(format!(
                    "Appendix A row ({names}: {list}: {value}) differs from MPFR at {} {} in {}: the table gives {}, MPFR gives {}",
                    g.name,
                    shown(f, &args),
                    f.ty(),
                    fp::text(f, table),
                    fp::text(f, mpfr)
                ));
            }
            out.push(args);
        }
    }
    Ok(out)
}

fn dyadic(f: Fmt, g: &Function) -> Result<Vec<Vec<u64>>, String> {
    let e = f.emax();
    let q = qmin(f);
    let list: Vec<String> = match g.name {
        "exp2" => [1, 2, 10, -1, -10, e, e + 1, 1 - e, -e, q, q - 1, q - 2]
            .iter()
            .map(|n| n.to_string())
            .chain(["max".to_string(), "-max".to_string()])
            .collect(),
        "log2" => [1, -1, 10, e, 1 - e, -e, q]
            .iter()
            .map(|&m| pow2(m).to_string())
            .collect(),
        "log10" => (1..)
            .take_while(|&m| Integer::from(5).pow(m).significant_bits() <= f.prec())
            .map(|m| Integer::from(10).pow(m).to_string())
            .collect(),
        "pow" => {
            let tie = Rational::from(3) * pow2((q - 1) / 5);
            let tiny = match f {
                Fmt::F64 => Rational::from(3) * pow2(-539),
                Fmt::F32 => Rational::from(5) * pow2(-77),
            };
            let root = (Integer::from(1) << (f.prec() / 2)) - 1u32;
            POW_DYADIC
                .iter()
                .map(|s| s.to_string())
                .chain([
                    format!("2 {}", e + 1),
                    format!("-2 {}", e + 2),
                    format!("2 {q}"),
                    format!("2 {}", q - 1),
                    format!("{tie} 5"),
                    format!("-{tie} 5"),
                    format!("{tiny} 2"),
                    format!("{} 3/2", root.square()),
                ])
                .collect()
        }
        _ => Vec::new(),
    };
    inputs(f, g, list.iter().map(String::as_str))
}

fn draws(stream: &mut Stream, f: Fmt, g: &Function) -> Result<Vec<Vec<u64>>, String> {
    let lo = exact(f, &pow2(-10))?;
    let hi = match g.name {
        "asin" | "acos" => exact(f, &Rational::from(1))?,
        _ => exact(f, &pow2(10))?,
    };
    let mut out = Vec::new();
    for _ in 0..DRAWS {
        out.push(g.params.iter().map(|_| stream.whole(f)).collect());
    }
    for _ in 0..DRAWS {
        let mut args = Vec::new();
        for i in 0..g.params.len() {
            let unsigned =
                matches!(g.name, "log" | "log2" | "log10") || (g.name == "pow" && i == 0);
            args.push(stream.range(f, lo, hi, !unsigned));
        }
        out.push(args);
    }
    Ok(out)
}

fn hex(text: &str) -> Result<u64, String> {
    let bad = || format!("`{text}` is not a hexadecimal float of binary64");
    let (neg, body) = match text.strip_prefix('-') {
        Some(body) => (true, body),
        None => (false, text),
    };
    let body = body.strip_prefix("0x").ok_or_else(bad)?;
    let (digits, exponent) = body.split_once('p').ok_or_else(bad)?;
    let (int, frac) = digits.split_once('.').unwrap_or((digits, ""));
    let all = format!("{int}{frac}");
    if int.is_empty() || !all.chars().all(|c| c.is_ascii_hexdigit()) {
        return Err(bad());
    }
    let n = Integer::from_str_radix(&all, 16).map_err(|_| bad())?;
    let shift: i32 = exponent.parse().map_err(|_| bad())?;
    let q = Rational::from(n) << (shift - 4 * frac.len() as i32);
    let bits = exact(Fmt::F64, &q).map_err(|_| bad())?;
    Ok(if neg { bits | Fmt::F64.sign() } else { bits })
}

fn run_after_rounding_bit(g: &Function, args: &[u64]) -> u32 {
    let f = Fmt::F64;
    let a: Vec<Float> = args.iter().map(|&b| fp::to_float(f, b)).collect();
    let mut v = Float::new(CHECK_PREC);
    (g.mpfr)(&mut v, &a, Round::Nearest);
    let Some((m, exp)) = v.to_integer_exp() else {
        return 0;
    };
    let m = m.abs();
    let bits = m.significant_bits();
    if bits == 0 {
        return 0;
    }
    let lead = bits as i32 + exp - 1;
    let m = m << (CHECK_PREC - bits);
    let low = lead + 1 - CHECK_PREC as i32;
    let last = (lead + 1 - f.prec() as i32).max(qmin(f));
    let Ok(top) = u32::try_from(last - 2 - low) else {
        return 0;
    };
    let first = m.get_bit(top);
    (0..=top)
        .rev()
        .take_while(|&i| m.get_bit(i) == first)
        .count() as u32
}

fn hard_cases() -> Result<Vec<(usize, Vec<u64>)>, String> {
    let mut out = Vec::new();
    for (k, source) in SOURCES.iter().enumerate() {
        let path = format!("{}/hard-cases/{source}", env!("CARGO_MANIFEST_DIR"));
        let text =
            std::fs::read_to_string(&path).map_err(|e| format!("cannot read {path}: {e}"))?;
        let mut lines = text.lines();
        if !lines.next().is_some_and(|l| l.starts_with("source: ")) {
            return Err(format!("line 1 of {source} is not a source line"));
        }
        for (n, line) in lines.enumerate() {
            let place = || format!("hard case `{line}` of {source} line {}", n + 2);
            let words: Vec<&str> = line.split_whitespace().collect();
            let index = words
                .first()
                .and_then(|w| FUNCTIONS.iter().position(|g| g.name == *w))
                .ok_or_else(|| format!("{}: unknown function", place()))?;
            let g = &FUNCTIONS[index];
            let arity = g.params.len();
            if words.len() != arity + 2 {
                return Err(format!("{}: wrong word count", place()));
            }
            let args = words[1..=arity]
                .iter()
                .map(|w| hex(w))
                .collect::<Result<Vec<u64>, String>>()
                .map_err(|e| format!("{}: {e}", place()))?;
            if k == 0 {
                let run = run_after_rounding_bit(g, &args);
                if run < CHECK_RUN {
                    return Err(format!(
                        "{}: {run} equal bits follow the rounding bit at {CHECK_PREC} bits, fewer than {CHECK_RUN}",
                        place()
                    ));
                }
            }
            out.push((index, args));
        }
    }
    Ok(out)
}

fn query(g: &Function, f: Fmt) -> String {
    let (first, rest) = g.name.split_at(1);
    format!("{}{rest}_{}", first.to_uppercase(), f.name())
}

pub fn file() -> Result<String, String> {
    let hard = hard_cases()?;
    let mut stream = Stream::new(SEED);
    let mut protocol = String::new();
    let mut cells = String::new();
    let mut examples = String::new();
    for (index, g) in FUNCTIONS.iter().enumerate() {
        for f in FORMATS {
            let name = query(g, f);
            let params: Vec<String> = g
                .params
                .iter()
                .map(|p| format!("({p} {})", f.ty()))
                .collect();
            protocol.push_str(&format!(
                "\n    (query {name} ({}) {})",
                params.join(" "),
                f.ty()
            ));
            cells.push_str(&format!(
                "\n      (on {name} (block (answer ({} {}))))",
                g.name,
                g.params.join(" ")
            ));
            let mut cases = appendix(f, g)?;
            cases.extend(dyadic(f, g)?);
            cases.extend(draws(&mut stream, f, g)?);
            if f == Fmt::F64 {
                cases.extend(
                    hard.iter()
                        .filter(|(i, _)| *i == index)
                        .map(|(_, args)| args.clone()),
                );
            }
            examples.push_str(&format!(
                "\n  (example {} (machine MathCalc) (key 1)\n    (actor u)",
                name.to_lowercase()
            ));
            for args in &cases {
                let operands: Vec<String> = args.iter().map(|&b| fp::literal(f, b)).collect();
                examples.push_str(&format!(
                    "\n    (send u {name} {} (expect (answer {})))",
                    operands.join(" "),
                    fp::literal(f, compute(f, g, args))
                ));
            }
            examples.push(')');
        }
    }
    Ok(format!(
        "(program\n  (protocol MathOps{protocol})\n  (machine MathCalc (key Int) (protocol MathOps) (uses) (init Ready)\n    (state Ready)\n    (in Ready{cells})){examples})\n"
    ))
}
