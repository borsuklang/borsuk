use rug::float::{Round, Special};
use rug::ops::Pow;
use rug::{Float, Integer, Rational};
use std::cmp::Ordering;

use crate::fmt::Fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
    Nan,
    Inf { neg: bool },
    Finite { neg: bool, magnitude: Rational },
}

fn mantissa_bits(f: Fmt) -> i32 {
    f.prec() as i32 - 1
}

fn quantum_min(f: Fmt) -> i32 {
    1 - f.emax() - mantissa_bits(f)
}

fn sign_bit(f: Fmt, neg: bool) -> u64 {
    if neg { f.sign() } else { 0 }
}

fn pow2(e: i32) -> Rational {
    Rational::from(1) << e
}

fn pow10(e: i32) -> Rational {
    let p = Integer::from(10).pow(e.unsigned_abs());
    if e < 0 {
        Rational::from((Integer::from(1), p))
    } else {
        Rational::from(p)
    }
}

fn floor_log2(v: &Rational) -> i32 {
    let e = v.numer().significant_bits() as i32 - v.denom().significant_bits() as i32;
    if *v < pow2(e) { e - 1 } else { e }
}

fn floor_log10(v: &Rational) -> i32 {
    let mut d = (floor_log2(v) * 1233) >> 12;
    while pow10(d + 1) <= *v {
        d += 1;
    }
    while pow10(d) > *v {
        d -= 1;
    }
    d
}

pub fn value(f: Fmt, bits: u64) -> Value {
    let neg = bits & f.sign() != 0;
    let mag = bits & !f.sign();
    if f.is_nan(bits) {
        return Value::Nan;
    }
    if mag == f.exponent_mask() {
        return Value::Inf { neg };
    }
    let m = mantissa_bits(f);
    let field = (mag >> m) as i32;
    let frac = mag & ((1 << m) - 1);
    let (n, q) = if field == 0 {
        (frac, quantum_min(f))
    } else {
        (frac | (1 << m), quantum_min(f) + field - 1)
    };
    Value::Finite {
        neg,
        magnitude: Rational::from(n) << q,
    }
}

pub fn round(f: Fmt, neg: bool, magnitude: &Rational) -> u64 {
    let sign = sign_bit(f, neg);
    if magnitude.cmp0() != Ordering::Greater {
        return sign;
    }
    let qmin = quantum_min(f);
    let e = floor_log2(magnitude);
    if e > f.emax() {
        return f.exponent_mask() | sign;
    }
    if e < qmin - 1 {
        return sign;
    }
    let m = mantissa_bits(f);
    let q = e.max(1 - f.emax()) - m;
    let scaled = Rational::from(magnitude << -q);
    let (num, den) = scaled.into_numer_denom();
    let (mut n, r) = num.div_rem(den.clone());
    match Integer::from(&r << 1).cmp(&den) {
        Ordering::Greater => n += 1,
        Ordering::Equal if n.is_odd() => n += 1,
        _ => {}
    }
    let n = n.to_u64().expect("significand fits in 64 bits");
    let bits = (((q - qmin) as u64) << m) + n;
    bits.min(f.exponent_mask()) | sign
}

pub fn to_float(f: Fmt, bits: u64) -> Float {
    let p = f.prec();
    match value(f, bits) {
        Value::Nan => Float::with_val(p, Special::Nan),
        Value::Inf { neg: false } => Float::with_val(p, Special::Infinity),
        Value::Inf { neg: true } => Float::with_val(p, Special::NegInfinity),
        Value::Finite { neg, magnitude } => {
            let x = Float::with_val(p, &magnitude);
            if neg { -x } else { x }
        }
    }
}

pub fn eval(f: Fmt, op: impl FnOnce(&mut Float, Round) -> Ordering) -> u64 {
    let mut x = Float::new(f.prec());
    let dir = op(&mut x, Round::Nearest);
    if x.is_nan() {
        return f.nan();
    }
    let neg = x.is_sign_negative();
    let sign = sign_bit(f, neg);
    if x.is_zero() {
        return sign;
    }
    let Some(e) = x.get_exp() else {
        return f.exponent_mask() | sign;
    };
    if e > f.emax() + 1 {
        return f.exponent_mask() | sign;
    }
    let qmin = quantum_min(f);
    if e < qmin {
        return sign;
    }
    if e > qmin {
        x.subnormalize_ieee_round(dir, Round::Nearest);
        return round(f, neg, &exact(&x));
    }
    let magnitude = exact(&x);
    let toward = if neg { dir.reverse() } else { dir };
    if magnitude == pow2(qmin - 1) && toward == Ordering::Less {
        return 1 | sign;
    }
    round(f, neg, &magnitude)
}

fn exact(x: &Float) -> Rational {
    x.to_rational().expect("finite value").abs()
}

fn candidate(f: Fmt, bits: u64, v: &Rational, k: u32, n0: i32) -> Option<(Integer, i32)> {
    let low = Integer::from(10).pow(k - 1);
    let high = Integer::from(10).pow(k) - 1u32;
    let mut best: Option<(Rational, Integer, i32)> = None;
    for n in n0 - 1..=n0 + 1 {
        let scale = pow10(n - k as i32);
        let t = Rational::from(v / &scale);
        let (fract, floor) = t.fract_floor(Integer::new());
        let ceil = if fract.cmp0() == Ordering::Equal {
            floor.clone()
        } else {
            Integer::from(&floor + 1u32)
        };
        for s in [floor, ceil] {
            let s = s.clamp(&low, &high);
            let d = Rational::from(&s) * &scale;
            if round(f, false, &d) != bits {
                continue;
            }
            let distance = Rational::from(&d - v).abs();
            let better = match &best {
                None => true,
                Some((bd, bs, _)) => {
                    distance < *bd || (distance == *bd && s.is_even() && bs.is_odd())
                }
            };
            if better {
                best = Some((distance, s, n));
            }
        }
    }
    best.map(|(_, s, n)| (s, n))
}

fn shortest(f: Fmt, bits: u64, v: &Rational) -> (String, i32) {
    let n0 = floor_log10(v) + 1;
    let mut k = 1;
    loop {
        if let Some((s, n)) = candidate(f, bits, v, k, n0) {
            return (s.to_string(), n);
        }
        k += 1;
    }
}

fn layout(d: &str, n: i32) -> String {
    let k = d.len() as i32;
    if (k..=21).contains(&n) {
        format!("{d}{}", "0".repeat((n - k) as usize))
    } else if (1..k).contains(&n) {
        let (a, b) = d.split_at(n as usize);
        format!("{a}.{b}")
    } else if (-5..=0).contains(&n) {
        format!("0.{}{d}", "0".repeat(n.unsigned_abs() as usize))
    } else {
        let (a, b) = d.split_at(1);
        let point = if b.is_empty() { "" } else { "." };
        let sign = if n > 0 { '+' } else { '-' };
        format!("{a}{point}{b}e{sign}{}", (n - 1).unsigned_abs())
    }
}

pub fn text(f: Fmt, bits: u64) -> String {
    match value(f, bits) {
        Value::Nan => "nan".to_string(),
        Value::Inf { neg } => format!("{}inf", if neg { "-" } else { "" }),
        Value::Finite { neg, magnitude } => {
            let body = if magnitude.cmp0() == Ordering::Equal {
                "0".to_string()
            } else {
                let (d, n) = shortest(f, bits & !f.sign(), &magnitude);
                layout(&d, n)
            };
            format!("{}{body}", if neg { "-" } else { "" })
        }
    }
}

pub fn literal(f: Fmt, bits: u64) -> String {
    format!("({} {})", f.name(), text(f, bits))
}
