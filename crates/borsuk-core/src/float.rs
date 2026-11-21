use crate::nat::{Int, Nat};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fmt {
    B64,
    B32,
}

impl Fmt {
    pub fn prec(self) -> u64 {
        match self {
            Fmt::B64 => 53,
            Fmt::B32 => 24,
        }
    }

    pub fn emax(self) -> u64 {
        match self {
            Fmt::B64 => 1023,
            Fmt::B32 => 127,
        }
    }

    pub fn width(self) -> u64 {
        match self {
            Fmt::B64 => 64,
            Fmt::B32 => 32,
        }
    }

    pub fn nan(self) -> u64 {
        match self {
            Fmt::B64 => 0x7FF8_0000_0000_0000,
            Fmt::B32 => 0x7FC0_0000,
        }
    }
}

pub fn qmin(f: Fmt) -> i64 {
    2 - f.emax() as i64 - f.prec() as i64
}

pub fn sign_bit(f: Fmt, neg: bool) -> u64 {
    if neg { 1 << (f.width() - 1) } else { 0 }
}

pub fn inf_bits(f: Fmt, neg: bool) -> u64 {
    sign_bit(f, neg) + ((1 << (f.width() - f.prec())) - 1) * (1 << (f.prec() - 1))
}

fn rat_of(base: u64, m: Nat, e: i64) -> (Nat, Nat) {
    if 0 <= e {
        (
            m * Nat::from_u64(base).pow(e.unsigned_abs()),
            Nat::from_u64(1),
        )
    } else {
        (m, Nat::from_u64(base).pow(e.unsigned_abs()))
    }
}

fn pack(f: Fmt, neg: bool, m: Nat, q: i64) -> u64 {
    let b = Nat::from_u64(u64::try_from(q - qmin(f)).unwrap_or(0))
        * Nat::from_u64(1 << (f.prec() - 1))
        + m;
    match b.to_u64() {
        Some(b) if b < inf_bits(f, false) => sign_bit(f, neg) + b,
        _ => inf_bits(f, neg),
    }
}

pub fn round_rat(f: Fmt, neg: bool, num: &Nat, den: &Nat) -> u64 {
    if num.is_zero() {
        sign_bit(f, neg)
    } else {
        let t = num.log2() as i64 - den.log2() as i64;
        let (a, b) = rat_of(2, Nat::from_u64(1), t);
        let e = if den * &a <= num * &b { t } else { t - 1 };
        let q = (e - (f.prec() as i64 - 1)).max(qmin(f));
        let (a, b) = rat_of(2, Nat::from_u64(1), q);
        let n = num * b;
        let d = den * a;
        let m = &n / &d;
        let r = &n % &d;
        let up = d < &r * 2 || (&r * 2 == d && &m % 2 == 1);
        pack(f, neg, if up { m + 1 } else { m }, q)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Unpacked {
    Nan,
    Inf(bool),
    Fin(bool, u64, i64),
}

pub fn unpack(f: Fmt, x: u64) -> Unpacked {
    let w = f.prec() - 1;
    let top: u64 = (1 << (f.width() - f.prec())) - 1;
    let neg = x / (1 << (f.width() - 1)) % 2 == 1;
    let be = x / (1 << w) % (top + 1);
    let fr = x % (1 << w);
    if be == top {
        if fr == 0 {
            Unpacked::Inf(neg)
        } else {
            Unpacked::Nan
        }
    } else if be == 0 {
        Unpacked::Fin(neg, fr, qmin(f))
    } else {
        Unpacked::Fin(neg, fr + (1 << w), qmin(f) + be as i64 - 1)
    }
}

impl Unpacked {
    fn negate(self) -> Unpacked {
        match self {
            Unpacked::Nan => Unpacked::Nan,
            Unpacked::Inf(s) => Unpacked::Inf(!s),
            Unpacked::Fin(s, m, e) => Unpacked::Fin(!s, m, e),
        }
    }
}

fn round_dy(f: Fmt, neg: bool, m: Nat, e: i64) -> u64 {
    let (a, b) = rat_of(2, m, e);
    round_rat(f, neg, &a, &b)
}

fn add_fin(f: Fmt, s: bool, m: Nat, e: i64, t: bool, n: Nat, d: i64) -> u64 {
    let c = e.min(d);
    let a = Int::from(m * Nat::from_u64(2).pow((e - c).unsigned_abs()));
    let b = Int::from(n * Nat::from_u64(2).pow((d - c).unsigned_abs()));
    let v = (if s { -a } else { a }) + (if t { -b } else { b });
    if v.is_zero() {
        sign_bit(f, s && t)
    } else {
        round_dy(f, v < 0, v.nat_abs(), c)
    }
}

fn add_unpacked(f: Fmt, x: Unpacked, y: Unpacked) -> u64 {
    match (x, y) {
        (Unpacked::Nan, _) => f.nan(),
        (_, Unpacked::Nan) => f.nan(),
        (Unpacked::Inf(s), Unpacked::Inf(t)) => {
            if s == t {
                inf_bits(f, s)
            } else {
                f.nan()
            }
        }
        (Unpacked::Inf(s), _) => inf_bits(f, s),
        (_, Unpacked::Inf(t)) => inf_bits(f, t),
        (Unpacked::Fin(s, m, e), Unpacked::Fin(t, n, d)) => {
            add_fin(f, s, Nat::from_u64(m), e, t, Nat::from_u64(n), d)
        }
    }
}

pub fn float_add(f: Fmt, x: u64, y: u64) -> u64 {
    add_unpacked(f, unpack(f, x), unpack(f, y))
}

pub fn float_sub(f: Fmt, x: u64, y: u64) -> u64 {
    add_unpacked(f, unpack(f, x), unpack(f, y).negate())
}

pub fn float_mul(f: Fmt, x: u64, y: u64) -> u64 {
    match (unpack(f, x), unpack(f, y)) {
        (Unpacked::Nan, _) => f.nan(),
        (_, Unpacked::Nan) => f.nan(),
        (Unpacked::Inf(s), Unpacked::Inf(t)) => inf_bits(f, s != t),
        (Unpacked::Inf(s), Unpacked::Fin(t, m, _)) => {
            if m == 0 {
                f.nan()
            } else {
                inf_bits(f, s != t)
            }
        }
        (Unpacked::Fin(s, m, _), Unpacked::Inf(t)) => {
            if m == 0 {
                f.nan()
            } else {
                inf_bits(f, s != t)
            }
        }
        (Unpacked::Fin(s, m, e), Unpacked::Fin(t, n, d)) => {
            round_dy(f, s != t, Nat::from_u64(m) * Nat::from_u64(n), e + d)
        }
    }
}

pub fn float_div(f: Fmt, x: u64, y: u64) -> u64 {
    match (unpack(f, x), unpack(f, y)) {
        (Unpacked::Nan, _) => f.nan(),
        (_, Unpacked::Nan) => f.nan(),
        (Unpacked::Inf(_), Unpacked::Inf(_)) => f.nan(),
        (Unpacked::Inf(s), Unpacked::Fin(t, _, _)) => inf_bits(f, s != t),
        (Unpacked::Fin(s, _, _), Unpacked::Inf(t)) => sign_bit(f, s != t),
        (Unpacked::Fin(s, m, e), Unpacked::Fin(t, n, d)) => {
            if n == 0 {
                if m == 0 { f.nan() } else { inf_bits(f, s != t) }
            } else {
                let (a, b) = rat_of(2, Nat::from_u64(m), e - d);
                round_rat(f, s != t, &a, &(b * Nat::from_u64(n)))
            }
        }
    }
}

pub fn float_sqrt(f: Fmt, x: u64) -> u64 {
    match unpack(f, x) {
        Unpacked::Nan => f.nan(),
        Unpacked::Inf(s) => {
            if s {
                f.nan()
            } else {
                inf_bits(f, false)
            }
        }
        Unpacked::Fin(s, m, e) => {
            if m == 0 {
                sign_bit(f, s)
            } else if s {
                f.nan()
            } else {
                let m = Nat::from_u64(m);
                let q = (m.log2() as i64 + e).div_euclid(2) - (f.prec() as i64 - 1);
                let n = m * Nat::from_u64(2).pow(u64::try_from(e - 2 * q).unwrap_or(0));
                let r = n.sqrt();
                let up = r < &n - &r * &r;
                pack(f, false, if up { r + 1 } else { r }, q)
            }
        }
    }
}

fn add_inf(f: Fmt, s: bool, w: Unpacked) -> u64 {
    match w {
        Unpacked::Inf(t) => {
            if s == t {
                inf_bits(f, s)
            } else {
                f.nan()
            }
        }
        _ => inf_bits(f, s),
    }
}

pub fn float_fma(f: Fmt, x: u64, y: u64, z: u64) -> u64 {
    match (unpack(f, x), unpack(f, y), unpack(f, z)) {
        (Unpacked::Nan, _, _) => f.nan(),
        (_, Unpacked::Nan, _) => f.nan(),
        (_, _, Unpacked::Nan) => f.nan(),
        (Unpacked::Inf(s), Unpacked::Inf(t), w) => add_inf(f, s != t, w),
        (Unpacked::Inf(s), Unpacked::Fin(t, m, _), w) => {
            if m == 0 {
                f.nan()
            } else {
                add_inf(f, s != t, w)
            }
        }
        (Unpacked::Fin(s, m, _), Unpacked::Inf(t), w) => {
            if m == 0 {
                f.nan()
            } else {
                add_inf(f, s != t, w)
            }
        }
        (Unpacked::Fin(_, _, _), Unpacked::Fin(_, _, _), Unpacked::Inf(u)) => inf_bits(f, u),
        (Unpacked::Fin(s, m, e), Unpacked::Fin(t, n, d), Unpacked::Fin(u, k, c)) => add_fin(
            f,
            s != t,
            Nat::from_u64(m) * Nat::from_u64(n),
            e + d,
            u,
            Nat::from_u64(k),
            c,
        ),
    }
}

fn order_key(f: Fmt, x: u64) -> u64 {
    let h: u64 = 1 << (f.width() - 1);
    if x / h % 2 == 1 {
        h - 1 - x % h
    } else {
        h + x % h
    }
}

pub fn float_lt(f: Fmt, a: u64, b: u64) -> bool {
    order_key(f, a) < order_key(f, b)
}

fn digits_text(s: &Nat, n: i64) -> String {
    let ds: Vec<char> = s.to_string().chars().collect();
    let k = ds.len() as i64;
    let whole = || -> String { ds.iter().collect() };
    let zeros = |c: i64| "0".repeat(usize::try_from(c).unwrap_or(0));
    let take = |c: i64| -> String { ds.iter().take(usize::try_from(c).unwrap_or(0)).collect() };
    let drop = |c: i64| -> String { ds.iter().skip(usize::try_from(c).unwrap_or(0)).collect() };
    let e = n - 1;
    if k <= n && n <= 21 {
        whole() + &zeros(n - k)
    } else if 0 < n && n < k {
        take(n) + "." + &drop(n)
    } else if -6 < n && n <= 0 {
        "0.".to_string() + &zeros(-n) + &whole()
    } else {
        take(1)
            + &(if 1 < k {
                ".".to_string() + &drop(1)
            } else {
                String::new()
            })
            + "e"
            + (if e < 0 { "-" } else { "+" })
            + &e.unsigned_abs().to_string()
    }
}

fn pow10_le(m: u64, e: i64, t: i64) -> bool {
    let (a, b) = rat_of(2, Nat::from_u64(m), e);
    let (c, d) = rat_of(10, Nat::from_u64(1), t);
    c * b <= a * d
}

fn dec_exp(m: u64, e: i64) -> i64 {
    let t = ((Nat::from_u64(m).log2() as i64 + e) * 1_292_913_986).div_euclid(1 << 32) + 1;
    if pow10_le(m, e, t) {
        t + 1
    } else if pow10_le(m, e, t - 1) {
        t
    } else {
        t - 1
    }
}

fn closest(lo: &Nat, hi: &Nat, y2: &Nat, exact: bool, n0: i64, k: u64) -> (Nat, i64) {
    let pw = Nat::from_u64(10).pow(17u64.saturating_sub(k));
    let sl = y2 / 2 / &pw;
    let c = (&sl * 2 + 1) * &pw;
    let in_l = *lo <= &sl * &pw;
    let in_h = (&sl + 1) * &pw <= *hi;
    let low = if in_l && in_h {
        *y2 < c || (*y2 == c && exact && &sl % 2 == 0)
    } else {
        in_l
    };
    if low {
        (sl, n0)
    } else if &sl + 1 == Nat::from_u64(10).pow(k) {
        (Nat::from_u64(10).pow(k.saturating_sub(1)), n0 + 1)
    } else {
        (sl + 1, n0)
    }
}

fn shortest(lo: &Nat, hi: &Nat, y2: &Nat, exact: bool, n0: i64, k: u64, fuel: u64) -> (Nat, i64) {
    match fuel {
        0 => closest(lo, hi, y2, exact, n0, k),
        _ => {
            let pw = Nat::from_u64(10).pow(17u64.saturating_sub(k));
            if *lo <= hi / &pw * &pw {
                closest(lo, hi, y2, exact, n0, k)
            } else {
                shortest(lo, hi, y2, exact, n0, k + 1, fuel - 1)
            }
        }
    }
}

fn pos_text(f: Fmt, m: u64, e: i64) -> String {
    let n0 = dec_exp(m, e);
    let (a, b) = rat_of(2, Nat::from_u64(1), e - 2);
    let (c, h) = rat_of(10, Nat::from_u64(1), 17 - n0);
    let p = a * c;
    let den = b * h;
    let g = if m == 1 << (f.prec() - 1) && qmin(f) < e {
        1
    } else {
        2
    };
    let ln = Nat::from_u64(4 * m - g) * &p;
    let hn = Nat::from_u64(4 * m + 2) * &p;
    let incl = m.is_multiple_of(2);
    let lo = if incl {
        (ln + &den - 1) / &den
    } else {
        ln / &den + 1
    };
    let hi = if incl { hn / &den } else { (hn - 1) / &den };
    let xn = Nat::from_u64(8 * m) * &p;
    let (s, n) = shortest(&lo, &hi, &(&xn / &den), (&xn % &den).is_zero(), n0, 1, 16);
    digits_text(&s, n)
}

pub fn float_text(f: Fmt, x: u64) -> String {
    match unpack(f, x) {
        Unpacked::Nan => "nan".to_string(),
        Unpacked::Inf(s) => (if s { "-inf" } else { "inf" }).to_string(),
        Unpacked::Fin(s, m, e) => {
            (if s { "-" } else { "" }).to_string()
                + &(if m == 0 {
                    "0".to_string()
                } else {
                    pos_text(f, m, e)
                })
        }
    }
}

fn nat_of(cs: &[char]) -> Nat {
    cs.iter().fold(Nat::default(), |a, &c| {
        a * 10 + u64::from(c).saturating_sub(48)
    })
}

fn plain_digits(cs: &[char]) -> bool {
    cs.iter().all(char::is_ascii_digit)
        && (cs == ['0'] || (!cs.is_empty() && cs.first() != Some(&'0')))
}

fn span_digits(cs: &[char]) -> (&[char], &[char]) {
    cs.split_at(
        cs.iter()
            .position(|c| !c.is_ascii_digit())
            .unwrap_or(cs.len()),
    )
}

fn frac_part(cs: &[char]) -> Option<(&[char], &[char])> {
    match cs {
        ['.', r @ ..] => {
            let (d, t) = span_digits(r);
            if d.is_empty() { None } else { Some((d, t)) }
        }
        r => Some((&[], r)),
    }
}

fn exp_part(cs: &[char]) -> Option<i64> {
    match cs {
        [] => Some(0),
        ['e', '+', r @ ..] => {
            if r.len() <= 3 && plain_digits(r) {
                Int::from(nat_of(r)).to_i64()
            } else {
                None
            }
        }
        ['e', '-', r @ ..] => {
            if r.len() <= 3 && plain_digits(r) {
                (-Int::from(nat_of(r))).to_i64()
            } else {
                None
            }
        }
        _ => None,
    }
}

fn atom_parts(cs: &[char]) -> Option<(bool, Nat, i64)> {
    let neg = cs.first() == Some(&'-');
    let (ip, rest) = span_digits(if neg { &cs[1..] } else { cs });
    if !plain_digits(ip) {
        return None;
    }
    let (fp, rest) = frac_part(rest)?;
    let x = exp_part(rest)?;
    Some((neg, nat_of(&[ip, fp].concat()), x - fp.len() as i64))
}

pub fn float_parse(f: Fmt, s: &str) -> Option<u64> {
    if s == "nan" {
        Some(f.nan())
    } else if s == "inf" {
        Some(inf_bits(f, false))
    } else if s == "-inf" {
        Some(inf_bits(f, true))
    } else if 25 < s.chars().count() {
        None
    } else {
        let (neg, n, x) = atom_parts(&s.chars().collect::<Vec<char>>())?;
        let (a, b) = rat_of(10, n, x);
        let r = round_rat(f, neg, &a, &b);
        if float_text(f, r) == s { Some(r) } else { None }
    }
}
