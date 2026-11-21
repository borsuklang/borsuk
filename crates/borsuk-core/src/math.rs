use crate::approx::{
    Bounds, Dyadic, atan_series, atanh_series, cos_series, exp_series, floor_int, ln2_bounds,
    ln10_bounds, pi_bounds, sin_series, sinh_series,
};
use crate::float::{Fmt, Unpacked, inf_bits, qmin, round_rat, sign_bit, unpack};
use crate::ir::{Fn1, Fn2};
use crate::nat::{Int, Nat};

fn int(x: u64) -> Int {
    Int::from(Nat::from_u64(x))
}

fn lit(x: i64) -> Dyadic {
    Dyadic::of_int(Int::from(x))
}

fn to_u(x: &Int) -> u64 {
    x.to_nat().to_u64().unwrap_or(u64::MAX)
}

fn abs_u(x: &Int) -> u64 {
    x.nat_abs().to_u64().unwrap_or(u64::MAX)
}

fn exact_round(f: Fmt, neg: bool, a: &Nat, t: &Int) -> u64 {
    if a.is_zero() {
        sign_bit(f, neg)
    } else {
        let top = int(a.log2()) + t;
        if int(f.emax()) < top {
            inf_bits(f, neg)
        } else if &top + 2i64 <= qmin(f) {
            sign_bit(f, neg)
        } else if *t >= 0i64 {
            round_rat(
                f,
                neg,
                &(a * Nat::from_u64(2).pow(to_u(t))),
                &Nat::from_u64(1),
            )
        } else {
            round_rat(f, neg, a, &Nat::from_u64(2).pow(to_u(&-t)))
        }
    }
}

fn one_of(f: Fmt, neg: bool) -> u64 {
    exact_round(f, neg, &Nat::from_u64(1), &Int::default())
}

fn round_end(f: Fmt, neg: bool, d: &Dyadic) -> u64 {
    match d {
        Dyadic::Zero => sign_bit(f, neg),
        Dyadic::OfOdd(n, k) => exact_round(f, neg, &n.nat_abs(), &-k),
    }
}

fn settle(f: Fmt, b: &Bounds) -> Option<u64> {
    let neg = b.lo < Dyadic::Zero;
    if neg && Dyadic::Zero < b.hi {
        None
    } else {
        let r = round_end(f, neg, &b.lo);
        if r == round_end(f, neg, &b.hi) {
            Some(r)
        } else {
            None
        }
    }
}

fn search<F: Fn(u64) -> Option<Bounds>>(f: Fmt, step: &F, j: u32, n: u32) -> Option<u64> {
    match n {
        0 => None,
        _ => match step(64 * 2u64.pow(j)).and_then(|b| settle(f, &b)) {
            Some(r) => Some(r),
            None => search(f, step, j + 1, n - 1),
        },
    }
}

fn refine<F: Fn(u64) -> Option<Bounds>>(f: Fmt, step: F) -> Option<u64> {
    search(f, &step, 0, 11)
}

fn to_dy(neg: bool, m: u64, e: i64) -> Dyadic {
    Dyadic::of_int_with_prec(if neg { -int(m) } else { int(m) }, Int::from(-e))
}

fn odd_parts(neg: bool, m: u64, e: i64) -> (Int, Int) {
    match to_dy(neg, m, e) {
        Dyadic::Zero => (Int::default(), Int::default()),
        Dyadic::OfOdd(n, k) => (n, k),
    }
}

fn top_of(m: &Nat, e: i64) -> i64 {
    m.log2() as i64 + e
}

fn one_half() -> Dyadic {
    Dyadic::of_int_with_prec(int(1), int(1))
}

fn one_bounds() -> Bounds {
    Bounds::exact(lit(1))
}

fn pi_const(f: Fmt, n: i64, k: i64) -> Option<u64> {
    refine(f, |w| {
        pi_bounds(w)
            .map(|p| Bounds::scale(&Int::from(k), &Bounds::mul(w, &Bounds::exact(lit(n)), &p)))
    })
}

fn exp_of(w: u64, t: &Bounds) -> Option<Bounds> {
    let p = w + 16;
    let l = ln2_bounds(p)?;
    let q = Bounds::div(p, t, &l)?;
    let k = floor_int(&(&q.lo + one_half()));
    let e = exp_series(
        p,
        &Bounds::sub(
            p,
            t,
            &Bounds::mul(p, &Bounds::exact(Dyadic::of_int(k.clone())), &l),
        ),
    )?;
    Some(Bounds::scale(&k, &e))
}

fn ln_parts(m: u64, e: i64) -> (i64, Dyadic) {
    let l = Nat::from_u64(m).log2();
    if 3u64 << l <= 2 * m {
        (l as i64 + e + 1, to_dy(false, m, -(l as i64) - 1))
    } else {
        (l as i64 + e, to_dy(false, m, -(l as i64)))
    }
}

fn ln_mant(w: u64, a: &Dyadic) -> Option<Bounds> {
    let z = Bounds::div(w, &Bounds::exact(a - lit(1)), &Bounds::exact(a + lit(1)))?;
    let s = atanh_series(w, &z)?;
    Some(Bounds::scale(&Int::from(1i64), &s))
}

fn ln_of(w: u64, m: u64, e: i64) -> Option<Bounds> {
    let (k, a) = ln_parts(m, e);
    let s = ln_mant(w, &a)?;
    let l = ln2_bounds(w)?;
    Some(Bounds::add(
        w,
        &Bounds::mul(w, &Bounds::exact(lit(k)), &l),
        &s,
    ))
}

fn log2_of(w: u64, m: u64, e: i64) -> Option<Bounds> {
    let (k, a) = ln_parts(m, e);
    let s = ln_mant(w, &a)?;
    let l = ln2_bounds(w)?;
    let q = Bounds::div(w, &s, &l)?;
    Some(Bounds::add(w, &Bounds::exact(lit(k)), &q))
}

fn log10_of(w: u64, m: u64, e: i64) -> Option<Bounds> {
    let v = ln_of(w, m, e)?;
    let t = ln10_bounds(w)?;
    Bounds::div(w, &v, &t)
}

fn reduce(w: u64, x: &Dyadic, top: i64) -> Option<(Int, Bounds)> {
    let p = w + u64::try_from(top).unwrap_or(0);
    let pi = pi_bounds(p)?;
    let h = Bounds::scale(&Int::from(-1i64), &pi);
    let q = Bounds::div(p, &Bounds::exact(x.clone()), &h)?;
    let k = floor_int(&(&q.lo + one_half()));
    Some((
        &k % 4i64,
        Bounds::sub(
            p,
            &Bounds::exact(x.clone()),
            &Bounds::mul(p, &Bounds::exact(Dyadic::of_int(k)), &h),
        ),
    ))
}

fn sin_of(w: u64, x: &Dyadic, top: i64) -> Option<Bounds> {
    let (k, r) = reduce(w, x, top)?;
    if k == 0i64 {
        sin_series(w, &r)
    } else if k == 1i64 {
        cos_series(w, &r)
    } else if k == 2i64 {
        sin_series(w, &r).map(|b| Bounds::neg(&b))
    } else {
        cos_series(w, &r).map(|b| Bounds::neg(&b))
    }
}

fn cos_of(w: u64, x: &Dyadic, top: i64) -> Option<Bounds> {
    let (k, r) = reduce(w, x, top)?;
    if k == 0i64 {
        cos_series(w, &r)
    } else if k == 1i64 {
        sin_series(w, &r).map(|b| Bounds::neg(&b))
    } else if k == 2i64 {
        cos_series(w, &r).map(|b| Bounds::neg(&b))
    } else {
        sin_series(w, &r)
    }
}

fn tan_of(w: u64, x: &Dyadic, top: i64) -> Option<Bounds> {
    let (k, r) = reduce(w, x, top)?;
    let s = sin_series(w, &r)?;
    let c = cos_series(w, &r)?;
    if &k % 2i64 == 0i64 {
        Bounds::div(w, &s, &c)
    } else {
        Bounds::div(w, &c, &s).map(|b| Bounds::neg(&b))
    }
}

fn asin_of(w: u64, x: &Dyadic) -> Option<Bounds> {
    let d = Bounds::mul(
        w,
        &Bounds::sub(w, &one_bounds(), &Bounds::exact(x.clone())),
        &Bounds::add(w, &one_bounds(), &Bounds::exact(x.clone())),
    );
    let q = Bounds::div(w, &Bounds::exact(x.clone()), &Bounds::sqrt(w, &d))?;
    atan_series(w, &q)
}

fn acos_of(w: u64, x: &Dyadic) -> Option<Bounds> {
    let u = Bounds::div(
        w,
        &Bounds::sub(w, &one_bounds(), &Bounds::exact(x.clone())),
        &Bounds::add(w, &one_bounds(), &Bounds::exact(x.clone())),
    )?;
    let t = atan_series(w, &Bounds::sqrt(w, &u))?;
    Some(Bounds::scale(&Int::from(1i64), &t))
}

fn sinh_of(w: u64, x: &Dyadic, big: bool) -> Option<Bounds> {
    if big {
        let a = exp_of(w, &Bounds::exact(x.clone()))?;
        let b = Bounds::div(w, &one_bounds(), &a)?;
        Some(Bounds::scale(&Int::from(-1i64), &Bounds::sub(w, &a, &b)))
    } else {
        sinh_series(w, &Bounds::exact(x.clone()))
    }
}

fn cosh_of(w: u64, x: &Dyadic) -> Option<Bounds> {
    let a = exp_of(w, &Bounds::exact(x.clone()))?;
    let b = Bounds::div(w, &one_bounds(), &a)?;
    Some(Bounds::scale(&Int::from(-1i64), &Bounds::add(w, &a, &b)))
}

fn tanh_of(w: u64, x: &Dyadic, neg: bool, big: bool) -> Option<Bounds> {
    if big {
        let a = exp_of(
            w,
            &Bounds::exact(if neg {
                x.shift_left(&Int::from(1i64))
            } else {
                -x.shift_left(&Int::from(1i64))
            }),
        )?;
        let t = Bounds::div(
            w,
            &Bounds::sub(w, &one_bounds(), &a),
            &Bounds::add(w, &one_bounds(), &a),
        )?;
        Some(if neg { Bounds::neg(&t) } else { t })
    } else {
        let s = sinh_series(w, &Bounds::exact(x.clone()))?;
        Bounds::div(
            w,
            &s,
            &Bounds::sqrt(w, &Bounds::add(w, &one_bounds(), &Bounds::mul(w, &s, &s))),
        )
    }
}

fn is_big(m: u64, e: i64) -> bool {
    lit(1) <= to_dy(false, m, e)
}

fn over_range(m: u64, e: i64) -> bool {
    11 <= top_of(&Nat::from_u64(m), e)
}

fn exp_fn(f: Fmt, a: Unpacked) -> Option<u64> {
    match a {
        Unpacked::Nan => Some(f.nan()),
        Unpacked::Inf(s) => Some(if s {
            sign_bit(f, false)
        } else {
            inf_bits(f, false)
        }),
        Unpacked::Fin(s, m, e) => {
            if m == 0 {
                Some(one_of(f, false))
            } else if over_range(m, e) {
                Some(if s {
                    sign_bit(f, false)
                } else {
                    inf_bits(f, false)
                })
            } else {
                refine(f, |w| exp_of(w, &Bounds::exact(to_dy(s, m, e))))
            }
        }
    }
}

fn exp2_fn(f: Fmt, a: Unpacked) -> Option<u64> {
    match a {
        Unpacked::Nan => Some(f.nan()),
        Unpacked::Inf(s) => Some(if s {
            sign_bit(f, false)
        } else {
            inf_bits(f, false)
        }),
        Unpacked::Fin(s, m, e) => {
            let (n, k) = odd_parts(s, m, e);
            if k <= 0i64 {
                Some(exact_round(f, false, &Nat::from_u64(1), &(&n << abs_u(&k))))
            } else if over_range(m, e) {
                Some(if s {
                    sign_bit(f, false)
                } else {
                    inf_bits(f, false)
                })
            } else {
                let x = to_dy(s, m, e);
                let i = floor_int(&(&x + one_half()));
                refine(f, |w| {
                    let l = ln2_bounds(w)?;
                    let v = exp_series(
                        w,
                        &Bounds::mul(w, &Bounds::exact(&x - Dyadic::of_int(i.clone())), &l),
                    )?;
                    Some(Bounds::scale(&i, &v))
                })
            }
        }
    }
}

fn log_fn<E: Fn(&Int, &Int) -> Option<u64>, S: Fn(u64, u64, i64) -> Option<Bounds>>(
    f: Fmt,
    exact: E,
    step: S,
    a: Unpacked,
) -> Option<u64> {
    match a {
        Unpacked::Nan => Some(f.nan()),
        Unpacked::Inf(s) => Some(if s { f.nan() } else { inf_bits(f, false) }),
        Unpacked::Fin(s, m, e) => {
            if m == 0 {
                Some(inf_bits(f, true))
            } else if s {
                Some(f.nan())
            } else {
                let (n, k) = odd_parts(false, m, e);
                if n == 1i64 && k == 0i64 {
                    Some(sign_bit(f, false))
                } else {
                    match exact(&n, &k) {
                        Some(r) => Some(r),
                        None => refine(f, |w| step(w, m, e)),
                    }
                }
            }
        }
    }
}

fn log2_exact(f: Fmt, n: &Int, k: &Int) -> Option<u64> {
    if *n == 1i64 {
        Some(exact_round(f, *k > 0i64, &k.nat_abs(), &Int::default()))
    } else {
        None
    }
}

fn log10_exact(f: Fmt, n: &Int, k: &Int) -> Option<u64> {
    if *k <= 0i64 && k.nat_abs() <= f.prec() && *n == Int::from(Nat::from_u64(5).pow(abs_u(k))) {
        Some(exact_round(f, false, &k.nat_abs(), &Int::default()))
    } else {
        None
    }
}

fn trig_fn<Z: Fn(bool) -> u64, S: Fn(u64, &Dyadic, i64) -> Option<Bounds>>(
    f: Fmt,
    zero: Z,
    step: S,
    a: Unpacked,
) -> Option<u64> {
    match a {
        Unpacked::Nan => Some(f.nan()),
        Unpacked::Inf(_) => Some(f.nan()),
        Unpacked::Fin(s, m, e) => {
            if m == 0 {
                Some(zero(s))
            } else {
                refine(f, |w| {
                    step(w, &to_dy(s, m, e), top_of(&Nat::from_u64(m), e))
                })
            }
        }
    }
}

fn asin_fn(f: Fmt, a: Unpacked) -> Option<u64> {
    match a {
        Unpacked::Nan => Some(f.nan()),
        Unpacked::Inf(_) => Some(f.nan()),
        Unpacked::Fin(s, m, e) => {
            let a = to_dy(false, m, e);
            if m == 0 {
                Some(sign_bit(f, s))
            } else if lit(1) < a {
                Some(f.nan())
            } else if a == lit(1) {
                pi_const(f, if s { -1 } else { 1 }, -1)
            } else {
                refine(f, |w| asin_of(w, &to_dy(s, m, e)))
            }
        }
    }
}

fn acos_fn(f: Fmt, a: Unpacked) -> Option<u64> {
    match a {
        Unpacked::Nan => Some(f.nan()),
        Unpacked::Inf(_) => Some(f.nan()),
        Unpacked::Fin(s, m, e) => {
            let a = to_dy(false, m, e);
            if lit(1) < a {
                Some(f.nan())
            } else if a == lit(1) {
                if s {
                    pi_const(f, 1, 0)
                } else {
                    Some(sign_bit(f, false))
                }
            } else {
                refine(f, |w| acos_of(w, &to_dy(s, m, e)))
            }
        }
    }
}

fn atan_fn(f: Fmt, a: Unpacked) -> Option<u64> {
    match a {
        Unpacked::Nan => Some(f.nan()),
        Unpacked::Inf(s) => pi_const(f, if s { -1 } else { 1 }, -1),
        Unpacked::Fin(s, m, e) => {
            if m == 0 {
                Some(sign_bit(f, s))
            } else {
                refine(f, |w| atan_series(w, &Bounds::exact(to_dy(s, m, e))))
            }
        }
    }
}

fn sinh_fn(f: Fmt, a: Unpacked) -> Option<u64> {
    match a {
        Unpacked::Nan => Some(f.nan()),
        Unpacked::Inf(s) => Some(inf_bits(f, s)),
        Unpacked::Fin(s, m, e) => {
            if m == 0 {
                Some(sign_bit(f, s))
            } else if over_range(m, e) {
                Some(inf_bits(f, s))
            } else {
                refine(f, |w| sinh_of(w, &to_dy(s, m, e), is_big(m, e)))
            }
        }
    }
}

fn cosh_fn(f: Fmt, a: Unpacked) -> Option<u64> {
    match a {
        Unpacked::Nan => Some(f.nan()),
        Unpacked::Inf(_) => Some(inf_bits(f, false)),
        Unpacked::Fin(s, m, e) => {
            if m == 0 {
                Some(one_of(f, false))
            } else if over_range(m, e) {
                Some(inf_bits(f, false))
            } else {
                refine(f, |w| cosh_of(w, &to_dy(s, m, e)))
            }
        }
    }
}

fn tanh_fn(f: Fmt, a: Unpacked) -> Option<u64> {
    match a {
        Unpacked::Nan => Some(f.nan()),
        Unpacked::Inf(s) => Some(one_of(f, s)),
        Unpacked::Fin(s, m, e) => {
            if m == 0 {
                Some(sign_bit(f, s))
            } else if over_range(m, e) {
                Some(one_of(f, s))
            } else {
                refine(f, |w| tanh_of(w, &to_dy(s, m, e), s, is_big(m, e)))
            }
        }
    }
}

fn cbrt_go(n: &Nat, i: u64, r: Nat) -> Nat {
    match i {
        0 => r,
        _ => {
            let t = &r + Nat::from_u64(2).pow(i - 1);
            cbrt_go(n, i - 1, if t.pow(3) <= *n { t } else { r })
        }
    }
}

fn root_round(f: Fmt, neg: bool, r: &Nat, exact: bool, q: i64) -> u64 {
    if exact {
        exact_round(f, neg, r, &Int::from(q))
    } else {
        exact_round(f, neg, &(r * 2 + 1), &Int::from(q - 1))
    }
}

fn cbrt_fn(f: Fmt, x: u64, a: Unpacked) -> Option<u64> {
    match a {
        Unpacked::Nan => Some(f.nan()),
        Unpacked::Inf(_) => Some(x),
        Unpacked::Fin(s, m, e) => {
            if m == 0 {
                Some(x)
            } else {
                let q = top_of(&Nat::from_u64(m), e).div_euclid(3) - f.prec() as i64 - 1;
                let n =
                    Nat::from_u64(m) * Nat::from_u64(2).pow(u64::try_from(e - 3 * q).unwrap_or(0));
                let r = cbrt_go(&n, n.log2() / 3 + 1, Nat::default());
                Some(root_round(f, s, &r, r.pow(3) == n, q))
            }
        }
    }
}

fn hypot_exact(f: Fmt, m: u64, e: i64, n: u64, d: i64) -> u64 {
    let c = e.min(d);
    let s = Nat::from_u64(m).pow(2) * Nat::from_u64(4).pow(u64::try_from(e - c).unwrap_or(0))
        + Nat::from_u64(n).pow(2) * Nat::from_u64(4).pow(u64::try_from(d - c).unwrap_or(0));
    let q = (top_of(&s, 2 * c).div_euclid(2) - f.prec() as i64 - 1).min(c);
    let v = s * Nat::from_u64(4).pow(u64::try_from(c - q).unwrap_or(0));
    let r = v.sqrt();
    root_round(f, false, &r, &r * &r == v, q)
}

fn hypot_fn(f: Fmt, a: Unpacked, b: Unpacked) -> Option<u64> {
    match (a, b) {
        (Unpacked::Inf(_), _) => Some(inf_bits(f, false)),
        (_, Unpacked::Inf(_)) => Some(inf_bits(f, false)),
        (Unpacked::Nan, _) => Some(f.nan()),
        (_, Unpacked::Nan) => Some(f.nan()),
        (Unpacked::Fin(_, m, e), Unpacked::Fin(_, n, d)) => {
            if n == 0 {
                Some(exact_round(f, false, &Nat::from_u64(m), &Int::from(e)))
            } else if m == 0 {
                Some(exact_round(f, false, &Nat::from_u64(n), &Int::from(d)))
            } else {
                Some(hypot_exact(f, m, e, n, d))
            }
        }
    }
}

fn atan2_of(w: u64, y: &Dyadic, x: &Dyadic, sy: bool, sx: bool) -> Option<Bounds> {
    let q = Bounds::div(w, &Bounds::exact(y.clone()), &Bounds::exact(x.clone()))?;
    let a = atan_series(w, &q)?;
    if sx {
        let pi = pi_bounds(w)?;
        Some(if sy {
            Bounds::sub(w, &a, &pi)
        } else {
            Bounds::add(w, &a, &pi)
        })
    } else {
        Some(a)
    }
}

fn atan2_fn(f: Fmt, a: Unpacked, b: Unpacked) -> Option<u64> {
    match (a, b) {
        (Unpacked::Nan, _) => Some(f.nan()),
        (_, Unpacked::Nan) => Some(f.nan()),
        (Unpacked::Fin(sy, my, ey), Unpacked::Fin(sx, mx, ex)) => {
            if my == 0 {
                if sx {
                    pi_const(f, if sy { -1 } else { 1 }, 0)
                } else {
                    Some(sign_bit(f, sy))
                }
            } else if mx == 0 {
                pi_const(f, if sy { -1 } else { 1 }, -1)
            } else {
                refine(f, |w| {
                    atan2_of(w, &to_dy(sy, my, ey), &to_dy(sx, mx, ex), sy, sx)
                })
            }
        }
        (Unpacked::Fin(sy, _, _), Unpacked::Inf(sx)) => {
            if sx {
                pi_const(f, if sy { -1 } else { 1 }, 0)
            } else {
                Some(sign_bit(f, sy))
            }
        }
        (Unpacked::Inf(sy), Unpacked::Fin(_, _, _)) => pi_const(f, if sy { -1 } else { 1 }, -1),
        (Unpacked::Inf(sy), Unpacked::Inf(sx)) => {
            if sx {
                pi_const(f, if sy { -3 } else { 3 }, -2)
            } else {
                pi_const(f, if sy { -1 } else { 1 }, -2)
            }
        }
    }
}

fn pow_odd(lim: u64, r: &Nat, c: &Nat) -> Option<Nat> {
    if *r == 1 {
        Some(Nat::from_u64(1))
    } else if Nat::from_u64(lim) < Nat::from_u64(r.log2()) * c + 1 {
        None
    } else {
        let v = r.pow(c.to_u64().unwrap_or(u64::MAX));
        if v.log2() < lim { Some(v) } else { None }
    }
}

fn root2k(a: Nat, k: u64) -> Option<Nat> {
    match k {
        0 => Some(a),
        _ => {
            if a == 1 {
                Some(Nat::from_u64(1))
            } else {
                let r = a.sqrt();
                if &r * &r == a { root2k(r, k - 1) } else { None }
            }
        }
    }
}

fn pow_exact(f: Fmt, neg: bool, a: &Nat, e: &Int, c: &Int, k: &Int) -> Option<u64> {
    let lim = f.prec() + 1;
    if *k <= 0i64 {
        let y = c << abs_u(k);
        if y > 0i64 {
            pow_odd(lim, a, &y.to_nat()).map(|v| exact_round(f, neg, &v, &(e * &y)))
        } else if *a == 1 {
            Some(exact_round(f, neg, &Nat::from_u64(1), &(e * &y)))
        } else {
            None
        }
    } else {
        let d = Int::from(Nat::from_u64(2).pow(to_u(k)));
        if e % &d != 0i64 {
            None
        } else {
            root2k(a.clone(), to_u(k)).and_then(|r| {
                if *c > 0i64 {
                    pow_odd(lim, &r, &c.to_nat()).map(|v| exact_round(f, neg, &v, &(e / &d * c)))
                } else if r == 1 {
                    Some(exact_round(f, neg, &Nat::from_u64(1), &(e / &d * c)))
                } else {
                    None
                }
            })
        }
    }
}

fn pow_steps(f: Fmt, neg: bool, m: u64, e: i64, y: &Dyadic) -> Option<u64> {
    refine(f, |w| {
        let l = ln_of(w + 16, m, e)?;
        let r = exp_of(w, &Bounds::mul(w + 16, &Bounds::exact(y.clone()), &l))?;
        Some(if neg { Bounds::neg(&r) } else { r })
    })
}

fn pow_loop(f: Fmt, neg: bool, m: u64, e: i64, y: &Dyadic) -> Option<u64> {
    match ln_of(64, m, e).map(|l| Bounds::mul(64, &Bounds::exact(y.clone()), &l)) {
        Some(t) => {
            if lit(2048) <= t.lo {
                Some(inf_bits(f, neg))
            } else if t.hi <= lit(-2048) {
                Some(sign_bit(f, neg))
            } else {
                pow_steps(f, neg, m, e, y)
            }
        }
        None => pow_steps(f, neg, m, e, y),
    }
}

fn odd_int(u: Unpacked) -> bool {
    match u {
        Unpacked::Fin(s, m, e) => m != 0 && odd_parts(s, m, e).1 == 0i64,
        _ => false,
    }
}

fn is_int(u: Unpacked) -> bool {
    match u {
        Unpacked::Fin(s, m, e) => odd_parts(s, m, e).1 <= 0i64,
        _ => false,
    }
}

fn below(u: Unpacked) -> bool {
    match u {
        Unpacked::Inf(s) => s,
        Unpacked::Fin(s, m, _) => s && m != 0,
        Unpacked::Nan => false,
    }
}

fn pow_fn(f: Fmt, x: Unpacked, y: Unpacked) -> Option<u64> {
    let one = match x {
        Unpacked::Fin(false, m, e) => odd_parts(false, m, e) == (int(1), Int::default()),
        _ => false,
    };
    let y_zero = match y {
        Unpacked::Fin(_, m, _) => m == 0,
        _ => false,
    };
    if one || y_zero {
        Some(one_of(f, false))
    } else {
        match (x, y) {
            (Unpacked::Nan, _) => Some(f.nan()),
            (_, Unpacked::Nan) => Some(f.nan()),
            (Unpacked::Inf(sx), _) => {
                let odd = sx && odd_int(y);
                Some(if below(y) {
                    sign_bit(f, odd)
                } else {
                    inf_bits(f, odd)
                })
            }
            (Unpacked::Fin(_, mx, ex), Unpacked::Inf(sy)) => {
                if mx == 0 {
                    Some(if sy {
                        inf_bits(f, false)
                    } else {
                        sign_bit(f, false)
                    })
                } else {
                    let a = to_dy(false, mx, ex);
                    if a == lit(1) {
                        Some(one_of(f, false))
                    } else {
                        Some(if (a < lit(1)) == sy {
                            inf_bits(f, false)
                        } else {
                            sign_bit(f, false)
                        })
                    }
                }
            }
            (Unpacked::Fin(sx, mx, ex), Unpacked::Fin(sy, my, ey)) => {
                let odd = sx && odd_int(y);
                if mx == 0 {
                    Some(if below(y) {
                        inf_bits(f, odd)
                    } else {
                        sign_bit(f, odd)
                    })
                } else if sx && !is_int(y) {
                    Some(f.nan())
                } else {
                    let (a, e) = odd_parts(false, mx, ex);
                    let (c, k) = odd_parts(sy, my, ey);
                    match pow_exact(f, odd, &a.to_nat(), &-e, &c, &k) {
                        Some(r) => Some(r),
                        None => pow_loop(f, odd, mx, ex, &to_dy(sy, my, ey)),
                    }
                }
            }
        }
    }
}

pub fn math1(f: Fmt, func: Fn1, x: u64) -> Option<u64> {
    let a = unpack(f, x);
    match func {
        Fn1::Exp => exp_fn(f, a),
        Fn1::Exp2 => exp2_fn(f, a),
        Fn1::Log => log_fn(f, |_, _| None, ln_of, a),
        Fn1::Log2 => log_fn(f, |n, k| log2_exact(f, n, k), log2_of, a),
        Fn1::Log10 => log_fn(f, |n, k| log10_exact(f, n, k), log10_of, a),
        Fn1::Sin => trig_fn(f, |s| sign_bit(f, s), sin_of, a),
        Fn1::Cos => trig_fn(f, |_| one_of(f, false), cos_of, a),
        Fn1::Tan => trig_fn(f, |s| sign_bit(f, s), tan_of, a),
        Fn1::Asin => asin_fn(f, a),
        Fn1::Acos => acos_fn(f, a),
        Fn1::Atan => atan_fn(f, a),
        Fn1::Sinh => sinh_fn(f, a),
        Fn1::Cosh => cosh_fn(f, a),
        Fn1::Tanh => tanh_fn(f, a),
        Fn1::Cbrt => cbrt_fn(f, x, a),
    }
}

pub fn math2(f: Fmt, func: Fn2, a: u64, b: u64) -> Option<u64> {
    match func {
        Fn2::Pow => pow_fn(f, unpack(f, a), unpack(f, b)),
        Fn2::Atan2 => atan2_fn(f, unpack(f, a), unpack(f, b)),
        Fn2::Hypot => hypot_fn(f, unpack(f, a), unpack(f, b)),
    }
}
