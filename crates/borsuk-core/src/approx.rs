use crate::nat::{Int, Nat};
use std::cmp::Ordering;
use std::ops::{Add, Mul, Neg, Sub};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Dyadic {
    Zero,
    OfOdd(Int, Int),
}

fn int(x: u64) -> Int {
    Int::from(Nat::from_u64(x))
}

fn amount(d: &Int) -> u64 {
    d.nat_abs().to_u64().unwrap_or(u64::MAX)
}

fn lit(x: i64) -> Dyadic {
    Dyadic::of_int(Int::from(x))
}

fn nat_dyadic(x: u64) -> Dyadic {
    Dyadic::of_int(int(x))
}

impl Dyadic {
    pub fn of_int_with_prec(i: Int, prec: Int) -> Dyadic {
        if i.is_zero() {
            Dyadic::Zero
        } else {
            let t = i.trailing_zeros();
            Dyadic::OfOdd(i >> t, prec - int(t))
        }
    }

    pub fn of_int(i: Int) -> Dyadic {
        Dyadic::of_int_with_prec(i, Int::default())
    }

    pub fn shift_left(&self, i: &Int) -> Dyadic {
        match self {
            Dyadic::Zero => Dyadic::Zero,
            Dyadic::OfOdd(n, k) => Dyadic::OfOdd(n.clone(), k - i),
        }
    }

    pub fn round_down(&self, prec: &Int) -> Dyadic {
        match self {
            Dyadic::Zero => Dyadic::Zero,
            Dyadic::OfOdd(n, k) => {
                let l = k - prec;
                if l < 0i64 {
                    self.clone()
                } else {
                    Dyadic::of_int_with_prec(n >> amount(&l), prec.clone())
                }
            }
        }
    }

    pub fn round_up(&self, prec: &Int) -> Dyadic {
        match self {
            Dyadic::Zero => Dyadic::Zero,
            Dyadic::OfOdd(n, k) => {
                let l = k - prec;
                if l < 0i64 {
                    self.clone()
                } else {
                    Dyadic::of_int_with_prec(-((-n) >> amount(&l)), prec.clone())
                }
            }
        }
    }

    pub fn div_at_prec(&self, b: &Dyadic, prec: &Int) -> Dyadic {
        match (self, b) {
            (_, Dyadic::Zero) | (Dyadic::Zero, _) => Dyadic::Zero,
            (Dyadic::OfOdd(na, ka), Dyadic::OfOdd(nb, kb)) => {
                let (num, den) = if *nb < 0i64 {
                    (-na, -nb)
                } else {
                    (na.clone(), nb.clone())
                };
                let e = kb - ka + prec;
                let q = if e < 0i64 {
                    num / (den << amount(&e))
                } else {
                    (num << amount(&e)) / den
                };
                Dyadic::of_int_with_prec(q, prec.clone())
            }
        }
    }
}

fn dyadic_add(x: &Dyadic, y: &Dyadic) -> Dyadic {
    match (x, y) {
        (Dyadic::Zero, y) => y.clone(),
        (x, Dyadic::Zero) => x.clone(),
        (Dyadic::OfOdd(n1, k1), Dyadic::OfOdd(n2, k2)) => {
            let d = k1 - k2;
            if d == 0i64 {
                Dyadic::of_int_with_prec(n1 + n2, k1.clone())
            } else if d > 0i64 {
                Dyadic::OfOdd(n1 + (n2 << amount(&d)), k1.clone())
            } else {
                Dyadic::OfOdd((n1 << amount(&d)) + n2, k2.clone())
            }
        }
    }
}

fn dyadic_mul(x: &Dyadic, y: &Dyadic) -> Dyadic {
    match (x, y) {
        (Dyadic::Zero, _) => Dyadic::Zero,
        (_, Dyadic::Zero) => Dyadic::Zero,
        (Dyadic::OfOdd(n1, k1), Dyadic::OfOdd(n2, k2)) => Dyadic::OfOdd(n1 * n2, k1 + k2),
    }
}

fn dyadic_neg(x: &Dyadic) -> Dyadic {
    match x {
        Dyadic::Zero => Dyadic::Zero,
        Dyadic::OfOdd(n, k) => Dyadic::OfOdd(-n, k.clone()),
    }
}

fn dyadic_sub(x: &Dyadic, y: &Dyadic) -> Dyadic {
    dyadic_add(x, &dyadic_neg(y))
}

macro_rules! binary {
    ($tr:ident, $method:ident, $func:ident) => {
        impl $tr<&Dyadic> for &Dyadic {
            type Output = Dyadic;
            fn $method(self, rhs: &Dyadic) -> Dyadic {
                $func(self, rhs)
            }
        }

        impl $tr<Dyadic> for &Dyadic {
            type Output = Dyadic;
            fn $method(self, rhs: Dyadic) -> Dyadic {
                $func(self, &rhs)
            }
        }

        impl $tr<&Dyadic> for Dyadic {
            type Output = Dyadic;
            fn $method(self, rhs: &Dyadic) -> Dyadic {
                $func(&self, rhs)
            }
        }

        impl $tr<Dyadic> for Dyadic {
            type Output = Dyadic;
            fn $method(self, rhs: Dyadic) -> Dyadic {
                $func(&self, &rhs)
            }
        }
    };
}

binary!(Add, add, dyadic_add);
binary!(Sub, sub, dyadic_sub);
binary!(Mul, mul, dyadic_mul);

impl Neg for &Dyadic {
    type Output = Dyadic;
    fn neg(self) -> Dyadic {
        dyadic_neg(self)
    }
}

impl Neg for Dyadic {
    type Output = Dyadic;
    fn neg(self) -> Dyadic {
        dyadic_neg(&self)
    }
}

impl Ord for Dyadic {
    fn cmp(&self, other: &Dyadic) -> Ordering {
        match (self, other) {
            (Dyadic::Zero, Dyadic::Zero) => Ordering::Equal,
            (Dyadic::Zero, Dyadic::OfOdd(n2, _)) => Int::default().cmp(n2),
            (Dyadic::OfOdd(n1, _), Dyadic::Zero) => n1.cmp(&Int::default()),
            (Dyadic::OfOdd(n1, k1), Dyadic::OfOdd(n2, k2)) => {
                let l = k2 - k1;
                if l < 0i64 {
                    n1.cmp(&(n2 << amount(&l)))
                } else {
                    (n1 << amount(&l)).cmp(n2)
                }
            }
        }
    }
}

impl PartialOrd for Dyadic {
    fn partial_cmp(&self, other: &Dyadic) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Bounds {
    pub lo: Dyadic,
    pub hi: Dyadic,
}

pub fn guard_bits() -> u64 {
    32
}

fn top_bit(x: &Dyadic) -> Int {
    match x {
        Dyadic::Zero => Int::default(),
        Dyadic::OfOdd(n, k) => int(n.nat_abs().log2()) - k,
    }
}

fn least(a: &Dyadic, b: &Dyadic) -> Dyadic {
    if a <= b { a.clone() } else { b.clone() }
}

fn greatest(a: &Dyadic, b: &Dyadic) -> Dyadic {
    if a <= b { b.clone() } else { a.clone() }
}

fn round_down_bits(p: u64, x: &Dyadic) -> Dyadic {
    x.round_down(&(int(p) - 1i64 - top_bit(x)))
}

fn round_up_bits(p: u64, x: &Dyadic) -> Dyadic {
    x.round_up(&(int(p) - 1i64 - top_bit(x)))
}

fn add_near(p: u64, a: &Dyadic, b: &Dyadic) -> Dyadic {
    if top_bit(b) + int(p) + 2i64 < top_bit(a) {
        if *b < Dyadic::Zero {
            a - lit(1).shift_left(&(top_bit(a) - int(p) - 2i64))
        } else {
            a.clone()
        }
    } else {
        a + b
    }
}

fn add_down(p: u64, a: &Dyadic, b: &Dyadic) -> Dyadic {
    round_down_bits(
        p,
        &(if *a == Dyadic::Zero {
            b.clone()
        } else if *b == Dyadic::Zero {
            a.clone()
        } else if top_bit(b) <= top_bit(a) {
            add_near(p, a, b)
        } else {
            add_near(p, b, a)
        }),
    )
}

fn add_up(p: u64, a: &Dyadic, b: &Dyadic) -> Dyadic {
    -add_down(p, &-a, &-b)
}

fn div_down(p: u64, a: &Dyadic, b: &Dyadic) -> Dyadic {
    a.div_at_prec(b, &(int(p) + top_bit(b) - top_bit(a)))
}

fn div_up(p: u64, a: &Dyadic, b: &Dyadic) -> Dyadic {
    -div_down(p, &-a, b)
}

fn sqrt_shift(p: u64, n: &Int, k: &Int) -> u64 {
    let s = (2 * p + 2).saturating_sub(n.nat_abs().log2() + 1);
    if (k + int(s)) % 2i64 == 0i64 {
        s
    } else {
        s + 1
    }
}

fn sqrt_down(p: u64, x: &Dyadic) -> Dyadic {
    match x {
        Dyadic::Zero => Dyadic::Zero,
        Dyadic::OfOdd(n, k) => {
            if *n < 0i64 {
                Dyadic::Zero
            } else {
                let s = sqrt_shift(p, n, k);
                round_down_bits(
                    p,
                    &Dyadic::of_int_with_prec(
                        Int::from((n.to_nat() << s).sqrt()),
                        (k + int(s)) / 2i64,
                    ),
                )
            }
        }
    }
}

fn sqrt_up(p: u64, x: &Dyadic) -> Dyadic {
    match x {
        Dyadic::Zero => Dyadic::Zero,
        Dyadic::OfOdd(n, k) => {
            if *n < 0i64 {
                Dyadic::Zero
            } else {
                let s = sqrt_shift(p, n, k);
                let m = n.to_nat() << s;
                let r = m.sqrt();
                let r = if &r * &r == m { r } else { r + 1u64 };
                round_up_bits(
                    p,
                    &Dyadic::of_int_with_prec(Int::from(r), (k + int(s)) / 2i64),
                )
            }
        }
    }
}

pub fn floor_int(x: &Dyadic) -> Int {
    match x {
        Dyadic::Zero => Int::default(),
        Dyadic::OfOdd(n, k) => {
            if *k <= 0i64 {
                n << amount(k)
            } else {
                n >> amount(k)
            }
        }
    }
}

impl Bounds {
    pub fn exact(x: Dyadic) -> Bounds {
        Bounds {
            lo: x.clone(),
            hi: x,
        }
    }

    pub fn neg(a: &Bounds) -> Bounds {
        Bounds {
            lo: -&a.hi,
            hi: -&a.lo,
        }
    }

    pub fn scale(k: &Int, a: &Bounds) -> Bounds {
        Bounds {
            lo: a.lo.shift_left(k),
            hi: a.hi.shift_left(k),
        }
    }

    fn mag(a: &Bounds) -> Dyadic {
        greatest(&-&a.lo, &a.hi)
    }

    pub fn add(w: u64, a: &Bounds, b: &Bounds) -> Bounds {
        Bounds {
            lo: add_down(w + guard_bits(), &a.lo, &b.lo),
            hi: add_up(w + guard_bits(), &a.hi, &b.hi),
        }
    }

    pub fn sub(w: u64, a: &Bounds, b: &Bounds) -> Bounds {
        Bounds::add(w, a, &Bounds::neg(b))
    }

    pub fn mul(w: u64, a: &Bounds, b: &Bounds) -> Bounds {
        let p1 = &a.lo * &b.lo;
        let p2 = &a.lo * &b.hi;
        let p3 = &a.hi * &b.lo;
        let p4 = &a.hi * &b.hi;
        Bounds {
            lo: round_down_bits(w + guard_bits(), &least(&least(&p1, &p2), &least(&p3, &p4))),
            hi: round_up_bits(
                w + guard_bits(),
                &greatest(&greatest(&p1, &p2), &greatest(&p3, &p4)),
            ),
        }
    }

    fn div_pos(w: u64, a: &Bounds, b: &Bounds) -> Bounds {
        Bounds {
            lo: div_down(
                w + guard_bits(),
                &a.lo,
                if Dyadic::Zero <= a.lo { &b.hi } else { &b.lo },
            ),
            hi: div_up(
                w + guard_bits(),
                &a.hi,
                if Dyadic::Zero <= a.hi { &b.lo } else { &b.hi },
            ),
        }
    }

    pub fn div(w: u64, a: &Bounds, b: &Bounds) -> Option<Bounds> {
        if Dyadic::Zero < b.lo {
            Some(Bounds::div_pos(w, a, b))
        } else if b.hi < Dyadic::Zero {
            Some(Bounds::neg(&Bounds::div_pos(w, a, &Bounds::neg(b))))
        } else {
            None
        }
    }

    pub fn sqrt(w: u64, a: &Bounds) -> Bounds {
        Bounds {
            lo: sqrt_down(w + guard_bits(), &a.lo),
            hi: sqrt_up(w + guard_bits(), &a.hi),
        }
    }
}

fn fact_go(t: u64, fuel: u64, n: u64, acc: u64) -> u64 {
    let (mut fuel, mut n, mut acc) = (fuel, n, acc);
    while fuel > 0 && acc < t {
        fuel -= 1;
        acc += u64::from((n + 1).ilog2());
        n += 1;
    }
    n
}

fn fact_terms(w: u64) -> u64 {
    fact_go(w + guard_bits() + 3, w + guard_bits() + 5, 1, 0)
}

fn halvings(w: u64) -> u64 {
    w.isqrt() / 4 + 1
}

fn sum_terms<F: Fn(u64, &Bounds) -> Bounds>(
    w: u64,
    next: &F,
    n: u64,
    k: u64,
    s: Bounds,
    t: Bounds,
) -> Bounds {
    let (mut k, mut s, mut t) = (k, s, t);
    for _ in 0..n {
        s = Bounds::add(w, &s, &t);
        t = next(k, &t);
        k += 1;
    }
    let r = Bounds::mag(&t).shift_left(&int(1));
    Bounds::add(w, &s, &Bounds { lo: -&r, hi: r })
}

fn taylor<F: Fn(u64, &Bounds) -> Bounds>(
    w: u64,
    x: &Bounds,
    n: u64,
    first: Bounds,
    next: F,
) -> Option<Bounds> {
    if Bounds::mag(x) <= lit(1) {
        Some(sum_terms(w, &next, n, 0, Bounds::exact(lit(0)), first))
    } else {
        None
    }
}

fn term(w: u64, t: &Bounds, y: &Bounds, d: u64) -> Bounds {
    Bounds::div_pos(w, &Bounds::mul(w, t, y), &Bounds::exact(nat_dyadic(d)))
}

pub fn exp_series(w: u64, x: &Bounds) -> Option<Bounds> {
    taylor(w, x, fact_terms(w), Bounds::exact(lit(1)), |k, t| {
        term(w, t, x, k + 1)
    })
}

pub fn sinh_series(w: u64, x: &Bounds) -> Option<Bounds> {
    let x2 = Bounds::mul(w, x, x);
    taylor(w, x, fact_terms(w) / 2 + 1, x.clone(), |k, t| {
        term(w, t, &x2, (2 * k + 2) * (2 * k + 3))
    })
}

pub fn sin_series(w: u64, x: &Bounds) -> Option<Bounds> {
    let x2 = Bounds::mul(w, x, x);
    taylor(w, x, fact_terms(w) / 2 + 1, x.clone(), |k, t| {
        Bounds::neg(&term(w, t, &x2, (2 * k + 2) * (2 * k + 3)))
    })
}

pub fn cos_series(w: u64, x: &Bounds) -> Option<Bounds> {
    let x2 = Bounds::mul(w, x, x);
    taylor(
        w,
        x,
        fact_terms(w) / 2 + 1,
        Bounds::exact(lit(1)),
        |k, t| Bounds::neg(&term(w, t, &x2, (2 * k + 1) * (2 * k + 2))),
    )
}

fn halve(w: u64, c: &Bounds, n: u64, x: Bounds) -> Bounds {
    let mut x = x;
    for _ in 0..n {
        let r = Bounds::sqrt(
            w,
            &Bounds::add(
                w,
                &Bounds::exact(lit(1)),
                &Bounds::mul(w, c, &Bounds::mul(w, &x, &x)),
            ),
        );
        x = Bounds::div_pos(w, &x, &Bounds::add(w, &Bounds::exact(lit(1)), &r));
    }
    x
}

fn half() -> Dyadic {
    Dyadic::of_int_with_prec(int(1), int(1))
}

fn arc_series(w: u64, c: &Bounds, x: &Bounds) -> Option<Bounds> {
    let h = halvings(w);
    let y = halve(w, c, h, x.clone());
    let y2 = Bounds::mul(w, &Bounds::neg(c), &Bounds::mul(w, &y, &y));
    let next = |k: u64, t: &Bounds| {
        term(
            w,
            &Bounds::mul(w, t, &y2),
            &Bounds::exact(nat_dyadic(2 * k + 1)),
            2 * k + 3,
        )
    };
    if Bounds::mag(&y) <= half() {
        Some(Bounds::scale(
            &int(h),
            &sum_terms(
                w,
                &next,
                (w + guard_bits() + 3) / (2 * h) + 1,
                0,
                Bounds::exact(lit(0)),
                y,
            ),
        ))
    } else {
        None
    }
}

pub fn atan_series(w: u64, x: &Bounds) -> Option<Bounds> {
    arc_series(w, &Bounds::exact(lit(1)), x)
}

pub fn atanh_series(w: u64, x: &Bounds) -> Option<Bounds> {
    if Bounds::mag(x) <= half() {
        arc_series(w, &Bounds::exact(lit(-1)), x)
    } else {
        None
    }
}

pub fn pi_bounds(w: u64) -> Option<Bounds> {
    atan_series(w, &Bounds::exact(lit(1))).map(|b| Bounds::scale(&int(2), &b))
}

pub fn ln2_bounds(w: u64) -> Option<Bounds> {
    atanh_series(
        w,
        &Bounds::div_pos(w, &Bounds::exact(lit(1)), &Bounds::exact(lit(3))),
    )
    .map(|b| Bounds::scale(&int(1), &b))
}

pub fn ln10_bounds(w: u64) -> Option<Bounds> {
    let l = ln2_bounds(w)?;
    let a = atanh_series(
        w,
        &Bounds::div_pos(w, &Bounds::exact(lit(1)), &Bounds::exact(lit(9))),
    )?;
    Some(Bounds::add(
        w,
        &Bounds::mul(w, &Bounds::exact(lit(3)), &l),
        &Bounds::scale(&int(1), &a),
    ))
}
