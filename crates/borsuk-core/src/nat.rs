use std::cmp::Ordering;
use std::fmt;
use std::ops::{Add, Div, Mul, Neg, Rem, Shl, Shr, Sub};

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Nat {
    limbs: Vec<u64>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Int {
    neg: bool,
    mag: Nat,
}

fn trim(mut v: Vec<u64>) -> Vec<u64> {
    while v.last() == Some(&0) {
        v.pop();
    }
    v
}

fn cmp_limbs(a: &[u64], b: &[u64]) -> Ordering {
    a.len()
        .cmp(&b.len())
        .then_with(|| a.iter().rev().cmp(b.iter().rev()))
}

fn add_limbs(a: &[u64], b: &[u64]) -> Vec<u64> {
    let (a, b) = if a.len() >= b.len() { (a, b) } else { (b, a) };
    let mut r = Vec::with_capacity(a.len() + 1);
    let mut carry = false;
    for (i, &x) in a.iter().enumerate() {
        let y = b.get(i).copied().unwrap_or(0);
        let (s, c1) = x.overflowing_add(y);
        let (s, c2) = s.overflowing_add(u64::from(carry));
        r.push(s);
        carry = c1 || c2;
    }
    if carry {
        r.push(1);
    }
    r
}

fn sub_limbs(a: &[u64], b: &[u64]) -> Vec<u64> {
    let mut r = Vec::with_capacity(a.len());
    let mut borrow = false;
    for (i, &x) in a.iter().enumerate() {
        let y = b.get(i).copied().unwrap_or(0);
        let (d, b1) = x.overflowing_sub(y);
        let (d, b2) = d.overflowing_sub(u64::from(borrow));
        r.push(d);
        borrow = b1 || b2;
    }
    trim(r)
}

fn mul_limbs(a: &[u64], b: &[u64]) -> Vec<u64> {
    if a.is_empty() || b.is_empty() {
        return Vec::new();
    }
    let mut r = vec![0u64; a.len() + b.len()];
    for (i, &x) in a.iter().enumerate() {
        let mut carry = 0u128;
        for (slot, &y) in r[i..i + b.len()].iter_mut().zip(b) {
            let t = u128::from(x) * u128::from(y) + u128::from(*slot) + carry;
            *slot = t as u64;
            carry = t >> 64;
        }
        r[i + b.len()] = carry as u64;
    }
    trim(r)
}

fn shift_up(a: &[u64], s: u32) -> Vec<u64> {
    let mut r = Vec::with_capacity(a.len() + 1);
    let mut carry = 0u64;
    for &x in a {
        if s == 0 {
            r.push(x);
        } else {
            r.push((x << s) | carry);
            carry = x >> (64 - s);
        }
    }
    r.push(carry);
    r
}

fn shift_down(a: &[u64], s: u32) -> Vec<u64> {
    let mut r = Vec::with_capacity(a.len());
    for (i, &x) in a.iter().enumerate() {
        if s == 0 {
            r.push(x);
        } else {
            let hi = a.get(i + 1).copied().unwrap_or(0);
            r.push((x >> s) | (hi << (64 - s)));
        }
    }
    trim(r)
}

fn shl_limbs(a: &[u64], s: u64) -> Vec<u64> {
    if a.is_empty() {
        return Vec::new();
    }
    let mut r = vec![0u64; (s / 64) as usize];
    r.extend(shift_up(a, (s % 64) as u32));
    trim(r)
}

fn shr_limbs(a: &[u64], s: u64) -> Vec<u64> {
    let skip = s / 64;
    if skip >= a.len() as u64 {
        return Vec::new();
    }
    shift_down(&a[skip as usize..], (s % 64) as u32)
}

fn div_rem_small(a: &[u64], d: u64) -> (Vec<u64>, u64) {
    let mut q = vec![0u64; a.len()];
    let mut rem = 0u128;
    for (slot, &x) in q.iter_mut().zip(a).rev() {
        let cur = (rem << 64) | u128::from(x);
        *slot = (cur / u128::from(d)) as u64;
        rem = cur % u128::from(d);
    }
    (trim(q), rem as u64)
}

fn div_rem_limbs(u: &[u64], v: &[u64]) -> (Vec<u64>, Vec<u64>) {
    if v.is_empty() || cmp_limbs(u, v) == Ordering::Less {
        return (Vec::new(), u.to_vec());
    }
    if let [d] = v {
        let (q, r) = div_rem_small(u, *d);
        return (q, trim(vec![r]));
    }
    let n = v.len();
    let m = u.len() - n;
    let s = v[n - 1].leading_zeros();
    let vn = &shift_up(v, s)[..n];
    let mut un = shift_up(u, s);
    let top = u128::from(vn[n - 1]);
    let next = u128::from(vn[n - 2]);
    let base = u128::from(u64::MAX);
    let mut q = Vec::with_capacity(m + 1);
    for j in (0..=m).rev() {
        let num = (u128::from(un[j + n]) << 64) | u128::from(un[j + n - 1]);
        let mut qhat = num / top;
        let mut rhat = num % top;
        while qhat > base || qhat * next > ((rhat << 64) | u128::from(un[j + n - 2])) {
            qhat -= 1;
            rhat += top;
            if rhat > base {
                break;
            }
        }
        let mut k = 0i128;
        for (x, &y) in un[j..j + n].iter_mut().zip(vn) {
            let p = qhat * u128::from(y);
            let t = i128::from(*x) - k - i128::from(p as u64);
            *x = t as u64;
            k = (p >> 64) as i128 - (t >> 64);
        }
        let t = i128::from(un[j + n]) - k;
        un[j + n] = t as u64;
        if t < 0 {
            qhat -= 1;
            let mut c = 0u128;
            for (x, &y) in un[j..j + n].iter_mut().zip(vn) {
                let sum = u128::from(*x) + u128::from(y) + c;
                *x = sum as u64;
                c = sum >> 64;
            }
            un[j + n] = un[j + n].wrapping_add(c as u64);
        }
        q.push(qhat as u64);
    }
    q.reverse();
    (trim(q), shift_down(&un[..n], s))
}

fn nat_add(a: &Nat, b: &Nat) -> Nat {
    Nat {
        limbs: add_limbs(&a.limbs, &b.limbs),
    }
}

fn nat_sub(a: &Nat, b: &Nat) -> Nat {
    if a <= b {
        Nat::default()
    } else {
        Nat {
            limbs: sub_limbs(&a.limbs, &b.limbs),
        }
    }
}

fn nat_mul(a: &Nat, b: &Nat) -> Nat {
    Nat {
        limbs: mul_limbs(&a.limbs, &b.limbs),
    }
}

fn nat_div_rem(a: &Nat, b: &Nat) -> (Nat, Nat) {
    let (q, r) = div_rem_limbs(&a.limbs, &b.limbs);
    (Nat { limbs: q }, Nat { limbs: r })
}

fn nat_div(a: &Nat, b: &Nat) -> Nat {
    nat_div_rem(a, b).0
}

fn nat_rem(a: &Nat, b: &Nat) -> Nat {
    nat_div_rem(a, b).1
}

fn nat_shl(a: &Nat, s: u64) -> Nat {
    Nat {
        limbs: shl_limbs(&a.limbs, s),
    }
}

fn nat_shr(a: &Nat, s: u64) -> Nat {
    Nat {
        limbs: shr_limbs(&a.limbs, s),
    }
}

impl Nat {
    pub fn from_u64(x: u64) -> Nat {
        Nat {
            limbs: trim(vec![x]),
        }
    }

    pub fn from_u128(x: u128) -> Nat {
        Nat {
            limbs: trim(vec![x as u64, (x >> 64) as u64]),
        }
    }

    pub fn to_u64(&self) -> Option<u64> {
        match self.limbs.as_slice() {
            [] => Some(0),
            [x] => Some(*x),
            _ => None,
        }
    }

    pub fn to_u128(&self) -> Option<u128> {
        match self.limbs.as_slice() {
            [] => Some(0),
            [x] => Some(u128::from(*x)),
            [x, y] => Some((u128::from(*y) << 64) | u128::from(*x)),
            _ => None,
        }
    }

    pub fn is_zero(&self) -> bool {
        self.limbs.is_empty()
    }

    pub fn log2(&self) -> u64 {
        match self.limbs.last() {
            None => 0,
            Some(top) => 64 * (self.limbs.len() as u64 - 1) + u64::from(63 - top.leading_zeros()),
        }
    }

    pub fn trailing_zeros(&self) -> u64 {
        let mut n = 0;
        for &x in &self.limbs {
            if x != 0 {
                return n + u64::from(x.trailing_zeros());
            }
            n += 64;
        }
        0
    }

    pub fn pow(&self, e: u64) -> Nat {
        let mut acc = Nat::from_u64(1);
        let mut base = self.clone();
        let mut e = e;
        while e > 0 {
            if e % 2 == 1 {
                acc = &acc * &base;
            }
            e /= 2;
            if e > 0 {
                base = &base * &base;
            }
        }
        acc
    }

    pub fn sqrt(&self) -> Nat {
        if *self <= 1 {
            return self.clone();
        }
        let mut guess = Nat::from_u64(1) << (self.log2() / 2 + 1);
        loop {
            let next = (&guess + self / &guess) / 2;
            if next < guess {
                guess = next;
            } else {
                return guess;
            }
        }
    }
}

fn make(neg: bool, mag: Nat) -> Int {
    Int {
        neg: neg && !mag.is_zero(),
        mag,
    }
}

fn add_signed(an: bool, a: &Nat, bn: bool, b: &Nat) -> Int {
    if an == bn {
        make(an, a + b)
    } else if a >= b {
        make(an, a - b)
    } else {
        make(bn, b - a)
    }
}

fn int_add(a: &Int, b: &Int) -> Int {
    add_signed(a.neg, &a.mag, b.neg, &b.mag)
}

fn int_sub(a: &Int, b: &Int) -> Int {
    add_signed(a.neg, &a.mag, !b.neg, &b.mag)
}

fn int_mul(a: &Int, b: &Int) -> Int {
    make(a.neg != b.neg, &a.mag * &b.mag)
}

fn int_div(a: &Int, b: &Int) -> Int {
    if b.mag.is_zero() {
        return Int::default();
    }
    let (q, r) = nat_div_rem(&a.mag, &b.mag);
    let q = if a.neg && !r.is_zero() { q + 1 } else { q };
    make(a.neg != b.neg, q)
}

fn int_rem(a: &Int, b: &Int) -> Int {
    if b.mag.is_zero() {
        return a.clone();
    }
    let r = &a.mag % &b.mag;
    if a.neg && !r.is_zero() {
        make(false, &b.mag - &r)
    } else {
        make(false, r)
    }
}

fn int_shl(a: &Int, s: u64) -> Int {
    make(a.neg, &a.mag << s)
}

fn int_shr(a: &Int, s: u64) -> Int {
    if a.neg {
        make(true, ((&a.mag - 1) >> s) + 1)
    } else {
        make(false, &a.mag >> s)
    }
}

impl Int {
    pub fn from_i64(x: i64) -> Int {
        make(x < 0, Nat::from_u64(x.unsigned_abs()))
    }

    pub fn from_i128(x: i128) -> Int {
        make(x < 0, Nat::from_u128(x.unsigned_abs()))
    }

    pub fn to_i64(&self) -> Option<i64> {
        let m = self.mag.to_u64()?;
        if self.neg {
            0i64.checked_sub_unsigned(m)
        } else {
            i64::try_from(m).ok()
        }
    }

    pub fn to_i128(&self) -> Option<i128> {
        let m = self.mag.to_u128()?;
        if self.neg {
            0i128.checked_sub_unsigned(m)
        } else {
            i128::try_from(m).ok()
        }
    }

    pub fn is_zero(&self) -> bool {
        self.mag.is_zero()
    }

    pub fn nat_abs(&self) -> Nat {
        self.mag.clone()
    }

    pub fn to_nat(&self) -> Nat {
        if self.neg {
            Nat::default()
        } else {
            self.mag.clone()
        }
    }

    pub fn trailing_zeros(&self) -> u64 {
        self.mag.trailing_zeros()
    }
}

impl From<u64> for Nat {
    fn from(x: u64) -> Nat {
        Nat::from_u64(x)
    }
}

impl From<i64> for Int {
    fn from(x: i64) -> Int {
        Int::from_i64(x)
    }
}

impl From<i128> for Int {
    fn from(x: i128) -> Int {
        Int::from_i128(x)
    }
}

impl From<Nat> for Int {
    fn from(x: Nat) -> Int {
        make(false, x)
    }
}

impl Ord for Nat {
    fn cmp(&self, other: &Nat) -> Ordering {
        cmp_limbs(&self.limbs, &other.limbs)
    }
}

impl PartialOrd for Nat {
    fn partial_cmp(&self, other: &Nat) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Int {
    fn cmp(&self, other: &Int) -> Ordering {
        match (self.neg, other.neg) {
            (false, false) => self.mag.cmp(&other.mag),
            (true, true) => other.mag.cmp(&self.mag),
            (false, true) => Ordering::Greater,
            (true, false) => Ordering::Less,
        }
    }
}

impl PartialOrd for Int {
    fn partial_cmp(&self, other: &Int) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq<u64> for Nat {
    fn eq(&self, other: &u64) -> bool {
        self.to_u64() == Some(*other)
    }
}

impl PartialOrd<u64> for Nat {
    fn partial_cmp(&self, other: &u64) -> Option<Ordering> {
        Some(match self.to_u64() {
            Some(x) => x.cmp(other),
            None => Ordering::Greater,
        })
    }
}

impl PartialEq<i64> for Int {
    fn eq(&self, other: &i64) -> bool {
        self.to_i64() == Some(*other)
    }
}

impl PartialOrd<i64> for Int {
    fn partial_cmp(&self, other: &i64) -> Option<Ordering> {
        Some(match self.to_i64() {
            Some(x) => x.cmp(other),
            None if self.neg => Ordering::Less,
            None => Ordering::Greater,
        })
    }
}

impl fmt::Display for Nat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut chunks = Vec::new();
        let mut rest = self.limbs.clone();
        while !rest.is_empty() {
            let (q, r) = div_rem_small(&rest, 10_000_000_000_000_000_000);
            chunks.push(r);
            rest = q;
        }
        match chunks.split_last() {
            None => write!(f, "0"),
            Some((top, low)) => {
                write!(f, "{top}")?;
                for c in low.iter().rev() {
                    write!(f, "{c:019}")?;
                }
                Ok(())
            }
        }
    }
}

impl Neg for Int {
    type Output = Int;
    fn neg(self) -> Int {
        make(!self.neg, self.mag)
    }
}

impl Neg for &Int {
    type Output = Int;
    fn neg(self) -> Int {
        make(!self.neg, self.mag.clone())
    }
}

macro_rules! binary {
    ($ty:ident, $prim:ty, $tr:ident, $method:ident, $func:ident) => {
        impl $tr<&$ty> for &$ty {
            type Output = $ty;
            fn $method(self, rhs: &$ty) -> $ty {
                $func(self, rhs)
            }
        }

        impl $tr<$ty> for &$ty {
            type Output = $ty;
            fn $method(self, rhs: $ty) -> $ty {
                $func(self, &rhs)
            }
        }

        impl $tr<&$ty> for $ty {
            type Output = $ty;
            fn $method(self, rhs: &$ty) -> $ty {
                $func(&self, rhs)
            }
        }

        impl $tr<$ty> for $ty {
            type Output = $ty;
            fn $method(self, rhs: $ty) -> $ty {
                $func(&self, &rhs)
            }
        }

        impl $tr<$prim> for &$ty {
            type Output = $ty;
            fn $method(self, rhs: $prim) -> $ty {
                $func(self, &$ty::from(rhs))
            }
        }

        impl $tr<$prim> for $ty {
            type Output = $ty;
            fn $method(self, rhs: $prim) -> $ty {
                $func(&self, &$ty::from(rhs))
            }
        }
    };
}

macro_rules! shift {
    ($ty:ident, $tr:ident, $method:ident, $func:ident) => {
        impl $tr<u64> for &$ty {
            type Output = $ty;
            fn $method(self, rhs: u64) -> $ty {
                $func(self, rhs)
            }
        }

        impl $tr<u64> for $ty {
            type Output = $ty;
            fn $method(self, rhs: u64) -> $ty {
                $func(&self, rhs)
            }
        }
    };
}

binary!(Nat, u64, Add, add, nat_add);
binary!(Nat, u64, Sub, sub, nat_sub);
binary!(Nat, u64, Mul, mul, nat_mul);
binary!(Nat, u64, Div, div, nat_div);
binary!(Nat, u64, Rem, rem, nat_rem);
binary!(Int, i64, Add, add, int_add);
binary!(Int, i64, Sub, sub, int_sub);
binary!(Int, i64, Mul, mul, int_mul);
binary!(Int, i64, Div, div, int_div);
binary!(Int, i64, Rem, rem, int_rem);
shift!(Nat, Shl, shl, nat_shl);
shift!(Nat, Shr, shr, nat_shr);
shift!(Int, Shl, shl, int_shl);
shift!(Int, Shr, shr, int_shr);
