use std::iter;

use crate::ir::{Fault, Mode, Ty};
use crate::nat::{Int, Nat};

pub const DEC_MAX: i128 = 10i128.pow(38) - 1;

pub fn dec_in(c: i128) -> bool {
    (-DEC_MAX..=DEC_MAX).contains(&c)
}

pub fn dec_fit(c: i128) -> Result<i128, Fault> {
    if dec_in(c) {
        Ok(c)
    } else {
        Err(Fault::Overflow)
    }
}

pub fn dec_add(a: i128, b: i128) -> Result<i128, Fault> {
    a.checked_add(b).map_or(Err(Fault::Overflow), dec_fit)
}

pub fn dec_sub(a: i128, b: i128) -> Result<i128, Fault> {
    a.checked_sub(b).map_or(Err(Fault::Overflow), dec_fit)
}

pub fn dec_mul(a: i128, b: i128) -> Result<i128, Fault> {
    a.checked_mul(b).map_or(Err(Fault::Overflow), dec_fit)
}

pub fn dec_text(scale: u32, c: i128) -> String {
    let scale = scale as usize;
    let ds: Vec<char> = c.unsigned_abs().to_string().chars().collect();
    let ds: Vec<char> = iter::repeat_n('0', (scale + 1).saturating_sub(ds.len()))
        .chain(ds)
        .collect();
    let (whole, frac) = ds.split_at(ds.len() - scale);
    let mut s = String::new();
    if c < 0 {
        s.push('-');
    }
    s.extend(whole);
    if scale != 0 {
        s.push('.');
        s.extend(frac);
    }
    s
}

fn dec_whole_ok(ds: &[char]) -> bool {
    match ds {
        ['0'] => true,
        [d, ..] => *d != '0' && ds.iter().all(char::is_ascii_digit),
        [] => false,
    }
}

fn dec_frac_ok(ds: &[char]) -> bool {
    match ds {
        [] => true,
        ['.', rest @ ..] => !rest.is_empty() && rest.iter().all(char::is_ascii_digit),
        _ => false,
    }
}

fn dec_digits_value(ds: &[char]) -> Option<i128> {
    ds.iter().try_fold(0i128, |n, &d| {
        n.checked_mul(10)?
            .checked_add(i128::from(u32::from(d).saturating_sub(u32::from('0'))))
    })
}

pub fn dec_parse(s: &str) -> Option<(u32, i128)> {
    let cs: Vec<char> = s.chars().collect();
    if 40 < cs.len() {
        None
    } else {
        let neg = cs.first() == Some(&'-');
        let body = if neg { &cs[1..] } else { &cs[..] };
        let (whole, rest) =
            body.split_at(body.iter().position(|&d| d == '.').unwrap_or(body.len()));
        let frac = rest.get(1..).unwrap_or_default();
        if dec_whole_ok(whole) && dec_frac_ok(rest) && frac.len() <= 37 {
            let mag = dec_digits_value(&[whole, frac].concat())?;
            let c = if neg { -mag } else { mag };
            let scale = frac.len() as u32;
            (dec_in(c) && dec_text(scale, c) == s).then_some((scale, c))
        } else {
            None
        }
    }
}

fn dec_bump(m: Mode, neg: bool, q: &Nat, r: &Nat, den: &Nat) -> Result<bool, Fault> {
    if r.is_zero() {
        Ok(false)
    } else {
        match m {
            Mode::Up => Ok(true),
            Mode::Down => Ok(false),
            Mode::Ceiling => Ok(!neg),
            Mode::Floor => Ok(neg),
            Mode::HalfUp => Ok(*den <= r * 2),
            Mode::HalfDown => Ok(*den < r * 2),
            Mode::HalfEven => Ok(*den < r * 2 || (*den == r * 2 && q % 2 == 1)),
            Mode::Exact => Err(Fault::Inexact),
        }
    }
}

pub fn round_mode(m: Mode, num: &Int, den: &Nat) -> Result<Int, Fault> {
    let a = num.nat_abs();
    let q = &a / den;
    let bump = dec_bump(m, *num < 0, &q, &(&a % den), den)?;
    let mag = Int::from(if bump { q + 1 } else { q });
    Ok(if *num < 0 { -mag } else { mag })
}

pub fn dec_rescale(m: Mode, num: &Int, den: &Nat, src: u32, dst: u32) -> Result<Int, Fault> {
    let ten = Nat::from_u64(10);
    round_mode(
        m,
        &(num * Int::from(ten.pow(u64::from(dst.saturating_sub(src))))),
        &(den * ten.pow(u64::from(src.saturating_sub(dst)))),
    )
}

pub fn dec_scale_of(t: &Ty) -> u32 {
    match t {
        Ty::Decimal(s) => *s,
        _ => 0,
    }
}

pub fn dec_fit_to(t: &Ty, c: &Int) -> Result<i128, Fault> {
    match t {
        Ty::Decimal(_) => c.to_i128().map_or(Err(Fault::Overflow), dec_fit),
        _ => c.to_i64().map(i128::from).ok_or(Fault::Overflow),
    }
}

pub fn dec_round(t: &Ty, m: Mode, scale: u32, c: i128) -> Result<i128, Fault> {
    dec_fit_to(
        t,
        &dec_rescale(m, &Int::from(c), &Nat::from_u64(1), scale, dec_scale_of(t))?,
    )
}

pub fn dec_div(t: &Ty, m: Mode, sa: u32, a: i128, sb: u32, b: i128) -> Result<i128, Fault> {
    if b == 0 {
        Err(Fault::DivZero)
    } else {
        let a = Int::from(a);
        dec_fit_to(
            t,
            &dec_rescale(
                m,
                &(if b < 0 { -a } else { a }),
                &Nat::from_u128(b.unsigned_abs()),
                sa,
                sb + dec_scale_of(t),
            )?,
        )
    }
}
