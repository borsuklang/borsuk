use std::mem::forget;

use crate::codec::{decode, encode};
use crate::eval::Value;
use crate::ir::{Program, Ty};

const DEC_MAX: i128 = 10i128.pow(38) - 1;

fn round_trip(p: &Program, t: &Ty, v: Value) -> Option<Value> {
    let d = encode(p, t, &v).and_then(|b| decode(p, t, &b));
    forget(v);
    d
}

fn bytes<const N: usize>() -> Vec<u8> {
    let all: [u8; N] = kani::any();
    let len: usize = kani::any();
    kani::assume(len <= N);
    all[..len].to_vec()
}

fn canonical(p: &Program, t: &Ty, b: &[u8]) -> bool {
    match decode(p, t, b) {
        Some(v) => {
            assert!(encode(p, t, &v).as_deref() == Some(b));
            forget(v);
            true
        }
        None => false,
    }
}

fn int_is(v: &Value, n: i64) -> bool {
    matches!(v, Value::Int(m) if *m == n)
}

#[kani::proof]
#[kani::unwind(0)]
fn codec_round_trip_scalars() {
    let p = Program { items: Vec::new() };
    let n: i64 = kani::any();
    let d = round_trip(&p, &Ty::Int, Value::Int(n));
    let int = matches!(&d, Some(v) if int_is(v, n));
    assert!(int);
    kani::cover!(int);
    forget(d);
    let b: bool = kani::any();
    let d = round_trip(&p, &Ty::Bool, Value::Bool(b));
    let boolean = matches!(&d, Some(Value::Bool(c)) if *c == b);
    assert!(boolean);
    kani::cover!(boolean);
    forget(d);
    let t: i64 = kani::any();
    let d = round_trip(&p, &Ty::Time, Value::Time(t));
    let time = matches!(&d, Some(Value::Time(u)) if *u == t);
    assert!(time);
    kani::cover!(time);
    forget(d);
    let s: i64 = kani::any();
    let d = round_trip(&p, &Ty::Duration, Value::Dur(s));
    let duration = matches!(&d, Some(Value::Dur(u)) if *u == s);
    assert!(duration);
    kani::cover!(duration);
    forget(d);
    let x: u64 = kani::any();
    let f64_value = x & !(1 << 63) <= 0x7FF0_0000_0000_0000 || x == 0x7FF8_0000_0000_0000;
    let e = encode(&p, &Ty::F64, &Value::F64(x));
    assert!(e.is_some() == f64_value);
    let d = e.and_then(|b| decode(&p, &Ty::F64, &b));
    let wide = matches!(&d, Some(Value::F64(y)) if *y == x);
    assert!(wide == f64_value);
    kani::cover!(f64_value && wide);
    forget(d);
    let x: u32 = kani::any();
    let f32_value = x & !(1 << 31) <= 0x7F80_0000 || x == 0x7FC0_0000;
    let e = encode(&p, &Ty::F32, &Value::F32(x));
    assert!(e.is_some() == f32_value);
    let d = e.and_then(|b| decode(&p, &Ty::F32, &b));
    let narrow = matches!(&d, Some(Value::F32(y)) if *y == x);
    assert!(narrow == f32_value);
    kani::cover!(f32_value && narrow);
    forget(d);
    let c: i128 = kani::any();
    let dec_value = (-DEC_MAX..=DEC_MAX).contains(&c);
    let e = encode(&p, &Ty::Decimal(2), &Value::Dec(2, c));
    assert!(e.is_some() == dec_value);
    let d = e.and_then(|b| decode(&p, &Ty::Decimal(2), &b));
    let money = matches!(&d, Some(Value::Dec(2, y)) if *y == c);
    assert!(money == dec_value);
    kani::cover!(dec_value && money);
    forget(d);
}

#[kani::proof]
#[kani::unwind(19)]
fn codec_canonical() {
    let p = Program { items: Vec::new() };
    let int = canonical(&p, &Ty::Int, &bytes::<20>());
    kani::cover!(int);
    let boolean = canonical(&p, &Ty::Bool, &bytes::<20>());
    kani::cover!(boolean);
    let wide = canonical(&p, &Ty::F64, &bytes::<20>());
    kani::cover!(wide);
    let narrow = canonical(&p, &Ty::F32, &bytes::<20>());
    kani::cover!(narrow);
    let money = canonical(&p, &Ty::Decimal(2), &bytes::<20>());
    kani::cover!(money);
    let time = canonical(&p, &Ty::Time, &bytes::<20>());
    kani::cover!(time);
    let duration = canonical(&p, &Ty::Duration, &bytes::<20>());
    kani::cover!(duration);
}
