use std::hint::black_box;

use crate::arm_f::ArmF;
use crate::types::{Arm, Corpus, Group, Input, InputKind, KINDS, Log, N, Refused, State};

const WORD: usize = 8;
const ZERO: [u8; WORD] = [0; WORD];
const EMPTY: u8 = 0x00;
const FULL: u8 = 0xFF;
const RUN: usize = 255;
const DENSE: usize = WORD - 1;
const HEAD: usize = 2;
const LENGTH: usize = 4;
const PARTS: usize = 4;

pub struct ArmP {
    f: ArmF,
    out: Vec<u8>,
}

fn word(b: &[u8], k: usize) -> [u8; WORD] {
    let at = k * WORD;
    let mut w = ZERO;
    match b.get(at..at + WORD) {
        Some(s) => w.copy_from_slice(s),
        None => w[..b.len() - at].copy_from_slice(&b[at..]),
    }
    w
}

fn dense(w: &[u8]) -> bool {
    w.iter().filter(|&&x| x != 0).count() >= DENSE
}

fn put_word(out: &mut Vec<u8>, w: [u8; WORD]) -> u8 {
    let mut s = [0; WORD + 1];
    let mut n = 1;
    for (i, x) in w.into_iter().enumerate() {
        s[0] |= u8::from(x != 0) << i;
        s[n] = x;
        n += usize::from(x != 0);
    }
    let len = out.len();
    out.extend_from_slice(&s);
    out.truncate(len + n);
    s[0]
}

fn pack(b: &[u8], out: &mut Vec<u8>) {
    out.clear();
    let words = b.len().div_ceil(WORD);
    let mut k = 0;
    while k < words {
        let tag = put_word(out, word(b, k));
        k += 1;
        if tag == EMPTY {
            let start = k;
            while k < words && k - start < RUN && word(b, k) == ZERO {
                k += 1;
            }
            out.push((k - start) as u8);
        } else if tag == FULL {
            let at = out.len();
            out.push(0);
            let start = k;
            while k < words && k - start < RUN {
                let w = word(b, k);
                if !dense(&w) {
                    break;
                }
                out.extend_from_slice(&w);
                k += 1;
            }
            out[at] = (k - start) as u8;
        }
    }
}

fn unpack(mut p: &[u8]) -> Option<Vec<u8>> {
    let mut b = Vec::new();
    while let Some((&tag, rest)) = p.split_first() {
        p = rest;
        for i in 0..WORD {
            if (tag >> i) & 1 == 0 {
                b.push(0);
            } else {
                let (&x, rest) = p.split_first()?;
                if x == 0 {
                    return None;
                }
                b.push(x);
                p = rest;
            }
        }
        if tag == EMPTY || tag == FULL {
            let (&n, rest) = p.split_first()?;
            let n = usize::from(n);
            p = rest;
            let more = if tag == EMPTY {
                b.resize(b.len() + n * WORD, 0);
                p.first() == Some(&EMPTY)
            } else {
                let raw = p.get(..n * WORD)?;
                if !raw.chunks(WORD).all(dense) {
                    return None;
                }
                b.extend_from_slice(raw);
                p = &p[n * WORD..];
                p.first().is_some_and(|&t| t.count_ones() as usize >= DENSE)
            };
            if n < RUN && more {
                return None;
            }
        }
    }
    Some(b)
}

fn end(b: &[u8]) -> Option<usize> {
    let mut at = HEAD;
    for _ in 0..PARTS {
        let mut n = [0; LENGTH];
        n.copy_from_slice(b.get(at..at + LENGTH)?);
        at += LENGTH + u32::from_le_bytes(n) as usize;
    }
    (at <= b.len()).then_some(at)
}

impl ArmP {
    fn packed(&mut self, sum: u64) -> u64 {
        pack(self.f.log(), &mut self.out);
        black_box(&self.out);
        sum
    }
}

impl Arm for ArmP {
    const NAME: &'static str = "P";

    fn new(corpus: &Corpus) -> Self {
        let f = ArmF::new(corpus);
        let longest = (0..N)
            .flat_map(|i| KINDS.map(|k| f.frame(k, i).len()))
            .max()
            .unwrap_or(0);
        ArmP {
            f,
            out: Vec::with_capacity(longest),
        }
    }

    fn reset(&mut self) {
        self.f.reset();
    }

    fn step_hold(&mut self, i: usize) -> u64 {
        let sum = self.f.step_hold(i);
        self.packed(sum)
    }

    fn step_confirm(&mut self, i: usize) -> u64 {
        let sum = self.f.step_confirm(i);
        self.packed(sum)
    }

    fn step_wide(&mut self, i: usize) -> u64 {
        let sum = self.f.step_wide(i);
        self.packed(sum)
    }

    fn step_varied(&mut self, i: usize) -> u64 {
        let sum = self.f.step_varied(i);
        self.packed(sum)
    }

    fn step_person(&mut self, i: usize) -> u64 {
        let sum = self.f.step_person(i);
        self.packed(sum)
    }

    fn frame(&self, kind: InputKind, i: usize) -> &[u8] {
        self.f.frame(kind, i)
    }

    fn log(&self) -> &[u8] {
        &self.out
    }

    fn state(&self, group: Group, i: usize) -> State {
        self.f.state(group, i)
    }

    fn admits(&mut self, kind: InputKind, frame: &[u8]) -> bool {
        self.f.admits(kind, frame)
    }

    fn encode(input: &Input) -> Option<Vec<u8>> {
        ArmF::encode(input)
    }

    fn decode(kind: InputKind, frame: &[u8]) -> Option<Input> {
        ArmF::decode(kind, frame)
    }

    fn decode_log(kind: InputKind, record: &[u8]) -> Option<Log> {
        let b = unpack(record)?;
        let (b, pad) = b.split_at(end(&b)?);
        if pad.len() >= WORD || pad.iter().any(|&x| x != 0) {
            return None;
        }
        ArmF::decode_log(kind, b)
    }

    fn refused(corpus: &Corpus) -> Vec<Refused> {
        ArmF::refused(corpus)
    }
}
