namespace Borsuk

inductive Fmt where
  | b64
  | b32
  deriving BEq

def Fmt.prec : Fmt → Nat
  | .b64 => 53
  | .b32 => 24

def Fmt.emax : Fmt → Nat
  | .b64 => 1023
  | .b32 => 127

def Fmt.width : Fmt → Nat
  | .b64 => 64
  | .b32 => 32

def Fmt.nan : Fmt → Nat
  | .b64 => 0x7FF8000000000000
  | .b32 => 0x7FC00000

def qmin (f : Fmt) : Int :=
  2 - (f.emax : Int) - (f.prec : Int)

def signBit (f : Fmt) (neg : Bool) : Nat :=
  if neg then 2 ^ (f.width - 1) else 0

def infBits (f : Fmt) (neg : Bool) : Nat :=
  signBit f neg + (2 ^ (f.width - f.prec) - 1) * 2 ^ (f.prec - 1)

private def ratOf (base m : Nat) (e : Int) : Nat × Nat :=
  if 0 ≤ e then (m * base ^ e.toNat, 1) else (m, base ^ (-e).toNat)

private def pack (f : Fmt) (neg : Bool) (m : Nat) (q : Int) : Nat :=
  let b := (q - qmin f).toNat * 2 ^ (f.prec - 1) + m
  if b < infBits f false then signBit f neg + b else infBits f neg

def roundRat (f : Fmt) (neg : Bool) (num den : Nat) : Nat :=
  if num == 0 then signBit f neg
  else
    let t : Int := (Nat.log2 num : Int) - (Nat.log2 den : Int)
    let (a, b) := ratOf 2 1 t
    let e := if den * a ≤ num * b then t else t - 1
    let q := max (e - ((f.prec : Int) - 1)) (qmin f)
    let (a, b) := ratOf 2 1 q
    let n := num * b
    let d := den * a
    let m := n / d
    let r := n % d
    let up := d < 2 * r || (2 * r == d && m % 2 == 1)
    pack f neg (if up then m + 1 else m) q

inductive Unpacked where
  | nan
  | inf (neg : Bool)
  | fin (neg : Bool) (m : Nat) (e : Int)

def unpack (f : Fmt) (x : Nat) : Unpacked :=
  let w := f.prec - 1
  let top := 2 ^ (f.width - f.prec) - 1
  let neg := x / 2 ^ (f.width - 1) % 2 == 1
  let be := x / 2 ^ w % (top + 1)
  let fr := x % 2 ^ w
  if be == top then (if fr == 0 then .inf neg else .nan)
  else if be == 0 then .fin neg fr (qmin f)
  else .fin neg (fr + 2 ^ w) (qmin f + (be : Int) - 1)

private def Unpacked.negate : Unpacked → Unpacked
  | .nan => .nan
  | .inf s => .inf (!s)
  | .fin s m e => .fin (!s) m e

private def roundDy (f : Fmt) (neg : Bool) (m : Nat) (e : Int) : Nat :=
  let (a, b) := ratOf 2 m e
  roundRat f neg a b

private def addFin (f : Fmt) (s : Bool) (m : Nat) (e : Int) (t : Bool) (n : Nat) (d : Int) : Nat :=
  let c := min e d
  let a : Int := (m * 2 ^ (e - c).toNat : Nat)
  let b : Int := (n * 2 ^ (d - c).toNat : Nat)
  let v := (if s then -a else a) + (if t then -b else b)
  if v == 0 then signBit f (s && t) else roundDy f (decide (v < 0)) v.natAbs c

private def addUnpacked (f : Fmt) : Unpacked → Unpacked → Nat
  | .nan, _ => f.nan
  | _, .nan => f.nan
  | .inf s, .inf t => if s == t then infBits f s else f.nan
  | .inf s, _ => infBits f s
  | _, .inf t => infBits f t
  | .fin s m e, .fin t n d => addFin f s m e t n d

def floatAdd (f : Fmt) (x y : Nat) : Nat :=
  addUnpacked f (unpack f x) (unpack f y)

def floatSub (f : Fmt) (x y : Nat) : Nat :=
  addUnpacked f (unpack f x) (unpack f y).negate

def floatMul (f : Fmt) (x y : Nat) : Nat :=
  match unpack f x, unpack f y with
  | .nan, _ => f.nan
  | _, .nan => f.nan
  | .inf s, .inf t => infBits f (s != t)
  | .inf s, .fin t m _ => if m == 0 then f.nan else infBits f (s != t)
  | .fin s m _, .inf t => if m == 0 then f.nan else infBits f (s != t)
  | .fin s m e, .fin t n d => roundDy f (s != t) (m * n) (e + d)

def floatDiv (f : Fmt) (x y : Nat) : Nat :=
  match unpack f x, unpack f y with
  | .nan, _ => f.nan
  | _, .nan => f.nan
  | .inf _, .inf _ => f.nan
  | .inf s, .fin t _ _ => infBits f (s != t)
  | .fin s _ _, .inf t => signBit f (s != t)
  | .fin s m e, .fin t n d =>
    if n == 0 then (if m == 0 then f.nan else infBits f (s != t))
    else
      let (a, b) := ratOf 2 m (e - d)
      roundRat f (s != t) a (b * n)

def floatSqrt (f : Fmt) (x : Nat) : Nat :=
  match unpack f x with
  | .nan => f.nan
  | .inf s => if s then f.nan else infBits f false
  | .fin s m e =>
    if m == 0 then signBit f s
    else if s then f.nan
    else
      let q := ((Nat.log2 m : Int) + e) / 2 - ((f.prec : Int) - 1)
      let n := m * 2 ^ (e - 2 * q).toNat
      let r := Nat.sqrt n
      pack f false (if r < n - r * r then r + 1 else r) q

private def addInf (f : Fmt) (s : Bool) : Unpacked → Nat
  | .inf t => if s == t then infBits f s else f.nan
  | _ => infBits f s

def floatFma (f : Fmt) (x y z : Nat) : Nat :=
  match unpack f x, unpack f y, unpack f z with
  | .nan, _, _ => f.nan
  | _, .nan, _ => f.nan
  | _, _, .nan => f.nan
  | .inf s, .inf t, w => addInf f (s != t) w
  | .inf s, .fin t m _, w => if m == 0 then f.nan else addInf f (s != t) w
  | .fin s m _, .inf t, w => if m == 0 then f.nan else addInf f (s != t) w
  | .fin _ _ _, .fin _ _ _, .inf u => infBits f u
  | .fin s m e, .fin t n d, .fin u k c => addFin f (s != t) (m * n) (e + d) u k c

private def orderKey (f : Fmt) (x : Nat) : Nat :=
  let h := 2 ^ (f.width - 1)
  if x / h % 2 == 1 then h - 1 - x % h else h + x % h

def floatLt (f : Fmt) (a b : Nat) : Bool :=
  decide (orderKey f a < orderKey f b)

private def digitsText (s : Nat) (n : Int) : String :=
  let ds := (toString s).toList
  let k : Int := ds.length
  let zeros (c : Int) : List Char := List.replicate c.toNat '0'
  let e := n - 1
  String.ofList <|
    if k ≤ n ∧ n ≤ 21 then ds ++ zeros (n - k)
    else if 0 < n ∧ n < k then ds.take n.toNat ++ '.' :: ds.drop n.toNat
    else if -6 < n ∧ n ≤ 0 then '0' :: '.' :: zeros (-n) ++ ds
    else
      ds.take 1 ++ (if 1 < k then '.' :: ds.drop 1 else []) ++
        'e' :: (if e < 0 then '-' else '+') :: (toString e.natAbs).toList

private def pow10Le (m : Nat) (e t : Int) : Bool :=
  let (a, b) := ratOf 2 m e
  let (c, d) := ratOf 10 1 t
  decide (c * b ≤ a * d)

private def decExp (m : Nat) (e : Int) : Int :=
  let t := ((Nat.log2 m : Int) + e) * 1292913986 / 2 ^ 32 + 1
  if pow10Le m e t then t + 1 else if pow10Le m e (t - 1) then t else t - 1

private def closest (lo hi y2 : Nat) (exact : Bool) (n0 : Int) (k : Nat) : Nat × Int :=
  let pw := 10 ^ (17 - k)
  let sl := y2 / 2 / pw
  let c := (2 * sl + 1) * pw
  let inL := lo ≤ sl * pw
  let inH := (sl + 1) * pw ≤ hi
  let low := if inL ∧ inH then y2 < c ∨ (y2 = c ∧ exact ∧ sl % 2 = 0) else inL
  if low then (sl, n0)
  else if sl + 1 == 10 ^ k then (10 ^ (k - 1), n0 + 1)
  else (sl + 1, n0)

private def shortest (lo hi y2 : Nat) (exact : Bool) (n0 : Int) : Nat → Nat → Nat × Int
  | k, 0 => closest lo hi y2 exact n0 k
  | k, fuel + 1 =>
    if lo ≤ hi / 10 ^ (17 - k) * 10 ^ (17 - k) then closest lo hi y2 exact n0 k
    else shortest lo hi y2 exact n0 (k + 1) fuel

private def posText (f : Fmt) (m : Nat) (e : Int) : String :=
  let n0 := decExp m e
  let (a, b) := ratOf 2 1 (e - 2)
  let (c, h) := ratOf 10 1 (17 - n0)
  let p := a * c
  let den := b * h
  let g := if m == 2 ^ (f.prec - 1) && decide (qmin f < e) then 1 else 2
  let ln := (4 * m - g) * p
  let hn := (4 * m + 2) * p
  let incl := m % 2 == 0
  let lo := if incl then (ln + den - 1) / den else ln / den + 1
  let hi := if incl then hn / den else (hn - 1) / den
  let xn := 8 * m * p
  let (s, n) := shortest lo hi (xn / den) (xn % den == 0) n0 1 16
  digitsText s n

def floatText (f : Fmt) (x : Nat) : String :=
  match unpack f x with
  | .nan => "nan"
  | .inf s => if s then "-inf" else "inf"
  | .fin s m e => (if s then "-" else "") ++ (if m == 0 then "0" else posText f m e)

private def natOf (cs : List Char) : Nat :=
  cs.foldl (fun a c => 10 * a + (c.toNat - 48)) 0

private def plainDigits (cs : List Char) : Bool :=
  cs.all Char.isDigit && (cs == ['0'] || (!cs.isEmpty && cs.head? != some '0'))

private def fracPart : List Char → Option (List Char × List Char)
  | '.' :: r =>
    let (d, t) := r.span Char.isDigit
    if d.isEmpty then none else some (d, t)
  | r => some ([], r)

private def expPart : List Char → Option Int
  | [] => some 0
  | 'e' :: '+' :: r => if r.length ≤ 3 && plainDigits r then some (natOf r : Int) else none
  | 'e' :: '-' :: r => if r.length ≤ 3 && plainDigits r then some (-(natOf r : Int)) else none
  | _ => none

private def atomParts (cs : List Char) : Option (Bool × Nat × Int) := do
  let neg := cs.head? == some '-'
  let (ip, rest) := (if neg then cs.drop 1 else cs).span Char.isDigit
  if !plainDigits ip then none
  let (fp, rest) ← fracPart rest
  let x ← expPart rest
  pure (neg, natOf (ip ++ fp), x - (fp.length : Int))

def floatParse (f : Fmt) (s : String) : Option Nat :=
  if s == "nan" then some f.nan
  else if s == "inf" then some (infBits f false)
  else if s == "-inf" then some (infBits f true)
  else if 25 < s.length then none
  else do
    let (neg, n, x) ← atomParts s.toList
    let (a, b) := ratOf 10 n x
    let r := roundRat f neg a b
    if floatText f r == s then some r else none

end Borsuk
