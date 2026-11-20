import Borsuk.Ir
import Borsuk.Float
import Borsuk.Approx

namespace Borsuk

private def exactRound (f : Fmt) (neg : Bool) (a : Nat) (t : Int) : Nat :=
  if a == 0 then signBit f neg
  else
    let top := (Nat.log2 a : Int) + t
    if (f.emax : Int) < top then infBits f neg
    else if top + 2 ≤ qmin f then signBit f neg
    else if 0 ≤ t then roundRat f neg (a * 2 ^ t.toNat) 1
    else roundRat f neg a (2 ^ (-t).toNat)

private def oneOf (f : Fmt) (neg : Bool) : Nat :=
  exactRound f neg 1 0

private def roundEnd (f : Fmt) (neg : Bool) : Dyadic → Nat
  | .zero => signBit f neg
  | .ofOdd n k _ => exactRound f neg n.natAbs (-k)

private def settle (f : Fmt) (b : Bounds) : Option Nat :=
  let neg := decide (b.lo < 0)
  if neg && decide (0 < b.hi) then none
  else
    let r := roundEnd f neg b.lo
    if r == roundEnd f neg b.hi then some r else none

private def search (f : Fmt) (step : Nat → Option Bounds) : Nat → Nat → Option Nat
  | _, 0 => none
  | j, n + 1 =>
    match (step (64 * 2 ^ j)).bind (settle f) with
    | some r => some r
    | none => search f step (j + 1) n

private def refine (f : Fmt) (step : Nat → Option Bounds) : Option Nat :=
  search f step 0 11

private def toDy (neg : Bool) (m : Nat) (e : Int) : Dyadic :=
  Dyadic.ofIntWithPrec (if neg then -(m : Int) else m) (-e)

private def oddParts (neg : Bool) (m : Nat) (e : Int) : Int × Int :=
  match toDy neg m e with
  | .zero => (0, 0)
  | .ofOdd n k _ => (n, k)

private def topOf (m : Nat) (e : Int) : Int :=
  (Nat.log2 m : Int) + e

private def oneHalf : Dyadic := Dyadic.ofIntWithPrec 1 1

private def oneBounds : Bounds := Bounds.exact 1

private def piConst (f : Fmt) (n k : Int) : Option Nat :=
  refine f fun w => (piBounds w).map fun p => Bounds.scale k (Bounds.mul w (Bounds.exact (n : Dyadic)) p)

private def expOf (w : Nat) (t : Bounds) : Option Bounds := do
  let p := w + 16
  let l ← ln2Bounds p
  let q ← Bounds.div p t l
  let k := floorInt (q.lo + oneHalf)
  let e ← expSeries p (Bounds.sub p t (Bounds.mul p (Bounds.exact (k : Dyadic)) l))
  pure (Bounds.scale k e)

private def lnParts (m : Nat) (e : Int) : Int × Dyadic :=
  let l := Nat.log2 m
  if 3 * 2 ^ l ≤ 2 * m then ((l : Int) + e + 1, toDy false m (-(l : Int) - 1))
  else ((l : Int) + e, toDy false m (-(l : Int)))

private def lnMant (w : Nat) (a : Dyadic) : Option Bounds := do
  let z ← Bounds.div w (Bounds.exact (a - 1)) (Bounds.exact (a + 1))
  let s ← atanhSeries w z
  pure (Bounds.scale 1 s)

private def lnOf (w : Nat) (m : Nat) (e : Int) : Option Bounds := do
  let (k, a) := lnParts m e
  let s ← lnMant w a
  let l ← ln2Bounds w
  pure (Bounds.add w (Bounds.mul w (Bounds.exact (k : Dyadic)) l) s)

private def log2Of (w : Nat) (m : Nat) (e : Int) : Option Bounds := do
  let (k, a) := lnParts m e
  let s ← lnMant w a
  let l ← ln2Bounds w
  let q ← Bounds.div w s l
  pure (Bounds.add w (Bounds.exact (k : Dyadic)) q)

private def log10Of (w : Nat) (m : Nat) (e : Int) : Option Bounds := do
  let v ← lnOf w m e
  let t ← ln10Bounds w
  Bounds.div w v t

private def reduce (w : Nat) (x : Dyadic) (top : Int) : Option (Int × Bounds) := do
  let p := w + top.toNat
  let pi ← piBounds p
  let h := Bounds.scale (-1) pi
  let q ← Bounds.div p (Bounds.exact x) h
  let k := floorInt (q.lo + oneHalf)
  pure (k % 4, Bounds.sub p (Bounds.exact x) (Bounds.mul p (Bounds.exact (k : Dyadic)) h))

private def sinOf (w : Nat) (x : Dyadic) (top : Int) : Option Bounds := do
  let (k, r) ← reduce w x top
  if k == 0 then sinSeries w r
  else if k == 1 then cosSeries w r
  else if k == 2 then (sinSeries w r).map Bounds.neg
  else (cosSeries w r).map Bounds.neg

private def cosOf (w : Nat) (x : Dyadic) (top : Int) : Option Bounds := do
  let (k, r) ← reduce w x top
  if k == 0 then cosSeries w r
  else if k == 1 then (sinSeries w r).map Bounds.neg
  else if k == 2 then (cosSeries w r).map Bounds.neg
  else sinSeries w r

private def tanOf (w : Nat) (x : Dyadic) (top : Int) : Option Bounds := do
  let (k, r) ← reduce w x top
  let s ← sinSeries w r
  let c ← cosSeries w r
  if k % 2 == 0 then Bounds.div w s c else (Bounds.div w c s).map Bounds.neg

private def asinOf (w : Nat) (x : Dyadic) : Option Bounds := do
  let d := Bounds.mul w (Bounds.sub w oneBounds (Bounds.exact x)) (Bounds.add w oneBounds (Bounds.exact x))
  let q ← Bounds.div w (Bounds.exact x) (Bounds.sqrt w d)
  atanSeries w q

private def acosOf (w : Nat) (x : Dyadic) : Option Bounds := do
  let u ← Bounds.div w (Bounds.sub w oneBounds (Bounds.exact x)) (Bounds.add w oneBounds (Bounds.exact x))
  let t ← atanSeries w (Bounds.sqrt w u)
  pure (Bounds.scale 1 t)

private def sinhOf (w : Nat) (x : Dyadic) (big : Bool) : Option Bounds :=
  if big then do
    let a ← expOf w (Bounds.exact x)
    let b ← Bounds.div w oneBounds a
    pure (Bounds.scale (-1) (Bounds.sub w a b))
  else sinhSeries w (Bounds.exact x)

private def coshOf (w : Nat) (x : Dyadic) : Option Bounds := do
  let a ← expOf w (Bounds.exact x)
  let b ← Bounds.div w oneBounds a
  pure (Bounds.scale (-1) (Bounds.add w a b))

private def tanhOf (w : Nat) (x : Dyadic) (neg big : Bool) : Option Bounds :=
  if big then do
    let a ← expOf w (Bounds.exact (if neg then x <<< (1 : Int) else -(x <<< (1 : Int))))
    let t ← Bounds.div w (Bounds.sub w oneBounds a) (Bounds.add w oneBounds a)
    pure (if neg then t.neg else t)
  else do
    let s ← sinhSeries w (Bounds.exact x)
    Bounds.div w s (Bounds.sqrt w (Bounds.add w oneBounds (Bounds.mul w s s)))

private def isBig (m : Nat) (e : Int) : Bool :=
  decide (1 ≤ toDy false m e)

private def overRange (m : Nat) (e : Int) : Bool :=
  decide (11 ≤ topOf m e)

private def expFn (f : Fmt) : Unpacked → Option Nat
  | .nan => some f.nan
  | .inf s => some (if s then signBit f false else infBits f false)
  | .fin s m e =>
    if m == 0 then some (oneOf f false)
    else if overRange m e then some (if s then signBit f false else infBits f false)
    else refine f fun w => expOf w (Bounds.exact (toDy s m e))

private def exp2Fn (f : Fmt) : Unpacked → Option Nat
  | .nan => some f.nan
  | .inf s => some (if s then signBit f false else infBits f false)
  | .fin s m e =>
    let (n, k) := oddParts s m e
    if k ≤ 0 then some (exactRound f false 1 (n <<< k.natAbs))
    else if overRange m e then some (if s then signBit f false else infBits f false)
    else
      let x := toDy s m e
      let i := floorInt (x + oneHalf)
      refine f fun w => do
        let l ← ln2Bounds w
        let v ← expSeries w (Bounds.mul w (Bounds.exact (x - (i : Dyadic))) l)
        pure (Bounds.scale i v)

private def logFn (f : Fmt) (exact : Int → Int → Option Nat)
    (step : Nat → Nat → Int → Option Bounds) : Unpacked → Option Nat
  | .nan => some f.nan
  | .inf s => some (if s then f.nan else infBits f false)
  | .fin s m e =>
    if m == 0 then some (infBits f true)
    else if s then some f.nan
    else
      let (n, k) := oddParts false m e
      if n == 1 && k == 0 then some (signBit f false)
      else match exact n k with
        | some r => some r
        | none => refine f fun w => step w m e

private def log2Exact (f : Fmt) (n k : Int) : Option Nat :=
  if n == 1 then some (exactRound f (decide (0 < k)) k.natAbs 0) else none

private def log10Exact (f : Fmt) (n k : Int) : Option Nat :=
  if k ≤ 0 && k.natAbs ≤ f.prec && n == ((5 ^ k.natAbs : Nat) : Int) then
    some (exactRound f false k.natAbs 0)
  else none

private def trigFn (f : Fmt) (zero : Bool → Nat) (step : Nat → Dyadic → Int → Option Bounds) :
    Unpacked → Option Nat
  | .nan => some f.nan
  | .inf _ => some f.nan
  | .fin s m e =>
    if m == 0 then some (zero s)
    else refine f fun w => step w (toDy s m e) (topOf m e)

private def asinFn (f : Fmt) : Unpacked → Option Nat
  | .nan => some f.nan
  | .inf _ => some f.nan
  | .fin s m e =>
    let a := toDy false m e
    if m == 0 then some (signBit f s)
    else if 1 < a then some f.nan
    else if a == 1 then piConst f (if s then -1 else 1) (-1)
    else refine f fun w => asinOf w (toDy s m e)

private def acosFn (f : Fmt) : Unpacked → Option Nat
  | .nan => some f.nan
  | .inf _ => some f.nan
  | .fin s m e =>
    let a := toDy false m e
    if 1 < a then some f.nan
    else if a == 1 then (if s then piConst f 1 0 else some (signBit f false))
    else refine f fun w => acosOf w (toDy s m e)

private def atanFn (f : Fmt) : Unpacked → Option Nat
  | .nan => some f.nan
  | .inf s => piConst f (if s then -1 else 1) (-1)
  | .fin s m e =>
    if m == 0 then some (signBit f s)
    else refine f fun w => atanSeries w (Bounds.exact (toDy s m e))

private def sinhFn (f : Fmt) : Unpacked → Option Nat
  | .nan => some f.nan
  | .inf s => some (infBits f s)
  | .fin s m e =>
    if m == 0 then some (signBit f s)
    else if overRange m e then some (infBits f s)
    else refine f fun w => sinhOf w (toDy s m e) (isBig m e)

private def coshFn (f : Fmt) : Unpacked → Option Nat
  | .nan => some f.nan
  | .inf _ => some (infBits f false)
  | .fin s m e =>
    if m == 0 then some (oneOf f false)
    else if overRange m e then some (infBits f false)
    else refine f fun w => coshOf w (toDy s m e)

private def tanhFn (f : Fmt) : Unpacked → Option Nat
  | .nan => some f.nan
  | .inf s => some (oneOf f s)
  | .fin s m e =>
    if m == 0 then some (signBit f s)
    else if overRange m e then some (oneOf f s)
    else refine f fun w => tanhOf w (toDy s m e) s (isBig m e)

private def cbrtGo (n : Nat) : Nat → Nat → Nat
  | 0, r => r
  | i + 1, r =>
    let t := r + 2 ^ i
    cbrtGo n i (if t ^ 3 ≤ n then t else r)

private def rootRound (f : Fmt) (neg : Bool) (r : Nat) (exact : Bool) (q : Int) : Nat :=
  if exact then exactRound f neg r q else exactRound f neg (2 * r + 1) (q - 1)

private def cbrtFn (f : Fmt) (x : Nat) : Unpacked → Option Nat
  | .nan => some f.nan
  | .inf _ => some x
  | .fin s m e =>
    if m == 0 then some x
    else
      let q := topOf m e / 3 - (f.prec : Int) - 1
      let n := m * 2 ^ (e - 3 * q).toNat
      let r := cbrtGo n (Nat.log2 n / 3 + 1) 0
      some (rootRound f s r (r ^ 3 == n) q)

private def hypotExact (f : Fmt) (m : Nat) (e : Int) (n : Nat) (d : Int) : Nat :=
  let c := min e d
  let s := m ^ 2 * 4 ^ (e - c).toNat + n ^ 2 * 4 ^ (d - c).toNat
  let q := min (topOf s (2 * c) / 2 - (f.prec : Int) - 1) c
  let v := s * 4 ^ (c - q).toNat
  let r := Nat.sqrt v
  rootRound f false r (r * r == v) q

private def hypotFn (f : Fmt) : Unpacked → Unpacked → Option Nat
  | .inf _, _ => some (infBits f false)
  | _, .inf _ => some (infBits f false)
  | .nan, _ => some f.nan
  | _, .nan => some f.nan
  | .fin _ m e, .fin _ n d =>
    if n == 0 then some (exactRound f false m e)
    else if m == 0 then some (exactRound f false n d)
    else some (hypotExact f m e n d)

private def atan2Of (w : Nat) (y x : Dyadic) (sy sx : Bool) : Option Bounds := do
  let q ← Bounds.div w (Bounds.exact y) (Bounds.exact x)
  let a ← atanSeries w q
  if sx then do
    let pi ← piBounds w
    pure (if sy then Bounds.sub w a pi else Bounds.add w a pi)
  else pure a

private def atan2Fn (f : Fmt) : Unpacked → Unpacked → Option Nat
  | .nan, _ => some f.nan
  | _, .nan => some f.nan
  | .fin sy my ey, .fin sx mx ex =>
    if my == 0 then (if sx then piConst f (if sy then -1 else 1) 0 else some (signBit f sy))
    else if mx == 0 then piConst f (if sy then -1 else 1) (-1)
    else refine f fun w => atan2Of w (toDy sy my ey) (toDy sx mx ex) sy sx
  | .fin sy _ _, .inf sx =>
    if sx then piConst f (if sy then -1 else 1) 0 else some (signBit f sy)
  | .inf sy, .fin _ _ _ => piConst f (if sy then -1 else 1) (-1)
  | .inf sy, .inf sx =>
    if sx then piConst f (if sy then -3 else 3) (-2) else piConst f (if sy then -1 else 1) (-2)

private def powOdd (lim r c : Nat) : Option Nat :=
  if r == 1 then some 1
  else if lim < Nat.log2 r * c + 1 then none
  else
    let v := r ^ c
    if Nat.log2 v < lim then some v else none

private def root2k (a : Nat) : Nat → Option Nat
  | 0 => some a
  | k + 1 =>
    if a == 1 then some 1
    else
      let r := Nat.sqrt a
      if r * r == a then root2k r k else none

private def powExact (f : Fmt) (neg : Bool) (a : Nat) (e : Int) (c k : Int) : Option Nat :=
  let lim := f.prec + 1
  if k ≤ 0 then
    let y := c <<< k.natAbs
    if 0 < y then (powOdd lim a y.toNat).map fun v => exactRound f neg v (e * y)
    else if a == 1 then some (exactRound f neg 1 (e * y))
    else none
  else
    let d : Int := ((2 ^ k.toNat : Nat) : Int)
    if e % d != 0 then none
    else (root2k a k.toNat).bind fun r =>
      if 0 < c then (powOdd lim r c.toNat).map fun v => exactRound f neg v (e / d * c)
      else if r == 1 then some (exactRound f neg 1 (e / d * c))
      else none

private def powSteps (f : Fmt) (neg : Bool) (m : Nat) (e : Int) (y : Dyadic) : Option Nat :=
  refine f fun w => do
    let l ← lnOf (w + 16) m e
    let r ← expOf w (Bounds.mul (w + 16) (Bounds.exact y) l)
    pure (if neg then r.neg else r)

private def powLoop (f : Fmt) (neg : Bool) (m : Nat) (e : Int) (y : Dyadic) : Option Nat :=
  match (lnOf 64 m e).map (Bounds.mul 64 (Bounds.exact y)) with
  | some t =>
    if (2048 : Dyadic) ≤ t.lo then some (infBits f neg)
    else if t.hi ≤ -2048 then some (signBit f neg)
    else powSteps f neg m e y
  | none => powSteps f neg m e y

private def oddInt : Unpacked → Bool
  | .fin s m e => m != 0 && (oddParts s m e).2 == 0
  | _ => false

private def isInt : Unpacked → Bool
  | .fin s m e => decide ((oddParts s m e).2 ≤ 0)
  | _ => false

private def below : Unpacked → Bool
  | .inf s => s
  | .fin s m _ => s && m != 0
  | .nan => false

private def powFn (f : Fmt) (x y : Unpacked) : Option Nat :=
  let one := match x with
    | .fin false m e => oddParts false m e == (1, 0)
    | _ => false
  let yZero := match y with
    | .fin _ m _ => m == 0
    | _ => false
  if one || yZero then some (oneOf f false)
  else match x, y with
  | .nan, _ => some f.nan
  | _, .nan => some f.nan
  | .inf sx, _ =>
    let odd := sx && oddInt y
    some (if below y then signBit f odd else infBits f odd)
  | .fin _ mx ex, .inf sy =>
    if mx == 0 then some (if sy then infBits f false else signBit f false)
    else
      let a := toDy false mx ex
      if a == 1 then some (oneOf f false)
      else some (if decide (a < 1) == sy then infBits f false else signBit f false)
  | .fin sx mx ex, .fin sy my ey =>
    let odd := sx && oddInt y
    if mx == 0 then some (if below y then infBits f odd else signBit f odd)
    else if sx && !isInt y then some f.nan
    else
      let (a, e) := oddParts false mx ex
      let (c, k) := oddParts sy my ey
      match powExact f odd a.toNat (-e) c k with
      | some r => some r
      | none => powLoop f odd mx ex (toDy sy my ey)

def math1 (f : Fmt) (fn : Fn1) (x : Nat) : Option Nat :=
  let a := unpack f x
  match fn with
  | .exp => expFn f a
  | .exp2 => exp2Fn f a
  | .log => logFn f (fun _ _ => none) lnOf a
  | .log2 => logFn f (log2Exact f) log2Of a
  | .log10 => logFn f (log10Exact f) log10Of a
  | .sin => trigFn f (signBit f) sinOf a
  | .cos => trigFn f (fun _ => oneOf f false) cosOf a
  | .tan => trigFn f (signBit f) tanOf a
  | .asin => asinFn f a
  | .acos => acosFn f a
  | .atan => atanFn f a
  | .sinh => sinhFn f a
  | .cosh => coshFn f a
  | .tanh => tanhFn f a
  | .cbrt => cbrtFn f x a

def math2 (f : Fmt) (fn : Fn2) (a b : Nat) : Option Nat :=
  match fn with
  | .pow => powFn f (unpack f a) (unpack f b)
  | .atan2 => atan2Fn f (unpack f a) (unpack f b)
  | .hypot => hypotFn f (unpack f a) (unpack f b)

end Borsuk
