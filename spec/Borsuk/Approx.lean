namespace Borsuk

structure Bounds where
  lo : Dyadic
  hi : Dyadic

def guardBits : Nat := 32

private def topBit : Dyadic → Int
  | .zero => 0
  | .ofOdd n k _ => (n.natAbs.log2 : Int) - k

private def least (a b : Dyadic) : Dyadic := if a ≤ b then a else b

private def greatest (a b : Dyadic) : Dyadic := if a ≤ b then b else a

private def roundDownBits (p : Nat) (x : Dyadic) : Dyadic :=
  x.roundDown ((p : Int) - 1 - topBit x)

private def roundUpBits (p : Nat) (x : Dyadic) : Dyadic :=
  x.roundUp ((p : Int) - 1 - topBit x)

private def addNear (p : Nat) (a b : Dyadic) : Dyadic :=
  if topBit b + p + 2 < topBit a then
    if b < 0 then a - ((1 : Dyadic) <<< (topBit a - p - 2)) else a
  else a + b

private def addDown (p : Nat) (a b : Dyadic) : Dyadic :=
  roundDownBits p
    (if a == 0 then b
    else if b == 0 then a
    else if topBit b ≤ topBit a then addNear p a b
    else addNear p b a)

private def addUp (p : Nat) (a b : Dyadic) : Dyadic := -(addDown p (-a) (-b))

private def divDown (p : Nat) (a b : Dyadic) : Dyadic :=
  a.divAtPrec b ((p : Int) + topBit b - topBit a)

private def divUp (p : Nat) (a b : Dyadic) : Dyadic := -(divDown p (-a) b)

private def sqrtShift (p : Nat) (n k : Int) : Nat :=
  let s := 2 * p + 2 - (n.natAbs.log2 + 1)
  if (k + s) % 2 == 0 then s else s + 1

private def sqrtDown (p : Nat) : Dyadic → Dyadic
  | .zero => 0
  | .ofOdd n k _ =>
    if n < 0 then 0
    else
      let s := sqrtShift p n k
      roundDownBits p (Dyadic.ofIntWithPrec (n.toNat <<< s).sqrt ((k + s) / 2))

private def sqrtUp (p : Nat) : Dyadic → Dyadic
  | .zero => 0
  | .ofOdd n k _ =>
    if n < 0 then 0
    else
      let s := sqrtShift p n k
      let m := n.toNat <<< s
      let r := m.sqrt
      roundUpBits p (Dyadic.ofIntWithPrec (if r * r == m then r else r + 1) ((k + s) / 2))

def floorInt : Dyadic → Int
  | .zero => 0
  | .ofOdd n k _ => if k ≤ 0 then n <<< k.natAbs else n >>> k.natAbs

namespace Bounds

def exact (x : Dyadic) : Bounds := ⟨x, x⟩

def neg (a : Bounds) : Bounds := ⟨-a.hi, -a.lo⟩

def scale (k : Int) (a : Bounds) : Bounds := ⟨a.lo <<< k, a.hi <<< k⟩

def lt (a b : Bounds) : Bool := decide (a.hi < b.lo)

private def mag (a : Bounds) : Dyadic := greatest (-a.lo) a.hi

def add (w : Nat) (a b : Bounds) : Bounds :=
  ⟨addDown (w + guardBits) a.lo b.lo, addUp (w + guardBits) a.hi b.hi⟩

def sub (w : Nat) (a b : Bounds) : Bounds := add w a b.neg

def mul (w : Nat) (a b : Bounds) : Bounds :=
  let p1 := a.lo * b.lo
  let p2 := a.lo * b.hi
  let p3 := a.hi * b.lo
  let p4 := a.hi * b.hi
  ⟨roundDownBits (w + guardBits) (least (least p1 p2) (least p3 p4)),
    roundUpBits (w + guardBits) (greatest (greatest p1 p2) (greatest p3 p4))⟩

private def divPos (w : Nat) (a b : Bounds) : Bounds :=
  ⟨divDown (w + guardBits) a.lo (if 0 ≤ a.lo then b.hi else b.lo),
    divUp (w + guardBits) a.hi (if 0 ≤ a.hi then b.lo else b.hi)⟩

def div (w : Nat) (a b : Bounds) : Option Bounds :=
  if 0 < b.lo then some (divPos w a b)
  else if b.hi < 0 then some (divPos w a b.neg).neg
  else none

def sqrt (w : Nat) (a : Bounds) : Bounds :=
  ⟨sqrtDown (w + guardBits) a.lo, sqrtUp (w + guardBits) a.hi⟩

end Bounds

private def factGo (t : Nat) : Nat → Nat → Nat → Nat
  | 0, n, _ => n
  | fuel + 1, n, acc => if t ≤ acc then n else factGo t fuel (n + 1) (acc + (n + 1).log2)

private def factTerms (w : Nat) : Nat :=
  factGo (w + guardBits + 3) (w + guardBits + 5) 1 0

private def halvings (w : Nat) : Nat := w.sqrt / 4 + 1

private def sumTerms (w : Nat) (next : Nat → Bounds → Bounds) :
    Nat → Nat → Bounds → Bounds → Bounds
  | 0, _, s, t =>
    let r := t.mag <<< (1 : Int)
    Bounds.add w s ⟨-r, r⟩
  | n + 1, k, s, t => sumTerms w next n (k + 1) (Bounds.add w s t) (next k t)

private def taylor (w : Nat) (x : Bounds) (n : Nat) (first : Bounds)
    (next : Nat → Bounds → Bounds) : Option Bounds :=
  if x.mag ≤ 1 then some (sumTerms w next n 0 (Bounds.exact 0) first) else none

private def term (w : Nat) (t y : Bounds) (d : Nat) : Bounds :=
  Bounds.divPos w (Bounds.mul w t y) (Bounds.exact (d : Dyadic))

def expSeries (w : Nat) (x : Bounds) : Option Bounds :=
  taylor w x (factTerms w) (Bounds.exact 1) fun k t => term w t x (k + 1)

def sinhSeries (w : Nat) (x : Bounds) : Option Bounds :=
  let x2 := Bounds.mul w x x
  taylor w x (factTerms w / 2 + 1) x fun k t => term w t x2 ((2 * k + 2) * (2 * k + 3))

def sinSeries (w : Nat) (x : Bounds) : Option Bounds :=
  let x2 := Bounds.mul w x x
  taylor w x (factTerms w / 2 + 1) x fun k t => (term w t x2 ((2 * k + 2) * (2 * k + 3))).neg

def cosSeries (w : Nat) (x : Bounds) : Option Bounds :=
  let x2 := Bounds.mul w x x
  taylor w x (factTerms w / 2 + 1) (Bounds.exact 1) fun k t =>
    (term w t x2 ((2 * k + 1) * (2 * k + 2))).neg

private def halve (w : Nat) (c : Bounds) : Nat → Bounds → Bounds
  | 0, x => x
  | n + 1, x =>
    let r := Bounds.sqrt w (Bounds.add w (Bounds.exact 1) (Bounds.mul w c (Bounds.mul w x x)))
    halve w c n (Bounds.divPos w x (Bounds.add w (Bounds.exact 1) r))

private def half : Dyadic := Dyadic.ofIntWithPrec 1 1

private def arcSeries (w : Nat) (c : Bounds) (x : Bounds) : Option Bounds :=
  let h := halvings w
  let y := halve w c h x
  let y2 := Bounds.mul w c.neg (Bounds.mul w y y)
  let next := fun k t =>
    term w (Bounds.mul w t y2) (Bounds.exact ((2 * k + 1 : Nat) : Dyadic)) (2 * k + 3)
  if y.mag ≤ half then
    some (Bounds.scale h (sumTerms w next ((w + guardBits + 3) / (2 * h) + 1) 0 (Bounds.exact 0) y))
  else none

def atanSeries (w : Nat) (x : Bounds) : Option Bounds :=
  arcSeries w (Bounds.exact 1) x

def atanhSeries (w : Nat) (x : Bounds) : Option Bounds :=
  if x.mag ≤ half then arcSeries w (Bounds.exact (-1)) x else none

def piBounds (w : Nat) : Option Bounds :=
  (atanSeries w (Bounds.exact 1)).map (Bounds.scale 2)

def ln2Bounds (w : Nat) : Option Bounds :=
  (atanhSeries w (Bounds.divPos w (Bounds.exact 1) (Bounds.exact 3))).map (Bounds.scale 1)

def ln10Bounds (w : Nat) : Option Bounds := do
  let l ← ln2Bounds w
  let a ← atanhSeries w (Bounds.divPos w (Bounds.exact 1) (Bounds.exact 9))
  some (Bounds.add w (Bounds.mul w (Bounds.exact 3) l) (Bounds.scale 1 a))

end Borsuk
