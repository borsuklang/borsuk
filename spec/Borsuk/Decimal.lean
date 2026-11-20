import Borsuk.Ir

namespace Borsuk

def decMax : Int := 10 ^ 38 - 1

def decIn (c : Int) : Bool :=
  -decMax ≤ c && c ≤ decMax

def decFit (c : Int) : Except Fault Int :=
  if decIn c then .ok c else .error .overflow

def decAdd (a b : Int) : Except Fault Int :=
  decFit (a + b)

def decSub (a b : Int) : Except Fault Int :=
  decFit (a - b)

def decMul (a b : Int) : Except Fault Int :=
  decFit (a * b)

def decText (scale : Nat) (c : Int) : String :=
  let ds := (toString c.natAbs).toList
  let ds := List.replicate (scale + 1 - ds.length) '0' ++ ds
  let whole := ds.take (ds.length - scale)
  let frac := ds.drop (ds.length - scale)
  String.ofList ((if c < 0 then ['-'] else []) ++ whole ++ (if scale == 0 then [] else '.' :: frac))

def decWholeOk : List Char → Bool
  | ['0'] => true
  | d :: ds => d != '0' && (d :: ds).all Char.isDigit
  | [] => false

def decFracOk : List Char → Bool
  | [] => true
  | '.' :: ds => !ds.isEmpty && ds.all Char.isDigit
  | _ => false

def decDigitsValue (ds : List Char) : Nat :=
  ds.foldl (fun n d => n * 10 + (d.toNat - '0'.toNat)) 0

def decParse (s : String) : Option (Nat × Int) :=
  if 40 < s.length then none
  else
    let cs := s.toList
    let neg := cs.head? == some '-'
    let (whole, rest) := (if neg then cs.drop 1 else cs).span (· != '.')
    let frac := rest.drop 1
    if decWholeOk whole && decFracOk rest && frac.length ≤ 37 then
      let mag : Int := decDigitsValue (whole ++ frac)
      let c := if neg then -mag else mag
      if decIn c && decText frac.length c == s then some (frac.length, c) else none
    else none

def decBump (m : Mode) (neg : Bool) (q r den : Nat) : Except Fault Bool :=
  if r == 0 then .ok false
  else
    match m with
    | .up => .ok true
    | .down => .ok false
    | .ceiling => .ok !neg
    | .floor => .ok neg
    | .halfUp => .ok (den ≤ 2 * r)
    | .halfDown => .ok (den < 2 * r)
    | .halfEven => .ok (den < 2 * r || (den == 2 * r && q % 2 == 1))
    | .exact => .error .inexact

def roundMode (m : Mode) (num : Int) (den : Nat) : Except Fault Int := do
  let a := num.natAbs
  let q := a / den
  let bump ← decBump m (num < 0) q (a % den) den
  let mag : Int := if bump then q + 1 else q
  pure (if num < 0 then -mag else mag)

def decRescale (m : Mode) (num : Int) (den src dst : Nat) : Except Fault Int :=
  roundMode m (num * 10 ^ (dst - src)) (den * 10 ^ (src - dst))

def decScaleOf : Ty → Nat
  | .decimal s => s
  | _ => 0

def decFitTo (t : Ty) (c : Int) : Except Fault Int :=
  match t with
  | .decimal _ => decFit c
  | _ => if inRange c then .ok c else .error .overflow

def decRound (t : Ty) (m : Mode) (scale : Nat) (c : Int) : Except Fault Int := do
  decFitTo t (← decRescale m c 1 scale (decScaleOf t))

def decDiv (t : Ty) (m : Mode) (sa : Nat) (a : Int) (sb : Nat) (b : Int) : Except Fault Int :=
  if b == 0 then .error .divZero
  else do
    decFitTo t (← decRescale m (if b < 0 then -a else a) b.natAbs sa (sb + decScaleOf t))

end Borsuk
