import Borsuk.Ir
import Borsuk.Eval
import Borsuk.Runtime
import Borsuk.Check
import Borsuk.Float
import Borsuk.Decimal

namespace Borsuk

def frameLimit : Nat := 2 ^ 32

def startFuel (p : Program) : Nat :=
  (typeNames p).length + 3

def formatVersion : Nat := 1

def findInits (p : Program) (name : Name) : Option (List (Param × XExpr)) :=
  p.items.findSome? fun
    | .record r _ inits => if r == name then some inits else none
    | _ => none

def findVariant (c : Name) : List Variant → Option (Nat × Variant)
  | [] => none
  | v :: vs => if v.name == c then some (0, v) else (findVariant c vs).map fun (i, w) => (i + 1, w)

def typeNamed (p : Program) : Ty → Bool
  | .option t => typeNamed p t
  | .result a b => typeNamed p a && typeNamed p b
  | .named n => isTypeName p n
  | _ => true

def allFixed (rec : Ty → Option Bool) : List Ty → Option Bool
  | [] => some true
  | t :: ts => do
    let x ← rec t
    let y ← allFixed rec ts
    some (x && y)

def fixedTy (p : Program) (rec : Ty → Option Bool) : Ty → Option Bool
  | .unit | .bool | .int | .time | .duration | .f64 | .f32 | .decimal _ => some true
  | .text | .principal | .stepId | .ticket => some false
  | .option t => fixedTy p rec t
  | .result a b => do
    let x ← fixedTy p rec a
    let y ← fixedTy p rec b
    some (x && y)
  | .named n =>
    match findRecord p n with
    | some _ => some false
    | none =>
      match findEnum p n with
      | some vs => allFixed rec (vs.flatMap (·.fields))
      | none =>
        match findNewtype p n with
        | some t => rec t
        | none => some false

def isFixed (p : Program) : Nat → Ty → Option Bool
  | 0, _ => none
  | k + 1, t => fixedTy p (isFixed p k) t

def sumSizes (rec : Ty → Option Nat) : List Ty → Option Nat
  | [] => some 0
  | t :: ts => do
    let x ← rec t
    let y ← sumSizes rec ts
    some (x + y)

def maxSizes (rec : Ty → Option Nat) : List Variant → Option Nat
  | [] => some 0
  | v :: vs => do
    let x ← sumSizes rec v.fields
    let y ← maxSizes rec vs
    some (max x y)

def sizeTy (p : Program) (rec : Ty → Option Nat) : Ty → Option Nat
  | .unit => some 0
  | .bool => some 1
  | .int | .time | .duration | .f64 => some 8
  | .f32 => some 4
  | .decimal _ => some 16
  | .text | .principal | .stepId | .ticket => none
  | .option t => (sizeTy p rec t).map (1 + ·)
  | .result a b => do
    let x ← sizeTy p rec a
    let y ← sizeTy p rec b
    some (1 + max x y)
  | .named n =>
    match findRecord p n with
    | some _ => none
    | none =>
      match findEnum p n with
      | some vs => (maxSizes rec vs).map (1 + ·)
      | none =>
        match findNewtype p n with
        | some t => rec t
        | none => none

def tySize (p : Program) : Nat → Ty → Option Nat
  | 0, _ => none
  | k + 1, t => sizeTy p (tySize p k) t

def slotOf (p : Program) (t : Ty) : Option (Option Nat) :=
  match isFixed p (startFuel p) t with
  | some true => (tySize p (startFuel p) t).map some
  | some false => some none
  | none => none

def slotsOf (p : Program) : List Ty → Option (List (Option Nat))
  | [] => some []
  | t :: ts => do
    let k ← slotOf p t
    let ks ← slotsOf p ts
    some (k :: ks)

def slotWidth : Option Nat → Nat
  | some n => n
  | none => 4

def slotsWidth : List (Option Nat) → Nat
  | [] => 0
  | k :: ks => slotWidth k + slotsWidth ks

def leBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | n + 1, x => UInt8.ofNat (x % 256) :: leBytes n (x / 256)

def leValue : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leValue bs

def intBytes (n : Nat) (x : Int) : List UInt8 :=
  leBytes n (x % (2 : Int) ^ (8 * n)).toNat

def intOf (n : Nat) (bs : List UInt8) : Int :=
  if leValue bs < 2 ^ (8 * n - 1) then (leValue bs : Int) else (leValue bs : Int) - (2 : Int) ^ (8 * n)

def utf8 (s : String) : List UInt8 :=
  s.toUTF8.data.toList

def fromUtf8 (bs : List UInt8) : Option String :=
  String.fromUTF8? ⟨bs.toArray⟩

def floatOk (f : Fmt) (x : Nat) : Bool :=
  x % 2 ^ (f.width - 1) ≤ (2 ^ (f.width - f.prec) - 1) * 2 ^ (f.prec - 1) || x == f.nan

def takeBytes (n : Nat) (bs : List UInt8) : Option (List UInt8 × List UInt8) :=
  if n ≤ bs.length then some (bs.take n, bs.drop n) else none

def slotBytes : Nat → List (Option Nat × List UInt8) → List UInt8
  | _, [] => []
  | pos, (some _, e) :: fs => e ++ slotBytes pos fs
  | pos, (none, e) :: fs => leBytes 4 pos ++ slotBytes (pos + e.length) fs

def partBytes : List (Option Nat × List UInt8) → List UInt8
  | [] => []
  | (some _, _) :: fs => partBytes fs
  | (none, e) :: fs => e ++ partBytes fs

def compose (head : List UInt8) (fs : List (Option Nat × List UInt8)) : List UInt8 :=
  let fixedLen := head.length + slotsWidth (fs.map (·.1))
  head ++ slotBytes fixedLen fs ++ partBytes fs

def padTo (n : Nat) (bs : List UInt8) : Option (List UInt8) :=
  if n < frameLimit then some (bs ++ List.replicate (n - bs.length) 0) else none

def tagged (p : Program) (t : Ty) (tag : Nat) (ts : List Ty) (es : List (List UInt8)) :
    Option (List UInt8) :=
  if tag < 2 ^ 8 && typeNamed p t then
    match isFixed p (startFuel p) t with
    | some true => do
      let n ← tySize p (startFuel p) t
      padTo n (UInt8.ofNat tag :: es.flatten)
    | some false => do
      let ks ← slotsOf p ts
      some (compose [UInt8.ofNat tag] (ks.zip es))
    | none => none
  else none

def recordBytes (p : Program) (ts : List Ty) (es : List (List UInt8)) : Option (List UInt8) :=
  if ts.length < 2 ^ 16 then do
    let ks ← slotsOf p ts
    some (compose (leBytes 2 ts.length) (ks.zip es))
  else none

def intField (n : Int) : Option (List UInt8) :=
  if inRange n then some (intBytes 8 n) else none

def intFields : List Int → Option (List (List UInt8))
  | [] => some []
  | n :: ns => do
    let e ← intField n
    let es ← intFields ns
    some (e :: es)

def stepBytes (p : Program) (m : Name) (key : Ty) (ek : List UInt8) (ns : List Int) :
    Option (List UInt8) := do
  let es ← intFields ns
  let ks ← slotsOf p (key :: List.replicate ns.length .int)
  some (leBytes 4 (utf8 m).length ++ utf8 m ++ compose [] (ks.zip (ek :: es)))

mutual
  def encodeValue (p : Program) : Ty → Value → Option (List UInt8)
    | .unit, .unit => some []
    | .bool, .bool b => some [if b then 1 else 0]
    | .int, .int n => intField n
    | .time, .time n => intField n
    | .duration, .dur n => intField n
    | .f64, .f64 b => if floatOk .b64 b.toNat then some (leBytes 8 b.toNat) else none
    | .f32, .f32 b => if floatOk .b32 b.toNat then some (leBytes 4 b.toNat) else none
    | .decimal s, .dec s' c => if s' == s && decIn c then some (intBytes 16 c) else none
    | .text, .text s => some (utf8 s)
    | .principal, .principal n => some (utf8 n)
    | .stepId, .stepId m k l q =>
      match findMachine p m with
      | some mach => do
        let ek ← encodeValue p mach.key k
        stepBytes p m mach.key ek [l, q]
      | none => none
    | .ticket, .ticket m k l q i =>
      match findMachine p m with
      | some mach => do
        let ek ← encodeValue p mach.key k
        stepBytes p m mach.key ek [l, q, i]
      | none => none
    | .option t, .none => tagged p (.option t) 0 [] []
    | .option t, .some w => do
      let e ← encodeValue p t w
      tagged p (.option t) 1 [t] [e]
    | .result a b, .ok w => do
      let e ← encodeValue p a w
      tagged p (.result a b) 0 [a] [e]
    | .result a b, .err w => do
      let e ← encodeValue p b w
      tagged p (.result a b) 1 [b] [e]
    | .named n, .con c args =>
      match findRecord p n with
      | some fs =>
        if c == n then do
          let es ← encodeList p (fs.map (·.ty)) args
          recordBytes p (fs.map (·.ty)) es
        else none
      | none =>
        match findEnum p n with
        | some vs =>
          match findVariant c vs with
          | some (i, v) => do
            let es ← encodeList p v.fields args
            tagged p (.named n) i v.fields es
          | none => none
        | none =>
          match findNewtype p n with
          | some inner =>
            if c == n then do
              let es ← encodeList p [inner] args
              match es with
              | [e] => some e
              | _ => none
            else none
          | none => none
    | _, _ => none

  def encodeList (p : Program) : List Ty → List Value → Option (List (List UInt8))
    | [], [] => some []
    | t :: ts, v :: vs => do
      let e ← encodeValue p t v
      let es ← encodeList p ts vs
      some (e :: es)
    | _, _ => none
end

def encode (p : Program) (t : Ty) (v : Value) : Option (List UInt8) := do
  let body ← encodeValue p t v
  if 2 + body.length < frameLimit then some (leBytes 2 formatVersion ++ body) else none

inductive Slot where
  | bytes (part : List UInt8)
  | offset (pos : Nat)

def readSlots : List (Option Nat) → List UInt8 → Option (List Slot)
  | [], _ => some []
  | some n :: ks, bs => do
    let (s, rest) ← takeBytes n bs
    let xs ← readSlots ks rest
    some (.bytes s :: xs)
  | none :: ks, bs => do
    let (s, rest) ← takeBytes 4 bs
    let xs ← readSlots ks rest
    some (.offset (leValue s) :: xs)

def slotOffsets : List Slot → List Nat
  | [] => []
  | .bytes _ :: xs => slotOffsets xs
  | .offset o :: xs => o :: slotOffsets xs

def cutParts : Nat → List Nat → List UInt8 → Option (List (List UInt8))
  | _, [], rest => some [rest]
  | pos, o :: os, rest =>
    if pos ≤ o && o - pos ≤ rest.length then
      (cutParts o os (rest.drop (o - pos))).map (rest.take (o - pos) :: ·)
    else none

def partsOf (fixedLen : Nat) (bs : List UInt8) : List Nat → Option (List (List UInt8))
  | [] => if bs.length == fixedLen then some [] else none
  | o :: os => if o == fixedLen then cutParts o os (bs.drop fixedLen) else none

def placeParts : List Slot → List (List UInt8) → Option (List (List UInt8))
  | [], [] => some []
  | .bytes s :: xs, ps => (placeParts xs ps).map (s :: ·)
  | .offset _ :: xs, q :: ps => (placeParts xs ps).map (q :: ·)
  | _, _ => none

def segments (p : Program) (head : Nat) (ts : List Ty) (bs : List UInt8) :
    Option (List (List UInt8)) := do
  let ks ← slotsOf p ts
  let fixedLen := head + slotsWidth ks
  if fixedLen ≤ bs.length then do
    let xs ← readSlots ks (bs.drop head)
    let ps ← partsOf fixedLen bs (slotOffsets xs)
    placeParts xs ps
  else none

def paddedSegments (p : Program) (ts : List Ty) (bs : List UInt8) : Option (List (List UInt8)) := do
  let ks ← slotsOf p ts
  let xs ← readSlots ks bs
  if (bs.drop (slotsWidth ks)).all (· == 0) then placeParts xs [] else none

def variantSegments (p : Program) (t : Ty) (ts : List Ty) (bs : List UInt8) :
    Option (List (List UInt8)) :=
  if typeNamed p t then
    match isFixed p (startFuel p) t with
    | some true => do
      let n ← tySize p (startFuel p) t
      if bs.length == n then paddedSegments p ts (bs.drop 1) else none
    | some false => segments p 1 ts bs
    | none => none
  else none

def decodeFields (rec : Ty → List UInt8 → Option (Value × Bool)) :
    List Ty → List (List UInt8) → Option (List Value × Bool)
  | [], [] => some ([], true)
  | t :: ts, s :: ss => do
    let (v, f) ← rec t s
    let (vs, g) ← decodeFields rec ts ss
    some (v :: vs, f && g)
  | _, _ => none

def decodeInt (bs : List UInt8) : Option Int :=
  if bs.length == 8 then some (intOf 8 bs) else none

def decodeInts : List (List UInt8) → Option (List Int)
  | [] => some []
  | s :: ss => do
    let n ← decodeInt s
    let ns ← decodeInts ss
    some (n :: ns)

def decodeStep (p : Program) (rec : Ty → List UInt8 → Option (Value × Bool)) (count : Nat)
    (bs : List UInt8) : Option (Name × Value × List Int × Bool) := do
  let (len, rest) ← takeBytes 4 bs
  let (name, body) ← takeBytes (leValue len) rest
  let m ← fromUtf8 name
  let mach ← findMachine p m
  let ss ← segments p 0 (mach.key :: List.replicate count .int) body
  match ss with
  | sk :: sn => do
    let (k, f) ← rec mach.key sk
    let ns ← decodeInts sn
    some (m, k, ns, f)
  | [] => none

def initValues (p : Program) (n : Name) (missing : Nat) : Option (List Value) := do
  let inits ← findInits p n
  if missing ≤ inits.length then xvalues none ((inits.drop (inits.length - missing)).map (·.2))
  else none

def decodeRecord (p : Program) (rec : Ty → List UInt8 → Option (Value × Bool)) (n : Name)
    (fs : List Param) (bs : List UInt8) : Option (Value × Bool) := do
  let (count, _) ← takeBytes 2 bs
  let k := leValue count
  if k ≤ fs.length then do
    let ts := (fs.take k).map (·.ty)
    let ss ← segments p 2 ts bs
    let (vs, f) ← decodeFields rec ts ss
    let rest ← initValues p n (fs.length - k)
    some (.con n (vs ++ rest), f && k == fs.length)
  else none

def decodeTy (p : Program) (rec : Ty → List UInt8 → Option (Value × Bool)) :
    Ty → List UInt8 → Option (Value × Bool)
  | .unit, bs => if bs.isEmpty then some (.unit, true) else none
  | .bool, bs =>
    match bs with
    | [b] => if b == 0 then some (.bool false, true) else if b == 1 then some (.bool true, true) else none
    | _ => none
  | .int, bs => (decodeInt bs).map fun n => (.int n, true)
  | .time, bs => (decodeInt bs).map fun n => (.time n, true)
  | .duration, bs => (decodeInt bs).map fun n => (.dur n, true)
  | .f64, bs =>
    if bs.length == 8 && floatOk .b64 (leValue bs) then some (.f64 (UInt64.ofNat (leValue bs)), true)
    else none
  | .f32, bs =>
    if bs.length == 4 && floatOk .b32 (leValue bs) then some (.f32 (UInt32.ofNat (leValue bs)), true)
    else none
  | .decimal s, bs =>
    if bs.length == 16 && decIn (intOf 16 bs) then some (.dec s (intOf 16 bs), true) else none
  | .text, bs => (fromUtf8 bs).map fun s => (.text s, true)
  | .principal, bs => (fromUtf8 bs).map fun s => (.principal s, true)
  | .stepId, bs => do
    let (m, k, ns, f) ← decodeStep p rec 2 bs
    match ns with
    | [l, q] => some (.stepId m k l q, f)
    | _ => none
  | .ticket, bs => do
    let (m, k, ns, f) ← decodeStep p rec 3 bs
    match ns with
    | [l, q, i] => some (.ticket m k l q i, f)
    | _ => none
  | .option t, bs =>
    match bs with
    | tag :: _ =>
      if tag == 0 then do
        let ss ← variantSegments p (.option t) [] bs
        if ss.isEmpty then some (.none, true) else none
      else if tag == 1 then do
        let ss ← variantSegments p (.option t) [t] bs
        match ss with
        | [s] => (decodeTy p rec t s).map fun (v, f) => (.some v, f)
        | _ => none
      else none
    | [] => none
  | .result a b, bs =>
    match bs with
    | tag :: _ =>
      if tag == 0 then do
        let ss ← variantSegments p (.result a b) [a] bs
        match ss with
        | [s] => (decodeTy p rec a s).map fun (v, f) => (.ok v, f)
        | _ => none
      else if tag == 1 then do
        let ss ← variantSegments p (.result a b) [b] bs
        match ss with
        | [s] => (decodeTy p rec b s).map fun (v, f) => (.err v, f)
        | _ => none
      else none
    | [] => none
  | .named n, bs =>
    match findRecord p n with
    | some fs => decodeRecord p rec n fs bs
    | none =>
      match findEnum p n with
      | some vs =>
        match bs with
        | tag :: _ =>
          match vs[tag.toNat]? with
          | some v =>
            if (findVariant v.name vs).map (·.1) == some tag.toNat then do
              let ss ← variantSegments p (.named n) v.fields bs
              let (vals, f) ← decodeFields rec v.fields ss
              some (.con v.name vals, f)
            else none
          | none => none
        | [] => none
      | none =>
        match findNewtype p n with
        | some inner => (rec inner bs).map fun (v, f) => (.con n [v], f)
        | none => none

def decodeAt (p : Program) : Nat → Ty → List UInt8 → Option (Value × Bool)
  | 0, _, _ => none
  | k + 1, t, bs => decodeTy p (decodeAt p k) t bs

def decodeFrame (p : Program) (t : Ty) (b : List UInt8) : Option (Value × Bool) :=
  if b.length < frameLimit then
    match takeBytes 2 b with
    | some (v, body) => if leValue v == formatVersion then decodeAt p (startFuel p) t body else none
    | none => none
  else none

def decode (p : Program) (t : Ty) (b : List UInt8) : Option Value :=
  (decodeFrame p t b).map (·.1)

def full (p : Program) (t : Ty) (b : List UInt8) : Bool :=
  match decodeFrame p t b with
  | some (_, f) => f
  | none => false

mutual
  def Typed (p : Program) : Ty → Value → Prop
    | .unit, .unit => True
    | .bool, .bool _ => True
    | .int, .int n => inRange n = true
    | .time, .time n => inRange n = true
    | .duration, .dur n => inRange n = true
    | .text, .text _ => True
    | .principal, .principal _ => True
    | .f64, .f64 b => floatOk .b64 b.toNat = true
    | .f32, .f32 b => floatOk .b32 b.toNat = true
    | .decimal s, .dec s' c => s' = s ∧ decIn c = true
    | .stepId, .stepId m k l q =>
      match findMachine p m with
      | some mach => Typed p mach.key k ∧ inRange l = true ∧ inRange q = true
      | none => False
    | .ticket, .ticket m k l q i =>
      match findMachine p m with
      | some mach => Typed p mach.key k ∧ inRange l = true ∧ inRange q = true ∧ inRange i = true
      | none => False
    | .option t, .none => typeNamed p t = true
    | .option t, .some w => Typed p t w
    | .result a b, .ok w => Typed p a w ∧ typeNamed p b = true
    | .result a b, .err w => typeNamed p a = true ∧ Typed p b w
    | .named n, .con c args =>
      match findRecord p n with
      | some fs => c = n ∧ TypedList p (fs.map (·.ty)) args
      | none =>
        match findEnum p n with
        | some vs =>
          match findVariant c vs with
          | some (_, v) => TypedList p v.fields args
          | none => False
        | none =>
          match findNewtype p n with
          | some inner => c = n ∧ TypedList p [inner] args
          | none => False
    | _, _ => False

  def TypedList (p : Program) : List Ty → List Value → Prop
    | [], [] => True
    | t :: ts, v :: vs => Typed p t v ∧ TypedList p ts vs
    | _, _ => False
end

def fieldSize (p : Program) (t : Ty) (part : Nat) : Nat :=
  match slotOf p t with
  | some (some n) => n
  | _ => 4 + part

def taggedSize (p : Program) (t : Ty) (fields : Nat) : Nat :=
  match isFixed p (startFuel p) t with
  | some true => (tySize p (startFuel p) t).getD 0
  | _ => 1 + fields

mutual
  def valueSize (p : Program) : Ty → Value → Nat
    | .unit, _ => 0
    | .bool, _ => 1
    | .int, _ | .time, _ | .duration, _ | .f64, _ => 8
    | .f32, _ => 4
    | .decimal _, _ => 16
    | .text, .text s => s.utf8ByteSize
    | .principal, .principal n => n.utf8ByteSize
    | .stepId, .stepId m k _ _ =>
      match findMachine p m with
      | some mach => 4 + m.utf8ByteSize + fieldSize p mach.key (valueSize p mach.key k) + 16
      | none => 0
    | .ticket, .ticket m k _ _ _ =>
      match findMachine p m with
      | some mach => 4 + m.utf8ByteSize + fieldSize p mach.key (valueSize p mach.key k) + 24
      | none => 0
    | .option t, .none => taggedSize p (.option t) 0
    | .option t, .some w => taggedSize p (.option t) (fieldSize p t (valueSize p t w))
    | .result a b, .ok w => taggedSize p (.result a b) (fieldSize p a (valueSize p a w))
    | .result a b, .err w => taggedSize p (.result a b) (fieldSize p b (valueSize p b w))
    | .named n, .con c args =>
      match findRecord p n with
      | some fs => 2 + fieldsSize p (fs.map (·.ty)) args
      | none =>
        match findEnum p n with
        | some vs =>
          match findVariant c vs with
          | some (_, v) => taggedSize p (.named n) (fieldsSize p v.fields args)
          | none => 0
        | none =>
          match findNewtype p n with
          | some inner =>
            match args with
            | [w] => valueSize p inner w
            | _ => 0
          | none => 0
    | _, _ => 0

  def fieldsSize (p : Program) : List Ty → List Value → Nat
    | t :: ts, v :: vs => fieldSize p t (valueSize p t v) + fieldsSize p ts vs
    | _, _ => 0
end

def size (p : Program) (t : Ty) (v : Value) : Nat :=
  2 + valueSize p t v

end Borsuk
