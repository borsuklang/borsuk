import Borsuk

open Borsuk

def faultIs (kind : Name) : Option Reply → Bool
  | some (.fault f) => f.text == kind
  | _ => false

def holds (inst : Option (Name × Value)) (ev : Event) (state : MachineState) : Fact → Bool
  | .outcome x => ev.reply == (xvalue inst x).map Reply.outcome
  | .reject r => ev.reply == some (Reply.reject r)
  | .answer x => ev.reply == (xvalue inst x).map Reply.answer
  | .refused => (ev matches .refused _)
  | .fault k => faultIs k ev.reply
  | .ignored => ev.reply == some Reply.ignored
  | .state s args => state.name == s && xvalues inst args == some state.fields

def findActor (ex : Example) (name : Name) : Actor :=
  (ex.actors.find? (·.name == name)).getD { name := name, roles := [] }

def lineInput (inst : Option (Name × Value)) (ex : Example) :
    Line → Option (Actor × Name × List Value × List Fact)
  | .send a input args facts =>
    (xvalues inst args).map fun vs => (findActor ex a, input, vs, facts)
  | .fire t facts =>
    (xvalue inst t).map fun v => ({ name := "runtime", roles := [] }, firedName, [v], facts)

def runLines (p : Program) (ex : Example) : Nat → Instance → List Line → IO Bool
  | _, _, [] => do
    IO.println s!"pass {ex.name}"
    pure true
  | n, inst, l :: rest => do
    let here := some (inst.machine, inst.key)
    let result := (lineInput here ex l).bind fun (caller, input, args, facts) =>
      (deliver p inst 0 0 caller input args).map fun r => (r, facts)
    match result with
    | some ((inst', ev), facts) =>
      IO.println (showEvent ev)
      if facts.all (holds here ev inst'.state) then runLines p ex (n + 1) inst' rest
      else do
        IO.println s!"fail {ex.name}: line {n}"
        pure false
    | none => do
      IO.println s!"fail {ex.name}: line {n}"
      pure false

def runExample (p : Program) (ex : Example) : IO Bool := do
  match findMachine p ex.machine, xvalue none ex.key with
  | some m, some key => runLines p ex 1 (start m key) ex.lines
  | _, _ => do
    IO.println s!"fail {ex.name}: line 1"
    pure false

def decodeHolds (p : Program) (t : Ty) (frame : List UInt8) : Option XExpr → Bool
  | some x =>
    match xvalue none x with
    | some v => decode p t frame == some v && (!full p t frame || encode p t v == some frame)
    | none => false
  | none => (decode p t frame).isNone

def runDecode (p : Program) (name : Name) (t : Ty) (frame : List UInt8) (expect : Option XExpr) :
    IO Bool := do
  let ok := decodeHolds p t frame expect
  IO.println s!"{if ok then "pass" else "fail"} {name}"
  pure ok

def runItem (p : Program) : Item → IO Bool
  | .«example» ex => runExample p ex
  | .decode name t frame expect => runDecode p name t frame expect
  | _ => pure true

def test (p : Program) : IO UInt32 := do
  let mut ok := true
  for it in p.items do
    if !(← runItem p it) then ok := false
  pure (if ok then 0 else 1)

def firstDeployment (p : Program) : Option Deployment :=
  p.items.findSome? fun
    | .deployment d => some d
    | _ => none

def printed : Output → Option String
  | .print (.text s) => some s
  | _ => none

def run (p : Program) : IO UInt32 := do
  match firstDeployment p with
  | none => do
    IO.println (showDiag { code := .badEntry, message := "no deployment" })
    pure 1
  | some d =>
    match (findFn p d.entry).bind (runEntry p) with
    | some (.ok outs) => do
      for o in outs do
        if let some s := printed o then IO.println s
      pure 0
    | some (.error fault) => do
      IO.println s!"fault {fault.text}"
      pure 1
    | none => pure 1

def usage : IO UInt32 := do
  IO.eprintln "usage: brk-ref check|run|test FILE"
  pure 2

def parseError : IO UInt32 := do
  IO.println (showDiag { code := .parse, message := "text is not a program" })
  pure 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [cmd, file] =>
    if !["check", "run", "test"].contains cmd then usage
    else
      match ← (IO.FS.readBinFile file).toBaseIO with
      | .error _ => parseError
      | .ok bytes =>
        match read bytes with
        | none => parseError
        | some p =>
          match check p with
          | .error ds => do
            for d in ds do IO.println (showDiag d)
            pure 1
          | .ok () =>
            match cmd with
            | "run" => run p
            | "test" => test p
            | _ => pure 0
  | _ => usage
