import Borsuk.Ir

namespace Borsuk

inductive Value where
  | int (value : Int)
  | bool (value : Bool)
  | unit
  | text (value : String)
  | dur (nanos : Int)
  | time (nanos : Int)
  | principal (name : Name)
  | stepId (machine : Name) (key : Value) (life seq : Int)
  | ticket (machine : Name) (key : Value) (life seq idx : Int)
  | con (name : Name) (args : List Value)
  | some (inner : Value)
  | none
  | ok (inner : Value)
  | err (inner : Value)
  deriving BEq, Inhabited

inductive Fault where
  | overflow
  | impossible
  deriving BEq

def Fault.text : Fault → String
  | .overflow => "overflow"
  | .impossible => "impossible"

inductive Stop where
  | fault (kind : Fault)
  | stuck

inductive Output where
  | print (text : Value)
  | after (delay : Value) (ticket : Value)
  | cancel (ticket : Value)

structure Envelope where
  machine : Name
  key : Value
  life : Int
  seq : Int
  now : Int
  deadline : Int
  sender : Name
  input : Name
  args : List Value

def Envelope.field (env : Envelope) : EnvField → Value
  | .now => .time env.now
  | .step => .stepId env.machine env.key env.life env.seq
  | .sender => .principal env.sender
  | .deadline => .time env.deadline

inductive Ending where
  | value (value : Value)
  | next (state : Name) (args : List Value) (outcome : Option Value)
  | stay (outcome : Option Value)
  | reject (reason : Name)
  | answer (value : Value)
  | ignore

abbrev M := StateT (Array Output) (Except Stop)

def stuck {α : Type} : M α :=
  throw .stuck

def checked (n : Int) : M Value :=
  if inRange n then pure (.int n) else throw (.fault .overflow)

def arith (op : Arith) (a b : Int) : Int :=
  match op with
  | .add => a + b
  | .sub => a - b
  | .mul => a * b

def less : Value → Value → Option Bool
  | .int a, .int b => some (a < b)
  | .time a, .time b => some (a < b)
  | .dur a, .dur b => some (a < b)
  | _, _ => none

def tickets (outs : Array Output) : Nat :=
  outs.foldl (fun n o => match o with
    | .after .. => n + 1
    | _ => n) 0

def bindValue (b : Bind) (v : Value) : List (Name × Value) :=
  match b with
  | .wild => []
  | .name x => [(x, v)]

def bindValues : List Bind → List Value → List (Name × Value)
  | b :: bs, v :: vs => bindValue b v ++ bindValues bs vs
  | _, _ => []

def matchPat : Pat → Value → Option (List (Name × Value))
  | .bool b, .bool v => if b == v then some [] else none
  | .none, .none => some []
  | .some b, .some v => some (bindValue b v)
  | .ok b, .ok v => some (bindValue b v)
  | .err b, .err v => some (bindValue b v)
  | .con c bs, .con d vs => if c == d then some (bindValues bs vs) else none
  | _, _ => none

def fieldIndex (p : Program) (record field : Name) : Option Nat :=
  p.items.findSome? fun
    | .record r fields => if r == record then fields.findIdx? (·.name == field) else none
    | _ => none

def fuelOf (p : Program) : Nat :=
  p.items.countP fun
    | .fn _ => true
    | _ => false

abbrev Call := Name → List Value → M Value

mutual
  def evalExpr (p : Program) (env : Option Envelope) (call : Call) (locals : List (Name × Value)) :
      Expr → M Value
    | .int n => pure (.int n)
    | .text s => pure (.text s)
    | .bool b => pure (.bool b)
    | .unit => pure .unit
    | .dur n => pure (.dur n)
    | .var x =>
      match locals.find? (·.1 == x) with
      | some (_, v) => pure v
      | none => stuck
    | .env field =>
      match env with
      | some e => pure (e.field field)
      | none => stuck
    | .call callee args => do
      let vs ← evalArgs p env call locals args
      call callee vs
    | .new ctor args => do
      let vs ← evalArgs p env call locals args
      pure (.con ctor vs)
    | .get target field => do
      let v ← evalExpr p env call locals target
      match v with
      | .con r vs =>
        match (fieldIndex p r field).bind fun i => vs[i]? with
        | some x => pure x
        | none => stuck
      | _ => stuck
    | .some inner => do
      let v ← evalExpr p env call locals inner
      pure (.some v)
    | .none => pure .none
    | .ok inner => do
      let v ← evalExpr p env call locals inner
      pure (.ok v)
    | .err inner => do
      let v ← evalExpr p env call locals inner
      pure (.err v)
    | .arith op a b => do
      let va ← evalExpr p env call locals a
      let vb ← evalExpr p env call locals b
      match va, vb with
      | .int x, .int y => checked (arith op x y)
      | _, _ => stuck
    | .eq a b => do
      let va ← evalExpr p env call locals a
      let vb ← evalExpr p env call locals b
      pure (.bool (va == vb))
    | .lt a b => do
      let va ← evalExpr p env call locals a
      let vb ← evalExpr p env call locals b
      match less va vb with
      | some r => pure (.bool r)
      | none => stuck
    | .and a b => do
      let va ← evalExpr p env call locals a
      let vb ← evalExpr p env call locals b
      match va, vb with
      | .bool x, .bool y => pure (.bool (x && y))
      | _, _ => stuck
    | .not a => do
      let va ← evalExpr p env call locals a
      match va with
      | .bool x => pure (.bool !x)
      | _ => stuck
    | .op .print arg => do
      let v ← evalExpr p env call locals arg
      modify (·.push (.print v))
      pure .unit
    | .op .after arg => do
      let d ← evalExpr p env call locals arg
      match env with
      | some e => do
        let idx := tickets (← get)
        let t := Value.ticket e.machine e.key e.life e.seq idx
        modify (·.push (.after d t))
        pure t
      | none => stuck
    | .op .cancel arg => do
      let t ← evalExpr p env call locals arg
      modify (·.push (.cancel t))
      pure .unit

  def evalArgs (p : Program) (env : Option Envelope) (call : Call) (locals : List (Name × Value)) :
      List Expr → M (List Value)
    | [] => pure []
    | e :: es => do
      let v ← evalExpr p env call locals e
      let vs ← evalArgs p env call locals es
      pure (v :: vs)
end

def evalOutcome (p : Program) (env : Option Envelope) (call : Call) (locals : List (Name × Value)) :
    Option Expr → M (Option Value)
  | some e => do
    let v ← evalExpr p env call locals e
    pure (some v)
  | none => pure none

def evalStmts (p : Program) (env : Option Envelope) (call : Call) (locals : List (Name × Value)) :
    List Stmt → M (List (Name × Value))
  | [] => pure locals
  | .«let» x e :: rest => do
    let v ← evalExpr p env call locals e
    evalStmts p env call ((x, v) :: locals) rest
  | .«do» e :: rest => do
    let _ ← evalExpr p env call locals e
    evalStmts p env call locals rest

mutual
  def evalBlock (p : Program) (env : Option Envelope) (call : Call) (locals : List (Name × Value)) :
      Block → M Ending
    | .mk stmts t => do
      let locals' ← evalStmts p env call locals stmts
      evalTail p env call locals' t

  def evalTail (p : Program) (env : Option Envelope) (call : Call) (locals : List (Name × Value)) :
      Tail → M Ending
    | .value e => do
      let v ← evalExpr p env call locals e
      pure (.value v)
    | .next s args o => do
      let vs ← evalArgs p env call locals args
      let ov ← evalOutcome p env call locals o
      pure (.next s vs ov)
    | .stay o => do
      let ov ← evalOutcome p env call locals o
      pure (.stay ov)
    | .reject r => pure (.reject r)
    | .answer e => do
      let v ← evalExpr p env call locals e
      pure (.answer v)
    | .ignore => pure .ignore
    | .impossible => throw (.fault .impossible)
    | .«match» subject arms => do
      let v ← evalExpr p env call locals subject
      evalArms p env call locals v arms

  def evalArms (p : Program) (env : Option Envelope) (call : Call) (locals : List (Name × Value))
      (subject : Value) : List Arm → M Ending
    | [] => stuck
    | .mk pat body :: rest =>
      match matchPat pat subject with
      | some binds => evalBlock p env call (binds ++ locals) body
      | none => evalArms p env call locals subject rest
end

def callFn (p : Program) : Nat → Call
  | 0, _, _ => stuck
  | k + 1, callee, args =>
    match findFn p callee with
    | some f => do
      let ending ← evalBlock p none (callFn p k) ((f.params.map (·.name)).zip args) f.body
      match ending with
      | .value v => pure v
      | _ => stuck
    | none => stuck

end Borsuk
