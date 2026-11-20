namespace Borsuk

abbrev Name := String

inductive Ty where
  | unit
  | bool
  | int
  | text
  | time
  | duration
  | principal
  | stepId
  | ticket
  | option (inner : Ty)
  | result (ok err : Ty)
  | named (name : Name)
  deriving BEq, Inhabited

inductive Effect where
  | consoleOut
  | timer
  deriving BEq

inductive EnvField where
  | now
  | step
  | sender
  | deadline
  deriving BEq

inductive Arith where
  | add
  | sub
  | mul

inductive Op where
  | print
  | after
  | cancel

inductive Expr where
  | int (value : Int)
  | text (value : String)
  | bool (value : Bool)
  | unit
  | dur (value : Int)
  | var (name : Name)
  | env (field : EnvField)
  | call (callee : Name) (args : List Expr)
  | new (ctor : Name) (args : List Expr)
  | get (target : Expr) (field : Name)
  | some (inner : Expr)
  | none
  | ok (inner : Expr)
  | err (inner : Expr)
  | arith (op : Arith) (left right : Expr)
  | eq (left right : Expr)
  | lt (left right : Expr)
  | and (left right : Expr)
  | not (inner : Expr)
  | op (op : Op) (arg : Expr)

inductive Bind where
  | wild
  | name (name : Name)

inductive Pat where
  | bool (value : Bool)
  | none
  | some (bind : Bind)
  | ok (bind : Bind)
  | err (bind : Bind)
  | con (ctor : Name) (binds : List Bind)

inductive Stmt where
  | «let» (name : Name) (value : Expr)
  | «do» (value : Expr)

mutual
  inductive Block where
    | mk (stmts : List Stmt) (tail : Tail)

  inductive Tail where
    | value (value : Expr)
    | next (state : Name) (args : List Expr) (outcome : Option Expr)
    | stay (outcome : Option Expr)
    | reject (reason : Name)
    | answer (value : Expr)
    | ignore
    | impossible
    | «match» (subject : Expr) (arms : List Arm)

  inductive Arm where
    | mk (pat : Pat) (body : Block)
end

structure Param where
  name : Name
  ty : Ty

structure Variant where
  name : Name
  fields : List Ty

structure Fn where
  name : Name
  params : List Param
  result : Ty
  uses : List Effect
  body : Block

inductive Msg where
  | command (name : Name) (params : List Param) (result : Ty) (rejects : List Name) (role : Option Name)
  | query (name : Name) (params : List Param) (result : Ty)

structure Protocol where
  name : Name
  msgs : List Msg

structure State where
  name : Name
  fields : List Param

structure Group where
  name : Name
  members : List Name

structure Cell where
  input : Name
  body : Block

structure In where
  target : Name
  cells : List Cell

structure Machine where
  name : Name
  key : Ty
  protocol : Name
  uses : List Effect
  init : Name
  states : List State
  groups : List Group
  ins : List In

inductive Platform where
  | cli

structure Deployment where
  name : Name
  platform : Platform
  entry : Name

inductive XExpr where
  | int (value : Int)
  | text (value : String)
  | bool (value : Bool)
  | unit
  | dur (value : Int)
  | var (name : Name)
  | new (ctor : Name) (args : List XExpr)
  | some (inner : XExpr)
  | none
  | ok (inner : XExpr)
  | err (inner : XExpr)
  | step (seq : Int)
  | ticket (seq : Int)

inductive Fact where
  | outcome (value : XExpr)
  | reject (reason : Name)
  | answer (value : XExpr)
  | refused
  | fault (kind : Name)
  | ignored
  | state (name : Name) (args : List XExpr)

inductive Line where
  | send (actor : Name) (input : Name) (args : List XExpr) (facts : List Fact)
  | fire (ticket : XExpr) (facts : List Fact)

structure Actor where
  name : Name
  roles : List Name

structure Example where
  name : Name
  machine : Name
  key : XExpr
  actors : List Actor
  lines : List Line

inductive Item where
  | newtype (name : Name) (ty : Ty)
  | record (name : Name) (fields : List Param)
  | enum (name : Name) (variants : List Variant)
  | role (name : Name)
  | fn (fn : Fn)
  | protocol (protocol : Protocol)
  | machine (machine : Machine)
  | deployment (deployment : Deployment)
  | «example» (ex : Example)

structure Program where
  items : List Item

def firedName : Name := "Fired"

def minInt : Int := -9223372036854775808

def maxInt : Int := 9223372036854775807

def inRange (n : Int) : Bool :=
  minInt ≤ n && n ≤ maxInt

def Msg.name : Msg → Name
  | .command name .. => name
  | .query name .. => name

def Msg.params : Msg → List Param
  | .command _ params .. => params
  | .query _ params _ => params

def Msg.result : Msg → Ty
  | .command _ _ result .. => result
  | .query _ _ result => result

def findProtocol (p : Program) (name : Name) : Option Protocol :=
  p.items.findSome? fun
    | .protocol q => if q.name == name then some q else none
    | _ => none

def findFn (p : Program) (name : Name) : Option Fn :=
  p.items.findSome? fun
    | .fn f => if f.name == name then some f else none
    | _ => none

def findMsg (p : Program) (m : Machine) (name : Name) : Option Msg :=
  (findProtocol p m.protocol).bind fun q => q.msgs.find? (·.name == name)

def firedParams : List Param :=
  [{ name := "ticket", ty := .ticket }]

def inputParams (p : Program) (m : Machine) (input : Name) : List Param :=
  match findMsg p m input with
  | some msg => msg.params
  | none => firedParams

def findState (m : Machine) (name : Name) : Option State :=
  m.states.find? (·.name == name)

def inputNames (p : Program) (m : Machine) : List Name :=
  ((findProtocol p m.protocol).map (·.msgs.map Msg.name)).getD [] ++
    (if m.uses.contains .timer then [firedName] else [])

def covers (m : Machine) (target state : Name) : Bool :=
  target == state || m.groups.any fun g => g.name == target && g.members.contains state

def cellsFor (m : Machine) (state input : Name) : List (Name × Cell) :=
  (m.ins.filter fun b => covers m b.target state).flatMap fun b =>
    (b.cells.filter (·.input == input)).map fun c => (b.target, c)

def findCell (m : Machine) (state input : Name) : Option (Name × Cell) :=
  (cellsFor m state input).head?

end Borsuk
