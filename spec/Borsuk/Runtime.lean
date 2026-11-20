import Borsuk.Eval

namespace Borsuk

inductive Reply where
  | outcome (value : Value)
  | reject (reason : Name)
  | answer (value : Value)
  | ignored
  | fault (kind : Fault)
  | next
  deriving BEq

structure MachineState where
  name : Name
  fields : List Value

structure Instance where
  state : MachineState
  seq : Int

inductive Event where
  | step (env : Envelope) (reply : Reply) (state : MachineState) (outputs : List Output)
  | query (env : Envelope) (reply : Reply)
  | refused (env : Envelope)

def Event.reply : Event → Option Reply
  | .step _ reply _ _ => some reply
  | .query _ reply => some reply
  | .refused _ => none

def life : Int := 1

def start (m : Machine) : Instance :=
  { state := { name := m.init, fields := [] }, seq := 0 }

def cellLocals (p : Program) (m : Machine) (st : MachineState) (target : Name) (env : Envelope) :
    List (Name × Value) :=
  let fields := if target == st.name then
      match findState m st.name with
      | some s => (s.fields.map (·.name)).zip st.fields
      | none => []
    else []
  fields ++ ((inputParams p m env.input).map (·.name)).zip env.args

def runCell (p : Program) (m : Machine) (inst : Instance) (env : Envelope) :
    Option (Except Fault (Ending × List Output)) :=
  match findCell m inst.state.name env.input with
  | none => none
  | some (target, cell) =>
    let locals := cellLocals p m inst.state target env
    match (evalBlock p (some env) (callFn p (fuelOf p)) locals cell.body).run #[] with
    | .ok (ending, outs) => some (.ok (ending, outs.toList))
    | .error (.fault f) => some (.error f)
    | .error .stuck => none

def settle (st : MachineState) : Ending → Option (Reply × MachineState)
  | .next s vs o => some ((o.map .outcome).getD .next, { name := s, fields := vs })
  | .stay o => some ((o.map .outcome).getD .next, st)
  | .reject r => some (.reject r, st)
  | .answer v => some (.answer v, st)
  | .ignore => some (.ignored, st)
  | .value _ => none

def step (p : Program) (m : Machine) (inst : Instance) (env : Envelope) :
    Option (Instance × Event) := do
  match ← runCell p m inst env with
  | .error f => some ({ inst with seq := env.seq }, .step env (.fault f) inst.state [])
  | .ok (ending, outs) =>
    let (reply, state) ← settle inst.state ending
    some ({ state := state, seq := env.seq }, .step env reply state outs)

def query (p : Program) (m : Machine) (inst : Instance) (env : Envelope) :
    Option (Instance × Event) := do
  match ← runCell p m inst env with
  | .error f => some (inst, .query env (.fault f))
  | .ok (ending, _) =>
    let (reply, _) ← settle inst.state ending
    some (inst, .query env reply)

def deliver (p : Program) (m : Machine) (key : Value) (inst : Instance) (now deadline : Int)
    (sender : Name) (roles : List Name) (input : Name) (args : List Value) :
    Option (Instance × Event) :=
  let env (seq : Int) : Envelope :=
    { machine := m.name, key := key, life := life, seq := seq, now := now, deadline := deadline,
      sender := sender, input := input, args := args }
  match findMsg p m input with
  | some (.command _ _ _ _ (some role)) =>
    if roles.contains role then step p m inst (env (inst.seq + 1))
    else some (inst, .refused (env inst.seq))
  | some (.query ..) => query p m inst (env inst.seq)
  | _ => step p m inst (env (inst.seq + 1))

def runEntry (p : Program) (f : Fn) : Option (Except Fault (List Output)) :=
  match (evalBlock p none (callFn p (fuelOf p)) [] f.body).run #[] with
  | .ok (.value _, outs) => some (.ok outs.toList)
  | .ok _ => none
  | .error (.fault fault) => some (.error fault)
  | .error .stuck => none

end Borsuk
