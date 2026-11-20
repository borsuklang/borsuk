import Borsuk.Check
import Borsuk.Runtime

namespace Borsuk

def form (parts : List String) : String :=
  "(" ++ " ".intercalate parts ++ ")"

def escapeText (s : String) : String :=
  String.join (s.toList.map fun c =>
    if c == '"' then "\\\"" else if c == '\\' then "\\\\" else c.toString)

def quote (s : String) : String :=
  "\"" ++ escapeText s ++ "\""

mutual
  def showValue : Value → String
    | .int n => toString n
    | .bool b => if b then "true" else "false"
    | .unit => "(unit)"
    | .text s => quote s
    | .dur n => form ["dur", toString n]
    | .time n => form ["time", toString n]
    | .principal name => form ["principal", quote name]
    | .stepId m k life seq => form ["step", m, showValue k, toString life, toString seq]
    | .ticket m k life seq idx =>
      form ["ticket", m, showValue k, toString life, toString seq, toString idx]
    | .con name args => form (name :: showValues args)
    | .some v => form ["some", showValue v]
    | .none => "(none)"
    | .ok v => form ["ok", showValue v]
    | .err v => form ["err", showValue v]

  def showValues : List Value → List String
    | [] => []
    | v :: vs => showValue v :: showValues vs
end

def showReply : Reply → String
  | .outcome v => form ["outcome", showValue v]
  | .reject r => form ["reject", r]
  | .answer v => form ["answer", showValue v]
  | .ignored => "(ignored)"
  | .fault f => form ["fault", f.text]
  | .next => "(next)"

def showOutput : Output → String
  | .print v => form ["ConsoleOut.print", showValue v]
  | .after d t => form ["Timer.after", showValue d, showValue t]
  | .cancel t => form ["Timer.cancel", showValue t]

def showEnvelope (env : Envelope) : List String :=
  [form ["now", showValue (.time env.now)],
   form ["deadline", showValue (.time env.deadline)],
   form ["by", showValue (.principal env.sender)],
   form ["input", form (env.input :: showValues env.args)]]

def showInstance (env : Envelope) : String :=
  form [env.machine, showValue env.key]

def showEvent : Event → String
  | .step env reply state outputs =>
    form (["step", showValue (env.field .step)] ++ showEnvelope env ++
      [form ["result", showReply reply],
       form ["state", form (state.name :: showValues state.fields)],
       form ("outputs" :: outputs.map showOutput)])
  | .query env reply =>
    form (["query", showInstance env] ++ showEnvelope env ++ [form ["result", showReply reply]])
  | .refused env =>
    form (["refused", showInstance env] ++ showEnvelope env ++ ["forbidden"])

def showDiag (d : Diag) : String :=
  "error[" ++ d.code.text ++ "]: " ++ d.message

end Borsuk
