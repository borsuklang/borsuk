import Borsuk.Ir

namespace Borsuk

inductive Token where
  | lp
  | rp
  | atom (value : String)
  | text (value : String)
  deriving BEq

inductive Lex where
  | gap
  | atom (chars : List Char)
  | text (chars : List Char)
  | escape (chars : List Char)
  | closed

def isSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n'

def isParen (c : Char) : Bool :=
  c == '(' || c == ')'

def paren (c : Char) : Token :=
  if c == '(' then .lp else .rp

def atomToken (chars : List Char) : Token :=
  .atom (String.ofList chars.reverse)

def lex : Lex → List Char → List Token → Option (List Token)
  | .gap, [], acc => some acc.reverse
  | .gap, c :: cs, acc =>
    if isSpace c then lex .gap cs acc
    else if isParen c then lex .gap cs (paren c :: acc)
    else if c == '"' then lex (.text []) cs acc
    else lex (.atom [c]) cs acc
  | .atom chars, [], acc => some (atomToken chars :: acc).reverse
  | .atom chars, c :: cs, acc =>
    if isSpace c then lex .gap cs (atomToken chars :: acc)
    else if isParen c then lex .gap cs (paren c :: atomToken chars :: acc)
    else if c == '"' then none
    else lex (.atom (c :: chars)) cs acc
  | .text _, [], _ => none
  | .text chars, c :: cs, acc =>
    if c == '"' then lex .closed cs (.text (String.ofList chars.reverse) :: acc)
    else if c == '\\' then lex (.escape chars) cs acc
    else if c.toNat < 0x20 || c.toNat == 0x7F then none
    else lex (.text (c :: chars)) cs acc
  | .escape _, [], _ => none
  | .escape chars, c :: cs, acc =>
    if c == '"' || c == '\\' then lex (.text (c :: chars)) cs acc else none
  | .closed, [], acc => some acc.reverse
  | .closed, c :: cs, acc =>
    if isSpace c then lex .gap cs acc
    else if isParen c then lex .gap cs (paren c :: acc)
    else none

def isLetter (c : Char) : Bool :=
  ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z')

def isDigit (c : Char) : Bool :=
  '0' ≤ c && c ≤ '9'

def isIdent (s : String) : Bool :=
  match s.toList with
  | c :: cs => isLetter c && cs.all fun d => isLetter d || isDigit d || d == '_'
  | [] => false

def digitsValue (cs : List Char) : Nat :=
  cs.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0

def natural (cs : List Char) : Option Nat :=
  match cs with
  | c :: rest => if c != '0' && isDigit c && rest.all isDigit then some (digitsValue cs) else none
  | [] => none

def parseInt (s : String) : Option Int :=
  let n : Option Int :=
    if s == "0" then some 0
    else match s.toList with
      | '-' :: cs => (natural cs).map fun v => -(v : Int)
      | cs => (natural cs).map fun v => (v : Int)
  n.bind fun v => if inRange v then some v else none

def reserved : List String :=
  ["program", "newtype", "record", "enum", "role", "fn", "uses", "block", "protocol", "machine",
   "key", "init", "state", "group", "in", "on", "deployment", "platform", "entry", "example",
   "command", "rejects", "by", "query", "let", "do", "value", "next", "outcome", "stay",
   "reject", "answer", "ignore", "impossible", "match", "arm", "unit", "dur", "env", "call",
   "new", "get", "some", "none", "ok", "err", "and", "not", "actor", "send", "fire", "expect",
   "refused", "fault", "ignored", "step", "ticket",
   "Unit", "Bool", "Int", "Text", "Time", "Duration", "Principal", "StepId", "Ticket",
   "Option", "Result", "true", "false", "Fired", "ConsoleOut", "Timer"]

abbrev Reader := StateT (List Token) Option

def token : Reader Token := fun
  | t :: ts => some (t, ts)
  | [] => none

def peekClose : Reader Bool := fun ts =>
  match ts with
  | .rp :: _ => some (true, ts)
  | _ => some (false, ts)

def peekHead : Reader (Option String) := fun ts =>
  match ts with
  | .lp :: .atom h :: _ => some (some h, ts)
  | _ => some (none, ts)

def openParen : Reader Unit := do
  let .lp ← token | failure

def closeParen : Reader Unit := do
  let .rp ← token | failure

def atom : Reader String := do
  let .atom s ← token | failure
  pure s

def keyword (word : String) : Reader Unit := do
  let s ← atom
  if s != word then failure

def head (word : String) : Reader Unit := do
  openParen
  keyword word

def ident : Reader Name := do
  let s ← atom
  if isIdent s then pure s else failure

def declName : Reader Name := do
  let s ← ident
  if reserved.contains s then failure else pure s

def localName : Reader Name := do
  let s ← ident
  if s == "true" || s == "false" then failure else pure s

def int : Reader Int := do
  let some n := parseInt (← atom) | failure
  pure n

partial def untilClose {α : Type} (item : Reader α) : Reader (List α) := do
  if ← peekClose then pure []
  else
    let x ← item
    let xs ← untilClose item
    pure (x :: xs)

def some1 {α : Type} (item : Reader α) : Reader (List α) := do
  let xs ← untilClose item
  if xs.isEmpty then failure else pure xs

partial def headed {α : Type} (word : String) (item : Reader α) : Reader (List α) := do
  if (← peekHead) == some word then
    let x ← item
    let xs ← headed word item
    pure (x :: xs)
  else pure []

partial def ty : Reader Ty := do
  match ← token with
  | .atom "Unit" => pure .unit
  | .atom "Bool" => pure .bool
  | .atom "Int" => pure .int
  | .atom "Text" => pure .text
  | .atom "Time" => pure .time
  | .atom "Duration" => pure .duration
  | .atom "Principal" => pure .principal
  | .atom "StepId" => pure .stepId
  | .atom "Ticket" => pure .ticket
  | .atom s => if isIdent s then pure (.named s) else failure
  | .lp =>
    match ← atom with
    | "Option" =>
      let t ← ty
      closeParen
      pure (.option t)
    | "Result" =>
      let ok ← ty
      let err ← ty
      closeParen
      pure (.result ok err)
    | _ => failure
  | _ => failure

def envField : Reader EnvField := do
  match ← atom with
  | "now" => pure .now
  | "step" => pure .step
  | "sender" => pure .sender
  | "deadline" => pure .deadline
  | _ => failure

def atomExpr (s : String) : Reader Expr :=
  match parseInt s with
  | some n => pure (.int n)
  | none =>
    if s == "true" then pure (.bool true)
    else if s == "false" then pure (.bool false)
    else if isIdent s then pure (.var s)
    else failure

partial def expr : Reader Expr := do
  match ← token with
  | .text s => pure (.text s)
  | .atom s => atomExpr s
  | .lp =>
    let e ← match ← atom with
      | "unit" => pure .unit
      | "dur" => pure (.dur (← int))
      | "env" => pure (.env (← envField))
      | "call" => pure (.call (← ident) (← untilClose expr))
      | "new" => pure (.new (← ident) (← untilClose expr))
      | "get" => pure (.get (← expr) (← ident))
      | "some" => pure (.some (← expr))
      | "none" => pure .none
      | "ok" => pure (.ok (← expr))
      | "err" => pure (.err (← expr))
      | "+" => pure (.arith .add (← expr) (← expr))
      | "-" => pure (.arith .sub (← expr) (← expr))
      | "*" => pure (.arith .mul (← expr) (← expr))
      | "==" => pure (.eq (← expr) (← expr))
      | "<" => pure (.lt (← expr) (← expr))
      | "and" => pure (.and (← expr) (← expr))
      | "not" => pure (.not (← expr))
      | "ConsoleOut.print" => pure (.op .print (← expr))
      | "Timer.after" => pure (.op .after (← expr))
      | "Timer.cancel" => pure (.op .cancel (← expr))
      | _ => failure
    closeParen
    pure e
  | .rp => failure

def bind : Reader Bind := do
  let s ← atom
  if s == "_" then pure .wild
  else if isIdent s && s != "true" && s != "false" then pure (.name s)
  else failure

def pat : Reader Pat := do
  match ← token with
  | .atom "true" => pure (.bool true)
  | .atom "false" => pure (.bool false)
  | .lp =>
    let h ← atom
    let binds ← untilClose bind
    closeParen
    match h, binds with
    | "none", [] => pure .none
    | "some", [b] => pure (.some b)
    | "ok", [b] => pure (.ok b)
    | "err", [b] => pure (.err b)
    | _, _ => if isIdent h then pure (.con h binds) else failure
  | _ => failure

def outcome : Reader (Option Expr) := do
  if ← peekClose then pure none
  else
    head "outcome"
    let e ← expr
    closeParen
    pure (some e)

mutual
  partial def block : Reader Block := do
    head "block"
    let (stmts, tail) ← blockBody
    pure (.mk stmts tail)

  partial def blockBody : Reader (List Stmt × Tail) := do
    openParen
    match ← atom with
    | "let" =>
      let x ← localName
      let e ← expr
      closeParen
      let (stmts, t) ← blockBody
      pure (.«let» x e :: stmts, t)
    | "do" =>
      let e ← expr
      closeParen
      let (stmts, t) ← blockBody
      pure (.«do» e :: stmts, t)
    | h =>
      let t ← tail h
      closeParen
      pure ([], t)

  partial def tail (h : String) : Reader Tail := do
    match h with
    | "value" =>
      let e ← expr
      closeParen
      pure (.value e)
    | "next" =>
      openParen
      let s ← ident
      let args ← untilClose expr
      closeParen
      let o ← outcome
      closeParen
      pure (.next s args o)
    | "stay" =>
      let o ← outcome
      closeParen
      pure (.stay o)
    | "reject" =>
      let r ← ident
      closeParen
      pure (.reject r)
    | "answer" =>
      let e ← expr
      closeParen
      pure (.answer e)
    | "ignore" =>
      keyword "stale"
      closeParen
      pure .ignore
    | "impossible" =>
      closeParen
      pure .impossible
    | "match" =>
      let e ← expr
      let arms ← some1 arm
      closeParen
      pure (.«match» e arms)
    | _ => failure

  partial def arm : Reader Arm := do
    head "arm"
    let p ← pat
    let b ← block
    closeParen
    pure (.mk p b)
end

def param : Reader Param := do
  openParen
  let x ← localName
  let t ← ty
  closeParen
  pure { name := x, ty := t }

def field : Reader Param := do
  openParen
  let x ← ident
  let t ← ty
  closeParen
  pure { name := x, ty := t }

def params : Reader (List Param) := do
  openParen
  let ps ← untilClose param
  closeParen
  pure ps

def variant : Reader Variant := do
  openParen
  let n ← declName
  let ts ← untilClose ty
  closeParen
  pure { name := n, fields := ts }

def optionalAtom (word : String) : Reader Bool := fun ts =>
  match ts with
  | .atom s :: rest => if s == word then some (true, rest) else some (false, ts)
  | _ => some (false, ts)

def uses (timer : Bool) : Reader (List Effect) := do
  head "uses"
  let c ← optionalAtom "ConsoleOut"
  let t ← if timer then optionalAtom "Timer" else pure false
  closeParen
  pure ((if c then [.consoleOut] else []) ++ (if t then [.timer] else []))

def fn : Reader Fn := do
  let n ← declName
  let ps ← params
  let r ← ty
  let u ← uses false
  let b ← block
  closeParen
  pure { name := n, params := ps, result := r, uses := u, body := b }

def msg : Reader Msg := do
  openParen
  match ← atom with
  | "command" =>
    let n ← declName
    let ps ← params
    let r ← ty
    head "rejects"
    let rs ← untilClose ident
    closeParen
    let role ← if ← peekClose then pure none
      else
        head "by"
        let x ← ident
        closeParen
        pure (some x)
    closeParen
    pure (.command n ps r rs role)
  | "query" =>
    let n ← declName
    let ps ← params
    let r ← ty
    closeParen
    pure (.query n ps r)
  | _ => failure

def state : Reader State := do
  head "state"
  let n ← declName
  let fs ← untilClose param
  closeParen
  pure { name := n, fields := fs }

def group : Reader Group := do
  head "group"
  let n ← declName
  let ms ← some1 ident
  closeParen
  pure { name := n, members := ms }

def cell : Reader Cell := do
  head "on"
  let i ← ident
  let b ← block
  closeParen
  pure { input := i, body := b }

def «in» : Reader In := do
  head "in"
  let t ← ident
  let cs ← some1 cell
  closeParen
  pure { target := t, cells := cs }

def nonEmpty {α : Type} (xs : List α) : Reader (List α) :=
  if xs.isEmpty then failure else pure xs

def machine : Reader Machine := do
  let n ← declName
  head "key"
  let k ← ty
  closeParen
  head "protocol"
  let q ← ident
  closeParen
  let u ← uses true
  head "init"
  let i ← ident
  closeParen
  let ss ← nonEmpty (← headed "state" state)
  let gs ← headed "group" group
  let ins ← nonEmpty (← headed "in" «in»)
  closeParen
  pure { name := n, key := k, protocol := q, uses := u, init := i, states := ss, groups := gs,
         ins := ins }

def deployment : Reader Deployment := do
  let n ← declName
  head "platform"
  keyword "cli"
  closeParen
  head "entry"
  let e ← ident
  closeParen
  closeParen
  pure { name := n, platform := .cli, entry := e }

partial def xexpr : Reader XExpr := do
  match ← token with
  | .text s => pure (.text s)
  | .atom s =>
    match parseInt s with
    | some n => pure (.int n)
    | none =>
      if s == "true" then pure (.bool true)
      else if s == "false" then pure (.bool false)
      else if isIdent s then pure (.var s)
      else failure
  | .lp =>
    let x ← match ← atom with
      | "unit" => pure .unit
      | "dur" => pure (.dur (← int))
      | "new" => pure (.new (← ident) (← untilClose xexpr))
      | "some" => pure (.some (← xexpr))
      | "none" => pure .none
      | "ok" => pure (.ok (← xexpr))
      | "err" => pure (.err (← xexpr))
      | "step" => pure (.step (← int))
      | "ticket" => pure (.ticket (← int))
      | _ => failure
    closeParen
    pure x
  | .rp => failure

def fact : Reader Fact := do
  openParen
  let f ← match ← atom with
    | "outcome" => pure (.outcome (← xexpr))
    | "reject" => pure (.reject (← ident))
    | "answer" => pure (.answer (← xexpr))
    | "refused" =>
      keyword "forbidden"
      pure .refused
    | "fault" => pure (.fault (← ident))
    | "ignored" => pure .ignored
    | "state" => pure (.state (← ident) (← untilClose xexpr))
    | _ => failure
  closeParen
  pure f

def expect : Reader (List Fact) := do
  head "expect"
  let fs ← untilClose fact
  closeParen
  pure fs

partial def sendArgs : Reader (List XExpr) := do
  if (← peekHead) == some "expect" then pure []
  else
    let x ← xexpr
    let xs ← sendArgs
    pure (x :: xs)

def line : Reader Line := do
  openParen
  let l ← match ← atom with
    | "send" =>
      let a ← ident
      let i ← ident
      let args ← sendArgs
      let fs ← expect
      pure (.send a i args fs)
    | "fire" =>
      let t ← xexpr
      let fs ← expect
      pure (.fire t fs)
    | _ => failure
  closeParen
  pure l

def actor : Reader Actor := do
  head "actor"
  let n ← localName
  let rs ← untilClose ident
  closeParen
  pure { name := n, roles := rs }

def «example» : Reader Example := do
  let n ← declName
  head "machine"
  let m ← ident
  closeParen
  head "key"
  let k ← xexpr
  closeParen
  let actors ← headed "actor" actor
  let lines ← some1 line
  closeParen
  pure { name := n, machine := m, key := k, actors := actors, lines := lines }

def item : Reader Item := do
  openParen
  match ← atom with
  | "newtype" =>
    let n ← declName
    let t ← ty
    closeParen
    pure (.newtype n t)
  | "record" =>
    let n ← declName
    let fs ← some1 field
    closeParen
    pure (.record n fs)
  | "enum" =>
    let n ← declName
    let vs ← some1 variant
    closeParen
    pure (.enum n vs)
  | "role" =>
    let n ← declName
    closeParen
    pure (.role n)
  | "fn" => pure (.fn (← fn))
  | "protocol" =>
    let n ← declName
    let ms ← some1 msg
    closeParen
    pure (.protocol { name := n, msgs := ms })
  | "machine" => pure (.machine (← machine))
  | "deployment" => pure (.deployment (← deployment))
  | "example" => pure (.«example» (← «example»))
  | _ => failure

def program : Reader Program := do
  head "program"
  let items ← untilClose item
  closeParen
  pure { items := items }

def read (bytes : ByteArray) : Option Program := do
  let text ← String.fromUTF8? bytes
  let tokens ← lex .gap text.toList []
  let (p, rest) ← program tokens
  if rest.isEmpty then some p else none

end Borsuk
