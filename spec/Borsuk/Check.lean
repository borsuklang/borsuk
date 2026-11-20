import Borsuk.Ir

namespace Borsuk

inductive Code where
  | parse
  | unknownName
  | duplicateName
  | recursion
  | wrongEnding
  | typeMismatch
  | matchArms
  | effectPosition
  | effectNotDeclared
  | envPosition
  | initHasFields
  | duplicateCell
  | missingCell
  | rejectNotDeclared
  | badEntry
  | recursiveType
  | layoutLimit
  deriving BEq

def Code.rank : Code → Nat
  | .parse => 0
  | .unknownName => 1
  | .duplicateName => 2
  | .recursion => 3
  | .recursiveType => 4
  | .layoutLimit => 5
  | .wrongEnding => 6
  | .typeMismatch => 7
  | .matchArms => 8
  | .effectPosition => 9
  | .effectNotDeclared => 10
  | .envPosition => 11
  | .initHasFields => 12
  | .duplicateCell => 13
  | .missingCell => 14
  | .rejectNotDeclared => 15
  | .badEntry => 16

def Code.text : Code → String
  | .parse => "parse"
  | .unknownName => "unknown-name"
  | .duplicateName => "duplicate-name"
  | .recursion => "recursion"
  | .wrongEnding => "wrong-ending"
  | .typeMismatch => "type-mismatch"
  | .matchArms => "match-arms"
  | .effectPosition => "effect-position"
  | .effectNotDeclared => "effect-not-declared"
  | .envPosition => "env-position"
  | .initHasFields => "init-has-fields"
  | .duplicateCell => "duplicate-cell"
  | .missingCell => "missing-cell"
  | .rejectNotDeclared => "reject-not-declared"
  | .badEntry => "bad-entry"
  | .recursiveType => "recursive-type"
  | .layoutLimit => "layout-limit"

structure Diag where
  code : Code
  message : String

def tick (s : String) : String :=
  "`" ++ s ++ "`"

def Effect.text : Effect → String
  | .consoleOut => "ConsoleOut"
  | .timer => "Timer"

def EnvField.text : EnvField → String
  | .now => "now"
  | .step => "step"
  | .sender => "sender"
  | .deadline => "deadline"

def findRecord (p : Program) (name : Name) : Option (List Param) :=
  p.items.findSome? fun
    | .record r fields inits => if r == name then some (fields ++ inits.map (·.1)) else none
    | _ => none

def findEnum (p : Program) (name : Name) : Option (List Variant) :=
  p.items.findSome? fun
    | .enum e variants => if e == name then some variants else none
    | _ => none

def findNewtype (p : Program) (name : Name) : Option Ty :=
  p.items.findSome? fun
    | .newtype n t => if n == name then some t else none
    | _ => none

def isRole (p : Program) (name : Name) : Bool :=
  p.items.any fun
    | .role r => r == name
    | _ => false

def isTypeName (p : Program) (name : Name) : Bool :=
  p.items.any fun
    | .newtype n _ => n == name
    | .record r _ _ => r == name
    | .enum e _ => e == name
    | _ => false

def findCtor (p : Program) (name : Name) : Option (Ty × List Ty) :=
  p.items.findSome? fun
    | .newtype n t => if n == name then some (.named n, [t]) else none
    | .record r fields inits =>
      if r == name then some (.named r, (fields ++ inits.map (·.1)).map (·.ty)) else none
    | .enum e variants => (variants.find? (·.name == name)).map fun v => (.named e, v.fields)
    | _ => none

def findCase (p : Program) (name : Name) : Option (Ty × List Ty) :=
  p.items.findSome? fun
    | .newtype n t => if n == name then some (.named n, [t]) else none
    | .enum e variants => (variants.find? (·.name == name)).map fun v => (.named e, v.fields)
    | _ => none

def fnIndex (p : Program) (name : Name) : Option Nat :=
  p.items.findIdx? fun
    | .fn f => f.name == name
    | _ => false

def findGroup (m : Machine) (name : Name) : Option Group :=
  m.groups.find? (·.name == name)

def usesConsole (p : Program) (name : Name) : Bool :=
  match findFn p name with
  | some f => f.uses.contains .consoleOut
  | none => false

def isOp (p : Program) : Expr → Bool
  | .op _ _ => true
  | .call f _ => usesConsole p f
  | _ => false

mutual
  def hasOp (p : Program) : Expr → Bool
    | .int _ | .text _ | .bool _ | .unit | .dur _ | .var _ | .env _ | .none => false
    | .f64 _ | .f32 _ | .dec _ _ => false
    | .call f args => usesConsole p f || hasOpAny p args
    | .new _ args => hasOpAny p args
    | .get e _ => hasOp p e
    | .some e => hasOp p e
    | .ok e => hasOp p e
    | .err e => hasOp p e
    | .not e => hasOp p e
    | .arith _ a b => hasOp p a || hasOp p b
    | .eq a b => hasOp p a || hasOp p b
    | .lt a b => hasOp p a || hasOp p b
    | .and a b => hasOp p a || hasOp p b
    | .op _ _ => true
    | .div a b => hasOp p a || hasOp p b
    | .sqrt a => hasOp p a
    | .fma a b c => hasOp p a || hasOp p b || hasOp p c
    | .fn1 _ a => hasOp p a
    | .fn2 _ a b => hasOp p a || hasOp p b
    | .round _ _ a => hasOp p a
    | .divMode _ _ a b => hasOp p a || hasOp p b

  def hasOpAny (p : Program) : List Expr → Bool
    | [] => false
    | e :: es => hasOp p e || hasOpAny p es
end

def envType : EnvField → Ty
  | .now => .time
  | .step => .stepId
  | .sender => .principal
  | .deadline => .time

def Op.effect : Op → Effect
  | .print => .consoleOut
  | .after => .timer
  | .cancel => .timer

def Op.arg : Op → Ty
  | .print => .text
  | .after => .duration
  | .cancel => .ticket

def Op.result : Op → Ty
  | .print => .unit
  | .after => .ticket
  | .cancel => .unit

def ctorsOf (p : Program) : Ty → Option (List Name)
  | .bool => some ["true", "false"]
  | .option _ => some ["none", "some"]
  | .result _ _ => some ["ok", "err"]
  | .named n =>
    match findEnum p n with
    | some variants => some (variants.map (·.name))
    | none => (findNewtype p n).map fun _ => [n]
  | _ => none

def Pat.ctor : Pat → Name
  | .bool true => "true"
  | .bool false => "false"
  | .none => "none"
  | .some _ => "some"
  | .ok _ => "ok"
  | .err _ => "err"
  | .con c _ => c

def coversOnce (ctors names : List Name) : Bool :=
  ctors.length == names.length && ctors.all fun c => (names.filter (· == c)).length == 1

inductive Site where
  | fn (result : Ty)
  | command (name : Name) (result : Ty) (rejects : List Name)
  | query (result : Ty)
  | fired
  | unknown

def Site.permits (site : Site) (t : Tail) : Bool :=
  match site, t with
  | .unknown, _ => true
  | _, .«match» _ _ => true
  | .fn _, .value _ => true
  | .command .., .next _ _ o => o.isSome
  | .command .., .stay o => o.isSome
  | .command .., .reject _ => true
  | .command .., .impossible => true
  | .query _, .answer _ => true
  | .query _, .impossible => true
  | .fired, .next _ _ o => o.isNone
  | .fired, .stay o => o.isNone
  | .fired, .ignore => true
  | .fired, .impossible => true
  | _, _ => false

def Site.outcome : Site → Option Ty
  | .command _ result _ => some result
  | _ => none

def Site.answer : Site → Option Ty
  | .query result => some result
  | _ => none

def Site.value : Site → Option Ty
  | .fn result => some result
  | _ => none

def inputSite (p : Program) (m : Machine) (input : Name) : Option (Site × List Param) :=
  match findMsg p m input with
  | some (.command name params result rejects _) => some (.command name result rejects, params)
  | some (.query _ params result) => some (.query result, params)
  | none =>
    if input == firedName && m.uses.contains .timer then
      some (.fired, firedParams)
    else none

structure Ctx where
  item : Name
  fnIndex : Option Nat
  machine : Option Machine
  site : Site
  uses : List Effect
  scope : List (Name × Option Ty)

structure Walk where
  diags : Array Diag
  declared : List Name
  locals : List Name
  deployments : Nat

abbrev W := StateM Walk

def emit (code : Code) (message : String) : W Unit :=
  modify fun w => { w with diags := w.diags.push { code := code, message := message } }

def unknown (name : Name) : W Unit :=
  emit .unknownName s!"name {tick name} is not declared"

def duplicate (name : Name) : W Unit :=
  emit .duplicateName s!"name {tick name} is declared twice"

def mismatch (ctx : Ctx) : W Unit :=
  emit .typeMismatch s!"type mismatch in {tick ctx.item}"

def wrongEnding (ctx : Ctx) : W Unit :=
  emit .wrongEnding s!"wrong ending in {tick ctx.item}"

def declare (name : Name) : W Unit := do
  let w ← get
  if w.declared.contains name || w.locals.contains name then duplicate name
  modify fun w => { w with declared := name :: w.declared }

def declareLocal (ctx : Ctx) (name : Name) (ty : Option Ty) : W Ctx := do
  let w ← get
  if w.declared.contains name || ctx.scope.any (·.1 == name) then duplicate name
  modify fun w => { w with locals := name :: w.locals }
  pure { ctx with scope := (name, ty) :: ctx.scope }

def bindLocal (ctx : Ctx) (name : Name) (ty : Option Ty) : W Ctx := do
  if ctx.scope.any (·.1 == name) then duplicate name
  pure { ctx with scope := (name, ty) :: ctx.scope }

def fits (ctx : Ctx) (want got : Option Ty) : W (Option Ty) := do
  match want, got with
  | some w, some g => if w == g then pure got else do mismatch ctx; pure got
  | _, _ => pure got

def arity (ctx : Ctx) (got want : Nat) : W Unit :=
  if got == want then pure () else mismatch ctx

def opCheck (ctx : Ctx) (allowOp : Bool) (effect : Effect) : W Unit := do
  if !allowOp then emit .effectPosition s!"wrong operation position in {tick ctx.item}"
  if !ctx.uses.contains effect then
    emit .effectNotDeclared s!"{tick ctx.item} does not declare effect {tick effect.text}"

def envCheck (ctx : Ctx) (field : EnvField) : W Unit :=
  let bad : Bool := match ctx.site with
    | .fn _ => true
    | .query _ => field == .step
    | _ => false
  if bad then emit .envPosition s!"{tick ("(env " ++ field.text ++ ")")} is not legal in {tick ctx.item}"
  else pure ()

def recursionCheck (p : Program) (ctx : Ctx) (callee : Name) : W Unit :=
  match ctx.fnIndex, fnIndex p callee with
  | some caller, some target =>
    if caller ≤ target then
      emit .recursion s!"{tick ctx.item} calls {tick callee} before its declaration"
    else pure ()
  | _, _ => pure ()

def Ty.isFloat : Ty → Bool
  | .f64 | .f32 => true
  | _ => false

def Ty.isOrdered : Ty → Bool
  | .int | .time | .duration | .f64 | .f32 | .decimal _ => true
  | _ => false

def sameType (ok : Ty → Bool) : List Ty → Option Ty
  | t :: ts => if ok t && ts.all (· == t) then some t else none
  | [] => none

def arithType : Arith → List Ty → Option Ty
  | .mul, [.decimal a, .decimal b] => if a + b ≤ 37 then some (.decimal (a + b)) else none
  | .mul, ts => sameType (fun t => t == .int || t.isFloat) ts
  | _, ts => sameType (fun t => t == .int || t.isFloat || t matches .decimal _) ts

def lessType (ts : List Ty) : Option Ty :=
  (sameType Ty.isOrdered ts).map fun _ => .bool

def roundLegal (target source : Ty) : Bool :=
  match target, source with
  | .decimal s, .decimal a => s != a
  | .decimal _, .int => true
  | .int, .decimal _ => true
  | _, _ => false

def keepsDigits (target source : Ty) : Bool :=
  match target, source with
  | .decimal s, .decimal a => a < s
  | .decimal _, .int => true
  | .int, .decimal a => a == 0
  | _, _ => false

def roundType (target : Ty) (mode : Mode) : List Ty → Option Ty
  | [source] =>
    if roundLegal target source && (mode == .exact || !keepsDigits target source) then some target
    else none
  | _ => none

def divType (target : Ty) : List Ty → Option Ty
  | [.decimal _, .decimal _] => if target matches .decimal _ then some target else none
  | _ => none

def formResult (ctx : Ctx) (want : Option Ty) (operands : List (Option Ty))
    (rule : List Ty → Option Ty) : W (Option Ty) :=
  match operands.mapM id with
  | none => pure none
  | some ts =>
    match rule ts with
    | some t => fits ctx want (some t)
    | none => do
      mismatch ctx
      pure none

def walkType (p : Program) : Ty → W Unit
  | .named n => if isTypeName p n then pure () else unknown n
  | .option t => walkType p t
  | .result a b => do
    walkType p a
    walkType p b
  | _ => pure ()

mutual
  def walkExpr (p : Program) (ctx : Ctx) (allowOp : Bool) (want : Option Ty) :
      Expr → W (Option Ty)
    | .int _ => fits ctx want (some .int)
    | .text _ => fits ctx want (some .text)
    | .bool _ => fits ctx want (some .bool)
    | .unit => fits ctx want (some .unit)
    | .dur _ => fits ctx want (some .duration)
    | .var x =>
      match ctx.scope.find? (·.1 == x) with
      | some (_, t) => fits ctx want t
      | none => do
        unknown x
        pure none
    | .env field => do
      envCheck ctx field
      fits ctx want (some (envType field))
    | .call callee args =>
      match findFn p callee with
      | none => do
        unknown callee
        walkArgs p ctx args []
        pure none
      | some f => do
        recursionCheck p ctx callee
        if f.uses.contains .consoleOut then opCheck ctx allowOp .consoleOut
        arity ctx args.length f.params.length
        walkArgs p ctx args (f.params.map (·.ty))
        fits ctx want (some f.result)
    | .new ctor args =>
      match findCtor p ctor with
      | none => do
        unknown ctor
        walkArgs p ctx args []
        pure none
      | some (t, fields) => do
        arity ctx args.length fields.length
        walkArgs p ctx args fields
        fits ctx want (some t)
    | .get target field => do
      let t ← walkExpr p ctx false none target
      match t with
      | some (.named r) =>
        match (findRecord p r).bind fun fs => fs.find? (·.name == field) with
        | some f => fits ctx want (some f.ty)
        | none => do
          mismatch ctx
          pure none
      | some _ => do
        mismatch ctx
        pure none
      | none => pure none
    | .some inner =>
      match want with
      | some (.option t) => do
        let _ ← walkExpr p ctx false (some t) inner
        pure want
      | some _ => do
        mismatch ctx
        let _ ← walkExpr p ctx false none inner
        pure none
      | none => do
        let t ← walkExpr p ctx false none inner
        pure (t.map .option)
    | .none =>
      match want with
      | some (.option _) => pure want
      | _ => do
        mismatch ctx
        pure none
    | .ok inner =>
      match want with
      | some (.result a _) => do
        let _ ← walkExpr p ctx false (some a) inner
        pure want
      | _ => do
        mismatch ctx
        let _ ← walkExpr p ctx false none inner
        pure none
    | .err inner =>
      match want with
      | some (.result _ e) => do
        let _ ← walkExpr p ctx false (some e) inner
        pure want
      | _ => do
        mismatch ctx
        let _ ← walkExpr p ctx false none inner
        pure none
    | .arith op a b => do
      let ta ← walkExpr p ctx false none a
      let tb ← walkExpr p ctx false none b
      formResult ctx want [ta, tb] (arithType op)
    | .eq a b => do
      let t ← walkExpr p ctx false none a
      let _ ← walkExpr p ctx false t b
      fits ctx want (some .bool)
    | .lt a b => do
      let ta ← walkExpr p ctx false none a
      let tb ← walkExpr p ctx false none b
      formResult ctx want [ta, tb] lessType
    | .and a b => do
      let _ ← walkExpr p ctx false (some .bool) a
      let _ ← walkExpr p ctx false (some .bool) b
      fits ctx want (some .bool)
    | .not a => do
      let _ ← walkExpr p ctx false (some .bool) a
      fits ctx want (some .bool)
    | .op o arg => do
      opCheck ctx allowOp o.effect
      let _ ← walkExpr p ctx false (some o.arg) arg
      fits ctx want (some o.result)
    | .f64 _ => fits ctx want (some .f64)
    | .f32 _ => fits ctx want (some .f32)
    | .dec s _ => fits ctx want (some (.decimal s))
    | .div a b => do
      let ta ← walkExpr p ctx false none a
      let tb ← walkExpr p ctx false none b
      formResult ctx want [ta, tb] (sameType Ty.isFloat)
    | .sqrt a => do
      let ta ← walkExpr p ctx false none a
      formResult ctx want [ta] (sameType Ty.isFloat)
    | .fma a b c => do
      let ta ← walkExpr p ctx false none a
      let tb ← walkExpr p ctx false none b
      let tc ← walkExpr p ctx false none c
      formResult ctx want [ta, tb, tc] (sameType Ty.isFloat)
    | .fn1 _ a => do
      let ta ← walkExpr p ctx false none a
      formResult ctx want [ta] (sameType Ty.isFloat)
    | .fn2 _ a b => do
      let ta ← walkExpr p ctx false none a
      let tb ← walkExpr p ctx false none b
      formResult ctx want [ta, tb] (sameType Ty.isFloat)
    | .round t mode a => do
      walkType p t
      let ta ← walkExpr p ctx false none a
      formResult ctx want [ta] (roundType t mode)
    | .divMode t _ a b => do
      walkType p t
      let ta ← walkExpr p ctx false none a
      let tb ← walkExpr p ctx false none b
      formResult ctx want [ta, tb] (divType t)

  def walkArgs (p : Program) (ctx : Ctx) : List Expr → List Ty → W Unit
    | [], _ => pure ()
    | e :: es, t :: ts => do
      let _ ← walkExpr p ctx false (some t) e
      walkArgs p ctx es ts
    | e :: es, [] => do
      let _ ← walkExpr p ctx false none e
      walkArgs p ctx es []
end

def walkBind (ctx : Ctx) (b : Bind) (ty : Option Ty) : W Ctx :=
  match b with
  | .wild => pure ctx
  | .name x => declareLocal ctx x ty

def walkBinds (ctx : Ctx) : List Bind → List Ty → W Ctx
  | [], _ => pure ctx
  | b :: bs, t :: ts => do
    let ctx ← walkBind ctx b (some t)
    walkBinds ctx bs ts
  | b :: bs, [] => do
    let ctx ← walkBind ctx b none
    walkBinds ctx bs []

def walkPat (p : Program) (ctx : Ctx) (subject : Option Ty) : Pat → W Ctx
  | .bool _ => do
    let _ ← fits ctx subject (some .bool)
    pure ctx
  | .none => do
    match subject with
    | some (.option _) | none => pure ()
    | some _ => mismatch ctx
    pure ctx
  | .some b =>
    match subject with
    | some (.option t) => walkBind ctx b (some t)
    | some _ => do
      mismatch ctx
      walkBind ctx b none
    | none => walkBind ctx b none
  | .ok b =>
    match subject with
    | some (.result a _) => walkBind ctx b (some a)
    | some _ => do
      mismatch ctx
      walkBind ctx b none
    | none => walkBind ctx b none
  | .err b =>
    match subject with
    | some (.result _ e) => walkBind ctx b (some e)
    | some _ => do
      mismatch ctx
      walkBind ctx b none
    | none => walkBind ctx b none
  | .con c binds =>
    match findCase p c with
    | none => do
      unknown c
      walkBinds ctx binds []
    | some (owner, fields) => do
      let _ ← fits ctx subject (some owner)
      arity ctx binds.length fields.length
      walkBinds ctx binds fields

def opOnPath (ctx : Ctx) (onPath : Bool) : W Unit :=
  if onPath then wrongEnding ctx else pure ()

def walkOutcome (p : Program) (ctx : Ctx) : Option Expr → W Unit
  | some e => do
    let _ ← walkExpr p ctx false ctx.site.outcome e
  | none => pure ()

def walkStmts (p : Program) (ctx : Ctx) (pathOp : Bool) : List Stmt → W (Ctx × Bool)
  | [] => pure (ctx, pathOp)
  | .«let» x e :: rest => do
    let ty ← walkExpr p ctx true none e
    let ctx' ← declareLocal ctx x ty
    walkStmts p ctx' (pathOp || hasOp p e) rest
  | .«do» e :: rest => do
    if !isOp p e then emit .effectPosition s!"wrong operation position in {tick ctx.item}"
    let _ ← walkExpr p ctx true none e
    walkStmts p ctx (pathOp || hasOp p e) rest

mutual
  def walkBlock (p : Program) (ctx : Ctx) (pathOp : Bool) : Block → W Unit
    | .mk stmts t => do
      let (ctx', pathOp') ← walkStmts p ctx pathOp stmts
      if !ctx'.site.permits t then wrongEnding ctx'
      walkTail p ctx' pathOp' t

  def walkTail (p : Program) (ctx : Ctx) (pathOp : Bool) : Tail → W Unit
    | .value e => do
      let _ ← walkExpr p ctx false ctx.site.value e
    | .next s args o => do
      match ctx.machine.bind (findState · s) with
      | none => do
        unknown s
        walkArgs p ctx args []
      | some st => do
        arity ctx args.length st.fields.length
        walkArgs p ctx args (st.fields.map (·.ty))
      walkOutcome p ctx o
    | .stay o => walkOutcome p ctx o
    | .reject r => do
      opOnPath ctx pathOp
      match ctx.site with
      | .command name _ rejects =>
        if !rejects.contains r then
          emit .rejectNotDeclared s!"command {tick name} does not declare reject {tick r}"
      | _ => pure ()
    | .answer e => do
      opOnPath ctx (pathOp || hasOp p e)
      let _ ← walkExpr p ctx false ctx.site.answer e
    | .ignore => opOnPath ctx pathOp
    | .impossible => opOnPath ctx pathOp
    | .«match» subject arms => do
      let ty ← walkExpr p ctx false none subject
      match ty with
      | some t =>
        match ctorsOf p t with
        | some ctors =>
          if !coversOnce ctors (arms.map fun | .mk pat _ => pat.ctor) then
            emit .matchArms s!"match in {tick ctx.item} does not name each constructor once"
        | none => mismatch ctx
      | none => pure ()
      walkArms p ctx (pathOp || hasOp p subject) ty arms

  def walkArms (p : Program) (ctx : Ctx) (pathOp : Bool) (subject : Option Ty) :
      List Arm → W Unit
    | [] => pure ()
    | .mk pat body :: rest => do
      let ctx' ← walkPat p ctx subject pat
      walkBlock p ctx' pathOp body
      walkArms p ctx pathOp subject rest
end

def baseCtx (item : Name) : Ctx :=
  { item := item, fnIndex := none, machine := none, site := .unknown, uses := [], scope := [] }

def walkFields (p : Program) (ctx : Ctx) : List Param → W Ctx
  | [] => pure ctx
  | f :: fs => do
    let ctx ← declareLocal ctx f.name (some f.ty)
    walkType p f.ty
    walkFields p ctx fs

def bindParams (ctx : Ctx) : List Param → W Ctx
  | [] => pure ctx
  | x :: xs => do
    let ctx ← bindLocal ctx x.name (some x.ty)
    bindParams ctx xs

def walkFn (p : Program) (index : Nat) (f : Fn) : W Unit := do
  declare f.name
  let ctx := { baseCtx f.name with fnIndex := some index, site := .fn f.result, uses := f.uses }
  let ctx ← walkFields p ctx f.params
  walkType p f.result
  walkBlock p ctx false f.body

def walkMsg (p : Program) (m : Msg) : W Unit := do
  declare m.name
  let _ ← walkFields p (baseCtx m.name) m.params
  walkType p m.result
  match m with
  | .command _ _ _ _ (some r) => if isRole p r then pure () else unknown r
  | _ => pure ()

def walkCell (p : Program) (m : Machine) (scope : List (Name × Option Ty)) (c : Cell) : W Unit := do
  let ctx := { baseCtx m.name with machine := some m, uses := m.uses, scope := scope }
  match inputSite p m c.input with
  | none => do
    unknown c.input
    walkBlock p ctx false c.body
  | some (site, params) => do
    let ctx ← bindParams { ctx with site := site } params
    walkBlock p ctx false c.body

def walkIn (p : Program) (m : Machine) (b : In) : W Unit := do
  let scope := match findState m b.target with
    | some st => st.fields.map fun f => (f.name, some f.ty)
    | none => []
  if (findState m b.target).isNone && (findGroup m b.target).isNone then unknown b.target
  b.cells.forM (walkCell p m scope)

def walkMachine (p : Program) (m : Machine) : W Unit := do
  declare m.name
  walkType p m.key
  if (findProtocol p m.protocol).isNone then unknown m.protocol
  match findState m m.init with
  | none => unknown m.init
  | some s =>
    if !s.fields.isEmpty then
      emit .initHasFields s!"init state {tick s.name} of machine {tick m.name} has fields"
  m.states.forM fun s => do
    declare s.name
    let _ ← walkFields p (baseCtx m.name) s.fields
  m.groups.forM fun g => do
    declare g.name
    g.members.forM fun x => if (findState m x).isSome then pure () else unknown x
  m.ins.forM (walkIn p m)

def machineKey (p : Program) (m : Name) : W (Option Ty) :=
  match findMachine p m with
  | some mach => pure (some mach.key)
  | none => do
    unknown m
    pure none

mutual
  def walkXExpr (p : Program) (ctx : Ctx) (want : Option Ty) : XExpr → W (Option Ty)
    | .int _ => fits ctx want (some .int)
    | .text _ => fits ctx want (some .text)
    | .bool _ => fits ctx want (some .bool)
    | .unit => fits ctx want (some .unit)
    | .dur _ => fits ctx want (some .duration)
    | .step _ => fits ctx want (some .stepId)
    | .ticket _ => fits ctx want (some .ticket)
    | .var x =>
      if ctx.scope.any (·.1 == x) then fits ctx want (some .principal)
      else do
        unknown x
        pure none
    | .new ctor args =>
      match findCtor p ctor with
      | none => do
        unknown ctor
        walkXArgs p ctx args []
        pure none
      | some (t, fields) => do
        arity ctx args.length fields.length
        walkXArgs p ctx args fields
        fits ctx want (some t)
    | .some inner =>
      match want with
      | some (.option t) => do
        let _ ← walkXExpr p ctx (some t) inner
        pure want
      | some _ => do
        mismatch ctx
        let _ ← walkXExpr p ctx none inner
        pure none
      | none => do
        let t ← walkXExpr p ctx none inner
        pure (t.map .option)
    | .none =>
      match want with
      | some (.option _) => pure want
      | _ => do
        mismatch ctx
        pure none
    | .ok inner =>
      match want with
      | some (.result a _) => do
        let _ ← walkXExpr p ctx (some a) inner
        pure want
      | _ => do
        mismatch ctx
        let _ ← walkXExpr p ctx none inner
        pure none
    | .err inner =>
      match want with
      | some (.result _ e) => do
        let _ ← walkXExpr p ctx (some e) inner
        pure want
      | _ => do
        mismatch ctx
        let _ ← walkXExpr p ctx none inner
        pure none
    | .f64 _ => fits ctx want (some .f64)
    | .f32 _ => fits ctx want (some .f32)
    | .dec s _ => fits ctx want (some (.decimal s))
    | .time _ => fits ctx want (some .time)
    | .principal _ => fits ctx want (some .principal)
    | .stepOf m k _ _ => do
      let key ← machineKey p m
      let _ ← walkXExpr p ctx key k
      fits ctx want (some .stepId)
    | .ticketOf m k _ _ _ => do
      let key ← machineKey p m
      let _ ← walkXExpr p ctx key k
      fits ctx want (some .ticket)

  def walkXArgs (p : Program) (ctx : Ctx) : List XExpr → List Ty → W Unit
    | [], _ => pure ()
    | x :: xs, t :: ts => do
      let _ ← walkXExpr p ctx (some t) x
      walkXArgs p ctx xs ts
    | x :: xs, [] => do
      let _ ← walkXExpr p ctx none x
      walkXArgs p ctx xs []
end

mutual
  def refersToInstance : XExpr → Bool
    | .step _ => true
    | .ticket _ => true
    | .new _ args => anyRefersToInstance args
    | .some x => refersToInstance x
    | .ok x => refersToInstance x
    | .err x => refersToInstance x
    | .stepOf _ k _ _ => refersToInstance k
    | .ticketOf _ k _ _ _ => refersToInstance k
    | .int _ | .text _ | .bool _ | .unit | .dur _ | .var _ | .none => false
    | .f64 _ | .f32 _ | .dec _ _ | .time _ | .principal _ => false

  def anyRefersToInstance : List XExpr → Bool
    | [] => false
    | x :: xs => refersToInstance x || anyRefersToInstance xs
end

def walkConstant (p : Program) (ctx : Ctx) (want : Option Ty) (x : XExpr) : W Unit := do
  let _ ← walkXExpr p ctx want x
  if refersToInstance x then mismatch ctx

def walkRecordFields (p : Program) (ctx : Ctx) :
    List Name → List (Param × Option XExpr) → W Unit
  | _, [] => pure ()
  | seen, (f, init) :: fs => do
    if seen.contains f.name then duplicate f.name
    walkType p f.ty
    match init with
    | some x => walkConstant p ctx (some f.ty) x
    | none => pure ()
    walkRecordFields p ctx (f.name :: seen) fs

def walkFact (p : Program) (ctx : Ctx) (site : Site) : Fact → W Unit
  | .outcome x => do
    match site with
    | .command _ result _ =>
      let _ ← walkXExpr p ctx (some result) x
    | .unknown =>
      let _ ← walkXExpr p ctx none x
    | _ => do
      mismatch ctx
      let _ ← walkXExpr p ctx none x
  | .answer x => do
    match site with
    | .query result =>
      let _ ← walkXExpr p ctx (some result) x
    | .unknown =>
      let _ ← walkXExpr p ctx none x
    | _ => do
      mismatch ctx
      let _ ← walkXExpr p ctx none x
  | .state s args =>
    match ctx.machine.bind (findState · s) with
    | none => do
      unknown s
      walkXArgs p ctx args []
    | some st => do
      arity ctx args.length st.fields.length
      walkXArgs p ctx args (st.fields.map (·.ty))
  | _ => pure ()

def walkLine (p : Program) (ctx : Ctx) : Line → W Unit
  | .send a input args facts => do
    if !ctx.scope.any (·.1 == a) then unknown a
    let site ← match ctx.machine.bind (findMsg p · input) with
      | some (.command name params result rejects _) => do
        arity ctx args.length params.length
        walkXArgs p ctx args (params.map (·.ty))
        pure (Site.command name result rejects)
      | some (.query _ params result) => do
        arity ctx args.length params.length
        walkXArgs p ctx args (params.map (·.ty))
        pure (Site.query result)
      | none => do
        unknown input
        walkXArgs p ctx args []
        pure Site.unknown
    facts.forM (walkFact p ctx site)
  | .fire t facts => do
    match ctx.machine with
    | some m => if m.uses.contains .timer then pure () else unknown firedName
    | none => pure ()
    let _ ← walkXExpr p ctx (some .ticket) t
    facts.forM (walkFact p ctx .fired)

def walkActors (p : Program) (ctx : Ctx) : List Actor → W Ctx
  | [] => pure ctx
  | a :: rest => do
    let ctx ← declareLocal ctx a.name (some .principal)
    a.roles.forM fun r => if isRole p r then pure () else unknown r
    walkActors p ctx rest

def walkExample (p : Program) (ex : Example) : W Unit := do
  declare ex.name
  let m := findMachine p ex.machine
  if m.isNone then unknown ex.machine
  let ctx := { baseCtx ex.name with machine := m }
  walkConstant p ctx (m.map (·.key)) ex.key
  let ctx ← walkActors p ctx ex.actors
  ex.lines.forM (walkLine p ctx)

def walkDeployment (p : Program) (d : Deployment) : W Unit := do
  declare d.name
  match findFn p d.entry with
  | none => unknown d.entry
  | some f =>
    if !f.params.isEmpty || !(f.result == .unit) then
      emit .badEntry s!"deployment {tick d.name} has no legal entry"
  if (← get).deployments > 0 then
    emit .badEntry s!"deployment {tick d.name} has no legal entry"
  modify fun w => { w with deployments := w.deployments + 1 }

def walkItem (p : Program) (index : Nat) : Item → W Unit
  | .newtype n t => do
    declare n
    walkType p t
  | .record r fields inits => do
    declare r
    walkRecordFields p (baseCtx r) [] (fields.map (·, none) ++ inits.map fun (f, x) => (f, some x))
  | .enum e variants => do
    declare e
    variants.forM fun v => do
      declare v.name
      v.fields.forM (walkType p)
  | .role r => declare r
  | .fn f => walkFn p index f
  | .protocol q => do
    declare q.name
    q.msgs.forM (walkMsg p)
  | .machine m => walkMachine p m
  | .deployment d => walkDeployment p d
  | .«example» ex => walkExample p ex
  | .decode n t _ expect => do
    declare n
    walkType p t
    match expect with
    | some x => walkConstant p (baseCtx n) (some t) x
    | none => pure ()

def walkItems (p : Program) : Nat → List Item → W Unit
  | _, [] => pure ()
  | index, it :: rest => do
    walkItem p index it
    walkItems p (index + 1) rest

def walkProgram (p : Program) : List Diag :=
  let start : Walk := { diags := #[], declared := [], locals := [], deployments := 0 }
  ((walkItems p 0 p.items).run start).2.diags.toList

def pairs (p : Program) (m : Machine) : List (Name × Name) :=
  (m.states.map (·.name)).flatMap fun s => (inputNames p m).map fun i => (s, i)

def missingCells (p : Program) (m : Machine) : List (Name × Name) :=
  (pairs p m).filter fun (s, i) => (findCell m s i).isNone

def duplicateCells (p : Program) (m : Machine) : List (Name × Name) :=
  (pairs p m).filter fun (s, i) => (cellsFor m s i).length ≥ 2

def cellDiags (p : Program) : Item → List Diag
  | .machine m =>
    (duplicateCells p m).map (fun (s, i) =>
      { code := .duplicateCell, message := s!"machine {tick m.name} has two cells for ({s}, {i})" }) ++
    (missingCells p m).map (fun (s, i) =>
      { code := .missingCell, message := s!"machine {tick m.name} has no cell for ({s}, {i})" })
  | _ => []

inductive Node where
  | named (name : Name)
  | stepId
  | ticket
  deriving BEq

def Node.text : Node → String
  | .named n => n
  | .stepId => "StepId"
  | .ticket => "Ticket"

def tyNodes : Ty → List Node
  | .named n => [.named n]
  | .option t => tyNodes t
  | .result a b => tyNodes a ++ tyNodes b
  | .stepId => [.stepId]
  | .ticket => [.ticket]
  | _ => []

def itemNodes (p : Program) (n : Name) : List Node :=
  p.items.flatMap fun
    | .record r fields inits =>
      if r == n then (fields ++ inits.map (·.1)).flatMap fun f => tyNodes f.ty else []
    | .enum e variants => if e == n then variants.flatMap fun v => v.fields.flatMap tyNodes else []
    | .newtype m t => if m == n then tyNodes t else []
    | _ => []

def keyNodes (p : Program) : List Node :=
  p.items.flatMap fun
    | .machine m => tyNodes m.key
    | _ => []

def edges (p : Program) : Node → List Node
  | .named n => itemNodes p n
  | .stepId => keyNodes p
  | .ticket => keyNodes p

def typeNames (p : Program) : List Name :=
  p.items.filterMap fun
    | .record r _ _ => some r
    | .enum e _ => some e
    | .newtype n _ => some n
    | _ => none

def nodeCount (p : Program) : Nat :=
  (typeNames p).length + 2

def addNew (seen : List Node) : List Node → List Node
  | [] => []
  | x :: xs => if seen.contains x then addNew seen xs else x :: addNew (x :: seen) xs

def reach (p : Program) : Nat → List Node → List Node → List Node
  | 0, seen, _ => seen
  | k + 1, seen, frontier =>
    match addNew seen (frontier.flatMap (edges p)) with
    | [] => seen
    | next => reach p k (seen ++ next) next

def reachFrom (p : Program) (start : List Node) : List Node :=
  let first := addNew [] start
  reach p (nodeCount p) first first

def reachesSelf (p : Program) (n : Node) : Bool :=
  (reachFrom p (edges p n)).contains n

def reachesSpecial (p : Program) (start : List Node) : Bool :=
  let ns := reachFrom p start
  ns.contains .stepId || ns.contains .ticket

def firstSpecial (p : Program) : Nat → Ty → Option Node
  | _, .stepId => some .stepId
  | _, .ticket => some .ticket
  | k, .option t => firstSpecial p k t
  | k, .result a b => (firstSpecial p k a).orElse fun _ => firstSpecial p k b
  | 0, .named _ => none
  | k + 1, .named n =>
    if reachesSpecial p (edges p (.named n)) then
      p.items.findSome? fun
        | .record r fields inits =>
          if r == n then (fields ++ inits.map (·.1)).findSome? fun f => firstSpecial p k f.ty else none
        | .enum e variants =>
          if e == n then variants.findSome? fun v => v.fields.findSome? (firstSpecial p k) else none
        | .newtype m t => if m == n then firstSpecial p k t else none
        | _ => none
    else none
  | _, _ => none

def recursiveTypeDiags (p : Program) : List Diag :=
  let message (n : Node) : Diag :=
    { code := .recursiveType, message := s!"type {tick n.text} contains itself" }
  match (typeNames p).find? fun n => reachesSelf p (.named n) with
  | some n => [message (.named n)]
  | none =>
    let keyLoop := p.items.findSome? fun
      | .machine m =>
        if reachesSpecial p (tyNodes m.key) then firstSpecial p (nodeCount p) m.key
        else none
      | _ => none
    match keyLoop with
    | some n => [message n]
    | none => []

def layoutDiag (t : Name) : Diag :=
  { code := .layoutLimit, message := s!"type {tick t} exceeds the layout limits" }

def layoutDiags : Item → List Diag
  | .record r fields inits => if fields.length + inits.length > 65535 then [layoutDiag r] else []
  | .enum e variants => if variants.length > 256 then [layoutDiag e] else []
  | _ => []

def diagnose (p : Program) : List Diag :=
  walkProgram p ++ p.items.flatMap layoutDiags ++ recursiveTypeDiags p ++
    p.items.flatMap (cellDiags p)

def select (ds : List Diag) : List Diag :=
  let best := ds.foldl (fun r d => min r d.code.rank) Code.badEntry.rank
  let firsts := ds.filter (·.code.rank == best)
  if best == Code.missingCell.rank then firsts else firsts.take 1

def check (p : Program) : Except (List Diag) Unit :=
  match diagnose p with
  | [] => .ok ()
  | ds => .error (select ds)

end Borsuk
