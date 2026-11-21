use crate::ir::{
    Actor, Arith, Arm, Bind, Block, Cell, Deployment, Effect, EnvField, Example, Expr, FIRED_NAME,
    Fact, Fn, Group, In, Item, Line, Machine, Mode, Msg, Name, Op, Param, Pat, Program, Stmt, Tail,
    Ty, Variant, XExpr, cells_for, find_cell, find_fn, find_machine, find_msg, find_protocol,
    find_state, fired_params, input_names,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Code {
    Parse,
    UnknownName,
    DuplicateName,
    Recursion,
    WrongEnding,
    TypeMismatch,
    MatchArms,
    EffectPosition,
    EffectNotDeclared,
    EnvPosition,
    InitHasFields,
    DuplicateCell,
    MissingCell,
    RejectNotDeclared,
    BadEntry,
    RecursiveType,
    LayoutLimit,
}

impl Code {
    pub fn rank(self) -> u64 {
        match self {
            Code::Parse => 0,
            Code::UnknownName => 1,
            Code::DuplicateName => 2,
            Code::Recursion => 3,
            Code::RecursiveType => 4,
            Code::LayoutLimit => 5,
            Code::WrongEnding => 6,
            Code::TypeMismatch => 7,
            Code::MatchArms => 8,
            Code::EffectPosition => 9,
            Code::EffectNotDeclared => 10,
            Code::EnvPosition => 11,
            Code::InitHasFields => 12,
            Code::DuplicateCell => 13,
            Code::MissingCell => 14,
            Code::RejectNotDeclared => 15,
            Code::BadEntry => 16,
        }
    }

    pub fn text(self) -> &'static str {
        match self {
            Code::Parse => "parse",
            Code::UnknownName => "unknown-name",
            Code::DuplicateName => "duplicate-name",
            Code::Recursion => "recursion",
            Code::WrongEnding => "wrong-ending",
            Code::TypeMismatch => "type-mismatch",
            Code::MatchArms => "match-arms",
            Code::EffectPosition => "effect-position",
            Code::EffectNotDeclared => "effect-not-declared",
            Code::EnvPosition => "env-position",
            Code::InitHasFields => "init-has-fields",
            Code::DuplicateCell => "duplicate-cell",
            Code::MissingCell => "missing-cell",
            Code::RejectNotDeclared => "reject-not-declared",
            Code::BadEntry => "bad-entry",
            Code::RecursiveType => "recursive-type",
            Code::LayoutLimit => "layout-limit",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diag {
    pub code: Code,
    pub message: String,
}

pub fn tick(s: &str) -> String {
    format!("`{s}`")
}

impl Effect {
    pub fn text(self) -> &'static str {
        match self {
            Effect::ConsoleOut => "ConsoleOut",
            Effect::Timer => "Timer",
        }
    }
}

impl EnvField {
    pub fn text(self) -> &'static str {
        match self {
            EnvField::Now => "now",
            EnvField::Step => "step",
            EnvField::Sender => "sender",
            EnvField::Deadline => "deadline",
        }
    }
}

pub fn find_record<'a>(p: &'a Program, name: &str) -> Option<Vec<&'a Param>> {
    p.items.iter().find_map(|item| match item {
        Item::Record(r, fields, inits) if r == name => {
            Some(fields.iter().chain(inits.iter().map(|(f, _)| f)).collect())
        }
        _ => None,
    })
}

pub fn find_enum<'a>(p: &'a Program, name: &str) -> Option<&'a [Variant]> {
    p.items.iter().find_map(|item| match item {
        Item::Enum(e, variants) if e == name => Some(variants.as_slice()),
        _ => None,
    })
}

pub fn find_newtype<'a>(p: &'a Program, name: &str) -> Option<&'a Ty> {
    p.items.iter().find_map(|item| match item {
        Item::Newtype(n, t) if n == name => Some(t),
        _ => None,
    })
}

pub fn is_role(p: &Program, name: &str) -> bool {
    p.items.iter().any(|item| match item {
        Item::Role(r) => r == name,
        _ => false,
    })
}

pub fn is_type_name(p: &Program, name: &str) -> bool {
    p.items.iter().any(|item| match item {
        Item::Newtype(n, _) => n == name,
        Item::Record(r, _, _) => r == name,
        Item::Enum(e, _) => e == name,
        _ => false,
    })
}

pub fn find_ctor(p: &Program, name: &str) -> Option<(Ty, Vec<Ty>)> {
    p.items.iter().find_map(|item| match item {
        Item::Newtype(n, t) if n == name => Some((Ty::Named(n.clone()), vec![t.clone()])),
        Item::Record(r, fields, inits) if r == name => Some((
            Ty::Named(r.clone()),
            fields
                .iter()
                .chain(inits.iter().map(|(f, _)| f))
                .map(|f| f.ty.clone())
                .collect(),
        )),
        Item::Enum(e, variants) => variants
            .iter()
            .find(|v| v.name == name)
            .map(|v| (Ty::Named(e.clone()), v.fields.clone())),
        _ => None,
    })
}

pub fn find_case(p: &Program, name: &str) -> Option<(Ty, Vec<Ty>)> {
    p.items.iter().find_map(|item| match item {
        Item::Newtype(n, t) if n == name => Some((Ty::Named(n.clone()), vec![t.clone()])),
        Item::Enum(e, variants) => variants
            .iter()
            .find(|v| v.name == name)
            .map(|v| (Ty::Named(e.clone()), v.fields.clone())),
        _ => None,
    })
}

pub fn fn_index(p: &Program, name: &str) -> Option<usize> {
    p.items.iter().position(|item| match item {
        Item::Fn(f) => f.name == name,
        _ => false,
    })
}

pub fn find_group<'a>(m: &'a Machine, name: &str) -> Option<&'a Group> {
    m.groups.iter().find(|g| g.name == name)
}

pub fn uses_console(p: &Program, name: &str) -> bool {
    match find_fn(p, name) {
        Some(f) => f.uses.contains(&Effect::ConsoleOut),
        None => false,
    }
}

pub fn is_op(p: &Program, e: &Expr) -> bool {
    match e {
        Expr::Op(_, _) => true,
        Expr::Call(f, _) => uses_console(p, f),
        _ => false,
    }
}

pub fn has_op(p: &Program, e: &Expr) -> bool {
    match e {
        Expr::Int(_)
        | Expr::Text(_)
        | Expr::Bool(_)
        | Expr::Unit
        | Expr::Dur(_)
        | Expr::Var(_)
        | Expr::Env(_)
        | Expr::None => false,
        Expr::F64(_) | Expr::F32(_) | Expr::Dec(_, _) => false,
        Expr::Call(f, args) => uses_console(p, f) || has_op_any(p, args),
        Expr::New(_, args) => has_op_any(p, args),
        Expr::Get(e, _) => has_op(p, e),
        Expr::Some(e) => has_op(p, e),
        Expr::Ok(e) => has_op(p, e),
        Expr::Err(e) => has_op(p, e),
        Expr::Not(e) => has_op(p, e),
        Expr::Arith(_, a, b) => has_op(p, a) || has_op(p, b),
        Expr::Eq(a, b) => has_op(p, a) || has_op(p, b),
        Expr::Lt(a, b) => has_op(p, a) || has_op(p, b),
        Expr::And(a, b) => has_op(p, a) || has_op(p, b),
        Expr::Op(_, _) => true,
        Expr::Div(a, b) => has_op(p, a) || has_op(p, b),
        Expr::Sqrt(a) => has_op(p, a),
        Expr::Fma(a, b, c) => has_op(p, a) || has_op(p, b) || has_op(p, c),
        Expr::Fn1(_, a) => has_op(p, a),
        Expr::Fn2(_, a, b) => has_op(p, a) || has_op(p, b),
        Expr::Round(_, _, a) => has_op(p, a),
        Expr::DivMode(_, _, a, b) => has_op(p, a) || has_op(p, b),
    }
}

pub fn has_op_any(p: &Program, es: &[Expr]) -> bool {
    match es {
        [] => false,
        [e, rest @ ..] => has_op(p, e) || has_op_any(p, rest),
    }
}

pub fn env_type(field: EnvField) -> Ty {
    match field {
        EnvField::Now => Ty::Time,
        EnvField::Step => Ty::StepId,
        EnvField::Sender => Ty::Principal,
        EnvField::Deadline => Ty::Time,
    }
}

impl Op {
    pub fn effect(self) -> Effect {
        match self {
            Op::Print => Effect::ConsoleOut,
            Op::After => Effect::Timer,
            Op::Cancel => Effect::Timer,
        }
    }

    pub fn arg(self) -> Ty {
        match self {
            Op::Print => Ty::Text,
            Op::After => Ty::Duration,
            Op::Cancel => Ty::Ticket,
        }
    }

    pub fn result(self) -> Ty {
        match self {
            Op::Print => Ty::Unit,
            Op::After => Ty::Ticket,
            Op::Cancel => Ty::Unit,
        }
    }
}

pub fn ctors_of(p: &Program, t: &Ty) -> Option<Vec<Name>> {
    match t {
        Ty::Bool => Some(vec!["true".to_string(), "false".to_string()]),
        Ty::Option(_) => Some(vec!["none".to_string(), "some".to_string()]),
        Ty::Result(_, _) => Some(vec!["ok".to_string(), "err".to_string()]),
        Ty::Named(n) => match find_enum(p, n) {
            Some(variants) => Some(variants.iter().map(|v| v.name.clone()).collect()),
            None => find_newtype(p, n).map(|_| vec![n.clone()]),
        },
        _ => None,
    }
}

impl Pat {
    pub fn ctor(&self) -> Name {
        match self {
            Pat::Bool(true) => "true".to_string(),
            Pat::Bool(false) => "false".to_string(),
            Pat::None => "none".to_string(),
            Pat::Some(_) => "some".to_string(),
            Pat::Ok(_) => "ok".to_string(),
            Pat::Err(_) => "err".to_string(),
            Pat::Con(c, _) => c.clone(),
        }
    }
}

pub fn covers_once(ctors: &[Name], names: &[Name]) -> bool {
    ctors.len() == names.len()
        && ctors
            .iter()
            .all(|c| names.iter().filter(|x| *x == c).count() == 1)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Site {
    Fn(Ty),
    Command(Name, Ty, Vec<Name>),
    Query(Ty),
    Fired,
    Unknown,
}

impl Site {
    pub fn permits(&self, t: &Tail) -> bool {
        match (self, t) {
            (Site::Unknown, _) => true,
            (_, Tail::Match(_, _)) => true,
            (Site::Fn(_), Tail::Value(_)) => true,
            (Site::Command(..), Tail::Next(_, _, o)) => o.is_some(),
            (Site::Command(..), Tail::Stay(o)) => o.is_some(),
            (Site::Command(..), Tail::Reject(_)) => true,
            (Site::Command(..), Tail::Impossible) => true,
            (Site::Query(_), Tail::Answer(_)) => true,
            (Site::Query(_), Tail::Impossible) => true,
            (Site::Fired, Tail::Next(_, _, o)) => o.is_none(),
            (Site::Fired, Tail::Stay(o)) => o.is_none(),
            (Site::Fired, Tail::Ignore) => true,
            (Site::Fired, Tail::Impossible) => true,
            (_, _) => false,
        }
    }

    pub fn outcome(&self) -> Option<Ty> {
        match self {
            Site::Command(_, result, _) => Some(result.clone()),
            _ => None,
        }
    }

    pub fn answer(&self) -> Option<Ty> {
        match self {
            Site::Query(result) => Some(result.clone()),
            _ => None,
        }
    }

    pub fn value(&self) -> Option<Ty> {
        match self {
            Site::Fn(result) => Some(result.clone()),
            _ => None,
        }
    }
}

pub fn input_site(p: &Program, m: &Machine, input: &str) -> Option<(Site, Vec<Param>)> {
    match find_msg(p, m, input) {
        Some(Msg::Command {
            name,
            params,
            result,
            rejects,
            ..
        }) => Some((
            Site::Command(name.clone(), result.clone(), rejects.clone()),
            params.clone(),
        )),
        Some(Msg::Query { params, result, .. }) => {
            Some((Site::Query(result.clone()), params.clone()))
        }
        None => {
            if input == FIRED_NAME && m.uses.contains(&Effect::Timer) {
                Some((Site::Fired, fired_params()))
            } else {
                None
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct Ctx<'a> {
    pub item: Name,
    pub fn_index: Option<usize>,
    pub machine: Option<&'a Machine>,
    pub site: Site,
    pub uses: Vec<Effect>,
    pub scope: Vec<(Name, Option<Ty>)>,
}

#[derive(Clone, Debug)]
pub struct Walk {
    pub diags: Vec<Diag>,
    pub declared: Vec<Name>,
    pub locals: Vec<Name>,
    pub deployments: u64,
}

pub fn emit(w: &mut Walk, code: Code, message: String) {
    w.diags.push(Diag { code, message });
}

pub fn unknown(w: &mut Walk, name: &str) {
    emit(
        w,
        Code::UnknownName,
        format!("name {} is not declared", tick(name)),
    );
}

pub fn duplicate(w: &mut Walk, name: &str) {
    emit(
        w,
        Code::DuplicateName,
        format!("name {} is declared twice", tick(name)),
    );
}

pub fn mismatch(w: &mut Walk, ctx: &Ctx) {
    emit(
        w,
        Code::TypeMismatch,
        format!("type mismatch in {}", tick(&ctx.item)),
    );
}

pub fn wrong_ending(w: &mut Walk, ctx: &Ctx) {
    emit(
        w,
        Code::WrongEnding,
        format!("wrong ending in {}", tick(&ctx.item)),
    );
}

pub fn declare(w: &mut Walk, name: &str) {
    if w.declared.iter().any(|x| x == name) || w.locals.iter().any(|x| x == name) {
        duplicate(w, name);
    }
    w.declared.push(name.to_string());
}

pub fn declare_local(w: &mut Walk, ctx: &mut Ctx, name: &str, ty: Option<Ty>) {
    if w.declared.iter().any(|x| x == name) || ctx.scope.iter().any(|(x, _)| x == name) {
        duplicate(w, name);
    }
    w.locals.push(name.to_string());
    ctx.scope.push((name.to_string(), ty));
}

pub fn bind_local(w: &mut Walk, ctx: &mut Ctx, name: &str, ty: Option<Ty>) {
    if ctx.scope.iter().any(|(x, _)| x == name) {
        duplicate(w, name);
    }
    ctx.scope.push((name.to_string(), ty));
}

pub fn fits(w: &mut Walk, ctx: &Ctx, want: Option<Ty>, got: Option<Ty>) -> Option<Ty> {
    match (want, got) {
        (Some(a), Some(g)) => {
            if a != g {
                mismatch(w, ctx);
            }
            Some(g)
        }
        (_, got) => got,
    }
}

pub fn arity(w: &mut Walk, ctx: &Ctx, got: usize, want: usize) {
    if got != want {
        mismatch(w, ctx);
    }
}

pub fn op_check(w: &mut Walk, ctx: &Ctx, allow_op: bool, effect: Effect) {
    if !allow_op {
        emit(
            w,
            Code::EffectPosition,
            format!("wrong operation position in {}", tick(&ctx.item)),
        );
    }
    if !ctx.uses.contains(&effect) {
        emit(
            w,
            Code::EffectNotDeclared,
            format!(
                "{} does not declare effect {}",
                tick(&ctx.item),
                tick(effect.text())
            ),
        );
    }
}

pub fn env_check(w: &mut Walk, ctx: &Ctx, field: EnvField) {
    let bad = match ctx.site {
        Site::Fn(_) => true,
        Site::Query(_) => field == EnvField::Step,
        _ => false,
    };
    if bad {
        emit(
            w,
            Code::EnvPosition,
            format!(
                "{} is not legal in {}",
                tick(&format!("(env {})", field.text())),
                tick(&ctx.item)
            ),
        );
    }
}

pub fn recursion_check(w: &mut Walk, p: &Program, ctx: &Ctx, callee: &str) {
    if let (Some(caller), Some(target)) = (ctx.fn_index, fn_index(p, callee))
        && caller <= target
    {
        emit(
            w,
            Code::Recursion,
            format!(
                "{} calls {} before its declaration",
                tick(&ctx.item),
                tick(callee)
            ),
        );
    }
}

impl Ty {
    pub fn is_float(&self) -> bool {
        matches!(self, Ty::F64 | Ty::F32)
    }

    pub fn is_ordered(&self) -> bool {
        matches!(
            self,
            Ty::Int | Ty::Time | Ty::Duration | Ty::F64 | Ty::F32 | Ty::Decimal(_)
        )
    }
}

pub fn same_type(ok: fn(&Ty) -> bool, ts: &[Ty]) -> Option<Ty> {
    match ts {
        [t, rest @ ..] => {
            if ok(t) && rest.iter().all(|x| x == t) {
                Some(t.clone())
            } else {
                None
            }
        }
        [] => None,
    }
}

pub fn arith_type(op: Arith, ts: &[Ty]) -> Option<Ty> {
    match (op, ts) {
        (Arith::Mul, [Ty::Decimal(a), Ty::Decimal(b)]) => {
            a.checked_add(*b).filter(|s| *s <= 37).map(Ty::Decimal)
        }
        (Arith::Mul, ts) => same_type(|t| *t == Ty::Int || t.is_float(), ts),
        (_, ts) => same_type(
            |t| *t == Ty::Int || t.is_float() || matches!(t, Ty::Decimal(_)),
            ts,
        ),
    }
}

pub fn less_type(ts: &[Ty]) -> Option<Ty> {
    same_type(Ty::is_ordered, ts).map(|_| Ty::Bool)
}

pub fn round_legal(target: &Ty, source: &Ty) -> bool {
    match (target, source) {
        (Ty::Decimal(s), Ty::Decimal(a)) => s != a,
        (Ty::Decimal(_), Ty::Int) => true,
        (Ty::Int, Ty::Decimal(_)) => true,
        (_, _) => false,
    }
}

pub fn keeps_digits(target: &Ty, source: &Ty) -> bool {
    match (target, source) {
        (Ty::Decimal(s), Ty::Decimal(a)) => a < s,
        (Ty::Decimal(_), Ty::Int) => true,
        (Ty::Int, Ty::Decimal(a)) => *a == 0,
        (_, _) => false,
    }
}

pub fn round_type(target: &Ty, mode: Mode, ts: &[Ty]) -> Option<Ty> {
    match ts {
        [source] => {
            if round_legal(target, source) && (mode == Mode::Exact || !keeps_digits(target, source))
            {
                Some(target.clone())
            } else {
                None
            }
        }
        _ => None,
    }
}

pub fn div_type(target: &Ty, ts: &[Ty]) -> Option<Ty> {
    match ts {
        [Ty::Decimal(_), Ty::Decimal(_)] => {
            if matches!(target, Ty::Decimal(_)) {
                Some(target.clone())
            } else {
                None
            }
        }
        _ => None,
    }
}

pub fn form_result(
    w: &mut Walk,
    ctx: &Ctx,
    want: Option<Ty>,
    operands: Vec<Option<Ty>>,
    rule: impl FnOnce(&[Ty]) -> Option<Ty>,
) -> Option<Ty> {
    match operands.into_iter().collect::<Option<Vec<Ty>>>() {
        None => None,
        Some(ts) => match rule(&ts) {
            Some(t) => fits(w, ctx, want, Some(t)),
            None => {
                mismatch(w, ctx);
                None
            }
        },
    }
}

pub fn walk_type(w: &mut Walk, p: &Program, t: &Ty) {
    match t {
        Ty::Named(n) => {
            if !is_type_name(p, n) {
                unknown(w, n);
            }
        }
        Ty::Option(t) => walk_type(w, p, t),
        Ty::Result(a, b) => {
            walk_type(w, p, a);
            walk_type(w, p, b);
        }
        _ => {}
    }
}

pub fn walk_expr(
    w: &mut Walk,
    p: &Program,
    ctx: &Ctx,
    allow_op: bool,
    want: Option<Ty>,
    e: &Expr,
) -> Option<Ty> {
    match e {
        Expr::Int(_) => fits(w, ctx, want, Some(Ty::Int)),
        Expr::Text(_) => fits(w, ctx, want, Some(Ty::Text)),
        Expr::Bool(_) => fits(w, ctx, want, Some(Ty::Bool)),
        Expr::Unit => fits(w, ctx, want, Some(Ty::Unit)),
        Expr::Dur(_) => fits(w, ctx, want, Some(Ty::Duration)),
        Expr::Var(x) => match ctx.scope.iter().rev().find(|(n, _)| n == x) {
            Some((_, t)) => fits(w, ctx, want, t.clone()),
            None => {
                unknown(w, x);
                None
            }
        },
        Expr::Env(field) => {
            env_check(w, ctx, *field);
            fits(w, ctx, want, Some(env_type(*field)))
        }
        Expr::Call(callee, args) => match find_fn(p, callee) {
            None => {
                unknown(w, callee);
                walk_args(w, p, ctx, args, &[]);
                None
            }
            Some(f) => {
                recursion_check(w, p, ctx, callee);
                if f.uses.contains(&Effect::ConsoleOut) {
                    op_check(w, ctx, allow_op, Effect::ConsoleOut);
                }
                arity(w, ctx, args.len(), f.params.len());
                let tys: Vec<Ty> = f.params.iter().map(|x| x.ty.clone()).collect();
                walk_args(w, p, ctx, args, &tys);
                fits(w, ctx, want, Some(f.result.clone()))
            }
        },
        Expr::New(ctor, args) => match find_ctor(p, ctor) {
            None => {
                unknown(w, ctor);
                walk_args(w, p, ctx, args, &[]);
                None
            }
            Some((t, fields)) => {
                arity(w, ctx, args.len(), fields.len());
                walk_args(w, p, ctx, args, &fields);
                fits(w, ctx, want, Some(t))
            }
        },
        Expr::Get(target, field) => {
            let t = walk_expr(w, p, ctx, false, None, target);
            match t {
                Some(Ty::Named(r)) => {
                    match find_record(p, &r)
                        .and_then(|fs| fs.into_iter().find(|f| f.name == *field))
                    {
                        Some(f) => fits(w, ctx, want, Some(f.ty.clone())),
                        None => {
                            mismatch(w, ctx);
                            None
                        }
                    }
                }
                Some(_) => {
                    mismatch(w, ctx);
                    None
                }
                None => None,
            }
        }
        Expr::Some(inner) => match &want {
            Some(Ty::Option(t)) => {
                walk_expr(w, p, ctx, false, Some((**t).clone()), inner);
                want
            }
            Some(_) => {
                mismatch(w, ctx);
                walk_expr(w, p, ctx, false, None, inner);
                None
            }
            None => {
                let t = walk_expr(w, p, ctx, false, None, inner);
                t.map(|t| Ty::Option(Box::new(t)))
            }
        },
        Expr::None => match &want {
            Some(Ty::Option(_)) => want,
            _ => {
                mismatch(w, ctx);
                None
            }
        },
        Expr::Ok(inner) => match &want {
            Some(Ty::Result(a, _)) => {
                walk_expr(w, p, ctx, false, Some((**a).clone()), inner);
                want
            }
            _ => {
                mismatch(w, ctx);
                walk_expr(w, p, ctx, false, None, inner);
                None
            }
        },
        Expr::Err(inner) => match &want {
            Some(Ty::Result(_, e)) => {
                walk_expr(w, p, ctx, false, Some((**e).clone()), inner);
                want
            }
            _ => {
                mismatch(w, ctx);
                walk_expr(w, p, ctx, false, None, inner);
                None
            }
        },
        Expr::Arith(op, a, b) => {
            let ta = walk_expr(w, p, ctx, false, None, a);
            let tb = walk_expr(w, p, ctx, false, None, b);
            form_result(w, ctx, want, vec![ta, tb], |ts| arith_type(*op, ts))
        }
        Expr::Eq(a, b) => {
            let t = walk_expr(w, p, ctx, false, None, a);
            walk_expr(w, p, ctx, false, t, b);
            fits(w, ctx, want, Some(Ty::Bool))
        }
        Expr::Lt(a, b) => {
            let ta = walk_expr(w, p, ctx, false, None, a);
            let tb = walk_expr(w, p, ctx, false, None, b);
            form_result(w, ctx, want, vec![ta, tb], less_type)
        }
        Expr::And(a, b) => {
            walk_expr(w, p, ctx, false, Some(Ty::Bool), a);
            walk_expr(w, p, ctx, false, Some(Ty::Bool), b);
            fits(w, ctx, want, Some(Ty::Bool))
        }
        Expr::Not(a) => {
            walk_expr(w, p, ctx, false, Some(Ty::Bool), a);
            fits(w, ctx, want, Some(Ty::Bool))
        }
        Expr::Op(o, arg) => {
            op_check(w, ctx, allow_op, o.effect());
            walk_expr(w, p, ctx, false, Some(o.arg()), arg);
            fits(w, ctx, want, Some(o.result()))
        }
        Expr::F64(_) => fits(w, ctx, want, Some(Ty::F64)),
        Expr::F32(_) => fits(w, ctx, want, Some(Ty::F32)),
        Expr::Dec(s, _) => fits(w, ctx, want, Some(Ty::Decimal(*s))),
        Expr::Div(a, b) => {
            let ta = walk_expr(w, p, ctx, false, None, a);
            let tb = walk_expr(w, p, ctx, false, None, b);
            form_result(w, ctx, want, vec![ta, tb], |ts| same_type(Ty::is_float, ts))
        }
        Expr::Sqrt(a) => {
            let ta = walk_expr(w, p, ctx, false, None, a);
            form_result(w, ctx, want, vec![ta], |ts| same_type(Ty::is_float, ts))
        }
        Expr::Fma(a, b, c) => {
            let ta = walk_expr(w, p, ctx, false, None, a);
            let tb = walk_expr(w, p, ctx, false, None, b);
            let tc = walk_expr(w, p, ctx, false, None, c);
            form_result(w, ctx, want, vec![ta, tb, tc], |ts| {
                same_type(Ty::is_float, ts)
            })
        }
        Expr::Fn1(_, a) => {
            let ta = walk_expr(w, p, ctx, false, None, a);
            form_result(w, ctx, want, vec![ta], |ts| same_type(Ty::is_float, ts))
        }
        Expr::Fn2(_, a, b) => {
            let ta = walk_expr(w, p, ctx, false, None, a);
            let tb = walk_expr(w, p, ctx, false, None, b);
            form_result(w, ctx, want, vec![ta, tb], |ts| same_type(Ty::is_float, ts))
        }
        Expr::Round(t, mode, a) => {
            walk_type(w, p, t);
            let ta = walk_expr(w, p, ctx, false, None, a);
            form_result(w, ctx, want, vec![ta], |ts| round_type(t, *mode, ts))
        }
        Expr::DivMode(t, _, a, b) => {
            walk_type(w, p, t);
            let ta = walk_expr(w, p, ctx, false, None, a);
            let tb = walk_expr(w, p, ctx, false, None, b);
            form_result(w, ctx, want, vec![ta, tb], |ts| div_type(t, ts))
        }
    }
}

pub fn walk_args(w: &mut Walk, p: &Program, ctx: &Ctx, args: &[Expr], tys: &[Ty]) {
    match (args, tys) {
        ([], _) => {}
        ([e, es @ ..], [t, ts @ ..]) => {
            walk_expr(w, p, ctx, false, Some(t.clone()), e);
            walk_args(w, p, ctx, es, ts);
        }
        ([e, es @ ..], []) => {
            walk_expr(w, p, ctx, false, None, e);
            walk_args(w, p, ctx, es, &[]);
        }
    }
}

pub fn walk_bind(w: &mut Walk, ctx: &mut Ctx, b: &Bind, ty: Option<Ty>) {
    match b {
        Bind::Wild => {}
        Bind::Name(x) => declare_local(w, ctx, x, ty),
    }
}

pub fn walk_binds(w: &mut Walk, ctx: &mut Ctx, binds: &[Bind], tys: &[Ty]) {
    match (binds, tys) {
        ([], _) => {}
        ([b, bs @ ..], [t, ts @ ..]) => {
            walk_bind(w, ctx, b, Some(t.clone()));
            walk_binds(w, ctx, bs, ts);
        }
        ([b, bs @ ..], []) => {
            walk_bind(w, ctx, b, None);
            walk_binds(w, ctx, bs, &[]);
        }
    }
}

pub fn walk_pat(w: &mut Walk, p: &Program, ctx: &mut Ctx, subject: Option<Ty>, pat: &Pat) {
    match pat {
        Pat::Bool(_) => {
            fits(w, ctx, subject, Some(Ty::Bool));
        }
        Pat::None => match subject {
            Some(Ty::Option(_)) | None => {}
            Some(_) => mismatch(w, ctx),
        },
        Pat::Some(b) => match subject {
            Some(Ty::Option(t)) => walk_bind(w, ctx, b, Some(*t)),
            Some(_) => {
                mismatch(w, ctx);
                walk_bind(w, ctx, b, None);
            }
            None => walk_bind(w, ctx, b, None),
        },
        Pat::Ok(b) => match subject {
            Some(Ty::Result(a, _)) => walk_bind(w, ctx, b, Some(*a)),
            Some(_) => {
                mismatch(w, ctx);
                walk_bind(w, ctx, b, None);
            }
            None => walk_bind(w, ctx, b, None),
        },
        Pat::Err(b) => match subject {
            Some(Ty::Result(_, e)) => walk_bind(w, ctx, b, Some(*e)),
            Some(_) => {
                mismatch(w, ctx);
                walk_bind(w, ctx, b, None);
            }
            None => walk_bind(w, ctx, b, None),
        },
        Pat::Con(c, binds) => match find_case(p, c) {
            None => {
                unknown(w, c);
                walk_binds(w, ctx, binds, &[]);
            }
            Some((owner, fields)) => {
                fits(w, ctx, subject, Some(owner));
                arity(w, ctx, binds.len(), fields.len());
                walk_binds(w, ctx, binds, &fields);
            }
        },
    }
}

pub fn op_on_path(w: &mut Walk, ctx: &Ctx, on_path: bool) {
    if on_path {
        wrong_ending(w, ctx);
    }
}

pub fn walk_outcome(w: &mut Walk, p: &Program, ctx: &Ctx, o: Option<&Expr>) {
    if let Some(e) = o {
        walk_expr(w, p, ctx, false, ctx.site.outcome(), e);
    }
}

pub fn walk_stmts(w: &mut Walk, p: &Program, ctx: &mut Ctx, path_op: bool, stmts: &[Stmt]) -> bool {
    match stmts {
        [] => path_op,
        [Stmt::Let(x, e), rest @ ..] => {
            let ty = walk_expr(w, p, ctx, true, None, e);
            declare_local(w, ctx, x, ty);
            walk_stmts(w, p, ctx, path_op || has_op(p, e), rest)
        }
        [Stmt::Do(e), rest @ ..] => {
            if !is_op(p, e) {
                emit(
                    w,
                    Code::EffectPosition,
                    format!("wrong operation position in {}", tick(&ctx.item)),
                );
            }
            walk_expr(w, p, ctx, true, None, e);
            walk_stmts(w, p, ctx, path_op || has_op(p, e), rest)
        }
    }
}

pub fn walk_block(w: &mut Walk, p: &Program, ctx: &mut Ctx, path_op: bool, b: &Block) {
    let mark = ctx.scope.len();
    let inner_op = walk_stmts(w, p, ctx, path_op, &b.stmts);
    if !ctx.site.permits(&b.tail) {
        wrong_ending(w, ctx);
    }
    walk_tail(w, p, ctx, inner_op, &b.tail);
    ctx.scope.truncate(mark);
}

pub fn walk_tail(w: &mut Walk, p: &Program, ctx: &mut Ctx, path_op: bool, t: &Tail) {
    match t {
        Tail::Value(e) => {
            walk_expr(w, p, ctx, false, ctx.site.value(), e);
        }
        Tail::Next(s, args, o) => {
            match ctx.machine.and_then(|m| find_state(m, s)) {
                None => {
                    unknown(w, s);
                    walk_args(w, p, ctx, args, &[]);
                }
                Some(st) => {
                    arity(w, ctx, args.len(), st.fields.len());
                    let tys: Vec<Ty> = st.fields.iter().map(|f| f.ty.clone()).collect();
                    walk_args(w, p, ctx, args, &tys);
                }
            }
            walk_outcome(w, p, ctx, o.as_ref());
        }
        Tail::Stay(o) => walk_outcome(w, p, ctx, o.as_ref()),
        Tail::Reject(r) => {
            op_on_path(w, ctx, path_op);
            if let Site::Command(name, _, rejects) = &ctx.site
                && !rejects.contains(r)
            {
                emit(
                    w,
                    Code::RejectNotDeclared,
                    format!("command {} does not declare reject {}", tick(name), tick(r)),
                );
            }
        }
        Tail::Answer(e) => {
            op_on_path(w, ctx, path_op || has_op(p, e));
            walk_expr(w, p, ctx, false, ctx.site.answer(), e);
        }
        Tail::Ignore => op_on_path(w, ctx, path_op),
        Tail::Impossible => op_on_path(w, ctx, path_op),
        Tail::Match(subject, arms) => {
            let ty = walk_expr(w, p, ctx, false, None, subject);
            if let Some(t) = &ty {
                match ctors_of(p, t) {
                    Some(ctors) => {
                        let names: Vec<Name> = arms.iter().map(|a| a.pat.ctor()).collect();
                        if !covers_once(&ctors, &names) {
                            emit(
                                w,
                                Code::MatchArms,
                                format!(
                                    "match in {} does not name each constructor once",
                                    tick(&ctx.item)
                                ),
                            );
                        }
                    }
                    None => mismatch(w, ctx),
                }
            }
            walk_arms(w, p, ctx, path_op || has_op(p, subject), ty, arms);
        }
    }
}

pub fn walk_arms(
    w: &mut Walk,
    p: &Program,
    ctx: &mut Ctx,
    path_op: bool,
    subject: Option<Ty>,
    arms: &[Arm],
) {
    match arms {
        [] => {}
        [arm, rest @ ..] => {
            let mark = ctx.scope.len();
            walk_pat(w, p, ctx, subject.clone(), &arm.pat);
            walk_block(w, p, ctx, path_op, &arm.body);
            ctx.scope.truncate(mark);
            walk_arms(w, p, ctx, path_op, subject, rest);
        }
    }
}

pub fn base_ctx<'a>(item: &str) -> Ctx<'a> {
    Ctx {
        item: item.to_string(),
        fn_index: None,
        machine: None,
        site: Site::Unknown,
        uses: Vec::new(),
        scope: Vec::new(),
    }
}

pub fn walk_fields(w: &mut Walk, p: &Program, ctx: &mut Ctx, fields: &[Param]) {
    match fields {
        [] => {}
        [f, fs @ ..] => {
            declare_local(w, ctx, &f.name, Some(f.ty.clone()));
            walk_type(w, p, &f.ty);
            walk_fields(w, p, ctx, fs);
        }
    }
}

pub fn bind_params(w: &mut Walk, ctx: &mut Ctx, params: &[Param]) {
    match params {
        [] => {}
        [x, xs @ ..] => {
            bind_local(w, ctx, &x.name, Some(x.ty.clone()));
            bind_params(w, ctx, xs);
        }
    }
}

pub fn walk_fn(w: &mut Walk, p: &Program, index: usize, f: &Fn) {
    declare(w, &f.name);
    let mut ctx = Ctx {
        fn_index: Some(index),
        site: Site::Fn(f.result.clone()),
        uses: f.uses.clone(),
        ..base_ctx(&f.name)
    };
    walk_fields(w, p, &mut ctx, &f.params);
    walk_type(w, p, &f.result);
    walk_block(w, p, &mut ctx, false, &f.body);
}

pub fn walk_msg(w: &mut Walk, p: &Program, m: &Msg) {
    declare(w, m.name());
    walk_fields(w, p, &mut base_ctx(m.name()), m.params());
    walk_type(w, p, m.result());
    if let Msg::Command { role: Some(r), .. } = m
        && !is_role(p, r)
    {
        unknown(w, r);
    }
}

pub fn walk_cell(w: &mut Walk, p: &Program, m: &Machine, scope: &[(Name, Option<Ty>)], c: &Cell) {
    let mut ctx = Ctx {
        machine: Some(m),
        uses: m.uses.clone(),
        scope: scope.to_vec(),
        ..base_ctx(&m.name)
    };
    match input_site(p, m, &c.input) {
        None => {
            unknown(w, &c.input);
            walk_block(w, p, &mut ctx, false, &c.body);
        }
        Some((site, params)) => {
            ctx.site = site;
            bind_params(w, &mut ctx, &params);
            walk_block(w, p, &mut ctx, false, &c.body);
        }
    }
}

pub fn walk_in(w: &mut Walk, p: &Program, m: &Machine, b: &In) {
    let scope: Vec<(Name, Option<Ty>)> = match find_state(m, &b.target) {
        Some(st) => st
            .fields
            .iter()
            .rev()
            .map(|f| (f.name.clone(), Some(f.ty.clone())))
            .collect(),
        None => Vec::new(),
    };
    if find_state(m, &b.target).is_none() && find_group(m, &b.target).is_none() {
        unknown(w, &b.target);
    }
    for c in &b.cells {
        walk_cell(w, p, m, &scope, c);
    }
}

pub fn walk_machine(w: &mut Walk, p: &Program, m: &Machine) {
    declare(w, &m.name);
    walk_type(w, p, &m.key);
    if find_protocol(p, &m.protocol).is_none() {
        unknown(w, &m.protocol);
    }
    match find_state(m, &m.init) {
        None => unknown(w, &m.init),
        Some(s) => {
            if !s.fields.is_empty() {
                emit(
                    w,
                    Code::InitHasFields,
                    format!(
                        "init state {} of machine {} has fields",
                        tick(&s.name),
                        tick(&m.name)
                    ),
                );
            }
        }
    }
    for s in &m.states {
        declare(w, &s.name);
        walk_fields(w, p, &mut base_ctx(&m.name), &s.fields);
    }
    for g in &m.groups {
        declare(w, &g.name);
        for x in &g.members {
            if find_state(m, x).is_none() {
                unknown(w, x);
            }
        }
    }
    for b in &m.ins {
        walk_in(w, p, m, b);
    }
}

pub fn machine_key(w: &mut Walk, p: &Program, m: &str) -> Option<Ty> {
    match find_machine(p, m) {
        Some(mach) => Some(mach.key.clone()),
        None => {
            unknown(w, m);
            None
        }
    }
}

pub fn walk_x_expr(
    w: &mut Walk,
    p: &Program,
    ctx: &Ctx,
    want: Option<Ty>,
    x: &XExpr,
) -> Option<Ty> {
    match x {
        XExpr::Int(_) => fits(w, ctx, want, Some(Ty::Int)),
        XExpr::Text(_) => fits(w, ctx, want, Some(Ty::Text)),
        XExpr::Bool(_) => fits(w, ctx, want, Some(Ty::Bool)),
        XExpr::Unit => fits(w, ctx, want, Some(Ty::Unit)),
        XExpr::Dur(_) => fits(w, ctx, want, Some(Ty::Duration)),
        XExpr::Step(_) => fits(w, ctx, want, Some(Ty::StepId)),
        XExpr::Ticket(_) => fits(w, ctx, want, Some(Ty::Ticket)),
        XExpr::Var(v) => {
            if ctx.scope.iter().any(|(n, _)| n == v) {
                fits(w, ctx, want, Some(Ty::Principal))
            } else {
                unknown(w, v);
                None
            }
        }
        XExpr::New(ctor, args) => match find_ctor(p, ctor) {
            None => {
                unknown(w, ctor);
                walk_x_args(w, p, ctx, args, &[]);
                None
            }
            Some((t, fields)) => {
                arity(w, ctx, args.len(), fields.len());
                walk_x_args(w, p, ctx, args, &fields);
                fits(w, ctx, want, Some(t))
            }
        },
        XExpr::Some(inner) => match &want {
            Some(Ty::Option(t)) => {
                walk_x_expr(w, p, ctx, Some((**t).clone()), inner);
                want
            }
            Some(_) => {
                mismatch(w, ctx);
                walk_x_expr(w, p, ctx, None, inner);
                None
            }
            None => {
                let t = walk_x_expr(w, p, ctx, None, inner);
                t.map(|t| Ty::Option(Box::new(t)))
            }
        },
        XExpr::None => match &want {
            Some(Ty::Option(_)) => want,
            _ => {
                mismatch(w, ctx);
                None
            }
        },
        XExpr::Ok(inner) => match &want {
            Some(Ty::Result(a, _)) => {
                walk_x_expr(w, p, ctx, Some((**a).clone()), inner);
                want
            }
            _ => {
                mismatch(w, ctx);
                walk_x_expr(w, p, ctx, None, inner);
                None
            }
        },
        XExpr::Err(inner) => match &want {
            Some(Ty::Result(_, e)) => {
                walk_x_expr(w, p, ctx, Some((**e).clone()), inner);
                want
            }
            _ => {
                mismatch(w, ctx);
                walk_x_expr(w, p, ctx, None, inner);
                None
            }
        },
        XExpr::F64(_) => fits(w, ctx, want, Some(Ty::F64)),
        XExpr::F32(_) => fits(w, ctx, want, Some(Ty::F32)),
        XExpr::Dec(s, _) => fits(w, ctx, want, Some(Ty::Decimal(*s))),
        XExpr::Time(_) => fits(w, ctx, want, Some(Ty::Time)),
        XExpr::Principal(_) => fits(w, ctx, want, Some(Ty::Principal)),
        XExpr::StepOf(m, k, _, _) => {
            let key = machine_key(w, p, m);
            walk_x_expr(w, p, ctx, key, k);
            fits(w, ctx, want, Some(Ty::StepId))
        }
        XExpr::TicketOf(m, k, _, _, _) => {
            let key = machine_key(w, p, m);
            walk_x_expr(w, p, ctx, key, k);
            fits(w, ctx, want, Some(Ty::Ticket))
        }
    }
}

pub fn walk_x_args(w: &mut Walk, p: &Program, ctx: &Ctx, args: &[XExpr], tys: &[Ty]) {
    match (args, tys) {
        ([], _) => {}
        ([x, xs @ ..], [t, ts @ ..]) => {
            walk_x_expr(w, p, ctx, Some(t.clone()), x);
            walk_x_args(w, p, ctx, xs, ts);
        }
        ([x, xs @ ..], []) => {
            walk_x_expr(w, p, ctx, None, x);
            walk_x_args(w, p, ctx, xs, &[]);
        }
    }
}

pub fn refers_to_instance(x: &XExpr) -> bool {
    match x {
        XExpr::Step(_) => true,
        XExpr::Ticket(_) => true,
        XExpr::New(_, args) => any_refers_to_instance(args),
        XExpr::Some(x) => refers_to_instance(x),
        XExpr::Ok(x) => refers_to_instance(x),
        XExpr::Err(x) => refers_to_instance(x),
        XExpr::StepOf(_, k, _, _) => refers_to_instance(k),
        XExpr::TicketOf(_, k, _, _, _) => refers_to_instance(k),
        XExpr::Int(_)
        | XExpr::Text(_)
        | XExpr::Bool(_)
        | XExpr::Unit
        | XExpr::Dur(_)
        | XExpr::Var(_)
        | XExpr::None => false,
        XExpr::F64(_) | XExpr::F32(_) | XExpr::Dec(_, _) | XExpr::Time(_) | XExpr::Principal(_) => {
            false
        }
    }
}

pub fn any_refers_to_instance(xs: &[XExpr]) -> bool {
    match xs {
        [] => false,
        [x, rest @ ..] => refers_to_instance(x) || any_refers_to_instance(rest),
    }
}

pub fn walk_constant(w: &mut Walk, p: &Program, ctx: &Ctx, want: Option<Ty>, x: &XExpr) {
    walk_x_expr(w, p, ctx, want, x);
    if refers_to_instance(x) {
        mismatch(w, ctx);
    }
}

pub fn walk_record_fields(
    w: &mut Walk,
    p: &Program,
    ctx: &Ctx,
    seen: Vec<Name>,
    fields: &[(&Param, Option<&XExpr>)],
) {
    match fields {
        [] => {}
        [(f, init), fs @ ..] => {
            if seen.contains(&f.name) {
                duplicate(w, &f.name);
            }
            walk_type(w, p, &f.ty);
            if let Some(x) = init {
                walk_constant(w, p, ctx, Some(f.ty.clone()), x);
            }
            let mut seen = seen;
            seen.push(f.name.clone());
            walk_record_fields(w, p, ctx, seen, fs);
        }
    }
}

pub fn walk_fact(w: &mut Walk, p: &Program, ctx: &Ctx, site: &Site, f: &Fact) {
    match f {
        Fact::Outcome(x) => match site {
            Site::Command(_, result, _) => {
                walk_x_expr(w, p, ctx, Some(result.clone()), x);
            }
            Site::Unknown => {
                walk_x_expr(w, p, ctx, None, x);
            }
            _ => {
                mismatch(w, ctx);
                walk_x_expr(w, p, ctx, None, x);
            }
        },
        Fact::Answer(x) => match site {
            Site::Query(result) => {
                walk_x_expr(w, p, ctx, Some(result.clone()), x);
            }
            Site::Unknown => {
                walk_x_expr(w, p, ctx, None, x);
            }
            _ => {
                mismatch(w, ctx);
                walk_x_expr(w, p, ctx, None, x);
            }
        },
        Fact::State(s, args) => match ctx.machine.and_then(|m| find_state(m, s)) {
            None => {
                unknown(w, s);
                walk_x_args(w, p, ctx, args, &[]);
            }
            Some(st) => {
                arity(w, ctx, args.len(), st.fields.len());
                let tys: Vec<Ty> = st.fields.iter().map(|f| f.ty.clone()).collect();
                walk_x_args(w, p, ctx, args, &tys);
            }
        },
        _ => {}
    }
}

pub fn walk_line(w: &mut Walk, p: &Program, ctx: &Ctx, l: &Line) {
    match l {
        Line::Send {
            actor,
            input,
            args,
            facts,
        } => {
            if !ctx.scope.iter().any(|(n, _)| n == actor) {
                unknown(w, actor);
            }
            let site = match ctx.machine.and_then(|m| find_msg(p, m, input)) {
                Some(Msg::Command {
                    name,
                    params,
                    result,
                    rejects,
                    ..
                }) => {
                    arity(w, ctx, args.len(), params.len());
                    let tys: Vec<Ty> = params.iter().map(|x| x.ty.clone()).collect();
                    walk_x_args(w, p, ctx, args, &tys);
                    Site::Command(name.clone(), result.clone(), rejects.clone())
                }
                Some(Msg::Query { params, result, .. }) => {
                    arity(w, ctx, args.len(), params.len());
                    let tys: Vec<Ty> = params.iter().map(|x| x.ty.clone()).collect();
                    walk_x_args(w, p, ctx, args, &tys);
                    Site::Query(result.clone())
                }
                None => {
                    unknown(w, input);
                    walk_x_args(w, p, ctx, args, &[]);
                    Site::Unknown
                }
            };
            for f in facts {
                walk_fact(w, p, ctx, &site, f);
            }
        }
        Line::Fire { ticket, facts } => {
            if let Some(m) = ctx.machine
                && !m.uses.contains(&Effect::Timer)
            {
                unknown(w, FIRED_NAME);
            }
            walk_x_expr(w, p, ctx, Some(Ty::Ticket), ticket);
            for f in facts {
                walk_fact(w, p, ctx, &Site::Fired, f);
            }
        }
    }
}

pub fn walk_actors(w: &mut Walk, p: &Program, ctx: &mut Ctx, actors: &[Actor]) {
    match actors {
        [] => {}
        [a, rest @ ..] => {
            declare_local(w, ctx, &a.name, Some(Ty::Principal));
            for r in &a.roles {
                if !is_role(p, r) {
                    unknown(w, r);
                }
            }
            walk_actors(w, p, ctx, rest);
        }
    }
}

pub fn walk_example(w: &mut Walk, p: &Program, ex: &Example) {
    declare(w, &ex.name);
    let m = find_machine(p, &ex.machine);
    if m.is_none() {
        unknown(w, &ex.machine);
    }
    let mut ctx = Ctx {
        machine: m,
        ..base_ctx(&ex.name)
    };
    walk_constant(w, p, &ctx, m.map(|m| m.key.clone()), &ex.key);
    walk_actors(w, p, &mut ctx, &ex.actors);
    for l in &ex.lines {
        walk_line(w, p, &ctx, l);
    }
}

pub fn walk_deployment(w: &mut Walk, p: &Program, d: &Deployment) {
    declare(w, &d.name);
    match find_fn(p, &d.entry) {
        None => unknown(w, &d.entry),
        Some(f) => {
            if !f.params.is_empty() || f.result != Ty::Unit {
                emit(
                    w,
                    Code::BadEntry,
                    format!("deployment {} has no legal entry", tick(&d.name)),
                );
            }
        }
    }
    if w.deployments > 0 {
        emit(
            w,
            Code::BadEntry,
            format!("deployment {} has no legal entry", tick(&d.name)),
        );
    }
    w.deployments += 1;
}

pub fn walk_item(w: &mut Walk, p: &Program, index: usize, it: &Item) {
    match it {
        Item::Newtype(n, t) => {
            declare(w, n);
            walk_type(w, p, t);
        }
        Item::Record(r, fields, inits) => {
            declare(w, r);
            let all: Vec<(&Param, Option<&XExpr>)> = fields
                .iter()
                .map(|f| (f, None))
                .chain(inits.iter().map(|(f, x)| (f, Some(x))))
                .collect();
            walk_record_fields(w, p, &base_ctx(r), Vec::new(), &all);
        }
        Item::Enum(e, variants) => {
            declare(w, e);
            for v in variants {
                declare(w, &v.name);
                for t in &v.fields {
                    walk_type(w, p, t);
                }
            }
        }
        Item::Role(r) => declare(w, r),
        Item::Fn(f) => walk_fn(w, p, index, f),
        Item::Protocol(q) => {
            declare(w, &q.name);
            for m in &q.msgs {
                walk_msg(w, p, m);
            }
        }
        Item::Machine(m) => walk_machine(w, p, m),
        Item::Deployment(d) => walk_deployment(w, p, d),
        Item::Example(ex) => walk_example(w, p, ex),
        Item::Decode(n, t, _, expect) => {
            declare(w, n);
            walk_type(w, p, t);
            if let Some(x) = expect {
                walk_constant(w, p, &base_ctx(n), Some(t.clone()), x);
            }
        }
    }
}

pub fn walk_items(w: &mut Walk, p: &Program, index: usize, items: &[Item]) {
    for (i, it) in items.iter().enumerate() {
        walk_item(w, p, index + i, it);
    }
}

pub fn walk_program(p: &Program) -> Vec<Diag> {
    let mut w = Walk {
        diags: Vec::new(),
        declared: Vec::new(),
        locals: Vec::new(),
        deployments: 0,
    };
    walk_items(&mut w, p, 0, &p.items);
    w.diags
}

pub fn pairs(p: &Program, m: &Machine) -> Vec<(Name, Name)> {
    m.states
        .iter()
        .flat_map(|s| {
            input_names(p, m)
                .into_iter()
                .map(move |i| (s.name.clone(), i))
        })
        .collect()
}

pub fn missing_cells(p: &Program, m: &Machine) -> Vec<(Name, Name)> {
    pairs(p, m)
        .into_iter()
        .filter(|(s, i)| find_cell(m, s, i).is_none())
        .collect()
}

pub fn duplicate_cells(p: &Program, m: &Machine) -> Vec<(Name, Name)> {
    pairs(p, m)
        .into_iter()
        .filter(|(s, i)| cells_for(m, s, i).len() >= 2)
        .collect()
}

pub fn cell_diags(p: &Program, it: &Item) -> Vec<Diag> {
    match it {
        Item::Machine(m) => {
            let mut ds: Vec<Diag> = duplicate_cells(p, m)
                .into_iter()
                .map(|(s, i)| Diag {
                    code: Code::DuplicateCell,
                    message: format!("machine {} has two cells for ({s}, {i})", tick(&m.name)),
                })
                .collect();
            ds.extend(missing_cells(p, m).into_iter().map(|(s, i)| Diag {
                code: Code::MissingCell,
                message: format!("machine {} has no cell for ({s}, {i})", tick(&m.name)),
            }));
            ds
        }
        _ => Vec::new(),
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Node {
    Named(Name),
    StepId,
    Ticket,
}

impl Node {
    pub fn text(&self) -> &str {
        match self {
            Node::Named(n) => n,
            Node::StepId => "StepId",
            Node::Ticket => "Ticket",
        }
    }
}

pub fn ty_nodes(t: &Ty) -> Vec<Node> {
    match t {
        Ty::Named(n) => vec![Node::Named(n.clone())],
        Ty::Option(t) => ty_nodes(t),
        Ty::Result(a, b) => {
            let mut ns = ty_nodes(a);
            ns.extend(ty_nodes(b));
            ns
        }
        Ty::StepId => vec![Node::StepId],
        Ty::Ticket => vec![Node::Ticket],
        _ => Vec::new(),
    }
}

pub fn item_nodes(p: &Program, n: &str) -> Vec<Node> {
    p.items
        .iter()
        .flat_map(|item| match item {
            Item::Record(r, fields, inits) if r == n => fields
                .iter()
                .chain(inits.iter().map(|(f, _)| f))
                .flat_map(|f| ty_nodes(&f.ty))
                .collect(),
            Item::Enum(e, variants) if e == n => variants
                .iter()
                .flat_map(|v| v.fields.iter().flat_map(ty_nodes))
                .collect(),
            Item::Newtype(m, t) if m == n => ty_nodes(t),
            _ => Vec::new(),
        })
        .collect()
}

pub fn key_nodes(p: &Program) -> Vec<Node> {
    p.items
        .iter()
        .flat_map(|item| match item {
            Item::Machine(m) => ty_nodes(&m.key),
            _ => Vec::new(),
        })
        .collect()
}

pub fn edges(p: &Program, n: &Node) -> Vec<Node> {
    match n {
        Node::Named(n) => item_nodes(p, n),
        Node::StepId => key_nodes(p),
        Node::Ticket => key_nodes(p),
    }
}

pub fn type_names(p: &Program) -> Vec<Name> {
    p.items
        .iter()
        .filter_map(|item| match item {
            Item::Record(r, _, _) => Some(r.clone()),
            Item::Enum(e, _) => Some(e.clone()),
            Item::Newtype(n, _) => Some(n.clone()),
            _ => None,
        })
        .collect()
}

pub fn node_count(p: &Program) -> usize {
    type_names(p).len() + 2
}

pub fn add_new(seen: &[Node], xs: &[Node]) -> Vec<Node> {
    let mut known = seen.to_vec();
    let mut fresh = Vec::new();
    for x in xs {
        if !known.contains(x) {
            known.push(x.clone());
            fresh.push(x.clone());
        }
    }
    fresh
}

pub fn reach(p: &Program, k: usize, seen: Vec<Node>, frontier: &[Node]) -> Vec<Node> {
    match k.checked_sub(1) {
        None => seen,
        Some(k) => {
            let out: Vec<Node> = frontier.iter().flat_map(|n| edges(p, n)).collect();
            let next = add_new(&seen, &out);
            if next.is_empty() {
                seen
            } else {
                let mut seen = seen;
                seen.extend(next.iter().cloned());
                reach(p, k, seen, &next)
            }
        }
    }
}

pub fn reach_from(p: &Program, start: &[Node]) -> Vec<Node> {
    let first = add_new(&[], start);
    reach(p, node_count(p), first.clone(), &first)
}

pub fn reaches_self(p: &Program, n: &Node) -> bool {
    reach_from(p, &edges(p, n)).contains(n)
}

pub fn reaches_special(p: &Program, start: &[Node]) -> bool {
    let ns = reach_from(p, start);
    ns.contains(&Node::StepId) || ns.contains(&Node::Ticket)
}

pub fn first_special(p: &Program, k: usize, t: &Ty) -> Option<Node> {
    match t {
        Ty::StepId => Some(Node::StepId),
        Ty::Ticket => Some(Node::Ticket),
        Ty::Option(t) => first_special(p, k, t),
        Ty::Result(a, b) => first_special(p, k, a).or_else(|| first_special(p, k, b)),
        Ty::Named(n) => match k.checked_sub(1) {
            None => None,
            Some(k) => {
                if reaches_special(p, &edges(p, &Node::Named(n.clone()))) {
                    p.items.iter().find_map(|item| match item {
                        Item::Record(r, fields, inits) if r == n => fields
                            .iter()
                            .chain(inits.iter().map(|(f, _)| f))
                            .find_map(|f| first_special(p, k, &f.ty)),
                        Item::Enum(e, variants) if e == n => variants
                            .iter()
                            .find_map(|v| v.fields.iter().find_map(|t| first_special(p, k, t))),
                        Item::Newtype(m, t) if m == n => first_special(p, k, t),
                        _ => None,
                    })
                } else {
                    None
                }
            }
        },
        _ => None,
    }
}

pub fn recursive_type_diags(p: &Program) -> Vec<Diag> {
    let message = |n: &Node| Diag {
        code: Code::RecursiveType,
        message: format!("type {} contains itself", tick(n.text())),
    };
    match type_names(p)
        .into_iter()
        .find(|n| reaches_self(p, &Node::Named(n.clone())))
    {
        Some(n) => vec![message(&Node::Named(n))],
        None => {
            let key_loop = p.items.iter().find_map(|item| match item {
                Item::Machine(m) => {
                    if reaches_special(p, &ty_nodes(&m.key)) {
                        first_special(p, node_count(p), &m.key)
                    } else {
                        None
                    }
                }
                _ => None,
            });
            match key_loop {
                Some(n) => vec![message(&n)],
                None => Vec::new(),
            }
        }
    }
}

pub fn layout_diag(t: &str) -> Diag {
    Diag {
        code: Code::LayoutLimit,
        message: format!("type {} exceeds the layout limits", tick(t)),
    }
}

pub fn layout_diags(it: &Item) -> Vec<Diag> {
    match it {
        Item::Record(r, fields, inits) => {
            if fields.len() + inits.len() > 65535 {
                vec![layout_diag(r)]
            } else {
                Vec::new()
            }
        }
        Item::Enum(e, variants) => {
            if variants.len() > 256 {
                vec![layout_diag(e)]
            } else {
                Vec::new()
            }
        }
        _ => Vec::new(),
    }
}

pub fn diagnose(p: &Program) -> Vec<Diag> {
    let mut ds = walk_program(p);
    ds.extend(p.items.iter().flat_map(layout_diags));
    ds.extend(recursive_type_diags(p));
    ds.extend(p.items.iter().flat_map(|it| cell_diags(p, it)));
    ds
}

pub fn select(ds: &[Diag]) -> Vec<Diag> {
    let best = ds
        .iter()
        .fold(Code::BadEntry.rank(), |r, d| r.min(d.code.rank()));
    let firsts: Vec<Diag> = ds
        .iter()
        .filter(|d| d.code.rank() == best)
        .cloned()
        .collect();
    if best == Code::MissingCell.rank() {
        firsts
    } else {
        firsts.into_iter().take(1).collect()
    }
}

pub fn check(p: &Program) -> Result<(), Vec<Diag>> {
    match diagnose(p).as_slice() {
        [] => Ok(()),
        ds => Err(select(ds)),
    }
}
