use crate::decimal::dec_parse;
use crate::float::{Fmt, float_parse};
use crate::ir::{
    Actor, Arith, Arm, Bind, Block, Cell, Deployment, Effect, EnvField, Example, Expr, Fact, Fn,
    Fn1, Fn2, Group, In, Item, Line, Machine, Mode, Msg, Name, Op, Param, Pat, Platform, Program,
    Protocol, State, Stmt, Tail, Ty, Variant, XExpr,
};

#[derive(Clone, Debug, PartialEq, Eq)]
enum Token {
    Lp,
    Rp,
    Atom(String),
    Text(String),
}

enum Lex {
    Gap,
    Atom(Vec<char>),
    Text(Vec<char>),
    Escape(Vec<char>),
    Closed,
}

fn is_space(c: char) -> bool {
    c == ' ' || c == '\t' || c == '\n'
}

fn is_paren(c: char) -> bool {
    c == '(' || c == ')'
}

fn paren(c: char) -> Token {
    if c == '(' { Token::Lp } else { Token::Rp }
}

fn atom_token(chars: &[char]) -> Token {
    Token::Atom(chars.iter().collect())
}

fn lex(mut state: Lex, chars: &[char], mut acc: Vec<Token>) -> Option<Vec<Token>> {
    for &c in chars {
        state = match state {
            Lex::Gap => {
                if is_space(c) {
                    Lex::Gap
                } else if is_paren(c) {
                    acc.push(paren(c));
                    Lex::Gap
                } else if c == '"' {
                    Lex::Text(Vec::new())
                } else {
                    Lex::Atom(vec![c])
                }
            }
            Lex::Atom(mut atom) => {
                if is_space(c) {
                    acc.push(atom_token(&atom));
                    Lex::Gap
                } else if is_paren(c) {
                    acc.push(atom_token(&atom));
                    acc.push(paren(c));
                    Lex::Gap
                } else if c == '"' {
                    return None;
                } else {
                    atom.push(c);
                    Lex::Atom(atom)
                }
            }
            Lex::Text(mut text) => {
                if c == '"' {
                    acc.push(Token::Text(text.iter().collect()));
                    Lex::Closed
                } else if c == '\\' {
                    Lex::Escape(text)
                } else if u32::from(c) < 0x20 || u32::from(c) == 0x7F {
                    return None;
                } else {
                    text.push(c);
                    Lex::Text(text)
                }
            }
            Lex::Escape(mut text) => {
                if c == '"' || c == '\\' {
                    text.push(c);
                    Lex::Text(text)
                } else {
                    return None;
                }
            }
            Lex::Closed => {
                if is_space(c) {
                    Lex::Gap
                } else if is_paren(c) {
                    acc.push(paren(c));
                    Lex::Gap
                } else {
                    return None;
                }
            }
        };
    }
    match state {
        Lex::Gap | Lex::Closed => Some(acc),
        Lex::Atom(atom) => {
            acc.push(atom_token(&atom));
            Some(acc)
        }
        Lex::Text(_) | Lex::Escape(_) => None,
    }
}

fn is_letter(c: char) -> bool {
    c.is_ascii_uppercase() || c.is_ascii_lowercase()
}

fn is_digit(c: char) -> bool {
    c.is_ascii_digit()
}

fn is_ident(s: &str) -> bool {
    let mut cs = s.chars();
    match cs.next() {
        Some(c) => is_letter(c) && cs.all(|d| is_letter(d) || is_digit(d) || d == '_'),
        None => false,
    }
}

fn digits_value(cs: &[char]) -> Option<u64> {
    cs.iter().try_fold(0u64, |n, &c| {
        n.checked_mul(10)?
            .checked_add(u64::from(c) - u64::from('0'))
    })
}

fn natural(cs: &[char]) -> Option<u64> {
    match cs {
        [c, rest @ ..] => {
            if *c != '0' && is_digit(*c) && rest.iter().all(|&d| is_digit(d)) {
                digits_value(cs)
            } else {
                None
            }
        }
        [] => None,
    }
}

fn parse_int(s: &str) -> Option<i64> {
    let chars: Vec<char> = s.chars().collect();
    let n: Option<i128> = if s == "0" {
        Some(0)
    } else {
        match chars.as_slice() {
            ['-', cs @ ..] => natural(cs).map(|v| -i128::from(v)),
            cs => natural(cs).map(i128::from),
        }
    };
    n.and_then(|v| i64::try_from(v).ok())
}

const FN1_NAMES: &[(&str, Fn1)] = &[
    ("exp", Fn1::Exp),
    ("exp2", Fn1::Exp2),
    ("log", Fn1::Log),
    ("log2", Fn1::Log2),
    ("log10", Fn1::Log10),
    ("sin", Fn1::Sin),
    ("cos", Fn1::Cos),
    ("tan", Fn1::Tan),
    ("asin", Fn1::Asin),
    ("acos", Fn1::Acos),
    ("atan", Fn1::Atan),
    ("sinh", Fn1::Sinh),
    ("cosh", Fn1::Cosh),
    ("tanh", Fn1::Tanh),
    ("cbrt", Fn1::Cbrt),
];

const FN2_NAMES: &[(&str, Fn2)] = &[
    ("pow", Fn2::Pow),
    ("atan2", Fn2::Atan2),
    ("hypot", Fn2::Hypot),
];

const MODE_NAMES: &[(&str, Mode)] = &[
    ("up", Mode::Up),
    ("down", Mode::Down),
    ("ceiling", Mode::Ceiling),
    ("floor", Mode::Floor),
    ("half_up", Mode::HalfUp),
    ("half_down", Mode::HalfDown),
    ("half_even", Mode::HalfEven),
    ("exact", Mode::Exact),
];

fn reserved() -> impl Iterator<Item = &'static str> {
    [
        "program",
        "newtype",
        "record",
        "enum",
        "role",
        "fn",
        "uses",
        "block",
        "protocol",
        "machine",
        "key",
        "init",
        "state",
        "group",
        "in",
        "on",
        "deployment",
        "platform",
        "entry",
        "example",
        "command",
        "rejects",
        "by",
        "query",
        "let",
        "do",
        "value",
        "next",
        "outcome",
        "stay",
        "reject",
        "answer",
        "ignore",
        "impossible",
        "match",
        "arm",
        "unit",
        "dur",
        "env",
        "call",
        "new",
        "get",
        "some",
        "none",
        "ok",
        "err",
        "and",
        "not",
        "actor",
        "send",
        "fire",
        "expect",
        "refused",
        "fault",
        "ignored",
        "step",
        "ticket",
        "decode",
        "invalid",
        "f64",
        "f32",
        "dec",
        "sqrt",
        "fma",
        "round",
        "div",
        "time",
        "principal",
        "Unit",
        "Bool",
        "Int",
        "Text",
        "Time",
        "Duration",
        "Principal",
        "StepId",
        "Ticket",
        "Option",
        "Result",
        "true",
        "false",
        "Fired",
        "ConsoleOut",
        "Timer",
        "F64",
        "F32",
        "Decimal",
    ]
    .into_iter()
    .chain(FN1_NAMES.iter().map(|&(n, _)| n))
    .chain(FN2_NAMES.iter().map(|&(n, _)| n))
}

fn lookup<T: Copy>(table: &[(&str, T)], key: &str) -> Option<T> {
    table.iter().find(|&&(k, _)| k == key).map(|&(_, v)| v)
}

fn hex_digit(c: char) -> Option<u8> {
    let b = u8::try_from(c).ok()?;
    if is_digit(c) {
        Some(b - b'0')
    } else if ('a'..='f').contains(&c) {
        Some(b - b'a' + 10)
    } else {
        None
    }
}

fn hex_bytes(cs: &[char]) -> Option<Vec<u8>> {
    let mut bytes = Vec::new();
    let mut rest = cs;
    loop {
        match rest {
            [] => return Some(bytes),
            [_] => return None,
            [hi, lo, more @ ..] => {
                bytes.push(16 * hex_digit(*hi)? + hex_digit(*lo)?);
                rest = more;
            }
        }
    }
}

fn atom_expr(s: String) -> Option<Expr> {
    match parse_int(&s) {
        Some(n) => Some(Expr::Int(n)),
        None => {
            if s == "true" {
                Some(Expr::Bool(true))
            } else if s == "false" {
                Some(Expr::Bool(false))
            } else if is_ident(&s) {
                Some(Expr::Var(s))
            } else {
                None
            }
        }
    }
}

fn non_empty<T>(xs: Vec<T>) -> Option<Vec<T>> {
    if xs.is_empty() { None } else { Some(xs) }
}

fn init_fields(fs: Vec<(Param, Option<XExpr>)>) -> Option<Vec<(Param, XExpr)>> {
    fs.into_iter().map(|(f, x)| x.map(|v| (f, v))).collect()
}

struct Reader {
    tokens: Vec<Token>,
    pos: usize,
}

impl Reader {
    fn token(&mut self) -> Option<Token> {
        let t = self.tokens.get(self.pos)?.clone();
        self.pos += 1;
        Some(t)
    }

    fn peek_close(&self) -> bool {
        matches!(self.tokens.get(self.pos..), Some([Token::Rp, ..]))
    }

    fn peek_head(&self) -> Option<&str> {
        match self.tokens.get(self.pos..) {
            Some([Token::Lp, Token::Atom(h), ..]) => Some(h),
            _ => None,
        }
    }

    fn open_paren(&mut self) -> Option<()> {
        match self.token()? {
            Token::Lp => Some(()),
            _ => None,
        }
    }

    fn close_paren(&mut self) -> Option<()> {
        match self.token()? {
            Token::Rp => Some(()),
            _ => None,
        }
    }

    fn atom(&mut self) -> Option<String> {
        match self.token()? {
            Token::Atom(s) => Some(s),
            _ => None,
        }
    }

    fn keyword(&mut self, word: &str) -> Option<()> {
        let s = self.atom()?;
        if s == word { Some(()) } else { None }
    }

    fn head(&mut self, word: &str) -> Option<()> {
        self.open_paren()?;
        self.keyword(word)
    }

    fn ident(&mut self) -> Option<Name> {
        let s = self.atom()?;
        if is_ident(&s) { Some(s) } else { None }
    }

    fn decl_name(&mut self) -> Option<Name> {
        let s = self.ident()?;
        if reserved().any(|w| w == s) {
            None
        } else {
            Some(s)
        }
    }

    fn local_name(&mut self) -> Option<Name> {
        let s = self.ident()?;
        if s == "true" || s == "false" {
            None
        } else {
            Some(s)
        }
    }

    fn int(&mut self) -> Option<i64> {
        parse_int(&self.atom()?)
    }

    fn decimal_scale(&mut self) -> Option<u32> {
        let s = self.int()?;
        if (0..=37).contains(&s) {
            Some(s as u32)
        } else {
            None
        }
    }

    fn float_atom(&mut self, f: Fmt) -> Option<u64> {
        float_parse(f, &self.atom()?)
    }

    fn decimal_atom(&mut self) -> Option<(u32, i128)> {
        dec_parse(&self.atom()?)
    }

    fn mode_atom(&mut self) -> Option<Mode> {
        lookup(MODE_NAMES, &self.atom()?)
    }

    fn text_token(&mut self) -> Option<String> {
        match self.token()? {
            Token::Text(s) => Some(s),
            _ => None,
        }
    }

    fn until_close<T>(&mut self, mut item: impl FnMut(&mut Reader) -> Option<T>) -> Option<Vec<T>> {
        let mut xs = Vec::new();
        while !self.peek_close() {
            xs.push(item(self)?);
        }
        Some(xs)
    }

    fn some1<T>(&mut self, item: impl FnMut(&mut Reader) -> Option<T>) -> Option<Vec<T>> {
        let xs = self.until_close(item)?;
        if xs.is_empty() { None } else { Some(xs) }
    }

    fn headed<T>(
        &mut self,
        word: &str,
        mut item: impl FnMut(&mut Reader) -> Option<T>,
    ) -> Option<Vec<T>> {
        let mut xs = Vec::new();
        while self.peek_head() == Some(word) {
            xs.push(item(self)?);
        }
        Some(xs)
    }

    fn ty(&mut self) -> Option<Ty> {
        match self.token()? {
            Token::Atom(s) => match s.as_str() {
                "Unit" => Some(Ty::Unit),
                "Bool" => Some(Ty::Bool),
                "Int" => Some(Ty::Int),
                "Text" => Some(Ty::Text),
                "Time" => Some(Ty::Time),
                "Duration" => Some(Ty::Duration),
                "Principal" => Some(Ty::Principal),
                "StepId" => Some(Ty::StepId),
                "Ticket" => Some(Ty::Ticket),
                "F64" => Some(Ty::F64),
                "F32" => Some(Ty::F32),
                _ => {
                    if is_ident(&s) {
                        Some(Ty::Named(s))
                    } else {
                        None
                    }
                }
            },
            Token::Lp => match self.atom()?.as_str() {
                "Option" => {
                    let t = self.ty()?;
                    self.close_paren()?;
                    Some(Ty::Option(Box::new(t)))
                }
                "Result" => {
                    let ok = self.ty()?;
                    let err = self.ty()?;
                    self.close_paren()?;
                    Some(Ty::Result(Box::new(ok), Box::new(err)))
                }
                "Decimal" => {
                    let s = self.decimal_scale()?;
                    self.close_paren()?;
                    Some(Ty::Decimal(s))
                }
                _ => None,
            },
            _ => None,
        }
    }

    fn env_field(&mut self) -> Option<EnvField> {
        match self.atom()?.as_str() {
            "now" => Some(EnvField::Now),
            "step" => Some(EnvField::Step),
            "sender" => Some(EnvField::Sender),
            "deadline" => Some(EnvField::Deadline),
            _ => None,
        }
    }

    fn expr(&mut self) -> Option<Expr> {
        match self.token()? {
            Token::Text(s) => Some(Expr::Text(s)),
            Token::Atom(s) => atom_expr(s),
            Token::Lp => {
                let e = match self.atom()?.as_str() {
                    "unit" => Expr::Unit,
                    "dur" => Expr::Dur(self.int()?),
                    "env" => Expr::Env(self.env_field()?),
                    "call" => Expr::Call(self.ident()?, self.until_close(Reader::expr)?),
                    "new" => Expr::New(self.ident()?, self.until_close(Reader::expr)?),
                    "get" => Expr::Get(Box::new(self.expr()?), self.ident()?),
                    "some" => Expr::Some(Box::new(self.expr()?)),
                    "none" => Expr::None,
                    "ok" => Expr::Ok(Box::new(self.expr()?)),
                    "err" => Expr::Err(Box::new(self.expr()?)),
                    "+" => Expr::Arith(Arith::Add, Box::new(self.expr()?), Box::new(self.expr()?)),
                    "-" => Expr::Arith(Arith::Sub, Box::new(self.expr()?), Box::new(self.expr()?)),
                    "*" => Expr::Arith(Arith::Mul, Box::new(self.expr()?), Box::new(self.expr()?)),
                    "==" => Expr::Eq(Box::new(self.expr()?), Box::new(self.expr()?)),
                    "<" => Expr::Lt(Box::new(self.expr()?), Box::new(self.expr()?)),
                    "and" => Expr::And(Box::new(self.expr()?), Box::new(self.expr()?)),
                    "not" => Expr::Not(Box::new(self.expr()?)),
                    "ConsoleOut.print" => Expr::Op(Op::Print, Box::new(self.expr()?)),
                    "Timer.after" => Expr::Op(Op::After, Box::new(self.expr()?)),
                    "Timer.cancel" => Expr::Op(Op::Cancel, Box::new(self.expr()?)),
                    "f64" => Expr::F64(self.float_atom(Fmt::B64)?),
                    "f32" => Expr::F32(self.float_atom(Fmt::B32)? as u32),
                    "dec" => {
                        let (s, c) = self.decimal_atom()?;
                        Expr::Dec(s, c)
                    }
                    "/" => Expr::Div(Box::new(self.expr()?), Box::new(self.expr()?)),
                    "sqrt" => Expr::Sqrt(Box::new(self.expr()?)),
                    "fma" => Expr::Fma(
                        Box::new(self.expr()?),
                        Box::new(self.expr()?),
                        Box::new(self.expr()?),
                    ),
                    "round" => Expr::Round(self.ty()?, self.mode_atom()?, Box::new(self.expr()?)),
                    "div" => Expr::DivMode(
                        self.ty()?,
                        self.mode_atom()?,
                        Box::new(self.expr()?),
                        Box::new(self.expr()?),
                    ),
                    h => match (lookup(FN1_NAMES, h), lookup(FN2_NAMES, h)) {
                        (Some(f), _) => Expr::Fn1(f, Box::new(self.expr()?)),
                        (None, Some(f)) => {
                            Expr::Fn2(f, Box::new(self.expr()?), Box::new(self.expr()?))
                        }
                        (None, None) => return None,
                    },
                };
                self.close_paren()?;
                Some(e)
            }
            Token::Rp => None,
        }
    }

    fn bind(&mut self) -> Option<Bind> {
        let s = self.atom()?;
        if s == "_" {
            Some(Bind::Wild)
        } else if is_ident(&s) && s != "true" && s != "false" {
            Some(Bind::Name(s))
        } else {
            None
        }
    }

    fn pat(&mut self) -> Option<Pat> {
        match self.token()? {
            Token::Atom(s) => match s.as_str() {
                "true" => Some(Pat::Bool(true)),
                "false" => Some(Pat::Bool(false)),
                _ => None,
            },
            Token::Lp => {
                let h = self.atom()?;
                let binds = self.until_close(Reader::bind)?;
                self.close_paren()?;
                match (h.as_str(), binds.as_slice()) {
                    ("none", []) => Some(Pat::None),
                    ("some", [b]) => Some(Pat::Some(b.clone())),
                    ("ok", [b]) => Some(Pat::Ok(b.clone())),
                    ("err", [b]) => Some(Pat::Err(b.clone())),
                    _ => {
                        if is_ident(&h) {
                            Some(Pat::Con(h, binds))
                        } else {
                            None
                        }
                    }
                }
            }
            _ => None,
        }
    }

    fn outcome(&mut self) -> Option<Option<Expr>> {
        if self.peek_close() {
            Some(None)
        } else {
            self.head("outcome")?;
            let e = self.expr()?;
            self.close_paren()?;
            Some(Some(e))
        }
    }

    fn block(&mut self) -> Option<Block> {
        self.head("block")?;
        let (stmts, tail) = self.block_body()?;
        Some(Block { stmts, tail })
    }

    fn block_body(&mut self) -> Option<(Vec<Stmt>, Tail)> {
        let mut stmts = Vec::new();
        loop {
            self.open_paren()?;
            let h = self.atom()?;
            match h.as_str() {
                "let" => {
                    let x = self.local_name()?;
                    let e = self.expr()?;
                    self.close_paren()?;
                    stmts.push(Stmt::Let(x, e));
                }
                "do" => {
                    let e = self.expr()?;
                    self.close_paren()?;
                    stmts.push(Stmt::Do(e));
                }
                _ => {
                    let t = self.tail(&h)?;
                    self.close_paren()?;
                    return Some((stmts, t));
                }
            }
        }
    }

    fn tail(&mut self, h: &str) -> Option<Tail> {
        match h {
            "value" => {
                let e = self.expr()?;
                self.close_paren()?;
                Some(Tail::Value(e))
            }
            "next" => {
                self.open_paren()?;
                let s = self.ident()?;
                let args = self.until_close(Reader::expr)?;
                self.close_paren()?;
                let o = self.outcome()?;
                self.close_paren()?;
                Some(Tail::Next(s, args, o))
            }
            "stay" => {
                let o = self.outcome()?;
                self.close_paren()?;
                Some(Tail::Stay(o))
            }
            "reject" => {
                let r = self.ident()?;
                self.close_paren()?;
                Some(Tail::Reject(r))
            }
            "answer" => {
                let e = self.expr()?;
                self.close_paren()?;
                Some(Tail::Answer(e))
            }
            "ignore" => {
                self.keyword("stale")?;
                self.close_paren()?;
                Some(Tail::Ignore)
            }
            "impossible" => {
                self.close_paren()?;
                Some(Tail::Impossible)
            }
            "match" => {
                let e = self.expr()?;
                let arms = self.some1(Reader::arm)?;
                self.close_paren()?;
                Some(Tail::Match(e, arms))
            }
            _ => None,
        }
    }

    fn arm(&mut self) -> Option<Arm> {
        self.head("arm")?;
        let p = self.pat()?;
        let b = self.block()?;
        self.close_paren()?;
        Some(Arm { pat: p, body: b })
    }

    fn param(&mut self) -> Option<Param> {
        self.open_paren()?;
        let x = self.local_name()?;
        let t = self.ty()?;
        self.close_paren()?;
        Some(Param { name: x, ty: t })
    }

    fn params(&mut self) -> Option<Vec<Param>> {
        self.open_paren()?;
        let ps = self.until_close(Reader::param)?;
        self.close_paren()?;
        Some(ps)
    }

    fn variant(&mut self) -> Option<Variant> {
        self.open_paren()?;
        let n = self.decl_name()?;
        let ts = self.until_close(Reader::ty)?;
        self.close_paren()?;
        Some(Variant {
            name: n,
            fields: ts,
        })
    }

    fn optional_atom(&mut self, word: &str) -> bool {
        match self.tokens.get(self.pos) {
            Some(Token::Atom(s)) if s == word => {
                self.pos += 1;
                true
            }
            _ => false,
        }
    }

    fn uses(&mut self, timer: bool) -> Option<Vec<Effect>> {
        self.head("uses")?;
        let c = self.optional_atom("ConsoleOut");
        let t = if timer {
            self.optional_atom("Timer")
        } else {
            false
        };
        self.close_paren()?;
        let mut effects = Vec::new();
        if c {
            effects.push(Effect::ConsoleOut);
        }
        if t {
            effects.push(Effect::Timer);
        }
        Some(effects)
    }

    fn r#fn(&mut self) -> Option<Fn> {
        let n = self.decl_name()?;
        let ps = self.params()?;
        let r = self.ty()?;
        let u = self.uses(false)?;
        let b = self.block()?;
        self.close_paren()?;
        Some(Fn {
            name: n,
            params: ps,
            result: r,
            uses: u,
            body: b,
        })
    }

    fn msg(&mut self) -> Option<Msg> {
        self.open_paren()?;
        match self.atom()?.as_str() {
            "command" => {
                let n = self.decl_name()?;
                let ps = self.params()?;
                let r = self.ty()?;
                self.head("rejects")?;
                let rs = self.until_close(Reader::ident)?;
                self.close_paren()?;
                let role = if self.peek_close() {
                    None
                } else {
                    self.head("by")?;
                    let x = self.ident()?;
                    self.close_paren()?;
                    Some(x)
                };
                self.close_paren()?;
                Some(Msg::Command {
                    name: n,
                    params: ps,
                    result: r,
                    rejects: rs,
                    role,
                })
            }
            "query" => {
                let n = self.decl_name()?;
                let ps = self.params()?;
                let r = self.ty()?;
                self.close_paren()?;
                Some(Msg::Query {
                    name: n,
                    params: ps,
                    result: r,
                })
            }
            _ => None,
        }
    }

    fn state(&mut self) -> Option<State> {
        self.head("state")?;
        let n = self.decl_name()?;
        let fs = self.until_close(Reader::param)?;
        self.close_paren()?;
        Some(State {
            name: n,
            fields: fs,
        })
    }

    fn group(&mut self) -> Option<Group> {
        self.head("group")?;
        let n = self.decl_name()?;
        let ms = self.some1(Reader::ident)?;
        self.close_paren()?;
        Some(Group {
            name: n,
            members: ms,
        })
    }

    fn cell(&mut self) -> Option<Cell> {
        self.head("on")?;
        let i = self.ident()?;
        let b = self.block()?;
        self.close_paren()?;
        Some(Cell { input: i, body: b })
    }

    fn r#in(&mut self) -> Option<In> {
        self.head("in")?;
        let t = self.ident()?;
        let cs = self.some1(Reader::cell)?;
        self.close_paren()?;
        Some(In {
            target: t,
            cells: cs,
        })
    }

    fn machine(&mut self) -> Option<Machine> {
        let n = self.decl_name()?;
        self.head("key")?;
        let k = self.ty()?;
        self.close_paren()?;
        self.head("protocol")?;
        let q = self.ident()?;
        self.close_paren()?;
        let u = self.uses(true)?;
        self.head("init")?;
        let i = self.ident()?;
        self.close_paren()?;
        let ss = non_empty(self.headed("state", Reader::state)?)?;
        let gs = self.headed("group", Reader::group)?;
        let ins = non_empty(self.headed("in", Reader::r#in)?)?;
        self.close_paren()?;
        Some(Machine {
            name: n,
            key: k,
            protocol: q,
            uses: u,
            init: i,
            states: ss,
            groups: gs,
            ins,
        })
    }

    fn deployment(&mut self) -> Option<Deployment> {
        let n = self.decl_name()?;
        self.head("platform")?;
        self.keyword("cli")?;
        self.close_paren()?;
        self.head("entry")?;
        let e = self.ident()?;
        self.close_paren()?;
        self.close_paren()?;
        Some(Deployment {
            name: n,
            platform: Platform::Cli,
            entry: e,
        })
    }

    fn xexpr(&mut self, stored: bool) -> Option<XExpr> {
        match self.token()? {
            Token::Text(s) => Some(XExpr::Text(s)),
            Token::Atom(s) => match parse_int(&s) {
                Some(n) => Some(XExpr::Int(n)),
                None => {
                    if s == "true" {
                        Some(XExpr::Bool(true))
                    } else if s == "false" {
                        Some(XExpr::Bool(false))
                    } else if is_ident(&s) {
                        Some(XExpr::Var(s))
                    } else {
                        None
                    }
                }
            },
            Token::Lp => {
                let x = match self.atom()?.as_str() {
                    "unit" => XExpr::Unit,
                    "dur" => XExpr::Dur(self.int()?),
                    "new" => XExpr::New(self.ident()?, self.until_close(|r| r.xexpr(stored))?),
                    "some" => XExpr::Some(Box::new(self.xexpr(stored)?)),
                    "none" => XExpr::None,
                    "ok" => XExpr::Ok(Box::new(self.xexpr(stored)?)),
                    "err" => XExpr::Err(Box::new(self.xexpr(stored)?)),
                    "f64" => XExpr::F64(self.float_atom(Fmt::B64)?),
                    "f32" => XExpr::F32(self.float_atom(Fmt::B32)? as u32),
                    "dec" => {
                        let (s, c) = self.decimal_atom()?;
                        XExpr::Dec(s, c)
                    }
                    "step" => {
                        let a = self.atom()?;
                        match parse_int(&a) {
                            Some(n) => XExpr::Step(n),
                            None => {
                                if stored && is_ident(&a) {
                                    XExpr::StepOf(
                                        a,
                                        Box::new(self.xexpr(stored)?),
                                        self.int()?,
                                        self.int()?,
                                    )
                                } else {
                                    return None;
                                }
                            }
                        }
                    }
                    "ticket" => {
                        let a = self.atom()?;
                        match parse_int(&a) {
                            Some(n) => XExpr::Ticket(n),
                            None => {
                                if stored && is_ident(&a) {
                                    XExpr::TicketOf(
                                        a,
                                        Box::new(self.xexpr(stored)?),
                                        self.int()?,
                                        self.int()?,
                                        self.int()?,
                                    )
                                } else {
                                    return None;
                                }
                            }
                        }
                    }
                    "time" if stored => XExpr::Time(self.int()?),
                    "principal" if stored => XExpr::Principal(self.text_token()?),
                    _ => return None,
                };
                self.close_paren()?;
                Some(x)
            }
            Token::Rp => None,
        }
    }

    fn fact(&mut self) -> Option<Fact> {
        self.open_paren()?;
        let f = match self.atom()?.as_str() {
            "outcome" => Fact::Outcome(self.xexpr(false)?),
            "reject" => Fact::Reject(self.ident()?),
            "answer" => Fact::Answer(self.xexpr(false)?),
            "refused" => {
                self.keyword("forbidden")?;
                Fact::Refused
            }
            "fault" => Fact::Fault(self.ident()?),
            "ignored" => Fact::Ignored,
            "state" => Fact::State(self.ident()?, self.until_close(|r| r.xexpr(false))?),
            _ => return None,
        };
        self.close_paren()?;
        Some(f)
    }

    fn expect(&mut self) -> Option<Vec<Fact>> {
        self.head("expect")?;
        let fs = self.until_close(Reader::fact)?;
        self.close_paren()?;
        Some(fs)
    }

    fn send_args(&mut self) -> Option<Vec<XExpr>> {
        let mut xs = Vec::new();
        while self.peek_head() != Some("expect") {
            xs.push(self.xexpr(false)?);
        }
        Some(xs)
    }

    fn line(&mut self) -> Option<Line> {
        self.open_paren()?;
        let l = match self.atom()?.as_str() {
            "send" => {
                let a = self.ident()?;
                let i = self.ident()?;
                let args = self.send_args()?;
                let fs = self.expect()?;
                Line::Send {
                    actor: a,
                    input: i,
                    args,
                    facts: fs,
                }
            }
            "fire" => {
                let t = self.xexpr(false)?;
                let fs = self.expect()?;
                Line::Fire {
                    ticket: t,
                    facts: fs,
                }
            }
            _ => return None,
        };
        self.close_paren()?;
        Some(l)
    }

    fn actor(&mut self) -> Option<Actor> {
        self.head("actor")?;
        let n = self.local_name()?;
        let rs = self.until_close(Reader::ident)?;
        self.close_paren()?;
        Some(Actor { name: n, roles: rs })
    }

    fn field(&mut self) -> Option<(Param, Option<XExpr>)> {
        self.open_paren()?;
        let x = self.ident()?;
        let t = self.ty()?;
        let init = if self.peek_close() {
            None
        } else {
            self.head("init")?;
            let v = self.xexpr(true)?;
            self.close_paren()?;
            Some(v)
        };
        self.close_paren()?;
        Some((Param { name: x, ty: t }, init))
    }

    fn expected(&mut self) -> Option<Option<XExpr>> {
        self.open_paren()?;
        let x = match self.atom()?.as_str() {
            "value" => Some(self.xexpr(true)?),
            "invalid" => None,
            _ => return None,
        };
        self.close_paren()?;
        Some(x)
    }

    fn example(&mut self) -> Option<Example> {
        let n = self.decl_name()?;
        self.head("machine")?;
        let m = self.ident()?;
        self.close_paren()?;
        self.head("key")?;
        let k = self.xexpr(false)?;
        self.close_paren()?;
        let actors = self.headed("actor", Reader::actor)?;
        let lines = self.some1(Reader::line)?;
        self.close_paren()?;
        Some(Example {
            name: n,
            machine: m,
            key: k,
            actors,
            lines,
        })
    }

    fn item(&mut self) -> Option<Item> {
        self.open_paren()?;
        match self.atom()?.as_str() {
            "newtype" => {
                let n = self.decl_name()?;
                let t = self.ty()?;
                self.close_paren()?;
                Some(Item::Newtype(n, t))
            }
            "record" => {
                let n = self.decl_name()?;
                let mut fs = self.until_close(Reader::field)?;
                let rest = fs.split_off(fs.iter().take_while(|f| f.1.is_none()).count());
                let inits = init_fields(rest)?;
                let plain = non_empty(fs)?;
                self.close_paren()?;
                Some(Item::Record(
                    n,
                    plain.into_iter().map(|f| f.0).collect(),
                    inits,
                ))
            }
            "enum" => {
                let n = self.decl_name()?;
                let vs = self.some1(Reader::variant)?;
                self.close_paren()?;
                Some(Item::Enum(n, vs))
            }
            "role" => {
                let n = self.decl_name()?;
                self.close_paren()?;
                Some(Item::Role(n))
            }
            "fn" => Some(Item::Fn(self.r#fn()?)),
            "protocol" => {
                let n = self.decl_name()?;
                let ms = self.some1(Reader::msg)?;
                self.close_paren()?;
                Some(Item::Protocol(Protocol { name: n, msgs: ms }))
            }
            "machine" => Some(Item::Machine(self.machine()?)),
            "deployment" => Some(Item::Deployment(self.deployment()?)),
            "example" => Some(Item::Example(self.example()?)),
            "decode" => {
                let n = self.decl_name()?;
                let t = self.ty()?;
                let chars: Vec<char> = self.text_token()?.chars().collect();
                let frame = hex_bytes(&chars)?;
                let x = self.expected()?;
                self.close_paren()?;
                Some(Item::Decode(n, t, frame, x))
            }
            _ => None,
        }
    }

    fn program(&mut self) -> Option<Program> {
        self.head("program")?;
        let items = self.until_close(Reader::item)?;
        self.close_paren()?;
        Some(Program { items })
    }
}

pub fn read(bytes: &[u8]) -> Option<Program> {
    let text = std::str::from_utf8(bytes).ok()?;
    let chars: Vec<char> = text.chars().collect();
    let tokens = lex(Lex::Gap, &chars, Vec::new())?;
    let mut reader = Reader { tokens, pos: 0 };
    let p = reader.program()?;
    if reader.pos == reader.tokens.len() {
        Some(p)
    } else {
        None
    }
}
