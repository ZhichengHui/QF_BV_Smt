//! Command-line front end: reads an SMT-LIB 2 script in the logic QF_BV, builds the terms of
//! `bvsmt` and answers `check-sat` and `get-model`.
//!
//! This front end is not verified. Every bit-vector operation is passed to the solver as it is;
//! the front end only parses, handles the Core-theory parts (`Bool`, the Boolean connectives,
//! chainable `=`, pairwise `distinct`, `let`, `define-fun`) and reads the model. Booleans are
//! bit-vectors of width 1. Every `let`-bound term and every argument of a defined function
//! becomes a definition of the problem, so terms are not copied.

use bvsmt::{Answer, Op, Problem, Term, solve};
use std::collections::HashMap;
use std::io::Read;

// ---------------------------------------------------------------------------------------------
// S-expressions

#[derive(Clone, Debug)]
enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}

fn tokenize(src: &str) -> Result<Vec<String>, String> {
    let mut toks = Vec::new();
    let cs: Vec<char> = src.chars().collect();
    let mut i = 0;
    while i < cs.len() {
        let c = cs[i];
        if c == ';' {
            while i < cs.len() && cs[i] != '\n' {
                i += 1;
            }
        } else if c.is_whitespace() {
            i += 1;
        } else if c == '(' || c == ')' {
            toks.push(c.to_string());
            i += 1;
        } else if c == '|' {
            let mut j = i + 1;
            while j < cs.len() && cs[j] != '|' {
                j += 1;
            }
            if j == cs.len() {
                return Err("unterminated quoted symbol".into());
            }
            toks.push(cs[i..=j].iter().collect());
            i = j + 1;
        } else if c == '"' {
            let mut j = i + 1;
            loop {
                if j >= cs.len() {
                    return Err("unterminated string".into());
                }
                if cs[j] == '"' {
                    if j + 1 < cs.len() && cs[j + 1] == '"' {
                        j += 2;
                        continue;
                    }
                    break;
                }
                j += 1;
            }
            toks.push(cs[i..=j].iter().collect());
            i = j + 1;
        } else {
            let mut j = i;
            while j < cs.len() && !cs[j].is_whitespace() && cs[j] != '(' && cs[j] != ')' && cs[j] != ';' {
                j += 1;
            }
            toks.push(cs[i..j].iter().collect());
            i = j;
        }
    }
    Ok(toks)
}

fn parse_sexps(toks: &[String]) -> Result<Vec<Sexp>, String> {
    let mut stack: Vec<Vec<Sexp>> = vec![Vec::new()];
    for t in toks {
        if t == "(" {
            stack.push(Vec::new());
        } else if t == ")" {
            let l = stack.pop().unwrap();
            match stack.last_mut() {
                Some(top) => top.push(Sexp::List(l)),
                None => return Err("unbalanced ')'".into()),
            }
            if stack.is_empty() {
                return Err("unbalanced ')'".into());
            }
        } else {
            stack.last_mut().unwrap().push(Sexp::Atom(t.clone()));
        }
    }
    if stack.len() != 1 {
        return Err("unbalanced '('".into());
    }
    Ok(stack.pop().unwrap())
}

fn atom(s: &Sexp) -> Option<&str> {
    match s {
        Sexp::Atom(a) => Some(a.as_str()),
        Sexp::List(_) => None,
    }
}

fn symbol_name(s: &str) -> String {
    if s.len() >= 2 && s.starts_with('|') && s.ends_with('|') {
        s[1..s.len() - 1].to_string()
    } else {
        s.to_string()
    }
}

fn num(s: &Sexp) -> Result<usize, String> {
    atom(s).and_then(|a| a.parse().ok()).ok_or_else(|| format!("expected a numeral, got {:?}", s))
}

// ---------------------------------------------------------------------------------------------
// Terms

fn clone_op(op: &Op) -> Op {
    match op {
        Op::And => Op::And,
        Op::Or => Op::Or,
        Op::Xor => Op::Xor,
        Op::Nand => Op::Nand,
        Op::Nor => Op::Nor,
        Op::Xnor => Op::Xnor,
        Op::Comp => Op::Comp,
        Op::Add => Op::Add,
        Op::Sub => Op::Sub,
        Op::Mul => Op::Mul,
        Op::Udiv => Op::Udiv,
        Op::Urem => Op::Urem,
        Op::Sdiv => Op::Sdiv,
        Op::Srem => Op::Srem,
        Op::Smod => Op::Smod,
        Op::Shl => Op::Shl,
        Op::Lshr => Op::Lshr,
        Op::Ashr => Op::Ashr,
        Op::Concat => Op::Concat,
        Op::Eq => Op::Eq,
        Op::Distinct => Op::Distinct,
        Op::Ult => Op::Ult,
        Op::Ule => Op::Ule,
        Op::Ugt => Op::Ugt,
        Op::Uge => Op::Uge,
        Op::Slt => Op::Slt,
        Op::Sle => Op::Sle,
        Op::Sgt => Op::Sgt,
        Op::Sge => Op::Sge,
    }
}

fn clone_term(t: &Term) -> Term {
    match t {
        Term::Const(bs) => Term::Const(bs.clone()),
        Term::Var(i) => Term::Var(*i),
        Term::Ref(i) => Term::Ref(*i),
        Term::Not(a) => Term::Not(Box::new(clone_term(a))),
        Term::Neg(a) => Term::Neg(Box::new(clone_term(a))),
        Term::Bin(op, a, b) => Term::Bin(clone_op(op), Box::new(clone_term(a)), Box::new(clone_term(b))),
        Term::Extract(h, l, a) => Term::Extract(*h, *l, Box::new(clone_term(a))),
        Term::Repeat(i, a) => Term::Repeat(*i, Box::new(clone_term(a))),
        Term::ZeroExtend(i, a) => Term::ZeroExtend(*i, Box::new(clone_term(a))),
        Term::SignExtend(i, a) => Term::SignExtend(*i, Box::new(clone_term(a))),
        Term::RotateLeft(i, a) => Term::RotateLeft(*i, Box::new(clone_term(a))),
        Term::RotateRight(i, a) => Term::RotateRight(*i, Box::new(clone_term(a))),
        Term::Ite(c, a, b) => Term::Ite(Box::new(clone_term(c)), Box::new(clone_term(a)), Box::new(clone_term(b))),
    }
}

/// Sorts: `Bool` (represented as width 1) or `(_ BitVec w)`.
#[derive(Clone, Copy, PartialEq, Debug)]
enum Sort {
    Bool,
    Bv(usize),
}

impl Sort {
    fn width(self) -> usize {
        match self {
            Sort::Bool => 1,
            Sort::Bv(w) => w,
        }
    }
}

#[derive(Clone)]
enum Binding {
    Var(usize, Sort),
    Ref(usize, Sort),
}

struct Macro {
    params: Vec<(String, Sort)>,
    sort: Sort,
    body: Sexp,
}

struct Builder {
    widths: Vec<usize>,
    defs: Vec<Term>,
    asserts: Vec<Term>,
    /// Declared variables in order, for the model.
    decls: Vec<(String, Sort)>,
    globals: HashMap<String, Binding>,
    macros: HashMap<String, Macro>,
}

fn bin(op: Op, a: Term, b: Term) -> Term {
    Term::Bin(op, Box::new(a), Box::new(b))
}

fn not(a: Term) -> Term {
    Term::Not(Box::new(a))
}

fn ite(c: Term, a: Term, b: Term) -> Term {
    Term::Ite(Box::new(c), Box::new(a), Box::new(b))
}

fn tt() -> Term {
    Term::Const(vec![true])
}

/// The left-associative application of `op` to at least one term.
fn fold_left(op: Op, ts: Vec<Term>) -> Term {
    let mut it = ts.into_iter();
    let mut r = it.next().unwrap();
    for t in it {
        r = bin(clone_op(&op), r, t);
    }
    r
}

/// The binary operator named `f`, if it is one of QF_BV.
fn bv_op(f: &str) -> Option<Op> {
    Some(match f {
        "bvand" => Op::And,
        "bvor" => Op::Or,
        "bvxor" => Op::Xor,
        "bvnand" => Op::Nand,
        "bvnor" => Op::Nor,
        "bvxnor" => Op::Xnor,
        "bvcomp" => Op::Comp,
        "bvadd" => Op::Add,
        "bvsub" => Op::Sub,
        "bvmul" => Op::Mul,
        "bvudiv" => Op::Udiv,
        "bvurem" => Op::Urem,
        "bvsdiv" => Op::Sdiv,
        "bvsrem" => Op::Srem,
        "bvsmod" => Op::Smod,
        "bvshl" => Op::Shl,
        "bvlshr" => Op::Lshr,
        "bvashr" => Op::Ashr,
        "concat" => Op::Concat,
        "bvult" => Op::Ult,
        "bvule" => Op::Ule,
        "bvugt" => Op::Ugt,
        "bvuge" => Op::Uge,
        "bvslt" => Op::Slt,
        "bvsle" => Op::Sle,
        "bvsgt" => Op::Sgt,
        "bvsge" => Op::Sge,
        _ => return None,
    })
}

impl Builder {
    fn new() -> Self {
        Builder {
            widths: Vec::new(),
            defs: Vec::new(),
            asserts: Vec::new(),
            decls: Vec::new(),
            globals: HashMap::new(),
            macros: HashMap::new(),
        }
    }

    /// Adds `t` as a definition; the result refers to it.
    fn share(&mut self, t: Term) -> usize {
        self.defs.push(t);
        self.defs.len() - 1
    }

    fn sort_of(&self, s: &Sexp) -> Result<Sort, String> {
        match s {
            Sexp::Atom(a) if a == "Bool" => Ok(Sort::Bool),
            Sexp::List(l) if l.len() == 3 && atom(&l[0]) == Some("_") && atom(&l[1]) == Some("BitVec") => {
                let w = num(&l[2])?;
                if w == 0 {
                    return Err("bit-vector width 0".into());
                }
                Ok(Sort::Bv(w))
            }
            _ => Err(format!("unsupported sort {:?}", s)),
        }
    }

    fn lookup(&self, env: &[(String, Binding)], name: &str) -> Option<Binding> {
        for (n, b) in env.iter().rev() {
            if n == name {
                return Some(b.clone());
            }
        }
        self.globals.get(name).cloned()
    }

    fn elab_bool(&mut self, env: &mut Vec<(String, Binding)>, s: &Sexp) -> Result<Term, String> {
        let (t, sort) = self.elab(env, s)?;
        if sort != Sort::Bool {
            return Err(format!("expected a Boolean term: {:?}", s));
        }
        Ok(t)
    }

    fn elab_args(&mut self, env: &mut Vec<(String, Binding)>, args: &[Sexp]) -> Result<Vec<(Term, Sort)>, String> {
        args.iter().map(|a| self.elab(env, a)).collect()
    }

    fn elab(&mut self, env: &mut Vec<(String, Binding)>, s: &Sexp) -> Result<(Term, Sort), String> {
        match s {
            Sexp::Atom(a) => self.elab_atom(env, a),
            Sexp::List(l) if l.is_empty() => Err("empty application".into()),
            Sexp::List(l) => {
                if let Sexp::List(head) = &l[0] {
                    return self.elab_indexed(env, head, &l[1..]);
                }
                let f = atom(&l[0]).unwrap();
                if f == "_" {
                    return self.elab_bv_literal(l);
                }
                match f {
                    "let" => self.elab_let(env, l),
                    "!" => self.elab(env, &l[1]),
                    _ => {
                        let args = self.elab_args(env, &l[1..])?;
                        self.apply(f, args)
                    }
                }
            }
        }
    }

    fn elab_atom(&mut self, env: &[(String, Binding)], a: &str) -> Result<(Term, Sort), String> {
        if a == "true" {
            return Ok((tt(), Sort::Bool));
        }
        if a == "false" {
            return Ok((Term::Const(vec![false]), Sort::Bool));
        }
        if let Some(b) = a.strip_prefix("#b") {
            let bits: Vec<bool> = b.chars().rev().map(|c| c == '1').collect();
            let w = bits.len();
            return Ok((Term::Const(bits), Sort::Bv(w)));
        }
        if let Some(h) = a.strip_prefix("#x") {
            let mut bits = Vec::new();
            for c in h.chars().rev() {
                let d = c.to_digit(16).ok_or_else(|| format!("bad hex literal {}", a))?;
                for i in 0..4 {
                    bits.push((d >> i) & 1 == 1);
                }
            }
            let w = bits.len();
            return Ok((Term::Const(bits), Sort::Bv(w)));
        }
        let name = symbol_name(a);
        match self.lookup(env, &name) {
            Some(Binding::Var(i, sort)) => Ok((Term::Var(i), sort)),
            Some(Binding::Ref(i, sort)) => Ok((Term::Ref(i), sort)),
            None => {
                if self.macros.contains_key(&name) {
                    return self.apply(&name, Vec::new());
                }
                Err(format!("unknown symbol {}", a))
            }
        }
    }

    /// `(_ bvN w)`: the decimal numeral `N` modulo `2^w`.
    fn elab_bv_literal(&self, l: &[Sexp]) -> Result<(Term, Sort), String> {
        let digits = match (l.len(), atom(&l[1]).and_then(|a| a.strip_prefix("bv"))) {
            (3, Some(d)) if !d.is_empty() && d.chars().all(|c| c.is_ascii_digit()) => d,
            _ => return Err(format!("unsupported term {:?}", l)),
        };
        let w = num(&l[2])?;
        if w == 0 {
            return Err("bit-vector width 0".into());
        }
        // Repeated halving of the decimal digits gives the bits, least significant first.
        let mut ds: Vec<u32> = digits.chars().map(|c| c.to_digit(10).unwrap()).collect();
        let mut bits = Vec::new();
        for _ in 0..w {
            let mut rem = 0;
            for d in ds.iter_mut() {
                let cur = rem * 10 + *d;
                *d = cur / 2;
                rem = cur % 2;
            }
            bits.push(rem == 1);
        }
        Ok((Term::Const(bits), Sort::Bv(w)))
    }

    fn elab_let(&mut self, env: &mut Vec<(String, Binding)>, l: &[Sexp]) -> Result<(Term, Sort), String> {
        if l.len() != 3 {
            return Err("malformed let".into());
        }
        let binds = match &l[1] {
            Sexp::List(b) => b,
            _ => return Err("malformed let".into()),
        };
        let mut new = Vec::new();
        for b in binds {
            match b {
                Sexp::List(p) if p.len() == 2 => {
                    let name = symbol_name(atom(&p[0]).ok_or("malformed let binding")?);
                    let (t, sort) = self.elab(env, &p[1])?;
                    let i = self.share(t);
                    new.push((name, Binding::Ref(i, sort)));
                }
                _ => return Err("malformed let binding".into()),
            }
        }
        let n = env.len();
        env.extend(new);
        let r = self.elab(env, &l[2]);
        env.truncate(n);
        r
    }

    /// Indexed operators `((_ f i j) args)`.
    fn elab_indexed(&mut self, env: &mut Vec<(String, Binding)>, head: &[Sexp], args: &[Sexp]) -> Result<(Term, Sort), String> {
        if head.len() < 2 || atom(&head[0]) != Some("_") {
            return Err(format!("unsupported application {:?}", head));
        }
        let f = atom(&head[1]).ok_or("bad indexed operator")?;
        let idx: Vec<usize> = head[2..].iter().map(num).collect::<Result<_, _>>()?;
        let mut a = self.elab_args(env, args)?;
        if a.len() != 1 {
            return Err(format!("{} takes one argument", f));
        }
        let (t, sort) = a.pop().unwrap();
        let w = match sort {
            Sort::Bv(w) => w,
            Sort::Bool => return Err(format!("{} on a Boolean", f)),
        };
        let t = Box::new(t);
        match (f, idx.as_slice()) {
            ("extract", [hi, lo]) => {
                if lo > hi || *hi >= w {
                    return Err("extract out of range".into());
                }
                Ok((Term::Extract(*hi, *lo, t), Sort::Bv(hi - lo + 1)))
            }
            ("repeat", [i]) => {
                if *i == 0 {
                    return Err("repeat 0".into());
                }
                Ok((Term::Repeat(*i, t), Sort::Bv(w * i)))
            }
            ("zero_extend", [i]) => Ok((Term::ZeroExtend(*i, t), Sort::Bv(w + i))),
            ("sign_extend", [i]) => Ok((Term::SignExtend(*i, t), Sort::Bv(w + i))),
            ("rotate_left", [i]) => Ok((Term::RotateLeft(*i, t), sort)),
            ("rotate_right", [i]) => Ok((Term::RotateRight(*i, t), sort)),
            _ => Err(format!("unsupported indexed operator {}", f)),
        }
    }

    fn apply(&mut self, f: &str, args: Vec<(Term, Sort)>) -> Result<(Term, Sort), String> {
        let name = symbol_name(f);
        if self.macros.contains_key(&name) {
            return self.apply_macro(&name, args);
        }
        let sorts: Vec<Sort> = args.iter().map(|a| a.1).collect();
        let mut ts: Vec<Term> = args.into_iter().map(|a| a.0).collect();
        let all_bool = sorts.iter().all(|s| *s == Sort::Bool);
        let same = sorts.windows(2).all(|p| p[0] == p[1]);
        let bv = !sorts.is_empty() && sorts.iter().all(|s| matches!(s, Sort::Bv(_)));
        let arity = |n: usize| -> Result<(), String> {
            if sorts.len() == n { Ok(()) } else { Err(format!("{} takes {} arguments", f, n)) }
        };
        let bool_r = |t: Term| Ok((t, Sort::Bool));
        match f {
            // The Boolean connectives, on bit-vectors of width 1.
            "not" => {
                arity(1)?;
                if !all_bool {
                    return Err("not on a non-Boolean".into());
                }
                bool_r(not(ts.pop().unwrap()))
            }
            "and" | "or" | "xor" => {
                if !all_bool || ts.is_empty() {
                    return Err(format!("{} needs Boolean arguments", f));
                }
                let op = match f {
                    "and" => Op::And,
                    "or" => Op::Or,
                    _ => Op::Xor,
                };
                bool_r(fold_left(op, ts))
            }
            "=>" => {
                if !all_bool || ts.len() < 2 {
                    return Err("=> needs Boolean arguments".into());
                }
                // Right associative.
                let mut r = ts.pop().unwrap();
                while let Some(t) = ts.pop() {
                    r = bin(Op::Or, not(t), r);
                }
                bool_r(r)
            }
            // `=` is chainable and `distinct` pairwise: conjunctions of the binary operators.
            "=" | "distinct" => {
                if ts.len() < 2 || !same {
                    return Err(format!("{} needs at least two arguments of one sort", f));
                }
                let ts: Vec<Term> = if ts.len() == 2 {
                    ts
                } else {
                    ts.into_iter().map(|t| Term::Ref(self.share(t))).collect()
                };
                let mut conj: Vec<Term> = Vec::new();
                if f == "=" {
                    for i in 0..ts.len() - 1 {
                        conj.push(bin(Op::Eq, clone_term(&ts[i]), clone_term(&ts[i + 1])));
                    }
                } else {
                    for i in 0..ts.len() {
                        for j in i + 1..ts.len() {
                            conj.push(bin(Op::Distinct, clone_term(&ts[i]), clone_term(&ts[j])));
                        }
                    }
                }
                bool_r(fold_left(Op::And, conj))
            }
            "ite" => {
                arity(3)?;
                if sorts[0] != Sort::Bool || sorts[1] != sorts[2] {
                    return Err("ill-sorted ite".into());
                }
                let e = ts.pop().unwrap();
                let t = ts.pop().unwrap();
                let c = ts.pop().unwrap();
                Ok((ite(c, t, e), sorts[1]))
            }
            _ => {
                if !bv {
                    return Err(format!("unknown function or ill-sorted application: {}", f));
                }
                self.apply_bv(f, ts, &sorts, same)
            }
        }
    }

    /// The operators of QF_BV, each passed to the solver as it is.
    fn apply_bv(&mut self, f: &str, mut ts: Vec<Term>, sorts: &[Sort], same: bool) -> Result<(Term, Sort), String> {
        let n = ts.len();
        let w = sorts[0].width();
        if f == "concat" {
            if n != 2 {
                return Err("concat takes 2 arguments".into());
            }
            let b = ts.pop().unwrap();
            let a = ts.pop().unwrap();
            return Ok((bin(Op::Concat, a, b), Sort::Bv(w + sorts[1].width())));
        }
        if !same {
            return Err(format!("{}: operands of different widths", f));
        }
        if f == "bvnot" || f == "bvneg" {
            if n != 1 {
                return Err(format!("{} takes 1 argument", f));
            }
            let a = Box::new(ts.pop().unwrap());
            return Ok((if f == "bvnot" { Term::Not(a) } else { Term::Neg(a) }, Sort::Bv(w)));
        }
        let op = bv_op(f).ok_or_else(|| format!("unknown function {}", f))?;
        // These operators have the :left-assoc attribute and may take more than two arguments.
        let assoc = matches!(f, "bvand" | "bvor" | "bvxor" | "bvxnor" | "bvadd" | "bvmul");
        if (assoc && n < 2) || (!assoc && n != 2) {
            return Err(format!("{}: wrong number of arguments", f));
        }
        let sort = match op {
            Op::Comp => Sort::Bv(1),
            Op::Ult | Op::Ule | Op::Ugt | Op::Uge | Op::Slt | Op::Sle | Op::Sgt | Op::Sge => Sort::Bool,
            _ => Sort::Bv(w),
        };
        Ok((fold_left(op, ts), sort))
    }

    fn apply_macro(&mut self, name: &str, args: Vec<(Term, Sort)>) -> Result<(Term, Sort), String> {
        let m = self.macros.get(name).unwrap();
        if m.params.len() != args.len() {
            return Err(format!("{} takes {} arguments", name, m.params.len()));
        }
        let params = m.params.clone();
        let sort = m.sort;
        let body = m.body.clone();
        let mut env = Vec::new();
        for ((p, ps), (t, s)) in params.into_iter().zip(args) {
            if ps != s {
                return Err(format!("ill-sorted argument of {}", name));
            }
            let i = self.share(t);
            env.push((p, Binding::Ref(i, s)));
        }
        let (t, s) = self.elab(&mut env, &body)?;
        if s != sort {
            return Err(format!("body of {} has the wrong sort", name));
        }
        Ok((t, s))
    }

    fn declare(&mut self, name: String, sort: Sort) {
        self.widths.push(sort.width());
        let i = self.widths.len() - 1;
        self.decls.push((name.clone(), sort));
        self.globals.insert(name, Binding::Var(i, sort));
    }

    fn problem(&self) -> Problem {
        Problem {
            widths: self.widths.clone(),
            defs: self.defs.iter().map(clone_term).collect(),
            asserts: self.asserts.iter().map(clone_term).collect(),
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Commands

fn bits_literal(bits: &[bool]) -> String {
    let s: String = bits.iter().rev().map(|b| if *b { '1' } else { '0' }).collect();
    format!("#b{}", s)
}

fn run(src: &str) -> Result<(), String> {
    let cmds = parse_sexps(&tokenize(src)?)?;
    let mut b = Builder::new();
    let mut last: Option<Vec<Vec<bool>>> = None;
    for c in &cmds {
        let l = match c {
            Sexp::List(l) if !l.is_empty() => l,
            _ => return Err(format!("not a command: {:?}", c)),
        };
        let name = atom(&l[0]).ok_or("not a command")?;
        match name {
            // Accepted silently.
            "set-logic" | "set-option" | "set-info" => {}
            "declare-const" => {
                let n = symbol_name(atom(&l[1]).ok_or("bad declare-const")?);
                let s = b.sort_of(&l[2])?;
                b.declare(n, s);
            }
            "declare-fun" => {
                let n = symbol_name(atom(&l[1]).ok_or("bad declare-fun")?);
                match &l[2] {
                    Sexp::List(ps) if ps.is_empty() => {}
                    _ => return Err("uninterpreted functions are not supported (QF_BV)".into()),
                }
                let s = b.sort_of(&l[3])?;
                b.declare(n, s);
            }
            "define-fun" => {
                let n = symbol_name(atom(&l[1]).ok_or("bad define-fun")?);
                let ps = match &l[2] {
                    Sexp::List(ps) => ps,
                    _ => return Err("bad define-fun".into()),
                };
                let mut params = Vec::new();
                for p in ps {
                    match p {
                        Sexp::List(q) if q.len() == 2 => {
                            params.push((symbol_name(atom(&q[0]).ok_or("bad parameter")?), b.sort_of(&q[1])?));
                        }
                        _ => return Err("bad parameter".into()),
                    }
                }
                let sort = b.sort_of(&l[3])?;
                if params.is_empty() {
                    let (t, s) = b.elab(&mut Vec::new(), &l[4])?;
                    if s != sort {
                        return Err(format!("body of {} has the wrong sort", n));
                    }
                    let i = b.share(t);
                    b.globals.insert(n, Binding::Ref(i, sort));
                } else {
                    b.macros.insert(n, Macro { params, sort, body: l[4].clone() });
                }
            }
            "assert" => {
                let t = b.elab_bool(&mut Vec::new(), &l[1])?;
                b.asserts.push(t);
            }
            "check-sat" => match solve(&b.problem()) {
                Answer::Sat(m) => {
                    println!("sat");
                    last = Some(m);
                }
                Answer::Unsat => {
                    println!("unsat");
                    last = None;
                }
            },
            "get-model" => match &last {
                Some(m) => {
                    println!("(");
                    for (i, (n, s)) in b.decls.iter().enumerate() {
                        match s {
                            Sort::Bool => println!("  (define-fun {} () Bool {})", n, m[i][0]),
                            Sort::Bv(w) => println!("  (define-fun {} () (_ BitVec {}) {})", n, w, bits_literal(&m[i])),
                        }
                    }
                    println!(")");
                }
                None => println!("(error \"no model available\")"),
            },
            "exit" => break,
            "push" | "pop" | "reset" | "get-value" | "get-assertions" | "check-sat-assuming" => {
                return Err(format!("{} is not supported", name));
            }
            _ => return Err(format!("unknown command {}", name)),
        }
    }
    Ok(())
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let src = if args.len() > 1 {
        std::fs::read_to_string(&args[1]).unwrap_or_else(|e| {
            eprintln!("cannot read {}: {}", args[1], e);
            std::process::exit(2)
        })
    } else {
        let mut s = String::new();
        std::io::stdin().read_to_string(&mut s).expect("cannot read stdin");
        s
    };
    // The solver recurses on terms and on DPLL decisions; give it a large stack.
    let child = std::thread::Builder::new().stack_size(1 << 30).spawn(move || run(&src)).unwrap();
    if let Err(e) = child.join().unwrap() {
        println!("(error \"{}\")", e.replace('"', "'"));
        std::process::exit(1);
    }
}
