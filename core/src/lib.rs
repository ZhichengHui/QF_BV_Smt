//! A vanilla SMT solver for quantifier-free bit-vector formulas (QF_BV).
//!
//! The solver bit-blasts the terms into a CNF formula with the Tseitin encoding and decides the
//! CNF formula with DPLL (unit propagation and chronological backtracking). It answers either
//! `Sat` with a model or `Unsat`.
//!
//! Booleans are bit-vectors of width 1 (1 is true). A bit-vector is a list of bits with the
//! least significant bit first.

/// A literal of the CNF formula: variable `var`, negated when `neg` is true.
#[derive(Clone, Copy)]
pub struct Lit {
    pub var: usize,
    pub neg: bool,
}

/// Binary operators. `Eq` and `Ult` give width 1; `Concat(a, b)` has `a` as the high part;
/// the others give the width of their operands, which must be equal.
pub enum BinOp {
    And,
    Or,
    Xor,
    Add,
    Mul,
    Udiv,
    Urem,
    Shl,
    Lshr,
    Concat,
    Eq,
    Ult,
}

/// Bit-vector terms.
pub enum Term {
    /// A constant, least significant bit first.
    Const(Vec<bool>),
    /// The variable with this index into `Problem::widths`.
    Var(usize),
    /// The definition with this index into `Problem::defs`; it must be an earlier definition.
    Ref(usize),
    /// Bitwise negation.
    Not(Box<Term>),
    Bin(BinOp, Box<Term>, Box<Term>),
    /// `Extract(hi, lo, t)`: bits `lo..=hi` of `t`.
    Extract(usize, usize, Box<Term>),
    /// `Ite(c, t, e)`: `t` if the width-1 term `c` is 1, otherwise `e`.
    Ite(Box<Term>, Box<Term>, Box<Term>),
}

/// A problem: variables of the given widths, definitions, and assertions (terms of width 1).
pub struct Problem {
    pub widths: Vec<usize>,
    pub defs: Vec<Term>,
    pub asserts: Vec<Term>,
}

/// The answer. A model gives each variable its bits, least significant bit first.
pub enum Answer {
    Sat(Vec<Vec<bool>>),
    Unsat,
}

/// A CNF formula over the variables `0..num_vars`. Variable 0 is true.
pub struct Cnf {
    pub num_vars: usize,
    pub clauses: Vec<Vec<Lit>>,
}

// ---------------------------------------------------------------------------------------------
// Literals and gates

fn lit_const(b: bool) -> Lit {
    Lit { var: 0, neg: !b }
}

fn lit_neg(l: Lit) -> Lit {
    Lit { var: l.var, neg: !l.neg }
}

fn fresh(cnf: Cnf) -> (Cnf, Lit) {
    let l = Lit { var: cnf.num_vars, neg: false };
    (Cnf { num_vars: cnf.num_vars + 1, clauses: cnf.clauses }, l)
}

fn add_clause(cnf: Cnf, c: Vec<Lit>) -> Cnf {
    let mut clauses = cnf.clauses;
    clauses.push(c);
    Cnf { num_vars: cnf.num_vars, clauses }
}

fn clause1(a: Lit) -> Vec<Lit> {
    let mut c = Vec::new();
    c.push(a);
    c
}

fn clause2(a: Lit, b: Lit) -> Vec<Lit> {
    let mut c = Vec::new();
    c.push(a);
    c.push(b);
    c
}

fn clause3(a: Lit, b: Lit, d: Lit) -> Vec<Lit> {
    let mut c = Vec::new();
    c.push(a);
    c.push(b);
    c.push(d);
    c
}

/// A fresh literal `x` with `x <-> a & b`.
fn gate_and(cnf: Cnf, a: Lit, b: Lit) -> (Cnf, Lit) {
    let (cnf, x) = fresh(cnf);
    let cnf = add_clause(cnf, clause2(lit_neg(x), a));
    let cnf = add_clause(cnf, clause2(lit_neg(x), b));
    let cnf = add_clause(cnf, clause3(x, lit_neg(a), lit_neg(b)));
    (cnf, x)
}

/// A literal `x` with `x <-> a | b`.
fn gate_or(cnf: Cnf, a: Lit, b: Lit) -> (Cnf, Lit) {
    let (cnf, x) = gate_and(cnf, lit_neg(a), lit_neg(b));
    (cnf, lit_neg(x))
}

/// A fresh literal `x` with `x <-> a ^ b`.
fn gate_xor(cnf: Cnf, a: Lit, b: Lit) -> (Cnf, Lit) {
    let (cnf, x) = fresh(cnf);
    let cnf = add_clause(cnf, clause3(lit_neg(x), a, b));
    let cnf = add_clause(cnf, clause3(lit_neg(x), lit_neg(a), lit_neg(b)));
    let cnf = add_clause(cnf, clause3(x, lit_neg(a), b));
    let cnf = add_clause(cnf, clause3(x, a, lit_neg(b)));
    (cnf, x)
}

/// A fresh literal `x` with `x <-> (if c then a else b)`.
fn gate_ite(cnf: Cnf, c: Lit, a: Lit, b: Lit) -> (Cnf, Lit) {
    let (cnf, x) = fresh(cnf);
    let cnf = add_clause(cnf, clause3(lit_neg(c), lit_neg(x), a));
    let cnf = add_clause(cnf, clause3(lit_neg(c), x, lit_neg(a)));
    let cnf = add_clause(cnf, clause3(c, lit_neg(x), b));
    let cnf = add_clause(cnf, clause3(c, x, lit_neg(b)));
    (cnf, x)
}

/// `gate_and`, `gate_or` or `gate_xor`, by the operator.
fn gate_bitwise(cnf: Cnf, op: &BinOp, a: Lit, b: Lit) -> (Cnf, Lit) {
    match op {
        BinOp::And => gate_and(cnf, a, b),
        BinOp::Or => gate_or(cnf, a, b),
        _ => gate_xor(cnf, a, b),
    }
}

// ---------------------------------------------------------------------------------------------
// Bit-vector circuits. Every bit-vector is a list of literals, least significant bit first.

fn bv_const(bits: &Vec<bool>) -> Vec<Lit> {
    let mut r = Vec::new();
    let mut i: usize = 0;
    while i < bits.len() {
        r.push(lit_const(bits[i]));
        i += 1;
    }
    r
}

/// The `w` low bits of `v`.
fn bv_of_nat(v: usize, w: usize) -> Vec<Lit> {
    let mut r = Vec::new();
    let mut x = v;
    let mut i: usize = 0;
    while i < w {
        r.push(lit_const(x % 2 == 1));
        x = x / 2;
        i += 1;
    }
    r
}

fn bv_fresh(cnf: Cnf, w: usize) -> (Cnf, Vec<Lit>) {
    let mut cnf = cnf;
    let mut r = Vec::new();
    let mut i: usize = 0;
    while i < w {
        let (c, x) = fresh(cnf);
        cnf = c;
        r.push(x);
        i += 1;
    }
    (cnf, r)
}

fn bv_not(a: &Vec<Lit>) -> Vec<Lit> {
    let mut r = Vec::new();
    let mut i: usize = 0;
    while i < a.len() {
        r.push(lit_neg(a[i]));
        i += 1;
    }
    r
}

fn bv_bitwise(cnf: Cnf, op: &BinOp, a: &Vec<Lit>, b: &Vec<Lit>) -> (Cnf, Vec<Lit>) {
    let mut cnf = cnf;
    let mut r = Vec::new();
    let mut i: usize = 0;
    while i < a.len() {
        let (c, x) = gate_bitwise(cnf, op, a[i], b[i]);
        cnf = c;
        r.push(x);
        i += 1;
    }
    (cnf, r)
}

/// Ripple-carry adder: the sum of `a`, `b` and the carry `cin`, and the carry out.
fn bv_add(cnf: Cnf, a: &Vec<Lit>, b: &Vec<Lit>, cin: Lit) -> (Cnf, Vec<Lit>, Lit) {
    let mut cnf = cnf;
    let mut carry = cin;
    let mut r = Vec::new();
    let mut i: usize = 0;
    while i < a.len() {
        let (c1, t) = gate_xor(cnf, a[i], b[i]);
        let (c2, s) = gate_xor(c1, t, carry);
        let (c3, c) = gate_ite(c2, t, carry, a[i]);
        cnf = c3;
        carry = c;
        r.push(s);
        i += 1;
    }
    (cnf, r, carry)
}

/// The partial product `(a << i) & b_i`, truncated to the width of `a`.
fn bv_partial(cnf: Cnf, a: &Vec<Lit>, bi: Lit, i: usize) -> (Cnf, Vec<Lit>) {
    let mut cnf = cnf;
    let mut r = Vec::new();
    let mut j: usize = 0;
    while j < a.len() {
        if j < i {
            r.push(lit_const(false));
        } else {
            let (c, x) = gate_and(cnf, a[j - i], bi);
            cnf = c;
            r.push(x);
        }
        j += 1;
    }
    (cnf, r)
}

/// Shift-and-add multiplier, truncated to the width of the operands.
fn bv_mul(cnf: Cnf, a: &Vec<Lit>, b: &Vec<Lit>) -> (Cnf, Vec<Lit>) {
    let mut cnf = cnf;
    let mut acc = vec![lit_const(false); a.len()];
    let mut i: usize = 0;
    while i < a.len() {
        let (c1, p) = bv_partial(cnf, a, b[i], i);
        let (c2, s, _) = bv_add(c1, &acc, &p, lit_const(false));
        cnf = c2;
        acc = s;
        i += 1;
    }
    (cnf, acc)
}

/// A literal that is true iff `a` and `b` are equal.
fn bv_eq(cnf: Cnf, a: &Vec<Lit>, b: &Vec<Lit>) -> (Cnf, Lit) {
    let mut cnf = cnf;
    let mut r = lit_const(true);
    let mut i: usize = 0;
    while i < a.len() {
        let (c1, x) = gate_xor(cnf, a[i], b[i]);
        let (c2, y) = gate_and(c1, r, lit_neg(x));
        cnf = c2;
        r = y;
        i += 1;
    }
    (cnf, r)
}

/// A literal that is true iff `a < b` (unsigned): `a + !b + 1` has no carry out.
fn bv_ult(cnf: Cnf, a: &Vec<Lit>, b: &Vec<Lit>) -> (Cnf, Lit) {
    let nb = bv_not(b);
    let (cnf, _, c) = bv_add(cnf, a, &nb, lit_const(true));
    (cnf, lit_neg(c))
}

fn bv_ite(cnf: Cnf, c: Lit, a: &Vec<Lit>, b: &Vec<Lit>) -> (Cnf, Vec<Lit>) {
    let mut cnf = cnf;
    let mut r = Vec::new();
    let mut i: usize = 0;
    while i < a.len() {
        let (c1, x) = gate_ite(cnf, c, a[i], b[i]);
        cnf = c1;
        r.push(x);
        i += 1;
    }
    (cnf, r)
}

/// `a` shifted by the constant `s`, to the left (towards the high bits) or to the right.
fn bv_shift_const(a: &Vec<Lit>, s: usize, left: bool) -> Vec<Lit> {
    let mut r = Vec::new();
    let mut j: usize = 0;
    while j < a.len() {
        if left {
            if j < s {
                r.push(lit_const(false));
            } else {
                r.push(a[j - s]);
            }
        } else if s < a.len() - j {
            r.push(a[j + s]);
        } else {
            r.push(lit_const(false));
        }
        j += 1;
    }
    r
}

/// `a` shifted by `b`: the result is `a` shifted by `s` if `b = s` for some `s` below the
/// width, and 0 otherwise.
fn bv_shift(cnf: Cnf, a: &Vec<Lit>, b: &Vec<Lit>, left: bool) -> (Cnf, Vec<Lit>) {
    let mut cnf = cnf;
    let mut r = vec![lit_const(false); a.len()];
    let mut s: usize = 0;
    while s < a.len() {
        let (c1, e) = bv_eq(cnf, b, &bv_of_nat(s, a.len()));
        let (c2, x) = bv_ite(c1, e, &bv_shift_const(a, s, left), &r);
        cnf = c2;
        r = x;
        s += 1;
    }
    (cnf, r)
}

/// `a` extended with zeros to width `w`.
fn bv_zext(a: &Vec<Lit>, w: usize) -> Vec<Lit> {
    let mut r = Vec::new();
    let mut i: usize = 0;
    while i < w {
        if i < a.len() {
            r.push(a[i]);
        } else {
            r.push(lit_const(false));
        }
        i += 1;
    }
    r
}

/// Bits `lo..=hi` of `a`.
fn bv_extract(a: &Vec<Lit>, hi: usize, lo: usize) -> Vec<Lit> {
    let mut r = Vec::new();
    let mut i: usize = lo;
    while i <= hi {
        r.push(a[i]);
        i += 1;
    }
    r
}

/// The concatenation with `hi` as the high part.
fn bv_concat(hi: &Vec<Lit>, lo: &Vec<Lit>) -> Vec<Lit> {
    let mut r = lo.clone();
    let mut i: usize = 0;
    while i < hi.len() {
        r.push(hi[i]);
        i += 1;
    }
    r
}

/// Fresh bit-vectors `q` and `r` constrained to be the unsigned quotient and remainder of
/// `a` and `b`: if `b = 0` then `q` is all ones and `r = a`; otherwise `a = q * b + r` (computed
/// in twice the width, so it does not overflow) and `r < b`.
fn bv_divrem(cnf: Cnf, a: &Vec<Lit>, b: &Vec<Lit>) -> (Cnf, Vec<Lit>, Vec<Lit>) {
    let w = a.len();
    let (cnf, q) = bv_fresh(cnf, w);
    let (cnf, r) = bv_fresh(cnf, w);
    let (cnf, b_zero) = bv_eq(cnf, b, &vec![lit_const(false); w]);
    let (cnf, q_ones) = bv_eq(cnf, &q, &vec![lit_const(true); w]);
    let (cnf, r_a) = bv_eq(cnf, &r, a);
    let (cnf, case_zero) = gate_and(cnf, q_ones, r_a);
    let w2 = w + w;
    let (cnf, prod) = bv_mul(cnf, &bv_zext(&q, w2), &bv_zext(b, w2));
    let (cnf, sum, _) = bv_add(cnf, &prod, &bv_zext(&r, w2), lit_const(false));
    let (cnf, sum_a) = bv_eq(cnf, &sum, &bv_zext(a, w2));
    let (cnf, r_lt) = bv_ult(cnf, &r, b);
    let (cnf, case_nonzero) = gate_and(cnf, sum_a, r_lt);
    let (cnf, ok) = gate_ite(cnf, b_zero, case_zero, case_nonzero);
    let cnf = add_clause(cnf, clause1(ok));
    (cnf, q, r)
}

fn blast_bin(cnf: Cnf, op: &BinOp, a: &Vec<Lit>, b: &Vec<Lit>) -> (Cnf, Vec<Lit>) {
    match op {
        BinOp::And => bv_bitwise(cnf, op, a, b),
        BinOp::Or => bv_bitwise(cnf, op, a, b),
        BinOp::Xor => bv_bitwise(cnf, op, a, b),
        BinOp::Add => {
            let (cnf, s, _) = bv_add(cnf, a, b, lit_const(false));
            (cnf, s)
        }
        BinOp::Mul => bv_mul(cnf, a, b),
        BinOp::Udiv => {
            let (cnf, q, _) = bv_divrem(cnf, a, b);
            (cnf, q)
        }
        BinOp::Urem => {
            let (cnf, _, r) = bv_divrem(cnf, a, b);
            (cnf, r)
        }
        BinOp::Shl => bv_shift(cnf, a, b, true),
        BinOp::Lshr => bv_shift(cnf, a, b, false),
        BinOp::Concat => (cnf, bv_concat(a, b)),
        BinOp::Eq => {
            let (cnf, x) = bv_eq(cnf, a, b);
            (cnf, clause1(x))
        }
        BinOp::Ult => {
            let (cnf, x) = bv_ult(cnf, a, b);
            (cnf, clause1(x))
        }
    }
}

/// The literals of the bits of `t`. `vars` and `defs` give the literals of the variables and of
/// the definitions blasted so far.
fn blast(cnf: Cnf, vars: &Vec<Vec<Lit>>, defs: &Vec<Vec<Lit>>, t: &Term) -> (Cnf, Vec<Lit>) {
    match t {
        Term::Const(bits) => (cnf, bv_const(bits)),
        Term::Var(i) => (cnf, vars[*i].clone()),
        Term::Ref(i) => (cnf, defs[*i].clone()),
        Term::Not(a) => {
            let (cnf, la) = blast(cnf, vars, defs, a);
            (cnf, bv_not(&la))
        }
        Term::Bin(op, a, b) => {
            let (cnf, la) = blast(cnf, vars, defs, a);
            let (cnf, lb) = blast(cnf, vars, defs, b);
            blast_bin(cnf, op, &la, &lb)
        }
        Term::Extract(hi, lo, a) => {
            let (cnf, la) = blast(cnf, vars, defs, a);
            (cnf, bv_extract(&la, *hi, *lo))
        }
        Term::Ite(c, a, b) => {
            let (cnf, lc) = blast(cnf, vars, defs, c);
            let (cnf, la) = blast(cnf, vars, defs, a);
            let (cnf, lb) = blast(cnf, vars, defs, b);
            bv_ite(cnf, lc[0], &la, &lb)
        }
    }
}

// ---------------------------------------------------------------------------------------------
// DPLL. A partial assignment gives each variable `Some(value)` or `None` (unassigned).

/// The state of a clause under a partial assignment.
enum Status {
    /// Some literal is true.
    Satisfied,
    /// Every literal is false.
    Conflict,
    /// Exactly one literal (this one) is unassigned and the others are false.
    Unit(Lit),
    /// At least two literals are unassigned and the others are false.
    Open,
}

fn lit_value(a: &Vec<Option<bool>>, l: Lit) -> Option<bool> {
    match a[l.var] {
        Some(b) => Some(b != l.neg),
        None => None,
    }
}

fn clause_status(a: &Vec<Option<bool>>, c: &Vec<Lit>) -> Status {
    let mut unit: Option<Lit> = None;
    let mut open = false;
    let mut i: usize = 0;
    while i < c.len() {
        match lit_value(a, c[i]) {
            Some(true) => return Status::Satisfied,
            Some(false) => {}
            None => {
                if unit.is_some() {
                    open = true;
                } else {
                    unit = Some(c[i]);
                }
            }
        }
        i += 1;
    }
    if open {
        return Status::Open;
    }
    match unit {
        Some(l) => Status::Unit(l),
        None => Status::Conflict,
    }
}

/// One pass of unit propagation over the clauses: `None` on a conflict, otherwise the new
/// assignment and whether it differs from `a`.
fn propagate_pass(a: Vec<Option<bool>>, cs: &Vec<Vec<Lit>>) -> Option<(Vec<Option<bool>>, bool)> {
    let mut a = a;
    let mut changed = false;
    let mut i: usize = 0;
    while i < cs.len() {
        match clause_status(&a, &cs[i]) {
            Status::Conflict => return None,
            Status::Unit(l) => {
                a[l.var] = Some(!l.neg);
                changed = true;
            }
            Status::Satisfied => {}
            Status::Open => {}
        }
        i += 1;
    }
    Some((a, changed))
}

/// Unit propagation to a fixpoint: `None` on a conflict.
fn propagate(a: Vec<Option<bool>>, cs: &Vec<Vec<Lit>>) -> Option<Vec<Option<bool>>> {
    let mut a = a;
    loop {
        match propagate_pass(a, cs) {
            None => return None,
            Some((a1, changed)) => {
                if !changed {
                    return Some(a1);
                }
                a = a1;
            }
        }
    }
}

fn find_unassigned(a: &Vec<Option<bool>>) -> Option<usize> {
    let mut i: usize = 0;
    while i < a.len() {
        if a[i].is_none() {
            return Some(i);
        }
        i += 1;
    }
    None
}

/// A total assignment that extends `a` and satisfies the clauses, if there is one.
fn dpll(cs: &Vec<Vec<Lit>>, a: Vec<Option<bool>>) -> Option<Vec<Option<bool>>> {
    match propagate(a, cs) {
        None => None,
        Some(a) => match find_unassigned(&a) {
            None => Some(a),
            Some(v) => {
                let mut a1 = a.clone();
                a1[v] = Some(true);
                match dpll(cs, a1) {
                    Some(r) => Some(r),
                    None => {
                        let mut a2 = a;
                        a2[v] = Some(false);
                        dpll(cs, a2)
                    }
                }
            }
        },
    }
}

// ---------------------------------------------------------------------------------------------
// The solver

fn read_bits(a: &Vec<Option<bool>>, ls: &Vec<Lit>) -> Vec<bool> {
    let mut r = Vec::new();
    let mut i: usize = 0;
    while i < ls.len() {
        r.push(lit_value(a, ls[i]) == Some(true));
        i += 1;
    }
    r
}

fn read_model(a: &Vec<Option<bool>>, vars: &Vec<Vec<Lit>>) -> Vec<Vec<bool>> {
    let mut m = Vec::new();
    let mut i: usize = 0;
    while i < vars.len() {
        m.push(read_bits(a, &vars[i]));
        i += 1;
    }
    m
}

/// The CNF formula of the problem, and the literals of its variables.
fn encode(p: &Problem) -> (Cnf, Vec<Vec<Lit>>) {
    let mut cnf = add_clause(Cnf { num_vars: 1, clauses: Vec::new() }, clause1(lit_const(true)));
    let mut vars = Vec::new();
    let mut i: usize = 0;
    while i < p.widths.len() {
        let (c, ls) = bv_fresh(cnf, p.widths[i]);
        cnf = c;
        vars.push(ls);
        i += 1;
    }
    let mut defs = Vec::new();
    let mut j: usize = 0;
    while j < p.defs.len() {
        let (c, ls) = blast(cnf, &vars, &defs, &p.defs[j]);
        cnf = c;
        defs.push(ls);
        j += 1;
    }
    let mut k: usize = 0;
    while k < p.asserts.len() {
        let (c, ls) = blast(cnf, &vars, &defs, &p.asserts[k]);
        cnf = add_clause(c, clause1(ls[0]));
        k += 1;
    }
    (cnf, vars)
}

pub fn solve(p: &Problem) -> Answer {
    let (cnf, vars) = encode(p);
    match dpll(&cnf.clauses, vec![None; cnf.num_vars]) {
        None => Answer::Unsat,
        Some(a) => Answer::Sat(read_model(&a, &vars)),
    }
}
