//! A vanilla SMT solver for quantifier-free bit-vector formulas (QF_BV).
//!
//! A problem is written with every bit-vector operation of SMT-LIB 2.6 (the theory
//! FixedSizeBitVectors and the logic QF_BV; `Term`). The solver first rewrites it, following the
//! definitions of SMT-LIB, into the core language `CoreTerm` of fifteen basic operations
//! (`lower_problem`); it then bit-blasts the core problem into a CNF formula with the Tseitin
//! encoding and decides the CNF formula with DPLL (unit propagation and chronological
//! backtracking). It answers either `Sat` with a model or `Unsat`.
//!
//! Booleans are bit-vectors of width 1 (1 is true). A bit-vector is a list of bits with the
//! least significant bit first.

/// A literal of the CNF formula: variable `var`, negated when `neg` is true.
#[derive(Clone, Copy)]
pub struct Lit {
    pub var: usize,
    pub neg: bool,
}

// ---------------------------------------------------------------------------------------------
// The core language: the terms that are bit-blasted

/// Binary operators of the core language. `Eq` and `Ult` give width 1; `Concat(a, b)` has `a` as
/// the high part; the others give the width of their operands, which must be equal.
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

/// Terms of the core language.
pub enum CoreTerm {
    /// A constant, least significant bit first.
    Const(Vec<bool>),
    /// The variable with this index into `CoreProblem::widths`.
    Var(usize),
    /// The definition with this index into `CoreProblem::defs`; it must be an earlier definition.
    Ref(usize),
    /// Bitwise negation.
    Not(Box<CoreTerm>),
    Bin(BinOp, Box<CoreTerm>, Box<CoreTerm>),
    /// `Extract(hi, lo, t)`: bits `lo..=hi` of `t`.
    Extract(usize, usize, Box<CoreTerm>),
    /// `Ite(c, t, e)`: `t` if the width-1 term `c` is 1, otherwise `e`.
    Ite(Box<CoreTerm>, Box<CoreTerm>, Box<CoreTerm>),
}

/// A problem of the core language: variables of the given widths, definitions, and assertions
/// (terms of width 1).
pub struct CoreProblem {
    pub widths: Vec<usize>,
    pub defs: Vec<CoreTerm>,
    pub asserts: Vec<CoreTerm>,
}

/// The answer. A model gives each variable its bits, least significant bit first.
pub enum Answer {
    Sat(Vec<Vec<bool>>),
    Unsat,
}

// ---------------------------------------------------------------------------------------------
// The extended language: every bit-vector operation of SMT-LIB 2.6

/// The binary operators of SMT-LIB 2.6 on bit-vectors, with `=` and `distinct` (binary) of the
/// Core theory. `Concat(a, b)` has `a` as the high part and gives the sum of the widths; `Comp`
/// and the predicates (`Eq`, `Distinct`, `Ult`, ..., `Sge`) give width 1; the others give the
/// width of their operands. Operands other than those of `Concat` must have equal widths.
pub enum Op {
    And,
    Or,
    Xor,
    Nand,
    Nor,
    Xnor,
    Comp,
    Add,
    Sub,
    Mul,
    Udiv,
    Urem,
    Sdiv,
    Srem,
    Smod,
    Shl,
    Lshr,
    Ashr,
    Concat,
    Eq,
    Distinct,
    Ult,
    Ule,
    Ugt,
    Uge,
    Slt,
    Sle,
    Sgt,
    Sge,
}

/// Terms of the extended language. Every width is at least 1, as in SMT-LIB.
pub enum Term {
    /// A constant, least significant bit first.
    Const(Vec<bool>),
    /// The variable with this index into `Problem::widths`.
    Var(usize),
    /// The definition with this index into `Problem::defs`; it must be an earlier definition.
    Ref(usize),
    /// `bvnot`.
    Not(Box<Term>),
    /// `bvneg`.
    Neg(Box<Term>),
    Bin(Op, Box<Term>, Box<Term>),
    /// `Extract(hi, lo, t)`: `((_ extract hi lo) t)`, bits `lo..=hi` of `t`.
    Extract(usize, usize, Box<Term>),
    /// `Repeat(i, t)`: `((_ repeat i) t)`, `i >= 1` copies of `t`.
    Repeat(usize, Box<Term>),
    /// `ZeroExtend(i, t)`: `((_ zero_extend i) t)`.
    ZeroExtend(usize, Box<Term>),
    /// `SignExtend(i, t)`: `((_ sign_extend i) t)`.
    SignExtend(usize, Box<Term>),
    /// `RotateLeft(i, t)`: `((_ rotate_left i) t)`.
    RotateLeft(usize, Box<Term>),
    /// `RotateRight(i, t)`: `((_ rotate_right i) t)`.
    RotateRight(usize, Box<Term>),
    /// `Ite(c, t, e)`: `t` if the width-1 term `c` is 1, otherwise `e`.
    Ite(Box<Term>, Box<Term>, Box<Term>),
}

/// A problem: variables of the given widths, definitions, and assertions (terms of width 1).
pub struct Problem {
    pub widths: Vec<usize>,
    pub defs: Vec<Term>,
    pub asserts: Vec<Term>,
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
fn blast(cnf: Cnf, vars: &Vec<Vec<Lit>>, defs: &Vec<Vec<Lit>>, t: &CoreTerm) -> (Cnf, Vec<Lit>) {
    match t {
        CoreTerm::Const(bits) => (cnf, bv_const(bits)),
        CoreTerm::Var(i) => (cnf, vars[*i].clone()),
        CoreTerm::Ref(i) => (cnf, defs[*i].clone()),
        CoreTerm::Not(a) => {
            let (cnf, la) = blast(cnf, vars, defs, a);
            (cnf, bv_not(&la))
        }
        CoreTerm::Bin(op, a, b) => {
            let (cnf, la) = blast(cnf, vars, defs, a);
            let (cnf, lb) = blast(cnf, vars, defs, b);
            blast_bin(cnf, op, &la, &lb)
        }
        CoreTerm::Extract(hi, lo, a) => {
            let (cnf, la) = blast(cnf, vars, defs, a);
            (cnf, bv_extract(&la, *hi, *lo))
        }
        CoreTerm::Ite(c, a, b) => {
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
fn encode(p: &CoreProblem) -> (Cnf, Vec<Vec<Lit>>) {
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

fn solve_core(p: &CoreProblem) -> Answer {
    let (cnf, vars) = encode(p);
    match dpll(&cnf.clauses, vec![None; cnf.num_vars]) {
        None => Answer::Unsat,
        Some(a) => Answer::Sat(read_model(&a, &vars)),
    }
}

// ---------------------------------------------------------------------------------------------
// Rewriting the extended language into the core language.
//
// Every subterm of the extended problem becomes a definition of the core problem, so no subterm
// is copied: the core term of an operation refers to its operands by `CoreTerm::Ref`. Each
// operation is rewritten following its definition in SMT-LIB 2.6 (the logic QF_BV, `:extensions`,
// and the theory FixedSizeBitVectors).

/// The core definitions built so far, with their widths.
pub struct Lower {
    pub defs: Vec<CoreTerm>,
    pub widths: Vec<usize>,
}

/// Adds the core term `t` of width `w` as a definition; returns its index.
fn push_def(l: Lower, t: CoreTerm, w: usize) -> (Lower, usize) {
    let k = l.defs.len();
    let mut defs = l.defs;
    defs.push(t);
    let mut widths = l.widths;
    widths.push(w);
    (Lower { defs, widths }, k)
}

fn cref(k: usize) -> CoreTerm {
    CoreTerm::Ref(k)
}

fn cnot(a: CoreTerm) -> CoreTerm {
    CoreTerm::Not(Box::new(a))
}

fn cbin(op: BinOp, a: CoreTerm, b: CoreTerm) -> CoreTerm {
    CoreTerm::Bin(op, Box::new(a), Box::new(b))
}

fn cite(c: CoreTerm, a: CoreTerm, b: CoreTerm) -> CoreTerm {
    CoreTerm::Ite(Box::new(c), Box::new(a), Box::new(b))
}

fn cextract(hi: usize, lo: usize, a: CoreTerm) -> CoreTerm {
    CoreTerm::Extract(hi, lo, Box::new(a))
}

/// The constant 1 of width `w >= 1`: the bit 1 below `w - 1` zero bits.
fn cone(w: usize) -> CoreTerm {
    let mut one = Vec::new();
    one.push(true);
    cbin(BinOp::Concat, CoreTerm::Const(vec![false; w - 1]), CoreTerm::Const(one))
}

/// `bvneg` of definition `k` of width `w`: `bvnot k` plus 1 (`2^w - k` modulo `2^w`).
fn cneg(k: usize, w: usize) -> CoreTerm {
    cbin(BinOp::Add, cnot(cref(k)), cone(w))
}

/// The most significant bit of definition `k` of width `w`, as a term of width 1.
fn cmsb(k: usize, w: usize) -> CoreTerm {
    cextract(w - 1, w - 1, cref(k))
}

/// The absolute value of definition `k` of width `w`: `bvneg k` if its sign bit is set, else `k`.
fn cabs(k: usize, w: usize) -> CoreTerm {
    cite(cmsb(k, w), cneg(k, w), cref(k))
}

/// `bvslt` of definitions `ka`, `kb` of width `w` as defined in QF_BV: the sign bits are 1 and
/// 0, or they are equal and `ka` is below `kb` unsigned.
fn cslt(ka: usize, kb: usize, w: usize) -> CoreTerm {
    cbin(
        BinOp::Or,
        cbin(BinOp::And, cmsb(ka, w), cnot(cmsb(kb, w))),
        cbin(BinOp::And, cnot(cbin(BinOp::Xor, cmsb(ka, w), cmsb(kb, w))), cbin(BinOp::Ult, cref(ka), cref(kb))),
    )
}

/// `bvsle` of definitions `ka`, `kb` of width `w` as defined in QF_BV: as `bvslt` with `bvule`
/// (`kb` is not below `ka`) in place of `bvult`.
fn csle(ka: usize, kb: usize, w: usize) -> CoreTerm {
    cbin(
        BinOp::Or,
        cbin(BinOp::And, cmsb(ka, w), cnot(cmsb(kb, w))),
        cbin(BinOp::And, cnot(cbin(BinOp::Xor, cmsb(ka, w), cmsb(kb, w))), cnot(cbin(BinOp::Ult, cref(kb), cref(ka)))),
    )
}

/// The binary operation `op` of the definitions `ka` and `kb`, as a new definition.
fn lower_bin(l: Lower, op: &Op, ka: usize, kb: usize) -> (Lower, usize) {
    let w = l.widths[ka];
    match op {
        Op::And => push_def(l, cbin(BinOp::And, cref(ka), cref(kb)), w),
        Op::Or => push_def(l, cbin(BinOp::Or, cref(ka), cref(kb)), w),
        Op::Xor => push_def(l, cbin(BinOp::Xor, cref(ka), cref(kb)), w),
        Op::Nand => push_def(l, cnot(cbin(BinOp::And, cref(ka), cref(kb))), w),
        Op::Nor => push_def(l, cnot(cbin(BinOp::Or, cref(ka), cref(kb))), w),
        Op::Xnor => push_def(l, cnot(cbin(BinOp::Xor, cref(ka), cref(kb))), w),
        Op::Comp => push_def(l, cbin(BinOp::Eq, cref(ka), cref(kb)), 1),
        Op::Add => push_def(l, cbin(BinOp::Add, cref(ka), cref(kb)), w),
        // `bvsub s t` is `bvadd s (bvneg t)`.
        Op::Sub => push_def(l, cbin(BinOp::Add, cref(ka), cneg(kb, w)), w),
        Op::Mul => push_def(l, cbin(BinOp::Mul, cref(ka), cref(kb)), w),
        Op::Udiv => push_def(l, cbin(BinOp::Udiv, cref(ka), cref(kb)), w),
        Op::Urem => push_def(l, cbin(BinOp::Urem, cref(ka), cref(kb)), w),
        // `bvsdiv`: the unsigned quotient of the absolute values, negated iff the sign bits
        // differ. This is the case definition of QF_BV with the four cases merged.
        Op::Sdiv => {
            let (l, q) = push_def(l, cbin(BinOp::Udiv, cabs(ka, w), cabs(kb, w)), w);
            push_def(l, cite(cbin(BinOp::Xor, cmsb(ka, w), cmsb(kb, w)), cneg(q, w), cref(q)), w)
        }
        // `bvsrem`: the unsigned remainder of the absolute values, negated iff the dividend's
        // sign bit is set.
        Op::Srem => {
            let (l, r) = push_def(l, cbin(BinOp::Urem, cabs(ka, w), cabs(kb, w)), w);
            push_def(l, cite(cmsb(ka, w), cneg(r, w), cref(r)), w)
        }
        // `bvsmod`: with `u` the unsigned remainder of the absolute values: `u` if it is 0 or
        // both sign bits are 0; `bvneg u + t` for sign bits 1, 0; `u + t` for 0, 1; `bvneg u`
        // for 1, 1.
        Op::Smod => {
            let (l, u) = push_def(l, cbin(BinOp::Urem, cabs(ka, w), cabs(kb, w)), w);
            let (l, nu) = push_def(l, cneg(u, w), w);
            let zero = cbin(BinOp::Eq, cref(u), CoreTerm::Const(vec![false; w]));
            let neg_a = cite(cmsb(kb, w), cref(nu), cbin(BinOp::Add, cref(nu), cref(kb)));
            let pos_a = cite(cmsb(kb, w), cbin(BinOp::Add, cref(u), cref(kb)), cref(u));
            push_def(l, cite(zero, cref(u), cite(cmsb(ka, w), neg_a, pos_a)), w)
        }
        Op::Shl => push_def(l, cbin(BinOp::Shl, cref(ka), cref(kb)), w),
        Op::Lshr => push_def(l, cbin(BinOp::Lshr, cref(ka), cref(kb)), w),
        // `bvashr s t` is `bvlshr s t` if the sign bit of `s` is 0, else `bvnot (bvlshr (bvnot s) t)`.
        Op::Ashr => push_def(
            l,
            cite(cmsb(ka, w), cnot(cbin(BinOp::Lshr, cnot(cref(ka)), cref(kb))), cbin(BinOp::Lshr, cref(ka), cref(kb))),
            w,
        ),
        Op::Concat => {
            let wb = l.widths[kb];
            push_def(l, cbin(BinOp::Concat, cref(ka), cref(kb)), w + wb)
        }
        Op::Eq => push_def(l, cbin(BinOp::Eq, cref(ka), cref(kb)), 1),
        Op::Distinct => push_def(l, cnot(cbin(BinOp::Eq, cref(ka), cref(kb))), 1),
        Op::Ult => push_def(l, cbin(BinOp::Ult, cref(ka), cref(kb)), 1),
        // `bvule s t` is `bvult s t` or `s = t`, that is, not `bvult t s`.
        Op::Ule => push_def(l, cnot(cbin(BinOp::Ult, cref(kb), cref(ka))), 1),
        Op::Ugt => push_def(l, cbin(BinOp::Ult, cref(kb), cref(ka)), 1),
        Op::Uge => push_def(l, cnot(cbin(BinOp::Ult, cref(ka), cref(kb))), 1),
        Op::Slt => push_def(l, cslt(ka, kb, w), 1),
        Op::Sle => push_def(l, csle(ka, kb, w), 1),
        Op::Sgt => push_def(l, cslt(kb, ka, w), 1),
        Op::Sge => push_def(l, csle(kb, ka, w), 1),
    }
}

/// Rewrites `t` into definitions of the core language and returns the index of the definition
/// whose value is that of `t`. `ws` gives the widths of the variables and `dm` the core
/// definition of each definition of the extended problem rewritten so far.
fn lower(ws: &Vec<usize>, dm: &Vec<usize>, l: Lower, t: &Term) -> (Lower, usize) {
    match t {
        Term::Const(bits) => push_def(l, CoreTerm::Const(bits.clone()), bits.len()),
        Term::Var(i) => push_def(l, CoreTerm::Var(*i), ws[*i]),
        Term::Ref(j) => (l, dm[*j]),
        Term::Not(a) => {
            let (l, ka) = lower(ws, dm, l, a);
            let w = l.widths[ka];
            push_def(l, cnot(cref(ka)), w)
        }
        Term::Neg(a) => {
            let (l, ka) = lower(ws, dm, l, a);
            let w = l.widths[ka];
            push_def(l, cneg(ka, w), w)
        }
        Term::Bin(op, a, b) => {
            let (l, ka) = lower(ws, dm, l, a);
            let (l, kb) = lower(ws, dm, l, b);
            lower_bin(l, op, ka, kb)
        }
        Term::Extract(hi, lo, a) => {
            let (l, ka) = lower(ws, dm, l, a);
            push_def(l, cextract(*hi, *lo, cref(ka)), *hi - *lo + 1)
        }
        // `((_ repeat i) t)` is `t` concatenated (as the high part) with `((_ repeat (i-1)) t)`:
        // starting from the empty constant, `i` concatenations.
        Term::Repeat(i, a) => {
            let (l, ka) = lower(ws, dm, l, a);
            let w = l.widths[ka];
            let (l, k0) = push_def(l, CoreTerm::Const(Vec::new()), 0);
            let mut l = l;
            let mut k = k0;
            let mut acc: usize = 0;
            let mut j: usize = 0;
            while j < *i {
                let (l1, k1) = push_def(l, cbin(BinOp::Concat, cref(ka), cref(k)), acc + w);
                l = l1;
                k = k1;
                acc = acc + w;
                j += 1;
            }
            (l, k)
        }
        // `((_ zero_extend i) t)` is `i` zero bits concatenated with `t`.
        Term::ZeroExtend(i, a) => {
            let (l, ka) = lower(ws, dm, l, a);
            let w = l.widths[ka];
            push_def(l, cbin(BinOp::Concat, CoreTerm::Const(vec![false; *i]), cref(ka)), w + *i)
        }
        // `((_ sign_extend i) t)` is `i` copies of the sign bit of `t` concatenated with `t`.
        Term::SignExtend(i, a) => {
            let (l, ka) = lower(ws, dm, l, a);
            let w = l.widths[ka];
            let ext = cite(cmsb(ka, w), CoreTerm::Const(vec![true; *i]), CoreTerm::Const(vec![false; *i]));
            push_def(l, cbin(BinOp::Concat, ext, cref(ka)), w + *i)
        }
        // `((_ rotate_left i) t)` moves every bit up by `r = i mod w` places, the top `r` bits
        // going to the bottom: the low `w - r` bits of `t` concatenated with its high `r` bits.
        Term::RotateLeft(i, a) => {
            let (l, ka) = lower(ws, dm, l, a);
            let w = l.widths[ka];
            let r = *i % w;
            if r == 0 {
                (l, ka)
            } else {
                push_def(l, cbin(BinOp::Concat, cextract(w - 1 - r, 0, cref(ka)), cextract(w - 1, w - r, cref(ka))), w)
            }
        }
        // `((_ rotate_right i) t)` moves every bit down by `r = i mod w` places, the bottom `r`
        // bits going to the top: the low `r` bits of `t` concatenated with its high `w - r` bits.
        Term::RotateRight(i, a) => {
            let (l, ka) = lower(ws, dm, l, a);
            let w = l.widths[ka];
            let r = *i % w;
            if r == 0 {
                (l, ka)
            } else {
                push_def(l, cbin(BinOp::Concat, cextract(r - 1, 0, cref(ka)), cextract(w - 1, r, cref(ka))), w)
            }
        }
        Term::Ite(c, a, b) => {
            let (l, kc) = lower(ws, dm, l, c);
            let (l, ka) = lower(ws, dm, l, a);
            let (l, kb) = lower(ws, dm, l, b);
            let w = l.widths[ka];
            push_def(l, cite(cref(kc), cref(ka), cref(kb)), w)
        }
    }
}

/// The core problem of `p`: the same variables; the definitions of `p` and all their subterms
/// as core definitions; each assertion as a reference to its core definition.
fn lower_problem(p: &Problem) -> CoreProblem {
    let mut l = Lower { defs: Vec::new(), widths: Vec::new() };
    let mut dm = Vec::new();
    let mut j: usize = 0;
    while j < p.defs.len() {
        let (l1, k) = lower(&p.widths, &dm, l, &p.defs[j]);
        l = l1;
        dm.push(k);
        j += 1;
    }
    let mut asserts = Vec::new();
    let mut i: usize = 0;
    while i < p.asserts.len() {
        let (l1, k) = lower(&p.widths, &dm, l, &p.asserts[i]);
        l = l1;
        asserts.push(cref(k));
        i += 1;
    }
    CoreProblem { widths: p.widths.clone(), defs: l.defs, asserts }
}

/// The solver: rewrites the problem into the core language and solves it.
pub fn solve(p: &Problem) -> Answer {
    let q = lower_problem(p);
    solve_core(&q)
}

// ---------------------------------------------------------------------------------------------
// The general problem structure: the interface to the SMT-LIB front end. These definitions are,
// word for word, those of the front end (`frontend/src/problem.rs`); see there for their meaning.

/// A sort.
pub enum SmtSort {
    Bool,
    /// `(_ BitVec w)`, `w >= 1`.
    BitVec(usize),
    /// The uninterpreted sort with this number.
    Uninterpreted(usize),
}

/// The theory function symbols of Core and FixedSizeBitVectors/QF_BV (SMT-LIB 2.6).
pub enum SmtOp {
    // Core
    Not,
    And,
    Or,
    Xor,
    Implies,
    Eq,
    Distinct,
    Ite,
    // FixedSizeBitVectors
    Concat,
    /// `(_ extract i j)`.
    Extract(usize, usize),
    Bvnot,
    Bvand,
    Bvor,
    Bvneg,
    Bvadd,
    Bvmul,
    Bvudiv,
    Bvurem,
    Bvshl,
    Bvlshr,
    Bvult,
    // QF_BV extensions
    Bvnand,
    Bvnor,
    Bvxor,
    Bvxnor,
    Bvcomp,
    Bvsub,
    Bvsdiv,
    Bvsrem,
    Bvsmod,
    Bvashr,
    /// `(_ repeat i)`.
    Repeat(usize),
    /// `(_ zero_extend i)`.
    ZeroExtend(usize),
    /// `(_ sign_extend i)`.
    SignExtend(usize),
    /// `(_ rotate_left i)`.
    RotateLeft(usize),
    /// `(_ rotate_right i)`.
    RotateRight(usize),
    Bvule,
    Bvugt,
    Bvuge,
    Bvslt,
    Bvsle,
    Bvsgt,
    Bvsge,
}

/// A term.
pub enum SmtTerm {
    BoolConst(bool),
    /// A bit-vector constant, least significant bit first.
    BvConst(Vec<bool>),
    /// The parameter with this number of the enclosing definition.
    Param(usize),
    /// A declared function symbol applied to arguments (none for a constant).
    Fun(usize, Vec<SmtTerm>),
    /// A defined function applied to arguments (one per parameter).
    Def(usize, Vec<SmtTerm>),
    /// A theory function symbol applied to arguments.
    App(SmtOp, Vec<SmtTerm>),
}

/// A declared function symbol: the sorts of its arguments and of its result.
pub struct SmtFun {
    pub args: Vec<SmtSort>,
    pub ret: SmtSort,
}

/// A defined function: the sorts of its parameters and of its result, and its body.
pub struct SmtDef {
    pub params: Vec<SmtSort>,
    pub ret: SmtSort,
    pub body: SmtTerm,
}

pub struct SmtProblem {
    pub num_sorts: usize,
    pub funs: Vec<SmtFun>,
    pub defs: Vec<SmtDef>,
    pub asserts: Vec<SmtTerm>,
}

/// A value: a truth value, a bit-vector (least significant bit first) or an element of an
/// uninterpreted sort (an index into its domain).
pub enum SmtValue {
    Bool(bool),
    Bv(Vec<bool>),
    Elem(usize),
}

/// One point of a function table: the arguments and the value there.
pub struct SmtEntry {
    pub args: Vec<SmtValue>,
    pub val: SmtValue,
}

/// The interpretation of a declared function symbol: at given arguments, the value of the first
/// entry with these arguments, and `default` if there is none (for a constant: the first entry, if
/// there is one).
pub struct SmtInterp {
    pub entries: Vec<SmtEntry>,
    pub default: SmtValue,
}

/// A model: the size of the domain of every uninterpreted sort (at least 1; the elements are
/// `Elem(0)` to `Elem(size - 1)`) and the interpretation of every declared function symbol.
pub struct SmtModel {
    pub domains: Vec<usize>,
    pub funs: Vec<SmtInterp>,
}

/// The answer to `check-sat`. `Unknown` is the answer for a problem the solver does not handle.
pub enum SmtAnswer {
    Sat(SmtModel),
    Unsat,
    Unknown,
}

// ---------------------------------------------------------------------------------------------
// Translation of a general problem into a problem of the extended language.
//
// A general problem is in the fragment of this solver if it has no uninterpreted sort and every
// declared function symbol is a constant. For a well-sorted problem (as the front end produces),
// every sort is then Bool or a bit-vector sort: Bool becomes width 1, true being 1. The declared
// constants become the variables, in order. Every argument of a theory function becomes a
// definition of the extended problem, so that no subterm is copied; a definition without
// parameters is translated once, and a definition with parameters is expanded where it is applied,
// its parameters referring to the definitions of the arguments.

/// The state of the translation: the definitions of the extended problem built so far.
pub struct Tr {
    pub defs: Vec<Term>,
}

/// The bit list `[b]`.
fn bits1(b: bool) -> Vec<bool> {
    let mut v = Vec::new();
    v.push(b);
    v
}

/// Adds `t` as a definition; returns its index.
fn tr_push(s: Tr, t: Term) -> (Tr, usize) {
    let k = s.defs.len();
    let mut defs = s.defs;
    defs.push(t);
    (Tr { defs }, k)
}

fn tref(k: usize) -> Term {
    Term::Ref(k)
}

fn tbin(op: Op, a: Term, b: Term) -> Term {
    Term::Bin(op, Box::new(a), Box::new(b))
}

/// The width of a sort of the fragment: Bool is width 1.
fn sort_width(s: &SmtSort) -> usize {
    match s {
        SmtSort::Bool => 1,
        SmtSort::BitVec(w) => *w,
        SmtSort::Uninterpreted(_) => 0,
    }
}

/// Whether `p` is in the fragment: no uninterpreted sort, and every declared symbol a constant.
fn in_fragment(p: &SmtProblem) -> bool {
    if p.num_sorts != 0 {
        return false;
    }
    let mut i: usize = 0;
    while i < p.funs.len() {
        if p.funs[i].args.len() != 0 {
            return false;
        }
        i += 1;
    }
    true
}

/// The binary operator of the extended language for a binary theory function.
fn tr_op(o: &SmtOp) -> Op {
    match o {
        SmtOp::And | SmtOp::Bvand => Op::And,
        SmtOp::Or | SmtOp::Bvor => Op::Or,
        SmtOp::Xor | SmtOp::Bvxor => Op::Xor,
        SmtOp::Bvnand => Op::Nand,
        SmtOp::Bvnor => Op::Nor,
        SmtOp::Bvxnor => Op::Xnor,
        SmtOp::Bvcomp => Op::Comp,
        SmtOp::Bvadd => Op::Add,
        SmtOp::Bvsub => Op::Sub,
        SmtOp::Bvmul => Op::Mul,
        SmtOp::Bvudiv => Op::Udiv,
        SmtOp::Bvurem => Op::Urem,
        SmtOp::Bvsdiv => Op::Sdiv,
        SmtOp::Bvsrem => Op::Srem,
        SmtOp::Bvsmod => Op::Smod,
        SmtOp::Bvshl => Op::Shl,
        SmtOp::Bvlshr => Op::Lshr,
        SmtOp::Bvashr => Op::Ashr,
        SmtOp::Concat => Op::Concat,
        SmtOp::Eq => Op::Eq,
        SmtOp::Distinct => Op::Distinct,
        SmtOp::Bvult => Op::Ult,
        SmtOp::Bvule => Op::Ule,
        SmtOp::Bvugt => Op::Ugt,
        SmtOp::Bvuge => Op::Uge,
        SmtOp::Bvslt => Op::Slt,
        SmtOp::Bvsle => Op::Sle,
        SmtOp::Bvsgt => Op::Sgt,
        SmtOp::Bvsge => Op::Sge,
        _ => Op::Eq,
    }
}

/// `o` applied to the definitions `ks` from the left: `(o (o k0 k1) k2) ...`.
fn fold_left(o: &SmtOp, ks: &Vec<usize>) -> Term {
    let mut acc = tref(ks[0]);
    let mut i: usize = 1;
    while i < ks.len() {
        acc = tbin(tr_op(o), acc, tref(ks[i]));
        i += 1;
    }
    acc
}

/// The conjunction of `o` on the consecutive definitions of `ks` (chainable `=`).
fn chain(o: &SmtOp, ks: &Vec<usize>) -> Term {
    let mut acc = tbin(tr_op(o), tref(ks[0]), tref(ks[1]));
    let mut i: usize = 2;
    while i < ks.len() {
        acc = tbin(Op::And, acc, tbin(tr_op(o), tref(ks[i - 1]), tref(ks[i])));
        i += 1;
    }
    acc
}

/// The conjunction of `distinct` on every pair of definitions of `ks` (pairwise `distinct`).
fn pairwise(ks: &Vec<usize>) -> Term {
    let mut acc = tbin(Op::Distinct, tref(ks[0]), tref(ks[1]));
    let mut i: usize = 0;
    while i < ks.len() {
        let mut j: usize = i + 1;
        while j < ks.len() {
            if i != 0 || j != 1 {
                acc = tbin(Op::And, acc, tbin(Op::Distinct, tref(ks[i]), tref(ks[j])));
            }
            j += 1;
        }
        i += 1;
    }
    acc
}

/// Right-associative `=>` on the definitions `ks`: `(or (not k0) (or (not k1) ... k_last))`.
fn implies(ks: &Vec<usize>) -> Term {
    let n = ks.len();
    let mut acc = tref(ks[n - 1]);
    let mut i: usize = n - 1;
    while i > 0 {
        i -= 1;
        acc = tbin(Op::Or, Term::Not(Box::new(tref(ks[i]))), acc);
    }
    acc
}

/// The theory function `o` applied to the definitions `ks` of its arguments.
fn tr_app(o: &SmtOp, ks: &Vec<usize>) -> Term {
    match o {
        SmtOp::Not | SmtOp::Bvnot => Term::Not(Box::new(tref(ks[0]))),
        SmtOp::Bvneg => Term::Neg(Box::new(tref(ks[0]))),
        SmtOp::And | SmtOp::Or | SmtOp::Xor | SmtOp::Bvand | SmtOp::Bvor | SmtOp::Bvadd | SmtOp::Bvmul | SmtOp::Bvxor => fold_left(o, ks),
        SmtOp::Implies => implies(ks),
        SmtOp::Eq => chain(o, ks),
        SmtOp::Distinct => pairwise(ks),
        SmtOp::Ite => Term::Ite(Box::new(tref(ks[0])), Box::new(tref(ks[1])), Box::new(tref(ks[2]))),
        SmtOp::Extract(i, j) => Term::Extract(*i, *j, Box::new(tref(ks[0]))),
        SmtOp::Repeat(i) => Term::Repeat(*i, Box::new(tref(ks[0]))),
        SmtOp::ZeroExtend(i) => Term::ZeroExtend(*i, Box::new(tref(ks[0]))),
        SmtOp::SignExtend(i) => Term::SignExtend(*i, Box::new(tref(ks[0]))),
        SmtOp::RotateLeft(i) => Term::RotateLeft(*i, Box::new(tref(ks[0]))),
        SmtOp::RotateRight(i) => Term::RotateRight(*i, Box::new(tref(ks[0]))),
        _ => tbin(tr_op(o), tref(ks[0]), tref(ks[1])),
    }
}

/// The arguments `ts`, each translated and added as a definition; returns their indices.
fn tr_args(p: &SmtProblem, dm: &Vec<usize>, env: &Vec<usize>, s: Tr, ts: &Vec<SmtTerm>) -> (Tr, Vec<usize>) {
    let mut s = s;
    let mut ks = Vec::new();
    let mut i: usize = 0;
    while i < ts.len() {
        let (s1, t) = tr_term(p, dm, env, s, &ts[i]);
        let (s2, k) = tr_push(s1, t);
        s = s2;
        ks.push(k);
        i += 1;
    }
    (s, ks)
}

/// The term of the extended language for `t`. `env` gives the definition of each parameter of
/// the enclosing definition, `dm` the definition of each definition without parameters of `p`
/// translated so far.
fn tr_term(p: &SmtProblem, dm: &Vec<usize>, env: &Vec<usize>, s: Tr, t: &SmtTerm) -> (Tr, Term) {
    match t {
        SmtTerm::BoolConst(b) => (s, Term::Const(bits1(*b))),
        SmtTerm::BvConst(bits) => (s, Term::Const(bits.clone())),
        SmtTerm::Param(k) => (s, tref(env[*k])),
        SmtTerm::Fun(i, _) => (s, Term::Var(*i)),
        SmtTerm::Def(d, args) => {
            if p.defs[*d].params.len() == 0 {
                (s, tref(dm[*d]))
            } else {
                let (s, ks) = tr_args(p, dm, env, s, args);
                tr_term(p, dm, &ks, s, &p.defs[*d].body)
            }
        }
        SmtTerm::App(o, args) => {
            let (s, ks) = tr_args(p, dm, env, s, args);
            (s, tr_app(o, &ks))
        }
    }
}

/// The problem of the extended language for `p`.
fn tr_problem(p: &SmtProblem) -> Problem {
    let mut widths = Vec::new();
    let mut i: usize = 0;
    while i < p.funs.len() {
        widths.push(sort_width(&p.funs[i].ret));
        i += 1;
    }
    let mut s = Tr { defs: Vec::new() };
    let mut dm = Vec::new();
    let no_params = Vec::new();
    let mut d: usize = 0;
    while d < p.defs.len() {
        if p.defs[d].params.len() == 0 {
            let (s1, t) = tr_term(p, &dm, &no_params, s, &p.defs[d].body);
            let (s2, k) = tr_push(s1, t);
            s = s2;
            dm.push(k);
        } else {
            dm.push(0);
        }
        d += 1;
    }
    let mut asserts = Vec::new();
    let mut j: usize = 0;
    while j < p.asserts.len() {
        let (s1, t) = tr_term(p, &dm, &no_params, s, &p.asserts[j]);
        s = s1;
        asserts.push(t);
        j += 1;
    }
    Problem { widths, defs: s.defs, asserts }
}

/// The model of `p` for the assignment `m` of the variables of its translation.
fn tr_model(p: &SmtProblem, m: &Vec<Vec<bool>>) -> SmtModel {
    let mut funs = Vec::new();
    let mut i: usize = 0;
    while i < p.funs.len() {
        let v = match &p.funs[i].ret {
            SmtSort::Bool => SmtValue::Bool(m[i][0]),
            _ => SmtValue::Bv(m[i].clone()),
        };
        funs.push(SmtInterp { entries: Vec::new(), default: v });
        i += 1;
    }
    SmtModel { domains: Vec::new(), funs }
}

// ---------------------------------------------------------------------------------------------
// Size checks. The solver of the extended language (`solve`) is verified for problems whose
// `size_bound` (spec/BVSmt_Spec.thy) is below 2^64, and the translation indexes its definitions
// by `usize`. `check_sat` answers `Unknown` when the translation would add 2^63 definitions or
// more, or when the translated problem is too large for `solve`. The computations below saturate
// at 2^63: each returns the exact value if it is below 2^63, and 2^63 otherwise.

/// The bound at which the size computations saturate: 2^63.
fn cap() -> usize {
    9223372036854775808
}

/// `a + b`, saturated at `cap()`.
fn sat_add(a: usize, b: usize) -> usize {
    if a >= cap() || b >= cap() - a {
        cap()
    } else {
        a + b
    }
}

/// `a * b`, saturated at `cap()`.
fn sat_mul(a: usize, b: usize) -> usize {
    if a == 0 || b == 0 {
        0
    } else if a >= cap() || b >= cap() || b > (cap() - 1) / a {
        cap()
    } else {
        a * b
    }
}

/// The number of definitions the translation of `t` adds. `dc` gives, for each definition with
/// parameters of `p` before the current one, the number its body adds where it is expanded.
fn tr_count(p: &SmtProblem, dc: &Vec<usize>, t: &SmtTerm) -> usize {
    match t {
        SmtTerm::Def(d, args) => {
            if p.defs[*d].params.len() == 0 {
                0
            } else {
                sat_add(tr_count_args(p, dc, args), dc[*d])
            }
        }
        SmtTerm::App(_, args) => tr_count_args(p, dc, args),
        _ => 0,
    }
}

/// The number of definitions the translation of the arguments `ts` adds (each argument is
/// itself added as a definition).
fn tr_count_args(p: &SmtProblem, dc: &Vec<usize>, ts: &Vec<SmtTerm>) -> usize {
    let mut n: usize = 0;
    let mut i: usize = 0;
    while i < ts.len() {
        n = sat_add(n, sat_add(1, tr_count(p, dc, &ts[i])));
        i += 1;
    }
    n
}

/// The number of definitions of the translation of `p` (`tr_problem`).
fn tr_size(p: &SmtProblem) -> usize {
    let mut dc = Vec::new();
    let mut n: usize = 0;
    let mut d: usize = 0;
    while d < p.defs.len() {
        let c = tr_count(p, &dc, &p.defs[d].body);
        if p.defs[d].params.len() == 0 {
            n = sat_add(n, sat_add(1, c));
            dc.push(0);
        } else {
            dc.push(c);
        }
        d += 1;
    }
    let mut j: usize = 0;
    while j < p.asserts.len() {
        n = sat_add(n, tr_count(p, &dc, &p.asserts[j]));
        j += 1;
    }
    n
}

/// The width of the result of the binary operator `op` on operands of widths `wa` and `wb`.
fn op_width(op: &Op, wa: usize, wb: usize) -> usize {
    match op {
        Op::Concat => sat_add(wa, wb),
        Op::Comp | Op::Eq | Op::Distinct => 1,
        Op::Ult | Op::Ule | Op::Ugt | Op::Uge => 1,
        Op::Slt | Op::Sle | Op::Sgt | Op::Sge => 1,
        _ => wa,
    }
}

/// `(w + 1)^3`.
fn cube1(w: usize) -> usize {
    let v = sat_add(w, 1);
    sat_mul(v, sat_mul(v, v))
}

/// The width of `t` and its weight (`width` and `term_weight` of the specification), for the
/// widths `ws` of the variables and `ds` of the definitions.
fn term_size(ws: &Vec<usize>, ds: &Vec<usize>, t: &Term) -> (usize, usize) {
    let (w, g) = match t {
        Term::Const(bs) => (bs.len(), 0),
        Term::Var(i) => (ws[*i], 0),
        Term::Ref(i) => (ds[*i], 0),
        Term::Not(a) => term_size(ws, ds, a),
        Term::Neg(a) => term_size(ws, ds, a),
        Term::Bin(op, a, b) => {
            let (wa, ga) = term_size(ws, ds, a);
            let (wb, gb) = term_size(ws, ds, b);
            (op_width(op, wa, wb), sat_add(ga, gb))
        }
        Term::Extract(hi, lo, a) => {
            let (_, ga) = term_size(ws, ds, a);
            (sat_add(*hi - *lo, 1), ga)
        }
        Term::Repeat(i, a) => {
            let (wa, ga) = term_size(ws, ds, a);
            (sat_mul(*i, wa), ga)
        }
        Term::ZeroExtend(i, a) => {
            let (wa, ga) = term_size(ws, ds, a);
            (sat_add(wa, *i), ga)
        }
        Term::SignExtend(i, a) => {
            let (wa, ga) = term_size(ws, ds, a);
            (sat_add(wa, *i), ga)
        }
        Term::RotateLeft(_, a) => term_size(ws, ds, a),
        Term::RotateRight(_, a) => term_size(ws, ds, a),
        Term::Ite(c, a, b) => {
            let (_, gc) = term_size(ws, ds, c);
            let (wa, ga) = term_size(ws, ds, a);
            let (_, gb) = term_size(ws, ds, b);
            (wa, sat_add(gc, sat_add(ga, gb)))
        }
    };
    (w, sat_add(cube1(w), g))
}

/// Whether the `size_bound` of `q` is below 2^63.
fn size_ok(q: &Problem) -> bool {
    let mut ds = Vec::new();
    let mut d: usize = 0;
    while d < q.defs.len() {
        let (w, _) = term_size(&q.widths, &ds, &q.defs[d]);
        ds.push(w);
        d += 1;
    }
    let mut n: usize = 1;
    let mut i: usize = 0;
    while i < q.widths.len() {
        n = sat_add(n, q.widths[i]);
        i += 1;
    }
    n = sat_add(n, q.widths.len());
    n = sat_add(n, q.defs.len());
    n = sat_add(n, q.asserts.len());
    let mut k: usize = 0;
    while k < q.defs.len() {
        let (_, g) = term_size(&q.widths, &ds, &q.defs[k]);
        n = sat_add(n, g);
        k += 1;
    }
    let mut j: usize = 0;
    while j < q.asserts.len() {
        let (_, g) = term_size(&q.widths, &ds, &q.asserts[j]);
        n = sat_add(n, g);
        j += 1;
    }
    sat_mul(1000000, n) < cap()
}

/// The solver on a general problem: `Unknown` outside the fragment, or if the problem is too
/// large (see the size checks above); otherwise the problem is translated into the extended
/// language and solved.
pub fn check_sat(p: &SmtProblem) -> SmtAnswer {
    if !in_fragment(p) {
        return SmtAnswer::Unknown;
    }
    if tr_size(p) >= cap() {
        return SmtAnswer::Unknown;
    }
    let q = tr_problem(p);
    if !size_ok(&q) {
        return SmtAnswer::Unknown;
    }
    match solve(&q) {
        Answer::Sat(m) => SmtAnswer::Sat(tr_model(p, &m)),
        Answer::Unsat => SmtAnswer::Unsat,
    }
}
