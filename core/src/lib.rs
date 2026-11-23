//! A vanilla SMT solver for quantifier-free bit-vector formulas (QF_BV).
//!
//! A problem is written with every bit-vector operation of SMT-LIB 2.6 (the theory
//! FixedSizeBitVectors and the logic QF_BV; `Term`). The solver first rewrites it, following the
//! definitions of SMT-LIB, into the core language `CoreTerm` of fifteen basic operations
//! (`lower_problem`); it then bit-blasts the core problem into a CNF formula with the Tseitin
//! encoding and decides the CNF formula with DPLL (unit propagation over two watched literals per
//! clause, and chronological backtracking). It answers either `Sat` with a model or `Unsat`.
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
fn tseitin_and(cnf: Cnf, a: Lit, b: Lit) -> (Cnf, Lit) {
    let (cnf, x) = fresh(cnf);
    let cnf = add_clause(cnf, clause2(lit_neg(x), a));
    let cnf = add_clause(cnf, clause2(lit_neg(x), b));
    let cnf = add_clause(cnf, clause3(x, lit_neg(a), lit_neg(b)));
    (cnf, x)
}

/// A fresh literal `x` with `x <-> a ^ b`.
fn tseitin_xor(cnf: Cnf, a: Lit, b: Lit) -> (Cnf, Lit) {
    let (cnf, x) = fresh(cnf);
    let cnf = add_clause(cnf, clause3(lit_neg(x), a, b));
    let cnf = add_clause(cnf, clause3(lit_neg(x), lit_neg(a), lit_neg(b)));
    let cnf = add_clause(cnf, clause3(x, lit_neg(a), b));
    let cnf = add_clause(cnf, clause3(x, a, lit_neg(b)));
    (cnf, x)
}

/// A fresh literal `x` with `x <-> (if c then a else b)`.
fn tseitin_ite(cnf: Cnf, c: Lit, a: Lit, b: Lit) -> (Cnf, Lit) {
    let (cnf, x) = fresh(cnf);
    let cnf = add_clause(cnf, clause3(lit_neg(c), lit_neg(x), a));
    let cnf = add_clause(cnf, clause3(lit_neg(c), x, lit_neg(a)));
    let cnf = add_clause(cnf, clause3(c, lit_neg(x), b));
    let cnf = add_clause(cnf, clause3(c, x, lit_neg(b)));
    (cnf, x)
}

// The gates below simplify before they fall back to a Tseitin gate: variable 0 is the constant
// (`lit_const`), so an input on variable 0 is a constant, and two inputs on the same variable are
// equal or complementary.

/// A literal `x` with `x <-> a & b`.
fn gate_and(cnf: Cnf, a: Lit, b: Lit) -> (Cnf, Lit) {
    if a.var == 0 {
        if a.neg { (cnf, a) } else { (cnf, b) }
    } else if b.var == 0 {
        if b.neg { (cnf, b) } else { (cnf, a) }
    } else if a.var == b.var {
        if a.neg == b.neg { (cnf, a) } else { (cnf, lit_const(false)) }
    } else {
        tseitin_and(cnf, a, b)
    }
}

/// A literal `x` with `x <-> a | b`.
fn gate_or(cnf: Cnf, a: Lit, b: Lit) -> (Cnf, Lit) {
    let (cnf, x) = gate_and(cnf, lit_neg(a), lit_neg(b));
    (cnf, lit_neg(x))
}

/// A literal `x` with `x <-> a ^ b`.
fn gate_xor(cnf: Cnf, a: Lit, b: Lit) -> (Cnf, Lit) {
    if a.var == 0 {
        if a.neg { (cnf, b) } else { (cnf, lit_neg(b)) }
    } else if b.var == 0 {
        if b.neg { (cnf, a) } else { (cnf, lit_neg(a)) }
    } else if a.var == b.var {
        if a.neg == b.neg { (cnf, lit_const(false)) } else { (cnf, lit_const(true)) }
    } else {
        tseitin_xor(cnf, a, b)
    }
}

/// A literal `x` with `x <-> (if c then a else b)`.
fn gate_ite(cnf: Cnf, c: Lit, a: Lit, b: Lit) -> (Cnf, Lit) {
    if c.var == 0 {
        if c.neg { (cnf, b) } else { (cnf, a) }
    } else if a.var == b.var {
        if a.neg == b.neg {
            (cnf, a)
        } else {
            let (cnf, x) = gate_xor(cnf, c, a);
            (cnf, lit_neg(x))
        }
    } else if a.var == 0 {
        if a.neg { gate_and(cnf, lit_neg(c), b) } else { gate_or(cnf, c, b) }
    } else if b.var == 0 {
        if b.neg { gate_and(cnf, c, a) } else { gate_or(cnf, lit_neg(c), a) }
    } else {
        tseitin_ite(cnf, c, a, b)
    }
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

/// `a` shifted by `b`, by a barrel shifter. Stage `i` shifts by `p = 2^i` if bit `i` of `b` is
/// set, for every `i` with `2^i` below the width. The bits of `b` from the first `i` with `2^i`
/// at least the width on are or-ed into `big`: if `big` holds, the shift is at least the width and
/// the result is 0. Once `2 p` exceeds the width, `p` is set to the width instead of doubled, so
/// that it does not overflow.
fn bv_shift(cnf: Cnf, a: &Vec<Lit>, b: &Vec<Lit>, left: bool) -> (Cnf, Vec<Lit>) {
    let mut cnf = cnf;
    let mut r = bv_shift_const(a, 0, left);
    let mut big = lit_const(false);
    let mut p: usize = 1;
    let mut i: usize = 0;
    while i < b.len() {
        if p < a.len() {
            let (c1, x) = bv_ite(cnf, b[i], &bv_shift_const(&r, p, left), &r);
            cnf = c1;
            r = x;
            if p <= a.len() - p {
                p = p + p;
            } else {
                p = a.len();
            }
        } else {
            let (c1, o) = gate_or(cnf, big, b[i]);
            cnf = c1;
            big = o;
        }
        i += 1;
    }
    bv_ite(cnf, big, &vec![lit_const(false); a.len()], &r)
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

/// Unassigns the variables of the trail from position `p` on, and removes them from the trail.
fn backtrack(a: Vec<Option<bool>>, trail: Vec<Lit>, p: usize) -> (Vec<Option<bool>>, Vec<Lit>) {
    let mut a = a;
    let mut trail = trail;
    while p < trail.len() {
        match trail.pop() {
            Some(l) => a[l.var] = None,
            None => {}
        }
    }
    (a, trail)
}

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

/// One pass of unit propagation over the clauses: assigns the literal of every unit clause in
/// place and pushes it on the trail, and the index of the clause on the reasons `rs`. The flag is
/// false on a conflict, which ends the pass.
fn propagate_pass(cs: &Vec<Vec<Lit>>, a: Vec<Option<bool>>, trail: Vec<Lit>, rs: Vec<usize>) -> (Vec<Option<bool>>, Vec<Lit>, Vec<usize>, bool) {
    let mut a = a;
    let mut trail = trail;
    let mut rs = rs;
    let mut i: usize = 0;
    while i < cs.len() {
        match clause_status(&a, &cs[i]) {
            Status::Conflict => return (a, trail, rs, false),
            Status::Unit(l) => {
                a[l.var] = Some(!l.neg);
                trail.push(l);
                rs.push(i);
            }
            Status::Satisfied => {}
            Status::Open => {}
        }
        i += 1;
    }
    (a, trail, rs, true)
}

// Watched literals. Each clause of at least two literals watches two of them; slot `2c + k` is
// the watch `k` of clause `c`. `pos[s]` is the position in its clause of the literal that slot `s`
// watches, `next[s]` the next slot in the list of the same literal, and `head[lit_index(l)]` the
// first slot of the list of literal `l`. A link at or above `next.len()` ends a list; the lists end
// with `usize::MAX`, so that they stay well formed when the slots of learned clauses are appended. Every unit or
// conflict the watches point to is also confirmed by `clause_status`.

fn lit_index(l: Lit) -> usize {
    if l.neg {
        2 * l.var + 1
    } else {
        2 * l.var
    }
}

/// The watch lists of the clauses over `n` variables: every clause of at least two literals watches
/// its first two.
fn watch_init(cs: &Vec<Vec<Lit>>, n: usize) -> (Vec<usize>, Vec<usize>, Vec<usize>) {
    let m = cs.len();
    let mut pos: Vec<usize> = vec![0; 2 * m];
    let mut next: Vec<usize> = vec![usize::MAX; 2 * m];
    let mut head: Vec<usize> = vec![usize::MAX; 2 * n];
    let mut c: usize = 0;
    while c < m {
        if cs[c].len() >= 2 {
            let s = 2 * c;
            pos[s + 1] = 1;
            let x0 = lit_index(cs[c][0]);
            next[s] = head[x0];
            head[x0] = s;
            let x1 = lit_index(cs[c][1]);
            next[s + 1] = head[x1];
            head[x1] = s + 1;
        }
        c += 1;
    }
    (pos, next, head)
}

/// A position of the clause, other than `i` and `j`, whose literal is not false.
fn find_watch(a: &Vec<Option<bool>>, c: &Vec<Lit>, i: usize, j: usize) -> Option<usize> {
    let mut k: usize = 0;
    while k < c.len() {
        if k != i && k != j && lit_value(a, c[k]) != Some(false) {
            return Some(k);
        }
        k += 1;
    }
    None
}

fn set_at(v: Vec<usize>, i: usize, e: usize) -> Vec<usize> {
    let mut v = v;
    v[i] = e;
    v
}

/// Moves the watch of slot `s` to position `k` of its clause, whose literal has index `y`: unlinks
/// the slot from the list of the literal of index `x` (after slot `prev`, or at its head) and links
/// it at the head of the list of `y`.
fn move_watch(pos: Vec<usize>, next: Vec<usize>, head: Vec<usize>, s: usize, prev: usize, x: usize, k: usize, y: usize) -> (Vec<usize>, Vec<usize>, Vec<usize>) {
    let ns = next[s];
    let pos = set_at(pos, s, k);
    if prev < next.len() {
        let next = set_at(next, prev, ns);
        let hy = head[y];
        (pos, set_at(next, s, hy), set_at(head, y, s))
    } else {
        let head = set_at(head, x, ns);
        let hy = head[y];
        (pos, set_at(next, s, hy), set_at(head, y, s))
    }
}

/// Visits slot `s` of the list of the literal of index `x`, which has become false (`prev` is the
/// slot before it in the list). If the other watched literal of the clause is true, the slot stays;
/// otherwise its watch moves to another literal that is not false, if there is one, and else the
/// clause is unit (its literal is assigned and pushed on the trail, the clause on the reasons) or in
/// conflict. The first flag
/// tells whether the slot stays on the list, the second is false on a conflict.
fn visit_slot(cs: &Vec<Vec<Lit>>, pos: Vec<usize>, next: Vec<usize>, head: Vec<usize>, a: Vec<Option<bool>>, trail: Vec<Lit>, rs: Vec<usize>, x: usize, s: usize, prev: usize) -> (Vec<usize>, Vec<usize>, Vec<usize>, Vec<Option<bool>>, Vec<Lit>, Vec<usize>, bool, bool) {
    let mut a = a;
    let mut trail = trail;
    let mut rs = rs;
    let c = s / 2;
    let o = if s % 2 == 0 { s + 1 } else { s - 1 };
    let i = pos[s];
    let j = pos[o];
    if i < cs[c].len() && j < cs[c].len() && lit_value(&a, cs[c][j]) != Some(true) {
        match find_watch(&a, &cs[c], i, j) {
            Some(k) => {
                let y = lit_index(cs[c][k]);
                let (p1, n1, h1) = move_watch(pos, next, head, s, prev, x, k, y);
                return (p1, n1, h1, a, trail, rs, false, true);
            }
            None => match clause_status(&a, &cs[c]) {
                Status::Conflict => return (pos, next, head, a, trail, rs, true, false),
                Status::Unit(l) => {
                    a[l.var] = Some(!l.neg);
                    trail.push(l);
                    rs.push(c);
                }
                Status::Satisfied => {}
                Status::Open => {}
            },
        }
    }
    (pos, next, head, a, trail, rs, true, true)
}

/// Visits the clauses that watch the literal of index `x`, which has become false, slot by slot
/// (`visit_slot`). The flag is false on a conflict, which ends the visit; the last result is then
/// the index of the clause in conflict.
fn visit(cs: &Vec<Vec<Lit>>, pos: Vec<usize>, next: Vec<usize>, head: Vec<usize>, a: Vec<Option<bool>>, trail: Vec<Lit>, rs: Vec<usize>, x: usize) -> (Vec<usize>, Vec<usize>, Vec<usize>, Vec<Option<bool>>, Vec<Lit>, Vec<usize>, bool, usize) {
    let mut pos = pos;
    let mut next = next;
    let mut head = head;
    let mut a = a;
    let mut trail = trail;
    let mut rs = rs;
    let nil = next.len();
    let mut s = head[x];
    let mut prev = nil;
    let mut steps: usize = 0;
    while s < nil && steps < nil {
        steps += 1;
        let ns = next[s];
        let (p1, n1, h1, a1, t1, r1, keep, ok) = visit_slot(cs, pos, next, head, a, trail, rs, x, s, prev);
        pos = p1;
        next = n1;
        head = h1;
        a = a1;
        trail = t1;
        rs = r1;
        if !ok {
            return (pos, next, head, a, trail, rs, false, s / 2);
        }
        if keep {
            prev = s;
        }
        s = ns;
    }
    (pos, next, head, a, trail, rs, true, 0)
}

/// Unit propagation over the watches: visits the clauses watching the negation of every trail
/// entry from position `q` on. The flag is false on a conflict; the last result is then the index
/// of the clause in conflict.
fn wpropagate(cs: &Vec<Vec<Lit>>, pos: Vec<usize>, next: Vec<usize>, head: Vec<usize>, a: Vec<Option<bool>>, trail: Vec<Lit>, rs: Vec<usize>, q: usize) -> (Vec<usize>, Vec<usize>, Vec<usize>, Vec<Option<bool>>, Vec<Lit>, Vec<usize>, usize, bool, usize) {
    let mut pos = pos;
    let mut next = next;
    let mut head = head;
    let mut a = a;
    let mut trail = trail;
    let mut rs = rs;
    let mut q = q;
    while q < trail.len() {
        let x = lit_index(lit_neg(trail[q]));
        q += 1;
        let (p1, n1, h1, a1, t1, r1, ok, cf) = visit(cs, pos, next, head, a, trail, rs, x);
        pos = p1;
        next = n1;
        head = h1;
        a = a1;
        trail = t1;
        rs = r1;
        if !ok {
            return (pos, next, head, a, trail, rs, q, false, cf);
        }
    }
    (pos, next, head, a, trail, rs, q, true, 0)
}

/// Removes the entries of `v` from position `p` on.
fn cut(v: Vec<usize>, p: usize) -> Vec<usize> {
    let mut v = v;
    while p < v.len() {
        v.pop();
    }
    v
}

/// A total assignment of the `n` variables that satisfies the clauses, if there is one.
///
/// The search assigns in place and records the true literals in order on the trail; `lim` holds
/// the trail positions of the decisions, so that the decision level of an entry is the number of
/// decisions at or before it. `rs` holds the reason of every trail entry: the clause that implied
/// it, or 0 for a decision or a flipped decision (not used yet). A pass over the clauses first
/// assigns the unit clauses; then the watches propagate the trail entries from position `q` on. On
/// a conflict the last decision is
/// undone with every entry after it and its negation is pushed as an implied entry (chronological
/// backtracking). The watches are complete (every clause of at least two literals that is not
/// satisfied watches two literals that are not false, or its unit literal is still to be
/// propagated), so a total assignment reached without a conflict satisfies every clause.
fn dpll(cs: &Vec<Vec<Lit>>, n: usize) -> Option<Vec<Option<bool>>> {
    let (pos0, next0, head0) = watch_init(cs, n);
    let mut pos = pos0;
    let mut next = next0;
    let mut head = head0;
    let (a0, t0, r0, ok0) = propagate_pass(cs, vec![None; n], Vec::new(), Vec::new());
    if !ok0 {
        return None;
    }
    let mut a: Vec<Option<bool>> = a0;
    let mut trail: Vec<Lit> = t0;
    let mut rs: Vec<usize> = r0;
    let mut lim: Vec<usize> = Vec::new();
    let mut q: usize = 0;
    loop {
        let (p1, n1, h1, a1, t1, r1, q1, ok, _cf) = wpropagate(cs, pos, next, head, a, trail, rs, q);
        pos = p1;
        next = n1;
        head = h1;
        a = a1;
        trail = t1;
        rs = r1;
        q = q1;
        if ok {
            match find_unassigned(&a) {
                None => return Some(a),
                Some(v) => {
                    lim.push(trail.len());
                    a[v] = Some(true);
                    trail.push(Lit { var: v, neg: false });
                    rs.push(0);
                }
            }
        }
        if !ok {
            match lim.pop() {
                None => return None,
                Some(p) => {
                    let d = trail[p];
                    let (a2, t2) = backtrack(a, trail, p);
                    a = a2;
                    trail = t2;
                    rs = cut(rs, p);
                    a[d.var] = Some(d.neg);
                    trail.push(lit_neg(d));
                    rs.push(0);
                    q = p;
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------------------------
// The solver

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
    match dpll(&cnf.clauses, cnf.num_vars) {
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

/// The solver: rewrites the problem into the core language, normalizes it, eliminates its
/// unconstrained definitions, solves the result and reconstructs a model of the problem from a
/// model of it.
pub fn solve(p: &Problem) -> Answer {
    let q = normalize(&lower_problem(p));
    let (q2, kind, mark) = elim(&q);
    match solve_core(&q2) {
        Answer::Sat(m2) => Answer::Sat(reconstruct(&q, &kind, &mark, &q2, &m2)),
        Answer::Unsat => Answer::Unsat,
    }
}

// ---------------------------------------------------------------------------------------------
// Evaluation of core terms. A value is a list of bits, least significant bit first, as in a
// model. Model reconstruction needs the values of definitions under a model.

fn bits_not(a: &Vec<bool>) -> Vec<bool> {
    let mut r = Vec::new();
    let mut i: usize = 0;
    while i < a.len() {
        r.push(!a[i]);
        i += 1;
    }
    r
}

/// `x & y`, `x | y` or `x ^ y` for `And`, `Or` or `Xor` (any other operator).
fn bit_op(op: &BinOp, x: bool, y: bool) -> bool {
    match op {
        BinOp::And => x && y,
        BinOp::Or => x || y,
        _ => x != y,
    }
}

/// `And`, `Or` or `Xor` (any other operator) bit by bit.
fn bits_bitwise(op: &BinOp, a: &Vec<bool>, b: &Vec<bool>) -> Vec<bool> {
    let mut r = Vec::new();
    let mut i: usize = 0;
    while i < a.len() {
        r.push(bit_op(op, a[i], b[i]));
        i += 1;
    }
    r
}

/// The sum bit and the carry of `x + y + c`.
fn full_add(x: bool, y: bool, c: bool) -> (bool, bool) {
    let s = x != (y != c);
    if x == y {
        (s, x)
    } else {
        (s, c)
    }
}

/// The sum of `a`, `b` and the carry `cin`, truncated to the width of `a`, and the carry out.
fn bits_add(a: &Vec<bool>, b: &Vec<bool>, cin: bool) -> (Vec<bool>, bool) {
    let mut carry = cin;
    let mut r = Vec::new();
    let mut i: usize = 0;
    while i < a.len() {
        let (s, c) = full_add(a[i], b[i], carry);
        r.push(s);
        carry = c;
        i += 1;
    }
    (r, carry)
}

/// `a` shifted by `s` places, to the left (towards the high bits) or to the right.
fn bits_shift_const(a: &Vec<bool>, s: usize, left: bool) -> Vec<bool> {
    let mut r = Vec::new();
    let mut j: usize = 0;
    while j < a.len() {
        if left {
            if j < s {
                r.push(false);
            } else {
                r.push(a[j - s]);
            }
        } else if s < a.len() - j {
            r.push(a[j + s]);
        } else {
            r.push(false);
        }
        j += 1;
    }
    r
}

/// The product of `a` and `b`, truncated to the width of `a`: the sum of `a << i` over the set
/// bits `i` of `b`.
fn bits_mul(a: &Vec<bool>, b: &Vec<bool>) -> Vec<bool> {
    let mut acc = vec![false; a.len()];
    let mut i: usize = 0;
    while i < a.len() {
        if b[i] {
            let (s, _) = bits_add(&acc, &bits_shift_const(a, i, true), false);
            acc = s;
        }
        i += 1;
    }
    acc
}

fn bits_eq(a: &Vec<bool>, b: &Vec<bool>) -> bool {
    let mut r = true;
    let mut i: usize = 0;
    while i < a.len() {
        if a[i] != b[i] {
            r = false;
        }
        i += 1;
    }
    r
}

/// Whether `a < b` (unsigned): `a + !b + 1` has no carry out.
fn bits_ult(a: &Vec<bool>, b: &Vec<bool>) -> bool {
    let (_, c) = bits_add(a, &bits_not(b), true);
    !c
}

/// `a` extended with zeros, or truncated, to width `w`.
fn bits_zext(a: &Vec<bool>, w: usize) -> Vec<bool> {
    let mut r = Vec::new();
    let mut i: usize = 0;
    while i < w {
        if i < a.len() {
            r.push(a[i]);
        } else {
            r.push(false);
        }
        i += 1;
    }
    r
}

/// `2 r + x`, truncated to the width of `r`: `x` below the bits of `r` but its highest.
fn bits_shl1(r: &Vec<bool>, x: bool) -> Vec<bool> {
    let mut s = Vec::new();
    s.push(x);
    let mut k: usize = 0;
    while k + 1 < r.len() {
        s.push(r[k]);
        k += 1;
    }
    s
}

/// The unsigned quotient and remainder of `a` and `b` (all ones and `a` if `b` is 0), by long
/// division: from the highest bit of `a` down, the remainder so far (one bit wider than `a`, so
/// that `2 r + 1` fits) takes the next bit, and `b` is subtracted where it fits.
fn bits_divrem(a: &Vec<bool>, b: &Vec<bool>) -> (Vec<bool>, Vec<bool>) {
    let w = a.len();
    if bits_eq(b, &vec![false; w]) {
        return (vec![true; w], a.clone());
    }
    let nb = bits_not(&bits_zext(b, w + 1));
    let mut q = vec![false; w];
    let mut r = vec![false; w + 1];
    let mut i: usize = w;
    while i > 0 {
        i -= 1;
        let r1 = bits_shl1(&r, a[i]);
        let (d, c) = bits_add(&r1, &nb, true);
        if c {
            r = d;
            q[i] = true;
        } else {
            r = r1;
        }
    }
    (q, bits_zext(&r, w))
}

/// One step of the shift amount: `2 s + x`, at most `w`, if `s < w`; otherwise `s`.
fn shift_amount_step(s: usize, x: bool, w: usize) -> usize {
    if s < w {
        let t = if x { s + s + 1 } else { s + s };
        if t > w {
            w
        } else {
            t
        }
    } else {
        s
    }
}

/// `a` shifted by `b`: by the value of `b`, or by the width of `a` (all zeros) if that is smaller.
/// The shift is computed from the highest bit of `b` down and kept at most the width.
fn bits_shift(a: &Vec<bool>, b: &Vec<bool>, left: bool) -> Vec<bool> {
    let w = a.len();
    let mut s: usize = 0;
    let mut i: usize = b.len();
    while i > 0 {
        i -= 1;
        s = shift_amount_step(s, b[i], w);
    }
    bits_shift_const(a, s, left)
}

/// Bits `lo..=hi` of `a`.
fn bits_extract(a: &Vec<bool>, hi: usize, lo: usize) -> Vec<bool> {
    let mut r = Vec::new();
    let mut i: usize = lo;
    while i <= hi {
        r.push(a[i]);
        i += 1;
    }
    r
}

/// The concatenation with `hi` as the high part.
fn bits_concat(hi: &Vec<bool>, lo: &Vec<bool>) -> Vec<bool> {
    let mut r = lo.clone();
    let mut i: usize = 0;
    while i < hi.len() {
        r.push(hi[i]);
        i += 1;
    }
    r
}

fn eval_bin(op: &BinOp, a: &Vec<bool>, b: &Vec<bool>) -> Vec<bool> {
    match op {
        BinOp::And => bits_bitwise(op, a, b),
        BinOp::Or => bits_bitwise(op, a, b),
        BinOp::Xor => bits_bitwise(op, a, b),
        BinOp::Add => {
            let (s, _) = bits_add(a, b, false);
            s
        }
        BinOp::Mul => bits_mul(a, b),
        BinOp::Udiv => {
            let (q, _) = bits_divrem(a, b);
            q
        }
        BinOp::Urem => {
            let (_, r) = bits_divrem(a, b);
            r
        }
        BinOp::Shl => bits_shift(a, b, true),
        BinOp::Lshr => bits_shift(a, b, false),
        BinOp::Concat => bits_concat(a, b),
        BinOp::Eq => {
            let mut r = Vec::new();
            r.push(bits_eq(a, b));
            r
        }
        BinOp::Ult => {
            let mut r = Vec::new();
            r.push(bits_ult(a, b));
            r
        }
    }
}

/// The value of `t`, given the values `vars` of the variables and `defs` of the definitions.
pub fn eval_term(vars: &Vec<Vec<bool>>, defs: &Vec<Vec<bool>>, t: &CoreTerm) -> Vec<bool> {
    match t {
        CoreTerm::Const(bits) => bits.clone(),
        CoreTerm::Var(i) => vars[*i].clone(),
        CoreTerm::Ref(i) => defs[*i].clone(),
        CoreTerm::Not(a) => bits_not(&eval_term(vars, defs, a)),
        CoreTerm::Bin(op, a, b) => {
            let x = eval_term(vars, defs, a);
            let y = eval_term(vars, defs, b);
            eval_bin(op, &x, &y)
        }
        CoreTerm::Extract(hi, lo, a) => bits_extract(&eval_term(vars, defs, a), *hi, *lo),
        CoreTerm::Ite(c, a, b) => {
            let x = eval_term(vars, defs, c);
            if x[0] {
                eval_term(vars, defs, a)
            } else {
                eval_term(vars, defs, b)
            }
        }
    }
}

/// The values of the definitions of `p` under the assignment `m` of its variables.
pub fn eval_defs(p: &CoreProblem, m: &Vec<Vec<bool>>) -> Vec<Vec<bool>> {
    let mut defs = Vec::new();
    let mut j: usize = 0;
    while j < p.defs.len() {
        let v = eval_term(m, &defs, &p.defs[j]);
        defs.push(v);
        j += 1;
    }
    defs
}

// ---------------------------------------------------------------------------------------------
// Elimination of unconstrained definitions. A definition is *free* when its value can be chosen
// freely, independently of everything else: a variable that occurs once in the problem, or an
// operation that can take every value by the choice of an operand that is itself free and occurs
// once (it is *consumed*). Each free definition is rewritten to (the low bits of) the operand it
// consumes, so that in the new problem its value is the low bits of a variable; the definitions no
// longer reachable from the assertions become constants. The variables, the number of definitions
// and the width of every definition stay the same, and no term grows. A model of the new problem
// gives a model of the problem by pushing the value of each free definition down to its variable.
//
// The kind of a definition: 0 not free; 1 a variable that occurs once; 2 free, consuming its first
// operand (the condition of `Ite`); 3 free, consuming its second operand; 4 `Mul` or `Udiv` of two
// free operands: the first is consumed and the second is set to 1. The mark of a definition: 1 if
// consumed, 2 if it is the second operand of a definition of kind 4, else 0.

/// `c[i]` plus one, at most 2.
fn bump(c: Vec<usize>, i: usize) -> Vec<usize> {
    let mut c = c;
    if c[i] < 2 {
        c[i] = c[i] + 1;
    }
    c
}

/// Adds the occurrences of variables and of definitions in `t` to `vc` and `rc` (at most 2).
fn count_occ(vc: Vec<usize>, rc: Vec<usize>, t: &CoreTerm) -> (Vec<usize>, Vec<usize>) {
    match t {
        CoreTerm::Const(_) => (vc, rc),
        CoreTerm::Var(i) => (bump(vc, *i), rc),
        CoreTerm::Ref(i) => (vc, bump(rc, *i)),
        CoreTerm::Not(a) => count_occ(vc, rc, a),
        CoreTerm::Bin(_, a, b) => {
            let (vc, rc) = count_occ(vc, rc, a);
            count_occ(vc, rc, b)
        }
        CoreTerm::Extract(_, _, a) => count_occ(vc, rc, a),
        CoreTerm::Ite(c, a, b) => {
            let (vc, rc) = count_occ(vc, rc, c);
            let (vc, rc) = count_occ(vc, rc, a);
            count_occ(vc, rc, b)
        }
    }
}

/// The width of `t`, given the widths `ws` of the variables and `dw` of the definitions.
fn term_width(ws: &Vec<usize>, dw: &Vec<usize>, t: &CoreTerm) -> usize {
    match t {
        CoreTerm::Const(bits) => bits.len(),
        CoreTerm::Var(i) => ws[*i],
        CoreTerm::Ref(i) => dw[*i],
        CoreTerm::Not(a) => term_width(ws, dw, a),
        CoreTerm::Bin(op, a, b) => match op {
            BinOp::Concat => term_width(ws, dw, a) + term_width(ws, dw, b),
            BinOp::Eq => 1,
            BinOp::Ult => 1,
            _ => term_width(ws, dw, a),
        },
        CoreTerm::Extract(hi, lo, _) => *hi - *lo + 1,
        CoreTerm::Ite(_, a, _) => term_width(ws, dw, a),
    }
}

/// The index `i` of `Ref(i)`; `n` for any other term.
fn ref_index(t: &CoreTerm, n: usize) -> usize {
    match t {
        CoreTerm::Ref(i) => *i,
        _ => n,
    }
}

/// 0 or 1 for a constant of width 1; 2 for any other term.
fn bit_const(t: &CoreTerm) -> usize {
    match t {
        CoreTerm::Const(bits) => {
            if bits.len() == 1 {
                if bits[0] {
                    1
                } else {
                    0
                }
            } else {
                2
            }
        }
        _ => 2,
    }
}

/// Whether `i` refers to a free definition (of index below `kind.len()`) that occurs once.
fn free_once(kind: &Vec<usize>, rc: &Vec<usize>, i: usize) -> bool {
    i < kind.len() && kind[i] != 0 && rc[i] == 1
}

/// The kind of the definition `t`, given the definitions before it (`defs`, with widths `dw` and
/// kinds `kind`) and the occurrence counts `vc`, `rc`.
fn free_kind(defs: &Vec<CoreTerm>, dw: &Vec<usize>, vc: &Vec<usize>, rc: &Vec<usize>, kind: &Vec<usize>, t: &CoreTerm) -> usize {
    let n = kind.len();
    match t {
        CoreTerm::Var(i) => {
            if vc[*i] == 1 {
                1
            } else {
                0
            }
        }
        CoreTerm::Not(a) => {
            if free_once(kind, rc, ref_index(a, n)) {
                2
            } else {
                0
            }
        }
        CoreTerm::Extract(_, _, a) => {
            if free_once(kind, rc, ref_index(a, n)) {
                2
            } else {
                0
            }
        }
        CoreTerm::Bin(op, a, b) => {
            let ia = ref_index(a, n);
            let ib = ref_index(b, n);
            match op {
                BinOp::Add => {
                    if free_once(kind, rc, ia) {
                        2
                    } else if free_once(kind, rc, ib) {
                        3
                    } else {
                        0
                    }
                }
                BinOp::Xor => {
                    if free_once(kind, rc, ia) {
                        2
                    } else if free_once(kind, rc, ib) {
                        3
                    } else {
                        0
                    }
                }
                BinOp::Eq => {
                    if free_once(kind, rc, ia) && dw[ia] > 0 {
                        2
                    } else if free_once(kind, rc, ib) && dw[ib] > 0 {
                        3
                    } else {
                        0
                    }
                }
                BinOp::Mul => {
                    if free_once(kind, rc, ia) && free_once(kind, rc, ib) && ia != ib {
                        4
                    } else {
                        0
                    }
                }
                BinOp::Udiv => {
                    if free_once(kind, rc, ia) && free_once(kind, rc, ib) && ia != ib {
                        4
                    } else {
                        0
                    }
                }
                _ => 0,
            }
        }
        CoreTerm::Ite(c, a, b) => {
            let ic = ref_index(c, n);
            let ia = ref_index(a, n);
            let ib = ref_index(b, n);
            if free_once(kind, rc, ic) && ia < n && ib < n {
                let x = bit_const(&defs[ia]);
                let y = bit_const(&defs[ib]);
                if x < 2 && y < 2 && x != y {
                    2
                } else {
                    0
                }
            } else {
                0
            }
        }
        _ => 0,
    }
}

/// The operand that a definition `t` of kind `k` (2, 3 or 4) consumes.
fn consumed(t: &CoreTerm, k: usize, n: usize) -> usize {
    match t {
        CoreTerm::Not(a) => ref_index(a, n),
        CoreTerm::Extract(_, _, a) => ref_index(a, n),
        CoreTerm::Bin(_, a, b) => {
            if k == 3 {
                ref_index(b, n)
            } else {
                ref_index(a, n)
            }
        }
        CoreTerm::Ite(c, _, _) => ref_index(c, n),
        _ => n,
    }
}

/// The second operand of a binary operation.
fn second(t: &CoreTerm, n: usize) -> usize {
    match t {
        CoreTerm::Bin(_, _, b) => ref_index(b, n),
        _ => n,
    }
}

fn copy_op(op: &BinOp) -> BinOp {
    match op {
        BinOp::And => BinOp::And,
        BinOp::Or => BinOp::Or,
        BinOp::Xor => BinOp::Xor,
        BinOp::Add => BinOp::Add,
        BinOp::Mul => BinOp::Mul,
        BinOp::Udiv => BinOp::Udiv,
        BinOp::Urem => BinOp::Urem,
        BinOp::Shl => BinOp::Shl,
        BinOp::Lshr => BinOp::Lshr,
        BinOp::Concat => BinOp::Concat,
        BinOp::Eq => BinOp::Eq,
        BinOp::Ult => BinOp::Ult,
    }
}

fn copy_term(t: &CoreTerm) -> CoreTerm {
    match t {
        CoreTerm::Const(bits) => CoreTerm::Const(bits.clone()),
        CoreTerm::Var(i) => CoreTerm::Var(*i),
        CoreTerm::Ref(i) => CoreTerm::Ref(*i),
        CoreTerm::Not(a) => cnot(copy_term(a)),
        CoreTerm::Bin(op, a, b) => cbin(copy_op(op), copy_term(a), copy_term(b)),
        CoreTerm::Extract(hi, lo, a) => cextract(*hi, *lo, copy_term(a)),
        CoreTerm::Ite(c, a, b) => cite(copy_term(c), copy_term(a), copy_term(b)),
    }
}

/// Marks the definitions referred to in `t` as live.
fn mark_live(live: Vec<bool>, t: &CoreTerm) -> Vec<bool> {
    match t {
        CoreTerm::Const(_) => live,
        CoreTerm::Var(_) => live,
        CoreTerm::Ref(i) => {
            let mut live = live;
            live[*i] = true;
            live
        }
        CoreTerm::Not(a) => mark_live(live, a),
        CoreTerm::Bin(_, a, b) => {
            let live = mark_live(live, a);
            mark_live(live, b)
        }
        CoreTerm::Extract(_, _, a) => mark_live(live, a),
        CoreTerm::Ite(c, a, b) => {
            let live = mark_live(live, c);
            let live = mark_live(live, a);
            mark_live(live, b)
        }
    }
}

/// Adds the occurrences of variables and of definitions in the terms `ts` to `vc` and `rc`.
fn count_terms(vc: Vec<usize>, rc: Vec<usize>, ts: &Vec<CoreTerm>) -> (Vec<usize>, Vec<usize>) {
    let mut vc = vc;
    let mut rc = rc;
    let mut i: usize = 0;
    while i < ts.len() {
        let (v1, r1) = count_occ(vc, rc, &ts[i]);
        vc = v1;
        rc = r1;
        i += 1;
    }
    (vc, rc)
}

/// The definition `t` of kind `c` and width `w` rewritten (given the widths `dw` of the
/// definitions before it, and the number `n` of definitions), and the marks updated.
fn rewrite_def(t: &CoreTerm, c: usize, w: usize, dw: &Vec<usize>, n: usize, mark: Vec<usize>) -> (CoreTerm, Vec<usize>) {
    if c >= 2 {
        let a = consumed(t, c, n);
        let mut mark = set_at(mark, a, 1);
        if c == 4 {
            mark = set_at(mark, second(t, n), 2);
        }
        if dw[a] == w {
            (CoreTerm::Ref(a), mark)
        } else {
            (cextract(w - 1, 0, cref(a)), mark)
        }
    } else {
        (copy_term(t), mark)
    }
}

/// The widths, the kinds and the marks of the definitions of `q`, and the definitions with the
/// free ones rewritten, given the occurrence counts `vc`, `rc`.
fn analyse(q: &CoreProblem, vc: &Vec<usize>, rc: &Vec<usize>) -> (Vec<usize>, Vec<usize>, Vec<usize>, Vec<CoreTerm>) {
    let n = q.defs.len();
    let mut dw: Vec<usize> = Vec::new();
    let mut kind: Vec<usize> = Vec::new();
    let mut mark: Vec<usize> = vec![0; n];
    let mut defs: Vec<CoreTerm> = Vec::new();
    let mut k: usize = 0;
    while k < n {
        let t = &q.defs[k];
        let w = term_width(&q.widths, &dw, t);
        let c = free_kind(&q.defs, &dw, vc, rc, &kind, t);
        let (t2, m1) = rewrite_def(t, c, w, &dw, n, mark);
        mark = m1;
        defs.push(t2);
        dw.push(w);
        kind.push(c);
        k += 1;
    }
    (dw, kind, mark, defs)
}

/// Marks the definitions referred to in the terms `ts` as live.
fn mark_terms(live: Vec<bool>, ts: &Vec<CoreTerm>) -> Vec<bool> {
    let mut live = live;
    let mut l: usize = 0;
    while l < ts.len() {
        live = mark_live(live, &ts[l]);
        l += 1;
    }
    live
}

/// From the last definition down: a live definition marks the definitions it refers to as live,
/// any other one becomes the constant zero of its width (`dw`).
fn dce(live: Vec<bool>, dw: &Vec<usize>, defs: Vec<CoreTerm>) -> Vec<CoreTerm> {
    let mut live = live;
    let mut defs = defs;
    let mut d: usize = defs.len();
    while d > 0 {
        d -= 1;
        if live[d] {
            live = mark_live(live, &defs[d]);
        } else {
            defs[d] = CoreTerm::Const(vec![false; dw[d]]);
        }
    }
    defs
}

fn copy_terms(ts: &Vec<CoreTerm>) -> Vec<CoreTerm> {
    let mut r: Vec<CoreTerm> = Vec::new();
    let mut a: usize = 0;
    while a < ts.len() {
        r.push(copy_term(&ts[a]));
        a += 1;
    }
    r
}

/// The problem with the free definitions rewritten and the unreachable ones replaced by
/// constants, the kinds and the marks of the definitions.
pub fn elim(q: &CoreProblem) -> (CoreProblem, Vec<usize>, Vec<usize>) {
    let n = q.defs.len();
    let (vc, rc) = count_terms(vec![0; q.widths.len()], vec![0; n], &q.defs);
    let (vc, rc) = count_terms(vc, rc, &q.asserts);
    let (dw, kind, mark, defs) = analyse(q, &vc, &rc);
    let live = mark_terms(vec![false; n], &q.asserts);
    let defs = dce(live, &dw, defs);
    (CoreProblem { widths: q.widths.clone(), defs, asserts: copy_terms(&q.asserts) }, kind, mark)
}

/// The constant 1 of width `w` (0 if `w` is 0).
fn bits_one(w: usize) -> Vec<bool> {
    let mut r = vec![false; w];
    if w > 0 {
        r[0] = true;
    }
    r
}

/// The operand that the definition `t` of kind `k` (2, 3 or 4) consumes, and the value it must
/// take for `t` to have the value `v`, given the values `m` of the variables and `dv` of the
/// definitions the other operands refer to, and the widths (the lengths of `dv2`) of all
/// definitions.
fn invert(t: &CoreTerm, k: usize, v: &Vec<bool>, m: &Vec<Vec<bool>>, dv: &Vec<Vec<bool>>, dv2: &Vec<Vec<bool>>) -> (usize, Vec<bool>) {
    let n = dv2.len();
    match t {
        CoreTerm::Not(a) => (ref_index(a, n), bits_not(v)),
        CoreTerm::Extract(hi, lo, a) => {
            let ia = ref_index(a, n);
            let w = dv2[ia].len();
            let low = bits_concat(v, &vec![false; *lo]);
            (ia, bits_concat(&vec![false; w - 1 - *hi], &low))
        }
        CoreTerm::Bin(op, a, b) => {
            let ic = if k == 3 { ref_index(b, n) } else { ref_index(a, n) };
            let o = if k == 3 { eval_term(m, dv, a) } else { eval_term(m, dv, b) };
            match op {
                BinOp::Add => {
                    let (s, _) = bits_add(v, &bits_not(&o), true);
                    (ic, s)
                }
                BinOp::Xor => (ic, bits_bitwise(op, v, &o)),
                BinOp::Eq => {
                    if v[0] {
                        (ic, o)
                    } else {
                        (ic, bits_not(&o))
                    }
                }
                _ => (ic, v.clone()),
            }
        }
        CoreTerm::Ite(c, a, _) => {
            let ia = ref_index(a, n);
            let mut r = Vec::new();
            r.push(bits_eq(v, &dv[ia]));
            (ref_index(c, n), r)
        }
        _ => (n, v.clone()),
    }
}

/// The index of the variable of `Var(i)`; 0 for any other term.
fn var_index(t: &CoreTerm) -> usize {
    match t {
        CoreTerm::Var(i) => *i,
        _ => 0,
    }
}

/// Gives the free definition `k` the value `v`: down the chain of consumed operands from `k`,
/// each definition gets the value that gives its parent its value, and the variable at the
/// bottom gets the value of its definition.
fn settle(defs: &Vec<CoreTerm>, kind: &Vec<usize>, dv2: &Vec<Vec<bool>>, dv: Vec<Vec<bool>>, m: Vec<Vec<bool>>, k: usize, v: Vec<bool>) -> (Vec<Vec<bool>>, Vec<Vec<bool>>) {
    let mut dv = dv;
    let mut m = m;
    let mut j = k;
    let mut v = v;
    let mut i: usize = 0;
    while i <= k {
        dv[j] = v.clone();
        if kind[j] == 1 {
            m[var_index(&defs[j])] = v;
            return (dv, m);
        }
        let (a, va) = invert(&defs[j], kind[j], &v, &m, &dv, dv2);
        j = a;
        v = va;
        i += 1;
    }
    (dv, m)
}

/// A model of `q` from a model `m2` of its elimination `q2` (with the kinds and marks returned by
/// `elim`): the free definitions that are not consumed take their values in `q2` (1 for the second
/// operands of kind 4), which are pushed down to their variables; the other variables keep their
/// values.
pub fn reconstruct(q: &CoreProblem, kind: &Vec<usize>, mark: &Vec<usize>, q2: &CoreProblem, m2: &Vec<Vec<bool>>) -> Vec<Vec<bool>> {
    let dv2 = eval_defs(q2, m2);
    let mut m = m2.clone();
    let mut dv: Vec<Vec<bool>> = Vec::new();
    let mut k: usize = 0;
    while k < q.defs.len() {
        if mark[k] == 1 {
            dv.push(Vec::new());
        } else if kind[k] == 0 {
            let v = eval_term(&m, &dv, &q.defs[k]);
            dv.push(v);
        } else {
            dv.push(Vec::new());
            let v = if mark[k] == 2 { bits_one(dv2[k].len()) } else { dv2[k].clone() };
            let (dv1, m1) = settle(&q.defs, kind, &dv2, dv, m, k, v);
            dv = dv1;
            m = m1;
        }
        k += 1;
    }
    m
}

// ---------------------------------------------------------------------------------------------
// Word-level normalization. The definitions are rebuilt in order with sharing (a definition equal
// to an earlier one, up to the order of the operands of a commutative operator, is replaced by
// it) and a few rewrites: `x = x` is 1, `x + ~x` is all ones, `x * ones` is `-x`, products of
// definitions are flattened and their factors sorted, the operands of a commutative operator are
// sorted. A variable `v` with an assertion `v = t` is replaced by `t` in the definitions after `t`
// other than the one of that assertion; the assertion itself is kept. The variables and their
// widths stay the same, and the new problem has the same models as the old one.
//
// The earlier definitions are found by a hash of the term into a fixed number of buckets, each a
// list of definitions through `next` (ending in `usize::MAX`), as the watch lists; a definition
// is shared only if it is equal (`norm_eq`) to the new one, so the hash does not matter for the
// result being correct.

fn op_code(op: &BinOp) -> usize {
    match op {
        BinOp::And => 0,
        BinOp::Or => 1,
        BinOp::Xor => 2,
        BinOp::Add => 3,
        BinOp::Mul => 4,
        BinOp::Udiv => 5,
        BinOp::Urem => 6,
        BinOp::Shl => 7,
        BinOp::Lshr => 8,
        BinOp::Concat => 9,
        BinOp::Eq => 10,
        BinOp::Ult => 11,
    }
}

fn commutative(op: &BinOp) -> bool {
    op_code(op) <= 4 || op_code(op) == 10
}

/// Whether the bit lists `a` and `b` are equal.
fn same_bits(a: &Vec<bool>, b: &Vec<bool>) -> bool {
    let mut r = a.len() == b.len();
    let mut i: usize = 0;
    while r && i < a.len() {
        if a[i] != b[i] {
            r = false;
        }
        i += 1;
    }
    r
}

/// Whether `a` and `b` are the same term.
fn term_eq(a: &CoreTerm, b: &CoreTerm) -> bool {
    match a {
        CoreTerm::Const(x) => match b {
            CoreTerm::Const(y) => same_bits(x, y),
            _ => false,
        },
        CoreTerm::Var(i) => match b {
            CoreTerm::Var(j) => *i == *j,
            _ => false,
        },
        CoreTerm::Ref(i) => match b {
            CoreTerm::Ref(j) => *i == *j,
            _ => false,
        },
        CoreTerm::Not(x) => match b {
            CoreTerm::Not(y) => term_eq(x, y),
            _ => false,
        },
        CoreTerm::Bin(o, x1, x2) => match b {
            CoreTerm::Bin(p, y1, y2) => op_code(o) == op_code(p) && term_eq(x1, y1) && term_eq(x2, y2),
            _ => false,
        },
        CoreTerm::Extract(h, l, x) => match b {
            CoreTerm::Extract(g, m, y) => *h == *g && *l == *m && term_eq(x, y),
            _ => false,
        },
        CoreTerm::Ite(c, x1, x2) => match b {
            CoreTerm::Ite(d, y1, y2) => term_eq(c, d) && term_eq(x1, y1) && term_eq(x2, y2),
            _ => false,
        },
    }
}

/// Whether `a` and `b` are the same term up to the order of the operands of the commutative
/// operator at the top.
fn norm_eq(a: &CoreTerm, b: &CoreTerm) -> bool {
    match a {
        CoreTerm::Bin(o, x1, x2) => match b {
            CoreTerm::Bin(p, y1, y2) => {
                op_code(o) == op_code(p)
                    && ((term_eq(x1, y1) && term_eq(x2, y2)) || (commutative(o) && term_eq(x1, y2) && term_eq(x2, y1)))
            }
            _ => false,
        },
        _ => term_eq(a, b),
    }
}

/// The prime modulus of the hash.
fn hash_mod() -> usize {
    2147483647
}

/// `h` (below the modulus) combined with `x`.
fn mix(h: usize, x: usize) -> usize {
    (h * 31 + x % hash_mod()) % hash_mod()
}

/// The hash of `t`, below the modulus; it does not depend on the order of the operands of a
/// commutative operator at the top.
fn term_hash(t: &CoreTerm) -> usize {
    match t {
        CoreTerm::Const(bits) => {
            let mut h: usize = 1;
            let mut i: usize = 0;
            while i < bits.len() {
                h = mix(h, if bits[i] { 1 } else { 0 });
                i += 1;
            }
            mix(h, 2)
        }
        CoreTerm::Var(i) => mix(3, *i),
        CoreTerm::Ref(i) => mix(4, *i),
        CoreTerm::Not(a) => mix(5, term_hash(a)),
        CoreTerm::Bin(op, a, b) => {
            let ha = term_hash(a);
            let hb = term_hash(b);
            if commutative(op) {
                mix(mix(6, op_code(op)), (ha + hb) % hash_mod())
            } else {
                mix(mix(mix(7, op_code(op)), ha), hb)
            }
        }
        CoreTerm::Extract(hi, lo, a) => mix(mix(mix(8, *hi), *lo), term_hash(a)),
        CoreTerm::Ite(c, a, b) => mix(mix(mix(9, term_hash(c)), term_hash(a)), term_hash(b)),
    }
}

/// `t` with every reference `Ref(i)` replaced by `Ref(map[i])`.
fn remap(t: &CoreTerm, map: &Vec<usize>) -> CoreTerm {
    match t {
        CoreTerm::Const(bits) => CoreTerm::Const(bits.clone()),
        CoreTerm::Var(i) => CoreTerm::Var(*i),
        CoreTerm::Ref(i) => CoreTerm::Ref(map[*i]),
        CoreTerm::Not(a) => cnot(remap(a, map)),
        CoreTerm::Bin(op, a, b) => cbin(copy_op(op), remap(a, map), remap(b, map)),
        CoreTerm::Extract(hi, lo, a) => cextract(*hi, *lo, remap(a, map)),
        CoreTerm::Ite(c, a, b) => cite(remap(c, map), remap(a, map), remap(b, map)),
    }
}

/// The index of the variable of `Var(i)`; `usize::MAX` for any other term.
fn var_of(t: &CoreTerm) -> usize {
    match t {
        CoreTerm::Var(i) => *i,
        _ => usize::MAX,
    }
}

/// Whether every bit is 1.
fn all_ones(bits: &Vec<bool>) -> bool {
    let mut r = true;
    let mut i: usize = 0;
    while i < bits.len() {
        if !bits[i] {
            r = false;
        }
        i += 1;
    }
    r
}

/// Whether `t` is a constant of ones, or refers to a definition that is one.
fn is_ones(defs: &Vec<CoreTerm>, t: &CoreTerm) -> bool {
    match t {
        CoreTerm::Const(bits) => all_ones(bits),
        CoreTerm::Ref(k) => match &defs[*k] {
            CoreTerm::Const(bits) => all_ones(bits),
            _ => false,
        },
        _ => false,
    }
}

/// `x` if `t` refers to a definition `Not(Ref(x))`; `usize::MAX` otherwise.
fn not_of(defs: &Vec<CoreTerm>, t: &CoreTerm) -> usize {
    match t {
        CoreTerm::Ref(k) => match &defs[*k] {
            CoreTerm::Not(a) => ref_index(a, usize::MAX),
            _ => usize::MAX,
        },
        _ => usize::MAX,
    }
}

/// `out` with the factors of the product that the definition `k` stands for (definitions that
/// are not a product of two definitions), and whether there are at most `cap` of them in all.
fn factors(defs: &Vec<CoreTerm>, k: usize, out: Vec<usize>, cap: usize) -> (Vec<usize>, bool) {
    let mut out = out;
    if out.len() > cap {
        return (out, false);
    }
    let mut x = usize::MAX;
    let mut y = usize::MAX;
    match &defs[k] {
        CoreTerm::Bin(op, a, b) => {
            if op_code(op) == 4 {
                x = ref_index(a, usize::MAX);
                y = ref_index(b, usize::MAX);
            }
        }
        _ => {}
    }
    if x != usize::MAX && y != usize::MAX {
        let (o1, ok) = factors(defs, x, out, cap);
        if ok {
            factors(defs, y, o1, cap)
        } else {
            (o1, false)
        }
    } else {
        out.push(k);
        let ok = out.len() <= cap;
        (out, ok)
    }
}

/// The factors of the product `t` if it is one of two definitions, and whether there are at
/// most 16 of them.
fn product_factors(defs: &Vec<CoreTerm>, t: &CoreTerm) -> (Vec<usize>, bool) {
    match t {
        CoreTerm::Bin(op, a, b) => {
            let ka = ref_index(a, usize::MAX);
            let kb = ref_index(b, usize::MAX);
            if op_code(op) == 4 && ka != usize::MAX && kb != usize::MAX {
                let (f1, ok) = factors(defs, ka, Vec::new(), 16);
                if ok {
                    factors(defs, kb, f1, 16)
                } else {
                    (f1, false)
                }
            } else {
                (Vec::new(), false)
            }
        }
        _ => (Vec::new(), false),
    }
}

/// `v` sorted (insertion sort).
fn sort_usize(v: Vec<usize>) -> Vec<usize> {
    let mut v = v;
    let mut i: usize = 1;
    while i < v.len() {
        let x = v[i];
        let mut j = i;
        while j > 0 && v[j - 1] > x {
            v[j] = v[j - 1];
            j -= 1;
        }
        v[j] = x;
        i += 1;
    }
    v
}

/// `t` of width `w` (over the new definitions `defs`) with the rewrites that need no new
/// definition.
fn rewrite(defs: &Vec<CoreTerm>, t: &CoreTerm, w: usize) -> CoreTerm {
    match t {
        CoreTerm::Bin(op, a, b) => {
            let ka = ref_index(a, usize::MAX);
            let kb = ref_index(b, usize::MAX);
            let c = op_code(op);
            if c == 10 && term_eq(a, b) {
                CoreTerm::Const(vec![true; 1])
            } else if c == 3 && ((ka != usize::MAX && not_of(defs, b) == ka) || (kb != usize::MAX && not_of(defs, a) == kb)) {
                CoreTerm::Const(vec![true; w])
            } else if c == 4 && w > 0 && ka != usize::MAX && is_ones(defs, b) {
                cneg(ka, w)
            } else if c == 4 && w > 0 && kb != usize::MAX && is_ones(defs, a) {
                cneg(kb, w)
            } else {
                copy_term(t)
            }
        }
        _ => copy_term(t),
    }
}

/// The first definition in the list from `k` on (through `next`) of width `w` equal to `t`;
/// `usize::MAX` if there is none.
fn find_def(defs: &Vec<CoreTerm>, widths: &Vec<usize>, next: &Vec<usize>, k: usize, t: &CoreTerm, w: usize) -> usize {
    let mut k = k;
    let mut r = usize::MAX;
    while k != usize::MAX && r == usize::MAX {
        if widths[k] == w && norm_eq(&defs[k], t) {
            r = k;
        } else {
            k = next[k];
        }
    }
    r
}

/// The definition of `t` of width `w`: `k` if `t` is `Ref(k)`, an earlier equal one, or a new
/// one, added to its bucket.
fn mk_raw(defs: Vec<CoreTerm>, widths: Vec<usize>, head: Vec<usize>, next: Vec<usize>, t: CoreTerm, w: usize) -> (Vec<CoreTerm>, Vec<usize>, Vec<usize>, Vec<usize>, usize) {
    let r = ref_index(&t, usize::MAX);
    if r != usize::MAX {
        return (defs, widths, head, next, r);
    }
    let h = term_hash(&t) % head.len();
    let f = find_def(&defs, &widths, &next, head[h], &t, w);
    if f != usize::MAX {
        return (defs, widths, head, next, f);
    }
    let mut defs = defs;
    let mut widths = widths;
    let mut head = head;
    let mut next = next;
    let k = defs.len();
    next.push(head[h]);
    head[h] = k;
    defs.push(t);
    widths.push(w);
    (defs, widths, head, next, k)
}

/// The definition of the term `t` of width `w` (over the new definitions), rewritten; a product
/// of more than two factors becomes the product of its sorted factors, from the left.
fn mk(defs: Vec<CoreTerm>, widths: Vec<usize>, head: Vec<usize>, next: Vec<usize>, t: &CoreTerm, w: usize) -> (Vec<CoreTerm>, Vec<usize>, Vec<usize>, Vec<usize>, usize) {
    let r = rewrite(&defs, t, w);
    let (fs, ok) = product_factors(&defs, &r);
    if ok && fs.len() > 2 {
        let fs = sort_usize(fs);
        let mut defs = defs;
        let mut widths = widths;
        let mut head = head;
        let mut next = next;
        let mut acc = fs[0];
        let mut i: usize = 1;
        while i < fs.len() {
            let (d1, w1, h1, n1, k) = mk_raw(defs, widths, head, next, cbin(BinOp::Mul, cref(acc), cref(fs[i])), w);
            defs = d1;
            widths = w1;
            head = h1;
            next = n1;
            acc = k;
            i += 1;
        }
        (defs, widths, head, next, acc)
    } else {
        mk_raw(defs, widths, head, next, r, w)
    }
}

/// The widths of the definitions of `q`.
fn def_widths(q: &CoreProblem) -> Vec<usize> {
    let mut dw: Vec<usize> = Vec::new();
    let mut j: usize = 0;
    while j < q.defs.len() {
        let w = term_width(&q.widths, &dw, &q.defs[j]);
        dw.push(w);
        j += 1;
    }
    dw
}

/// The substitution of `sb`, `ss` with `v := o` (by the definition `s`, `Var(v)`) if `s` is a
/// variable `v` without one yet and `o` is not `Var(v)`; and whether it was added.
fn add_sub(defs: &Vec<CoreTerm>, sb: Vec<usize>, ss: Vec<usize>, s: usize, o: usize) -> (Vec<usize>, Vec<usize>, bool) {
    let mut sb = sb;
    let mut ss = ss;
    let v = var_of(&defs[s]);
    if v != usize::MAX && sb[v] == usize::MAX && var_of(&defs[o]) != v {
        sb[v] = o;
        ss[v] = s;
        (sb, ss, true)
    } else {
        (sb, ss, false)
    }
}

/// The substitution of the assertions `v = t` of `q`: for a variable `v`, `sb[v]` is the
/// definition `t` and `ss[v]` the definition `Var(v)` of the first such assertion; `usize::MAX`
/// if there is none.
fn substitution(q: &CoreProblem) -> (Vec<usize>, Vec<usize>) {
    let mut sb: Vec<usize> = vec![usize::MAX; q.widths.len()];
    let mut ss: Vec<usize> = vec![usize::MAX; q.widths.len()];
    let mut i: usize = 0;
    while i < q.asserts.len() {
        let k = ref_index(&q.asserts[i], usize::MAX);
        let mut x = usize::MAX;
        let mut y = usize::MAX;
        if k != usize::MAX {
            match &q.defs[k] {
                CoreTerm::Bin(op, a, b) => {
                    if op_code(op) == 10 {
                        x = ref_index(a, usize::MAX);
                        y = ref_index(b, usize::MAX);
                    }
                }
                _ => {}
            }
        }
        if x != usize::MAX && y != usize::MAX {
            let (s1, t1, done) = add_sub(&q.defs, sb, ss, x, y);
            if done {
                sb = s1;
                ss = t1;
            } else {
                let (s2, t2, _) = add_sub(&q.defs, s1, t1, y, x);
                sb = s2;
                ss = t2;
            }
        }
        i += 1;
    }
    (sb, ss)
}

/// The normalization of `q`.
pub fn normalize(q: &CoreProblem) -> CoreProblem {
    let dw = def_widths(q);
    let (sb, ss) = substitution(q);
    let mut defs: Vec<CoreTerm> = Vec::new();
    let mut widths: Vec<usize> = Vec::new();
    let mut head: Vec<usize> = vec![usize::MAX; 2 * q.defs.len() + 1];
    let mut next: Vec<usize> = Vec::new();
    let mut map: Vec<usize> = Vec::new();
    let mut j: usize = 0;
    while j < q.defs.len() {
        let v = var_of(&q.defs[j]);
        if v != usize::MAX && sb[v] < j && ss[v] != j {
            let m = map[sb[v]];
            map.push(m);
        } else {
            let t = remap(&q.defs[j], &map);
            let (d1, w1, h1, n1, k) = mk(defs, widths, head, next, &t, dw[j]);
            defs = d1;
            widths = w1;
            head = h1;
            next = n1;
            map.push(k);
        }
        j += 1;
    }
    let mut asserts: Vec<CoreTerm> = Vec::new();
    let mut i: usize = 0;
    while i < q.asserts.len() {
        asserts.push(remap(&q.asserts[i], &map));
        i += 1;
    }
    CoreProblem { widths: q.widths.clone(), defs, asserts }
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
// `size_bound` (spec/QFBV_Spec.thy) is below 2^64, and the translation indexes its definitions
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

/// The least `i` with `n <= 2^i` (at most 64).
fn stages(n: usize) -> usize {
    let mut i: usize = 0;
    let mut p: usize = 1;
    while p < n && i < 64 {
        p = sat_mul(p, 2);
        i += 1;
    }
    i
}

/// A bound on the CNF variables and clauses that blasting the rewriting of the binary operator
/// `op` on operands of width `w` adds (`ebin` of the specification).
fn bin_cost(op: &Op, w: usize) -> usize {
    match op {
        Op::Mul | Op::Udiv | Op::Urem | Op::Sdiv | Op::Srem | Op::Smod => {
            sat_add(sat_add(sat_mul(sat_mul(76, w), w), sat_mul(300, w)), 20)
        }
        Op::Shl | Op::Lshr | Op::Ashr => sat_add(sat_mul(sat_mul(10, w), stages(w)), sat_mul(30, w)),
        _ => sat_add(sat_mul(30, w), 20),
    }
}

/// The width of `t` and its cost: the sum over its subterms of `4 * (width + 1)` and of the
/// CNF bound of the node (`width`, `lweight` and `ecount` of the specification), for the widths
/// `ws` of the variables and `ds` of the definitions.
fn term_size(ws: &Vec<usize>, ds: &Vec<usize>, t: &Term) -> (usize, usize) {
    let (w, g) = match t {
        Term::Const(bs) => (bs.len(), 0),
        Term::Var(i) => (ws[*i], 0),
        Term::Ref(i) => (ds[*i], 0),
        Term::Not(a) => term_size(ws, ds, a),
        Term::Neg(a) => {
            let (wa, ga) = term_size(ws, ds, a);
            (wa, sat_add(sat_mul(15, wa), ga))
        }
        Term::Bin(op, a, b) => {
            let (wa, ga) = term_size(ws, ds, a);
            let (wb, gb) = term_size(ws, ds, b);
            (op_width(op, wa, wb), sat_add(bin_cost(op, wa), sat_add(ga, gb)))
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
            (sat_add(wa, *i), sat_add(sat_mul(5, *i), ga))
        }
        Term::RotateLeft(_, a) => term_size(ws, ds, a),
        Term::RotateRight(_, a) => term_size(ws, ds, a),
        Term::Ite(c, a, b) => {
            let (_, gc) = term_size(ws, ds, c);
            let (wa, ga) = term_size(ws, ds, a);
            let (_, gb) = term_size(ws, ds, b);
            (wa, sat_add(sat_mul(5, wa), sat_add(gc, sat_add(ga, gb))))
        }
    };
    (w, sat_add(sat_mul(4, sat_add(w, 1)), g))
}

/// Whether the `ovf_bound` of `q` is below 2^63 (`sizes_ok` of the specification): then no
/// counter of the solver overflows.
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
    sat_mul(4, n) < cap()
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
