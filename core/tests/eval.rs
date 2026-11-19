//! Tests of the evaluator of core terms `eval_term` against machine arithmetic (widths up to 64),
//! and of its division on wide operands against the identity `a = q * b + r` with `r < b`.

use qfbv::*;

fn bits(v: u64, w: usize) -> Vec<bool> {
    (0..w).map(|i| i < 64 && (v >> i) & 1 == 1).collect()
}

fn num(bs: &[bool]) -> u64 {
    bs.iter().rev().fold(0u64, |a, &b| 2 * a + b as u64)
}

fn mask(w: usize) -> u64 {
    if w >= 64 { u64::MAX } else { (1u64 << w) - 1 }
}

fn bin(op: BinOp, a: CoreTerm, b: CoreTerm) -> CoreTerm {
    CoreTerm::Bin(op, Box::new(a), Box::new(b))
}

/// A small linear congruential generator, so that the test needs no crate.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0 ^ (self.0 >> 29)
    }
}

/// The expected value of `op` on `x`, `y` of width `w` (SMT-LIB semantics).
fn expected(op: &BinOp, x: u64, y: u64, w: usize) -> (u64, usize) {
    let m = mask(w);
    match op {
        BinOp::And => (x & y, w),
        BinOp::Or => (x | y, w),
        BinOp::Xor => (x ^ y, w),
        BinOp::Add => (x.wrapping_add(y) & m, w),
        BinOp::Mul => (x.wrapping_mul(y) & m, w),
        BinOp::Udiv => (if y == 0 { m } else { x / y }, w),
        BinOp::Urem => (if y == 0 { x } else { x % y }, w),
        BinOp::Shl => (if y >= w as u64 { 0 } else { (x << y) & m }, w),
        BinOp::Lshr => (if y >= w as u64 { 0 } else { x >> y }, w),
        BinOp::Concat => ((x << w) | y, 2 * w),
        BinOp::Eq => ((x == y) as u64, 1),
        BinOp::Ult => ((x < y) as u64, 1),
    }
}

fn ops() -> Vec<BinOp> {
    vec![
        BinOp::And,
        BinOp::Or,
        BinOp::Xor,
        BinOp::Add,
        BinOp::Mul,
        BinOp::Udiv,
        BinOp::Urem,
        BinOp::Shl,
        BinOp::Lshr,
        BinOp::Concat,
        BinOp::Eq,
        BinOp::Ult,
    ]
}

#[test]
fn binary_operators_match_machine_arithmetic() {
    let mut rng = Rng(42);
    for _ in 0..3000 {
        let w = 1 + (rng.next() % 64) as usize;
        let small = rng.next() % 4 == 0;
        let x = if small { rng.next() % 5 } else { rng.next() } & mask(w);
        let y = if small { rng.next() % 5 } else { rng.next() } & mask(w);
        let vars = vec![bits(x, w), bits(y, w)];
        for op in ops() {
            let concat = matches!(op, BinOp::Concat);
            if concat && w > 32 {
                continue;
            }
            let (e, ew) = expected(&op, x, y, w);
            let t = bin(op, CoreTerm::Var(0), CoreTerm::Var(1));
            let r = eval_term(&vars, &Vec::new(), &t);
            assert_eq!(r.len(), ew);
            assert_eq!(num(&r), e, "x = {x}, y = {y}, w = {w}");
        }
    }
}

#[test]
fn unary_terms_and_definitions() {
    // not, extract, ite and references through eval_defs.
    let p = CoreProblem {
        widths: vec![8, 1],
        defs: vec![
            CoreTerm::Not(Box::new(CoreTerm::Var(0))),
            CoreTerm::Extract(6, 2, Box::new(CoreTerm::Ref(0))),
            CoreTerm::Ite(Box::new(CoreTerm::Var(1)), Box::new(CoreTerm::Ref(1)), Box::new(CoreTerm::Const(bits(9, 5)))),
        ],
        asserts: Vec::new(),
    };
    for c in [false, true] {
        let m = vec![bits(0b1010_0110, 8), vec![c]];
        let d = eval_defs(&p, &m);
        assert_eq!(num(&d[0]), 0b0101_1001);
        assert_eq!(num(&d[1]), 0b10110);
        assert_eq!(num(&d[2]), if c { 0b10110 } else { 9 });
    }
}

#[test]
fn wide_division() {
    // 1024-bit operands: q * b + r = a and r < b, computed in twice the width.
    let mut rng = Rng(7);
    let w = 1024;
    for k in 0..6 {
        let a: Vec<bool> = (0..w).map(|_| rng.next() % 2 == 0).collect();
        let bw = if k < 3 { w } else { 40 };
        let b: Vec<bool> = (0..w).map(|i| i < bw && rng.next() % 2 == 0).collect();
        let vars = vec![a.clone(), b.clone()];
        let q = eval_term(&vars, &Vec::new(), &bin(BinOp::Udiv, CoreTerm::Var(0), CoreTerm::Var(1)));
        let r = eval_term(&vars, &Vec::new(), &bin(BinOp::Urem, CoreTerm::Var(0), CoreTerm::Var(1)));
        let ext = |v: &Vec<bool>| {
            let mut e = v.clone();
            e.extend(vec![false; w]);
            e
        };
        let wide = vec![ext(&q), ext(&b), ext(&r), ext(&a)];
        let t = bin(
            BinOp::Eq,
            bin(BinOp::Add, bin(BinOp::Mul, CoreTerm::Var(0), CoreTerm::Var(1)), CoreTerm::Var(2)),
            CoreTerm::Var(3),
        );
        assert_eq!(eval_term(&wide, &Vec::new(), &t), vec![true]);
        let lt = bin(BinOp::Ult, CoreTerm::Var(2), CoreTerm::Var(1));
        assert_eq!(eval_term(&wide, &Vec::new(), &lt), vec![true]);
    }
    // Division by zero.
    let a: Vec<bool> = (0..w).map(|i| i % 3 == 0).collect();
    let vars = vec![a.clone(), vec![false; w]];
    let q = eval_term(&vars, &Vec::new(), &bin(BinOp::Udiv, CoreTerm::Var(0), CoreTerm::Var(1)));
    let r = eval_term(&vars, &Vec::new(), &bin(BinOp::Urem, CoreTerm::Var(0), CoreTerm::Var(1)));
    assert_eq!(q, vec![true; w]);
    assert_eq!(r, a);
}
