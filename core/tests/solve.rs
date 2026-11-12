//! Tests of the core solver `solve` on problems of the extended language, built directly (without
//! the front end). Every `Sat` answer's assignment is checked by evaluating the assertions with
//! the independent evaluator below.

use bvsmt::*;

fn var(i: usize) -> Term {
    Term::Var(i)
}

fn cnst(v: u64, w: usize) -> Term {
    Term::Const((0..w).map(|i| (v >> i) & 1 == 1).collect())
}

fn bin(op: Op, a: Term, b: Term) -> Term {
    Term::Bin(op, Box::new(a), Box::new(b))
}

/// The value of `t` (least significant bit first, widths up to 64) under the assignment `m`.
fn eval(m: &[Vec<bool>], t: &Term) -> (u64, usize) {
    let num = |bs: &Vec<bool>| bs.iter().rev().fold(0u64, |a, &b| 2 * a + b as u64);
    match t {
        Term::Const(bs) => (num(bs), bs.len()),
        Term::Var(i) => (num(&m[*i]), m[*i].len()),
        Term::Not(a) => {
            let (x, w) = eval(m, a);
            (!x & mask(w), w)
        }
        Term::Bin(op, a, b) => {
            let (x, w) = eval(m, a);
            let (y, _) = eval(m, b);
            match op {
                Op::And => (x & y, w),
                Op::Or => (x | y, w),
                Op::Xor => (x ^ y, w),
                Op::Add => (x.wrapping_add(y) & mask(w), w),
                Op::Mul => (x.wrapping_mul(y) & mask(w), w),
                Op::Eq => ((x == y) as u64, 1),
                Op::Ult => ((x < y) as u64, 1),
                _ => panic!("operator not covered by this evaluator"),
            }
        }
        _ => panic!("term not covered by this evaluator"),
    }
}

fn mask(w: usize) -> u64 {
    if w >= 64 { u64::MAX } else { (1u64 << w) - 1 }
}

/// Solves `p`; for `Sat`, checks that the assignment has the declared widths and satisfies every
/// assertion. Returns whether the answer is `Sat`.
fn solve_checked(p: &Problem) -> bool {
    match solve(p) {
        Answer::Sat(m) => {
            assert_eq!(m.len(), p.widths.len());
            for (i, w) in p.widths.iter().enumerate() {
                assert_eq!(m[i].len(), *w);
            }
            for t in &p.asserts {
                assert_eq!(eval(&m, t), (1, 1));
            }
            true
        }
        Answer::Unsat => false,
    }
}

#[test]
fn sum_and_order() {
    // x + y = 5 and x < y over 4 bits: satisfiable.
    let p = Problem {
        widths: vec![4, 4],
        defs: Vec::new(),
        asserts: vec![bin(Op::Eq, bin(Op::Add, var(0), var(1)), cnst(5, 4)), bin(Op::Ult, var(0), var(1))],
    };
    assert!(solve_checked(&p));
}

#[test]
fn increment_is_never_identity() {
    let p = Problem { widths: vec![4], defs: Vec::new(), asserts: vec![bin(Op::Eq, bin(Op::Add, var(0), cnst(1, 4)), var(0))] };
    assert!(!solve_checked(&p));
}

#[test]
fn odd_square() {
    // x * x = 9 over 8 bits: satisfiable (x = 3).
    let p = Problem { widths: vec![8], defs: Vec::new(), asserts: vec![bin(Op::Eq, bin(Op::Mul, var(0), var(0)), cnst(9, 8))] };
    assert!(solve_checked(&p));
}

#[test]
fn xor_with_itself_is_zero() {
    // (x xor x) = 1 over 3 bits: unsatisfiable.
    let p = Problem { widths: vec![3], defs: Vec::new(), asserts: vec![bin(Op::Eq, bin(Op::Xor, var(0), var(0)), cnst(1, 3))] };
    assert!(!solve_checked(&p));
}
