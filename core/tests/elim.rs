//! Tests of the elimination of unconstrained definitions (`elim`, `reconstruct`) on random core
//! problems: for every assignment `m2` of the eliminated problem, the reconstructed assignment
//! gives every assertion of the problem the value it has in the eliminated problem under `m2`, and
//! the eliminated problem keeps the variables and the widths of the definitions.

use qfbv::*;

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0 ^ (self.0 >> 29)
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

fn rf(i: usize) -> Box<CoreTerm> {
    Box::new(CoreTerm::Ref(i))
}

/// A random well-sorted core problem whose variables mostly occur once, in the shapes that the
/// lowering produces (every operand a reference to a definition).
fn random_problem(r: &mut Rng) -> CoreProblem {
    let nv = 1 + r.below(8);
    let widths: Vec<usize> = (0..nv).map(|_| 1 + r.below(6)).collect();
    let mut defs: Vec<CoreTerm> = Vec::new();
    let mut dw: Vec<usize> = Vec::new();
    for i in 0..nv {
        defs.push(CoreTerm::Var(i));
        dw.push(widths[i]);
    }
    for _ in 0..3 + r.below(15) {
        let n = defs.len();
        let a = r.below(n);
        let w = dw[a];
        let same: Vec<usize> = (0..n).filter(|&j| dw[j] == w).collect();
        let b = same[r.below(same.len())];
        let (t, tw) = match r.below(13) {
            0 => (CoreTerm::Not(rf(a)), w),
            1 => {
                let hi = r.below(w);
                let lo = r.below(hi + 1);
                (CoreTerm::Extract(hi, lo, rf(a)), hi - lo + 1)
            }
            2 => (CoreTerm::Bin(BinOp::Add, rf(a), rf(b)), w),
            3 => (CoreTerm::Bin(BinOp::Xor, rf(a), rf(b)), w),
            4 => (CoreTerm::Bin(BinOp::Mul, rf(a), rf(b)), w),
            5 => (CoreTerm::Bin(BinOp::Udiv, rf(a), rf(b)), w),
            6 => (CoreTerm::Bin(BinOp::Eq, rf(a), rf(b)), 1),
            7 => (CoreTerm::Bin(BinOp::Ult, rf(a), rf(b)), 1),
            8 => (CoreTerm::Bin(BinOp::And, rf(a), rf(b)), w),
            9 => (CoreTerm::Var(r.below(nv)), widths[0]),
            10 => {
                let x = r.below(2) == 1;
                (CoreTerm::Const(vec![x]), 1)
            }
            11 => {
                let ones: Vec<usize> = (0..n).filter(|&j| dw[j] == 1).collect();
                if ones.len() >= 3 {
                    let c = ones[r.below(ones.len())];
                    let x = ones[r.below(ones.len())];
                    let y = ones[r.below(ones.len())];
                    (CoreTerm::Ite(rf(c), rf(x), rf(y)), 1)
                } else {
                    (CoreTerm::Not(rf(a)), w)
                }
            }
            _ => (CoreTerm::Bin(BinOp::Concat, rf(a), rf(b)), 2 * w),
        };
        // A variable term must have the width of its variable.
        let (t, tw) = match t {
            CoreTerm::Var(i) => (CoreTerm::Var(i), widths[i]),
            t => (t, tw),
        };
        defs.push(t);
        dw.push(tw);
    }
    // Width-1 constants of both values, so that `Ite` over them is eliminated.
    let n = defs.len();
    let ones: Vec<usize> = (0..n).filter(|&j| dw[j] == 1).collect();
    if ones.len() >= 1 {
        let c = ones[r.below(ones.len())];
        defs.push(CoreTerm::Const(vec![true]));
        defs.push(CoreTerm::Const(vec![false]));
        defs.push(CoreTerm::Ite(rf(c), rf(n), rf(n + 1)));
        dw.push(1);
        dw.push(1);
        dw.push(1);
    }
    let ones: Vec<usize> = (0..defs.len()).filter(|&j| dw[j] == 1).collect();
    let mut asserts = Vec::new();
    for _ in 0..1 + r.below(3) {
        if !ones.is_empty() {
            asserts.push(CoreTerm::Ref(ones[r.below(ones.len())]));
        }
    }
    CoreProblem { widths, defs, asserts }
}

#[test]
fn reconstruction_keeps_assertion_values() {
    let mut r = Rng(12345);
    let mut eliminated = 0;
    for _ in 0..3000 {
        let q = random_problem(&mut r);
        let (q2, kind, mark) = elim(&q);
        assert_eq!(q2.widths, q.widths);
        assert_eq!(q2.defs.len(), q.defs.len());
        assert_eq!(q2.asserts.len(), q.asserts.len());
        eliminated += kind.iter().filter(|&&k| k >= 2).count();
        for _ in 0..4 {
            let m2: Vec<Vec<bool>> = q.widths.iter().map(|&w| (0..w).map(|_| r.below(2) == 1).collect()).collect();
            let m = reconstruct(&q, &kind, &mark, &q2, &m2);
            let lens: Vec<usize> = m.iter().map(|v| v.len()).collect();
            assert_eq!(lens, q.widths);
            let d1 = eval_defs(&q, &m);
            let d2 = eval_defs(&q2, &m2);
            for j in 0..q.defs.len() {
                assert_eq!(d1[j].len(), d2[j].len(), "width of definition {}", j);
            }
            for t in &q.asserts {
                assert_eq!(eval_term(&m, &d1, t), eval_term(&m2, &d2, t));
            }
        }
    }
    assert!(eliminated > 1000, "only {} definitions eliminated", eliminated);
}
