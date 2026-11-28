use qfbv::*;
fn r(k: usize) -> CoreTerm { CoreTerm::Ref(k) }
fn mul(a: CoreTerm, b: CoreTerm) -> CoreTerm { CoreTerm::Bin(BinOp::Mul, Box::new(a), Box::new(b)) }
/// A chain of products whose sorted flattening shares no prefix: without a budget the products
/// grow 8x; with factor `f` the cost (all products of width 32) stays within `f` times.
#[test]
fn flat_budget() {
    let n = 16;
    let mut defs = Vec::new();
    for i in 0..n { defs.push(CoreTerm::Var(i)); }
    defs.push(mul(r(n - 2), r(n - 1)));
    for k in 3..=n { let prev = defs.len() - 1; defs.push(mul(r(n - k), r(prev))); }
    let last = defs.len() - 1;
    let q = CoreProblem { widths: vec![32; n], defs, asserts: vec![CoreTerm::Bin(BinOp::Eq, Box::new(r(last)), Box::new(r(0)))] };
    for f in [1usize, 2, 3, 1 << 62] {
        let q2 = normalize_k(&q, f);
        let muls = q2.defs.iter().filter(|t| matches!(t, CoreTerm::Bin(BinOp::Mul, _, _))).count();
        println!("f={} defs {} -> {}, muls {}", f, q.defs.len(), q2.defs.len(), muls);
        if f < 4 {
            assert!(muls <= f * (n - 1));
        } else {
            assert!(muls > 3 * (n - 1));
        }
    }
}
