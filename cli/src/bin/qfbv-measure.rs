//! Measures of SMT-LIB problems, as `spec/` defines them (`SMT_Semantics`: `smt_size`,
//! `smt_max_width`, `smt_max_mul_width`, `smt_max_distinct`, `smt_cost`). Not part of the solver:
//! it checks the input range (`smt_in_range` of `spec/QFBV_Spec.thy`) against benchmark sets.
//! Usage: `qfbv-measure FILE.smt2...`; prints, per `check-sat` of each file, one line
//! `FILE size max_width max_mul_width max_distinct cost` (numbers saturate at `u128::MAX`).

use smtlib::{SmtDef, SmtFun, SmtOp, SmtProblem, SmtSort, SmtTerm};

#[derive(Clone, Copy, PartialEq)]
enum S {
    Bool,
    Bv(usize),
    Other,
}

fn sort(s: &SmtSort) -> S {
    match s {
        SmtSort::Bool => S::Bool,
        SmtSort::BitVec(w) => S::Bv(*w),
        SmtSort::Uninterpreted(_) => S::Other,
    }
}

fn width(s: S) -> u128 {
    match s {
        S::Bv(w) => w as u128,
        _ => 0,
    }
}

/// `smt_tsort` for a well-sorted term (the front end checks sorts).
fn tsort(fs: &[SmtFun], ds: &[SmtDef], ps: &[SmtSort], t: &SmtTerm) -> S {
    match t {
        SmtTerm::BoolConst(_) => S::Bool,
        SmtTerm::BvConst(bs) => S::Bv(bs.len()),
        SmtTerm::Param(k) => sort(&ps[*k]),
        SmtTerm::Fun(f, _) => sort(&fs[*f].ret),
        SmtTerm::Def(d, _) => sort(&ds[*d].ret),
        SmtTerm::App(op, args) => {
            let a = |i: usize| tsort(fs, ds, ps, &args[i]);
            match op {
                SmtOp::Not | SmtOp::And | SmtOp::Or | SmtOp::Xor | SmtOp::Implies | SmtOp::Eq
                | SmtOp::Distinct | SmtOp::Bvult | SmtOp::Bvule | SmtOp::Bvugt | SmtOp::Bvuge
                | SmtOp::Bvslt | SmtOp::Bvsle | SmtOp::Bvsgt | SmtOp::Bvsge => S::Bool,
                SmtOp::Ite => a(1),
                SmtOp::Concat => S::Bv((width(a(0)) + width(a(1))) as usize),
                SmtOp::Extract(i, j) => S::Bv(i - j + 1),
                SmtOp::Bvcomp => S::Bv(1),
                SmtOp::Repeat(i) => S::Bv(width(a(0)) as usize * i),
                SmtOp::ZeroExtend(i) | SmtOp::SignExtend(i) => S::Bv(width(a(0)) as usize + i),
                _ => a(0),
            }
        }
    }
}

fn args(t: &SmtTerm) -> &[SmtTerm] {
    match t {
        SmtTerm::Fun(_, a) | SmtTerm::Def(_, a) | SmtTerm::App(_, a) => a,
        _ => &[],
    }
}

fn mul_div(t: &SmtTerm) -> bool {
    matches!(
        t,
        SmtTerm::App(SmtOp::Bvmul | SmtOp::Bvudiv | SmtOp::Bvurem | SmtOp::Bvsdiv | SmtOp::Bvsrem | SmtOp::Bvsmod, _)
    )
}

/// `smt_ncost`: the cost of one node.
fn ncost(fs: &[SmtFun], ds: &[SmtDef], ps: &[SmtSort], t: &SmtTerm) -> u128 {
    let a = args(t);
    let w = a.iter().map(|x| width(tsort(fs, ds, ps, x))).fold(width(tsort(fs, ds, ps, t)), u128::max).max(1);
    let c = if mul_div(t) {
        w * w
    } else if matches!(t, SmtTerm::App(SmtOp::Distinct, _)) {
        a.len() as u128 * w
    } else {
        w
    };
    (1 + a.len() as u128) * c
}

struct M<'a> {
    fs: &'a [SmtFun],
    ds: &'a [SmtDef],
    /// Nodes and cost of the body of each definition with parameters (`None`: not yet computed).
    body: Vec<Option<(u128, u128)>>,
    max_width: u128,
    max_mul: u128,
    max_distinct: u128,
}

impl M<'_> {
    /// `smt_nodes (take n ds) t` and `smt_cost fs (take n ds) ps t`.
    fn nodes_cost(&mut self, n: usize, ps: &[SmtSort], t: &SmtTerm) -> (u128, u128) {
        let (fs, ds) = (self.fs, &self.ds[..n]);
        let mut nodes: u128 = 1;
        let mut cost = ncost(fs, ds, ps, t);
        for a in args(t) {
            let (x, y) = self.nodes_cost(n, ps, a);
            nodes = nodes.saturating_add(x);
            cost = cost.saturating_add(y);
        }
        if let SmtTerm::Def(d, _) = t {
            if *d < n && !self.ds[*d].params.is_empty() {
                let (x, y) = self.def_body(*d);
                nodes = nodes.saturating_add(x);
                cost = cost.saturating_add(y);
            }
        }
        (nodes, cost)
    }

    fn def_body(&mut self, d: usize) -> (u128, u128) {
        if let Some(r) = self.body[d] {
            return r;
        }
        let def = &self.ds[d];
        let r = self.nodes_cost(d, &def.params, &def.body);
        self.body[d] = Some(r);
        r
    }

    /// The widths of the subterms (`smt_term_widths`) and of `distinct`.
    fn widths(&mut self, n: usize, ps: &[SmtSort], t: &SmtTerm) {
        let w = width(tsort(self.fs, &self.ds[..n], ps, t));
        self.max_width = self.max_width.max(w);
        if mul_div(t) {
            self.max_mul = self.max_mul.max(w);
        }
        if let SmtTerm::App(SmtOp::Distinct, a) = t {
            self.max_distinct = self.max_distinct.max(a.len() as u128);
        }
        for a in args(t) {
            self.widths(n, ps, a);
        }
    }
}

fn measure(p: &SmtProblem) -> [u128; 5] {
    let mut m = M { fs: &p.funs, ds: &p.defs, body: vec![None; p.defs.len()], max_width: 0, max_mul: 0, max_distinct: 0 };
    for f in &p.funs {
        for s in f.args.iter().chain([&f.ret]) {
            m.max_width = m.max_width.max(width(sort(s)));
        }
    }
    let mut size = (p.funs.len() + p.defs.len() + p.asserts.len()) as u128;
    let mut cost: u128 = 0;
    for (d, def) in p.defs.iter().enumerate() {
        for s in def.params.iter().chain([&def.ret]) {
            m.max_width = m.max_width.max(width(sort(s)));
        }
        m.widths(d, &def.params, &def.body);
        if def.params.is_empty() {
            let (x, y) = m.nodes_cost(d, &[], &def.body);
            size = size.saturating_add(x);
            cost = cost.saturating_add(y);
        }
    }
    for a in &p.asserts {
        m.widths(p.defs.len(), &[], a);
        let (x, y) = m.nodes_cost(p.defs.len(), &[], a);
        size = size.saturating_add(x);
        cost = cost.saturating_add(y);
    }
    [size, m.max_width, m.max_mul, m.max_distinct, cost]
}

fn main() {
    let files: Vec<String> = std::env::args().skip(1).collect();
    let worker = std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(move || {
            for f in files {
                let src = match std::fs::read(&f) {
                    Ok(s) => s,
                    Err(e) => {
                        println!("{f} error {e}");
                        continue;
                    }
                };
                let mut rows = Vec::new();
                let mut solve = |p: &SmtProblem| {
                    rows.push(measure(p));
                    smtlib::SmtAnswer::Unknown
                };
                let mut out = Vec::new();
                let _ = smtlib::script::run(&src, &mut solve, &mut out);
                if rows.is_empty() {
                    let msg = String::from_utf8_lossy(&out).replace('\n', " ");
                    println!("{f} none {}", msg.trim());
                }
                for r in rows {
                    println!("{f} {} {} {} {} {}", r[0], r[1], r[2], r[3], r[4]);
                }
            }
        })
        .expect("spawn the measuring thread");
    worker.join().expect("measuring thread");
}
