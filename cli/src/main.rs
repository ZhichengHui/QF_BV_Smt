//! The solver binary: the shared SMT-LIB front end (`frontend/`, not verified) with this
//! solver's `check_sat` (`core/`, verified). Usage: `qfbv FILE.smt2`, or the script on standard
//! input.

smtlib::bridge!(qfbv);

fn solve(p: &smtlib::SmtProblem) -> smtlib::SmtAnswer {
    let t = qfbv::prof::rep("parse", *qfbv::prof::START.get().unwrap());
    let c = problem_to_core(p);
    let t = qfbv::prof::rep("bridge", t);
    let r = answer_from_core(qfbv::check_sat(&c));
    qfbv::prof::rep("solve_total", t);
    qfbv::prof::rep("total_to_answer", *qfbv::prof::START.get().unwrap());
    r
}

fn main() {
    let _ = qfbv::prof::START.set(qfbv::prof::now());
    smtlib::cli_main(solve)
}
