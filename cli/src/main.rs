//! The solver binary: the shared SMT-LIB front end (`frontend/`, not verified) with this
//! solver's `check_sat` (`core/`, verified). Usage: `qfbv FILE.smt2`, or the script on standard
//! input.

smtlib::bridge!(qfbv);

fn solve(p: &smtlib::SmtProblem) -> smtlib::SmtAnswer {
    if std::env::var("QFBV_GROWTH").is_ok() {
        // Debug (scratch only): growth of normalization, budget factors 1 (no flattening), 2, 3 and none.
        let c = problem_to_core(p);
        for f in [1usize, 2, 3, 1usize << 62] {
            println!("growth f={} {:?}", f, qfbv::norm_growth(&c, f));
        }
        std::process::exit(0);
    }
    answer_from_core(qfbv::check_sat(&problem_to_core(p)))
}

fn main() {
    smtlib::cli_main(solve)
}
