//! The solver binary: the shared SMT-LIB front end (`frontend/`, not verified) with this
//! solver's `check_sat` (`core/`, verified). Usage: `bvsmt FILE.smt2`, or the script on standard
//! input.

smtlib::bridge!(bvsmt);

fn solve(p: &smtlib::SmtProblem) -> smtlib::SmtAnswer {
    answer_from_core(bvsmt::check_sat(&problem_to_core(p)))
}

fn main() {
    smtlib::cli_main(solve)
}
