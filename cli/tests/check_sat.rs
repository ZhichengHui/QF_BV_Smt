//! End-to-end tests: SMT-LIB scripts through the shared front end and this solver's `check_sat`.
//! Every `sat` answer's model is checked with the front end's reference evaluator
//! (`smtlib::semantics::check_model`), and every answer is compared with the expected one.

use smtlib::{SmtAnswer, SmtProblem};

smtlib::bridge!(qfbv);

/// Runs `src` and returns the answers of its `check-sat` commands ("sat", "unsat", "unknown").
fn answers(src: &str) -> Vec<&'static str> {
    let mut got = Vec::new();
    let mut solve = |p: &SmtProblem| -> SmtAnswer {
        let a = answer_from_core(qfbv::check_sat(&problem_to_core(p)));
        match &a {
            SmtAnswer::Sat(m) => {
                assert_eq!(smtlib::semantics::check_model(p, m), Ok(true), "bad model for {src}");
                got.push("sat");
            }
            SmtAnswer::Unsat => got.push("unsat"),
            SmtAnswer::Unknown => got.push("unknown"),
        }
        a
    };
    let mut out = Vec::new();
    smtlib::script::run(src.as_bytes(), &mut solve, &mut out).unwrap();
    got
}

#[test]
fn increment_is_never_identity() {
    let s = "(set-logic QF_BV)(declare-const x (_ BitVec 4))(assert (= (bvadd x #x1) x))(check-sat)";
    assert_eq!(answers(s), ["unsat"]);
}

#[test]
fn bvxor_is_left_associative() {
    let s = "(set-logic QF_BV)(declare-const s (_ BitVec 3))(declare-const t (_ BitVec 3))
             (declare-const u (_ BitVec 3))(assert (= (bvxor s t u) #b101))(assert (= s #b001))
             (assert (= t #b010))(check-sat)";
    assert_eq!(answers(s), ["sat"]);
}

#[test]
fn three_distinct_bits() {
    let s = "(set-logic QF_BV)(declare-const a (_ BitVec 1))(declare-const b (_ BitVec 1))
             (declare-const c (_ BitVec 1))(assert (distinct a b c))(check-sat)";
    assert_eq!(answers(s), ["unsat"]);
}

#[test]
fn define_fun_with_parameters() {
    let s = "(set-logic QF_BV)(define-fun double ((y (_ BitVec 8))) (_ BitVec 8) (bvadd y y))
             (declare-const x (_ BitVec 8))(assert (= (double x) #x0a))(check-sat)";
    assert_eq!(answers(s), ["sat"]);
}

#[test]
fn division_by_zero_is_all_ones() {
    let s = "(set-logic QF_BV)(declare-const x (_ BitVec 4))
             (assert (not (= (bvudiv x #x0) #xf)))(check-sat)";
    assert_eq!(answers(s), ["unsat"]);
}

#[test]
fn boolean_ite() {
    let s = "(set-logic QF_BV)(declare-const p Bool)(declare-const x (_ BitVec 2))
             (assert (= (ite p x #b11) #b01))(check-sat)";
    assert_eq!(answers(s), ["sat"]);
}
