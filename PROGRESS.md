# Progress

The state and milestones of this repository, kept up to date by summarize sessions (see `PLAN.md`).
Per-session details are in `progress/`.

## Current state

As of main b60eaf1 (2026-11-19).

- Solver (`solve` in `core/src/lib.rs`): rewriting into a core language of fifteen operations
  (`lower_problem`); bit-blasting into CNF (`encode`) with Tseitin gates simplified on constant and
  same-variable inputs; an iterative DPLL over a trail (`dpll`) with two-watched-literal unit
  propagation (`watch_init`, `wpropagate`), chronological backtracking, no clause learning and no
  decision heuristic; returns a model or `Unsat`.
- Verified but not yet used by `solve`: a word-level evaluator of core terms (`eval_term`,
  `eval_defs`), and elimination of unconstrained definitions with model reconstruction (`elim`,
  `reconstruct`). Their functional models are proved correct (`proof/QFBV_Eval.thy`,
  `proof/QFBV_Elim.thy`); the contracts of the evaluator are proved, those of `elim`/`reconstruct`
  and the call in `solve` are in open PR #54.
- Verification: `QFBV_heap.check_sat_correct` is proved against `spec/`, with no `sorry`; input
  range `smt_in_range`: size at most 2^30, widths at most 2^18, multiplication and division widths
  at most 2^12, distinct with at most 2^8 arguments. The watch lists are verified, not trusted: the
  watch-list invariant (`proof/QFBV_Watch.thy`) shows that a total assignment reached without a
  conflict satisfies every clause.
- Framework: the code translates with the AutoCorrode front end without placeholders.
- Benchmarks: active suite `QF_BV_Smt-2026-11-18` (101 instances, 40 sat, 61 unsat; 30 s, 8 GB,
  4 jobs). Target (Bitwuzla 0.10.0, #34): **101/101, PAR-2 52.2 s**. qfbv on main (#50, measured
  at the same time as main ee6a195): **49/101 (27 sat, 22 unsat), PAR-2 3125.4 s**; no wrong
  answers or bad models. With elimination called from `solve` (#51 with a local hook, PR #54):
  52/101, PAR-2 2944.3 s.
- Tests (auxiliary): `core/tests/` (`solve.rs`, `eval.rs`, `elim.rs`), `tools/fuzz.py` against z3.

## Limitations and open work

- The suite is far from saturated (directive #26): 49 of 101 against 101, PAR-2 about 60 times
  that of Bitwuzla. Most unsolved instances are in the families Sage2, bruttomesso, Noetzli, spear
  and UltimateAutomizer (per-family table at 44/101, comment on #26).
- The search has no conflict analysis, learned clauses, backjumping or decision heuristic; CDCL is
  issue #56. Its termination proof bounds the search loop by `3 ^ n` iterations (n CNF variables),
  which enters the fuel of the top-level theorem.
- Three `brummayerbiere4/unconstrained*` instances run out of memory on main while bit-blasting
  nested 1024-bit `bvudiv`; elimination (PR #54) solves them.
- Unused leftovers in the proofs: `pass_m` (`QFBV_Defs`), `unat64_lt`, and `dprop_post` /
  `dpll_prop_loop` / `dpll_facts` (`QFBV_DpllPure`).
- `isabelle-check` takes about 25 minutes; the Pool Server is slow on the large theories
  (`QFBV_Refine`, `QFBV_Elim`), and sessions work on task heaps or batch builds instead.

## Milestones

- 2026-11-12: the translation and the size checks verified
- 2026-11-14: the solver answers every problem of the fixed input range; top-level theorem
  `QFBV_heap.check_sat_correct`
- 2026-11-18: first benchmark suite, `QF_BV_Smt-2026-11-18`, active (#25, #30); qfbv 32/101,
  PAR-2 4181.1 s (#32); Bitwuzla 101/101, PAR-2 52.2 s (#41)
- 2026-11-18: simplifying Tseitin gates: 44/101, PAR-2 3427.3 s (#38)
- 2026-11-18: prism lists of generated functions in `spec/` follow the implementation (#39)
- 2026-11-18: iterative DPLL over a trail, no change on the suite (#40)
- 2026-11-19: verified word-level evaluator of core terms (#46)
- 2026-11-19: two-watched-literal propagation: 49/101, PAR-2 3126.2 s (#47); its watch-list
  invariant proved and the final full check dropped, same result (#50)
- 2026-11-19: elimination of unconstrained definitions and model reconstruction: code and proved
  functional models, not yet called by `solve` (#53)
