# Progress

The state and milestones of this repository, kept up to date by summarize sessions (see `PLAN.md`).
Per-session details are in `progress/`.

## Current state

- Solver: rewriting into a core language of fifteen operations, bit-blasting into CNF (Tseitin), DPLL with unit propagation and chronological backtracking; returns a model or `Unsat`.
- Verification: `QFBV_heap.check_sat_correct` is proved against `spec/`, with no `sorry`; input range `smt_in_range`: size at most 2^30, widths at most 2^18, multiplication and division widths at most 2^12, distinct with at most 2^8 arguments.
- Framework: the code translates with the AutoCorrode front end without placeholders.
- Benchmarks: none yet; the benchmark measurement is being re-established.
- Tests (auxiliary): `core/tests/`, `tools/fuzz.py` against z3.

## Milestones

- 2026-11-12: the translation and the size checks verified
- 2026-11-14: the solver answers every problem of the fixed input range; top-level theorem `QFBV_heap.check_sat_correct`
