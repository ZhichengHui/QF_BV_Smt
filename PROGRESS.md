# Progress

The state and milestones of this repository, kept up to date by summarize sessions (see `PLAN.md`).
Per-session details are in `progress/`; what went wrong before is in `LESSONS.md`.

## Current state

As of main 51cde83 (2026-11-27). Three levels must be kept apart: what `solve` on main does
(verified end to end), what is proved only as a pure model (not yet connected to the Rust code),
and what is only measured, on unmerged scratch branches.

### On main: the verified solver

- `solve` (`core/src/lib.rs`): rewriting into a core language of fifteen operations
  (`lower_problem`); elimination of unconstrained definitions (`elim`), with model reconstruction
  (`reconstruct`) of a model of the reduced problem (#54); bit-blasting into CNF (`encode`) with
  Tseitin gates simplified on constant and same-variable inputs; an iterative DPLL over a trail
  (`dpll`) with two-watched-literal unit propagation and chronological backtracking. Since #61 the
  propagation functions also return the reason of each propagated literal and the index of the
  clause in conflict, but `dpll` does not use them: there is still no conflict analysis, no learned
  clause, no backjump, no decision heuristic and no restart. No word-level normalization.
- Verification: `QFBV_heap.check_sat_correct` is proved against `spec/` with no `sorry`
  (`grep -rnwE 'sorry|oops|quick_and_dirty' spec proof` finds nothing). Input range
  `smt_in_range`: size at most 2^30, widths at most 2^18, multiplication and division widths at
  most 2^12, distinct with at most 2^8 arguments. The contracts of `elim`, `reconstruct` and the
  call in `solve` are proved (#54); the contracts of the propagation functions carry the reasons
  (`rext`) and the conflict clause (`cfl`) (#61). About 26,300 lines of theories in `proof/`.
- Benchmarks: active suite `QF_BV_Smt-2026-11-18` (101 instances, 40 sat, 61 unsat; 30 s, 8 GB,
  4 jobs). Target (Bitwuzla 0.10.0, #34): **101/101, PAR-2 52.2 s**. main: **52/101 (30 sat,
  22 unsat), PAR-2 2945.1 s** (round A of `progress/20261123T101736Z_69be3427`, main b6f1260, whose
  solver is the same as 51cde83's: `core/` and `cli/` are unchanged since); #54 reported
  52/101, PAR-2 2944.3 s. No wrong answer or bad model in any run.
- Tests (auxiliary): `core/tests/` (`solve.rs`, `eval.rs`, `elim.rs`), `tools/fuzz.py` against z3.

### On main, proved only as pure models

These theories are proved, but no Rust function on main has a contract against them yet:

- `proof/QFBV_Cdcl.thy` (#60): CDCL with 1-UIP analysis (`analyze_m`, `analyze_ok`: the learned
  clause follows from the clauses), the search invariant `cinv` and its steps (propagate, decide,
  backjump, chronological fallback, unsat, total assignment), and the measure of the backjump
  within the existing fuel `3 ^ n`. Imported by `QFBV_DpllWatch` (#61).
- `proof/QFBV_Heap.thy` (#76, #89): list model of the decision heap (insert, pop, pick, back,
  bump, rebuild) with the heap invariant `hinv` and the coverage `hcov` (every unassigned variable
  is in the heap); since #89 a tie-break direction flag `rv`. The heap order is not proved, and
  correctness does not need it. Imports only `Main`; nothing imports it.

### On unmerged branches

- PR #72 (`agent/d33210fb`, head 287b477; #64): migration of `spec/` and `proof/` to the rvec
  model of front end 236538c, with the owner-approved range bound `smt_cost p ≤ 2^43` and
  `check_sat_correct` proved without `sorry`. CI's `proofs`, `rust` and `translation up to date`
  pass; `spec unchanged` fails only on `tools/spec.sha256`, which only the owner updates.
  Reviewed in #73 (`progress/20261123T070000Z_681022ae`): no findings that need a spec change.
- PR #80 (`agent/038a092d-norm`, head 2f14491; #79), stacked on #72: `proof/QFBV_Norm.thy`, the
  pure model `normalize_m` of word-level normalization (sharing, `x = x`, `x + ~x`, `x * ones`,
  product flattening; without the substitution of `v = t`) and its model equivalence. Reviewed in
  #85 (`progress/20261127T194854Z_f1a1ecaf`): the model matches the Rust; the bounds need a
  flattening budget weighted by `ccount` in `core/`.
- Proved on a branch, waiting for #64: `agent/c01c78d1` 7be81a0 (#69): `QFBV_Cdcl.thy` facts for
  phase saving and restarts (decisions of either sign, restart cut, bounded lexicographic
  measure). Progress entry of #67's measurements: `agent/28207582` 2883667.
- Measured only (prototypes, tested with `cargo test` and fuzzing against z3, not verified; all on
  `QF_BV_Smt-2026-11-18` with the same limits, no wrong answer or bad model):

  | prototype | branch, commit | solved | PAR-2 | source |
  |---|---|---|---|---|
  | CDCL (1-UIP, backjump, learning) | `agent/12ac712d-cdcl-rust` | 74/101 | 1629.1 s | `progress/20261120T005000Z_12ac712d` |
  | CDCL (#59) | `agent/d78019dd` df0b0a3 | 78/101 | 1390.0 s | #67, comment on #26 (2026-11-21) |
  | + decision heap, phase saving, Luby restarts (b') | `agent/28207582-perf` 7378d3b | 93–94/101 | 514.0–559.7 s | #67, comment on #26 |
  | (b') + normalization, subset, keep operand order | `agent/69be3427-norm-cdcl-keep` 2b969c1 | 98/101 | 290.3–298.7 s | `progress/20261123T101736Z_69be3427` |
  | 2b969c1 + two decision orders + guarded distributivity | `agent/c0a5fe8b-modes-distrib` 8945699 | **100/101** | **130.7–131.3 s** | `progress/20261127T193336Z_c0a5fe8b` |

  Ranges are over repeated rounds; numbers vary with the load of the shared machine (2b969c1 gave
  97/101 in one round of #81). The best prototype leaves only uclid `tcas60_k_0` unsolved, and its
  PAR-2 is about 2.5 times Bitwuzla's. The normalization alone on main (`agent/69be3427-norm-keep`
  b709dd8; the subset version 6ed46a7 gave 58/101, PAR-2 2589.9 s) gains little without CDCL.

## Limitations and open work

- **The bottleneck is #64 (PR #72), which waits on the owner.** The front end 236538c translates
  `Vec<T>` as `rvec`, so any regeneration of `urust/` from main breaks `spec/`, and CI's
  `translation up to date` fails on every pull request until PR #72 merges. Every change of
  `core/src/lib.rs` waits for it. The owner must update `tools/spec.sha256` (and merge PR #72);
  PR #80 can merge only after it.
- Chain after #64, in order: #65 (CDCL analysis and backjump in the Rust `dpll` with contracts
  against `QFBV_Cdcl.thy`, on the rvec model), #69 (land 7be81a0) and #67 (land the progress entry
  2883667); then PR #80; then contracts of the heap functions against `QFBV_Heap.thy` with the
  port of (a') and (b'); the substitution (item 2) and the Rust contracts (item 3) of the
  normalization, with the flattening budget; and the port of #81's two changes (decision orders
  with the heap, distributivity with the normalization). Until all of this lands, main stays at
  52/101 although 100/101 is measured.
- The suite is not saturated (directive #26): 52 of 101 on main, PAR-2 about 56 times that of
  Bitwuzla. Even the best prototype misses one instance, which is sensitive to the search order;
  #81 chose not to tune the heuristic to it.
- The search termination bound `3 ^ n` (n CNF variables) enters the fuel of the top-level theorem;
  the CDCL prototypes stop learning at `usize::MAX / 4` clauses to stay within it.
- Repair sessions keep picking PR #72 and PR #80 although only the owner can unblock them (more
  than 60 repair claims on PR #72, `LESSONS.md`).
- Unused leftovers in the proofs: `pass_m` (`QFBV_Defs`), `unat64_lt`, and `dprop_post` /
  `dpll_prop_loop` / `dpll_facts` (`QFBV_DpllPure`).
- `isabelle-check` takes about 25–27 minutes; the Pool Server is slow on the large theories, and
  sessions use task heaps (e.g. AutoCorrode plus the theories up to `QFBV_Watch`).

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
  functional models (#53)
- 2026-11-20: `solve` calls `elim`/`reconstruct` with verified contracts: 52/101, PAR-2 2944.3 s
  (#54)
- 2026-11-20: pure CDCL model with entailment, invariant and measure proofs (#60); reasons and
  conflict clause from propagation, search unchanged (#61)
- 2026-11-21: CDCL, heap, phase saving and restarts measured on prototypes: 94/101 (#67, not
  merged: waits for #64)
- 2026-11-23: review of PR #72's spec change and of `qfbv-measure` (#74)
- 2026-11-23: pure decision-heap model, `hinv` and `hcov` (#76)
- 2026-11-23: word-level normalization in the uRust subset, measured: 98/101 with CDCL (#78)
- 2026-11-27: diagnosis of the last three instances; two decision orders and guarded
  distributivity: 100/101, PAR-2 ≈ 131 s on a prototype (#82)
- 2026-11-27: first `LESSONS.md` (#84); review of PR #80 (#86)
- 2026-11-27: tie-break direction flag in the decision-heap model (#89), reviewed (#91)
