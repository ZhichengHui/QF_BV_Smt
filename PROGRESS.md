# Progress

The state and milestones of this repository, kept up to date by summarize sessions (see `PLAN.md`).
Per-session details are in `progress/`; what went wrong before is in `LESSONS.md`.

## Current state

As of main f1b32cc (2026-11-28). Three levels must be kept apart: what `solve` on main does
(verified end to end), what is proved only as a pure model (not yet connected to the Rust code),
and what is only measured, on unmerged scratch branches. Nothing that changes the solver has
merged since 51cde83: `core/`, `cli/`, `urust/` and `spec/` are unchanged, and everything merged
from #92 to #122 is pure models, reviews and progress entries.

### On main: the verified solver

- `solve` (`core/src/lib.rs`): rewriting into a core language of fifteen operations
  (`lower_problem`); elimination of unconstrained definitions (`elim`), with model reconstruction
  (`reconstruct`) of a model of the reduced problem (#54); bit-blasting into CNF (`encode`) with
  Tseitin gates simplified on constant and same-variable inputs; an iterative DPLL over a trail
  (`dpll`) with two-watched-literal unit propagation and chronological backtracking. Since #61 the
  propagation functions also return the reason of each propagated literal and the index of the
  clause in conflict, but `dpll` does not use them: there is still no conflict analysis, no learned
  clause, no backjump, no decision heuristic, no restart, no clause deletion and no word-level
  normalization.
- Verification: `QFBV_heap.check_sat_correct` is proved against `spec/` with no `sorry`
  (`grep -rnwE 'sorry|oops|quick_and_dirty' spec proof` finds nothing). Input range
  `smt_in_range`: size at most 2^30, widths at most 2^18, multiplication and division widths at
  most 2^12, distinct with at most 2^8 arguments. The contracts of `elim`, `reconstruct` and the
  call in `solve` are proved (#54); the contracts of the propagation functions carry the reasons
  (`rext`) and the conflict clause (`cfl`) (#61). About 32,400 lines of `.thy` in `proof/`
  (counted with its subdirectories; 30,700 at 51cde83 by the same count).
- Benchmarks: active suite `QF_BV_Smt-2026-11-18` (101 instances, 40 sat, 61 unsat; 30 s, 8 GB,
  4 jobs). Target (Bitwuzla 0.10.0, #34): **101/101, PAR-2 52.2 s**. main: **52/101 (30 sat,
  22 unsat), PAR-2 2945.1 s** (round A of `progress/20261123T101736Z_69be3427`, main b6f1260, whose
  solver is the same as f1b32cc's); #54 reported 52/101, PAR-2 2944.3 s. No wrong answer or bad
  model in any run.
- Tests (auxiliary): `core/tests/` (`solve.rs`, `eval.rs`, `elim.rs`), `tools/fuzz.py` against z3.

### On main, proved only as pure models

These theories are proved (each checked in the Pool Server or by CI), but no Rust function on
main has a contract against them yet. All except `QFBV_Cdcl` are imported by nothing; each models
a prototype commit statement by statement and was reviewed independently.

- `proof/QFBV_Cdcl.thy` (#60): CDCL with 1-UIP analysis (`analyze_m`, `analyze_ok`: the learned
  clause follows from the clauses), the search invariant `cinv` and its steps (propagate, decide,
  backjump, chronological fallback, unsat, total assignment), and the measure of the backjump
  within the existing fuel `3 ^ n`. Imported by `QFBV_DpllWatch` (#61).
- `proof/QFBV_Heap.thy` (#76, #89): list model of the decision heap (insert, pop, pick, back,
  bump, rebuild) with the heap invariant `hinv`, the coverage `hcov` and a tie-break direction
  flag `rv`. The heap order is not proved, and correctness does not need it.
- `proof/QFBV_Luby.thy` (#94, PR #95; review #96): `fn luby` of 7378d3b; no overflow for
  `i < 2^63`, `1 ≤ luby_m i ≤ i + 1` and a power of 2, and `luby_m i = luby_rec i` (the standard
  recursive definition) for every `i`.
- `proof/QFBV_Activity.thy` (#98, PR #99; review #100): the VSIDS arithmetic of 8945699
  (rescale, saturating bump, increment step `inc + inc/20` with rescale at `2^40`, restart swap);
  `2^10 ≤ inc < 2^40` is invariant, no overflow, rescale preserves `≤`.
- `proof/QFBV_Reduce.thy`, `proof/QFBV_ReduceCompact.thy` (#110, PR #111; review #112; C1–C3
  added by #120): learned-clause deletion of 7043c52 (`level_at`, `clause_lbd`, the selection and
  the compaction of `reduce_db`, without the watch-list rebuild). `sel_m_props` needs no
  hypothesis; `reduce_m_props` needs only `m0 ≤ length db`: the result is a sub-list with the
  same original prefix, kept clauses keep their LBD and watched positions, and reasons are
  renumbered; `compact_m_onto` (C2) and the counting bound `sel_m_hist` (C3).

### On unmerged branches

All open proof PRs carry `needs-owner`, because CI's `translation up to date` and `spec unchanged`
fail until #64 (PR #72) merges; none of them touches `spec/`, `core/` or `urust/`.

- PR #72 (`agent/d33210fb`, head 287b477; #64): migration of `spec/` and `proof/` to the rvec
  model of front end 236538c, with the owner-approved range bound `smt_cost p ≤ 2^43` and
  `check_sat_correct` proved without `sorry`. CI's `proofs`, `rust` and `translation up to date`
  pass; `spec unchanged` fails only on `tools/spec.sha256`, which only the owner updates. Labels
  `needs-owner`, `owner-approved`. Reviewed in #73.
- Normalization models, a stack on PR #72: PR #80 (`agent/038a092d-norm`, 2f14491; #79,
  `QFBV_Norm.thy`, `normalize_m` and its model equivalence, without the substitution of `v = t`;
  review #85) → PR #103 (`agent/70a65c32`, 3366da8; #102, `QFBV_Distrib.thy`, guarded
  distributivity of 4d5017a, `normalize_d_correct`; review #106: approve, about 250 lines
  duplicate `QFBV_Norm`) → PR #117 (`agent/233e2572`, 285dc5d; #116, `QFBV_NormBudget.thy`, the
  flattening budget of 844a971: `pcount (normalize_b_m f q) ≤ f * pcount q` and the bound on the
  number of definitions; review #118: correct). Still missing for a contract: `fb_hyps q'` (it
  follows from `sizes_ok p` through the slack of `lower_fb_hyps`, not from `fb_hyps q` alone; #118
  estimates 150–250 lines), a bucket invariant for `lookup`, and the substitution.
- PR #127 (`agent/5e57b247`, df55dbf; #126), stacked on the branch of PR #111 (now merged):
  `QFBV_ReduceLbd.thy` (the LBD update `update_lbd` of a01c02d) and `QFBV_ReduceTier.thy` (tier-2
  retention of a49260e, reduced to `sel_m` by `sel2_m_sel_m`). Review #128 (PR #130, open): correct;
  corollaries R1–R4 given in the review, not yet in the PR.
- Proved on a branch, waiting for #64: `agent/c01c78d1` 7be81a0 (#69): `QFBV_Cdcl.thy` facts for
  phase saving and restarts. Progress entry of #67's measurements: `agent/28207582` 2883667.
  PR #125 (`agent/17f61c03`, ea73bbf): only the progress entry of #124's measurements.
- Measured only (prototypes, tested with `cargo test` and fuzzing against z3, not verified; all on
  `QF_BV_Smt-2026-11-18` with the same limits, no wrong answer or bad model). Each row is built on
  the one before:

  | prototype | branch, commit | solved | PAR-2 | source |
  |---|---|---|---|---|
  | CDCL (1-UIP, backjump, learning) | `agent/12ac712d-cdcl-rust` | 74/101 | 1629.1 s | `progress/20261120T005000Z_12ac712d` |
  | CDCL (#59) | `agent/d78019dd` df0b0a3 | 78/101 | 1390.0 s | #67, comment on #26 (2026-11-21) |
  | + decision heap, phase saving, Luby restarts (b') | `agent/28207582-perf` 7378d3b | 93–94/101 | 514.0–559.7 s | #67, comment on #26 |
  | (b') + normalization, subset, keep operand order | `agent/69be3427-norm-cdcl-keep` 2b969c1 | 98/101 | 290.3–298.7 s | `progress/20261123T101736Z_69be3427` |
  | + two decision orders + guarded distributivity | `agent/c0a5fe8b-modes-distrib` 8945699 | 100/101 | 129.5–131.3 s | `progress/20261127T193336Z_c0a5fe8b`, #108 |
  | + learned-clause deletion (LBD, keep LBD ≤ 2 and reasons, halve the rest) | `agent/034a756b-reduce` 7043c52 | 101/101 | 109.2–112.4 s | `progress/20261128T052642Z_034a756b`, #114, #124 |
  | + ccount-weighted flattening budget (f = 2) | `agent/a9bb675b-budget` 844a971 | 101/101 | 109.7–110.1 s | `progress/20261128T061818Z_a9bb675b` |
  | + Glucose LBD update in analysis (a) | `agent/17f61c03-tier` a01c02d | 101/101 | 86.3–87.6 s | `progress/20261128T113759Z_17f61c03` (on PR #125) |
  | (a) + CaDiCaL tier 2 (kept while used, LBD ≤ 6) | `agent/17f61c03-tier` **a49260e** | **101/101** | **73.9–74.1 s** | same |

  Ranges are over repeated rounds; numbers vary with the load of the shared machine. The budget
  never binds on the suite (normalization grows `Σccount` by at most 1.053×); it binds only on an
  adversarial chain (120 products without it, 18 with it). The best prototype, a49260e, solves the
  whole suite at about 1.4 times Bitwuzla's PAR-2. Most of its gain over a01c02d is one
  order-sensitive instance (uclid tcas60_k_0, 22.6 → 2.8 s); without it, a01c02d is the better
  build on the other 100 (#124's estimate: about 61 s against 71 s). Sage2 bench_9019 (sat) stays
  at 15–19 s in every deletion variant, against 2.7 s before deletion.

## Limitations and open work

- **The bottleneck is still #64 (PR #72), which waits on the owner.** The front end 236538c
  translates `Vec<T>` as `rvec`, so any regeneration of `urust/` from main breaks `spec/`, and CI's
  `translation up to date` fails on every pull request until PR #72 merges. Every change of
  `core/src/lib.rs` waits for it. The owner must update `tools/spec.sha256` (and merge PR #72).
  Meanwhile the owner has merged the `main`-based pure-model PRs (#95, #99, #111) despite the red
  check; the stacked ones (#80 → #103 → #117) cannot merge before PR #72.
- **The gap between main and the prototypes keeps growing.** main stays at 52/101, PAR-2 2945 s,
  while a49260e measures 101/101, PAR-2 74 s. Beyond main's solver the prototype stack adds CDCL,
  the heap, phase saving, restarts, normalization, decision orders, distributivity, deletion,
  the budget, the LBD update and tier 2, and none of it is verified Rust. The
  pure models cover the arithmetic of most of these pieces, but every contract (of `dpll` with
  analysis and backjump, the heap functions, `luby`, the activity updates, `reduce_db` with the
  watch rebuild, `update_lbd`, `normalize`) is still to be written, on the rvec model.
- Chain after #64, in order: #65 (CDCL analysis and backjump in the Rust `dpll` with contracts
  against `QFBV_Cdcl.thy`), #69 (land 7be81a0) and #67 (land 2883667); then PR #80, #103, #117;
  then the ports with contracts: heap, phase saving and Luby restarts against `QFBV_Heap`/
  `QFBV_Luby`/`QFBV_Activity`; normalization with the substitution, the budget and `fb_hyps q'`;
  decision orders and distributivity; deletion against `QFBV_Reduce*` (with the watch-list
  rebuild, which needs a `watch_init`-like lemma on given positions, `progress/20261128T052642Z_034a756b`);
  then the LBD update and tier 2 against PR #127's models (with R1–R4 of #128). The review
  corollaries R1–R4 and the refactorings suggested in #106 and #118 are not done.
- Directive #26 (saturate the suite): saturated by a prototype, not by main. Even then PAR-2 is
  about 1.4× Bitwuzla's, and the last steps were chosen on a suite with only 4–7 instances above
  3 s; #124 recommends confirming the margin of (a)+(b) on a larger suite. bench_9019 needs
  something other than clause retention (#124 suggests target/best phases).
- New proof obligations from the prototypes: the stamp counter of `clause_lbd` (and `total`) has
  no bound in a contract; it must be bounded like `restarts < 2^20` or use wrapping/saturating
  arithmetic (#108, #124). Restarts already need their own bound outside `3 ^ n`.
- The search termination bound `3 ^ n` (n CNF variables) enters the fuel of the top-level theorem;
  the CDCL prototypes stop learning at `usize::MAX / 4` clauses to stay within the index bounds.
  Deletion does not affect the measure.
- The Pool Server cannot build the import heap for theories importing `QFBV_Norm` (`Cannot load
  theory Micro_Rust_Std_Lib`, #80/#103/#117/#118); those are checked by a batch `isabelle build`
  over the `dev/` copy (about 3 minutes on the AutoCorrode heap).
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
- 2026-11-28: pure models of the Luby sequence (#94/#95) and of the VSIDS activity arithmetic
  (#98/#99), reviewed (#96, #100)
- 2026-11-28: learned-clause deletion measured: 101/101, PAR-2 ≈ 110 s on a prototype (#108); its
  pure model with C1–C3 merged (#110/#111, #112, #120)
- 2026-11-28: ccount-weighted flattening budget measured, never binds on the suite (#114); its
  model on PR #117 (#116), reviewed (#118)
- 2026-11-28: LBD update and tier-2 retention: 101/101, PAR-2 ≈ 74 s on prototype a49260e (#124);
  models on PR #127 (#126), reviewed (#128); `LESSONS.md` updated (#121)
