# Lessons

Guidance distilled from repeated struggles and failed approaches in this repository, kept up to date
by lessons sessions (see `PLAN.md`). Read it before starting a task. Each lesson states what goes
wrong, what to do instead, and the evidence (progress entries, issues, pull requests); lessons that
no longer apply are removed. Progress entries are cited by the session prefix of their file name in
`progress/`.

## Scope

- **Decompose large issues early.** Most solver features need new Rust code, a pure model with its
  proofs, and the contracts. Doing all three in one session does not fit: #45 ran out of context
  after 3 h 22 min and left no commits. Split along that line instead: (1) Rust code that `solve`
  does not call yet, plus the HOL models and their correctness; (2) the contracts, the call in
  `solve`, the fuel and the suite run. Write the design you worked out into the sub-issue bodies.
  Evidence: #43 → #44/#45 (`d323bcd4`), #45 → #51/#52 (`d1d56686`), #56 → #58/#59 plus PR #60
  (`12ac712d`).
- **Prototype the Rust first and measure it before you prove anything.** Keep it on its own branch
  (`agent/<id>-…-rust`), test it (`cargo test`, fuzz against z3) and run the suite with a local
  hook. That shows the payoff and finds bugs before the proofs depend on the code. #51 found the
  compound-operand bug of `invert` through the suite. The CDCL prototype (74/101) fixed the scope of
  #58/#59. Evidence: `d1d56686`, `12ac712d`.
- **A proof can replace a trusted shortcut later.** For #37, the watch lists were not trusted:
  every unit and conflict was re-checked, and a final full check gave completeness. The invariant
  came later as its own issue (#49). Choosing a cheaper proof is fine if `check_sat_correct` stays
  the same. Say so on the issue so that the planner files the rest. Evidence: #37 thread, `388ea2ca`,
  `ef633d4d`.

## Front end and `urust/`

- **The front end can change under the repository.** `URUST_FRONTEND_DIR` follows the newest
  front-end commit. Front end 236538c translates `Vec<T>` as `T rvec`, which changes every
  generated type and the locale and breaks `spec/` (lists). Before relying on a regeneration, diff
  `urust/QFBV_Types.thy` and the locale against main. If the types change, do not touch `spec/`.
  Report it with `coordination needs-owner`, and push the branch first. A translation made with the
  previous commit (5eac898) in a scratch clone of the front end is a valid way to check that your
  code translates. Until the owner answers on #59, it is not a settled way to generate committed
  `urust/`. Evidence: #59 (`d78019dd`, branch `agent/d78019dd`).
- **Function order in `core/src/lib.rs` decides the prism order.** A new `Vec` type in a function
  above `read_model` renumbered the prisms of the locale. Keep `propagate_pass`, and new functions
  with new mutable-local types, below `read_model`, or accept the locale update in `spec/` (the one
  allowed change). Evidence: `860aa6d2` (#35 swapped two prisms), `12ac712d`, `4342c617`.
- **Avoid new mutable-local types.** The 2WL watch lists are three `Vec<usize>` linked lists rather
  than a new struct, so the locale did not change. Evidence: `388ea2ca`.

## Benchmarks and external tools

- **Run main and the change at the same time, under the same conditions.** The machine is shared
  and its load (10–50 on 64 cores) changes from hour to hour. Numbers from different runs or
  different main commits are not comparable: the #34 re-measurement differed from #29 by a merged
  PR and two to three times the load. Build main from `git archive` of its commit and run it beside
  the branch. Start the two `bench/run.sh` runs a few seconds apart: runs started in the same second
  write the same results CSV. Evidence: `03e859bf`, `388ea2ca`, `322d3567`.
- **"No gain" needs a profile, not a guess.** The iterative DPLL (#35) did not speed up the suite.
  callgrind showed 96 % of the time in `propagate_pass`, which led to 2WL (#37: 44 → 49). Profile
  before you choose the next optimisation. Evidence: `860aa6d2`.
- **External solvers:** the owner allows downloading an official release of an established tool into
  `target/` and running it from there (#34). `eval.py` passes no arguments, so put flags such as
  `--produce-models` in a wrapper script outside the repository. Set `BENCH_CACHE=target/bench-cache`
  (`target/` is ignored). If the permission classifier refuses, quote the refusal on the issue and
  stop. Do not get around it. Evidence: #29, #34 thread, `7ce7c4c7`, `03e859bf`.

## Checking proofs

- **Use a task heap for any theory over ~1000 lines.** Rechecking `QFBV_Refine`, `QFBV_Elim`,
  `QFBV_DpllWatch` or `QFBV_Cdcl` in the Pool Server took 2–20 min per edit under load. With a heap
  (`isabelle_build_heap` or a batch session on AutoCorrode with the theories your file imports),
  each check took seconds. Work copies must import the heap's theories qualified. Evidence:
  `d1d56686`, `322d3567`, `12ac712d`, `4342c617`.
- **A batch build of one small session beats the Pool Server for `apply`-heavy contract proofs.**
  It runs proofs in parallel and lists every error at once. Turn the `sorry` you are working on
  into `done` so the log shows its goals. Evidence: `6837961a`, `d323bcd4`, `388ea2ca`.
- `isabelle-devcopy` deletes everything in `dev/`. Keep logs and scratch sessions in `target/`.
  The Pool Server caches imported theories by path: after changing an imported theory, check a
  renamed copy. `isabelle_multi_attempt` rechecks the whole prefix, so stash finished slow proofs
  while you work on later ones. Evidence: `6837961a`, `322d3567`.
- **`isabelle-check` only loads theories reachable from `QFBV_Top`.** A theory that is only listed
  in `proof/ROOT` is not checked. Import a new theory from one the top level imports, and find it
  in the check log. A full check takes about 25 min. Evidence: `d323bcd4`.
- **Imports change which theory a short name refers to.** Adding `QFBV_Elim` and `QFBV_ElimSpec`
  to `QFBV_Proof` changed which theory `defs_wt_nth` and `wt_width_append` resolve to. It also
  brought `lower_m.simps` back into the simpset. Add new imports last, qualify clashing names, and
  re-declare `[simp del]` where needed. Evidence: `d1d56686`, `322d3567`.

## Contract proofs (crush)

- **State facts in the normal form crush produces.** Use `< 18446744073709551616`, not `< 2 ^ 64`;
  use `Suc 0`, not `1`; use the folded `foldl` form; use `xs ≠ []`, not `0 < length xs`. Otherwise
  `crush_base` neither uses the fact nor applies a callee contract whose precondition needs it.
  Evidence: `6837961a`, `322d3567`, #37 thread (gap 2).
- **Keep loop bodies small and their models opaque.** Short-circuit `&&`/`||` and `if`s on bits
  inside a loop body made `crush_base` split into many branches (one step ran > 10 min). Move
  per-bit logic and word arithmetic into tiny helper functions with their own contracts. Write each
  `Vec` at most once per function outside a loop (use a one-write helper such as `set_at`). Count
  loops down (`while i > 0 { i -= 1; … }`) instead of indexing with `len - 1 - j`. Evidence:
  `d323bcd4`, `388ea2ca`, #37 thread (gap 1), #52 (one-loop helpers, `322d3567`).
- **Loop invariants: component-wise, with recursive predicates folded.** A tuple equation
  `st = (…)` blocks lemmas guarded by `k < n`; `map unat dwv = fst (ana_st q k)` does not. Keep
  recursive predicates and results (`settle_pre`, `settle_res`) folded in contracts. Otherwise
  crush unfolds them in the precondition and splits before the loop rule. Give unfolded facts to
  helper lemmas, because `simp add:` definitions are unfolded in the hypotheses too. Evidence:
  `322d3567`, `ef633d4d`.
- **Termination and fuel of the search loop.** Reading the trail as a base-3 number (`meas`)
  bounds the search by `3 ^ n` iterations. That bound is in `dpll_fuel`, and CDCL with backjumps
  keeps it (`meas_backjump`). Any new state the loop grows (learned clauses) needs its own bound
  below 2^64 within that fuel: learning stops at `usize::MAX / 4` clauses. Evidence: `860aa6d2`,
  `12ac712d`.
- **Rule chains with bound indices.** `rule r; assumption` and `frule` take the first matching
  hypothesis, and they can leave premises open or pick the wrong instance. Apply premises in order
  (`rule r, assumption, …`), end with `(simp; fail)` to force backtracking, or use `(drule r)+` to
  take all instances. Targeted steps go after the final `auto` of a crush proof. Evidence:
  `ef633d4d`, `4342c617`.

## Isabelle names and syntax

- `step`, `back`, and `o` are reserved. A fact named `ML` makes the Pool Server reject the file.
  `D` and `K` clash with constants outside a locale. `let a = …; b = … in` is ambiguous with
  uRust's `;`, so nest the `let`s. Evidence: `d323bcd4`, `d1d56686`, `322d3567`, `12ac712d`.
- `simp` does not use `∀i<k. P i ⟶ a ! i = e i ∧ length (a ! i) = w i` (it rewrites one conjunct
  with the other). Get instances with `blast` first. `intro conjI allI impI` also splits under
  quantifiers, so use a dedicated introduction rule. `by blast` closes one goal; use `by blast+` for
  more. Evidence: `d1d56686`, `4342c617`.
