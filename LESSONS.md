# Lessons

Guidance distilled from repeated struggles and failed approaches in this repository, kept up to date
by lessons sessions (see `PLAN.md`). Read it before starting a task. Each lesson states what goes
wrong, what to do instead, and the evidence (progress entries, issues, pull requests); lessons that
no longer apply are removed. Progress entries are cited by the session prefix of their file name in
`progress/`; entries marked "PR #N" are on that pull request's branch and not yet on `main`.

## Scope

- **Decompose large issues early.** Most solver features need new Rust code, a pure model with its
  proofs, and the contracts. All three do not fit in one session: #45 ran out of context after
  3 h 22 min and left no commits. Split along that line instead: (1) Rust code that `solve` does not
  call yet, plus the HOL models and their correctness; (2) the contracts, the call in `solve`, the
  fuel and the suite run. Write the design you worked out into the sub-issue bodies. Forked
  subagents inherit the whole context and die of "prompt too long" on long tasks; give fresh agents
  a self-contained brief instead. Evidence: #43 → #44/#45 (`d323bcd4`), #45 → #51/#52 (`d1d56686`),
  #56 → #58/#59 (`12ac712d`), #59 → #64/#65; `d33210fb` (PR #72).
- **Prototype and measure before you prove anything.** Put the Rust on scratch branches
  (`agent/<id>-…`, not for merge), test it (`cargo test`, fuzz against z3), translate it into a
  scratch directory (0 placeholders, templates and locale unchanged against main's translation) and
  run the suite with a local hook. That shows the payoff, finds bugs before proofs depend on the
  code, and fixes the scope of the verification issues. A measurement-only PR (progress entry
  only) with the scratch branches named is a normal result. Fuzz instances rarely reach thresholds
  such as "reduce every 2000 conflicts": also test a stress variant with tiny thresholds (it ran
  the suite with no wrong answer). Measure whether a change binds at all: deletion gained an
  instance and 15 % PAR-2, the flattening budget never binds on the suite (growth ≤ 1.053×) and
  exists only so that the bound can be proved. Evidence: #51's `invert` bug found by the suite
  (`d1d56686`), CDCL prototype 74/101 (`12ac712d`), #77 (`69be3427`), #81 (PR #82, `c0a5fe8b`),
  `034a756b` (#108), `a9bb675b` (#114).
- **State the model's lemmas from the later contract's obligations.** Reviews of faithful pure
  models kept finding lemmas the contract will need and the model PR did not prove: that the
  compaction map is onto, that histogram counters cannot overflow, a `level_at` bound without
  `sorted` (#111, follow-up #120); a bucket invariant or relational spec for `lookup` (#103); and
  that `fb_hyps q'` does not follow from `fb_hyps q` with `f = 2` but needs the slack of
  `lower_fb_hyps` (#117). Before writing the model, list the obligations (the prototype's progress
  entry often has them, as in `034a756b`): every index below its length, every counter and sum
  below 2^64, maps onto/injective where lists are rebuilt, and the end-to-end bound composed with
  the existing chain (`sizes_ok` → `lower_fb_hyps` → …). Evidence: `dd7cf7da`, reviews on PR #103,
  #111, #117.
- **A proof can replace a trusted shortcut later.** For #37 the watch lists were not trusted: every
  unit and conflict was re-checked and a final full check gave completeness; the invariant came
  later as #49. A cheaper proof is fine if `check_sat_correct` stays the same; say so on the issue so
  that the planner files the rest. Evidence: `388ea2ca`, `ef633d4d`.
- **Check the size bounds before designing a pass that grows the problem.** The range is tight:
  `sizes_ok` leaves a factor of about 1.9 over `smt_in_range`, and `lower_fb_hyps` a factor of about
  4–8 for the counts of the lowered problem. Normalization's product flattening can grow the
  definitions 15-fold, so `fb_hyps` of its result cannot be proved, and `size_ok` cannot be
  tightened without answering `Unknown` in range. Budget the growth in the code (at most a constant
  factor of the input) from the start; the fuel itself is existential and is not the problem.
  Evidence: `69be3427` ("check this first"), #79 (PR #80, `038a092d`); range of #64 (`2023e589`,
  `d33210fb`, PR #72).

## Front end, `urust/` and CI

- **The front end can change under the repository.** `URUST_FRONTEND_DIR` and CI follow the newest
  front-end commit. Front end 236538c translates `Vec<T>` as `T rvec`, which changed every generated
  type and the locale and broke `spec/`; the owner chose to migrate `spec/` and `proof/` (#59, #64,
  PR #72). Until PR #72 merges, `translation up to date` fails on every PR, including `main`. To tell
  drift from your own failure: regenerate `urust/` from unchanged `origin/main`; if it differs too,
  the failure is not yours. Say so in the PR body and change nothing for it. After any regeneration,
  diff `urust/QFBV_Types.thy` and the locale against main; if the types change, do not touch
  `spec/`: put the question on the issue with `coordination needs-owner` and push your branch first.
  Evidence: #59, #62, closed PRs #63, #68, #70.
- **Do not close a PR because of a failure that every PR has.** #63, #68 and #70 were closed as
  "unsalvageable" only for the drift above; their content was fine and had to be replanned. Leave
  such PRs open with a comment naming the blocking issue. Evidence: #63, #68, #70.
- **A PR waiting only on the owner needs no more repair sessions.** PR #72 waits for the owner's
  `tools/spec.sha256` update (agents may not edit it); more than 60 repair sessions each re-checked it
  and released it without a change (2026-11-23). Repair sessions now post one "Needs an owner
  decision" comment, label `needs-owner` and skip the PR afterwards. In a repair session, read the
  last repair comments first: if they name the same owner-only blocker and neither the PR head nor
  the failing check has changed, release at once without re-running checks. Evidence: PR #72
  comments, PR #103, #111, #117, #119.
- **Do not stack chains on an owner-blocked PR; prefer work that merges on `main`.** The owner merges
  `main`-based PRs although `translation up to date` fails (#95, #99, #115 merged). Stacked PRs also
  fail `spec unchanged` and cannot merge before their base: #72 → #80 → #103 → #117 now waits with
  four PRs, each base needing its own review, and `proof/ROOT` conflicts needed fix issues (#104,
  #120). The stack also froze duplication: #103 copies ~250 lines of `QFBV_Norm` and #117 another
  ~160 because the base PRs may not be edited. Stack at most one level, and only when the work
  needs the base (the rvec model); otherwise choose a pure model that imports `Main` or merged
  theories only (`QFBV_Luby`, `QFBV_Activity`, `QFBV_Reduce` are on or based on `main`). If you
  must stack, generalise the base first (parametrise `norm_loop` over `mk`), state "merge after #N"
  in the PR body, and expect the base's failing checks. Evidence: PR #80 (`038a092d`), reviews on
  #103 (`ab6e7b40`) and #117.
- **Fixing another PR's branch:** it may be checked out in another worktree, so use a local branch
  of another name: `git checkout -b tmp origin/<branch>`, merge, `git push origin tmp:<branch>`.
  `coordination plan --help` creates an issue titled `--help` (#87). Evidence: `c878859a`, #87.
- **Function order in `core/src/lib.rs` decides the prism order.** A new `Vec` type in a function
  above `read_model` renumbers the prisms of the locale. Keep functions with new mutable-local types
  below `read_model`, or accept the locale update in `spec/` (the one allowed change). Prefer
  existing types: the 2WL watch lists are three `Vec<usize>` linked lists, and the normalization
  passes tuples instead of a struct, so the locale did not change. Evidence: `860aa6d2`,
  `388ea2ca`, `12ac712d`, `69be3427`.

## Benchmarks and diagnosis

- **Run the variants at the same time, more than once.** The machine is shared (load 10–50 on 64
  cores). Numbers from different runs or different main commits are not comparable, and single
  instances near the limit flip between rounds (calypto problem_15: 25 s or timeout). Build each
  variant, start the `bench/run.sh` runs 15 s apart (same-second starts write the same results CSV),
  and repeat the round; the suite decides, not single-instance timings. Evidence: `03e859bf`,
  `388ea2ca`, `69be3427`, `c0a5fe8b` (PR #82).
- **Find where the time goes before choosing the next optimization.** The iterative DPLL (#35) gave
  nothing; callgrind showed 96 % in `propagate_pass`, which led to 2WL (44 → 49). For a hard
  instance, write the CNF of `encode` as DIMACS and give it to `z3 -dimacs`: if z3 solves it fast,
  the search is at fault (ext_con: the heap's lowest-index tie-break), if not, the encoding needs a
  word-level step (distrib64). Evidence: `860aa6d2`, `c0a5fe8b` (PR #82).
- **Small changes of the CNF change the heuristics' results.** Sorting commutative operands lost two
  instances that the input order keeps; a reversed tie-break gained three and lost six. Prefer the
  input's order, and keep both decision orders (alternate at restarts) rather than replacing one.
  Do not tune for single instances (tcas60_k_0 is order-sensitive). Evidence: `69be3427`,
  `c0a5fe8b` (PR #82).
- **External solvers:** downloading an official release into `target/` or a scratch directory and
  running it is allowed (#34). `eval.py` passes no arguments, so put flags such as
  `--produce-models` in a wrapper script outside the repository; set `BENCH_CACHE=target/bench-cache`.
  If the permission classifier refuses, quote the refusal on the issue and stop. Evidence:
  `7ce7c4c7`, `03e859bf`.

## Checking proofs

- **Use a task heap for any theory over ~1000 lines or with slow imports.** Rechecking
  `QFBV_Refine`, `QFBV_Elim`, `QFBV_DpllWatch` or `QFBV_Cdcl` took 2–20 min per edit; on a heap
  each check took seconds. The Pool Server's automatic import heap has parent `HOL` and lacks
  AutoCorrode: build the heap with parent `AutoCorrode` (`isabelle_build_heap` from a directory with
  its own `ROOT`, or a batch session), and import its theories qualified in a work copy. The build
  call times out on the client after 10 min but keeps running. For `dev/` theories importing
  `QFBV_Norm` or `QFBV_Bound` the automatic import heap fails outright (`Cannot load theory
  "Micro_Rust_Std_Lib…"`, #80/#103/#117): go straight to a task heap or a scratch batch session
  `AutoCorrode + <theory>` (2–3 min). Evidence: `860aa6d2`, `d1d56686`,
  `322d3567`, `12ac712d`, `4342c617`, `038a092d` (PR #80), `d33210fb` (PR #72).
- **When the imports are too heavy, check against `sorry` copies of them.** The Pool Server ran out
  of memory or timed out loading the full `QFBV_Refine`. Copy the imports with every proof replaced
  by `sorry` (statements unchanged; a small script over the top-level `lemma` blocks), develop on
  them, then confirm with a batch build. Evidence: `2023e589`, `cb89602a`, `d33210fb` (PR #72).
- **A batch build of one small session beats the Pool Server for `apply`-heavy contract proofs.** It
  runs proofs in parallel and lists every error at once; turn the `sorry` you are working on into
  `done` so the log shows its goals. Evidence: `6837961a`, `d323bcd4`, `388ea2ca`.
- **Pool Server habits.** `isabelle-devcopy` deletes everything in `dev/`: keep logs and scratch
  sessions in `target/`. Imported theories are cached by path: after changing one, check a renamed
  copy. `isabelle_multi_attempt` rechecks the whole prefix, so stash finished slow proofs while you
  work on later ones. An idle session is reaped after ~10 min. To test a lemma without editing the
  file (a review's corollary), `isabelle_multi_attempt` at the line of the final `end` with lemma
  text that contains no `end`. Evidence: `6837961a`, `322d3567`, `2023e589` (PR #72), `78bbda65`,
  `dd7cf7da`.
- **`isabelle-check` only loads theories reachable from `QFBV_Top`.** A theory only listed in
  `proof/ROOT` is not checked by it. Import a new theory from one the top level imports and find it
  in the check log. A full check takes about 25 min. Evidence: `d323bcd4`.
- **Imports change which theory a short name refers to.** Adding `QFBV_Elim` changed what
  `defs_wt_nth` resolves to and brought `lower_m.simps` back into the simpset; on a heap with many
  theories, `ref_ok`, `env_ok`, `N` resolved to other constants; `QFBV_Bound` and `QFBV_Norm` both
  define `mul_step`. Add new imports last, qualify clashing names, and re-declare `[simp del]` where
  needed. Evidence: `d1d56686`, `322d3567`, `d33210fb` (PR #72), review on PR #117.

## Pure models

- **The shape reviews accept quickly.** One `function` per Rust loop (measure on the index), its
  `.simps` `[simp del]`, a closed-form lemma for each loop, the Rust quoted next to it, and values
  on `nat` with explicit `< 2^64` bounds instead of words (no word gap; saturating ops as `min (a +
  b) USIZE_MAX`). A guard only needed for termination on `nat` is fine if a lemma shows it holds on
  reachable states. Split a theory past ~500 lines. Evidence: `4123cad2`, `0003b1cb`, `8c00b4eb`,
  review on PR #111.
- **Do not let `simp` evaluate large powers.** `simp` on `2 ^ (seq + 1) ≤ 2 ^ 64` ran over 100 s; use
  `power_le_imp_le_exp`/`metis` with the exponent kept symbolic. Evidence: `4123cad2`.

## Contract proofs (crush)

- **Give `crush_base` only cheap rules.** With many arithmetic lemmas in `simp add:`
  (`antisym_conv`, `unat_word_Suc_simp` were the worst) a contract proof takes 5–25 min or does not
  end. Two phases: `crush_base` with the definitions of the result predicate and cheap facts, then
  `simp_all`/`auto` with the `unat_*` and model step lemmas. Evidence: `2023e589`, `cb89602a`
  (PR #72), `388ea2ca`.
- **State facts in the normal form crush produces.** `< 18446744073709551616`, not `< 2 ^ 64`;
  `Suc 0`, not `1`; the folded `foldl` form; `xs ≠ []`, not `0 < length xs`. Otherwise `crush_base`
  neither uses the fact nor applies a callee contract whose precondition needs it. Simp-split
  states (`st_of_simps`) do not match lemmas over a state variable: instantiate them
  (`[where s=…, simplified]`). Evidence: `6837961a`, `322d3567`, #37, `2023e589` (PR #72).
- **Keep loop bodies small and their models opaque.** Short-circuit `&&`/`||` and `if`s on bits in a
  loop body made `crush_base` split into many branches (> 10 min per step). Move per-bit logic and
  word arithmetic into tiny helpers with their own contracts, one loop per function, write each
  `Vec` at most once outside a loop (`set_at`), and count loops down (`while i > 0 { i -= 1; … }`)
  instead of indexing with `len - 1 - j`. Evidence: `d323bcd4`, `388ea2ca`, `322d3567`.
- **Loop invariants: component-wise, with recursive predicates folded.** A tuple equation
  `st = (…)` blocks lemmas guarded by `k < n`; `map unat dwv = fst (ana_st q k)` does not. Keep
  recursive predicates and results (`settle_pre`, `settle_res`) folded in contracts, or crush
  unfolds them and splits before the loop rule. Evidence: `322d3567`, `ef633d4d`, `cb89602a` (PR #72).
- **rvec: no assumptions on the input's layout.** The spec does not constrain capacity or layout of
  input vectors, and a `clone` keeps them, so a cloned input cannot be shown to grow within
  `rvec_cap_max`; copy element by element (`bits_copy`). Every vector the solver grows stays below
  2^56 elements (`vok`). Evidence: `cb89602a`, `d33210fb` (PR #72).
- **Bound every state the search loop grows.** The search is bounded by `3 ^ n` iterations (`meas`
  reads the trail as a base-3 number; `meas_backjump` keeps it for CDCL). Learned clauses need their
  own bound below 2^64 within that fuel: learning stops at `usize::MAX / 4` clauses. Evidence:
  `860aa6d2`, `12ac712d`.
- **Rule chains with bound indices.** `rule r; assumption` and `frule` take the first matching
  hypothesis and can leave premises open or pick the wrong instance. Apply premises in order
  (`rule r, assumption, …`), end with `(simp; fail)` to force backtracking, or use `(drule r)+`.
  Put targeted steps after the final `auto` of a crush proof. Evidence: `ef633d4d`, `4342c617`.

## Isabelle names and syntax

- `step`, `back` and `o` are reserved; a fact named `ML` makes the Pool Server reject the file; `D`
  and `K` clash with constants outside a locale; `let a = …; b = … in` is ambiguous with uRust's
  `;`, so nest the `let`s. Evidence: `d323bcd4`, `d1d56686`, `322d3567`, `12ac712d`.
- `simp` does not use `∀i<k. P i ⟶ a ! i = e i ∧ length (a ! i) = w i`: get instances with `blast`
  first. `intro conjI allI impI` also splits under quantifiers: use an introduction rule. `by blast`
  closes one goal: `by blast+`. Unfolding the `.simps` of a `function` with `auto` loops: declare
  them `[simp del]` and unfold once. Evidence: `d1d56686`, `4342c617`, `36ecc257`.
