# 工作进展（2026-11-06，暂停时）

任务：用 Rust 实现支持 QF_BV、能生成模型的 SMT 求解器，用 AutoCorrode 前端翻译到 Isabelle，写顶层规约并证明。

状态：Rust 求解器已完成并通过测试；Isabelle 证明大部分已写出，但没有一次完整检查通过，不能说"已证明"。暂停原因：远端计算主机 `s2982359.pgr.inf.ed.ac.uk` 从约 13:00 起不可达（跳板机正常，从跳板机 ping 丢包 100%，22 端口不通）。

位置：worktree `~/Work/BVSmt/.claude/worktrees/bvsmt`，分支 `worktree-bvsmt`；主仓库 `~/Work/BVSmt`（无远端，未合并进 main）。

## Rust（已完成）

- `core/src/lib.rs`：核心库，被翻译和验证的部分。核心语言只有一种项 `Term`（`Const`、`Var`、`Ref`、`Not`、`Bin`、`Extract`、`Ite`）。布尔值是宽度 1 的位向量。`Ref` 引用之前的定义，以共享子项。流程：Tseitin 位爆破（`blast`、`encode`），然后用带单元传播的 DPLL 求解（`dpll`），`Sat` 时读出模型。入口 `pub fn solve(p: &Problem) -> Answer`。
- `cli/src/main.rs`：SMT-LIB 前端，不验证。它把完整 QF_BV 的运算（有符号运算、`bvsub`、`bvneg`、移位、扩展、旋转、`let`、`define-fun`、`(_ bvN w)`）按 SMT-LIB 的定义翻译成核心语言。
- 构建：`~/Work/AutoCorrodeRustFrontEnd/scripts/cargo.sh build --release`，产物为 `target/release/bvsmt`。
- 测试：`tools/fuzz.py` 和 `tools/remote_fuzz.sh N SEED...` 在远端与 z3 做差分测试。800 个随机问题（371 sat、429 unsat）与 z3 结论全部一致，所有模型经 z3 校验成立。
- 翻译：`~/Work/AutoCorrodeRustFrontEnd/scripts/urust-frontend.sh --out urust --name BVSmt core/src/lib.rs`，结果在 `urust/`。0 个占位符，没有外部函数模板，Isabelle2026 接受。

## Isabelle

检查命令：`BVSMT_WORK=<远端目录名> QD=1 tools/check.sh <会话>.<theory> <超时秒数>`。它在远端 `/disk/scratch/s2982359/<目录名>` 中，以 AutoCorrode heap（Isabelle2026，`~/builds/AutoCorrode`，提交 `d15effd`）为 logic 运行 `process_theories`。`QD=1` 表示 quick_and_dirty（允许 sorry）。单次检查要 10–40 分钟。

| 文件 | 内容 | 状态 |
|---|---|---|
| `spec/BVSmt_Spec.thy` | 顶层规约：SMT-LIB 语义（值为自然数，运算取模 `2^w`，除以 0 按 SMT-LIB 2.6）、`problem_wt`、`is_model`、`satisfies`、`solve_contract` | 检查通过；待用户审阅 |
| `proof/BVSmt_Defs.thy` | 每个 Rust 函数的函数式模型（CNF 状态 `st = nat × Lit list list`，循环用 `foldl` 表示），CNF 语义，`fuel_bound` | 检查通过；已逐个核对模型与翻译一致 |
| `proof/BVSmt_Circuits_Iface.thy` | A1 要证的引理陈述（sorry），供 Encode 先行使用 | 临时文件，完成后删除 |
| `proof/BVSmt_Encode.thy` | `encode_sound`、`encode_complete`、`encode_wf` | 已证完，检查通过（依赖接口文件中的 sorry） |
| `proof/BVSmt_Circuits.thy` | 门电路与位向量电路的语义，含 12 种运算的 `blast_bin_correct` | 除 `fresh_vec_correct` 外，QD 下检查通过 |
| `proof/BVSmt_Refine.thy` | AutoCorrode 合约：从 `lit_const` 到 `encode` 的 Rust 函数等于模型，最终为 `encode_spec` | 已全部写出，无 sorry；部分未检查 |
| `proof/BVSmt_Dpll.thy` | DPLL 的语义与合约：`dpll_top_spec`、`read_model_spec`、`read_model_sigma` | 620 行，无 sorry；检查状态未知 |
| `proof/BVSmt_Proof.thy` | 顶层定理 `solve_spec`（前提 `fuel_bound p ≤ urust_fuel`、`fuel_bound p < 2^64`） | 草稿，未检查 |

各部分的细节：

- `BVSmt_Circuits.thy`：`fresh_vec_correct` 的证明中有一步不终止，导致检查超时。怀疑是 simp 用 `of_nat_add` 改写 `word_of_nat (fst s + i)` 引起的。最后一版已改成结构化证明，并使用 `del: of_nat_add`，但还没检查过。
- `BVSmt_Refine.thy`：合约以模型状态 `s` 为参数，规约的对象是对 `cnf_of s` 的调用，这样可以避免 `st_of`/`cnf_of` 往返转换拖慢 crush。
  - 在 QD 下通过：门电路，以及 `bv_not`、`bv_const`、`bv_shift_const`、`bv_extract`、`bv_concat`、`bv_fresh`、`bv_bitwise`、`bv_add`、`bv_partial`、`bv_mul`、`bv_eq`、`bv_ult`、`bv_ite`、`bv_shift`。其中一部分有 full-blown clarsimp 警告，运行较慢。
  - 修改后未检查：`bv_of_nat`、`bv_zext`、`gate_bitwise`、`blast_bin`、`blast_rec_step`、`bv_divrem`（拆成了中间状态 `dr3`…`dr12`）、`encode` 的三个循环（第 3 个循环 `subgoal for` 的参数名是推测的）、纯引理 `bok_intro`、`enc_*`、`fb_*`、`tbound_width`。
  - B 的私有检查脚本在本地 `/tmp/bvchk`，其中的 ROOT 只列 `BVSmt_Refine`，并可以把已通过的引理替换成 sorry 以缩短检查时间。用法：先 `bash /tmp/bvchk/go2.sh bvsmt-b3 3000 NOGB`；最终检查用 `QD= W=bvsmt-b3 bash /tmp/bvchk/run.sh 3600`。

## 接手步骤

1. 主机恢复后控制并发，同一时间只跑一两个检查。失联前主机负载约 80（64 核），曾有一个 agent 同时跑 5 个检查。负载过高可能是主机失联的原因（推测，未核实）。
2. 依次检查 Circuits（修好 `fresh_vec_correct`）、Dpll、Refine。
3. 把 `BVSmt_Encode.thy` 的 import 从 `BVSmt_Circuits_Iface` 改成 `BVSmt_Circuits`，删除接口文件。
4. 检查 `BVSmt_Proof.BVSmt_Proof`，不带 QD。
5. 清理残留：
   - 远端 `/disk/scratch/s2982359/` 下的 `bvsmt-*` 目录（`bvsmt-work`、`bvsmt-me`、`bvsmt-a1*`、`bvsmt-a2`、`bvsmt-b*`、`bvsmt-c`、`bvsmt-fuzz`），以及可能残留的 Isabelle 进程。
   - 本地 `/tmp/bvchk`、`/tmp/var_*`。
   - AFS 上没有生成新的 heap。
