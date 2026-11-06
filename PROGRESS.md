# 工作进展（2026-11-06 晚）

任务：用 Rust 实现支持 QF_BV、能生成模型的 SMT 求解器，用 AutoCorrode 前端翻译到 Isabelle，写顶层规约并证明。

状态：完成。`BVSmt_Proof.BVSmt_Proof` 及其导入的全部 theory 在不开 quick_and_dirty 的情况下检查通过（`EXIT 0`），
没有 sorry。顶层定理是 `BVSmt_ctx.solve_spec`：前提为 `fuel_bound p ≤ urust_fuel` 和 `fuel_bound p < 2^64` 时，
`solve p` 满足 `solve_contract p`。规约 `spec/BVSmt_Spec.thy` 仍待用户审阅。

位置：worktree `~/Work/BVSmt/.claude/worktrees/bvsmt`，分支 `worktree-bvsmt`；主仓库 `~/Work/BVSmt`（无远端，未合并进 main）。

## Rust

- `core/src/lib.rs`：核心库（位爆破 + DPLL），被翻译和验证的部分。入口 `pub fn solve(p: &Problem) -> Answer`。
- `cli/src/main.rs`：SMT-LIB 前端，不验证。
- 构建：`~/Work/AutoCorrodeRustFrontEnd/scripts/cargo.sh build --release`，产物为 `target/release/bvsmt`。
- 测试：`tools/fuzz.py`、`tools/remote_fuzz.sh` 与 z3 差分测试，800 个随机问题全部一致。
- 翻译：`~/Work/AutoCorrodeRustFrontEnd/scripts/urust-frontend.sh --out urust --name BVSmt core/src/lib.rs`。

## Isabelle

| 文件 | 内容 |
|---|---|
| `spec/BVSmt_Spec.thy` | 顶层规约：SMT-LIB 语义、`problem_wt`、`is_model`、`satisfies`、`solve_contract` |
| `proof/BVSmt_Defs.thy` | 每个 Rust 函数的函数式模型，CNF 语义，`fuel_bound` |
| `proof/BVSmt_Circuits.thy` | 门电路与位向量电路的语义 |
| `proof/BVSmt_Encode.thy` | `encode_sound`、`encode_complete`、`encode_wf` |
| `proof/BVSmt_Refine.thy` | AutoCorrode 合约：Rust 函数等于模型，最终为 `encode_spec` |
| `proof/BVSmt_Dpll.thy` | DPLL 的语义与合约 |
| `proof/BVSmt_Proof.thy` | 顶层定理 `solve_spec` |

检查：`BVSMT_WORK=<远端目录名> tools/check.sh BVSmt_Proof.BVSmt_Proof 7200`，在远端
`/disk/scratch/s2982359/<目录名>` 中以 AutoCorrode heap 运行 `process_theories`，约 45 分钟。`QD=1` 允许 sorry；
`OPTS="-o parallel_proofs=0"` 让证明按顺序执行，可以从输出看出哪一步不终止。检查要在保持登录的 ssh 会话里前台运行
（退出登录后后台进程访问不了 AFS）。
