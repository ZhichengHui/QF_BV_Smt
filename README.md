# BVSmt

一个支持 QF_BV（无量词定长位向量）的 SMT 求解器，能给出模型。求解器核心用 Rust 写成，经 AutoCorrode 前端翻译到
Isabelle/HOL，并证明满足顶层规约。

## 目录结构

| 路径 | 内容 |
|---|---|
| `core/src/lib.rs` | 求解器核心（被验证的部分）：把位向量问题位爆破为 CNF，再用带单元传播的 DPLL 求解，Sat 时读出模型。入口 `pub fn solve(p: &Problem) -> Answer` |
| `cli/src/main.rs` | SMT-LIB 前端（未验证）：解析 QF_BV 脚本，把全部运算按 SMT-LIB 的定义翻译成核心支持的运算，调用 `solve` 并输出结果 |
| `urust/` | AutoCorrode 前端从 `core/src/lib.rs` 生成的 Isabelle 翻译，session `BVSmt` |
| `spec/` | 顶层规约 `BVSmt_Spec.thy`，session `BVSmt_Spec` |
| `proof/` | 证明，session `BVSmt_Proof` |
| `tools/` | 测试与检查脚本 |

## 求解器

核心支持的运算：`not`、`and`、`or`、`xor`、`add`、`mul`、`udiv`、`urem`、`shl`、`lshr`、`concat`、`extract`、`=`、`bvult`、`ite`。
问题由变量（给定位宽）、定义（可引用之前的定义，用于共享子项）和断言（宽度为 1 的项）组成。

构建（需要 Rust 工具链）：

    cargo build --release

产物为 `target/release/bvsmt`。用法：`bvsmt FILE.smt2`，或从标准输入读入脚本。

## 规约与定理

规约 `spec/BVSmt_Spec.thy` 按 SMT-LIB 2.6 的 FixedSizeBitVectors 给出语义（值为小于 `2^w` 的自然数），定义：

- `problem_wt p`：问题良类型；
- `is_assignment p m`：`m` 给每个变量一个宽度正确的位串；
- `is_model p m`：`m` 是使全部断言为 1 的赋值；
- `size_bound p`：由变量位宽、定义和断言的个数、各子项的宽度算出的问题规模；
- `solve_contract p`：前置条件为 `problem_wt p`；返回 `Sat m` 时 `is_model p m`，返回 `Unsat` 时不存在模型；求解器不崩溃。

顶层定理 `BVSmt_ctx.solve_spec`（`proof/BVSmt_Proof.thy`）：若 `size_bound p ≤ urust_fuel` 且 `size_bound p < 2^64`，则
`solve p` 满足 `solve_contract p`。`urust_fuel` 是翻译给每个循环和递归设的次数上限。

证明的组成：

| 文件 | 内容 |
|---|---|
| `proof/BVSmt_Defs.thy` | 每个 Rust 函数的函数式模型，CNF 的语义 |
| `proof/BVSmt_Circuits.thy` | 各个门和位向量电路的语义 |
| `proof/BVSmt_Encode.thy` | 编码的可靠性和完备性：CNF 可满足当且仅当问题有模型 |
| `proof/BVSmt_Refine.thy` | Rust 函数（翻译）的行为等于对应的函数式模型 |
| `proof/BVSmt_Dpll.thy` | DPLL 的正确性 |
| `proof/BVSmt_Bound.thy` | 编码产生的变量数和子句数的上界，由此得到实现所需的次数不超过 `size_bound` |
| `proof/BVSmt_Proof.thy` | 顶层定理 `solve_spec` |

## 检查证明

需要 Isabelle2026 和已构建的 AutoCorrode heap。在仓库根目录：

    isabelle process_theories -l AutoCorrode -d urust -d spec -d proof -O -o threads=8 BVSmt_Proof.BVSmt_Proof

全部通过时输出以 `Finished` 结束、退出码为 0。`tools/check.sh` 把上述目录复制到计算服务器上执行同一检查。

## 测试

`tools/fuzz.py BVSMT Z3 N [SEED]` 随机生成 N 个 QF_BV 问题，与 z3 比较 sat/unsat 结论，并把 bvsmt 给出的模型作为断言加回问题，
用 z3 检验其成立。`tools/remote_fuzz.sh N SEED...` 在计算服务器上并行运行它。
