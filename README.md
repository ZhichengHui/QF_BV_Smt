# BVSmt

一个支持 QF_BV（无量词定长位向量）的 SMT 求解器，能给出模型。求解器核心用 Rust 写成，经 AutoCorrode 前端翻译到
Isabelle/HOL，并证明满足顶层规约。

## 目录结构

| 路径 | 内容 |
|---|---|
| `core/src/lib.rs` | 求解器核心（被验证的部分）：把位向量问题位爆破为 CNF，再用带单元传播的 DPLL 求解，Sat 时读出模型。入口 `pub fn solve(p: &Problem) -> Answer` |
| `cli/src/main.rs` | SMT-LIB 前端（未验证）：解析 QF_BV 脚本，直接输出扩展项（不展开位向量运算），只处理 Bool/let/define-fun 等非位向量部分，调用 `solve` 并输出结果 |
| `urust/` | AutoCorrode 前端从 `core/src/lib.rs` 生成的 Isabelle 翻译，session `BVSmt` |
| `spec/` | 顶层规约 `BVSmt_Spec.thy`，session `BVSmt_Spec` |
| `proof/` | 证明，session `BVSmt_Proof` |
| `tools/` | 测试与检查脚本 |

## 求解器

核心覆盖 SMT-LIB 2.6 的 FixedSizeBitVectors 理论和 QF_BV 逻辑规定的全部位向量运算：
`concat`、`extract`、`bvnot`、`bvand`、`bvor`、`bvneg`、`bvadd`、`bvmul`、`bvudiv`、`bvurem`、`bvshl`、`bvlshr`、`bvult`，
以及 `bvnand`、`bvnor`、`bvxor`、`bvxnor`、`bvcomp`、`bvsub`、`bvsdiv`、`bvsrem`、`bvsmod`、`bvashr`、`repeat`、`zero_extend`、
`sign_extend`、`rotate_left`、`rotate_right`、`bvule`、`bvugt`、`bvuge`、`bvslt`、`bvsle`、`bvsgt`、`bvsge`，再加上位向量上的
`=`、`distinct`、`ite`。

问题由变量（给定位宽）、定义（可引用之前的定义，用于共享子项）和断言（宽度为 1 的项）组成，项可直接写出上述任一运算。
核心先把扩展的项按 SMT-LIB 的定义改写（lower）成一小组基本运算（`not`、`and`、`or`、`xor`、`add`、`mul`、`udiv`、`urem`、
`shl`、`lshr`、`concat`、`extract`、`=`、`bvult`、`ite`），再做位爆破和 DPLL。改写保持语义，已在 Isabelle 中证明。

构建（需要 Rust 工具链）：

    cargo build --release

产物为 `target/release/bvsmt`。用法：`bvsmt FILE.smt2`，或从标准输入读入脚本。

## 规约与定理

规约 `spec/BVSmt_Spec.thy` 按 SMT-LIB 2.6 的 FixedSizeBitVectors 原文逐条给出每个运算的语义（值为小于 `2^w` 的自然数，
有符号运算按补码，除以 0 等边界按原文），不以"等于其他运算的组合"来定义；二元运算见 `bin_sem`，其余项见 `eval`。规约还定义：

- `problem_wt p`：问题良类型；
- `is_assignment p m`：`m` 给每个变量一个宽度正确的位串；
- `is_model p m`：`m` 是使全部断言为 1 的赋值；
- `size_bound p`：由变量位宽、定义和断言的个数、各子项的宽度算出的问题规模；
- `sizes_ok p`：`size_bound p < 2^64`，即求解器的 `usize` 计数器不溢出；
- `solve_contract p`：前置条件为 `problem_wt p`（扩展问题的良类型）；返回 `Answer_Sat m` 时 `is_model p m`，返回 `Answer_Unsat` 时不存在模型；求解器不崩溃；
- `solve_correct Γ`：对每个满足 `problem_wt p` 和 `sizes_ok p` 的问题 `p`，存在 `N`，使得翻译取任意不小于 `N` 的 fuel 时，
  `solve p` 都满足 `solve_contract p`。fuel 是翻译给每个循环和递归设的次数上限（`BVSmt_ctx` 的参数 `urust_fuel`）；
  `solve_correct` 在去掉 fuel 参数的 locale `BVSmt_heap` 中陈述，对 fuel 取存在量词，不规定它要多大。

顶层定理 `BVSmt_heap.solve_correct`（`proof/BVSmt_Proof.thy`）证明 `solve_correct Γ`。证明中的 `N` 取 `size_bound p`，
来自 `BVSmt_ctx.solve_spec`：若 `size_bound p ≤ urust_fuel` 且 `size_bound p < 2^64`，则 `solve p` 满足 `solve_contract p`。

证明的组成：

| 文件 | 内容 |
|---|---|
| `proof/BVSmt_Core.thy` | 基本运算的核心项语言 `CoreTerm` 的语义（原规约，常量名加前缀 `c`）与求解合约 `csolve_contract` |
| `proof/BVSmt_Lower.thy` | 改写的函数式模型 `lower_m`/`lower_problem_m`，及改写保持语义：`lower_problem_correct` |
| `proof/BVSmt_LowerRefine.thy` | Rust 改写函数（翻译）的行为等于 `lower_m`/`lower_problem_m`：`lower_spec`、`lower_problem_spec` |
| `proof/BVSmt_LowerBound.thy` | 改写后的核心问题规模不超过原问题的 `size_bound`：`lower_size_bound` |
| `proof/BVSmt_Defs.thy` | 每个 Rust 函数的函数式模型，CNF 的语义 |
| `proof/BVSmt_Circuits.thy` | 各个门和位向量电路的语义 |
| `proof/BVSmt_Encode.thy` | 编码的可靠性和完备性：CNF 可满足当且仅当问题有模型 |
| `proof/BVSmt_Refine.thy` | Rust 函数（翻译）的行为等于对应的函数式模型 |
| `proof/BVSmt_Dpll.thy` | DPLL 的正确性 |
| `proof/BVSmt_Bound.thy` | 编码产生的变量数和子句数的上界，由此得到实现所需的次数不超过 `size_bound` |
| `proof/BVSmt_Proof.thy` | `solve_spec`（fuel 不小于 `size_bound` 时满足合约）与顶层定理 `solve_correct` |

## 检查证明

需要 Isabelle2026 和已构建的 AutoCorrode heap。在仓库根目录：

    isabelle process_theories -l AutoCorrode -d urust -d spec -d proof -O -o threads=8 BVSmt_Proof.BVSmt_Proof

全部通过时输出以 `Finished` 结束、退出码为 0。`tools/check.sh` 把上述目录复制到计算服务器上执行同一检查。

## 测试

`tools/fuzz.py BVSMT Z3 N [SEED]` 随机生成 N 个 QF_BV 问题，与 z3 比较 sat/unsat 结论，并把 bvsmt 给出的模型作为断言加回问题，
用 z3 检验其成立。`tools/remote_fuzz.sh N SEED...` 在计算服务器上并行运行它。
