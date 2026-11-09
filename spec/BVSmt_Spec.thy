theory BVSmt_Spec
  imports BVSmt.BVSmt_Funs
begin

text \<open>\<open>map\<close> below is \<^const>\<open>List.map\<close>, not the iterator function of AutoCorrode.\<close>
hide_const (open) Rust_Iterator.map

section \<open>The top-level specification of the solver\<close>

text \<open>
  OVERVIEW

  The Rust entry point is \<^verbatim>\<open>pub fn solve(p: &Problem) -> Answer\<close> (\<^verbatim>\<open>core/src/lib.rs\<close>), translated
  to \<^verbatim>\<open>BVSmt_ctx.solve\<close>. A problem has variables of the widths \<^const>\<open>Problem_widths\<close>,
  definitions \<^const>\<open>Problem_defs\<close> (each may refer to the earlier ones by \<^const>\<open>Term_Ref\<close>), and
  assertions \<^const>\<open>Problem_asserts\<close> (terms of width 1). Booleans are bit-vectors of width 1, true
  being 1. Bit lists are least significant bit first.

  The specification: for a well-sorted problem, the answer \<open>Sat m\<close> gives a model \<open>m\<close> (bits of
  every variable, of the declared widths) under which every assertion evaluates to 1; the answer
  \<open>Unsat\<close> means that no such model exists.

  The solver does not panic when the problem is well-sorted (\<open>problem_wt\<close>), the fuel
  \<^term>\<open>urust_fuel\<close> of the translation is not less than \<open>size_bound\<close> of the problem,
  and \<open>size_bound\<close> of the problem is less than \<open>2^64\<close> (so that the \<^verbatim>\<open>usize\<close> counters of
  the solver do not overflow).

  Semantics of the operators, following the SMT-LIB 2.6 theory FixedSizeBitVectors (values are
  natural numbers below \<open>2^w\<close>, as with \<^verbatim>\<open>bv2nat\<close>):
  \<^item> \<open>bvnot\<close> is \<open>2^w - 1 - x\<close>; \<open>bvand\<close>, \<open>bvor\<close>, \<open>bvxor\<close> are the bitwise operations on natural numbers.
  \<^item> \<open>bvadd\<close>, \<open>bvmul\<close> are taken modulo \<open>2^w\<close>; \<open>bvshl\<close> is \<open>x * 2^y mod 2^w\<close>; \<open>bvlshr\<close> is \<open>x div 2^y\<close>.
  \<^item> \<open>bvudiv\<close> by 0 is \<open>2^w - 1\<close>; \<open>bvurem\<close> by 0 is the dividend.
  \<^item> \<open>concat a b\<close> has \<open>a\<close> as the high part; \<open>extract hi lo\<close> takes bits \<open>lo..hi\<close>.
  \<^item> \<open>=\<close> and \<open>bvult\<close> give 1 or 0; \<open>ite c a b\<close> is \<open>a\<close> iff \<open>c\<close> is 1.
  The other SMT-LIB operators (signed ones, \<open>bvsub\<close>, \<open>bvneg\<close>, Boolean connectives, \<open>let\<close>, ...)
  are translated into these by the command-line parser (\<^verbatim>\<open>cli/src\<close>), which is not verified.

  Widths: SMT-LIB requires every bit-vector width to be at least 1. This specification places no
  such restriction: a variable of width 0 and the empty constant \<^term>\<open>Term_Const []\<close> are allowed, with
  the value 0 of width 0. The specification therefore generalizes SMT-LIB, and the theorem
  \<open>solve_spec\<close> holds for these problems as well.

  Choices of the transcription:
  \<^item> \<^verbatim>\<open>usize\<close> fields are @{typ \<open>64 word\<close>}; widths and indices are read with \<^const>\<open>unat\<close>.
  \<^item> \<open>xs ! i\<close> is unspecified out of bounds; \<open>wt\<close> keeps every index in bounds.
  \<^item> The problem is passed by shared reference, which the translation passes by value.
  \<^item> \<open>can_alloc_reference\<close>: the solver allocates mutable locals; this is AutoCorrode's requirement.
  \<^item> \<^const>\<open>make_function_contract\<close> makes the abort postcondition false: the contract also states
    that the solver does not panic (no out-of-bounds index, no arithmetic overflow).
  \<^item> The translation bounds every loop and the recursion by the locale parameter
    \<^term>\<open>urust_fuel\<close> and panics when it runs out. \<open>size_bound\<close> is defined from the
    problem alone (outside the locale), so the condition on the fuel does not mention the
    implementation. The theorem \<open>solve_spec\<close> in \<^verbatim>\<open>BVSmt_Proof\<close> assumes
    \<open>size_bound p \<le> urust_fuel\<close> and \<open>size_bound p < 2^64\<close>.
\<close>

subsection \<open>Values\<close>

text \<open>The number a bit list denotes, least significant bit first (\<^verbatim>\<open>bv2nat\<close>).\<close>
fun bits_nat :: \<open>bool list \<Rightarrow> nat\<close> where
  \<open>bits_nat [] = 0\<close>
| \<open>bits_nat (b # bs) = of_bool b + 2 * bits_nat bs\<close>

subsection \<open>Sorts\<close>

text \<open>The width of a term, given the widths \<open>ws\<close> of the variables and \<open>ds\<close> of the definitions.\<close>
fun width :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> Term \<Rightarrow> nat\<close> where
  \<open>width ws ds (Term_Const bs) = length bs\<close>
| \<open>width ws ds (Term_Var i) = ws ! unat i\<close>
| \<open>width ws ds (Term_Ref i) = ds ! unat i\<close>
| \<open>width ws ds (Term_Not a) = width ws ds a\<close>
| \<open>width ws ds (Term_Bin op a b) =
     (case op of BinOp_Concat \<Rightarrow> width ws ds a + width ws ds b
               | BinOp_Eq \<Rightarrow> 1
               | BinOp_Ult \<Rightarrow> 1
               | _ \<Rightarrow> width ws ds a)\<close>
| \<open>width ws ds (Term_Extract hi lo a) = unat hi - unat lo + 1\<close>
| \<open>width ws ds (Term_Ite c a b) = width ws ds a\<close>

text \<open>Well-sortedness: indices in bounds, operands of equal widths (except for \<open>concat\<close>), the
  condition of \<open>ite\<close> of width 1, and \<open>lo \<le> hi < w\<close> for \<open>extract\<close>.\<close>
fun wt :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> Term \<Rightarrow> bool\<close> where
  \<open>wt ws ds (Term_Const bs) = True\<close>
| \<open>wt ws ds (Term_Var i) = (unat i < length ws)\<close>
| \<open>wt ws ds (Term_Ref i) = (unat i < length ds)\<close>
| \<open>wt ws ds (Term_Not a) = wt ws ds a\<close>
| \<open>wt ws ds (Term_Bin op a b) =
     (wt ws ds a \<and> wt ws ds b \<and> (op \<noteq> BinOp_Concat \<longrightarrow> width ws ds a = width ws ds b))\<close>
| \<open>wt ws ds (Term_Extract hi lo a) = (wt ws ds a \<and> unat lo \<le> unat hi \<and> unat hi < width ws ds a)\<close>
| \<open>wt ws ds (Term_Ite c a b) =
     (wt ws ds c \<and> wt ws ds a \<and> wt ws ds b \<and> width ws ds c = 1 \<and> width ws ds a = width ws ds b)\<close>

subsection \<open>Evaluation\<close>

text \<open>A binary operator on the values \<open>x\<close>, \<open>y\<close> of operands of widths \<open>w\<close>, \<open>v\<close>.\<close>
fun bin_sem :: \<open>BinOp \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>bin_sem BinOp_And w x v y = Bit_Operations.and x y\<close>
| \<open>bin_sem BinOp_Or w x v y = Bit_Operations.or x y\<close>
| \<open>bin_sem BinOp_Xor w x v y = Bit_Operations.xor x y\<close>
| \<open>bin_sem BinOp_Add w x v y = (x + y) mod 2 ^ w\<close>
| \<open>bin_sem BinOp_Mul w x v y = (x * y) mod 2 ^ w\<close>
| \<open>bin_sem BinOp_Udiv w x v y = (if y = 0 then 2 ^ w - 1 else x div y)\<close>
| \<open>bin_sem BinOp_Urem w x v y = (if y = 0 then x else x mod y)\<close>
| \<open>bin_sem BinOp_Shl w x v y = (x * 2 ^ y) mod 2 ^ w\<close>
| \<open>bin_sem BinOp_Lshr w x v y = x div 2 ^ y\<close>
| \<open>bin_sem BinOp_Concat w x v y = x * 2 ^ v + y\<close>
| \<open>bin_sem BinOp_Eq w x v y = of_bool (x = y)\<close>
| \<open>bin_sem BinOp_Ult w x v y = of_bool (x < y)\<close>

text \<open>The value of a term, given the widths \<open>ws\<close>, \<open>ds\<close> and the values \<open>vs\<close>, \<open>dv\<close> of the variables
  and the definitions.\<close>
fun eval :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> Term \<Rightarrow> nat\<close> where
  \<open>eval ws ds vs dv (Term_Const bs) = bits_nat bs\<close>
| \<open>eval ws ds vs dv (Term_Var i) = vs ! unat i\<close>
| \<open>eval ws ds vs dv (Term_Ref i) = dv ! unat i\<close>
| \<open>eval ws ds vs dv (Term_Not a) = 2 ^ width ws ds a - 1 - eval ws ds vs dv a\<close>
| \<open>eval ws ds vs dv (Term_Bin op a b) =
     bin_sem op (width ws ds a) (eval ws ds vs dv a) (width ws ds b) (eval ws ds vs dv b)\<close>
| \<open>eval ws ds vs dv (Term_Extract hi lo a) =
     (eval ws ds vs dv a div 2 ^ unat lo) mod 2 ^ (unat hi - unat lo + 1)\<close>
| \<open>eval ws ds vs dv (Term_Ite c a b) =
     (if eval ws ds vs dv c = 1 then eval ws ds vs dv a else eval ws ds vs dv b)\<close>

subsection \<open>Problems\<close>

text \<open>The definitions in order: each is well-sorted over the earlier ones.\<close>
fun defs_wt :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> Term list \<Rightarrow> bool\<close> where
  \<open>defs_wt ws ds [] = True\<close>
| \<open>defs_wt ws ds (d # dd) = (wt ws ds d \<and> defs_wt ws (ds @ [width ws ds d]) dd)\<close>

text \<open>The widths of the definitions, appended to \<open>ds\<close>.\<close>
fun def_widths :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> Term list \<Rightarrow> nat list\<close> where
  \<open>def_widths ws ds [] = ds\<close>
| \<open>def_widths ws ds (d # dd) = def_widths ws (ds @ [width ws ds d]) dd\<close>

text \<open>The values of the definitions, appended to \<open>dv\<close> (the values of definitions of widths \<open>ds\<close>), given
  the widths \<open>ws\<close> and values \<open>vs\<close> of the variables.\<close>
fun def_values :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> Term list \<Rightarrow> nat list\<close> where
  \<open>def_values ws ds vs dv [] = dv\<close>
| \<open>def_values ws ds vs dv (d # dd) =
     def_values ws (ds @ [width ws ds d]) vs (dv @ [eval ws ds vs dv d]) dd\<close>

definition var_widths :: \<open>Problem \<Rightarrow> nat list\<close> where
  \<open>var_widths p \<equiv> map unat (Problem_widths p)\<close>

text \<open>A well-sorted problem: well-sorted definitions and assertions of width 1.\<close>
definition problem_wt :: \<open>Problem \<Rightarrow> bool\<close> where
  \<open>problem_wt p \<equiv>
     let ws = var_widths p in
     let ds = def_widths ws [] (Problem_defs p) in
     defs_wt ws [] (Problem_defs p) \<and>
     (\<forall>t \<in> set (Problem_asserts p). wt ws ds t \<and> width ws ds t = 1)\<close>

text \<open>A model gives every variable a bit list of its width.\<close>
definition is_model :: \<open>Problem \<Rightarrow> bool list list \<Rightarrow> bool\<close> where
  \<open>is_model p m \<equiv> map length m = var_widths p\<close>

text \<open>Every assertion evaluates to 1 under the model.\<close>
definition satisfies :: \<open>Problem \<Rightarrow> bool list list \<Rightarrow> bool\<close> where
  \<open>satisfies p m \<equiv>
     let ws = var_widths p in
     let vs = map bits_nat m in
     let ds = def_widths ws [] (Problem_defs p) in
     let dv = def_values ws [] vs [] (Problem_defs p) in
     \<forall>t \<in> set (Problem_asserts p). eval ws ds vs dv t = 1\<close>

subsection \<open>The size of a problem\<close>

text \<open>The subterms of a term, the term included.\<close>
primrec subterms :: \<open>Term \<Rightarrow> Term list\<close> where
  \<open>subterms (Term_Const bs) = [Term_Const bs]\<close>
| \<open>subterms (Term_Var i) = [Term_Var i]\<close>
| \<open>subterms (Term_Ref i) = [Term_Ref i]\<close>
| \<open>subterms (Term_Not a) = Term_Not a # subterms a\<close>
| \<open>subterms (Term_Bin op a b) = Term_Bin op a b # subterms a @ subterms b\<close>
| \<open>subterms (Term_Extract hi lo a) = Term_Extract hi lo a # subterms a\<close>
| \<open>subterms (Term_Ite c a b) = Term_Ite c a b # subterms c @ subterms a @ subterms b\<close>

text \<open>The weight of a term: the sum over its subterms (counted with multiplicity) of the square of
  the width plus one. Widths are those given by \<^const>\<open>width\<close>, so a \<^const>\<open>Term_Ref\<close> weighs by the
  width of the definition it refers to, however large that is.\<close>
definition term_weight :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> Term \<Rightarrow> nat\<close> where
  \<open>term_weight ws ds t \<equiv> sum_list (map (\<lambda>u. (width ws ds u + 1) ^ 2) (subterms t))\<close>

text \<open>The size of a problem, as a bound on the work of the solver: one plus the sum of the widths of
  the variables, plus the numbers of variables, definitions and assertions, plus the weights of
  all definitions and assertions, times 1000. It is linear in the number of subterms and
  quadratic in their widths. The solver needs a fuel (a bound on the iterations of each loop and
  on the depth of the recursion) and counters (of type \<^verbatim>\<open>usize\<close>) of this size.\<close>
definition size_bound :: \<open>Problem \<Rightarrow> nat\<close> where
  \<open>size_bound p \<equiv>
     let ws = var_widths p in
     let ds = def_widths ws [] (Problem_defs p) in
     1000 * (1 + sum_list ws + length ws + length (Problem_defs p) + length (Problem_asserts p) +
             sum_list (map (term_weight ws ds) (Problem_defs p @ Problem_asserts p)))\<close>

context BVSmt_ctx
begin

subsection \<open>The contract\<close>

definition solve_contract :: \<open>Problem \<Rightarrow> ('s, Answer, 'abort) function_contract\<close> where
  \<open>solve_contract p \<equiv>
     let pre = can_alloc_reference \<star> \<langle>problem_wt p\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>case r of
           Answer_Sat m \<Rightarrow> is_model p m \<and> satisfies p m
         | Answer_Unsat \<Rightarrow> (\<forall>m. is_model p m \<longrightarrow> \<not> satisfies p m)\<rangle> in
     make_function_contract pre post\<close>

end

end
