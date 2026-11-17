theory QFBV_Core
  imports "QFBV_CoreSpec.QFBV_CoreSpec"
begin

section \<open>The core language\<close>

text \<open>
  The core language (\<^typ>\<open>CoreTerm\<close>, \<^typ>\<open>CoreProblem\<close>) is the language the solver bit-blasts: the
  terms of the extended language are rewritten into it by \<^verbatim>\<open>lower_problem\<close>. This theory gives
  it the same kind of semantics as \<^verbatim>\<open>QFBV_Spec\<close> gives the extended language, with the names
  prefixed by \<open>c\<close>: widths, well-sortedness, evaluation, models and the size bound of a core
  problem. It is part of the proof, not of the specification.

  The widths of core terms may be 0 (the rewriting of \<open>repeat\<close> starts from the empty constant).
  The semantics of the twelve binary operators, \<open>bvnot\<close>, \<open>extract\<close> and \<open>ite\<close> are those of
  \<^verbatim>\<open>QFBV_Spec\<close> (with \<open>2^0 - 1 = 0\<close> for the empty constant).
\<close>

subsection \<open>Sorts\<close>

text \<open>The cwidth of a term, given the widths \<open>ws\<close> of the variables and \<open>ds\<close> of the definitions.\<close>
fun cwidth :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> CoreTerm \<Rightarrow> nat\<close> where
  \<open>cwidth ws ds (CoreTerm_Const bs) = length bs\<close>
| \<open>cwidth ws ds (CoreTerm_Var i) = ws ! unat i\<close>
| \<open>cwidth ws ds (CoreTerm_Ref i) = ds ! unat i\<close>
| \<open>cwidth ws ds (CoreTerm_Not a) = cwidth ws ds a\<close>
| \<open>cwidth ws ds (CoreTerm_Bin op a b) =
     (case op of BinOp_Concat \<Rightarrow> cwidth ws ds a + cwidth ws ds b
               | BinOp_Eq \<Rightarrow> 1
               | BinOp_Ult \<Rightarrow> 1
               | _ \<Rightarrow> cwidth ws ds a)\<close>
| \<open>cwidth ws ds (CoreTerm_Extract hi lo a) = unat hi - unat lo + 1\<close>
| \<open>cwidth ws ds (CoreTerm_Ite c a b) = cwidth ws ds a\<close>

text \<open>Well-sortedness: indices in bounds, operands of equal widths (except for \<open>concat\<close>), the
  condition of \<open>ite\<close> of cwidth 1, and \<open>lo \<le> hi < w\<close> for \<open>extract\<close>.\<close>
fun cwt :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> CoreTerm \<Rightarrow> bool\<close> where
  \<open>cwt ws ds (CoreTerm_Const bs) = True\<close>
| \<open>cwt ws ds (CoreTerm_Var i) = (unat i < length ws)\<close>
| \<open>cwt ws ds (CoreTerm_Ref i) = (unat i < length ds)\<close>
| \<open>cwt ws ds (CoreTerm_Not a) = cwt ws ds a\<close>
| \<open>cwt ws ds (CoreTerm_Bin op a b) =
     (cwt ws ds a \<and> cwt ws ds b \<and> (op \<noteq> BinOp_Concat \<longrightarrow> cwidth ws ds a = cwidth ws ds b))\<close>
| \<open>cwt ws ds (CoreTerm_Extract hi lo a) = (cwt ws ds a \<and> unat lo \<le> unat hi \<and> unat hi < cwidth ws ds a)\<close>
| \<open>cwt ws ds (CoreTerm_Ite c a b) =
     (cwt ws ds c \<and> cwt ws ds a \<and> cwt ws ds b \<and> cwidth ws ds c = 1 \<and> cwidth ws ds a = cwidth ws ds b)\<close>

subsection \<open>Evaluation\<close>

text \<open>A binary operator on the values \<open>x\<close>, \<open>y\<close> of operands of widths \<open>w\<close>, \<open>v\<close>.\<close>
definition cbin_sem :: \<open>BinOp \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>cbin_sem op w x v y \<equiv>
     (case op of
        BinOp_And \<Rightarrow> (Bit_Operations.and x y)
      | BinOp_Or \<Rightarrow> (Bit_Operations.or x y)
      | BinOp_Xor \<Rightarrow> (Bit_Operations.xor x y)
      | BinOp_Add \<Rightarrow> ((x + y) mod 2 ^ w)
      | BinOp_Mul \<Rightarrow> ((x * y) mod 2 ^ w)
      | BinOp_Udiv \<Rightarrow> (if y = 0 then 2 ^ w - 1 else x div y)
      | BinOp_Urem \<Rightarrow> (if y = 0 then x else x mod y)
      | BinOp_Shl \<Rightarrow> ((x * 2 ^ y) mod 2 ^ w)
      | BinOp_Lshr \<Rightarrow> (x div 2 ^ y)
      | BinOp_Concat \<Rightarrow> (x * 2 ^ v + y)
      | BinOp_Eq \<Rightarrow> (of_bool (x = y))
      | BinOp_Ult \<Rightarrow> (of_bool (x < y)))\<close>

lemma cbin_sem_simps [simp]:
  \<open>cbin_sem BinOp_And w x v y = Bit_Operations.and x y\<close>
  \<open>cbin_sem BinOp_Or w x v y = Bit_Operations.or x y\<close>
  \<open>cbin_sem BinOp_Xor w x v y = Bit_Operations.xor x y\<close>
  \<open>cbin_sem BinOp_Add w x v y = (x + y) mod 2 ^ w\<close>
  \<open>cbin_sem BinOp_Mul w x v y = (x * y) mod 2 ^ w\<close>
  \<open>cbin_sem BinOp_Udiv w x v y = (if y = 0 then 2 ^ w - 1 else x div y)\<close>
  \<open>cbin_sem BinOp_Urem w x v y = (if y = 0 then x else x mod y)\<close>
  \<open>cbin_sem BinOp_Shl w x v y = (x * 2 ^ y) mod 2 ^ w\<close>
  \<open>cbin_sem BinOp_Lshr w x v y = x div 2 ^ y\<close>
  \<open>cbin_sem BinOp_Concat w x v y = x * 2 ^ v + y\<close>
  \<open>cbin_sem BinOp_Eq w x v y = of_bool (x = y)\<close>
  \<open>cbin_sem BinOp_Ult w x v y = of_bool (x < y)\<close>
  by (simp_all add: cbin_sem_def)

text \<open>The value of a term, given the widths \<open>ws\<close>, \<open>ds\<close> and the values \<open>vs\<close>, \<open>dv\<close> of the variables
  and the definitions.\<close>
fun ceval :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> CoreTerm \<Rightarrow> nat\<close> where
  \<open>ceval ws ds vs dv (CoreTerm_Const bs) = bits_nat bs\<close>
| \<open>ceval ws ds vs dv (CoreTerm_Var i) = vs ! unat i\<close>
| \<open>ceval ws ds vs dv (CoreTerm_Ref i) = dv ! unat i\<close>
| \<open>ceval ws ds vs dv (CoreTerm_Not a) = 2 ^ cwidth ws ds a - 1 - ceval ws ds vs dv a\<close>
| \<open>ceval ws ds vs dv (CoreTerm_Bin op a b) =
     cbin_sem op (cwidth ws ds a) (ceval ws ds vs dv a) (cwidth ws ds b) (ceval ws ds vs dv b)\<close>
| \<open>ceval ws ds vs dv (CoreTerm_Extract hi lo a) =
     (ceval ws ds vs dv a div 2 ^ unat lo) mod 2 ^ (unat hi - unat lo + 1)\<close>
| \<open>ceval ws ds vs dv (CoreTerm_Ite c a b) =
     (if ceval ws ds vs dv c = 1 then ceval ws ds vs dv a else ceval ws ds vs dv b)\<close>

subsection \<open>Problems\<close>

text \<open>The definitions in order: each is well-sorted over the earlier ones.\<close>
fun cdefs_wt :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> CoreTerm list \<Rightarrow> bool\<close> where
  \<open>cdefs_wt ws ds [] = True\<close>
| \<open>cdefs_wt ws ds (d # dd) = (cwt ws ds d \<and> cdefs_wt ws (ds @ [cwidth ws ds d]) dd)\<close>

text \<open>The widths of the definitions, appended to \<open>ds\<close>.\<close>
fun cdef_widths :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> CoreTerm list \<Rightarrow> nat list\<close> where
  \<open>cdef_widths ws ds [] = ds\<close>
| \<open>cdef_widths ws ds (d # dd) = cdef_widths ws (ds @ [cwidth ws ds d]) dd\<close>

text \<open>The values of the definitions, appended to \<open>dv\<close> (the values of definitions of widths \<open>ds\<close>), given
  the widths \<open>ws\<close> and values \<open>vs\<close> of the variables.\<close>
fun cdef_values :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> CoreTerm list \<Rightarrow> nat list\<close> where
  \<open>cdef_values ws ds vs dv [] = dv\<close>
| \<open>cdef_values ws ds vs dv (d # dd) =
     cdef_values ws (ds @ [cwidth ws ds d]) vs (dv @ [ceval ws ds vs dv d]) dd\<close>

definition cvar_widths :: \<open>CoreProblem \<Rightarrow> nat list\<close> where
  \<open>cvar_widths p \<equiv> map unat (CoreProblem_widths p)\<close>

text \<open>A well-sorted problem: well-sorted definitions and assertions of cwidth 1.\<close>
definition cproblem_wt :: \<open>CoreProblem \<Rightarrow> bool\<close> where
  \<open>cproblem_wt p \<equiv>
     let ws = cvar_widths p in
     let ds = cdef_widths ws [] (CoreProblem_defs p) in
     cdefs_wt ws [] (CoreProblem_defs p) \<and>
     (\<forall>t \<in> set (CoreProblem_asserts p). cwt ws ds t \<and> cwidth ws ds t = 1)\<close>

text \<open>An assignment gives every variable a bit list of its cwidth.\<close>
definition cis_assignment :: \<open>CoreProblem \<Rightarrow> bool list list \<Rightarrow> bool\<close> where
  \<open>cis_assignment p m \<equiv> map length m = cvar_widths p\<close>

text \<open>Every assertion evaluates to 1 under the assignment.\<close>
definition csatisfies :: \<open>CoreProblem \<Rightarrow> bool list list \<Rightarrow> bool\<close> where
  \<open>csatisfies p m \<equiv>
     let ws = cvar_widths p in
     let vs = map bits_nat m in
     let ds = cdef_widths ws [] (CoreProblem_defs p) in
     let dv = cdef_values ws [] vs [] (CoreProblem_defs p) in
     \<forall>t \<in> set (CoreProblem_asserts p). ceval ws ds vs dv t = 1\<close>

text \<open>A model is an assignment under which every assertion evaluates to 1.\<close>
definition cis_model :: \<open>CoreProblem \<Rightarrow> bool list list \<Rightarrow> bool\<close> where
  \<open>cis_model p m \<equiv> cis_assignment p m \<and> csatisfies p m\<close>

subsection \<open>The size of a problem\<close>

text \<open>The csubterms of a term, the term included.\<close>
primrec csubterms :: \<open>CoreTerm \<Rightarrow> CoreTerm list\<close> where
  \<open>csubterms (CoreTerm_Const bs) = [CoreTerm_Const bs]\<close>
| \<open>csubterms (CoreTerm_Var i) = [CoreTerm_Var i]\<close>
| \<open>csubterms (CoreTerm_Ref i) = [CoreTerm_Ref i]\<close>
| \<open>csubterms (CoreTerm_Not a) = CoreTerm_Not a # csubterms a\<close>
| \<open>csubterms (CoreTerm_Bin op a b) = CoreTerm_Bin op a b # csubterms a @ csubterms b\<close>
| \<open>csubterms (CoreTerm_Extract hi lo a) = CoreTerm_Extract hi lo a # csubterms a\<close>
| \<open>csubterms (CoreTerm_Ite c a b) = CoreTerm_Ite c a b # csubterms c @ csubterms a @ csubterms b\<close>

text \<open>The weight of a term: the sum over its csubterms (counted with multiplicity) of the square of
  the cwidth plus one. Widths are those given by \<^const>\<open>cwidth\<close>, so a \<^const>\<open>CoreTerm_Ref\<close> weighs by the
  cwidth of the definition it refers to, however large that is.\<close>
definition cterm_weight :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> CoreTerm \<Rightarrow> nat\<close> where
  \<open>cterm_weight ws ds t \<equiv> sum_list (map (\<lambda>u. (cwidth ws ds u + 1) ^ 2) (csubterms t))\<close>

text \<open>The size of a problem, as a bound on the work of the solver: one plus the sum of the widths of
  the variables, plus the numbers of variables, definitions and assertions, plus the weights of
  all definitions and assertions, times 1000. It is linear in the number of csubterms and
  quadratic in their widths. The solver needs a fuel (a bound on the iterations of each loop and
  on the depth of the recursion) and counters (of type \<^verbatim>\<open>usize\<close>) of this size.\<close>
definition csize_bound :: \<open>CoreProblem \<Rightarrow> nat\<close> where
  \<open>csize_bound p \<equiv>
     let ws = cvar_widths p in
     let ds = cdef_widths ws [] (CoreProblem_defs p) in
     1000 * (1 + sum_list ws + length ws + length (CoreProblem_defs p) + length (CoreProblem_asserts p) +
             sum_list (map (cterm_weight ws ds) (CoreProblem_defs p @ CoreProblem_asserts p)))\<close>

context QFBV_ctx
begin

subsection \<open>The contract\<close>

definition csolve_contract :: \<open>CoreProblem \<Rightarrow> ('s, Answer, 'abort) function_contract\<close> where
  \<open>csolve_contract p \<equiv>
     let pre = can_alloc_reference \<star> \<langle>cproblem_wt p\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>case r of
           Answer_Sat m \<Rightarrow> cis_model p m
         | Answer_Unsat \<Rightarrow> (\<forall>m. \<not> cis_model p m)\<rangle> in
     make_function_contract pre post\<close>

end

end
