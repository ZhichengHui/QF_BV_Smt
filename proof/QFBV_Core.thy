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

subsection \<open>The list views of the generated types\<close>

text \<open>As \<^typ>\<open>TermL\<close> and \<^typ>\<open>ProblemL\<close> for \<^typ>\<open>Term\<close> and \<^typ>\<open>Problem\<close>: the core
  language on lists, and the views of the generated values.\<close>

datatype CoreTermL =
    CoreTermL_Const \<open>bool list\<close>
  | CoreTermL_Var \<open>64 word\<close>
  | CoreTermL_Ref \<open>64 word\<close>
  | CoreTermL_Not CoreTermL
  | CoreTermL_Bin BinOp CoreTermL CoreTermL
  | CoreTermL_Extract \<open>64 word\<close> \<open>64 word\<close> CoreTermL
  | CoreTermL_Ite CoreTermL CoreTermL CoreTermL

datatype_record CoreProblemL =
  CoreProblemL_widths :: \<open>64 word list\<close>
  CoreProblemL_defs :: \<open>CoreTermL list\<close>
  CoreProblemL_asserts :: \<open>CoreTermL list\<close>

primrec ct_of :: \<open>CoreTerm \<Rightarrow> CoreTermL\<close> where
  \<open>ct_of (CoreTerm_Const bs) = CoreTermL_Const (rvec_elems bs)\<close>
| \<open>ct_of (CoreTerm_Var i) = CoreTermL_Var i\<close>
| \<open>ct_of (CoreTerm_Ref i) = CoreTermL_Ref i\<close>
| \<open>ct_of (CoreTerm_Not a) = CoreTermL_Not (ct_of a)\<close>
| \<open>ct_of (CoreTerm_Bin op a b) = CoreTermL_Bin op (ct_of a) (ct_of b)\<close>
| \<open>ct_of (CoreTerm_Extract hi lo a) = CoreTermL_Extract hi lo (ct_of a)\<close>
| \<open>ct_of (CoreTerm_Ite c a b) = CoreTermL_Ite (ct_of c) (ct_of a) (ct_of b)\<close>

definition cprob_of :: \<open>CoreProblem \<Rightarrow> CoreProblemL\<close> where
  \<open>cprob_of p \<equiv> make_CoreProblemL (rvec_elems (CoreProblem_widths p))
     (map ct_of (rvec_elems (CoreProblem_defs p))) (map ct_of (rvec_elems (CoreProblem_asserts p)))\<close>

lemma cprob_of_simps [simp]:
  \<open>CoreProblemL_widths (cprob_of p) = rvec_elems (CoreProblem_widths p)\<close>
  \<open>CoreProblemL_defs (cprob_of p) = map ct_of (rvec_elems (CoreProblem_defs p))\<close>
  \<open>CoreProblemL_asserts (cprob_of p) = map ct_of (rvec_elems (CoreProblem_asserts p))\<close>
  by (simp_all add: cprob_of_def)

subsection \<open>Sorts\<close>

text \<open>The cwidth of a term, given the widths \<open>ws\<close> of the variables and \<open>ds\<close> of the definitions.\<close>
fun cwidth :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> CoreTermL \<Rightarrow> nat\<close> where
  \<open>cwidth ws ds (CoreTermL_Const bs) = length bs\<close>
| \<open>cwidth ws ds (CoreTermL_Var i) = ws ! unat i\<close>
| \<open>cwidth ws ds (CoreTermL_Ref i) = ds ! unat i\<close>
| \<open>cwidth ws ds (CoreTermL_Not a) = cwidth ws ds a\<close>
| \<open>cwidth ws ds (CoreTermL_Bin op a b) =
     (case op of BinOp_Concat \<Rightarrow> cwidth ws ds a + cwidth ws ds b
               | BinOp_Eq \<Rightarrow> 1
               | BinOp_Ult \<Rightarrow> 1
               | _ \<Rightarrow> cwidth ws ds a)\<close>
| \<open>cwidth ws ds (CoreTermL_Extract hi lo a) = unat hi - unat lo + 1\<close>
| \<open>cwidth ws ds (CoreTermL_Ite c a b) = cwidth ws ds a\<close>

text \<open>Well-sortedness: indices in bounds, operands of equal widths (except for \<open>concat\<close>), the
  condition of \<open>ite\<close> of cwidth 1, and \<open>lo \<le> hi < w\<close> for \<open>extract\<close>.\<close>
fun cwt :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> CoreTermL \<Rightarrow> bool\<close> where
  \<open>cwt ws ds (CoreTermL_Const bs) = True\<close>
| \<open>cwt ws ds (CoreTermL_Var i) = (unat i < length ws)\<close>
| \<open>cwt ws ds (CoreTermL_Ref i) = (unat i < length ds)\<close>
| \<open>cwt ws ds (CoreTermL_Not a) = cwt ws ds a\<close>
| \<open>cwt ws ds (CoreTermL_Bin op a b) =
     (cwt ws ds a \<and> cwt ws ds b \<and> (op \<noteq> BinOp_Concat \<longrightarrow> cwidth ws ds a = cwidth ws ds b))\<close>
| \<open>cwt ws ds (CoreTermL_Extract hi lo a) = (cwt ws ds a \<and> unat lo \<le> unat hi \<and> unat hi < cwidth ws ds a)\<close>
| \<open>cwt ws ds (CoreTermL_Ite c a b) =
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
fun ceval :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> CoreTermL \<Rightarrow> nat\<close> where
  \<open>ceval ws ds vs dv (CoreTermL_Const bs) = bits_nat bs\<close>
| \<open>ceval ws ds vs dv (CoreTermL_Var i) = vs ! unat i\<close>
| \<open>ceval ws ds vs dv (CoreTermL_Ref i) = dv ! unat i\<close>
| \<open>ceval ws ds vs dv (CoreTermL_Not a) = 2 ^ cwidth ws ds a - 1 - ceval ws ds vs dv a\<close>
| \<open>ceval ws ds vs dv (CoreTermL_Bin op a b) =
     cbin_sem op (cwidth ws ds a) (ceval ws ds vs dv a) (cwidth ws ds b) (ceval ws ds vs dv b)\<close>
| \<open>ceval ws ds vs dv (CoreTermL_Extract hi lo a) =
     (ceval ws ds vs dv a div 2 ^ unat lo) mod 2 ^ (unat hi - unat lo + 1)\<close>
| \<open>ceval ws ds vs dv (CoreTermL_Ite c a b) =
     (if ceval ws ds vs dv c = 1 then ceval ws ds vs dv a else ceval ws ds vs dv b)\<close>

subsection \<open>Problems\<close>

text \<open>The definitions in order: each is well-sorted over the earlier ones.\<close>
fun cdefs_wt :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> CoreTermL list \<Rightarrow> bool\<close> where
  \<open>cdefs_wt ws ds [] = True\<close>
| \<open>cdefs_wt ws ds (d # dd) = (cwt ws ds d \<and> cdefs_wt ws (ds @ [cwidth ws ds d]) dd)\<close>

text \<open>The widths of the definitions, appended to \<open>ds\<close>.\<close>
fun cdef_widths :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> CoreTermL list \<Rightarrow> nat list\<close> where
  \<open>cdef_widths ws ds [] = ds\<close>
| \<open>cdef_widths ws ds (d # dd) = cdef_widths ws (ds @ [cwidth ws ds d]) dd\<close>

text \<open>The values of the definitions, appended to \<open>dv\<close> (the values of definitions of widths \<open>ds\<close>), given
  the widths \<open>ws\<close> and values \<open>vs\<close> of the variables.\<close>
fun cdef_values :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> CoreTermL list \<Rightarrow> nat list\<close> where
  \<open>cdef_values ws ds vs dv [] = dv\<close>
| \<open>cdef_values ws ds vs dv (d # dd) =
     cdef_values ws (ds @ [cwidth ws ds d]) vs (dv @ [ceval ws ds vs dv d]) dd\<close>

definition cvar_widths :: \<open>CoreProblemL \<Rightarrow> nat list\<close> where
  \<open>cvar_widths p \<equiv> map unat (CoreProblemL_widths p)\<close>

text \<open>A well-sorted problem: well-sorted definitions and assertions of cwidth 1.\<close>
definition cproblem_wt :: \<open>CoreProblemL \<Rightarrow> bool\<close> where
  \<open>cproblem_wt p \<equiv>
     let ws = cvar_widths p in
     let ds = cdef_widths ws [] (CoreProblemL_defs p) in
     cdefs_wt ws [] (CoreProblemL_defs p) \<and>
     (\<forall>t \<in> set (CoreProblemL_asserts p). cwt ws ds t \<and> cwidth ws ds t = 1)\<close>

text \<open>An assignment gives every variable a bit list of its cwidth.\<close>
definition cis_assignment :: \<open>CoreProblemL \<Rightarrow> bool list list \<Rightarrow> bool\<close> where
  \<open>cis_assignment p m \<equiv> map length m = cvar_widths p\<close>

text \<open>Every assertion evaluates to 1 under the assignment.\<close>
definition csatisfies :: \<open>CoreProblemL \<Rightarrow> bool list list \<Rightarrow> bool\<close> where
  \<open>csatisfies p m \<equiv>
     let ws = cvar_widths p in
     let vs = map bits_nat m in
     let ds = cdef_widths ws [] (CoreProblemL_defs p) in
     let dv = cdef_values ws [] vs [] (CoreProblemL_defs p) in
     \<forall>t \<in> set (CoreProblemL_asserts p). ceval ws ds vs dv t = 1\<close>

text \<open>A model is an assignment under which every assertion evaluates to 1.\<close>
definition cis_model :: \<open>CoreProblemL \<Rightarrow> bool list list \<Rightarrow> bool\<close> where
  \<open>cis_model p m \<equiv> cis_assignment p m \<and> csatisfies p m\<close>

subsection \<open>The size of a problem\<close>

text \<open>The csubterms of a term, the term included.\<close>
primrec csubterms :: \<open>CoreTermL \<Rightarrow> CoreTermL list\<close> where
  \<open>csubterms (CoreTermL_Const bs) = [CoreTermL_Const bs]\<close>
| \<open>csubterms (CoreTermL_Var i) = [CoreTermL_Var i]\<close>
| \<open>csubterms (CoreTermL_Ref i) = [CoreTermL_Ref i]\<close>
| \<open>csubterms (CoreTermL_Not a) = CoreTermL_Not a # csubterms a\<close>
| \<open>csubterms (CoreTermL_Bin op a b) = CoreTermL_Bin op a b # csubterms a @ csubterms b\<close>
| \<open>csubterms (CoreTermL_Extract hi lo a) = CoreTermL_Extract hi lo a # csubterms a\<close>
| \<open>csubterms (CoreTermL_Ite c a b) = CoreTermL_Ite c a b # csubterms c @ csubterms a @ csubterms b\<close>

text \<open>The weight of a term: the sum over its csubterms (counted with multiplicity) of the square of
  the cwidth plus one. Widths are those given by \<^const>\<open>cwidth\<close>, so a \<^const>\<open>CoreTermL_Ref\<close> weighs by the
  cwidth of the definition it refers to, however large that is.\<close>
definition cterm_weight :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> CoreTermL \<Rightarrow> nat\<close> where
  \<open>cterm_weight ws ds t \<equiv> sum_list (map (\<lambda>u. (cwidth ws ds u + 1) ^ 2) (csubterms t))\<close>

text \<open>The size of a problem, as a bound on the work of the solver: one plus the sum of the widths of
  the variables, plus the numbers of variables, definitions and assertions, plus the weights of
  all definitions and assertions, times 1000. It is linear in the number of csubterms and
  quadratic in their widths. The solver needs a fuel (a bound on the iterations of each loop and
  on the depth of the recursion) and counters (of type \<^verbatim>\<open>usize\<close>) of this size.\<close>
definition csize_bound :: \<open>CoreProblemL \<Rightarrow> nat\<close> where
  \<open>csize_bound p \<equiv>
     let ws = cvar_widths p in
     let ds = cdef_widths ws [] (CoreProblemL_defs p) in
     1000 * (1 + sum_list ws + length ws + length (CoreProblemL_defs p) + length (CoreProblemL_asserts p) +
             sum_list (map (cterm_weight ws ds) (CoreProblemL_defs p @ CoreProblemL_asserts p)))\<close>

context QFBV_ctx
begin

subsection \<open>The contract\<close>

definition csolve_contract :: \<open>CoreProblem \<Rightarrow> ('s, Answer, 'abort) function_contract\<close> where
  \<open>csolve_contract p \<equiv>
     let pre = can_alloc_reference \<star> \<langle>cproblem_wt (cprob_of p)\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>case r of
           Answer_Sat m \<Rightarrow> cis_model (cprob_of p) (vecs_of m)
         | Answer_Unsat \<Rightarrow> (\<forall>m. \<not> cis_model (cprob_of p) m)\<rangle> in
     make_function_contract pre post\<close>

end

end
