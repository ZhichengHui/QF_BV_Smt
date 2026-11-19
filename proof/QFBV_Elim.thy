theory QFBV_Elim
  imports QFBV_Eval QFBV_LowerBound
begin

section \<open>Elimination of unconstrained definitions\<close>

text \<open>
  \<^verbatim>\<open>elim\<close> rewrites the free definitions of a core problem to the low bits of the operand they
  consume and replaces the definitions that are no longer reachable from the assertions by
  constants; \<^verbatim>\<open>reconstruct\<close> turns a model of the result into a model of the problem. This theory
  gives the functional models of these functions and of their helpers and proves: the result is
  well-sorted, has the same variables, definition widths and assertions, and no term of it is
  larger (\<^const>\<open>cterm_weight\<close>, \<^const>\<open>ccount\<close>, \<^const>\<open>tbound\<close>); a model of the problem gives a model
  of the result; and the reconstructed assignment is a model of the problem whenever the
  assignment of the result is one.
\<close>

subsection \<open>Functional models\<close>

definition bump_m :: \<open>nat list \<Rightarrow> nat \<Rightarrow> nat list\<close> where
  \<open>bump_m c i \<equiv> if c ! i < 2 then c[i := Suc (c ! i)] else c\<close>

primrec count_occ_m :: \<open>nat list \<times> nat list \<Rightarrow> CoreTerm \<Rightarrow> nat list \<times> nat list\<close> where
  \<open>count_occ_m vr (CoreTerm_Const bs) = vr\<close>
| \<open>count_occ_m vr (CoreTerm_Var i) = (bump_m (fst vr) (unat i), snd vr)\<close>
| \<open>count_occ_m vr (CoreTerm_Ref i) = (fst vr, bump_m (snd vr) (unat i))\<close>
| \<open>count_occ_m vr (CoreTerm_Not a) = count_occ_m vr a\<close>
| \<open>count_occ_m vr (CoreTerm_Bin op a b) = count_occ_m (count_occ_m vr a) b\<close>
| \<open>count_occ_m vr (CoreTerm_Extract hi lo a) = count_occ_m vr a\<close>
| \<open>count_occ_m vr (CoreTerm_Ite c a b) = count_occ_m (count_occ_m (count_occ_m vr c) a) b\<close>

definition ref_index_m :: \<open>CoreTerm \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>ref_index_m t n \<equiv> (case t of CoreTerm_Ref i \<Rightarrow> unat i | _ \<Rightarrow> n)\<close>

definition bit_const_m :: \<open>CoreTerm \<Rightarrow> nat\<close> where
  \<open>bit_const_m t \<equiv> (case t of
     CoreTerm_Const bs \<Rightarrow> if length bs = 1 then (if bs ! 0 then 1 else 0) else 2
   | _ \<Rightarrow> 2)\<close>

definition free_once_m :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>free_once_m kind rc i \<equiv> i < length kind \<and> kind ! i \<noteq> 0 \<and> rc ! i = 1\<close>

definition free_kind_m :: \<open>CoreTerm list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> CoreTerm \<Rightarrow> nat\<close> where
  \<open>free_kind_m defs dw vc rc kind t \<equiv>
     let n = length kind in
     (case t of
        CoreTerm_Var i \<Rightarrow> if vc ! unat i = 1 then 1 else 0
      | CoreTerm_Not a \<Rightarrow> if free_once_m kind rc (ref_index_m a n) then 2 else 0
      | CoreTerm_Extract hi lo a \<Rightarrow> if free_once_m kind rc (ref_index_m a n) then 2 else 0
      | CoreTerm_Bin op a b \<Rightarrow>
          (let ia = ref_index_m a n; ib = ref_index_m b n in
           case op of
             BinOp_Add \<Rightarrow> if free_once_m kind rc ia then 2 else if free_once_m kind rc ib then 3 else 0
           | BinOp_Xor \<Rightarrow> if free_once_m kind rc ia then 2 else if free_once_m kind rc ib then 3 else 0
           | BinOp_Eq \<Rightarrow> if free_once_m kind rc ia \<and> 0 < dw ! ia then 2
                        else if free_once_m kind rc ib \<and> 0 < dw ! ib then 3 else 0
           | BinOp_Mul \<Rightarrow> if free_once_m kind rc ia \<and> free_once_m kind rc ib \<and> ia \<noteq> ib then 4 else 0
           | BinOp_Udiv \<Rightarrow> if free_once_m kind rc ia \<and> free_once_m kind rc ib \<and> ia \<noteq> ib then 4 else 0
           | _ \<Rightarrow> 0)
      | CoreTerm_Ite c a b \<Rightarrow>
          (let ic = ref_index_m c n; ia = ref_index_m a n; ib = ref_index_m b n in
           if free_once_m kind rc ic \<and> ia < n \<and> ib < n then
             (let x = bit_const_m (defs ! ia); y = bit_const_m (defs ! ib) in
              if x < 2 \<and> y < 2 \<and> x \<noteq> y then 2 else 0)
           else 0)
      | _ \<Rightarrow> 0)\<close>

definition consumed_m :: \<open>CoreTerm \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>consumed_m t k n \<equiv> (case t of
     CoreTerm_Not a \<Rightarrow> ref_index_m a n
   | CoreTerm_Extract hi lo a \<Rightarrow> ref_index_m a n
   | CoreTerm_Bin op a b \<Rightarrow> if k = 3 then ref_index_m b n else ref_index_m a n
   | CoreTerm_Ite c a b \<Rightarrow> ref_index_m c n
   | _ \<Rightarrow> n)\<close>

definition second_m :: \<open>CoreTerm \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>second_m t n \<equiv> (case t of CoreTerm_Bin op a b \<Rightarrow> ref_index_m b n | _ \<Rightarrow> n)\<close>

primrec mark_live_m :: \<open>bool list \<Rightarrow> CoreTerm \<Rightarrow> bool list\<close> where
  \<open>mark_live_m live (CoreTerm_Const bs) = live\<close>
| \<open>mark_live_m live (CoreTerm_Var i) = live\<close>
| \<open>mark_live_m live (CoreTerm_Ref i) = live[unat i := True]\<close>
| \<open>mark_live_m live (CoreTerm_Not a) = mark_live_m live a\<close>
| \<open>mark_live_m live (CoreTerm_Bin op a b) = mark_live_m (mark_live_m live a) b\<close>
| \<open>mark_live_m live (CoreTerm_Extract hi lo a) = mark_live_m live a\<close>
| \<open>mark_live_m live (CoreTerm_Ite c a b) = mark_live_m (mark_live_m (mark_live_m live c) a) b\<close>

text \<open>The rewritten definition: the consumed operand \<open>a\<close>, or its low bits.\<close>
definition rewrite_m :: \<open>nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> CoreTerm\<close> where
  \<open>rewrite_m dw a w \<equiv>
     if dw ! a = w then CoreTerm_Ref (word_of_nat a)
     else CoreTerm_Extract (word_of_nat (w - 1)) 0 (CoreTerm_Ref (word_of_nat a))\<close>

text \<open>One step of the analysis loop: the width, the kind and the rewritten term of definition \<open>k\<close>,
  and the marks of its operands.\<close>
definition elim_step :: \<open>nat list \<Rightarrow> CoreTerm list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    nat list \<times> nat list \<times> nat list \<times> CoreTerm list \<Rightarrow> nat \<Rightarrow> nat list \<times> nat list \<times> nat list \<times> CoreTerm list\<close> where
  \<open>elim_step ws D vc rc st k \<equiv>
     (case st of (dw, kind, mark, defs) \<Rightarrow>
       let n = length D; t = D ! k; w = cwidth ws dw t; c = free_kind_m D dw vc rc kind t in
       if 2 \<le> c then
         (let a = consumed_m t c n;
              mark1 = mark[a := 1];
              mark2 = (if c = 4 then mark1[second_m t n := 2] else mark1) in
          (dw @ [w], kind @ [c], mark2, defs @ [rewrite_m dw a w]))
       else (dw @ [w], kind @ [c], mark, defs @ [t]))\<close>

text \<open>One step of the backward loop: a live definition marks its operands live, any other one
  becomes the constant zero of its width.\<close>
definition dce_step :: \<open>nat list \<Rightarrow> bool list \<times> CoreTerm list \<Rightarrow> nat \<Rightarrow> bool list \<times> CoreTerm list\<close> where
  \<open>dce_step dw st d \<equiv>
     (case st of (live, defs) \<Rightarrow>
       if live ! d then (mark_live_m live (defs ! d), defs)
       else (live, defs[d := CoreTerm_Const (replicate (dw ! d) False)]))\<close>

definition occ_res :: \<open>CoreProblem \<Rightarrow> nat list \<times> nat list\<close> where
  \<open>occ_res q \<equiv> foldl count_occ_m (replicate (length (CoreProblem_widths q)) 0, replicate (length (CoreProblem_defs q)) 0)
     (CoreProblem_defs q @ CoreProblem_asserts q)\<close>

definition ana_res :: \<open>CoreProblem \<Rightarrow> nat list \<times> nat list \<times> nat list \<times> CoreTerm list\<close> where
  \<open>ana_res q \<equiv>
     let D = CoreProblem_defs q in
     foldl (elim_step (cvar_widths q) D (fst (occ_res q)) (snd (occ_res q)))
       ([], [], replicate (length D) 0, []) [0..<length D]\<close>

definition dce_res :: \<open>CoreProblem \<Rightarrow> bool list \<times> CoreTerm list\<close> where
  \<open>dce_res q \<equiv>
     let D = CoreProblem_defs q; (dw, kind, mark, defs) = ana_res q in
     foldl (dce_step dw) (foldl mark_live_m (replicate (length D) False) (CoreProblem_asserts q), defs)
       (rev [0..<length D])\<close>

definition elim_m :: \<open>CoreProblem \<Rightarrow> CoreProblem \<times> nat list \<times> nat list\<close> where
  \<open>elim_m q \<equiv>
     (make_CoreProblem (CoreProblem_widths q) (snd (dce_res q)) (CoreProblem_asserts q),
      fst (snd (ana_res q)), fst (snd (snd (ana_res q))))\<close>

definition bits_one_m :: \<open>nat \<Rightarrow> bool list\<close> where
  \<open>bits_one_m w \<equiv> if 0 < w then (replicate w False)[0 := True] else replicate w False\<close>

definition invert_m :: \<open>CoreTerm \<Rightarrow> nat \<Rightarrow> bool list \<Rightarrow> bool list list \<Rightarrow> bool list list \<Rightarrow> bool list list \<Rightarrow> nat \<times> bool list\<close> where
  \<open>invert_m t k v m dv dv2 \<equiv>
     let n = length dv2 in
     (case t of
        CoreTerm_Not a \<Rightarrow> (ref_index_m a n, bnot_m v)
      | CoreTerm_Extract hi lo a \<Rightarrow>
          (let ia = ref_index_m a n; w = length (dv2 ! ia) in
           (ia, bconcat_m (replicate (w - 1 - unat hi) False) (bconcat_m v (replicate (unat lo) False))))
      | CoreTerm_Bin op a b \<Rightarrow>
          (let ic = (if k = 3 then ref_index_m b n else ref_index_m a n);
               ov = (if k = 3 then eval_m m dv a else eval_m m dv b) in
           case op of
             BinOp_Add \<Rightarrow> (ic, fst (badd_m v (bnot_m ov) True))
           | BinOp_Xor \<Rightarrow> (ic, bbitw_m op v ov)
           | BinOp_Eq \<Rightarrow> (ic, if v ! 0 then ov else bnot_m ov)
           | _ \<Rightarrow> (ic, v))
      | CoreTerm_Ite c a b \<Rightarrow> (ref_index_m c n, [beq_m v (dv ! ref_index_m a n)])
      | _ \<Rightarrow> (n, v))\<close>

definition var_index_m :: \<open>CoreTerm \<Rightarrow> nat\<close> where
  \<open>var_index_m t \<equiv> (case t of CoreTerm_Var i \<Rightarrow> unat i | _ \<Rightarrow> 0)\<close>

text \<open>The loop of \<^verbatim>\<open>settle\<close>, with at most \<open>f\<close> iterations left.\<close>
fun settle_m :: \<open>CoreTerm list \<Rightarrow> nat list \<Rightarrow> bool list list \<Rightarrow> nat \<Rightarrow> bool list list \<Rightarrow> bool list list \<Rightarrow>
    nat \<Rightarrow> bool list \<Rightarrow> bool list list \<times> bool list list\<close> where
  \<open>settle_m D kind dv2 0 dv m j v = (dv, m)\<close>
| \<open>settle_m D kind dv2 (Suc f) dv m j v =
     (let dv' = dv[j := v] in
      if kind ! j = 1 then (dv', m[var_index_m (D ! j) := v])
      else (case invert_m (D ! j) (kind ! j) v m dv' dv2 of (a, va) \<Rightarrow> settle_m D kind dv2 f dv' m a va))\<close>

definition recon_step :: \<open>CoreTerm list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool list list \<Rightarrow>
    bool list list \<times> bool list list \<Rightarrow> nat \<Rightarrow> bool list list \<times> bool list list\<close> where
  \<open>recon_step D kind mark dv2 st k \<equiv>
     (case st of (dv, m) \<Rightarrow>
       if mark ! k = 1 then (dv @ [[]], m)
       else if kind ! k = 0 then (dv @ [eval_m m dv (D ! k)], m)
       else settle_m D kind dv2 (Suc k) (dv @ [[]]) m k
              (if mark ! k = 2 then bits_one_m (length (dv2 ! k)) else dv2 ! k))\<close>

definition reconstruct_m :: \<open>CoreProblem \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> CoreProblem \<Rightarrow> bool list list \<Rightarrow> bool list list\<close> where
  \<open>reconstruct_m q kind mark q2 m2 \<equiv>
     snd (foldl (recon_step (CoreProblem_defs q) kind mark (eval_defs_m q2 m2)) ([], m2) [0..<length (CoreProblem_defs q)])\<close>

subsection \<open>Occurrence counts\<close>

definition is_var :: \<open>nat \<Rightarrow> CoreTerm \<Rightarrow> bool\<close> where
  \<open>is_var x u \<equiv> (case u of CoreTerm_Var i \<Rightarrow> unat i = x | _ \<Rightarrow> False)\<close>

definition is_ref :: \<open>nat \<Rightarrow> CoreTerm \<Rightarrow> bool\<close> where
  \<open>is_ref x u \<equiv> (case u of CoreTerm_Ref i \<Rightarrow> unat i = x | _ \<Rightarrow> False)\<close>

text \<open>The numbers of occurrences of variable \<open>x\<close> and of definition \<open>x\<close> in the terms \<open>ts\<close>.\<close>
definition vcnt :: \<open>CoreTerm list \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>vcnt ts x \<equiv> length (filter (is_var x) (concat (map csubterms ts)))\<close>

definition rcnt :: \<open>CoreTerm list \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>rcnt ts x \<equiv> length (filter (is_ref x) (concat (map csubterms ts)))\<close>

lemma vcnt_simps [simp]:
  \<open>vcnt [] x = 0\<close> \<open>vcnt (ts @ us) x = vcnt ts x + vcnt us x\<close>
  by (simp_all add: vcnt_def)

lemma vcnt_Cons: \<open>vcnt (t # ts) x = vcnt [t] x + vcnt ts x\<close>
  by (simp add: vcnt_def)

lemma rcnt_simps [simp]:
  \<open>rcnt [] x = 0\<close> \<open>rcnt (ts @ us) x = rcnt ts x + rcnt us x\<close>
  by (simp_all add: rcnt_def)

lemma rcnt_Cons: \<open>rcnt (t # ts) x = rcnt [t] x + rcnt ts x\<close>
  by (simp add: rcnt_def)

lemma length_bump [simp]: \<open>length (bump_m c i) = length c\<close>
  by (simp add: bump_m_def)

lemma length_count_occ [simp]:
  \<open>length (fst (count_occ_m vr t)) = length (fst vr)\<close> \<open>length (snd (count_occ_m vr t)) = length (snd vr)\<close>
  by (induction t arbitrary: vr) simp_all

lemma count_occ_fst:
  assumes \<open>x < length (fst vr)\<close> \<open>fst vr ! x \<le> 2\<close>
  shows \<open>fst (count_occ_m vr t) ! x = min 2 (fst vr ! x + vcnt [t] x)\<close>
  using assms
proof (induction t arbitrary: vr)
  case (CoreTerm_Var i)
  then show ?case by (auto simp add: bump_m_def vcnt_def is_var_def nth_list_update)
next
  case (CoreTerm_Bin op a b)
  have \<open>fst (count_occ_m vr a) ! x \<le> 2\<close> using CoreTerm_Bin.IH(1)[OF CoreTerm_Bin.prems] by simp
  then show ?case using CoreTerm_Bin by (simp add: vcnt_def is_var_def)
next
  case (CoreTerm_Ite c a b)
  have \<open>fst (count_occ_m vr c) ! x \<le> 2\<close> using CoreTerm_Ite.IH(1)[OF CoreTerm_Ite.prems] by simp
  moreover have \<open>fst (count_occ_m (count_occ_m vr c) a) ! x \<le> 2\<close>
    using CoreTerm_Ite.IH(2)[OF _ calculation] CoreTerm_Ite.prems by simp
  ultimately show ?case using CoreTerm_Ite by (simp add: vcnt_def is_var_def)
qed (simp_all add: vcnt_def is_var_def)

lemma count_occ_snd:
  assumes \<open>x < length (snd vr)\<close> \<open>snd vr ! x \<le> 2\<close>
  shows \<open>snd (count_occ_m vr t) ! x = min 2 (snd vr ! x + rcnt [t] x)\<close>
  using assms
proof (induction t arbitrary: vr)
  case (CoreTerm_Ref i)
  then show ?case by (auto simp add: bump_m_def rcnt_def is_ref_def nth_list_update)
next
  case (CoreTerm_Bin op a b)
  have \<open>snd (count_occ_m vr a) ! x \<le> 2\<close> using CoreTerm_Bin.IH(1)[OF CoreTerm_Bin.prems] by simp
  then show ?case using CoreTerm_Bin by (simp add: rcnt_def is_ref_def)
next
  case (CoreTerm_Ite c a b)
  have \<open>snd (count_occ_m vr c) ! x \<le> 2\<close> using CoreTerm_Ite.IH(1)[OF CoreTerm_Ite.prems] by simp
  moreover have \<open>snd (count_occ_m (count_occ_m vr c) a) ! x \<le> 2\<close>
    using CoreTerm_Ite.IH(2)[OF _ calculation] CoreTerm_Ite.prems by simp
  ultimately show ?case using CoreTerm_Ite by (simp add: rcnt_def is_ref_def)
qed (simp_all add: rcnt_def is_ref_def)

lemma count_occ_fold:
  shows \<open>length (fst (foldl count_occ_m vr ts)) = length (fst vr) \<and> length (snd (foldl count_occ_m vr ts)) = length (snd vr) \<and>
    (\<forall>x < length (fst vr). fst vr ! x \<le> 2 \<longrightarrow> fst (foldl count_occ_m vr ts) ! x = min 2 (fst vr ! x + vcnt ts x)) \<and>
    (\<forall>x < length (snd vr). snd vr ! x \<le> 2 \<longrightarrow> snd (foldl count_occ_m vr ts) ! x = min 2 (snd vr ! x + rcnt ts x))\<close>
proof (induction ts arbitrary: vr)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  note IH = Cons.IH[of \<open>count_occ_m vr t\<close>]
  show ?case using IH count_occ_fst[of _ vr t] count_occ_snd[of _ vr t] vcnt_Cons[of t ts] rcnt_Cons[of t ts] by auto
qed

lemma occ_res:
  shows \<open>length (fst (occ_res q)) = length (CoreProblem_widths q)\<close> \<open>length (snd (occ_res q)) = length (CoreProblem_defs q)\<close>
    \<open>x < length (CoreProblem_widths q) \<Longrightarrow> fst (occ_res q) ! x = min 2 (vcnt (CoreProblem_defs q @ CoreProblem_asserts q) x)\<close>
    \<open>j < length (CoreProblem_defs q) \<Longrightarrow> snd (occ_res q) ! j = min 2 (rcnt (CoreProblem_defs q @ CoreProblem_asserts q) j)\<close>
  using count_occ_fold[of \<open>(replicate (length (CoreProblem_widths q)) 0, replicate (length (CoreProblem_defs q)) 0)\<close>
      \<open>CoreProblem_defs q @ CoreProblem_asserts q\<close>]
  by (simp_all add: occ_res_def del: vcnt_simps rcnt_simps)

subsection \<open>The analysis loop\<close>

lemma ana_fold:
  assumes \<open>k \<le> length D\<close>
    \<open>foldl (elim_step ws D vc rc) ([], [], replicate (length D) 0, []) [0..<k] = (dw, kind, mark, defs)\<close>
  shows \<open>dw = cdef_widths ws [] (take k D) \<and> length kind = k \<and> length mark = length D \<and> length defs = k \<and>
    (\<forall>i<k. kind ! i = free_kind_m D (take i dw) vc rc (take i kind) (D ! i) \<and>
       defs ! i = (if 2 \<le> kind ! i then rewrite_m (take i dw) (consumed_m (D ! i) (kind ! i) (length D)) (dw ! i)
                   else D ! i))\<close>
  using assms
proof (induction k arbitrary: dw kind mark defs)
  case 0
  then show ?case by auto
next
  case (Suc k)
  obtain dw0 kind0 mark0 defs0 where s0:
    \<open>foldl (elim_step ws D vc rc) ([], [], replicate (length D) 0, []) [0..<k] = (dw0, kind0, mark0, defs0)\<close>
    by (cases \<open>foldl (elim_step ws D vc rc) ([], [], replicate (length D) 0, []) [0..<k]\<close>)
  have IH: \<open>dw0 = cdef_widths ws [] (take k D) \<and> length kind0 = k \<and> length mark0 = length D \<and> length defs0 = k \<and>
    (\<forall>i<k. kind0 ! i = free_kind_m D (take i dw0) vc rc (take i kind0) (D ! i) \<and>
       defs0 ! i = (if 2 \<le> kind0 ! i then rewrite_m (take i dw0) (consumed_m (D ! i) (kind0 ! i) (length D)) (dw0 ! i)
                   else D ! i))\<close>
    using Suc.IH[OF _ s0] Suc.prems(1) by simp
  have st: \<open>elim_step ws D vc rc (dw0, kind0, mark0, defs0) k = (dw, kind, mark, defs)\<close>
    using Suc.prems(2) s0 by simp
  have lk: \<open>length dw0 = k\<close> using IH Suc.prems(1) by (simp add: cdef_widths_length min_def)
  have cw: \<open>cdef_widths ws [] (take (Suc k) D) = dw0 @ [cwidth ws dw0 (D ! k)]\<close>
    using IH Suc.prems(1) by (simp add: take_Suc_conv_app_nth cdef_widths_append)
  show ?case
  proof -
    let ?c = \<open>free_kind_m D dw0 vc rc kind0 (D ! k)\<close>
    have e: \<open>dw = dw0 @ [cwidth ws dw0 (D ! k)] \<and> kind = kind0 @ [?c] \<and> length mark = length D \<and>
      defs = defs0 @ [if 2 \<le> ?c then rewrite_m dw0 (consumed_m (D ! k) ?c (length D)) (cwidth ws dw0 (D ! k)) else D ! k]\<close>
      using st IH by (auto simp: elim_step_def Let_def split: if_splits)
    have A: \<open>\<forall>i<Suc k. kind ! i = free_kind_m D (take i dw) vc rc (take i kind) (D ! i) \<and>
       defs ! i = (if 2 \<le> kind ! i then rewrite_m (take i dw) (consumed_m (D ! i) (kind ! i) (length D)) (dw ! i) else D ! i)\<close>
    proof (intro allI impI)
      fix i assume i: \<open>i < Suc k\<close>
      show \<open>kind ! i = free_kind_m D (take i dw) vc rc (take i kind) (D ! i) \<and>
       defs ! i = (if 2 \<le> kind ! i then rewrite_m (take i dw) (consumed_m (D ! i) (kind ! i) (length D)) (dw ! i) else D ! i)\<close>
      proof (cases \<open>i < k\<close>)
        case True
        then show ?thesis using IH e lk by (simp add: nth_append)
      next
        case False
        then have \<open>i = k\<close> using i by simp
        then show ?thesis using IH e lk by (simp add: nth_append)
      qed
    qed
    show ?thesis using e IH cw lk A by simp
  qed
qed

lemma fo_ref:
  assumes \<open>free_once_m kind rc (ref_index_m a (length kind))\<close>
  shows \<open>\<exists>i. a = CoreTerm_Ref i \<and> free_once_m kind rc (unat i)\<close>
  using assms by (cases a) (simp_all add: ref_index_m_def free_once_m_def)

lemma fo_ref_eq: \<open>free_once_m kind rc (ref_index_m a (length kind)) \<Longrightarrow> length kind \<le> N \<Longrightarrow>
    ref_index_m a N = ref_index_m a (length kind)\<close>
  by (cases a) (simp_all add: ref_index_m_def free_once_m_def)

lemma free_kind_le: \<open>free_kind_m D dw vc rc kind t \<le> 4\<close>
  unfolding free_kind_m_def Let_def by (cases t) (auto split: BinOp_split)

lemma free_kind_simps:
  \<open>free_kind_m D dw vc rc kind (CoreTerm_Const bs) = 0\<close>
  \<open>free_kind_m D dw vc rc kind (CoreTerm_Var i) = (if vc ! unat i = 1 then 1 else 0)\<close>
  \<open>free_kind_m D dw vc rc kind (CoreTerm_Ref i) = 0\<close>
  \<open>free_kind_m D dw vc rc kind (CoreTerm_Not a) =
     (if free_once_m kind rc (ref_index_m a (length kind)) then 2 else 0)\<close>
  \<open>free_kind_m D dw vc rc kind (CoreTerm_Extract hi lo a) =
     (if free_once_m kind rc (ref_index_m a (length kind)) then 2 else 0)\<close>
  \<open>free_kind_m D dw vc rc kind (CoreTerm_Ite x a b) =
     (if free_once_m kind rc (ref_index_m x (length kind)) \<and> ref_index_m a (length kind) < length kind \<and>
         ref_index_m b (length kind) < length kind \<and>
         bit_const_m (D ! ref_index_m a (length kind)) < 2 \<and> bit_const_m (D ! ref_index_m b (length kind)) < 2 \<and>
         bit_const_m (D ! ref_index_m a (length kind)) \<noteq> bit_const_m (D ! ref_index_m b (length kind))
      then 2 else 0)\<close>
  by (simp_all add: free_kind_m_def Let_def)

lemma free_kind_Bin:
  \<open>free_kind_m D dw vc rc kind (CoreTerm_Bin op a b) =
     (let ia = ref_index_m a (length kind); ib = ref_index_m b (length kind); fo = free_once_m kind rc in
      if op = BinOp_Add \<or> op = BinOp_Xor then (if fo ia then 2 else if fo ib then 3 else 0)
      else if op = BinOp_Eq then (if fo ia \<and> 0 < dw ! ia then 2 else if fo ib \<and> 0 < dw ! ib then 3 else 0)
      else if op = BinOp_Mul \<or> op = BinOp_Udiv then (if fo ia \<and> fo ib \<and> ia \<noteq> ib then 4 else 0)
      else 0)\<close>
  by (cases op) (simp_all add: free_kind_m_def Let_def)

lemma free_kind_1:
  assumes h: \<open>free_kind_m D dw vc rc kind t = 1\<close>
  shows \<open>\<exists>i. t = CoreTerm_Var i \<and> vc ! unat i = 1\<close>
proof (cases t)
  case (CoreTerm_Bin op a b)
  have \<open>free_kind_m D dw vc rc kind t \<in> {0, 2, 3, 4}\<close> unfolding CoreTerm_Bin free_kind_Bin Let_def by simp
  then show ?thesis using h by simp
next
  case (CoreTerm_Ite x a b)
  have \<open>free_kind_m D dw vc rc kind t \<in> {0, 2}\<close> unfolding CoreTerm_Ite free_kind_simps by simp
  then show ?thesis using h by simp
next
  case (CoreTerm_Not a)
  have \<open>free_kind_m D dw vc rc kind t \<in> {0, 2}\<close> unfolding CoreTerm_Not free_kind_simps by simp
  then show ?thesis using h by simp
next
  case (CoreTerm_Extract hi lo a)
  have \<open>free_kind_m D dw vc rc kind t \<in> {0, 2}\<close> unfolding CoreTerm_Extract free_kind_simps by simp
  then show ?thesis using h by simp
next
  case (CoreTerm_Const bs)
  then show ?thesis using h by (simp only: free_kind_simps)
next
  case (CoreTerm_Ref i)
  then show ?thesis using h by (simp only: free_kind_simps)
next
  case (CoreTerm_Var i)
  have \<open>(if vc ! unat i = 1 then 1 else 0) = (1::nat)\<close> using h free_kind_simps(2)[of D dw vc rc kind i] CoreTerm_Var by simp
  then have \<open>vc ! unat i = 1\<close> by (cases \<open>vc ! unat i = 1\<close>) simp_all
  then show ?thesis using CoreTerm_Var by blast
qed

text \<open>The free definitions of kind 2 to 4, by their shapes.\<close>
lemma free_kind_shape:
  assumes \<open>c = free_kind_m D dw vc rc kind t\<close> \<open>2 \<le> c\<close>
  shows \<open>(\<exists>a. t = CoreTerm_Not (CoreTerm_Ref a) \<and> c = 2 \<and> free_once_m kind rc (unat a))
    \<or> (\<exists>hi lo a. t = CoreTerm_Extract hi lo (CoreTerm_Ref a) \<and> c = 2 \<and> free_once_m kind rc (unat a))
    \<or> (\<exists>op a b. t = CoreTerm_Bin op a b \<and> (op = BinOp_Add \<or> op = BinOp_Xor) \<and>
         (c = 2 \<and> (\<exists>i. a = CoreTerm_Ref i \<and> free_once_m kind rc (unat i)) \<or>
          c = 3 \<and> (\<exists>i. b = CoreTerm_Ref i \<and> free_once_m kind rc (unat i))))
    \<or> (\<exists>a b. t = CoreTerm_Bin BinOp_Eq a b \<and>
         (c = 2 \<and> (\<exists>i. a = CoreTerm_Ref i \<and> free_once_m kind rc (unat i) \<and> 0 < dw ! unat i) \<or>
          c = 3 \<and> (\<exists>i. b = CoreTerm_Ref i \<and> free_once_m kind rc (unat i) \<and> 0 < dw ! unat i)))
    \<or> (\<exists>op a b. t = CoreTerm_Bin op (CoreTerm_Ref a) (CoreTerm_Ref b) \<and> (op = BinOp_Mul \<or> op = BinOp_Udiv) \<and> c = 4 \<and>
         free_once_m kind rc (unat a) \<and> free_once_m kind rc (unat b) \<and> unat a \<noteq> unat b)
    \<or> (\<exists>x a b. t = CoreTerm_Ite (CoreTerm_Ref x) (CoreTerm_Ref a) (CoreTerm_Ref b) \<and> c = 2 \<and>
         free_once_m kind rc (unat x) \<and> unat a < length kind \<and> unat b < length kind \<and>
         bit_const_m (D ! unat a) < 2 \<and> bit_const_m (D ! unat b) < 2 \<and> bit_const_m (D ! unat a) \<noteq> bit_const_m (D ! unat b))\<close>
proof -
  let ?fo = \<open>free_once_m kind rc\<close> and ?n = \<open>length kind\<close>
  have ri: \<open>ref_index_m a ?n < ?n \<Longrightarrow> \<exists>i. a = CoreTerm_Ref i \<and> unat i = ref_index_m a ?n\<close> for a
    by (cases a) (simp_all add: ref_index_m_def)
  show ?thesis
  proof (cases t)
    case (CoreTerm_Not a)
    then have fo: \<open>?fo (ref_index_m a ?n)\<close> and c: \<open>c = 2\<close>
      using assms unfolding CoreTerm_Not free_kind_simps by (simp_all split: if_splits)
    obtain i where i: \<open>a = CoreTerm_Ref i\<close> \<open>?fo (unat i)\<close> using fo_ref[OF fo] by blast
    show ?thesis using CoreTerm_Not i c by simp
  next
    case (CoreTerm_Extract hi lo a)
    then have fo: \<open>?fo (ref_index_m a ?n)\<close> and c: \<open>c = 2\<close>
      using assms unfolding CoreTerm_Extract free_kind_simps by (simp_all split: if_splits)
    obtain i where i: \<open>a = CoreTerm_Ref i\<close> \<open>?fo (unat i)\<close> using fo_ref[OF fo] by blast
    show ?thesis using CoreTerm_Extract i c by simp
  next
    case (CoreTerm_Ite x a b)
    then have fo: \<open>?fo (ref_index_m x ?n)\<close> and c: \<open>c = 2\<close>
      and ia: \<open>ref_index_m a ?n < ?n\<close> and ib: \<open>ref_index_m b ?n < ?n\<close>
      and bc: \<open>bit_const_m (D ! ref_index_m a ?n) < 2\<close> \<open>bit_const_m (D ! ref_index_m b ?n) < 2\<close>
        \<open>bit_const_m (D ! ref_index_m a ?n) \<noteq> bit_const_m (D ! ref_index_m b ?n)\<close>
      using assms unfolding CoreTerm_Ite free_kind_simps by (simp_all split: if_splits)
    obtain ix where x: \<open>x = CoreTerm_Ref ix\<close> \<open>?fo (unat ix)\<close> using fo_ref[OF fo] by blast
    obtain i where i: \<open>a = CoreTerm_Ref i\<close> \<open>unat i = ref_index_m a ?n\<close> using ri[OF ia] by blast
    obtain j where j: \<open>b = CoreTerm_Ref j\<close> \<open>unat j = ref_index_m b ?n\<close> using ri[OF ib] by blast
    show ?thesis using CoreTerm_Ite x i j c ia ib bc by auto
  next
    case (CoreTerm_Bin op a b)
    let ?ia = \<open>ref_index_m a ?n\<close> and ?ib = \<open>ref_index_m b ?n\<close>
    have cv: \<open>c = (if op = BinOp_Add \<or> op = BinOp_Xor then (if ?fo ?ia then 2 else if ?fo ?ib then 3 else 0)
      else if op = BinOp_Eq then (if ?fo ?ia \<and> 0 < dw ! ?ia then 2 else if ?fo ?ib \<and> 0 < dw ! ?ib then 3 else 0)
      else if op = BinOp_Mul \<or> op = BinOp_Udiv then (if ?fo ?ia \<and> ?fo ?ib \<and> ?ia \<noteq> ?ib then 4 else 0)
      else 0)\<close>
      using assms(1) unfolding CoreTerm_Bin free_kind_Bin Let_def .
    consider (ax) \<open>op = BinOp_Add \<or> op = BinOp_Xor\<close> | (eq) \<open>op = BinOp_Eq\<close> | (md) \<open>op = BinOp_Mul \<or> op = BinOp_Udiv\<close>
      | (other) \<open>\<not> (op = BinOp_Add \<or> op = BinOp_Xor)\<close> \<open>op \<noteq> BinOp_Eq\<close> \<open>\<not> (op = BinOp_Mul \<or> op = BinOp_Udiv)\<close>
      by blast
    then show ?thesis
    proof cases
      case ax
      show ?thesis
      proof (cases \<open>?fo ?ia\<close>)
        case True
        then show ?thesis using cv ax fo_ref[OF True] CoreTerm_Bin by auto
      next
        case False
        then have \<open>?fo ?ib\<close> using cv ax assms(2) by (auto split: if_splits)
        then show ?thesis using cv ax False fo_ref[of kind rc b] CoreTerm_Bin by auto
      qed
    next
      case eq
      show ?thesis
      proof (cases \<open>?fo ?ia \<and> 0 < dw ! ?ia\<close>)
        case True
        then show ?thesis using cv eq fo_ref[of kind rc a] CoreTerm_Bin by (auto simp: ref_index_m_def)
      next
        case False
        then have \<open>?fo ?ib \<and> 0 < dw ! ?ib\<close> using cv eq assms(2) by (auto split: if_splits)
        then show ?thesis using cv eq False fo_ref[of kind rc b] CoreTerm_Bin by (auto simp: ref_index_m_def)
      qed
    next
      case md
      then have f: \<open>?fo ?ia\<close> \<open>?fo ?ib\<close> \<open>?ia \<noteq> ?ib\<close> and c: \<open>c = 4\<close> using cv assms(2) by (auto split: if_splits)
      obtain i where i: \<open>a = CoreTerm_Ref i\<close> \<open>?fo (unat i)\<close> using fo_ref[OF f(1)] by blast
      obtain j where j: \<open>b = CoreTerm_Ref j\<close> \<open>?fo (unat j)\<close> using fo_ref[OF f(2)] by blast
      show ?thesis using CoreTerm_Bin md i j c f(3) by (auto simp: ref_index_m_def)
    next
      case other
      then show ?thesis using cv assms(2) by simp
    qed
  next
    case (CoreTerm_Const bs)
    then show ?thesis using assms unfolding CoreTerm_Const free_kind_simps by simp
  next
    case (CoreTerm_Ref i)
    then show ?thesis using assms unfolding CoreTerm_Ref free_kind_simps by simp
  next
    case (CoreTerm_Var i)
    then show ?thesis using assms unfolding CoreTerm_Var free_kind_simps by (simp split: if_splits)
  qed
qed

subsection \<open>Counting references\<close>

lemma rcnt_sum: \<open>rcnt ts x = sum_list (map (\<lambda>t. rcnt [t] x) ts)\<close>
  by (induction ts) (simp_all add: rcnt_Cons[where ts = \<open>_ # _\<close>] rcnt_def)

lemma rcnt_pos: \<open>u \<in> set (csubterms t) \<Longrightarrow> is_ref x u \<Longrightarrow> 0 < rcnt [t] x\<close>
  by (auto simp: rcnt_def filter_empty_conv)

lemma rcnt_le: \<open>t \<in> set ts \<Longrightarrow> rcnt [t] x \<le> rcnt ts x\<close>
  unfolding rcnt_sum[of ts] by (rule member_le_sum_list) auto

text \<open>A definition referred to once is referred to by one term only.\<close>
lemma rcnt1_unique:
  assumes \<open>rcnt ts x = 1\<close> \<open>i < length ts\<close> \<open>j < length ts\<close>
    \<open>u \<in> set (csubterms (ts ! i))\<close> \<open>is_ref x u\<close> \<open>u' \<in> set (csubterms (ts ! j))\<close> \<open>is_ref x u'\<close>
  shows \<open>i = j\<close>
proof (rule ccontr)
  assume ne: \<open>i \<noteq> j\<close>
  let ?f = \<open>\<lambda>k. rcnt [ts ! k] x\<close>
  have \<open>rcnt ts x = (\<Sum>k<length ts. ?f k)\<close>
    unfolding rcnt_sum[of ts] by (simp add: sum_list_sum_nth atLeast0LessThan)
  moreover have \<open>(\<Sum>k\<in>{i, j}. ?f k) \<le> (\<Sum>k<length ts. ?f k)\<close>
    using assms(2,3) by (intro sum_mono2) auto
  moreover have \<open>0 < ?f i\<close> \<open>0 < ?f j\<close> using rcnt_pos assms(4-7) by blast+
  ultimately show False using ne assms(1) by simp
qed

lemma rcnt_Bin: \<open>rcnt [CoreTerm_Bin op a b] x = rcnt [a] x + rcnt [b] x\<close>
  by (simp add: rcnt_def is_ref_def)

lemma rcnt_Ref: \<open>rcnt [CoreTerm_Ref i] x = (if unat i = x then 1 else 0)\<close>
  by (simp add: rcnt_def is_ref_def)

subsection \<open>The analysis of a problem\<close>

locale elim_prob =
  fixes q :: CoreProblem
  assumes wt: \<open>cproblem_wt q\<close> and nlt: \<open>length (CoreProblem_defs q) < 2 ^ 64\<close>
begin

definition \<open>eD = CoreProblem_defs q\<close>
definition \<open>eA = CoreProblem_asserts q\<close>
definition \<open>ews = cvar_widths q\<close>
definition \<open>eds = cdef_widths ews [] eD\<close>
definition \<open>en = length eD\<close>
definition \<open>evc = fst (occ_res q)\<close>
definition \<open>erc = snd (occ_res q)\<close>
definition \<open>kd = fst (snd (ana_res q))\<close>
definition \<open>mk = fst (snd (snd (ana_res q)))\<close>
definition \<open>d1 = snd (snd (snd (ana_res q)))\<close>
definition \<open>cons k = consumed_m (eD ! k) (kd ! k) en\<close>
definition \<open>sec k = second_m (eD ! k) en\<close>

lemma ana:
  shows \<open>fst (ana_res q) = eds\<close> \<open>length kd = en\<close> \<open>length mk = en\<close> \<open>length d1 = en\<close>
    \<open>k < en \<Longrightarrow> kd ! k = free_kind_m eD (take k eds) evc erc (take k kd) (eD ! k)\<close>
    \<open>k < en \<Longrightarrow> d1 ! k = (if 2 \<le> kd ! k then rewrite_m (take k eds) (cons k) (eds ! k) else eD ! k)\<close>
proof -
  obtain dw kind mark defs where r: \<open>ana_res q = (dw, kind, mark, defs)\<close> by (cases \<open>ana_res q\<close>)
  have \<open>foldl (elim_step ews eD evc erc) ([], [], replicate (length eD) 0, []) [0..<length eD] = (dw, kind, mark, defs)\<close>
    using r by (simp add: ana_res_def ews_def eD_def evc_def erc_def Let_def)
  note F = ana_fold[OF order_refl this]
  show \<open>fst (ana_res q) = eds\<close> \<open>length kd = en\<close> \<open>length mk = en\<close> \<open>length d1 = en\<close>
    using F r by (simp_all add: eds_def kd_def mk_def d1_def en_def)
  show \<open>k < en \<Longrightarrow> kd ! k = free_kind_m eD (take k eds) evc erc (take k kd) (eD ! k)\<close>
    using F r by (simp add: eds_def kd_def en_def)
  show \<open>k < en \<Longrightarrow> d1 ! k = (if 2 \<le> kd ! k then rewrite_m (take k eds) (cons k) (eds ! k) else eD ! k)\<close>
    using F r by (simp add: eds_def kd_def d1_def en_def cons_def)
qed

lemma len_eds: \<open>length eds = en\<close>
  by (simp add: eds_def en_def cdef_widths_length)

lemma take_eds: \<open>k \<le> en \<Longrightarrow> take k eds = cdef_widths ews [] (take k eD)\<close>
proof -
  assume k: \<open>k \<le> en\<close>
  have \<open>eds = cdef_widths ews (cdef_widths ews [] (take k eD)) (drop k eD)\<close>
    using cdef_widths_append[of ews \<open>[]\<close> \<open>take k eD\<close> \<open>drop k eD\<close>] by (simp add: eds_def)
  then obtain e where \<open>eds = cdef_widths ews [] (take k eD) @ e\<close> using cdef_widths_prefix by metis
  then show ?thesis using k by (simp add: cdef_widths_length en_def)
qed

lemma dwt: \<open>cdefs_wt ews [] eD\<close>
  using wt by (simp add: cproblem_wt_def Let_def ews_def eD_def)

lemma wt_D: \<open>k < en \<Longrightarrow> cwt ews (take k eds) (eD ! k)\<close>
  using cdefs_wt_nth[OF dwt, of k] take_eds[of k] by (simp add: en_def)

lemma wt_D': \<open>k < en \<Longrightarrow> cwt ews eds (eD ! k)\<close>
  using cdefs_wt_each[OF dwt, of k] by (simp add: en_def eds_def)

lemma eds_nth: \<open>k < en \<Longrightarrow> eds ! k = cwidth ews (take k eds) (eD ! k)\<close>
proof -
  assume k: \<open>k < en\<close>
  have \<open>take (Suc k) eds = take k eds @ [cwidth ews (take k eds) (eD ! k)]\<close>
    using take_eds[of \<open>Suc k\<close>] take_eds[of k] k
    by (simp add: take_Suc_conv_app_nth en_def cdef_widths_append)
  then show ?thesis using k len_eds by (metis nth_take lessI nth_append_length length_take min.absorb4 less_imp_le_nat)
qed

lemma wt_A: \<open>t \<in> set eA \<Longrightarrow> cwt ews eds t \<and> cwidth ews eds t = 1\<close>
  using wt by (simp add: cproblem_wt_def Let_def ews_def eds_def eA_def eD_def)

lemma wsub: \<open>cwt ws ds t \<Longrightarrow> u \<in> set (csubterms t) \<Longrightarrow> cwt ws ds u\<close>
  by (rule wt_sub)

lemma ref_lt_D: \<open>k < en \<Longrightarrow> u \<in> set (csubterms (eD ! k)) \<Longrightarrow> is_ref x u \<Longrightarrow> x < k\<close>
  using wsub[OF wt_D] len_eds by (cases u) (fastforce simp: is_ref_def)+

lemma ref_lt_A: \<open>t \<in> set eA \<Longrightarrow> u \<in> set (csubterms t) \<Longrightarrow> is_ref x u \<Longrightarrow> x < en\<close>
  using wsub[OF conjunct1[OF wt_A]] len_eds by (cases u) (fastforce simp: is_ref_def)+

end

lemma vcnt_sum: \<open>vcnt ts x = sum_list (map (\<lambda>t. vcnt [t] x) ts)\<close>
  by (induction ts) (simp_all add: vcnt_Cons[where ts = \<open>_ # _\<close>] vcnt_def)

lemma vcnt_pos: \<open>u \<in> set (csubterms t) \<Longrightarrow> is_var x u \<Longrightarrow> 0 < vcnt [t] x\<close>
  by (auto simp: vcnt_def filter_empty_conv)

lemma vcnt1_unique:
  assumes \<open>vcnt ts x = 1\<close> \<open>i < length ts\<close> \<open>j < length ts\<close>
    \<open>u \<in> set (csubterms (ts ! i))\<close> \<open>is_var x u\<close> \<open>u' \<in> set (csubterms (ts ! j))\<close> \<open>is_var x u'\<close>
  shows \<open>i = j\<close>
proof (rule ccontr)
  assume ne: \<open>i \<noteq> j\<close>
  let ?f = \<open>\<lambda>k. vcnt [ts ! k] x\<close>
  have \<open>vcnt ts x = (\<Sum>k<length ts. ?f k)\<close>
    unfolding vcnt_sum[of ts] by (simp add: sum_list_sum_nth atLeast0LessThan)
  moreover have \<open>(\<Sum>k\<in>{i, j}. ?f k) \<le> (\<Sum>k<length ts. ?f k)\<close>
    using assms(2,3) by (intro sum_mono2) auto
  moreover have \<open>0 < ?f i\<close> \<open>0 < ?f j\<close> using vcnt_pos assms(4-7) by blast+
  ultimately show False using ne assms(1) by simp
qed

lemma min2_eq1: \<open>min 2 (v::nat) = 1 \<Longrightarrow> v = 1\<close>
  by (cases v) (simp_all add: min_def split: if_splits)

context elim_prob
begin

lemma kd_le: \<open>k < en \<Longrightarrow> kd ! k \<le> 4\<close>
  using ana(5) free_kind_le by metis

lemma lws: \<open>length (CoreProblem_widths q) = length ews\<close>
  by (simp add: ews_def cvar_widths_def)

lemma kd_1:
  assumes \<open>k < en\<close> \<open>kd ! k = 1\<close>
  shows \<open>\<exists>i. eD ! k = CoreTerm_Var i \<and> unat i < length ews \<and> vcnt (eD @ eA) (unat i) = 1\<close>
proof -
  obtain i where i: \<open>eD ! k = CoreTerm_Var i\<close> \<open>evc ! unat i = 1\<close>
    using free_kind_1[of eD \<open>take k eds\<close> evc erc \<open>take k kd\<close> \<open>eD ! k\<close>] ana(5)[OF assms(1)] assms(2) by metis
  have l: \<open>unat i < length ews\<close> using wt_D[OF assms(1)] i(1) by simp
  have \<open>min 2 (vcnt (eD @ eA) (unat i)) = 1\<close>
    using occ_res(3)[of \<open>unat i\<close> q] l i(2) lws by (simp add: evc_def eD_def eA_def)
  then show ?thesis using i l min2_eq1 by blast
qed

lemma fo_take:
  assumes \<open>free_once_m (take k kd) erc x\<close> \<open>k < en\<close>
  shows \<open>x < k \<and> kd ! x \<noteq> 0 \<and> rcnt (eD @ eA) x = 1\<close>
proof -
  have x: \<open>x < k\<close> \<open>kd ! x \<noteq> 0\<close> \<open>erc ! x = 1\<close>
    using assms ana(2) by (auto simp: free_once_m_def)
  have \<open>min 2 (rcnt (eD @ eA) x) = 1\<close>
    using occ_res(4)[of x q] x assms(2) by (simp add: erc_def eD_def eA_def en_def)
  then show ?thesis using x min2_eq1 by blast
qed

lemma kd_cons:
  assumes \<open>k < en\<close> \<open>2 \<le> kd ! k\<close>
  shows \<open>cons k < k \<and> kd ! cons k \<noteq> 0 \<and> rcnt (eD @ eA) (cons k) = 1 \<and>
    (\<exists>u \<in> set (csubterms (eD ! k)). is_ref (cons k) u)\<close>
proof -
  note sh = free_kind_shape[OF ana(5)[OF assms(1)] assms(2)]
  have \<open>free_once_m (take k kd) erc (cons k) \<and> (\<exists>u \<in> set (csubterms (eD ! k)). is_ref (cons k) u)\<close>
    using sh by (auto simp: cons_def consumed_m_def ref_index_m_def is_ref_def)
  then show ?thesis using fo_take assms(1) by blast
qed

lemma kd_sec:
  assumes \<open>k < en\<close> \<open>kd ! k = 4\<close>
  shows \<open>sec k < k \<and> kd ! sec k \<noteq> 0 \<and> rcnt (eD @ eA) (sec k) = 1 \<and> sec k \<noteq> cons k \<and>
    (\<exists>u \<in> set (csubterms (eD ! k)). is_ref (sec k) u)\<close>
proof -
  have h2: \<open>2 \<le> kd ! k\<close> using assms(2) by simp
  note sh = free_kind_shape[OF ana(5)[OF assms(1)] h2] assms(2)
  have \<open>free_once_m (take k kd) erc (sec k) \<and> sec k \<noteq> cons k \<and> (\<exists>u \<in> set (csubterms (eD ! k)). is_ref (sec k) u)\<close>
    using sh by (auto simp: cons_def sec_def consumed_m_def second_m_def ref_index_m_def is_ref_def)
  then show ?thesis using fo_take assms(1) by blast
qed

lemma eDA: \<open>k < en \<Longrightarrow> (eD @ eA) ! k = eD ! k\<close> \<open>length (eD @ eA) = en + length eA\<close>
  by (simp_all add: nth_append en_def)

text \<open>A definition referred to once is referred to by one definition, and not by an assertion.\<close>
lemma ref_unique:
  assumes \<open>rcnt (eD @ eA) x = 1\<close> \<open>k < en\<close> \<open>k' < en\<close>
    \<open>u \<in> set (csubterms (eD ! k))\<close> \<open>is_ref x u\<close> \<open>u' \<in> set (csubterms (eD ! k'))\<close> \<open>is_ref x u'\<close>
  shows \<open>k = k'\<close>
  using rcnt1_unique[OF assms(1), of k k' u u'] assms eDA by simp

lemma ref_not_A:
  assumes \<open>rcnt (eD @ eA) x = 1\<close> \<open>k < en\<close> \<open>u \<in> set (csubterms (eD ! k))\<close> \<open>is_ref x u\<close>
    \<open>t \<in> set eA\<close> \<open>u' \<in> set (csubterms t)\<close> \<open>is_ref x u'\<close>
  shows False
proof -
  obtain j where j: \<open>j < length eA\<close> \<open>eA ! j = t\<close> using assms(5) by (meson in_set_conv_nth)
  have \<open>(eD @ eA) ! (en + j) = t\<close> using j by (simp add: nth_append en_def)
  then have \<open>k = en + j\<close> using rcnt1_unique[OF assms(1), of k \<open>en + j\<close> u u'] assms eDA j by simp
  then show False using assms(2) by simp
qed

lemma var_unique:
  assumes \<open>vcnt (eD @ eA) x = 1\<close> \<open>k < en\<close> \<open>k' < en\<close>
    \<open>u \<in> set (csubterms (eD ! k))\<close> \<open>is_var x u\<close> \<open>u' \<in> set (csubterms (eD ! k'))\<close> \<open>is_var x u'\<close>
  shows \<open>k = k'\<close>
  using vcnt1_unique[OF assms(1), of k k' u u'] assms eDA by simp

lemma var_not_A:
  assumes \<open>vcnt (eD @ eA) x = 1\<close> \<open>k < en\<close> \<open>u \<in> set (csubterms (eD ! k))\<close> \<open>is_var x u\<close>
    \<open>t \<in> set eA\<close> \<open>u' \<in> set (csubterms t)\<close> \<open>is_var x u'\<close>
  shows False
proof -
  obtain j where j: \<open>j < length eA\<close> \<open>eA ! j = t\<close> using assms(5) by (meson in_set_conv_nth)
  have \<open>(eD @ eA) ! (en + j) = t\<close> using j by (simp add: nth_append en_def)
  then have \<open>k = en + j\<close> using vcnt1_unique[OF assms(1), of k \<open>en + j\<close> u u'] assms eDA j by simp
  then show False using assms(2) by simp
qed

end

lemma elim_step_app: \<open>\<exists>w c m' t'. elim_step ws D vc rc (dw, kind, mark, defs) k = (dw @ [w], kind @ [c], m', defs @ [t'])\<close>
  by (auto simp: elim_step_def Let_def)

lemma elim_fold_app:
  \<open>\<exists>e1 e2 m e3. foldl (elim_step ws D vc rc) (dw, kind, mark, defs) xs = (dw @ e1, kind @ e2, m, defs @ e3)\<close>
proof (induction xs arbitrary: dw kind mark defs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  obtain w c m' t' where e: \<open>elim_step ws D vc rc (dw, kind, mark, defs) x = (dw @ [w], kind @ [c], m', defs @ [t'])\<close>
    using elim_step_app by blast
  obtain e1 e2 m e3 where
    \<open>foldl (elim_step ws D vc rc) (dw @ [w], kind @ [c], m', defs @ [t']) xs = (dw @ [w] @ e1, kind @ [c] @ e2, m, defs @ [t'] @ e3)\<close>
    using Cons.IH[of \<open>dw @ [w]\<close> \<open>kind @ [c]\<close> m' \<open>defs @ [t']\<close>] by auto
  then show ?case using e by auto
qed

context elim_prob
begin

lemma ana_res_eq: \<open>ana_res q = foldl (elim_step ews eD evc erc) ([], [], replicate en 0, []) [0..<en]\<close>
  by (simp add: ana_res_def Let_def ews_def eD_def evc_def erc_def en_def)

lemma ana_parts: \<open>ana_res q = (eds, kd, mk, d1)\<close>
  using ana(1) by (cases \<open>ana_res q\<close>) (simp add: kd_def mk_def d1_def)

lemma ana_prefix:
  assumes \<open>k \<le> en\<close>
  shows \<open>\<exists>M. foldl (elim_step ews eD evc erc) ([], [], replicate en 0, []) [0..<k] = (take k eds, take k kd, M, take k d1)\<close>
proof -
  obtain dw kind mark defs where s: \<open>foldl (elim_step ews eD evc erc) ([], [], replicate en 0, []) [0..<k] = (dw, kind, mark, defs)\<close>
    by (cases \<open>foldl (elim_step ews eD evc erc) ([], [], replicate en 0, []) [0..<k]\<close>)
  have l: \<open>length dw = k\<close> \<open>length kind = k\<close> \<open>length defs = k\<close>
    using ana_fold[of k eD ews evc erc dw kind mark defs] s assms by (simp_all add: en_def cdef_widths_length min_def)
  obtain e1 e2 m e3 where f: \<open>foldl (elim_step ews eD evc erc) (dw, kind, mark, defs) [k..<en] = (dw @ e1, kind @ e2, m, defs @ e3)\<close>
    using elim_fold_app by blast
  have \<open>[0..<en] = [0..<k] @ [k..<en]\<close> using assms by (metis le_add_diff_inverse upt_add_eq_append zero_le)
  then have \<open>ana_res q = (dw @ e1, kind @ e2, m, defs @ e3)\<close> using ana_res_eq s f by simp
  then show ?thesis using ana_parts l s by auto
qed

lemma ex_lsuc: \<open>(\<exists>i<Suc k. P i) \<longleftrightarrow> (\<exists>i<k. P i) \<or> P k\<close>
  by (auto simp: less_Suc_eq)

definition MK :: \<open>nat \<Rightarrow> nat list\<close> where
  \<open>MK k = map (\<lambda>j. if \<exists>i<k. 2 \<le> kd ! i \<and> cons i = j then 1 else if \<exists>i<k. kd ! i = 4 \<and> sec i = j then 2 else 0) [0..<en]\<close>

lemma cons_sec_ne:
  assumes \<open>i < en\<close> \<open>k < en\<close> \<open>2 \<le> kd ! i\<close> \<open>kd ! k = 4\<close> \<open>cons i = sec k\<close>
  shows False
proof -
  obtain u where u: \<open>u \<in> set (csubterms (eD ! i))\<close> \<open>is_ref (cons i) u\<close> using kd_cons[OF assms(1,3)] by blast
  obtain u' where u': \<open>u' \<in> set (csubterms (eD ! k))\<close> \<open>is_ref (sec k) u'\<close> using kd_sec[OF assms(2,4)] by blast
  have \<open>i = k\<close> using ref_unique[of \<open>sec k\<close> i k u u'] kd_sec[OF assms(2,4)] assms u u' by simp
  then show False using kd_sec[OF assms(2,4)] assms(5) by simp
qed

lemma cons_unique:
  assumes \<open>i < en\<close> \<open>k < en\<close> \<open>2 \<le> kd ! i\<close> \<open>2 \<le> kd ! k\<close> \<open>cons i = cons k\<close>
  shows \<open>i = k\<close>
proof -
  obtain u where u: \<open>u \<in> set (csubterms (eD ! i))\<close> \<open>is_ref (cons i) u\<close> using kd_cons[OF assms(1,3)] by blast
  obtain u' where u': \<open>u' \<in> set (csubterms (eD ! k))\<close> \<open>is_ref (cons k) u'\<close> using kd_cons[OF assms(2,4)] by blast
  show ?thesis using ref_unique[of \<open>cons k\<close> i k u u'] kd_cons[OF assms(2,4)] assms u u' by simp
qed

lemma sec_unique:
  assumes \<open>i < en\<close> \<open>k < en\<close> \<open>kd ! i = 4\<close> \<open>kd ! k = 4\<close> \<open>sec i = sec k\<close>
  shows \<open>i = k\<close>
proof -
  obtain u where u: \<open>u \<in> set (csubterms (eD ! i))\<close> \<open>is_ref (sec i) u\<close> using kd_sec[OF assms(1,3)] by blast
  obtain u' where u': \<open>u' \<in> set (csubterms (eD ! k))\<close> \<open>is_ref (sec k) u'\<close> using kd_sec[OF assms(2,4)] by blast
  show ?thesis using ref_unique[of \<open>sec k\<close> i k u u'] kd_sec[OF assms(2,4)] assms u u' by simp
qed

lemma mk_fold:
  assumes \<open>k \<le> en\<close>
  shows \<open>fst (snd (snd (foldl (elim_step ews eD evc erc) ([], [], replicate en 0, []) [0..<k]))) = MK k\<close>
  using assms
proof (induction k)
  case 0
  then show ?case by (simp add: MK_def map_replicate_const)
next
  case (Suc k)
  then have k: \<open>k < en\<close> by simp
  obtain M where s: \<open>foldl (elim_step ews eD evc erc) ([], [], replicate en 0, []) [0..<k] = (take k eds, take k kd, M, take k d1)\<close>
    using ana_prefix[of k] k by auto
  have M: \<open>M = MK k\<close> using Suc.IH s k by simp
  have c: \<open>free_kind_m eD (take k eds) evc erc (take k kd) (eD ! k) = kd ! k\<close> using ana(5)[OF k] by simp
  have l: \<open>length (MK k) = en\<close> by (simp add: MK_def)
  have st: \<open>fst (snd (snd (foldl (elim_step ews eD evc erc) ([], [], replicate en 0, []) [0..<Suc k]))) =
    (if 2 \<le> kd ! k then (if kd ! k = 4 then list_update (list_update (MK k) (cons k) 1) (sec k) 2 else list_update (MK k) (cons k) 1) else MK k)\<close>
    using s M c by (simp add: elim_step_def Let_def cons_def sec_def en_def)
  show ?case
  proof (rule nth_equalityI)
    show \<open>length (fst (snd (snd (foldl (elim_step ews eD evc erc) ([], [], replicate en 0, []) [0..<Suc k])))) = length (MK (Suc k))\<close>
      using st l by (simp add: MK_def)
  next
    fix j assume \<open>j < length (fst (snd (snd (foldl (elim_step ews eD evc erc) ([], [], replicate en 0, []) [0..<Suc k]))))\<close>
    then have j: \<open>j < en\<close> using st l by (simp split: if_splits)
    have ck: \<open>2 \<le> kd ! k \<Longrightarrow> cons k < en\<close> using kd_cons[OF k] k by simp
    have sk: \<open>kd ! k = 4 \<Longrightarrow> sec k < en \<and> sec k \<noteq> cons k\<close> using kd_sec[OF k] k by simp
    have no1: \<open>kd ! k = 4 \<Longrightarrow> \<not> (\<exists>i<Suc k. 2 \<le> kd ! i \<and> cons i = sec k)\<close>
      using cons_sec_ne[OF _ k] sk k by (metis less_Suc_eq less_trans)
    show \<open>fst (snd (snd (foldl (elim_step ews eD evc erc) ([], [], replicate en 0, []) [0..<Suc k]))) ! j = MK (Suc k) ! j\<close>
    proof (cases \<open>2 \<le> kd ! k\<close>)
      case False
      then show ?thesis unfolding st using j l by (auto simp: MK_def ex_lsuc)
    next
      case T2: True
      show ?thesis
      proof (cases \<open>kd ! k = 4\<close>)
        case T4: True
        have s1: \<open>sec k < en\<close> \<open>sec k \<noteq> cons k\<close> \<open>cons k < en\<close> using sk[OF T4] ck[OF T2] by simp_all
        consider \<open>j = sec k\<close> | \<open>j = cons k\<close> | \<open>j \<noteq> sec k\<close> \<open>j \<noteq> cons k\<close> by blast
        then show ?thesis
        proof cases
          case 1
          then show ?thesis unfolding st using j l T2 T4 s1 no1[OF T4] by (auto simp: MK_def ex_lsuc)
        next
          case 2
          then show ?thesis unfolding st using j l T2 T4 s1 by (auto simp: MK_def ex_lsuc)
        next
          case 3
          then show ?thesis unfolding st using j l T2 T4 s1 by (auto simp: MK_def ex_lsuc)
        qed
      next
        case F4: False
        have s1: \<open>cons k < en\<close> using ck[OF T2] by simp_all
        show ?thesis
        proof (cases \<open>j = cons k\<close>)
          case True
          then show ?thesis unfolding st using j l T2 F4 s1 by (auto simp: MK_def ex_lsuc)
        next
          case False
          then show ?thesis unfolding st using j l T2 F4 s1 by (auto simp: MK_def ex_lsuc)
        qed
      qed
    qed
  qed
qed

lemma mk_MK: \<open>mk = MK en\<close>
  using mk_fold[of en] ana_parts ana_res_eq by simp

lemma mk_char:
  assumes \<open>j < en\<close>
  shows \<open>mk ! j = 1 \<longleftrightarrow> (\<exists>i<en. 2 \<le> kd ! i \<and> cons i = j)\<close>
    \<open>mk ! j = 2 \<longleftrightarrow> (\<exists>i<en. kd ! i = 4 \<and> sec i = j)\<close>
  using assms cons_sec_ne by (auto simp: mk_MK MK_def)

end

context elim_prob
begin

lemma take_eds_nth: \<open>i < k \<Longrightarrow> k \<le> en \<Longrightarrow> take k eds ! i = eds ! i\<close>
  by simp

text \<open>A rewritten definition is no wider than the operand it consumes; when narrower, it is an
  \<open>extract\<close> of width at least 1.\<close>
lemma kd_width:
  assumes k: \<open>k < en\<close> and h: \<open>2 \<le> kd ! k\<close>
  shows \<open>eds ! k \<le> eds ! cons k \<and> (eds ! k \<noteq> eds ! cons k \<longrightarrow> 1 \<le> eds ! k \<and> eds ! k - 1 < 2 ^ 64)\<close>
proof -
  note sh = free_kind_shape[OF ana(5)[OF k] h]
  have W: \<open>cwt ews (take k eds) (eD ! k)\<close> using wt_D[OF k] .
  have E: \<open>eds ! k = cwidth ews (take k eds) (eD ! k)\<close> using eds_nth[OF k] .
  have lk: \<open>length (take k eds) = k\<close> using k len_eds by simp
  have fl: \<open>free_once_m (take k kd) erc x \<Longrightarrow> x < k\<close> for x using fo_take k by blast
  have ec: \<open>i < en \<Longrightarrow> eD ! i = CoreTerm_Const bs \<Longrightarrow> eds ! i = length bs\<close> for i bs
    using eds_nth[of i] by simp
  have u64: \<open>unat (w :: 64 word) - y < 18446744073709551616\<close> for w y
    using unat_lt2p[of w] by simp
  show ?thesis
    using sh
  proof (elim disjE exE conjE)
  qed (use W E lk fl k ec in \<open>auto simp: cons_def consumed_m_def ref_index_m_def bit_const_m_def u64 split: CoreTerm.splits if_splits\<close>)
qed

end

lemma length_mark_live [simp]: \<open>length (mark_live_m L t) = length L\<close>
  by (induction t arbitrary: L) simp_all

lemma mark_live_nth:
  \<open>x < length L \<Longrightarrow> mark_live_m L t ! x \<longleftrightarrow> L ! x \<or> (\<exists>u \<in> set (csubterms t). is_ref x u)\<close>
proof (induction t arbitrary: L)
  case (CoreTerm_Ref i)
  then show ?case by (cases \<open>unat i < length L\<close>) (auto simp: nth_list_update is_ref_def)
qed (auto simp: is_ref_def)

lemma mark_live_fold:
  \<open>length (foldl mark_live_m L ts) = length L\<close>
  \<open>x < length L \<Longrightarrow> foldl mark_live_m L ts ! x \<longleftrightarrow> L ! x \<or> (\<exists>t \<in> set ts. \<exists>u \<in> set (csubterms t). is_ref x u)\<close>
proof (induction ts arbitrary: L)
  case (Cons t ts)
  { case 1 show ?case using Cons.IH(1) by simp }
  { case 2 then show ?case using Cons.IH(2)[of \<open>mark_live_m L t\<close>] mark_live_nth[of x L t] by auto }
qed simp_all

lemma cdefs_wt_I:
  assumes \<open>length D = length ds\<close> \<open>\<forall>j < length D. cwt ws (take j ds) (D ! j) \<and> cwidth ws (take j ds) (D ! j) = ds ! j\<close>
  shows \<open>cdefs_wt ws [] D \<and> cdef_widths ws [] D = ds\<close>
  using assms
proof (induction D arbitrary: ds rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc d D)
  obtain ds' w where ds: \<open>ds = ds' @ [w]\<close> using snoc.prems(1) by (cases ds rule: rev_cases) auto
  have l: \<open>length D = length ds'\<close> using snoc.prems(1) ds by simp
  have \<open>\<forall>j < length D. cwt ws (take j ds') (D ! j) \<and> cwidth ws (take j ds') (D ! j) = ds' ! j\<close>
  proof (intro allI impI)
    fix j assume j: \<open>j < length D\<close>
    have \<open>cwt ws (take j ds) ((D @ [d]) ! j) \<and> cwidth ws (take j ds) ((D @ [d]) ! j) = ds ! j\<close>
      using snoc.prems(2) j by simp
    then show \<open>cwt ws (take j ds') (D ! j) \<and> cwidth ws (take j ds') (D ! j) = ds' ! j\<close>
      using j l ds by (simp add: nth_append)
  qed
  note IH = snoc.IH[OF l this]
  have \<open>cwt ws ds' d \<and> cwidth ws ds' d = w\<close>
    using snoc.prems(2)[rule_format, of \<open>length D\<close>] l ds by (simp add: nth_append)
  then show ?case using IH ds by (simp add: cdefs_wt_append cdef_widths_append)
qed

context elim_prob
begin

lemma cons_lt: \<open>k < en \<Longrightarrow> 2 \<le> kd ! k \<Longrightarrow> cons k < k\<close>
  using kd_cons by blast

lemma unat_nat: \<open>x < en \<Longrightarrow> unat (word_of_nat x :: 64 word) = x\<close>
  using nlt by (simp add: unat_of_nat_eq en_def eD_def)

lemma d1_wt:
  assumes j: \<open>j < en\<close>
  shows \<open>cwt ews (take j eds) (d1 ! j) \<and> cwidth ews (take j eds) (d1 ! j) = eds ! j\<close>
proof (cases \<open>2 \<le> kd ! j\<close>)
  case True
  let ?c = \<open>cons j\<close>
  have c: \<open>?c < j\<close> using cons_lt[OF j True] .
  have cu: \<open>unat (word_of_nat ?c :: 64 word) = ?c\<close> using unat_nat c j by simp
  have tk: \<open>take j eds ! ?c = eds ! ?c\<close> \<open>length (take j eds) = j\<close> using c j len_eds by simp_all
  note W = kd_width[OF j True]
  have wu: \<open>eds ! j \<noteq> eds ! ?c \<Longrightarrow> unat (word_of_nat (eds ! j - 1) :: 64 word) = eds ! j - 1\<close>
    by (rule unat_of_nat_eq) (use W in simp)
  show ?thesis
    using ana(6)[OF j] True cu tk W wu c by (auto simp: rewrite_m_def)
next
  case False
  then show ?thesis using ana(6)[OF j] wt_D[OF j] eds_nth[OF j] by simp
qed

lemma d1_refs: \<open>j < en \<Longrightarrow> u \<in> set (csubterms (d1 ! j)) \<Longrightarrow> is_ref x u \<Longrightarrow> x < j\<close>
  using wsub[OF conjunct1[OF d1_wt]] len_eds by (cases u) (fastforce simp: is_ref_def)+

definition \<open>L0 = foldl mark_live_m (replicate en False) eA\<close>
definition \<open>DS d = foldl (dce_step eds) (L0, d1) (rev [d..<en])\<close>

definition dinv :: \<open>nat \<Rightarrow> bool list \<Rightarrow> CoreTerm list \<Rightarrow> bool\<close> where
  \<open>dinv d L Ds \<equiv> length L = en \<and> length Ds = en \<and> (\<forall>j<d. Ds ! j = d1 ! j) \<and>
     (\<forall>j. d \<le> j \<longrightarrow> j < en \<longrightarrow> Ds ! j = (if L ! j then d1 ! j else CoreTerm_Const (replicate (eds ! j) False))) \<and>
     (\<forall>j. d \<le> j \<longrightarrow> j < en \<longrightarrow> L ! j \<longrightarrow> (\<forall>u \<in> set (csubterms (d1 ! j)). \<forall>x. is_ref x u \<longrightarrow> L ! x)) \<and>
     (\<forall>t \<in> set eA. \<forall>u \<in> set (csubterms t). \<forall>x. is_ref x u \<longrightarrow> L ! x)\<close>

lemma dinv_en: \<open>dinv en L0 d1\<close>
proof -
  have \<open>length L0 = en\<close> by (simp add: L0_def mark_live_fold(1))
  moreover have \<open>\<forall>t \<in> set eA. \<forall>u \<in> set (csubterms t). \<forall>x. is_ref x u \<longrightarrow> L0 ! x\<close>
    using mark_live_fold(2) ref_lt_A unfolding L0_def by fastforce
  ultimately show ?thesis using ana(4) by (simp add: dinv_def)
qed

lemma dinv_step:
  assumes \<open>d < en\<close> \<open>dinv (Suc d) L Ds\<close>
  shows \<open>case dce_step eds (L, Ds) d of (L', Ds') \<Rightarrow> dinv d L' Ds'\<close>
proof (cases \<open>L ! d\<close>)
  case True
  let ?L = \<open>mark_live_m L (d1 ! d)\<close>
  have I: \<open>length L = en\<close> \<open>length Ds = en\<close> \<open>Ds ! d = d1 ! d\<close> using assms by (simp_all add: dinv_def)
  have st: \<open>dce_step eds (L, Ds) d = (?L, Ds)\<close> using True I by (simp add: dce_step_def)
  have Ln: \<open>x < en \<Longrightarrow> ?L ! x \<longleftrightarrow> L ! x \<or> (\<exists>u \<in> set (csubterms (d1 ! d)). is_ref x u)\<close> for x
    using mark_live_nth[of x L] I by simp
  have hi: \<open>d \<le> x \<Longrightarrow> x < en \<Longrightarrow> ?L ! x = L ! x\<close> for x
    using Ln d1_refs[OF assms(1)] by fastforce
  have \<open>dinv d ?L Ds\<close>
    unfolding dinv_def
  proof (intro conjI allI impI ballI)
    show \<open>length ?L = en\<close> \<open>length Ds = en\<close> using I by simp_all
  next
    fix j assume \<open>j < d\<close> then show \<open>Ds ! j = d1 ! j\<close> using assms(2) by (simp add: dinv_def)
  next
    fix j assume j: \<open>d \<le> j\<close> \<open>j < en\<close>
    show \<open>Ds ! j = (if ?L ! j then d1 ! j else CoreTerm_Const (replicate (eds ! j) False))\<close>
    proof (cases \<open>j = d\<close>)
      case True
      then show ?thesis using I hi[of d] \<open>L ! d\<close> assms(1) by simp
    next
      case False
      then show ?thesis using assms(2) j hi[of j] by (simp add: dinv_def)
    qed
  next
    fix j u x assume j: \<open>d \<le> j\<close> \<open>j < en\<close> \<open>?L ! j\<close> \<open>u \<in> set (csubterms (d1 ! j))\<close> \<open>is_ref x u\<close>
    have xl: \<open>x < en\<close> using d1_refs[OF j(2,4,5)] j(2) by simp
    show \<open>?L ! x\<close>
    proof (cases \<open>j = d\<close>)
      case True
      then show ?thesis using Ln[OF xl] j by blast
    next
      case False
      then have \<open>L ! j\<close> using j hi by simp
      then have \<open>L ! x\<close> using assms(2) j False unfolding dinv_def by (metis Suc_leI le_neq_implies_less)
      then show ?thesis using Ln[OF xl] by blast
    qed
  next
    fix t u x assume t: \<open>t \<in> set eA\<close> \<open>u \<in> set (csubterms t)\<close> \<open>is_ref x u\<close>
    have \<open>L ! x\<close> \<open>x < en\<close> using assms(2) t ref_lt_A[OF t] unfolding dinv_def by blast+
    then show \<open>?L ! x\<close> using Ln by blast
  qed
  then show ?thesis using st by simp
next
  case False
  let ?Ds = \<open>Ds[d := CoreTerm_Const (replicate (eds ! d) False)]\<close>
  have st: \<open>dce_step eds (L, Ds) d = (L, ?Ds)\<close> using False by (simp add: dce_step_def)
  have I: \<open>length L = en\<close> \<open>length Ds = en\<close> using assms by (simp_all add: dinv_def)
  have \<open>dinv d L ?Ds\<close>
    unfolding dinv_def
  proof (intro conjI allI impI ballI)
    show \<open>length L = en\<close> \<open>length ?Ds = en\<close> using I by simp_all
  next
    fix j assume \<open>j < d\<close> then show \<open>?Ds ! j = d1 ! j\<close> using assms(2) by (simp add: dinv_def)
  next
    fix j assume j: \<open>d \<le> j\<close> \<open>j < en\<close>
    show \<open>?Ds ! j = (if L ! j then d1 ! j else CoreTerm_Const (replicate (eds ! j) False))\<close>
    proof (cases \<open>j = d\<close>)
      case True
      then show ?thesis using I False j by simp
    next
      case F: False
      then have \<open>Suc d \<le> j\<close> using j by simp
      then show ?thesis using assms(2) j F unfolding dinv_def by simp
    qed
  next
    fix j u x assume j: \<open>d \<le> j\<close> \<open>j < en\<close> \<open>L ! j\<close> \<open>u \<in> set (csubterms (d1 ! j))\<close> \<open>is_ref x u\<close>
    then have \<open>Suc d \<le> j\<close> using False by (cases \<open>j = d\<close>) auto
    then show \<open>L ! x\<close> using assms(2) j unfolding dinv_def by blast
  next
    fix t u x assume \<open>t \<in> set eA\<close> \<open>u \<in> set (csubterms t)\<close> \<open>is_ref x u\<close>
    then show \<open>L ! x\<close> using assms(2) unfolding dinv_def by blast
  qed
  then show ?thesis using st by simp
qed

lemma dinv_DS: \<open>m \<le> en \<Longrightarrow> case DS (en - m) of (L, Ds) \<Rightarrow> dinv (en - m) L Ds\<close>
proof (induction m)
  case 0
  then show ?case using dinv_en by (simp add: DS_def)
next
  case (Suc m)
  let ?d = \<open>en - Suc m\<close>
  have d: \<open>?d < en\<close> \<open>Suc ?d = en - m\<close> using Suc.prems by simp_all
  have \<open>rev [?d..<en] = rev [Suc ?d..<en] @ [?d]\<close> using d by (simp add: upt_rec)
  then have e: \<open>DS ?d = dce_step eds (DS (Suc ?d)) ?d\<close> by (simp add: DS_def)
  obtain L Ds where s: \<open>DS (Suc ?d) = (L, Ds)\<close> by (cases \<open>DS (Suc ?d)\<close>)
  have \<open>dinv (Suc ?d) L Ds\<close> using Suc.IH Suc.prems s d(2) by simp
  then show ?case using dinv_step[OF d(1)] e s by simp
qed

definition \<open>live = fst (dce_res q)\<close>
definition \<open>D2 = snd (dce_res q)\<close>

lemma dce_DS: \<open>dce_res q = DS 0\<close>
  using ana_parts by (simp add: dce_res_def DS_def L0_def en_def eD_def eA_def Let_def)

lemma dinv_final: \<open>dinv 0 live D2\<close>
  using dinv_DS[of en] dce_DS by (cases \<open>DS 0\<close>) (simp add: live_def D2_def)

lemma D2:
  shows \<open>length D2 = en\<close> \<open>length live = en\<close>
    \<open>j < en \<Longrightarrow> D2 ! j = (if live ! j then d1 ! j else CoreTerm_Const (replicate (eds ! j) False))\<close>
    \<open>j < en \<Longrightarrow> live ! j \<Longrightarrow> u \<in> set (csubterms (d1 ! j)) \<Longrightarrow> is_ref x u \<Longrightarrow> live ! x\<close>
    \<open>t \<in> set eA \<Longrightarrow> u \<in> set (csubterms t) \<Longrightarrow> is_ref x u \<Longrightarrow> live ! x\<close>
  using dinv_final unfolding dinv_def by blast+

lemma D2_wt: \<open>j < en \<Longrightarrow> cwt ews (take j eds) (D2 ! j) \<and> cwidth ews (take j eds) (D2 ! j) = eds ! j\<close>
  using D2(3) d1_wt by auto

end

end
