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

lemma rcnt_Ite: \<open>rcnt [CoreTerm_Ite c a b] x = rcnt [c] x + rcnt [a] x + rcnt [b] x\<close>
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

subsection \<open>The eliminated problem is well-sorted and no larger\<close>

lemma csubterms_hd: \<open>\<exists>r. csubterms t = t # r\<close>
  by (cases t) simp_all

lemma weight_mem: \<open>u \<in> set (csubterms t) \<Longrightarrow> (cwidth ws ds u + 1) ^ 2 \<le> cterm_weight ws ds t\<close>
  unfolding cterm_weight_def by (rule member_le_sum_list) auto

lemma weight_two:
  assumes \<open>u \<in> set (csubterms t)\<close> \<open>u \<noteq> t\<close>
  shows \<open>(cwidth ws ds t + 1) ^ 2 + (cwidth ws ds u + 1) ^ 2 \<le> cterm_weight ws ds t\<close>
proof -
  obtain r where r: \<open>csubterms t = t # r\<close> using csubterms_hd by blast
  have \<open>u \<in> set r\<close> using assms r by simp
  then have \<open>(cwidth ws ds u + 1) ^ 2 \<le> sum_list (map (\<lambda>u. (cwidth ws ds u + 1) ^ 2) r)\<close>
    by (intro member_le_sum_list) auto
  then show ?thesis using r by (simp add: cterm_weight_def)
qed

lemma tbound_mem: \<open>u \<in> set (csubterms t) \<Longrightarrow> 2 * cwidth ws ds u + 2 \<le> tbound ws ds t\<close>
  unfolding tbound_def by (rule le_trans[OF _ max.cobounded2]) (rule Max_ge; simp)

lemma tbound_size: \<open>Suc (size t) \<le> tbound ws ds t\<close>
  unfolding tbound_def by simp

lemma size_pos: \<open>u \<in> set (csubterms t) \<Longrightarrow> u \<noteq> t \<Longrightarrow> 1 \<le> size t\<close>
  by (cases t) simp_all

lemma ccount_atom: \<open>ccount ws ds (CoreTerm_Ref i) = 0\<close> \<open>ccount ws ds (CoreTerm_Const bs) = 0\<close>
  \<open>ccount ws ds (CoreTerm_Extract hi lo (CoreTerm_Ref i)) = 0\<close>
  by (simp_all add: ccount_def ncost_def)

lemma sum_list_map_nth_le:
  assumes \<open>length xs = length ys\<close> \<open>\<forall>j < length xs. f (xs ! j) \<le> g (ys ! j)\<close>
  shows \<open>sum_list (map f xs) \<le> (sum_list (map g ys) :: nat)\<close>
proof -
  have \<open>sum_list (map f xs) = (\<Sum>j<length xs. f (xs ! j))\<close> by (simp add: sum_list_sum_nth atLeast0LessThan)
  also have \<open>\<dots> \<le> (\<Sum>j<length xs. g (ys ! j))\<close> using assms(2) by (intro sum_mono) simp
  also have \<open>\<dots> = sum_list (map g ys)\<close> using assms(1) by (simp add: sum_list_sum_nth atLeast0LessThan)
  finally show ?thesis .
qed

context elim_prob
begin

definition \<open>q2 = fst (elim_m q)\<close>

lemma q2_parts: \<open>CoreProblem_widths q2 = CoreProblem_widths q\<close> \<open>CoreProblem_defs q2 = D2\<close> \<open>CoreProblem_asserts q2 = eA\<close>
  by (simp_all add: q2_def elim_m_def D2_def eA_def)

lemma q2_ws: \<open>cvar_widths q2 = ews\<close>
  by (simp add: cvar_widths_def q2_parts ews_def)

lemma D2_defs: \<open>cdefs_wt ews [] D2 \<and> cdef_widths ews [] D2 = eds\<close>
  by (rule cdefs_wt_I) (simp_all add: D2(1) len_eds D2_wt)

theorem q2_wt: \<open>cproblem_wt q2\<close>
  using D2_defs wt_A by (simp add: cproblem_wt_def Let_def q2_ws q2_parts)

lemma cwidth_eD: \<open>j < en \<Longrightarrow> cwidth ews eds (eD ! j) = eds ! j\<close>
proof -
  assume j: \<open>j < en\<close>
  have \<open>eds = take j eds @ drop j eds\<close> by simp
  then show ?thesis using wt_width_app[OF wt_D[OF j], of \<open>drop j eds\<close>] eds_nth[OF j] by simp
qed

lemma cwidth_D2: \<open>j < en \<Longrightarrow> cwidth ews eds (D2 ! j) = eds ! j\<close>
proof -
  assume j: \<open>j < en\<close>
  have \<open>eds = take j eds @ drop j eds\<close> by simp
  then show ?thesis using wt_width_app[OF conjunct1[OF D2_wt[OF j]], of \<open>drop j eds\<close>] D2_wt[OF j] by simp
qed

text \<open>The consumed operand occurs as a proper subterm.\<close>
lemma cons_sub:
  assumes \<open>j < en\<close> \<open>2 \<le> kd ! j\<close>
  shows \<open>CoreTerm_Ref (word_of_nat (cons j)) \<in> set (csubterms (eD ! j)) \<and> CoreTerm_Ref (word_of_nat (cons j)) \<noteq> eD ! j\<close>
proof -
  obtain u where u: \<open>u \<in> set (csubterms (eD ! j))\<close> \<open>is_ref (cons j) u\<close> using kd_cons[OF assms] by blast
  obtain i where i: \<open>u = CoreTerm_Ref i\<close> \<open>unat i = cons j\<close> using u(2) by (cases u) (auto simp: is_ref_def)
  have \<open>word_of_nat (cons j) = i\<close> using i(2) by (metis word_unat.Rep_inverse)
  moreover have \<open>eD ! j \<noteq> CoreTerm_Ref i\<close>
    using assms ana(5)[OF assms(1)] free_kind_simps(3)[of eD \<open>take j eds\<close> evc erc \<open>take j kd\<close> i] by auto
  ultimately show ?thesis using u i by auto
qed

lemma D2_size:
  assumes j: \<open>j < en\<close>
  shows \<open>cterm_weight ews eds (D2 ! j) \<le> cterm_weight ews eds (eD ! j) \<and>
    ccount ews eds (D2 ! j) \<le> ccount ews eds (eD ! j) \<and> tbound ews eds (D2 ! j) \<le> tbound ews eds (eD ! j)\<close>
proof -
  have self: \<open>eD ! j \<in> set (csubterms (eD ! j))\<close> using csubterms_self .
  have w: \<open>cwidth ews eds (eD ! j) = eds ! j\<close> using cwidth_eD[OF j] .
  consider (dead) \<open>\<not> live ! j\<close> | (keep) \<open>live ! j\<close> \<open>\<not> 2 \<le> kd ! j\<close> | (rw) \<open>live ! j\<close> \<open>2 \<le> kd ! j\<close> by blast
  then show ?thesis
  proof cases
    case dead
    then have e: \<open>D2 ! j = CoreTerm_Const (replicate (eds ! j) False)\<close> using D2(3)[OF j] by simp
    show ?thesis
      using weight_mem[OF self, of ews eds] tbound_mem[OF self, of ews eds] tbound_size[of \<open>eD ! j\<close> ews eds] w
      unfolding e by (simp add: cterm_weight_def ccount_atom tbound_def)
  next
    case keep
    then show ?thesis using D2(3)[OF j] ana(6)[OF j] by simp
  next
    case rw
    let ?c = \<open>cons j\<close>
    let ?r = \<open>CoreTerm_Ref (word_of_nat ?c) :: CoreTerm\<close>
    note cs = cons_sub[OF j rw(2)]
    have c: \<open>?c < j\<close> using cons_lt[OF j rw(2)] .
    have cu: \<open>unat (word_of_nat ?c :: 64 word) = ?c\<close> using unat_nat c j by simp
    have tk: \<open>take j eds ! ?c = eds ! ?c\<close> using c j len_eds by simp
    have wr: \<open>cwidth ews eds ?r = eds ! ?c\<close> using cu by simp
    have W2: \<open>(eds ! j + 1) ^ 2 + (eds ! ?c + 1) ^ 2 \<le> cterm_weight ews eds (eD ! j)\<close>
      using weight_two[OF cs[THEN conjunct1] cs[THEN conjunct2], of ews eds] w wr by simp
    have T1: \<open>2 * eds ! ?c + 2 \<le> tbound ews eds (eD ! j)\<close> using tbound_mem[OF cs[THEN conjunct1], of ews eds] wr by simp
    have T2: \<open>2 * eds ! j + 2 \<le> tbound ews eds (eD ! j)\<close> using tbound_mem[OF self, of ews eds] w by simp
    have T3: \<open>2 \<le> tbound ews eds (eD ! j)\<close>
      using tbound_size[of \<open>eD ! j\<close> ews eds] size_pos[OF cs[THEN conjunct1] cs[THEN conjunct2]] by simp
    have d: \<open>D2 ! j = rewrite_m (take j eds) ?c (eds ! j)\<close> using D2(3)[OF j] ana(6)[OF j] rw by simp
    note W = kd_width[OF j rw(2)]
    show ?thesis
    proof (cases \<open>eds ! ?c = eds ! j\<close>)
      case True
      then have \<open>D2 ! j = ?r\<close> using d tk by (simp add: rewrite_m_def)
      then show ?thesis using W2 T1 True wr
        by (simp add: cterm_weight_def ccount_atom tbound_def)
    next
      case False
      obtain hi :: \<open>64 word\<close> where hi: \<open>hi = word_of_nat (eds ! j - 1)\<close> by blast
      then have e: \<open>D2 ! j = CoreTerm_Extract hi 0 ?r\<close> using d tk False by (simp add: rewrite_m_def)
      have hu: \<open>unat hi = eds ! j - 1\<close>
        unfolding hi by (rule unat_of_nat_eq) (use W False in simp)
      have w1: \<open>1 \<le> eds ! j\<close> using W False by simp
      show ?thesis using W2 T1 T2 T3 wr hu w1 unfolding e
        by (simp add: cterm_weight_def ccount_atom tbound_def)
    qed
  qed
qed

theorem elim_csize: \<open>csize_bound q2 \<le> csize_bound q\<close>
proof -
  have \<open>sum_list (map (cterm_weight ews eds) D2) \<le> sum_list (map (cterm_weight ews eds) eD)\<close>
    by (rule sum_list_map_nth_le) (simp_all add: D2(1) en_def D2_size)
  then show ?thesis
    using D2_defs D2(1) by (simp add: csize_bound_def Let_def q2_ws q2_parts ews_def eds_def eD_def eA_def en_def)
qed

theorem elim_fuel_lt:
  assumes \<open>2 + sum_list (cvar_widths q) + length (CoreProblem_asserts q) +
     sum_list (map (ccount (cvar_widths q) (cdef_widths (cvar_widths q) [] (CoreProblem_defs q)))
                   (CoreProblem_defs q @ CoreProblem_asserts q)) < 2 ^ 63\<close>
    \<open>length (cvar_widths q) < 2 ^ 63\<close> \<open>length (CoreProblem_defs q) < 2 ^ 63\<close>
    \<open>length (CoreProblem_asserts q) < 2 ^ 63\<close>
    \<open>\<forall>t \<in> set (CoreProblem_defs q @ CoreProblem_asserts q).
       tbound (cvar_widths q) (cdef_widths (cvar_widths q) [] (CoreProblem_defs q)) t < 2 ^ 63\<close>
  shows \<open>fuel_bound q2 < 2 ^ 64\<close>
proof (rule fuel_bound_lt)
  have cc: \<open>sum_list (map (ccount ews eds) D2) \<le> sum_list (map (ccount ews eds) eD)\<close>
    by (rule sum_list_map_nth_le) (simp_all add: D2(1) en_def D2_size)
  show \<open>cproblem_wt q2\<close> by (rule q2_wt)
  show \<open>2 + sum_list (cvar_widths q2) + length (CoreProblem_asserts q2) +
     sum_list (map (ccount (cvar_widths q2) (cdef_widths (cvar_widths q2) [] (CoreProblem_defs q2)))
                   (CoreProblem_defs q2 @ CoreProblem_asserts q2)) < 2 ^ 63\<close>
    using assms(1) cc D2_defs by (simp add: q2_ws q2_parts ews_def eds_def eD_def eA_def)
  show \<open>length (cvar_widths q2) < 2 ^ 63\<close> using assms(2) by (simp add: q2_ws ews_def)
  show \<open>length (CoreProblem_defs q2) < 2 ^ 63\<close> using assms(3) D2(1) by (simp add: q2_parts en_def eD_def)
  show \<open>length (CoreProblem_asserts q2) < 2 ^ 63\<close> using assms(4) by (simp add: q2_parts eA_def)
  show \<open>\<forall>t \<in> set (CoreProblem_defs q2 @ CoreProblem_asserts q2).
       tbound (cvar_widths q2) (cdef_widths (cvar_widths q2) [] (CoreProblem_defs q2)) t < 2 ^ 63\<close>
  proof
    fix t assume t: \<open>t \<in> set (CoreProblem_defs q2 @ CoreProblem_asserts q2)\<close>
    have T: \<open>\<forall>t \<in> set (eD @ eA). tbound ews eds t < 2 ^ 63\<close>
      using assms(5) by (simp add: ews_def eds_def eD_def eA_def)
    show \<open>tbound (cvar_widths q2) (cdef_widths (cvar_widths q2) [] (CoreProblem_defs q2)) t < 2 ^ 63\<close>
    proof (cases \<open>t \<in> set eA\<close>)
      case True
      then show ?thesis using T D2_defs by (simp add: q2_ws q2_parts)
    next
      case False
      then obtain j where j: \<open>j < en\<close> \<open>t = D2 ! j\<close> using t D2(1) by (auto simp: q2_parts in_set_conv_nth)
      have \<open>tbound ews eds (eD ! j) < 2 ^ 63\<close> using T j(1) by (simp add: en_def)
      then show ?thesis using D2_size[OF j(1)] D2_defs j by (simp add: q2_ws q2_parts)
    qed
  qed
qed

end

subsection \<open>Evaluation depends on the variables and definitions a term mentions\<close>

lemma eval_m_cong:
  assumes \<open>\<forall>u \<in> set (csubterms t). \<forall>x. is_var x u \<longrightarrow> vs ! x = vs' ! x\<close>
    \<open>\<forall>u \<in> set (csubterms t). \<forall>x. is_ref x u \<longrightarrow> dv ! x = dv' ! x\<close>
  shows \<open>eval_m vs dv t = eval_m vs' dv' t\<close>
  using assms
proof (induction t)
  case (CoreTerm_Bin op a b)
  have \<open>eval_m vs dv a = eval_m vs' dv' a\<close>
    by (rule CoreTerm_Bin.IH(1)) (use CoreTerm_Bin.prems in auto)
  moreover have \<open>eval_m vs dv b = eval_m vs' dv' b\<close>
    by (rule CoreTerm_Bin.IH(2)) (use CoreTerm_Bin.prems in auto)
  ultimately show ?case by simp
next
  case (CoreTerm_Ite c a b)
  have \<open>eval_m vs dv c = eval_m vs' dv' c\<close>
    by (rule CoreTerm_Ite.IH(1)) (use CoreTerm_Ite.prems in auto)
  moreover have \<open>eval_m vs dv a = eval_m vs' dv' a\<close>
    by (rule CoreTerm_Ite.IH(2)) (use CoreTerm_Ite.prems in auto)
  moreover have \<open>eval_m vs dv b = eval_m vs' dv' b\<close>
    by (rule CoreTerm_Ite.IH(3)) (use CoreTerm_Ite.prems in auto)
  ultimately show ?case by simp
qed (simp_all add: is_var_def is_ref_def)

lemma eval_defs_len: \<open>length (eval_defs_from vs dv D) = length dv + length D\<close>
  by (induction D arbitrary: dv) (simp_all add: eval_defs_from_def)

lemma eval_defs_prefix: \<open>\<exists>e. eval_defs_from vs dv D = dv @ e\<close>
proof (induction D arbitrary: dv)
  case (Cons d D)
  then show ?case by (simp add: eval_defs_from_def) (metis append_assoc)
qed (simp add: eval_defs_from_def)

lemma eval_defs_take:
  assumes \<open>k \<le> length D\<close>
  shows \<open>take k (eval_defs_from vs [] D) = eval_defs_from vs [] (take k D)\<close>
proof -
  have \<open>eval_defs_from vs [] D = eval_defs_from vs (eval_defs_from vs [] (take k D)) (drop k D)\<close>
    unfolding eval_defs_from_def foldl_append[symmetric] by simp
  then obtain e where \<open>eval_defs_from vs [] D = eval_defs_from vs [] (take k D) @ e\<close> using eval_defs_prefix by metis
  then show ?thesis using assms eval_defs_len[of vs \<open>[]\<close> \<open>take k D\<close>] by simp
qed

lemma eval_defs_nth:
  assumes \<open>j < length D\<close>
  shows \<open>eval_defs_from vs [] D ! j = eval_m vs (take j (eval_defs_from vs [] D)) (D ! j)\<close>
proof -
  have \<open>take (Suc j) (eval_defs_from vs [] D) = eval_defs_from vs [] (take j D @ [D ! j])\<close>
    using eval_defs_take[of \<open>Suc j\<close> D vs] assms by (simp add: take_Suc_conv_app_nth)
  also have \<open>\<dots> = eval_defs_from vs [] (take j D) @ [eval_m vs (eval_defs_from vs [] (take j D)) (D ! j)]\<close>
    by (rule eval_defs_from_snoc)
  finally have \<open>take (Suc j) (eval_defs_from vs [] D) ! j = eval_m vs (eval_defs_from vs [] (take j D)) (D ! j)\<close>
    using eval_defs_len[of vs \<open>[]\<close> \<open>take j D\<close>] assms by (simp add: nth_append)
  then show ?thesis using eval_defs_take[of j D vs] assms by simp
qed

subsection \<open>Chains of consumed definitions\<close>

context elim_prob
begin

text \<open>The parent of a consumed definition: the definition that consumes it.\<close>
definition par :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>par j = (LEAST k. k < en \<and> 2 \<le> kd ! k \<and> cons k = j)\<close>

lemma par:
  assumes \<open>j < en\<close> \<open>mk ! j = 1\<close>
  shows \<open>par j < en \<and> 2 \<le> kd ! par j \<and> cons (par j) = j \<and> j < par j\<close>
proof -
  obtain i where i: \<open>i < en \<and> 2 \<le> kd ! i \<and> cons i = j\<close> using mk_char(1)[OF assms(1)] assms(2) by blast
  have P: \<open>par j < en \<and> 2 \<le> kd ! par j \<and> cons (par j) = j\<close>
    unfolding par_def by (rule LeastI[of _ i]) (use i in blast)
  then show ?thesis using cons_lt[of \<open>par j\<close>] by auto
qed

lemma mk_cons: \<open>k < en \<Longrightarrow> 2 \<le> kd ! k \<Longrightarrow> mk ! cons k = 1\<close>
  using mk_char(1)[of \<open>cons k\<close>] cons_lt[of k] by auto

lemma par_cons:
  assumes \<open>k < en\<close> \<open>2 \<le> kd ! k\<close>
  shows \<open>par (cons k) = k\<close>
proof -
  have c: \<open>cons k < en\<close> using cons_lt[OF assms] assms(1) by simp
  note P = par[OF c mk_cons[OF assms]]
  show ?thesis using cons_unique[OF _ assms(1) _ assms(2)] P by blast
qed

primrec tp_f :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>tp_f 0 j = j\<close>
| \<open>tp_f (Suc f) j = (if j < en \<and> mk ! j = 1 then tp_f f (par j) else j)\<close>

lemma tp_f_eq: \<open>en \<le> f + j \<Longrightarrow> en \<le> f' + j \<Longrightarrow> tp_f f j = tp_f f' j\<close>
proof (induction f arbitrary: j f')
  case 0
  then show ?case by (cases f') simp_all
next
  case (Suc g)
  show ?case
  proof (cases \<open>j < en \<and> mk ! j = 1\<close>)
    case True
    then obtain g' where g': \<open>f' = Suc g'\<close> using Suc.prems by (cases f') auto
    have \<open>j < par j\<close> using par True by blast
    then show ?thesis using Suc.IH[of \<open>par j\<close> g'] Suc.prems True g' by simp
  next
    case False
    then show ?thesis using False by (cases f') auto
  qed
qed

text \<open>The top of the chain of a definition: itself unless it is consumed.\<close>
definition tp :: \<open>nat \<Rightarrow> nat\<close> where \<open>tp j = tp_f en j\<close>

lemma tp_non: \<open>j < en \<Longrightarrow> mk ! j \<noteq> 1 \<Longrightarrow> tp j = j\<close>
  by (cases en) (simp_all add: tp_def)

lemma tp_par: \<open>j < en \<Longrightarrow> mk ! j = 1 \<Longrightarrow> tp j = tp (par j)\<close>
proof -
  assume j: \<open>j < en\<close> \<open>mk ! j = 1\<close>
  then obtain g where g: \<open>en = Suc g\<close> by (cases en) auto
  have \<open>j < par j\<close> using par j by blast
  then show ?thesis using j g tp_f_eq[of g \<open>par j\<close> en] by (simp add: tp_def)
qed

lemma tp_props: \<open>j < en \<Longrightarrow> j \<le> tp j \<and> tp j < en \<and> mk ! tp j \<noteq> 1\<close>
proof (induction \<open>en - j\<close> arbitrary: j rule: less_induct)
  case less
  show ?case
  proof (cases \<open>mk ! j = 1\<close>)
    case True
    note P = par[OF less.prems True]
    have \<open>en - par j < en - j\<close> using P less.prems by (meson diff_less_mono2)
    then show ?thesis using less.hyps[of \<open>par j\<close>] P tp_par[OF less.prems True] by simp
  next
    case False
    then show ?thesis using tp_non less.prems by simp
  qed
qed

primrec leaf_f :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>leaf_f 0 j = j\<close>
| \<open>leaf_f (Suc f) j = (if j < en \<and> 2 \<le> kd ! j then leaf_f f (cons j) else j)\<close>

lemma leaf_f_eq: \<open>j < f \<Longrightarrow> j < f' \<Longrightarrow> leaf_f f j = leaf_f f' j\<close>
proof (induction f arbitrary: j f')
  case 0
  then show ?case by simp
next
  case (Suc g)
  obtain g' where g': \<open>f' = Suc g'\<close> using Suc.prems by (cases f') auto
  show ?case
  proof (cases \<open>j < en \<and> 2 \<le> kd ! j\<close>)
    case True
    have \<open>cons j < j\<close> using cons_lt True by blast
    then show ?thesis using Suc.IH[of \<open>cons j\<close> g'] Suc.prems True g' by simp
  next
    case False
    then show ?thesis using g' by auto
  qed
qed

text \<open>The bottom of the chain of a definition.\<close>
definition leaf :: \<open>nat \<Rightarrow> nat\<close> where \<open>leaf j = leaf_f en j\<close>

lemma leaf_stop: \<open>j < en \<Longrightarrow> \<not> 2 \<le> kd ! j \<Longrightarrow> leaf j = j\<close>
  by (cases en) (simp_all add: leaf_def)

lemma leaf_step: \<open>j < en \<Longrightarrow> 2 \<le> kd ! j \<Longrightarrow> leaf j = leaf (cons j)\<close>
proof -
  assume j: \<open>j < en\<close> \<open>2 \<le> kd ! j\<close>
  then obtain g where g: \<open>en = Suc g\<close> by (cases en) auto
  have \<open>cons j < j\<close> using cons_lt j by blast
  then show ?thesis using j g leaf_f_eq[of \<open>cons j\<close> g en] by (simp add: leaf_def)
qed

lemma leaf_props:
  \<open>j < en \<Longrightarrow> kd ! j \<noteq> 0 \<Longrightarrow> kd ! leaf j = 1 \<and> leaf j \<le> j \<and> eds ! j \<le> eds ! leaf j \<and> tp (leaf j) = tp j\<close>
proof (induction j rule: less_induct)
  case (less j)
  show ?case
  proof (cases \<open>2 \<le> kd ! j\<close>)
    case True
    have c: \<open>cons j < j\<close> \<open>kd ! cons j \<noteq> 0\<close> using kd_cons[OF less.prems(1) True] by simp_all
    note IH = less.IH[OF c(1) _ c(2)]
    have \<open>tp (cons j) = tp j\<close>
      using tp_par[of \<open>cons j\<close>] mk_cons par_cons less.prems(1) True c(1) by simp
    then show ?thesis using IH leaf_step[OF less.prems(1) True] kd_width[OF less.prems(1) True] c less.prems(1)
      by simp
  next
    case False
    then have \<open>kd ! j = 1\<close> using less.prems by simp
    then show ?thesis using leaf_stop[OF less.prems(1)] False by simp
  qed
qed

end

subsection \<open>A model of the problem gives a model of the eliminated problem\<close>

lemma bzext_take: \<open>length a \<le> w \<Longrightarrow> take (length a) (bzext_m a w) = a\<close>
  by (rule nth_equalityI) (simp_all add: bzext_m_def)

lemma bzext_id: \<open>length a = w \<Longrightarrow> bzext_m a w = a\<close>
  by (rule nth_equalityI) (simp_all add: bzext_m_def)

lemma bextract_take: \<open>Suc hi \<le> length a \<Longrightarrow> bextract_m a hi 0 = take (Suc hi) a\<close>
  by (rule nth_equalityI) (simp_all add: bextract_m_def nth_map_upt del: upt_Suc)

lemma cwt_ref_lt: \<open>cwt ws ds t \<Longrightarrow> u \<in> set (csubterms t) \<Longrightarrow> is_ref x u \<Longrightarrow> x < length ds\<close>
  using wt_sub[of ws ds t u] by (cases u) (auto simp: is_ref_def)

lemma cwt_var_lt: \<open>cwt ws ds t \<Longrightarrow> u \<in> set (csubterms t) \<Longrightarrow> is_var x u \<Longrightarrow> x < length ws\<close>
  using wt_sub[of ws ds t u] by (cases u) (auto simp: is_var_def)

text \<open>The values of the definitions under an assignment: each is the value of its term.\<close>
lemma eval_defs_props:
  assumes \<open>cdefs_wt ws [] D\<close> \<open>ws = map length m\<close>
  shows \<open>map length (eval_defs_from m [] D) = cdef_widths ws [] D\<close>
    \<open>j < length D \<Longrightarrow> eval_defs_from m [] D ! j = eval_m m (eval_defs_from m [] D) (D ! j)\<close>
proof -
  show \<open>map length (eval_defs_from m [] D) = cdef_widths ws [] D\<close>
    using eval_defs_from[OF assms(1,2), of \<open>[]\<close>] by simp
  assume j: \<open>j < length D\<close>
  have w: \<open>cwt ws (cdef_widths ws [] (take j D)) (D ! j)\<close> using cdefs_wt_nth[OF assms(1) j] .
  have l: \<open>length (cdef_widths ws [] (take j D)) = j\<close> using j by (simp add: cdef_widths_length)
  have \<open>eval_m m (take j (eval_defs_from m [] D)) (D ! j) = eval_m m (eval_defs_from m [] D) (D ! j)\<close>
    using cwt_ref_lt[OF w] l eval_defs_len[of m \<open>[]\<close> D] j by (intro eval_m_cong) auto
  then show \<open>eval_defs_from m [] D ! j = eval_m m (eval_defs_from m [] D) (D ! j)\<close>
    using eval_defs_nth[OF j] by simp
qed

lemma csat_bits:
  assumes \<open>cproblem_wt p\<close> \<open>map length m = cvar_widths p\<close>
  shows \<open>csatisfies p m \<longleftrightarrow> (\<forall>t \<in> set (CoreProblem_asserts p). bits_nat (eval_m m (eval_defs_m p m) t) = 1)\<close>
proof -
  let ?ws = \<open>cvar_widths p\<close> and ?D = \<open>CoreProblem_defs p\<close>
  have dw: \<open>cdefs_wt ?ws [] ?D\<close> using assms(1) by (simp add: cproblem_wt_def Let_def)
  note E = eval_defs_m_correct[OF dw assms(2)[symmetric]]
  have H: \<open>bits_nat (eval_m m (eval_defs_m p m) t) =
      ceval ?ws (cdef_widths ?ws [] ?D) (map bits_nat m) (cdef_values ?ws [] (map bits_nat m) [] ?D) t\<close>
    if \<open>t \<in> set (CoreProblem_asserts p)\<close> for t
  proof -
    have \<open>cwt ?ws (cdef_widths ?ws [] ?D) t\<close> using assms(1) that by (simp add: cproblem_wt_def Let_def)
    note C = eval_m_correct[OF this assms(2)[symmetric] conjunct1[OF E, symmetric]]
    show ?thesis using conjunct2[OF C] conjunct2[OF E] by (simp only:)
  qed
  show ?thesis
    unfolding csatisfies_def Let_def
  proof (intro iffI ballI)
    fix t assume A: \<open>\<forall>t \<in> set (CoreProblem_asserts p).
      ceval ?ws (cdef_widths ?ws [] ?D) (map bits_nat m) (cdef_values ?ws [] (map bits_nat m) [] ?D) t = 1\<close>
      and t: \<open>t \<in> set (CoreProblem_asserts p)\<close>
    have \<open>ceval ?ws (cdef_widths ?ws [] ?D) (map bits_nat m) (cdef_values ?ws [] (map bits_nat m) [] ?D) t = 1\<close>
      using A t by blast
    with H[OF t] show \<open>bits_nat (eval_m m (eval_defs_m p m) t) = 1\<close> by (rule trans)
  next
    fix t assume A: \<open>\<forall>t \<in> set (CoreProblem_asserts p). bits_nat (eval_m m (eval_defs_m p m) t) = 1\<close>
      and t: \<open>t \<in> set (CoreProblem_asserts p)\<close>
    have \<open>bits_nat (eval_m m (eval_defs_m p m) t) = 1\<close> using A t by blast
    with H[OF t, symmetric]
    show \<open>ceval ?ws (cdef_widths ?ws [] ?D) (map bits_nat m) (cdef_values ?ws [] (map bits_nat m) [] ?D) t = 1\<close>
      by (rule trans)
  qed
qed

context elim_prob
begin

definition isleaf :: \<open>nat \<Rightarrow> bool\<close> where
  \<open>isleaf x = (\<exists>l<en. kd ! l = 1 \<and> is_var x (eD ! l))\<close>

definition ldef :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>ldef x = (SOME l. l < en \<and> kd ! l = 1 \<and> is_var x (eD ! l))\<close>

lemma ldef: \<open>isleaf x \<Longrightarrow> ldef x < en \<and> kd ! ldef x = 1 \<and> is_var x (eD ! ldef x)\<close>
  unfolding isleaf_def ldef_def by (rule someI_ex)

text \<open>The variable of a leaf occurs in its definition only.\<close>
lemma leaf_var_unique:
  assumes \<open>l < en\<close> \<open>kd ! l = 1\<close> \<open>is_var x (eD ! l)\<close> \<open>k < en\<close> \<open>u \<in> set (csubterms (eD ! k))\<close> \<open>is_var x u\<close>
  shows \<open>k = l\<close>
proof -
  obtain i where i: \<open>eD ! l = CoreTerm_Var i\<close> \<open>vcnt (eD @ eA) (unat i) = 1\<close> using kd_1[OF assms(1,2)] by blast
  have x: \<open>x = unat i\<close> using assms(3) i(1) by (simp add: is_var_def)
  show ?thesis using var_unique[of x k l u \<open>eD ! l\<close>] i x assms by (simp add: csubterms_self)
qed

lemma leaf_var_not_A:
  assumes \<open>l < en\<close> \<open>kd ! l = 1\<close> \<open>is_var x (eD ! l)\<close> \<open>t \<in> set eA\<close> \<open>u \<in> set (csubterms t)\<close> \<open>is_var x u\<close>
  shows False
proof -
  obtain i where i: \<open>eD ! l = CoreTerm_Var i\<close> \<open>vcnt (eD @ eA) (unat i) = 1\<close> using kd_1[OF assms(1,2)] by blast
  have x: \<open>x = unat i\<close> using assms(3) i(1) by (simp add: is_var_def)
  show False using var_not_A[of x l \<open>eD ! l\<close> t u] i x assms by (simp add: csubterms_self)
qed

text \<open>A consumed definition is referred to by its parent only.\<close>
lemma member_ref:
  assumes \<open>x < en\<close> \<open>mk ! x = 1\<close> \<open>k < en\<close> \<open>u \<in> set (csubterms (eD ! k))\<close> \<open>is_ref x u\<close>
  shows \<open>k = par x\<close>
proof -
  note P = par[OF assms(1,2)]
  obtain u' where u': \<open>u' \<in> set (csubterms (eD ! par x))\<close> \<open>is_ref x u'\<close> using kd_cons[of \<open>par x\<close>] P by auto
  have \<open>rcnt (eD @ eA) x = 1\<close> using kd_cons[of \<open>par x\<close>] P by auto
  then show ?thesis using ref_unique[of x k \<open>par x\<close> u u'] P assms u' by simp
qed

lemma member_not_A:
  assumes \<open>x < en\<close> \<open>mk ! x = 1\<close> \<open>t \<in> set eA\<close> \<open>u \<in> set (csubterms t)\<close> \<open>is_ref x u\<close>
  shows False
proof -
  note P = par[OF assms(1,2)]
  obtain u' where u': \<open>u' \<in> set (csubterms (eD ! par x))\<close> \<open>is_ref x u'\<close> using kd_cons[of \<open>par x\<close>] P by auto
  have \<open>rcnt (eD @ eA) x = 1\<close> using kd_cons[of \<open>par x\<close>] P by auto
  then show False using ref_not_A[of x \<open>par x\<close> u' t u] P assms u' by simp
qed

lemma kd0_not_member: \<open>j < en \<Longrightarrow> kd ! j = 0 \<Longrightarrow> mk ! j \<noteq> 1\<close>
  using mk_char(1) kd_cons by fastforce

text \<open>The variable at the bottom of the chain of a free definition.\<close>
definition lvar :: \<open>nat \<Rightarrow> nat\<close> where \<open>lvar j = var_index_m (eD ! leaf j)\<close>

lemma lvar:
  assumes \<open>j < en\<close> \<open>kd ! j \<noteq> 0\<close>
  shows \<open>lvar j < length ews \<and> ews ! lvar j = eds ! leaf j \<and> isleaf (lvar j) \<and> ldef (lvar j) = leaf j \<and>
    eD ! leaf j = CoreTerm_Var (word_of_nat (lvar j))\<close>
proof -
  note L = leaf_props[OF assms]
  have ll: \<open>leaf j < en\<close> using L assms(1) by simp
  obtain i where i: \<open>eD ! leaf j = CoreTerm_Var i\<close> \<open>unat i < length ews\<close> using kd_1[OF ll] L by blast
  have lv: \<open>lvar j = unat i\<close> using i by (simp add: lvar_def var_index_m_def)
  have iv: \<open>is_var (lvar j) (eD ! leaf j)\<close> using i lv by (simp add: is_var_def)
  have il: \<open>isleaf (lvar j)\<close> using ll L iv by (auto simp: isleaf_def)
  have \<open>ldef (lvar j) = leaf j\<close>
    using ldef[OF il] leaf_var_unique[OF ll _ iv, of \<open>ldef (lvar j)\<close> \<open>eD ! ldef (lvar j)\<close>] L csubterms_self by auto
  moreover have \<open>ews ! lvar j = eds ! leaf j\<close> using eds_nth[OF ll] i lv by simp
  ultimately show ?thesis using i lv il by simp
qed

definition m2_of :: \<open>bool list list \<Rightarrow> bool list list\<close> where
  \<open>m2_of m = map (\<lambda>x. if isleaf x then bzext_m (eval_defs_m q m ! tp (ldef x)) (ews ! x) else m ! x) [0..<length ews]\<close>

theorem elim_complete:
  assumes M: \<open>cis_model q m\<close>
  shows \<open>cis_model q2 (m2_of m)\<close>
proof -
  have ml: \<open>map length m = ews\<close> using M by (simp add: cis_model_def cis_assignment_def ews_def)
  define dvb where \<open>dvb = eval_defs_m q m\<close>
  define m2 where \<open>m2 = m2_of m\<close>
  define dv2b where \<open>dv2b = eval_defs_m q2 m2\<close>
  have m2l: \<open>length m2 = length ews\<close> by (simp add: m2_def m2_of_def)
  have m2n: \<open>x < length ews \<Longrightarrow> m2 ! x = (if isleaf x then bzext_m (dvb ! tp (ldef x)) (ews ! x) else m ! x)\<close> for x
    by (simp add: m2_def m2_of_def dvb_def)
  have ml2: \<open>map length m2 = ews\<close>
  proof (rule nth_equalityI)
    show \<open>length (map length m2) = length ews\<close> using m2l by simp
  next
    fix x assume \<open>x < length (map length m2)\<close>
    then have x: \<open>x < length ews\<close> using m2l by simp
    have \<open>length (m ! x) = ews ! x\<close> using ml x by (metis length_map nth_map)
    then show \<open>map length m2 ! x = ews ! x\<close> using m2n[OF x] x m2l by (simp add: bzext_m_def)
  qed
  have dvbP: \<open>map length dvb = eds\<close> \<open>j < en \<Longrightarrow> dvb ! j = eval_m m dvb (eD ! j)\<close> for j
    using eval_defs_props[OF dwt ml[symmetric]] by (simp_all add: dvb_def eval_defs_m_def eds_def en_def eD_def)
  have dv2P: \<open>map length dv2b = eds\<close> \<open>j < en \<Longrightarrow> dv2b ! j = eval_m m2 dv2b (D2 ! j)\<close> for j
    using eval_defs_props[OF conjunct1[OF D2_defs] ml2[symmetric]] D2_defs D2(1)
    by (simp_all add: dv2b_def eval_defs_m_def q2_parts)
  have dvbl: \<open>j < en \<Longrightarrow> length (dvb ! j) = eds ! j\<close> for j using dvbP(1) len_eds by (metis nth_map length_map)
  have dv2l: \<open>j < en \<Longrightarrow> length (dv2b ! j) = eds ! j\<close> for j using dv2P(1) len_eds by (metis nth_map length_map)
  have claim: \<open>j < en \<Longrightarrow> live ! j \<Longrightarrow> (mk ! j \<noteq> 1 \<longrightarrow> dv2b ! j = dvb ! j) \<and>
      (kd ! j \<noteq> 0 \<longrightarrow> dv2b ! j = take (eds ! j) (m2 ! lvar j))\<close> for j
  proof (induction j rule: less_induct)
    case (less j)
    note j = less.prems(1) and lj = less.prems(2)
    consider (k0) \<open>kd ! j = 0\<close> | (k1) \<open>kd ! j = 1\<close> | (k2) \<open>2 \<le> kd ! j\<close> by linarith
    then show ?case
    proof cases
      case k0
      have d: \<open>D2 ! j = eD ! j\<close> using D2(3)[OF j] ana(6)[OF j] lj k0 by simp
      have refs: \<open>dv2b ! x = dvb ! x\<close> if u: \<open>u \<in> set (csubterms (eD ! j))\<close> \<open>is_ref x u\<close> for u x
      proof -
        have x: \<open>x < j\<close> using ref_lt_D[OF j u] .
        have lx: \<open>live ! x\<close> using D2(4)[OF j lj] ana(6)[OF j] k0 u by simp
        have mx: \<open>mk ! x \<noteq> 1\<close>
        proof
          assume mx1: \<open>mk ! x = 1\<close>
          then have \<open>j = par x\<close> using member_ref[of x j u] x j u by simp
          then show False using par[of x] mx1 k0 x j by auto
        qed
        show ?thesis using less.IH[of x] x j lx mx by auto
      qed
      have vars: \<open>m2 ! x = m ! x\<close> if u: \<open>u \<in> set (csubterms (eD ! j))\<close> \<open>is_var x u\<close> for u x
      proof -
        have xl: \<open>x < length ews\<close> using cwt_var_lt[OF wt_D'[OF j] u] .
        have \<open>\<not> isleaf x\<close>
        proof
          assume \<open>isleaf x\<close>
          note L = ldef[OF this]
          have \<open>j = ldef x\<close> using leaf_var_unique[of \<open>ldef x\<close> x j u] L j u by simp
          then show False using L k0 by simp
        qed
        then show ?thesis using m2n[OF xl] by simp
      qed
      have \<open>eval_m m2 dv2b (eD ! j) = eval_m m dvb (eD ! j)\<close>
        using refs vars by (intro eval_m_cong) auto
      then have \<open>dv2b ! j = dvb ! j\<close> using dv2P(2)[OF j] dvbP(2)[OF j] d by simp
      then show ?thesis using k0 by simp
    next
      case k1
      obtain i where i: \<open>eD ! j = CoreTerm_Var i\<close> \<open>unat i < length ews\<close> using kd_1[OF j k1] by blast
      have d: \<open>D2 ! j = eD ! j\<close> using D2(3)[OF j] ana(6)[OF j] lj k1 by simp
      have lf: \<open>leaf j = j\<close> using leaf_stop[OF j] k1 by simp
      have lv: \<open>lvar j = unat i\<close> by (simp add: lvar_def lf i var_index_m_def)
      have w: \<open>ews ! unat i = eds ! j\<close> using eds_nth[OF j] i by simp
      have e: \<open>dv2b ! j = m2 ! unat i\<close> using dv2P(2)[OF j] d i by simp
      have len: \<open>length (m2 ! unat i) = eds ! j\<close> using ml2 i w by (metis nth_map m2l)
      have U2: \<open>dv2b ! j = take (eds ! j) (m2 ! lvar j)\<close> using e len lv by simp
      have U1: \<open>dv2b ! j = dvb ! j\<close> if mj: \<open>mk ! j \<noteq> 1\<close>
      proof -
        note LV = lvar[OF j, unfolded lf lv] 
        have \<open>m2 ! unat i = bzext_m (dvb ! tp j) (ews ! unat i)\<close> using m2n[OF i(2)] LV k1 by simp
        then show ?thesis using e tp_non[OF j mj] bzext_id[of \<open>dvb ! j\<close>] dvbl[OF j] w by simp
      qed
      show ?thesis using U1 U2 k1 by simp
    next
      case k2
      let ?c = \<open>cons j\<close>
      have c: \<open>?c < j\<close> \<open>kd ! ?c \<noteq> 0\<close> using kd_cons[OF j k2] by simp_all
      have cl: \<open>?c < en\<close> using c j by simp
      have cu: \<open>unat (word_of_nat ?c :: 64 word) = ?c\<close> using unat_nat cl by simp
      have tk: \<open>take j eds ! ?c = eds ! ?c\<close> using c j len_eds by simp
      have d1j: \<open>d1 ! j = rewrite_m (take j eds) ?c (eds ! j)\<close> using ana(6)[OF j] k2 by simp
      have d: \<open>D2 ! j = d1 ! j\<close> using D2(3)[OF j] lj by simp
      have \<open>CoreTerm_Ref (word_of_nat ?c) \<in> set (csubterms (d1 ! j))\<close> using d1j by (simp add: rewrite_m_def)
      moreover have \<open>is_ref ?c (CoreTerm_Ref (word_of_nat ?c))\<close> using cu by (simp add: is_ref_def)
      ultimately have lc: \<open>live ! ?c\<close> using D2(4)[OF j lj] by blast
      have IHc: \<open>dv2b ! ?c = take (eds ! ?c) (m2 ! lvar ?c)\<close> using less.IH[of ?c] c cl lc by auto
      have lvc: \<open>lvar ?c = lvar j\<close> using leaf_step[OF j k2] by (simp add: lvar_def)
      note W = kd_width[OF j k2]
      have U2: \<open>dv2b ! j = take (eds ! j) (m2 ! lvar j)\<close>
      proof (cases \<open>eds ! ?c = eds ! j\<close>)
        case True
        then have \<open>D2 ! j = CoreTerm_Ref (word_of_nat ?c)\<close> using d d1j tk by (simp add: rewrite_m_def)
        then show ?thesis using dv2P(2)[OF j] cu IHc lvc True by simp
      next
        case False
        obtain hi :: \<open>64 word\<close> where hi: \<open>hi = word_of_nat (eds ! j - 1)\<close> by blast
        then have e: \<open>D2 ! j = CoreTerm_Extract hi 0 (CoreTerm_Ref (word_of_nat ?c))\<close>
          using d d1j tk False by (simp add: rewrite_m_def)
        have hu: \<open>unat hi = eds ! j - 1\<close> unfolding hi by (rule unat_of_nat_eq) (use W False in simp)
        have \<open>dv2b ! j = bextract_m (dv2b ! ?c) (unat hi) 0\<close> using dv2P(2)[OF j] e cu by simp
        also have \<open>\<dots> = take (eds ! j) (dv2b ! ?c)\<close>
          using bextract_take[of \<open>unat hi\<close> \<open>dv2b ! ?c\<close>] hu W False dv2l[OF cl] by simp
        finally show ?thesis using IHc lvc W by (simp add: min_def)
      qed
      have U1: \<open>dv2b ! j = dvb ! j\<close> if mj: \<open>mk ! j \<noteq> 1\<close>
      proof -
        have k0: \<open>kd ! j \<noteq> 0\<close> using k2 by simp
        note LV = lvar[OF j k0]
        note LP = leaf_props[OF j k0]
        have \<open>m2 ! lvar j = bzext_m (dvb ! tp (leaf j)) (ews ! lvar j)\<close> using m2n LV by simp
        then have \<open>m2 ! lvar j = bzext_m (dvb ! j) (ews ! lvar j)\<close> using LP tp_non[OF j mj] by simp
        moreover have \<open>length (dvb ! j) \<le> ews ! lvar j\<close> using dvbl[OF j] LV LP by simp
        ultimately show ?thesis using U2 bzext_take dvbl[OF j] by metis
      qed
      show ?thesis using U1 U2 by simp
    qed
  qed
  have A: \<open>eval_m m2 dv2b t = eval_m m dvb t\<close> if t: \<open>t \<in> set eA\<close> for t
  proof (rule eval_m_cong)
    show \<open>\<forall>u \<in> set (csubterms t). \<forall>x. is_var x u \<longrightarrow> m2 ! x = m ! x\<close>
    proof (intro ballI allI impI)
      fix u x assume u: \<open>u \<in> set (csubterms t)\<close> \<open>is_var x u\<close>
      have xl: \<open>x < length ews\<close> using cwt_var_lt[OF conjunct1[OF wt_A[OF t]] u] .
      have \<open>\<not> isleaf x\<close> using ldef leaf_var_not_A t u by blast
      then show \<open>m2 ! x = m ! x\<close> using m2n[OF xl] by simp
    qed
    show \<open>\<forall>u \<in> set (csubterms t). \<forall>x. is_ref x u \<longrightarrow> dv2b ! x = dvb ! x\<close>
    proof (intro ballI allI impI)
      fix u x assume u: \<open>u \<in> set (csubterms t)\<close> \<open>is_ref x u\<close>
      have x: \<open>x < en\<close> using ref_lt_A[OF t u] .
      have \<open>mk ! x \<noteq> 1\<close> using member_not_A[OF x _ t u] by blast
      then show \<open>dv2b ! x = dvb ! x\<close> using claim[OF x D2(5)[OF t u]] by simp
    qed
  qed
  have \<open>csatisfies q m\<close> using M by (simp add: cis_model_def)
  then have S: \<open>\<forall>t \<in> set eA. bits_nat (eval_m m dvb t) = 1\<close>
    using csat_bits[OF wt] ml by (simp add: dvb_def eA_def ews_def)
  have \<open>csatisfies q2 m2\<close>
    using csat_bits[OF q2_wt] ml2 S A by (simp add: q2_ws q2_parts dv2b_def)
  then show ?thesis using ml2 by (simp add: cis_model_def cis_assignment_def q2_ws m2_def)
qed

end

subsection \<open>Inverting an operation on bit lists\<close>

lemma bits_nat_inj: \<open>length a = length b \<Longrightarrow> bits_nat a = bits_nat b \<Longrightarrow> a = b\<close>
  by (rule nth_equalityI) (simp_all, metis bit_bits_nat)

lemma beq_eq: \<open>length a = length b \<Longrightarrow> beq_m a b = (a = b)\<close>
  using beq_m bits_nat_inj by blast

lemma inv_not: \<open>bnot_m (bnot_m v) = v\<close>
  by (simp add: bnot_m_def comp_def)

lemma inv_add:
  assumes \<open>length ob = length v\<close>
  shows \<open>fst (badd_m (fst (badd_m v (bnot_m ob) True)) ob False) = v\<close>
    \<open>fst (badd_m ob (fst (badd_m v (bnot_m ob) True)) False) = v\<close>
    \<open>length (fst (badd_m v (bnot_m ob) True)) = length v\<close>
proof -
  let ?w = \<open>length v\<close>
  let ?a = \<open>fst (badd_m v (bnot_m ob) True)\<close>
  have lo: \<open>bits_nat ob < 2 ^ ?w\<close> \<open>bits_nat v < 2 ^ ?w\<close> using bits_nat_lt assms by metis+
  have a: \<open>bits_nat ?a = (bits_nat v + (2 ^ ?w - 1 - bits_nat ob) + 1) mod 2 ^ ?w\<close>
    using bits_nat_badd[of v \<open>bnot_m ob\<close> True] bits_nat_bnot[of ob] assms by simp
  have s: \<open>(bits_nat v + (2 ^ ?w - 1 - bits_nat ob) + 1 + bits_nat ob) mod 2 ^ ?w = bits_nat v\<close>
  proof -
    have \<open>bits_nat v + (2 ^ ?w - 1 - bits_nat ob) + 1 + bits_nat ob = bits_nat v + 2 ^ ?w\<close> using lo by simp
    then show ?thesis using lo by simp
  qed
  have la: \<open>length ?a = ?w\<close> by simp
  show \<open>length (fst (badd_m v (bnot_m ob) True)) = length v\<close> by simp
  have \<open>bits_nat (fst (badd_m ?a ob False)) = bits_nat v\<close>
    using bits_nat_badd[of ?a ob False] la assms a s by (simp add: mod_add_left_eq)
  then show \<open>fst (badd_m ?a ob False) = v\<close> using la by (intro bits_nat_inj) simp_all
  have \<open>bits_nat (fst (badd_m ob ?a False)) = bits_nat v\<close>
    using bits_nat_badd[of ob ?a False] la assms a s by (simp add: mod_add_right_eq add.commute)
  then show \<open>fst (badd_m ob ?a False) = v\<close> using la assms by (intro bits_nat_inj) simp_all
qed

lemma inv_xor:
  assumes \<open>length ob = length v\<close>
  shows \<open>bbitw_m BinOp_Xor (bbitw_m BinOp_Xor v ob) ob = v\<close> \<open>bbitw_m BinOp_Xor ob (bbitw_m BinOp_Xor v ob) = v\<close>
    \<open>length (bbitw_m BinOp_Xor v ob) = length v\<close>
  using assms by (auto intro!: nth_equalityI simp: nth_bbitw bop_def)

lemma bits_one: \<open>length (bits_one_m w) = w\<close> \<open>0 < w \<Longrightarrow> bits_nat (bits_one_m w) = 1\<close>
proof -
  show \<open>length (bits_one_m w) = w\<close> by (simp add: bits_one_m_def)
  assume w: \<open>0 < w\<close>
  obtain w' where w': \<open>w = Suc w'\<close> using w by (cases w) auto
  have z: \<open>bits_nat (replicate n False) = 0\<close> for n by (induction n) simp_all
  have \<open>bits_one_m w = True # replicate w' False\<close> using w' by (simp add: bits_one_m_def)
  then show \<open>bits_nat (bits_one_m w) = 1\<close> using z by simp
qed

lemma inv_mul:
  assumes \<open>length v = w\<close>
  shows \<open>bmul_m v (bits_one_m w) = v\<close> \<open>fst (bdivrem_m v (bits_one_m w)) = v\<close>
proof -
  have l: \<open>length (bits_one_m w) = length v\<close> using bits_one(1) assms by simp
  show \<open>bmul_m v (bits_one_m w) = v\<close>
  proof (cases \<open>w = 0\<close>)
    case True
    then show ?thesis using assms bmul_m(1)[OF l[symmetric]] by simp
  next
    case False
    then show ?thesis using bmul_m[OF l[symmetric]] bits_one(2)[of w] assms bits_nat_lt[of v]
      by (intro bits_nat_inj) simp_all
  qed
  show \<open>fst (bdivrem_m v (bits_one_m w)) = v\<close>
  proof (cases \<open>w = 0\<close>)
    case True
    then show ?thesis using assms bdivrem_m(1)[OF l[symmetric]] by simp
  next
    case False
    then show ?thesis using bdivrem_m(1,3)[OF l[symmetric]] bits_one(2)[of w] assms
      by (intro bits_nat_inj) simp_all
  qed
qed

lemma inv_extract:
  assumes \<open>length v = Suc hi - lo\<close> \<open>lo \<le> hi\<close> \<open>hi < w\<close>
  shows \<open>bextract_m (bconcat_m (replicate (w - 1 - hi) False) (bconcat_m v (replicate lo False))) hi lo = v\<close>
    \<open>length (bconcat_m (replicate (w - 1 - hi) False) (bconcat_m v (replicate lo False))) = w\<close>
proof -
  show \<open>length (bconcat_m (replicate (w - 1 - hi) False) (bconcat_m v (replicate lo False))) = w\<close>
    using assms by simp
  show \<open>bextract_m (bconcat_m (replicate (w - 1 - hi) False) (bconcat_m v (replicate lo False))) hi lo = v\<close>
    using assms by (intro nth_equalityI) (auto simp: bextract_m_def bconcat_m_def nth_append nth_map_upt simp del: upt_Suc)
qed

lemma inv_eq:
  assumes \<open>length v = 1\<close> \<open>0 < length ob\<close>
  shows \<open>[beq_m (if v ! 0 then ob else bnot_m ob) ob] = v\<close> \<open>[beq_m ob (if v ! 0 then ob else bnot_m ob)] = v\<close>
    \<open>length (if v ! 0 then ob else bnot_m ob) = length ob\<close>
proof -
  have ne: \<open>bnot_m ob \<noteq> ob\<close> using assms(2) by (metis bnot_m_def length_greater_0_conv list.map(2) list.sel(1) neq_Nil_conv)
  obtain b where v: \<open>v = [b]\<close> using assms(1) by (cases v) auto
  show \<open>[beq_m (if v ! 0 then ob else bnot_m ob) ob] = v\<close> using ne v by (simp add: beq_eq)
  show \<open>[beq_m ob (if v ! 0 then ob else bnot_m ob)] = v\<close> using ne v by (auto simp: beq_eq)
  show \<open>length (if v ! 0 then ob else bnot_m ob) = length ob\<close> by simp
qed

lemma inv_ite:
  assumes \<open>length v = 1\<close> \<open>ca \<noteq> cb\<close>
  shows \<open>(if [beq_m v [ca]] ! 0 then [ca] else [cb]) = v\<close>
  using assms by (cases v) (auto simp: beq_eq)

lemma eval_m_len:
  assumes \<open>cwt ws ds t\<close> \<open>map length vs = ws\<close>
    \<open>\<forall>u \<in> set (csubterms t). \<forall>x. is_ref x u \<longrightarrow> x < length dv \<and> length (dv ! x) = ds ! x\<close>
  shows \<open>length (eval_m vs dv t) = cwidth ws ds t\<close>
proof -
  define dv' where \<open>dv' = map (\<lambda>x. if x < length dv \<and> length (dv ! x) = ds ! x then dv ! x else replicate (ds ! x) False) [0..<length ds]\<close>
  have l: \<open>ds = map length dv'\<close> by (rule nth_equalityI) (auto simp: dv'_def)
  have \<open>eval_m vs dv t = eval_m vs dv' t\<close>
  proof (rule eval_m_cong)
    show \<open>\<forall>u \<in> set (csubterms t). \<forall>x. is_var x u \<longrightarrow> vs ! x = vs ! x\<close> by simp
    show \<open>\<forall>u \<in> set (csubterms t). \<forall>x. is_ref x u \<longrightarrow> dv ! x = dv' ! x\<close>
      using assms(3) cwt_ref_lt[OF assms(1)] by (auto simp: dv'_def)
  qed
  then show ?thesis using eval_m_correct[OF assms(1) assms(2)[symmetric] l] by simp
qed

lemma csubterms_trans: \<open>v \<in> set (csubterms u) \<Longrightarrow> u \<in> set (csubterms t) \<Longrightarrow> v \<in> set (csubterms t)\<close>
  by (induction t) auto

lemma bit_const_cases: \<open>bit_const_m t < 2 \<Longrightarrow> \<exists>c. t = CoreTerm_Const [c] \<and> bit_const_m t = (if c then 1 else 0)\<close>
proof (cases t)
  case (CoreTerm_Const bs)
  assume b: \<open>bit_const_m t < 2\<close>
  then have \<open>length bs = 1\<close> using CoreTerm_Const by (simp add: bit_const_m_def split: if_splits)
  then obtain c where \<open>bs = [c]\<close> by (cases bs) auto
  then show ?thesis using CoreTerm_Const by (simp add: bit_const_m_def)
qed (simp_all add: bit_const_m_def)

lemma no_ref_of_rcnt0: \<open>rcnt [t] x = 0 \<Longrightarrow> \<forall>u \<in> set (csubterms t). \<not> is_ref x u\<close>
  using rcnt_pos by fastforce

context elim_prob
begin

lemma cons_once:
  assumes \<open>j < en\<close> \<open>2 \<le> kd ! j\<close>
  shows \<open>rcnt [eD ! j] (cons j) = 1\<close>
proof -
  have r1: \<open>rcnt (eD @ eA) (cons j) = 1\<close> and ex: \<open>\<exists>u \<in> set (csubterms (eD ! j)). is_ref (cons j) u\<close>
    using kd_cons[OF assms] by simp_all
  have \<open>rcnt [eD ! j] (cons j) \<le> 1\<close> using rcnt_le[of \<open>eD ! j\<close> \<open>eD @ eA\<close> \<open>cons j\<close>] r1 assms(1) by (simp add: en_def)
  moreover have \<open>0 < rcnt [eD ! j] (cons j)\<close> using ex rcnt_pos by blast
  ultimately show ?thesis by simp
qed

text \<open>What the inversion of a free definition needs: the values of its other operands are final
  (and have their widths), and its variables keep their values.\<close>
definition invpre :: \<open>nat \<Rightarrow> bool list \<Rightarrow> bool list list \<Rightarrow> bool list list \<Rightarrow> bool list list \<Rightarrow> bool list list \<Rightarrow>
    bool list list \<Rightarrow> bool\<close> where
  \<open>invpre j v m dv m' dv' dv2 \<equiv> length v = eds ! j \<and> map length m = ews \<and> map length m' = ews \<and>
     map length dv2 = eds \<and> cons j < length dv' \<and>
     (\<forall>u \<in> set (csubterms (eD ! j)). \<forall>x. is_ref x u \<and> x \<noteq> cons j \<longrightarrow>
        x < length dv \<and> x < length dv' \<and> dv' ! x = dv ! x \<and> length (dv ! x) = eds ! x \<and> dv ! x = eval_m m dv (eD ! x)) \<and>
     (\<forall>u \<in> set (csubterms (eD ! j)). \<forall>x. is_var x u \<longrightarrow> m' ! x = m ! x) \<and>
     (kd ! j = 4 \<longrightarrow> dv ! sec j = bits_one_m (eds ! sec j))\<close>

lemma inv_def:
  assumes j: \<open>j < en\<close> and k2: \<open>2 \<le> kd ! j\<close> and P: \<open>invpre j v m dv m' dv' dv2\<close>
  shows \<open>fst (invert_m (eD ! j) (kd ! j) v m dv dv2) = cons j \<and>
    length (snd (invert_m (eD ! j) (kd ! j) v m dv dv2)) = eds ! cons j \<and>
    (dv' ! cons j = snd (invert_m (eD ! j) (kd ! j) v m dv dv2) \<longrightarrow> eval_m m' dv' (eD ! j) = v)\<close>
proof -
  have lv: \<open>length v = eds ! j\<close> and ml: \<open>map length m = ews\<close> and d2: \<open>map length dv2 = eds\<close>
    and O: \<open>\<forall>u \<in> set (csubterms (eD ! j)). \<forall>x. is_ref x u \<and> x \<noteq> cons j \<longrightarrow>
        x < length dv \<and> x < length dv' \<and> dv' ! x = dv ! x \<and> length (dv ! x) = eds ! x \<and> dv ! x = eval_m m dv (eD ! x)\<close>
    and V: \<open>\<forall>u \<in> set (csubterms (eD ! j)). \<forall>x. is_var x u \<longrightarrow> m' ! x = m ! x\<close>
    and T4: \<open>kd ! j = 4 \<longrightarrow> dv ! sec j = bits_one_m (eds ! sec j)\<close>
    using P unfolding invpre_def by blast+
  have n2: \<open>length dv2 = en\<close> using d2 len_eds by (metis length_map)
  have d2n: \<open>x < en \<Longrightarrow> length (dv2 ! x) = eds ! x\<close> for x using d2 n2 by (metis nth_map)
  have wtj: \<open>cwt ews eds (eD ! j)\<close> using wt_D'[OF j] .
  have E: \<open>cwidth ews eds (eD ! j) = eds ! j\<close> using cwidth_eD[OF j] .
  have once: \<open>rcnt [eD ! j] (cons j) = 1\<close> using cons_once[OF j k2] .
  have cj: \<open>cons j < j\<close> using cons_lt[OF j k2] .
  have sub: \<open>eval_m m' dv' ob = eval_m m dv ob \<and> length (eval_m m dv ob) = cwidth ews eds ob\<close>
    if ob: \<open>ob \<in> set (csubterms (eD ! j))\<close> and nr: \<open>\<forall>u \<in> set (csubterms ob). \<not> is_ref (cons j) u\<close> for ob
  proof -
    have tr: \<open>u \<in> set (csubterms ob) \<Longrightarrow> u \<in> set (csubterms (eD ! j))\<close> for u using csubterms_trans ob by blast
    have \<open>eval_m m' dv' ob = eval_m m dv ob\<close>
      by (rule eval_m_cong) (use O V tr nr in \<open>fastforce+\<close>)
    moreover have \<open>length (eval_m m dv ob) = cwidth ews eds ob\<close>
      by (rule eval_m_len[OF wsub[OF wtj ob] ml]) (use O tr nr in fastforce)
    ultimately show ?thesis by simp
  qed
  note sh = free_kind_shape[OF ana(5)[OF j] k2]
  have tk: \<open>x < j \<Longrightarrow> take j eds ! x = eds ! x\<close> for x using j len_eds by simp
  have fo: \<open>free_once_m (take j kd) erc x \<Longrightarrow> x < j\<close> for x using fo_take j by blast
  consider
      (Not) a where \<open>eD ! j = CoreTerm_Not (CoreTerm_Ref a)\<close> \<open>kd ! j = 2\<close>
    | (Ext) hi lo a where \<open>eD ! j = CoreTerm_Extract hi lo (CoreTerm_Ref a)\<close> \<open>kd ! j = 2\<close>
    | (AX2) op i b where \<open>eD ! j = CoreTerm_Bin op (CoreTerm_Ref i) b\<close> \<open>op = BinOp_Add \<or> op = BinOp_Xor\<close> \<open>kd ! j = 2\<close>
    | (AX3) op a i where \<open>eD ! j = CoreTerm_Bin op a (CoreTerm_Ref i)\<close> \<open>op = BinOp_Add \<or> op = BinOp_Xor\<close> \<open>kd ! j = 3\<close>
    | (Eq2) i b where \<open>eD ! j = CoreTerm_Bin BinOp_Eq (CoreTerm_Ref i) b\<close> \<open>kd ! j = 2\<close> \<open>0 < eds ! unat i\<close>
    | (Eq3) a i where \<open>eD ! j = CoreTerm_Bin BinOp_Eq a (CoreTerm_Ref i)\<close> \<open>kd ! j = 3\<close> \<open>0 < eds ! unat i\<close>
    | (MD) op a b where \<open>eD ! j = CoreTerm_Bin op (CoreTerm_Ref a) (CoreTerm_Ref b)\<close> \<open>op = BinOp_Mul \<or> op = BinOp_Udiv\<close>
        \<open>kd ! j = 4\<close> \<open>unat a \<noteq> unat b\<close>
    | (Ite) x a b where \<open>eD ! j = CoreTerm_Ite (CoreTerm_Ref x) (CoreTerm_Ref a) (CoreTerm_Ref b)\<close> \<open>kd ! j = 2\<close>
        \<open>bit_const_m (eD ! unat a) < 2\<close> \<open>bit_const_m (eD ! unat b) < 2\<close> \<open>bit_const_m (eD ! unat a) \<noteq> bit_const_m (eD ! unat b)\<close>
    using sh fo tk by (elim disjE exE conjE) (blast | metis)+
  then show ?thesis
  proof cases
    case (Not a)
    have c: \<open>cons j = unat a\<close> using Not by (simp add: cons_def consumed_m_def ref_index_m_def)
    have inv: \<open>invert_m (eD ! j) (kd ! j) v m dv dv2 = (unat a, bnot_m v)\<close>
      using Not by (simp add: invert_m_def ref_index_m_def)
    have w: \<open>eds ! unat a = eds ! j\<close> using E Not by simp
    show ?thesis using inv c w lv Not inv_not by simp
  next
    case (Ext hi lo a)
    have c: \<open>cons j = unat a\<close> using Ext by (simp add: cons_def consumed_m_def ref_index_m_def)
    have al: \<open>unat a < en\<close> using c cj j by simp
    have wa: \<open>unat lo \<le> unat hi\<close> \<open>unat hi < eds ! unat a\<close> using wtj Ext by simp_all
    have lv': \<open>length v = Suc (unat hi) - unat lo\<close> using lv E Ext wa by simp
    have inv: \<open>invert_m (eD ! j) (kd ! j) v m dv dv2 =
        (unat a, bconcat_m (replicate (eds ! unat a - 1 - unat hi) False) (bconcat_m v (replicate (unat lo) False)))\<close>
      using Ext n2 d2n[OF al] by (simp add: invert_m_def ref_index_m_def Let_def)
    show ?thesis using inv c inv_extract[OF lv' wa] Ext by simp
  next
    case (AX2 op i b)
    have c: \<open>cons j = unat i\<close> using AX2 by (auto simp: cons_def consumed_m_def ref_index_m_def)
    have \<open>rcnt [b] (unat i) = 0\<close> using once AX2 c by (simp add: rcnt_Bin rcnt_Ref)
    then have S: \<open>eval_m m' dv' b = eval_m m dv b \<and> length (eval_m m dv b) = cwidth ews eds b\<close>
      using sub[of b] AX2 c no_ref_of_rcnt0 by auto
    have w: \<open>cwidth ews eds b = eds ! j\<close> \<open>eds ! unat i = eds ! j\<close> using wtj E AX2 by auto
    let ?o = \<open>eval_m m dv b\<close>
    have lo: \<open>length ?o = length v\<close> using S w lv by simp
    show ?thesis
    proof (cases \<open>op = BinOp_Add\<close>)
      case True
      have inv: \<open>invert_m (eD ! j) (kd ! j) v m dv dv2 = (unat i, fst (badd_m v (bnot_m ?o) True))\<close>
        using AX2 True by (simp add: invert_m_def ref_index_m_def)
      show ?thesis using inv c inv_add[OF lo] S AX2 True w lv by (simp add: eval_bin_m_def)
    next
      case False
      then have X: \<open>op = BinOp_Xor\<close> using AX2 by simp
      have inv: \<open>invert_m (eD ! j) (kd ! j) v m dv dv2 = (unat i, bbitw_m BinOp_Xor v ?o)\<close>
        using AX2 X by (simp add: invert_m_def ref_index_m_def)
      show ?thesis using inv c inv_xor[OF lo] S AX2 X w lv by (simp add: eval_bin_m_def)
    qed
  next
    case (AX3 op a i)
    have c: \<open>cons j = unat i\<close> using AX3 by (auto simp: cons_def consumed_m_def ref_index_m_def)
    have \<open>rcnt [a] (unat i) = 0\<close> using once AX3 c by (simp add: rcnt_Bin rcnt_Ref)
    then have S: \<open>eval_m m' dv' a = eval_m m dv a \<and> length (eval_m m dv a) = cwidth ews eds a\<close>
      using sub[of a] AX3 c no_ref_of_rcnt0 by auto
    have nc: \<open>op \<noteq> BinOp_Concat\<close> \<open>op \<noteq> BinOp_Eq\<close> \<open>op \<noteq> BinOp_Ult\<close> using AX3(2) by auto
    have ww: \<open>cwidth ews eds a = eds ! unat i\<close> using wtj AX3(1) nc by simp
    have we: \<open>cwidth ews eds (eD ! j) = cwidth ews eds a\<close> using AX3(1) nc by (cases op) simp_all
    have w: \<open>cwidth ews eds a = eds ! j\<close> \<open>eds ! unat i = eds ! j\<close> using ww we E by simp_all
    let ?o = \<open>eval_m m dv a\<close>
    have lo: \<open>length ?o = length v\<close> using S w lv by simp
    show ?thesis
    proof (cases \<open>op = BinOp_Add\<close>)
      case True
      have inv: \<open>invert_m (eD ! j) (kd ! j) v m dv dv2 = (unat i, fst (badd_m v (bnot_m ?o) True))\<close>
        using AX3 True by (simp add: invert_m_def ref_index_m_def)
      show ?thesis using inv c inv_add[OF lo] S AX3 True w lv by (simp add: eval_bin_m_def)
    next
      case False
      then have X: \<open>op = BinOp_Xor\<close> using AX3 by simp
      have inv: \<open>invert_m (eD ! j) (kd ! j) v m dv dv2 = (unat i, bbitw_m BinOp_Xor v ?o)\<close>
        using AX3 X by (simp add: invert_m_def ref_index_m_def)
      show ?thesis using inv c inv_xor[OF lo] S AX3 X w lv by (simp add: eval_bin_m_def)
    qed
  next
    case (Eq2 i b)
    have c: \<open>cons j = unat i\<close> using Eq2 by (simp add: cons_def consumed_m_def ref_index_m_def)
    have \<open>rcnt [b] (unat i) = 0\<close> using once Eq2 c by (simp add: rcnt_Bin rcnt_Ref)
    then have S: \<open>eval_m m' dv' b = eval_m m dv b \<and> length (eval_m m dv b) = cwidth ews eds b\<close>
      using sub[of b] Eq2 c no_ref_of_rcnt0 by auto
    have w: \<open>cwidth ews eds b = eds ! unat i\<close> \<open>eds ! j = 1\<close> using wtj E Eq2 by auto
    let ?o = \<open>eval_m m dv b\<close>
    have l1: \<open>length v = 1\<close> \<open>0 < length ?o\<close> using lv w S Eq2 by simp_all
    have inv: \<open>invert_m (eD ! j) (kd ! j) v m dv dv2 = (unat i, if v ! 0 then ?o else bnot_m ?o)\<close>
      using Eq2 by (simp add: invert_m_def ref_index_m_def)
    show ?thesis using inv c inv_eq[OF l1] S Eq2 w by (simp add: eval_bin_m_def)
  next
    case (Eq3 a i)
    have c: \<open>cons j = unat i\<close> using Eq3 by (simp add: cons_def consumed_m_def ref_index_m_def)
    have \<open>rcnt [a] (unat i) = 0\<close> using once Eq3 c by (simp add: rcnt_Bin rcnt_Ref)
    then have S: \<open>eval_m m' dv' a = eval_m m dv a \<and> length (eval_m m dv a) = cwidth ews eds a\<close>
      using sub[of a] Eq3 c no_ref_of_rcnt0 by auto
    have w: \<open>cwidth ews eds a = eds ! unat i\<close> \<open>eds ! j = 1\<close> using wtj E Eq3 by auto
    let ?o = \<open>eval_m m dv a\<close>
    have l1: \<open>length v = 1\<close> \<open>0 < length ?o\<close> using lv w S Eq3 by simp_all
    have inv: \<open>invert_m (eD ! j) (kd ! j) v m dv dv2 = (unat i, if v ! 0 then ?o else bnot_m ?o)\<close>
      using Eq3 by (simp add: invert_m_def ref_index_m_def)
    show ?thesis using inv c inv_eq[OF l1] S Eq3 w by (simp add: eval_bin_m_def)
  next
    case (MD op a b)
    have c: \<open>cons j = unat a\<close> \<open>sec j = unat b\<close> using MD by (simp_all add: cons_def consumed_m_def sec_def second_m_def ref_index_m_def)
    have inv: \<open>invert_m (eD ! j) (kd ! j) v m dv dv2 = (unat a, v)\<close>
      using MD by (auto simp: invert_m_def ref_index_m_def)
    have nc: \<open>op \<noteq> BinOp_Concat\<close> \<open>op \<noteq> BinOp_Eq\<close> \<open>op \<noteq> BinOp_Ult\<close> using MD(2) by auto
    have ww: \<open>eds ! unat a = eds ! unat b\<close> using wtj MD(1) nc by simp
    have we: \<open>cwidth ews eds (eD ! j) = eds ! unat a\<close> using MD(1) nc by (cases op) simp_all
    have w: \<open>eds ! unat a = eds ! j\<close> \<open>eds ! unat b = eds ! j\<close> using ww we E by simp_all
    have rb: \<open>is_ref (unat b) (CoreTerm_Ref b)\<close> \<open>CoreTerm_Ref b \<in> set (csubterms (eD ! j))\<close>
      using MD by (simp_all add: is_ref_def)
    have Ob: \<open>dv' ! unat b = dv ! unat b\<close>
      using O[THEN bspec, OF rb(2), THEN spec, of \<open>unat b\<close>] rb(1) c MD(4) by simp
    have db: \<open>dv' ! unat b = bits_one_m (eds ! j)\<close> using Ob T4 MD(3) c w by simp
    show ?thesis
    proof (cases \<open>op = BinOp_Mul\<close>)
      case True
      then show ?thesis using inv c w lv db MD inv_mul(1)[of v \<open>eds ! j\<close>] by (simp add: eval_bin_m_def)
    next
      case False
      then have U: \<open>op = BinOp_Udiv\<close> using MD by simp
      then show ?thesis using inv c w lv db MD inv_mul(2)[of v \<open>eds ! j\<close>] by (simp add: eval_bin_m_def)
    qed
  next
    case (Ite x a b)
    have c: \<open>cons j = unat x\<close> using Ite by (simp add: cons_def consumed_m_def ref_index_m_def)
    have \<open>rcnt [CoreTerm_Ref a] (unat x) = 0\<close> \<open>rcnt [CoreTerm_Ref b] (unat x) = 0\<close>
      using once Ite(1) c by (simp_all add: rcnt_Ite rcnt_Ref)
    then have ne: \<open>unat a \<noteq> unat x\<close> \<open>unat b \<noteq> unat x\<close> by (simp_all add: rcnt_Ref split: if_splits)
    obtain ca where ca: \<open>eD ! unat a = CoreTerm_Const [ca]\<close> \<open>bit_const_m (eD ! unat a) = (if ca then 1 else 0)\<close>
      using bit_const_cases[OF Ite(3)] by blast
    obtain cb where cb: \<open>eD ! unat b = CoreTerm_Const [cb]\<close> \<open>bit_const_m (eD ! unat b) = (if cb then 1 else 0)\<close>
      using bit_const_cases[OF Ite(4)] by blast
    have cab: \<open>ca \<noteq> cb\<close> using Ite(5) ca(2) cb(2) by (cases ca; cases cb) simp_all
    have ra: \<open>dv' ! unat a = [ca]\<close> \<open>dv ! unat a = [ca]\<close>
      using O Ite ne c ca by (auto simp: is_ref_def)
    have rb: \<open>dv' ! unat b = [cb]\<close> using O Ite ne c cb by (auto simp: is_ref_def)
    have w: \<open>eds ! unat x = 1\<close> \<open>eds ! j = eds ! unat a\<close> using wtj E Ite by auto
    have wa: \<open>eds ! unat a = 1\<close>
    proof -
      have \<open>unat a < j\<close> using wt_D[OF j] Ite(1) len_eds j by simp
      then show ?thesis using eds_nth[of \<open>unat a\<close>] ca j by simp
    qed
    have l1: \<open>length v = 1\<close> using lv w wa by simp
    have inv: \<open>invert_m (eD ! j) (kd ! j) v m dv dv2 = (unat x, [beq_m v [ca]])\<close>
      using Ite ra by (simp add: invert_m_def ref_index_m_def)
    show ?thesis using inv c w ra rb Ite inv_ite[OF l1 cab] by (auto split: if_splits)
  qed
qed

end

subsection \<open>The chain below a free definition\<close>

context elim_prob
begin

primrec below_f :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>below_f 0 j i = (i = j)\<close>
| \<open>below_f (Suc f) j i = (i = j \<or> (j < en \<and> 2 \<le> kd ! j \<and> below_f f (cons j) i))\<close>

lemma below_f_eq: \<open>j < f \<Longrightarrow> j < f' \<Longrightarrow> below_f f j i = below_f f' j i\<close>
proof (induction f arbitrary: j f')
  case 0
  then show ?case by simp
next
  case (Suc g)
  obtain g' where g': \<open>f' = Suc g'\<close> using Suc.prems by (cases f') auto
  show ?case
  proof (cases \<open>j < en \<and> 2 \<le> kd ! j\<close>)
    case True
    have \<open>cons j < j\<close> using cons_lt True by blast
    then show ?thesis using Suc.IH[of \<open>cons j\<close> g'] Suc.prems True g' by simp
  next
    case False
    then show ?thesis using g' by auto
  qed
qed

text \<open>\<open>i\<close> is on the chain of consumed operands from \<open>j\<close> down.\<close>
definition below :: \<open>nat \<Rightarrow> nat \<Rightarrow> bool\<close> where \<open>below j i = below_f (Suc j) j i\<close>

lemma below_self: \<open>below j j\<close>
  by (simp add: below_def)

lemma below_step: \<open>j < en \<Longrightarrow> 2 \<le> kd ! j \<Longrightarrow> below j i \<longleftrightarrow> i = j \<or> below (cons j) i\<close>
  using below_f_eq[of \<open>cons j\<close> j \<open>Suc (cons j)\<close> i] cons_lt by (simp add: below_def)

lemma below_stop: \<open>\<not> (j < en \<and> 2 \<le> kd ! j) \<Longrightarrow> below j i \<longleftrightarrow> i = j\<close>
  by (auto simp: below_def)

lemma below_props: \<open>j < en \<Longrightarrow> below j i \<Longrightarrow> i \<le> j \<and> tp i = tp j\<close>
proof (induction j rule: less_induct)
  case (less j)
  show ?case
  proof (cases \<open>2 \<le> kd ! j\<close>)
    case True
    have c: \<open>cons j < j\<close> using cons_lt less.prems(1) True by blast
    have tc: \<open>tp (cons j) = tp j\<close> using tp_par[of \<open>cons j\<close>] mk_cons par_cons less.prems(1) True c by simp
    show ?thesis
    proof (cases \<open>i = j\<close>)
      case False
      then have \<open>below (cons j) i\<close> using below_step[OF less.prems(1) True] less.prems(2) by simp
      then show ?thesis using less.IH[OF c] c tc less.prems(1) by simp
    qed simp
  next
    case False
    then show ?thesis using below_stop less.prems by simp
  qed
qed

lemma below_cons: \<open>j < en \<Longrightarrow> below j p \<Longrightarrow> p < en \<Longrightarrow> 2 \<le> kd ! p \<Longrightarrow> below j (cons p)\<close>
proof (induction j rule: less_induct)
  case (less j)
  show ?case
  proof (cases \<open>p = j\<close>)
    case True
    then show ?thesis using below_step less.prems below_self by simp
  next
    case False
    then have jj: \<open>2 \<le> kd ! j\<close> using below_stop less.prems by auto
    have c: \<open>cons j < j\<close> using cons_lt less.prems(1) jj by blast
    have \<open>below (cons j) p\<close> using below_step[OF less.prems(1) jj] less.prems(2) False by simp
    then have \<open>below (cons j) (cons p)\<close> using less.IH[OF c] c less.prems by simp
    then show ?thesis using below_step[OF less.prems(1) jj] by simp
  qed
qed

lemma tp_member: \<open>i < en \<Longrightarrow> mk ! i = 1 \<Longrightarrow> 2 \<le> kd ! tp i\<close>
proof (induction \<open>en - i\<close> arbitrary: i rule: less_induct)
  case less
  note P = par[OF less.prems]
  show ?case
  proof (cases \<open>mk ! par i = 1\<close>)
    case True
    have \<open>en - par i < en - i\<close> using P less.prems by (meson diff_less_mono2)
    then show ?thesis using less.hyps[of \<open>par i\<close>] P True tp_par[OF less.prems] by simp
  next
    case False
    then show ?thesis using tp_par[OF less.prems] tp_non[of \<open>par i\<close>] P by simp
  qed
qed

text \<open>Every definition whose top is \<open>t\<close> is on the chain below \<open>t\<close>.\<close>
lemma tree_below: \<open>i < en \<Longrightarrow> below (tp i) i\<close>
proof (induction \<open>en - i\<close> arbitrary: i rule: less_induct)
  case less
  show ?case
  proof (cases \<open>mk ! i = 1\<close>)
    case True
    note P = par[OF less.prems True]
    have \<open>en - par i < en - i\<close> using P less.prems by (meson diff_less_mono2)
    then have \<open>below (tp (par i)) (par i)\<close> using less.hyps[of \<open>par i\<close>] P by simp
    then have \<open>below (tp (par i)) (cons (par i))\<close> using below_cons tp_props P by blast
    then show ?thesis using P tp_par[OF less.prems True] by simp
  next
    case False
    then show ?thesis using tp_non[OF less.prems] below_self by simp
  qed
qed

end

subsection \<open>The reconstructed assignment is a model\<close>

locale recon_prob = elim_prob +
  fixes m2 :: \<open>bool list list\<close>
  assumes ml2: \<open>map length m2 = ews\<close>
begin

definition \<open>dv2 = eval_defs_m q2 m2\<close>

lemma dv2P: \<open>map length dv2 = eds\<close> \<open>length dv2 = en\<close> \<open>j < en \<Longrightarrow> dv2 ! j = eval_m m2 dv2 (D2 ! j)\<close>
proof -
  note E = eval_defs_props[OF conjunct1[OF D2_defs] ml2[symmetric]]
  show \<open>map length dv2 = eds\<close> using E(1) D2_defs by (simp add: dv2_def eval_defs_m_def q2_parts)
  then show \<open>length dv2 = en\<close> using len_eds by (metis length_map)
  show \<open>j < en \<Longrightarrow> dv2 ! j = eval_m m2 dv2 (D2 ! j)\<close> using E(2) D2(1) by (simp add: dv2_def eval_defs_m_def q2_parts)
qed

definition target :: \<open>nat \<Rightarrow> bool list\<close> where
  \<open>target j = (if mk ! j = 2 then bits_one_m (length (dv2 ! j)) else dv2 ! j)\<close>

lemma target_len: \<open>j < en \<Longrightarrow> length (target j) = eds ! j\<close>
  using dv2P(1,2) bits_one(1) by (auto simp: target_def) (metis nth_map)+

lemma lvar_var: \<open>j < en \<Longrightarrow> kd ! j \<noteq> 0 \<Longrightarrow> \<exists>i. eD ! leaf j = CoreTerm_Var i \<and> lvar j = unat i \<and> unat i < length ews\<close>
  using leaf_props[of j] kd_1[of \<open>leaf j\<close>] by (auto simp: lvar_def var_index_m_def)

lemma lvar_only:
  assumes \<open>j < en\<close> \<open>kd ! j \<noteq> 0\<close> \<open>i < en\<close> \<open>u \<in> set (csubterms (eD ! i))\<close> \<open>is_var (lvar j) u\<close>
  shows \<open>i = leaf j\<close>
proof -
  obtain x where x: \<open>eD ! leaf j = CoreTerm_Var x\<close> \<open>lvar j = unat x\<close> using lvar_var[OF assms(1,2)] by blast
  note L = leaf_props[OF assms(1,2)]
  have \<open>is_var (lvar j) (eD ! leaf j)\<close> using x by (simp add: is_var_def)
  then show ?thesis using leaf_var_unique[of \<open>leaf j\<close> \<open>lvar j\<close> i u] L assms by simp
qed

lemma settle_ok:
  assumes \<open>j < en\<close> \<open>kd ! j \<noteq> 0\<close> \<open>j < f\<close> \<open>length v = eds ! j\<close> \<open>length dv = N\<close> \<open>j < N\<close> \<open>N \<le> en\<close>
    \<open>map length m = ews\<close>
    \<open>\<forall>i<N. tp i < tp j \<longrightarrow> dv ! i = eval_m m dv (eD ! i) \<and> length (dv ! i) = eds ! i\<close>
    \<open>\<forall>i<N. tp i < tp j \<and> tp i = i \<and> mk ! i = 2 \<longrightarrow> dv ! i = bits_one_m (eds ! i)\<close>
  shows \<open>case settle_m eD kd dv2 f dv m j v of (dv', m') \<Rightarrow>
    length dv' = N \<and> map length m' = ews \<and>
    (\<forall>i<N. \<not> below j i \<longrightarrow> dv' ! i = dv ! i) \<and> (\<forall>x. x \<noteq> lvar j \<longrightarrow> m' ! x = m ! x) \<and> dv' ! j = v \<and>
    (\<forall>i<N. below j i \<longrightarrow> dv' ! i = eval_m m' dv' (eD ! i) \<and> length (dv' ! i) = eds ! i)\<close>
  using assms
proof (induction f arbitrary: j v dv m)
  case 0
  then show ?case by simp
next
  case (Suc g)
  note j = Suc.prems(1) and k0 = Suc.prems(2) and jf = Suc.prems(3) and lv = Suc.prems(4) and ld = Suc.prems(5)
    and jN = Suc.prems(6) and Ne = Suc.prems(7) and ml = Suc.prems(8) and S = Suc.prems(9) and T = Suc.prems(10)
  let ?dv1 = \<open>dv[j := v]\<close>
  show ?case
  proof (cases \<open>kd ! j = 1\<close>)
    case True
    obtain i where i: \<open>eD ! j = CoreTerm_Var i\<close> \<open>unat i < length ews\<close> using kd_1[OF j True] by blast
    have lf: \<open>leaf j = j\<close> using leaf_stop j True by simp
    have lvj: \<open>lvar j = unat i\<close> by (simp add: lvar_def lf i var_index_m_def)
    have st: \<open>settle_m eD kd dv2 (Suc g) dv m j v = (?dv1, m[unat i := v])\<close> using True i by (simp add: var_index_m_def)
    have w: \<open>ews ! unat i = eds ! j\<close> using eds_nth[OF j] i by simp
    have bl: \<open>below j i' \<longleftrightarrow> i' = j\<close> for i' using below_stop True by simp
    have lm: \<open>length m = length ews\<close> using ml by (metis length_map)
    have ue: \<open>ews[unat i := eds ! j] = ews\<close> using w by (metis list_update_id)
    have ml': \<open>map length (m[unat i := v]) = ews\<close> using ml lv ue by (simp add: map_update)
    have ev: \<open>eval_m (m[unat i := v]) ?dv1 (eD ! j) = v\<close> using i lm by simp
    show ?thesis using st ld jN ml' lvj bl ev lv by (auto simp: nth_list_update)
  next
    case False
    then have k2: \<open>2 \<le> kd ! j\<close> using k0 by simp
    obtain c va where inv: \<open>invert_m (eD ! j) (kd ! j) v m ?dv1 dv2 = (c, va)\<close> by force
    have st: \<open>settle_m eD kd dv2 (Suc g) dv m j v = settle_m eD kd dv2 g ?dv1 m c va\<close> using False inv by simp
    have cj: \<open>cons j < j\<close> \<open>kd ! cons j \<noteq> 0\<close> using kd_cons[OF j k2] by simp_all
    have tj: \<open>j \<le> tp j\<close> using tp_props[OF j] by simp
    have tc: \<open>tp (cons j) = tp j\<close> using tp_par[of \<open>cons j\<close>] mk_cons par_cons j k2 cj by simp
    have lvc: \<open>lvar (cons j) = lvar j\<close> using leaf_step[OF j k2] by (simp add: lvar_def)
    have lj: \<open>leaf j < j\<close> using leaf_step[OF j k2] leaf_props[of \<open>cons j\<close>] cj j by simp
    have pre: \<open>invpre j v m ?dv1 m'' dv'' dv2\<close>
      if F: \<open>length dv'' = N\<close> \<open>map length m'' = ews\<close> \<open>\<forall>i<N. \<not> below (cons j) i \<longrightarrow> dv'' ! i = ?dv1 ! i\<close>
        \<open>\<forall>x. x \<noteq> lvar j \<longrightarrow> m'' ! x = m ! x\<close> for m'' dv''
    proof -
      have c1: \<open>\<forall>u \<in> set (csubterms (eD ! j)). \<forall>x. is_ref x u \<and> x \<noteq> cons j \<longrightarrow>
        x < length ?dv1 \<and> x < length dv'' \<and> dv'' ! x = ?dv1 ! x \<and> length (?dv1 ! x) = eds ! x \<and>
        ?dv1 ! x = eval_m m ?dv1 (eD ! x)\<close>
      proof (intro ballI allI impI)
        fix u x assume u: \<open>u \<in> set (csubterms (eD ! j))\<close> and rx: \<open>is_ref x u \<and> x \<noteq> cons j\<close>
        have x: \<open>x < j\<close> using ref_lt_D[OF j u] rx by simp
        have xm: \<open>mk ! x \<noteq> 1\<close>
        proof
          assume mx: \<open>mk ! x = 1\<close>
          then have \<open>j = par x\<close> using member_ref[of x j u] x j u rx by simp
          then show False using par[of x] mx x j rx by auto
        qed
        have tx: \<open>tp x = x\<close> using tp_non[of x] xm x j by simp
        have xN: \<open>x < N\<close> using x jN by simp
        have tlt: \<open>tp x < tp j\<close> using tx x tj by simp
        have Sx: \<open>dv ! x = eval_m m dv (eD ! x)\<close> \<open>length (dv ! x) = eds ! x\<close> using S xN tlt by blast+
        have e1: \<open>eval_m m ?dv1 (eD ! x) = eval_m m dv (eD ! x)\<close>
          by (rule eval_m_cong) (use ref_lt_D[of x] x j in fastforce)+
        have nb: \<open>\<not> below (cons j) x\<close> using below_props[of \<open>cons j\<close> x] cj j tc tx x tj by auto
        have d1x: \<open>?dv1 ! x = dv ! x\<close> using x by simp
        show \<open>x < length ?dv1 \<and> x < length dv'' \<and> dv'' ! x = ?dv1 ! x \<and> length (?dv1 ! x) = eds ! x \<and>
            ?dv1 ! x = eval_m m ?dv1 (eD ! x)\<close>
          using Sx e1 nb F(1,3) xN ld d1x by simp
      qed
      have c2: \<open>\<forall>u \<in> set (csubterms (eD ! j)). \<forall>y. is_var y u \<longrightarrow> m'' ! y = m ! y\<close>
      proof (intro ballI allI impI)
        fix u y assume u: \<open>u \<in> set (csubterms (eD ! j))\<close> and y: \<open>is_var y u\<close>
        have \<open>y \<noteq> lvar j\<close> using lvar_only[OF j k0 j u] y lj by auto
        then show \<open>m'' ! y = m ! y\<close> using F(4) by simp
      qed
      have c3: \<open>kd ! j = 4 \<longrightarrow> ?dv1 ! sec j = bits_one_m (eds ! sec j)\<close>
      proof
        assume k4: \<open>kd ! j = 4\<close>
        have sj: \<open>sec j < j\<close> \<open>mk ! sec j = 2\<close> using kd_sec[OF j k4] mk_char(2)[of \<open>sec j\<close>] j k4 by auto
        have ts: \<open>tp (sec j) = sec j\<close> using tp_non[of \<open>sec j\<close>] sj j by simp
        have \<open>sec j < N\<close> \<open>tp (sec j) < tp j\<close> using sj ts tj jN by simp_all
        then have \<open>dv ! sec j = bits_one_m (eds ! sec j)\<close> using T ts sj by blast
        then show \<open>?dv1 ! sec j = bits_one_m (eds ! sec j)\<close> using sj by simp
      qed
      have c0: \<open>cons j < length dv''\<close> using cj jN F(1) by simp
      show ?thesis unfolding invpre_def by (intro conjI lv ml F(2) dv2P(1) c0 c1 c2 c3)
    qed
    have pre0: \<open>invpre j v m ?dv1 m ?dv1 dv2\<close> by (rule pre) (use ld ml in simp_all)
    note I0 = inv_def[OF j k2 pre0]
    have cv: \<open>c = cons j\<close> \<open>length va = eds ! cons j\<close> using I0 inv by simp_all
    have S': \<open>\<forall>i<N. tp i < tp (cons j) \<longrightarrow> ?dv1 ! i = eval_m m ?dv1 (eD ! i) \<and> length (?dv1 ! i) = eds ! i\<close>
    proof (intro allI impI)
      fix i assume i: \<open>i < N\<close> \<open>tp i < tp (cons j)\<close>
      have ij: \<open>i \<noteq> j\<close> using i tc by auto
      have il: \<open>i < en\<close> using i Ne by simp
      have nr: \<open>\<not> is_ref j u\<close> if u: \<open>u \<in> set (csubterms (eD ! i))\<close> for u
      proof
        assume r: \<open>is_ref j u\<close>
        show False
        proof (cases \<open>mk ! j = 1\<close>)
          case True
          then have \<open>i = par j\<close> using member_ref[OF j True il u r] by simp
          then show False using tp_par[OF j True] i tc by simp
        next
          case False
          then have \<open>tp j = j\<close> using tp_non j by simp
          moreover have \<open>j < i\<close> using ref_lt_D[OF il u r] .
          ultimately show False using tp_props[OF il] i tc by simp
        qed
      qed
      have rr: \<open>\<forall>u \<in> set (csubterms (eD ! i)). \<forall>x. is_ref x u \<longrightarrow> ?dv1 ! x = dv ! x\<close>
      proof (intro ballI allI impI)
        fix u x assume u: \<open>u \<in> set (csubterms (eD ! i))\<close> and r: \<open>is_ref x u\<close>
        have \<open>x \<noteq> j\<close> using nr[OF u] r by auto
        then show \<open>?dv1 ! x = dv ! x\<close> by simp
      qed
      have e: \<open>eval_m m ?dv1 (eD ! i) = eval_m m dv (eD ! i)\<close> by (rule eval_m_cong) (use rr in simp_all)
      have tl: \<open>tp i < tp j\<close> using i tc by simp
      have Si: \<open>dv ! i = eval_m m dv (eD ! i)\<close> \<open>length (dv ! i) = eds ! i\<close> using S i(1) tl by blast+
      show \<open>?dv1 ! i = eval_m m ?dv1 (eD ! i) \<and> length (?dv1 ! i) = eds ! i\<close> using Si e ij by simp
    qed
    have T': \<open>\<forall>i<N. tp i < tp (cons j) \<and> tp i = i \<and> mk ! i = 2 \<longrightarrow> ?dv1 ! i = bits_one_m (eds ! i)\<close>
    proof (intro allI impI)
      fix i assume i: \<open>i < N\<close> \<open>tp i < tp (cons j) \<and> tp i = i \<and> mk ! i = 2\<close>
      then have ij: \<open>i \<noteq> j\<close> using tc by auto
      have \<open>dv ! i = bits_one_m (eds ! i)\<close> using T i tc by simp
      then show \<open>?dv1 ! i = bits_one_m (eds ! i)\<close> using ij by simp
    qed
    have cen: \<open>cons j < en\<close> \<open>cons j < g\<close> \<open>length ?dv1 = N\<close> \<open>cons j < N\<close> using cj j jf ld jN by simp_all
    note IH' = Suc.IH[OF cen(1) cj(2) cen(2) cv(2) cen(3) cen(4) Ne ml S' T']
    obtain dv' m' where r: \<open>settle_m eD kd dv2 g ?dv1 m (cons j) va = (dv', m')\<close> by force
    have R0: \<open>length dv' = N \<and> map length m' = ews \<and>
      (\<forall>i<N. \<not> below (cons j) i \<longrightarrow> dv' ! i = ?dv1 ! i) \<and> (\<forall>x. x \<noteq> lvar (cons j) \<longrightarrow> m' ! x = m ! x) \<and> dv' ! cons j = va \<and>
      (\<forall>i<N. below (cons j) i \<longrightarrow> dv' ! i = eval_m m' dv' (eD ! i) \<and> length (dv' ! i) = eds ! i)\<close>
      using IH' unfolding r by (simp only: prod.case) blast
    have R: \<open>length dv' = N\<close> \<open>map length m' = ews\<close> \<open>\<forall>i<N. \<not> below (cons j) i \<longrightarrow> dv' ! i = ?dv1 ! i\<close>
      \<open>\<forall>x. x \<noteq> lvar j \<longrightarrow> m' ! x = m ! x\<close> \<open>dv' ! cons j = va\<close>
      \<open>\<forall>i<N. below (cons j) i \<longrightarrow> dv' ! i = eval_m m' dv' (eD ! i) \<and> length (dv' ! i) = eds ! i\<close>
      using R0 lvc by auto
    have nbj: \<open>\<not> below (cons j) j\<close> using below_props[of \<open>cons j\<close> j] cj j by auto
    have dj: \<open>dv' ! j = v\<close> using R(3) nbj jN ld by simp
    have ej: \<open>eval_m m' dv' (eD ! j) = v\<close> using inv_def[OF j k2 pre[OF R(1-4)]] inv cv R(5) by simp
    have below_j: \<open>below j i \<longleftrightarrow> i = j \<or> below (cons j) i\<close> for i using below_step[OF j k2] .
    show ?thesis
      unfolding st cv(1) r
      using R dj ej lv below_j ld
      by (auto simp: nth_list_update)
  qed
qed

end

context recon_prob
begin

definition rinv :: \<open>nat \<Rightarrow> bool list list \<Rightarrow> bool list list \<Rightarrow> bool\<close> where
  \<open>rinv k dv m \<equiv> length dv = k \<and> map length m = ews \<and>
     (\<forall>i<k. tp i < k \<longrightarrow> dv ! i = eval_m m dv (eD ! i) \<and> length (dv ! i) = eds ! i) \<and>
     (\<forall>x<length ews. \<not> (isleaf x \<and> tp (ldef x) < k) \<longrightarrow> m ! x = m2 ! x) \<and>
     (\<forall>i<k. tp i = i \<and> kd ! i \<noteq> 0 \<longrightarrow> dv ! i = target i)\<close>

lemma rinvI:
  assumes \<open>length dv = k\<close> \<open>map length m = ews\<close>
    \<open>\<And>i. i < k \<Longrightarrow> tp i < k \<Longrightarrow> dv ! i = eval_m m dv (eD ! i) \<and> length (dv ! i) = eds ! i\<close>
    \<open>\<And>x. x < length ews \<Longrightarrow> \<not> (isleaf x \<and> tp (ldef x) < k) \<Longrightarrow> m ! x = m2 ! x\<close>
    \<open>\<And>i. i < k \<Longrightarrow> tp i = i \<and> kd ! i \<noteq> 0 \<Longrightarrow> dv ! i = target i\<close>
  shows \<open>rinv k dv m\<close>
  unfolding rinv_def using assms by blast

lemma app_eval: \<open>i < en \<Longrightarrow> i \<le> length dv \<Longrightarrow> eval_m m (dv @ [e]) (eD ! i) = eval_m m dv (eD ! i)\<close>
  by (rule eval_m_cong) (use ref_lt_D[of i] in \<open>fastforce simp: nth_append\<close>)+

lemma tp_k_free: \<open>i < en \<Longrightarrow> tp i = k \<Longrightarrow> i \<noteq> k \<Longrightarrow> mk ! i = 1 \<and> 2 \<le> kd ! k\<close>
  using tp_non tp_member by fastforce

lemma rinv_step:
  assumes k: \<open>k < en\<close> and I: \<open>rinv k dv m\<close>
  shows \<open>case recon_step eD kd mk dv2 (dv, m) k of (dv', m') \<Rightarrow> rinv (Suc k) dv' m'\<close>
proof -
  have L: \<open>length dv = k\<close> and Mlen: \<open>map length m = ews\<close>
    and LC: \<open>\<forall>i<k. tp i < k \<longrightarrow> dv ! i = eval_m m dv (eD ! i) \<and> length (dv ! i) = eds ! i\<close>
    and VA: \<open>\<forall>x<length ews. \<not> (isleaf x \<and> tp (ldef x) < k) \<longrightarrow> m ! x = m2 ! x\<close>
    and TO: \<open>\<forall>i<k. tp i = i \<and> kd ! i \<noteq> 0 \<longrightarrow> dv ! i = target i\<close>
    using I unfolding rinv_def by blast+
  have ke: \<open>Suc k \<le> en\<close> using k by simp
  consider (A) \<open>mk ! k = 1\<close> | (B) \<open>mk ! k \<noteq> 1\<close> \<open>kd ! k = 0\<close> | (C) \<open>mk ! k \<noteq> 1\<close> \<open>kd ! k \<noteq> 0\<close> by blast
  then show ?thesis
  proof cases
    case A
    have st: \<open>recon_step eD kd mk dv2 (dv, m) k = (dv @ [[]], m)\<close> using A by (simp add: recon_step_def)
    have ntk: \<open>i < en \<Longrightarrow> tp i \<noteq> k\<close> for i using tp_props[of i] A by auto
    have tk: \<open>k < tp k\<close> using tp_par[OF k A] par[OF k A] tp_props[of \<open>par k\<close>] by simp
    have \<open>rinv (Suc k) (dv @ [[]]) m\<close>
    proof (rule rinvI)
      show \<open>length (dv @ [[]]) = Suc k\<close> \<open>map length m = ews\<close> using L Mlen by simp_all
    next
      fix i assume i: \<open>i < Suc k\<close> \<open>tp i < Suc k\<close>
      then have ik: \<open>i < k\<close> \<open>tp i < k\<close> using tk ntk[of i] k by (auto simp: less_Suc_eq)
      have Li: \<open>dv ! i = eval_m m dv (eD ! i)\<close> \<open>length (dv ! i) = eds ! i\<close> using LC ik by blast+
      show \<open>(dv @ [[]]) ! i = eval_m m (dv @ [[]]) (eD ! i) \<and> length ((dv @ [[]]) ! i) = eds ! i\<close>
        using Li app_eval[of i dv m \<open>[]\<close>] ik k L by (simp add: nth_append)
    next
      fix x assume x: \<open>x < length ews\<close> \<open>\<not> (isleaf x \<and> tp (ldef x) < Suc k)\<close>
      then have \<open>\<not> (isleaf x \<and> tp (ldef x) < k)\<close> by auto
      then show \<open>m ! x = m2 ! x\<close> using VA x by simp
    next
      fix i assume i: \<open>i < Suc k\<close> \<open>tp i = i \<and> kd ! i \<noteq> 0\<close>
      then have \<open>i < k\<close> using tk by (auto simp: less_Suc_eq)
      then show \<open>(dv @ [[]]) ! i = target i\<close> using TO i L by (simp add: nth_append)
    qed
    then show ?thesis using st by simp
  next
    case B
    let ?e = \<open>eval_m m dv (eD ! k)\<close>
    have st: \<open>recon_step eD kd mk dv2 (dv, m) k = (dv @ [?e], m)\<close> using B by (simp add: recon_step_def)
    have tkk: \<open>tp k = k\<close> using tp_non k B by simp
    have ntk: \<open>i < en \<Longrightarrow> tp i = k \<Longrightarrow> i = k\<close> for i using tp_k_free B by fastforce
    have le: \<open>length ?e = eds ! k\<close>
    proof -
      have \<open>length ?e = cwidth ews eds (eD ! k)\<close>
      proof (rule eval_m_len[OF wt_D'[OF k] Mlen], intro ballI allI impI conjI)
        fix u x assume u: \<open>u \<in> set (csubterms (eD ! k))\<close> and r: \<open>is_ref x u\<close>
        have x: \<open>x < k\<close> using ref_lt_D[OF k u r] .
        show \<open>x < length dv\<close> using x L by simp
        have \<open>mk ! x \<noteq> 1\<close>
        proof
          assume mx: \<open>mk ! x = 1\<close>
          then have \<open>k = par x\<close> using member_ref[of x k u] x k u r by simp
          then show False using par[of x] mx x k B by auto
        qed
        then have \<open>tp x = x\<close> using tp_non x k by simp
        then have \<open>tp x < k\<close> using x by simp
        then show \<open>length (dv ! x) = eds ! x\<close> using LC x by blast
      qed
      then show ?thesis using cwidth_eD[OF k] by simp
    qed
    have \<open>rinv (Suc k) (dv @ [?e]) m\<close>
    proof (rule rinvI)
      show \<open>length (dv @ [?e]) = Suc k\<close> \<open>map length m = ews\<close> using L Mlen by simp_all
    next
      fix i assume i: \<open>i < Suc k\<close> \<open>tp i < Suc k\<close>
      show \<open>(dv @ [?e]) ! i = eval_m m (dv @ [?e]) (eD ! i) \<and> length ((dv @ [?e]) ! i) = eds ! i\<close>
      proof (cases \<open>i = k\<close>)
        case True
        then show ?thesis using app_eval[of k dv m ?e] L le k by (simp add: nth_append)
      next
        case False
        then have ik: \<open>i < k\<close> \<open>tp i < k\<close> using i ntk[of i] k by (auto simp: less_Suc_eq)
        have Li: \<open>dv ! i = eval_m m dv (eD ! i)\<close> \<open>length (dv ! i) = eds ! i\<close> using LC ik by blast+
        then show ?thesis using app_eval[of i dv m ?e] ik k L by (simp add: nth_append)
      qed
    next
      fix x assume x: \<open>x < length ews\<close> \<open>\<not> (isleaf x \<and> tp (ldef x) < Suc k)\<close>
      have \<open>\<not> (isleaf x \<and> tp (ldef x) < k)\<close>
      proof
        assume h: \<open>isleaf x \<and> tp (ldef x) < k\<close>
        then show False using x by auto
      qed
      moreover have \<open>isleaf x \<Longrightarrow> tp (ldef x) \<noteq> k\<close> using ldef ntk B by fastforce
      ultimately show \<open>m ! x = m2 ! x\<close> using VA x by (auto simp: less_Suc_eq)
    next
      fix i assume i: \<open>i < Suc k\<close> \<open>tp i = i \<and> kd ! i \<noteq> 0\<close>
      then have \<open>i < k\<close> using B by (auto simp: less_Suc_eq)
      then show \<open>(dv @ [?e]) ! i = target i\<close> using TO i L by (simp add: nth_append)
    qed
    then show ?thesis using st by simp
  next
    case C
    have tkk: \<open>tp k = k\<close> using tp_non k C by simp
    let ?v = \<open>target k\<close>
    have st: \<open>recon_step eD kd mk dv2 (dv, m) k = settle_m eD kd dv2 (Suc k) (dv @ [[]]) m k ?v\<close>
      using C by (simp add: recon_step_def target_def)
    have S: \<open>\<forall>i<Suc k. tp i < tp k \<longrightarrow> (dv @ [[]]) ! i = eval_m m (dv @ [[]]) (eD ! i) \<and> length ((dv @ [[]]) ! i) = eds ! i\<close>
    proof (intro allI impI)
      fix i assume i: \<open>i < Suc k\<close> \<open>tp i < tp k\<close>
      then have ik: \<open>i < k\<close> using tkk by (auto simp: less_Suc_eq)
      have tl: \<open>tp i < k\<close> using i tkk by simp
      have Li: \<open>dv ! i = eval_m m dv (eD ! i)\<close> \<open>length (dv ! i) = eds ! i\<close> using LC ik tl by blast+
      show \<open>(dv @ [[]]) ! i = eval_m m (dv @ [[]]) (eD ! i) \<and> length ((dv @ [[]]) ! i) = eds ! i\<close>
        using Li app_eval[of i dv m \<open>[]\<close>] k L ik by (simp add: nth_append)
    qed
    have T: \<open>\<forall>i<Suc k. tp i < tp k \<and> tp i = i \<and> mk ! i = 2 \<longrightarrow> (dv @ [[]]) ! i = bits_one_m (eds ! i)\<close>
    proof (intro allI impI)
      fix i assume i: \<open>i < Suc k\<close> \<open>tp i < tp k \<and> tp i = i \<and> mk ! i = 2\<close>
      then have ik: \<open>i < k\<close> using tkk by auto
      obtain p where p: \<open>p < en\<close> \<open>kd ! p = 4\<close> \<open>sec p = i\<close> using mk_char(2)[of i] i ik k by auto
      have ki: \<open>kd ! i \<noteq> 0\<close> using kd_sec[OF p(1,2)] p(3) by simp
      have \<open>dv ! i = target i\<close> using TO ik i ki by simp
      have l2: \<open>length (dv2 ! i) = eds ! i\<close> using dv2P(1,2) ik k by (metis nth_map less_trans)
      show \<open>(dv @ [[]]) ! i = bits_one_m (eds ! i)\<close>
        using \<open>dv ! i = target i\<close> ik L i l2 by (simp add: nth_append target_def)
    qed
    have lv: \<open>length ?v = eds ! k\<close> using target_len[OF k] .
    have lN: \<open>length (dv @ [[]]) = Suc k\<close> using L by simp
    note SO = settle_ok[OF k C(2) lessI lv lN lessI ke Mlen S T]
    obtain dv' m' where r: \<open>settle_m eD kd dv2 (Suc k) (dv @ [[]]) m k ?v = (dv', m')\<close> by force
    have R: \<open>length dv' = Suc k\<close> \<open>map length m' = ews\<close> \<open>\<forall>i<Suc k. \<not> below k i \<longrightarrow> dv' ! i = (dv @ [[]]) ! i\<close>
      \<open>\<forall>x. x \<noteq> lvar k \<longrightarrow> m' ! x = m ! x\<close> \<open>dv' ! k = ?v\<close>
      \<open>\<forall>i<Suc k. below k i \<longrightarrow> dv' ! i = eval_m m' dv' (eD ! i) \<and> length (dv' ! i) = eds ! i\<close>
      using SO unfolding r by (simp only: prod.case, blast)+
    have nb: \<open>\<not> below k i\<close> if \<open>i < en\<close> \<open>tp i \<noteq> k\<close> for i
    proof
      assume \<open>below k i\<close>
      then have \<open>tp i = tp k\<close> using below_props[OF k] by blast
      then show False using tkk that(2) by simp
    qed
    have LV: \<open>isleaf (lvar k) \<and> ldef (lvar k) = leaf k\<close> \<open>tp (leaf k) = k\<close> using lvar[OF k C(2)] leaf_props[OF k C(2)] tkk by simp_all
    have \<open>rinv (Suc k) dv' m'\<close>
    proof (rule rinvI)
      show \<open>length dv' = Suc k\<close> \<open>map length m' = ews\<close> using R by simp_all
    next
      fix i assume i: \<open>i < Suc k\<close> \<open>tp i < Suc k\<close>
      have il: \<open>i < en\<close> using i k by simp
      show \<open>dv' ! i = eval_m m' dv' (eD ! i) \<and> length (dv' ! i) = eds ! i\<close>
      proof (cases \<open>tp i = k\<close>)
        case True
        then have \<open>below k i\<close> using tree_below[OF il] by simp
        then show ?thesis using R(6) i(1) by blast
      next
        case False
        then have ik: \<open>i < k\<close> \<open>tp i < k\<close> using i tkk by (auto simp: less_Suc_eq)
        have di: \<open>dv' ! i = dv ! i\<close> using R(3) nb[OF il False] ik L by (simp add: nth_append)
        have rr: \<open>\<forall>u \<in> set (csubterms (eD ! i)). \<forall>x. is_ref x u \<longrightarrow> dv' ! x = dv ! x\<close>
        proof (intro ballI allI impI)
          fix u x assume u: \<open>u \<in> set (csubterms (eD ! i))\<close> and r: \<open>is_ref x u\<close>
          have x: \<open>x < i\<close> using ref_lt_D[OF il u r] .
          have \<open>tp x \<noteq> k\<close>
          proof (cases \<open>mk ! x = 1\<close>)
            case True
            then have \<open>i = par x\<close> using member_ref[of x i u] x il u r by simp
            then show ?thesis using tp_par[of x] True x il ik by simp
          next
            case False
            then show ?thesis using tp_non[of x] x ik il by simp
          qed
          then show \<open>dv' ! x = dv ! x\<close> using R(3) nb[of x] x ik L il by (simp add: nth_append)
        qed
        have vv: \<open>\<forall>u \<in> set (csubterms (eD ! i)). \<forall>y. is_var y u \<longrightarrow> m' ! y = m ! y\<close>
        proof (intro ballI allI impI)
          fix u y assume u: \<open>u \<in> set (csubterms (eD ! i))\<close> and y: \<open>is_var y u\<close>
          have \<open>y \<noteq> lvar k\<close>
          proof
            assume \<open>y = lvar k\<close>
            then have \<open>i = leaf k\<close> using lvar_only[OF k C(2) il u] y by simp
            then show False using LV False by simp
          qed
          then show \<open>m' ! y = m ! y\<close> using R(4) by simp
        qed
        have \<open>eval_m m' dv' (eD ! i) = eval_m m dv (eD ! i)\<close>
          by (rule eval_m_cong) (use rr vv in simp_all)
        moreover have \<open>dv ! i = eval_m m dv (eD ! i)\<close> \<open>length (dv ! i) = eds ! i\<close> using LC ik by blast+
        ultimately show ?thesis using di by simp
      qed
    next
      fix x assume x: \<open>x < length ews\<close> \<open>\<not> (isleaf x \<and> tp (ldef x) < Suc k)\<close>
      have xk: \<open>x \<noteq> lvar k\<close> using x LV by auto
      have \<open>\<not> (isleaf x \<and> tp (ldef x) < k)\<close> using x by auto
      then show \<open>m' ! x = m2 ! x\<close> using VA x R(4) xk by simp
    next
      fix i assume i: \<open>i < Suc k\<close> \<open>tp i = i \<and> kd ! i \<noteq> 0\<close>
      show \<open>dv' ! i = target i\<close>
      proof (cases \<open>i = k\<close>)
        case True
        then show ?thesis using R(5) by simp
      next
        case False
        then have ik: \<open>i < k\<close> using i by simp
        have \<open>\<not> below k i\<close> using nb[of i] i ik k by simp
        then show ?thesis using R(3) TO i ik L by (simp add: nth_append)
      qed
    qed
    then show ?thesis using st r by simp
  qed
qed

lemma rinv_fold: \<open>k \<le> en \<Longrightarrow> case foldl (recon_step eD kd mk dv2) ([], m2) [0..<k] of (dv, m) \<Rightarrow> rinv k dv m\<close>
proof (induction k)
  case 0
  then show ?case using ml2 by (simp add: rinv_def)
next
  case (Suc k)
  obtain dv m where s: \<open>foldl (recon_step eD kd mk dv2) ([], m2) [0..<k] = (dv, m)\<close> by force
  have \<open>rinv k dv m\<close> using Suc s by simp
  then show ?case using rinv_step[of k dv m] Suc.prems s by simp
qed

lemma lc_defs:
  assumes \<open>length dv = en\<close> \<open>\<forall>i<en. dv ! i = eval_m m dv (eD ! i)\<close> \<open>map length m = ews\<close>
  shows \<open>dv = eval_defs_m q m\<close>
proof -
  let ?E = \<open>eval_defs_m q m\<close>
  note E = eval_defs_props[OF dwt assms(3)[symmetric]]
  have lE: \<open>length ?E = en\<close> using E(1) len_eds by (metis eval_defs_m_def eD_def eds_def length_map)
  have En: \<open>i < en \<Longrightarrow> ?E ! i = eval_m m ?E (eD ! i)\<close> for i using E(2) by (simp add: eval_defs_m_def eD_def en_def)
  have \<open>i < en \<Longrightarrow> dv ! i = ?E ! i\<close> for i
  proof (induction i rule: less_induct)
    case (less i)
    have \<open>eval_m m dv (eD ! i) = eval_m m ?E (eD ! i)\<close>
      by (rule eval_m_cong) (use less ref_lt_D[OF less.prems] in fastforce)+
    then show ?case using assms(2) En less.prems by simp
  qed
  then show ?thesis using assms(1) lE by (intro nth_equalityI) simp_all
qed

end

context elim_prob
begin

lemma elim_parts: \<open>elim_m q = (q2, kd, mk)\<close>
  by (simp add: elim_m_def q2_def kd_def mk_def)

theorem recon_sound:
  assumes M: \<open>cis_model q2 m2\<close>
  shows \<open>cis_model q (reconstruct_m q kd mk q2 m2)\<close>
proof -
  have ml2: \<open>map length m2 = ews\<close> using M by (simp add: cis_model_def cis_assignment_def q2_ws)
  interpret R: recon_prob q m2 by unfold_locales (rule ml2)
  obtain dvF mF where f: \<open>foldl (recon_step eD kd mk R.dv2) ([], m2) [0..<en] = (dvF, mF)\<close> by force
  have I: \<open>R.rinv en dvF mF\<close> using R.rinv_fold[of en] f by simp
  have rc: \<open>reconstruct_m q kd mk q2 m2 = mF\<close> using f by (simp add: reconstruct_m_def R.dv2_def eD_def en_def)
  have L: \<open>length dvF = en\<close> and Mlen: \<open>map length mF = ews\<close>
    and LC: \<open>\<forall>i<en. tp i < en \<longrightarrow> dvF ! i = eval_m mF dvF (eD ! i) \<and> length (dvF ! i) = eds ! i\<close>
    and VA: \<open>\<forall>x<length ews. \<not> (isleaf x \<and> tp (ldef x) < en) \<longrightarrow> mF ! x = m2 ! x\<close>
    and TO: \<open>\<forall>i<en. tp i = i \<and> kd ! i \<noteq> 0 \<longrightarrow> dvF ! i = R.target i\<close>
    using I unfolding R.rinv_def by blast+
  have LC': \<open>\<forall>i<en. dvF ! i = eval_m mF dvF (eD ! i)\<close> using LC tp_props by blast
  have dF: \<open>dvF = eval_defs_m q mF\<close> using R.lc_defs[OF L LC' Mlen] .
  have VA': \<open>x < length ews \<Longrightarrow> \<not> isleaf x \<Longrightarrow> mF ! x = m2 ! x\<close> for x using VA by simp
  have not2: \<open>mk ! x \<noteq> 2\<close> if x: \<open>x < en\<close> \<open>u \<in> set (csubterms t)\<close> \<open>is_ref x u\<close> \<open>t = eD ! j \<and> j < en \<and> kd ! j < 2 \<or> t \<in> set eA\<close> for x u t j
  proof
    assume m2x: \<open>mk ! x = 2\<close>
    obtain p where p: \<open>p < en\<close> \<open>kd ! p = 4\<close> \<open>sec p = x\<close> using mk_char(2)[OF x(1)] m2x by auto
    note KS = kd_sec[OF p(1,2)]
    obtain u' where u': \<open>u' \<in> set (csubterms (eD ! p))\<close> \<open>is_ref x u'\<close> using KS p(3) by blast
    show False using x(4)
    proof
      assume t: \<open>t = eD ! j \<and> j < en \<and> kd ! j < 2\<close>
      then have \<open>j = p\<close> using ref_unique[of x j p u u'] KS p(1,3) x u' by simp
      then show False using t p(2) by simp
    next
      assume \<open>t \<in> set eA\<close>
      then show False using ref_not_A[of x p u' t u] KS p(1,3) x u' by simp
    qed
  qed
  have claim: \<open>j < en \<Longrightarrow> live ! j \<Longrightarrow> mk ! j \<noteq> 1 \<Longrightarrow> mk ! j \<noteq> 2 \<Longrightarrow> dvF ! j = R.dv2 ! j\<close> for j
  proof (induction j rule: less_induct)
    case (less j)
    note j = less.prems(1)
    show ?case
    proof (cases \<open>kd ! j = 0\<close>)
      case True
      have d: \<open>D2 ! j = eD ! j\<close> using D2(3)[OF j] ana(6)[OF j] less.prems(2) True by simp
      have rr: \<open>\<forall>u \<in> set (csubterms (eD ! j)). \<forall>x. is_ref x u \<longrightarrow> dvF ! x = R.dv2 ! x\<close>
      proof (intro ballI allI impI)
        fix u x assume u: \<open>u \<in> set (csubterms (eD ! j))\<close> and r: \<open>is_ref x u\<close>
        have x: \<open>x < j\<close> using ref_lt_D[OF j u r] .
        have lx: \<open>live ! x\<close> using D2(4)[OF j less.prems(2)] ana(6)[OF j] True u r by simp
        have mx: \<open>mk ! x \<noteq> 1\<close>
        proof
          assume mx: \<open>mk ! x = 1\<close>
          then have \<open>j = par x\<close> using member_ref[of x j u] x j u r by simp
          then show False using par[of x] mx True x j by auto
        qed
        have \<open>mk ! x \<noteq> 2\<close> using not2[of x u \<open>eD ! j\<close> j] x j u r True by simp
        then show \<open>dvF ! x = R.dv2 ! x\<close> using less.IH[of x] x j lx mx by simp
      qed
      have vv: \<open>\<forall>u \<in> set (csubterms (eD ! j)). \<forall>y. is_var y u \<longrightarrow> mF ! y = m2 ! y\<close>
      proof (intro ballI allI impI)
        fix u y assume u: \<open>u \<in> set (csubterms (eD ! j))\<close> and y: \<open>is_var y u\<close>
        have yl: \<open>y < length ews\<close> using cwt_var_lt[OF wt_D'[OF j] u y] .
        have \<open>\<not> isleaf y\<close>
        proof
          assume \<open>isleaf y\<close>
          note Ld = ldef[OF this]
          have \<open>j = ldef y\<close> using leaf_var_unique[of \<open>ldef y\<close> y j u] Ld j u y by simp
          then show False using Ld True by simp
        qed
        then show \<open>mF ! y = m2 ! y\<close> using VA' yl by simp
      qed
      have \<open>eval_m mF dvF (eD ! j) = eval_m m2 R.dv2 (eD ! j)\<close> by (rule eval_m_cong) (use vv rr in simp_all)
      then show ?thesis using LC' j R.dv2P(3)[OF j] d by simp
    next
      case False
      have \<open>tp j = j\<close> using tp_non j less.prems(3) by simp
      then show ?thesis using TO j False less.prems(4) by (simp add: R.target_def)
    qed
  qed
  have A: \<open>eval_m mF dvF t = eval_m m2 R.dv2 t\<close> if t: \<open>t \<in> set eA\<close> for t
  proof (rule eval_m_cong)
    show \<open>\<forall>u \<in> set (csubterms t). \<forall>x. is_var x u \<longrightarrow> mF ! x = m2 ! x\<close>
    proof (intro ballI allI impI)
      fix u x assume u: \<open>u \<in> set (csubterms t)\<close> \<open>is_var x u\<close>
      have xl: \<open>x < length ews\<close> using cwt_var_lt[OF conjunct1[OF wt_A[OF t]] u] .
      have \<open>\<not> isleaf x\<close> using ldef leaf_var_not_A t u by blast
      then show \<open>mF ! x = m2 ! x\<close> using VA' xl by simp
    qed
    show \<open>\<forall>u \<in> set (csubterms t). \<forall>x. is_ref x u \<longrightarrow> dvF ! x = R.dv2 ! x\<close>
    proof (intro ballI allI impI)
      fix u x assume u: \<open>u \<in> set (csubterms t)\<close> \<open>is_ref x u\<close>
      have x: \<open>x < en\<close> using ref_lt_A[OF t u] .
      have \<open>mk ! x \<noteq> 1\<close> using member_not_A[OF x _ t u] by blast
      moreover have \<open>mk ! x \<noteq> 2\<close> using not2[of x u t 0] x u t by simp
      ultimately show \<open>dvF ! x = R.dv2 ! x\<close> using claim[OF x D2(5)[OF t u]] by simp
    qed
  qed
  have \<open>csatisfies q2 m2\<close> using M by (simp add: cis_model_def)
  then have S: \<open>\<forall>t \<in> set eA. bits_nat (eval_m m2 R.dv2 t) = 1\<close>
    using csat_bits[OF q2_wt] ml2 by (simp add: R.dv2_def q2_ws q2_parts)
  have \<open>csatisfies q mF\<close>
    using csat_bits[OF wt] Mlen S A dF by (simp add: eA_def ews_def)
  then show ?thesis using Mlen rc by (simp add: cis_model_def cis_assignment_def ews_def)
qed

end

end
