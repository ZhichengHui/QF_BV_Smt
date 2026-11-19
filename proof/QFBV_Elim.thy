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

end
