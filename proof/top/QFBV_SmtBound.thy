theory QFBV_SmtBound
  imports QFBV_SmtSize
begin

section \<open>The translation of a problem in the input range is within the overflow bound\<close>

text \<open>For a well-sorted problem of the fragment within \<^const>\<open>smt_in_range\<close>, the translation has
  fewer than \<open>2^56\<close> definitions and is within \<^const>\<open>sizes_ok\<close>. The cost of a translated term is
  \<^const>\<open>ow\<close>, and one more for each definition. Every node of the problem (an application of a
  definition with parameters counted with its body at each application, as in \<^const>\<open>smt_tcost\<close>)
  adds terms of cost at most \<open>cK\<close> times its cost \<^const>\<open>smt_ncost\<close>; an argument adds its own
  definition and costs at its own node. So a term costs at most \<open>cK\<close> times its
  \<^const>\<open>smt_tcost\<close>, and the problem at most \<open>cK * 2^43\<close>, below the \<open>2^54\<close> that
  \<^const>\<open>sizes_ok\<close> needs.\<close>

subsection \<open>Constants\<close>

definition WB :: nat where \<open>WB \<equiv> 2 ^ 18\<close>
definition cK :: nat where \<open>cK \<equiv> 1024\<close>

lemma fw_mono: \<open>x \<le> y \<Longrightarrow> fw x \<le> fw y\<close>
  by (simp add: fw_def)

lemma nst_mono: \<open>x \<le> y \<Longrightarrow> nst x \<le> nst y\<close>
  using nst_le_iff[of x \<open>nst y\<close>] nst_le_iff[of y \<open>nst y\<close>] by auto

lemma ebin_mono: \<open>x \<le> y \<Longrightarrow> ebin op x \<le> ebin op y\<close>
  by (auto simp: ebin_def intro!: add_mono mult_mono nst_mono)

lemma nst_WB: \<open>w \<le> WB \<Longrightarrow> nst w \<le> 18\<close>
  using nst_le_iff[of w 18] by (simp add: WB_def)

lemma fw_le: \<open>x \<le> w \<Longrightarrow> 1 \<le> w \<Longrightarrow> fw x \<le> 8 * w\<close>
  by (simp add: fw_def)

text \<open>The bounds of \<^const>\<open>ebin\<close> for a width \<open>w\<close> between 1 and \<^const>\<open>WB\<close>: linear except for
  multiplication, division and remainder.\<close>
lemma ebin_le:
  assumes \<open>1 \<le> w\<close> \<open>w \<le> WB\<close>
  shows \<open>op \<notin> {Op_Mul, Op_Udiv, Op_Urem, Op_Sdiv, Op_Srem, Op_Smod} \<Longrightarrow> ebin op w \<le> 210 * w\<close>
    and \<open>ebin op w \<le> 396 * (w * w)\<close>
proof -
  have s: \<open>10 * w * nst w \<le> 10 * w * 18\<close> using nst_WB[OF assms(2)] by (intro mult_le_mono2) simp
  have ww: \<open>w \<le> w * w\<close> using assms(1) by simp
  show \<open>op \<notin> {Op_Mul, Op_Udiv, Op_Urem, Op_Sdiv, Op_Srem, Op_Smod} \<Longrightarrow> ebin op w \<le> 210 * w\<close>
    using s assms(1) by (auto simp: ebin_def)
  show \<open>ebin op w \<le> 396 * (w * w)\<close>
    using s assms(1) ww by (auto simp: ebin_def)
qed

subsection \<open>Costs of the shapes of translated terms\<close>

lemma width_tref: \<open>k < 2 ^ 64 \<Longrightarrow> width ws D (tref k) = D ! k\<close>
  by (simp add: tref_def unat_of_nat_eq)

lemma ow_tref: \<open>k < 2 ^ 64 \<Longrightarrow> ow ws D (tref k) = fw (D ! k)\<close>
  by (simp add: tref_def ow_eqs unat_of_nat_eq)

lemma ow_fold:
  \<open>(\<forall>k \<in> set xs. k < 2 ^ 64 \<and> D ! k \<le> w) \<Longrightarrow> width ws D a \<le> w \<Longrightarrow>
   op \<in> {Op_And, Op_Or, Op_Xor, Op_Add, Op_Mul} \<Longrightarrow>
   ow ws D (foldl (\<lambda>acc k. TermL_Bin op acc (tref k)) a xs) \<le> ow ws D a + length xs * (2 * fw w + ebin op w) \<and>
   width ws D (foldl (\<lambda>acc k. TermL_Bin op acc (tref k)) a xs) = width ws D a\<close>
proof (induction xs arbitrary: a)
  case Nil
  then show ?case by simp
next
  case (Cons k xs)
  have k: \<open>k < 2 ^ 64\<close> \<open>D ! k \<le> w\<close> using Cons.prems(1) by auto
  have o: \<open>opw op (width ws D a) (D ! k) = width ws D a\<close> using Cons.prems(3) by (auto simp: opw_def)
  have wb: \<open>width ws D (TermL_Bin op a (tref k)) = width ws D a\<close>
    using o by (simp only: width_Bin_opw width_tref[OF k(1)])
  have e: \<open>ow ws D (TermL_Bin op a (tref k)) = fw (width ws D a) + (ebin op (width ws D a) + (ow ws D a + fw (D ! k)))\<close>
    by (simp only: ow_eqs ow_tref[OF k(1)] width_tref[OF k(1)] o)
  have m: \<open>fw (width ws D a) \<le> fw w\<close> \<open>fw (D ! k) \<le> fw w\<close> \<open>ebin op (width ws D a) \<le> ebin op w\<close>
    using Cons.prems(2) k(2) by (auto intro: fw_mono ebin_mono)
  have ob: \<open>ow ws D (TermL_Bin op a (tref k)) \<le> ow ws D a + (2 * fw w + ebin op w)\<close> using e m by linarith
  have IH: \<open>ow ws D (foldl (\<lambda>acc k. TermL_Bin op acc (tref k)) (TermL_Bin op a (tref k)) xs) \<le>
      ow ws D (TermL_Bin op a (tref k)) + length xs * (2 * fw w + ebin op w) \<and>
      width ws D (foldl (\<lambda>acc k. TermL_Bin op acc (tref k)) (TermL_Bin op a (tref k)) xs) = width ws D (TermL_Bin op a (tref k))\<close>
    using Cons.IH[of \<open>TermL_Bin op a (tref k)\<close>] Cons.prems wb by simp
  show ?case using IH ob wb by simp
qed

lemma ow_fold_and:
  \<open>(\<forall>x \<in> set xs. ow ws D (g x) \<le> c) \<Longrightarrow> width ws D a = 1 \<Longrightarrow>
   ow ws D (foldl (\<lambda>acc x. TermL_Bin Op_And acc (g x)) a xs) \<le> ow ws D a + length xs * (fw 1 + ebin Op_And 1 + c) \<and>
   width ws D (foldl (\<lambda>acc x. TermL_Bin Op_And acc (g x)) a xs) = 1\<close>
proof (induction xs arbitrary: a)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have o: \<open>opw Op_And (width ws D a) (width ws D (g x)) = 1\<close> using Cons.prems(2) by (simp add: opw_def)
  have wb: \<open>width ws D (TermL_Bin Op_And a (g x)) = 1\<close> using o by (simp only: width_Bin_opw)
  have e: \<open>ow ws D (TermL_Bin Op_And a (g x)) = fw 1 + (ebin Op_And 1 + (ow ws D a + ow ws D (g x)))\<close>
    using Cons.prems(2) by (simp add: ow_eqs opw_def)
  have ob: \<open>ow ws D (TermL_Bin Op_And a (g x)) \<le> ow ws D a + (fw 1 + ebin Op_And 1 + c)\<close>
    using e Cons.prems(1) by simp
  have IH: \<open>ow ws D (foldl (\<lambda>acc x. TermL_Bin Op_And acc (g x)) (TermL_Bin Op_And a (g x)) xs) \<le>
      ow ws D (TermL_Bin Op_And a (g x)) + length xs * (fw 1 + ebin Op_And 1 + c) \<and>
      width ws D (foldl (\<lambda>acc x. TermL_Bin Op_And acc (g x)) (TermL_Bin Op_And a (g x)) xs) = 1\<close>
    using Cons.IH[of \<open>TermL_Bin Op_And a (g x)\<close>] Cons.prems wb by simp
  show ?case using IH ob by simp
qed

lemma ow_foldr_imp:
  \<open>(\<forall>k \<in> set xs. k < 2 ^ 64 \<and> D ! k \<le> w) \<Longrightarrow>
   ow ws D (foldr (\<lambda>k acc. TermL_Bin Op_Or (TermL_Not (tref k)) acc) xs b) \<le> ow ws D b + length xs * (3 * fw w + ebin Op_Or w)\<close>
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons k xs)
  let ?r = \<open>foldr (\<lambda>k acc. TermL_Bin Op_Or (TermL_Not (tref k)) acc) xs b\<close>
  have k: \<open>k < 2 ^ 64\<close> \<open>D ! k \<le> w\<close> using Cons.prems by auto
  have o: \<open>opw Op_Or (D ! k) (width ws D ?r) = D ! k\<close> by (simp add: opw_def)
  have e: \<open>ow ws D (TermL_Bin Op_Or (TermL_Not (tref k)) ?r) = fw (D ! k) + (ebin Op_Or (D ! k) + ((fw (D ! k) + fw (D ! k)) + ow ws D ?r))\<close>
    by (simp only: ow_eqs ow_tref[OF k(1)] width_tref[OF k(1)] width.simps(4) o)
  have m: \<open>fw (D ! k) \<le> fw w\<close> \<open>ebin Op_Or (D ! k) \<le> ebin Op_Or w\<close> using k(2) by (auto intro: fw_mono ebin_mono)
  have IH: \<open>ow ws D ?r \<le> ow ws D b + length xs * (3 * fw w + ebin Op_Or w)\<close> using Cons.IH Cons.prems by simp
  show ?case using e m IH by simp
qed

lemma sum_list_Suc: \<open>sum_list (map (\<lambda>x. Suc (f x)) xs) = length xs + sum_list (map f xs)\<close>
  by (induction xs) auto

lemma sum_desc: \<open>2 * sum_list (map (\<lambda>i. n - Suc i) [0..<n]) = n * (n - 1)\<close>
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have e: \<open>map (\<lambda>i. Suc n - Suc i) [0..<Suc n] = map (\<lambda>i. Suc (n - Suc i)) [0..<n] @ [0]\<close>
    by (auto simp: Suc_diff_Suc)
  show ?case using Suc.IH by (simp only: e sum_list_append map_append sum_list_Suc) (cases n; simp add: algebra_simps)
qed

lemma pairs_m_len2: \<open>2 * length (pairs_m n) \<le> n * (n - 1)\<close>
proof -
  have \<open>length (pairs_m n) \<le> length (concat (map (\<lambda>i. map (\<lambda>j. (i, j)) [Suc i..<n]) [0..<n]))\<close>
    unfolding pairs_m_def by (rule length_filter_le)
  also have \<open>\<dots> = sum_list (map (\<lambda>i. n - Suc i) [0..<n])\<close> by (simp add: length_concat comp_def)
  finally show ?thesis using sum_desc[of n] by linarith
qed

text \<open>The least number of arguments of a well-sorted application of \<open>op\<close>.\<close>
definition sop_ar :: \<open>SmtOp \<Rightarrow> nat\<close> where
  \<open>sop_ar op \<equiv>
     (case op of
        SmtOp_Not \<Rightarrow> 1
      | SmtOp_Bvnot \<Rightarrow> 1
      | SmtOp_Bvneg \<Rightarrow> 1
      | SmtOp_Extract i j \<Rightarrow> 1
      | SmtOp_Repeat i \<Rightarrow> 1
      | SmtOp_ZeroExtend i \<Rightarrow> 1
      | SmtOp_SignExtend i \<Rightarrow> 1
      | SmtOp_RotateLeft i \<Rightarrow> 1
      | SmtOp_RotateRight i \<Rightarrow> 1
      | SmtOp_Ite \<Rightarrow> 3
      | _ \<Rightarrow> 2)\<close>

lemma sop_ar_simps [simp]:
  \<open>sop_ar SmtOp_Not = 1\<close>
  \<open>sop_ar SmtOp_Bvnot = 1\<close>
  \<open>sop_ar SmtOp_Bvneg = 1\<close>
  \<open>sop_ar (SmtOp_Extract i j) = 1\<close>
  \<open>sop_ar (SmtOp_Repeat i) = 1\<close>
  \<open>sop_ar (SmtOp_ZeroExtend i) = 1\<close>
  \<open>sop_ar (SmtOp_SignExtend i) = 1\<close>
  \<open>sop_ar (SmtOp_RotateLeft i) = 1\<close>
  \<open>sop_ar (SmtOp_RotateRight i) = 1\<close>
  \<open>sop_ar SmtOp_Ite = 3\<close>
  \<open>sop_ar SmtOp_And = 2\<close>
  \<open>sop_ar SmtOp_Or = 2\<close>
  \<open>sop_ar SmtOp_Xor = 2\<close>
  \<open>sop_ar SmtOp_Implies = 2\<close>
  \<open>sop_ar SmtOp_Eq = 2\<close>
  \<open>sop_ar SmtOp_Distinct = 2\<close>
  \<open>sop_ar SmtOp_Concat = 2\<close>
  \<open>sop_ar SmtOp_Bvand = 2\<close>
  \<open>sop_ar SmtOp_Bvor = 2\<close>
  \<open>sop_ar SmtOp_Bvadd = 2\<close>
  \<open>sop_ar SmtOp_Bvmul = 2\<close>
  \<open>sop_ar SmtOp_Bvudiv = 2\<close>
  \<open>sop_ar SmtOp_Bvurem = 2\<close>
  \<open>sop_ar SmtOp_Bvshl = 2\<close>
  \<open>sop_ar SmtOp_Bvlshr = 2\<close>
  \<open>sop_ar SmtOp_Bvult = 2\<close>
  \<open>sop_ar SmtOp_Bvnand = 2\<close>
  \<open>sop_ar SmtOp_Bvnor = 2\<close>
  \<open>sop_ar SmtOp_Bvxor = 2\<close>
  \<open>sop_ar SmtOp_Bvxnor = 2\<close>
  \<open>sop_ar SmtOp_Bvcomp = 2\<close>
  \<open>sop_ar SmtOp_Bvsub = 2\<close>
  \<open>sop_ar SmtOp_Bvsdiv = 2\<close>
  \<open>sop_ar SmtOp_Bvsrem = 2\<close>
  \<open>sop_ar SmtOp_Bvsmod = 2\<close>
  \<open>sop_ar SmtOp_Bvashr = 2\<close>
  \<open>sop_ar SmtOp_Bvule = 2\<close>
  \<open>sop_ar SmtOp_Bvugt = 2\<close>
  \<open>sop_ar SmtOp_Bvuge = 2\<close>
  \<open>sop_ar SmtOp_Bvslt = 2\<close>
  \<open>sop_ar SmtOp_Bvsle = 2\<close>
  \<open>sop_ar SmtOp_Bvsgt = 2\<close>
  \<open>sop_ar SmtOp_Bvsge = 2\<close>
  by (simp_all add: sop_ar_def)

lemma smt_bin_width_len: \<open>smt_bin_width ss \<noteq> None \<Longrightarrow> length ss = 2\<close>
  using smt_bin_width_Some by fastforce

lemma sop_ar_sort: \<open>smt_op_sort op ss = Some s \<Longrightarrow> sop_ar op \<le> length ss\<close>
  by (cases op) (auto split: if_splits list.splits SmtSort.splits dest!: smt_bin_width_Some)

lemma un_cost:
  assumes \<open>k < 2 ^ 64\<close> \<open>D ! k \<le> w\<close> \<open>width ws D t \<le> w\<close> \<open>1 \<le> w\<close>
    \<open>t = TermL_Not (tref k) \<or> t = TermL_Neg (tref k) \<or> t = TermL_Extract hi lo (tref k) \<or>
     t = TermL_Repeat i (tref k) \<or> t = TermL_ZeroExtend i (tref k) \<or> t = TermL_SignExtend i (tref k) \<or>
     t = TermL_RotateLeft i (tref k) \<or> t = TermL_RotateRight i (tref k)\<close>
  shows \<open>ow ws D t \<le> 31 * w\<close>
proof -
  have r: \<open>ow ws D (tref k) \<le> 8 * w\<close> \<open>width ws D (tref k) \<le> w\<close>
    using assms(1,2,4) fw_le[OF assms(2,4)] by (simp_all add: ow_tref width_tref)
  have f: \<open>fw (width ws D t) \<le> 8 * w\<close> using assms(3,4) by (rule fw_le)
  have fr: \<open>fw (width ws D (tref k)) \<le> 8 * w\<close> using r(2) assms(4) by (rule fw_le)
  show ?thesis using assms(5)
  proof (elim disjE)
    assume t: \<open>t = TermL_Neg (tref k)\<close>
    show ?thesis using r fr unfolding t ow_eqs by simp
  next
    assume t: \<open>t = TermL_SignExtend i (tref k)\<close>
    have \<open>unat i \<le> w\<close> using assms(3) unfolding t by simp
    then show ?thesis using r f unfolding t ow_eqs width.simps by simp
  qed (use r f in \<open>simp_all add: ow_eqs\<close>)
qed

lemma bin_cost_le:
  assumes \<open>k0 < 2 ^ 64\<close> \<open>k1 < 2 ^ 64\<close> \<open>D ! k0 \<le> w\<close> \<open>D ! k1 \<le> w\<close>
    \<open>width ws D (TermL_Bin bo (tref k0) (tref k1)) \<le> w\<close> \<open>1 \<le> w\<close>
  shows \<open>ow ws D (TermL_Bin bo (tref k0) (tref k1)) \<le> 24 * w + ebin bo w\<close>
proof -
  have a: \<open>fw (opw bo (width ws D (tref k0)) (width ws D (tref k1))) \<le> 8 * w\<close>
    using fw_le[OF assms(5,6)] by (simp only: width_Bin_opw)
  have b: \<open>fw (D ! k0) \<le> 8 * w\<close> \<open>fw (D ! k1) \<le> 8 * w\<close> using assms(3,4,6) fw_le by simp_all
  have e: \<open>ebin bo (D ! k0) \<le> ebin bo w\<close> using assms(3) by (rule ebin_mono)
  have \<open>ow ws D (TermL_Bin bo (tref k0) (tref k1)) =
      fw (opw bo (width ws D (tref k0)) (width ws D (tref k1))) + (ebin bo (D ! k0) + (fw (D ! k0) + fw (D ! k1)))\<close>
    using assms(1,2) by (simp only: ow_eqs ow_tref width_tref)
  then show ?thesis using a b e by simp
qed

lemma cmp_cost:
  assumes \<open>bo = Op_Eq \<or> bo = Op_Distinct\<close> \<open>k0 < 2 ^ 64\<close> \<open>k1 < 2 ^ 64\<close> \<open>D ! k0 \<le> w\<close> \<open>D ! k1 \<le> w\<close>
    \<open>1 \<le> w\<close> \<open>w \<le> WB\<close>
  shows \<open>ow ws D (TermL_Bin bo (tref k0) (tref k1)) \<le> 234 * w\<close> \<open>width ws D (TermL_Bin bo (tref k0) (tref k1)) = 1\<close>
proof -
  have o: \<open>opw bo (width ws D (tref k0)) (width ws D (tref k1)) = 1\<close> using assms(1) by (auto simp: opw_def)
  have e: \<open>ebin bo (D ! k0) \<le> 210 * w\<close>
    using ebin_mono[OF assms(4), of bo] ebin_le(1)[OF assms(6,7), of bo] assms(1) by auto
  have b: \<open>fw (D ! k0) \<le> 8 * w\<close> \<open>fw (D ! k1) \<le> 8 * w\<close> using assms(4,5,6) fw_le by simp_all
  have \<open>ow ws D (TermL_Bin bo (tref k0) (tref k1)) = fw 1 + (ebin bo (D ! k0) + (fw (D ! k0) + fw (D ! k1)))\<close>
    using assms(2,3) o by (simp only: ow_eqs ow_tref width_tref)
  then show \<open>ow ws D (TermL_Bin bo (tref k0) (tref k1)) \<le> 234 * w\<close> using e b assms(6) by (simp add: fw_def)
  show \<open>width ws D (TermL_Bin bo (tref k0) (tref k1)) = 1\<close> using o by (simp only: width_Bin_opw)
qed

lemma pairs_m_lt:
  assumes \<open>2 \<le> n\<close> \<open>ij \<in> set (pairs_m n)\<close>
  shows \<open>fst ij < n \<and> snd ij < n\<close>
proof -
  have \<open>ij \<in> {(i, j). i < j \<and> j < n}\<close> using pairs_m_set[OF assms(1)] assms(2) by blast
  then show ?thesis by (cases ij) simp
qed

text \<open>The cost of a node per argument and per one more, as in \<^const>\<open>smt_ncost\<close>.\<close>
definition ucost :: \<open>SmtOp \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>ucost op k w \<equiv>
     if op \<in> {SmtOp_Bvmul, SmtOp_Bvudiv, SmtOp_Bvurem, SmtOp_Bvsdiv, SmtOp_Bvsrem, SmtOp_Bvsmod} then w * w
     else if op = SmtOp_Distinct then k * w else w\<close>

lemma lin_bound:
  assumes \<open>1 \<le> W\<close> \<open>x \<le> a * W + k * (b * W)\<close> \<open>a + 1 \<le> cK\<close> \<open>b \<le> cK\<close>
  shows \<open>x + 1 \<le> cK * ((1 + k) * W)\<close>
proof -
  have 1: \<open>(a + 1) * W \<le> cK * W\<close> using assms(3) by (rule mult_le_mono1)
  have 2: \<open>k * (b * W) \<le> k * (cK * W)\<close> using assms(4) by (intro mult_le_mono2 mult_le_mono1)
  have 3: \<open>cK * ((1 + k) * W) = cK * W + k * (cK * W)\<close> by (simp add: algebra_simps)
  show ?thesis using assms(1,2) 1 2 3 by (simp add: algebra_simps)
qed

text \<open>The cost of the translation of an application with the arguments \<open>ks\<close>, whose definitions
  and result have widths at most \<open>w\<close>.\<close>
lemma app_cost:
  assumes \<open>sop_ar op \<le> length ks\<close> \<open>\<forall>k \<in> set ks. k < 2 ^ 64 \<and> D ! k \<le> w\<close>
    \<open>width ws D (tr_app_m op ks) \<le> w\<close> \<open>1 \<le> w\<close> \<open>w \<le> WB\<close>
  shows \<open>ow ws D (tr_app_m op ks) + 1 \<le> cK * ((1 + length ks) * ucost op (length ks) w)\<close>
proof -
  let ?k = \<open>length ks\<close>
  have w1: \<open>1 \<le> w\<close> and wW: \<open>w \<le> WB\<close> using assms(4,5) .
  have ww: \<open>w \<le> w * w\<close> \<open>1 \<le> w * w\<close> using w1 by simp_all
  have kk: \<open>\<And>i. i < ?k \<Longrightarrow> ks ! i < 2 ^ 64 \<and> D ! (ks ! i) \<le> w\<close> using assms(2) nth_mem by blast
  have ksl: \<open>\<forall>k \<in> set ks. k < 2 ^ 64 \<and> D ! k \<le> w\<close> using assms(2) .
  have nel: \<open>1 \<le> ?k \<Longrightarrow> ks \<noteq> []\<close> \<open>2 \<le> ?k \<Longrightarrow> ks \<noteq> []\<close> \<open>3 \<le> ?k \<Longrightarrow> ks \<noteq> []\<close> by auto
  have cK: \<open>cK = 1024\<close> by (simp add: cK_def)
  have U: \<open>\<And>t hi lo i. 1 \<le> ?k \<Longrightarrow> width ws D t \<le> w \<Longrightarrow>
      t = TermL_Not (tref (ks ! 0)) \<or> t = TermL_Neg (tref (ks ! 0)) \<or> t = TermL_Extract hi lo (tref (ks ! 0)) \<or>
      t = TermL_Repeat i (tref (ks ! 0)) \<or> t = TermL_ZeroExtend i (tref (ks ! 0)) \<or> t = TermL_SignExtend i (tref (ks ! 0)) \<or>
      t = TermL_RotateLeft i (tref (ks ! 0)) \<or> t = TermL_RotateRight i (tref (ks ! 0)) \<Longrightarrow>
      ow ws D t + 1 \<le> cK * ((1 + ?k) * w)\<close>
  proof -
    fix t hi lo i assume a: \<open>1 \<le> ?k\<close> \<open>width ws D t \<le> w\<close>
      \<open>t = TermL_Not (tref (ks ! 0)) \<or> t = TermL_Neg (tref (ks ! 0)) \<or> t = TermL_Extract hi lo (tref (ks ! 0)) \<or>
      t = TermL_Repeat i (tref (ks ! 0)) \<or> t = TermL_ZeroExtend i (tref (ks ! 0)) \<or> t = TermL_SignExtend i (tref (ks ! 0)) \<or>
      t = TermL_RotateLeft i (tref (ks ! 0)) \<or> t = TermL_RotateRight i (tref (ks ! 0))\<close>
    have \<open>ow ws D t \<le> 31 * w\<close>
      using un_cost[OF kk[of 0, THEN conjunct1] kk[of 0, THEN conjunct2] a(2) w1 a(3)] a(1) nel by auto
    then show \<open>ow ws D t + 1 \<le> cK * ((1 + ?k) * w)\<close> using lin_bound[OF w1, of _ 31 ?k 0] by (simp add: cK)
  qed
  have Bn: \<open>\<And>bo W. 2 \<le> ?k \<Longrightarrow> width ws D (TermL_Bin bo (tref (ks ! 0)) (tref (ks ! 1))) \<le> w \<Longrightarrow>
      1 \<le> W \<Longrightarrow> w \<le> W \<Longrightarrow> ebin bo w \<le> 396 * W \<Longrightarrow>
      ow ws D (TermL_Bin bo (tref (ks ! 0)) (tref (ks ! 1))) + 1 \<le> cK * ((1 + ?k) * W)\<close>
  proof -
    fix bo W assume a: \<open>2 \<le> ?k\<close> \<open>width ws D (TermL_Bin bo (tref (ks ! 0)) (tref (ks ! 1))) \<le> w\<close>
      \<open>1 \<le> W\<close> \<open>w \<le> W\<close> \<open>ebin bo w \<le> 396 * W\<close>
    have \<open>ow ws D (TermL_Bin bo (tref (ks ! 0)) (tref (ks ! 1))) \<le> 24 * w + ebin bo w\<close>
      using bin_cost_le[OF kk[of 0, THEN conjunct1] kk[of 1, THEN conjunct1] kk[of 0, THEN conjunct2]
          kk[of 1, THEN conjunct2] a(2) w1] a(1) nel by auto
    then have \<open>ow ws D (TermL_Bin bo (tref (ks ! 0)) (tref (ks ! 1))) \<le> 420 * W + ?k * (0 * W)\<close> using a(4,5) by simp
    then show \<open>ow ws D (TermL_Bin bo (tref (ks ! 0)) (tref (ks ! 1))) + 1 \<le> cK * ((1 + ?k) * W)\<close>
      using lin_bound[OF a(3)] by (simp add: cK)
  qed
  have nm: \<open>\<And>bo. bo \<notin> {Op_Mul, Op_Udiv, Op_Urem, Op_Sdiv, Op_Srem, Op_Smod} \<Longrightarrow> ebin bo w \<le> 396 * w\<close>
    using ebin_le(1)[OF w1 wW] by fastforce
  have md: \<open>\<And>bo. ebin bo w \<le> 396 * (w * w)\<close> using ebin_le(2)[OF w1 wW] .
  have FOLD: \<open>\<And>bo. bo \<in> {Op_And, Op_Or, Op_Xor, Op_Add} \<Longrightarrow> 2 \<le> ?k \<Longrightarrow>
      ow ws D (foldl (\<lambda>acc k. TermL_Bin bo acc (tref k)) (tref (hd ks)) (tl ks)) + 1 \<le> cK * ((1 + ?k) * w)\<close>
  proof -
    fix bo assume a: \<open>bo \<in> {Op_And, Op_Or, Op_Xor, Op_Add}\<close> \<open>2 \<le> ?k\<close>
    have ne: \<open>ks \<noteq> []\<close> using a(2) by auto
    have h: \<open>hd ks < 2 ^ 64 \<and> D ! hd ks \<le> w\<close> using ksl hd_in_set[OF ne] by blast
    have t: \<open>\<forall>k \<in> set (tl ks). k < 2 ^ 64 \<and> D ! k \<le> w\<close> using ksl by (meson list.set_sel(2) ne)
    have F: \<open>ow ws D (foldl (\<lambda>acc k. TermL_Bin bo acc (tref k)) (tref (hd ks)) (tl ks)) \<le>
        ow ws D (tref (hd ks)) + length (tl ks) * (2 * fw w + ebin bo w)\<close>
      using ow_fold[OF t, of ws \<open>tref (hd ks)\<close> bo] h a(1) by (auto simp: width_tref)
    have e: \<open>2 * fw w + ebin bo w \<le> 226 * w\<close> using ebin_le(1)[OF w1 wW, of bo] a(1) fw_le[OF le_refl w1] by auto
    have r: \<open>ow ws D (tref (hd ks)) \<le> 8 * w\<close> using h fw_le w1 by (simp add: ow_tref)
    have m: \<open>length (tl ks) * (2 * fw w + ebin bo w) \<le> ?k * (226 * w)\<close> using e by (intro mult_le_mono) simp_all
    show \<open>ow ws D (foldl (\<lambda>acc k. TermL_Bin bo acc (tref k)) (tref (hd ks)) (tl ks)) + 1 \<le> cK * ((1 + ?k) * w)\<close>
      using lin_bound[OF w1, of _ 8 ?k 226] F r m by (simp add: cK)
  qed
  show ?thesis
  proof (cases op)
    case (SmtOp_Not )
    show ?thesis using U[of \<open>TermL_Not (tref (ks ! 0))\<close> _ _ _] assms(1,3) unfolding SmtOp_Not by (simp add: ucost_def)
  next
    case (SmtOp_Bvnot )
    show ?thesis using U[of \<open>TermL_Not (tref (ks ! 0))\<close> _ _ _] assms(1,3) unfolding SmtOp_Bvnot by (simp add: ucost_def)
  next
    case (SmtOp_Bvneg )
    show ?thesis using U[of \<open>TermL_Neg (tref (ks ! 0))\<close> _ _ _] assms(1,3) unfolding SmtOp_Bvneg by (simp add: ucost_def)
  next
    case (SmtOp_Extract i j)
    show ?thesis using U[of \<open>TermL_Extract i j (tref (ks ! 0))\<close> i j _] assms(1,3) unfolding SmtOp_Extract by (simp add: ucost_def)
  next
    case (SmtOp_Repeat i)
    show ?thesis using U[of \<open>TermL_Repeat i (tref (ks ! 0))\<close> _ _ i] assms(1,3) unfolding SmtOp_Repeat by (simp add: ucost_def)
  next
    case (SmtOp_ZeroExtend i)
    show ?thesis using U[of \<open>TermL_ZeroExtend i (tref (ks ! 0))\<close> _ _ i] assms(1,3) unfolding SmtOp_ZeroExtend by (simp add: ucost_def)
  next
    case (SmtOp_SignExtend i)
    show ?thesis using U[of \<open>TermL_SignExtend i (tref (ks ! 0))\<close> _ _ i] assms(1,3) unfolding SmtOp_SignExtend by (simp add: ucost_def)
  next
    case (SmtOp_RotateLeft i)
    show ?thesis using U[of \<open>TermL_RotateLeft i (tref (ks ! 0))\<close> _ _ i] assms(1,3) unfolding SmtOp_RotateLeft by (simp add: ucost_def)
  next
    case (SmtOp_RotateRight i)
    show ?thesis using U[of \<open>TermL_RotateRight i (tref (ks ! 0))\<close> _ _ i] assms(1,3) unfolding SmtOp_RotateRight by (simp add: ucost_def)
  next
    case SmtOp_And
    show ?thesis using FOLD[of \<open>tr_op SmtOp_And\<close>] assms(1) unfolding SmtOp_And by (simp add: fold_left_m_def ucost_def)
  next
    case SmtOp_Or
    show ?thesis using FOLD[of \<open>tr_op SmtOp_Or\<close>] assms(1) unfolding SmtOp_Or by (simp add: fold_left_m_def ucost_def)
  next
    case SmtOp_Xor
    show ?thesis using FOLD[of \<open>tr_op SmtOp_Xor\<close>] assms(1) unfolding SmtOp_Xor by (simp add: fold_left_m_def ucost_def)
  next
    case SmtOp_Bvand
    show ?thesis using FOLD[of \<open>tr_op SmtOp_Bvand\<close>] assms(1) unfolding SmtOp_Bvand by (simp add: fold_left_m_def ucost_def)
  next
    case SmtOp_Bvor
    show ?thesis using FOLD[of \<open>tr_op SmtOp_Bvor\<close>] assms(1) unfolding SmtOp_Bvor by (simp add: fold_left_m_def ucost_def)
  next
    case SmtOp_Bvadd
    show ?thesis using FOLD[of \<open>tr_op SmtOp_Bvadd\<close>] assms(1) unfolding SmtOp_Bvadd by (simp add: fold_left_m_def ucost_def)
  next
    case SmtOp_Bvxor
    show ?thesis using FOLD[of \<open>tr_op SmtOp_Bvxor\<close>] assms(1) unfolding SmtOp_Bvxor by (simp add: fold_left_m_def ucost_def)
  next
    case SmtOp_Bvudiv
    show ?thesis using Bn[of \<open>tr_op SmtOp_Bvudiv\<close> \<open>w * w\<close>] md[of \<open>tr_op SmtOp_Bvudiv\<close>] ww assms(1,3) unfolding SmtOp_Bvudiv by (simp add: ucost_def)
  next
    case SmtOp_Bvurem
    show ?thesis using Bn[of \<open>tr_op SmtOp_Bvurem\<close> \<open>w * w\<close>] md[of \<open>tr_op SmtOp_Bvurem\<close>] ww assms(1,3) unfolding SmtOp_Bvurem by (simp add: ucost_def)
  next
    case SmtOp_Bvsdiv
    show ?thesis using Bn[of \<open>tr_op SmtOp_Bvsdiv\<close> \<open>w * w\<close>] md[of \<open>tr_op SmtOp_Bvsdiv\<close>] ww assms(1,3) unfolding SmtOp_Bvsdiv by (simp add: ucost_def)
  next
    case SmtOp_Bvsrem
    show ?thesis using Bn[of \<open>tr_op SmtOp_Bvsrem\<close> \<open>w * w\<close>] md[of \<open>tr_op SmtOp_Bvsrem\<close>] ww assms(1,3) unfolding SmtOp_Bvsrem by (simp add: ucost_def)
  next
    case SmtOp_Bvsmod
    show ?thesis using Bn[of \<open>tr_op SmtOp_Bvsmod\<close> \<open>w * w\<close>] md[of \<open>tr_op SmtOp_Bvsmod\<close>] ww assms(1,3) unfolding SmtOp_Bvsmod by (simp add: ucost_def)
  next
    case SmtOp_Concat
    show ?thesis using Bn[of \<open>tr_op SmtOp_Concat\<close> w] nm[of \<open>tr_op SmtOp_Concat\<close>] w1 assms(1,3) unfolding SmtOp_Concat by (simp add: ucost_def)
  next
    case SmtOp_Bvult
    show ?thesis using Bn[of \<open>tr_op SmtOp_Bvult\<close> w] nm[of \<open>tr_op SmtOp_Bvult\<close>] w1 assms(1,3) unfolding SmtOp_Bvult by (simp add: ucost_def)
  next
    case SmtOp_Bvnand
    show ?thesis using Bn[of \<open>tr_op SmtOp_Bvnand\<close> w] nm[of \<open>tr_op SmtOp_Bvnand\<close>] w1 assms(1,3) unfolding SmtOp_Bvnand by (simp add: ucost_def)
  next
    case SmtOp_Bvnor
    show ?thesis using Bn[of \<open>tr_op SmtOp_Bvnor\<close> w] nm[of \<open>tr_op SmtOp_Bvnor\<close>] w1 assms(1,3) unfolding SmtOp_Bvnor by (simp add: ucost_def)
  next
    case SmtOp_Bvxnor
    show ?thesis using Bn[of \<open>tr_op SmtOp_Bvxnor\<close> w] nm[of \<open>tr_op SmtOp_Bvxnor\<close>] w1 assms(1,3) unfolding SmtOp_Bvxnor by (simp add: ucost_def)
  next
    case SmtOp_Bvcomp
    show ?thesis using Bn[of \<open>tr_op SmtOp_Bvcomp\<close> w] nm[of \<open>tr_op SmtOp_Bvcomp\<close>] w1 assms(1,3) unfolding SmtOp_Bvcomp by (simp add: ucost_def)
  next
    case SmtOp_Bvsub
    show ?thesis using Bn[of \<open>tr_op SmtOp_Bvsub\<close> w] nm[of \<open>tr_op SmtOp_Bvsub\<close>] w1 assms(1,3) unfolding SmtOp_Bvsub by (simp add: ucost_def)
  next
    case SmtOp_Bvshl
    show ?thesis using Bn[of \<open>tr_op SmtOp_Bvshl\<close> w] nm[of \<open>tr_op SmtOp_Bvshl\<close>] w1 assms(1,3) unfolding SmtOp_Bvshl by (simp add: ucost_def)
  next
    case SmtOp_Bvlshr
    show ?thesis using Bn[of \<open>tr_op SmtOp_Bvlshr\<close> w] nm[of \<open>tr_op SmtOp_Bvlshr\<close>] w1 assms(1,3) unfolding SmtOp_Bvlshr by (simp add: ucost_def)
  next
    case SmtOp_Bvashr
    show ?thesis using Bn[of \<open>tr_op SmtOp_Bvashr\<close> w] nm[of \<open>tr_op SmtOp_Bvashr\<close>] w1 assms(1,3) unfolding SmtOp_Bvashr by (simp add: ucost_def)
  next
    case SmtOp_Bvule
    show ?thesis using Bn[of \<open>tr_op SmtOp_Bvule\<close> w] nm[of \<open>tr_op SmtOp_Bvule\<close>] w1 assms(1,3) unfolding SmtOp_Bvule by (simp add: ucost_def)
  next
    case SmtOp_Bvugt
    show ?thesis using Bn[of \<open>tr_op SmtOp_Bvugt\<close> w] nm[of \<open>tr_op SmtOp_Bvugt\<close>] w1 assms(1,3) unfolding SmtOp_Bvugt by (simp add: ucost_def)
  next
    case SmtOp_Bvuge
    show ?thesis using Bn[of \<open>tr_op SmtOp_Bvuge\<close> w] nm[of \<open>tr_op SmtOp_Bvuge\<close>] w1 assms(1,3) unfolding SmtOp_Bvuge by (simp add: ucost_def)
  next
    case SmtOp_Bvslt
    show ?thesis using Bn[of \<open>tr_op SmtOp_Bvslt\<close> w] nm[of \<open>tr_op SmtOp_Bvslt\<close>] w1 assms(1,3) unfolding SmtOp_Bvslt by (simp add: ucost_def)
  next
    case SmtOp_Bvsle
    show ?thesis using Bn[of \<open>tr_op SmtOp_Bvsle\<close> w] nm[of \<open>tr_op SmtOp_Bvsle\<close>] w1 assms(1,3) unfolding SmtOp_Bvsle by (simp add: ucost_def)
  next
    case SmtOp_Bvsgt
    show ?thesis using Bn[of \<open>tr_op SmtOp_Bvsgt\<close> w] nm[of \<open>tr_op SmtOp_Bvsgt\<close>] w1 assms(1,3) unfolding SmtOp_Bvsgt by (simp add: ucost_def)
  next
    case SmtOp_Bvsge
    show ?thesis using Bn[of \<open>tr_op SmtOp_Bvsge\<close> w] nm[of \<open>tr_op SmtOp_Bvsge\<close>] w1 assms(1,3) unfolding SmtOp_Bvsge by (simp add: ucost_def)
  next
    case SmtOp_Bvmul
    have ne: \<open>ks \<noteq> []\<close> using assms(1) unfolding SmtOp_Bvmul by auto
    have h: \<open>hd ks < 2 ^ 64 \<and> D ! hd ks \<le> w\<close> using ksl hd_in_set[OF ne] by blast
    have t: \<open>\<forall>k \<in> set (tl ks). k < 2 ^ 64 \<and> D ! k \<le> w\<close> using ksl by (meson list.set_sel(2) ne)
    have F: \<open>ow ws D (foldl (\<lambda>acc k. TermL_Bin Op_Mul acc (tref k)) (tref (hd ks)) (tl ks)) \<le>
        ow ws D (tref (hd ks)) + length (tl ks) * (2 * fw w + ebin Op_Mul w)\<close>
      using ow_fold[OF t, of ws \<open>tref (hd ks)\<close> Op_Mul] h by (simp add: width_tref)
    have r: \<open>ow ws D (tref (hd ks)) \<le> 8 * (w * w)\<close> using h fw_le[of \<open>D ! hd ks\<close> w] w1 ww by (simp add: ow_tref)
    have e: \<open>2 * fw w + ebin Op_Mul w \<le> 412 * (w * w)\<close> using md[of Op_Mul] fw_le[OF le_refl w1] ww by linarith
    have l: \<open>length (tl ks) * (2 * fw w + ebin Op_Mul w) \<le> ?k * (412 * (w * w))\<close> using e by (intro mult_le_mono) simp_all
    show ?thesis using lin_bound[OF ww(2), of _ 8 ?k 412] F r l unfolding SmtOp_Bvmul
      by (simp add: fold_left_m_def ucost_def cK)
  next
    case SmtOp_Implies
    have ne: \<open>ks \<noteq> []\<close> using assms(1) unfolding SmtOp_Implies by auto
    have h: \<open>last ks < 2 ^ 64 \<and> D ! last ks \<le> w\<close> using ksl last_in_set[OF ne] by blast
    have t: \<open>\<forall>k \<in> set (butlast ks). k < 2 ^ 64 \<and> D ! k \<le> w\<close> using ksl by (meson in_set_butlastD)
    have F: \<open>ow ws D (implies_m ks) \<le> ow ws D (tref (last ks)) + length (butlast ks) * (3 * fw w + ebin Op_Or w)\<close>
      unfolding implies_m_def by (rule ow_foldr_imp[OF t])
    have r: \<open>ow ws D (tref (last ks)) \<le> 8 * w\<close> using h fw_le w1 by (simp add: ow_tref)
    have e: \<open>3 * fw w + ebin Op_Or w \<le> 234 * w\<close> using ebin_le(1)[OF w1 wW, of Op_Or] fw_le[OF le_refl w1] by simp
    have l: \<open>length (butlast ks) * (3 * fw w + ebin Op_Or w) \<le> ?k * (234 * w)\<close> using e by (intro mult_le_mono) simp_all
    show ?thesis using lin_bound[OF w1, of _ 8 ?k 234] F r l unfolding SmtOp_Implies by (simp add: ucost_def cK)
  next
    case SmtOp_Ite
    have k3: \<open>3 \<le> ?k\<close> using assms(1) unfolding SmtOp_Ite by simp
    have w': \<open>ks ! 0 < 2 ^ 64 \<and> D ! (ks ! 0) \<le> w\<close> \<open>ks ! 1 < 2 ^ 64 \<and> D ! (ks ! 1) \<le> w\<close> \<open>ks ! 2 < 2 ^ 64 \<and> D ! (ks ! 2) \<le> w\<close>
      using kk[of 0] kk[of 1] kk[of 2] k3 nel by auto
    have b: \<open>fw (D ! (ks ! 0)) \<le> 8 * w\<close> \<open>fw (D ! (ks ! 1)) \<le> 8 * w\<close> \<open>fw (D ! (ks ! 2)) \<le> 8 * w\<close>
      using w' fw_le w1 by simp_all
    have \<open>ow ws D (TermL_Ite (tref (ks ! 0)) (tref (ks ! 1)) (tref (ks ! 2))) =
        fw (D ! (ks ! 1)) + (5 * D ! (ks ! 1) + (fw (D ! (ks ! 0)) + (fw (D ! (ks ! 1)) + fw (D ! (ks ! 2)))))\<close>
      using w' by (simp only: ow_eqs ow_tref width_tref)
    then have \<open>ow ws D (TermL_Ite (tref (ks ! 0)) (tref (ks ! 1)) (tref (ks ! 2))) \<le> 37 * w + ?k * (0 * w)\<close>
      using b w'(2) by simp
    then show ?thesis using lin_bound[OF w1] unfolding SmtOp_Ite by (simp add: ucost_def cK)
  next
    case SmtOp_Eq
    have k2: \<open>2 \<le> ?k\<close> using assms(1) unfolding SmtOp_Eq by simp
    have g: \<open>\<forall>i \<in> set [2..<?k]. ow ws D (TermL_Bin Op_Eq (tref (ks ! (i - 1))) (tref (ks ! i))) \<le> 234 * w\<close>
    proof
      fix i assume \<open>i \<in> set [2..<?k]\<close>
      then have \<open>i - 1 < ?k\<close> \<open>i < ?k\<close> by auto
      then show \<open>ow ws D (TermL_Bin Op_Eq (tref (ks ! (i - 1))) (tref (ks ! i))) \<le> 234 * w\<close>
        using cmp_cost(1)[of Op_Eq _ _ D w ws, OF _ _ _ _ _ w1 wW] kk by blast
    qed
    have b0: \<open>ow ws D (TermL_Bin Op_Eq (tref (ks ! 0)) (tref (ks ! 1))) \<le> 234 * w\<close>
      \<open>width ws D (TermL_Bin Op_Eq (tref (ks ! 0)) (tref (ks ! 1))) = 1\<close>
      using cmp_cost[of Op_Eq \<open>ks ! 0\<close> \<open>ks ! 1\<close> D w ws, OF _ _ _ _ _ w1 wW] kk[of 0] kk[of 1] k2 nel by auto
    have F: \<open>ow ws D (chain_m SmtOp_Eq ks) \<le> 234 * w + length [2..<?k] * (fw 1 + ebin Op_And 1 + 234 * w)\<close>
      using ow_fold_and[OF g b0(2)] b0(1) unfolding chain_m_def by simp
    have e: \<open>fw 1 + ebin Op_And 1 + 234 * w \<le> 292 * w\<close> using w1 by (simp add: fw_def ebin_def)
    have l: \<open>length [2..<?k] * (fw 1 + ebin Op_And 1 + 234 * w) \<le> ?k * (292 * w)\<close> using e by (intro mult_le_mono) simp_all
    show ?thesis using lin_bound[OF w1, of _ 234 ?k 292] F l unfolding SmtOp_Eq by (simp add: ucost_def cK)
  next
    case SmtOp_Distinct
    have k2: \<open>2 \<le> ?k\<close> using assms(1) unfolding SmtOp_Distinct by simp
    have kw: \<open>1 \<le> ?k * w\<close> \<open>w \<le> ?k * w\<close> using k2 w1 by simp_all
    have g: \<open>\<forall>ij \<in> set (pairs_m ?k). ow ws D (TermL_Bin Op_Distinct (tref (ks ! fst ij)) (tref (ks ! snd ij))) \<le> 234 * w\<close>
    proof
      fix ij assume \<open>ij \<in> set (pairs_m ?k)\<close>
      then have \<open>fst ij < ?k\<close> \<open>snd ij < ?k\<close> using pairs_m_lt[OF k2] by blast+
      then show \<open>ow ws D (TermL_Bin Op_Distinct (tref (ks ! fst ij)) (tref (ks ! snd ij))) \<le> 234 * w\<close>
        using cmp_cost(1)[of Op_Distinct _ _ D w ws, OF _ _ _ _ _ w1 wW] kk by blast
    qed
    have b0: \<open>ow ws D (TermL_Bin Op_Distinct (tref (ks ! 0)) (tref (ks ! 1))) \<le> 234 * w\<close>
      \<open>width ws D (TermL_Bin Op_Distinct (tref (ks ! 0)) (tref (ks ! 1))) = 1\<close>
      using cmp_cost[of Op_Distinct \<open>ks ! 0\<close> \<open>ks ! 1\<close> D w ws, OF _ _ _ _ _ w1 wW] kk[of 0] kk[of 1] k2 nel by auto
    have F: \<open>ow ws D (pairwise_m ks) \<le> 234 * w + length (pairs_m ?k) * (fw 1 + ebin Op_And 1 + 234 * w)\<close>
      using ow_fold_and[OF g b0(2)] b0(1) unfolding pairwise_m_def by simp
    have e: \<open>fw 1 + ebin Op_And 1 + 234 * w \<le> 292 * w\<close> using w1 by (simp add: fw_def ebin_def)
    have P: \<open>2 * length (pairs_m ?k) \<le> ?k * ?k\<close> using pairs_m_len2[of ?k] by (simp add: algebra_simps)
    have \<open>2 * (length (pairs_m ?k) * (fw 1 + ebin Op_And 1 + 234 * w)) \<le> (?k * ?k) * (292 * w)\<close>
      using mult_le_mono[OF P e] by (simp add: algebra_simps)
    then have \<open>length (pairs_m ?k) * (fw 1 + ebin Op_And 1 + 234 * w) \<le> ?k * (146 * (?k * w))\<close>
      by (simp add: algebra_simps)
    moreover have \<open>234 * w \<le> 234 * (?k * w)\<close> using kw(2) by simp
    ultimately have \<open>ow ws D (pairwise_m ks) \<le> 234 * (?k * w) + ?k * (146 * (?k * w))\<close> using F by linarith
    then show ?thesis using lin_bound[OF kw(1), of _ 234 ?k 146] unfolding SmtOp_Distinct by (simp add: ucost_def cK)
  qed
qed

subsection \<open>The range of every node\<close>

text \<open>A node within the range, and a term all of whose subterms are.\<close>
definition nr :: \<open>SmtFun list \<Rightarrow> SmtDef list \<Rightarrow> SmtSort list \<Rightarrow> SmtTerm \<Rightarrow> bool\<close> where
  \<open>nr fs ds ps u \<equiv> smt_twidth fs ds ps u \<le> WB\<close>

definition rng :: \<open>SmtFun list \<Rightarrow> SmtDef list \<Rightarrow> SmtSort list \<Rightarrow> SmtTerm \<Rightarrow> bool\<close> where
  \<open>rng fs ds ps t \<equiv> \<forall>u \<in> set (smt_subterms t). nr fs ds ps u\<close>

lemma rng_simps:
  \<open>rng fs ds ps (SmtTerm_App op args) \<longleftrightarrow> nr fs ds ps (SmtTerm_App op args) \<and> (\<forall>a \<in> set (rvec_elems args). rng fs ds ps a)\<close>
  \<open>rng fs ds ps (SmtTerm_Def d args) \<longleftrightarrow> nr fs ds ps (SmtTerm_Def d args) \<and> (\<forall>a \<in> set (rvec_elems args). rng fs ds ps a)\<close>
  \<open>rng fs ds ps (SmtTerm_Fun f args) \<longleftrightarrow> nr fs ds ps (SmtTerm_Fun f args) \<and> (\<forall>a \<in> set (rvec_elems args). rng fs ds ps a)\<close>
  \<open>rng fs ds ps (SmtTerm_BoolConst b) \<longleftrightarrow> nr fs ds ps (SmtTerm_BoolConst b)\<close>
  \<open>rng fs ds ps (SmtTerm_BvConst bs) \<longleftrightarrow> nr fs ds ps (SmtTerm_BvConst bs)\<close>
  \<open>rng fs ds ps (SmtTerm_Param k) \<longleftrightarrow> nr fs ds ps (SmtTerm_Param k)\<close>
  by (auto simp: rng_def)

lemma sw_le: \<open>smt_width s \<le> WB \<Longrightarrow> sort_width_m s \<le> WB\<close>
  by (cases s) (auto simp: WB_def)

lemma nr_width:
  \<open>nr fs ds ps u \<Longrightarrow> smt_tsort fs ds ps u = Some s \<Longrightarrow> sort_width_m s \<le> WB\<close>
  by (auto simp: nr_def smt_twidth_def intro: sw_le)

text \<open>Every node of the bodies of the definitions and of the assertions of a problem in the range.\<close>
lemma in_range_rng:
  assumes \<open>smt_in_range p\<close>
  shows \<open>\<forall>d < length (sdefs p). rng (sfuns p) (take d (sdefs p))
            (dpar (sdefs p ! d)) (SmtDef_body (sdefs p ! d))\<close>
    and \<open>\<forall>t \<in> set (sasserts p). rng (sfuns p) (sdefs p) [] t\<close>
    and \<open>\<forall>f \<in> set (sfuns p). smt_width (SmtFun_ret f) \<le> WB\<close>
    and \<open>smt_size p \<le> 2 ^ 30\<close> and \<open>smt_cost p \<le> 2 ^ 43\<close>
proof -
  let ?fs = \<open>sfuns p\<close> and ?ds = \<open>sdefs p\<close> and ?as = \<open>sasserts p\<close>
  have R: \<open>smt_max_width p \<le> WB\<close> using assms by (simp add: smt_in_range_def WB_def)
  show \<open>smt_size p \<le> 2 ^ 30\<close> \<open>smt_cost p \<le> 2 ^ 43\<close> using assms by (simp_all add: smt_in_range_def)
  have fT: \<open>finite (smt_term_widths Q p)\<close> for Q by (simp add: smt_term_widths_def Let_def)
  have fS: \<open>finite (smt_sort_widths p)\<close> by (simp add: smt_sort_widths_def)
  have mw: \<open>x \<le> WB\<close> if \<open>x \<in> smt_term_widths (\<lambda>_. True) p \<or> x \<in> smt_sort_widths p\<close> for x
  proof -
    have \<open>x \<le> smt_max_width p\<close> unfolding smt_max_width_def using that fT fS by (intro Max_ge) auto
    then show ?thesis using R by simp
  qed
  show \<open>\<forall>d < length ?ds. rng ?fs (take d ?ds) (dpar (?ds ! d)) (SmtDef_body (?ds ! d))\<close>
  proof (intro allI impI)
    fix d assume d: \<open>d < length ?ds\<close>
    show \<open>rng ?fs (take d ?ds) (dpar (?ds ! d)) (SmtDef_body (?ds ! d))\<close>
      unfolding rng_def nr_def
    proof
      fix u assume u: \<open>u \<in> set (smt_subterms (SmtDef_body (?ds ! d)))\<close>
      show \<open>smt_twidth ?fs (take d ?ds) (dpar (?ds ! d)) u \<le> WB\<close>
        using d u by (intro mw) (auto simp: smt_term_widths_def Let_def)
    qed
  qed
  show \<open>\<forall>t \<in> set ?as. rng ?fs ?ds [] t\<close>
  proof
    fix t assume t: \<open>t \<in> set ?as\<close>
    show \<open>rng ?fs ?ds [] t\<close> unfolding rng_def nr_def
    proof
      fix u assume u: \<open>u \<in> set (smt_subterms t)\<close>
      show \<open>smt_twidth ?fs ?ds [] u \<le> WB\<close> using t u by (intro mw) (auto simp: smt_term_widths_def Let_def)
    qed
  qed
  show \<open>\<forall>f \<in> set ?fs. smt_width (SmtFun_ret f) \<le> WB\<close>
    using mw by (auto simp: smt_sort_widths_def)
qed

subsection \<open>The number of definitions\<close>

lemma cnt_le_nodes:
  \<open>n \<le> length (sdefs p) \<Longrightarrow> Suc (cnt p n t) \<le> smt_nodes (take n (sdefs p)) t\<close>
  \<open>n \<le> length (sdefs p) \<Longrightarrow> cnt_args p n ts \<le> sum_list (map (smt_nodes (take n (sdefs p))) ts)\<close>
proof (induction p n t and p n ts rule: cnt_cnt_args.induct)
  case (1 p n d args)
  let ?ds = \<open>sdefs p\<close>
  show ?case
  proof (cases \<open>dpar (?ds ! unat d) = [] \<or> \<not> unat d < n\<close>)
    case True
    then show ?thesis by auto
  next
    case False
    then have nd: \<open>unat d < n\<close> \<open>dpar (?ds ! unat d) \<noteq> []\<close> by auto
    have a: \<open>cnt_args p n args \<le> sum_list (map (smt_nodes (take n ?ds)) args)\<close> using 1(1) nd 1(3) by simp
    have b: \<open>Suc (cnt p (unat d) (SmtDef_body (?ds ! unat d))) \<le> smt_nodes (take (unat d) ?ds) (SmtDef_body (?ds ! unat d))\<close>
      using 1(2) nd 1(3) by simp
    have tk: \<open>take (unat d) (take n ?ds) = take (unat d) ?ds\<close> \<open>take n ?ds ! unat d = ?ds ! unat d\<close>
      \<open>unat d < length (take n ?ds)\<close> using nd 1(3) by (simp_all add: min_def)
    show ?thesis using a b nd tk by simp
  qed
next
  case (2 p n op args)
  then show ?case by simp
qed auto

lemma tsize_le_size: \<open>tsize p \<le> smt_size p\<close>
proof -
  let ?ds = \<open>sdefs p\<close>
  have 1: \<open>sum_list (map (\<lambda>d. if dpar (?ds ! d) = [] then Suc (cnt p d (SmtDef_body (?ds ! d))) else 0) [0..<length ?ds]) \<le>
      sum_list (map (\<lambda>d. if dpar (?ds ! d) = [] then smt_nodes (take d ?ds) (SmtDef_body (?ds ! d)) else 0) [0..<length ?ds])\<close>
    by (rule sum_list_mono) (auto intro: cnt_le_nodes(1))
  have 2: \<open>sum_list (map (cnt p (length ?ds)) (sasserts p)) \<le> sum_list (map (smt_nodes ?ds) (sasserts p))\<close>
  proof (rule sum_list_mono)
    fix a show \<open>cnt p (length ?ds) a \<le> smt_nodes ?ds a\<close> using cnt_le_nodes(1)[of \<open>length ?ds\<close> p a] by simp
  qed
  show ?thesis using 1 2 by (simp add: tsize_def smt_size_def Let_def)
qed


subsection \<open>The cost of the translation of a term\<close>

lemma df_prefix: \<open>\<exists>e. Df = def_widths ws [] S' @ e \<Longrightarrow> S' = S1 @ E \<Longrightarrow> \<exists>e. Df = def_widths ws [] S1 @ e\<close>
  by (metis append.assoc def_widths_append' def_widths_prefix')

lemma df_width: \<open>\<exists>e. Df = def_widths ws [] S @ e \<Longrightarrow> wt ws (def_widths ws [] S) t \<Longrightarrow>
  width ws Df t = width ws (def_widths ws [] S) t\<close>
  using wt_width_eval_append[of ws \<open>def_widths ws [] S\<close> t \<open>replicate (length (def_widths ws [] S)) 0\<close>] by auto

lemma df_nth: \<open>\<exists>e. Df = def_widths ws [] S @ e \<Longrightarrow> k < length S \<Longrightarrow> Df ! k = def_widths ws [] S ! k\<close>
  by (auto simp: nth_append def_widths_length')

lemma ow_ref: \<open>ref_ok ws vs S k s v \<Longrightarrow> \<exists>e. Df = def_widths ws [] S @ e \<Longrightarrow>
  ow ws Df (tref k) = fw (sort_width_m s)\<close>
  by (auto simp: ref_ok_def tref_def ow_eqs unat_of_nat_eq nth_append def_widths_length')

lemma rng_self: \<open>rng fs ds ps t \<Longrightarrow> nr fs ds ps t\<close>
  by (cases t) (auto simp: rng_def)

text \<open>The width \<open>w\<close> of \<^const>\<open>smt_ncost\<close>: the largest width of a node and of its arguments, at
  least 1.\<close>
definition nw :: \<open>SmtFun list \<Rightarrow> SmtDef list \<Rightarrow> SmtSort list \<Rightarrow> SmtTerm \<Rightarrow> nat\<close> where
  \<open>nw fs ds ps u \<equiv> Max (insert 1 (smt_twidth fs ds ps ` set (u # smt_args u)))\<close>

lemma nw_ge: \<open>x \<in> set (u # smt_args u) \<Longrightarrow> smt_twidth fs ds ps x \<le> nw fs ds ps u\<close>
  unfolding nw_def by (rule Max_ge) auto

lemma nw_1: \<open>1 \<le> nw fs ds ps u\<close>
  unfolding nw_def by (rule Max_ge) auto

lemma nw_WB: \<open>\<forall>x \<in> set (u # smt_args u). smt_twidth fs ds ps x \<le> WB \<Longrightarrow> nw fs ds ps u \<le> WB\<close>
  unfolding nw_def by (subst Max_le_iff) (auto simp: WB_def)

lemma swm_nw: \<open>smt_tsort fs ds ps x = Some s \<Longrightarrow> x \<in> set (u # smt_args u) \<Longrightarrow> sort_width_m s \<le> nw fs ds ps u\<close>
  using nw_ge[of x u fs ds ps] nw_1[of fs ds ps u] by (cases s) (auto simp: smt_twidth_def)

lemma ncost_nw:
  \<open>\<not> smt_mul_div u \<Longrightarrow> \<not> smt_distinct u \<Longrightarrow> smt_ncost fs ds ps u = (1 + length (smt_args u)) * nw fs ds ps u\<close>
  by (simp add: smt_ncost_def nw_def Let_def)

lemma ncost_leaf: \<open>smt_args u = [] \<Longrightarrow> \<not> smt_mul_div u \<Longrightarrow> \<not> smt_distinct u \<Longrightarrow> smt_ncost fs ds ps u = nw fs ds ps u\<close>
  by (simp add: ncost_nw)

lemma ncost_app:
  \<open>smt_ncost fs ds ps (SmtTerm_App op args) =
     (1 + length (rvec_elems args)) * ucost op (length (rvec_elems args)) (nw fs ds ps (SmtTerm_App op args))\<close>
  by (simp add: smt_ncost_def nw_def Let_def ucost_def)

lemma leaf_bound: \<open>x \<le> nw fs ds ps u \<Longrightarrow> fw x + 1 \<le> cK * nw fs ds ps u\<close>
  using nw_1[of fs ds ps u] by (simp add: fw_def cK_def)

lemma tr_cost:
  shows \<open>tr_term_m p dm env n S t = (S', t') \<Longrightarrow> ctx_ok p I ws vs n dm S \<Longrightarrow>
     smt_tsort (sfuns p) (take n (sdefs p)) ps t = Some s \<Longrightarrow>
     \<forall>x \<in> set ps. frag_sort x \<Longrightarrow> length env = length ps \<Longrightarrow> length xs = length ps \<Longrightarrow>
     (\<forall>i < length ps. ref_ok ws vs S (env ! i) (ps ! i) (xs ! i)) \<Longrightarrow>
     defs_wt ws [] S \<Longrightarrow> length S' < 2 ^ 64 \<Longrightarrow> \<exists>e. Df = def_widths ws [] S' @ e \<Longrightarrow>
     (\<forall>d < length (sdefs p). rng (sfuns p) (take d (sdefs p))
        (dpar (sdefs p ! d)) (SmtDef_body (sdefs p ! d))) \<Longrightarrow>
     rng (sfuns p) (take n (sdefs p)) ps t \<Longrightarrow>
     sum_list (map (\<lambda>d. ow ws Df d + 1) (drop (length S) S')) + ow ws Df t' + 1 \<le>
       cK * smt_tcost (sfuns p) (take n (sdefs p)) ps t\<close>
    and \<open>tr_args_m p dm env n S ts = (S', ks) \<Longrightarrow> ctx_ok p I ws vs n dm S \<Longrightarrow>
     map (smt_tsort (sfuns p) (take n (sdefs p)) ps) ts = map Some ss \<Longrightarrow>
     \<forall>x \<in> set ps. frag_sort x \<Longrightarrow> length env = length ps \<Longrightarrow> length xs = length ps \<Longrightarrow>
     (\<forall>i < length ps. ref_ok ws vs S (env ! i) (ps ! i) (xs ! i)) \<Longrightarrow>
     defs_wt ws [] S \<Longrightarrow> length S' < 2 ^ 64 \<Longrightarrow> \<exists>e. Df = def_widths ws [] S' @ e \<Longrightarrow>
     (\<forall>d < length (sdefs p). rng (sfuns p) (take d (sdefs p))
        (dpar (sdefs p ! d)) (SmtDef_body (sdefs p ! d))) \<Longrightarrow>
     (\<forall>a \<in> set ts. rng (sfuns p) (take n (sdefs p)) ps a) \<Longrightarrow>
     sum_list (map (\<lambda>d. ow ws Df d + 1) (drop (length S) S')) \<le>
       cK * sum_list (map (smt_tcost (sfuns p) (take n (sdefs p)) ps) ts)\<close>
proof (induction p dm env n S t and p dm env n S ts arbitrary: S' t' ps s xs and S' ks ps ss xs
    rule: tr_term_m_tr_args_m.induct)
  case (1 p dm env n S b S' t' ps s xs)
  let ?u = \<open>SmtTerm_BoolConst b\<close>
  have res: \<open>S' = S\<close> \<open>t' = TermL_Const [b]\<close> using 1(1) by auto
  have \<open>ow ws Df t' + 1 \<le> cK * nw (sfuns p) (take n (sdefs p)) ps ?u\<close>
    using leaf_bound[of 1] nw_1 res by (simp add: ow_eqs)
  then show ?case using res by (simp add: ncost_leaf)
next
  case (2 p dm env n S bs S' t' ps s xs)
  let ?u = \<open>SmtTerm_BvConst bs\<close>
  have res: \<open>S' = S\<close> \<open>t' = TermL_Const (rvec_elems bs)\<close> using 2(1) by auto
  have \<open>sort_width_m s \<le> nw (sfuns p) (take n (sdefs p)) ps ?u\<close> using swm_nw[OF 2(3)] by simp
  moreover have \<open>sort_width_m s = length (rvec_elems bs)\<close> using 2(3) by (auto split: if_splits simp: unat_of_nat_eq)
  ultimately have \<open>ow ws Df t' + 1 \<le> cK * nw (sfuns p) (take n (sdefs p)) ps ?u\<close>
    using leaf_bound res by (simp add: ow_eqs)
  then show ?case using res by (simp add: ncost_leaf)
next
  case (3 p dm env n S k S' t' ps s xs)
  let ?u = \<open>SmtTerm_Param k\<close>
  then have k: \<open>unat k < length ps\<close> \<open>s = ps ! unat k\<close> by (auto split: if_splits)
  have r: \<open>ref_ok ws vs S (env ! unat k) s (xs ! unat k)\<close> using 3(7) k by simp
  have res: \<open>S' = S\<close> \<open>t' = tref (env ! unat k)\<close> using 3(1) by auto
  have Df3: \<open>\<exists>e. Df = def_widths ws [] S @ e\<close> using 3(10) res by simp
  have \<open>ow ws Df t' + 1 \<le> cK * nw (sfuns p) (take n (sdefs p)) ps ?u\<close>
    using ow_ref[OF r Df3] res leaf_bound swm_nw[OF 3(3)] by simp
  then show ?case using res by (simp add: ncost_leaf)
next
  case (4 p dm env n S i args S' t' ps s xs)
  let ?fs = \<open>sfuns p\<close> and ?u = \<open>SmtTerm_Fun i args\<close>
  have i: \<open>unat i < length ?fs\<close> \<open>s = SmtFun_ret (?fs ! unat i)\<close> using 4(3) by (auto split: if_splits)
  have wsd: \<open>ws = map (\<lambda>f. sort_width_m (SmtFun_ret f)) ?fs\<close> using 4(2) by (simp add: ctx_ok_def Let_def)
  have res: \<open>S' = S\<close> \<open>t' = TermL_Var i\<close> using 4(1) by auto
  have \<open>ow ws Df t' + 1 \<le> cK * nw ?fs (take n (sdefs p)) ps ?u\<close>
    using res wsd i leaf_bound swm_nw[OF 4(3)] by (simp add: ow_eqs)
  moreover have \<open>nw ?fs (take n (sdefs p)) ps ?u \<le> smt_ncost ?fs (take n (sdefs p)) ps ?u\<close> by (simp add: ncost_nw)
  ultimately show ?case using res by (simp add: order_trans[OF _ mult_le_mono2] trans_le_add1)
next
  case (5 p dm env n S d args S' t' ps s xs)
  let ?fs = \<open>sfuns p\<close> and ?ds = \<open>sdefs p\<close> and ?dv = \<open>smt_def_sems I (sdefs p)\<close>
  let ?u = \<open>SmtTerm_Def d args\<close>
  have d: \<open>unat d < length (take n ?ds)\<close> \<open>map (smt_tsort ?fs (take n ?ds) ps) (rvec_elems args) = map Some (dpar (?ds ! unat d))\<close>
    \<open>s = SmtDef_ret (?ds ! unat d)\<close> using 5(5) by (auto split: if_splits)
  have dn: \<open>unat d < n\<close> \<open>unat d < length ?ds\<close> using d(1) by auto
  have fr: \<open>smt_fragment p\<close> using 5(4) by (simp add: ctx_ok_def Let_def)
  have wfr: \<open>frag_sort (SmtDef_ret (?ds ! unat d))\<close> \<open>\<forall>x \<in> set (dpar (?ds ! unat d)). frag_sort x\<close>
    using ctx_ok_wf_sorts(2)[OF 5(4)] frag_of_wf[OF fr] dn(2) by (meson nth_mem)+
  have ra: \<open>\<forall>a \<in> set (rvec_elems args). rng ?fs (take n ?ds) ps a\<close> using 5(14) by (simp add: rng_simps)
  have T: \<open>smt_tcost ?fs (take n ?ds) ps ?u = smt_ncost ?fs (take n ?ds) ps ?u +
      sum_list (map (smt_tcost ?fs (take n ?ds) ps) (rvec_elems args)) +
      (if dpar (?ds ! unat d) \<noteq> [] then smt_tcost ?fs (take (unat d) ?ds) (dpar (?ds ! unat d)) (SmtDef_body (?ds ! unat d)) else 0)\<close>
    using dn by (simp add: min_def)
  show ?case
  proof (cases \<open>dpar (?ds ! unat d) = []\<close>)
    case True
    have res: \<open>S' = S\<close> \<open>t' = tref (dm ! unat d)\<close> using 5(3) True by auto
    have r: \<open>ref_ok ws vs S (dm ! unat d) (SmtDef_ret (?ds ! unat d)) ((?dv ! unat d) [])\<close>
      using 5(4) dn True unfolding ctx_ok_def Let_def by blast
    have Df5: \<open>\<exists>e. Df = def_widths ws [] S @ e\<close> using 5(12) res by simp
    have \<open>ow ws Df t' + 1 \<le> cK * nw ?fs (take n ?ds) ps ?u\<close>
      using ow_ref[OF r Df5] res d(3) leaf_bound swm_nw[OF 5(5)] by simp
    moreover have \<open>nw ?fs (take n ?ds) ps ?u \<le> smt_ncost ?fs (take n ?ds) ps ?u\<close> by (simp add: ncost_nw)
    ultimately have \<open>ow ws Df t' + 1 \<le> cK * smt_ncost ?fs (take n ?ds) ps ?u\<close>
      using mult_le_mono2[of _ _ cK] by (meson order_trans)
    then show ?thesis using res T by (simp add: add_mult_distrib2 trans_le_add1)
  next
    case False
    obtain S1 ks1 where r: \<open>tr_args_m p dm env n S (rvec_elems args) = (S1, ks1)\<close> by (cases \<open>tr_args_m p dm env n S (rvec_elems args)\<close>)
    have res: \<open>tr_term_m p dm ks1 (unat d) S1 (SmtDef_body (?ds ! unat d)) = (S', t')\<close>
      using 5(3) False dn(1) r by (simp add: Let_def)
    obtain E2 where E2: \<open>S' = S1 @ E2\<close> using tr_prefix(1)[OF res] by blast
    have len1: \<open>length S1 < 2 ^ 64\<close> using 5(11) E2 by simp
    let ?xs' = \<open>map (smt_eval I ?dv xs) (rvec_elems args)\<close>
    have A: \<open>(\<exists>E. S1 = S @ E) \<and> defs_wt ws [] S1 \<and> length ks1 = length (rvec_elems args) \<and>
        (\<forall>i < length (rvec_elems args). ref_ok ws vs S1 (ks1 ! i) (dpar (?ds ! unat d) ! i) (smt_eval I ?dv xs (rvec_elems args ! i)))\<close>
      using tr_term_args_correct(2)[OF r 5(4) d(2) 5(6,7,8,9,10) len1] .
    obtain E1 where E1: \<open>S1 = S @ E1\<close> using A by blast
    have la: \<open>length (rvec_elems args) = length (dpar (?ds ! unat d))\<close> using d(2) by (metis length_map)
    have ctx1: \<open>ctx_ok p I ws vs (unat d) dm S1\<close> using ctx_ok_mono[OF ctx_ok_ext[OF 5(4), of E1]] E1 dn(1) by simp
    have tb: \<open>smt_tsort ?fs (take (unat d) ?ds) (dpar (?ds ! unat d)) (SmtDef_body (?ds ! unat d)) = Some (SmtDef_ret (?ds ! unat d))\<close>
      using ctx_ok_wf_sorts(3)[OF 5(4)] dn(2) by blast
    have Df1: \<open>\<exists>e. Df = def_widths ws [] S1 @ e\<close> using df_prefix[OF 5(12) E2] .
    have rb: \<open>rng ?fs (take (unat d) ?ds) (dpar (?ds ! unat d)) (SmtDef_body (?ds ! unat d))\<close>
      using 5(13) dn(2) by blast
    have IA: \<open>sum_list (map (\<lambda>d. ow ws Df d + 1) (drop (length S) S1)) \<le>
        cK * sum_list (map (smt_tcost ?fs (take n ?ds) ps) (rvec_elems args))\<close>
      using 5(1)[OF False dn(1) r 5(4) d(2) 5(6,7,8,9,10) len1 Df1 5(13) ra] .
    have IB: \<open>sum_list (map (\<lambda>d. ow ws Df d + 1) (drop (length S1) S')) + ow ws Df t' + 1 \<le>
        cK * smt_tcost ?fs (take (unat d) ?ds) (dpar (?ds ! unat d)) (SmtDef_body (?ds ! unat d))\<close>
      using 5(2)[of \<open>(S1, ks1)\<close> S' t' \<open>dpar (?ds ! unat d)\<close> \<open>SmtDef_ret (?ds ! unat d)\<close> ?xs'] False dn(1) r res ctx1 tb wfr(2)
        A la 5(11,12,13) rb by auto
    have sp: \<open>drop (length S) S' = drop (length S) S1 @ drop (length S1) S'\<close> using E1 E2 by simp
    show ?thesis using IA IB sp T False by (simp add: algebra_simps)
  qed
next
  case (6 p dm env n S op args S' t' ps s xs)
  let ?fs = \<open>sfuns p\<close> and ?ds = \<open>sdefs p\<close> and ?dv = \<open>smt_def_sems I (sdefs p)\<close>
  let ?u = \<open>SmtTerm_App op args\<close> and ?as = \<open>rvec_elems args\<close>
  let ?w = \<open>nw ?fs (take n ?ds) ps ?u\<close>
  let ?ss = \<open>map (the \<circ> smt_tsort ?fs (take n ?ds) ps) ?as\<close>
  obtain S1 ks1 where r: \<open>tr_args_m p dm env n S ?as = (S1, ks1)\<close> by (cases \<open>tr_args_m p dm env n S ?as\<close>)
  have res: \<open>S' = S1\<close> \<open>t' = tr_app_m op ks1\<close> using 6(2) r by (auto simp: Let_def)
  have o: \<open>None \<notin> set (map (smt_tsort ?fs (take n ?ds) ps) ?as)\<close> \<open>smt_op_sort op ?ss = Some s\<close>
    using 6(4) by (auto split: if_splits)
  have m: \<open>map (smt_tsort ?fs (take n ?ds) ps) ?as = map Some ?ss\<close> using o(1) by (induction ?as) auto
  have A: \<open>(\<exists>E. S1 = S @ E) \<and> defs_wt ws [] S1 \<and> length ks1 = length ?as \<and>
      (\<forall>i < length ?as. ref_ok ws vs S1 (ks1 ! i) (?ss ! i) (smt_eval I ?dv xs (?as ! i)))\<close>
    using tr_term_args_correct(2)[OF r 6(3) m 6(5,6,7,8,9)] res 6(10) by simp
  have C: \<open>(\<exists>E. S' = S @ E) \<and> defs_wt ws [] S' \<and> wt ws (def_widths ws [] S') t' \<and>
     width ws (def_widths ws [] S') t' = sort_width_m s \<and>
     eval ws (def_widths ws [] S') vs (def_values ws [] vs [] S') t' = enc (smt_eval I ?dv xs ?u)\<close>
    using tr_term_args_correct(1)[OF 6(2,3,4,5,6,7,8,9,10)] .
  have wd: \<open>width ws Df t' = sort_width_m s\<close> using df_width[OF 6(11)] C by simp
  have len6: \<open>length S1 < 2 ^ 64\<close> using 6(10) res by simp
  have Df6: \<open>\<exists>e. Df = def_widths ws [] S1 @ e\<close> using 6(11) res by simp
  have nrn: \<open>nr ?fs (take n ?ds) ps ?u\<close> and ra: \<open>\<forall>a \<in> set ?as. rng ?fs (take n ?ds) ps a\<close>
    using 6(13) by (simp_all add: rng_simps)
  have IA: \<open>sum_list (map (\<lambda>d. ow ws Df d + 1) (drop (length S) S1)) \<le>
      cK * sum_list (map (smt_tcost ?fs (take n ?ds) ps) ?as)\<close>
    using 6(1)[OF r 6(3) m 6(5,6,7,8,9) len6 Df6 6(12) ra] .
  have lk: \<open>length ks1 = length ?ss\<close> using A by simp
  have kw: \<open>\<forall>k \<in> set ks1. k < 2 ^ 64\<close> using A by (auto simp: in_set_conv_nth ref_ok_def)
  have Dk: \<open>Df ! (ks1 ! i) = sort_width_m (?ss ! i)\<close> if \<open>i < length ?as\<close> for i
  proof -
    have \<open>ref_ok ws vs S1 (ks1 ! i) (?ss ! i) (smt_eval I ?dv xs (?as ! i))\<close> using A that by blast
    then show ?thesis using df_nth[OF 6(11)] res by (simp add: ref_ok_def)
  qed
  have ts: \<open>smt_tsort ?fs (take n ?ds) ps (?as ! i) = Some (?ss ! i)\<close> if \<open>i < length ?as\<close> for i
    using m that by (metis length_map nth_map)
  have kW: \<open>\<forall>k \<in> set ks1. k < 2 ^ 64 \<and> Df ! k \<le> ?w\<close>
  proof
    fix k assume \<open>k \<in> set ks1\<close>
    then obtain i where i: \<open>i < length ?as\<close> \<open>k = ks1 ! i\<close> using A by (auto simp: in_set_conv_nth)
    have \<open>sort_width_m (?ss ! i) \<le> ?w\<close> using swm_nw[OF ts[OF i(1)]] i(1) by simp
    then show \<open>k < 2 ^ 64 \<and> Df ! k \<le> ?w\<close> using Dk[OF i(1)] i kw \<open>k \<in> set ks1\<close> by simp
  qed
  have wt': \<open>width ws Df (tr_app_m op ks1) \<le> ?w\<close> using wd res swm_nw[OF 6(4)] by simp
  have wW: \<open>?w \<le> WB\<close>
  proof (rule nw_WB, intro ballI)
    fix x assume \<open>x \<in> set (?u # smt_args ?u)\<close>
    then have \<open>nr ?fs (take n ?ds) ps x\<close> using nrn ra rng_self by auto
    then show \<open>smt_twidth ?fs (take n ?ds) ps x \<le> WB\<close> by (simp add: nr_def)
  qed
  have AC: \<open>ow ws Df (tr_app_m op ks1) + 1 \<le> cK * ((1 + length ks1) * ucost op (length ks1) ?w)\<close>
    by (rule app_cost[OF _ kW wt' nw_1 wW]) (use sop_ar_sort[OF o(2)] lk in simp)
  have N: \<open>smt_ncost ?fs (take n ?ds) ps ?u = (1 + length ks1) * ucost op (length ks1) ?w\<close>
    using lk by (simp add: ncost_app)
  show ?case using IA AC res A N by (simp add: algebra_simps)
next
  case (7 p dm env n S S' ks ps ss xs)
  then show ?case by simp
next
  case (8 p dm env n S a rest S' ks ps ss xs)
  obtain S1 t1 where r1: \<open>tr_term_m p dm env n S a = (S1, t1)\<close> by (cases \<open>tr_term_m p dm env n S a\<close>)
  obtain S2 ks2 where r2: \<open>tr_args_m p dm env n (S1 @ [t1]) rest = (S2, ks2)\<close>
    by (cases \<open>tr_args_m p dm env n (S1 @ [t1]) rest\<close>)
  have res: \<open>S' = S2\<close> \<open>ks = length S1 # ks2\<close> using 8(3) r1 r2 by (auto simp: Let_def)
  obtain s0 ss' where ss: \<open>ss = s0 # ss'\<close> \<open>smt_tsort (sfuns p) (take n (sdefs p)) ps a = Some s0\<close>
    \<open>map (smt_tsort (sfuns p) (take n (sdefs p)) ps) rest = map Some ss'\<close>
    using 8(5) by (cases ss) auto
  obtain E2 where E2: \<open>S2 = (S1 @ [t1]) @ E2\<close> using tr_prefix(2)[OF r2] by blast
  have len1: \<open>length S1 < 2 ^ 64\<close> using 8(11) res E2 by simp
  have A: \<open>(\<exists>E. S1 = S @ E) \<and> defs_wt ws [] S1 \<and> wt ws (def_widths ws [] S1) t1 \<and>
      width ws (def_widths ws [] S1) t1 = sort_width_m s0 \<and>
      eval ws (def_widths ws [] S1) vs (def_values ws [] vs [] S1) t1 =
        enc (smt_eval I (smt_def_sems I (sdefs p)) xs a)\<close>
    using tr_term_args_correct(1)[OF r1 8(4) ss(2) 8(6,7,8,9,10) len1] .
  have hs: \<open>smt_has_sort s0 (smt_eval I (smt_def_sems I (sdefs p)) xs a)\<close>
    using val_sort[OF 8(4) ss(2)] 8(6) la2_of_refs[OF 8(8,9)] wf_of_frag by blast
  have refa: \<open>ref_ok ws vs (S1 @ [t1]) (length S1) s0 (smt_eval I (smt_def_sems I (sdefs p)) xs a)\<close>
    using A hs len1 by (simp add: ref_ok_def def_snoc)
  have dw1: \<open>defs_wt ws [] (S1 @ [t1])\<close> using A by (simp add: def_snoc)
  obtain E1 where E1: \<open>S1 = S @ E1\<close> using A by blast
  have ctx1: \<open>ctx_ok p I ws vs n dm (S1 @ [t1])\<close> using ctx_ok_ext[OF 8(4), of \<open>E1 @ [t1]\<close>] E1 by simp
  have env1: \<open>\<forall>i < length ps. ref_ok ws vs (S1 @ [t1]) (env ! i) (ps ! i) (xs ! i)\<close>
    using 8(9) ref_ok_ext[of ws vs S _ _ _ \<open>E1 @ [t1]\<close>] E1 by simp
  have Df1: \<open>\<exists>e. Df = def_widths ws [] S1 @ e\<close> using df_prefix[OF 8(12)] res E2 by simp
  have ra: \<open>rng (sfuns p) (take n (sdefs p)) ps a\<close>
    \<open>\<forall>a \<in> set rest. rng (sfuns p) (take n (sdefs p)) ps a\<close> using 8(14) by simp_all
  have IA: \<open>sum_list (map (\<lambda>d. ow ws Df d + 1) (drop (length S) S1)) + ow ws Df t1 + 1 \<le>
      cK * smt_tcost (sfuns p) (take n (sdefs p)) ps a\<close>
    using 8(1)[OF r1 8(4) ss(2) 8(6,7,8,9,10) len1 Df1 8(13) ra(1)] .
  have IB: \<open>sum_list (map (\<lambda>d. ow ws Df d + 1) (drop (length (S1 @ [t1])) S2)) \<le>
      cK * sum_list (map (smt_tcost (sfuns p) (take n (sdefs p)) ps) rest)\<close>
    using 8(2)[of \<open>(S1, t1)\<close> S2 ks2 ps ss' xs] r1 r2 ctx1 ss(3) 8(6,7,8) env1 dw1 res 8(11,12,13) ra(2) by auto
  have sp: \<open>drop (length S) S2 = drop (length S) S1 @ [t1] @ drop (length (S1 @ [t1])) S2\<close> using E1 E2 by simp
  show ?case using IA IB sp res by (simp add: algebra_simps)
qed

subsection \<open>The whole translation\<close>

definition dflt :: \<open>SmtSort \<Rightarrow> sval\<close> where
  \<open>dflt s \<equiv> case s of SmtSort_Bool \<Rightarrow> VBool False | SmtSort_BitVec w \<Rightarrow> VBv (unat w) 0 | SmtSort_Uninterpreted u \<Rightarrow> VElem 0\<close>

lemma dflt_sort: \<open>smt_has_sort s (dflt s)\<close>
  by (cases s) (simp_all add: dflt_def)

text \<open>The cost of the bodies of the definitions without parameters.\<close>
definition dcost :: \<open>SmtProblem \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>dcost p k \<equiv> sum_list (map (\<lambda>d. if dpar (sdefs p ! d) = []
     then smt_tcost (sfuns p) (take d (sdefs p)) [] (SmtDef_body (sdefs p ! d)) else 0) [0..<k])\<close>

lemma defs_cost:
  assumes c0: \<open>ctx_ok p I ws vs 0 [] []\<close> and len: \<open>length (fst (tr_defs_m p)) < 2 ^ 64\<close>
    and Df: \<open>\<exists>e. Df = def_widths ws [] (fst (tr_defs_m p)) @ e\<close>
    and RD: \<open>\<forall>d < length (sdefs p). rng (sfuns p) (take d (sdefs p))
        (dpar (sdefs p ! d)) (SmtDef_body (sdefs p ! d))\<close>
  shows \<open>k \<le> length (sdefs p) \<Longrightarrow>
    sum_list (map (\<lambda>d. ow ws Df d + 1) (fst (foldl (tr_defs_step p) ([], []) [0..<k]))) \<le> cK * dcost p k\<close>
proof (induction k)
  case 0
  then show ?case by (simp add: dcost_def)
next
  case (Suc k)
  let ?ds = \<open>sdefs p\<close> and ?fs = \<open>sfuns p\<close>
  obtain S dm where st: \<open>foldl (tr_defs_step p) ([], []) [0..<k] = (S, dm)\<close>
    by (cases \<open>foldl (tr_defs_step p) ([], []) [0..<k]\<close>)
  have kd: \<open>k < length ?ds\<close> using Suc.prems by simp
  have IH: \<open>sum_list (map (\<lambda>d. ow ws Df d + 1) S) \<le> cK * dcost p k\<close> using Suc kd st by simp
  have C: \<open>ctx_ok p I ws vs k dm S\<close> \<open>defs_wt ws [] S\<close> using tr_defs_correct[OF c0 _ len, of k] kd st by auto
  have un: \<open>foldl (tr_defs_step p) ([], []) [0..<Suc k] = tr_defs_step p (S, dm) k\<close> using st by simp
  have fin: \<open>\<exists>E. fst (tr_defs_m p) = fst (tr_defs_step p (S, dm) k) @ E\<close>
  proof -
    have \<open>[0..<length ?ds] = [0..<Suc k] @ [Suc k..<length ?ds]\<close> using kd by (metis Suc_leI le_add_diff_inverse upt_add_eq_append zero_le)
    then have \<open>tr_defs_m p = foldl (tr_defs_step p) (tr_defs_step p (S, dm) k) [Suc k..<length ?ds]\<close>
      using un by (simp add: tr_defs_m_step)
    then show ?thesis using tr_defs_prefix[of p \<open>fst (tr_defs_step p (S, dm) k)\<close> \<open>snd (tr_defs_step p (S, dm) k)\<close>] by simp
  qed
  have dn: \<open>dcost p (Suc k) = dcost p k +
      (if dpar (?ds ! k) = [] then smt_tcost (sfuns p) (take k ?ds) [] (SmtDef_body (?ds ! k)) else 0)\<close>
    by (simp add: dcost_def)
  show ?case
  proof (cases \<open>dpar (?ds ! k) = []\<close>)
    case True
    obtain S1 t1 where r: \<open>tr_term_m p dm [] k S (SmtDef_body (?ds ! k)) = (S1, t1)\<close>
      by (cases \<open>tr_term_m p dm [] k S (SmtDef_body (?ds ! k))\<close>)
    have stp: \<open>tr_defs_step p (S, dm) k = (S1 @ [t1], dm @ [length S1])\<close> using True r by (simp add: tr_defs_step_def)
    obtain E where E: \<open>fst (tr_defs_m p) = S1 @ ([t1] @ E)\<close> using fin stp by auto
    have len1: \<open>length S1 < 2 ^ 64\<close> using E len by simp
    have tb: \<open>smt_tsort ?fs (take k ?ds) [] (SmtDef_body (?ds ! k)) = Some (SmtDef_ret (?ds ! k))\<close>
      using ctx_ok_wf_sorts(3)[OF C(1)] kd True by metis
    have Df1: \<open>\<exists>e. Df = def_widths ws [] S1 @ e\<close> using df_prefix[OF Df E] .
    have rb: \<open>rng ?fs (take k ?ds) [] (SmtDef_body (?ds ! k))\<close> using RD kd True by metis
    have W: \<open>sum_list (map (\<lambda>d. ow ws Df d + 1) (drop (length S) S1)) + ow ws Df t1 + 1 \<le>
        cK * smt_tcost (sfuns p) (take k ?ds) [] (SmtDef_body (?ds ! k))\<close>
      using tr_cost(1)[where xs = \<open>[]\<close>, OF r C(1) tb _ _ _ _ C(2) len1 Df1 RD rb] by simp
    obtain E1 where E1: \<open>S1 = S @ E1\<close> using tr_prefix(1)[OF r] by blast
    let ?f = \<open>\<lambda>d. ow ws Df d + 1\<close>
    have e: \<open>sum_list (map ?f (fst (foldl (tr_defs_step p) ([], []) [0..<Suc k]))) =
        sum_list (map ?f S) + (sum_list (map ?f (drop (length S) S1)) + (ow ws Df t1 + 1))\<close>
      using un stp E1 by simp
    have n: \<open>dcost p (Suc k) = dcost p k + smt_tcost (sfuns p) (take k ?ds) [] (SmtDef_body (?ds ! k))\<close> using dn True by simp
    have m: \<open>cK * dcost p (Suc k) = cK * dcost p k + cK * smt_tcost (sfuns p) (take k ?ds) [] (SmtDef_body (?ds ! k))\<close>
      unfolding n by (simp add: algebra_simps)
    show ?thesis unfolding e m using IH W by linarith
  next
    case False
    have stp: \<open>tr_defs_step p (S, dm) k = (S, dm @ [0])\<close> using False by (simp add: tr_defs_step_def)
    show ?thesis using IH un stp False dn by simp
  qed
qed

lemma asserts_cost:
  assumes \<open>ctx_ok p I ws vs (length (sdefs p)) dm S\<close> \<open>defs_wt ws [] S\<close>
    \<open>\<forall>a \<in> set ass. smt_tsort (sfuns p) (sdefs p) [] a = Some SmtSort_Bool\<close>
    \<open>foldl (tr_asserts_step p dm) (S, acc) ass = (S', acc')\<close> \<open>length S' < 2 ^ 64\<close>
    \<open>\<exists>e. Df = def_widths ws [] S' @ e\<close>
    \<open>\<forall>d < length (sdefs p). rng (sfuns p) (take d (sdefs p))
        (dpar (sdefs p ! d)) (SmtDef_body (sdefs p ! d))\<close>
    \<open>\<forall>a \<in> set ass. rng (sfuns p) (sdefs p) [] a\<close>
  shows \<open>sum_list (map (\<lambda>d. ow ws Df d + 1) S') + sum_list (map (ow ws Df) acc') \<le>
    sum_list (map (\<lambda>d. ow ws Df d + 1) S) + sum_list (map (ow ws Df) acc) +
    cK * sum_list (map (smt_tcost (sfuns p) (sdefs p) []) ass)\<close>
  using assms
proof (induction ass arbitrary: S acc)
  case Nil
  then show ?case by simp
next
  case (Cons a ass)
  obtain S1 t1 where r: \<open>tr_term_m p dm [] (length (sdefs p)) S a = (S1, t1)\<close>
    by (cases \<open>tr_term_m p dm [] (length (sdefs p)) S a\<close>)
  have f: \<open>foldl (tr_asserts_step p dm) (S1, acc @ [t1]) ass = (S', acc')\<close>
    using Cons.prems(4) r by (simp add: tr_asserts_step_def)
  obtain E1 where E1: \<open>S1 = S @ E1\<close> using tr_prefix(1)[OF r] by blast
  have ta: \<open>smt_tsort (sfuns p) (take (length (sdefs p)) (sdefs p)) [] a = Some SmtSort_Bool\<close>
    using Cons.prems(3) by simp
  obtain E2 where E2: \<open>S' = S1 @ E2\<close> using tr_prefix_asserts[OF f] by blast
  have len1: \<open>length S1 < 2 ^ 64\<close> using E2 Cons.prems(5) by simp
  have A: \<open>defs_wt ws [] S1\<close>
    using tr_term_args_correct(1)[OF r Cons.prems(1) ta, of \<open>[]\<close>] Cons.prems(2) len1 by simp
  have ctx1: \<open>ctx_ok p I ws vs (length (sdefs p)) dm S1\<close> using ctx_ok_ext[OF Cons.prems(1)] E1 by simp
  have Df1: \<open>\<exists>e. Df = def_widths ws [] S1 @ e\<close> using df_prefix[OF Cons.prems(6) E2] .
  have ra: \<open>rng (sfuns p) (take (length (sdefs p)) (sdefs p)) [] a\<close>
    using Cons.prems(8) by simp
  have W: \<open>sum_list (map (\<lambda>d. ow ws Df d + 1) (drop (length S) S1)) + ow ws Df t1 + 1 \<le>
      cK * smt_tcost (sfuns p) (take (length (sdefs p)) (sdefs p)) [] a\<close>
    using tr_cost(1)[where xs = \<open>[]\<close>, OF r Cons.prems(1) ta _ _ _ _ Cons.prems(2) len1 Df1 Cons.prems(7) ra] by simp
  have IH: \<open>sum_list (map (\<lambda>d. ow ws Df d + 1) S') + sum_list (map (ow ws Df) acc') \<le>
      sum_list (map (\<lambda>d. ow ws Df d + 1) S1) + sum_list (map (ow ws Df) (acc @ [t1])) +
      cK * sum_list (map (smt_tcost (sfuns p) (sdefs p) []) ass)\<close>
    using Cons.IH[OF ctx1 A _ f Cons.prems(5,6,7)] Cons.prems(3,8) by simp
  let ?f = \<open>\<lambda>d. ow ws Df d + 1\<close>
  have e1: \<open>sum_list (map ?f S1) = sum_list (map ?f S) + sum_list (map ?f (drop (length S) S1))\<close> using E1 by simp
  have e2: \<open>sum_list (map (ow ws Df) (acc @ [t1])) = sum_list (map (ow ws Df) acc) + ow ws Df t1\<close> by simp
  have e3: \<open>cK * sum_list (map (smt_tcost (sfuns p) (sdefs p) []) (a # ass)) =
      cK * smt_tcost (sfuns p) (sdefs p) [] a + cK * sum_list (map (smt_tcost (sfuns p) (sdefs p) []) ass)\<close>
    by (simp add: algebra_simps)
  have W': \<open>sum_list (map ?f (drop (length S) S1)) + ow ws Df t1 + 1 \<le> cK * smt_tcost (sfuns p) (sdefs p) [] a\<close>
    using W by simp
  show ?case unfolding e3 using IH W' e1 e2 by linarith
qed

lemma tr_asserts_len: \<open>length (snd (foldl (tr_asserts_step p dm) (S, acc) ass)) = length acc + length ass\<close>
  by (induction ass arbitrary: S acc) (simp_all add: tr_asserts_step_def Let_def)

lemma sum_ow1: \<open>sum_list (map (\<lambda>d. f d + 1) xs) = sum_list (map f xs) + length xs\<close> for f :: \<open>'a \<Rightarrow> nat\<close>
  by (induction xs) auto

lemma final_arith:
  assumes \<open>X \<le> 1 + F * WB + F + A + cK * N\<close> \<open>F + A \<le> Z\<close> \<open>Z \<le> 2 ^ 30\<close> \<open>N \<le> 2 ^ 43\<close>
  shows \<open>4 * X < 2 ^ 56\<close>
proof -
  have a: \<open>F * WB \<le> Z * WB\<close> using assms(2) by simp
  have b: \<open>Z * WB \<le> 2 ^ 30 * WB\<close> using assms(3) by simp
  have c: \<open>cK * N \<le> cK * 2 ^ 43\<close> using assms(4) by simp
  have \<open>X \<le> 1 + 2 ^ 30 * WB + 2 ^ 30 + cK * 2 ^ 43\<close> using assms(1,2,3) a b c by linarith
  then show ?thesis by (simp add: WB_def cK_def)
qed

theorem tr_size_bound:
  assumes \<open>smt_wf p\<close> \<open>smt_fragment p\<close> \<open>smt_in_range p\<close>
  shows \<open>tsize p < 2 ^ 56\<close> and \<open>sizes_ok (tr_problem_m p)\<close>
proof -
  let ?fs = \<open>sfuns p\<close> and ?ds = \<open>sdefs p\<close> and ?as = \<open>sasserts p\<close>
  note RR = in_range_rng[OF assms(3)]
  show T: \<open>tsize p < 2 ^ 56\<close> using tsize_le_size[of p] RR(4) by simp
  define I0 where \<open>I0 = (\<lambda>f (xs :: sval list). dflt (SmtFun_ret (?fs ! f)))\<close>
  define vs0 where \<open>vs0 = map (\<lambda>f. enc (I0 f [])) [0..<length ?fs]\<close>
  define ws0 where \<open>ws0 = map (\<lambda>f. sort_width_m (SmtFun_ret f)) ?fs\<close>
  have isd: \<open>interp_sound ?fs I0\<close> by (simp add: interp_sound_def I0_def dflt_sort)
  have lvs: \<open>length vs0 = length ?fs\<close> \<open>\<forall>f < length ?fs. vs0 ! f = enc (I0 f [])\<close> by (simp_all add: vs0_def)
  have lenT: \<open>length (fst (tr_asserts_m p (tr_defs_m p))) < 2 ^ 64\<close> using T tsize_length[of p] by simp
  have c0: \<open>ctx_ok p I0 ws0 vs0 0 [] []\<close> using assms(1,2) isd lvs by (simp add: ctx_ok_def Let_def ws0_def)
  have vw: \<open>var_widths (tr_problem_m p) = ws0\<close>
    using tr_problem_sem[OF assms(1,2) isd lvs lenT] by (simp add: ws0_def)
  obtain S0 dm where d: \<open>tr_defs_m p = (S0, dm)\<close> by (cases \<open>tr_defs_m p\<close>)
  obtain S' ts where a: \<open>tr_asserts_m p (S0, dm) = (S', ts)\<close> by (cases \<open>tr_asserts_m p (S0, dm)\<close>)
  have af: \<open>foldl (tr_asserts_step p dm) (S0, []) ?as = (S', ts)\<close> using a by (simp add: tr_asserts_m_step)
  have lenS': \<open>length S' < 2 ^ 64\<close> using lenT d a by simp
  obtain E where E: \<open>S' = S0 @ E\<close> using tr_prefix_asserts[OF af] by blast
  have len0: \<open>length (fst (tr_defs_m p)) < 2 ^ 64\<close> using lenS' E d by simp
  have D: \<open>ctx_ok p I0 ws0 vs0 (length ?ds) dm S0 \<and> defs_wt ws0 [] S0\<close>
    using tr_defs_correct[OF c0 le_refl len0] d by (simp add: tr_defs_m_step)
  define Df where \<open>Df = def_widths ws0 [] S'\<close>
  have Dfa: \<open>\<exists>e. Df = def_widths ws0 [] S' @ e\<close> by (simp add: Df_def)
  have Df0: \<open>\<exists>e. Df = def_widths ws0 [] (fst (tr_defs_m p)) @ e\<close> using df_prefix[OF Dfa E] d by simp
  have wsA: \<open>\<forall>a \<in> set ?as. smt_tsort ?fs ?ds [] a = Some SmtSort_Bool\<close> using assms(1) by (simp add: smt_wf_def Let_def)
  have AW: \<open>sum_list (map (\<lambda>d. ow ws0 Df d + 1) S') + sum_list (map (ow ws0 Df) ts) \<le>
      sum_list (map (\<lambda>d. ow ws0 Df d + 1) S0) + cK * sum_list (map (smt_tcost ?fs ?ds []) ?as)\<close>
    using asserts_cost[OF conjunct1[OF D] conjunct2[OF D] wsA af lenS' Dfa RR(1) RR(2)] by simp
  have DW: \<open>sum_list (map (\<lambda>d. ow ws0 Df d + 1) S0) \<le> cK * dcost p (length ?ds)\<close>
    using defs_cost[OF c0 len0 Df0 RR(1), of \<open>length ?ds\<close>] d by (simp add: tr_defs_m_step)
  have q: \<open>ProblemL_defs (tr_problem_m p) = S'\<close> \<open>ProblemL_asserts (tr_problem_m p) = ts\<close>
    by (simp_all add: tr_problem_m_def d a Let_def)
  have lts: \<open>length ts = length ?as\<close> using tr_asserts_len[of p dm S0 \<open>[]\<close> ?as] af by simp
  have mw: \<open>map unat (ProblemL_widths (tr_problem_m p)) = ws0\<close> using vw by (simp add: var_widths_def)
  have lw: \<open>length (ProblemL_widths (tr_problem_m p)) = length ws0\<close> by (metis length_map mw)
  have sw: \<open>sum_list (map unat (ProblemL_widths (tr_problem_m p))) = sum_list ws0\<close> using mw by simp
  have sws: \<open>sum_list ws0 \<le> length ?fs * WB\<close>
  proof -
    have \<open>sum_list ws0 \<le> sum_list (map (\<lambda>f. WB) ?fs)\<close>
      unfolding ws0_def by (rule sum_list_mono) (use RR(3) sw_le in blast)
    then show ?thesis by (simp add: sum_list_triv)
  qed
  have lws: \<open>length ws0 = length ?fs\<close> by (simp add: ws0_def)
  have ovf: \<open>ovf_bound (tr_problem_m p) = 4 * (base (tr_problem_m p) + sum_list (map (ow ws0 Df) S') + sum_list (map (ow ws0 Df) ts))\<close>
    using ovf_bound_eq[of \<open>tr_problem_m p\<close>] mw q by (simp add: DSq_def Df_def)
  have bs: \<open>base (tr_problem_m p) = Suc (sum_list ws0 + length ws0 + length S' + length ts)\<close>
    using q lw sw by (simp add: base_def)
  have X: \<open>base (tr_problem_m p) + sum_list (map (ow ws0 Df) S') + sum_list (map (ow ws0 Df) ts) \<le>
      1 + length ?fs * WB + length ?fs + length ?as + cK * (dcost p (length ?ds) + sum_list (map (smt_tcost ?fs ?ds []) ?as))\<close>
  proof -
    have \<open>sum_list (map (\<lambda>d. ow ws0 Df d + 1) S') = sum_list (map (ow ws0 Df) S') + length S'\<close> by (rule sum_ow1)
    moreover have \<open>cK * (dcost p (length ?ds) + sum_list (map (smt_tcost ?fs ?ds []) ?as)) =
        cK * dcost p (length ?ds) + cK * sum_list (map (smt_tcost ?fs ?ds []) ?as)\<close> by (simp add: algebra_simps)
    ultimately show ?thesis using bs AW DW sws lws lts by linarith
  qed
  have Z: \<open>length ?fs + length ?as \<le> smt_size p\<close> by (simp add: smt_size_def Let_def)
  have N: \<open>dcost p (length ?ds) + sum_list (map (smt_tcost ?fs ?ds []) ?as) = smt_cost p\<close>
    by (simp add: smt_cost_def dcost_def Let_def)
  show \<open>sizes_ok (tr_problem_m p)\<close>
    unfolding sizes_ok_def ovf using final_arith[OF X[unfolded N] Z RR(4) RR(5)] .
qed


end
