theory BVSmt_Proof
  imports BVSmt_Refine BVSmt_Encode BVSmt_Dpll BVSmt_Bound BVSmt_LowerRefine BVSmt_LowerBound
begin

section \<open>Bounds relating the size of a term to its weight\<close>

text \<open>The recursion depth \<open>Suc (size t)\<close> and the width of any subterm are bounded by the weight of
  the term, hence by \<^const>\<open>size_bound\<close>.\<close>
lemma size_le_len_sub: \<open>Suc (size t) \<le> length (subterms t)\<close>
  by (induction t) auto

lemma len_le_cubesum: \<open>length xs \<le> sum_list (map (\<lambda>u. (width ws ds u + 1) ^ 3) xs)\<close>
proof (induction xs)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  show ?case using add_le_mono[OF cube1[of \<open>width ws ds x\<close>] Cons.IH] by simp
qed

lemma len_sub_le_tw: \<open>length (subterms t) \<le> term_weight ws ds t\<close>
  using len_le_cubesum[of \<open>subterms t\<close>] by (simp add: term_weight_def)

lemma size_le_tw: \<open>Suc (size t) \<le> term_weight ws ds t\<close>
  using size_le_len_sub[of t] len_sub_le_tw[of t ws ds] by simp

lemma width_le_tw:
  assumes \<open>u \<in> set (subterms t)\<close>
  shows \<open>width ws ds u \<le> term_weight ws ds t\<close>
proof -
  have \<open>width ws ds u \<le> (width ws ds u + 1) ^ 3\<close>
    using power_increasing[of 1 3 \<open>width ws ds u + 1\<close>] by simp
  also have \<open>(width ws ds u + 1) ^ 3 \<le> term_weight ws ds t\<close>
    unfolding term_weight_def using assms by (intro member_le_sum_list; simp)
  finally show ?thesis .
qed

section \<open>A length bound on the rewriting, free of \<open>bnd\<close>\<close>

text \<open>\<^verbatim>\<open>lower_m_cost\<close> assumes \<^const>\<open>bnd\<close> of its result; to establish \<^const>\<open>bnd\<close> in the first
  place, this purely structural bound counts the definitions the rewriting adds, with no
  overflow assumption.\<close>

lemma lower_bin_m_len3: \<open>length (fst (fst (lower_bin_m L op ka kb))) \<le> length (fst L) + 3\<close>
  by (cases op) (simp_all add: lower_bin_m_def Let_def push_m_def split_def)

lemma lower_m_length:
  \<open>wt ws ds t \<Longrightarrow> length (fst (fst (lower_m ws dm L t))) \<le> length (fst L) + 2 * term_weight ws ds t\<close>
proof (induction t arbitrary: L)
  case (Term_Const bs)
  show ?case using cube1[of \<open>length bs\<close>] by (simp add: push_m_def tw_leaf; linarith)
next
  case (Term_Var i)
  show ?case using cube1[of \<open>ws ! unat i\<close>] by (simp add: push_m_def tw_leaf; linarith)
next
  case (Term_Ref j)
  show ?case by (simp add: tw_leaf; linarith)
next
  case (Term_Not a)
  have wta: \<open>wt ws ds a\<close> using Term_Not.prems by simp
  have ih: \<open>length (fst (fst (lower_m ws dm L a))) \<le> length (fst L) + 2 * term_weight ws ds a\<close>
    using Term_Not.IH[OF wta] by simp
  have L: \<open>length (fst (fst (lower_m ws dm L (Term_Not a)))) = length (fst (fst (lower_m ws dm L a))) + 1\<close>
    by (simp add: push_m_def split_def)
  show ?case using ih L cube1[of \<open>width ws ds (Term_Not a)\<close>]
    unfolding tw_un add_mult_distrib2 by linarith
next
  case (Term_Neg a)
  have wta: \<open>wt ws ds a\<close> using Term_Neg.prems by simp
  have ih: \<open>length (fst (fst (lower_m ws dm L a))) \<le> length (fst L) + 2 * term_weight ws ds a\<close>
    using Term_Neg.IH[OF wta] by simp
  have L: \<open>length (fst (fst (lower_m ws dm L (Term_Neg a)))) = length (fst (fst (lower_m ws dm L a))) + 1\<close>
    by (simp add: push_m_def split_def)
  show ?case using ih L cube1[of \<open>width ws ds (Term_Neg a)\<close>]
    unfolding tw_un add_mult_distrib2 by linarith
next
  case (Term_Bin op a b)
  have w: \<open>wt ws ds a\<close> \<open>wt ws ds b\<close> using Term_Bin.prems by simp_all
  have c3: \<open>3 \<le> 2 * (width ws ds (Term_Bin op a b) + 1) ^ 3\<close>
    using wt_width_pos[OF Term_Bin.prems(1)] power_increasing[of 1 3 \<open>width ws ds (Term_Bin op a b) + 1\<close>] by simp
  have lb: \<open>length (fst (fst (lower_m ws dm L (Term_Bin op a b)))) \<le>
           length (fst (fst (lower_m ws dm (fst (lower_m ws dm L a)) b))) + 3\<close>
    using lower_bin_m_len3[of \<open>fst (lower_m ws dm (fst (lower_m ws dm L a)) b)\<close> op
        \<open>snd (lower_m ws dm L a)\<close> \<open>snd (lower_m ws dm (fst (lower_m ws dm L a)) b)\<close>] by simp
  have \<open>length (fst (fst (lower_m ws dm L (Term_Bin op a b)))) \<le>
        length (fst L) + 2 * term_weight ws ds a + 2 * term_weight ws ds b + 3\<close>
    using lb Term_Bin.IH(2)[OF w(2), of \<open>fst (lower_m ws dm L a)\<close>] Term_Bin.IH(1)[OF w(1), of L] by linarith
  then show ?case using c3 unfolding tw_Bin add_mult_distrib2 by linarith
next
  case (Term_Extract hi lo a)
  have wta: \<open>wt ws ds a\<close> using Term_Extract.prems by simp
  have ih: \<open>length (fst (fst (lower_m ws dm L a))) \<le> length (fst L) + 2 * term_weight ws ds a\<close>
    using Term_Extract.IH[OF wta] by simp
  have L: \<open>length (fst (fst (lower_m ws dm L (Term_Extract hi lo a)))) = length (fst (fst (lower_m ws dm L a))) + 1\<close>
    by (simp add: push_m_def split_def Let_def)
  show ?case using ih L cube1[of \<open>width ws ds (Term_Extract hi lo a)\<close>]
    unfolding tw_un add_mult_distrib2 by linarith
next
  case (Term_Repeat i a)
  have w: \<open>wt ws ds a\<close> \<open>1 \<le> unat i\<close> using Term_Repeat.prems by simp_all
  have wp: \<open>1 \<le> width ws ds a\<close> using wt_width_pos[OF w(1)] .
  have iW: \<open>unat i \<le> width ws ds (Term_Repeat i a)\<close>
    using mult_le_mono2[OF wp, of \<open>unat i\<close>] by simp
  have cR: \<open>width ws ds (Term_Repeat i a) + 1 \<le> (width ws ds (Term_Repeat i a) + 1) ^ 3\<close>
    using power_increasing[of 1 3 \<open>width ws ds (Term_Repeat i a) + 1\<close>] by simp
  have L: \<open>length (fst (fst (lower_m ws dm L (Term_Repeat i a)))) =
           length (fst (fst (lower_m ws dm L a))) + 1 + unat i\<close>
    unfolding lower_m_Repeat'' by (simp add: rep_fold_len)
  have \<open>\<dots> \<le> length (fst L) + 2 * term_weight ws ds a + 1 + unat i\<close>
    using Term_Repeat.IH[OF w(1), of L] by simp
  also have \<open>\<dots> \<le> length (fst L) + 2 * term_weight ws ds (Term_Repeat i a)\<close>
    using iW cR unfolding tw_un add_mult_distrib2 by linarith
  finally show ?case using L by simp
next
  case (Term_ZeroExtend i a)
  have wta: \<open>wt ws ds a\<close> using Term_ZeroExtend.prems by simp
  have ih: \<open>length (fst (fst (lower_m ws dm L a))) \<le> length (fst L) + 2 * term_weight ws ds a\<close>
    using Term_ZeroExtend.IH[OF wta] by simp
  have L: \<open>length (fst (fst (lower_m ws dm L (Term_ZeroExtend i a)))) = length (fst (fst (lower_m ws dm L a))) + 1\<close>
    by (simp add: push_m_def split_def Let_def)
  show ?case using ih L cube1[of \<open>width ws ds (Term_ZeroExtend i a)\<close>]
    unfolding tw_un add_mult_distrib2 by linarith
next
  case (Term_SignExtend i a)
  have wta: \<open>wt ws ds a\<close> using Term_SignExtend.prems by simp
  have ih: \<open>length (fst (fst (lower_m ws dm L a))) \<le> length (fst L) + 2 * term_weight ws ds a\<close>
    using Term_SignExtend.IH[OF wta] by simp
  have L: \<open>length (fst (fst (lower_m ws dm L (Term_SignExtend i a)))) = length (fst (fst (lower_m ws dm L a))) + 1\<close>
    by (simp add: push_m_def split_def Let_def)
  show ?case using ih L cube1[of \<open>width ws ds (Term_SignExtend i a)\<close>]
    unfolding tw_un add_mult_distrib2 by linarith
next
  case (Term_RotateLeft i a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  have w: \<open>wt ws ds a\<close> using Term_RotateLeft.prems by simp
  have L: \<open>length (fst (fst (lower_m ws dm L (Term_RotateLeft i a)))) \<le> length (fst L1) + 1\<close>
    using a by (simp add: lower_m_RotateLeft' Let_def push_m_def split: if_splits)
  have ih: \<open>length (fst L1) \<le> length (fst L) + 2 * term_weight ws ds a\<close>
    using Term_RotateLeft.IH[OF w, of L] a by simp
  show ?case using L ih cube1[of \<open>width ws ds (Term_RotateLeft i a)\<close>]
    unfolding tw_un add_mult_distrib2 by linarith
next
  case (Term_RotateRight i a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  have w: \<open>wt ws ds a\<close> using Term_RotateRight.prems by simp
  have L: \<open>length (fst (fst (lower_m ws dm L (Term_RotateRight i a)))) \<le> length (fst L1) + 1\<close>
    using a by (simp add: lower_m_RotateRight' Let_def push_m_def split: if_splits)
  have ih: \<open>length (fst L1) \<le> length (fst L) + 2 * term_weight ws ds a\<close>
    using Term_RotateRight.IH[OF w, of L] a by simp
  show ?case using L ih cube1[of \<open>width ws ds (Term_RotateRight i a)\<close>]
    unfolding tw_un add_mult_distrib2 by linarith
next
  case (Term_Ite c a b)
  have w: \<open>wt ws ds c\<close> \<open>wt ws ds a\<close> \<open>wt ws ds b\<close> using Term_Ite.prems by simp_all
  have \<open>length (fst (fst (lower_m ws dm L (Term_Ite c a b)))) =
        length (fst (fst (lower_m ws dm (fst (lower_m ws dm (fst (lower_m ws dm L c)) a)) b))) + 1\<close>
    by (simp add: push_m_def)
  also have \<open>\<dots> \<le> length (fst (fst (lower_m ws dm (fst (lower_m ws dm L c)) a))) + 2 * term_weight ws ds b + 1\<close>
    using Term_Ite.IH(3)[OF w(3), of \<open>fst (lower_m ws dm (fst (lower_m ws dm L c)) a)\<close>] by simp
  also have \<open>\<dots> \<le> length (fst (fst (lower_m ws dm L c))) + 2 * term_weight ws ds a + 2 * term_weight ws ds b + 1\<close>
    using Term_Ite.IH(2)[OF w(2), of \<open>fst (lower_m ws dm L c)\<close>] by simp
  also have \<open>\<dots> \<le> length (fst L) + 2 * term_weight ws ds c + 2 * term_weight ws ds a + 2 * term_weight ws ds b + 1\<close>
    using Term_Ite.IH(1)[OF w(1), of L] by simp
  also have \<open>\<dots> \<le> length (fst L) + 2 * term_weight ws ds (Term_Ite c a b)\<close>
    using cube1[of \<open>width ws ds (Term_Ite c a b)\<close>] unfolding tw_Ite add_mult_distrib2 by linarith
  finally show ?case .
qed

section \<open>A width bound on the rewriting, free of \<open>bnd\<close> of the result\<close>

text \<open>Every definition the rewriting produces has a width that is the width of some subterm, and the
  number of definitions stays within the budget; so \<^const>\<open>bnd\<close> of the result follows from
  \<^const>\<open>bnd\<close> of the input, the length budget and the subterm widths, all of which the problem's
  \<^const>\<open>size_bound\<close> provides.\<close>

lemma bnd_push:
  \<open>bnd L \<Longrightarrow> w < 2 ^ 64 \<Longrightarrow> length (fst L) + 1 < 2 ^ 64 \<Longrightarrow> bnd (fst (push_m L t w))\<close>
  by (auto simp add: bnd_def push_m_def)

lemma repeat_fold_bnd:
  \<open>bnd L0 \<Longrightarrow> acc + w * j < 2 ^ 64 \<Longrightarrow> length (fst L0) + j < 2 ^ 64 \<Longrightarrow>
   bnd (fst (foldl (repeat_step ka w) (L0, k0, acc) [0..<j]))\<close>
proof (induction j)
  case 0
  then show ?case by simp
next
  case (Suc j)
  let ?F = \<open>foldl (repeat_step ka w) (L0, k0, acc) [0..<j]\<close>
  have b: \<open>bnd (fst ?F)\<close> using Suc.IH Suc.prems by (simp add: mult_Suc_right)
  have acc: \<open>snd (snd ?F) = acc + w * j\<close> by (rule repeat_F_acc)
  have len: \<open>length (fst (fst ?F)) = length (fst L0) + j\<close> by (rule repeat_F_len)
  show ?case using b acc len Suc.prems(2,3)
    by (simp add: repeat_step_def push_m_def split_def bnd_def mult_Suc_right)
qed

lemma lower_bin_m_bnd:
  assumes \<open>bnd L\<close> \<open>length (fst L) + 3 < 2 ^ 64\<close> \<open>snd L ! ka < 2 ^ 64\<close> \<open>snd L ! kb < 2 ^ 64\<close>
    \<open>op = Op_Concat \<longrightarrow> snd L ! ka + snd L ! kb < 2 ^ 64\<close>
  shows \<open>bnd (fst (lower_bin_m L op ka kb))\<close>
  using assms by (cases op) (auto simp add: lower_bin_m_def Let_def push_m_def bnd_def split_def)

lemma lower_m_bnd:
  \<open>wt ws ds t \<Longrightarrow> lok ws L \<Longrightarrow> dm_ok ds dm L \<Longrightarrow> bnd L \<Longrightarrow>
   length (fst L) + 2 * term_weight ws ds t < 2 ^ 64 \<Longrightarrow>
   (\<forall>u \<in> set (subterms t). width ws ds u < 2 ^ 64) \<Longrightarrow>
   bnd (fst (lower_m ws dm L t))\<close>
proof (induction t arbitrary: L)
  case (Term_Const bs)
  have wb: \<open>length bs < 2 ^ 64\<close> using Term_Const.prems(6) by simp
  have len: \<open>length (fst L) + 1 < 2 ^ 64\<close>
    using Term_Const.prems(5) cube1[of \<open>length bs\<close>] unfolding tw_leaf width.simps add_mult_distrib2 by linarith
  show ?case using bnd_push[OF Term_Const.prems(4) wb len] by simp
next
  case (Term_Var i)
  have wb: \<open>ws ! unat i < 2 ^ 64\<close> using Term_Var.prems(6) by simp
  have len: \<open>length (fst L) + 1 < 2 ^ 64\<close>
    using Term_Var.prems(5) cube1[of \<open>ws ! unat i\<close>] unfolding tw_leaf width.simps add_mult_distrib2 by linarith
  show ?case using bnd_push[OF Term_Var.prems(4) wb len] by simp
next
  case (Term_Ref j)
  then show ?case by simp
next
  case (Term_Not a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  have wta: \<open>wt ws ds a\<close> using Term_Not.prems(1) by simp
  have sub: \<open>\<forall>u \<in> set (subterms a). width ws ds u < 2 ^ 64\<close> using Term_Not.prems(6) by simp
  have bud: \<open>length (fst L) + 2 * term_weight ws ds a < 2 ^ 64\<close>
    using Term_Not.prems(5) cube1[of \<open>width ws ds (Term_Not a)\<close>] unfolding tw_un add_mult_distrib2 by linarith
  have B1: \<open>bnd L1\<close> using Term_Not.IH[OF wta Term_Not.prems(2,3,4) bud sub] a by simp
  have EA: \<open>env_ok ws L1 ka (width ws ds a)\<close>
    using lower_m_correct[OF wta Term_Not.prems(2,3) a B1] by simp
  have wa: \<open>snd L1 ! ka = width ws ds a\<close> and ka64: \<open>ka < 2 ^ 64\<close> using EA by (simp_all add: env_ok_def)
  have wsub: \<open>snd L1 ! ka < 2 ^ 64\<close> using wa Term_Not.prems(6) by simp
  have lena: \<open>length (fst L1) \<le> length (fst L) + 2 * term_weight ws ds a\<close>
    using lower_m_length[OF wta, of dm L] a by simp
  have len: \<open>length (fst L1) + 1 < 2 ^ 64\<close>
    using lena Term_Not.prems(5) cube1[of \<open>width ws ds (Term_Not a)\<close>] unfolding tw_un add_mult_distrib2 by linarith
  show ?case using a bnd_push[OF B1 wsub len] by simp
next
  case (Term_Neg a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  have wta: \<open>wt ws ds a\<close> using Term_Neg.prems(1) by simp
  have sub: \<open>\<forall>u \<in> set (subterms a). width ws ds u < 2 ^ 64\<close> using Term_Neg.prems(6) by simp
  have bud: \<open>length (fst L) + 2 * term_weight ws ds a < 2 ^ 64\<close>
    using Term_Neg.prems(5) cube1[of \<open>width ws ds (Term_Neg a)\<close>] unfolding tw_un add_mult_distrib2 by linarith
  have B1: \<open>bnd L1\<close> using Term_Neg.IH[OF wta Term_Neg.prems(2,3,4) bud sub] a by simp
  have EA: \<open>env_ok ws L1 ka (width ws ds a)\<close>
    using lower_m_correct[OF wta Term_Neg.prems(2,3) a B1] by simp
  have wa: \<open>snd L1 ! ka = width ws ds a\<close> using EA by (simp add: env_ok_def)
  have wsub: \<open>snd L1 ! ka < 2 ^ 64\<close> using wa Term_Neg.prems(6) by simp
  have lena: \<open>length (fst L1) \<le> length (fst L) + 2 * term_weight ws ds a\<close>
    using lower_m_length[OF wta, of dm L] a by simp
  have len: \<open>length (fst L1) + 1 < 2 ^ 64\<close>
    using lena Term_Neg.prems(5) cube1[of \<open>width ws ds (Term_Neg a)\<close>] unfolding tw_un add_mult_distrib2 by linarith
  show ?case using a bnd_push[OF B1 wsub len] by simp
next
  case (Term_Bin op a b)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  obtain L2 kb where b: \<open>lower_m ws dm L1 b = (L2, kb)\<close> by (cases \<open>lower_m ws dm L1 b\<close>)
  have wt: \<open>wt ws ds a\<close> \<open>wt ws ds b\<close> \<open>op \<noteq> Op_Concat \<longrightarrow> width ws ds b = width ws ds a\<close>
    using Term_Bin.prems(1) by simp_all
  have suba: \<open>\<forall>u \<in> set (subterms a). width ws ds u < 2 ^ 64\<close> using Term_Bin.prems(6) by simp
  have subb: \<open>\<forall>u \<in> set (subterms b). width ws ds u < 2 ^ 64\<close> using Term_Bin.prems(6) by simp
  have buda: \<open>length (fst L) + 2 * term_weight ws ds a < 2 ^ 64\<close>
    using Term_Bin.prems(5) cube1[of \<open>width ws ds (Term_Bin op a b)\<close>] unfolding tw_Bin add_mult_distrib2 by linarith
  have B1: \<open>bnd L1\<close> using Term_Bin.IH(1)[OF wt(1) Term_Bin.prems(2,3,4) buda suba] a by simp
  have Sa: \<open>env_ok ws L1 ka (width ws ds a) \<and> lok ws L1 \<and> lext ws L L1\<close>
    using lower_m_correct[OF wt(1) Term_Bin.prems(2,3) a B1] lext_lok by blast
  have L1: \<open>lok ws L1\<close> and X1: \<open>lext ws L L1\<close> using Sa by blast+
  have D1: \<open>dm_ok ds dm L1\<close> using dm_ok_lext[OF Term_Bin.prems(2,3) X1] .
  have lena: \<open>length (fst L1) \<le> length (fst L) + 2 * term_weight ws ds a\<close>
    using lower_m_length[OF wt(1), of dm L] a by simp
  have budb: \<open>length (fst L1) + 2 * term_weight ws ds b < 2 ^ 64\<close>
    using lena Term_Bin.prems(5) cube1[of \<open>width ws ds (Term_Bin op a b)\<close>] unfolding tw_Bin add_mult_distrib2 by linarith
  have B2: \<open>bnd L2\<close> using Term_Bin.IH(2)[OF wt(2) L1 D1 B1 budb subb] b by simp
  have EA: \<open>env_ok ws L2 ka (width ws ds a)\<close>
    using lower_m_correct[OF wt(1) Term_Bin.prems(2,3) a B1] lower_m_correct[OF wt(2) L1 D1 b B2] env_lext by blast
  have EB: \<open>env_ok ws L2 kb (width ws ds b)\<close>
    using lower_m_correct[OF wt(2) L1 D1 b B2] by simp
  have wa: \<open>snd L2 ! ka = width ws ds a\<close> and wb: \<open>snd L2 ! kb = width ws ds b\<close>
    using EA EB by (simp_all add: env_ok_def)
  have selfa: \<open>a \<in> set (subterms a)\<close> by (cases a) auto
  have selfb: \<open>b \<in> set (subterms b)\<close> by (cases b) auto
  have wa64: \<open>snd L2 ! ka < 2 ^ 64\<close> using wa bspec[OF suba selfa] by simp
  have wb64: \<open>snd L2 ! kb < 2 ^ 64\<close> using wb bspec[OF subb selfb] by simp
  have cc: \<open>op = Op_Concat \<longrightarrow> snd L2 ! ka + snd L2 ! kb < 2 ^ 64\<close>
  proof
    assume \<open>op = Op_Concat\<close>
    then have \<open>snd L2 ! ka + snd L2 ! kb = width ws ds (Term_Bin op a b)\<close> using wa wb by simp
    then show \<open>snd L2 ! ka + snd L2 ! kb < 2 ^ 64\<close> using Term_Bin.prems(6) by simp
  qed
  have lenb: \<open>length (fst L2) \<le> length (fst L) + 2 * term_weight ws ds a + 2 * term_weight ws ds b\<close>
    using lower_m_length[OF wt(2), of dm L1] b lena by simp
  have c3: \<open>3 \<le> 2 * (width ws ds (Term_Bin op a b) + 1) ^ 3\<close>
    using wt_width_pos[OF Term_Bin.prems(1)] power_increasing[of 1 3 \<open>width ws ds (Term_Bin op a b) + 1\<close>] by simp
  have len3: \<open>length (fst L2) + 3 < 2 ^ 64\<close>
    using lenb Term_Bin.prems(5) c3 unfolding tw_Bin add_mult_distrib2 by linarith
  have R: \<open>lower_m ws dm L (Term_Bin op a b) = lower_bin_m L2 op ka kb\<close> using a b by simp
  show ?case using R lower_bin_m_bnd[OF B2 len3 wa64 wb64 cc] by simp
next
  case (Term_Extract hi lo a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  have wt: \<open>wt ws ds a\<close> \<open>unat lo \<le> unat hi\<close> \<open>unat hi < width ws ds a\<close> using Term_Extract.prems(1) by simp_all
  have sub: \<open>\<forall>u \<in> set (subterms a). width ws ds u < 2 ^ 64\<close> using Term_Extract.prems(6) by simp
  have bud: \<open>length (fst L) + 2 * term_weight ws ds a < 2 ^ 64\<close>
    using Term_Extract.prems(5) cube1[of \<open>width ws ds (Term_Extract hi lo a)\<close>] unfolding tw_un add_mult_distrib2 by linarith
  have B1: \<open>bnd L1\<close> using Term_Extract.IH[OF wt(1) Term_Extract.prems(2,3,4) bud sub] a by simp
  have selfa: \<open>a \<in> set (subterms a)\<close> by (cases a) auto
  have wsub: \<open>unat hi - unat lo + 1 < 2 ^ 64\<close>
  proof -
    have \<open>unat hi - unat lo + 1 \<le> width ws ds a\<close> using wt(2,3) by simp
    then show ?thesis using bspec[OF sub selfa] by simp
  qed
  have lena: \<open>length (fst L1) \<le> length (fst L) + 2 * term_weight ws ds a\<close>
    using lower_m_length[OF wt(1), of dm L] a by simp
  have len: \<open>length (fst L1) + 1 < 2 ^ 64\<close>
    using lena Term_Extract.prems(5) cube1[of \<open>width ws ds (Term_Extract hi lo a)\<close>] unfolding tw_un add_mult_distrib2 by linarith
  show ?case using a bnd_push[OF B1 wsub len] by (simp add: Let_def)
next
  case (Term_Repeat i a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  have wt: \<open>wt ws ds a\<close> \<open>1 \<le> unat i\<close> using Term_Repeat.prems(1) by simp_all
  have sub: \<open>\<forall>u \<in> set (subterms a). width ws ds u < 2 ^ 64\<close> using Term_Repeat.prems(6) by simp
  have wR: \<open>width ws ds (Term_Repeat i a) < 2 ^ 64\<close> using Term_Repeat.prems(6) by simp
  have bud: \<open>length (fst L) + 2 * term_weight ws ds a < 2 ^ 64\<close>
    using Term_Repeat.prems(5) cube1[of \<open>width ws ds (Term_Repeat i a)\<close>] unfolding tw_un add_mult_distrib2 by linarith
  have B1: \<open>bnd L1\<close> using Term_Repeat.IH[OF wt(1) Term_Repeat.prems(2,3,4) bud sub] a by simp
  have EA: \<open>env_ok ws L1 ka (width ws ds a)\<close>
    using lower_m_correct[OF wt(1) Term_Repeat.prems(2,3) a B1] by simp
  have wa: \<open>snd L1 ! ka = width ws ds a\<close> and L1: \<open>lok ws L1\<close> using EA by (simp_all add: env_ok_def)
  obtain L2 k0 where p: \<open>push_m L1 (CoreTerm_Const []) 0 = (L2, k0)\<close> by (cases \<open>push_m L1 (CoreTerm_Const []) 0\<close>)
  have lenL1: \<open>length (fst L1) \<le> length (fst L) + 2 * term_weight ws ds a\<close>
    using lower_m_length[OF wt(1), of dm L] a by simp
  have iW: \<open>unat i \<le> width ws ds (Term_Repeat i a)\<close>
    using mult_le_mono2[OF wt_width_pos[OF wt(1)], of \<open>unat i\<close>] by simp
  have cR: \<open>width ws ds (Term_Repeat i a) + 1 \<le> (width ws ds (Term_Repeat i a) + 1) ^ 3\<close>
    using power_increasing[of 1 3 \<open>width ws ds (Term_Repeat i a) + 1\<close>] by simp
  have cubeW: \<open>unat i + 1 \<le> 2 * (width ws ds (Term_Repeat i a) + 1) ^ 3\<close>
    using iW cR by linarith
  have lenbud: \<open>length (fst L1) + 1 + unat i < 2 ^ 64\<close>
    using lenL1 Term_Repeat.prems(5) cubeW unfolding tw_un add_mult_distrib2 by linarith
  have lb2: \<open>length (fst L1) + 1 < 2 ^ 64\<close> using lenbud by linarith
  have B2: \<open>bnd L2\<close>
    using bnd_push[OF B1 _ lb2, where t=\<open>CoreTerm_Const []\<close> and w=0] p by (simp add: push_m_def)
  have L2': \<open>L2 = fst (push_m L1 (CoreTerm_Const []) 0)\<close> using p by simp
  have L2len: \<open>length (fst L2) = length (fst L1) + 1\<close> by (simp add: L2' push_m_def)
  have k0len: \<open>length (fst L2) + unat i < 2 ^ 64\<close> using L2len lenbud by simp
  have wmul: \<open>0 + snd L1 ! ka * unat i < 2 ^ 64\<close> using wR wa by (simp add: mult.commute)
  have R: \<open>lower_m ws dm L (Term_Repeat i a) = (fst (foldl (repeat_step ka (snd L1 ! ka)) (L2, k0, 0) [0..<unat i]),
            fst (snd (foldl (repeat_step ka (snd L1 ! ka)) (L2, k0, 0) [0..<unat i])))\<close>
    using a p by (simp add: lower_m_Repeat' Let_def split_def)
  show ?case using R repeat_fold_bnd[OF B2 wmul k0len, of ka] by simp
next
  case (Term_ZeroExtend i a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  have wt: \<open>wt ws ds a\<close> using Term_ZeroExtend.prems(1) by simp
  have sub: \<open>\<forall>u \<in> set (subterms a). width ws ds u < 2 ^ 64\<close> using Term_ZeroExtend.prems(6) by simp
  have bud: \<open>length (fst L) + 2 * term_weight ws ds a < 2 ^ 64\<close>
    using Term_ZeroExtend.prems(5) cube1[of \<open>width ws ds (Term_ZeroExtend i a)\<close>] unfolding tw_un add_mult_distrib2 by linarith
  have B1: \<open>bnd L1\<close> using Term_ZeroExtend.IH[OF wt Term_ZeroExtend.prems(2,3,4) bud sub] a by simp
  have EA: \<open>env_ok ws L1 ka (width ws ds a)\<close>
    using lower_m_correct[OF wt Term_ZeroExtend.prems(2,3) a B1] by simp
  have wa: \<open>snd L1 ! ka = width ws ds a\<close> using EA by (simp add: env_ok_def)
  have wsub: \<open>snd L1 ! ka + unat i < 2 ^ 64\<close> using wa Term_ZeroExtend.prems(6) by simp
  have lena: \<open>length (fst L1) \<le> length (fst L) + 2 * term_weight ws ds a\<close>
    using lower_m_length[OF wt, of dm L] a by simp
  have len: \<open>length (fst L1) + 1 < 2 ^ 64\<close>
    using lena Term_ZeroExtend.prems(5) cube1[of \<open>width ws ds (Term_ZeroExtend i a)\<close>] unfolding tw_un add_mult_distrib2 by linarith
  show ?case using a bnd_push[OF B1 wsub len] by (simp add: Let_def)
next
  case (Term_SignExtend i a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  have wt: \<open>wt ws ds a\<close> using Term_SignExtend.prems(1) by simp
  have sub: \<open>\<forall>u \<in> set (subterms a). width ws ds u < 2 ^ 64\<close> using Term_SignExtend.prems(6) by simp
  have bud: \<open>length (fst L) + 2 * term_weight ws ds a < 2 ^ 64\<close>
    using Term_SignExtend.prems(5) cube1[of \<open>width ws ds (Term_SignExtend i a)\<close>] unfolding tw_un add_mult_distrib2 by linarith
  have B1: \<open>bnd L1\<close> using Term_SignExtend.IH[OF wt Term_SignExtend.prems(2,3,4) bud sub] a by simp
  have EA: \<open>env_ok ws L1 ka (width ws ds a)\<close>
    using lower_m_correct[OF wt Term_SignExtend.prems(2,3) a B1] by simp
  have wa: \<open>snd L1 ! ka = width ws ds a\<close> using EA by (simp add: env_ok_def)
  have wsub: \<open>snd L1 ! ka + unat i < 2 ^ 64\<close> using wa Term_SignExtend.prems(6) by simp
  have lena: \<open>length (fst L1) \<le> length (fst L) + 2 * term_weight ws ds a\<close>
    using lower_m_length[OF wt, of dm L] a by simp
  have len: \<open>length (fst L1) + 1 < 2 ^ 64\<close>
    using lena Term_SignExtend.prems(5) cube1[of \<open>width ws ds (Term_SignExtend i a)\<close>] unfolding tw_un add_mult_distrib2 by linarith
  show ?case using a bnd_push[OF B1 wsub len] by (simp add: Let_def)
next
  case (Term_RotateLeft i a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  have wt: \<open>wt ws ds a\<close> using Term_RotateLeft.prems(1) by simp
  have sub: \<open>\<forall>u \<in> set (subterms a). width ws ds u < 2 ^ 64\<close> using Term_RotateLeft.prems(6) by simp
  have bud: \<open>length (fst L) + 2 * term_weight ws ds a < 2 ^ 64\<close>
    using Term_RotateLeft.prems(5) cube1[of \<open>width ws ds (Term_RotateLeft i a)\<close>] unfolding tw_un add_mult_distrib2 by linarith
  have B1: \<open>bnd L1\<close> using Term_RotateLeft.IH[OF wt Term_RotateLeft.prems(2,3,4) bud sub] a by simp
  have EA: \<open>env_ok ws L1 ka (width ws ds a)\<close>
    using lower_m_correct[OF wt Term_RotateLeft.prems(2,3) a B1] by simp
  have wa: \<open>snd L1 ! ka = width ws ds a\<close> using EA by (simp add: env_ok_def)
  have wsub: \<open>snd L1 ! ka < 2 ^ 64\<close> using wa Term_RotateLeft.prems(6) by simp
  have lena: \<open>length (fst L1) \<le> length (fst L) + 2 * term_weight ws ds a\<close>
    using lower_m_length[OF wt, of dm L] a by simp
  have len: \<open>length (fst L1) + 1 < 2 ^ 64\<close>
    using lena Term_RotateLeft.prems(5) cube1[of \<open>width ws ds (Term_RotateLeft i a)\<close>] unfolding tw_un add_mult_distrib2 by linarith
  show ?case using a bnd_push[OF B1 wsub len] B1
    by (simp add: lower_m_RotateLeft' Let_def split: if_splits)
next
  case (Term_RotateRight i a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  have wt: \<open>wt ws ds a\<close> using Term_RotateRight.prems(1) by simp
  have sub: \<open>\<forall>u \<in> set (subterms a). width ws ds u < 2 ^ 64\<close> using Term_RotateRight.prems(6) by simp
  have bud: \<open>length (fst L) + 2 * term_weight ws ds a < 2 ^ 64\<close>
    using Term_RotateRight.prems(5) cube1[of \<open>width ws ds (Term_RotateRight i a)\<close>] unfolding tw_un add_mult_distrib2 by linarith
  have B1: \<open>bnd L1\<close> using Term_RotateRight.IH[OF wt Term_RotateRight.prems(2,3,4) bud sub] a by simp
  have EA: \<open>env_ok ws L1 ka (width ws ds a)\<close>
    using lower_m_correct[OF wt Term_RotateRight.prems(2,3) a B1] by simp
  have wa: \<open>snd L1 ! ka = width ws ds a\<close> using EA by (simp add: env_ok_def)
  have wsub: \<open>snd L1 ! ka < 2 ^ 64\<close> using wa Term_RotateRight.prems(6) by simp
  have lena: \<open>length (fst L1) \<le> length (fst L) + 2 * term_weight ws ds a\<close>
    using lower_m_length[OF wt, of dm L] a by simp
  have len: \<open>length (fst L1) + 1 < 2 ^ 64\<close>
    using lena Term_RotateRight.prems(5) cube1[of \<open>width ws ds (Term_RotateRight i a)\<close>] unfolding tw_un add_mult_distrib2 by linarith
  show ?case using a bnd_push[OF B1 wsub len] B1
    by (simp add: lower_m_RotateRight' Let_def split: if_splits)
next
  case (Term_Ite c a b)
  obtain L1 kc where c: \<open>lower_m ws dm L c = (L1, kc)\<close> by (cases \<open>lower_m ws dm L c\<close>)
  obtain L2 ka where a: \<open>lower_m ws dm L1 a = (L2, ka)\<close> by (cases \<open>lower_m ws dm L1 a\<close>)
  obtain L3 kb where b: \<open>lower_m ws dm L2 b = (L3, kb)\<close> by (cases \<open>lower_m ws dm L2 b\<close>)
  have wt: \<open>wt ws ds c\<close> \<open>wt ws ds a\<close> \<open>wt ws ds b\<close> \<open>width ws ds a = width ws ds b\<close>
    using Term_Ite.prems(1) by simp_all
  have subc: \<open>\<forall>u \<in> set (subterms c). width ws ds u < 2 ^ 64\<close> using Term_Ite.prems(6) by simp
  have suba: \<open>\<forall>u \<in> set (subterms a). width ws ds u < 2 ^ 64\<close> using Term_Ite.prems(6) by simp
  have subb: \<open>\<forall>u \<in> set (subterms b). width ws ds u < 2 ^ 64\<close> using Term_Ite.prems(6) by simp
  have budc: \<open>length (fst L) + 2 * term_weight ws ds c < 2 ^ 64\<close>
    using Term_Ite.prems(5) cube1[of \<open>width ws ds (Term_Ite c a b)\<close>] unfolding tw_Ite add_mult_distrib2 by linarith
  have B1: \<open>bnd L1\<close> using Term_Ite.IH(1)[OF wt(1) Term_Ite.prems(2,3,4) budc subc] c by simp
  have L1: \<open>lok ws L1\<close> and X1: \<open>lext ws L L1\<close>
    using lower_m_correct[OF wt(1) Term_Ite.prems(2,3) c B1] lext_lok by blast+
  have D1: \<open>dm_ok ds dm L1\<close> using dm_ok_lext[OF Term_Ite.prems(2,3) X1] .
  have lenc: \<open>length (fst L1) \<le> length (fst L) + 2 * term_weight ws ds c\<close>
    using lower_m_length[OF wt(1), of dm L] c by simp
  have buda: \<open>length (fst L1) + 2 * term_weight ws ds a < 2 ^ 64\<close>
    using lenc Term_Ite.prems(5) cube1[of \<open>width ws ds (Term_Ite c a b)\<close>] unfolding tw_Ite add_mult_distrib2 by linarith
  have B2: \<open>bnd L2\<close> using Term_Ite.IH(2)[OF wt(2) L1 D1 B1 buda suba] a by simp
  have L2: \<open>lok ws L2\<close> and X2: \<open>lext ws L1 L2\<close>
    using lower_m_correct[OF wt(2) L1 D1 a B2] lext_lok by blast+
  have D2: \<open>dm_ok ds dm L2\<close> using dm_ok_lext[OF L1 D1 X2] .
  have lena: \<open>length (fst L2) \<le> length (fst L) + 2 * term_weight ws ds c + 2 * term_weight ws ds a\<close>
    using lower_m_length[OF wt(2), of dm L1] a lenc by simp
  have budb: \<open>length (fst L2) + 2 * term_weight ws ds b < 2 ^ 64\<close>
    using lena Term_Ite.prems(5) cube1[of \<open>width ws ds (Term_Ite c a b)\<close>] unfolding tw_Ite add_mult_distrib2 by linarith
  have B3: \<open>bnd L3\<close> using Term_Ite.IH(3)[OF wt(3) L2 D2 B2 budb subb] b by simp
  have EA: \<open>env_ok ws L3 ka (width ws ds a)\<close>
    using lower_m_correct[OF wt(2) L1 D1 a B2] lower_m_correct[OF wt(3) L2 D2 b B3] env_lext by blast
  have wa: \<open>snd L3 ! ka = width ws ds a\<close> using EA by (simp add: env_ok_def)
  have wsub: \<open>snd L3 ! ka < 2 ^ 64\<close> using wa Term_Ite.prems(6) by simp
  have lenb: \<open>length (fst L3) \<le> length (fst L) + 2 * term_weight ws ds c + 2 * term_weight ws ds a + 2 * term_weight ws ds b\<close>
    using lower_m_length[OF wt(3), of dm L2] b lena by simp
  have len: \<open>length (fst L3) + 1 < 2 ^ 64\<close>
    using lenb Term_Ite.prems(5) cube1[of \<open>width ws ds (Term_Ite c a b)\<close>] unfolding tw_Ite add_mult_distrib2 by linarith
  show ?case using c a b bnd_push[OF B3 wsub len] by simp
qed

section \<open>The rewriting of a whole problem stays within \<open>bnd\<close>\<close>

lemma length_le_lcost: \<open>length (fst L) \<le> lcost ws L\<close>
  by (simp add: lcost_def)

lemma sum_list_take_app_le:
  fixes f :: \<open>'a \<Rightarrow> nat\<close>
  shows \<open>sum_list (map f (take j xs)) \<le> sum_list (map f (xs @ ys))\<close>
proof -
  have \<open>sum_list (map f (take j xs)) \<le> sum_list (map f (take j xs)) + sum_list (map f (drop j xs @ ys))\<close>
    by simp
  also have \<open>\<dots> = sum_list (map f (xs @ ys))\<close>
    by (metis append.assoc append_take_drop_id map_append sum_list_append)
  finally show ?thesis .
qed

lemma member_tw_app_le:
  assumes \<open>t \<in> set xs\<close>
  shows \<open>term_weight ws ds t \<le> sum_list (map (term_weight ws ds) (xs @ ys))\<close>
proof -
  have \<open>term_weight ws ds t \<le> sum_list (map (term_weight ws ds) xs)\<close>
    using assms by (intro member_le_sum_list; simp)
  then show ?thesis by simp
qed

lemma size_bound_sum:
  \<open>1000000 * sum_list (map (term_weight (var_widths p) (def_widths (var_widths p) [] (Problem_defs p)))
     (Problem_defs p @ Problem_asserts p)) \<le> size_bound p\<close>
  by (simp add: size_bound_def Let_def)

text \<open>Named partial results of the two loops of \<^const>\<open>lower_problem_m\<close>, with the step rule as a
  simp rule so that the loop proof can advance the invariant one iteration at a time.\<close>
definition ldefs_part :: \<open>Problem \<Rightarrow> nat \<Rightarrow> lst \<times> nat list\<close> where
  \<open>ldefs_part p n \<equiv> foldl (ldefs_step p) (([], []), []) [0..<n]\<close>

definition lasserts_part :: \<open>Problem \<Rightarrow> nat \<Rightarrow> lst \<times> CoreTerm list\<close> where
  \<open>lasserts_part p n \<equiv> foldl (lasserts_step p (snd (ldefs_res p))) (fst (ldefs_res p), []) [0..<n]\<close>

lemma ldefs_part_simps [simp]:
  \<open>ldefs_part p 0 = (([], []), [])\<close>
  \<open>ldefs_part p (Suc n) =
     (let (L1, k) = lower_m (var_widths p) (snd (ldefs_part p n)) (fst (ldefs_part p n)) (Problem_defs p ! n)
      in (L1, snd (ldefs_part p n) @ [k]))\<close>
  by (simp_all add: ldefs_part_def ldefs_step_def split_def Let_def)

lemma lasserts_part_simps [simp]:
  \<open>lasserts_part p 0 = (fst (ldefs_res p), [])\<close>
  \<open>lasserts_part p (Suc n) =
     (let (L1, k) = lower_m (var_widths p) (snd (ldefs_res p)) (fst (lasserts_part p n)) (Problem_asserts p ! n)
      in (L1, snd (lasserts_part p n) @ [cr k]))\<close>
  by (simp_all add: lasserts_part_def lasserts_step_def split_def Let_def)

lemma ldefs_part_res: \<open>ldefs_part p (length (Problem_defs p)) = ldefs_res p\<close>
  by (simp add: ldefs_part_def ldefs_res_def)

lemma lasserts_part_res: \<open>lasserts_part p (length (Problem_asserts p)) = lasserts_res p\<close>
  by (simp add: lasserts_part_def lasserts_res_def)

lemma ldefs_bnd:
  assumes \<open>problem_wt p\<close> \<open>size_bound p < 2 ^ 64\<close>
  shows \<open>j \<le> length (Problem_defs p) \<Longrightarrow> bnd (fst (foldl (ldefs_step p) (([], []), []) [0..<j]))\<close>
proof (induction j)
  case 0
  show ?case by (simp add: bnd_def)
next
  case (Suc j)
  let ?ws = \<open>var_widths p\<close> and ?D = \<open>Problem_defs p\<close> and ?A = \<open>Problem_asserts p\<close>
  let ?ds = \<open>def_widths ?ws [] ?D\<close>
  let ?dsj = \<open>def_widths ?ws [] (take j ?D)\<close>
  let ?SUM = \<open>sum_list (map (term_weight ?ws ?ds) (?D @ ?A))\<close>
  obtain Lj dmj where f: \<open>foldl (ldefs_step p) (([], []), []) [0..<j] = (Lj, dmj)\<close>
    by (cases \<open>foldl (ldefs_step p) (([], []), []) [0..<j]\<close>)
  have jl: \<open>j < length ?D\<close> and jle: \<open>j \<le> length ?D\<close> using Suc.prems by simp_all
  have Bj: \<open>bnd Lj\<close> using Suc.IH jle f by simp
  have dwt: \<open>defs_wt ?ws [] ?D\<close> using assms(1) by (simp add: problem_wt_def Let_def)
  have inv: \<open>ldefs_inv p j (Lj, dmj)\<close> using ldefs_loop[OF dwt jle f Bj] .
  have lok: \<open>lok ?ws Lj\<close> and dmok: \<open>dm_ok ?dsj dmj Lj\<close>
    using inv by (simp_all add: ldefs_inv_def Let_def)
  have wtj: \<open>wt ?ws ?dsj (?D ! j)\<close> using defs_wt_nth[OF dwt jl] .
  have sb: \<open>1000000 * ?SUM \<le> size_bound p\<close> using size_bound_sum by simp
  have twj: \<open>term_weight ?ws ?dsj (?D ! j) \<le> ?SUM\<close>
    using term_weight_take[OF dwt jl] member_tw_app_le[of \<open>?D ! j\<close> ?D ?ws ?ds ?A] nth_mem[OF jl] by simp
  have sumj: \<open>sum_list (map (term_weight ?ws ?ds) (take j ?D)) \<le> ?SUM\<close>
    by (rule sum_list_take_app_le)
  have budget: \<open>length (fst Lj) + 2 * term_weight ?ws ?dsj (?D ! j) < 2 ^ 64\<close>
  proof -
    have \<open>length (fst Lj) \<le> 800 * sum_list (map (term_weight ?ws ?ds) (take j ?D))\<close>
      using ldefs_cost[OF assms(1) jle f Bj] length_le_lcost[of Lj ?ws] by simp
    then have \<open>length (fst Lj) + 2 * term_weight ?ws ?dsj (?D ! j) \<le> 802 * ?SUM\<close>
      using twj sumj by simp
    also have \<open>\<dots> \<le> 1000000 * ?SUM\<close> by simp
    also have \<open>\<dots> \<le> size_bound p\<close> using sb by simp
    also have \<open>\<dots> < 2 ^ 64\<close> using assms(2) by simp
    finally show ?thesis .
  qed
  have subw: \<open>\<forall>u \<in> set (subterms (?D ! j)). width ?ws ?dsj u < 2 ^ 64\<close>
  proof
    fix u assume \<open>u \<in> set (subterms (?D ! j))\<close>
    then have \<open>width ?ws ?dsj u \<le> term_weight ?ws ?dsj (?D ! j)\<close> by (rule width_le_tw)
    also have \<open>\<dots> \<le> ?SUM\<close> using twj by simp
    also have \<open>\<dots> \<le> size_bound p\<close> using sb by simp
    also have \<open>\<dots> < 2 ^ 64\<close> using assms(2) by simp
    finally show \<open>width ?ws ?dsj u < 2 ^ 64\<close> .
  qed
  have R: \<open>foldl (ldefs_step p) (([], []), []) [0..<Suc j] =
           (fst (lower_m ?ws dmj Lj (?D ! j)), dmj @ [snd (lower_m ?ws dmj Lj (?D ! j))])\<close>
    using f by (simp add: ldefs_step_def split_def Let_def)
  show ?case using R lower_m_bnd[OF wtj lok dmok Bj budget subw] by simp
qed

lemma lasserts_bnd:
  assumes \<open>problem_wt p\<close> \<open>size_bound p < 2 ^ 64\<close>
  shows \<open>i \<le> length (Problem_asserts p) \<Longrightarrow>
         bnd (fst (foldl (lasserts_step p (snd (ldefs_res p))) (fst (ldefs_res p), []) [0..<i]))\<close>
proof (induction i)
  case 0
  show ?case using ldefs_bnd[OF assms, of \<open>length (Problem_defs p)\<close>] by (simp add: ldefs_res_def)
next
  case (Suc i)
  let ?ws = \<open>var_widths p\<close> and ?D = \<open>Problem_defs p\<close> and ?A = \<open>Problem_asserts p\<close>
  let ?ds = \<open>def_widths ?ws [] ?D\<close>
  let ?SUM = \<open>sum_list (map (term_weight ?ws ?ds) (?D @ ?A))\<close>
  let ?dm = \<open>snd (ldefs_res p)\<close> and ?L0 = \<open>fst (ldefs_res p)\<close>
  obtain Li csi where f: \<open>foldl (lasserts_step p ?dm) (?L0, []) [0..<i] = (Li, csi)\<close>
    by (cases \<open>foldl (lasserts_step p ?dm) (?L0, []) [0..<i]\<close>)
  have il: \<open>i < length ?A\<close> and ile: \<open>i \<le> length ?A\<close> using Suc.prems by simp_all
  have Bi: \<open>bnd Li\<close> using Suc.IH ile f by simp
  have B0: \<open>bnd ?L0\<close> using ldefs_bnd[OF assms, of \<open>length ?D\<close>] by (simp add: ldefs_res_def)
  have dwt: \<open>defs_wt ?ws [] ?D\<close> using assms(1) by (simp add: problem_wt_def Let_def)
  have feq: \<open>foldl (ldefs_step p) (([], []), []) [0..<length ?D] = (?L0, ?dm)\<close>
    by (simp add: ldefs_res_def)
  have I1: \<open>ldefs_inv p (length ?D) (?L0, ?dm)\<close>
    using ldefs_loop[OF dwt order_refl feq B0] .
  have inv: \<open>lasserts_inv p ?dm ?L0 i (Li, csi)\<close>
    using lasserts_loop[OF assms(1) ile I1 f Bi] .
  have lok: \<open>lok ?ws Li\<close> using inv lext_lok by (simp add: lasserts_inv_def Let_def) blast
  have dmok: \<open>dm_ok ?ds ?dm Li\<close>
  proof -
    have lx: \<open>lext ?ws ?L0 Li\<close> using inv by (simp add: lasserts_inv_def Let_def)
    have lok0: \<open>lok ?ws ?L0\<close> using I1 by (simp add: ldefs_inv_def Let_def)
    have dmok0: \<open>dm_ok ?ds ?dm ?L0\<close> using I1 by (simp add: ldefs_inv_def Let_def take_all)
    show ?thesis using dm_ok_lext[OF lok0 dmok0 lx] .
  qed
  have wti: \<open>wt ?ws ?ds (?A ! i)\<close> using assms(1) il by (simp add: problem_wt_def Let_def)
  have sb: \<open>1000000 * ?SUM \<le> size_bound p\<close> using size_bound_sum by simp
  have twi: \<open>term_weight ?ws ?ds (?A ! i) \<le> ?SUM\<close>
    using member_tw_app_le[of \<open>?A ! i\<close> ?A ?ws ?ds, where ys = \<open>[]\<close>] nth_mem[OF il]
      member_le_sum_list[of \<open>term_weight ?ws ?ds (?A ! i)\<close> \<open>map (term_weight ?ws ?ds) (?D @ ?A)\<close>] by simp
  have Licost: \<open>length (fst Li) \<le> lcost ?ws Li\<close> by (rule length_le_lcost)
  have budget: \<open>length (fst Li) + 2 * term_weight ?ws ?ds (?A ! i) < 2 ^ 64\<close>
  proof -
    have \<open>lcost ?ws Li \<le> lcost ?ws ?L0 + 800 * sum_list (map (term_weight ?ws ?ds) (take i ?A))\<close>
      using lasserts_cost[OF assms(1) ile I1 f Bi] by simp
    moreover have \<open>lcost ?ws ?L0 \<le> 800 * sum_list (map (term_weight ?ws ?ds) ?D)\<close>
      using ldefs_cost[OF assms(1) order_refl feq B0] by (simp add: ldefs_res_def take_all)
    ultimately have \<open>length (fst Li) \<le> 800 * (sum_list (map (term_weight ?ws ?ds) ?D) + sum_list (map (term_weight ?ws ?ds) (take i ?A)))\<close>
      using Licost by simp
    moreover have \<open>sum_list (map (term_weight ?ws ?ds) ?D) + sum_list (map (term_weight ?ws ?ds) (take i ?A)) \<le> ?SUM\<close>
      using sum_list_take_app_le[of \<open>term_weight ?ws ?ds\<close> i ?A \<open>[]\<close>] by simp
    ultimately have \<open>length (fst Li) + 2 * term_weight ?ws ?ds (?A ! i) \<le> 802 * ?SUM\<close>
      using twi by simp
    also have \<open>\<dots> \<le> 1000000 * ?SUM\<close> by simp
    also have \<open>\<dots> \<le> size_bound p\<close> using sb by simp
    also have \<open>\<dots> < 2 ^ 64\<close> using assms(2) by simp
    finally show ?thesis .
  qed
  have subw: \<open>\<forall>u \<in> set (subterms (?A ! i)). width ?ws ?ds u < 2 ^ 64\<close>
  proof
    fix u assume \<open>u \<in> set (subterms (?A ! i))\<close>
    then have \<open>width ?ws ?ds u \<le> term_weight ?ws ?ds (?A ! i)\<close> by (rule width_le_tw)
    also have \<open>\<dots> \<le> ?SUM\<close> using twi by simp
    also have \<open>\<dots> \<le> size_bound p\<close> using sb by simp
    also have \<open>\<dots> < 2 ^ 64\<close> using assms(2) by simp
    finally show \<open>width ?ws ?ds u < 2 ^ 64\<close> .
  qed
  have R: \<open>foldl (lasserts_step p ?dm) (?L0, []) [0..<Suc i] =
           (fst (lower_m ?ws ?dm Li (?A ! i)), csi @ [cr (snd (lower_m ?ws ?dm Li (?A ! i)))])\<close>
    using f by (simp add: lasserts_step_def split_def Let_def)
  show ?case using R lower_m_bnd[OF wti lok dmok Bi budget subw] by simp
qed

lemma prob_bnd:
  assumes \<open>problem_wt p\<close> \<open>size_bound p < 2 ^ 64\<close>
  shows \<open>bnd (fst (lasserts_res p))\<close>
  using lasserts_bnd[OF assms, of \<open>length (Problem_asserts p)\<close>] by (simp add: lasserts_res_def)


section \<open>The top-level theorem\<close>

subsection \<open>The two answers\<close>

lemma fuel_bound_ge:
  assumes \<open>encode_m p = (s, vs)\<close>
  shows \<open>fst s + 2 \<le> fuel_bound p\<close> \<open>length (snd s) + 2 \<le> fuel_bound p\<close>
    \<open>\<forall>c \<in> set (snd s). length c + 2 \<le> fuel_bound p\<close>
    \<open>\<forall>w \<in> set (cvar_widths p). w + 2 \<le> fuel_bound p\<close>
    \<open>length (cvar_widths p) + 2 \<le> fuel_bound p\<close>
  using assms by (auto intro!: fb_ge simp: fb_set_def intro: rev_image_eqI)

text \<open>No assignment csatisfies the CNF formula: no model csatisfies the problem.\<close>
lemma unsat_answer:
  assumes \<open>cproblem_wt p\<close> \<open>encode_m p = (s, vs)\<close> \<open>fst s < 2 ^ 64\<close>
    \<open>\<not> (\<exists>\<sigma>. agrees (replicate (fst s) None) \<sigma> \<and> cnf_sem \<sigma> (snd s))\<close>
  shows \<open>\<forall>m. cis_assignment p m \<longrightarrow> \<not> csatisfies p m\<close>
  using assms encode_complete[OF assms(1-3)] by (auto simp add: agrees_def)

text \<open>A total assignment csatisfies the CNF formula: the model read from it csatisfies the problem.\<close>
lemma sat_answer:
  assumes \<open>cproblem_wt p\<close> \<open>encode_m p = (s, vs)\<close> \<open>fst s < 2 ^ 64\<close>
    \<open>length a = fst s\<close> \<open>\<forall>v < length a. a ! v \<noteq> None\<close> \<open>cnf_sem (sigma_of a) (snd s)\<close>
  shows \<open>cis_assignment p (read_model_m a vs) \<and> csatisfies p (read_model_m a vs)\<close>
proof -
  have \<open>\<forall>ls \<in> set vs. lits_lt (length a) ls\<close>
    using encode_wf[OF assms(1-3)] assms(4) by simp
  then have \<open>read_model_m a vs = map (map (lit_sem (sigma_of a))) vs\<close>
    using read_model_sigma assms(5) by blast
  then show ?thesis
    using encode_sound[OF assms(1-3) assms(6)] by simp
qed

context BVSmt_ctx
begin

subsection \<open>The solver meets its contract\<close>

text \<open>The theorem: \<^const>\<open>csolve_contract\<close> holds whenever the translation's fuel covers
  \<^const>\<open>csize_bound\<close> and \<^const>\<open>csize_bound\<close> is small enough for \<^verbatim>\<open>usize\<close>. \<^const>\<open>csize_bound\<close> is defined
  in the specification from the problem alone. For a well-sorted problem it is at least
  \<^const>\<open>fuel_bound\<close> (\<open>fuel_bound_le\<close>), which the proof uses; a problem that is not well-sorted
  makes the precondition of the contract false.\<close>
theorem solve_core_spec:
  assumes \<open>csize_bound p \<le> urust_fuel\<close> \<open>csize_bound p < 2 ^ 64\<close>
  shows \<open>\<Gamma>; solve_core p \<Turnstile>\<^sub>F csolve_contract p\<close>
proof (cases \<open>cproblem_wt p\<close>)
  case True
  have assms2: \<open>fuel_bound p \<le> urust_fuel\<close> \<open>fuel_bound p < 2 ^ 64\<close>
    using fuel_bound_le[OF True] assms by simp_all
  obtain s vs where e: \<open>encode_m p = (s, vs)\<close>
    by (cases \<open>encode_m p\<close>)
  note fb = fuel_bound_ge[OF e]
  have s64: \<open>fst s < 2 ^ 64\<close>
    using fb(1) assms2(2) by simp
  have nv: \<open>unat (word_of_nat (fst s) :: 64 word) = fst s\<close>
    using s64 by (simp add: unat_of_nat_eq)
  have dpll_pre: \<open>cproblem_wt p \<Longrightarrow>
      (\<forall>c \<in> set (snd s). lits_lt (fst s) c \<and> length c + 2 \<le> urust_fuel \<and> length c < 2 ^ 64) \<and>
      length (snd s) + 2 \<le> urust_fuel \<and> length (snd s) < 2 ^ 64 \<and>
      fst s + 2 \<le> urust_fuel \<and> fst s < 2 ^ 64\<close>
    using encode_wf[OF _ e s64] fb assms2 by fastforce
  have rm_pre: \<open>cproblem_wt p \<Longrightarrow>
      (\<forall>ls \<in> set vs. lits_lt (fst s) ls \<and> length ls + 2 \<le> urust_fuel \<and> length ls < 2 ^ 64) \<and>
      length vs + 2 \<le> urust_fuel \<and> length vs < 2 ^ 64\<close>
  proof -
    assume cwt: \<open>cproblem_wt p\<close>
    note w = encode_wf[OF cwt e s64]
    have \<open>\<forall>ls \<in> set vs. length ls + 2 \<le> fuel_bound p\<close>
      using w fb(4) by (auto simp add: in_set_conv_nth cvar_widths_def) (blast intro: nth_mem)
    moreover have \<open>length vs + 2 \<le> fuel_bound p\<close>
      using w fb(5) by (simp add: cvar_widths_def)
    ultimately show ?thesis
      using w assms2 by fastforce
  qed
  show ?thesis
    apply (crush_boot f: solve_core_def contract: csolve_contract_def)
    apply (crush_base specs add: encode_spec dpll_top_spec read_model_spec
        contracts add: encode_contract_def dpll_top_contract_def read_model_contract_def
        split: option.splits
        simp add: e assms2 nv Cnf_Cnf_clauses_lens_view_update_modify Cnf_Cnf_num_vars_lens_view_update_modify)
    using assms2 dpll_pre rm_pre unsat_answer[OF _ e s64] sat_answer[OF _ e s64]
    by (auto simp: cis_model_def split: option.splits)
next
  case False
  show ?thesis
    apply (crush_boot f: solve_core_def contract: csolve_contract_def)
    using False by simp
qed

section \<open>Each step of the problem loop meets \<open>lower\<close>'s contract\<close>

text \<open>For every definition and assertion, the recursion depth is within the fuel and the rewriting
  precondition \<^const>\<open>lpre\<close> holds, because both are bounded by the weight of the term, hence by
  \<^const>\<open>size_bound\<close>.\<close>
lemma ldefs_step_pre:
  assumes \<open>problem_wt p\<close> \<open>size_bound p \<le> urust_fuel\<close> \<open>size_bound p < 2 ^ 64\<close> \<open>j < length (Problem_defs p)\<close>
  shows \<open>Suc (size (Problem_defs p ! j)) \<le> urust_fuel \<and>
         lpre urust_fuel (var_widths p) (snd (foldl (ldefs_step p) (([], []), []) [0..<j]))
           (fst (foldl (ldefs_step p) (([], []), []) [0..<j])) (Problem_defs p ! j) \<and>
         snd (lower_m (var_widths p) (snd (foldl (ldefs_step p) (([], []), []) [0..<j]))
           (fst (foldl (ldefs_step p) (([], []), []) [0..<j])) (Problem_defs p ! j)) < 2 ^ 64\<close>
proof -
  let ?ws = \<open>var_widths p\<close> and ?D = \<open>Problem_defs p\<close> and ?A = \<open>Problem_asserts p\<close>
  let ?ds = \<open>def_widths ?ws [] ?D\<close>
  let ?dsj = \<open>def_widths ?ws [] (take j ?D)\<close>
  let ?SUM = \<open>sum_list (map (term_weight ?ws ?ds) (?D @ ?A))\<close>
  obtain Lj dmj where f: \<open>foldl (ldefs_step p) (([], []), []) [0..<j] = (Lj, dmj)\<close>
    by (cases \<open>foldl (ldefs_step p) (([], []), []) [0..<j]\<close>)
  have jl: \<open>j < length ?D\<close> and jle: \<open>j \<le> length ?D\<close> using assms(4) by simp_all
  have dwt: \<open>defs_wt ?ws [] ?D\<close> using assms(1) by (simp add: problem_wt_def Let_def)
  have Bj: \<open>bnd Lj\<close> using ldefs_bnd[OF assms(1,3) jle] f by simp
  have inv: \<open>ldefs_inv p j (Lj, dmj)\<close> using ldefs_loop[OF dwt jle f Bj] .
  have lok: \<open>lok ?ws Lj\<close> and dmok: \<open>dm_ok ?dsj dmj Lj\<close> using inv by (simp_all add: ldefs_inv_def Let_def)
  have wtj: \<open>wt ?ws ?dsj (?D ! j)\<close> using defs_wt_nth[OF dwt jl] .
  have R: \<open>foldl (ldefs_step p) (([], []), []) [0..<Suc j] =
           (fst (lower_m ?ws dmj Lj (?D ! j)), dmj @ [snd (lower_m ?ws dmj Lj (?D ! j))])\<close>
    using f by (simp add: ldefs_step_def split_def Let_def)
  have Bsuc: \<open>bnd (fst (lower_m ?ws dmj Lj (?D ! j)))\<close> using ldefs_bnd[OF assms(1,3), of \<open>Suc j\<close>] R assms(4) by simp
  have sb: \<open>1000000 * ?SUM \<le> size_bound p\<close> using size_bound_sum by simp
  have twj: \<open>term_weight ?ws ?dsj (?D ! j) \<le> ?SUM\<close>
    using term_weight_take[OF dwt jl] member_tw_app_le[of \<open>?D ! j\<close> ?D ?ws ?ds ?A] nth_mem[OF jl] by simp
  have twle: \<open>term_weight ?ws ?dsj (?D ! j) \<le> urust_fuel\<close> using twj sb assms(2) by simp
  have sz: \<open>Suc (size (?D ! j)) \<le> urust_fuel\<close> using size_le_tw[of \<open>?D ! j\<close> ?ws ?dsj] twle by simp
  have subw: \<open>\<forall>u \<in> set (subterms (?D ! j)). width ?ws ?dsj u \<le> urust_fuel\<close>
  proof
    fix u assume \<open>u \<in> set (subterms (?D ! j))\<close>
    then have \<open>width ?ws ?dsj u \<le> term_weight ?ws ?dsj (?D ! j)\<close> by (rule width_le_tw)
    then show \<open>width ?ws ?dsj u \<le> urust_fuel\<close> using twle by simp
  qed
  have lp: \<open>lpre urust_fuel ?ws dmj Lj (?D ! j)\<close> using lpre_intro[OF wtj lok dmok Bsuc subw] .
  have kb: \<open>snd (lower_m ?ws dmj Lj (?D ! j)) < 2 ^ 64\<close>
    using lower_m_correct[OF wtj lok dmok _ Bsuc] by (simp add: env_ok_def)
  show ?thesis using sz lp kb f by simp
qed

lemma lasserts_step_pre:
  assumes \<open>problem_wt p\<close> \<open>size_bound p \<le> urust_fuel\<close> \<open>size_bound p < 2 ^ 64\<close> \<open>i < length (Problem_asserts p)\<close>
  shows \<open>Suc (size (Problem_asserts p ! i)) \<le> urust_fuel \<and>
         lpre urust_fuel (var_widths p) (snd (ldefs_res p))
           (fst (foldl (lasserts_step p (snd (ldefs_res p))) (fst (ldefs_res p), []) [0..<i])) (Problem_asserts p ! i) \<and>
         snd (lower_m (var_widths p) (snd (ldefs_res p))
           (fst (foldl (lasserts_step p (snd (ldefs_res p))) (fst (ldefs_res p), []) [0..<i])) (Problem_asserts p ! i)) < 2 ^ 64\<close>
proof -
  let ?ws = \<open>var_widths p\<close> and ?D = \<open>Problem_defs p\<close> and ?A = \<open>Problem_asserts p\<close>
  let ?ds = \<open>def_widths ?ws [] ?D\<close>
  let ?SUM = \<open>sum_list (map (term_weight ?ws ?ds) (?D @ ?A))\<close>
  let ?dm = \<open>snd (ldefs_res p)\<close> and ?L0 = \<open>fst (ldefs_res p)\<close>
  obtain Li csi where f: \<open>foldl (lasserts_step p ?dm) (?L0, []) [0..<i] = (Li, csi)\<close>
    by (cases \<open>foldl (lasserts_step p ?dm) (?L0, []) [0..<i]\<close>)
  have il: \<open>i < length ?A\<close> and ile: \<open>i \<le> length ?A\<close> using assms(4) by simp_all
  have dwt: \<open>defs_wt ?ws [] ?D\<close> using assms(1) by (simp add: problem_wt_def Let_def)
  have B0: \<open>bnd ?L0\<close> using ldefs_bnd[OF assms(1,3), of \<open>length ?D\<close>] by (simp add: ldefs_res_def)
  have feq: \<open>foldl (ldefs_step p) (([], []), []) [0..<length ?D] = (?L0, ?dm)\<close>
    by (simp add: ldefs_res_def)
  have I1: \<open>ldefs_inv p (length ?D) (?L0, ?dm)\<close>
    using ldefs_loop[OF dwt order_refl feq B0] .
  have Bi: \<open>bnd Li\<close> using lasserts_bnd[OF assms(1,3) ile] f by simp
  have inv: \<open>lasserts_inv p ?dm ?L0 i (Li, csi)\<close> using lasserts_loop[OF assms(1) ile I1 f Bi] .
  have lok: \<open>lok ?ws Li\<close> using inv lext_lok by (simp add: lasserts_inv_def Let_def) blast
  have dmok: \<open>dm_ok ?ds ?dm Li\<close>
  proof -
    have lx: \<open>lext ?ws ?L0 Li\<close> using inv by (simp add: lasserts_inv_def Let_def)
    have lok0: \<open>lok ?ws ?L0\<close> using I1 by (simp add: ldefs_inv_def Let_def)
    have dmok0: \<open>dm_ok ?ds ?dm ?L0\<close> using I1 by (simp add: ldefs_inv_def Let_def take_all)
    show ?thesis using dm_ok_lext[OF lok0 dmok0 lx] .
  qed
  have wti: \<open>wt ?ws ?ds (?A ! i)\<close> using assms(1) il by (simp add: problem_wt_def Let_def)
  have R: \<open>foldl (lasserts_step p ?dm) (?L0, []) [0..<Suc i] =
           (fst (lower_m ?ws ?dm Li (?A ! i)), csi @ [cr (snd (lower_m ?ws ?dm Li (?A ! i)))])\<close>
    using f by (simp add: lasserts_step_def split_def Let_def)
  have Bsuc: \<open>bnd (fst (lower_m ?ws ?dm Li (?A ! i)))\<close>
    using lasserts_bnd[OF assms(1,3), of \<open>Suc i\<close>] R assms(4) by simp
  have sb: \<open>1000000 * ?SUM \<le> size_bound p\<close> using size_bound_sum by simp
  have twi: \<open>term_weight ?ws ?ds (?A ! i) \<le> ?SUM\<close>
    using member_le_sum_list[of \<open>term_weight ?ws ?ds (?A ! i)\<close> \<open>map (term_weight ?ws ?ds) (?D @ ?A)\<close>] nth_mem[OF il] by simp
  have twle: \<open>term_weight ?ws ?ds (?A ! i) \<le> urust_fuel\<close> using twi sb assms(2) by simp
  have sz: \<open>Suc (size (?A ! i)) \<le> urust_fuel\<close> using size_le_tw[of \<open>?A ! i\<close> ?ws ?ds] twle by simp
  have subw: \<open>\<forall>u \<in> set (subterms (?A ! i)). width ?ws ?ds u \<le> urust_fuel\<close>
  proof
    fix u assume \<open>u \<in> set (subterms (?A ! i))\<close>
    then have \<open>width ?ws ?ds u \<le> term_weight ?ws ?ds (?A ! i)\<close> by (rule width_le_tw)
    then show \<open>width ?ws ?ds u \<le> urust_fuel\<close> using twle by simp
  qed
  have lp: \<open>lpre urust_fuel ?ws ?dm Li (?A ! i)\<close> using lpre_intro[OF wti lok dmok Bsuc subw] .
  have kb: \<open>snd (lower_m ?ws ?dm Li (?A ! i)) < 2 ^ 64\<close>
    using lower_m_correct[OF wti lok dmok _ Bsuc] by (simp add: env_ok_def)
  show ?thesis using sz lp kb f by simp
qed


subsection \<open>\<^verbatim>\<open>lower_problem\<close> computes the core problem\<close>

definition lp_pre :: \<open>Problem \<Rightarrow> bool\<close> where
  \<open>lp_pre p \<equiv> problem_wt p \<and> size_bound p \<le> urust_fuel \<and> size_bound p < 2 ^ 64\<close>

lemma lp_lens:
  assumes \<open>lp_pre p\<close>
  shows \<open>length (Problem_defs p) \<le> urust_fuel\<close> \<open>length (Problem_defs p) < 2 ^ 64\<close>
    \<open>length (Problem_asserts p) \<le> urust_fuel\<close> \<open>length (Problem_asserts p) < 2 ^ 64\<close>
proof -
  have \<open>length (Problem_defs p) \<le> size_bound p\<close> \<open>length (Problem_asserts p) \<le> size_bound p\<close>
    by (simp_all add: size_bound_def Let_def)
  then show \<open>length (Problem_defs p) \<le> urust_fuel\<close> \<open>length (Problem_defs p) < 2 ^ 64\<close>
    \<open>length (Problem_asserts p) \<le> urust_fuel\<close> \<open>length (Problem_asserts p) < 2 ^ 64\<close>
    using assms by (auto simp add: lp_pre_def)
qed

definition lower_problem_contract :: \<open>Problem \<Rightarrow> ('s, CoreProblem, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>lower_problem_contract p \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>lp_pre p\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = lower_problem_m p\<rangle>)\<close>

text \<open>The rewriting of a problem only calls \<^const>\<open>lower\<close> and builds references with \<^const>\<open>cref\<close>;
  narrow the automation to those two specifications so the loop proofs stay fast.\<close>
declare dpll_lit_value_spec dpll_clause_status_spec dpll_propagate_pass_spec dpll_propagate_spec dpll_find_unassigned_spec dpll_top_spec dpll_read_bits_spec read_model_spec push_def_spec cnot_spec cbin_spec cite_spec cextract_spec cone_spec cneg_spec cmsb_spec cabs_spec cslt_spec csle_spec lower_bin_spec lit_const_spec lit_neg_spec fresh_fn_spec add_clause_spec clause3_spec clause2_spec gate_and_spec clause1_spec gate_or_spec gate_xor_spec gate_ite_spec gate_bitwise_spec bv_not_spec bv_const_spec bv_of_nat_spec bv_shift_const_spec bv_zext_spec bv_extract_spec bv_concat_spec bv_fresh_spec bv_bitwise_spec bv_add_spec bv_partial_spec bv_mul_spec bv_eq_spec bv_ult_spec bv_ite_spec bv_shift_spec bv_divrem_spec blast_bin_spec blast_spec encode_spec [crush_specs del]

lemma lower_problem_spec [crush_specs]:
  shows \<open>\<Gamma>; lower_problem p \<Turnstile>\<^sub>F lower_problem_contract p\<close>
proof (cases \<open>lp_pre p\<close>)
  case True
  note pre = True[unfolded lp_pre_def]
  note L = lp_lens[OF True]
  note SP = ldefs_step_pre[OF conjunct1[OF pre] conjunct1[OF conjunct2[OF pre]] conjunct2[OF conjunct2[OF pre]],
      folded ldefs_part_def]
  note AP = lasserts_step_pre[OF conjunct1[OF pre] conjunct1[OF conjunct2[OF pre]] conjunct2[OF conjunct2[OF pre]],
      folded lasserts_part_def]
  note SPc = SP[THEN conjunct1] SP[THEN conjunct2, THEN conjunct1] SP[THEN conjunct2, THEN conjunct2]
  note APc = AP[THEN conjunct1] AP[THEN conjunct2, THEN conjunct1] AP[THEN conjunct2, THEN conjunct2]
  have num64: \<open>(2::nat) ^ 64 = 18446744073709551616\<close> by simp
  have lonil: \<open>lower_of ([], []) = make_Lower [] []\<close> by (simp add: lower_of_def)
  have I1: \<open>\<And>j. j < length (Problem_defs p) \<Longrightarrow> j < 18446744073709551615\<close> using L(2)[unfolded num64] by linarith
  have I2: \<open>\<And>i. i < length (Problem_asserts p) \<Longrightarrow> i < 18446744073709551615\<close> using L(4)[unfolded num64] by linarith
  note I = I1 I2
  have U1: \<open>\<And>j. j < length (Problem_defs p) \<Longrightarrow>
      unat (word64_of_nat (snd (lower_m (var_widths p) (snd (ldefs_part p j)) (fst (ldefs_part p j)) (Problem_defs p ! j))) :: 64 word)
      = snd (lower_m (var_widths p) (snd (ldefs_part p j)) (fst (ldefs_part p j)) (Problem_defs p ! j))\<close>
    by (rule unat_of_nat_64'[OF SPc(3)[unfolded num64]])
  have U2: \<open>unat (word64_of_nat (length (Problem_defs p)) :: 64 word) = length (Problem_defs p)\<close>
    using L(2)[unfolded num64] by (rule unat_of_nat_64')
  have U3: \<open>unat (word64_of_nat (length (Problem_asserts p)) :: 64 word) = length (Problem_asserts p)\<close>
    using L(4)[unfolded num64] by (rule unat_of_nat_64')
  show ?thesis
    apply (crush_boot f: lower_problem_def contract: lower_problem_contract_def)
    apply (crush_base inline: len_def simp add: lower_of_def)
    subgoal for l_ref dm_ref j_ref
      apply (ucincl_discharge\<open>rule_tac
        INV=\<open>\<lambda>c. \<Squnion>gl gd dm gj j. l_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>(lower_of (fst (ldefs_part p (unat j)))) \<star> dm_ref \<mapsto>\<langle>\<top>\<rangle> gd\<down>dm \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star>
             can_alloc_reference \<star>
             \<langle>unat j \<le> length (Problem_defs p) \<and>
              map unat dm = snd (ldefs_part p (unat j)) \<and> length (Problem_defs p) - unat j \<le> c\<rangle>\<close> and
        INV'=\<open>\<lambda>c. \<Squnion>gl gd dm gj j. l_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>(lower_of (fst (ldefs_part p (unat j)))) \<star> dm_ref \<mapsto>\<langle>\<top>\<rangle> gd\<down>dm \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star>
             can_alloc_reference \<star>
             \<langle>unat j < length (Problem_defs p) \<and>
              map unat dm = snd (ldefs_part p (unat j)) \<and> length (Problem_defs p) - unat j \<le> Suc c\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_bounded_while_framedI\<close>)
      apply (crush_base inline: vec_push_def len_def
          simp add: word_less_nat_alt unat_of_nat_eq unat_of_nat_64 unat_word_Suc_simp L I U1 U2 U3 SPc unat_of_nat_64' antisym_conv split_def lonil num64 var_widths_def[symmetric])
      subgoal for gl gd dm gj j asserts_ref i_ref
        apply (ucincl_discharge\<open>rule_tac
          INV=\<open>\<lambda>c. \<Squnion>gl gd dm gj j ga asl gi i. l_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>(lower_of (fst (lasserts_part p (unat i)))) \<star> dm_ref \<mapsto>\<langle>\<top>\<rangle> gd\<down>dm \<star>
               j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> asserts_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>asl \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i \<le> length (Problem_asserts p) \<and> map unat dm = snd (ldefs_res p) \<and>
                asl = snd (lasserts_part p (unat i)) \<and>
                length (Problem_asserts p) - unat i \<le> c\<rangle>\<close> and
          INV'=\<open>\<lambda>c. \<Squnion>gl gd dm gj j ga asl gi i. l_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>(lower_of (fst (lasserts_part p (unat i)))) \<star> dm_ref \<mapsto>\<langle>\<top>\<rangle> gd\<down>dm \<star>
               j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> asserts_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>asl \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i < length (Problem_asserts p) \<and> map unat dm = snd (ldefs_res p) \<and>
                asl = snd (lasserts_part p (unat i)) \<and>
                length (Problem_asserts p) - unat i \<le> Suc c\<rangle>\<close> and
          \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
          in wp_bounded_while_framedI\<close>)
        apply (crush_base inline: vec_push_def len_def
            simp add: word_less_nat_alt unat_of_nat_eq unat_of_nat_64 unat_word_Suc_simp L I U1 U2 U3 APc unat_of_nat_64' cr_def antisym_conv split_def lonil num64 var_widths_def[symmetric])
        apply (simp_all add: lower_problem_m_eq lasserts_part_res ldefs_part_res lower_of_def U1 U2 U3)
        done
      done
    done
next
  case False
  then have F: \<open>lp_pre p = False\<close> by simp
  show ?thesis
    apply (ucincl_discharge\<open>intro satisfies_function_contractI\<close>)
    apply (subst wp_sstriple_iff)
    apply (simp add: lower_problem_contract_def F apure_precise_False asepconj_bot_zero2 bot_aentails_all)
    done
qed

subsection \<open>\<^verbatim>\<open>solve\<close> meets the specification's contract on the extended problem\<close>

text \<open>The top-level theorem: \<^const>\<open>solve\<close> meets \<^const>\<open>solve_contract\<close> of the specification (Sat yields a
  model, Unsat rules out every model, well-sortedness as precondition) whenever the translation's
  fuel covers \<^const>\<open>size_bound\<close>, which is expressed on the problem alone.\<close>
text \<open>\<^const>\<open>solve\<close> only calls \<^const>\<open>lower_problem\<close> and \<^const>\<open>solve_core\<close>; narrow the
  automation's specification set to those so its proof stays fast.\<close>
declare lower_spec cref_spec lower_problem_spec [crush_specs del]

theorem solve_spec:
  assumes \<open>size_bound p \<le> urust_fuel\<close> \<open>size_bound p < 2 ^ 64\<close>
  shows \<open>\<Gamma>; solve p \<Turnstile>\<^sub>F solve_contract p\<close>
proof (cases \<open>problem_wt p\<close>)
  case True
  have bnd: \<open>bnd (fst (lasserts_res p))\<close> using prob_bnd[OF True assms(2)] .
  \<comment> \<open>Abstract the rewritten problem to a variable, so the automation works on a small goal
      instead of the (very large) unfolded \<^term>\<open>lower_problem_m p\<close>.\<close>
  obtain q where q: \<open>lower_problem_m p = q\<close> by blast
  have sz: \<open>csize_bound q \<le> urust_fuel\<close> using lower_size_bound[OF True bnd] assms(1) q by simp
  have sz2: \<open>csize_bound q < 2 ^ 64\<close> using lower_size_bound[OF True bnd] assms(2) q by simp
  have cwt: \<open>cproblem_wt q\<close> using lower_problem_correct(1)[OF True bnd] q by simp
  have cm: \<open>cis_model q m = is_model p m\<close> for m using lower_problem_correct(2)[OF True bnd] q by simp
  show ?thesis
    apply (crush_boot f: solve_def contract: solve_contract_def)
    apply (crush_base specs add: lower_problem_spec solve_core_spec[OF sz sz2]
        contracts add: lower_problem_contract_def csolve_contract_def
        simp add: lp_pre_def True assms q cwt)
    using cm assms by (auto split: Answer.splits)
next
  case False
  then have F: \<open>problem_wt p = False\<close> by simp
  show ?thesis
    apply (ucincl_discharge\<open>intro satisfies_function_contractI\<close>)
    apply (subst wp_sstriple_iff)
    apply (simp add: solve_contract_def Let_def F apure_precise_False asepconj_bot_zero2 bot_aentails_all)
    done
qed
end

subsection \<open>The specification over all instances with enough fuel\<close>

context BVSmt_heap
begin

text \<open>\<^verbatim>\<open>BVSmt_heap\<close> has the assumptions of \<^locale>\<open>BVSmt_ctx\<close> (it drops only the fuel, which carries
  no assumption), so its parameters with any fuel form an instance of \<^locale>\<open>BVSmt_ctx\<close> and the
  contract lemmas of \<^locale>\<open>BVSmt_ctx\<close> apply.\<close>
lemma BVSmt_ctxI:
  \<open>BVSmt_ctx update_raw_fun dereference_raw_fun reference_raw_fun points_to_raw' gref_can_store
     new_gref_can_store can_alloc_reference prism_1 prism_2 prism_3 prism_4 prism_5 prism_6
     prism_7 prism_8 prism_9 prism_10 prism_11 prism_12 prism_13 prism_14 prism_15 prism_16 prism_17\<close>
  by intro_locales

text \<open>The statement of the specification, \<^const>\<open>solve_correct\<close> in \<^verbatim>\<open>BVSmt_Spec\<close>. The bound on
  the fuel is \<^const>\<open>size_bound\<close> \<open>p\<close>, which \<open>BVSmt_ctx.solve_spec\<close> needs; \<^const>\<open>sizes_ok\<close> \<open>p\<close>
  supplies its \<open>< 2 ^ 64\<close> hypothesis.\<close>
theorem solve_correct:
  shows \<open>solve_correct \<Gamma>\<close>
proof (unfold solve_correct_def, intro allI impI)
  fix p :: Problem
  assume \<open>problem_wt p \<and> sizes_ok p\<close>
  then have ov: \<open>size_bound p < 2 ^ 64\<close> by (simp add: sizes_ok_def)
  have \<open>\<Gamma>; solve fuel p \<Turnstile>\<^sub>F solve_contract p\<close> if \<open>size_bound p \<le> fuel\<close> for fuel
    by (rule BVSmt_ctx.solve_spec[OF BVSmt_ctxI that ov])
  then show \<open>\<exists>N. \<forall>fuel \<ge> N. \<Gamma>; solve fuel p \<Turnstile>\<^sub>F solve_contract p\<close>
    by (intro exI[of _ \<open>size_bound p\<close>]) simp
qed

end

end
