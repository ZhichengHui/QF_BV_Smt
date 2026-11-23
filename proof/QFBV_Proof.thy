theory QFBV_Proof
  imports QFBV_Refine QFBV_Eval QFBV_Encode QFBV_Dpll QFBV_Bound QFBV_LowerRefine QFBV_LowerBound QFBV_LowerCount QFBV_ElimSpec
begin

text \<open>The proofs below use the equations of \<^const>\<open>lower_m\<close> of \<^verbatim>\<open>QFBV_LowerRefine\<close>; importing
  \<^verbatim>\<open>QFBV_ElimSpec\<close> (through \<^verbatim>\<open>QFBV_Elim\<close>) brings back the original ones.\<close>
declare lower_m.simps(4-13) [simp del]

lemma lin1: \<open>1 \<le> w + 1\<close> for w :: nat
  by simp

lemma lin2: \<open>x \<le> y \<Longrightarrow> x + 1 \<le> 2 * (y + 1)\<close> for x y :: nat
  by simp

lemma ob_arith:
  assumes \<open>4 * (1 + w + a + b + c + (4 * S + E)) < (2::nat) ^ 56\<close>
  shows \<open>L \<le> E \<Longrightarrow> 2 + w + c + L < 2 ^ 56\<close> \<open>a < 2 ^ 56\<close> \<open>c < 2 ^ 56\<close> \<open>n \<le> 2 * S \<Longrightarrow> n < 2 ^ 56\<close>
  using assms by simp_all

lemma tb_arith:
  \<open>T \<le> 2 * (2 * S) + 52 \<Longrightarrow> 4 * (1 + a + b + c + d + (4 * S + E)) < (2::nat) ^ 56 \<Longrightarrow> T < 2 ^ 56\<close>
  for T S a b c d E :: nat
  by simp

lemma lw_leaf:
  \<open>lweight ws ds (TermL_Const bs) = width ws ds (TermL_Const bs) + 1\<close>
  \<open>lweight ws ds (TermL_Var i) = width ws ds (TermL_Var i) + 1\<close>
  \<open>lweight ws ds (TermL_Ref j) = width ws ds (TermL_Ref j) + 1\<close>
  by (simp_all add: lweight_def)

lemma lw_un:
  \<open>lweight ws ds (TermL_Not a) = width ws ds (TermL_Not a) + 1 + lweight ws ds a\<close>
  \<open>lweight ws ds (TermL_Neg a) = width ws ds (TermL_Neg a) + 1 + lweight ws ds a\<close>
  \<open>lweight ws ds (TermL_Extract hi lo a) = width ws ds (TermL_Extract hi lo a) + 1 + lweight ws ds a\<close>
  \<open>lweight ws ds (TermL_Repeat i a) = width ws ds (TermL_Repeat i a) + 1 + lweight ws ds a\<close>
  \<open>lweight ws ds (TermL_ZeroExtend i a) = width ws ds (TermL_ZeroExtend i a) + 1 + lweight ws ds a\<close>
  \<open>lweight ws ds (TermL_SignExtend i a) = width ws ds (TermL_SignExtend i a) + 1 + lweight ws ds a\<close>
  \<open>lweight ws ds (TermL_RotateLeft i a) = width ws ds (TermL_RotateLeft i a) + 1 + lweight ws ds a\<close>
  \<open>lweight ws ds (TermL_RotateRight i a) = width ws ds (TermL_RotateRight i a) + 1 + lweight ws ds a\<close>
  by (simp_all add: lweight_def)

lemma lw_Bin:
  \<open>lweight ws ds (TermL_Bin op a b) = width ws ds (TermL_Bin op a b) + 1 + lweight ws ds a + lweight ws ds b\<close>
  by (simp add: lweight_def)

lemma lw_Ite:
  \<open>lweight ws ds (TermL_Ite c a b) = width ws ds (TermL_Ite c a b) + 1 + lweight ws ds c + lweight ws ds a + lweight ws ds b\<close>
  by (simp add: lweight_def)

section \<open>Bounds relating the size of a term to its weight\<close>

text \<open>The recursion depth \<open>Suc (size t)\<close> and the width of any subterm are bounded by the weight of
  the term, hence by \<^const>\<open>size_bound\<close>.\<close>
lemma size_le_len_sub: \<open>Suc (size t) \<le> length (subterms t)\<close>
  by (induction t) auto

lemma len_le_linsum: \<open>length xs \<le> sum_list (map (\<lambda>u. (width ws ds u + 1)) xs)\<close>
proof (induction xs)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  show ?case using add_le_mono[OF lin1[of \<open>width ws ds x\<close>] Cons.IH] by simp
qed

lemma len_sub_le_tw: \<open>length (subterms t) \<le> lweight ws ds t\<close>
  using len_le_linsum[of \<open>subterms t\<close>] by (simp add: lweight_def)

lemma size_le_tw: \<open>Suc (size t) \<le> lweight ws ds t\<close>
  using size_le_len_sub[of t] len_sub_le_tw[of t ws ds] by simp

lemma width_le_tw:
  assumes \<open>u \<in> set (subterms t)\<close>
  shows \<open>width ws ds u \<le> lweight ws ds t\<close>
proof -
  have \<open>width ws ds u \<le> (width ws ds u + 1)\<close>
    by simp
  also have \<open>(width ws ds u + 1) \<le> lweight ws ds t\<close>
    unfolding lweight_def using assms by (intro member_le_sum_list; simp)
  finally show ?thesis .
qed

section \<open>A length bound on the rewriting, free of \<open>bnd\<close>\<close>

text \<open>\<^verbatim>\<open>lower_m_cost\<close> assumes \<^const>\<open>bnd\<close> of its result; to establish \<^const>\<open>bnd\<close> in the first
  place, this purely structural bound counts the definitions the rewriting adds, with no
  overflow assumption.\<close>

lemma lower_bin_m_len3: \<open>length (fst (fst (lower_bin_m L op ka kb))) \<le> length (fst L) + 3\<close>
  by (cases op) (simp_all add: lower_bin_m_def Let_def push_m_def split_def)

lemma lower_m_length:
  \<open>wt ws ds t \<Longrightarrow> length (fst (fst (lower_m ws dm L t))) \<le> length (fst L) + 2 * lweight ws ds t\<close>
proof (induction t arbitrary: L)
  case (TermL_Const bs)
  show ?case using lin1[of \<open>length bs\<close>] by (simp add: push_m_def lw_leaf; linarith)
next
  case (TermL_Var i)
  show ?case using lin1[of \<open>ws ! unat i\<close>] by (simp add: push_m_def lw_leaf; linarith)
next
  case (TermL_Ref j)
  show ?case by (simp add: lw_leaf; linarith)
next
  case (TermL_Not a)
  have wta: \<open>wt ws ds a\<close> using TermL_Not.prems by simp
  have ih: \<open>length (fst (fst (lower_m ws dm L a))) \<le> length (fst L) + 2 * lweight ws ds a\<close>
    using TermL_Not.IH[OF wta] by simp
  have L: \<open>length (fst (fst (lower_m ws dm L (TermL_Not a)))) = length (fst (fst (lower_m ws dm L a))) + 1\<close>
    by (simp add: push_m_def split_def)
  show ?case using ih L lin1[of \<open>width ws ds (TermL_Not a)\<close>]
    unfolding lw_un add_mult_distrib2 by linarith
next
  case (TermL_Neg a)
  have wta: \<open>wt ws ds a\<close> using TermL_Neg.prems by simp
  have ih: \<open>length (fst (fst (lower_m ws dm L a))) \<le> length (fst L) + 2 * lweight ws ds a\<close>
    using TermL_Neg.IH[OF wta] by simp
  have L: \<open>length (fst (fst (lower_m ws dm L (TermL_Neg a)))) = length (fst (fst (lower_m ws dm L a))) + 1\<close>
    by (simp add: push_m_def split_def)
  show ?case using ih L lin1[of \<open>width ws ds (TermL_Neg a)\<close>]
    unfolding lw_un add_mult_distrib2 by linarith
next
  case (TermL_Bin op a b)
  have w: \<open>wt ws ds a\<close> \<open>wt ws ds b\<close> using TermL_Bin.prems by simp_all
  have c3: \<open>3 \<le> 2 * (width ws ds (TermL_Bin op a b) + 1)\<close>
    using wt_width_pos[OF TermL_Bin.prems(1)] by simp
  have lb: \<open>length (fst (fst (lower_m ws dm L (TermL_Bin op a b)))) \<le>
           length (fst (fst (lower_m ws dm (fst (lower_m ws dm L a)) b))) + 3\<close>
    using lower_bin_m_len3[of \<open>fst (lower_m ws dm (fst (lower_m ws dm L a)) b)\<close> op
        \<open>snd (lower_m ws dm L a)\<close> \<open>snd (lower_m ws dm (fst (lower_m ws dm L a)) b)\<close>] by simp
  have \<open>length (fst (fst (lower_m ws dm L (TermL_Bin op a b)))) \<le>
        length (fst L) + 2 * lweight ws ds a + 2 * lweight ws ds b + 3\<close>
    using lb TermL_Bin.IH(2)[OF w(2), of \<open>fst (lower_m ws dm L a)\<close>] TermL_Bin.IH(1)[OF w(1), of L] by linarith
  then show ?case using c3 unfolding lw_Bin add_mult_distrib2 by linarith
next
  case (TermL_Extract hi lo a)
  have wta: \<open>wt ws ds a\<close> using TermL_Extract.prems by simp
  have ih: \<open>length (fst (fst (lower_m ws dm L a))) \<le> length (fst L) + 2 * lweight ws ds a\<close>
    using TermL_Extract.IH[OF wta] by simp
  have L: \<open>length (fst (fst (lower_m ws dm L (TermL_Extract hi lo a)))) = length (fst (fst (lower_m ws dm L a))) + 1\<close>
    by (simp add: push_m_def split_def Let_def)
  show ?case using ih L lin1[of \<open>width ws ds (TermL_Extract hi lo a)\<close>]
    unfolding lw_un add_mult_distrib2 by linarith
next
  case (TermL_Repeat i a)
  have w: \<open>wt ws ds a\<close> \<open>1 \<le> unat i\<close> using TermL_Repeat.prems by simp_all
  have wp: \<open>1 \<le> width ws ds a\<close> using wt_width_pos[OF w(1)] .
  have iW: \<open>unat i \<le> width ws ds (TermL_Repeat i a)\<close>
    using mult_le_mono2[OF wp, of \<open>unat i\<close>] by simp
  have cR: \<open>width ws ds (TermL_Repeat i a) + 1 \<le> (width ws ds (TermL_Repeat i a) + 1)\<close>
    by simp
  have L: \<open>length (fst (fst (lower_m ws dm L (TermL_Repeat i a)))) =
           length (fst (fst (lower_m ws dm L a))) + 1 + unat i\<close>
    unfolding lower_m_Repeat'' by (simp add: rep_fold_len)
  have \<open>\<dots> \<le> length (fst L) + 2 * lweight ws ds a + 1 + unat i\<close>
    using TermL_Repeat.IH[OF w(1), of L] by simp
  also have \<open>\<dots> \<le> length (fst L) + 2 * lweight ws ds (TermL_Repeat i a)\<close>
    using iW cR unfolding lw_un add_mult_distrib2 by linarith
  finally show ?case using L by simp
next
  case (TermL_ZeroExtend i a)
  have wta: \<open>wt ws ds a\<close> using TermL_ZeroExtend.prems by simp
  have ih: \<open>length (fst (fst (lower_m ws dm L a))) \<le> length (fst L) + 2 * lweight ws ds a\<close>
    using TermL_ZeroExtend.IH[OF wta] by simp
  have L: \<open>length (fst (fst (lower_m ws dm L (TermL_ZeroExtend i a)))) = length (fst (fst (lower_m ws dm L a))) + 1\<close>
    by (simp add: push_m_def split_def Let_def)
  show ?case using ih L lin1[of \<open>width ws ds (TermL_ZeroExtend i a)\<close>]
    unfolding lw_un add_mult_distrib2 by linarith
next
  case (TermL_SignExtend i a)
  have wta: \<open>wt ws ds a\<close> using TermL_SignExtend.prems by simp
  have ih: \<open>length (fst (fst (lower_m ws dm L a))) \<le> length (fst L) + 2 * lweight ws ds a\<close>
    using TermL_SignExtend.IH[OF wta] by simp
  have L: \<open>length (fst (fst (lower_m ws dm L (TermL_SignExtend i a)))) = length (fst (fst (lower_m ws dm L a))) + 1\<close>
    by (simp add: push_m_def split_def Let_def)
  show ?case using ih L lin1[of \<open>width ws ds (TermL_SignExtend i a)\<close>]
    unfolding lw_un add_mult_distrib2 by linarith
next
  case (TermL_RotateLeft i a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  have w: \<open>wt ws ds a\<close> using TermL_RotateLeft.prems by simp
  have L: \<open>length (fst (fst (lower_m ws dm L (TermL_RotateLeft i a)))) \<le> length (fst L1) + 1\<close>
    using a by (simp add: lower_m_RotateLeft' Let_def push_m_def split: if_splits)
  have ih: \<open>length (fst L1) \<le> length (fst L) + 2 * lweight ws ds a\<close>
    using TermL_RotateLeft.IH[OF w, of L] a by simp
  show ?case using L ih lin1[of \<open>width ws ds (TermL_RotateLeft i a)\<close>]
    unfolding lw_un add_mult_distrib2 by linarith
next
  case (TermL_RotateRight i a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  have w: \<open>wt ws ds a\<close> using TermL_RotateRight.prems by simp
  have L: \<open>length (fst (fst (lower_m ws dm L (TermL_RotateRight i a)))) \<le> length (fst L1) + 1\<close>
    using a by (simp add: lower_m_RotateRight' Let_def push_m_def split: if_splits)
  have ih: \<open>length (fst L1) \<le> length (fst L) + 2 * lweight ws ds a\<close>
    using TermL_RotateRight.IH[OF w, of L] a by simp
  show ?case using L ih lin1[of \<open>width ws ds (TermL_RotateRight i a)\<close>]
    unfolding lw_un add_mult_distrib2 by linarith
next
  case (TermL_Ite c a b)
  have w: \<open>wt ws ds c\<close> \<open>wt ws ds a\<close> \<open>wt ws ds b\<close> using TermL_Ite.prems by simp_all
  have \<open>length (fst (fst (lower_m ws dm L (TermL_Ite c a b)))) =
        length (fst (fst (lower_m ws dm (fst (lower_m ws dm (fst (lower_m ws dm L c)) a)) b))) + 1\<close>
    by (simp add: push_m_def)
  also have \<open>\<dots> \<le> length (fst (fst (lower_m ws dm (fst (lower_m ws dm L c)) a))) + 2 * lweight ws ds b + 1\<close>
    using TermL_Ite.IH(3)[OF w(3), of \<open>fst (lower_m ws dm (fst (lower_m ws dm L c)) a)\<close>] by simp
  also have \<open>\<dots> \<le> length (fst (fst (lower_m ws dm L c))) + 2 * lweight ws ds a + 2 * lweight ws ds b + 1\<close>
    using TermL_Ite.IH(2)[OF w(2), of \<open>fst (lower_m ws dm L c)\<close>] by simp
  also have \<open>\<dots> \<le> length (fst L) + 2 * lweight ws ds c + 2 * lweight ws ds a + 2 * lweight ws ds b + 1\<close>
    using TermL_Ite.IH(1)[OF w(1), of L] by simp
  also have \<open>\<dots> \<le> length (fst L) + 2 * lweight ws ds (TermL_Ite c a b)\<close>
    using lin1[of \<open>width ws ds (TermL_Ite c a b)\<close>] unfolding lw_Ite add_mult_distrib2 by linarith
  finally show ?case .
qed

section \<open>A width bound on the rewriting, free of \<open>bnd\<close> of the result\<close>

text \<open>Every definition the rewriting produces has a width that is the width of some subterm, and the
  number of definitions stays within the budget; so \<^const>\<open>bnd\<close> of the result follows from
  \<^const>\<open>bnd\<close> of the input, the length budget and the subterm widths, all of which the problem's
  \<^const>\<open>size_bound\<close> provides.\<close>

lemma bnd_push:
  \<open>bnd L \<Longrightarrow> w < 2 ^ 56 \<Longrightarrow> length (fst L) + 1 < 2 ^ 56 \<Longrightarrow> bnd (fst (push_m L t w))\<close>
  by (auto simp add: bnd_def push_m_def)

lemma repeat_fold_bnd:
  \<open>bnd L0 \<Longrightarrow> acc + w * j < 2 ^ 56 \<Longrightarrow> length (fst L0) + j < 2 ^ 56 \<Longrightarrow>
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
  assumes \<open>bnd L\<close> \<open>length (fst L) + 3 < 2 ^ 56\<close> \<open>snd L ! ka < 2 ^ 56\<close> \<open>snd L ! kb < 2 ^ 56\<close>
    \<open>op = Op_Concat \<longrightarrow> snd L ! ka + snd L ! kb < 2 ^ 56\<close>
  shows \<open>bnd (fst (lower_bin_m L op ka kb))\<close>
  using assms by (cases op) (auto simp add: lower_bin_m_def Let_def push_m_def bnd_def split_def)

lemma lower_m_bnd:
  \<open>wt ws ds t \<Longrightarrow> lok ws L \<Longrightarrow> dm_ok ds dm L \<Longrightarrow> bnd L \<Longrightarrow>
   length (fst L) + 2 * lweight ws ds t < 2 ^ 56 \<Longrightarrow>
   (\<forall>u \<in> set (subterms t). width ws ds u < 2 ^ 56) \<Longrightarrow>
   bnd (fst (lower_m ws dm L t))\<close>
proof (induction t arbitrary: L)
  case (TermL_Const bs)
  have wb: \<open>length bs < 2 ^ 56\<close> using TermL_Const.prems(6) by simp
  have len: \<open>length (fst L) + 1 < 2 ^ 56\<close>
    using TermL_Const.prems(5) lin1[of \<open>length bs\<close>] unfolding lw_leaf width.simps add_mult_distrib2 by linarith
  show ?case using bnd_push[OF TermL_Const.prems(4) wb len] by simp
next
  case (TermL_Var i)
  have wb: \<open>ws ! unat i < 2 ^ 56\<close> using TermL_Var.prems(6) by simp
  have len: \<open>length (fst L) + 1 < 2 ^ 56\<close>
    using TermL_Var.prems(5) lin1[of \<open>ws ! unat i\<close>] unfolding lw_leaf width.simps add_mult_distrib2 by linarith
  show ?case using bnd_push[OF TermL_Var.prems(4) wb len] by simp
next
  case (TermL_Ref j)
  then show ?case by simp
next
  case (TermL_Not a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  have wta: \<open>wt ws ds a\<close> using TermL_Not.prems(1) by simp
  have sub: \<open>\<forall>u \<in> set (subterms a). width ws ds u < 2 ^ 56\<close> using TermL_Not.prems(6) by simp
  have bud: \<open>length (fst L) + 2 * lweight ws ds a < 2 ^ 56\<close>
    using TermL_Not.prems(5) lin1[of \<open>width ws ds (TermL_Not a)\<close>] unfolding lw_un add_mult_distrib2 by linarith
  have B1: \<open>bnd L1\<close> using TermL_Not.IH[OF wta TermL_Not.prems(2,3,4) bud sub] a by simp
  have EA: \<open>QFBV_Lower.env_ok ws L1 ka (width ws ds a)\<close>
    using lower_m_correct[OF wta TermL_Not.prems(2,3) a B1] by simp
  have wa: \<open>snd L1 ! ka = width ws ds a\<close> and ka64: \<open>ka < 2 ^ 64\<close> using EA by (simp_all add: QFBV_Lower.env_ok_def)
  have wsub: \<open>snd L1 ! ka < 2 ^ 56\<close> using wa TermL_Not.prems(6) by simp
  have lena: \<open>length (fst L1) \<le> length (fst L) + 2 * lweight ws ds a\<close>
    using lower_m_length[OF wta, of dm L] a by simp
  have len: \<open>length (fst L1) + 1 < 2 ^ 56\<close>
    using lena TermL_Not.prems(5) lin1[of \<open>width ws ds (TermL_Not a)\<close>] unfolding lw_un add_mult_distrib2 by linarith
  show ?case using a bnd_push[OF B1 wsub len] by simp
next
  case (TermL_Neg a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  have wta: \<open>wt ws ds a\<close> using TermL_Neg.prems(1) by simp
  have sub: \<open>\<forall>u \<in> set (subterms a). width ws ds u < 2 ^ 56\<close> using TermL_Neg.prems(6) by simp
  have bud: \<open>length (fst L) + 2 * lweight ws ds a < 2 ^ 56\<close>
    using TermL_Neg.prems(5) lin1[of \<open>width ws ds (TermL_Neg a)\<close>] unfolding lw_un add_mult_distrib2 by linarith
  have B1: \<open>bnd L1\<close> using TermL_Neg.IH[OF wta TermL_Neg.prems(2,3,4) bud sub] a by simp
  have EA: \<open>QFBV_Lower.env_ok ws L1 ka (width ws ds a)\<close>
    using lower_m_correct[OF wta TermL_Neg.prems(2,3) a B1] by simp
  have wa: \<open>snd L1 ! ka = width ws ds a\<close> using EA by (simp add: QFBV_Lower.env_ok_def)
  have wsub: \<open>snd L1 ! ka < 2 ^ 56\<close> using wa TermL_Neg.prems(6) by simp
  have lena: \<open>length (fst L1) \<le> length (fst L) + 2 * lweight ws ds a\<close>
    using lower_m_length[OF wta, of dm L] a by simp
  have len: \<open>length (fst L1) + 1 < 2 ^ 56\<close>
    using lena TermL_Neg.prems(5) lin1[of \<open>width ws ds (TermL_Neg a)\<close>] unfolding lw_un add_mult_distrib2 by linarith
  show ?case using a bnd_push[OF B1 wsub len] by simp
next
  case (TermL_Bin op a b)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  obtain L2 kb where b: \<open>lower_m ws dm L1 b = (L2, kb)\<close> by (cases \<open>lower_m ws dm L1 b\<close>)
  have wt: \<open>wt ws ds a\<close> \<open>wt ws ds b\<close> \<open>op \<noteq> Op_Concat \<longrightarrow> width ws ds b = width ws ds a\<close>
    using TermL_Bin.prems(1) by simp_all
  have suba: \<open>\<forall>u \<in> set (subterms a). width ws ds u < 2 ^ 56\<close> using TermL_Bin.prems(6) by simp
  have subb: \<open>\<forall>u \<in> set (subterms b). width ws ds u < 2 ^ 56\<close> using TermL_Bin.prems(6) by simp
  have buda: \<open>length (fst L) + 2 * lweight ws ds a < 2 ^ 56\<close>
    using TermL_Bin.prems(5) lin1[of \<open>width ws ds (TermL_Bin op a b)\<close>] unfolding lw_Bin add_mult_distrib2 by linarith
  have B1: \<open>bnd L1\<close> using TermL_Bin.IH(1)[OF wt(1) TermL_Bin.prems(2,3,4) buda suba] a by simp
  have Sa: \<open>QFBV_Lower.env_ok ws L1 ka (width ws ds a) \<and> lok ws L1 \<and> lext ws L L1\<close>
    using lower_m_correct[OF wt(1) TermL_Bin.prems(2,3) a B1] lext_lok by blast
  have L1: \<open>lok ws L1\<close> and X1: \<open>lext ws L L1\<close> using Sa by blast+
  have D1: \<open>dm_ok ds dm L1\<close> using dm_ok_lext[OF TermL_Bin.prems(2,3) X1] .
  have lena: \<open>length (fst L1) \<le> length (fst L) + 2 * lweight ws ds a\<close>
    using lower_m_length[OF wt(1), of dm L] a by simp
  have budb: \<open>length (fst L1) + 2 * lweight ws ds b < 2 ^ 56\<close>
    using lena TermL_Bin.prems(5) lin1[of \<open>width ws ds (TermL_Bin op a b)\<close>] unfolding lw_Bin add_mult_distrib2 by linarith
  have B2: \<open>bnd L2\<close> using TermL_Bin.IH(2)[OF wt(2) L1 D1 B1 budb subb] b by simp
  have EA: \<open>QFBV_Lower.env_ok ws L2 ka (width ws ds a)\<close>
    using lower_m_correct[OF wt(1) TermL_Bin.prems(2,3) a B1] lower_m_correct[OF wt(2) L1 D1 b B2] env_lext by blast
  have EB: \<open>QFBV_Lower.env_ok ws L2 kb (width ws ds b)\<close>
    using lower_m_correct[OF wt(2) L1 D1 b B2] by simp
  have wa: \<open>snd L2 ! ka = width ws ds a\<close> and wb: \<open>snd L2 ! kb = width ws ds b\<close>
    using EA EB by (simp_all add: QFBV_Lower.env_ok_def)
  have selfa: \<open>a \<in> set (subterms a)\<close> by (cases a) auto
  have selfb: \<open>b \<in> set (subterms b)\<close> by (cases b) auto
  have wa64: \<open>snd L2 ! ka < 2 ^ 56\<close> using wa bspec[OF suba selfa] by simp
  have wb64: \<open>snd L2 ! kb < 2 ^ 56\<close> using wb bspec[OF subb selfb] by simp
  have cc: \<open>op = Op_Concat \<longrightarrow> snd L2 ! ka + snd L2 ! kb < 2 ^ 56\<close>
  proof
    assume \<open>op = Op_Concat\<close>
    then have \<open>snd L2 ! ka + snd L2 ! kb = width ws ds (TermL_Bin op a b)\<close> using wa wb by simp
    then show \<open>snd L2 ! ka + snd L2 ! kb < 2 ^ 56\<close> using TermL_Bin.prems(6) by simp
  qed
  have lenb: \<open>length (fst L2) \<le> length (fst L) + 2 * lweight ws ds a + 2 * lweight ws ds b\<close>
    using lower_m_length[OF wt(2), of dm L1] b lena by simp
  have c3: \<open>3 \<le> 2 * (width ws ds (TermL_Bin op a b) + 1)\<close>
    using wt_width_pos[OF TermL_Bin.prems(1)] by simp
  have len3: \<open>length (fst L2) + 3 < 2 ^ 56\<close>
    using lenb TermL_Bin.prems(5) c3 unfolding lw_Bin add_mult_distrib2 by linarith
  have R: \<open>lower_m ws dm L (TermL_Bin op a b) = lower_bin_m L2 op ka kb\<close> using a b by simp
  show ?case using R lower_bin_m_bnd[OF B2 len3 wa64 wb64 cc] by simp
next
  case (TermL_Extract hi lo a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  have wt: \<open>wt ws ds a\<close> \<open>unat lo \<le> unat hi\<close> \<open>unat hi < width ws ds a\<close> using TermL_Extract.prems(1) by simp_all
  have sub: \<open>\<forall>u \<in> set (subterms a). width ws ds u < 2 ^ 56\<close> using TermL_Extract.prems(6) by simp
  have bud: \<open>length (fst L) + 2 * lweight ws ds a < 2 ^ 56\<close>
    using TermL_Extract.prems(5) lin1[of \<open>width ws ds (TermL_Extract hi lo a)\<close>] unfolding lw_un add_mult_distrib2 by linarith
  have B1: \<open>bnd L1\<close> using TermL_Extract.IH[OF wt(1) TermL_Extract.prems(2,3,4) bud sub] a by simp
  have selfa: \<open>a \<in> set (subterms a)\<close> by (cases a) auto
  have wsub: \<open>unat hi - unat lo + 1 < 2 ^ 56\<close>
  proof -
    have \<open>unat hi - unat lo + 1 \<le> width ws ds a\<close> using wt(2,3) by simp
    then show ?thesis using bspec[OF sub selfa] by simp
  qed
  have lena: \<open>length (fst L1) \<le> length (fst L) + 2 * lweight ws ds a\<close>
    using lower_m_length[OF wt(1), of dm L] a by simp
  have len: \<open>length (fst L1) + 1 < 2 ^ 56\<close>
    using lena TermL_Extract.prems(5) lin1[of \<open>width ws ds (TermL_Extract hi lo a)\<close>] unfolding lw_un add_mult_distrib2 by linarith
  show ?case using a bnd_push[OF B1 wsub len] by (simp add: Let_def)
next
  case (TermL_Repeat i a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  have wt: \<open>wt ws ds a\<close> \<open>1 \<le> unat i\<close> using TermL_Repeat.prems(1) by simp_all
  have sub: \<open>\<forall>u \<in> set (subterms a). width ws ds u < 2 ^ 56\<close> using TermL_Repeat.prems(6) by simp
  have wR: \<open>width ws ds (TermL_Repeat i a) < 2 ^ 56\<close> using TermL_Repeat.prems(6) by simp
  have bud: \<open>length (fst L) + 2 * lweight ws ds a < 2 ^ 56\<close>
    using TermL_Repeat.prems(5) lin1[of \<open>width ws ds (TermL_Repeat i a)\<close>] unfolding lw_un add_mult_distrib2 by linarith
  have B1: \<open>bnd L1\<close> using TermL_Repeat.IH[OF wt(1) TermL_Repeat.prems(2,3,4) bud sub] a by simp
  have EA: \<open>QFBV_Lower.env_ok ws L1 ka (width ws ds a)\<close>
    using lower_m_correct[OF wt(1) TermL_Repeat.prems(2,3) a B1] by simp
  have wa: \<open>snd L1 ! ka = width ws ds a\<close> and L1: \<open>lok ws L1\<close> using EA by (simp_all add: QFBV_Lower.env_ok_def)
  obtain L2 k0 where p: \<open>push_m L1 (CoreTermL_Const []) 0 = (L2, k0)\<close> by (cases \<open>push_m L1 (CoreTermL_Const []) 0\<close>)
  have lenL1: \<open>length (fst L1) \<le> length (fst L) + 2 * lweight ws ds a\<close>
    using lower_m_length[OF wt(1), of dm L] a by simp
  have iW: \<open>unat i \<le> width ws ds (TermL_Repeat i a)\<close>
    using mult_le_mono2[OF wt_width_pos[OF wt(1)], of \<open>unat i\<close>] by simp
  have cR: \<open>width ws ds (TermL_Repeat i a) + 1 \<le> (width ws ds (TermL_Repeat i a) + 1)\<close>
    by simp
  have cubeW: \<open>unat i + 1 \<le> 2 * (width ws ds (TermL_Repeat i a) + 1)\<close>
    using lin2[OF iW] .
  have lenbud: \<open>length (fst L1) + 1 + unat i < 2 ^ 56\<close>
    using lenL1 TermL_Repeat.prems(5) cubeW unfolding lw_un add_mult_distrib2 by linarith
  have lb2: \<open>length (fst L1) + 1 < 2 ^ 56\<close> using lenbud by linarith
  have B2: \<open>bnd L2\<close>
    using bnd_push[OF B1 _ lb2, where t=\<open>CoreTermL_Const []\<close> and w=0] p by (simp add: push_m_def)
  have L2': \<open>L2 = fst (push_m L1 (CoreTermL_Const []) 0)\<close> using p by simp
  have L2len: \<open>length (fst L2) = length (fst L1) + 1\<close> by (simp add: L2' push_m_def)
  have k0len: \<open>length (fst L2) + unat i < 2 ^ 56\<close> using L2len lenbud by simp
  have wmul: \<open>0 + snd L1 ! ka * unat i < 2 ^ 56\<close> using wR wa by (simp add: mult.commute)
  have R: \<open>lower_m ws dm L (TermL_Repeat i a) = (fst (foldl (repeat_step ka (snd L1 ! ka)) (L2, k0, 0) [0..<unat i]),
            fst (snd (foldl (repeat_step ka (snd L1 ! ka)) (L2, k0, 0) [0..<unat i])))\<close>
    using a p by (simp add: lower_m_Repeat' Let_def split_def)
  show ?case using R repeat_fold_bnd[OF B2 wmul k0len, of ka] by simp
next
  case (TermL_ZeroExtend i a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  have wt: \<open>wt ws ds a\<close> using TermL_ZeroExtend.prems(1) by simp
  have sub: \<open>\<forall>u \<in> set (subterms a). width ws ds u < 2 ^ 56\<close> using TermL_ZeroExtend.prems(6) by simp
  have bud: \<open>length (fst L) + 2 * lweight ws ds a < 2 ^ 56\<close>
    using TermL_ZeroExtend.prems(5) lin1[of \<open>width ws ds (TermL_ZeroExtend i a)\<close>] unfolding lw_un add_mult_distrib2 by linarith
  have B1: \<open>bnd L1\<close> using TermL_ZeroExtend.IH[OF wt TermL_ZeroExtend.prems(2,3,4) bud sub] a by simp
  have EA: \<open>QFBV_Lower.env_ok ws L1 ka (width ws ds a)\<close>
    using lower_m_correct[OF wt TermL_ZeroExtend.prems(2,3) a B1] by simp
  have wa: \<open>snd L1 ! ka = width ws ds a\<close> using EA by (simp add: QFBV_Lower.env_ok_def)
  have wsub: \<open>snd L1 ! ka + unat i < 2 ^ 56\<close> using wa TermL_ZeroExtend.prems(6) by simp
  have lena: \<open>length (fst L1) \<le> length (fst L) + 2 * lweight ws ds a\<close>
    using lower_m_length[OF wt, of dm L] a by simp
  have len: \<open>length (fst L1) + 1 < 2 ^ 56\<close>
    using lena TermL_ZeroExtend.prems(5) lin1[of \<open>width ws ds (TermL_ZeroExtend i a)\<close>] unfolding lw_un add_mult_distrib2 by linarith
  show ?case using a bnd_push[OF B1 wsub len] by (simp add: Let_def)
next
  case (TermL_SignExtend i a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  have wt: \<open>wt ws ds a\<close> using TermL_SignExtend.prems(1) by simp
  have sub: \<open>\<forall>u \<in> set (subterms a). width ws ds u < 2 ^ 56\<close> using TermL_SignExtend.prems(6) by simp
  have bud: \<open>length (fst L) + 2 * lweight ws ds a < 2 ^ 56\<close>
    using TermL_SignExtend.prems(5) lin1[of \<open>width ws ds (TermL_SignExtend i a)\<close>] unfolding lw_un add_mult_distrib2 by linarith
  have B1: \<open>bnd L1\<close> using TermL_SignExtend.IH[OF wt TermL_SignExtend.prems(2,3,4) bud sub] a by simp
  have EA: \<open>QFBV_Lower.env_ok ws L1 ka (width ws ds a)\<close>
    using lower_m_correct[OF wt TermL_SignExtend.prems(2,3) a B1] by simp
  have wa: \<open>snd L1 ! ka = width ws ds a\<close> using EA by (simp add: QFBV_Lower.env_ok_def)
  have wsub: \<open>snd L1 ! ka + unat i < 2 ^ 56\<close> using wa TermL_SignExtend.prems(6) by simp
  have lena: \<open>length (fst L1) \<le> length (fst L) + 2 * lweight ws ds a\<close>
    using lower_m_length[OF wt, of dm L] a by simp
  have len: \<open>length (fst L1) + 1 < 2 ^ 56\<close>
    using lena TermL_SignExtend.prems(5) lin1[of \<open>width ws ds (TermL_SignExtend i a)\<close>] unfolding lw_un add_mult_distrib2 by linarith
  show ?case using a bnd_push[OF B1 wsub len] by (simp add: Let_def)
next
  case (TermL_RotateLeft i a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  have wt: \<open>wt ws ds a\<close> using TermL_RotateLeft.prems(1) by simp
  have sub: \<open>\<forall>u \<in> set (subterms a). width ws ds u < 2 ^ 56\<close> using TermL_RotateLeft.prems(6) by simp
  have bud: \<open>length (fst L) + 2 * lweight ws ds a < 2 ^ 56\<close>
    using TermL_RotateLeft.prems(5) lin1[of \<open>width ws ds (TermL_RotateLeft i a)\<close>] unfolding lw_un add_mult_distrib2 by linarith
  have B1: \<open>bnd L1\<close> using TermL_RotateLeft.IH[OF wt TermL_RotateLeft.prems(2,3,4) bud sub] a by simp
  have EA: \<open>QFBV_Lower.env_ok ws L1 ka (width ws ds a)\<close>
    using lower_m_correct[OF wt TermL_RotateLeft.prems(2,3) a B1] by simp
  have wa: \<open>snd L1 ! ka = width ws ds a\<close> using EA by (simp add: QFBV_Lower.env_ok_def)
  have wsub: \<open>snd L1 ! ka < 2 ^ 56\<close> using wa TermL_RotateLeft.prems(6) by simp
  have lena: \<open>length (fst L1) \<le> length (fst L) + 2 * lweight ws ds a\<close>
    using lower_m_length[OF wt, of dm L] a by simp
  have len: \<open>length (fst L1) + 1 < 2 ^ 56\<close>
    using lena TermL_RotateLeft.prems(5) lin1[of \<open>width ws ds (TermL_RotateLeft i a)\<close>] unfolding lw_un add_mult_distrib2 by linarith
  show ?case using a bnd_push[OF B1 wsub len] B1
    by (simp add: lower_m_RotateLeft' Let_def split: if_splits)
next
  case (TermL_RotateRight i a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  have wt: \<open>wt ws ds a\<close> using TermL_RotateRight.prems(1) by simp
  have sub: \<open>\<forall>u \<in> set (subterms a). width ws ds u < 2 ^ 56\<close> using TermL_RotateRight.prems(6) by simp
  have bud: \<open>length (fst L) + 2 * lweight ws ds a < 2 ^ 56\<close>
    using TermL_RotateRight.prems(5) lin1[of \<open>width ws ds (TermL_RotateRight i a)\<close>] unfolding lw_un add_mult_distrib2 by linarith
  have B1: \<open>bnd L1\<close> using TermL_RotateRight.IH[OF wt TermL_RotateRight.prems(2,3,4) bud sub] a by simp
  have EA: \<open>QFBV_Lower.env_ok ws L1 ka (width ws ds a)\<close>
    using lower_m_correct[OF wt TermL_RotateRight.prems(2,3) a B1] by simp
  have wa: \<open>snd L1 ! ka = width ws ds a\<close> using EA by (simp add: QFBV_Lower.env_ok_def)
  have wsub: \<open>snd L1 ! ka < 2 ^ 56\<close> using wa TermL_RotateRight.prems(6) by simp
  have lena: \<open>length (fst L1) \<le> length (fst L) + 2 * lweight ws ds a\<close>
    using lower_m_length[OF wt, of dm L] a by simp
  have len: \<open>length (fst L1) + 1 < 2 ^ 56\<close>
    using lena TermL_RotateRight.prems(5) lin1[of \<open>width ws ds (TermL_RotateRight i a)\<close>] unfolding lw_un add_mult_distrib2 by linarith
  show ?case using a bnd_push[OF B1 wsub len] B1
    by (simp add: lower_m_RotateRight' Let_def split: if_splits)
next
  case (TermL_Ite c a b)
  obtain L1 kc where c: \<open>lower_m ws dm L c = (L1, kc)\<close> by (cases \<open>lower_m ws dm L c\<close>)
  obtain L2 ka where a: \<open>lower_m ws dm L1 a = (L2, ka)\<close> by (cases \<open>lower_m ws dm L1 a\<close>)
  obtain L3 kb where b: \<open>lower_m ws dm L2 b = (L3, kb)\<close> by (cases \<open>lower_m ws dm L2 b\<close>)
  have wt: \<open>wt ws ds c\<close> \<open>wt ws ds a\<close> \<open>wt ws ds b\<close> \<open>width ws ds a = width ws ds b\<close>
    using TermL_Ite.prems(1) by simp_all
  have subc: \<open>\<forall>u \<in> set (subterms c). width ws ds u < 2 ^ 56\<close> using TermL_Ite.prems(6) by simp
  have suba: \<open>\<forall>u \<in> set (subterms a). width ws ds u < 2 ^ 56\<close> using TermL_Ite.prems(6) by simp
  have subb: \<open>\<forall>u \<in> set (subterms b). width ws ds u < 2 ^ 56\<close> using TermL_Ite.prems(6) by simp
  have budc: \<open>length (fst L) + 2 * lweight ws ds c < 2 ^ 56\<close>
    using TermL_Ite.prems(5) lin1[of \<open>width ws ds (TermL_Ite c a b)\<close>] unfolding lw_Ite add_mult_distrib2 by linarith
  have B1: \<open>bnd L1\<close> using TermL_Ite.IH(1)[OF wt(1) TermL_Ite.prems(2,3,4) budc subc] c by simp
  have L1: \<open>lok ws L1\<close> and X1: \<open>lext ws L L1\<close>
    using lower_m_correct[OF wt(1) TermL_Ite.prems(2,3) c B1] lext_lok by blast+
  have D1: \<open>dm_ok ds dm L1\<close> using dm_ok_lext[OF TermL_Ite.prems(2,3) X1] .
  have lenc: \<open>length (fst L1) \<le> length (fst L) + 2 * lweight ws ds c\<close>
    using lower_m_length[OF wt(1), of dm L] c by simp
  have buda: \<open>length (fst L1) + 2 * lweight ws ds a < 2 ^ 56\<close>
    using lenc TermL_Ite.prems(5) lin1[of \<open>width ws ds (TermL_Ite c a b)\<close>] unfolding lw_Ite add_mult_distrib2 by linarith
  have B2: \<open>bnd L2\<close> using TermL_Ite.IH(2)[OF wt(2) L1 D1 B1 buda suba] a by simp
  have L2: \<open>lok ws L2\<close> and X2: \<open>lext ws L1 L2\<close>
    using lower_m_correct[OF wt(2) L1 D1 a B2] lext_lok by blast+
  have D2: \<open>dm_ok ds dm L2\<close> using dm_ok_lext[OF L1 D1 X2] .
  have lena: \<open>length (fst L2) \<le> length (fst L) + 2 * lweight ws ds c + 2 * lweight ws ds a\<close>
    using lower_m_length[OF wt(2), of dm L1] a lenc by simp
  have budb: \<open>length (fst L2) + 2 * lweight ws ds b < 2 ^ 56\<close>
    using lena TermL_Ite.prems(5) lin1[of \<open>width ws ds (TermL_Ite c a b)\<close>] unfolding lw_Ite add_mult_distrib2 by linarith
  have B3: \<open>bnd L3\<close> using TermL_Ite.IH(3)[OF wt(3) L2 D2 B2 budb subb] b by simp
  have EA: \<open>QFBV_Lower.env_ok ws L3 ka (width ws ds a)\<close>
    using lower_m_correct[OF wt(2) L1 D1 a B2] lower_m_correct[OF wt(3) L2 D2 b B3] env_lext by blast
  have wa: \<open>snd L3 ! ka = width ws ds a\<close> using EA by (simp add: QFBV_Lower.env_ok_def)
  have wsub: \<open>snd L3 ! ka < 2 ^ 56\<close> using wa TermL_Ite.prems(6) by simp
  have lenb: \<open>length (fst L3) \<le> length (fst L) + 2 * lweight ws ds c + 2 * lweight ws ds a + 2 * lweight ws ds b\<close>
    using lower_m_length[OF wt(3), of dm L2] b lena by simp
  have len: \<open>length (fst L3) + 1 < 2 ^ 56\<close>
    using lenb TermL_Ite.prems(5) lin1[of \<open>width ws ds (TermL_Ite c a b)\<close>] unfolding lw_Ite add_mult_distrib2 by linarith
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
  shows \<open>lweight ws ds t \<le> sum_list (map (lweight ws ds) (xs @ ys))\<close>
proof -
  have \<open>lweight ws ds t \<le> sum_list (map (lweight ws ds) xs)\<close>
    using assms by (intro member_le_sum_list; simp)
  then show ?thesis by simp
qed

lemma lweight_le_tw: \<open>lweight ws ds t \<le> term_weight ws ds t\<close>
  unfolding lweight_def term_weight_def
  by (rule sum_list_mono) (simp add: power_increasing[of 1 3, simplified])

lemma lweight_append: \<open>wt ws ds t \<Longrightarrow> lweight ws (ds @ e) t = lweight ws ds t\<close>
  unfolding lweight_def
  using wt_subterm QFBV_Lower.wt_width_append by (auto intro!: arg_cong[where f = sum_list] map_cong)

lemma lweight_take:
  assumes \<open>defs_wt ws [] D\<close> \<open>j < length D\<close>
  shows \<open>lweight ws (def_widths ws [] (take j D)) (D ! j) = lweight ws (def_widths ws [] D) (D ! j)\<close>
proof -
  have \<open>def_widths ws [] D = def_widths ws (def_widths ws [] (take j D)) (drop j D)\<close>
    using QFBV_Lower.def_widths_append[of ws \<open>[]\<close> \<open>take j D\<close> \<open>drop j D\<close>] by simp
  then obtain e where \<open>def_widths ws [] D = def_widths ws [] (take j D) @ e\<close>
    using QFBV_Lower.def_widths_prefix by metis
  then show ?thesis using lweight_append[OF QFBV_Lower.defs_wt_nth[OF assms]] by simp
qed

lemma size_bound_sum:
  \<open>1000000 * sum_list (map (lweight (var_widths p) (def_widths (var_widths p) [] (ProblemL_defs p)))
     (ProblemL_defs p @ ProblemL_asserts p)) \<le> size_bound p\<close>
proof -
  let ?ws = \<open>var_widths p\<close> and ?ds = \<open>def_widths (var_widths p) [] (ProblemL_defs p)\<close>
  have \<open>sum_list (map (lweight ?ws ?ds) (ProblemL_defs p @ ProblemL_asserts p)) \<le>
        sum_list (map (term_weight ?ws ?ds) (ProblemL_defs p @ ProblemL_asserts p))\<close>
    by (rule sum_list_mono) (rule lweight_le_tw)
  then show ?thesis by (simp add: size_bound_def Let_def)
qed

text \<open>\<^const>\<open>sizes_ok\<close> bounds the linear weights and the widths.\<close>
lemma ovf_sum:
  \<open>4 * sum_list (map (lweight (var_widths p) (def_widths (var_widths p) [] (ProblemL_defs p)))
     (ProblemL_defs p @ ProblemL_asserts p)) \<le> ovf_bound p\<close>
proof -
  let ?ws = \<open>var_widths p\<close> and ?ds = \<open>def_widths (var_widths p) [] (ProblemL_defs p)\<close>
  have \<open>sum_list (map (\<lambda>t. 4 * lweight ?ws ?ds t) (ProblemL_defs p @ ProblemL_asserts p)) \<le>
        sum_list (map (\<lambda>t. 4 * lweight ?ws ?ds t + ecount ?ws ?ds t) (ProblemL_defs p @ ProblemL_asserts p))\<close>
    by (rule sum_list_mono) simp
  moreover have \<open>sum_list (map (\<lambda>t. 4 * lweight ?ws ?ds t) (ProblemL_defs p @ ProblemL_asserts p)) =
                 4 * sum_list (map (lweight ?ws ?ds) (ProblemL_defs p @ ProblemL_asserts p))\<close>
    by (simp add: sum_list_const_mult)
  ultimately show ?thesis by (simp add: ovf_bound_def Let_def)
qed

text \<open>Named partial results of the two loops of \<^const>\<open>lower_problem_m\<close>, with the step rule as a
  simp rule so that the loop proof can advance the invariant one iteration at a time.\<close>
definition ldefs_part :: \<open>ProblemL \<Rightarrow> nat \<Rightarrow> lst \<times> nat list\<close> where
  \<open>ldefs_part p n \<equiv> foldl (ldefs_step p) (([], []), []) [0..<n]\<close>

definition lasserts_part :: \<open>ProblemL \<Rightarrow> nat \<Rightarrow> lst \<times> CoreTermL list\<close> where
  \<open>lasserts_part p n \<equiv> foldl (lasserts_step p (snd (ldefs_res p))) (fst (ldefs_res p), []) [0..<n]\<close>

lemma ldefs_part_simps [simp]:
  \<open>ldefs_part p 0 = (([], []), [])\<close>
  \<open>ldefs_part p (Suc n) =
     (let (L1, k) = lower_m (var_widths p) (snd (ldefs_part p n)) (fst (ldefs_part p n)) (ProblemL_defs p ! n)
      in (L1, snd (ldefs_part p n) @ [k]))\<close>
  by (simp_all add: ldefs_part_def ldefs_step_def split_def Let_def)

lemma lasserts_part_simps [simp]:
  \<open>lasserts_part p 0 = (fst (ldefs_res p), [])\<close>
  \<open>lasserts_part p (Suc n) =
     (let (L1, k) = lower_m (var_widths p) (snd (ldefs_res p)) (fst (lasserts_part p n)) (ProblemL_asserts p ! n)
      in (L1, snd (lasserts_part p n) @ [cr k]))\<close>
  by (simp_all add: lasserts_part_def lasserts_step_def split_def Let_def)

lemma ldefs_part_res: \<open>ldefs_part p (length (ProblemL_defs p)) = ldefs_res p\<close>
  by (simp add: ldefs_part_def ldefs_res_def)

lemma lasserts_part_res: \<open>lasserts_part p (length (ProblemL_asserts p)) = lasserts_res p\<close>
  by (simp add: lasserts_part_def lasserts_res_def)

lemma p6364: \<open>(2::nat) ^ 56 \<le> 2 ^ 56\<close>
  by simp

lemma ldefs_len:
  assumes \<open>problem_wt p\<close>
  shows \<open>j \<le> length (ProblemL_defs p) \<Longrightarrow>
    length (fst (fst (foldl (ldefs_step p) (([], []), []) [0..<j]))) \<le>
    2 * sum_list (map (lweight (var_widths p) (def_widths (var_widths p) [] (ProblemL_defs p))) (take j (ProblemL_defs p)))\<close>
proof (induction j)
  case 0
  then show ?case by simp
next
  case (Suc j)
  let ?ws = \<open>var_widths p\<close> and ?D = \<open>ProblemL_defs p\<close>
  let ?ds = \<open>def_widths ?ws [] ?D\<close>
  obtain Lj dmj where f: \<open>foldl (ldefs_step p) (([], []), []) [0..<j] = (Lj, dmj)\<close>
    by (cases \<open>foldl (ldefs_step p) (([], []), []) [0..<j]\<close>)
  have jl: \<open>j < length ?D\<close> using Suc.prems by simp
  have dwt: \<open>defs_wt ?ws [] ?D\<close> using assms by (simp add: problem_wt_def Let_def)
  have wtj: \<open>wt ?ws (def_widths ?ws [] (take j ?D)) (?D ! j)\<close> using QFBV_Lower.defs_wt_nth[OF dwt jl] .
  have IH: \<open>length (fst Lj) \<le> 2 * sum_list (map (lweight ?ws ?ds) (take j ?D))\<close> using Suc.IH jl f by simp
  have R: \<open>foldl (ldefs_step p) (([], []), []) [0..<Suc j] =
           (fst (lower_m ?ws dmj Lj (?D ! j)), dmj @ [snd (lower_m ?ws dmj Lj (?D ! j))])\<close>
    using f by (simp add: ldefs_step_def split_def Let_def)
  have st: \<open>length (fst (fst (lower_m ?ws dmj Lj (?D ! j)))) \<le> length (fst Lj) + 2 * lweight ?ws ?ds (?D ! j)\<close>
    using lower_m_length[OF wtj, of dmj Lj] lweight_take[OF dwt jl] by simp
  have tk: \<open>take (Suc j) ?D = take j ?D @ [?D ! j]\<close> using take_Suc_conv_app_nth[OF jl] .
  show ?case using R IH st by (simp add: tk)
qed

lemma lasserts_len:
  assumes \<open>problem_wt p\<close>
  shows \<open>i \<le> length (ProblemL_asserts p) \<Longrightarrow>
    length (fst (fst (foldl (lasserts_step p (snd (ldefs_res p))) (fst (ldefs_res p), []) [0..<i]))) \<le>
    length (fst (fst (ldefs_res p))) +
    2 * sum_list (map (lweight (var_widths p) (def_widths (var_widths p) [] (ProblemL_defs p))) (take i (ProblemL_asserts p)))\<close>
proof (induction i)
  case 0
  then show ?case by simp
next
  case (Suc i)
  let ?ws = \<open>var_widths p\<close> and ?D = \<open>ProblemL_defs p\<close> and ?A = \<open>ProblemL_asserts p\<close>
  let ?ds = \<open>def_widths ?ws [] ?D\<close>
  let ?dm = \<open>snd (ldefs_res p)\<close> and ?L0 = \<open>fst (ldefs_res p)\<close>
  obtain Li csi where f: \<open>foldl (lasserts_step p ?dm) (?L0, []) [0..<i] = (Li, csi)\<close>
    by (cases \<open>foldl (lasserts_step p ?dm) (?L0, []) [0..<i]\<close>)
  have il: \<open>i < length ?A\<close> using Suc.prems by simp
  have wti: \<open>wt ?ws ?ds (?A ! i)\<close> using assms il by (simp add: problem_wt_def Let_def)
  have IH: \<open>length (fst Li) \<le> length (fst ?L0) + 2 * sum_list (map (lweight ?ws ?ds) (take i ?A))\<close>
    using Suc.IH il f by simp
  have R: \<open>foldl (lasserts_step p ?dm) (?L0, []) [0..<Suc i] =
           (fst (lower_m ?ws ?dm Li (?A ! i)), csi @ [cr (snd (lower_m ?ws ?dm Li (?A ! i)))])\<close>
    using f by (simp add: lasserts_step_def split_def Let_def)
  have st: \<open>length (fst (fst (lower_m ?ws ?dm Li (?A ! i)))) \<le> length (fst Li) + 2 * lweight ?ws ?ds (?A ! i)\<close>
    using lower_m_length[OF wti, of ?dm Li] by simp
  have tk: \<open>take (Suc i) ?A = take i ?A @ [?A ! i]\<close> using take_Suc_conv_app_nth[OF il] .
  show ?case using R IH st by (simp add: tk)
qed

lemma ldefs_bnd:
  assumes \<open>problem_wt p\<close> \<open>sizes_ok p\<close>
  shows \<open>j \<le> length (ProblemL_defs p) \<Longrightarrow> bnd (fst (foldl (ldefs_step p) (([], []), []) [0..<j]))\<close>
proof (induction j)
  case 0
  show ?case by (simp add: bnd_def)
next
  case (Suc j)
  let ?ws = \<open>var_widths p\<close> and ?D = \<open>ProblemL_defs p\<close> and ?A = \<open>ProblemL_asserts p\<close>
  let ?ds = \<open>def_widths ?ws [] ?D\<close>
  let ?dsj = \<open>def_widths ?ws [] (take j ?D)\<close>
  let ?SUM = \<open>sum_list (map (lweight ?ws ?ds) (?D @ ?A))\<close>
  obtain Lj dmj where f: \<open>foldl (ldefs_step p) (([], []), []) [0..<j] = (Lj, dmj)\<close>
    by (cases \<open>foldl (ldefs_step p) (([], []), []) [0..<j]\<close>)
  have jl: \<open>j < length ?D\<close> and jle: \<open>j \<le> length ?D\<close> using Suc.prems by simp_all
  have Bj: \<open>bnd Lj\<close> using Suc.IH jle f by simp
  have dwt: \<open>defs_wt ?ws [] ?D\<close> using assms(1) by (simp add: problem_wt_def Let_def)
  have inv: \<open>ldefs_inv p j (Lj, dmj)\<close> using ldefs_loop[OF dwt jle f Bj] .
  have lok: \<open>lok ?ws Lj\<close> and dmok: \<open>dm_ok ?dsj dmj Lj\<close>
    using inv by (simp_all add: ldefs_inv_def Let_def)
  have wtj: \<open>wt ?ws ?dsj (?D ! j)\<close> using QFBV_Lower.defs_wt_nth[OF dwt jl] .
  have ob: \<open>4 * ?SUM < 2 ^ 56\<close> using ovf_sum[of p] assms(2) by (simp add: sizes_ok_def)
  have twj: \<open>lweight ?ws ?dsj (?D ! j) \<le> sum_list (map (lweight ?ws ?ds) (drop j ?D @ ?A))\<close>
  proof -
    have \<open>?D ! j \<in> set (drop j ?D)\<close> using jl by (simp add: in_set_conv_nth) (metis add.right_neutral nth_drop zero_less_diff)
    then show ?thesis using lweight_take[OF dwt jl] member_tw_app_le[of \<open>?D ! j\<close> \<open>drop j ?D\<close> ?ws ?ds ?A] by simp
  qed
  have split: \<open>?SUM = sum_list (map (lweight ?ws ?ds) (take j ?D)) + sum_list (map (lweight ?ws ?ds) (drop j ?D @ ?A))\<close>
    by (metis append_assoc append_take_drop_id map_append sum_list_append)
  have lenj: \<open>length (fst Lj) \<le> 2 * sum_list (map (lweight ?ws ?ds) (take j ?D))\<close>
    using ldefs_len[OF assms(1) jle] f by simp
  have budget: \<open>length (fst Lj) + 2 * lweight ?ws ?dsj (?D ! j) < 2 ^ 56\<close>
    using lenj twj split ob p6364 by linarith
  have subw: \<open>\<forall>u \<in> set (subterms (?D ! j)). width ?ws ?dsj u < 2 ^ 56\<close>
  proof
    fix u assume \<open>u \<in> set (subterms (?D ! j))\<close>
    then have \<open>width ?ws ?dsj u \<le> lweight ?ws ?dsj (?D ! j)\<close> by (rule width_le_tw)
    then show \<open>width ?ws ?dsj u < 2 ^ 56\<close> using twj split ob p6364 by linarith
  qed
  have R: \<open>foldl (ldefs_step p) (([], []), []) [0..<Suc j] =
           (fst (lower_m ?ws dmj Lj (?D ! j)), dmj @ [snd (lower_m ?ws dmj Lj (?D ! j))])\<close>
    using f by (simp add: ldefs_step_def split_def Let_def)
  show ?case using R lower_m_bnd[OF wtj lok dmok Bj budget subw] by simp
qed

lemma lasserts_bnd:
  assumes \<open>problem_wt p\<close> \<open>sizes_ok p\<close>
  shows \<open>i \<le> length (ProblemL_asserts p) \<Longrightarrow>
         bnd (fst (foldl (lasserts_step p (snd (ldefs_res p))) (fst (ldefs_res p), []) [0..<i]))\<close>
proof (induction i)
  case 0
  show ?case using ldefs_bnd[OF assms, of \<open>length (ProblemL_defs p)\<close>] by (simp add: ldefs_res_def)
next
  case (Suc i)
  let ?ws = \<open>var_widths p\<close> and ?D = \<open>ProblemL_defs p\<close> and ?A = \<open>ProblemL_asserts p\<close>
  let ?ds = \<open>def_widths ?ws [] ?D\<close>
  let ?SUM = \<open>sum_list (map (lweight ?ws ?ds) (?D @ ?A))\<close>
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
  have ob: \<open>4 * ?SUM < 2 ^ 56\<close> using ovf_sum[of p] assms(2) by (simp add: sizes_ok_def)
  have twi: \<open>lweight ?ws ?ds (?A ! i) \<le> sum_list (map (lweight ?ws ?ds) (drop i ?A))\<close>
  proof -
    have \<open>?A ! i \<in> set (drop i ?A)\<close> using il by (simp add: in_set_conv_nth) (metis add.right_neutral nth_drop zero_less_diff)
    then show ?thesis by (intro member_le_sum_list) simp_all
  qed
  have L0: \<open>length (fst ?L0) \<le> 2 * sum_list (map (lweight ?ws ?ds) ?D)\<close>
    using ldefs_len[OF assms(1) order_refl] by (simp add: ldefs_res_def)
  have Li: \<open>length (fst Li) \<le> length (fst ?L0) + 2 * sum_list (map (lweight ?ws ?ds) (take i ?A))\<close>
    using lasserts_len[OF assms(1) ile] f by simp
  have split: \<open>?SUM = sum_list (map (lweight ?ws ?ds) ?D) + sum_list (map (lweight ?ws ?ds) (take i ?A)) +
                      sum_list (map (lweight ?ws ?ds) (drop i ?A))\<close>
    by (metis add.assoc append_take_drop_id map_append sum_list_append)
  have budget: \<open>length (fst Li) + 2 * lweight ?ws ?ds (?A ! i) < 2 ^ 56\<close>
    using L0 Li twi split ob p6364 by linarith
  have subw: \<open>\<forall>u \<in> set (subterms (?A ! i)). width ?ws ?ds u < 2 ^ 56\<close>
  proof
    fix u assume \<open>u \<in> set (subterms (?A ! i))\<close>
    then have \<open>width ?ws ?ds u \<le> lweight ?ws ?ds (?A ! i)\<close> by (rule width_le_tw)
    then show \<open>width ?ws ?ds u < 2 ^ 56\<close> using twi split ob p6364 by linarith
  qed
  have R: \<open>foldl (lasserts_step p ?dm) (?L0, []) [0..<Suc i] =
           (fst (lower_m ?ws ?dm Li (?A ! i)), csi @ [cr (snd (lower_m ?ws ?dm Li (?A ! i)))])\<close>
    using f by (simp add: lasserts_step_def split_def Let_def)
  show ?case using R lower_m_bnd[OF wti lok dmok Bi budget subw] by simp
qed

lemma prob_bnd:
  assumes \<open>problem_wt p\<close> \<open>sizes_ok p\<close>
  shows \<open>bnd (fst (lasserts_res p))\<close>
  using lasserts_bnd[OF assms, of \<open>length (ProblemL_asserts p)\<close>] by (simp add: lasserts_res_def)

subsection \<open>The fuel of the core solver\<close>

lemma ecount_take:
  assumes \<open>defs_wt ws [] D\<close> \<open>j < length D\<close>
  shows \<open>ecount ws (def_widths ws [] (take j D)) (D ! j) = ecount ws (def_widths ws [] D) (D ! j)\<close>
proof -
  have \<open>def_widths ws [] D = def_widths ws (def_widths ws [] (take j D)) (drop j D)\<close>
    using QFBV_Lower.def_widths_append[of ws \<open>[]\<close> \<open>take j D\<close> \<open>drop j D\<close>] by simp
  then obtain e where \<open>def_widths ws [] D = def_widths ws [] (take j D) @ e\<close>
    using QFBV_Lower.def_widths_prefix by metis
  then show ?thesis using ecount_append[OF QFBV_Lower.defs_wt_nth[OF assms]] by simp
qed

text \<open>The rewriting of the definitions: its CNF count is at most the sum of the \<^const>\<open>ecount\<close> of
  the definitions rewritten so far, and every core definition is small.\<close>
lemma ldefs_count:
  assumes \<open>problem_wt p\<close> \<open>sizes_ok p\<close>
  shows \<open>j \<le> length (ProblemL_defs p) \<Longrightarrow>
    lcnt (var_widths p) (fst (foldl (ldefs_step p) (([], []), []) [0..<j])) \<le>
      sum_list (map (ecount (var_widths p) (def_widths (var_widths p) [] (ProblemL_defs p))) (take j (ProblemL_defs p))) \<and>
    lsmall (var_widths p)
      (2 * sum_list (map (lweight (var_widths p) (def_widths (var_widths p) [] (ProblemL_defs p))) (ProblemL_defs p @ ProblemL_asserts p)))
      (fst (foldl (ldefs_step p) (([], []), []) [0..<j]))\<close>
proof (induction j)
  case 0
  show ?case by (simp add: lcnt_def lsmall_nil)
next
  case (Suc j)
  let ?ws = \<open>var_widths p\<close> and ?D = \<open>ProblemL_defs p\<close> and ?A = \<open>ProblemL_asserts p\<close>
  let ?ds = \<open>def_widths ?ws [] ?D\<close>
  let ?dsj = \<open>def_widths ?ws [] (take j ?D)\<close>
  let ?SUM = \<open>sum_list (map (lweight ?ws ?ds) (?D @ ?A))\<close>
  obtain Lj dmj where f: \<open>foldl (ldefs_step p) (([], []), []) [0..<j] = (Lj, dmj)\<close>
    by (cases \<open>foldl (ldefs_step p) (([], []), []) [0..<j]\<close>)
  have jl: \<open>j < length ?D\<close> and jle: \<open>j \<le> length ?D\<close> using Suc.prems by simp_all
  have Bj: \<open>bnd Lj\<close> using ldefs_bnd[OF assms jle] f by simp
  have dwt: \<open>defs_wt ?ws [] ?D\<close> using assms(1) by (simp add: problem_wt_def Let_def)
  have inv: \<open>ldefs_inv p j (Lj, dmj)\<close> using ldefs_loop[OF dwt jle f Bj] .
  have lok: \<open>lok ?ws Lj\<close> and dmok: \<open>dm_ok ?dsj dmj Lj\<close>
    using inv by (simp_all add: ldefs_inv_def Let_def)
  have wtj: \<open>wt ?ws ?dsj (?D ! j)\<close> using QFBV_Lower.defs_wt_nth[OF dwt jl] .
  have IH: \<open>lcnt ?ws Lj \<le> sum_list (map (ecount ?ws ?ds) (take j ?D))\<close> \<open>lsmall ?ws (2 * ?SUM) Lj\<close>
    using Suc.IH jle f by simp_all
  obtain L' k where lm: \<open>lower_m ?ws dmj Lj (?D ! j) = (L', k)\<close> by (cases \<open>lower_m ?ws dmj Lj (?D ! j)\<close>)
  have R: \<open>foldl (ldefs_step p) (([], []), []) [0..<Suc j] = (L', dmj @ [k])\<close>
    using f lm by (simp add: ldefs_step_def split_def Let_def)
  have B': \<open>bnd L'\<close> using ldefs_bnd[OF assms Suc.prems] R by simp
  note C = lower_m_count[OF wtj lok dmok lm B', of \<open>2 * ?SUM\<close>]
  have twj: \<open>lweight ?ws ?dsj (?D ! j) \<le> ?SUM\<close>
  proof -
    have \<open>?D ! j \<in> set ?D\<close> using jl by simp
    then show ?thesis using lweight_take[OF dwt jl] member_tw_app_le[of \<open>?D ! j\<close> ?D ?ws ?ds ?A] by simp
  qed
  have ws: \<open>wsmall ?ws ?dsj (2 * ?SUM) (?D ! j)\<close>
    unfolding wsmall_def using width_le_tw twj by (meson le_trans mult_le_mono2)
  have ec: \<open>ecount ?ws ?dsj (?D ! j) = ecount ?ws ?ds (?D ! j)\<close> using ecount_take[OF dwt jl] .
  have tk: \<open>take (Suc j) ?D = take j ?D @ [?D ! j]\<close> using take_Suc_conv_app_nth[OF jl] .
  show ?case using IH C ws ec R tk by simp
qed

lemma lasserts_count:
  assumes \<open>problem_wt p\<close> \<open>sizes_ok p\<close>
  shows \<open>i \<le> length (ProblemL_asserts p) \<Longrightarrow>
    lcnt (var_widths p) (fst (foldl (lasserts_step p (snd (ldefs_res p))) (fst (ldefs_res p), []) [0..<i])) \<le>
      sum_list (map (ecount (var_widths p) (def_widths (var_widths p) [] (ProblemL_defs p)))
        (ProblemL_defs p @ take i (ProblemL_asserts p))) \<and>
    lsmall (var_widths p)
      (2 * sum_list (map (lweight (var_widths p) (def_widths (var_widths p) [] (ProblemL_defs p))) (ProblemL_defs p @ ProblemL_asserts p)))
      (fst (foldl (lasserts_step p (snd (ldefs_res p))) (fst (ldefs_res p), []) [0..<i]))\<close>
proof (induction i)
  case 0
  show ?case using ldefs_count[OF assms order_refl] by (simp add: ldefs_res_def)
next
  case (Suc i)
  let ?ws = \<open>var_widths p\<close> and ?D = \<open>ProblemL_defs p\<close> and ?A = \<open>ProblemL_asserts p\<close>
  let ?ds = \<open>def_widths ?ws [] ?D\<close>
  let ?SUM = \<open>sum_list (map (lweight ?ws ?ds) (?D @ ?A))\<close>
  let ?dm = \<open>snd (ldefs_res p)\<close> and ?L0 = \<open>fst (ldefs_res p)\<close>
  obtain Li csi where f: \<open>foldl (lasserts_step p ?dm) (?L0, []) [0..<i] = (Li, csi)\<close>
    by (cases \<open>foldl (lasserts_step p ?dm) (?L0, []) [0..<i]\<close>)
  have il: \<open>i < length ?A\<close> and ile: \<open>i \<le> length ?A\<close> using Suc.prems by simp_all
  have Bi: \<open>bnd Li\<close> using lasserts_bnd[OF assms ile] f by simp
  have B0: \<open>bnd ?L0\<close> using ldefs_bnd[OF assms, of \<open>length ?D\<close>] by (simp add: ldefs_res_def)
  have dwt: \<open>defs_wt ?ws [] ?D\<close> using assms(1) by (simp add: problem_wt_def Let_def)
  have feq: \<open>foldl (ldefs_step p) (([], []), []) [0..<length ?D] = (?L0, ?dm)\<close>
    by (simp add: ldefs_res_def)
  have I1: \<open>ldefs_inv p (length ?D) (?L0, ?dm)\<close>
    using ldefs_loop[OF dwt order_refl feq B0] .
  have inv: \<open>lasserts_inv p ?dm ?L0 i (Li, csi)\<close>
    using lasserts_loop[OF assms(1) ile I1 f Bi] .
  have lx: \<open>lext ?ws ?L0 Li\<close> using inv by (simp add: lasserts_inv_def Let_def)
  have lok: \<open>lok ?ws Li\<close> using lx lext_lok by blast
  have dmok: \<open>dm_ok ?ds ?dm Li\<close>
  proof -
    have lok0: \<open>lok ?ws ?L0\<close> using I1 by (simp add: ldefs_inv_def Let_def)
    have dmok0: \<open>dm_ok ?ds ?dm ?L0\<close> using I1 by (simp add: ldefs_inv_def Let_def take_all)
    show ?thesis using dm_ok_lext[OF lok0 dmok0 lx] .
  qed
  have wti: \<open>wt ?ws ?ds (?A ! i)\<close> using assms(1) il by (simp add: problem_wt_def Let_def)
  have IH: \<open>lcnt ?ws Li \<le> sum_list (map (ecount ?ws ?ds) (?D @ take i ?A))\<close> \<open>lsmall ?ws (2 * ?SUM) Li\<close>
    using Suc.IH ile f by simp_all
  obtain L' k where lm: \<open>lower_m ?ws ?dm Li (?A ! i) = (L', k)\<close> by (cases \<open>lower_m ?ws ?dm Li (?A ! i)\<close>)
  have R: \<open>foldl (lasserts_step p ?dm) (?L0, []) [0..<Suc i] = (L', csi @ [cr k])\<close>
    using f lm by (simp add: lasserts_step_def split_def Let_def)
  have B': \<open>bnd L'\<close> using lasserts_bnd[OF assms Suc.prems] R by simp
  note C = lower_m_count[OF wti lok dmok lm B', of \<open>2 * ?SUM\<close>]
  have twi: \<open>lweight ?ws ?ds (?A ! i) \<le> ?SUM\<close>
  proof -
    have \<open>?A ! i \<in> set (?D @ ?A)\<close> using il by simp
    then show ?thesis by (intro member_le_sum_list) auto
  qed
  have ws: \<open>wsmall ?ws ?ds (2 * ?SUM) (?A ! i)\<close>
    unfolding wsmall_def using width_le_tw twi by (meson le_trans mult_le_mono2)
  have tk: \<open>take (Suc i) ?A = take i ?A @ [?A ! i]\<close> using take_Suc_conv_app_nth[OF il] .
  show ?case using IH C ws R tk by simp
qed

text \<open>Within \<^const>\<open>sizes_ok\<close>, the core problem built by the rewriting is within the fuel of the
  core solver: it meets the hypotheses of \<open>fuel_bound_lt\<close>.\<close>
theorem lower_fb_hyps:
  assumes \<open>problem_wt p\<close> \<open>sizes_ok p\<close>
  shows \<open>fb_hyps (lower_problem_m p)\<close>
proof -
  let ?ws = \<open>var_widths p\<close> and ?D = \<open>ProblemL_defs p\<close> and ?A = \<open>ProblemL_asserts p\<close>
  let ?ds = \<open>def_widths ?ws [] ?D\<close>
  let ?SUM = \<open>sum_list (map (lweight ?ws ?ds) (?D @ ?A))\<close>
  let ?EC = \<open>sum_list (map (ecount ?ws ?ds) (?D @ ?A))\<close>
  obtain L2 cs where a: \<open>lasserts_res p = (L2, cs)\<close> by (cases \<open>lasserts_res p\<close>)
  let ?q = \<open>lower_problem_m p\<close>
  have q: \<open>?q = make_CoreProblemL (ProblemL_widths p) (fst L2) cs\<close> using lower_problem_m_eq[of p] a by simp
  have B2: \<open>bnd L2\<close> using prob_bnd[OF assms] a by simp
  have cwt: \<open>cproblem_wt ?q\<close> using lower_problem_correct(1)[OF assms(1)] prob_bnd[OF assms] .
  have qw: \<open>cvar_widths ?q = ?ws\<close> \<open>CoreProblemL_defs ?q = fst L2\<close> \<open>CoreProblemL_asserts ?q = cs\<close>
    using q by (simp_all add: cvar_widths_def var_widths_def)
  \<comment> \<open>The loop invariant of the assertions.\<close>
  have B0: \<open>bnd (fst (ldefs_res p))\<close> using ldefs_bnd[OF assms, of \<open>length ?D\<close>] by (simp add: ldefs_res_def)
  have dwt: \<open>defs_wt ?ws [] ?D\<close> using assms(1) by (simp add: problem_wt_def Let_def)
  have feq: \<open>foldl (ldefs_step p) (([], []), []) [0..<length ?D] = (fst (ldefs_res p), snd (ldefs_res p))\<close>
    by (simp add: ldefs_res_def)
  have I1: \<open>ldefs_inv p (length ?D) (fst (ldefs_res p), snd (ldefs_res p))\<close>
    using ldefs_loop[OF dwt order_refl feq B0] .
  have fa: \<open>foldl (lasserts_step p (snd (ldefs_res p))) (fst (ldefs_res p), []) [0..<length ?A] = (L2, cs)\<close>
    using a by (simp add: lasserts_res_def)
  have I2: \<open>lasserts_inv p (snd (ldefs_res p)) (fst (ldefs_res p)) (length ?A) (L2, cs)\<close>
    using lasserts_loop[OF assms(1) order_refl I1 fa B2] .
  have lok: \<open>lok ?ws L2\<close> using I2 lext_lok by (simp add: lasserts_inv_def Let_def) blast
  have cds: \<open>cdef_widths ?ws [] (fst L2) = snd L2\<close> using lok by (simp add: lok_def)
  have len: \<open>length cs = length ?A\<close> and each: \<open>\<forall>n < length ?A. \<exists>k. cs ! n = cr k \<and> QFBV_Lower.env_ok ?ws L2 k 1\<close>
    using I2 by (simp_all add: lasserts_inv_def Let_def) blast
  \<comment> \<open>The counts.\<close>
  have CNT: \<open>lcnt ?ws L2 \<le> ?EC\<close> and SM: \<open>lsmall ?ws (2 * ?SUM) L2\<close>
    using lasserts_count[OF assms order_refl] fa by simp_all
  have csz: \<open>\<forall>t \<in> set cs. ccount ?ws (snd L2) t = 0 \<and> tbound ?ws (snd L2) t \<le> 4\<close>
  proof
    fix t assume \<open>t \<in> set cs\<close>
    then obtain n where n: \<open>n < length ?A\<close> \<open>t = cs ! n\<close> using len by (auto simp add: in_set_conv_nth)
    then obtain k where k: \<open>t = cr k\<close> \<open>QFBV_Lower.env_ok ?ws L2 k 1\<close> using each by blast
    have \<open>cwidth ?ws (snd L2) (cr k) = 1\<close> using cr_env[OF k(2)] by simp
    moreover have \<open>size (cr k) = 0\<close> by (simp add: cr_def)
    ultimately show \<open>ccount ?ws (snd L2) t = 0 \<and> tbound ?ws (snd L2) t \<le> 4\<close>
      using k(1) by (simp add: cc_cr tbound_def)
  qed
  have sumc: \<open>sum_list (map (ccount ?ws (snd L2)) (fst L2 @ cs)) = lcnt ?ws L2\<close>
  proof -
    have \<open>sum_list (map (ccount ?ws (snd L2)) cs) = 0\<close> using csz by (simp add: sum_list_eq_0_iff)
    then show ?thesis by (simp add: lcnt_def)
  qed
  \<comment> \<open>The bounds from \<^const>\<open>sizes_ok\<close>.\<close>
  have ob: \<open>4 * (1 + sum_list ?ws + length ?ws + length ?D + length ?A + (4 * ?SUM + ?EC)) < 2 ^ 56\<close>
  proof -
    have \<open>sum_list (map (\<lambda>t. 4 * lweight ?ws ?ds t + ecount ?ws ?ds t) (?D @ ?A)) = 4 * ?SUM + ?EC\<close>
      by (simp add: sum_list_addf sum_list_const_mult)
    then show ?thesis using assms(2) by (simp add: sizes_ok_def ovf_bound_def Let_def)
  qed
  have l2: \<open>length (fst L2) \<le> 2 * ?SUM\<close>
  proof -
    have \<open>length (fst (fst (ldefs_res p))) \<le> 2 * sum_list (map (lweight ?ws ?ds) ?D)\<close>
      using ldefs_len[OF assms(1) order_refl] by (simp add: ldefs_res_def)
    moreover have \<open>length (fst L2) \<le> length (fst (fst (ldefs_res p))) + 2 * sum_list (map (lweight ?ws ?ds) ?A)\<close>
      using lasserts_len[OF assms(1) order_refl] fa by simp
    ultimately show ?thesis by simp
  qed
  have tb: \<open>\<forall>t \<in> set (fst L2 @ cs). tbound ?ws (snd L2) t < 2 ^ 56\<close>
  proof
    fix t assume \<open>t \<in> set (fst L2 @ cs)\<close>
    then consider \<open>t \<in> set (fst L2)\<close> | \<open>t \<in> set cs\<close> by auto
    then show \<open>tbound ?ws (snd L2) t < 2 ^ 56\<close>
    proof cases
      case 1
      show ?thesis using tb_arith[OF lsmall_tbound[OF SM 1] ob] .
    next
      case 2
      then show ?thesis using csz by fastforce
    qed
  qed
  show ?thesis
    unfolding fb_hyps_def
  proof (intro conjI)
    show \<open>2 + sum_list (cvar_widths ?q) + length (CoreProblemL_asserts ?q) +
      sum_list (map (ccount (cvar_widths ?q) (cdef_widths (cvar_widths ?q) [] (CoreProblemL_defs ?q)))
        (CoreProblemL_defs ?q @ CoreProblemL_asserts ?q)) < 2 ^ 56\<close>
      unfolding qw cds sumc len using ob_arith(1)[OF ob CNT] .
    show \<open>length (cvar_widths ?q) < 2 ^ 56\<close> unfolding qw using ob_arith(2)[OF ob] .
    show \<open>length (CoreProblemL_defs ?q) < 2 ^ 56\<close> unfolding qw using ob_arith(4)[OF ob l2] .
    show \<open>length (CoreProblemL_asserts ?q) < 2 ^ 56\<close> unfolding qw len using ob_arith(3)[OF ob] .
    show \<open>\<forall>t \<in> set (CoreProblemL_defs ?q @ CoreProblemL_asserts ?q).
       tbound (cvar_widths ?q) (cdef_widths (cvar_widths ?q) [] (CoreProblemL_defs ?q)) t < 2 ^ 56\<close>
      unfolding qw cds using tb .
  qed
qed

text \<open>Within \<^const>\<open>sizes_ok\<close>, the numbers of variables, definitions and assertions of the core
  problem are below \<open>2 ^ 55\<close> and its widths below \<open>2 ^ 56\<close>.\<close>
theorem lower_lens55:
  assumes \<open>problem_wt p\<close> \<open>sizes_ok p\<close>
  shows \<open>length (cvar_widths (lower_problem_m p)) < 2 ^ 55\<close> \<open>length (CoreProblemL_defs (lower_problem_m p)) < 2 ^ 55\<close>
    \<open>length (CoreProblemL_asserts (lower_problem_m p)) < 2 ^ 55\<close>
    \<open>\<forall>w \<in> set (cvar_widths (lower_problem_m p)). w < 2 ^ 56\<close>
proof -
  let ?ws = \<open>var_widths p\<close> and ?D = \<open>ProblemL_defs p\<close> and ?A = \<open>ProblemL_asserts p\<close>
  let ?ds = \<open>def_widths ?ws [] ?D\<close>
  let ?SUM = \<open>sum_list (map (lweight ?ws ?ds) (?D @ ?A))\<close>
  let ?EC = \<open>sum_list (map (ecount ?ws ?ds) (?D @ ?A))\<close>
  obtain L2 cs where a: \<open>lasserts_res p = (L2, cs)\<close> by (cases \<open>lasserts_res p\<close>)
  let ?q = \<open>lower_problem_m p\<close>
  have q: \<open>?q = make_CoreProblemL (ProblemL_widths p) (fst L2) cs\<close> using lower_problem_m_eq[of p] a by simp
  have qw: \<open>cvar_widths ?q = ?ws\<close> \<open>CoreProblemL_defs ?q = fst L2\<close> \<open>CoreProblemL_asserts ?q = cs\<close>
    using q by (simp_all add: cvar_widths_def var_widths_def)
  have B2: \<open>bnd L2\<close> using prob_bnd[OF assms] a by simp
  have B0: \<open>bnd (fst (ldefs_res p))\<close> using ldefs_bnd[OF assms, of \<open>length ?D\<close>] by (simp add: ldefs_res_def)
  have dwt: \<open>defs_wt ?ws [] ?D\<close> using assms(1) by (simp add: problem_wt_def Let_def)
  have feq: \<open>foldl (ldefs_step p) (([], []), []) [0..<length ?D] = (fst (ldefs_res p), snd (ldefs_res p))\<close>
    by (simp add: ldefs_res_def)
  have I1: \<open>ldefs_inv p (length ?D) (fst (ldefs_res p), snd (ldefs_res p))\<close>
    using ldefs_loop[OF dwt order_refl feq B0] .
  have fa: \<open>foldl (lasserts_step p (snd (ldefs_res p))) (fst (ldefs_res p), []) [0..<length ?A] = (L2, cs)\<close>
    using a by (simp add: lasserts_res_def)
  have I2: \<open>lasserts_inv p (snd (ldefs_res p)) (fst (ldefs_res p)) (length ?A) (L2, cs)\<close>
    using lasserts_loop[OF assms(1) order_refl I1 fa B2] .
  have len: \<open>length cs = length ?A\<close> using I2 by (simp add: lasserts_inv_def Let_def)
  have ob: \<open>4 * (1 + sum_list ?ws + length ?ws + length ?D + length ?A + (4 * ?SUM + ?EC)) < 2 ^ 56\<close>
  proof -
    have \<open>sum_list (map (\<lambda>t. 4 * lweight ?ws ?ds t + ecount ?ws ?ds t) (?D @ ?A)) = 4 * ?SUM + ?EC\<close>
      by (simp add: sum_list_addf sum_list_const_mult)
    then show ?thesis using assms(2) by (simp add: sizes_ok_def ovf_bound_def Let_def)
  qed
  have l2: \<open>length (fst L2) \<le> 2 * ?SUM\<close>
  proof -
    have \<open>length (fst (fst (ldefs_res p))) \<le> 2 * sum_list (map (lweight ?ws ?ds) ?D)\<close>
      using ldefs_len[OF assms(1) order_refl] by (simp add: ldefs_res_def)
    moreover have \<open>length (fst L2) \<le> length (fst (fst (ldefs_res p))) + 2 * sum_list (map (lweight ?ws ?ds) ?A)\<close>
      using lasserts_len[OF assms(1) order_refl] fa by simp
    ultimately show ?thesis by simp
  qed
  show \<open>length (cvar_widths ?q) < 2 ^ 55\<close> using ob unfolding qw by simp
  show \<open>length (CoreProblemL_defs ?q) < 2 ^ 55\<close> using ob l2 unfolding qw by simp
  show \<open>length (CoreProblemL_asserts ?q) < 2 ^ 55\<close> using ob len unfolding qw by simp
  show \<open>\<forall>w \<in> set (cvar_widths ?q). w < 2 ^ 56\<close>
  proof
    fix w assume \<open>w \<in> set (cvar_widths ?q)\<close>
    then have \<open>w \<le> sum_list ?ws\<close> unfolding qw by (rule member_le_sum_list; simp)
    then show \<open>w < 2 ^ 56\<close> using ob by simp
  qed
qed

theorem lower_fuel_lt:
  assumes \<open>problem_wt p\<close> \<open>sizes_ok p\<close>
  shows \<open>fuel_bound (lower_problem_m p) < 2 ^ 64\<close>
  using fb_hyps_lt[OF lower_problem_correct(1)[OF assms(1) prob_bnd[OF assms]] lower_fb_hyps[OF assms]] by simp

section \<open>The top-level theorem\<close>

subsection \<open>The two answers\<close>

lemma fuel_bound_ge:
  assumes \<open>encode_m p = (s, vs)\<close>
  shows \<open>fst s + 2 \<le> fuel_bound p\<close> \<open>length (snd s) + 2 \<le> fuel_bound p\<close>
    \<open>\<forall>c \<in> set (snd s). length c + 2 \<le> fuel_bound p\<close>
    \<open>\<forall>w \<in> set (cvar_widths p). w + 2 \<le> fuel_bound p\<close>
    \<open>length (cvar_widths p) + 2 \<le> fuel_bound p\<close>
    \<open>2 * (fst s + length (snd s)) \<le> fuel_bound p\<close>
proof -
  have c: \<open>2 * length (cvar_widths p) + 2 \<le> fuel_bound p\<close> by (rule fb_ge) (simp add: fb_set_def)
  show \<open>fst s + 2 \<le> fuel_bound p\<close> \<open>length (snd s) + 2 \<le> fuel_bound p\<close>
    \<open>\<forall>c \<in> set (snd s). length c + 2 \<le> fuel_bound p\<close>
    \<open>\<forall>w \<in> set (cvar_widths p). w + 2 \<le> fuel_bound p\<close>
    \<open>2 * (fst s + length (snd s)) \<le> fuel_bound p\<close>
    using assms by (auto intro!: fb_ge simp: fb_set_def intro: rev_image_eqI)
  show \<open>length (cvar_widths p) + 2 \<le> fuel_bound p\<close> using c by linarith
qed

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

text \<open>The fuel of the search loop of \<^verbatim>\<open>dpll\<close> on the CNF formula of \<open>p\<close>: each of its iterations
  increases a number below \<open>3 ^ n\<close>, \<open>n\<close> the number of variables (\<^const>\<open>meas\<close>).\<close>
definition dpll_fuel :: \<open>CoreProblemL \<Rightarrow> nat\<close> where
  \<open>dpll_fuel p \<equiv> 3 ^ fst (fst (encode_m p))\<close>

subsection \<open>A strict bound on the fuel of the core solver\<close>

text \<open>\<^verbatim>\<open>encode\<close> needs \<^const>\<open>fuel_bound\<close> below \<open>2 ^ 57\<close>; \<open>fuel_bound_lt\<close> gives only \<open>\<le> 2 ^ 57\<close>,
  which is strict once the numbers of variables, definitions and assertions are below \<open>2 ^ 55\<close>.\<close>
lemma fuel_bound_lt57:
  assumes \<open>cproblem_wt p\<close>
    \<open>2 + sum_list (cvar_widths p) + length (CoreProblemL_asserts p) +
     sum_list (map (ccount (cvar_widths p) (cdef_widths (cvar_widths p) [] (CoreProblemL_defs p)))
                   (CoreProblemL_defs p @ CoreProblemL_asserts p)) < 2 ^ 56\<close>
    \<open>length (cvar_widths p) < 2 ^ 55\<close> \<open>length (CoreProblemL_defs p) < 2 ^ 55\<close>
    \<open>length (CoreProblemL_asserts p) < 2 ^ 55\<close>
    \<open>\<forall>t \<in> set (CoreProblemL_defs p @ CoreProblemL_asserts p).
       tbound (cvar_widths p) (cdef_widths (cvar_widths p) [] (CoreProblemL_defs p)) t < 2 ^ 56\<close>
  shows \<open>fuel_bound p < 2 ^ 57\<close>
proof -
  obtain s vs where e: \<open>encode_m p = (s, vs)\<close> by (cases \<open>encode_m p\<close>)
  note EC = encode_cnt[OF assms(1) e]
  define ws where \<open>ws = cvar_widths p\<close>
  define ds where \<open>ds = cdef_widths ws [] (CoreProblemL_defs p)\<close>
  have c: \<open>fst s + length (snd s) < 2 ^ 56\<close> using EC assms(2) by (simp add: ws_def ds_def)
  have w: \<open>\<forall>w \<in> set ws. w + 2 < 2 ^ 57\<close>
  proof
    fix w assume \<open>w \<in> set ws\<close>
    then have \<open>w \<le> sum_list ws\<close> by (rule member_le_sum_list; simp)
    then show \<open>w + 2 < 2 ^ 57\<close> using assms(2) by (simp add: ws_def)
  qed
  have cl: \<open>\<forall>c \<in> set (snd s). length c + 2 < 2 ^ 57\<close> using EC by (auto simp: cl4_def)
  have tb: \<open>\<forall>t \<in> set (CoreProblemL_defs p @ CoreProblemL_asserts p). tbound ws ds t < 2 ^ 57\<close>
  proof
    fix t assume \<open>t \<in> set (CoreProblemL_defs p @ CoreProblemL_asserts p)\<close>
    then have \<open>tbound ws ds t < 2 ^ 56\<close> using assms(6) by (simp add: ws_def ds_def)
    then show \<open>tbound ws ds t < 2 ^ 57\<close> by simp
  qed
  define X where \<open>X = {fst s + 2, length (snd s) + 2, 2 * (fst s + length (snd s)), 2 * length ws + 2, 2 * length (CoreProblemL_defs p) + 2,
           2 * length (CoreProblemL_asserts p) + 2} \<union> set (map (\<lambda>w. w + 2) ws) \<union>
          set (map (\<lambda>c. length c + 2) (snd s)) \<union>
          set (map (tbound ws ds) (CoreProblemL_defs p @ CoreProblemL_asserts p))\<close>
  have fin: \<open>finite X\<close> and ne: \<open>X \<noteq> {}\<close> by (simp_all add: X_def)
  have all: \<open>\<forall>x \<in> X. x < 2 ^ 57\<close>
  proof
    fix x assume \<open>x \<in> X\<close>
    then consider \<open>x = fst s + 2\<close> | \<open>x = length (snd s) + 2\<close>
      | \<open>x = 2 * (fst s + length (snd s))\<close> | \<open>x = 2 * length ws + 2\<close>
      | \<open>x = 2 * length (CoreProblemL_defs p) + 2\<close> | \<open>x = 2 * length (CoreProblemL_asserts p) + 2\<close>
      | \<open>x \<in> set (map (\<lambda>w. w + 2) ws)\<close> | \<open>x \<in> set (map (\<lambda>c. length c + 2) (snd s))\<close>
      | \<open>x \<in> set (map (tbound ws ds) (CoreProblemL_defs p @ CoreProblemL_asserts p))\<close>
      unfolding X_def by blast
    then show \<open>x < 2 ^ 57\<close>
    proof cases
      case 1 then show ?thesis using c by simp
    next
      case 2 then show ?thesis using c by simp
    next
      case 3 then show ?thesis using c by simp
    next
      case 4 then show ?thesis using assms(3) by (simp add: ws_def)
    next
      case 5 then show ?thesis using assms(4) by simp
    next
      case 6 then show ?thesis using assms(5) by simp
    next
      case 7 then show ?thesis using w by auto
    next
      case 8 then show ?thesis using cl by auto
    next
      case 9 then show ?thesis using tb by auto
    qed
  qed
  have M: \<open>Max X < 2 ^ 57\<close> using all by (simp add: Max_less_iff[OF fin ne])
  have F: \<open>fuel_bound p = Max X\<close>
    unfolding fuel_bound_def X_def ws_def ds_def by (simp only: Let_def e prod.case)
  show ?thesis using M F by simp
qed

text \<open>The elimination keeps the strict bound (as \<open>elim_fuel_lt\<close> keeps the other one).\<close>
lemma elim_fuel_lt57:
  assumes wt: \<open>cproblem_wt q\<close> and H: \<open>fb_hyps q\<close>
    and L: \<open>length (cvar_widths q) < 2 ^ 55\<close> \<open>length (CoreProblemL_defs q) < 2 ^ 55\<close>
      \<open>length (CoreProblemL_asserts q) < 2 ^ 55\<close>
  shows \<open>fuel_bound (fst (elim_m q)) < 2 ^ 57\<close>
proof -
  interpret E: elim_prob q by unfold_locales (use wt H in \<open>simp_all add: fb_hyps_def\<close>)
  note h = H[unfolded fb_hyps_def]
  have cc: \<open>sum_list (map (ccount E.ews E.eds) E.D2) \<le> sum_list (map (ccount E.ews E.eds) E.eD)\<close>
    by (rule sum_list_map_nth_le) (simp_all add: E.D2(1) E.en_def E.D2_size)
  have \<open>fuel_bound E.q2 < 2 ^ 57\<close>
  proof (rule fuel_bound_lt57)
    show \<open>cproblem_wt E.q2\<close> by (rule E.q2_wt)
    show \<open>2 + sum_list (cvar_widths E.q2) + length (CoreProblemL_asserts E.q2) +
       sum_list (map (ccount (cvar_widths E.q2) (cdef_widths (cvar_widths E.q2) [] (CoreProblemL_defs E.q2)))
                     (CoreProblemL_defs E.q2 @ CoreProblemL_asserts E.q2)) < 2 ^ 56\<close>
      using h cc E.D2_defs by (simp add: E.q2_ws E.q2_parts E.ews_def E.eds_def E.eD_def E.eA_def)
    show \<open>length (cvar_widths E.q2) < 2 ^ 55\<close> using L(1) by (simp add: E.q2_ws E.ews_def)
    show \<open>length (CoreProblemL_defs E.q2) < 2 ^ 55\<close> using L(2) E.D2(1) by (simp add: E.q2_parts E.en_def E.eD_def)
    show \<open>length (CoreProblemL_asserts E.q2) < 2 ^ 55\<close> using L(3) by (simp add: E.q2_parts E.eA_def)
    show \<open>\<forall>t \<in> set (CoreProblemL_defs E.q2 @ CoreProblemL_asserts E.q2).
         tbound (cvar_widths E.q2) (cdef_widths (cvar_widths E.q2) [] (CoreProblemL_defs E.q2)) t < 2 ^ 56\<close>
    proof
      fix t assume t: \<open>t \<in> set (CoreProblemL_defs E.q2 @ CoreProblemL_asserts E.q2)\<close>
      have T: \<open>\<forall>t \<in> set (E.eD @ E.eA). tbound E.ews E.eds t < 2 ^ 56\<close>
        using h by (simp add: E.ews_def E.eds_def E.eD_def E.eA_def)
      show \<open>tbound (cvar_widths E.q2) (cdef_widths (cvar_widths E.q2) [] (CoreProblemL_defs E.q2)) t < 2 ^ 56\<close>
      proof (cases \<open>t \<in> set E.eA\<close>)
        case True
        then show ?thesis using T E.D2_defs by (simp add: E.q2_ws E.q2_parts)
      next
        case False
        then obtain j where j: \<open>j < E.en\<close> \<open>t = E.D2 ! j\<close> using t E.D2(1) by (auto simp: E.q2_parts in_set_conv_nth)
        have \<open>tbound E.ews E.eds (E.eD ! j) < 2 ^ 56\<close> using T j(1) by (simp add: E.en_def)
        then show ?thesis using E.D2_size[OF j(1)] E.D2_defs j by (simp add: E.q2_ws E.q2_parts)
      qed
    qed
  qed
  then show ?thesis by (simp add: E.q2_def)
qed

text \<open>The elimination keeps the variables.\<close>
lemma elim_widths:
  assumes \<open>cproblem_wt q\<close> \<open>length (CoreProblemL_defs q) < 2 ^ 64\<close>
  shows \<open>cvar_widths (fst (elim_m q)) = cvar_widths q\<close>
proof -
  interpret E: elim_prob q by unfold_locales (use assms in simp_all)
  show ?thesis using E.q2_ws by (simp add: E.q2_def E.ews_def)
qed

context QFBV_ctx
begin

subsection \<open>The solver meets its contract\<close>

text \<open>\<^verbatim>\<open>solve\<close> passes the model of \<^verbatim>\<open>solve_core\<close> to \<^verbatim>\<open>reconstruct\<close>, which needs its
  vectors to be able to grow (\<^const>\<open>allvok\<close>): the contract of \<^verbatim>\<open>solve_core\<close> used by \<^verbatim>\<open>solve\<close>
  is \<^const>\<open>csolve_contract\<close> with that fact added to a model.\<close>
definition core_ok :: \<open>CoreProblemL \<Rightarrow> bool\<close> where
  \<open>core_ok q \<equiv> csize_bound q \<le> urust_fuel \<and> fuel_bound q < 2 ^ 57 \<and> (\<forall>w \<in> set (cvar_widths q). w < 2 ^ 56) \<and>
     dpll_fuel q < urust_fuel\<close>

definition csolve_contract_v :: \<open>CoreProblem \<Rightarrow> ('s, Answer, 'abort) function_contract\<close> where
  \<open>csolve_contract_v p \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>cproblem_wt (cprob_of p) \<and> core_ok (cprob_of p)\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>case r of
             Answer_Sat m \<Rightarrow> cis_model (cprob_of p) (vecs_of m) \<and> allvok m
           | Answer_Unsat \<Rightarrow> (\<forall>m. \<not> cis_model (cprob_of p) m)\<rangle>)\<close>

text \<open>The theorem: \<^const>\<open>csolve_contract_v\<close> holds whenever the translation's fuel covers
  \<^const>\<open>csize_bound\<close> and the search loop of \<^verbatim>\<open>dpll\<close> (\<^const>\<open>dpll_fuel\<close>), \<^const>\<open>fuel_bound\<close> is below
  \<open>2 ^ 57\<close> and the widths below \<open>2 ^ 56\<close>. For a well-sorted problem \<^const>\<open>csize_bound\<close> is at least
  \<^const>\<open>fuel_bound\<close> (\<open>fuel_bound_le\<close>), which the proof uses; a problem that is not well-sorted
  makes the precondition of the contract false.\<close>
theorem solve_core_spec_v:
  shows \<open>\<Gamma>; solve_core p \<Turnstile>\<^sub>F csolve_contract_v p\<close>
proof (cases \<open>cproblem_wt (cprob_of p) \<and> core_ok (cprob_of p)\<close>)
  case TT: True
  let ?P = \<open>cprob_of p\<close>
  have True: \<open>cproblem_wt ?P\<close> using TT by simp
  have assms: \<open>csize_bound ?P \<le> urust_fuel\<close> \<open>fuel_bound ?P < 2 ^ 57\<close>
    \<open>\<forall>w \<in> set (cvar_widths ?P). w < 2 ^ 56\<close> \<open>dpll_fuel ?P < urust_fuel\<close>
    using TT by (simp_all add: core_ok_def)
  have assms2: \<open>fuel_bound ?P \<le> urust_fuel\<close> \<open>fuel_bound ?P < 2 ^ 57\<close>
    using fuel_bound_le[OF True] assms by (simp_all add: le_trans)
  obtain s vs where e: \<open>encode_m ?P = (s, vs)\<close>
    by (cases \<open>encode_m ?P\<close>)
  note fb = fuel_bound_ge[OF e]
  have s64: \<open>fst s < 2 ^ 64\<close>
    using fb(1) assms2(2) by simp
  have dpll_pre:
      \<open>dpll_cs_ok (snd s) (fst s) \<and>
      length (snd s) + 2 \<le> urust_fuel \<and> length (snd s) < 2 ^ 64 \<and>
      fst s + 2 \<le> urust_fuel \<and> 3 ^ fst s < urust_fuel \<and>
      2 * length (snd s) \<le> urust_fuel \<and> 2 * length (snd s) < 2 ^ 57 \<and> 2 * fst s < 2 ^ 57\<close>
  proof -
    have \<open>2 * fst s + 2 * length (snd s) \<le> fuel_bound ?P\<close> using fb(6) by simp
    then have dbl: \<open>2 * length (snd s) \<le> urust_fuel \<and> 2 * length (snd s) < 2 ^ 57 \<and> 2 * fst s < 2 ^ 57\<close>
      using assms2 by linarith
    show ?thesis
      using encode_wf[OF True e s64] fb assms2 assms(4) e dbl
      by (fastforce simp: dpll_cs_ok_def dpll_fuel_def)
  qed
  have unsat': \<open>\<not> (\<exists>\<sigma>. cnf_sem \<sigma> (snd s)) \<Longrightarrow> \<forall>m. \<not> cis_model ?P m\<close>
    using unsat_answer[OF True e s64] by (auto simp: cis_model_def)
  have rm_pre:
      \<open>(\<forall>ls \<in> set vs. lits_lt (fst s) ls \<and> length ls + 2 \<le> urust_fuel \<and> length ls < 2 ^ 56) \<and>
      length vs + 2 \<le> urust_fuel \<and> length vs < 2 ^ 56\<close>
  proof -
    note w = encode_wf[OF True e s64]
    have lw: \<open>\<forall>ls \<in> set vs. length ls + 2 \<le> fuel_bound ?P \<and> length ls < 2 ^ 56\<close>
      using w fb(4) assms(3) by (auto simp add: in_set_conv_nth cvar_widths_def; meson nth_mem)
    moreover have \<open>2 * length vs + 2 \<le> fuel_bound ?P\<close>
      using w fb_facts(3)[of ?P] by simp
    ultimately show ?thesis
      using w assms2 by fastforce
  qed
  have sat': \<open>length a = fst s \<Longrightarrow> \<forall>v < length a. a ! v \<noteq> None \<Longrightarrow> cnf_sem (sigma_of a) (snd s) \<Longrightarrow>
      cis_model ?P (read_model_m a vs)\<close> for a
    using sat_answer[OF True e s64, of a] by (simp add: cis_model_def)
  show ?thesis
    apply (crush_boot f: solve_core_def contract: csolve_contract_v_def)
    apply (crush_base contracts add: encode_contract_def dpll_top_contract_def read_model_contract_def
        split: option.splits
        simp add: e assms2 TT st_of_def Cnf_Cnf_clauses_lens_view_update_modify Cnf_Cnf_num_vars_lens_view_update_modify)
    apply (all \<open>(use dpll_pre rm_pre unsat' sat' in \<open>auto simp: dpll_cs_ok_def\<close>)?\<close>)
    using assms(2) by simp
next
  case False
  then have F: \<open>(cproblem_wt (cprob_of p) \<and> core_ok (cprob_of p)) = False\<close> by simp
  show ?thesis
    apply (ucincl_discharge\<open>intro satisfies_function_contractI\<close>)
    apply (subst wp_sstriple_iff)
    apply (simp add: csolve_contract_v_def F apure_precise_False asepconj_bot_zero2 bot_aentails_all)
    done
qed

section \<open>Each step of the problem loop meets \<open>lower\<close>'s contract\<close>

text \<open>For every definition and assertion, the recursion depth is within the fuel and the rewriting
  precondition \<^const>\<open>lpre\<close> holds, because both are bounded by the weight of the term, hence by
  \<^const>\<open>size_bound\<close>.\<close>
lemma ldefs_step_pre:
  assumes \<open>problem_wt p\<close> \<open>size_bound p \<le> urust_fuel\<close> \<open>sizes_ok p\<close> \<open>j < length (ProblemL_defs p)\<close>
  shows \<open>Suc (size (ProblemL_defs p ! j)) \<le> urust_fuel \<and>
         lpre urust_fuel (var_widths p) (snd (foldl (ldefs_step p) (([], []), []) [0..<j]))
           (fst (foldl (ldefs_step p) (([], []), []) [0..<j])) (ProblemL_defs p ! j) \<and>
         snd (lower_m (var_widths p) (snd (foldl (ldefs_step p) (([], []), []) [0..<j]))
           (fst (foldl (ldefs_step p) (([], []), []) [0..<j])) (ProblemL_defs p ! j)) < 2 ^ 64\<close>
proof -
  let ?ws = \<open>var_widths p\<close> and ?D = \<open>ProblemL_defs p\<close> and ?A = \<open>ProblemL_asserts p\<close>
  let ?ds = \<open>def_widths ?ws [] ?D\<close>
  let ?dsj = \<open>def_widths ?ws [] (take j ?D)\<close>
  let ?SUM = \<open>sum_list (map (lweight ?ws ?ds) (?D @ ?A))\<close>
  obtain Lj dmj where f: \<open>foldl (ldefs_step p) (([], []), []) [0..<j] = (Lj, dmj)\<close>
    by (cases \<open>foldl (ldefs_step p) (([], []), []) [0..<j]\<close>)
  have jl: \<open>j < length ?D\<close> and jle: \<open>j \<le> length ?D\<close> using assms(4) by simp_all
  have dwt: \<open>defs_wt ?ws [] ?D\<close> using assms(1) by (simp add: problem_wt_def Let_def)
  have Bj: \<open>bnd Lj\<close> using ldefs_bnd[OF assms(1,3) jle] f by simp
  have inv: \<open>ldefs_inv p j (Lj, dmj)\<close> using ldefs_loop[OF dwt jle f Bj] .
  have lok: \<open>lok ?ws Lj\<close> and dmok: \<open>dm_ok ?dsj dmj Lj\<close> using inv by (simp_all add: ldefs_inv_def Let_def)
  have wtj: \<open>wt ?ws ?dsj (?D ! j)\<close> using QFBV_Lower.defs_wt_nth[OF dwt jl] .
  have R: \<open>foldl (ldefs_step p) (([], []), []) [0..<Suc j] =
           (fst (lower_m ?ws dmj Lj (?D ! j)), dmj @ [snd (lower_m ?ws dmj Lj (?D ! j))])\<close>
    using f by (simp add: ldefs_step_def split_def Let_def)
  have Bsuc: \<open>bnd (fst (lower_m ?ws dmj Lj (?D ! j)))\<close> using ldefs_bnd[OF assms(1,3), of \<open>Suc j\<close>] R assms(4) by simp
  have sb: \<open>1000000 * ?SUM \<le> size_bound p\<close> using size_bound_sum by simp
  have twj: \<open>lweight ?ws ?dsj (?D ! j) \<le> ?SUM\<close>
    using lweight_take[OF dwt jl] member_tw_app_le[of \<open>?D ! j\<close> ?D ?ws ?ds ?A] nth_mem[OF jl] by simp
  have twle: \<open>lweight ?ws ?dsj (?D ! j) \<le> urust_fuel\<close> using twj sb assms(2) by simp
  have sz: \<open>Suc (size (?D ! j)) \<le> urust_fuel\<close> using size_le_tw[of \<open>?D ! j\<close> ?ws ?dsj] twle by simp
  have subw: \<open>\<forall>u \<in> set (subterms (?D ! j)). width ?ws ?dsj u \<le> urust_fuel\<close>
  proof
    fix u assume \<open>u \<in> set (subterms (?D ! j))\<close>
    then have \<open>width ?ws ?dsj u \<le> lweight ?ws ?dsj (?D ! j)\<close> by (rule width_le_tw)
    then show \<open>width ?ws ?dsj u \<le> urust_fuel\<close> using twle by simp
  qed
  have lp: \<open>lpre urust_fuel ?ws dmj Lj (?D ! j)\<close> using lpre_intro[OF wtj lok dmok Bsuc subw] .
  have kb: \<open>snd (lower_m ?ws dmj Lj (?D ! j)) < 2 ^ 64\<close>
    using lower_m_correct[OF wtj lok dmok _ Bsuc] by (simp add: QFBV_Lower.env_ok_def)
  show ?thesis using sz lp kb f by simp
qed

lemma lasserts_step_pre:
  assumes \<open>problem_wt p\<close> \<open>size_bound p \<le> urust_fuel\<close> \<open>sizes_ok p\<close> \<open>i < length (ProblemL_asserts p)\<close>
  shows \<open>Suc (size (ProblemL_asserts p ! i)) \<le> urust_fuel \<and>
         lpre urust_fuel (var_widths p) (snd (ldefs_res p))
           (fst (foldl (lasserts_step p (snd (ldefs_res p))) (fst (ldefs_res p), []) [0..<i])) (ProblemL_asserts p ! i) \<and>
         snd (lower_m (var_widths p) (snd (ldefs_res p))
           (fst (foldl (lasserts_step p (snd (ldefs_res p))) (fst (ldefs_res p), []) [0..<i])) (ProblemL_asserts p ! i)) < 2 ^ 64\<close>
proof -
  let ?ws = \<open>var_widths p\<close> and ?D = \<open>ProblemL_defs p\<close> and ?A = \<open>ProblemL_asserts p\<close>
  let ?ds = \<open>def_widths ?ws [] ?D\<close>
  let ?SUM = \<open>sum_list (map (lweight ?ws ?ds) (?D @ ?A))\<close>
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
  have twi: \<open>lweight ?ws ?ds (?A ! i) \<le> ?SUM\<close>
    using member_le_sum_list[of \<open>lweight ?ws ?ds (?A ! i)\<close> \<open>map (lweight ?ws ?ds) (?D @ ?A)\<close>] nth_mem[OF il] by simp
  have twle: \<open>lweight ?ws ?ds (?A ! i) \<le> urust_fuel\<close> using twi sb assms(2) by simp
  have sz: \<open>Suc (size (?A ! i)) \<le> urust_fuel\<close> using size_le_tw[of \<open>?A ! i\<close> ?ws ?ds] twle by simp
  have subw: \<open>\<forall>u \<in> set (subterms (?A ! i)). width ?ws ?ds u \<le> urust_fuel\<close>
  proof
    fix u assume \<open>u \<in> set (subterms (?A ! i))\<close>
    then have \<open>width ?ws ?ds u \<le> lweight ?ws ?ds (?A ! i)\<close> by (rule width_le_tw)
    then show \<open>width ?ws ?ds u \<le> urust_fuel\<close> using twle by simp
  qed
  have lp: \<open>lpre urust_fuel ?ws ?dm Li (?A ! i)\<close> using lpre_intro[OF wti lok dmok Bsuc subw] .
  have kb: \<open>snd (lower_m ?ws ?dm Li (?A ! i)) < 2 ^ 64\<close>
    using lower_m_correct[OF wti lok dmok _ Bsuc] by (simp add: QFBV_Lower.env_ok_def)
  show ?thesis using sz lp kb f by simp
qed


subsection \<open>\<^verbatim>\<open>lower_problem\<close> computes the core problem\<close>

definition lp_pre :: \<open>Problem \<Rightarrow> bool\<close> where
  \<open>lp_pre p \<equiv> problem_wt (prob_of p) \<and> size_bound (prob_of p) \<le> urust_fuel \<and> sizes_ok (prob_of p)\<close>

lemma lp_lens:
  assumes \<open>lp_pre p\<close>
  shows \<open>rvec_length (Problem_defs p) \<le> urust_fuel\<close> \<open>rvec_length (Problem_defs p) < 2 ^ 56\<close>
    \<open>rvec_length (Problem_asserts p) \<le> urust_fuel\<close> \<open>rvec_length (Problem_asserts p) < 2 ^ 56\<close>
proof -
  have \<open>length (ProblemL_defs (prob_of p)) \<le> size_bound (prob_of p)\<close>
    \<open>length (ProblemL_asserts (prob_of p)) \<le> size_bound (prob_of p)\<close>
    by (simp_all add: size_bound_def Let_def)
  moreover have \<open>4 * length (ProblemL_defs (prob_of p)) \<le> ovf_bound (prob_of p)\<close>
    \<open>4 * length (ProblemL_asserts (prob_of p)) \<le> ovf_bound (prob_of p)\<close>
    by (simp_all add: ovf_bound_def Let_def)
  ultimately show \<open>rvec_length (Problem_defs p) \<le> urust_fuel\<close> \<open>rvec_length (Problem_defs p) < 2 ^ 56\<close>
    \<open>rvec_length (Problem_asserts p) \<le> urust_fuel\<close> \<open>rvec_length (Problem_asserts p) < 2 ^ 56\<close>
    using assms by (auto simp add: lp_pre_def sizes_ok_def)
qed

text \<open>Every state of the two loops is a prefix of the final one, so it is within \<^const>\<open>bnd\<close>.\<close>
lemma ldefs_part_pfx:
  assumes \<open>j \<le> length (ProblemL_defs p)\<close>
  shows \<open>pfx (fst (ldefs_part p j)) (fst (ldefs_res p))\<close>
proof -
  have e: \<open>[0..<length (ProblemL_defs p)] = [0..<j] @ [j..<length (ProblemL_defs p)]\<close>
    using assms by (metis le_add_diff_inverse upt_add_eq_append zero_le)
  obtain L dm where f: \<open>foldl (ldefs_step p) (ldefs_part p j) [j..<length (ProblemL_defs p)] = (L, dm)\<close>
    by (cases \<open>foldl (ldefs_step p) (ldefs_part p j) [j..<length (ProblemL_defs p)]\<close>)
  have \<open>ldefs_res p = (L, dm)\<close> using f e by (simp add: ldefs_res_def ldefs_part_def)
  then show ?thesis using ldefs_fold_pfx[of p \<open>fst (ldefs_part p j)\<close> \<open>snd (ldefs_part p j)\<close>] f by simp
qed

lemma lasserts_part_pfx:
  assumes \<open>i \<le> length (ProblemL_asserts p)\<close>
  shows \<open>pfx (fst (lasserts_part p i)) (fst (lasserts_res p))\<close>
proof -
  have e: \<open>[0..<length (ProblemL_asserts p)] = [0..<i] @ [i..<length (ProblemL_asserts p)]\<close>
    using assms by (metis le_add_diff_inverse upt_add_eq_append zero_le)
  obtain L cs where f: \<open>foldl (lasserts_step p (snd (ldefs_res p))) (lasserts_part p i) [i..<length (ProblemL_asserts p)] = (L, cs)\<close>
    by (cases \<open>foldl (lasserts_step p (snd (ldefs_res p))) (lasserts_part p i) [i..<length (ProblemL_asserts p)]\<close>)
  have \<open>lasserts_res p = (L, cs)\<close> using f e by (simp add: lasserts_res_def lasserts_part_def)
  then show ?thesis using lasserts_fold_pfx[of p _ \<open>fst (lasserts_part p i)\<close> \<open>snd (lasserts_part p i)\<close>] f by simp
qed

lemma ldefs_part_len:
  assumes \<open>problem_wt p\<close> \<open>sizes_ok p\<close> \<open>j \<le> length (ProblemL_defs p)\<close>
  shows \<open>length (fst (fst (ldefs_part p j))) < 2 ^ 56\<close>
  using bnd_pfx[OF pfx_trans[OF ldefs_part_pfx[OF assms(3)] ldefs_res_pfx] prob_bnd[OF assms(1,2)]]
  by (simp add: bnd_def)

lemma lasserts_part_len:
  assumes \<open>problem_wt p\<close> \<open>sizes_ok p\<close> \<open>i \<le> length (ProblemL_asserts p)\<close>
  shows \<open>length (fst (fst (lasserts_part p i))) < 2 ^ 56\<close>
  using bnd_pfx[OF lasserts_part_pfx[OF assms(3)] prob_bnd[OF assms(1,2)]]
  by (simp add: bnd_def)

definition lower_problem_contract :: \<open>Problem \<Rightarrow> ('s, CoreProblem, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>lower_problem_contract p \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>lp_pre p\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>cprob_of r = lower_problem_m (prob_of p)\<rangle>)\<close>

text \<open>The rewriting of a problem only calls \<^const>\<open>lower\<close> and builds references with \<^const>\<open>cref\<close>;
  narrow the automation to those two specifications so the loop proofs stay fast.\<close>
declare dpll_lit_value_spec dpll_lit_index_spec dpll_watch_init_spec dpll_find_watch_spec dpll_set_at_spec dpll_move_watch_spec dpll_visit_slot_spec dpll_visit_spec dpll_wpropagate_spec dpll_clause_status_spec dpll_propagate_pass_spec dpll_find_unassigned_spec dpll_backtrack_spec dpll_cut_spec dpll_top_spec dpll_read_bits_spec read_model_spec push_def_spec cnot_spec cbin_spec cite_spec cextract_spec cone_spec cneg_spec cmsb_spec cabs_spec cslt_spec csle_spec lower_bin_spec lit_const_spec lit_neg_spec fresh_fn_spec add_clause_spec clause3_spec clause2_spec gate_and_spec clause1_spec gate_or_spec gate_xor_spec gate_ite_spec gate_bitwise_spec bv_not_spec bv_const_spec bv_of_nat_spec bv_shift_const_spec bv_zext_spec bv_extract_spec bv_concat_spec bv_fresh_spec bv_bitwise_spec bv_add_spec bv_partial_spec bv_mul_spec bv_eq_spec bv_ult_spec bv_ite_spec bv_shift_spec bv_divrem_spec blast_bin_spec blast_spec encode_spec [crush_specs del]

lemma unat_succ_p:
  assumes \<open>unat (x :: 64 word) < n\<close> \<open>n < 2 ^ 64\<close>
  shows \<open>unat (x + 1) = Suc (unat x)\<close>
proof -
  have \<open>x \<noteq> -1\<close> using assms by (auto simp: unat_minus_one_word)
  then show ?thesis by (rule unat_Suc2)
qed

lemma size_term_of_p: \<open>size (term_of t) = size t\<close>
  by (induction t) simp_all

lemma ldefs_part_snd_len: \<open>length (snd (ldefs_part p j)) = j\<close>
  by (induction j) (simp_all add: split_def Let_def)

lemma lasserts_part_snd_len: \<open>length (snd (lasserts_part p i)) = i\<close>
  by (induction i) (simp_all add: split_def Let_def)

lemma lower_problem_spec [crush_specs]:
  shows \<open>\<Gamma>; lower_problem p \<Turnstile>\<^sub>F lower_problem_contract p\<close>
proof (cases \<open>lp_pre p\<close>)
  case True
  let ?P = \<open>prob_of p\<close>
  note pre = True[unfolded lp_pre_def]
  note L = lp_lens[OF True]
  note SP = ldefs_step_pre[OF conjunct1[OF pre] conjunct1[OF conjunct2[OF pre]] conjunct2[OF conjunct2[OF pre]],
      folded ldefs_part_def]
  note AP = lasserts_step_pre[OF conjunct1[OF pre] conjunct1[OF conjunct2[OF pre]] conjunct2[OF conjunct2[OF pre]],
      folded lasserts_part_def]
  have ws: \<open>map unat (rvec_elems (Problem_widths p)) = var_widths ?P\<close> by (simp add: var_widths_def)
  have D: \<open>ProblemL_defs ?P ! j = term_of (rvec_elems (Problem_defs p) ! j)\<close> if \<open>j < rvec_length (Problem_defs p)\<close> for j
    using that by simp
  have A: \<open>ProblemL_asserts ?P ! i = term_of (rvec_elems (Problem_asserts p) ! i)\<close> if \<open>i < rvec_length (Problem_asserts p)\<close> for i
    using that by simp
  have SPd: \<open>Suc (size (rvec_elems (Problem_defs p) ! j)) \<le> urust_fuel \<and>
      lpre urust_fuel (var_widths ?P) (snd (ldefs_part ?P j)) (fst (ldefs_part ?P j)) (term_of (rvec_elems (Problem_defs p) ! j)) \<and>
      snd (lower_m (var_widths ?P) (snd (ldefs_part ?P j)) (fst (ldefs_part ?P j)) (term_of (rvec_elems (Problem_defs p) ! j))) < 2 ^ 64 \<and>
      length (fst (fst (lower_m (var_widths ?P) (snd (ldefs_part ?P j)) (fst (ldefs_part ?P j)) (term_of (rvec_elems (Problem_defs p) ! j))))) < 2 ^ 56\<close>
    if \<open>j < rvec_length (Problem_defs p)\<close> for j
  proof -
    have l: \<open>length (fst (fst (ldefs_part ?P (Suc j)))) < 2 ^ 56\<close>
      using ldefs_part_len[OF conjunct1[OF pre] conjunct2[OF conjunct2[OF pre]], of \<open>Suc j\<close>] that by simp
    show ?thesis using SP[of j] that l D[OF that] by (simp add: size_term_of_p split_def Let_def)
  qed
  have APd: \<open>Suc (size (rvec_elems (Problem_asserts p) ! i)) \<le> urust_fuel \<and>
      lpre urust_fuel (var_widths ?P) (snd (ldefs_res ?P)) (fst (lasserts_part ?P i)) (term_of (rvec_elems (Problem_asserts p) ! i)) \<and>
      snd (lower_m (var_widths ?P) (snd (ldefs_res ?P)) (fst (lasserts_part ?P i)) (term_of (rvec_elems (Problem_asserts p) ! i))) < 2 ^ 64 \<and>
      length (fst (fst (lower_m (var_widths ?P) (snd (ldefs_res ?P)) (fst (lasserts_part ?P i)) (term_of (rvec_elems (Problem_asserts p) ! i))))) < 2 ^ 56\<close>
    if \<open>i < rvec_length (Problem_asserts p)\<close> for i
  proof -
    have l: \<open>length (fst (fst (lasserts_part ?P (Suc i)))) < 2 ^ 56\<close>
      using lasserts_part_len[OF conjunct1[OF pre] conjunct2[OF conjunct2[OF pre]], of \<open>Suc i\<close>] that by simp
    show ?thesis using AP[of i] that l A[OF that] by (simp add: size_term_of_p split_def Let_def)
  qed
  have DL: \<open>length (ProblemL_defs ?P) = rvec_length (Problem_defs p)\<close> by simp
  have AL: \<open>length (ProblemL_asserts ?P) = rvec_length (Problem_asserts p)\<close> by simp
  have UL: \<open>rvec_length (Problem_defs p) < 2 ^ 64\<close> \<open>rvec_length (Problem_asserts p) < 2 ^ 64\<close>
    using L(2,4) by simp_all
  have WD: \<open>unat (word_of_nat (rvec_length (Problem_defs p)) :: 64 word) = rvec_length (Problem_defs p)\<close>
    using UL(1) by (simp add: unat_of_nat_eq)
  have WA: \<open>unat (word_of_nat (rvec_length (Problem_asserts p)) :: 64 word) = rvec_length (Problem_asserts p)\<close>
    using UL(2) by (simp add: unat_of_nat_eq)
  note L' = L[simplified]
  have PR: \<open>ldefs_part ?P (rvec_length (Problem_defs p)) = ldefs_res ?P\<close>
    using ldefs_part_res[of ?P] by simp
  have AR: \<open>lasserts_part ?P (rvec_length (Problem_asserts p)) = lasserts_res ?P\<close>
    using lasserts_part_res[of ?P] by simp
  have I1: \<open>\<And>j. j < rvec_length (Problem_defs p) \<Longrightarrow> Suc j < 2 ^ 64\<close> using L(2) by simp
  have I2: \<open>\<And>i. i < rvec_length (Problem_asserts p) \<Longrightarrow> Suc i < 2 ^ 64\<close> using L(4) by simp
  have FIN: \<open>cprob_of (make_CoreProblem w d a) = lower_problem_m ?P\<close>
    if \<open>rvec_elems w = rvec_elems (Problem_widths p)\<close>
      \<open>map ct_of (rvec_elems d) = fst (fst (lasserts_res ?P))\<close> \<open>map ct_of (rvec_elems a) = snd (lasserts_res ?P)\<close> for w d a
    using that by (simp add: lower_problem_m_eq)
  show ?thesis
    apply (crush_boot f: lower_problem_def contract: lower_problem_contract_def)
    apply (crush_base)
    subgoal for l_ref dm_ref j_ref
      apply (ucincl_discharge\<open>rule_tac
        INV=\<open>\<lambda>c. \<Squnion>gl l gd dm gj j. l_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>l \<star> dm_ref \<mapsto>\<langle>\<top>\<rangle> gd\<down>dm \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star>
             can_alloc_reference \<star>
             \<langle>unat j \<le> rvec_length (Problem_defs p) \<and> lower_ok l \<and> lst_of l = fst (ldefs_part ?P (unat j)) \<and>
              map unat (rvec_elems dm) = snd (ldefs_part ?P (unat j)) \<and> vok dm \<and> rvec_length dm = unat j \<and>
              rvec_length (Problem_defs p) - unat j \<le> c\<rangle>\<close> and
        INV'=\<open>\<lambda>c. \<Squnion>gl l gd dm gj j. l_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>l \<star> dm_ref \<mapsto>\<langle>\<top>\<rangle> gd\<down>dm \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star>
             can_alloc_reference \<star>
             \<langle>unat j < rvec_length (Problem_defs p) \<and> lower_ok l \<and> lst_of l = fst (ldefs_part ?P (unat j)) \<and>
              map unat (rvec_elems dm) = snd (ldefs_part ?P (unat j)) \<and> vok dm \<and> rvec_length dm = unat j \<and>
              rvec_length dm < 2 ^ 56 \<and>
              rvec_length (Problem_defs p) - unat j \<le> Suc c\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_bounded_while_framedI\<close>)
      apply (crush_base simp add: ws SPd push_not_None low_res_def word_less_nat_alt)
      apply (all \<open>(simp only: unat_succ_p[OF _ UL(1)])?\<close>)
      apply (auto simp add: lst_of_def split_def Let_def ldefs_part_snd_len unat_of_nat_eq SPd prod_eq_iff push_the L' WD SPd[simplified])
      subgoal using L(2) by simp
      subgoal for gl l gd dm gj j asserts_ref i_ref
        apply (ucincl_discharge\<open>rule_tac
          INV=\<open>\<lambda>c. \<Squnion>gl l gd dm ga asl gi i. l_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>l \<star> dm_ref \<mapsto>\<langle>\<top>\<rangle> gd\<down>dm \<star>
               asserts_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>asl \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star>
               \<langle>unat i \<le> rvec_length (Problem_asserts p) \<and> lower_ok l \<and> lst_of l = fst (lasserts_part ?P (unat i)) \<and>
                map unat (rvec_elems dm) = snd (ldefs_res ?P) \<and>
                map ct_of (rvec_elems asl) = snd (lasserts_part ?P (unat i)) \<and> vok asl \<and> rvec_length asl = unat i \<and>
                rvec_length (Problem_asserts p) - unat i \<le> c\<rangle>\<close> and
          INV'=\<open>\<lambda>c. \<Squnion>gl l gd dm ga asl gi i. l_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>l \<star> dm_ref \<mapsto>\<langle>\<top>\<rangle> gd\<down>dm \<star>
               asserts_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>asl \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star>
               \<langle>unat i < rvec_length (Problem_asserts p) \<and> lower_ok l \<and> lst_of l = fst (lasserts_part ?P (unat i)) \<and>
                map unat (rvec_elems dm) = snd (ldefs_res ?P) \<and>
                map ct_of (rvec_elems asl) = snd (lasserts_part ?P (unat i)) \<and> vok asl \<and> rvec_length asl = unat i \<and>
                rvec_length asl < 2 ^ 56 \<and>
                rvec_length (Problem_asserts p) - unat i \<le> Suc c\<rangle>\<close> and
          \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
          in wp_bounded_while_framedI\<close>)
        apply (crush_base simp add: ws APd push_not_None low_res_def word_less_nat_alt Lower_Lower_defs_focus_view_update_modify Lower_Lower_defs_lens_view_update_modify)
        apply (all \<open>(simp only: unat_succ_p[OF _ UL(2)])?\<close>)
        apply (auto simp add: lst_of_def split_def Let_def lasserts_part_snd_len unat_of_nat_eq APd prod_eq_iff push_the L' WA PR AR APd[simplified])
        subgoal using L(4) by simp
        subgoal by (simp add: lower_problem_m_eq)
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
  fuel covers \<^const>\<open>size_bound\<close>, which is expressed on the problem alone, and exceeds
  \<^const>\<open>dpll_fuel\<close> of the rewritten problem after the elimination of its unconstrained
  definitions, the bound of the search loop of \<^verbatim>\<open>dpll\<close>.\<close>
text \<open>\<^const>\<open>solve\<close> only calls \<^const>\<open>lower_problem\<close>, \<^const>\<open>elim\<close>, \<^const>\<open>solve_core\<close> and
  \<^const>\<open>reconstruct\<close>; their specifications are given to the automation explicitly.\<close>
declare lower_spec cref_spec lower_problem_spec [crush_specs del]

theorem solve_spec:
  assumes \<open>size_bound (prob_of p) \<le> urust_fuel\<close> \<open>sizes_ok (prob_of p)\<close>
    \<open>dpll_fuel (fst (elim_m (lower_problem_m (prob_of p)))) < urust_fuel\<close>
  shows \<open>\<Gamma>; solve p \<Turnstile>\<^sub>F solve_contract p\<close>
proof (cases \<open>problem_wt (prob_of p)\<close>)
  case True
  let ?P = \<open>prob_of p\<close>
  have bnd: \<open>bnd (fst (lasserts_res ?P))\<close> using prob_bnd[OF True assms(2)] .
  \<comment> \<open>Abstract the rewritten problem and its elimination to variables, so the automation works on
      a small goal instead of the (very large) unfolded \<^term>\<open>lower_problem_m ?P\<close>.\<close>
  obtain q where q: \<open>lower_problem_m ?P = q\<close> by blast
  obtain q2 kd mk where e: \<open>elim_m q = (q2, kd, mk)\<close> by (cases \<open>elim_m q\<close>) auto
  have sz: \<open>csize_bound q \<le> urust_fuel\<close> using lower_size_bound[OF True bnd] assms(1) q by simp
  have cwt: \<open>cproblem_wt q\<close> using lower_problem_correct(1)[OF True bnd] q by simp
  have H: \<open>fb_hyps q\<close> using lower_fb_hyps[OF True assms(2)] q by simp
  note LL = lower_lens55[OF True assms(2), unfolded q]
  have fq: \<open>fuel_bound q \<le> urust_fuel\<close> using fuel_bound_le[OF cwt] sz by simp
  note EF = elim_facts[OF cwt H fq e]
  have f57: \<open>fuel_bound q2 < 2 ^ 57\<close> using elim_fuel_lt57[OF cwt H LL(1-3)] e by simp
  have ws2: \<open>cvar_widths q2 = cvar_widths q\<close> using elim_widths[OF cwt] LL(2) e by simp
  have ok2: \<open>core_ok q2\<close>
    using EF(3) sz f57 ws2 LL(4) assms(3) q e by (simp add: core_ok_def)
  have cm: \<open>cis_model q m = is_model ?P m\<close> for m using lower_problem_correct(2)[OF True bnd] q by simp
  have unsat: \<open>\<forall>m. \<not> cis_model q2 m \<Longrightarrow> \<forall>m. \<not> is_model ?P m\<close> using EF(5) cm by blast
  have SP: \<open>map unat kind = kd \<Longrightarrow> map unat mark = mk \<Longrightarrow> cis_model q2 m2 \<Longrightarrow>
      recon_pre urust_fuel q (map unat kind) (map unat mark) q2 m2\<close>
    \<open>map unat kind = kd \<Longrightarrow> map unat mark = mk \<Longrightarrow> cis_model q2 m2 \<Longrightarrow>
      is_model ?P (reconstruct_m q (map unat kind) (map unat mark) q2 m2)\<close> for kind mark :: \<open>64 word list\<close> and m2
    using EF(6)[of m2] cm by simp_all
  show ?thesis
    apply (crush_boot f: solve_def contract: solve_contract_def)
    apply (crush_base specs add: lower_problem_spec elim_spec solve_core_spec_v reconstruct_spec
        contracts add: lower_problem_contract_def elim_contract_def csolve_contract_v_def reconstruct_contract_def
        simp add: lp_pre_def True assms q cwt fq H EF(2) ok2 e split: Answer.splits)
    apply (all \<open>use unsat SP in \<open>auto split: Answer.splits\<close>\<close>)
    done
next
  case False
  then have F: \<open>problem_wt (prob_of p) = False\<close> by simp
  show ?thesis
    apply (ucincl_discharge\<open>intro satisfies_function_contractI\<close>)
    apply (subst wp_sstriple_iff)
    apply (simp add: solve_contract_def Let_def F apure_precise_False asepconj_bot_zero2 bot_aentails_all)
    done
qed

end

subsection \<open>The specification over all instances with enough fuel\<close>

context QFBV_heap
begin

text \<open>\<^verbatim>\<open>QFBV_heap\<close> has the assumptions of \<^locale>\<open>QFBV_ctx\<close> (it drops only the fuel, which carries
  no assumption), so its parameters with any fuel form an instance of \<^locale>\<open>QFBV_ctx\<close> and the
  contract lemmas of \<^locale>\<open>QFBV_ctx\<close> apply.\<close>
lemma QFBV_ctxI:
  \<open>QFBV_ctx update_raw_fun dereference_raw_fun reference_raw_fun points_to_raw' gref_can_store
     new_gref_can_store can_alloc_reference prism_1 prism_2 prism_3 prism_4 prism_5 prism_6
     prism_7 prism_8 prism_9 prism_10 prism_11 prism_12 prism_13 prism_14 prism_15 prism_16 prism_17\<close>
  by intro_locales

text \<open>The statement of the specification, \<^const>\<open>solve_correct\<close> in \<^verbatim>\<open>QFBV_Spec\<close>. The bound on
  the fuel is \<^const>\<open>size_bound\<close> \<open>p\<close> plus \<^const>\<open>dpll_fuel\<close> of the rewritten problem after the
  elimination, which
  \<open>QFBV_ctx.solve_spec\<close> needs; \<^const>\<open>sizes_ok\<close> supplies its bounds.\<close>
theorem solve_correct:
  shows \<open>solve_correct \<Gamma>\<close>
proof (unfold solve_correct_def, intro allI impI)
  fix p :: Problem
  assume \<open>problem_wt (prob_of p) \<and> sizes_ok (prob_of p)\<close>
  then have ov: \<open>sizes_ok (prob_of p)\<close> by simp
  have \<open>\<Gamma>; solve fuel p \<Turnstile>\<^sub>F solve_contract p\<close>
    if \<open>size_bound (prob_of p) + Suc (dpll_fuel (fst (elim_m (lower_problem_m (prob_of p))))) \<le> fuel\<close> for fuel
    by (rule QFBV_ctx.solve_spec[OF QFBV_ctxI _ ov]) (use that in simp_all)
  then show \<open>\<exists>N. \<forall>fuel \<ge> N. \<Gamma>; solve fuel p \<Turnstile>\<^sub>F solve_contract p\<close>
    by (intro exI[of _ \<open>size_bound (prob_of p) + Suc (dpll_fuel (fst (elim_m (lower_problem_m (prob_of p)))))\<close>]) simp
qed

end

end
