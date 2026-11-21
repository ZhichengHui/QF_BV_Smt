theory QFBV_Bound
  imports QFBV_Defs
begin

section \<open>The size bound of the specification covers the fuel\<close>

text \<open>
  \<^const>\<open>fuel_bound\<close> is defined from the CNF formula that the encoding produces. Here it is shown to
  be at most \<^const>\<open>csize_bound\<close>, which only mentions the problem. The CNF formula is bounded by
  following the encoding: each circuit adds a number of variables and clauses polynomial in the
  cwidth of its operands.
\<close>

subsection \<open>Growth of the CNF state\<close>

text \<open>The clauses of \<open>s\<close> have at most 4 literals.\<close>
definition cl4 :: \<open>st \<Rightarrow> bool\<close> where
  \<open>cl4 s \<equiv> \<forall>c \<in> set (snd s). length c \<le> 4\<close>

text \<open>From \<open>s\<close> to \<open>s'\<close>, the number of variables plus the number of clauses grows by at most \<open>n\<close>,
  and short clauses stay short.\<close>
definition grows :: \<open>nat \<Rightarrow> st \<Rightarrow> st \<Rightarrow> bool\<close> where
  \<open>grows n s s' \<equiv> fst s' + length (snd s') \<le> fst s + length (snd s) + n \<and> (cl4 s \<longrightarrow> cl4 s')\<close>

lemma grows_refl: \<open>grows 0 s s\<close>
  by (simp add: grows_def)

lemma grows_trans: \<open>grows a s s1 \<Longrightarrow> grows b s1 s2 \<Longrightarrow> grows (a + b) s s2\<close>
  unfolding grows_def by auto

lemma grows_mono: \<open>grows a s s' \<Longrightarrow> a \<le> b \<Longrightarrow> grows b s s'\<close>
  unfolding grows_def by auto

lemma grows_any: \<open>grows n s s\<close>
  using grows_mono[OF grows_refl] by simp

lemma foldl_grows:
  fixes g :: \<open>'a \<Rightarrow> st\<close>
  assumes \<open>\<And>x i. Q x \<Longrightarrow> Q (f x i) \<and> grows k (g x) (g (f x i))\<close>
  shows \<open>Q x \<Longrightarrow> Q (foldl f x xs) \<and> grows (k * length xs) (g x) (g (foldl f x xs))\<close>
proof (induction xs arbitrary: x)
  case Nil
  then show ?case by (simp add: grows_refl)
next
  case (Cons a xs)
  have h: \<open>Q (f x a)\<close> \<open>grows k (g x) (g (f x a))\<close> using assms Cons.prems by blast+
  note IH = Cons.IH[OF h(1)]
  show ?case using IH grows_trans[OF h(2) conjunct2[OF IH]] by (simp add: algebra_simps)
qed

lemma foldl_grows_fst:
  fixes f :: \<open>st \<times> 'b \<Rightarrow> 'c \<Rightarrow> st \<times> 'b\<close>
  assumes \<open>\<And>x i. grows k (fst x) (fst (f x i))\<close> \<open>s = fst x\<close>
  shows \<open>grows (k * length xs) s (fst (foldl f x xs))\<close>
proof -
  have h: \<open>\<And>x i. True \<Longrightarrow> True \<and> grows k (fst x) (fst (f x i))\<close> using assms by simp
  show ?thesis
    using foldl_grows[where g = fst and f = f and x = x and xs = xs and Q = \<open>\<lambda>_. True\<close> and k = k, OF h TrueI]
      assms(2)
    by simp
qed

lemma foldl_len_snd:
  fixes f :: \<open>st \<times> 'b list \<Rightarrow> 'c \<Rightarrow> st \<times> 'b list\<close>
  assumes \<open>\<And>x i. length (snd (f x i)) = Suc (length (snd x))\<close>
  shows \<open>length (snd (foldl f x xs)) = length (snd x) + length xs\<close>
  by (induction xs arbitrary: x) (simp_all add: assms)

lemma foldl_len_r:
  fixes f :: \<open>st \<times> 'b list \<times> 'd \<Rightarrow> 'c \<Rightarrow> st \<times> 'b list \<times> 'd\<close>
  assumes \<open>\<And>x i. length (fst (snd (f x i))) = Suc (length (fst (snd x)))\<close>
  shows \<open>length (fst (snd (foldl f x xs))) = length (fst (snd x)) + length xs\<close>
  by (induction xs arbitrary: x) (simp_all add: assms)

lemma fresh_grows: \<open>grows 1 s (fst (fresh_m s))\<close>
  by (simp add: fresh_m_def grows_def cl4_def)

lemma addc_grows: \<open>length c \<le> 4 \<Longrightarrow> grows 1 s (addc_m s c)\<close>
  by (simp add: addc_m_def grows_def cl4_def)

lemma and_grows: \<open>grows 4 s (fst (and_m s a b))\<close>
  by (simp add: and_m_def and_t_def fresh_m_def addc_m_def grows_def cl4_def split_def Let_def)

lemma or_grows: \<open>grows 4 s (fst (or_m s a b))\<close>
  using and_grows[of s \<open>lneg a\<close> \<open>lneg b\<close>] by (simp add: or_m_def split_def Let_def)

lemma xor_grows: \<open>grows 5 s (fst (xor_m s a b))\<close>
  by (simp add: xor_m_def xor_t_def fresh_m_def addc_m_def grows_def cl4_def split_def Let_def)

lemma ite_grows: \<open>grows 5 s (fst (ite_m s c a b))\<close>
proof -
  have \<open>grows 5 s (fst (ite_t s c a b))\<close>
    by (simp add: ite_t_def fresh_m_def addc_m_def grows_def cl4_def split_def Let_def)
  moreover have \<open>grows 5 s (fst (and_m s c' b'))\<close> \<open>grows 5 s (fst (or_m s c' b'))\<close> for c' b'
    using grows_mono[OF and_grows] grows_mono[OF or_grows] by simp_all
  ultimately show ?thesis
    using xor_grows[of s c a] grows_any[of 5 s] by (simp add: ite_m_def split_def Let_def)
qed

lemma bitw_grows: \<open>grows 5 s (fst (bitw_m op s a b))\<close>
proof -
  have \<open>grows 5 s (fst (and_m s a b))\<close> \<open>grows 5 s (fst (or_m s a b))\<close>
    using grows_mono[OF and_grows] grows_mono[OF or_grows] by simp_all
  then show ?thesis using xor_grows by (cases op) (simp_all add: bitw_m_def)
qed

lemma fresh_vec_grows: \<open>grows w s (fst (fresh_vec_m s w))\<close>
  by (simp add: fresh_vec_m_def grows_def cl4_def)

subsection \<open>Circuits\<close>

lemma bitwise_m_grows:
  \<open>grows (5 * length a) s (fst (bitwise_m op s a b)) \<and> length (snd (bitwise_m op s a b)) = length a\<close>
proof -
  have \<open>grows (5 * length [0..<length a]) s (fst (bitwise_m op s a b))\<close>
    unfolding bitwise_m_def
    by (rule foldl_grows_fst)
       (auto simp: split_def Let_def intro: bitw_grows)
  moreover have \<open>length (snd (bitwise_m op s a b)) = length a\<close>
    unfolding bitwise_m_def
    by (rule trans[OF foldl_len_snd]) (simp_all add: split_def Let_def)
  ultimately show ?thesis by simp
qed

lemma add_step_grows: \<open>grows 15 (fst x) (fst (add_step a b x i))\<close>
proof -
  obtain s r c where x: \<open>x = (s, r, c)\<close> by (metis prod_cases3)
  show ?thesis
    unfolding x add_step_def
    by (simp add: split_def Let_def,
        rule grows_mono[OF grows_trans[OF grows_trans[OF xor_grows xor_grows] ite_grows]], simp)
qed

lemma add_m_grows:
  \<open>grows (15 * length a) s (fst (add_m s a b c)) \<and> length (fst (snd (add_m s a b c))) = length a\<close>
proof -
  have \<open>grows (15 * length [0..<length a]) s (fst (add_m s a b c))\<close>
    unfolding add_m_def
    by (rule foldl_grows_fst) (simp_all add: add_step_grows)
  moreover have \<open>length (fst (snd (add_m s a b c))) = length a\<close>
    unfolding add_m_def
    by (rule trans[OF foldl_len_r]) (simp_all add: add_step_def split_def Let_def)
  ultimately show ?thesis by simp
qed

lemma partial_m_grows:
  \<open>grows (4 * length a) s (fst (partial_m s a bi i)) \<and> length (snd (partial_m s a bi i)) = length a\<close>
proof -
  have \<open>grows (4 * length [0..<length a]) s (fst (partial_m s a bi i))\<close>
    unfolding partial_m_def
    by (rule foldl_grows_fst)
       (auto simp: split_def Let_def grows_any intro: grows_mono[OF and_grows])
  moreover have \<open>length (snd (partial_m s a bi i)) = length a\<close>
    unfolding partial_m_def
    by (rule trans[OF foldl_len_snd]) (simp_all add: split_def Let_def)
  ultimately show ?thesis by simp
qed

lemma mul_step_grows:
  assumes \<open>length (snd x) = length a\<close>
  shows \<open>length (snd (mul_step a b x i)) = length a \<and> grows (19 * length a) (fst x) (fst (mul_step a b x i))\<close>
proof -
  obtain s acc where x: \<open>x = (s, acc)\<close> by (cases x)
  obtain s1 p where P: \<open>partial_m s a (b ! i) i = (s1, p)\<close> by (cases \<open>partial_m s a (b ! i) i\<close>)
  obtain s2 sm c where A: \<open>add_m s1 acc p (lconst False) = (s2, sm, c)\<close> by (metis prod_cases3)
  have pg: \<open>grows (4 * length a) s s1\<close> \<open>length p = length a\<close>
    using partial_m_grows[where s = s and a = a and bi = \<open>b ! i\<close> and i = i] by (simp_all add: P)
  have ag: \<open>grows (15 * length acc) s1 s2\<close> \<open>length sm = length acc\<close>
    using add_m_grows[where s = s1 and a = acc and b = p and c = \<open>lconst False\<close>] by (simp_all add: A)
  have la: \<open>length acc = length a\<close> using assms x by simp
  have m: \<open>mul_step a b (s, acc) i = (s2, sm)\<close> by (simp add: mul_step_def P A)
  have tr: \<open>grows (4 * length a + 15 * length a) s s2\<close>
    using grows_trans[OF pg(1) ag(1)] la by simp
  show ?thesis
    unfolding x m using grows_mono[OF tr, of \<open>19 * length a\<close>] ag(2) la by simp
qed

lemma mul_m_grows:
  \<open>grows (19 * length a * length a) s (fst (mul_m s a b)) \<and> length (snd (mul_m s a b)) = length a\<close>
proof -
  have Q0: \<open>length (snd (s, replicate (length a) (lconst False))) = length a\<close> by simp
  have \<open>length (snd (mul_m s a b)) = length a \<and>
      grows (19 * length a * length [0..<length a]) (fst (s, replicate (length a) (lconst False)))
        (fst (mul_m s a b))\<close>
    unfolding mul_m_def
    using foldl_grows[where g = fst and Q = \<open>\<lambda>x. length (snd x) = length a\<close> and f = \<open>mul_step a b\<close>
        and k = \<open>19 * length a\<close> and xs = \<open>[0..<length a]\<close>
        and x = \<open>(s, replicate (length a) (lconst False))\<close>, OF mul_step_grows Q0]
    by simp
  then show ?thesis by simp
qed

lemma eq_step_grows: \<open>grows 9 (fst x) (fst (eq_step a b x i))\<close>
proof -
  obtain s r where x: \<open>x = (s, r)\<close> by (cases x)
  show ?thesis
    unfolding x eq_step_def
    by (simp add: split_def Let_def,
        rule grows_mono[OF grows_trans[OF xor_grows and_grows]], simp)
qed

lemma eq_m_grows: \<open>grows (9 * length a) s (fst (eq_m s a b))\<close>
proof -
  have \<open>grows (9 * length [0..<length a]) s (fst (eq_m s a b))\<close>
    unfolding eq_m_def
    by (rule foldl_grows_fst) (simp_all add: eq_step_grows)
  then show ?thesis by simp
qed

lemma ult_m_grows: \<open>grows (15 * length a) s (fst (ult_m s a b))\<close>
  using add_m_grows[where s = s and a = a and b = \<open>not_m b\<close> and c = \<open>lconst True\<close>] by (simp add: ult_m_def split_def Let_def)

lemma ite_vec_m_grows:
  \<open>grows (5 * length a) s (fst (ite_vec_m s c a b)) \<and> length (snd (ite_vec_m s c a b)) = length a\<close>
proof -
  have \<open>grows (5 * length [0..<length a]) s (fst (ite_vec_m s c a b))\<close>
    unfolding ite_vec_m_def
    by (rule foldl_grows_fst)
       (auto simp: split_def Let_def intro: ite_grows)
  moreover have \<open>length (snd (ite_vec_m s c a b)) = length a\<close>
    unfolding ite_vec_m_def
    by (rule trans[OF foldl_len_snd]) (simp_all add: split_def Let_def)
  ultimately show ?thesis by simp
qed

text \<open>The number of stages of the barrel shifter on width \<open>n\<close>: the least \<open>i\<close> with \<open>n \<le> 2^i\<close>; stage
  \<open>i\<close> is taken exactly when \<open>i\<close> is below it.\<close>

lemma nst_le: \<open>nst n \<le> n\<close>
  unfolding nst_def by (rule Least_le) (rule less_imp_le[OF less_exp])

lemma nst_ge: \<open>n \<le> 2 ^ nst n\<close>
  unfolding nst_def by (rule LeastI[where P = \<open>\<lambda>i. n \<le> 2 ^ i\<close> and k = n]) (rule less_imp_le[OF less_exp])

lemma nst_stage: \<open>2 ^ i < n \<longleftrightarrow> i < nst n\<close>
proof
  assume i: \<open>2 ^ i < n\<close>
  show \<open>i < nst n\<close>
  proof (rule ccontr)
    assume \<open>\<not> i < nst n\<close>
    then have \<open>(2::nat) ^ nst n \<le> 2 ^ i\<close> by (intro power_increasing) simp_all
    then show False using nst_ge[of n] i by linarith
  qed
next
  assume \<open>i < nst n\<close>
  then show \<open>2 ^ i < n\<close> unfolding nst_def using not_less_Least by fastforce
qed

lemma nst_mono_le: \<open>n \<le> 2 ^ k \<Longrightarrow> nst n \<le> k\<close>
  unfolding nst_def by (rule Least_le)

lemma or_m_grows': \<open>grows 4 s (fst (or_m s a b))\<close>
  using or_grows by simp

lemma shift_fold_grows:
  \<open>k \<le> length b \<Longrightarrow>
   (\<lambda>(s1, r1, g1, p1). grows (5 * length a * min k (nst (length a)) + 4 * k) s s1 \<and> length r1 = length a \<and>
      (2 ^ k < length a \<longrightarrow> p1 = 2 ^ k) \<and> (\<not> 2 ^ k < length a \<longrightarrow> length a \<le> p1))
   (foldl (shift_step a b left) (s, shift_const_m a 0 left, lconst False, 1) [0..<k])\<close>
proof (induction k)
  case 0
  then show ?case by (simp add: grows_refl shift_const_m_def)
next
  case (Suc k)
  obtain s1 r1 g1 p1 where F: \<open>foldl (shift_step a b left) (s, shift_const_m a 0 left, lconst False, 1) [0..<k] = (s1, r1, g1, p1)\<close>
    by (cases \<open>foldl (shift_step a b left) (s, shift_const_m a 0 left, lconst False, 1) [0..<k]\<close>)
  have I: \<open>grows (5 * length a * min k (nst (length a)) + 4 * k) s s1\<close> \<open>length r1 = length a\<close>
    \<open>2 ^ k < length a \<longrightarrow> p1 = 2 ^ k\<close> \<open>\<not> 2 ^ k < length a \<longrightarrow> length a \<le> p1\<close>
    using Suc F by auto
  show ?case
  proof (cases \<open>2 ^ k < length a\<close>)
    case True
    have km: \<open>k < nst (length a)\<close> using nst_stage True by blast
    have p1: \<open>p1 = 2 ^ k\<close> using I(3) True by simp
    obtain s2 x where 2: \<open>ite_vec_m s1 (b ! k) (shift_const_m r1 p1 left) r1 = (s2, x)\<close>
      by (cases \<open>ite_vec_m s1 (b ! k) (shift_const_m r1 p1 left) r1\<close>)
    have G: \<open>grows (5 * length a) s1 s2\<close> \<open>length x = length a\<close>
      using ite_vec_m_grows[of \<open>shift_const_m r1 p1 left\<close> s1 \<open>b ! k\<close> r1] 2 I(2) by (simp_all add: shift_const_m_def)
    define p' where \<open>p' = (if p1 \<le> length a - p1 then p1 + p1 else length a)\<close>
    have st: \<open>shift_step a b left (s1, r1, g1, p1) k = (s2, x, g1, p')\<close>
      using 2 True p1 by (simp add: shift_step_def p'_def)
    have n: \<open>5 * length a * min k (nst (length a)) + 4 * k + 5 * length a \<le>
             5 * length a * min (Suc k) (nst (length a)) + 4 * Suc k\<close> using km by simp
    have pn: \<open>(2 ^ Suc k < length a \<longrightarrow> p' = 2 ^ Suc k) \<and> (\<not> 2 ^ Suc k < length a \<longrightarrow> length a \<le> p')\<close>
      using p1 by (auto simp: p'_def)
    show ?thesis using F st grows_mono[OF grows_trans[OF I(1) G(1)] n] G(2) pn by simp
  next
    case False
    have km: \<open>nst (length a) \<le> k\<close> using nst_stage False by (meson not_less)
    have np: \<open>\<not> p1 < length a\<close> using I(4) False by simp
    have st: \<open>shift_step a b left (s1, r1, g1, p1) k = (fst (or_m s1 g1 (b ! k)), r1, snd (or_m s1 g1 (b ! k)), p1)\<close>
      using np by (simp add: shift_step_def split_def Let_def)
    have n: \<open>5 * length a * min k (nst (length a)) + 4 * k + 4 \<le>
             5 * length a * min (Suc k) (nst (length a)) + 4 * Suc k\<close> using km by simp
    have pn: \<open>\<not> 2 ^ Suc k < length a\<close> using nst_stage[of \<open>Suc k\<close>] km by simp
    show ?thesis using F st grows_mono[OF grows_trans[OF I(1) or_m_grows'] n] I(2) I(4) pn False
      by (simp add: le_trans[OF _ power_increasing[of k \<open>Suc k\<close> 2]])
  qed
qed

lemma shift_m_grows:
  assumes \<open>length b = length a\<close>
  shows \<open>grows (5 * length a * nst (length a) + 4 * length a + 5 * length a) s (fst (shift_m s a b left)) \<and>
         length (snd (shift_m s a b left)) = length a\<close>
proof -
  obtain s1 r1 g1 p1 where F: \<open>foldl (shift_step a b left) (s, shift_const_m a 0 left, lconst False, 1) [0..<length b] = (s1, r1, g1, p1)\<close>
    by (cases \<open>foldl (shift_step a b left) (s, shift_const_m a 0 left, lconst False, 1) [0..<length b]\<close>)
  have I: \<open>grows (5 * length a * min (length b) (nst (length a)) + 4 * length b) s s1\<close> \<open>length r1 = length a\<close>
    using shift_fold_grows[of \<open>length b\<close> b a s left] F by auto
  have G: \<open>grows (5 * length a) s1 (fst (ite_vec_m s1 g1 (replicate (length a) (lconst False)) r1))\<close>
    \<open>length (snd (ite_vec_m s1 g1 (replicate (length a) (lconst False)) r1)) = length a\<close>
    using ite_vec_m_grows[of \<open>replicate (length a) (lconst False)\<close> s1 g1 r1] by simp_all
  have e: \<open>shift_m s a b left = ite_vec_m s1 g1 (replicate (length a) (lconst False)) r1\<close>
    using F by (simp add: shift_m_def)
  have n: \<open>5 * length a * min (length b) (nst (length a)) + 4 * length b + 5 * length a \<le>
           5 * length a * nst (length a) + 4 * length a + 5 * length a\<close> using assms by simp
  show ?thesis using e grows_mono[OF grows_trans[OF I(1) G(1)] n] G(2) by simp
qed

lemma length_zext_m: \<open>length (zext_m a w) = w\<close>
  by (simp add: zext_m_def)

lemma divrem_m_grows:
  assumes \<open>length b = length a\<close> \<open>divrem_m s a b = (s', q, r)\<close>
  shows \<open>grows (76 * length a * length a + 92 * length a + 14) s s' \<and>
         length q = length a \<and> length r = length a\<close>
proof -
  define w where \<open>w = length a\<close>
  have wb: \<open>length b = w\<close> using assms(1) w_def by simp
  obtain s1 q1 where 1: \<open>fresh_vec_m s w = (s1, q1)\<close> by (cases \<open>fresh_vec_m s w\<close>)
  obtain s2 r1 where 2: \<open>fresh_vec_m s1 w = (s2, r1)\<close> by (cases \<open>fresh_vec_m s1 w\<close>)
  obtain s3 bz where 3: \<open>eq_m s2 b (replicate w (lconst False)) = (s3, bz)\<close>
    by (cases \<open>eq_m s2 b (replicate w (lconst False))\<close>)
  obtain s4 qo where 4: \<open>eq_m s3 q1 (replicate w (lconst True)) = (s4, qo)\<close>
    by (cases \<open>eq_m s3 q1 (replicate w (lconst True))\<close>)
  obtain s5 ra where 5: \<open>eq_m s4 r1 a = (s5, ra)\<close> by (cases \<open>eq_m s4 r1 a\<close>)
  obtain s6 cz where 6: \<open>and_m s5 qo ra = (s6, cz)\<close> by (cases \<open>and_m s5 qo ra\<close>)
  obtain s7 pr where 7: \<open>mul_m s6 (zext_m q1 (w + w)) (zext_m b (w + w)) = (s7, pr)\<close>
    by (cases \<open>mul_m s6 (zext_m q1 (w + w)) (zext_m b (w + w))\<close>)
  obtain s8 sm c where 8: \<open>add_m s7 pr (zext_m r1 (w + w)) (lconst False) = (s8, sm, c)\<close>
    by (metis prod_cases3)
  obtain s9 sa where 9: \<open>eq_m s8 sm (zext_m a (w + w)) = (s9, sa)\<close> by (cases \<open>eq_m s8 sm (zext_m a (w + w))\<close>)
  obtain s10 rl where 10: \<open>ult_m s9 r1 b = (s10, rl)\<close> by (cases \<open>ult_m s9 r1 b\<close>)
  obtain s11 cn where 11: \<open>and_m s10 sa rl = (s11, cn)\<close> by (cases \<open>and_m s10 sa rl\<close>)
  obtain s12 ok where 12: \<open>ite_m s11 bz cz cn = (s12, ok)\<close> by (cases \<open>ite_m s11 bz cz cn\<close>)
  have D: \<open>divrem_m s a b = (addc_m s12 [ok], q1, r1)\<close>
    using 1 2 3 4 5 6 7 8 9 10 11 12 by (simp add: divrem_m_def w_def[symmetric] Let_def)
  have e: \<open>s' = addc_m s12 [ok]\<close> \<open>q = q1\<close> \<open>r = r1\<close> using assms(2) D by simp_all
  have l1: \<open>length q1 = w\<close> using 1 by (auto simp: fresh_vec_m_def)
  have l2: \<open>length r1 = w\<close> using 2 by (auto simp: fresh_vec_m_def)
  have g1: \<open>grows w s s1\<close> using fresh_vec_grows[where s = s and w = w] 1 by simp
  have g2: \<open>grows w s1 s2\<close> using fresh_vec_grows[where s = s1 and w = w] 2 by simp
  have g3: \<open>grows (9 * w) s2 s3\<close> using eq_m_grows[where s = s2 and a = b and b = \<open>replicate w (lconst False)\<close>] 3 wb by simp
  have g4: \<open>grows (9 * w) s3 s4\<close> using eq_m_grows[where s = s3 and a = q1 and b = \<open>replicate w (lconst True)\<close>] 4 l1 by simp
  have g5: \<open>grows (9 * w) s4 s5\<close> using eq_m_grows[where s = s4 and a = r1 and b = a] 5 l2 w_def by simp
  have g6: \<open>grows 4 s5 s6\<close> using and_grows[where s = s5 and a = qo and b = ra] 6 by simp
  have g7: \<open>grows (19 * (w + w) * (w + w)) s6 s7\<close> and l7: \<open>length pr = w + w\<close>
    using mul_m_grows[where a = \<open>zext_m q1 (w + w)\<close> and s = s6 and b = \<open>zext_m b (w + w)\<close>] 7 by (simp_all add: length_zext_m)
  have g8: \<open>grows (15 * (w + w)) s7 s8\<close> and l8: \<open>length sm = w + w\<close>
    using add_m_grows[where s = s7 and a = pr and b = \<open>zext_m r1 (w + w)\<close> and c = \<open>lconst False\<close>] 8 l7 by simp_all
  have g9: \<open>grows (9 * (w + w)) s8 s9\<close>
    using eq_m_grows[where s = s8 and a = sm and b = \<open>zext_m a (w + w)\<close>] 9 l8 by simp
  have g10: \<open>grows (15 * w) s9 s10\<close> using ult_m_grows[where s = s9 and a = r1 and b = b] 10 l2 by simp
  have g11: \<open>grows 4 s10 s11\<close> using and_grows[where s = s10 and a = sa and b = rl] 11 by simp
  have g12: \<open>grows 5 s11 s12\<close> using ite_grows[where s = s11 and c = bz and a = cz and b = cn] 12 by simp
  have g13: \<open>grows 1 s12 s'\<close> using addc_grows[where c = \<open>[ok]\<close> and s = s12] e(1) by simp
  have \<open>grows (w + w + 9 * w + 9 * w + 9 * w + 4 + 19 * (w + w) * (w + w) + 15 * (w + w) +
        9 * (w + w) + 15 * w + 4 + 5 + 1) s s'\<close>
    using grows_trans[OF grows_trans[OF grows_trans[OF grows_trans[OF grows_trans[OF
      grows_trans[OF grows_trans[OF grows_trans[OF grows_trans[OF grows_trans[OF
      grows_trans[OF grows_trans[OF g1 g2] g3] g4] g5] g6] g7] g8] g9] g10] g11] g12] g13] .
  then have \<open>grows (76 * w * w + 92 * w + 14) s s'\<close>
    by (rule grows_mono) (simp add: algebra_simps)
  then show ?thesis using e l1 l2 by (simp add: w_def)
qed

lemma blast_bin_grows:
  assumes \<open>op \<noteq> BinOp_Concat \<longrightarrow> length b = length a\<close> \<open>blast_bin_m s op a b = (s', r)\<close>
  shows \<open>grows (100 * (length a + 1) ^ 2) s s' \<and> length r = bin_width op (length a) (length b)\<close>
proof -
  define w where \<open>w = length a\<close>
  have p1: \<open>5 * w \<le> 100 * (w + 1) ^ 2\<close> \<open>15 * w \<le> 100 * (w + 1) ^ 2\<close> \<open>9 * w \<le> 100 * (w + 1) ^ 2\<close>
    \<open>19 * w * w \<le> 100 * (w + 1) ^ 2\<close> \<open>14 * w * w \<le> 100 * (w + 1) ^ 2\<close>
    \<open>76 * w * w + 92 * w + 14 \<le> 100 * (w + 1) ^ 2\<close> \<open>0 \<le> 100 * (w + 1) ^ 2\<close>
    by (simp_all add: power2_eq_square algebra_simps)
  have p2: \<open>5 * w * nst w + 4 * w + 5 * w \<le> 100 * (w + 1) ^ 2\<close>
  proof -
    have a: \<open>5 * w * nst w \<le> 5 * (w * w)\<close> using nst_le[of w] by simp
    have b: \<open>5 * (w * w) + 9 * w \<le> 100 * (w + 1) ^ 2\<close> by (simp add: power2_eq_square algebra_simps)
    show ?thesis using a b by linarith
  qed
  have key: \<open>\<exists>n. n \<le> 100 * (w + 1) ^ 2 \<and> grows n s s' \<and> length r = bin_width op w (length b)\<close>
  proof (cases op)
    case BinOp_And
    then have H: \<open>bitwise_m op s a b = (s', r)\<close> using assms(2) by (simp add: blast_bin_m_def)
    show ?thesis
      using bitwise_m_grows[where op = op and s = s and a = a and b = b] H p1
      by (intro exI[where x = \<open>5 * w\<close>]) (simp add: BinOp_And bin_width_def w_def)
  next
    case BinOp_Or
    then have H: \<open>bitwise_m op s a b = (s', r)\<close> using assms(2) by (simp add: blast_bin_m_def)
    show ?thesis
      using bitwise_m_grows[where op = op and s = s and a = a and b = b] H p1
      by (intro exI[where x = \<open>5 * w\<close>]) (simp add: BinOp_Or bin_width_def w_def)
  next
    case BinOp_Xor
    then have H: \<open>bitwise_m op s a b = (s', r)\<close> using assms(2) by (simp add: blast_bin_m_def)
    show ?thesis
      using bitwise_m_grows[where op = op and s = s and a = a and b = b] H p1
      by (intro exI[where x = \<open>5 * w\<close>]) (simp add: BinOp_Xor bin_width_def w_def)
  next
    case BinOp_Add
    obtain s1 r1 c where H: \<open>add_m s a b (lconst False) = (s1, r1, c)\<close> by (metis prod_cases3)
    have E: \<open>s' = s1\<close> \<open>r = r1\<close> using assms(2) H BinOp_Add by (simp_all add: blast_bin_m_def)
    show ?thesis
      using add_m_grows[where s = s and a = a and b = b and c = \<open>lconst False\<close>] H p1
      by (intro exI[where x = \<open>15 * w\<close>]) (simp add: E BinOp_Add bin_width_def w_def)
  next
    case BinOp_Mul
    then have H: \<open>mul_m s a b = (s', r)\<close> using assms(2) by (simp add: blast_bin_m_def)
    show ?thesis
      using mul_m_grows[where s = s and a = a and b = b] H p1
      by (intro exI[where x = \<open>19 * w * w\<close>]) (simp add: BinOp_Mul bin_width_def w_def)
  next
    case BinOp_Udiv
    obtain s1 q r1 where H: \<open>divrem_m s a b = (s1, q, r1)\<close> by (metis prod_cases3)
    have E: \<open>s' = s1\<close> \<open>r = q\<close> using assms(2) H BinOp_Udiv by (simp_all add: blast_bin_m_def)
    show ?thesis
      using divrem_m_grows[where b = b and a = a and s = s and s' = s1 and q = q and r = r1] assms(1) H p1
      by (intro exI[where x = \<open>76 * w * w + 92 * w + 14\<close>]) (simp add: E BinOp_Udiv bin_width_def w_def)
  next
    case BinOp_Urem
    obtain s1 q r1 where H: \<open>divrem_m s a b = (s1, q, r1)\<close> by (metis prod_cases3)
    have E: \<open>s' = s1\<close> \<open>r = r1\<close> using assms(2) H BinOp_Urem by (simp_all add: blast_bin_m_def)
    show ?thesis
      using divrem_m_grows[where b = b and a = a and s = s and s' = s1 and q = q and r = r1] assms(1) H p1
      by (intro exI[where x = \<open>76 * w * w + 92 * w + 14\<close>]) (simp add: E BinOp_Urem bin_width_def w_def)
  next
    case BinOp_Shl
    then have H: \<open>shift_m s a b True = (s', r)\<close> using assms(2) by (simp add: blast_bin_m_def)
    show ?thesis
      using shift_m_grows[where b = b and a = a and s = s and left = True] assms(1) H p1 p2
      by (intro exI[where x = \<open>5 * w * nst w + 4 * w + 5 * w\<close>]) (simp add: BinOp_Shl bin_width_def w_def)
  next
    case BinOp_Lshr
    then have H: \<open>shift_m s a b False = (s', r)\<close> using assms(2) by (simp add: blast_bin_m_def)
    show ?thesis
      using shift_m_grows[where b = b and a = a and s = s and left = False] assms(1) H p1 p2
      by (intro exI[where x = \<open>5 * w * nst w + 4 * w + 5 * w\<close>]) (simp add: BinOp_Lshr bin_width_def w_def)
  next
    case BinOp_Concat
    then have E: \<open>s' = s\<close> \<open>r = concat_m a b\<close> using assms(2) by (simp_all add: blast_bin_m_def)
    show ?thesis
      using p1 by (intro exI[where x = 0]) (simp add: E BinOp_Concat bin_width_def concat_m_def w_def grows_refl)
  next
    case BinOp_Eq
    obtain s1 x where H: \<open>eq_m s a b = (s1, x)\<close> by (cases \<open>eq_m s a b\<close>)
    have E: \<open>s' = s1\<close> \<open>r = [x]\<close> using assms(2) H BinOp_Eq by (simp_all add: blast_bin_m_def)
    show ?thesis
      using eq_m_grows[where s = s and a = a and b = b] H p1
      by (intro exI[where x = \<open>9 * w\<close>]) (simp add: E BinOp_Eq bin_width_def w_def)
  next
    case BinOp_Ult
    obtain s1 x where H: \<open>ult_m s a b = (s1, x)\<close> by (cases \<open>ult_m s a b\<close>)
    have E: \<open>s' = s1\<close> \<open>r = [x]\<close> using assms(2) H BinOp_Ult by (simp_all add: blast_bin_m_def)
    show ?thesis
      using ult_m_grows[where s = s and a = a and b = b] H p1
      by (intro exI[where x = \<open>15 * w\<close>]) (simp add: E BinOp_Ult bin_width_def w_def)
  qed
  then obtain n where n: \<open>n \<le> 100 * (w + 1) ^ 2\<close> \<open>grows n s s'\<close> \<open>length r = bin_width op w (length b)\<close>
    by blast
  show ?thesis using grows_mono[OF n(2) n(1)] n(3) by (simp add: w_def)
qed

subsection \<open>Terms\<close>

lemma wt_sub: \<open>cwt ws ds t \<Longrightarrow> u \<in> set (csubterms t) \<Longrightarrow> cwt ws ds u\<close>
  by (induction t) auto

lemma wt_width_app: \<open>cwt ws ds t \<Longrightarrow> cwidth ws (ds @ e) t = cwidth ws ds t\<close>
  by (induction t) (auto simp: nth_append split: BinOp_splits)

lemma tw_app: \<open>cwt ws ds t \<Longrightarrow> cterm_weight ws (ds @ e) t = cterm_weight ws ds t\<close>
  unfolding cterm_weight_def
  using wt_sub wt_width_app by (auto intro!: arg_cong[where f = sum_list] map_cong)

lemma tw_leaf:
  \<open>t = CoreTermL_Const bs \<or> t = CoreTermL_Var i \<or> t = CoreTermL_Ref j \<Longrightarrow>
   cterm_weight ws ds t = (cwidth ws ds t + 1) ^ 2\<close>
  by (auto simp: cterm_weight_def)

lemma tw_Not: \<open>cterm_weight ws ds (CoreTermL_Not a) = (cwidth ws ds a + 1) ^ 2 + cterm_weight ws ds a\<close>
  by (simp add: cterm_weight_def)

lemma tw_Bin:
  \<open>cterm_weight ws ds (CoreTermL_Bin op a b) =
   (cwidth ws ds (CoreTermL_Bin op a b) + 1) ^ 2 + cterm_weight ws ds a + cterm_weight ws ds b\<close>
  by (simp add: cterm_weight_def)

lemma tw_Extract:
  \<open>cterm_weight ws ds (CoreTermL_Extract hi lo a) =
   (cwidth ws ds (CoreTermL_Extract hi lo a) + 1) ^ 2 + cterm_weight ws ds a\<close>
  by (simp add: cterm_weight_def)

lemma tw_Ite:
  \<open>cterm_weight ws ds (CoreTermL_Ite c a b) =
   (cwidth ws ds a + 1) ^ 2 + cterm_weight ws ds c + cterm_weight ws ds a + cterm_weight ws ds b\<close>
  by (simp add: cterm_weight_def)

lemma tw_ge: \<open>(cwidth ws ds t + 1) ^ 2 \<le> cterm_weight ws ds t\<close>
  by (cases t) (simp_all add: cterm_weight_def)

lemma width_Bin: \<open>cwidth ws ds (CoreTermL_Bin op a b) = bin_width op (cwidth ws ds a) (cwidth ws ds b)\<close>
  by (cases op) (simp_all add: bin_width_def)

text \<open>The lengths of the literal lists of an environment are the widths.\<close>
definition lenv :: \<open>nat list \<Rightarrow> Lit list list \<Rightarrow> bool\<close> where
  \<open>lenv ws vs \<equiv> length vs = length ws \<and> (\<forall>i < length ws. length (vs ! i) = ws ! i)\<close>

lemma blast_grows:
  \<open>cwt ws ds t \<Longrightarrow> lenv ws vs \<Longrightarrow> lenv ds dl \<Longrightarrow> blast_m vs dl s t = (s', ls) \<Longrightarrow>
   length ls = cwidth ws ds t \<and>
   (\<exists>n. grows n s s' \<and> n + 100 * (cwidth ws ds t + 1) ^ 2 \<le> 100 * cterm_weight ws ds t)\<close>
proof (induction t arbitrary: s s' ls)
  case (CoreTermL_Const bs)
  then show ?case
    using tw_leaf[of \<open>CoreTermL_Const bs\<close> bs undefined undefined ws ds]
    by (auto simp: const_m_def intro: exI[where x = 0] grows_refl)
next
  case (CoreTermL_Var i)
  then show ?case
    using tw_leaf[of \<open>CoreTermL_Var i\<close> undefined i undefined ws ds]
    by (auto simp: lenv_def intro: exI[where x = 0] grows_refl)
next
  case (CoreTermL_Ref i)
  then show ?case
    using tw_leaf[of \<open>CoreTermL_Ref i\<close> undefined undefined i ws ds]
    by (auto simp: lenv_def intro: exI[where x = 0] grows_refl)
next
  case (CoreTermL_Not a)
  obtain s1 la where A: \<open>blast_m vs dl s a = (s1, la)\<close> by (cases \<open>blast_m vs dl s a\<close>)
  have E: \<open>s' = s1\<close> \<open>ls = not_m la\<close> using CoreTermL_Not.prems(4) A by auto
  note IA = CoreTermL_Not.IH[OF _ CoreTermL_Not.prems(2,3) A]
  have wa: \<open>cwt ws ds a\<close> using CoreTermL_Not.prems(1) by simp
  obtain n where n: \<open>grows n s s1\<close> \<open>n + 100 * (cwidth ws ds a + 1) ^ 2 \<le> 100 * cterm_weight ws ds a\<close>
    using IA[OF wa] by blast
  show ?case
    using IA[OF wa] n by (auto simp: E not_m_def tw_Not intro!: exI[where x = n])
next
  case (CoreTermL_Bin op a b)
  obtain s1 la where A: \<open>blast_m vs dl s a = (s1, la)\<close> by (cases \<open>blast_m vs dl s a\<close>)
  obtain s2 lb where B: \<open>blast_m vs dl s1 b = (s2, lb)\<close> by (cases \<open>blast_m vs dl s1 b\<close>)
  have C: \<open>blast_bin_m s2 op la lb = (s', ls)\<close> using CoreTermL_Bin.prems(4) A B by simp
  have wa: \<open>cwt ws ds a\<close> and wb: \<open>cwt ws ds b\<close>
    and weq: \<open>op \<noteq> BinOp_Concat \<longrightarrow> cwidth ws ds a = cwidth ws ds b\<close>
    using CoreTermL_Bin.prems(1) by simp_all
  note IA = CoreTermL_Bin.IH(1)[OF wa CoreTermL_Bin.prems(2,3) A]
  note IB = CoreTermL_Bin.IH(2)[OF wb CoreTermL_Bin.prems(2,3) B]
  obtain n1 where n1: \<open>grows n1 s s1\<close> \<open>n1 + 100 * (cwidth ws ds a + 1) ^ 2 \<le> 100 * cterm_weight ws ds a\<close>
    using IA by blast
  obtain n2 where n2: \<open>grows n2 s1 s2\<close> \<open>n2 + 100 * (cwidth ws ds b + 1) ^ 2 \<le> 100 * cterm_weight ws ds b\<close>
    using IB by blast
  have len: \<open>op \<noteq> BinOp_Concat \<longrightarrow> length lb = length la\<close> using IA IB weq by simp
  note BB = blast_bin_grows[OF len C]
  have \<open>grows (n1 + n2 + 100 * (length la + 1) ^ 2) s s'\<close>
    using grows_trans[OF grows_trans[OF n1(1) n2(1)] BB[THEN conjunct1]] .
  then show ?case
    using BB IA IB n1 n2 by (auto simp: width_Bin tw_Bin bin_width_def intro!: exI[where x = \<open>n1 + n2 + 100 * (length la + 1) ^ 2\<close>])
next
  case (CoreTermL_Extract hi lo a)
  obtain s1 la where A: \<open>blast_m vs dl s a = (s1, la)\<close> by (cases \<open>blast_m vs dl s a\<close>)
  have E: \<open>s' = s1\<close> \<open>ls = extract_m la (unat hi) (unat lo)\<close> using CoreTermL_Extract.prems(4) A by auto
  have wa: \<open>cwt ws ds a\<close> and lh: \<open>unat lo \<le> unat hi\<close> using CoreTermL_Extract.prems(1) by simp_all
  note IA = CoreTermL_Extract.IH[OF wa CoreTermL_Extract.prems(2,3) A]
  obtain n where n: \<open>grows n s s1\<close> \<open>n + 100 * (cwidth ws ds a + 1) ^ 2 \<le> 100 * cterm_weight ws ds a\<close>
    using IA by blast
  show ?case
    using n lh by (auto simp: E extract_m_def tw_Extract intro!: exI[where x = n])
next
  case (CoreTermL_Ite c a b)
  obtain s1 lc where C: \<open>blast_m vs dl s c = (s1, lc)\<close> by (cases \<open>blast_m vs dl s c\<close>)
  obtain s2 la where A: \<open>blast_m vs dl s1 a = (s2, la)\<close> by (cases \<open>blast_m vs dl s1 a\<close>)
  obtain s3 lb where B: \<open>blast_m vs dl s2 b = (s3, lb)\<close> by (cases \<open>blast_m vs dl s2 b\<close>)
  have D: \<open>ite_vec_m s3 (lc ! 0) la lb = (s', ls)\<close> using CoreTermL_Ite.prems(4) C A B by simp
  have wc: \<open>cwt ws ds c\<close> and wa: \<open>cwt ws ds a\<close> and wb: \<open>cwt ws ds b\<close>
    using CoreTermL_Ite.prems(1) by simp_all
  note IC = CoreTermL_Ite.IH(1)[OF wc CoreTermL_Ite.prems(2,3) C]
  note IA = CoreTermL_Ite.IH(2)[OF wa CoreTermL_Ite.prems(2,3) A]
  note IB = CoreTermL_Ite.IH(3)[OF wb CoreTermL_Ite.prems(2,3) B]
  obtain nc where nc: \<open>grows nc s s1\<close> \<open>nc + 100 * (cwidth ws ds c + 1) ^ 2 \<le> 100 * cterm_weight ws ds c\<close>
    using IC by blast
  obtain na where na: \<open>grows na s1 s2\<close> \<open>na + 100 * (cwidth ws ds a + 1) ^ 2 \<le> 100 * cterm_weight ws ds a\<close>
    using IA by blast
  obtain nb where nb: \<open>grows nb s2 s3\<close> \<open>nb + 100 * (cwidth ws ds b + 1) ^ 2 \<le> 100 * cterm_weight ws ds b\<close>
    using IB by blast
  have V: \<open>grows (5 * length la) s3 s'\<close> \<open>length ls = length la\<close>
    using ite_vec_m_grows[where s = s3 and c = \<open>lc ! 0\<close> and a = la and b = lb] D by simp_all
  have p: \<open>5 * length la \<le> 100 * (length la + 1) ^ 2\<close> by (simp add: power2_eq_square algebra_simps)
  have \<open>grows (nc + na + nb + 5 * length la) s s'\<close>
    using grows_trans[OF grows_trans[OF grows_trans[OF nc(1) na(1)] nb(1)] V(1)] .
  then show ?case
    using V IA p nc na nb by (auto simp: tw_Ite intro!: exI[where x = \<open>nc + na + nb + 5 * length la\<close>])
qed

subsection \<open>The three loops of \<^verbatim>\<open>encode\<close>\<close>

lemma def_widths_snoc_b:
  \<open>cdef_widths ws ds (xs @ [x]) = cdef_widths ws ds xs @ [cwidth ws (cdef_widths ws ds xs) x]\<close>
  by (induction xs arbitrary: ds) auto

lemma def_widths_append:
  \<open>cdef_widths ws ds (xs @ ys) = cdef_widths ws (cdef_widths ws ds xs) ys\<close>
  by (induction xs arbitrary: ds) auto

lemma def_widths_prefix: \<open>\<exists>e. cdef_widths ws ds xs = ds @ e\<close>
proof (induction xs arbitrary: ds)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  obtain e where \<open>cdef_widths ws (ds @ [cwidth ws ds x]) xs = (ds @ [cwidth ws ds x]) @ e\<close>
    using Cons.IH by blast
  then show ?case by (auto intro!: exI[where x = \<open>cwidth ws ds x # e\<close>])
qed

lemma defs_wt_append_b:
  \<open>cdefs_wt ws ds (xs @ ys) = (cdefs_wt ws ds xs \<and> cdefs_wt ws (cdef_widths ws ds xs) ys)\<close>
  by (induction xs arbitrary: ds) auto

lemma defs_wt_nth_b:
  assumes \<open>cdefs_wt ws [] D\<close> \<open>k < length D\<close>
  shows \<open>cwt ws (cdef_widths ws [] (take k D)) (D ! k)\<close>
proof -
  have \<open>cdefs_wt ws [] (take k D @ drop k D)\<close> using assms(1) by simp
  then have \<open>cdefs_wt ws (cdef_widths ws [] (take k D)) (drop k D)\<close>
    by (simp only: defs_wt_append_b)
  then show ?thesis by (simp add: Cons_nth_drop_Suc[OF assms(2), symmetric])
qed

lemma vars_loop:
  \<open>k \<le> length W \<Longrightarrow> foldl (vars_step W) (init_st, []) [0..<k] = (s, vs) \<Longrightarrow>
   grows (sum_list (map unat (take k W))) init_st s \<and> lenv (map unat (take k W)) vs\<close>
proof (induction k arbitrary: s vs)
  case 0
  then show ?case by (simp add: grows_refl lenv_def)
next
  case (Suc k)
  obtain s0 vs0 where A: \<open>foldl (vars_step W) (init_st, []) [0..<k] = (s0, vs0)\<close>
    by (cases \<open>foldl (vars_step W) (init_st, []) [0..<k]\<close>)
  obtain s1 r where F: \<open>fresh_vec_m s0 (unat (W ! k)) = (s1, r)\<close>
    by (cases \<open>fresh_vec_m s0 (unat (W ! k))\<close>)
  have E: \<open>s = s1\<close> \<open>vs = vs0 @ [r]\<close> using Suc.prems(2) A F by (simp_all add: vars_step_def)
  have kl: \<open>k < length W\<close> using Suc.prems(1) by simp
  have IH: \<open>grows (sum_list (map unat (take k W))) init_st s0\<close> \<open>lenv (map unat (take k W)) vs0\<close>
    using Suc.IH[OF _ A] kl by simp_all
  have g: \<open>grows (unat (W ! k)) s0 s1\<close> using fresh_vec_grows[where s = s0 and w = \<open>unat (W ! k)\<close>] F by simp
  have lr: \<open>length r = unat (W ! k)\<close> using F by (auto simp: fresh_vec_m_def)
  have tk: \<open>take (Suc k) W = take k W @ [W ! k]\<close> using take_Suc_conv_app_nth[OF kl] .
  have g2: \<open>grows (sum_list (map unat (take k W)) + unat (W ! k)) init_st s1\<close>
    using grows_trans[OF IH(1) g] .
  show ?case
    using IH(2) kl lr g2 E by (auto simp: tk lenv_def nth_append less_Suc_eq)
qed

lemma defs_loop:
  assumes \<open>cdefs_wt ws [] D\<close> \<open>lenv ws vs\<close>
  shows \<open>k \<le> length D \<Longrightarrow> foldl (defs_step vs D) (s0, []) [0..<k] = (s, dl) \<Longrightarrow>
   \<exists>n. grows n s0 s \<and> lenv (cdef_widths ws [] (take k D)) dl \<and>
       n \<le> 100 * sum_list (map (cterm_weight ws (cdef_widths ws [] D)) (take k D))\<close>
proof (induction k arbitrary: s dl)
  case 0
  then show ?case by (auto simp: grows_refl lenv_def intro: exI[where x = 0])
next
  case (Suc k)
  obtain sp dp where A: \<open>foldl (defs_step vs D) (s0, []) [0..<k] = (sp, dp)\<close>
    by (cases \<open>foldl (defs_step vs D) (s0, []) [0..<k]\<close>)
  obtain s1 ls where B: \<open>blast_m vs dp sp (D ! k) = (s1, ls)\<close>
    by (cases \<open>blast_m vs dp sp (D ! k)\<close>)
  have E: \<open>s = s1\<close> \<open>dl = dp @ [ls]\<close> using Suc.prems(2) A B by (simp_all add: defs_step_def)
  have kl: \<open>k < length D\<close> using Suc.prems(1) by simp
  obtain n0 where n0: \<open>grows n0 s0 sp\<close> \<open>lenv (cdef_widths ws [] (take k D)) dp\<close>
    \<open>n0 \<le> 100 * sum_list (map (cterm_weight ws (cdef_widths ws [] D)) (take k D))\<close>
    using Suc.IH[OF _ A] kl by auto
  have wtk: \<open>cwt ws (cdef_widths ws [] (take k D)) (D ! k)\<close> using defs_wt_nth_b[OF assms(1) kl] .
  note BG = blast_grows[OF wtk assms(2) n0(2) B]
  obtain n1 where n1: \<open>grows n1 sp s1\<close>
    \<open>n1 + 100 * (cwidth ws (cdef_widths ws [] (take k D)) (D ! k) + 1) ^ 2 \<le>
     100 * cterm_weight ws (cdef_widths ws [] (take k D)) (D ! k)\<close>
    using BG by blast
  obtain e where e: \<open>cdef_widths ws [] D = cdef_widths ws [] (take k D) @ e\<close>
  proof -
    have \<open>cdef_widths ws [] D = cdef_widths ws [] (take k D @ drop k D)\<close> by simp
    also have \<open>\<dots> = cdef_widths ws (cdef_widths ws [] (take k D)) (drop k D)\<close>
      by (rule def_widths_append)
    finally show ?thesis using def_widths_prefix that by metis
  qed
  have tw: \<open>cterm_weight ws (cdef_widths ws [] D) (D ! k) = cterm_weight ws (cdef_widths ws [] (take k D)) (D ! k)\<close>
    unfolding e using tw_app[OF wtk] .
  have tk: \<open>take (Suc k) D = take k D @ [D ! k]\<close> using take_Suc_conv_app_nth[OF kl] .
  have g: \<open>grows (n0 + n1) s0 s1\<close> using grows_trans[OF n0(1) n1(1)] .
  show ?case
    using g n0(2) n0(3) n1(2) BG tw
    by (auto simp: E tk def_widths_snoc_b lenv_def nth_append less_Suc_eq
        intro!: exI[where x = \<open>n0 + n1\<close>])
qed

lemma asserts_loop:
  assumes \<open>lenv ws vs\<close> \<open>lenv ds dl\<close> \<open>\<forall>t \<in> set A. cwt ws ds t\<close>
  shows \<open>k \<le> length A \<Longrightarrow> foldl (asserts_step vs dl A) s0 [0..<k] = s \<Longrightarrow>
   \<exists>n. grows n s0 s \<and> n \<le> 100 * sum_list (map (cterm_weight ws ds) (take k A)) + k\<close>
proof (induction k arbitrary: s)
  case 0
  then show ?case by (auto simp: grows_refl intro: exI[where x = 0])
next
  case (Suc k)
  obtain sp where A: \<open>foldl (asserts_step vs dl A) s0 [0..<k] = sp\<close> by blast
  obtain s1 ls where B: \<open>blast_m vs dl sp (A ! k) = (s1, ls)\<close> by (cases \<open>blast_m vs dl sp (A ! k)\<close>)
  have E: \<open>s = addc_m s1 [ls ! 0]\<close> using Suc.prems(2) A B by (simp add: asserts_step_def)
  have kl: \<open>k < length A\<close> using Suc.prems(1) by simp
  obtain n0 where n0: \<open>grows n0 s0 sp\<close> \<open>n0 \<le> 100 * sum_list (map (cterm_weight ws ds) (take k A)) + k\<close>
    using Suc.IH[OF _ A] kl by auto
  have wtk: \<open>cwt ws ds (A ! k)\<close> using assms(3) kl by simp
  obtain n1 where n1: \<open>grows n1 sp s1\<close> \<open>n1 + 100 * (cwidth ws ds (A ! k) + 1) ^ 2 \<le> 100 * cterm_weight ws ds (A ! k)\<close>
    using blast_grows[OF wtk assms(1,2) B] by blast
  have g1: \<open>grows 1 s1 s\<close> using addc_grows[where c = \<open>[ls ! 0]\<close> and s = s1] E by simp
  have g: \<open>grows (n0 + n1 + 1) s0 s\<close> using grows_trans[OF grows_trans[OF n0(1) n1(1)] g1] .
  have tk: \<open>take (Suc k) A = take k A @ [A ! k]\<close> using take_Suc_conv_app_nth[OF kl] .
  show ?case using g n0(2) n1(2) by (auto simp: tk intro!: exI[where x = \<open>n0 + n1 + 1\<close>])
qed

lemma encode_grows:
  assumes \<open>cproblem_wt p\<close> \<open>encode_m p = (s, vs)\<close>
  shows \<open>fst s + length (snd s) \<le>
           2 + sum_list (cvar_widths p) + length (CoreProblemL_asserts p) +
           100 * sum_list (map (cterm_weight (cvar_widths p) (cdef_widths (cvar_widths p) [] (CoreProblemL_defs p)))
                              (CoreProblemL_defs p @ CoreProblemL_asserts p)) \<and>
         cl4 s\<close>
proof -
  let ?W = \<open>CoreProblemL_widths p\<close>
  let ?D = \<open>CoreProblemL_defs p\<close>
  let ?A = \<open>CoreProblemL_asserts p\<close>
  let ?ws = \<open>cvar_widths p\<close>
  let ?ds = \<open>cdef_widths ?ws [] ?D\<close>
  obtain s1 vs1 where V: \<open>foldl (vars_step ?W) (init_st, []) [0..<length ?W] = (s1, vs1)\<close>
    by (cases \<open>foldl (vars_step ?W) (init_st, []) [0..<length ?W]\<close>)
  obtain s2 dl where Dl: \<open>foldl (defs_step vs1 ?D) (s1, []) [0..<length ?D] = (s2, dl)\<close>
    by (cases \<open>foldl (defs_step vs1 ?D) (s1, []) [0..<length ?D]\<close>)
  have X: \<open>encode_m p = (foldl (asserts_step vs1 dl ?A) s2 [0..<length ?A], vs1)\<close>
    by (simp add: encode_m_def V Dl)
  have S: \<open>foldl (asserts_step vs1 dl ?A) s2 [0..<length ?A] = s\<close>
    using X assms(2) by (metis prod.inject)
  have dwt: \<open>cdefs_wt ?ws [] ?D\<close> and awt: \<open>\<forall>t \<in> set ?A. cwt ?ws ?ds t\<close>
    using assms(1) by (simp_all add: cproblem_wt_def Let_def)
  have VL: \<open>grows (sum_list ?ws) init_st s1\<close> \<open>lenv ?ws vs1\<close>
    using vars_loop[of \<open>length ?W\<close> ?W s1 vs1] V by (simp_all add: cvar_widths_def)
  obtain n2 where D2: \<open>grows n2 s1 s2\<close> \<open>lenv ?ds dl\<close>
    \<open>n2 \<le> 100 * sum_list (map (cterm_weight ?ws ?ds) ?D)\<close>
    using defs_loop[OF dwt VL(2) order_refl Dl] by auto
  obtain n3 where D3: \<open>grows n3 s2 s\<close>
    \<open>n3 \<le> 100 * sum_list (map (cterm_weight ?ws ?ds) ?A) + length ?A\<close>
    using asserts_loop[OF VL(2) D2(2) awt order_refl S] by auto
  have g: \<open>grows (sum_list ?ws + n2 + n3) init_st s\<close>
    using grows_trans[OF grows_trans[OF VL(1) D2(1)] D3(1)] .
  have ci: \<open>cl4 init_st\<close> by (simp add: cl4_def init_st_def)
  show ?thesis
    using g ci D2(3) D3(2) by (simp add: grows_def init_st_def algebra_simps)
qed

subsection \<open>Exact counts\<close>

text \<open>The growth of the CNF state for one operator on operands of width \<open>w\<close>: the bounds of the
  circuits above. Concatenation builds no gate.\<close>
definition bcost :: \<open>BinOp \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>bcost op w = (case op of
     BinOp_And \<Rightarrow> 5 * w | BinOp_Or \<Rightarrow> 5 * w | BinOp_Xor \<Rightarrow> 5 * w | BinOp_Add \<Rightarrow> 15 * w
   | BinOp_Mul \<Rightarrow> 19 * w * w | BinOp_Udiv \<Rightarrow> 76 * w * w + 92 * w + 14 | BinOp_Urem \<Rightarrow> 76 * w * w + 92 * w + 14
   | BinOp_Shl \<Rightarrow> 5 * w * nst w + 9 * w | BinOp_Lshr \<Rightarrow> 5 * w * nst w + 9 * w
   | BinOp_Concat \<Rightarrow> 0 | BinOp_Eq \<Rightarrow> 9 * w | BinOp_Ult \<Rightarrow> 15 * w)\<close>

lemma blast_bin_cost:
  assumes \<open>op \<noteq> BinOp_Concat \<longrightarrow> length b = length a\<close> \<open>blast_bin_m s op a b = (s', r)\<close>
  shows \<open>grows (bcost op (length a)) s s'\<close>
proof (cases op)
  case BinOp_And
  then show ?thesis using bitwise_m_grows[where op = op and s = s and a = a and b = b] assms(2)
    by (simp add: blast_bin_m_def bcost_def)
next
  case BinOp_Or
  then show ?thesis using bitwise_m_grows[where op = op and s = s and a = a and b = b] assms(2)
    by (simp add: blast_bin_m_def bcost_def)
next
  case BinOp_Xor
  then show ?thesis using bitwise_m_grows[where op = op and s = s and a = a and b = b] assms(2)
    by (simp add: blast_bin_m_def bcost_def)
next
  case BinOp_Add
  then show ?thesis using add_m_grows[where s = s and a = a and b = b and c = \<open>lconst False\<close>] assms(2)
    by (simp add: blast_bin_m_def bcost_def split_def Let_def)
next
  case BinOp_Mul
  then show ?thesis using mul_m_grows[where s = s and a = a and b = b] assms(2)
    by (simp add: blast_bin_m_def bcost_def)
next
  case BinOp_Udiv
  obtain s1 q1 r1 where E: \<open>divrem_m s a b = (s1, q1, r1)\<close> by (cases \<open>divrem_m s a b\<close>)
  then show ?thesis using divrem_m_grows[OF _ E] assms BinOp_Udiv
    by (simp add: blast_bin_m_def bcost_def)
next
  case BinOp_Urem
  obtain s1 q1 r1 where E: \<open>divrem_m s a b = (s1, q1, r1)\<close> by (cases \<open>divrem_m s a b\<close>)
  then show ?thesis using divrem_m_grows[OF _ E] assms BinOp_Urem
    by (simp add: blast_bin_m_def bcost_def)
next
  case BinOp_Shl
  then show ?thesis using shift_m_grows[where b = b and a = a and s = s and left = True] assms
    by (simp add: blast_bin_m_def bcost_def algebra_simps)
next
  case BinOp_Lshr
  then show ?thesis using shift_m_grows[where b = b and a = a and s = s and left = False] assms
    by (simp add: blast_bin_m_def bcost_def algebra_simps)
next
  case BinOp_Concat
  then show ?thesis using assms(2) by (simp add: blast_bin_m_def bcost_def grows_refl)
next
  case BinOp_Eq
  then show ?thesis using eq_m_grows[where s = s and a = a and b = b] assms(2)
    by (simp add: blast_bin_m_def bcost_def split_def Let_def)
next
  case BinOp_Ult
  then show ?thesis using ult_m_grows[where s = s and a = a and b = b] assms(2)
    by (simp add: blast_bin_m_def bcost_def split_def Let_def)
qed

text \<open>The cost of a node: its operator on the width of its first operand; \<open>ite\<close> builds one gate
  per bit; the other nodes build none.\<close>
definition ncost :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> CoreTermL \<Rightarrow> nat\<close> where
  \<open>ncost ws ds u = (case u of
     CoreTermL_Bin op a b \<Rightarrow> bcost op (cwidth ws ds a)
   | CoreTermL_Ite c a b \<Rightarrow> 5 * cwidth ws ds a
   | _ \<Rightarrow> 0)\<close>

definition ccount :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> CoreTermL \<Rightarrow> nat\<close> where
  \<open>ccount ws ds t = sum_list (map (ncost ws ds) (csubterms t))\<close>

lemma ccount_app: \<open>cwt ws ds t \<Longrightarrow> ccount ws (ds @ e) t = ccount ws ds t\<close>
proof -
  assume w: \<open>cwt ws ds t\<close>
  have \<open>ncost ws (ds @ e) u = ncost ws ds u\<close> if \<open>u \<in> set (csubterms t)\<close> for u
  proof -
    have wu: \<open>cwt ws ds u\<close> using wt_sub[OF w that] .
    show ?thesis using wu by (cases u) (auto simp: ncost_def wt_width_app)
  qed
  then show ?thesis unfolding ccount_def by (auto intro!: arg_cong[where f = sum_list] map_cong)
qed

lemma blast_cnt:
  \<open>cwt ws ds t \<Longrightarrow> lenv ws vs \<Longrightarrow> lenv ds dl \<Longrightarrow> blast_m vs dl s t = (s', ls) \<Longrightarrow>
   length ls = cwidth ws ds t \<and> grows (ccount ws ds t) s s'\<close>
proof (induction t arbitrary: s s' ls)
  case (CoreTermL_Const bs)
  then show ?case by (auto simp: const_m_def ccount_def ncost_def grows_refl)
next
  case (CoreTermL_Var i)
  then show ?case by (auto simp: lenv_def ccount_def ncost_def grows_refl)
next
  case (CoreTermL_Ref i)
  then show ?case by (auto simp: lenv_def ccount_def ncost_def grows_refl)
next
  case (CoreTermL_Not a)
  obtain s1 la where A: \<open>blast_m vs dl s a = (s1, la)\<close> by (cases \<open>blast_m vs dl s a\<close>)
  have E: \<open>s' = s1\<close> \<open>ls = not_m la\<close> using CoreTermL_Not.prems(4) A by auto
  have wa: \<open>cwt ws ds a\<close> using CoreTermL_Not.prems(1) by simp
  note IA = CoreTermL_Not.IH[OF wa CoreTermL_Not.prems(2,3) A]
  show ?case using IA by (auto simp: E not_m_def ccount_def ncost_def)
next
  case (CoreTermL_Bin op a b)
  obtain s1 la where A: \<open>blast_m vs dl s a = (s1, la)\<close> by (cases \<open>blast_m vs dl s a\<close>)
  obtain s2 lb where B: \<open>blast_m vs dl s1 b = (s2, lb)\<close> by (cases \<open>blast_m vs dl s1 b\<close>)
  have C: \<open>blast_bin_m s2 op la lb = (s', ls)\<close> using CoreTermL_Bin.prems(4) A B by simp
  have wa: \<open>cwt ws ds a\<close> and wb: \<open>cwt ws ds b\<close>
    and weq: \<open>op \<noteq> BinOp_Concat \<longrightarrow> cwidth ws ds a = cwidth ws ds b\<close>
    using CoreTermL_Bin.prems(1) by simp_all
  note IA = CoreTermL_Bin.IH(1)[OF wa CoreTermL_Bin.prems(2,3) A]
  note IB = CoreTermL_Bin.IH(2)[OF wb CoreTermL_Bin.prems(2,3) B]
  have len: \<open>op \<noteq> BinOp_Concat \<longrightarrow> length lb = length la\<close> using IA IB weq by simp
  have G: \<open>grows (bcost op (length la)) s2 s'\<close> using blast_bin_cost[OF len C] .
  have L: \<open>length ls = bin_width op (length la) (length lb)\<close> using blast_bin_grows[OF len C] by simp
  have g: \<open>grows (ccount ws ds a + ccount ws ds b + bcost op (length la)) s s'\<close>
    using grows_trans[OF grows_trans[OF IA[THEN conjunct2] IB[THEN conjunct2]] G] .
  show ?case using g L IA IB by (auto simp: width_Bin ccount_def ncost_def bin_width_def algebra_simps)
next
  case (CoreTermL_Extract hi lo a)
  obtain s1 la where A: \<open>blast_m vs dl s a = (s1, la)\<close> by (cases \<open>blast_m vs dl s a\<close>)
  have E: \<open>s' = s1\<close> \<open>ls = extract_m la (unat hi) (unat lo)\<close> using CoreTermL_Extract.prems(4) A by auto
  have wa: \<open>cwt ws ds a\<close> and lh: \<open>unat lo \<le> unat hi\<close> using CoreTermL_Extract.prems(1) by simp_all
  note IA = CoreTermL_Extract.IH[OF wa CoreTermL_Extract.prems(2,3) A]
  show ?case using IA lh by (auto simp: E extract_m_def ccount_def ncost_def)
next
  case (CoreTermL_Ite c a b)
  obtain s1 lc where C: \<open>blast_m vs dl s c = (s1, lc)\<close> by (cases \<open>blast_m vs dl s c\<close>)
  obtain s2 la where A: \<open>blast_m vs dl s1 a = (s2, la)\<close> by (cases \<open>blast_m vs dl s1 a\<close>)
  obtain s3 lb where B: \<open>blast_m vs dl s2 b = (s3, lb)\<close> by (cases \<open>blast_m vs dl s2 b\<close>)
  have D: \<open>ite_vec_m s3 (lc ! 0) la lb = (s', ls)\<close> using CoreTermL_Ite.prems(4) C A B by simp
  have wc: \<open>cwt ws ds c\<close> and wa: \<open>cwt ws ds a\<close> and wb: \<open>cwt ws ds b\<close>
    using CoreTermL_Ite.prems(1) by simp_all
  note IC = CoreTermL_Ite.IH(1)[OF wc CoreTermL_Ite.prems(2,3) C]
  note IA = CoreTermL_Ite.IH(2)[OF wa CoreTermL_Ite.prems(2,3) A]
  note IB = CoreTermL_Ite.IH(3)[OF wb CoreTermL_Ite.prems(2,3) B]
  have V: \<open>grows (5 * length la) s3 s'\<close> \<open>length ls = length la\<close>
    using ite_vec_m_grows[where s = s3 and c = \<open>lc ! 0\<close> and a = la and b = lb] D by simp_all
  have g: \<open>grows (ccount ws ds c + ccount ws ds a + ccount ws ds b + 5 * length la) s s'\<close>
    using grows_trans[OF grows_trans[OF grows_trans[OF IC[THEN conjunct2] IA[THEN conjunct2]] IB[THEN conjunct2]] V(1)] .
  show ?case using g V IA by (auto simp: ccount_def ncost_def algebra_simps)
qed

lemma defs_cnt:
  assumes \<open>cdefs_wt ws [] D\<close> \<open>lenv ws vs\<close>
  shows \<open>k \<le> length D \<Longrightarrow> foldl (defs_step vs D) (s0, []) [0..<k] = (s, dl) \<Longrightarrow>
   grows (sum_list (map (ccount ws (cdef_widths ws [] D)) (take k D))) s0 s \<and> lenv (cdef_widths ws [] (take k D)) dl\<close>
proof (induction k arbitrary: s dl)
  case 0
  then show ?case by (simp add: grows_refl lenv_def)
next
  case (Suc k)
  obtain sp dp where A: \<open>foldl (defs_step vs D) (s0, []) [0..<k] = (sp, dp)\<close>
    by (cases \<open>foldl (defs_step vs D) (s0, []) [0..<k]\<close>)
  obtain s1 ls where B: \<open>blast_m vs dp sp (D ! k) = (s1, ls)\<close>
    by (cases \<open>blast_m vs dp sp (D ! k)\<close>)
  have E: \<open>s = s1\<close> \<open>dl = dp @ [ls]\<close> using Suc.prems(2) A B by (simp_all add: defs_step_def)
  have kl: \<open>k < length D\<close> using Suc.prems(1) by simp
  have I: \<open>grows (sum_list (map (ccount ws (cdef_widths ws [] D)) (take k D))) s0 sp\<close>
    \<open>lenv (cdef_widths ws [] (take k D)) dp\<close> using Suc.IH[OF _ A] kl by auto
  have wtk: \<open>cwt ws (cdef_widths ws [] (take k D)) (D ! k)\<close> using defs_wt_nth_b[OF assms(1) kl] .
  note BG = blast_cnt[OF wtk assms(2) I(2) B]
  obtain e where e: \<open>cdef_widths ws [] D = cdef_widths ws [] (take k D) @ e\<close>
  proof -
    have \<open>cdef_widths ws [] D = cdef_widths ws [] (take k D @ drop k D)\<close> by simp
    also have \<open>\<dots> = cdef_widths ws (cdef_widths ws [] (take k D)) (drop k D)\<close>
      by (rule def_widths_append)
    finally show ?thesis using def_widths_prefix that by metis
  qed
  have cc: \<open>ccount ws (cdef_widths ws [] D) (D ! k) = ccount ws (cdef_widths ws [] (take k D)) (D ! k)\<close>
    unfolding e using ccount_app[OF wtk] .
  have tk: \<open>take (Suc k) D = take k D @ [D ! k]\<close> using take_Suc_conv_app_nth[OF kl] .
  have g: \<open>grows (sum_list (map (ccount ws (cdef_widths ws [] D)) (take k D)) +
                  ccount ws (cdef_widths ws [] D) (D ! k)) s0 s1\<close>
    using grows_trans[OF I(1) BG[THEN conjunct2]] cc by simp
  show ?case
    using g I(2) BG by (auto simp: E tk def_widths_snoc_b lenv_def nth_append less_Suc_eq)
qed

lemma asserts_cnt:
  assumes \<open>lenv ws vs\<close> \<open>lenv ds dl\<close> \<open>\<forall>t \<in> set A. cwt ws ds t\<close>
  shows \<open>k \<le> length A \<Longrightarrow> foldl (asserts_step vs dl A) s0 [0..<k] = s \<Longrightarrow>
   grows (sum_list (map (ccount ws ds) (take k A)) + k) s0 s\<close>
proof (induction k arbitrary: s)
  case 0
  then show ?case by (simp add: grows_refl)
next
  case (Suc k)
  obtain sp where A: \<open>foldl (asserts_step vs dl A) s0 [0..<k] = sp\<close> by blast
  obtain s1 ls where B: \<open>blast_m vs dl sp (A ! k) = (s1, ls)\<close> by (cases \<open>blast_m vs dl sp (A ! k)\<close>)
  have E: \<open>s = addc_m s1 [ls ! 0]\<close> using Suc.prems(2) A B by (simp add: asserts_step_def)
  have kl: \<open>k < length A\<close> using Suc.prems(1) by simp
  have I: \<open>grows (sum_list (map (ccount ws ds) (take k A)) + k) s0 sp\<close> using Suc.IH[OF _ A] kl by auto
  have wtk: \<open>cwt ws ds (A ! k)\<close> using assms(3) kl by simp
  have g1: \<open>grows (ccount ws ds (A ! k)) sp s1\<close> using blast_cnt[OF wtk assms(1,2) B] by simp
  have g2: \<open>grows 1 s1 s\<close> using addc_grows[where c = \<open>[ls ! 0]\<close> and s = s1] E by simp
  have tk: \<open>take (Suc k) A = take k A @ [A ! k]\<close> using take_Suc_conv_app_nth[OF kl] .
  show ?case using grows_trans[OF grows_trans[OF I g1] g2] by (simp add: tk algebra_simps)
qed

lemma encode_cnt:
  assumes \<open>cproblem_wt p\<close> \<open>encode_m p = (s, vs)\<close>
  shows \<open>fst s + length (snd s) \<le>
           2 + sum_list (cvar_widths p) + length (CoreProblemL_asserts p) +
           sum_list (map (ccount (cvar_widths p) (cdef_widths (cvar_widths p) [] (CoreProblemL_defs p)))
                              (CoreProblemL_defs p @ CoreProblemL_asserts p)) \<and>
         cl4 s\<close>
proof -
  let ?W = \<open>CoreProblemL_widths p\<close>
  let ?D = \<open>CoreProblemL_defs p\<close>
  let ?A = \<open>CoreProblemL_asserts p\<close>
  let ?ws = \<open>cvar_widths p\<close>
  let ?ds = \<open>cdef_widths ?ws [] ?D\<close>
  obtain s1 vs1 where V: \<open>foldl (vars_step ?W) (init_st, []) [0..<length ?W] = (s1, vs1)\<close>
    by (cases \<open>foldl (vars_step ?W) (init_st, []) [0..<length ?W]\<close>)
  obtain s2 dl where Dl: \<open>foldl (defs_step vs1 ?D) (s1, []) [0..<length ?D] = (s2, dl)\<close>
    by (cases \<open>foldl (defs_step vs1 ?D) (s1, []) [0..<length ?D]\<close>)
  have X: \<open>encode_m p = (foldl (asserts_step vs1 dl ?A) s2 [0..<length ?A], vs1)\<close>
    by (simp add: encode_m_def V Dl)
  have S: \<open>foldl (asserts_step vs1 dl ?A) s2 [0..<length ?A] = s\<close>
    using X assms(2) by (metis prod.inject)
  have dwt: \<open>cdefs_wt ?ws [] ?D\<close> and awt: \<open>\<forall>t \<in> set ?A. cwt ?ws ?ds t\<close>
    using assms(1) by (simp_all add: cproblem_wt_def Let_def)
  have VL: \<open>grows (sum_list ?ws) init_st s1\<close> \<open>lenv ?ws vs1\<close>
    using vars_loop[of \<open>length ?W\<close> ?W s1 vs1] V by (simp_all add: cvar_widths_def)
  have D2: \<open>grows (sum_list (map (ccount ?ws ?ds) ?D)) s1 s2\<close> \<open>lenv ?ds dl\<close>
    using defs_cnt[OF dwt VL(2) order_refl Dl] by auto
  have D3: \<open>grows (sum_list (map (ccount ?ws ?ds) ?A) + length ?A) s2 s\<close>
    using asserts_cnt[OF VL(2) D2(2) awt order_refl S] by simp
  have g: \<open>grows (sum_list ?ws + sum_list (map (ccount ?ws ?ds) ?D) + (sum_list (map (ccount ?ws ?ds) ?A) + length ?A)) init_st s\<close>
    using grows_trans[OF grows_trans[OF VL(1) D2(1)] D3] .
  have ci: \<open>cl4 init_st\<close> by (simp add: cl4_def init_st_def)
  show ?thesis
    using g ci by (simp add: grows_def init_st_def algebra_simps)
qed

text \<open>\<^const>\<open>fuel_bound\<close> is below \<open>2^57\<close> when the counts, the numbers of variables,
  definitions and assertions, the widths of the variables and the terms are small.\<close>
theorem fuel_bound_lt:
  assumes \<open>cproblem_wt p\<close>
    \<open>2 + sum_list (cvar_widths p) + length (CoreProblemL_asserts p) +
     sum_list (map (ccount (cvar_widths p) (cdef_widths (cvar_widths p) [] (CoreProblemL_defs p)))
                   (CoreProblemL_defs p @ CoreProblemL_asserts p)) < 2 ^ 56\<close>
    \<open>length (cvar_widths p) < 2 ^ 56\<close> \<open>length (CoreProblemL_defs p) < 2 ^ 56\<close>
    \<open>length (CoreProblemL_asserts p) < 2 ^ 56\<close>
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

subsection \<open>The fuel is bounded by the size bound\<close>

lemma sq1: \<open>1 \<le> (w + 1) ^ 2\<close> for w :: nat
proof -
  have \<open>0 < (w + 1) ^ 2\<close> by simp
  then show ?thesis by linarith
qed

lemma size_tw: \<open>Suc (size t) \<le> 2 * cterm_weight ws ds t\<close>
proof (induction t)
  case (CoreTermL_Const bs)
  then show ?case by (simp add: cterm_weight_def)
next
  case (CoreTermL_Var i)
  then show ?case by (simp add: cterm_weight_def)
next
  case (CoreTermL_Ref i)
  then show ?case by (simp add: cterm_weight_def)
next
  case (CoreTermL_Not a)
  have sz: \<open>size (CoreTermL_Not a) \<le> size a + 1\<close> by simp
  show ?case
    using CoreTermL_Not.IH tw_Not[of ws ds a] sq1[of \<open>cwidth ws ds a\<close>] sz by linarith
next
  case (CoreTermL_Bin op a b)
  have sz: \<open>size (CoreTermL_Bin op a b) \<le> size a + size b + 1\<close> by simp
  show ?case
    using CoreTermL_Bin.IH tw_Bin[of ws ds op a b] sq1[of \<open>cwidth ws ds (CoreTermL_Bin op a b)\<close>] sz by linarith
next
  case (CoreTermL_Extract hi lo a)
  have sz: \<open>size (CoreTermL_Extract hi lo a) \<le> size a + 1\<close> by simp
  show ?case
    using CoreTermL_Extract.IH tw_Extract[of ws ds hi lo a] sq1[of \<open>cwidth ws ds (CoreTermL_Extract hi lo a)\<close>] sz
    by linarith
next
  case (CoreTermL_Ite c a b)
  have sz: \<open>size (CoreTermL_Ite c a b) \<le> size c + size a + size b + 1\<close> by simp
  show ?case
    using CoreTermL_Ite.IH tw_Ite[of ws ds c a b] sq1[of \<open>cwidth ws ds a\<close>] sz by linarith
qed

lemma tbound_le: \<open>tbound ws ds t \<le> 2 * cterm_weight ws ds t\<close>
proof -
  have ne: \<open>set (map (\<lambda>u. 2 * cwidth ws ds u + 2) (csubterms t)) \<noteq> {}\<close> by (cases t) simp_all
  have \<open>Max (set (map (\<lambda>u. 2 * cwidth ws ds u + 2) (csubterms t))) \<le> 2 * cterm_weight ws ds t\<close>
  proof (rule Max.boundedI)
    show \<open>finite (set (map (\<lambda>u. 2 * cwidth ws ds u + 2) (csubterms t)))\<close> by simp
    show \<open>set (map (\<lambda>u. 2 * cwidth ws ds u + 2) (csubterms t)) \<noteq> {}\<close> by fact
    fix x assume \<open>x \<in> set (map (\<lambda>u. 2 * cwidth ws ds u + 2) (csubterms t))\<close>
    then obtain u where u: \<open>u \<in> set (csubterms t)\<close> \<open>x = 2 * cwidth ws ds u + 2\<close> by auto
    have mem: \<open>(cwidth ws ds u + 1) ^ 2 \<in> set (map (\<lambda>u. (cwidth ws ds u + 1) ^ 2) (csubterms t))\<close>
      using u(1) by simp
    have \<open>(cwidth ws ds u + 1) ^ 2 \<le> cterm_weight ws ds t\<close>
      unfolding cterm_weight_def by (rule member_le_sum_list[OF mem]; simp)
    then show \<open>x \<le> 2 * cterm_weight ws ds t\<close>
      using u(2) by (simp add: power2_eq_square algebra_simps)
  qed
  then show ?thesis using size_tw[of t ws ds] by (simp add: tbound_def)
qed

theorem fuel_bound_le:
  assumes \<open>cproblem_wt p\<close>
  shows \<open>fuel_bound p \<le> csize_bound p\<close>
proof -
  obtain s vs where e: \<open>encode_m p = (s, vs)\<close> by (cases \<open>encode_m p\<close>)
  note EG = encode_grows[OF assms e]
  define ws where \<open>ws = cvar_widths p\<close>
  define ds where \<open>ds = cdef_widths ws [] (CoreProblemL_defs p)\<close>
  define Y where \<open>Y = sum_list (map (cterm_weight ws ds) (CoreProblemL_defs p @ CoreProblemL_asserts p))\<close>
  define B where \<open>B = csize_bound p\<close>
  have EG': \<open>fst s + length (snd s) \<le> 2 + sum_list ws + length (CoreProblemL_asserts p) + 100 * Y\<close>
    using EG by (simp add: ws_def ds_def Y_def)
  have cl: \<open>cl4 s\<close> using EG by simp
  have Bdef: \<open>B = 1000 * (1 + sum_list ws + length ws + length (CoreProblemL_defs p) +
      length (CoreProblemL_asserts p) + Y)\<close>
    by (simp add: B_def csize_bound_def Let_def ws_def ds_def Y_def)
  have Bexp: \<open>B = 1000 + 1000 * sum_list ws + 1000 * length ws + 1000 * length (CoreProblemL_defs p) +
      1000 * length (CoreProblemL_asserts p) + 1000 * Y\<close> using Bdef by (simp add: algebra_simps)
  have gen: \<open>\<And>m. m \<le> 2 + sum_list ws + length (CoreProblemL_asserts p) + 100 * Y \<Longrightarrow> m + 2 \<le> B\<close>
  proof -
    fix m assume h: \<open>m \<le> 2 + sum_list ws + length (CoreProblemL_asserts p) + 100 * Y\<close>
    have a: \<open>B = 1000 + 1000 * sum_list ws + 1000 * length ws + 1000 * length (CoreProblemL_defs p) +
      1000 * length (CoreProblemL_asserts p) + 1000 * Y\<close> using Bdef by (simp add: algebra_simps)
    have b1: \<open>sum_list ws \<le> 1000 * sum_list ws\<close> and b2: \<open>length (CoreProblemL_asserts p) \<le> 1000 * length (CoreProblemL_asserts p)\<close>
      and b3: \<open>100 * Y \<le> 1000 * Y\<close> by simp_all
    show \<open>m + 2 \<le> B\<close> using a h b1 b2 b3 by linarith
  qed
  have h1: \<open>fst s + 2 \<le> B\<close> using gen[of \<open>fst s\<close>] EG' by simp
  have h2: \<open>length (snd s) + 2 \<le> B\<close> using gen[of \<open>length (snd s)\<close>] EG' by simp
  have h2': \<open>2 * (fst s + length (snd s)) \<le> B\<close>
  proof -
    have b1: \<open>2 * sum_list ws \<le> 1000 * sum_list ws\<close>
      and b2: \<open>2 * length (CoreProblemL_asserts p) \<le> 1000 * length (CoreProblemL_asserts p)\<close>
      and b3: \<open>200 * Y \<le> 1000 * Y\<close> by simp_all
    have \<open>2 * (fst s + length (snd s)) \<le> 2 * (2 + sum_list ws + length (CoreProblemL_asserts p) + 100 * Y)\<close>
      using EG' by simp
    then have \<open>2 * (fst s + length (snd s)) \<le> 4 + 2 * sum_list ws + 2 * length (CoreProblemL_asserts p) + 200 * Y\<close>
      by simp
    then show ?thesis using Bexp b1 b2 b3 by linarith
  qed
  have h3: \<open>2 * length ws + 2 \<le> B\<close> using Bexp by linarith
  have h4: \<open>2 * length (CoreProblemL_defs p) + 2 \<le> B\<close> using Bexp by linarith
  have h5: \<open>2 * length (CoreProblemL_asserts p) + 2 \<le> B\<close> using Bexp by linarith
  have h6: \<open>\<forall>w \<in> set ws. w + 2 \<le> B\<close>
  proof
    fix w assume \<open>w \<in> set ws\<close>
    then have \<open>w \<le> sum_list ws\<close> by (rule member_le_sum_list; simp)
    then show \<open>w + 2 \<le> B\<close> using Bexp by linarith
  qed
  have h7: \<open>\<forall>c \<in> set (snd s). length c + 2 \<le> B\<close>
    using cl Bexp by (auto simp: cl4_def)
  have h8: \<open>\<forall>t \<in> set (CoreProblemL_defs p @ CoreProblemL_asserts p). tbound ws ds t \<le> B\<close>
  proof
    fix t assume t: \<open>t \<in> set (CoreProblemL_defs p @ CoreProblemL_asserts p)\<close>
    have mem: \<open>cterm_weight ws ds t \<in> set (map (cterm_weight ws ds) (CoreProblemL_defs p @ CoreProblemL_asserts p))\<close>
      unfolding set_map by (rule imageI[OF t])
    have \<open>cterm_weight ws ds t \<le> Y\<close>
      unfolding Y_def by (rule member_le_sum_list[OF mem]; simp)
    then show \<open>tbound ws ds t \<le> B\<close> using tbound_le[of ws ds t] Bexp by linarith
  qed
  have \<open>fuel_bound p \<le> B\<close>
    unfolding fuel_bound_def
    apply (simp add: e Let_def ws_def[symmetric] ds_def[symmetric])
    using h1 h2 h2' h3 h4 h5 h6 h7 h8 by auto
  then show ?thesis by (simp add: B_def)
qed

end
