theory QFBV_Luby
  imports Main
begin

section \<open>The Luby sequence: the pure model\<close>

text \<open>A functional model of \<^verbatim>\<open>fn luby\<close> of the restart prototype (branch \<^verbatim>\<open>agent/28207582-perf\<close>,
  commit \<^verbatim>\<open>7378d3b\<close>), statement by statement, on \<open>nat\<close>:
  \<^verbatim>\<open>let mut size = 1; let mut seq = 0;\<close>
  \<^verbatim>\<open>while size < i + 1 { seq += 1; size = 2 * size + 1; }\<close>
  \<^verbatim>\<open>let mut x = i;\<close>
  \<^verbatim>\<open>while size - 1 != x { size = (size - 1) / 2; seq -= 1; x = x % size; }\<close>
  \<^verbatim>\<open>1 << seq\<close>. The variable \<^verbatim>\<open>size\<close> is \<open>sz\<close> here (\<open>size\<close> is a constant of HOL).
  The facts are the ones the contract needs: termination of both loops, the bounds that rule out
  every \<^verbatim>\<open>usize\<close> overflow and underflow and the division by zero, and a positive power-of-2 result
  (the restart budget is \<^verbatim>\<open>100 * luby(restarts)\<close>). The last subsection proves that the model computes
  the Luby sequence.\<close>

subsection \<open>Models\<close>

text \<open>The up loop of \<^verbatim>\<open>luby\<close>: \<open>seq += 1\<close>, \<open>size = 2 * size + 1\<close> while \<open>size < i + 1\<close>.\<close>
function luby_up :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat\<close> where
  \<open>luby_up i sz seq =
    (if sz < i + 1 then luby_up i (2 * sz + 1) (seq + 1) else (sz, seq))\<close>
  by pat_completeness auto
termination
  by (relation \<open>measure (\<lambda>(i, sz, _). i + 1 - sz)\<close>) auto

declare luby_up.simps [simp del]

text \<open>The down loop of \<^verbatim>\<open>luby\<close>: \<open>size = (size - 1) / 2\<close>, \<open>seq -= 1\<close>, \<open>x = x % size\<close> while
  \<open>size - 1 \<noteq> x\<close>. The guard \<open>0 < size\<close> is not in the code (there \<open>size - 1\<close> would underflow); it only
  makes the model terminate, and \<open>down_inv\<close> below shows that it always holds.\<close>
function luby_down :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat \<times> nat\<close> where
  \<open>luby_down sz seq x =
    (if 0 < sz \<and> sz - 1 \<noteq> x then
       (let sz' = (sz - 1) div 2 in luby_down sz' (seq - 1) (x mod sz'))
     else (sz, seq, x))\<close>
  by pat_completeness auto
termination
  by (relation \<open>measure (\<lambda>(sz, _, _). sz)\<close>) (auto simp: Let_def)

declare luby_down.simps [simp del]

definition luby_m :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>luby_m i =
    (case luby_up i 1 0 of (sz, seq) \<Rightarrow>
       (case luby_down sz seq i of (_, seq, _) \<Rightarrow> 2 ^ seq))\<close>

subsection \<open>The up loop\<close>

text \<open>The invariant of the up loop. It holds at the start (\<open>up_inv_init\<close>) and is kept by every
  iteration (\<open>up_inv_step\<close>); in every state \<open>sz \<le> 2 * i + 1\<close>, so for \<open>i < 2 ^ 63\<close> neither
  \<open>i + 1\<close> nor \<open>2 * sz + 1\<close> overflows (\<open>up_inv_no_overflow\<close>,
  \<open>up_step_no_overflow\<close>).\<close>
definition up_inv :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>up_inv i sz seq \<longleftrightarrow> sz = 2 ^ (seq + 1) - 1 \<and> sz \<le> 2 * i + 1\<close>

lemma up_inv_init: \<open>up_inv i 1 0\<close>
  by (simp add: up_inv_def)

lemma up_inv_step:
  assumes \<open>up_inv i sz seq\<close> \<open>sz < i + 1\<close>
  shows \<open>up_inv i (2 * sz + 1) (seq + 1)\<close>
  using assms one_le_power[of \<open>2::nat\<close> seq] unfolding up_inv_def by (simp; linarith)

lemma up_inv_no_overflow:
  assumes \<open>up_inv i sz seq\<close> \<open>i < 2 ^ 63\<close>
  shows \<open>i + 1 < 2 ^ 64\<close> \<open>sz < 2 ^ 64\<close> \<open>seq < 64\<close>
proof -
  have s: \<open>sz = 2 ^ (seq + 1) - 1\<close> \<open>sz \<le> 2 * i + 1\<close> using assms(1) by (auto simp: up_inv_def)
  show \<open>i + 1 < 2 ^ 64\<close> using assms(2) by simp
  have \<open>sz + 1 \<le> 2 ^ 64\<close> using s(2) assms(2) by simp
  moreover have \<open>sz + 1 = 2 ^ (seq + 1)\<close> using s(1) one_le_power[of \<open>2::nat\<close> \<open>seq + 1\<close>] by simp
  ultimately have \<open>(2::nat) ^ (seq + 1) \<le> 2 ^ 64\<close> by metis
  then have \<open>seq + 1 \<le> 64\<close> by (rule power_le_imp_le_exp[rotated]) simp
  then show \<open>seq < 64\<close> by simp
  show \<open>sz < 2 ^ 64\<close> using s(2) assms(2) by simp
qed

text \<open>The new \<open>size\<close> of an iteration, \<open>2 * sz + 1\<close>, does not overflow.\<close>
lemma up_step_no_overflow:
  assumes \<open>up_inv i sz seq\<close> \<open>sz < i + 1\<close> \<open>i < 2 ^ 63\<close>
  shows \<open>2 * sz + 1 < 2 ^ 64\<close> \<open>seq + 1 < 64\<close>
proof -
  show \<open>2 * sz + 1 < 2 ^ 64\<close> using assms(2,3) by simp
  show \<open>seq + 1 < 64\<close> using up_inv_no_overflow(3)[OF up_inv_step[OF assms(1,2)] assms(3)] .
qed

lemma luby_up_inv:
  \<open>up_inv i sz seq \<Longrightarrow> luby_up i sz seq = (sz', seq') \<Longrightarrow>
    up_inv i sz' seq' \<and> i + 1 \<le> sz' \<and> seq \<le> seq'\<close>
proof (induction i sz seq rule: luby_up.induct)
  case (1 i sz seq)
  show ?case
  proof (cases \<open>sz < i + 1\<close>)
    case True
    have \<open>luby_up i (2 * sz + 1) (seq + 1) = (sz', seq')\<close>
      using "1.prems"(2) True by (subst (asm) luby_up.simps) simp
    then show ?thesis using "1.IH"[OF True up_inv_step[OF "1.prems"(1) True]] by simp
  next
    case False
    then have \<open>sz' = sz\<close> \<open>seq' = seq\<close> using "1.prems"(2) by (subst (asm) luby_up.simps; simp)+
    then show ?thesis using False "1.prems"(1) by simp
  qed
qed

lemma luby_up_result:
  assumes \<open>luby_up i 1 0 = (sz, seq)\<close>
  shows \<open>sz = 2 ^ (seq + 1) - 1\<close> \<open>i + 1 \<le> sz\<close> \<open>sz \<le> 2 * i + 1\<close>
  using luby_up_inv[OF up_inv_init assms] by (auto simp: up_inv_def)

subsection \<open>The down loop\<close>

text \<open>The invariant of the down loop, for the argument \<open>i\<close>. In every state \<open>0 < sz\<close> and
  \<open>x < sz\<close>; when the loop goes on (\<open>sz - 1 \<noteq> x\<close>), \<open>1 < sz\<close> and \<open>0 < seq\<close>, so \<open>sz - 1\<close> and
  \<open>seq - 1\<close> do not underflow and the new \<open>sz\<close> is positive, the divisor of \<open>x % sz\<close>
  (\<open>down_inv_step\<close>).\<close>
definition down_inv :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>down_inv i sz seq x \<longleftrightarrow> sz = 2 ^ (seq + 1) - 1 \<and> x < sz \<and> x \<le> i \<and> sz \<le> 2 * i + 1\<close>

lemma down_inv_init:
  assumes \<open>luby_up i 1 0 = (sz, seq)\<close>
  shows \<open>down_inv i sz seq i\<close>
  using luby_up_result[OF assms] by (simp add: down_inv_def)

lemma down_inv_pos: \<open>down_inv i sz seq x \<Longrightarrow> 0 < sz\<close>
  unfolding down_inv_def by linarith

lemma down_inv_step:
  assumes \<open>down_inv i sz seq x\<close> \<open>sz - 1 \<noteq> x\<close>
  shows \<open>1 < sz\<close> \<open>0 < seq\<close> \<open>0 < (sz - 1) div 2\<close>
    \<open>down_inv i ((sz - 1) div 2) (seq - 1) (x mod ((sz - 1) div 2))\<close>
proof -
  have s: \<open>sz = 2 ^ (seq + 1) - 1\<close> \<open>x < sz\<close> \<open>x \<le> i\<close> \<open>sz \<le> 2 * i + 1\<close>
    using assms(1) by (auto simp: down_inv_def)
  show \<open>1 < sz\<close> using s(2) assms(2) by linarith
  show q: \<open>0 < seq\<close>
  proof (rule ccontr)
    assume \<open>\<not> 0 < seq\<close>
    then have \<open>sz = 1\<close> using s(1) by simp
    then show False using \<open>1 < sz\<close> by simp
  qed
  have m: \<open>(sz - 1) div 2 = 2 ^ seq - 1\<close>
  proof -
    have \<open>sz - 1 = 2 * (2 ^ seq - 1)\<close> using s(1) q
      by (simp add: right_diff_distrib' algebra_simps)
    then show ?thesis by simp
  qed
  show p: \<open>0 < (sz - 1) div 2\<close> using m q
    using one_less_power[of \<open>2::nat\<close> seq] by simp
  have \<open>seq - 1 + 1 = seq\<close> using q by simp
  moreover have \<open>x mod ((sz - 1) div 2) < (sz - 1) div 2\<close> using p by simp
  moreover have \<open>x mod ((sz - 1) div 2) \<le> i\<close> using s(3) mod_less_eq_dividend le_trans by blast
  moreover have \<open>(sz - 1) div 2 \<le> 2 * i + 1\<close> using s(4) by linarith
  ultimately show \<open>down_inv i ((sz - 1) div 2) (seq - 1) (x mod ((sz - 1) div 2))\<close>
    using m by (simp add: down_inv_def)
qed

lemma luby_down_inv:
  \<open>down_inv i sz seq x \<Longrightarrow> luby_down sz seq x = (sz', seq', x') \<Longrightarrow>
    down_inv i sz' seq' x' \<and> x' = sz' - 1 \<and> seq' \<le> seq\<close>
proof (induction sz seq x rule: luby_down.induct)
  case (1 sz seq x)
  show ?case
  proof (cases \<open>sz - 1 \<noteq> x\<close>)
    case True
    have c: \<open>0 < sz \<and> sz - 1 \<noteq> x\<close> using True down_inv_pos[OF "1.prems"(1)] by simp
    have r: \<open>luby_down ((sz - 1) div 2) (seq - 1) (x mod ((sz - 1) div 2)) = (sz', seq', x')\<close>
      using "1.prems"(2) c by (subst (asm) luby_down.simps) (simp add: Let_def)
    show ?thesis using "1.IH"[OF c refl down_inv_step(4)[OF "1.prems"(1) True] r] by auto
  next
    case False
    then have \<open>sz' = sz\<close> \<open>seq' = seq\<close> \<open>x' = x\<close>
      using "1.prems"(2) by (subst (asm) luby_down.simps; simp)+
    then show ?thesis using False "1.prems"(1) by simp
  qed
qed

subsection \<open>The result\<close>

lemma luby_m_bounds:
  shows \<open>1 \<le> luby_m i\<close> \<open>luby_m i \<le> i + 1\<close> \<open>\<exists>k. luby_m i = 2 ^ k\<close>
proof -
  obtain sz seq where u: \<open>luby_up i 1 0 = (sz, seq)\<close> by fastforce
  obtain sz' seq' x' where d: \<open>luby_down sz seq i = (sz', seq', x')\<close> by (metis prod.exhaust)
  have l: \<open>luby_m i = 2 ^ seq'\<close> using u d by (simp add: luby_m_def)
  have r: \<open>down_inv i sz' seq' x'\<close> \<open>x' = sz' - 1\<close>
    using luby_down_inv[OF down_inv_init[OF u] d] by auto
  have \<open>sz' = 2 ^ (seq' + 1) - 1\<close> \<open>x' \<le> i\<close> using r(1) by (simp_all add: down_inv_def)
  then have \<open>2 ^ (seq' + 1) - 2 \<le> i\<close> using r(2) by simp
  moreover have \<open>(2::nat) ^ seq' \<le> 2 ^ (seq' + 1) - 2 + 1\<close>
    using one_le_power[of 2 seq'] by simp
  ultimately show \<open>luby_m i \<le> i + 1\<close> using l by linarith
  show \<open>1 \<le> luby_m i\<close> using l by simp
  show \<open>\<exists>k. luby_m i = 2 ^ k\<close> using l by blast
qed

text \<open>The restart budget \<^verbatim>\<open>100 * luby(i)\<close> does not overflow for \<open>i < 2 ^ 57\<close> (this includes the
  range \<open>i < 2 ^ 20 + 1\<close> of the restart counter).\<close>
lemma luby_m_budget:
  assumes \<open>i < 2 ^ 57\<close>
  shows \<open>0 < 100 * luby_m i\<close> \<open>100 * luby_m i < 2 ^ 64\<close>
proof -
  show \<open>0 < 100 * luby_m i\<close> using luby_m_bounds(1)[of i] by simp
  have \<open>100 * luby_m i \<le> 100 * (i + 1)\<close> using luby_m_bounds(2)[of i] by simp
  also have \<open>\<dots> \<le> 100 * 2 ^ 57\<close> using assms by simp
  also have \<open>\<dots> < (2::nat) ^ 64\<close> by simp
  finally show \<open>100 * luby_m i < 2 ^ 64\<close> .
qed

text \<open>The shift \<^verbatim>\<open>1 << seq\<close> is in range: the final \<open>seq\<close> is below 64 for \<open>i < 2 ^ 63\<close>.\<close>
lemma luby_m_shift:
  assumes \<open>i < 2 ^ 63\<close> \<open>luby_up i 1 0 = (sz, seq)\<close> \<open>luby_down sz seq i = (sz', seq', x')\<close>
  shows \<open>seq' < 64\<close> \<open>luby_m i = 2 ^ seq'\<close>
proof -
  have \<open>up_inv i sz seq\<close> using luby_up_inv[OF up_inv_init assms(2)] by simp
  then have \<open>seq < 64\<close> using up_inv_no_overflow(3)[OF _ assms(1)] by simp
  then show \<open>seq' < 64\<close> using luby_down_inv[OF down_inv_init[OF assms(2)] assms(3)] by simp
  show \<open>luby_m i = 2 ^ seq'\<close> using assms(2,3) by (simp add: luby_m_def)
qed

lemma luby_m_first_values:
  \<open>map luby_m [0..<10] = [1, 1, 2, 1, 1, 2, 4, 1, 1, 2]\<close>
  by eval

subsection \<open>The model computes the Luby sequence\<close>

text \<open>The standard recursive definition: \<open>luby_rec i = 2 ^ (k - 1)\<close> if \<open>i + 1 = 2 ^ k - 1\<close>, else
  \<open>luby_rec (i - (2 ^ (k - 1) - 1))\<close>, for the least \<open>k\<close> with \<open>i + 1 \<le> 2 ^ k - 1\<close> (so that
  \<open>2 ^ (k - 1) - 1 < i + 1\<close>).\<close>

lemma luby_least:
  assumes \<open>2 ^ s - 1 < i + 1\<close> \<open>i + 1 \<le> 2 ^ (s + 1) - 1\<close>
  shows \<open>(LEAST k. i + 1 \<le> 2 ^ k - (1::nat)) = s + 1\<close>
proof (rule Least_equality)
  show \<open>i + 1 \<le> 2 ^ (s + 1) - 1\<close> by (fact assms(2))
next
  fix y assume y: \<open>i + 1 \<le> 2 ^ y - (1::nat)\<close>
  show \<open>s + 1 \<le> y\<close>
  proof (rule ccontr)
    assume \<open>\<not> s + 1 \<le> y\<close>
    then have \<open>(2::nat) ^ y \<le> 2 ^ s\<close> by (simp add: power_increasing)
    then show False using y assms(1) by linarith
  qed
qed

lemma luby_level: \<open>\<exists>s. 2 ^ s - 1 < i + 1 \<and> i + 1 \<le> 2 ^ (s + 1) - (1::nat)\<close>
proof -
  let ?P = \<open>\<lambda>k. i + 1 \<le> 2 ^ k - (1::nat)\<close>
  have \<open>i + 1 < 2 ^ (i + 1)\<close> by (rule less_exp)
  then have p: \<open>?P (i + 1)\<close> by simp
  let ?k = \<open>LEAST k. ?P k\<close>
  have k: \<open>?P ?k\<close> using LeastI[of ?P, OF p] .
  have \<open>?k \<noteq> 0\<close> using k by (intro notI) simp
  then obtain s where s: \<open>?k = s + 1\<close> by (metis Suc_eq_plus1 not0_implies_Suc)
  then have \<open>\<not> ?P s\<close> using not_less_Least[of s ?P] by simp
  then show ?thesis using k s by (intro exI[of _ s]) simp
qed

lemma luby_level_step:
  assumes \<open>2 ^ s - 1 < i + 1\<close> \<open>i + 1 \<le> 2 ^ (s + 1) - 1\<close> \<open>i + 1 \<noteq> 2 ^ (s + 1) - (1::nat)\<close>
  shows \<open>0 < s\<close> \<open>0 < 2 ^ s - (1::nat)\<close> \<open>i - (2 ^ s - 1) < i\<close>
proof -
  show s: \<open>0 < s\<close> using assms(2,3) by (cases s) auto
  show m: \<open>0 < 2 ^ s - (1::nat)\<close> using one_less_power[of \<open>2::nat\<close> s] s by simp
  show \<open>i - (2 ^ s - 1) < i\<close> using assms(1) m by linarith
qed

function luby_rec :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>luby_rec i =
    (let k = LEAST k. i + 1 \<le> 2 ^ k - 1 in
     if i + 1 = 2 ^ k - 1 then 2 ^ (k - 1) else luby_rec (i - (2 ^ (k - 1) - 1)))\<close>
  by pat_completeness auto
termination
proof (relation \<open>measure id\<close>)
  fix i k assume k: \<open>k = (LEAST k. i + 1 \<le> 2 ^ k - (1::nat))\<close> and ne: \<open>i + 1 \<noteq> 2 ^ k - 1\<close>
  obtain s where s: \<open>2 ^ s - 1 < i + 1\<close> \<open>i + 1 \<le> 2 ^ (s + 1) - (1::nat)\<close> using luby_level by blast
  have \<open>k = s + 1\<close> using k luby_least[OF s] by simp
  then show \<open>(i - (2 ^ (k - 1) - 1), i) \<in> measure id\<close> using luby_level_step(3)[OF s] ne by simp
qed simp

declare luby_rec.simps [simp del]

lemma luby_rec_level:
  assumes \<open>2 ^ s - 1 < i + 1\<close> \<open>i + 1 \<le> 2 ^ (s + 1) - (1::nat)\<close>
  shows \<open>luby_rec i = (if i + 1 = 2 ^ (s + 1) - 1 then 2 ^ s else luby_rec (i - (2 ^ s - 1)))\<close>
  by (simp only: luby_rec.simps[of i] Let_def luby_least[OF assms]) simp

lemma luby_down_rec:
  \<open>luby_down sz seq x = (sz', seq', x') \<Longrightarrow> sz = 2 ^ (seq + 1) - 1 \<Longrightarrow> x < sz \<Longrightarrow>
    luby_rec x = 2 ^ seq'\<close>
proof (induction sz seq x rule: luby_down.induct)
  case (1 sz seq x)
  show ?case
  proof (cases \<open>sz - 1 = x\<close>)
    case True
    then have \<open>luby_down sz seq x = (sz, seq, x)\<close> by (subst luby_down.simps) simp
    then have \<open>seq' = seq\<close> using "1.prems"(1) by simp
    have \<open>(2::nat) ^ seq < 2 ^ (seq + 1)\<close> by simp
    then have \<open>2 ^ seq - 1 < x + (1::nat)\<close> using True "1.prems"(2,3) one_le_power[of \<open>2::nat\<close> seq]
      by linarith
    moreover have \<open>x + 1 = 2 ^ (seq + 1) - 1\<close> using True "1.prems"(2,3) by linarith
    ultimately show ?thesis using luby_rec_level[of seq x] \<open>seq' = seq\<close> by simp
  next
    case False
    have dv: \<open>down_inv sz sz seq x\<close> using "1.prems"(2,3) by (auto simp: down_inv_def)
    have c: \<open>0 < sz \<and> sz - 1 \<noteq> x\<close> using False down_inv_pos[OF dv] by simp
    have q: \<open>0 < seq\<close> and p: \<open>0 < (sz - 1) div 2\<close> using down_inv_step[OF dv False] by simp_all
    define m where \<open>m = (sz - 1) div 2\<close>
    have m: \<open>m = 2 ^ seq - 1\<close> \<open>sz = 2 * m + 1\<close>
    proof -
      have \<open>sz - 1 = 2 * (2 ^ seq - 1)\<close> using "1.prems"(2) q
        by (simp add: right_diff_distrib' algebra_simps)
      then show \<open>m = 2 ^ seq - 1\<close> unfolding m_def by simp
      then show \<open>sz = 2 * m + 1\<close> using \<open>sz - 1 = 2 * (2 ^ seq - 1)\<close> c by linarith
    qed
    have r: \<open>luby_down m (seq - 1) (x mod m) = (sz', seq', x')\<close>
      using "1.prems"(1) c by (subst (asm) luby_down.simps) (simp add: Let_def m_def)
    have ih: \<open>luby_rec (x mod m) = 2 ^ seq'\<close>
      using "1.IH"[OF c refl r[unfolded m_def]] q p m(1) by (simp add: m_def)
    have \<open>luby_rec x = luby_rec (x mod m)\<close>
    proof (cases \<open>x < m\<close>)
      case True
      then show ?thesis by simp
    next
      case xm: False
      have x2: \<open>x < 2 * m\<close> using "1.prems"(3) False m(2) by linarith
      have \<open>x mod m = x - m\<close> using xm x2 by (simp add: le_mod_geq)
      moreover have \<open>luby_rec x = luby_rec (x - (2 ^ seq - 1))\<close>
      proof -
        have a: \<open>2 ^ seq - 1 < x + (1::nat)\<close> using xm m(1) by linarith
        have b: \<open>x + 1 \<le> 2 ^ (seq + 1) - (1::nat)\<close> using "1.prems"(2,3) by linarith
        have \<open>x + 1 \<noteq> 2 ^ (seq + 1) - (1::nat)\<close> using False "1.prems"(2) by linarith
        then show ?thesis using luby_rec_level[OF a b] by simp
      qed
      ultimately show ?thesis using m(1) by simp
    qed
    then show ?thesis using ih by simp
  qed
qed

theorem luby_m_luby_rec: \<open>luby_m i = luby_rec i\<close>
proof -
  obtain sz seq where u: \<open>luby_up i 1 0 = (sz, seq)\<close> by fastforce
  obtain sz' seq' x' where d: \<open>luby_down sz seq i = (sz', seq', x')\<close> by (metis prod.exhaust)
  have \<open>sz = 2 ^ (seq + 1) - 1\<close> \<open>i < sz\<close> using luby_up_result[OF u] by simp_all
  then show ?thesis using luby_down_rec[OF d] u d by (simp add: luby_m_def)
qed

end
