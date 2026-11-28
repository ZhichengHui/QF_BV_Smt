theory QFBV_Activity
  imports Main
begin

section \<open>The activity arithmetic: the pure model\<close>

text \<open>Functional models of the activity arithmetic of \<^verbatim>\<open>dpll\<close> (commit \<^verbatim>\<open>8945699\<close>, branch
  \<^verbatim>\<open>agent/c0a5fe8b-modes-distrib\<close>; the same arithmetic is in \<^verbatim>\<open>7378d3b\<close>), statement by
  statement, on \<open>nat\<close>: \<^verbatim>\<open>fn rescale\<close> (\<^verbatim>\<open>act[i] = act[i] >> r\<close> for every \<open>i\<close>), the bump of
  \<^verbatim>\<open>analyze_clause\<close> (\<^verbatim>\<open>act[v] = act[v].saturating_add(inc)\<close>), the increment step after an
  analysed conflict (\<^verbatim>\<open>inc = inc + inc / 20\<close>; if \<^verbatim>\<open>inc >= 1 << 40\<close> then both activity vectors
  are rescaled by 30 and \<^verbatim>\<open>inc = inc >> 30\<close>) and the swap of \<open>act\<close>, \<open>act2\<close> and \<open>rev\<close> at a
  restart. The facts are the ones the contracts need: the increment invariant
  \<open>2 ^ 10 \<le> inc < 2 ^ 40\<close>, no \<^verbatim>\<open>usize\<close> overflow anywhere, every activity at most
  \<^verbatim>\<open>usize::MAX\<close>, the lengths, and the order facts (rescale is monotone, a bump does not decrease
  the bumped entry). Ties can appear under rescale, which is why \<^verbatim>\<open>heap_rebuild\<close> follows it.\<close>

definition USIZE_MAX :: nat where
  \<open>USIZE_MAX = 2 ^ 64 - 1\<close>

text \<open>Every activity fits in a \<^verbatim>\<open>usize\<close>.\<close>
definition act_ok :: \<open>nat list \<Rightarrow> bool\<close> where
  \<open>act_ok act \<longleftrightarrow> (\<forall>a \<in> set act. a \<le> USIZE_MAX)\<close>

text \<open>The increment invariant.\<close>
definition inc_ok :: \<open>nat \<Rightarrow> bool\<close> where
  \<open>inc_ok inc \<longleftrightarrow> 2 ^ 10 \<le> inc \<and> inc < 2 ^ 40\<close>

subsection \<open>Models\<close>

text \<open>The loop of \<^verbatim>\<open>rescale\<close>: \<open>act[i] = act[i] >> r\<close>, \<open>i += 1\<close> while \<open>i < act.len()\<close>.\<close>
function rescale_loop :: \<open>nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list\<close> where
  \<open>rescale_loop act r i =
    (if i < length act then rescale_loop (act[i := act ! i div 2 ^ r]) r (i + 1) else act)\<close>
  by pat_completeness auto
termination
  by (relation \<open>measure (\<lambda>(act, _, i). length act - i)\<close>) auto

declare rescale_loop.simps [simp del]

definition rescale_m :: \<open>nat list \<Rightarrow> nat \<Rightarrow> nat list\<close> where
  \<open>rescale_m act r = rescale_loop act r 0\<close>

text \<open>\<^verbatim>\<open>a.saturating_add(b)\<close> on \<^verbatim>\<open>usize\<close>.\<close>
definition sat_add :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>sat_add a b = min (a + b) USIZE_MAX\<close>

text \<open>The bump of \<^verbatim>\<open>analyze_clause\<close>: \<^verbatim>\<open>act[v] = act[v].saturating_add(inc)\<close>.\<close>
definition bump_m :: \<open>nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list\<close> where
  \<open>bump_m act v inc = act[v := sat_add (act ! v) inc]\<close>

text \<open>The initial increment \<^verbatim>\<open>1 << 10\<close> and activities \<^verbatim>\<open>vec![0; n]\<close>.\<close>
definition inc0 :: nat where
  \<open>inc0 = 2 ^ 10\<close>

text \<open>The increment step after an analysed conflict: \<^verbatim>\<open>inc = inc + inc / 20\<close>; if
  \<^verbatim>\<open>inc >= 1 << 40\<close>, \<^verbatim>\<open>act = rescale(act, 30)\<close>, \<^verbatim>\<open>act2 = rescale(act2, 30)\<close>,
  \<^verbatim>\<open>inc = inc >> 30\<close> (the \<^verbatim>\<open>heap_rebuild\<close> that follows is \<open>heap_rebuild_m\<close> of
  \<^verbatim>\<open>QFBV_Heap\<close>).\<close>
definition inc_step_m :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list \<times> nat list \<times> nat\<close> where
  \<open>inc_step_m act act2 inc =
    (let inc = inc + inc div 20 in
     if 2 ^ 40 \<le> inc then (rescale_m act 30, rescale_m act2 30, inc div 2 ^ 30)
     else (act, act2, inc))\<close>

text \<open>The swap at a restart: \<^verbatim>\<open>let other = act2; act2 = act; act = other; rev = !rev\<close>.\<close>
definition swap_m :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> bool \<Rightarrow> nat list \<times> nat list \<times> bool\<close> where
  \<open>swap_m act act2 rv = (act2, act, \<not> rv)\<close>

subsection \<open>Rescale\<close>

lemma rescale_loop_eq:
  \<open>rescale_loop act r i = take i act @ map (\<lambda>a. a div 2 ^ r) (drop i act)\<close>
proof (induction act r i rule: rescale_loop.induct)
  case (1 act r i)
  show ?case
  proof (cases \<open>i < length act\<close>)
    case True
    have \<open>rescale_loop act r i = rescale_loop (act[i := act ! i div 2 ^ r]) r (i + 1)\<close>
      using True by (simp add: rescale_loop.simps)
    also have \<open>\<dots> = take (i + 1) (act[i := act ! i div 2 ^ r])
        @ map (\<lambda>a. a div 2 ^ r) (drop (i + 1) (act[i := act ! i div 2 ^ r]))\<close>
      using 1 True by simp
    also have \<open>\<dots> = take i act @ map (\<lambda>a. a div 2 ^ r) (drop i act)\<close>
      using True by (simp add: take_Suc_conv_app_nth Cons_nth_drop_Suc[symmetric])
    finally show ?thesis .
  next
    case False
    then show ?thesis by (simp add: rescale_loop.simps)
  qed
qed

lemma rescale_m_eq: \<open>rescale_m act r = map (\<lambda>a. a div 2 ^ r) act\<close>
  by (simp add: rescale_m_def rescale_loop_eq)

lemma length_rescale_m [simp]: \<open>length (rescale_m act r) = length act\<close>
  by (simp add: rescale_m_eq)

lemma nth_rescale_m: \<open>i < length act \<Longrightarrow> rescale_m act r ! i = act ! i div 2 ^ r\<close>
  by (simp add: rescale_m_eq)

text \<open>The index \<open>i\<close> of the loop is always below \<open>act.len()\<close> when it is used, and \<open>i += 1\<close> does
  not overflow (\<open>i < length act \<le> USIZE_MAX\<close>); the shift by \<open>r\<close> is defined for every \<open>r < 64\<close>
  (the code uses \<open>r = 30\<close>).\<close>

lemma rescale_m_mono:
  \<open>u < length act \<Longrightarrow> v < length act \<Longrightarrow> act ! u \<le> act ! v \<Longrightarrow>
   rescale_m act r ! u \<le> rescale_m act r ! v\<close>
  by (simp add: nth_rescale_m div_le_mono)

lemma rescale_m_le: \<open>i < length act \<Longrightarrow> rescale_m act r ! i \<le> act ! i\<close>
  by (simp add: nth_rescale_m)

lemma act_ok_rescale_m: \<open>act_ok act \<Longrightarrow> act_ok (rescale_m act r)\<close>
  by (auto simp: act_ok_def rescale_m_eq intro: le_trans[OF div_le_dividend])

text \<open>After a rescale by 30 of activities that fit in a \<^verbatim>\<open>usize\<close>, every activity is below \<open>2 ^ 34\<close>.\<close>
lemma rescale_m_30_bound: \<open>act_ok act \<Longrightarrow> a \<in> set (rescale_m act 30) \<Longrightarrow> a < 2 ^ 34\<close>
  by (auto simp: act_ok_def rescale_m_eq USIZE_MAX_def less_mult_imp_div_less)

subsection \<open>Bump\<close>

lemma sat_add_le_max: \<open>sat_add a b \<le> USIZE_MAX\<close>
  by (simp add: sat_add_def)

lemma sat_add_ge: \<open>a \<le> USIZE_MAX \<Longrightarrow> a \<le> sat_add a b\<close>
  by (simp add: sat_add_def)

lemma sat_add_exact: \<open>a + b \<le> USIZE_MAX \<Longrightarrow> sat_add a b = a + b\<close>
  by (simp add: sat_add_def)

lemma length_bump_m [simp]: \<open>length (bump_m act v inc) = length act\<close>
  by (simp add: bump_m_def)

lemma act_ok_bump_m: \<open>act_ok act \<Longrightarrow> act_ok (bump_m act v inc)\<close>
  by (auto simp: act_ok_def bump_m_def sat_add_le_max dest: set_update_subset_insert[THEN subsetD])

lemma bump_m_nth_ge: \<open>act_ok act \<Longrightarrow> v < length act \<Longrightarrow> act ! v \<le> bump_m act v inc ! v\<close>
  by (simp add: bump_m_def act_ok_def sat_add_ge)

lemma bump_m_nth: \<open>v < length act \<Longrightarrow> bump_m act v inc ! v = sat_add (act ! v) inc\<close>
  by (simp add: bump_m_def)

lemma bump_m_nth_other: \<open>u \<noteq> v \<Longrightarrow> bump_m act v inc ! u = act ! u\<close>
  by (simp add: bump_m_def)

lemma bump_m_mono: \<open>act_ok act \<Longrightarrow> u < length act \<Longrightarrow> act ! u \<le> bump_m act v inc ! u\<close>
  by (cases \<open>u = v\<close>) (simp_all add: bump_m_nth_ge bump_m_nth_other)

subsection \<open>The increment\<close>

lemma inc_ok_inc0: \<open>inc_ok inc0\<close>
  by (simp add: inc_ok_def inc0_def)

lemma act_ok_replicate: \<open>act_ok (replicate n 0)\<close>
  by (simp add: act_ok_def)

text \<open>No overflow in \<^verbatim>\<open>inc + inc / 20\<close>: for \<open>inc < 2 ^ 40\<close> the sum stays below \<open>2 ^ 41\<close>.\<close>
lemma inc_add_bound: \<open>inc < 2 ^ 40 \<Longrightarrow> inc + inc div 20 < (2 ^ 41 :: nat)\<close>
  using div_le_dividend[of inc 20] by simp

lemma inc_add_no_overflow: \<open>inc < 2 ^ 40 \<Longrightarrow> inc + inc div 20 \<le> USIZE_MAX\<close>
  using inc_add_bound[of inc] by (simp add: USIZE_MAX_def)

text \<open>After \<open>inc >> 30\<close> with \<open>2 ^ 40 \<le> inc < 2 ^ 41\<close>: \<open>2 ^ 10 \<le> inc >> 30 < 2 ^ 11\<close>.\<close>
lemma inc_shift_bounds:
  fixes j :: nat
  assumes \<open>2 ^ 40 \<le> j\<close> \<open>j < 2 ^ 41\<close>
  shows \<open>2 ^ 10 \<le> j div 2 ^ 30\<close> \<open>j div 2 ^ 30 < 2 ^ 11\<close>
proof -
  have \<open>(2 ^ 40 :: nat) div 2 ^ 30 \<le> j div 2 ^ 30\<close>
    using assms(1) by (rule div_le_mono)
  then show \<open>2 ^ 10 \<le> j div 2 ^ 30\<close> by simp
  show \<open>j div 2 ^ 30 < 2 ^ 11\<close>
    using assms(2) by (simp add: less_mult_imp_div_less)
qed

lemma inc_step_m_inc:
  assumes \<open>inc_ok inc\<close>
  shows \<open>inc_ok (snd (snd (inc_step_m act act2 inc)))\<close>
proof -
  let ?j = \<open>inc + inc div 20\<close>
  have j: \<open>?j < 2 ^ 41\<close> \<open>inc \<le> ?j\<close>
    using assms inc_add_bound[of inc] by (simp_all add: inc_ok_def)
  show ?thesis
  proof (cases \<open>2 ^ 40 \<le> ?j\<close>)
    case True
    then show ?thesis
      using inc_shift_bounds[OF True j(1)] by (simp add: inc_step_m_def inc_ok_def)
  next
    case False
    then show ?thesis
      using assms j(2) by (simp add: inc_step_m_def inc_ok_def Let_def)
  qed
qed

text \<open>The bound of the bump that the next conflict uses: \<open>inc < 2 ^ 40\<close>.\<close>
lemma inc_ok_le_max: \<open>inc_ok inc \<Longrightarrow> inc \<le> USIZE_MAX\<close>
  by (simp add: inc_ok_def USIZE_MAX_def)

lemma inc_step_m_lengths:
  \<open>inc_step_m act act2 inc = (act', act2', inc') \<Longrightarrow>
   length act' = length act \<and> length act2' = length act2\<close>
  by (auto simp: inc_step_m_def Let_def split: if_splits)

lemma inc_step_m_act_ok:
  \<open>inc_step_m act act2 inc = (act', act2', inc') \<Longrightarrow> act_ok act \<Longrightarrow> act_ok act2 \<Longrightarrow>
   act_ok act' \<and> act_ok act2'\<close>
  by (auto simp: inc_step_m_def Let_def act_ok_rescale_m split: if_splits)

text \<open>The step does not change the order of activities (it is the identity or a rescale).\<close>
lemma inc_step_m_mono:
  \<open>inc_step_m act act2 inc = (act', act2', inc') \<Longrightarrow> u < length act \<Longrightarrow> v < length act \<Longrightarrow>
   act ! u \<le> act ! v \<Longrightarrow> act' ! u \<le> act' ! v\<close>
  by (auto simp: inc_step_m_def Let_def rescale_m_mono split: if_splits)

text \<open>All facts of the step together.\<close>
lemma inc_step_m_inv:
  assumes \<open>inc_step_m act act2 inc = (act', act2', inc')\<close> \<open>inc_ok inc\<close>
    \<open>act_ok act\<close> \<open>act_ok act2\<close> \<open>length act = n\<close> \<open>length act2 = n\<close>
  shows \<open>inc_ok inc' \<and> act_ok act' \<and> act_ok act2' \<and> length act' = n \<and> length act2' = n\<close>
  using inc_step_m_inc[OF assms(2), of act act2] inc_step_m_lengths[OF assms(1)]
    inc_step_m_act_ok[OF assms(1,3,4)] assms(1,5,6) by simp

subsection \<open>The swap at a restart\<close>

lemma swap_m_inv:
  \<open>swap_m act act2 rv = (act', act2', rv') \<Longrightarrow> length act = n \<Longrightarrow> length act2 = n \<Longrightarrow>
   act_ok act \<Longrightarrow> act_ok act2 \<Longrightarrow>
   length act' = n \<and> length act2' = n \<and> act_ok act' \<and> act_ok act2' \<and> rv' = (\<not> rv)\<close>
  by (auto simp: swap_m_def)

end
