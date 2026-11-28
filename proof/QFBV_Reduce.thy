theory QFBV_Reduce
  imports Main "HOL-Library.Sublist"
begin

section \<open>Learned-clause deletion: the pure model\<close>

text \<open>Functional models of \<^verbatim>\<open>level_at\<close>, \<^verbatim>\<open>clause_lbd\<close> and the selection and compaction
  part of \<^verbatim>\<open>reduce_db\<close> of the deletion prototype (branch \<^verbatim>\<open>agent/034a756b-reduce\<close>, commit
  \<^verbatim>\<open>7043c52\<close>), statement by statement, on \<open>nat\<close>s and lists. A clause enters \<^verbatim>\<open>clause_lbd\<close> as
  the list of its variables (\<open>map (\<lambda>l. unat (Lit_var l)) c\<close>); in \<^verbatim>\<open>reduce_db\<close> the clauses
  are of any type \<open>'c\<close>. The rebuild of the watch lists (\<^verbatim>\<open>next2\<close>, \<^verbatim>\<open>head2\<close>) is not modelled
  here. The facts are the ones the contract needs: the bounds of every index, the closed form of
  every loop, that the original clauses, the reasons and the clauses of LBD at most 2 are kept,
  that at least half of the other learned clauses are kept, and that the kept clauses keep their
  order, their watched positions and (through \<^verbatim>\<open>map\<close>) the reasons.\<close>

subsection \<open>\<^verbatim>\<open>level_at\<close>\<close>

text \<open>The binary search of \<^verbatim>\<open>level_at\<close>:
  \<^verbatim>\<open>while lo < hi { let mid = lo + (hi - lo) / 2; if lim[mid] <= p { lo = mid + 1 } else { hi = mid } }\<close>.\<close>
function la_loop :: \<open>nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>la_loop lim p lo hi =
    (if lo < hi then
       (let mid = lo + (hi - lo) div 2 in
        if lim ! mid \<le> p then la_loop lim p (mid + 1) hi else la_loop lim p lo mid)
     else lo)\<close>
  by pat_completeness auto
termination
  by (relation \<open>measure (\<lambda>(_, _, lo, hi). hi - lo)\<close>) (auto simp: Let_def)

declare la_loop.simps [simp del]

definition level_at_m :: \<open>nat list \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>level_at_m lim p = la_loop lim p 0 (length lim)\<close>

text \<open>\<open>mid\<close> lies in \<open>[lo, hi)\<close>, so \<^verbatim>\<open>lim[mid]\<close> is in range when \<open>hi \<le> length lim\<close>, and
  \<open>mid + 1\<close> does not overflow.\<close>
lemma la_mid_range:
  \<open>(lo::nat) < hi \<Longrightarrow> lo \<le> lo + (hi - lo) div 2 \<and> lo + (hi - lo) div 2 < hi\<close>
  by auto

lemma la_loop_inv:
  assumes \<open>sorted lim\<close> \<open>lo \<le> hi\<close> \<open>hi \<le> length lim\<close>
    \<open>\<forall>i < lo. lim ! i \<le> p\<close> \<open>\<forall>i. hi \<le> i \<and> i < length lim \<longrightarrow> p < lim ! i\<close>
  shows \<open>la_loop lim p lo hi \<le> length lim \<and> (\<forall>i < la_loop lim p lo hi. lim ! i \<le> p) \<and>
    (\<forall>i. la_loop lim p lo hi \<le> i \<and> i < length lim \<longrightarrow> p < lim ! i)\<close>
  using assms
proof (induction lim p lo hi rule: la_loop.induct)
  case (1 lim p lo hi)
  show ?case
  proof (cases \<open>lo < hi\<close>)
    case True
    define mid where \<open>mid = lo + (hi - lo) div 2\<close>
    have mid: \<open>lo \<le> mid\<close> \<open>mid < hi\<close> using True by (auto simp: mid_def)
    show ?thesis
    proof (cases \<open>lim ! mid \<le> p\<close>)
      case le: True
      have lo': \<open>\<forall>i < mid + 1. lim ! i \<le> p\<close>
        using "1.prems"(1,3,4) le mid sorted_nth_mono[OF "1.prems"(1)]
        by (metis le_trans less_Suc_eq_le less_le_trans Suc_eq_plus1 linorder_not_le)
      have \<open>la_loop lim p lo hi = la_loop lim p (mid + 1) hi\<close>
        using True le by (subst la_loop.simps) (simp add: mid_def Let_def)
      then show ?thesis
        using "1.IH"(1)[OF True mid_def le "1.prems"(1) _ "1.prems"(3) lo' "1.prems"(5)] mid by simp
    next
      case gt: False
      have hi': \<open>\<forall>i. mid \<le> i \<and> i < length lim \<longrightarrow> p < lim ! i\<close>
        using gt sorted_nth_mono[OF "1.prems"(1)] by (meson le_less_trans linorder_not_le)
      have \<open>la_loop lim p lo hi = la_loop lim p lo mid\<close>
        using True gt by (subst la_loop.simps) (simp add: mid_def Let_def)
      then show ?thesis
        using "1.IH"(2)[OF True mid_def gt "1.prems"(1) _ _ "1.prems"(4) hi'] mid "1.prems"(3) by simp
    qed
  next
    case False
    then have \<open>la_loop lim p lo hi = lo\<close> by (subst la_loop.simps) simp
    then show ?thesis using False "1.prems" by auto
  qed
qed

lemma level_at_m_props:
  assumes \<open>sorted lim\<close>
  shows \<open>level_at_m lim p \<le> length lim\<close> \<open>\<forall>i < level_at_m lim p. lim ! i \<le> p\<close>
    \<open>\<forall>i. level_at_m lim p \<le> i \<and> i < length lim \<longrightarrow> p < lim ! i\<close>
  using la_loop_inv[OF assms, of 0 \<open>length lim\<close> p] by (auto simp: level_at_m_def)

text \<open>The level is the number of decision positions at or before \<open>p\<close>.\<close>
lemma level_at_m_eq:
  assumes \<open>sorted lim\<close>
  shows \<open>level_at_m lim p = length (filter (\<lambda>x. x \<le> p) lim)\<close>
proof -
  let ?r = \<open>level_at_m lim p\<close>
  note r = level_at_m_props[OF assms, of p]
  have \<open>filter (\<lambda>x. x \<le> p) (take ?r lim) = take ?r lim\<close>
    using r(2) by (auto simp: filter_id_conv in_set_conv_nth)
  moreover have \<open>filter (\<lambda>x. x \<le> p) (drop ?r lim) = []\<close>
    using r(3) by (auto simp: filter_empty_conv in_set_conv_nth not_le)
  ultimately have \<open>filter (\<lambda>x. x \<le> p) lim = take ?r lim\<close>
    by (metis append_Nil2 append_take_drop_id filter_append)
  then show ?thesis using r(1) by simp
qed

lemma level_at_m_le: \<open>sorted lim \<Longrightarrow> level_at_m lim p \<le> length lim\<close>
  using level_at_m_props(1) .

subsection \<open>\<^verbatim>\<open>clause_lbd\<close>\<close>

text \<open>The loop of \<^verbatim>\<open>clause_lbd\<close>, over the variables \<open>vs\<close> of the clause:
  \<^verbatim>\<open>let v = level_at(lim, tp[c[k].var]); if v < mark.len() && mark[v] != st { mark[v] = st; d += 1; } k += 1\<close>.\<close>
function lbd_loop :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat list\<close> where
  \<open>lbd_loop vs tp lim mark st d k =
    (if k < length vs then
       (let v = level_at_m lim (tp ! (vs ! k)) in
        if v < length mark \<and> mark ! v \<noteq> st then lbd_loop vs tp lim (mark[v := st]) st (d + 1) (k + 1)
        else lbd_loop vs tp lim mark st d (k + 1))
     else (d, mark))\<close>
  by pat_completeness auto
termination
  by (relation \<open>measure (\<lambda>(vs, _, _, _, _, _, k). length vs - k)\<close>) auto

declare lbd_loop.simps [simp del]

definition clause_lbd_m :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<times> nat list\<close> where
  \<open>clause_lbd_m vs tp lim mark st = lbd_loop vs tp lim mark st 0 0\<close>

text \<open>The levels below \<open>n\<close> of the variables \<open>vs\<close>.\<close>
definition lvls :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat set\<close> where
  \<open>lvls tp lim n vs = {v. v < n \<and> (\<exists>x \<in> set vs. level_at_m lim (tp ! x) = v)}\<close>

lemma lvls_finite: \<open>finite (lvls tp lim n vs)\<close>
  by (simp add: lvls_def)

lemma lvls_take_Suc:
  \<open>k < length vs \<Longrightarrow> lvls tp lim n (take (Suc k) vs) =
    lvls tp lim n (take k vs) \<union> {v. v < n \<and> v = level_at_m lim (tp ! (vs ! k))}\<close>
  by (auto simp: lvls_def take_Suc_conv_app_nth)

lemma lbd_loop_inv:
  assumes \<open>k \<le> length vs\<close> \<open>\<forall>v < length mark. mark ! v = st \<longleftrightarrow> v \<in> lvls tp lim (length mark) (take k vs)\<close>
    \<open>d = card (lvls tp lim (length mark) (take k vs))\<close>
    \<open>lbd_loop vs tp lim mark st d k = (d', mark')\<close>
  shows \<open>d' = card (lvls tp lim (length mark) vs) \<and> length mark' = length mark \<and>
    (\<forall>v < length mark. mark' ! v = st \<longleftrightarrow> v \<in> lvls tp lim (length mark) vs)\<close>
  using assms
proof (induction vs tp lim mark st d k rule: lbd_loop.induct)
  case (1 vs tp lim mark st d k)
  show ?case
  proof (cases \<open>k < length vs\<close>)
    case True
    define v where \<open>v = level_at_m lim (tp ! (vs ! k))\<close>
    note L = lvls_take_Suc[OF True, of tp lim]
    show ?thesis
    proof (cases \<open>v < length mark \<and> mark ! v \<noteq> st\<close>)
      case new: True
      have nin: \<open>v \<notin> lvls tp lim (length mark) (take k vs)\<close> using new "1.prems"(2) by blast
      have eq: \<open>lbd_loop vs tp lim mark st d k = lbd_loop vs tp lim (mark[v := st]) st (d + 1) (k + 1)\<close>
        using True new by (subst lbd_loop.simps) (simp add: v_def Let_def)
      have \<open>lvls tp lim (length mark) (take (k + 1) vs) = insert v (lvls tp lim (length mark) (take k vs))\<close>
        using new by (auto simp: L v_def)
      then have \<open>d + 1 = card (lvls tp lim (length mark) (take (k + 1) vs))\<close>
        using "1.prems"(3) nin by (simp add: lvls_finite)
      moreover have \<open>\<forall>u < length (mark[v := st]). mark[v := st] ! u = st \<longleftrightarrow>
          u \<in> lvls tp lim (length (mark[v := st])) (take (k + 1) vs)\<close>
        using "1.prems"(2) new by (auto simp: L v_def nth_list_update)
      ultimately show ?thesis
        using "1.IH"(1)[OF True v_def new _ _ _ "1.prems"(4)[unfolded eq]] True by simp
    next
      case old: False
      have eq: \<open>lbd_loop vs tp lim mark st d k = lbd_loop vs tp lim mark st d (k + 1)\<close>
        using True old[unfolded v_def] by (subst lbd_loop.simps) (auto simp: Let_def)
      have same: \<open>lvls tp lim (length mark) (take (k + 1) vs) = lvls tp lim (length mark) (take k vs)\<close>
        using old "1.prems"(2) by (auto simp: L v_def)
      show ?thesis
        using "1.IH"(2)[OF True v_def old _ _ _ "1.prems"(4)[unfolded eq]] True "1.prems"(2,3)
        unfolding same by simp
    qed
  next
    case False
    then have \<open>d' = d\<close> \<open>mark' = mark\<close> \<open>k = length vs\<close>
      using "1.prems"(1,4) by (subst (asm) lbd_loop.simps; simp)+
    then show ?thesis using "1.prems"(2,3) by simp
  qed
qed

text \<open>For a stamp \<open>st\<close> that no level holds, \<^verbatim>\<open>clause_lbd\<close> returns the number of distinct levels
  below \<^verbatim>\<open>mark.len()\<close> of the variables, which is at most their number, and \<open>mark\<close> keeps its
  length.\<close>
lemma clause_lbd_m_props:
  assumes \<open>st \<notin> set mark\<close> \<open>clause_lbd_m vs tp lim mark st = (d, mark')\<close>
  shows \<open>d = card (lvls tp lim (length mark) vs)\<close> \<open>length mark' = length mark\<close>
    \<open>\<forall>v < length mark. mark' ! v = st \<longleftrightarrow> v \<in> lvls tp lim (length mark) vs\<close>
proof -
  have \<open>\<forall>v < length mark. mark ! v = st \<longleftrightarrow> v \<in> lvls tp lim (length mark) (take 0 vs)\<close>
    using assms(1) by (auto simp: lvls_def in_set_conv_nth)
  note r = lbd_loop_inv[OF _ this _ assms(2)[unfolded clause_lbd_m_def]]
  show \<open>d = card (lvls tp lim (length mark) vs)\<close> \<open>length mark' = length mark\<close>
    \<open>\<forall>v < length mark. mark' ! v = st \<longleftrightarrow> v \<in> lvls tp lim (length mark) vs\<close>
    using r by (simp_all add: lvls_def)
qed

lemma lvls_card_le: \<open>card (lvls tp lim n vs) \<le> length vs\<close>
proof -
  have \<open>lvls tp lim n vs \<subseteq> (\<lambda>x. level_at_m lim (tp ! x)) ` set vs\<close> by (auto simp: lvls_def)
  then have \<open>card (lvls tp lim n vs) \<le> card (set vs)\<close>
    by (meson card_image_le card_mono finite_imageI finite_set le_trans)
  then show ?thesis using card_length le_trans by blast
qed

lemma clause_lbd_m_le:
  \<open>st \<notin> set mark \<Longrightarrow> clause_lbd_m vs tp lim mark st = (d, mark') \<Longrightarrow> d \<le> length vs\<close>
  using clause_lbd_m_props(1) lvls_card_le by metis

subsection \<open>Selection: \<^verbatim>\<open>locked\<close>, \<^verbatim>\<open>top\<close>, \<^verbatim>\<open>hist\<close>, \<^verbatim>\<open>t\<close>, \<^verbatim>\<open>keep\<close>\<close>

text \<open>The first loop of \<^verbatim>\<open>reduce_db\<close>: \<^verbatim>\<open>if rs[i] < m { locked[rs[i]] = true; } i += 1\<close>.\<close>
function lock_loop :: \<open>nat list \<Rightarrow> nat \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> bool list\<close> where
  \<open>lock_loop rs m locked i =
    (if i < length rs then
       lock_loop rs m (if rs ! i < m then locked[rs ! i := True] else locked) (i + 1)
     else locked)\<close>
  by pat_completeness auto
termination
  by (relation \<open>measure (\<lambda>(rs, _, _, i). length rs - i)\<close>) auto

declare lock_loop.simps [simp del]

definition locked_m :: \<open>nat list \<Rightarrow> nat \<Rightarrow> bool list\<close> where
  \<open>locked_m rs m = lock_loop rs m (replicate m False) 0\<close>

text \<open>The loop of \<^verbatim>\<open>top\<close>: \<^verbatim>\<open>if lbd[c - m0] >= top { top = lbd[c - m0] + 1; } c += 1\<close>.
  The variable \<^verbatim>\<open>top\<close> is \<open>tb\<close> here (\<open>top\<close> is a constant of HOL).\<close>
function top_loop :: \<open>nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>top_loop lbd m0 m tb c =
    (if c < m then
       top_loop lbd m0 m (if tb \<le> lbd ! (c - m0) then lbd ! (c - m0) + 1 else tb) (c + 1)
     else tb)\<close>
  by pat_completeness auto
termination
  by (relation \<open>measure (\<lambda>(_, _, m, _, c). m - c)\<close>) auto

declare top_loop.simps [simp del]

definition top_m :: \<open>nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>top_m lbd m0 m = top_loop lbd m0 m 3 m0\<close>

text \<open>A candidate for deletion: an unlocked learned clause of LBD above 2.\<close>
definition isc :: \<open>bool list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>isc locked lbd m0 c \<longleftrightarrow> \<not> locked ! c \<and> 2 < lbd ! (c - m0)\<close>

text \<open>The loop of \<^verbatim>\<open>hist\<close>:
  \<^verbatim>\<open>if !locked[c] && lbd[c - m0] > 2 { hist[lbd[c - m0]] += 1; cand += 1; } c += 1\<close>.\<close>
function hist_loop :: \<open>bool list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<times> nat\<close> where
  \<open>hist_loop locked lbd m0 m hist cand c =
    (if c < m then
       (if \<not> locked ! c \<and> 2 < lbd ! (c - m0) then
          hist_loop locked lbd m0 m (hist[lbd ! (c - m0) := hist ! (lbd ! (c - m0)) + 1]) (cand + 1) (c + 1)
        else hist_loop locked lbd m0 m hist cand (c + 1))
     else (hist, cand))\<close>
  by pat_completeness auto
termination
  by (relation \<open>measure (\<lambda>(_, _, _, m, _, _, c). m - c)\<close>) auto

declare hist_loop.simps [simp del]

text \<open>The loop of the threshold:
  \<^verbatim>\<open>while t < top && acc + hist[t] <= quota { acc += hist[t]; t += 1; }\<close>.\<close>
function thr_loop :: \<open>nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat\<close> where
  \<open>thr_loop hist tb quota t acc =
    (if t < tb \<and> acc + hist ! t \<le> quota then thr_loop hist tb quota (t + 1) (acc + hist ! t)
     else (t, acc))\<close>
  by pat_completeness auto
termination
  by (relation \<open>measure (\<lambda>(_, tb, _, t, _). tb - t)\<close>) auto

declare thr_loop.simps [simp del]

text \<open>The backward loop of \<^verbatim>\<open>keep\<close>: \<^verbatim>\<open>c -= 1; let b = lbd[c - m0];\<close>
  \<^verbatim>\<open>if !locked[c] && b > 2 && b >= t { if b == t && left > 0 { left -= 1; } else { keep[c] = false; } }\<close>,
  while \<open>c > m0\<close>; here \<open>c - 1\<close> is the new \<open>c\<close>.\<close>
function keep_loop :: \<open>bool list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool list \<times> nat\<close> where
  \<open>keep_loop locked lbd m0 t keep left c =
    (if m0 < c then
       (let b = lbd ! (c - 1 - m0) in
        if \<not> locked ! (c - 1) \<and> 2 < b \<and> t \<le> b then
          (if b = t \<and> 0 < left then keep_loop locked lbd m0 t keep (left - 1) (c - 1)
           else keep_loop locked lbd m0 t (keep[c - 1 := False]) left (c - 1))
        else keep_loop locked lbd m0 t keep left (c - 1))
     else (keep, left))\<close>
  by pat_completeness auto
termination
  by (relation \<open>measure (\<lambda>(_, _, _, _, _, _, c). c)\<close>) auto

declare keep_loop.simps [simp del]

text \<open>The selection of \<^verbatim>\<open>reduce_db\<close>, up to the \<^verbatim>\<open>keep\<close> mask.\<close>
definition sel_m :: \<open>nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow>
    bool list \<times> nat \<times> nat list \<times> nat \<times> nat \<times> nat \<times> nat \<times> bool list\<close> where
  \<open>sel_m m lbd rs m0 =
    (let locked = locked_m rs m; tb = top_m lbd m0 m in
     case hist_loop locked lbd m0 m (replicate tb 0) 0 m0 of (hist, cand) \<Rightarrow>
     (let quota = cand div 2 in
      case thr_loop hist tb quota 3 0 of (t, acc) \<Rightarrow>
      (case keep_loop locked lbd m0 t (replicate m True) (quota - acc) m of (keep, _) \<Rightarrow>
       (locked, tb, hist, cand, quota, t, acc, keep))))\<close>

definition keep_m :: \<open>nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool list\<close> where
  \<open>keep_m m lbd rs m0 = (case sel_m m lbd rs m0 of (_, _, _, _, _, _, _, keep) \<Rightarrow> keep)\<close>

subsubsection \<open>Closed forms of the loops\<close>

lemma lock_loop_eq:
  \<open>length locked = m \<Longrightarrow> length (lock_loop rs m locked i) = m \<and>
    (\<forall>c < m. lock_loop rs m locked i ! c \<longleftrightarrow> locked ! c \<or> c \<in> set (drop i rs))\<close>
proof (induction rs m locked i rule: lock_loop.induct)
  case (1 rs m locked i)
  show ?case
  proof (cases \<open>i < length rs\<close>)
    case True
    have d: \<open>drop i rs = rs ! i # drop (i + 1) rs\<close> using True by (simp add: Cons_nth_drop_Suc)
    have \<open>lock_loop rs m locked i = lock_loop rs m (if rs ! i < m then locked[rs ! i := True] else locked) (i + 1)\<close>
      using True by (subst lock_loop.simps) simp
    then show ?thesis using "1.IH"[OF True] "1.prems" d by (auto simp: nth_list_update)
  next
    case False
    then show ?thesis using "1.prems" by (subst lock_loop.simps; simp)+
  qed
qed

lemma locked_m_props:
  \<open>length (locked_m rs m) = m\<close> \<open>c < m \<Longrightarrow> locked_m rs m ! c \<longleftrightarrow> c \<in> set rs\<close>
  using lock_loop_eq[of \<open>replicate m False\<close> m rs 0] by (auto simp: locked_m_def)

lemma top_loop_bound:
  \<open>tb \<le> top_loop lbd m0 m tb c \<and> (\<forall>j. c \<le> j \<and> j < m \<longrightarrow> lbd ! (j - m0) < top_loop lbd m0 m tb c)\<close>
proof (induction lbd m0 m tb c rule: top_loop.induct)
  case (1 lbd m0 m tb c)
  show ?case
  proof (cases \<open>c < m\<close>)
    case True
    define tb' where \<open>tb' = (if tb \<le> lbd ! (c - m0) then lbd ! (c - m0) + 1 else tb)\<close>
    have e: \<open>top_loop lbd m0 m tb c = top_loop lbd m0 m tb' (c + 1)\<close>
      using True by (subst top_loop.simps) (simp add: tb'_def)
    have a: \<open>tb \<le> tb'\<close> \<open>lbd ! (c - m0) < tb'\<close> by (auto simp: tb'_def)
    note ih = "1.IH"[OF True, folded tb'_def]
    show ?thesis unfolding e
    proof (intro conjI allI impI)
      show \<open>tb \<le> top_loop lbd m0 m tb' (c + 1)\<close> using ih a(1) by linarith
      fix j assume j: \<open>c \<le> j \<and> j < m\<close>
      then consider \<open>j = c\<close> | \<open>c + 1 \<le> j\<close> by linarith
      then show \<open>lbd ! (j - m0) < top_loop lbd m0 m tb' (c + 1)\<close>
        using ih a(2) j by cases auto
    qed
  next
    case False
    then show ?thesis by (subst top_loop.simps; simp)
  qed
qed

text \<open>Every index of \<^verbatim>\<open>hist\<close> is below \<open>top\<close>, its length.\<close>
lemma top_m_bound:
  \<open>3 \<le> top_m lbd m0 m\<close> \<open>m0 \<le> j \<Longrightarrow> j < m \<Longrightarrow> lbd ! (j - m0) < top_m lbd m0 m\<close>
  using top_loop_bound[of 3 lbd m0 m m0] by (auto simp: top_m_def)

lemma hist_loop_eq:
  assumes \<open>\<forall>j. c \<le> j \<and> j < m \<longrightarrow> lbd ! (j - m0) < length hist\<close>
  shows \<open>hist_loop locked lbd m0 m hist cand c =
    (map (\<lambda>b. hist ! b + length (filter (\<lambda>j. isc locked lbd m0 j \<and> lbd ! (j - m0) = b) [c..<m]))
       [0..<length hist],
     cand + length (filter (isc locked lbd m0) [c..<m]))\<close>
  using assms
proof (induction locked lbd m0 m hist cand c rule: hist_loop.induct)
  case (1 locked lbd m0 m hist cand c)
  show ?case
  proof (cases \<open>c < m\<close>)
    case True
    have u: \<open>[c..<m] = c # [c + 1..<m]\<close> using True upt_conv_Cons by simp
    have b: \<open>lbd ! (c - m0) < length hist\<close> using "1.prems" True by simp
    show ?thesis
    proof (cases \<open>isc locked lbd m0 c\<close>)
      case c: True
      have e: \<open>hist_loop locked lbd m0 m hist cand c =
          hist_loop locked lbd m0 m (hist[lbd ! (c - m0) := hist ! (lbd ! (c - m0)) + 1]) (cand + 1) (c + 1)\<close>
        using True c by (subst hist_loop.simps) (simp only: if_P[OF True] if_P[OF c[unfolded isc_def]] if_True)
      show ?thesis
        unfolding e using "1.IH"(1)[OF True c[unfolded isc_def]] "1.prems" c b
        by (auto simp: u nth_list_update intro!: nth_equalityI)
    next
      case n: False
      have e: \<open>hist_loop locked lbd m0 m hist cand c = hist_loop locked lbd m0 m hist cand (c + 1)\<close>
        using True n by (subst hist_loop.simps) (simp only: if_P[OF True] if_not_P[OF n[unfolded isc_def]] if_True)
      show ?thesis
        unfolding e using "1.IH"(2)[OF True n[unfolded isc_def]] "1.prems" n
        by (auto simp: u intro!: nth_equalityI)
    qed
  next
    case False
    then show ?thesis by (subst hist_loop.simps) (simp add: map_nth)
  qed
qed

lemma thr_loop_props:
  assumes \<open>acc \<le> quota\<close> \<open>t \<le> tb\<close> \<open>thr_loop hist tb quota t acc = (t', acc')\<close>
  shows \<open>acc' \<le> quota \<and> t \<le> t' \<and> t' \<le> tb \<and> acc' = acc + sum_list (map (nth hist) [t..<t']) \<and>
    (t' < tb \<longrightarrow> quota < acc' + hist ! t')\<close>
  using assms
proof (induction hist tb quota t acc rule: thr_loop.induct)
  case (1 hist tb quota t acc)
  show ?case
  proof (cases \<open>t < tb \<and> acc + hist ! t \<le> quota\<close>)
    case True
    have e: \<open>thr_loop hist tb quota t acc = thr_loop hist tb quota (t + 1) (acc + hist ! t)\<close>
      using True by (subst thr_loop.simps) simp
    have \<open>[t..<t'] = t # [t + 1..<t']\<close> if \<open>t + 1 \<le> t'\<close> using that upt_conv_Cons by simp
    then show ?thesis
      using "1.IH"[OF True _ _ "1.prems"(3)[unfolded e]] True by fastforce
  next
    case False
    then have \<open>t' = t\<close> \<open>acc' = acc\<close> using "1.prems"(3) by (subst (asm) thr_loop.simps; simp)+
    then show ?thesis using False "1.prems"(1,2) by auto
  qed
qed

text \<open>The backward loop only clears candidates of LBD at least \<open>t\<close> below \<open>c\<close>.\<close>
lemma keep_loop_kept:
  assumes \<open>keep_loop locked lbd m0 t keep left c = (keep', left')\<close>
  shows \<open>length keep' = length keep \<and>
    (\<forall>j. keep ! j \<and> (j < m0 \<or> c \<le> j \<or> \<not> (isc locked lbd m0 j \<and> t \<le> lbd ! (j - m0))) \<longrightarrow> keep' ! j)\<close>
  using assms
proof (induction locked lbd m0 t keep left c rule: keep_loop.induct)
  case (1 locked lbd m0 t keep left c)
  show ?case
  proof (cases \<open>m0 < c\<close>)
    case True
    define b where \<open>b = lbd ! (c - 1 - m0)\<close>
    have bc: \<open>b = lbd ! ((c - 1) - m0)\<close> by (simp add: b_def)
    show ?thesis
    proof (cases \<open>\<not> locked ! (c - 1) \<and> 2 < b \<and> t \<le> b\<close>)
      case cnd: True
      show ?thesis
      proof (cases \<open>b = t \<and> 0 < left\<close>)
        case dec: True
        have e: \<open>keep_loop locked lbd m0 t keep left c = keep_loop locked lbd m0 t keep (left - 1) (c - 1)\<close>
          by (subst keep_loop.simps) (simp only: Let_def b_def[symmetric] if_P[OF True] if_P[OF cnd] if_P[OF dec])
        show ?thesis using "1.IH"(1)[OF True b_def cnd dec "1.prems"[unfolded e]] by auto
      next
        case clr: False
        have e: \<open>keep_loop locked lbd m0 t keep left c =
            keep_loop locked lbd m0 t (keep[c - 1 := False]) left (c - 1)\<close>
          by (subst keep_loop.simps) (simp only: Let_def b_def[symmetric] if_P[OF True] if_P[OF cnd] if_not_P[OF clr])
        have u: \<open>keep[c - 1 := False] ! j\<close>
          if \<open>keep ! j\<close> \<open>j < m0 \<or> c \<le> j \<or> \<not> (isc locked lbd m0 j \<and> t \<le> lbd ! (j - m0))\<close> for j
        proof (cases \<open>j = c - 1\<close>)
          case True
          then show ?thesis using that(2) cnd \<open>m0 < c\<close> by (auto simp: isc_def b_def)
        qed (simp add: that(1))
        have ih: \<open>\<forall>j. keep[c - 1 := False] ! j \<and>
            (j < m0 \<or> c - 1 \<le> j \<or> \<not> (isc locked lbd m0 j \<and> t \<le> lbd ! (j - m0))) \<longrightarrow> keep' ! j\<close>
          \<open>length keep' = length keep\<close>
          using "1.IH"(2)[OF True b_def cnd clr "1.prems"[unfolded e]] by simp_all
        show ?thesis
        proof (intro conjI allI impI)
          show \<open>length keep' = length keep\<close> using ih(2) .
          fix j assume j: \<open>keep ! j \<and> (j < m0 \<or> c \<le> j \<or> \<not> (isc locked lbd m0 j \<and> t \<le> lbd ! (j - m0)))\<close>
          then have \<open>j < m0 \<or> c - 1 \<le> j \<or> \<not> (isc locked lbd m0 j \<and> t \<le> lbd ! (j - m0))\<close> by auto
          then show \<open>keep' ! j\<close> using ih(1) u j by blast
        qed
      qed
    next
      case ncnd: False
      have e: \<open>keep_loop locked lbd m0 t keep left c = keep_loop locked lbd m0 t keep left (c - 1)\<close>
        by (subst keep_loop.simps) (simp only: Let_def b_def[symmetric] if_P[OF True] if_not_P[OF ncnd])
      show ?thesis using "1.IH"(3)[OF True b_def ncnd "1.prems"[unfolded e]] by auto
    qed
  next
    case False
    then show ?thesis using "1.prems" by (subst (asm) keep_loop.simps) auto
  qed
qed

text \<open>Of the candidates of LBD \<open>t\<close> below \<open>c\<close>, the backward loop keeps \<open>left\<close>, or all if there
  are fewer.\<close>
lemma keep_loop_count:
  assumes \<open>keep_loop locked lbd m0 t keep left c = (keep', left')\<close> \<open>c \<le> length keep\<close>
    \<open>\<forall>j. m0 \<le> j \<and> j < c \<longrightarrow> keep ! j\<close>
  shows \<open>min left (length (filter (\<lambda>j. isc locked lbd m0 j \<and> lbd ! (j - m0) = t) [m0..<c])) \<le>
    length (filter (\<lambda>j. isc locked lbd m0 j \<and> lbd ! (j - m0) = t \<and> keep' ! j) [m0..<c])\<close>
  using assms
proof (induction locked lbd m0 t keep left c rule: keep_loop.induct)
  case (1 locked lbd m0 t keep left c)
  show ?case
  proof (cases \<open>m0 < c\<close>)
    case True
    let ?P = \<open>\<lambda>j. isc locked lbd m0 j \<and> lbd ! (j - m0) = t\<close>
    let ?Q = \<open>\<lambda>j. isc locked lbd m0 j \<and> lbd ! (j - m0) = t \<and> keep' ! j\<close>
    define b where \<open>b = lbd ! (c - 1 - m0)\<close>
    have u: \<open>[m0..<c] = [m0..<c - 1] @ [c - 1]\<close> using True upt_Suc_append[of m0 \<open>c - 1\<close>] by simp
    have p: \<open>c - 1 \<le> length keep\<close> \<open>\<forall>j. m0 \<le> j \<and> j < c - 1 \<longrightarrow> keep ! j\<close>
      \<open>c - 1 \<le> length (keep[c - 1 := False])\<close> \<open>\<forall>j. m0 \<le> j \<and> j < c - 1 \<longrightarrow> keep[c - 1 := False] ! j\<close>
      using "1.prems"(2,3) by auto
    show ?thesis
    proof (cases \<open>\<not> locked ! (c - 1) \<and> 2 < b \<and> t \<le> b\<close>)
      case cnd: True
      show ?thesis
      proof (cases \<open>b = t \<and> 0 < left\<close>)
        case dec: True
        have e: \<open>keep_loop locked lbd m0 t keep left c = keep_loop locked lbd m0 t keep (left - 1) (c - 1)\<close>
          by (subst keep_loop.simps) (simp only: Let_def b_def[symmetric] if_P[OF True] if_P[OF cnd] if_P[OF dec])
        have k: \<open>keep' ! (c - 1)\<close>
          using keep_loop_kept[OF "1.prems"(1)[unfolded e]] "1.prems"(3) True by auto
        have ih: \<open>min (left - 1) (length (filter ?P [m0..<c - 1])) \<le> length (filter ?Q [m0..<c - 1])\<close>
          using "1.IH"(1)[OF True b_def cnd dec "1.prems"(1)[unfolded e] p(1,2)] by simp
        have \<open>?P (c - 1)\<close> \<open>?Q (c - 1)\<close> using cnd dec k by (simp_all add: isc_def b_def)
        then have l: \<open>length (filter ?P [m0..<c]) = Suc (length (filter ?P [m0..<c - 1]))\<close>
          \<open>length (filter ?Q [m0..<c]) = Suc (length (filter ?Q [m0..<c - 1]))\<close>
          by (simp_all add: u)
        show ?thesis unfolding l using ih dec by (auto simp: min_def split: if_split_asm) linarith
      next
        case clr: False
        have e: \<open>keep_loop locked lbd m0 t keep left c =
            keep_loop locked lbd m0 t (keep[c - 1 := False]) left (c - 1)\<close>
          by (subst keep_loop.simps) (simp only: Let_def b_def[symmetric] if_P[OF True] if_P[OF cnd] if_not_P[OF clr])
        have ih: \<open>min left (length (filter ?P [m0..<c - 1])) \<le> length (filter ?Q [m0..<c - 1])\<close>
          using "1.IH"(2)[OF True b_def cnd clr "1.prems"(1)[unfolded e] p(3,4)] by simp
        show ?thesis
        proof (cases \<open>b = t\<close>)
          case True
          then have \<open>left = 0\<close> using clr by simp
          then show ?thesis by simp
        next
          case False
          then have \<open>\<not> ?P (c - 1)\<close> by (simp add: b_def)
          then show ?thesis using ih by (auto simp: u)
        qed
      qed
    next
      case ncnd: False
      have e: \<open>keep_loop locked lbd m0 t keep left c = keep_loop locked lbd m0 t keep left (c - 1)\<close>
        by (subst keep_loop.simps) (simp only: Let_def b_def[symmetric] if_P[OF True] if_not_P[OF ncnd])
      have ih: \<open>min left (length (filter ?P [m0..<c - 1])) \<le> length (filter ?Q [m0..<c - 1])\<close>
        using "1.IH"(3)[OF True b_def ncnd "1.prems"(1)[unfolded e] p(1,2)] by simp
      have \<open>\<not> ?P (c - 1)\<close> using ncnd by (auto simp: isc_def b_def)
      then show ?thesis using ih by (auto simp: u)
    qed
  next
    case False
    then show ?thesis by simp
  qed
qed

end
