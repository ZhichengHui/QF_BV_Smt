theory QFBV_ReduceTier
  imports QFBV_ReduceCompact QFBV_ReduceLbd
begin

section \<open>Learned-clause deletion: the middle tier\<close>

text \<open>The tier-2 retention of the prototype commit \<^verbatim>\<open>a49260e\<close> (branch
  \<^verbatim>\<open>agent/17f61c03-tier\<close>, CaDiCaL's middle tier): \<^verbatim>\<open>reduce_db\<close> also keeps the learned clauses
  of LBD at most \<^verbatim>\<open>TIER2\<close> (6 there; a parameter \<open>T\<close> here) whose flag \<^verbatim>\<open>uf[c - m0]\<close> is set,
  and the flags \<^verbatim>\<open>uflag\<close> of \<^verbatim>\<open>dpll\<close>. Only the two candidate tests of \<^verbatim>\<open>reduce_db\<close> change,
  each by the conjunct \<^verbatim>\<open>!(lbd[c - m0] <= TIER2 && uf[c - m0])\<close>; \<open>hist2_loop\<close> and \<open>keep2_loop\<close>
  are \<open>hist_loop\<close> and \<open>keep_loop\<close> with it. Of the compaction, only \<^verbatim>\<open>uf2.push(false)\<close> is new:
  \<open>uf2_loop\<close> models it as a loop of its own beside \<open>compact_loop\<close> (the two loops have the same
  bounds and tests, and \<^verbatim>\<open>uf2\<close> is not read in the loop). The statements of
  \<open>QFBV_Reduce\<close> and \<open>QFBV_ReduceCompact\<close> are reused, not changed: a flagged clause of LBD at most
  \<open>T\<close> is a candidate of neither loop, as a locked one; so the tier-2 selection is the selection
  of \<open>sel_m\<close> with these clauses added to the reasons (\<open>sel2_m_sel_m\<close>).\<close>

subsection \<open>Selection\<close>

text \<open>A candidate for deletion: an unlocked learned clause of LBD above 2 that is not flagged with
  LBD at most \<open>T\<close>.\<close>
definition isc2 :: \<open>nat \<Rightarrow> bool list \<Rightarrow> nat list \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>isc2 T locked lbd uf m0 c \<longleftrightarrow>
    \<not> locked ! c \<and> 2 < lbd ! (c - m0) \<and> \<not> (lbd ! (c - m0) \<le> T \<and> uf ! (c - m0))\<close>

text \<open>The loop of \<^verbatim>\<open>hist\<close>: \<^verbatim>\<open>if !locked[c] && lbd[c - m0] > 2 && !(lbd[c - m0] <= TIER2 && uf[c - m0])\<close>
  \<^verbatim>\<open>{ hist[lbd[c - m0]] += 1; cand += 1; } c += 1\<close>.\<close>
function hist2_loop :: \<open>nat \<Rightarrow> bool list \<Rightarrow> nat list \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    nat list \<times> nat\<close> where
  \<open>hist2_loop T locked lbd uf m0 m hist cand c =
    (if c < m then
       (if \<not> locked ! c \<and> 2 < lbd ! (c - m0) \<and> \<not> (lbd ! (c - m0) \<le> T \<and> uf ! (c - m0)) then
          hist2_loop T locked lbd uf m0 m (hist[lbd ! (c - m0) := hist ! (lbd ! (c - m0)) + 1]) (cand + 1) (c + 1)
        else hist2_loop T locked lbd uf m0 m hist cand (c + 1))
     else (hist, cand))\<close>
  by pat_completeness auto
termination
  by (relation \<open>measure (\<lambda>(_, _, _, _, _, m, _, _, c). m - c)\<close>) auto

declare hist2_loop.simps [simp del]

text \<open>The backward loop of \<^verbatim>\<open>keep\<close>: \<^verbatim>\<open>c -= 1; let b = lbd[c - m0];\<close>
  \<^verbatim>\<open>if !locked[c] && b > 2 && b >= t && !(b <= TIER2 && uf[c - m0])\<close>
  \<^verbatim>\<open>{ if b == t && left > 0 { left -= 1; } else { keep[c] = false; } }\<close>, while \<open>c > m0\<close>.\<close>
function keep2_loop :: \<open>nat \<Rightarrow> bool list \<Rightarrow> nat list \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    bool list \<times> nat\<close> where
  \<open>keep2_loop T locked lbd uf m0 t keep left c =
    (if m0 < c then
       (let b = lbd ! (c - 1 - m0) in
        if \<not> locked ! (c - 1) \<and> 2 < b \<and> t \<le> b \<and> \<not> (b \<le> T \<and> uf ! (c - 1 - m0)) then
          (if b = t \<and> 0 < left then keep2_loop T locked lbd uf m0 t keep (left - 1) (c - 1)
           else keep2_loop T locked lbd uf m0 t (keep[c - 1 := False]) left (c - 1))
        else keep2_loop T locked lbd uf m0 t keep left (c - 1))
     else (keep, left))\<close>
  by pat_completeness auto
termination
  by (relation \<open>measure (\<lambda>(_, _, _, _, _, _, _, _, c). c)\<close>) auto

declare keep2_loop.simps [simp del]

text \<open>The selection of \<^verbatim>\<open>reduce_db\<close> of \<^verbatim>\<open>a49260e\<close>, up to the \<^verbatim>\<open>keep\<close> mask; \<^verbatim>\<open>locked\<close>,
  \<^verbatim>\<open>top\<close> and the threshold are unchanged.\<close>
definition sel2_m :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow>
    bool list \<times> nat \<times> nat list \<times> nat \<times> nat \<times> nat \<times> nat \<times> bool list\<close> where
  \<open>sel2_m T m lbd uf rs m0 =
    (let locked = locked_m rs m; tb = top_m lbd m0 m in
     case hist2_loop T locked lbd uf m0 m (replicate tb 0) 0 m0 of (hist, cand) \<Rightarrow>
     (let quota = cand div 2 in
      case thr_loop hist tb quota 3 0 of (t, acc) \<Rightarrow>
      (case keep2_loop T locked lbd uf m0 t (replicate m True) (quota - acc) m of (keep, _) \<Rightarrow>
       (locked, tb, hist, cand, quota, t, acc, keep))))\<close>

definition keep2_m :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool list\<close> where
  \<open>keep2_m T m lbd uf rs m0 = (case sel2_m T m lbd uf rs m0 of (_, _, _, _, _, _, _, keep) \<Rightarrow> keep)\<close>

subsubsection \<open>Reduction to \<^const>\<open>sel_m\<close>\<close>

text \<open>The flagged learned clauses of LBD at most \<open>T\<close>.\<close>
definition tier_rs :: \<open>nat \<Rightarrow> nat list \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list\<close> where
  \<open>tier_rs T lbd uf m0 m = filter (\<lambda>c. lbd ! (c - m0) \<le> T \<and> uf ! (c - m0)) [m0..<m]\<close>

lemma hist2_loop_eq:
  assumes \<open>\<forall>j. c \<le> j \<and> j < m \<longrightarrow> (locked' ! j \<longleftrightarrow> locked ! j \<or> (lbd ! (j - m0) \<le> T \<and> uf ! (j - m0)))\<close>
  shows \<open>hist2_loop T locked lbd uf m0 m hist cand c = hist_loop locked' lbd m0 m hist cand c\<close>
  using assms
proof (induction T locked lbd uf m0 m hist cand c rule: hist2_loop.induct)
  case (1 T locked lbd uf m0 m hist cand c)
  show ?case
  proof (cases \<open>c < m\<close>)
    case True
    have p: \<open>\<forall>j. c + 1 \<le> j \<and> j < m \<longrightarrow> (locked' ! j \<longleftrightarrow> locked ! j \<or> (lbd ! (j - m0) \<le> T \<and> uf ! (j - m0)))\<close>
      using "1.prems" by auto
    have iff: \<open>(\<not> locked ! c \<and> 2 < lbd ! (c - m0) \<and> \<not> (lbd ! (c - m0) \<le> T \<and> uf ! (c - m0))) \<longleftrightarrow>
        (\<not> locked' ! c \<and> 2 < lbd ! (c - m0))\<close>
      using "1.prems" True by auto
    show ?thesis
    proof (cases \<open>\<not> locked ! c \<and> 2 < lbd ! (c - m0) \<and> \<not> (lbd ! (c - m0) \<le> T \<and> uf ! (c - m0))\<close>)
      case y: True
      have y': \<open>\<not> locked' ! c \<and> 2 < lbd ! (c - m0)\<close> using y iff by blast
      have \<open>hist2_loop T locked lbd uf m0 m hist cand c =
          hist2_loop T locked lbd uf m0 m (hist[lbd ! (c - m0) := hist ! (lbd ! (c - m0)) + 1]) (cand + 1) (c + 1)\<close>
        by (subst hist2_loop.simps) (simp only: if_P[OF True] if_P[OF y])
      moreover have \<open>hist_loop locked' lbd m0 m hist cand c =
          hist_loop locked' lbd m0 m (hist[lbd ! (c - m0) := hist ! (lbd ! (c - m0)) + 1]) (cand + 1) (c + 1)\<close>
        by (subst hist_loop.simps) (simp only: if_P[OF True] if_P[OF y'])
      ultimately show ?thesis using "1.IH"(1)[OF True y p] by simp
    next
      case n: False
      have n': \<open>\<not> (\<not> locked' ! c \<and> 2 < lbd ! (c - m0))\<close> using n iff by blast
      have \<open>hist2_loop T locked lbd uf m0 m hist cand c = hist2_loop T locked lbd uf m0 m hist cand (c + 1)\<close>
        by (subst hist2_loop.simps) (simp only: if_P[OF True] if_not_P[OF n])
      moreover have \<open>hist_loop locked' lbd m0 m hist cand c = hist_loop locked' lbd m0 m hist cand (c + 1)\<close>
        by (subst hist_loop.simps) (simp only: if_P[OF True] if_not_P[OF n'])
      ultimately show ?thesis using "1.IH"(2)[OF True n p] by simp
    qed
  next
    case False
    then show ?thesis by (subst hist2_loop.simps, subst hist_loop.simps) simp
  qed
qed

lemma keep2_loop_eq:
  assumes \<open>\<forall>j. m0 \<le> j \<and> j < c \<longrightarrow> (locked' ! j \<longleftrightarrow> locked ! j \<or> (lbd ! (j - m0) \<le> T \<and> uf ! (j - m0)))\<close>
  shows \<open>keep2_loop T locked lbd uf m0 t keep left c = keep_loop locked' lbd m0 t keep left c\<close>
  using assms
proof (induction T locked lbd uf m0 t keep left c rule: keep2_loop.induct)
  case (1 T locked lbd uf m0 t keep left c)
  show ?case
  proof (cases \<open>m0 < c\<close>)
    case True
    define b where \<open>b = lbd ! (c - 1 - m0)\<close>
    have p: \<open>\<forall>j. m0 \<le> j \<and> j < c - 1 \<longrightarrow> (locked' ! j \<longleftrightarrow> locked ! j \<or> (lbd ! (j - m0) \<le> T \<and> uf ! (j - m0)))\<close>
      using "1.prems" by auto
    have iff: \<open>(\<not> locked ! (c - 1) \<and> 2 < b \<and> t \<le> b \<and> \<not> (b \<le> T \<and> uf ! (c - 1 - m0))) \<longleftrightarrow>
        (\<not> locked' ! (c - 1) \<and> 2 < b \<and> t \<le> b)\<close>
      using "1.prems" True by (auto simp: b_def)
    show ?thesis
    proof (cases \<open>\<not> locked ! (c - 1) \<and> 2 < b \<and> t \<le> b \<and> \<not> (b \<le> T \<and> uf ! (c - 1 - m0))\<close>)
      case cnd: True
      have cnd': \<open>\<not> locked' ! (c - 1) \<and> 2 < b \<and> t \<le> b\<close> using cnd iff by blast
      show ?thesis
      proof (cases \<open>b = t \<and> 0 < left\<close>)
        case dec: True
        have \<open>keep2_loop T locked lbd uf m0 t keep left c = keep2_loop T locked lbd uf m0 t keep (left - 1) (c - 1)\<close>
          by (subst keep2_loop.simps) (simp only: Let_def b_def[symmetric] if_P[OF True] if_P[OF cnd] if_P[OF dec])
        moreover have \<open>keep_loop locked' lbd m0 t keep left c = keep_loop locked' lbd m0 t keep (left - 1) (c - 1)\<close>
          by (subst keep_loop.simps) (simp only: Let_def b_def[symmetric] if_P[OF True] if_P[OF cnd'] if_P[OF dec])
        ultimately show ?thesis using "1.IH"(1)[OF True b_def cnd dec p] by simp
      next
        case clr: False
        have \<open>keep2_loop T locked lbd uf m0 t keep left c =
            keep2_loop T locked lbd uf m0 t (keep[c - 1 := False]) left (c - 1)\<close>
          by (subst keep2_loop.simps) (simp only: Let_def b_def[symmetric] if_P[OF True] if_P[OF cnd] if_not_P[OF clr])
        moreover have \<open>keep_loop locked' lbd m0 t keep left c = keep_loop locked' lbd m0 t (keep[c - 1 := False]) left (c - 1)\<close>
          by (subst keep_loop.simps) (simp only: Let_def b_def[symmetric] if_P[OF True] if_P[OF cnd'] if_not_P[OF clr])
        ultimately show ?thesis using "1.IH"(2)[OF True b_def cnd clr p] by simp
      qed
    next
      case ncnd: False
      have ncnd': \<open>\<not> (\<not> locked' ! (c - 1) \<and> 2 < b \<and> t \<le> b)\<close> using ncnd iff by blast
      have \<open>keep2_loop T locked lbd uf m0 t keep left c = keep2_loop T locked lbd uf m0 t keep left (c - 1)\<close>
        by (subst keep2_loop.simps) (simp only: Let_def b_def[symmetric] if_P[OF True] if_not_P[OF ncnd])
      moreover have \<open>keep_loop locked' lbd m0 t keep left c = keep_loop locked' lbd m0 t keep left (c - 1)\<close>
        by (subst keep_loop.simps) (simp only: Let_def b_def[symmetric] if_P[OF True] if_not_P[OF ncnd'])
      ultimately show ?thesis using "1.IH"(3)[OF True b_def ncnd p] by simp
    qed
  next
    case False
    then show ?thesis by (subst keep2_loop.simps, subst keep_loop.simps) simp
  qed
qed

lemma locked_tier:
  \<open>\<forall>j. m0 \<le> j \<and> j < m \<longrightarrow> (locked_m (rs @ tier_rs T lbd uf m0 m) m ! j \<longleftrightarrow>
    locked_m rs m ! j \<or> (lbd ! (j - m0) \<le> T \<and> uf ! (j - m0)))\<close>
  by (auto simp: locked_m_props tier_rs_def)

lemma isc_tier:
  \<open>m0 \<le> j \<Longrightarrow> j < m \<Longrightarrow>
    isc (locked_m (rs @ tier_rs T lbd uf m0 m) m) lbd m0 j \<longleftrightarrow> isc2 T (locked_m rs m) lbd uf m0 j\<close>
  using locked_tier[of m0 m rs T lbd uf] by (auto simp: isc_def isc2_def)

text \<open>The tier-2 selection is the selection of \<^const>\<open>sel_m\<close> with the flagged clauses of LBD at
  most \<open>T\<close> as further reasons, but for the returned \<^verbatim>\<open>locked\<close>.\<close>
lemma sel2_m_sel_m:
  \<open>sel2_m T m lbd uf rs m0 =
    (case sel_m m lbd (rs @ tier_rs T lbd uf m0 m) m0 of (_, r) \<Rightarrow> (locked_m rs m, r))\<close>
  by (simp add: sel2_m_def sel_m_def Let_def hist2_loop_eq[OF locked_tier] keep2_loop_eq[OF locked_tier]
      split: prod.split)

subsubsection \<open>The facts of the selection\<close>

text \<open>As \<open>sel_m_props\<close> and \<open>sel_m_hist\<close>: \<open>acc \<le> quota\<close>; the original clauses, the reasons, the
  clauses of LBD at most 2 and the flagged ones of LBD at most \<open>T\<close> are kept; at least \<open>quota\<close>
  of the \<open>cand\<close> candidates are kept; and \<open>hist ! b \<le> cand \<le> m - m0\<close>.\<close>
lemma sel2_m_props:
  assumes \<open>sel2_m T m lbd uf rs m0 = (locked, tb, hist, cand, quota, t, acc, keep)\<close>
  shows \<open>length locked = m\<close> \<open>\<forall>c < m. locked ! c \<longleftrightarrow> c \<in> set rs\<close>
    \<open>3 \<le> tb\<close> \<open>\<forall>j. m0 \<le> j \<and> j < m \<longrightarrow> lbd ! (j - m0) < tb\<close> \<open>length hist = tb\<close>
    \<open>cand = length (filter (isc2 T locked lbd uf m0) [m0..<m])\<close> \<open>quota = cand div 2\<close>
    \<open>acc \<le> quota\<close> \<open>3 \<le> t\<close> \<open>t \<le> tb\<close> \<open>length keep = m\<close>
    \<open>\<forall>c < m. c < m0 \<or> c \<in> set rs \<or> lbd ! (c - m0) \<le> 2 \<or> (lbd ! (c - m0) \<le> T \<and> uf ! (c - m0)) \<longrightarrow> keep ! c\<close>
    \<open>quota \<le> length (filter (\<lambda>c. isc2 T locked lbd uf m0 c \<and> keep ! c) [m0..<m])\<close>
    \<open>\<forall>b < tb. hist ! b \<le> cand\<close> \<open>cand \<le> m - m0\<close>
proof -
  let ?rs' = \<open>rs @ tier_rs T lbd uf m0 m\<close>
  have \<open>\<exists>x. sel_m m lbd ?rs' m0 = (x, tb, hist, cand, quota, t, acc, keep) \<and> locked = locked_m rs m\<close>
    using assms by (auto simp: sel2_m_sel_m split: prod.splits)
  then obtain x where sr: \<open>sel_m m lbd ?rs' m0 = (x, tb, hist, cand, quota, t, acc, keep)\<close>
    and lk: \<open>locked = locked_m rs m\<close> by blast
  note p = sel_m_props[OF sr] and hh = sel_m_hist[OF sr]
  have ic: \<open>isc x lbd m0 j \<longleftrightarrow> isc2 T locked lbd uf m0 j\<close> if \<open>j \<in> set [m0..<m]\<close> for j
    using that p(2) locked_m_props(2)[of j m rs] lk by (auto simp: isc_def isc2_def tier_rs_def)
  have fc: \<open>filter (isc x lbd m0) [m0..<m] = filter (isc2 T locked lbd uf m0) [m0..<m]\<close>
    \<open>filter (\<lambda>c. isc x lbd m0 c \<and> keep ! c) [m0..<m] = filter (\<lambda>c. isc2 T locked lbd uf m0 c \<and> keep ! c) [m0..<m]\<close>
    using ic by (auto intro: filter_cong)
  show \<open>length locked = m\<close> \<open>\<forall>c < m. locked ! c \<longleftrightarrow> c \<in> set rs\<close> using lk locked_m_props by auto
  show \<open>3 \<le> tb\<close> \<open>\<forall>j. m0 \<le> j \<and> j < m \<longrightarrow> lbd ! (j - m0) < tb\<close> \<open>length hist = tb\<close>
    \<open>cand = length (filter (isc2 T locked lbd uf m0) [m0..<m])\<close> \<open>quota = cand div 2\<close>
    \<open>acc \<le> quota\<close> \<open>3 \<le> t\<close> \<open>t \<le> tb\<close> \<open>length keep = m\<close>
    \<open>quota \<le> length (filter (\<lambda>c. isc2 T locked lbd uf m0 c \<and> keep ! c) [m0..<m])\<close>
    \<open>\<forall>b < tb. hist ! b \<le> cand\<close> \<open>cand \<le> m - m0\<close>
    using p hh fc by simp_all
  show \<open>\<forall>c < m. c < m0 \<or> c \<in> set rs \<or> lbd ! (c - m0) \<le> 2 \<or> (lbd ! (c - m0) \<le> T \<and> uf ! (c - m0)) \<longrightarrow> keep ! c\<close>
    using p(12) by (auto simp: tier_rs_def not_less)
qed

lemma keep2_m_props:
  \<open>length (keep2_m T m lbd uf rs m0) = m\<close>
  \<open>c < m \<Longrightarrow> c < m0 \<or> c \<in> set rs \<or> lbd ! (c - m0) \<le> 2 \<or> (lbd ! (c - m0) \<le> T \<and> uf ! (c - m0)) \<Longrightarrow>
    keep2_m T m lbd uf rs m0 ! c\<close>
proof -
  obtain locked tb hist cand quota t acc keep
    where s: \<open>sel2_m T m lbd uf rs m0 = (locked, tb, hist, cand, quota, t, acc, keep)\<close>
    by (cases \<open>sel2_m T m lbd uf rs m0\<close>) auto
  have \<open>keep2_m T m lbd uf rs m0 = keep\<close> using s by (simp add: keep2_m_def)
  then show \<open>length (keep2_m T m lbd uf rs m0) = m\<close>
    \<open>c < m \<Longrightarrow> c < m0 \<or> c \<in> set rs \<or> lbd ! (c - m0) \<le> 2 \<or> (lbd ! (c - m0) \<le> T \<and> uf ! (c - m0)) \<Longrightarrow>
      keep2_m T m lbd uf rs m0 ! c\<close>
    using sel2_m_props[OF s] by auto
qed

subsection \<open>The flags \<^verbatim>\<open>uflag\<close>\<close>

text \<open>\<^verbatim>\<open>uf2.push(false)\<close> in the compaction, in the branch \<^verbatim>\<open>if keep[c] { .. if c >= m0 { .. } }\<close>
  of the forward loop (\<^verbatim>\<open>while c < m\<close>, from \<^verbatim>\<open>c = 0\<close>).\<close>
function uf2_loop :: \<open>bool list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> bool list\<close> where
  \<open>uf2_loop keep m0 m uf2 c =
    (if c < m then uf2_loop keep m0 m (if keep ! c \<and> m0 \<le> c then uf2 @ [False] else uf2) (c + 1)
     else uf2)\<close>
  by pat_completeness auto
termination
  by (relation \<open>measure (\<lambda>(_, _, m, _, c). m - c)\<close>) auto

declare uf2_loop.simps [simp del]

lemma uf2_loop_eq:
  \<open>uf2_loop keep m0 m uf2 c = uf2 @ replicate (length (filter (\<lambda>j. m0 \<le> j) (filter (nth keep) [c..<m]))) False\<close>
proof (induction keep m0 m uf2 c rule: uf2_loop.induct)
  case (1 keep m0 m uf2 c)
  show ?case
  proof (cases \<open>c < m\<close>)
    case True
    have \<open>uf2_loop keep m0 m uf2 c = uf2_loop keep m0 m (if keep ! c \<and> m0 \<le> c then uf2 @ [False] else uf2) (c + 1)\<close>
      using True by (subst uf2_loop.simps) simp
    then show ?thesis using "1.IH"[OF True] True by (simp add: upt_conv_Cons replicate_append_same)
  next
    case False
    then show ?thesis by (subst uf2_loop.simps) simp
  qed
qed

text \<open>The flags set after an analysis:
  \<^verbatim>\<open>if u1[k] >= m0 && u1[k] - m0 < uflag.len() { uflag[u1[k] - m0] = true; } k += 1\<close>, while
  \<^verbatim>\<open>k < u1.len()\<close>, from \<^verbatim>\<open>k = 0\<close>.\<close>
function flag_loop :: \<open>nat list \<Rightarrow> nat \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> bool list\<close> where
  \<open>flag_loop used m0 uf k =
    (if k < length used then
       flag_loop used m0 (if m0 \<le> used ! k \<and> used ! k - m0 < length uf then uf[used ! k - m0 := True] else uf) (k + 1)
     else uf)\<close>
  by pat_completeness auto
termination
  by (relation \<open>measure (\<lambda>(used, _, _, k). length used - k)\<close>) auto

declare flag_loop.simps [simp del]

lemma flag_loop_eq:
  \<open>length (flag_loop used m0 uf k) = length uf \<and>
    (\<forall>i < length uf. flag_loop used m0 uf k ! i \<longleftrightarrow> uf ! i \<or> m0 + i \<in> set (drop k used))\<close>
proof (induction used m0 uf k rule: flag_loop.induct)
  case (1 used m0 uf k)
  show ?case
  proof (cases \<open>k < length used\<close>)
    case True
    have d: \<open>drop k used = used ! k # drop (k + 1) used\<close> using True by (simp add: Cons_nth_drop_Suc)
    have \<open>flag_loop used m0 uf k =
        flag_loop used m0 (if m0 \<le> used ! k \<and> used ! k - m0 < length uf then uf[used ! k - m0 := True] else uf) (k + 1)\<close>
      using True by (subst flag_loop.simps) simp
    then show ?thesis using "1.IH"[OF True] d by (auto simp: nth_list_update)
  next
    case False
    then show ?thesis by (subst flag_loop.simps; simp)+
  qed
qed

text \<open>\<^verbatim>\<open>reduce_db\<close> of \<^verbatim>\<open>a49260e\<close> without the watch lists: the new clauses, LBDs, flags,
  reasons and watched positions, and the mask and the map.\<close>
definition reduce2_m :: \<open>nat \<Rightarrow> 'c list \<Rightarrow> nat list \<Rightarrow> bool list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow>
    'c list \<times> nat list \<times> bool list \<times> nat list \<times> nat list \<times> bool list \<times> nat list\<close> where
  \<open>reduce2_m T db lbd uf pos rs m0 =
    (let keep = keep2_m T (length db) lbd uf rs m0 in
     case compact_m keep db lbd pos m0 of (mp, db2, lbd2, pos2) \<Rightarrow>
       (db2, lbd2, uf2_loop keep m0 (length db) [] 0, renum_loop mp (length db) rs 0, pos2, keep, mp))\<close>

text \<open>The facts of the reduction, for \<open>m0 \<le> length db\<close>: the kept clauses (the original ones,
  the reasons, those of LBD at most 2 and the flagged ones of LBD at most \<open>T\<close>) keep their
  clause, LBD and watched positions at index \<open>mp ! c\<close>; \<open>db2\<close> is a sub-list of \<open>db\<close> with the same
  original prefix; the reasons are renumbered; and the flags have one entry, cleared, per kept
  learned clause, so \<open>length uf2 = length lbd2\<close>.\<close>
lemma reduce2_m_props:
  assumes \<open>reduce2_m T db lbd uf pos rs m0 = (db2, lbd2, uf2, rs2, pos2, keep, mp)\<close> \<open>m0 \<le> length db\<close>
  shows \<open>keep = keep2_m T (length db) lbd uf rs m0\<close> \<open>length keep = length db\<close>
    \<open>\<forall>c < length db. c < m0 \<or> c \<in> set rs \<or> lbd ! (c - m0) \<le> 2 \<or> (lbd ! (c - m0) \<le> T \<and> uf ! (c - m0)) \<longrightarrow>
      keep ! c\<close>
    \<open>db2 = map (nth db) (filter (nth keep) [0..<length db])\<close> \<open>subseq db2 db\<close>
    \<open>take m0 db2 = take m0 db\<close> \<open>m0 \<le> length db2\<close>
    \<open>length lbd2 = length db2 - m0\<close> \<open>length pos2 = 2 * length db2\<close>
    \<open>length uf2 = length lbd2\<close> \<open>\<forall>x \<in> set uf2. \<not> x\<close>
    \<open>c < length db \<Longrightarrow> keep ! c \<Longrightarrow> mp ! c < length db2 \<and> db2 ! (mp ! c) = db ! c \<and>
      (\<forall>i < 2. pos2 ! (2 * mp ! c + i) = pos ! (2 * c + i))\<close>
    \<open>m0 \<le> c \<Longrightarrow> c < length db \<Longrightarrow> keep ! c \<Longrightarrow> m0 \<le> mp ! c \<and> lbd2 ! (mp ! c - m0) = lbd ! (c - m0)\<close>
    \<open>length rs2 = length rs\<close>
    \<open>j < length rs \<Longrightarrow> rs ! j < length db \<Longrightarrow> rs2 ! j = mp ! (rs ! j) \<and> rs2 ! j < length db2 \<and>
      db2 ! (rs2 ! j) = db ! (rs ! j)\<close>
proof -
  let ?m = \<open>length db\<close>
  have k: \<open>keep = keep2_m T ?m lbd uf rs m0\<close> and c: \<open>compact_m keep db lbd pos m0 = (mp, db2, lbd2, pos2)\<close>
    and u: \<open>uf2 = uf2_loop keep m0 ?m [] 0\<close> and rs2: \<open>rs2 = renum_loop mp ?m rs 0\<close>
    using assms(1) by (auto simp: reduce2_m_def Let_def split: prod.splits)
  show \<open>keep = keep2_m T ?m lbd uf rs m0\<close> by (rule k)
  show lk: \<open>length keep = ?m\<close> using keep2_m_props(1) k by simp
  show kept: \<open>\<forall>c < ?m. c < m0 \<or> c \<in> set rs \<or> lbd ! (c - m0) \<le> 2 \<or> (lbd ! (c - m0) \<le> T \<and> uf ! (c - m0)) \<longrightarrow>
      keep ! c\<close>
    using keep2_m_props(2) k by simp
  have k0: \<open>\<forall>c < m0. keep ! c\<close> using kept assms(2) by simp
  note cp = compact_m_props[OF c lk]
  show \<open>db2 = map (nth db) (filter (nth keep) [0..<?m])\<close> \<open>subseq db2 db\<close> using cp by simp_all
  show t: \<open>take m0 db2 = take m0 db\<close> using cp(9)[OF assms(2) k0] .
  then show \<open>m0 \<le> length db2\<close> using assms(2) by (metis length_take min.absorb2 min.bounded_iff nat_le_linear)
  show \<open>length lbd2 = length db2 - m0\<close> \<open>length pos2 = 2 * length db2\<close>
    using cp(4) cp(10)[OF assms(2) k0] by simp_all
  have l2: \<open>lbd2 = map (\<lambda>j. lbd ! (j - m0)) (filter (\<lambda>j. m0 \<le> j) (filter (nth keep) [0..<?m]))\<close>
    using compact_loop_eq[OF _ c[unfolded compact_m_def], simplified] by simp
  show \<open>length uf2 = length lbd2\<close> \<open>\<forall>x \<in> set uf2. \<not> x\<close> using l2 u uf2_loop_eq by simp_all
  show kc: \<open>mp ! c < length db2 \<and> db2 ! (mp ! c) = db ! c \<and> (\<forall>i < 2. pos2 ! (2 * mp ! c + i) = pos ! (2 * c + i))\<close>
    if \<open>c < ?m\<close> \<open>keep ! c\<close> for c
    using cp(5-7) that by simp
  show \<open>m0 \<le> c \<Longrightarrow> c < ?m \<Longrightarrow> keep ! c \<Longrightarrow> m0 \<le> mp ! c \<and> lbd2 ! (mp ! c - m0) = lbd ! (c - m0)\<close>
    using cp(8)[OF k0] by simp
  note rn = renum_loop_nth[of mp ?m rs 0, folded rs2]
  show \<open>length rs2 = length rs\<close> using rn by simp
  show \<open>rs2 ! j = mp ! (rs ! j) \<and> rs2 ! j < length db2 \<and> db2 ! (rs2 ! j) = db ! (rs ! j)\<close>
    if \<open>j < length rs\<close> \<open>rs ! j < ?m\<close> for j
  proof -
    have \<open>keep ! (rs ! j)\<close> using kept that by simp
    then show ?thesis using kc[OF that(2)] rn that by simp
  qed
qed

subsection \<open>The invariant \<open>length uflag = length lbd\<close>\<close>

text \<open>Each of the three steps of \<^verbatim>\<open>dpll\<close> that change \<^verbatim>\<open>lbd\<close> or \<^verbatim>\<open>uflag\<close> keeps their lengths
  equal: the learning of a clause (\<^verbatim>\<open>lbd.push(b); uflag.push(true)\<close>), the analysis
  (\<^verbatim>\<open>update_lbd\<close>, then \<open>flag_loop\<close>), and the reduction (\<^verbatim>\<open>lbd = l2; uflag = u2\<close>).\<close>
lemma uflag_learn: \<open>length uf = length lbd \<Longrightarrow> length (uf @ [True]) = length (lbd @ [b])\<close>
  by simp

lemma uflag_analysis:
  assumes \<open>length uf = length lbd\<close> \<open>\<forall>x \<in> set mark. x \<le> st\<close>
    \<open>update_lbd_m db used tp lim lbd mark st m0 = (lbd', mark', st')\<close>
  shows \<open>length (flag_loop used m0 uf 0) = length lbd'\<close>
    \<open>\<forall>i < length uf. flag_loop used m0 uf 0 ! i \<longleftrightarrow> uf ! i \<or> m0 + i \<in> set used\<close>
  using flag_loop_eq[of used m0 uf 0] update_lbd_m_props(1)[OF assms(2,3)] assms(1) by simp_all

lemma uflag_reduce:
  \<open>reduce2_m T db lbd uf pos rs m0 = (db2, lbd2, uf2, rs2, pos2, keep, mp) \<Longrightarrow> m0 \<le> length db \<Longrightarrow>
    length uf2 = length lbd2\<close>
  by (rule reduce2_m_props(10))

end
