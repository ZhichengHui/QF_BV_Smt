theory QFBV_Phase
  imports Main
begin

section \<open>Target phase and best-phase rephasing\<close>

text \<open>Functional models of \<^verbatim>\<open>copy_phases\<close> and \<^verbatim>\<open>rephase\<close> of the prototype commit
  \<^verbatim>\<open>a9ab341\<close> (branch \<^verbatim>\<open>agent/54f5519e-phase\<close>, CaDiCaL's target and best phases), statement by
  statement, on \<open>nat\<close>s and lists. A trail literal \<^verbatim>\<open>Lit { var, neg }\<close> is the pair \<open>(var, neg)\<close>.
  The facts are the obligations (a) and (b) of the prototype's progress entry (PR #133): the phase
  vectors keep their lengths, every index is guarded, \<open>tph\<close> stays \<open>None\<close> outside the recorded
  set, and the schedule counter \<^verbatim>\<open>rephased\<close> cannot overflow.\<close>

subsection \<open>\<^verbatim>\<open>copy_phases\<close>\<close>

text \<open>The clear loop: \<^verbatim>\<open>if set[i] < tph.len() { tph[set[i]] = None; } i += 1\<close>, while
  \<^verbatim>\<open>i < set.len()\<close>; from \<^verbatim>\<open>i = 0\<close>.\<close>
function clear_loop :: \<open>bool option list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool option list\<close> where
  \<open>clear_loop tph s i =
    (if i < length s then
       clear_loop (if s ! i < length tph then tph[s ! i := None] else tph) s (i + 1)
     else tph)\<close>
  by pat_completeness auto
termination
  by (relation \<open>measure (\<lambda>(_, s, i). length s - i)\<close>) auto

declare clear_loop.simps [simp del]

text \<open>The copy loop: \<^verbatim>\<open>let v = trail[k].var; if v < tph.len() { tph[v] = Some(!trail[k].neg);\<close>
  \<^verbatim>\<open>set.push(v); } k += 1\<close>, while \<^verbatim>\<open>k < nc && k < trail.len()\<close>; from \<^verbatim>\<open>k = 0\<close> and
  \<^verbatim>\<open>set = Vec::new()\<close>.\<close>
function copy_loop :: \<open>bool option list \<Rightarrow> nat list \<Rightarrow> (nat \<times> bool) list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    bool option list \<times> nat list\<close> where
  \<open>copy_loop tph s trail nc k =
    (if k < nc \<and> k < length trail then
       (let v = fst (trail ! k) in
        if v < length tph then
          copy_loop (tph[v := Some (\<not> snd (trail ! k))]) (s @ [v]) trail nc (k + 1)
        else copy_loop tph s trail nc (k + 1))
     else (tph, s))\<close>
  by pat_completeness auto
termination
  by (relation \<open>measure (\<lambda>(_, _, trail, _, k). length trail - k)\<close>) auto

declare copy_loop.simps [simp del]

definition copy_phases_m :: \<open>bool option list \<Rightarrow> nat list \<Rightarrow> (nat \<times> bool) list \<Rightarrow> nat \<Rightarrow>
    bool option list \<times> nat list\<close> where
  \<open>copy_phases_m tph s trail nc = copy_loop (clear_loop tph s 0) [] trail nc 0\<close>

subsubsection \<open>The clear loop\<close>

lemma clear_loop_length: \<open>length (clear_loop tph s i) = length tph\<close>
proof (induction tph s i rule: clear_loop.induct)
  case (1 tph s i)
  then show ?case
    by (cases \<open>i < length s\<close>) (subst clear_loop.simps, simp)+
qed

lemma clear_loop_nth:
  \<open>v < length tph \<Longrightarrow> clear_loop tph s i ! v = (if v \<in> set (drop i s) then None else tph ! v)\<close>
proof (induction tph s i rule: clear_loop.induct)
  case (1 tph s i)
  show ?case
  proof (cases \<open>i < length s\<close>)
    case True
    let ?t = \<open>if s ! i < length tph then tph[s ! i := None] else tph\<close>
    have l: \<open>v < length ?t\<close> using "1.prems" by simp
    have IH: \<open>clear_loop ?t s (i + 1) ! v = (if v \<in> set (drop (i + 1) s) then None else ?t ! v)\<close>
      using "1.IH"[OF True l] .
    have d: \<open>drop i s = s ! i # drop (i + 1) s\<close>
      using True by (simp add: Cons_nth_drop_Suc)
    have e: \<open>clear_loop tph s i = clear_loop ?t s (i + 1)\<close>
      by (subst clear_loop.simps) (simp only: if_P[OF True])
    show ?thesis using IH "1.prems" by (auto simp: e d nth_list_update)
  next
    case False
    then show ?thesis by (subst clear_loop.simps) simp
  qed
qed

lemmas clear_loop_props = clear_loop_length clear_loop_nth

text \<open>With the invariant (\<open>tph\<close> is \<open>None\<close> outside \<open>set\<close>), the clear loop gives all \<open>None\<close>.\<close>
lemma clear_loop_none:
  assumes \<open>\<forall>v < length tph. v \<notin> set s \<longrightarrow> tph ! v = None\<close>
  shows \<open>clear_loop tph s 0 = replicate (length tph) None\<close>
  by (rule nth_equalityI) (use assms in \<open>auto simp: clear_loop_props\<close>)

subsubsection \<open>The copy loop\<close>

lemma copy_loop_all:
  assumes \<open>copy_loop tph s trail nc k = (tph', s')\<close>
  shows \<open>length tph' = length tph \<and>
    s' = s @ filter (\<lambda>v. v < length tph) (map fst (drop k (take nc trail))) \<and>
    (\<forall>v. (\<forall>j. k \<le> j \<and> j < min nc (length trail) \<longrightarrow> fst (trail ! j) \<noteq> v) \<longrightarrow> tph' ! v = tph ! v) \<and>
    (\<forall>v j. k \<le> j \<and> j < min nc (length trail) \<and> fst (trail ! j) = v \<and> v < length tph \<and>
      (\<forall>j'. j < j' \<and> j' < min nc (length trail) \<longrightarrow> fst (trail ! j') \<noteq> v) \<longrightarrow>
      tph' ! v = Some (\<not> snd (trail ! j)))\<close>
  using assms
proof (induction tph s trail nc k arbitrary: tph' s' rule: copy_loop.induct)
  case (1 tph s trail nc k)
  show ?case
  proof (cases \<open>k < nc \<and> k < length trail\<close>)
    case True
    define v0 where \<open>v0 = fst (trail ! k)\<close>
    have kt: \<open>k < length (take nc trail)\<close> using True by simp
    have d: \<open>drop k (take nc trail) = trail ! k # drop (k + 1) (take nc trail)\<close>
      using Cons_nth_drop_Suc[OF kt, symmetric] True by simp
    show ?thesis
    proof (cases \<open>v0 < length tph\<close>)
      case vin: True
      let ?t = \<open>tph[v0 := Some (\<not> snd (trail ! k))]\<close>
      have e: \<open>copy_loop ?t (s @ [v0]) trail nc (k + 1) = (tph', s')\<close>
        using "1.prems" True vin by (subst (asm) copy_loop.simps) (simp add: v0_def Let_def)
      have IH: \<open>length tph' = length ?t \<and>
        s' = (s @ [v0]) @ filter (\<lambda>v. v < length ?t) (map fst (drop (k + 1) (take nc trail))) \<and>
        (\<forall>v. (\<forall>j. k + 1 \<le> j \<and> j < min nc (length trail) \<longrightarrow> fst (trail ! j) \<noteq> v) \<longrightarrow> tph' ! v = ?t ! v) \<and>
        (\<forall>v j. k + 1 \<le> j \<and> j < min nc (length trail) \<and> fst (trail ! j) = v \<and> v < length ?t \<and>
          (\<forall>j'. j < j' \<and> j' < min nc (length trail) \<longrightarrow> fst (trail ! j') \<noteq> v) \<longrightarrow>
          tph' ! v = Some (\<not> snd (trail ! j)))\<close>
        using "1.IH"(1)[OF True v0_def vin e] .
      have l: \<open>length ?t = length tph\<close> by simp
      show ?thesis
      proof (intro conjI allI impI)
        show \<open>length tph' = length tph\<close> using IH by simp
        show \<open>s' = s @ filter (\<lambda>v. v < length tph) (map fst (drop k (take nc trail)))\<close>
          using IH vin by (simp add: d v0_def)
      next
        fix v
        assume n: \<open>\<forall>j. k \<le> j \<and> j < min nc (length trail) \<longrightarrow> fst (trail ! j) \<noteq> v\<close>
        then have \<open>v \<noteq> v0\<close> using True by (auto simp: v0_def)
        moreover have \<open>\<forall>j. k + 1 \<le> j \<and> j < min nc (length trail) \<longrightarrow> fst (trail ! j) \<noteq> v\<close>
          using n by auto
        ultimately show \<open>tph' ! v = tph ! v\<close> using IH by auto
      next
        fix v j
        assume a: \<open>k \<le> j \<and> j < min nc (length trail) \<and> fst (trail ! j) = v \<and> v < length tph \<and>
          (\<forall>j'. j < j' \<and> j' < min nc (length trail) \<longrightarrow> fst (trail ! j') \<noteq> v)\<close>
        show \<open>tph' ! v = Some (\<not> snd (trail ! j))\<close>
        proof (cases \<open>j = k\<close>)
          case True
          then have \<open>v = v0\<close> using a by (simp add: v0_def)
          moreover have \<open>\<forall>j'. k + 1 \<le> j' \<and> j' < min nc (length trail) \<longrightarrow> fst (trail ! j') \<noteq> v\<close>
            using a True by auto
          ultimately show ?thesis using IH True vin by auto
        next
          case False
          then have \<open>k + 1 \<le> j\<close> using a by simp
          then show ?thesis using IH a l by auto
        qed
      qed
    next
      case vout: False
      have e: \<open>copy_loop tph s trail nc (k + 1) = (tph', s')\<close>
        using "1.prems" True vout by (subst (asm) copy_loop.simps) (simp add: v0_def Let_def)
      have IH: \<open>length tph' = length tph \<and>
        s' = s @ filter (\<lambda>v. v < length tph) (map fst (drop (k + 1) (take nc trail))) \<and>
        (\<forall>v. (\<forall>j. k + 1 \<le> j \<and> j < min nc (length trail) \<longrightarrow> fst (trail ! j) \<noteq> v) \<longrightarrow> tph' ! v = tph ! v) \<and>
        (\<forall>v j. k + 1 \<le> j \<and> j < min nc (length trail) \<and> fst (trail ! j) = v \<and> v < length tph \<and>
          (\<forall>j'. j < j' \<and> j' < min nc (length trail) \<longrightarrow> fst (trail ! j') \<noteq> v) \<longrightarrow>
          tph' ! v = Some (\<not> snd (trail ! j)))\<close>
        using "1.IH"(2)[OF True v0_def vout e] .
      show ?thesis
      proof (intro conjI allI impI)
        show \<open>length tph' = length tph\<close> using IH by simp
        show \<open>s' = s @ filter (\<lambda>v. v < length tph) (map fst (drop k (take nc trail)))\<close>
          using IH vout by (simp add: d v0_def)
      next
        fix v
        assume n: \<open>\<forall>j. k \<le> j \<and> j < min nc (length trail) \<longrightarrow> fst (trail ! j) \<noteq> v\<close>
        then have \<open>\<forall>j. k + 1 \<le> j \<and> j < min nc (length trail) \<longrightarrow> fst (trail ! j) \<noteq> v\<close> by auto
        then show \<open>tph' ! v = tph ! v\<close> using IH by auto
      next
        fix v j
        assume a: \<open>k \<le> j \<and> j < min nc (length trail) \<and> fst (trail ! j) = v \<and> v < length tph \<and>
          (\<forall>j'. j < j' \<and> j' < min nc (length trail) \<longrightarrow> fst (trail ! j') \<noteq> v)\<close>
        then have \<open>j \<noteq> k\<close> using vout by (auto simp: v0_def)
        then have \<open>k + 1 \<le> j\<close> using a by simp
        then show \<open>tph' ! v = Some (\<not> snd (trail ! j))\<close> using IH a by auto
      qed
    qed
  next
    case False
    have e: \<open>copy_loop tph s trail nc k = (tph, s)\<close>
      by (subst copy_loop.simps) (simp only: if_not_P[OF False])
    have \<open>tph' = tph\<close> \<open>s' = s\<close> using "1.prems" by (simp_all add: e)
    moreover have \<open>drop k (take nc trail) = []\<close> using False by auto
    ultimately show ?thesis using False by auto
  qed
qed

lemma copy_loop_props:
  assumes \<open>copy_loop tph s trail nc k = (tph', s')\<close>
  shows \<open>length tph' = length tph\<close>
    \<open>s' = s @ filter (\<lambda>v. v < length tph) (map fst (drop k (take nc trail)))\<close>
    \<open>\<forall>v. (\<forall>j. k \<le> j \<and> j < min nc (length trail) \<longrightarrow> fst (trail ! j) \<noteq> v) \<longrightarrow> tph' ! v = tph ! v\<close>
    \<open>\<forall>v j. k \<le> j \<and> j < min nc (length trail) \<and> fst (trail ! j) = v \<and> v < length tph \<and>
      (\<forall>j'. j < j' \<and> j' < min nc (length trail) \<longrightarrow> fst (trail ! j') \<noteq> v) \<longrightarrow>
      tph' ! v = Some (\<not> snd (trail ! j))\<close>
  using copy_loop_all[OF assms] by blast+

subsubsection \<open>The facts of \<^verbatim>\<open>copy_phases\<close>\<close>

text \<open>The recorded set is the list of the in-range variables of the first
  \<open>min nc (length trail)\<close> trail entries, in trail order.\<close>
lemma copy_phases_m_set:
  assumes \<open>copy_phases_m tph s trail nc = (tph', s')\<close>
  shows \<open>s' = filter (\<lambda>v. v < length tph) (map fst (take nc trail))\<close>
  using copy_loop_props(2)[OF assms[unfolded copy_phases_m_def]] by (simp add: clear_loop_props)

text \<open>\<open>tph\<close> keeps its length; every recorded variable is in range; at most
  \<open>min nc (length trail)\<close> variables are recorded. No assumption on \<open>set\<close> is needed: both loops
  guard every index.\<close>
lemma copy_phases_m_props:
  assumes \<open>copy_phases_m tph s trail nc = (tph', s')\<close>
  shows \<open>length tph' = length tph\<close> \<open>\<forall>v \<in> set s'. v < length tph\<close>
    \<open>length s' \<le> min nc (length trail)\<close>
proof -
  show \<open>length tph' = length tph\<close>
    using copy_loop_props(1)[OF assms[unfolded copy_phases_m_def]] by (simp add: clear_loop_props)
  show \<open>\<forall>v \<in> set s'. v < length tph\<close> using copy_phases_m_set[OF assms] by simp
  have \<open>length s' \<le> length (map fst (take nc trail))\<close>
    unfolding copy_phases_m_set[OF assms] by (rule length_filter_le)
  then show \<open>length s' \<le> min nc (length trail)\<close> by simp
qed

lemma copy_phases_m_mem:
  assumes \<open>copy_phases_m tph s trail nc = (tph', s')\<close>
  shows \<open>v \<in> set s' \<longleftrightarrow> v < length tph \<and> (\<exists>j < min nc (length trail). fst (trail ! j) = v)\<close>
proof -
  have \<open>v \<in> set (map fst (take nc trail)) \<longleftrightarrow> (\<exists>j < min nc (length trail). fst (trail ! j) = v)\<close>
    by (simp only: in_set_conv_nth length_map length_take) auto
  then show ?thesis by (auto simp: copy_phases_m_set[OF assms])
qed

text \<open>With the invariant (\<open>tph\<close> is \<open>None\<close> outside \<open>set\<close>), \<open>tph'\<close> is \<open>None\<close> outside
  \<open>set'\<close>, and for every \<open>v\<close> in \<open>set'\<close>, \<open>tph' ! v\<close> is the phase of the last trail entry of
  \<open>v\<close> before \<open>min nc (length trail)\<close>.\<close>
theorem copy_phases_m_inv:
  assumes \<open>copy_phases_m tph s trail nc = (tph', s')\<close>
    and inv: \<open>\<forall>v < length tph. v \<notin> set s \<longrightarrow> tph ! v = None\<close>
  shows \<open>\<forall>v < length tph'. v \<notin> set s' \<longrightarrow> tph' ! v = None\<close>
    \<open>\<forall>v j. j < min nc (length trail) \<and> fst (trail ! j) = v \<and> v < length tph \<and>
      (\<forall>j'. j < j' \<and> j' < min nc (length trail) \<longrightarrow> fst (trail ! j') \<noteq> v) \<longrightarrow>
      tph' ! v = Some (\<not> snd (trail ! j))\<close>
    \<open>\<forall>v \<in> set s'. \<exists>j < min nc (length trail). fst (trail ! j) = v \<and>
      (\<forall>j'. j < j' \<and> j' < min nc (length trail) \<longrightarrow> fst (trail ! j') \<noteq> v) \<and>
      tph' ! v = Some (\<not> snd (trail ! j))\<close>
proof -
  let ?c = \<open>replicate (length tph) (None :: bool option)\<close>
  have e: \<open>copy_loop ?c [] trail nc 0 = (tph', s')\<close>
    using assms(1) by (simp add: copy_phases_m_def clear_loop_none[OF inv])
  note P = copy_loop_props[OF e]
  have len: \<open>length tph' = length tph\<close> using P(1) by simp
  show \<open>\<forall>v < length tph'. v \<notin> set s' \<longrightarrow> tph' ! v = None\<close>
  proof (intro allI impI)
    fix v
    assume v: \<open>v < length tph'\<close> \<open>v \<notin> set s'\<close>
    then have \<open>\<forall>j. 0 \<le> j \<and> j < min nc (length trail) \<longrightarrow> fst (trail ! j) \<noteq> v\<close>
      using copy_phases_m_mem[OF assms(1), of v] len by auto
    then show \<open>tph' ! v = None\<close> using P(3) v len by auto
  qed
  show last: \<open>\<forall>v j. j < min nc (length trail) \<and> fst (trail ! j) = v \<and> v < length tph \<and>
      (\<forall>j'. j < j' \<and> j' < min nc (length trail) \<longrightarrow> fst (trail ! j') \<noteq> v) \<longrightarrow>
      tph' ! v = Some (\<not> snd (trail ! j))\<close>
    using P(4) by simp
  show \<open>\<forall>v \<in> set s'. \<exists>j < min nc (length trail). fst (trail ! j) = v \<and>
      (\<forall>j'. j < j' \<and> j' < min nc (length trail) \<longrightarrow> fst (trail ! j') \<noteq> v) \<and>
      tph' ! v = Some (\<not> snd (trail ! j))\<close>
  proof
    fix v
    assume vs: \<open>v \<in> set s'\<close>
    let ?J = \<open>{j. j < min nc (length trail) \<and> fst (trail ! j) = v}\<close>
    have vl: \<open>v < length tph\<close> and ne: \<open>?J \<noteq> {}\<close>
      using copy_phases_m_mem[OF assms(1), of v] vs by auto
    have fin: \<open>finite ?J\<close> by simp
    define j where \<open>j = Max ?J\<close>
    have jJ: \<open>j \<in> ?J\<close> using Max_in[OF fin ne] by (simp add: j_def)
    have mx: \<open>\<forall>j'. j < j' \<and> j' < min nc (length trail) \<longrightarrow> fst (trail ! j') \<noteq> v\<close>
    proof (intro allI impI notI)
      fix j'
      assume \<open>j < j' \<and> j' < min nc (length trail)\<close> \<open>fst (trail ! j') = v\<close>
      then have \<open>j' \<in> ?J\<close> \<open>j < j'\<close> by auto
      have \<open>j' \<le> j\<close> using Max_ge[OF fin \<open>j' \<in> ?J\<close>] by (simp only: j_def)
      then show False using \<open>j < j'\<close> by simp
    qed
    show \<open>\<exists>j < min nc (length trail). fst (trail ! j) = v \<and>
      (\<forall>j'. j < j' \<and> j' < min nc (length trail) \<longrightarrow> fst (trail ! j') \<noteq> v) \<and>
      tph' ! v = Some (\<not> snd (trail ! j))\<close>
      using jJ mx vl last by blast
  qed
qed

text \<open>If the trail entries before \<open>min nc (length trail)\<close> have distinct variables (as on a
  trail), every one of them in range has its phase in \<open>tph'\<close>.\<close>
corollary copy_phases_m_distinct:
  assumes \<open>copy_phases_m tph s trail nc = (tph', s')\<close>
    and \<open>\<forall>v < length tph. v \<notin> set s \<longrightarrow> tph ! v = None\<close>
    and d: \<open>distinct (map fst (take nc trail))\<close>
    and \<open>j < min nc (length trail)\<close> \<open>fst (trail ! j) < length tph\<close>
  shows \<open>tph' ! fst (trail ! j) = Some (\<not> snd (trail ! j))\<close>
proof -
  have \<open>\<forall>j'. j < j' \<and> j' < min nc (length trail) \<longrightarrow> fst (trail ! j') \<noteq> fst (trail ! j)\<close>
  proof (intro allI impI)
    fix j'
    assume j': \<open>j < j' \<and> j' < min nc (length trail)\<close>
    have \<open>map fst (take nc trail) ! j' \<noteq> map fst (take nc trail) ! j\<close>
      using nth_eq_iff_index_eq[OF d, of j' j] j' assms(4) by simp
    then show \<open>fst (trail ! j') \<noteq> fst (trail ! j)\<close> using j' assms(4) by simp
  qed
  then show ?thesis using copy_phases_m_inv(2)[OF assms(1,2)] assms(4,5) by blast
qed

text \<open>With \<open>nc = 0\<close>, \<^verbatim>\<open>copy_phases\<close> clears \<open>tph\<close> and records nothing.\<close>
corollary copy_phases_m_zero:
  assumes \<open>\<forall>v < length tph. v \<notin> set s \<longrightarrow> tph ! v = None\<close>
  shows \<open>copy_phases_m tph s trail 0 = (replicate (length tph) None, [])\<close>
  by (simp add: copy_phases_m_def clear_loop_none[OF assms] copy_loop.simps)

subsection \<open>\<^verbatim>\<open>rephase\<close>\<close>

text \<open>The choice of \<^verbatim>\<open>kind\<close>: \<^verbatim>\<open>let mut kind = 0; if k == 1 { kind = 1; } else if k >= 2\<close>
  \<^verbatim>\<open>{ let r = (k - 2) % 4; if r == 0 || r == 2 { kind = 2; } else if r == 3 { kind = 1; } }\<close>.
  Kind 0 is original (all true), 1 inverted (all false), 2 best.\<close>
definition rephase_kind :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>rephase_kind k =
    (if k = 1 then 1
     else if 2 \<le> k then
       (let r = (k - 2) mod 4 in if r = 0 \<or> r = 2 then 2 else if r = 3 then 1 else 0)
     else 0)\<close>

text \<open>The loop: \<^verbatim>\<open>if kind == 0 { ph[i] = true; } else if kind == 1 { ph[i] = false; }\<close>
  \<^verbatim>\<open>else if i < bph.len() { match bph[i] { Some(b) => ph[i] = b, None => {} } } i += 1\<close>, while
  \<^verbatim>\<open>i < ph.len()\<close>; from \<^verbatim>\<open>i = 0\<close>.\<close>
function rph_loop :: \<open>bool list \<Rightarrow> bool option list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool list\<close> where
  \<open>rph_loop ph bph kind i =
    (if i < length ph then
       rph_loop
         (if kind = 0 then ph[i := True]
          else if kind = 1 then ph[i := False]
          else if i < length bph then (case bph ! i of Some b \<Rightarrow> ph[i := b] | None \<Rightarrow> ph)
          else ph) bph kind (i + 1)
     else ph)\<close>
  by pat_completeness auto
termination
  by (relation \<open>measure (\<lambda>(ph, _, _, i). length ph - i)\<close>) (auto split: option.split)

declare rph_loop.simps [simp del]

definition rephase_m :: \<open>bool list \<Rightarrow> bool option list \<Rightarrow> nat \<Rightarrow> bool list\<close> where
  \<open>rephase_m ph bph k = rph_loop ph bph (rephase_kind k) 0\<close>

text \<open>The new value of entry \<open>i\<close> for a kind.\<close>
definition rph_entry :: \<open>bool list \<Rightarrow> bool option list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>rph_entry ph bph kind i =
    (if kind = 0 then True
     else if kind = 1 then False
     else if i < length bph \<and> bph ! i \<noteq> None then the (bph ! i)
     else ph ! i)\<close>

lemma rph_loop_props:
  \<open>length (rph_loop ph bph kind i) = length ph\<close>
  \<open>j < length ph \<Longrightarrow> rph_loop ph bph kind i ! j = (if j < i then ph ! j else rph_entry ph bph kind j)\<close>
proof (induction ph bph kind i rule: rph_loop.induct)
  case (1 ph bph kind i)
  let ?p = \<open>if kind = 0 then ph[i := True]
          else if kind = 1 then ph[i := False]
          else if i < length bph then (case bph ! i of Some b \<Rightarrow> ph[i := b] | None \<Rightarrow> ph)
          else ph\<close>
  have l: \<open>length ?p = length ph\<close> by (simp split: option.split)
  have pi: \<open>i < length ph \<Longrightarrow> ?p ! i = rph_entry ph bph kind i\<close>
    by (auto simp: rph_entry_def split: option.split)
  have po: \<open>j \<noteq> i \<Longrightarrow> ?p ! j = ph ! j\<close> for j
    by (auto split: option.split)
  have pe: \<open>j \<noteq> i \<Longrightarrow> rph_entry ?p bph kind j = rph_entry ph bph kind j\<close> for j
    unfolding rph_entry_def using po[of j] by presburger
  {
    case 1
    show ?case
    proof (cases \<open>i < length ph\<close>)
      case True
      then show ?thesis using "1.IH"(1)[OF True] l by (subst rph_loop.simps) simp
    next
      case False
      then show ?thesis by (subst rph_loop.simps) simp
    qed
  next
    case 2
    show ?case
    proof (cases \<open>i < length ph\<close>)
      case True
      have IH: \<open>rph_loop ?p bph kind (i + 1) ! j = (if j < i + 1 then ?p ! j else rph_entry ?p bph kind j)\<close>
        using "1.IH"(2)[OF True] 2 l by simp
      show ?thesis
        using True IH pi po pe 2 by (subst rph_loop.simps) (auto simp: less_Suc_eq)
    next
      case False
      then show ?thesis using 2 by (subst rph_loop.simps) simp
    qed
  }
qed

subsubsection \<open>The facts of \<^verbatim>\<open>rephase\<close>\<close>

lemma rephase_kind_range: \<open>rephase_kind k \<in> {0, 1, 2}\<close>
  by (simp add: rephase_kind_def Let_def)

text \<open>The schedule: original, inverted, then best, original, best, inverted repeated.\<close>
lemma rephase_kind_schedule:
  \<open>rephase_kind 0 = 0\<close> \<open>rephase_kind 1 = 1\<close> \<open>rephase_kind (k + 2) = [2, 0, 2, 1] ! (k mod 4)\<close>
proof -
  show \<open>rephase_kind 0 = 0\<close> \<open>rephase_kind 1 = 1\<close> by (simp_all add: rephase_kind_def)
  have \<open>k mod 4 < 4\<close> by simp
  then have \<open>k mod 4 = 0 \<or> k mod 4 = 1 \<or> k mod 4 = 2 \<or> k mod 4 = 3\<close> by linarith
  then show \<open>rephase_kind (k + 2) = [2, 0, 2, 1] ! (k mod 4)\<close>
    by (auto simp: rephase_kind_def Let_def)
qed

text \<open>\<^verbatim>\<open>rephase\<close> keeps \<open>length ph\<close>, and every entry has its closed form by \<open>rephase_kind k\<close>:
  \<open>True\<close> (0), \<open>False\<close> (1), the best phase \<open>the (bph ! i)\<close> if it is recorded, else the old one
  (2). \<open>bph\<close> is read only under \<open>i < length bph\<close>, so its length is not constrained.\<close>
theorem rephase_m_props:
  \<open>length (rephase_m ph bph k) = length ph\<close>
  \<open>i < length ph \<Longrightarrow> rephase_m ph bph k ! i =
    (if rephase_kind k = 0 then True
     else if rephase_kind k = 1 then False
     else case (if i < length bph then bph ! i else None) of Some b \<Rightarrow> b | None \<Rightarrow> ph ! i)\<close>
  by (auto simp: rephase_m_def rph_loop_props rph_entry_def split: option.split)

subsection \<open>The rephase schedule bound\<close>

text \<open>In \<^verbatim>\<open>dpll\<close>: \<^verbatim>\<open>if REPHASE && total >= next_rephase && rephased < 1 << 20 { ...;\<close>
  \<^verbatim>\<open>rephased += 1; next_rephase = total + 1000 * (rephased + 1); }\<close>. With the guard, neither
  \<^verbatim>\<open>rephased += 1\<close> nor \<^verbatim>\<open>1000 * (rephased + 1)\<close> (with the new \<^verbatim>\<open>rephased\<close>) overflows
  \<^verbatim>\<open>usize\<close>: both are at most \<open>1000 * 2^20\<close>.\<close>
lemma rephase_schedule_bound:
  assumes \<open>(r :: nat) < 2 ^ 20\<close>
  shows \<open>r + 1 < 2 ^ 64\<close> \<open>1000 * (r + 1 + 1) < 2 ^ 64\<close> \<open>1000 * (r + 1) < 2 ^ 64\<close>
proof -
  have \<open>r + 1 + 1 \<le> 2 ^ 20 + 1\<close> using assms by simp
  then have \<open>1000 * (r + 1 + 1) \<le> 1000 * (2 ^ 20 + 1)\<close> by (rule mult_le_mono2)
  also have \<open>\<dots> < (2 :: nat) ^ 64\<close> by simp
  finally show b: \<open>1000 * (r + 1 + 1) < 2 ^ 64\<close> .
  have \<open>1000 * (r + 1) \<le> 1000 * (r + 1 + 1)\<close> \<open>r + 1 \<le> 1000 * (r + 1 + 1)\<close> by simp_all
  then show \<open>1000 * (r + 1) < 2 ^ 64\<close> \<open>r + 1 < 2 ^ 64\<close> using b by (meson le_less_trans)+
qed

text \<open>The sum \<^verbatim>\<open>total + 1000 * (rephased + 1)\<close> also needs a bound on \<^verbatim>\<open>total\<close>, the conflict
  count, which is unbounded in the present contract: it needs the bound on \<^verbatim>\<open>total\<close> of #108
  (bounded as \<^verbatim>\<open>restarts\<close>, or the sum taken with \<^verbatim>\<open>saturating_add\<close>), as PR #133 says. With
  \<open>total + 1000 * (2^20 + 1) < 2^64\<close>, the sum is in range by \<open>rephase_schedule_bound\<close>.\<close>

end
