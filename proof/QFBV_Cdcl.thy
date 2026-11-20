theory QFBV_Cdcl
  imports QFBV_Watch
begin

section \<open>Conflict-driven clause learning: the pure model\<close>

text \<open>Functional models of the conflict analysis and the backjump of \<^verbatim>\<open>dpll\<close> with clause learning,
  and the facts its contracts need: the learned clause follows from the clauses, the state of the
  search is kept, and the measure of the search grows. The clauses of the search (\<open>db\<close>) are the
  clauses of the problem followed by the learned ones. Trail positions, reasons and decision
  positions are natural numbers here.\<close>

abbreviation lv :: \<open>Lit \<Rightarrow> nat\<close> where
  \<open>lv l \<equiv> unat (Lit_var l)\<close>

subsection \<open>The models\<close>

text \<open>One literal of \<^verbatim>\<open>analyze_clause\<close>: a variable not yet marked is marked; it is counted if
  it was assigned at or after trail position \<open>st\<close> (the current decision level), otherwise its
  literal is learned.\<close>
definition ac_step :: \<open>nat list \<Rightarrow> nat \<Rightarrow> bool list \<times> Lit list \<times> nat \<Rightarrow> Lit \<Rightarrow> bool list \<times> Lit list \<times> nat\<close> where
  \<open>ac_step tp st s l \<equiv> (case s of (sn, ln, k) \<Rightarrow>
     if sn ! lv l then (sn, ln, k)
     else if st \<le> tp ! lv l then (sn[lv l := True], ln, Suc k)
     else (sn[lv l := True], ln @ [l], k))\<close>

text \<open>\<^verbatim>\<open>analyze_clause\<close>.\<close>
definition ac_m :: \<open>nat list \<Rightarrow> nat \<Rightarrow> Lit list \<Rightarrow> bool list \<times> Lit list \<times> nat \<Rightarrow> bool list \<times> Lit list \<times> nat\<close> where
  \<open>ac_m tp st c s \<equiv> foldl (ac_step tp st) s c\<close>

text \<open>The loop of \<^verbatim>\<open>analyze\<close> from trail position \<open>i\<close> down to \<open>st\<close>: the state is the marks, the
  learned literals and the count of marked entries of the current level; the result also gives
  the position reached and the flag \<^verbatim>\<open>ok\<close> (false once the first unique implication point is
  found).\<close>
function ana_loop ::
  \<open>Lit list list \<Rightarrow> Lit list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool list \<times> Lit list \<times> nat \<Rightarrow> nat \<Rightarrow>
   bool list \<times> Lit list \<times> nat \<times> nat \<times> bool\<close> where
  \<open>ana_loop cs t rs tp st s i =
     (case s of (sn, ln, k) \<Rightarrow>
        if st < i then
          (if sn ! lv (t ! (i - 1)) then
             (if k \<le> 1 then (sn, ln[0 := lneg (t ! (i - 1))], k, i - 1, False)
              else ana_loop cs t rs tp st (ac_m tp st (cs ! (rs ! (i - 1))) (sn, ln, k - 1)) (i - 1))
           else ana_loop cs t rs tp st s (i - 1))
        else (sn, ln, k, i, True))\<close>
  by pat_completeness auto
termination by (relation \<open>measure (\<lambda>(cs, t, rs, tp, st, s, i). i)\<close>) auto

text \<open>The two loops of \<^verbatim>\<open>analyze\<close> that clear the marks.\<close>
definition clr_m :: \<open>Lit list \<Rightarrow> Lit list \<Rightarrow> nat \<Rightarrow> bool list \<Rightarrow> bool list\<close> where
  \<open>clr_m ln t st sn \<equiv>
     foldl (\<lambda>s j. s[lv (t ! j) := False]) (foldl (\<lambda>s l. s[lv l := False]) sn ln) [st..<length t]\<close>

text \<open>\<^verbatim>\<open>analyze\<close> of the clause \<open>cf\<close> in conflict, with the trail \<open>t\<close>, the reasons \<open>rs\<close> (per trail
  position), the trail positions \<open>tp\<close> (per variable), the start \<open>st\<close> of the current level and the
  marks \<open>sn\<close>: the learned clause, the marks, and whether a clause was learned.\<close>
definition analyze_m ::
  \<open>Lit list list \<Rightarrow> Lit list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> Lit list \<times> bool list \<times> bool\<close> where
  \<open>analyze_m cs t rs tp st sn cf \<equiv>
     (case ac_m tp st (cs ! cf) (sn, [make_Lit 0 False], 0) of (s1, l1, k1) \<Rightarrow>
       (case (if 0 < k1 then ana_loop cs t rs tp st (s1, l1, k1) (length t) else (s1, l1, k1, length t, False)) of
          (s2, l2, k2, i2, ok2) \<Rightarrow> (l2, clr_m l2 t st s2, k2 = 1 \<and> \<not> ok2)))\<close>

subsection \<open>The trail\<close>

text \<open>\<open>tp\<close> gives the trail position of the variable of every trail entry.\<close>
definition tpos :: \<open>Lit list \<Rightarrow> nat list \<Rightarrow> bool\<close> where
  \<open>tpos t tp \<equiv> \<forall>j < length t. lv (t ! j) < length tp \<and> tp ! lv (t ! j) = j\<close>

text \<open>The entry \<open>j\<close> of the trail has the reason \<open>r\<close>: a clause that holds it and whose other literals
  are false by the entries before it.\<close>
definition reason :: \<open>Lit list list \<Rightarrow> Lit list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>reason cs t j r \<equiv> r < length cs \<and> t ! j \<in> set (cs ! r) \<and>
     (\<forall>l \<in> set (cs ! r). l \<noteq> t ! j \<longrightarrow> (\<exists>k < j. t ! k = lneg l))\<close>

lemma tr_var_inj:
  assumes \<open>tr_ok n a t\<close> \<open>i < length t\<close> \<open>j < length t\<close> \<open>lv (t ! i) = lv (t ! j)\<close>
  shows \<open>i = j\<close>
proof -
  have \<open>distinct (map lv t)\<close> using assms(1) by (simp add: tr_ok_def)
  then show ?thesis using assms(2-4) unfolding distinct_conv_nth by (metis length_map nth_map)
qed

lemma tr_var_lt: \<open>tr_ok n a t \<Longrightarrow> j < length t \<Longrightarrow> lv (t ! j) < n\<close>
  by (simp add: tr_ok_def)

lemma lneg_inj: \<open>lneg l = lneg l' \<Longrightarrow> l = l'\<close>
  by (metis lneg_lneg)

lemma lv_lneg: \<open>lv (lneg l) = lv l\<close>
  by (simp add: lneg_def)

lemma cdcl_lit_sem_lneg: \<open>lit_sem \<sigma> (lneg l) = (\<not> lit_sem \<sigma> l)\<close>
  by (simp add: lit_sem_def lneg_def)

subsection \<open>The analysis\<close>

text \<open>The marked entries of the current level below position \<open>i\<close>.\<close>
definition cur :: \<open>Lit list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool list \<Rightarrow> nat set\<close> where
  \<open>cur t st i sn \<equiv> {j. st \<le> j \<and> j < i \<and> sn ! lv (t ! j)}\<close>

text \<open>The clause the state of the analysis stands for: the learned literals after the first, and
  the negations of the marked entries of the current level below \<open>i\<close>.\<close>
definition acl :: \<open>Lit list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool list \<Rightarrow> Lit list \<Rightarrow> Lit set\<close> where
  \<open>acl t st i sn ln \<equiv> set (tl ln) \<union> lneg ` (\<lambda>j. t ! j) ` cur t st i sn\<close>

text \<open>The invariant of the marks: \<open>k\<close> counts the marked entries of the current level below \<open>i\<close>; the
  learned literals are false by entries below \<open>st\<close>; a marked variable is one of the current level
  or of a learned literal.\<close>
definition aj :: \<open>Lit list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool list \<Rightarrow> Lit list \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>aj t st i sn ln k \<equiv> k = card (cur t st i sn) \<and> ln \<noteq> [] \<and>
     (\<forall>l \<in> set (tl ln). \<exists>j < st. j < length t \<and> t ! j = lneg l) \<and>
     (\<forall>v < length sn. sn ! v \<longrightarrow> (\<exists>j. st \<le> j \<and> j < length t \<and> lv (t ! j) = v) \<or> (\<exists>l \<in> set (tl ln). lv l = v))\<close>

lemma cur_finite: \<open>finite (cur t st i sn)\<close>
  unfolding cur_def by (rule finite_subset[of _ \<open>{..<i}\<close>]) auto

locale atrail =
  fixes n :: nat and a :: \<open>bool option list\<close> and t :: \<open>Lit list\<close> and tp :: \<open>nat list\<close>
  assumes T: \<open>tr_ok n a t\<close> and P: \<open>tpos t tp\<close>
begin

lemma var_inj: \<open>i < length t \<Longrightarrow> j < length t \<Longrightarrow> lv (t ! i) = lv (t ! j) \<Longrightarrow> i = j\<close>
  using tr_var_inj[OF T] by blast

lemma var_lt: \<open>j < length t \<Longrightarrow> lv (t ! j) < n\<close>
  using tr_var_lt[OF T] by blast

lemma tp_at: \<open>j < length t \<Longrightarrow> tp ! lv (t ! j) = j\<close>
  using P by (simp add: tpos_def)

text \<open>A literal already marked and false by an entry below \<open>p\<close> is in the clause of the state.\<close>
lemma acl_marked:
  assumes \<open>aj t st p sn ln k\<close> \<open>length sn = n\<close> \<open>sn ! lv l\<close> \<open>j < p\<close> \<open>p \<le> length t\<close> \<open>t ! j = lneg l\<close>
  shows \<open>l \<in> acl t st p sn ln\<close>
proof (cases \<open>st \<le> j\<close>)
  case True
  have \<open>lv (t ! j) = lv l\<close> using assms(6) by (simp add: lv_lneg)
  then have \<open>j \<in> cur t st p sn\<close> using True assms(3,4) by (simp add: cur_def)
  moreover have \<open>l = lneg (t ! j)\<close> using assms(6) lneg_lneg by metis
  ultimately show ?thesis unfolding acl_def by blast
next
  case False
  have jt: \<open>j < length t\<close> using assms(4,5) by simp
  have vl: \<open>lv l < length sn\<close> using var_lt[OF jt] assms(2,6) by (simp add: lv_lneg)
  have vj: \<open>lv (t ! j) = lv l\<close> using assms(6) by (simp add: lv_lneg)
  have A: \<open>\<forall>v < length sn. sn ! v \<longrightarrow> (\<exists>j. st \<le> j \<and> j < length t \<and> lv (t ! j) = v) \<or> (\<exists>l \<in> set (tl ln). lv l = v)\<close>
    \<open>\<forall>l \<in> set (tl ln). \<exists>j < st. j < length t \<and> t ! j = lneg l\<close>
    using assms(1) by (simp_all add: aj_def)
  show ?thesis
  proof (cases \<open>\<exists>j'. st \<le> j' \<and> j' < length t \<and> lv (t ! j') = lv l\<close>)
    case True
    then obtain j' where \<open>st \<le> j'\<close> \<open>j' < length t\<close> \<open>lv (t ! j') = lv l\<close> by blast
    then have \<open>j' = j\<close> using var_inj[OF _ jt] vj by simp
    then show ?thesis using False \<open>st \<le> j'\<close> by simp
  next
    case no: False
    then obtain l' where l': \<open>l' \<in> set (tl ln)\<close> \<open>lv l' = lv l\<close> using A(1) vl assms(3) by blast
    then obtain j'' where j'': \<open>j'' < st\<close> \<open>t ! j'' = lneg l'\<close> \<open>j'' < length t\<close> using A(2) by blast
    have j''t: \<open>j'' < length t\<close> using j''(3) .
    have \<open>lv (t ! j'') = lv (t ! j)\<close> using j''(2) l'(2) vj by (simp add: lv_lneg)
    then have \<open>j'' = j\<close> using var_inj[OF j''t jt] by simp
    then have \<open>l' = l\<close> using j''(2) assms(6) lneg_inj by simp
    then show ?thesis using l'(1) by (simp add: acl_def)
  qed
qed

lemma ac_step_inv:
  assumes A: \<open>aj t st p sn ln k\<close> \<open>length sn = n\<close> \<open>p \<le> length t\<close>
    and hl: \<open>(\<exists>j < p. t ! j = lneg l) \<or> sn ! lv l\<close>
    and S: \<open>ac_step tp st (sn, ln, k) l = (sn', ln', k')\<close>
  shows \<open>aj t st p sn' ln' k' \<and> length sn' = n \<and> acl t st p sn ln \<subseteq> acl t st p sn' ln' \<and>
         ((\<exists>j < p. t ! j = lneg l) \<longrightarrow> l \<in> acl t st p sn' ln') \<and> (\<forall>v. sn ! v \<longrightarrow> sn' ! v) \<and>
         (\<exists>e. ln' = ln @ e) \<and> k \<le> k' \<and> sn' ! lv l\<close>
proof (cases \<open>sn ! lv l\<close>)
  case True
  then have e: \<open>sn' = sn\<close> \<open>ln' = ln\<close> \<open>k' = k\<close> using S by (auto simp: ac_step_def)
  then show ?thesis using A acl_marked[OF A(1,2) True _ A(3)] True by auto
next
  case nm: False
  then obtain j where j: \<open>j < p\<close> \<open>t ! j = lneg l\<close> using hl by blast
  have jt: \<open>j < length t\<close> using j(1) A(3) by simp
  have vj: \<open>lv (t ! j) = lv l\<close> using j(2) by (simp add: lv_lneg)
  have vn: \<open>lv l < length sn\<close> using var_lt[OF jt] vj A(2) by simp
  have tpj: \<open>tp ! lv l = j\<close> using tp_at[OF jt] vj by simp
  have AA: \<open>k = card (cur t st p sn)\<close> \<open>ln \<noteq> []\<close> \<open>\<forall>l \<in> set (tl ln). \<exists>j < st. j < length t \<and> t ! j = lneg l\<close>
    \<open>\<forall>v < length sn. sn ! v \<longrightarrow> (\<exists>j. st \<le> j \<and> j < length t \<and> lv (t ! j) = v) \<or> (\<exists>l \<in> set (tl ln). lv l = v)\<close>
    using A(1) by (simp_all add: aj_def)
  let ?sn = \<open>sn[lv l := True]\<close>
  have upd: \<open>?sn ! v = (v = lv l \<or> sn ! v)\<close> if \<open>v < length sn\<close> for v
    using that vn by (auto simp: nth_list_update)
  have cur_eq: \<open>cur t st p ?sn = cur t st p sn \<union> (if st \<le> j then {j} else {})\<close>
  proof -
    have \<open>j' \<in> cur t st p ?sn \<longleftrightarrow> j' \<in> cur t st p sn \<or> (st \<le> j \<and> j' = j)\<close> for j'
    proof (cases \<open>j' < p\<close>)
      case True
      then have jt': \<open>j' < length t\<close> using A(3) by simp
      have \<open>lv (t ! j') < length sn\<close> using var_lt[OF jt'] A(2) by simp
      moreover have \<open>lv (t ! j') = lv l \<longleftrightarrow> j' = j\<close> using var_inj[OF jt' jt] vj by auto
      ultimately show ?thesis using upd True j(1) by (auto simp: cur_def)
    qed (use j(1) in \<open>auto simp: cur_def\<close>)
    then show ?thesis by auto
  qed
  have jn: \<open>j \<notin> cur t st p sn\<close> using nm vj by (simp add: cur_def)
  have seen': \<open>\<forall>v. sn ! v \<longrightarrow> ?sn ! v\<close>
  proof (intro allI impI)
    fix v assume \<open>sn ! v\<close>
    then show \<open>?sn ! v\<close> by (cases \<open>v = lv l\<close>) (simp_all add: vn)
  qed
  show ?thesis
  proof (cases \<open>st \<le> tp ! lv l\<close>)
    case True
    then have e: \<open>sn' = ?sn\<close> \<open>ln' = ln\<close> \<open>k' = Suc k\<close> using S nm by (auto simp: ac_step_def)
    have sj: \<open>st \<le> j\<close> using True tpj by simp
    have c: \<open>cur t st p ?sn = insert j (cur t st p sn)\<close> using cur_eq sj by auto
    have card: \<open>Suc k = card (cur t st p ?sn)\<close> using c jn cur_finite AA(1) by simp
    have marks: \<open>\<forall>v < length ?sn. ?sn ! v \<longrightarrow> (\<exists>j. st \<le> j \<and> j < length t \<and> lv (t ! j) = v) \<or> (\<exists>l \<in> set (tl ln). lv l = v)\<close>
      using AA(4) upd sj jt vj by auto
    have \<open>l \<in> acl t st p ?sn ln\<close> using c j(2) by (auto simp: acl_def lneg_lneg)
    moreover have \<open>acl t st p sn ln \<subseteq> acl t st p ?sn ln\<close> using c by (auto simp: acl_def)
    ultimately show ?thesis using e card marks AA(2,3) A(2) seen' vn by (auto simp: aj_def)
  next
    case False
    then have e: \<open>sn' = ?sn\<close> \<open>ln' = ln @ [l]\<close> \<open>k' = k\<close> using S nm by (auto simp: ac_step_def)
    have sj: \<open>j < st\<close> using False tpj by simp
    have c: \<open>cur t st p ?sn = cur t st p sn\<close> using cur_eq sj by auto
    have tl: \<open>tl (ln @ [l]) = tl ln @ [l]\<close> using AA(2) by simp
    have marks: \<open>\<forall>v < length ?sn. ?sn ! v \<longrightarrow> (\<exists>j. st \<le> j \<and> j < length t \<and> lv (t ! j) = v) \<or> (\<exists>l' \<in> set (tl (ln @ [l])). lv l' = v)\<close>
      using AA(4) upd tl by auto
    have low: \<open>\<forall>l' \<in> set (tl (ln @ [l])). \<exists>j < st. j < length t \<and> t ! j = lneg l'\<close>
      using AA(3) tl sj j(2) jt by auto
    have \<open>l \<in> acl t st p ?sn (ln @ [l])\<close> using tl by (simp add: acl_def)
    moreover have \<open>acl t st p sn ln \<subseteq> acl t st p ?sn (ln @ [l])\<close> using c tl by (auto simp: acl_def)
    ultimately show ?thesis using e c AA(1,2) marks low A(2) seen' vn by (auto simp: aj_def)
  qed
qed

lemma ac_inv:
  assumes \<open>aj t st p sn ln k\<close> \<open>length sn = n\<close> \<open>p \<le> length t\<close>
    \<open>\<forall>l \<in> set c. (\<exists>j < p. t ! j = lneg l) \<or> sn ! lv l\<close>
    \<open>ac_m tp st c (sn, ln, k) = (sn', ln', k')\<close>
  shows \<open>aj t st p sn' ln' k' \<and> length sn' = n \<and> acl t st p sn ln \<subseteq> acl t st p sn' ln' \<and>
         (\<forall>l \<in> set c. (\<exists>j < p. t ! j = lneg l) \<longrightarrow> l \<in> acl t st p sn' ln') \<and> (\<exists>e. ln' = ln @ e) \<and> k \<le> k' \<and>
         (\<forall>v. sn ! v \<longrightarrow> sn' ! v) \<and> (\<forall>l \<in> set c. sn' ! lv l)\<close>
  using assms
proof (induction c arbitrary: sn ln k)
  case Nil
  then show ?case by (simp add: ac_m_def)
next
  case (Cons l c)
  obtain s1 l1 k1 where s1: \<open>ac_step tp st (sn, ln, k) l = (s1, l1, k1)\<close> by (cases \<open>ac_step tp st (sn, ln, k) l\<close>) auto
  note S = ac_step_inv[OF Cons.prems(1,2,3) _ s1]
  have h: \<open>(\<exists>j < p. t ! j = lneg l) \<or> sn ! lv l\<close> using Cons.prems(4) by simp
  note S1 = S[OF h]
  have h1: \<open>\<forall>l \<in> set c. (\<exists>j < p. t ! j = lneg l) \<or> s1 ! lv l\<close> using Cons.prems(4) S1 by auto
  have h2: \<open>ac_m tp st c (s1, l1, k1) = (sn', ln', k')\<close> using Cons.prems(5) s1 by (simp add: ac_m_def)
  note IH = Cons.IH[OF conjunct1[OF S1] conjunct1[OF conjunct2[OF S1]] Cons.prems(3) h1 h2]
  show ?case using IH S1 by auto
qed


lemma cur_empty: \<open>cur t st st sn = {}\<close>
  by (simp add: cur_def)

text \<open>The loop of the analysis keeps the invariant and ends at the first unique implication point,
  with a learned clause that follows from the clauses.\<close>
lemma ana_loop_inv:
  assumes \<open>aj t st i sn ln k\<close> \<open>length sn = n\<close> \<open>st \<le> i\<close> \<open>i \<le> length t\<close> \<open>0 < k\<close>
    \<open>\<forall>\<sigma>. cnf_sem \<sigma> cs \<longrightarrow> (\<exists>l \<in> acl t st i sn ln. lit_sem \<sigma> l)\<close>
    \<open>\<forall>j. st < j \<and> j < length t \<longrightarrow> reason cs t j (rs ! j)\<close>
    \<open>ana_loop cs t rs tp st (sn, ln, k) i = (sn', ln', k', i', ok')\<close>
  shows \<open>\<not> ok' \<and> k' = 1 \<and> st \<le> i' \<and> i' < length t \<and> ln' \<noteq> [] \<and> hd ln' = lneg (t ! i') \<and>
     (\<forall>l \<in> set (tl ln'). \<exists>j < st. j < length t \<and> t ! j = lneg l) \<and>
     (\<forall>\<sigma>. cnf_sem \<sigma> cs \<longrightarrow> (\<exists>l \<in> set ln'. lit_sem \<sigma> l)) \<and> length sn' = n \<and>
     (\<forall>v < n. sn' ! v \<longrightarrow> (\<exists>j. st \<le> j \<and> j < length t \<and> lv (t ! j) = v) \<or> (\<exists>l \<in> set (tl ln'). lv l = v))\<close>
  using assms
proof (induction i arbitrary: sn ln k rule: less_induct)
  case (less i)
  have AA: \<open>k = card (cur t st i sn)\<close> \<open>ln \<noteq> []\<close> \<open>\<forall>l \<in> set (tl ln). \<exists>j < st. j < length t \<and> t ! j = lneg l\<close>
    \<open>\<forall>v < length sn. sn ! v \<longrightarrow> (\<exists>j. st \<le> j \<and> j < length t \<and> lv (t ! j) = v) \<or> (\<exists>l \<in> set (tl ln). lv l = v)\<close>
    using less.prems(1) by (simp_all add: aj_def)
  show ?case
  proof (cases \<open>st < i\<close>)
    case False
    then have \<open>i = st\<close> using less.prems(3) by simp
    then show ?thesis using AA(1) less.prems(5) cur_empty by simp
  next
    case si: True
    let ?p = \<open>i - 1\<close>
    have pt: \<open>?p < length t\<close> and pi: \<open>?p < i\<close> using si less.prems(4) by auto
    have cur_p: \<open>cur t st ?p sn = cur t st i sn - {?p}\<close> by (auto simp: cur_def)
    show ?thesis
    proof (cases \<open>sn ! lv (t ! ?p)\<close>)
      case False
      then have r: \<open>ana_loop cs t rs tp st (sn, ln, k) ?p = (sn', ln', k', i', ok')\<close>
        using less.prems(8) si by simp
      have pn: \<open>?p \<notin> cur t st i sn\<close> using False by (simp add: cur_def)
      then have c: \<open>cur t st ?p sn = cur t st i sn\<close> using cur_p by simp
      have \<open>aj t st ?p sn ln k\<close> using less.prems(1) c by (simp add: aj_def)
      moreover have \<open>acl t st ?p sn ln = acl t st i sn ln\<close> using c by (simp add: acl_def)
      ultimately show ?thesis
        using less.IH[OF pi _ less.prems(2) _ _ less.prems(5) _ less.prems(7) r] si pt less.prems(6) by simp
    next
      case seen: True
      have pc: \<open>?p \<in> cur t st i sn\<close> using seen si by (simp add: cur_def)
      show ?thesis
      proof (cases \<open>k \<le> 1\<close>)
        case True
        then have e: \<open>sn' = sn\<close> \<open>ln' = ln[0 := lneg (t ! ?p)]\<close> \<open>k' = k\<close> \<open>i' = ?p\<close> \<open>ok' = False\<close>
          using less.prems(8) si seen by auto
        have k1: \<open>k = 1\<close> using True less.prems(5) by simp
        have one: \<open>cur t st i sn = {?p}\<close>
          using AA(1) k1 pc cur_finite card_1_singletonE by (metis singletonD)
        obtain x xs where ln: \<open>ln = x # xs\<close> using AA(2) by (cases ln) auto
        have ln': \<open>ln' = lneg (t ! ?p) # xs\<close> using e(2) ln by simp
        have \<open>acl t st i sn ln = insert (lneg (t ! ?p)) (set xs)\<close> using one ln by (auto simp: acl_def)
        then have \<open>\<forall>\<sigma>. cnf_sem \<sigma> cs \<longrightarrow> (\<exists>l \<in> set ln'. lit_sem \<sigma> l)\<close> using less.prems(6) ln' by simp
        then show ?thesis using e ln' ln AA(3,4) less.prems(2) si pt k1 by auto
      next
        case False
        obtain j where j: \<open>j \<in> cur t st i sn\<close> \<open>j \<noteq> ?p\<close>
        proof -
          have \<open>cur t st i sn \<noteq> {?p}\<close> using False AA(1) by auto
          then show ?thesis using that pc by blast
        qed
        have sp: \<open>st < ?p\<close> using j by (auto simp: cur_def)
        have R: \<open>reason cs t ?p (rs ! ?p)\<close> using less.prems(7) sp pt by simp
        let ?R = \<open>cs ! (rs ! ?p)\<close>
        obtain s2 l2 k2 where a2: \<open>ac_m tp st ?R (sn, ln, k - 1) = (s2, l2, k2)\<close>
          by (cases \<open>ac_m tp st ?R (sn, ln, k - 1)\<close>) auto
        have r: \<open>ana_loop cs t rs tp st (s2, l2, k2) ?p = (sn', ln', k', i', ok')\<close>
          using less.prems(8) si seen False a2 by simp
        have aj1: \<open>aj t st ?p sn ln (k - 1)\<close>
          using less.prems(1) cur_p pc cur_finite AA(1) by (simp add: aj_def)
        have hR: \<open>\<forall>l \<in> set ?R. (\<exists>j < ?p. t ! j = lneg l) \<or> sn ! lv l\<close>
          using R seen by (auto simp: reason_def)
        note I = ac_inv[OF aj1 less.prems(2) less_imp_le[OF pt] hR a2]
        have ent: \<open>\<forall>\<sigma>. cnf_sem \<sigma> cs \<longrightarrow> (\<exists>l \<in> acl t st ?p s2 l2. lit_sem \<sigma> l)\<close>
        proof (intro allI impI)
          fix \<sigma> assume m: \<open>cnf_sem \<sigma> cs\<close>
          obtain x where x: \<open>x \<in> acl t st i sn ln\<close> \<open>lit_sem \<sigma> x\<close> using less.prems(6) m by blast
          show \<open>\<exists>l \<in> acl t st ?p s2 l2. lit_sem \<sigma> l\<close>
          proof (cases \<open>x = lneg (t ! ?p)\<close>)
            case False
            have \<open>x \<in> acl t st ?p sn ln\<close>
            proof -
              have \<open>x \<in> set (tl ln) \<or> (\<exists>j \<in> cur t st i sn. x = lneg (t ! j))\<close> using x(1) by (auto simp: acl_def)
              then show ?thesis
              proof
                assume \<open>\<exists>j \<in> cur t st i sn. x = lneg (t ! j)\<close>
                then obtain j where \<open>j \<in> cur t st i sn\<close> \<open>x = lneg (t ! j)\<close> by blast
                then have \<open>j \<in> cur t st ?p sn\<close> using False cur_p by auto
                then show ?thesis using \<open>x = lneg (t ! j)\<close> by (auto simp: acl_def)
              qed (simp add: acl_def)
            qed
            then show ?thesis using I x(2) by blast
          next
            case True
            then have np: \<open>\<not> lit_sem \<sigma> (t ! ?p)\<close> using x(2) cdcl_lit_sem_lneg by simp
            have \<open>rs ! ?p < length cs\<close> using R by (simp add: reason_def)
            then have \<open>?R \<in> set cs\<close> by simp
            then obtain y where y: \<open>y \<in> set ?R\<close> \<open>lit_sem \<sigma> y\<close> using m unfolding cnf_sem_def by blast
            then have \<open>y \<noteq> t ! ?p\<close> using np by auto
            then have \<open>\<exists>j < ?p. t ! j = lneg y\<close> using R y(1) by (simp add: reason_def)
            then have \<open>y \<in> acl t st ?p s2 l2\<close> using I y(1) by blast
            then show ?thesis using y(2) by blast
          qed
        qed
        have \<open>k - 1 \<le> k2\<close> using I by blast
        then have k2: \<open>0 < k2\<close> using False by linarith
        show ?thesis
          using less.IH[OF pi conjunct1[OF I] conjunct1[OF conjunct2[OF I]] _ _ k2 ent less.prems(7) r] sp pt by simp
      qed
    qed
  qed
qed

lemma clr_nth:
  \<open>v < length s \<Longrightarrow> foldl (\<lambda>s x. s[f x := False]) s xs ! v = (if v \<in> f ` set xs then False else s ! v)\<close>
  by (induction xs arbitrary: s) (auto simp: nth_list_update)

lemma clr_length: \<open>length (foldl (\<lambda>s x. s[f x := False]) s xs) = length s\<close>
  by (induction xs arbitrary: s) auto

lemma clr_all:
  assumes \<open>length sn = n\<close>
    \<open>\<forall>v < n. sn ! v \<longrightarrow> (\<exists>j. st \<le> j \<and> j < length t \<and> lv (t ! j) = v) \<or> (\<exists>l \<in> set ln. lv l = v)\<close>
  shows \<open>clr_m ln t st sn = replicate n False\<close>
proof (rule nth_equalityI)
  show \<open>length (clr_m ln t st sn) = length (replicate n False)\<close>
    using assms(1) by (simp add: clr_m_def clr_length)
next
  fix v assume \<open>v < length (clr_m ln t st sn)\<close>
  then have v: \<open>v < n\<close> using assms(1) by (simp add: clr_m_def clr_length)
  let ?s1 = \<open>foldl (\<lambda>s l. s[lv l := False]) sn ln\<close>
  have l1: \<open>length ?s1 = n\<close> using assms(1) clr_length by metis
  have \<open>clr_m ln t st sn ! v = (if v \<in> (\<lambda>j. lv (t ! j)) ` set [st..<length t] then False else ?s1 ! v)\<close>
    unfolding clr_m_def using clr_nth[of v ?s1 \<open>\<lambda>j. lv (t ! j)\<close>] l1 v by simp
  moreover have \<open>?s1 ! v = (if v \<in> lv ` set ln then False else sn ! v)\<close>
    using clr_nth[of v sn lv ln] assms(1) v by simp
  ultimately show \<open>clr_m ln t st sn ! v = replicate n False ! v\<close> using assms(2) v by force
qed

text \<open>The analysis of a clause in conflict: the marks are cleared; a learned clause follows from the
  clauses, its first literal is the negation of an entry of the current level and its other
  literals are false by entries below \<open>st\<close>; a clause is learned if the conflict has a literal of
  the current level.\<close>
theorem analyze_ok:
  assumes \<open>dpll_wf n cs\<close> \<open>st \<le> length t\<close> \<open>\<forall>j. st < j \<and> j < length t \<longrightarrow> reason cs t j (rs ! j)\<close>
    \<open>cf < length cs\<close> \<open>\<forall>l \<in> set (cs ! cf). \<exists>j < length t. t ! j = lneg l\<close>
    \<open>analyze_m cs t rs tp st (replicate n False) cf = (C, sn', found)\<close>
  shows \<open>sn' = replicate n False \<and>
    (found \<longrightarrow> C \<noteq> [] \<and> (\<exists>u. st \<le> u \<and> u < length t \<and> hd C = lneg (t ! u)) \<and>
       (\<forall>l \<in> set (tl C). \<exists>j < st. j < length t \<and> t ! j = lneg l) \<and>
       (\<forall>\<sigma>. cnf_sem \<sigma> cs \<longrightarrow> (\<exists>l \<in> set C. lit_sem \<sigma> l))) \<and>
    ((\<exists>l \<in> set (cs ! cf). \<exists>j. st \<le> j \<and> j < length t \<and> t ! j = lneg l) \<longrightarrow> found)\<close>
proof -
  let ?s0 = \<open>replicate n False\<close>
  obtain s1 l1 k1 where a1: \<open>ac_m tp st (cs ! cf) (?s0, [make_Lit 0 False], 0) = (s1, l1, k1)\<close>
    by (cases \<open>ac_m tp st (cs ! cf) (?s0, [make_Lit 0 False], 0)\<close>) auto
  have aj0: \<open>aj t st (length t) ?s0 [make_Lit 0 False] 0\<close>
    by (auto simp: aj_def cur_def var_lt)
  have h0: \<open>\<forall>l \<in> set (cs ! cf). (\<exists>j < length t. t ! j = lneg l) \<or> ?s0 ! lv l\<close> using assms(5) by blast
  note I = ac_inv[OF aj0 _ order_refl h0 a1]
  have I1: \<open>aj t st (length t) s1 l1 k1\<close> \<open>length s1 = n\<close> \<open>\<forall>l \<in> set (cs ! cf). s1 ! lv l\<close>
    \<open>\<forall>l \<in> set (cs ! cf). l \<in> acl t st (length t) s1 l1\<close>
    using I assms(5) by auto
  have ent: \<open>\<forall>\<sigma>. cnf_sem \<sigma> cs \<longrightarrow> (\<exists>l \<in> acl t st (length t) s1 l1. lit_sem \<sigma> l)\<close>
  proof (intro allI impI)
    fix \<sigma> assume \<open>cnf_sem \<sigma> cs\<close>
    moreover have \<open>cs ! cf \<in> set cs\<close> using assms(4) by simp
    ultimately obtain l where \<open>l \<in> set (cs ! cf)\<close> \<open>lit_sem \<sigma> l\<close> unfolding cnf_sem_def by blast
    then show \<open>\<exists>l \<in> acl t st (length t) s1 l1. lit_sem \<sigma> l\<close> using I1(4) by blast
  qed
  have J: \<open>k1 = card (cur t st (length t) s1)\<close> \<open>l1 \<noteq> []\<close>
    \<open>\<forall>v < length s1. s1 ! v \<longrightarrow> (\<exists>j. st \<le> j \<and> j < length t \<and> lv (t ! j) = v) \<or> (\<exists>l \<in> set (tl l1). lv l = v)\<close>
    using I1(1) by (simp_all add: aj_def)
  have tl_sub: \<open>set (tl xs) \<subseteq> set xs\<close> for xs :: \<open>Lit list\<close> by (cases xs) auto
  have cur_found: \<open>0 < k1\<close> if h: \<open>\<exists>l \<in> set (cs ! cf). \<exists>j. st \<le> j \<and> j < length t \<and> t ! j = lneg l\<close>
  proof -
    obtain l j where lj: \<open>l \<in> set (cs ! cf)\<close> \<open>st \<le> j\<close> \<open>j < length t\<close> \<open>t ! j = lneg l\<close> using h by blast
    have \<open>s1 ! lv (t ! j)\<close> using I1(3) lj by (simp add: lv_lneg)
    then have \<open>j \<in> cur t st (length t) s1\<close> using lj by (simp add: cur_def)
    then show ?thesis using J(1) cur_finite by (metis card_gt_0_iff empty_iff)
  qed
  show ?thesis
  proof (cases \<open>0 < k1\<close>)
    case True
    obtain s2 l2 k2 i2 ok2 where a2: \<open>ana_loop cs t rs tp st (s1, l1, k1) (length t) = (s2, l2, k2, i2, ok2)\<close>
      by (cases \<open>ana_loop cs t rs tp st (s1, l1, k1) (length t)\<close>) auto
    have r: \<open>C = l2\<close> \<open>sn' = clr_m l2 t st s2\<close> \<open>found = (k2 = 1 \<and> \<not> ok2)\<close>
      using assms(6) a1 a2 True by (auto simp: analyze_m_def)
    note L = ana_loop_inv[OF I1(1,2) assms(2) order_refl True ent assms(3) a2]
    have \<open>\<forall>v < n. s2 ! v \<longrightarrow> (\<exists>j. st \<le> j \<and> j < length t \<and> lv (t ! j) = v) \<or> (\<exists>l \<in> set l2. lv l = v)\<close>
      using L tl_sub by blast
    then have \<open>sn' = ?s0\<close> using clr_all L r(2) by blast
    moreover have \<open>hd l2 = lneg (t ! i2)\<close> \<open>st \<le> i2\<close> \<open>i2 < length t\<close> using L by simp_all
    ultimately show ?thesis using L r True by blast
  next
    case False
    have r: \<open>C = l1\<close> \<open>sn' = clr_m l1 t st s1\<close> \<open>found = False\<close>
      using assms(6) a1 False by (auto simp: analyze_m_def)
    have \<open>\<forall>v < n. s1 ! v \<longrightarrow> (\<exists>j. st \<le> j \<and> j < length t \<and> lv (t ! j) = v) \<or> (\<exists>l \<in> set l1. lv l = v)\<close>
      using J(3) I1(2) tl_sub by blast
    then have \<open>sn' = ?s0\<close> using clr_all I1(2) r(2) by blast
    then show ?thesis using r False cur_found by blast
  qed
qed


lemma notin_prefix: \<open>i < length t \<Longrightarrow> k \<le> i \<Longrightarrow> t ! i \<notin> set (take k t)\<close>
proof
  assume i: \<open>i < length t\<close> \<open>k \<le> i\<close> and m: \<open>t ! i \<in> set (take k t)\<close>
  then obtain i' where \<open>i' < length (take k t)\<close> \<open>take k t ! i' = t ! i\<close> by (auto simp: in_set_conv_nth)
  then have \<open>i' < k\<close> \<open>i' < length t\<close> \<open>t ! i' = t ! i\<close> by auto
  then show False using var_inj[of i' i] i by simp
qed

end


subsection \<open>The backjump\<close>

text \<open>\<^verbatim>\<open>second_watch\<close>: the position after the first of a literal of the clause \<open>c\<close> whose trail
  position is the highest (the first such one), swapped to position 1.\<close>
definition sw_pos :: \<open>nat list \<Rightarrow> Lit list \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>sw_pos tp c m \<equiv> foldl (\<lambda>b k. if tp ! lv (c ! b) < tp ! lv (c ! k) then k else b) 1 [2..<m]\<close>

definition sw_m :: \<open>nat list \<Rightarrow> Lit list \<Rightarrow> Lit list\<close> where
  \<open>sw_m tp c \<equiv> let b = sw_pos tp c (length c) in c[1 := c ! b, b := c ! 1]\<close>

text \<open>\<^verbatim>\<open>level_of\<close>: the number of decision positions at or below \<open>p\<close>.\<close>
definition level_of_m :: \<open>nat list \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>level_of_m L p \<equiv> length (takeWhile (\<lambda>x. x \<le> p) L)\<close>

text \<open>\<^verbatim>\<open>add_clause_watched\<close>.\<close>
definition acw_m ::
  \<open>Lit list list \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> Lit list \<Rightarrow>
   Lit list list \<times> 64 word list \<times> 64 word list \<times> 64 word list\<close> where
  \<open>acw_m db p nx h c \<equiv>
     let s = length nx; p1 = p @ [0, 1]; nx1 = nx @ [- 1, - 1] in
     if 2 \<le> length c then
       let x0 = lidx (c ! 0); nx2 = nx1[s := h ! x0]; h2 = h[x0 := word_of_nat s];
           x1 = lidx (c ! 1); nx3 = nx2[Suc s := h2 ! x1]; h3 = h2[x1 := word_of_nat (Suc s)]
       in (db @ [c], p1, nx3, h3)
     else (db @ [c], p1, nx1, h)\<close>

text \<open>\<^verbatim>\<open>set_pos\<close>.\<close>
definition set_pos_m :: \<open>nat list \<Rightarrow> Lit list \<Rightarrow> nat \<Rightarrow> nat list\<close> where
  \<open>set_pos_m tp t k \<equiv> foldl (\<lambda>tp j. tp[lv (t ! j) := j]) tp [k..<length t]\<close>

lemma sw_pos_max:
  assumes \<open>2 \<le> length c\<close> \<open>m \<le> length c\<close>
  shows \<open>1 \<le> sw_pos tp c m \<and> sw_pos tp c m < length c \<and> (m \<le> 2 \<longrightarrow> sw_pos tp c m = 1) \<and>
         (\<forall>k. 1 \<le> k \<and> k < m \<longrightarrow> tp ! lv (c ! k) \<le> tp ! lv (c ! sw_pos tp c m))\<close>
  using assms(2)
proof (induction m)
  case 0
  then show ?case using assms(1) by (simp add: sw_pos_def)
next
  case (Suc m)
  show ?case
  proof (cases \<open>2 \<le> m\<close>)
    case False
    then have \<open>Suc m \<le> 2\<close> by simp
    then have \<open>[2..<Suc m] = []\<close> by simp
    then have e: \<open>sw_pos tp c (Suc m) = 1\<close> by (simp add: sw_pos_def)
    have \<open>\<forall>k. 1 \<le> k \<and> k < Suc m \<longrightarrow> k = 1\<close> using False by auto
    then show ?thesis using e assms(1) by auto
  next
    case True
    have u: \<open>[2..<Suc m] = [2..<m] @ [m]\<close> using True by simp
    have IH: \<open>1 \<le> sw_pos tp c m\<close> \<open>sw_pos tp c m < length c\<close>
      \<open>\<forall>k. 1 \<le> k \<and> k < m \<longrightarrow> tp ! lv (c ! k) \<le> tp ! lv (c ! sw_pos tp c m)\<close>
      using Suc by auto
    have e: \<open>sw_pos tp c (Suc m) = (if tp ! lv (c ! sw_pos tp c m) < tp ! lv (c ! m) then m else sw_pos tp c m)\<close>
      unfolding sw_pos_def using u by simp
    show ?thesis using IH e Suc.prems True by (auto simp: less_Suc_eq)
  qed
qed

lemma set_swap: \<open>i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> set (xs[i := xs ! j, j := xs ! i]) = set xs\<close>
  by (metis mset_eq_setD mset_swap)

lemma sw_m_facts:
  assumes \<open>2 \<le> length c\<close>
  shows \<open>length (sw_m tp c) = length c \<and> sw_m tp c ! 0 = c ! 0 \<and> set (sw_m tp c) = set c \<and>
         set (tl (sw_m tp c)) = set (tl c) \<and>
         (\<forall>k. 1 \<le> k \<and> k < length c \<longrightarrow> tp ! lv (sw_m tp c ! k) \<le> tp ! lv (sw_m tp c ! 1))\<close>
proof -
  let ?b = \<open>sw_pos tp c (length c)\<close>
  note B = sw_pos_max[OF assms order_refl, of tp]
  let ?c = \<open>c[1 := c ! ?b, ?b := c ! 1]\<close>
  have c: \<open>sw_m tp c = ?c\<close> by (simp add: sw_m_def Let_def)
  have l: \<open>length ?c = length c\<close> by simp
  have z: \<open>?c ! 0 = c ! 0\<close> using B by (simp add: nth_list_update)
  have s: \<open>set ?c = set c\<close> using set_swap[of 1 c ?b] B assms by simp
  have ms: \<open>mset ?c = mset c\<close> using B assms by (simp add: mset_swap)
  have ne: \<open>c \<noteq> []\<close> \<open>?c \<noteq> []\<close> using assms by auto
  have \<open>mset (?c ! 0 # tl ?c) = mset (c ! 0 # tl c)\<close>
    using ms ne by (metis hd_Cons_tl hd_conv_nth)
  then have \<open>mset (tl ?c) = mset (tl c)\<close> using z by simp
  then have s1: \<open>set (tl ?c) = set (tl c)\<close> by (metis set_mset_mset)
  have m: \<open>tp ! lv (?c ! k) \<le> tp ! lv (?c ! 1)\<close> if \<open>1 \<le> k\<close> \<open>k < length c\<close> for k
  proof -
    have one: \<open>?c ! 1 = c ! ?b\<close> using B assms by (cases \<open>?b = 1\<close>) (auto simp: nth_list_update)
    have \<open>?c ! k = c ! k \<or> ?c ! k = c ! 1 \<or> ?c ! k = c ! ?b\<close> using that B by (auto simp: nth_list_update)
    moreover have mx: \<open>\<forall>k'. 1 \<le> k' \<and> k' < length c \<longrightarrow> tp ! lv (c ! k') \<le> tp ! lv (c ! ?b)\<close> using B by blast
    moreover have \<open>1 < length c\<close> using assms by simp
    ultimately show ?thesis using one that by auto
  qed
  show ?thesis using c l z s s1 m by simp
qed

lemma level_of_facts:
  assumes \<open>sorted_wrt (<) L\<close> \<open>L \<noteq> []\<close> \<open>p < last L\<close>
  shows \<open>level_of_m L p < length L \<and> p < L ! level_of_m L p \<and> (\<forall>x \<in> set (take (level_of_m L p) L). x \<le> p)\<close>
proof -
  let ?j = \<open>level_of_m L p\<close>
  have tw: \<open>take ?j L = takeWhile (\<lambda>x. x \<le> p) L\<close> by (metis level_of_m_def takeWhile_eq_take)
  have lt: \<open>?j < length L\<close>
  proof (rule ccontr)
    assume \<open>\<not> ?j < length L\<close>
    then have \<open>?j = length L\<close> using length_takeWhile_le[of _ L] unfolding level_of_m_def by (meson le_antisym not_le)
    then have \<open>takeWhile (\<lambda>x. x \<le> p) L = L\<close> using tw by simp
    then have \<open>\<forall>x \<in> set L. x \<le> p\<close> by (metis set_takeWhileD)
    then show False using assms(2,3) last_in_set[OF assms(2)] by fastforce
  qed
  have \<open>\<not> L ! ?j \<le> p\<close> unfolding level_of_m_def
    by (rule nth_length_takeWhile) (use lt in \<open>simp add: level_of_m_def\<close>)
  moreover have \<open>\<forall>x \<in> set (take ?j L). x \<le> p\<close> using tw by (metis set_takeWhileD)
  ultimately show ?thesis using lt by simp
qed

lemma meas_fewer: \<open>set L2 \<subseteq> set L1 \<Longrightarrow> meas n m L1 \<le> meas n m L2\<close>
  unfolding meas_def by (rule sum_mono) auto

text \<open>A backjump to the decision position \<open>L ! j\<close>, where an implied entry is pushed, increases the
  measure.\<close>
lemma meas_backjump:
  assumes \<open>sorted_wrt (<) L\<close> \<open>j < length L\<close> \<open>L ! j < m\<close> \<open>m \<le> n\<close>
  shows \<open>meas n m L < meas n (Suc (L ! j)) (take j L)\<close>
proof -
  have \<open>set (take j L @ [L ! j]) \<subseteq> set L\<close> using assms(2) by (auto dest: in_set_takeD)
  then have \<open>meas n m L \<le> meas n m (take j L @ [L ! j])\<close> by (rule meas_fewer)
  moreover have \<open>\<forall>q \<in> set (take j L). q < L ! j\<close>
    using assms(1,2) by (auto simp: in_set_conv_nth sorted_wrt_iff_nth_less)
  ultimately show ?thesis using meas_backtrack[of \<open>take j L\<close> \<open>L ! j\<close> m n] assms(3,4) by linarith
qed

subsection \<open>Appending a clause with its watches\<close>

text \<open>Every link of the lists is a slot or the end \<open>2 ^ 64 - 1\<close>.\<close>
definition lends :: \<open>64 word list \<Rightarrow> 64 word list \<Rightarrow> bool\<close> where
  \<open>lends nx h \<equiv> \<forall>y \<in> set nx \<union> set h. unat y < length nx \<or> unat y = 2 ^ 64 - 1\<close>

lemma lseg_app:
  assumes \<open>lseg nx s xs\<close> \<open>s < length nx \<or> s = 2 ^ 64 - 1\<close>
    \<open>\<forall>y \<in> set nx. unat y < length nx \<or> unat y = 2 ^ 64 - 1\<close> \<open>length (nx @ e) \<le> 2 ^ 64 - 1\<close>
  shows \<open>lseg (nx @ e) s xs\<close>
  using assms(1,2)
proof (induction xs arbitrary: s)
  case Nil
  then show ?case using assms(4) by auto
next
  case (Cons y ys)
  have y: \<open>s = y\<close> \<open>y < length nx\<close> \<open>lseg nx (unat (nx ! y)) ys\<close> using Cons.prems(1) by simp_all
  have \<open>unat (nx ! y) < length nx \<or> unat (nx ! y) = 2 ^ 64 - 1\<close> using assms(3) y(2) by simp
  then show ?case using Cons.IH[OF y(3)] y by (simp add: nth_append)
qed

lemma wl_lists_p:
  assumes \<open>wl_lists cs m p nx h Ls\<close> \<open>length p' = length p\<close>
    \<open>\<forall>s. wact cs m s \<longrightarrow> p' ! s = p ! s\<close>
  shows \<open>wl_lists cs m p' nx h Ls\<close>
proof -
  have w: \<open>wlit cs p' s = wlit cs p s\<close> if \<open>wact cs m s\<close> for s using assms(3) that by (simp add: wlit_def)
  have \<open>p' ! (2 * c) = p ! (2 * c) \<and> p' ! Suc (2 * c) = p ! Suc (2 * c)\<close> if \<open>c < m\<close> \<open>2 \<le> length (cs ! c)\<close> for c
    using assms(3) that by (simp add: wact_def)
  then show ?thesis using assms(1,2) w assms(3) unfolding wl_lists_def by auto
qed

lemma wl_lists_app:
  assumes L: \<open>wl_lists db (length db) p nx h Ls\<close> and E: \<open>lends nx h\<close> \<open>length nx + 2 \<le> 2 ^ 64 - 1\<close>
    and e: \<open>length e = 2\<close>
  shows \<open>wl_lists (db @ [c]) (length db) (p @ e) (nx @ [- 1, - 1]) h Ls\<close>
proof -
  have W: \<open>length p = 2 * length db\<close> \<open>length nx = 2 * length db\<close> \<open>length Ls = length h\<close>
    \<open>\<forall>s. wact db (length db) s \<longrightarrow> unat (p ! s) < length (db ! (s div 2)) \<and> lidx (wlit db p s) < length h\<close>
    \<open>\<forall>c < length db. 2 \<le> length (db ! c) \<longrightarrow> p ! (2 * c) \<noteq> p ! Suc (2 * c)\<close>
    \<open>\<forall>x < length h. lseg nx (unat (h ! x)) (Ls ! x) \<and> distinct (Ls ! x) \<and>
        (\<forall>s. s \<in> set (Ls ! x) \<longleftrightarrow> wact db (length db) s \<and> lidx (wlit db p s) = x)\<close>
    using L unfolding wl_lists_def by blast+
  have act: \<open>wact (db @ [c]) (length db) s \<longleftrightarrow> wact db (length db) s\<close> for s
    by (auto simp: wact_def nth_append)
  have wl: \<open>wlit (db @ [c]) (p @ e) s = wlit db p s\<close> if \<open>wact db (length db) s\<close> for s
    using that W(1) by (auto simp: wact_def wlit_def nth_append)
  have pe: \<open>(p @ e) ! s = p ! s\<close> if \<open>s < 2 * length db\<close> for s using that W(1) by (simp add: nth_append)
  have ends: \<open>\<forall>y \<in> set nx. unat y < length nx \<or> unat y = 2 ^ 64 - 1\<close> using E(1) by (simp add: lends_def)
  have ls: \<open>lseg (nx @ [- 1, - 1]) (unat (h ! x)) (Ls ! x)\<close> if \<open>x < length h\<close> for x
  proof -
    have \<open>unat (h ! x) < length nx \<or> unat (h ! x) = 2 ^ 64 - 1\<close> using E(1) that by (simp add: lends_def)
    then show ?thesis using lseg_app[of nx _ _ \<open>[- 1, - 1]\<close>] W(6) that ends E(2) by simp
  qed
  have pos: \<open>\<forall>c' < length db. 2 \<le> length ((db @ [c]) ! c') \<longrightarrow> (p @ e) ! (2 * c') \<noteq> (p @ e) ! Suc (2 * c')\<close>
    using W(5) pe by (simp add: nth_append)
  have \<open>\<forall>s. wact (db @ [c]) (length db) s \<longrightarrow> unat ((p @ e) ! s) < length ((db @ [c]) ! (s div 2)) \<and>
      lidx (wlit (db @ [c]) (p @ e) s) < length h\<close>
    using W(4) act wl pe by (auto simp: wact_def nth_append)
  then show ?thesis using W act wl ls pos e unfolding wl_lists_def by auto
qed

lemma acw_facts:
  assumes \<open>wl_ok db p nx h\<close> \<open>lends nx h\<close> \<open>2 * length db + 4 < 2 ^ 64\<close> \<open>\<forall>l \<in> set c. lidx l < length h\<close>
    \<open>acw_m db p nx h c = (db', p', nx', h')\<close>
  shows \<open>wl_ok db' p' nx' h' \<and> lends nx' h' \<and> length h' = length h \<and> db' = db @ [c] \<and> p' = p @ [0, 1] \<and>
         length nx' = length nx + 2\<close>
proof -
  obtain Ls where L: \<open>wl_lists db (length db) p nx h Ls\<close> using assms(1) by (auto simp: wl_ok_def)
  have lp: \<open>length p = 2 * length db\<close> \<open>length nx = 2 * length db\<close> using L by (simp_all add: wl_lists_def)
  let ?c = \<open>length db\<close>
  let ?s = \<open>length nx\<close>
  have b: \<open>length nx + 2 \<le> 2 ^ 64 - 1\<close> using assms(3) lp by simp
  note L0 = wl_lists_app[OF L assms(2) b, of \<open>[0, 0]\<close> c]
  have L1: \<open>wl_lists (db @ [c]) (length db) (p @ [0, 0]) (nx @ [- 1, - 1]) h Ls\<close> using L0 by simp
  have nl: \<open>length (nx @ [- 1, - 1 :: 64 word]) = ?s + 2\<close> by simp
  have us: \<open>unat (word_of_nat ?s :: 64 word) = ?s\<close> \<open>unat (word_of_nat (Suc ?s) :: 64 word) = Suc ?s\<close>
    using b by (intro unat_of_nat_eq; simp)+
  have E0: \<open>\<forall>y \<in> set nx \<union> set h. unat y < length nx \<or> unat y = 2 ^ 64 - 1\<close> using assms(2) by (simp add: lends_def)
  have m1: \<open>unat (- 1 :: 64 word) = 2 ^ 64 - 1\<close> by (simp add: unat_minus_one_word)
  have E1: \<open>unat y < length nx \<or> unat y = 2 ^ 64 - 1\<close> if \<open>y \<in> set nx \<or> y \<in> set h\<close> for y
    using E0 that by blast
  show ?thesis
  proof (cases \<open>2 \<le> length c\<close>)
    case False
    have r: \<open>db' = db @ [c]\<close> \<open>p' = p @ [0, 1]\<close> \<open>nx' = nx @ [- 1, - 1]\<close> \<open>h' = h\<close>
      using assms(5) False by (auto simp: acw_m_def Let_def)
    have \<open>wl_lists (db @ [c]) (Suc ?c) (p @ [0, 1]) (nx @ [- 1, - 1]) h Ls\<close>
    proof -
      have \<open>wl_lists (db @ [c]) (Suc ?c) (p @ [0, 0]) (nx @ [- 1, - 1]) h Ls\<close>
        using wl_init_short[OF L1] False by simp
      moreover have \<open>wact (db @ [c]) (Suc ?c) s \<Longrightarrow> s < 2 * ?c\<close> for s using False
        by (auto simp: wact_def nth_append less_Suc_eq split: if_splits)
      ultimately show ?thesis using wl_lists_p[of \<open>db @ [c]\<close> \<open>Suc ?c\<close> \<open>p @ [0, 0]\<close>] False lp
        by (auto simp: nth_append less_Suc_eq)
    qed
    moreover have \<open>lends (nx @ [- 1, - 1]) h\<close> unfolding lends_def
    proof
      fix y assume \<open>y \<in> set (nx @ [- 1, - 1]) \<union> set h\<close>
      then have \<open>y \<in> set nx \<or> y \<in> set h \<or> y = - 1\<close> by auto
      then show \<open>unat y < length (nx @ [- 1, - 1]) \<or> unat y = 2 ^ 64 - 1\<close> using E1 m1 by fastforce
    qed
    ultimately show ?thesis using r by (auto simp: wl_ok_def)
  next
    case True
    let ?x0 = \<open>lidx (c ! 0)\<close> and ?x1 = \<open>lidx (c ! 1)\<close>
    have \<open>c ! 0 \<in> set c\<close> \<open>c ! 1 \<in> set c\<close> using True by (auto intro!: nth_mem)
    then have x: \<open>?x0 < length h\<close> \<open>?x1 < length h\<close> using assms(4) by blast+
    have z: \<open>\<forall>s. 2 * ?c \<le> s \<and> s < 2 * length (db @ [c]) \<longrightarrow> (p @ [0, 0]) ! s = 0\<close>
    proof (intro allI impI)
      fix s assume \<open>2 * ?c \<le> s \<and> s < 2 * length (db @ [c])\<close>
      then have \<open>s = 2 * ?c \<or> s = Suc (2 * ?c)\<close> by auto
      then show \<open>(p @ [0, 0]) ! s = 0\<close> using lp by (auto simp: nth_append)
    qed
    have bb: \<open>2 * length (db @ [c]) < 2 ^ 64\<close> using assms(3) by simp
    have x': \<open>lidx ((db @ [c]) ! ?c ! 0) < length h\<close> \<open>lidx ((db @ [c]) ! ?c ! 1) < length h\<close> using x by simp_all
    have cc: \<open>?c < length (db @ [c])\<close> \<open>2 \<le> length ((db @ [c]) ! ?c)\<close> using True by simp_all
    note S = wl_init_step[OF L1 cc z refl refl x' bb]
    have pq: \<open>(p @ [0, 0])[Suc (2 * ?c) := 1] = p @ [0, 1]\<close> using lp by (simp add: list_update_append)
    have r: \<open>db' = db @ [c]\<close> \<open>p' = p @ [0, 1]\<close>
      \<open>nx' = ((nx @ [- 1, - 1])[?s := h ! ?x0])[Suc ?s := (h[?x0 := word_of_nat ?s]) ! ?x1]\<close>
      \<open>h' = (h[?x0 := word_of_nat ?s])[?x1 := word_of_nat (Suc ?s)]\<close>
      using assms(5) True by (auto simp: acw_m_def Let_def)
    have W: \<open>wl_ok db' p' nx' h'\<close> using S True r pq lp unfolding wl_ok_def by (auto simp: nth_append)
    have hs: \<open>set (h[?x0 := word_of_nat ?s]) \<subseteq> insert (word_of_nat ?s) (set h)\<close> by (rule set_update_subset_insert)
    have hs2: \<open>set h' \<subseteq> insert (word_of_nat (Suc ?s)) (insert (word_of_nat ?s) (set h))\<close>
      using r(4) hs set_update_subset_insert by fastforce
    have ns: \<open>set nx' \<subseteq> set nx \<union> {- 1} \<union> set h \<union> insert (word_of_nat ?s) (set h)\<close>
    proof -
      have \<open>set ((nx @ [- 1, - 1])[?s := h ! ?x0]) \<subseteq> insert (h ! ?x0) (set nx \<union> {- 1})\<close>
        using set_update_subset_insert by fastforce
      moreover have \<open>(h[?x0 := word_of_nat ?s]) ! ?x1 \<in> insert (word_of_nat ?s) (set h)\<close>
        using hs x by (metis length_list_update nth_mem subsetD)
      ultimately show ?thesis using r(3) set_update_subset_insert x(1) by fastforce
    qed
    have ln': \<open>length nx' = ?s + 2\<close> using r(3) by simp
    have \<open>lends nx' h'\<close> unfolding lends_def
    proof
      fix y assume \<open>y \<in> set nx' \<union> set h'\<close>
      then have \<open>y \<in> set nx \<union> set h \<or> y = - 1 \<or> y = word_of_nat ?s \<or> y = word_of_nat (Suc ?s)\<close>
        using ns hs2 by blast
      then show \<open>unat y < length nx' \<or> unat y = 2 ^ 64 - 1\<close> using E1 ln' us m1 by fastforce
    qed
    then show ?thesis using W r ln' by simp
  qed
qed

text \<open>The invariants of the watches after a clause is appended with \<open>acw_m\<close>.\<close>
lemma WS_app:
  assumes \<open>length p = 2 * length db\<close> \<open>WS db p t S\<close>
    \<open>2 \<le> length c \<longrightarrow> (lneg (c ! 0) \<in> S \<longrightarrow> c ! 1 \<in> set t) \<and> (lneg (c ! 1) \<in> S \<longrightarrow> c ! 0 \<in> set t)\<close>
  shows \<open>WS (db @ [c]) (p @ [0, 1]) t S\<close>
  unfolding WS_def
proof (intro allI impI)
  fix s assume a: \<open>wact (db @ [c]) (length (db @ [c])) s\<close> and f: \<open>lneg (wlit (db @ [c]) (p @ [0, 1]) s) \<in> S\<close>
  show \<open>wlit (db @ [c]) (p @ [0, 1]) (oth s) \<in> set t\<close>
  proof (cases \<open>s < 2 * length db\<close>)
    case True
    have o: \<open>oth s < 2 * length db\<close> using True by (auto simp: oth_def)
    have w: \<open>wlit (db @ [c]) (p @ [0, 1]) s' = wlit db p s'\<close> if \<open>s' < 2 * length db\<close> for s'
      using that assms(1) by (auto simp: wlit_def nth_append)
    have \<open>s div 2 < length db\<close> using True by linarith
    then have \<open>wact db (length db) s\<close> using a True by (auto simp: wact_def nth_append)
    then show ?thesis using assms(2) f w[OF True] w[OF o] unfolding WS_def by metis
  next
    case False
    then have s: \<open>s = 2 * length db \<or> s = Suc (2 * length db)\<close> using a by (auto simp: wact_def)
    have lc: \<open>2 \<le> length c\<close> using a s by (auto simp: wact_def nth_append)
    have w0: \<open>wlit (db @ [c]) (p @ [0, 1]) (2 * length db) = c ! 0\<close>
      and w1: \<open>wlit (db @ [c]) (p @ [0, 1]) (Suc (2 * length db)) = c ! 1\<close>
      using assms(1) by (simp_all add: wlit_def nth_append)
    have o: \<open>oth (2 * length db) = Suc (2 * length db)\<close> \<open>oth (Suc (2 * length db)) = 2 * length db\<close>
      by (simp_all add: oth_def)
    show ?thesis using s assms(3) lc f w0 w1 o by auto
  qed
qed

lemma SP_app: \<open>SP db t \<Longrightarrow> (length c < 2 \<longrightarrow> (\<exists>l \<in> set c. l \<in> set t)) \<Longrightarrow> SP (db @ [c]) t\<close>
  unfolding SP_def by auto


subsection \<open>The invariant of the search\<close>

text \<open>The state of the search over the clauses \<open>db\<close>, which are the clauses \<open>cs\<close> of the problem
  followed by learned ones that follow from them: the trail \<open>t\<close> with the decision positions \<open>L\<close>
  (\<^const>\<open>dstate\<close>), the reasons \<open>rs\<close> of the implied entries while learning is on (\<open>lr\<close>), the
  trail positions \<open>tp\<close>, and the watches \<open>p\<close>, \<open>nx\<close>, \<open>h\<close> with the invariant at the decision
  positions. It holds at every conflict; \<^const>\<open>wstate\<close> adds the invariant at the propagated
  prefix of the trail.\<close>
definition cinv ::
  \<open>Lit list list \<Rightarrow> nat \<Rightarrow> Lit list list \<Rightarrow> bool option list \<Rightarrow> Lit list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
   nat list \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> bool \<Rightarrow> bool\<close> where
  \<open>cinv cs n db a t rs tp L p nx h lr \<equiv>
     (\<exists>ls. db = cs @ ls) \<and> dpll_wf n db \<and> (\<forall>\<sigma>. cnf_sem \<sigma> cs \<longrightarrow> cnf_sem \<sigma> db) \<and>
     0 < length db \<and> length db < 2 ^ 62 \<and>
     dstate db n a t L \<and> length rs = length t \<and> (\<forall>j < length t. rs ! j < length db) \<and>
     (lr \<longrightarrow> (\<forall>j < length t. j \<notin> set L \<longrightarrow> reason db t j (rs ! j))) \<and>
     tpos t tp \<and> length tp = n \<and> lends nx h \<and> length h = 2 * n \<and>
     wl_ok db p nx h \<and> SP db t \<and> (\<forall>k \<in> set L. k \<le> length t \<and> WP db p t k \<and> SP db (take k t))\<close>

lemma tr_imp_mono: \<open>(\<forall>\<sigma>. cnf_sem \<sigma> db' \<longrightarrow> cnf_sem \<sigma> db) \<Longrightarrow> tr_imp db t j \<Longrightarrow> tr_imp db' t j\<close>
  unfolding tr_imp_def by blast

lemma reason_imp: \<open>reason db t j r \<Longrightarrow> tr_imp db t j\<close>
  unfolding tr_imp_def
proof (intro allI impI)
  fix \<sigma> assume r: \<open>reason db t j r\<close> and m: \<open>cnf_sem \<sigma> db \<and> (\<forall>k < j. lit_sem \<sigma> (t ! k))\<close>
  have \<open>db ! r \<in> set db\<close> using r by (simp add: reason_def)
  then obtain l where l: \<open>l \<in> set (db ! r)\<close> \<open>lit_sem \<sigma> l\<close> using m unfolding cnf_sem_def by blast
  show \<open>lit_sem \<sigma> (t ! j)\<close>
  proof (rule ccontr)
    assume n: \<open>\<not> lit_sem \<sigma> (t ! j)\<close>
    then have \<open>l \<noteq> t ! j\<close> using l(2) by blast
    then obtain k where \<open>k < j\<close> \<open>t ! k = lneg l\<close> using r l(1) by (auto simp: reason_def)
    then show False using m l(2) cdcl_lit_sem_lneg by metis
  qed
qed

lemma cnf_sem_app: \<open>cnf_sem \<sigma> (cs @ ls) \<Longrightarrow> cnf_sem \<sigma> cs\<close>
  by (simp add: cnf_sem_def)

lemma sorted_last: \<open>sorted_wrt (<) L \<Longrightarrow> x \<in> set L \<Longrightarrow> x \<le> last L\<close> for L :: \<open>nat list\<close>
proof -
  assume a: \<open>sorted_wrt (<) L\<close> \<open>x \<in> set L\<close>
  then obtain i where i: \<open>i < length L\<close> \<open>L ! i = x\<close> by (auto simp: in_set_conv_nth)
  have ne: \<open>L \<noteq> []\<close> using a(2) by auto
  have l: \<open>last L = L ! (length L - 1)\<close> using last_conv_nth[OF ne] .
  show ?thesis
  proof (cases \<open>i = length L - 1\<close>)
    case False
    then have \<open>i < length L - 1\<close> using i(1) by simp
    then show ?thesis using sorted_wrt_nth_less[OF a(1)] i l by fastforce
  qed (use i l in simp)
qed

lemma sorted_take_lt: \<open>sorted_wrt (<) L \<Longrightarrow> j < length L \<Longrightarrow> x \<in> set (take j L) \<Longrightarrow> x < L ! j\<close> for L :: \<open>nat list\<close>
  by (auto simp: in_set_conv_nth sorted_wrt_iff_nth_less)

lemma sorted_lt_take: \<open>sorted_wrt (<) L \<Longrightarrow> j < length L \<Longrightarrow> x \<in> set L \<Longrightarrow> x < L ! j \<Longrightarrow> x \<in> set (take j L)\<close>
  for L :: \<open>nat list\<close>
proof -
  assume a: \<open>sorted_wrt (<) L\<close> \<open>j < length L\<close> \<open>x \<in> set L\<close> \<open>x < L ! j\<close>
  then obtain i where i: \<open>i < length L\<close> \<open>L ! i = x\<close> by (auto simp: in_set_conv_nth)
  have \<open>i < j\<close>
  proof (rule ccontr)
    assume \<open>\<not> i < j\<close>
    then have \<open>j = i \<or> j < i\<close> by auto
    then have \<open>L ! j \<le> L ! i\<close>
    proof
      assume \<open>j < i\<close>
      then show ?thesis using sorted_wrt_nth_less[OF a(1) _ i(1)] by fastforce
    qed simp
    then show False using a(4) i(2) by simp
  qed
  then show ?thesis using i a(2) by (auto simp: in_set_conv_nth)
qed

text \<open>The backjump after a conflict of the clause \<open>cf\<close> (all its literals false) at a decision
  level above 0, with learning on: the analysis learns a clause \<open>C\<close>; its literal of the highest
  trail position after the first is moved to position 1 (if it has two literals); the search
  returns to the decision position \<open>L ! j\<close> of the level of that literal (\<open>j = 0\<close> for a unit
  clause), where the first literal of the clause is implied with the new clause as its reason.\<close>
theorem cinv_backjump:
  assumes I: \<open>cinv cs n db a t rs tp L p nx h True\<close> and L: \<open>L \<noteq> []\<close>
    and cf: \<open>cf < length db\<close> \<open>\<forall>l \<in> set (db ! cf). lneg l \<in> set t\<close>
    and sz: \<open>length db < 2 ^ 62 - 1\<close>
    and A: \<open>analyze_m db t rs tp (last L) (replicate n False) cf = (C, sn, True)\<close>
    and C2: \<open>C2 = (if 2 \<le> length C then sw_m tp C else C)\<close>
    and j: \<open>j = (if 2 \<le> length C then level_of_m L (tp ! lv (C2 ! 1)) else 0)\<close>
    and a2: \<open>tr_ok n a2 (take (L ! j) t)\<close>
    and W: \<open>acw_m db p nx h C2 = (db', p', nx', h')\<close>
  shows \<open>sn = replicate n False \<and> j < length L \<and> db' = db @ [C2] \<and> C2 \<noteq> [] \<and>
    cinv cs n db' (a2[lv (hd C2) := Some (\<not> Lit_neg (hd C2))]) (take (L ! j) t @ [hd C2])
      (take (L ! j) rs @ [length db]) (tp[lv (hd C2) := L ! j]) (take j L) p' nx' h' True \<and>
    wstate db' p' nx' h' (take (L ! j) t @ [hd C2]) (L ! j) (take j L) \<and>
    meas n (length t) L < meas n (Suc (L ! j)) (take j L)\<close>
proof -
  have D: \<open>\<exists>ls. db = cs @ ls\<close> \<open>dpll_wf n db\<close> \<open>\<forall>\<sigma>. cnf_sem \<sigma> cs \<longrightarrow> cnf_sem \<sigma> db\<close> \<open>0 < length db\<close>
    \<open>dstate db n a t L\<close> \<open>length rs = length t\<close> \<open>\<forall>j < length t. rs ! j < length db\<close>
    \<open>\<forall>j < length t. j \<notin> set L \<longrightarrow> reason db t j (rs ! j)\<close>
    \<open>tpos t tp\<close> \<open>length tp = n\<close> \<open>lends nx h\<close> \<open>length h = 2 * n\<close> \<open>wl_ok db p nx h\<close> \<open>SP db t\<close>
    \<open>\<forall>k \<in> set L. k \<le> length t \<and> WP db p t k \<and> SP db (take k t)\<close>
    using I by (simp_all add: cinv_def)
  have DS: \<open>tr_ok n a t\<close> \<open>sorted_wrt (<) L\<close> \<open>\<forall>q \<in> set L. q < length t\<close>
    \<open>\<forall>j < length t. j \<notin> set L \<longrightarrow> tr_imp db t j\<close>
    using D(5) by (simp_all add: dstate_def)
  interpret atrail n a t tp using DS(1) D(9) by unfold_locales
  let ?st = \<open>last L\<close>
  have stL: \<open>?st \<in> set L\<close> using L by simp
  have st: \<open>?st < length t\<close> using DS(3) stL by blast
  have Lst: \<open>\<forall>x \<in> set L. x \<le> ?st\<close> using sorted_last[OF DS(2)] by blast
  have rsn: \<open>\<forall>j. ?st < j \<and> j < length t \<longrightarrow> reason db t j (rs ! j)\<close>
    using D(8) Lst by (meson leD)
  have cfl: \<open>\<forall>l \<in> set (db ! cf). \<exists>j < length t. t ! j = lneg l\<close>
    using cf(2) by (metis in_set_conv_nth)
  note AN = analyze_ok[OF D(2) less_imp_le[OF st] rsn cf(1) cfl A]
  obtain u where u: \<open>?st \<le> u\<close> \<open>u < length t\<close> \<open>hd C = lneg (t ! u)\<close> using AN by blast
  have Cne: \<open>C \<noteq> []\<close> and Clow: \<open>\<forall>l \<in> set (tl C). \<exists>j < ?st. j < length t \<and> t ! j = lneg l\<close>
    and Cent: \<open>\<forall>\<sigma>. cnf_sem \<sigma> db \<longrightarrow> (\<exists>l \<in> set C. lit_sem \<sigma> l)\<close> using AN by auto
  have C2f: \<open>C2 \<noteq> [] \<and> hd C2 = hd C \<and> set C2 = set C \<and> set (tl C2) = set (tl C) \<and> length C2 = length C\<close>
  proof (cases \<open>2 \<le> length C\<close>)
    case True
    note F = sw_m_facts[OF True, of tp]
    have \<open>hd (sw_m tp C) = hd C\<close> using F True by (metis hd_conv_nth list.size(3) not_numeral_le_zero)
    then show ?thesis using F C2 True Cne by auto
  qed (use C2 Cne in simp)
  let ?d = \<open>hd C2\<close>
  have d: \<open>?d = lneg (t ! u)\<close> using C2f u(3) by simp
  have C2d: \<open>C2 = ?d # tl C2\<close> using C2f list.collapse by metis
  have C2low: \<open>\<forall>l \<in> set (tl C2). \<exists>j < ?st. j < length t \<and> t ! j = lneg l\<close> using Clow C2f by simp
  \<comment> \<open>The level of the backjump.\<close>
  have J: \<open>j < length L \<and> (\<forall>l \<in> set (tl C2). \<exists>jl < L ! j. t ! jl = lneg l) \<and>
           (2 \<le> length C2 \<longrightarrow> (\<exists>mp. t ! mp = lneg (C2 ! 1) \<and> mp < length t \<and> (\<forall>x \<in> set (take j L). x \<le> mp)))\<close>
  proof (cases \<open>2 \<le> length C\<close>)
    case True
    note F = sw_m_facts[OF True, of tp]
    have c2: \<open>C2 = sw_m tp C\<close> using C2 True by simp
    have \<open>0 < length (tl C2)\<close> using True C2f by simp
    then have \<open>tl C2 ! 0 \<in> set (tl C2)\<close> by (rule nth_mem)
    moreover have \<open>tl C2 ! 0 = C2 ! 1\<close> using \<open>0 < length (tl C2)\<close> by (simp add: nth_tl)
    ultimately have \<open>C2 ! 1 \<in> set (tl C2)\<close> by metis
    then obtain j1 where j1: \<open>j1 < ?st\<close> \<open>j1 < length t\<close> \<open>t ! j1 = lneg (C2 ! 1)\<close> using C2low by blast
    have tp1: \<open>tp ! lv (C2 ! 1) = j1\<close> using tp_at[OF j1(2)] j1(3) by (simp add: lv_lneg)
    have jj: \<open>j = level_of_m L j1\<close> using j True tp1 by simp
    note LV = level_of_facts[OF DS(2) L, of j1] j1(1)
    have lowj: \<open>\<exists>jl < L ! j. t ! jl = lneg l\<close> if hl: \<open>l \<in> set (tl C2)\<close> for l
    proof -
      obtain jl where jl: \<open>jl < ?st\<close> \<open>jl < length t\<close> \<open>t ! jl = lneg l\<close> using bspec[OF C2low hl] by blast
      obtain k' where k': \<open>k' < length (tl C2)\<close> \<open>tl C2 ! k' = l\<close> using hl by (auto simp: in_set_conv_nth)
      have k: \<open>1 \<le> Suc k'\<close> \<open>Suc k' < length C2\<close> \<open>C2 ! Suc k' = l\<close> using k' by (auto simp: nth_tl)
      have \<open>tp ! lv l \<le> tp ! lv (C2 ! 1)\<close> using F k c2 by (metis (no_types, lifting))
      moreover have \<open>tp ! lv l = jl\<close> using tp_at[OF jl(2)] jl(3) by (simp add: lv_lneg)
      ultimately have \<open>jl \<le> j1\<close> using tp1 by simp
      then have \<open>jl < L ! j\<close> using LV jj by simp
      then show ?thesis using jl(3) by blast
    qed
    show ?thesis using LV jj lowj j1 C2f True by auto
  next
    case False
    have \<open>0 < length C\<close> using Cne by simp
    then have \<open>length C = 1\<close> using False by linarith
    then have \<open>length (tl C2) = 0\<close> using C2f by simp
    then have \<open>tl C2 = []\<close> by (simp only: length_0_conv)
    moreover have \<open>j = 0\<close> using j False by simp
    ultimately show ?thesis using L C2f False by simp
  qed
  let ?pp = \<open>L ! j\<close>
  have ppL: \<open>?pp \<in> set L\<close> using J by simp
  have pst: \<open>?pp \<le> ?st\<close> using Lst ppL by blast
  have ppt: \<open>?pp < length t\<close> using DS(3) ppL by blast
  have up: \<open>?pp \<le> u\<close> using pst u(1) by simp
  have takeL: \<open>\<forall>x \<in> set (take j L). x < ?pp\<close> using sorted_take_lt[OF DS(2)] J by blast
  have Ltake: \<open>x \<in> set (take j L)\<close> if \<open>x \<in> set L\<close> \<open>x < ?pp\<close> for x
    using sorted_lt_take[OF DS(2)] J that by blast
  have lowpp: \<open>\<forall>l \<in> set (tl C2). \<exists>jl < ?pp. t ! jl = lneg l\<close> using J by blast
  let ?t' = \<open>take ?pp t @ [?d]\<close>
  let ?a' = \<open>a2[lv ?d := Some (\<not> Lit_neg ?d)]\<close>
  let ?rs' = \<open>take ?pp rs @ [length db]\<close>
  let ?tp' = \<open>tp[lv ?d := ?pp]\<close>
  let ?L' = \<open>take j L\<close>
  have lt': \<open>length ?t' = Suc ?pp\<close> using ppt by simp
  have t'k: \<open>?t' ! k = t ! k\<close> if \<open>k < ?pp\<close> for k using that ppt by (simp add: nth_append)
  have t'pp: \<open>?t' ! ?pp = ?d\<close> using ppt by (simp add: nth_append)
  have vd: \<open>lv ?d = lv (t ! u)\<close> using d by (simp add: lv_lneg)
  have vdn: \<open>lv ?d < n\<close> using vd var_lt[OF u(2)] by simp
  have vne: \<open>lv (t ! k) \<noteq> lv ?d\<close> if \<open>k < ?pp\<close> for k using var_inj[of k u] that vd up ppt u(2) by force
  \<comment> \<open>The clauses.\<close>
  have lits: \<open>\<forall>l \<in> set C2. lv l < n\<close>
  proof
    fix l assume l: \<open>l \<in> set C2\<close>
    show \<open>lv l < n\<close>
    proof (cases \<open>l = ?d\<close>)
      case False
      then have \<open>l \<in> set (tl C2)\<close> using l C2d by (metis set_ConsD)
      then obtain jl where \<open>jl < ?st\<close> \<open>jl < length t\<close> \<open>t ! jl = lneg l\<close> using C2low by blast
      then show ?thesis using var_lt by (metis lv_lneg)
    qed (use vdn in simp)
  qed
  have lidx: \<open>\<forall>l \<in> set C2. lidx l < length h\<close> using lits D(12) by (auto simp: lidx_def)
  have sz4: \<open>2 * length db + 4 < 2 ^ 64\<close> using sz by simp
  note AW = acw_facts[OF D(13,11) sz4 lidx W]
  have db': \<open>db' = db @ [C2]\<close> and p': \<open>p' = p @ [0, 1]\<close> using AW by simp_all
  have lp: \<open>length p = 2 * length db\<close>
    using D(13) by (auto simp: wl_ok_def wl_lists_def)
  have ent': \<open>\<forall>\<sigma>. cnf_sem \<sigma> cs \<longrightarrow> cnf_sem \<sigma> db'\<close>
  proof (intro allI impI)
    fix \<sigma> assume \<open>cnf_sem \<sigma> cs\<close>
    then have m: \<open>cnf_sem \<sigma> db\<close> using D(3) by blast
    then have \<open>\<exists>l \<in> set C2. lit_sem \<sigma> l\<close> using Cent C2f by simp
    then show \<open>cnf_sem \<sigma> db'\<close> using m db' by (simp add: cnf_sem_def)
  qed
  have bk: \<open>\<forall>\<sigma>. cnf_sem \<sigma> db' \<longrightarrow> cnf_sem \<sigma> db\<close> using db' cnf_sem_app by blast
  have wf': \<open>dpll_wf n db'\<close> using D(2) lits db' by (simp add: dpll_wf_def lits_lt_def)
  have dbapp: \<open>\<exists>ls. db' = cs @ ls\<close> using D(1) db' by auto
  \<comment> \<open>The trail.\<close>
  have none: \<open>a2 ! lv ?d = None\<close>
  proof (rule ccontr)
    assume \<open>a2 ! lv ?d \<noteq> None\<close>
    then obtain l where l: \<open>l \<in> set (take ?pp t)\<close> \<open>lv l = lv ?d\<close> using a2 vdn by (auto simp: tr_ok_def)
    then obtain k where \<open>k < ?pp\<close> \<open>t ! k = l\<close> using ppt by (auto simp: in_set_conv_nth)
    then show False using vne l(2) by blast
  qed
  have tr': \<open>tr_ok n ?a' ?t'\<close> using tr_ok_push[OF a2 vdn none] by simp
  have imp_new: \<open>tr_imp db' ?t' ?pp\<close>
    unfolding tr_imp_def
  proof (intro allI impI)
    fix \<sigma> assume m: \<open>cnf_sem \<sigma> db' \<and> (\<forall>k < ?pp. lit_sem \<sigma> (?t' ! k))\<close>
    have \<open>C2 \<in> set db'\<close> using db' by simp
    then obtain l where l: \<open>l \<in> set C2\<close> \<open>lit_sem \<sigma> l\<close> using m unfolding cnf_sem_def by blast
    show \<open>lit_sem \<sigma> (?t' ! ?pp)\<close>
    proof (cases \<open>l = ?d\<close>)
      case False
      then have \<open>l \<in> set (tl C2)\<close> using l(1) C2d by (metis set_ConsD)
      then obtain jl where \<open>jl < ?pp\<close> \<open>t ! jl = lneg l\<close> using lowpp by blast
      then have \<open>lit_sem \<sigma> (lneg l)\<close> using m t'k by metis
      then show ?thesis using l(2) cdcl_lit_sem_lneg by simp
    qed (use l t'pp in simp)
  qed
  have imp': \<open>\<forall>k < length ?t'. k \<notin> set ?L' \<longrightarrow> tr_imp db' ?t' k\<close>
  proof (intro allI impI)
    fix k assume k: \<open>k < length ?t'\<close> \<open>k \<notin> set ?L'\<close>
    show \<open>tr_imp db' ?t' k\<close>
    proof (cases \<open>k = ?pp\<close>)
      case False
      then have kp: \<open>k < ?pp\<close> using k(1) lt' by simp
      then have \<open>k \<notin> set L\<close> using Ltake k(2) by blast
      then have \<open>tr_imp db t k\<close> using DS(4) kp ppt by simp
      moreover have \<open>t = take ?pp t @ drop ?pp t\<close> by simp
      ultimately have \<open>tr_imp db (take ?pp t) k\<close> using tr_imp_append[of k \<open>take ?pp t\<close> db \<open>drop ?pp t\<close>] kp ppt by simp
      then have \<open>tr_imp db ?t' k\<close> using tr_imp_append[of k \<open>take ?pp t\<close> db \<open>[?d]\<close>] kp ppt by simp
      then show ?thesis using tr_imp_mono[OF bk] by blast
    qed (use imp_new in simp)
  qed
  have sortedL': \<open>sorted_wrt (<) ?L'\<close> using DS(2) by (metis sorted_wrt_take)
  have L't: \<open>\<forall>x \<in> set ?L'. x < length ?t'\<close> using takeL lt' by auto
  have ds': \<open>dstate db' n ?a' ?t' ?L'\<close> using tr' sortedL' L't imp' by (simp add: dstate_def)
  \<comment> \<open>Reasons and positions.\<close>
  have rsl: \<open>length ?rs' = length ?t'\<close> using D(6) ppt by simp
  have rs'k: \<open>?rs' ! k = rs ! k\<close> if \<open>k < ?pp\<close> for k using that D(6) ppt by (simp add: nth_append)
  have rs'pp: \<open>?rs' ! ?pp = length db\<close> using D(6) ppt by (simp add: nth_append)
  have rslt: \<open>\<forall>k < length ?t'. ?rs' ! k < length db'\<close>
  proof (intro allI impI)
    fix k assume \<open>k < length ?t'\<close>
    then have \<open>k < ?pp \<or> k = ?pp\<close> using lt' by auto
    then show \<open>?rs' ! k < length db'\<close>
    proof
      assume kp: \<open>k < ?pp\<close>
      then have \<open>k < length t\<close> using ppt by simp
      then have \<open>rs ! k < length db\<close> using D(7) by blast
      then show ?thesis using rs'k[OF kp] db' by simp
    qed (use rs'pp db' in simp)
  qed
  have rsn': \<open>\<forall>k < length ?t'. k \<notin> set ?L' \<longrightarrow> reason db' ?t' k (?rs' ! k)\<close>
  proof (intro allI impI)
    fix k assume k: \<open>k < length ?t'\<close> \<open>k \<notin> set ?L'\<close>
    show \<open>reason db' ?t' k (?rs' ! k)\<close>
    proof (cases \<open>k = ?pp\<close>)
      case True
      have \<open>db' ! length db = C2\<close> using db' by simp
      moreover have \<open>\<forall>l \<in> set C2. l \<noteq> ?d \<longrightarrow> (\<exists>k' < ?pp. ?t' ! k' = lneg l)\<close>
        using lowpp C2d t'k by (metis set_ConsD)
      ultimately show ?thesis using True rs'pp t'pp db' C2d by (auto simp: reason_def) (metis list.set_intros(1))
    next
      case False
      then have kp: \<open>k < ?pp\<close> using k(1) lt' by simp
      then have \<open>k \<notin> set L\<close> using Ltake k(2) by blast
      then have R: \<open>reason db t k (rs ! k)\<close> using D(8) kp ppt by simp
      have e: \<open>db' ! (rs ! k) = db ! (rs ! k)\<close> using R db' by (simp add: reason_def nth_append)
      have e2: \<open>\<forall>k' < k. ?t' ! k' = t ! k'\<close> using t'k kp by simp
      have R': \<open>rs ! k < length db\<close> \<open>t ! k \<in> set (db ! (rs ! k))\<close>
        \<open>\<forall>l \<in> set (db ! (rs ! k)). l \<noteq> t ! k \<longrightarrow> (\<exists>k' < k. t ! k' = lneg l)\<close> using R by (simp_all add: reason_def)
      show ?thesis unfolding reason_def rs'k[OF kp] t'k[OF kp] e
      proof (intro conjI ballI impI)
        show \<open>rs ! k < length db'\<close> using R'(1) db' by simp
        show \<open>t ! k \<in> set (db ! (rs ! k))\<close> using R'(2) .
        fix l assume \<open>l \<in> set (db ! (rs ! k))\<close> \<open>l \<noteq> t ! k\<close>
        then obtain k' where \<open>k' < k\<close> \<open>t ! k' = lneg l\<close> using R'(3) by blast
        then show \<open>\<exists>k' < k. ?t' ! k' = lneg l\<close> using e2 by metis
      qed
    qed
  qed
  have tpos': \<open>tpos ?t' ?tp'\<close> unfolding tpos_def
  proof (intro allI impI)
    fix k assume \<open>k < length ?t'\<close>
    then have \<open>k < ?pp \<or> k = ?pp\<close> using lt' by auto
    then show \<open>lv (?t' ! k) < length ?tp' \<and> ?tp' ! lv (?t' ! k) = k\<close>
    proof
      assume kp: \<open>k < ?pp\<close>
      then show ?thesis using t'k[OF kp] vne[OF kp] tp_at[of k] P ppt by (simp add: tpos_def)
    qed (use t'pp vdn D(10) in simp)
  qed
  \<comment> \<open>The watches.\<close>
  have notd: \<open>t ! u \<notin> set (take k t)\<close> if \<open>k \<le> ?pp\<close> for k using notin_prefix[OF u(2)] that up by simp
  have WPpp: \<open>WP db p t ?pp\<close> \<open>SP db (take ?pp t)\<close> using D(15) ppL by auto
  have wsnew: \<open>2 \<le> length C2 \<longrightarrow> (lneg (C2 ! 0) \<in> set (take ?pp t) \<longrightarrow> C2 ! 1 \<in> set ?t') \<and>
                 (lneg (C2 ! 1) \<in> set (take ?pp t) \<longrightarrow> C2 ! 0 \<in> set ?t')\<close>
  proof
    assume \<open>2 \<le> length C2\<close>
    have \<open>C2 ! 0 = ?d\<close> using C2d by (metis nth_Cons_0)
    then have \<open>lneg (C2 ! 0) \<notin> set (take ?pp t)\<close> using d notd[of ?pp] by (simp add: lneg_lneg)
    moreover have \<open>C2 ! 0 \<in> set ?t'\<close> using \<open>C2 ! 0 = ?d\<close> by simp
    ultimately show \<open>(lneg (C2 ! 0) \<in> set (take ?pp t) \<longrightarrow> C2 ! 1 \<in> set ?t') \<and>
                 (lneg (C2 ! 1) \<in> set (take ?pp t) \<longrightarrow> C2 ! 0 \<in> set ?t')\<close> by blast
  qed
  have tk: \<open>take ?pp ?t' = take ?pp t\<close> using ppt by simp
  have sub: \<open>set (take ?pp t) \<subseteq> set ?t'\<close> by auto
  have WS1: \<open>WS db p ?t' (set (take ?pp t))\<close>
    using WPpp(1) WS_mono[OF _ sub] by (simp add: WP_def)
  have WS': \<open>WS db' p' ?t' (set (take ?pp ?t'))\<close>
    using WS_app[OF lp WS1 wsnew] db' p' tk by simp
  have SP': \<open>SP db' ?t'\<close>
  proof -
    have \<open>SP db ?t'\<close> using SP_mono[OF WPpp(2) sub] .
    moreover have \<open>length C2 < 2 \<longrightarrow> (\<exists>l \<in> set C2. l \<in> set ?t')\<close> using C2d by (metis list.set_intros(1) rotate1.simps(2) set_append set_rotate1 Un_iff)
    ultimately show ?thesis using SP_app db' by blast
  qed
  have LL': \<open>\<forall>k \<in> set ?L'. k \<le> length ?t' \<and> WP db' p' ?t' k \<and> SP db' (take k ?t')\<close>
  proof
    fix k assume k: \<open>k \<in> set ?L'\<close>
    have kp: \<open>k < ?pp\<close> using takeL k by blast
    have kL: \<open>k \<in> set L\<close> using k by (meson in_set_takeD)
    have tk': \<open>take k ?t' = take k t\<close> using kp ppt by simp
    have W0: \<open>WP db p t k\<close> \<open>SP db (take k t)\<close> using D(15) kL by auto
    have long: \<open>2 \<le> length C2\<close>
    proof (rule ccontr)
      assume \<open>\<not> 2 \<le> length C2\<close>
      then have \<open>j = 0\<close> using j C2f by simp
      then show False using k by simp
    qed
    obtain mp where mp: \<open>t ! mp = lneg (C2 ! 1)\<close> \<open>mp < length t\<close> \<open>\<forall>x \<in> set (take j L). x \<le> mp\<close>
      using J long by blast
    have km: \<open>k \<le> mp\<close> using mp(3) k by blast
    have n1: \<open>lneg (C2 ! 1) \<notin> set (take k t)\<close> using notin_prefix[OF mp(2) km] mp(1) by simp
    have \<open>C2 ! 0 = ?d\<close> using C2d by (metis nth_Cons_0)
    then have n0: \<open>lneg (C2 ! 0) \<notin> set (take k t)\<close> using d notd[of k] kp by (simp add: lneg_lneg)
    have \<open>WS db p (take k t) (set (take k t))\<close> using W0(1) by (simp add: WP_def)
    then have \<open>WS db' p' (take k t) (set (take k t))\<close> using WS_app[OF lp] n0 n1 db' p' by blast
    then have \<open>WP db' p' ?t' k\<close> using tk' by (simp add: WP_def)
    moreover have \<open>SP db' (take k ?t')\<close> using SP_app[OF W0(2)] long db' tk' by simp
    ultimately show \<open>k \<le> length ?t' \<and> WP db' p' ?t' k \<and> SP db' (take k ?t')\<close> using kp lt' by simp
  qed
  have ws': \<open>wstate db' p' nx' h' ?t' ?pp ?L'\<close>
    unfolding wstate_def using AW WS' SP' LL' takeL lt' by auto
  \<comment> \<open>The measure.\<close>
  have \<open>length t \<le> n\<close> using tr_ok_length[OF DS(1)] .
  then have meas: \<open>meas n (length t) L < meas n (Suc ?pp) ?L'\<close>
    using meas_backjump[OF DS(2)] J ppt by blast
  have ci: \<open>cinv cs n db' ?a' ?t' ?rs' ?tp' ?L' p' nx' h' True\<close>
    unfolding cinv_def using dbapp wf' ent' db' sz ds' rsl rslt rsn' tpos' D(10,12) AW SP' LL' by auto
  show ?thesis using AN ci ws' meas J db' C2f by simp
qed

end
