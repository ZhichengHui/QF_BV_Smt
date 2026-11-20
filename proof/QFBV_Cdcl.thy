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


lemma cdcl_lit_sem_lneg: \<open>lit_sem \<sigma> (lneg l) = (\<not> lit_sem \<sigma> l)\<close>
  by (simp add: lit_sem_def lneg_def)

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

end

end
