theory BVSmt_Dpll
  imports BVSmt_Defs
begin

section \<open>DPLL: pure facts\<close>

text \<open>The number of unassigned variables of a partial assignment.\<close>
definition dpll_nnone :: \<open>bool option list \<Rightarrow> nat\<close> where
  \<open>dpll_nnone a \<equiv> length (filter (\<lambda>x. x = None) a)\<close>

text \<open>Every clause mentions only variables below \<open>n\<close>.\<close>
definition dpll_wf :: \<open>nat \<Rightarrow> Lit list list \<Rightarrow> bool\<close> where
  \<open>dpll_wf n cs \<equiv> \<forall>c \<in> set cs. lits_lt n c\<close>

text \<open>No clause is in conflict or unit under \<open>a\<close>.\<close>
definition dpll_quiet :: \<open>bool option list \<Rightarrow> Lit list list \<Rightarrow> bool\<close> where
  \<open>dpll_quiet a cs \<equiv>
     \<forall>c \<in> set cs. status_m a c None False \<noteq> Status_Conflict \<and> (\<forall>l. status_m a c None False \<noteq> Status_Unit l)\<close>

lemma dpll_unat_Suc:
  fixes x :: \<open>64 word\<close>
  assumes \<open>unat x < 18446744073709551615\<close>
  shows \<open>unat (x + 1) = Suc (unat x)\<close>
  using assms by (metis Suc_eq_plus1 add.commute unatSuc2 unat_minus_one_word word_less_nat_alt
      unsigned_less linorder_neq_iff word_of_nat_less)

lemma dpll_nnone_le: \<open>dpll_nnone a \<le> length a\<close>
  by (simp add: dpll_nnone_def)

lemma dpll_nnone_upd:
  \<open>i < length a \<Longrightarrow> a ! i = None \<Longrightarrow> dpll_nnone (a[i := Some b]) < dpll_nnone a\<close>
  by (induction a arbitrary: i) (auto simp: dpll_nnone_def split: nat.splits)

lemma dpll_nnone_fuel: \<open>Suc (Suc (length a)) \<le> n \<Longrightarrow> dpll_nnone a < n\<close>
  using dpll_nnone_le[of a] by simp

lemma dpll_nnone_branch:
  \<open>i < length x \<Longrightarrow> x ! i = None \<Longrightarrow> dpll_nnone x < Suc k \<Longrightarrow> dpll_nnone (x[i := Some b]) < k\<close>
  using dpll_nnone_upd[of i x b] by simp

lemma dpll_nnone_zero:
  \<open>dpll_nnone a = 0 \<longleftrightarrow> (\<forall>v < length a. a ! v \<noteq> None)\<close>
  by (auto simp: dpll_nnone_def filter_empty_conv in_set_conv_nth)

lemma dpll_status_drop:
  \<open>i < length c \<Longrightarrow> status_m a (drop i c) u op =
     (case lit_value_m a (c ! i) of
        Some True \<Rightarrow> Status_Satisfied
      | Some False \<Rightarrow> status_m a (drop (Suc i) c) u op
      | None \<Rightarrow> (if u \<noteq> None then status_m a (drop (Suc i) c) u True
                 else status_m a (drop (Suc i) c) (Some (c ! i)) op))\<close>
  by (simp add: Cons_nth_drop_Suc[symmetric])

lemma dpll_pass_drop:
  \<open>i < length cs \<Longrightarrow> pass_m (drop i cs) a ch =
     (case status_m a (cs ! i) None False of
        Status_Conflict \<Rightarrow> None
      | Status_Unit l \<Rightarrow> pass_m (drop (Suc i) cs) (a[unat (Lit_var l) := Some (\<not> Lit_neg l)]) True
      | Status_Satisfied \<Rightarrow> pass_m (drop (Suc i) cs) a ch
      | Status_Open \<Rightarrow> pass_m (drop (Suc i) cs) a ch)\<close>
  by (simp add: Cons_nth_drop_Suc[symmetric])

lemma dpll_status_Sat:
  \<open>status_m a ls u op = Status_Satisfied \<Longrightarrow> \<exists>l \<in> set ls. lit_value_m a l = Some True\<close>
  by (induction a ls u op rule: status_m.induct) (auto split: option.splits bool.splits if_splits)

lemma dpll_status_Conflict:
  \<open>status_m a ls u op = Status_Conflict \<Longrightarrow> u = None \<and> \<not> op \<and> (\<forall>l \<in> set ls. lit_value_m a l = Some False)\<close>
  by (induction a ls u op rule: status_m.induct) (auto split: option.splits bool.splits if_splits)

lemma dpll_status_opT:
  \<open>status_m a ls u True \<noteq> Status_Conflict \<and> status_m a ls u True \<noteq> Status_Unit l\<close>
  by (induction ls arbitrary: u) (auto split: option.splits bool.splits)

lemma dpll_status_Unit:
  \<open>status_m a ls u op = Status_Unit l \<Longrightarrow>
     (\<forall>l' \<in> set ls. lit_value_m a l' = Some False \<or> (u = None \<and> l' = l)) \<and>
     (u = None \<longrightarrow> l \<in> set ls \<and> lit_value_m a l = None) \<and> (u \<noteq> None \<longrightarrow> u = Some l)\<close>
  by (induction a ls u op rule: status_m.induct) (auto simp: dpll_status_opT split: option.splits bool.splits if_splits)

lemma dpll_status_Open:
  \<open>status_m a ls u op = Status_Open \<Longrightarrow> op \<or> (\<exists>l \<in> set ls. lit_value_m a l = None)\<close>
  by (induction a ls u op rule: status_m.induct) (auto split: option.splits bool.splits if_splits)

lemma dpll_status_Unit_var:
  \<open>status_m a c None False = Status_Unit l \<Longrightarrow> lits_lt n c \<Longrightarrow> unat (Lit_var l) < n\<close>
  using dpll_status_Unit[of a c None False l] by (auto simp: lits_lt_def)

lemma dpll_lits_lt_nth:
  \<open>lits_lt n c \<Longrightarrow> i < length c \<Longrightarrow> unat (Lit_var (c ! i)) < n\<close>
  by (simp add: lits_lt_def)

lemma dpll_unit_var_nth:
  \<open>\<forall>c \<in> set cs. lits_lt n c \<and> Q c \<Longrightarrow> i < length cs \<Longrightarrow>
   status_m r (cs ! i) None False = Status_Unit l \<Longrightarrow> unat (Lit_var l) < n\<close>
  using dpll_status_Unit_var nth_mem by blast

lemma dpll_lit_value_sem:
  \<open>agrees a \<sigma> \<Longrightarrow> unat (Lit_var l) < length a \<Longrightarrow> lit_value_m a l = Some b \<Longrightarrow> lit_sem \<sigma> l = b\<close>
  by (auto simp: agrees_def lit_value_m_def lit_sem_def split: option.splits)

lemma dpll_agrees_sigma: \<open>agrees a (sigma_of a)\<close>
  by (auto simp: agrees_def sigma_of_def)

lemma dpll_agrees_ext:
  \<open>length a' = length a \<Longrightarrow> (\<forall>v < length a. a ! v \<noteq> None \<longrightarrow> a' ! v = a ! v) \<Longrightarrow>
   agrees a' \<sigma> \<Longrightarrow> agrees a \<sigma>\<close>
  unfolding agrees_def by (metis option.distinct(1))

lemma dpll_split:
  \<open>v < length a \<Longrightarrow> agrees a \<sigma> \<Longrightarrow> agrees (a[v := Some True]) \<sigma> \<or> agrees (a[v := Some False]) \<sigma>\<close>
  by (cases \<open>\<sigma> v\<close>) (auto simp: agrees_def nth_list_update)

lemma dpll_unit_assign:
  assumes \<open>status_m a c None False = Status_Unit l\<close> \<open>agrees a \<sigma>\<close> \<open>lits_lt (length a) c\<close>
    \<open>\<exists>l' \<in> set c. lit_sem \<sigma> l'\<close>
  shows \<open>agrees (a[unat (Lit_var l) := Some (\<not> Lit_neg l)]) \<sigma>\<close>
proof -
  from dpll_status_Unit[OF assms(1)]
  have u: \<open>\<forall>l' \<in> set c. lit_value_m a l' = Some False \<or> l' = l\<close> by simp
  have \<open>lit_sem \<sigma> l\<close>
  proof -
    from assms(4) obtain l' where l': \<open>l' \<in> set c\<close> \<open>lit_sem \<sigma> l'\<close> by blast
    show ?thesis
    proof (cases \<open>l' = l\<close>)
      case False
      then have \<open>lit_value_m a l' = Some False\<close> using u l' by blast
      then have \<open>\<not> lit_sem \<sigma> l'\<close>
        using dpll_lit_value_sem[OF assms(2)] assms(3) l' by (auto simp: lits_lt_def)
      then show ?thesis using l' by blast
    qed (use l' in simp)
  qed
  show ?thesis
    unfolding agrees_def
  proof (intro allI impI)
    fix v b
    assume v: \<open>v < length (a[unat (Lit_var l) := Some (\<not> Lit_neg l)])\<close>
      and e: \<open>a[unat (Lit_var l) := Some (\<not> Lit_neg l)] ! v = Some b\<close>
    show \<open>\<sigma> v = b\<close>
    proof (cases \<open>v = unat (Lit_var l)\<close>)
      case True
      then show ?thesis using e v \<open>lit_sem \<sigma> l\<close> by (auto simp: lit_sem_def)
    next
      case False
      then show ?thesis using e v assms(2) by (auto simp: agrees_def)
    qed
  qed
qed

lemma dpll_pass_sem:
  \<open>dpll_wf (length a) cs \<Longrightarrow> set cs \<subseteq> set cs0 \<Longrightarrow> agrees a \<sigma> \<Longrightarrow> cnf_sem \<sigma> cs0 \<Longrightarrow>
   (case pass_m cs a ch of None \<Rightarrow> False | Some (a', ch') \<Rightarrow> agrees a' \<sigma>)\<close>
proof (induction cs arbitrary: a ch)
  case Nil
  then show ?case by simp
next
  case (Cons c cs)
  have wf: \<open>lits_lt (length a) c\<close> \<open>dpll_wf (length a) cs\<close>
    using Cons.prems(1) by (auto simp: dpll_wf_def)
  have sat: \<open>\<exists>l' \<in> set c. lit_sem \<sigma> l'\<close>
    using Cons.prems(2,4) by (auto simp: cnf_sem_def)
  show ?case
  proof (cases \<open>status_m a c None False\<close>)
    case Status_Conflict
    then have \<open>\<forall>l \<in> set c. lit_value_m a l = Some False\<close>
      using dpll_status_Conflict by blast
    then have False
      using sat wf(1) dpll_lit_value_sem[OF Cons.prems(3)] by (fastforce simp: lits_lt_def)
    then show ?thesis ..
  next
    case (Status_Unit l)
    have \<open>agrees (a[unat (Lit_var l) := Some (\<not> Lit_neg l)]) \<sigma>\<close>
      using dpll_unit_assign[OF Status_Unit Cons.prems(3) wf(1) sat] .
    then show ?thesis
      using Cons.IH[of \<open>a[unat (Lit_var l) := Some (\<not> Lit_neg l)]\<close> True] wf(2) Cons.prems(2,4) Status_Unit
      by simp
  qed (use Cons.IH[of a ch] wf(2) Cons.prems in simp_all)
qed

lemma dpll_pass_shape:
  \<open>dpll_wf (length a) cs \<Longrightarrow> pass_m cs a ch = Some (a', ch') \<Longrightarrow>
   length a' = length a \<and> (\<forall>v < length a. a ! v \<noteq> None \<longrightarrow> a' ! v = a ! v) \<and>
   dpll_nnone a' \<le> dpll_nnone a \<and> (ch' \<longrightarrow> ch \<or> dpll_nnone a' < dpll_nnone a) \<and>
   (\<not> ch' \<longrightarrow> a' = a \<and> \<not> ch \<and> dpll_quiet a cs)\<close>
proof (induction cs arbitrary: a ch)
  case Nil
  then show ?case by (auto simp: dpll_quiet_def)
next
  case (Cons c cs)
  have wf: \<open>lits_lt (length a) c\<close> \<open>dpll_wf (length a) cs\<close>
    using Cons.prems(1) by (auto simp: dpll_wf_def)
  show ?case
  proof (cases \<open>status_m a c None False\<close>)
    case Status_Conflict
    then show ?thesis using Cons.prems(2) by simp
  next
    case (Status_Unit l)
    let ?i = \<open>unat (Lit_var l)\<close>
    let ?a1 = \<open>a[?i := Some (\<not> Lit_neg l)]\<close>
    have i: \<open>?i < length a\<close> using dpll_status_Unit_var[OF Status_Unit wf(1)] .
    have n: \<open>a ! ?i = None\<close>
      using dpll_status_Unit[OF Status_Unit] by (auto simp: lit_value_m_def split: option.splits)
    have lt: \<open>dpll_nnone ?a1 < dpll_nnone a\<close> using dpll_nnone_upd[OF i n] .
    have p: \<open>pass_m cs ?a1 True = Some (a', ch')\<close> using Cons.prems(2) Status_Unit by simp
    have ih: \<open>length a' = length ?a1 \<and> (\<forall>v < length ?a1. ?a1 ! v \<noteq> None \<longrightarrow> a' ! v = ?a1 ! v) \<and>
       dpll_nnone a' \<le> dpll_nnone ?a1 \<and> ch'\<close>
      using Cons.IH[OF _ p] wf(2) by auto
    then show ?thesis
      using lt i n by (auto simp: nth_list_update)
  next
    case Status_Satisfied
    then show ?thesis using Cons.IH[of a ch] wf(2) Cons.prems(2) by (auto simp: dpll_quiet_def)
  next
    case Status_Open
    then show ?thesis using Cons.IH[of a ch] wf(2) Cons.prems(2) by (auto simp: dpll_quiet_def)
  qed
qed

lemma dpll_quiet_total:
  assumes \<open>dpll_wf (length a) cs\<close> \<open>dpll_quiet a cs\<close> \<open>\<forall>v < length a. a ! v \<noteq> None\<close>
  shows \<open>cnf_sem (sigma_of a) cs\<close>
  unfolding cnf_sem_def
proof
  fix c assume c: \<open>c \<in> set cs\<close>
  then have wf: \<open>lits_lt (length a) c\<close> using assms(1) by (auto simp: dpll_wf_def)
  have nn: \<open>\<forall>l \<in> set c. lit_value_m a l \<noteq> None\<close>
    using wf assms(3) by (auto simp: lits_lt_def lit_value_m_def split: option.splits)
  show \<open>\<exists>l \<in> set c. lit_sem (sigma_of a) l\<close>
  proof (cases \<open>status_m a c None False\<close>)
    case Status_Satisfied
    then obtain l where l: \<open>l \<in> set c\<close> \<open>lit_value_m a l = Some True\<close> using dpll_status_Sat by blast
    have \<open>lit_sem (sigma_of a) l = True\<close>
      by (rule dpll_lit_value_sem[OF dpll_agrees_sigma]) (use l wf in \<open>auto simp: lits_lt_def\<close>)
    then show ?thesis using l by blast
  next
    case Status_Open
    then show ?thesis using dpll_status_Open nn by blast
  qed (use assms(2) c in \<open>auto simp: dpll_quiet_def\<close>)
qed

text \<open>The facts about one pass of propagation from a state with \<open>ch = False\<close>.\<close>
lemma dpll_pass_props:
  assumes \<open>dpll_wf (length a) cs\<close>
  shows \<open>pass_m cs a False = None \<Longrightarrow> \<not> (\<exists>\<sigma>. agrees a \<sigma> \<and> cnf_sem \<sigma> cs)\<close>
    and \<open>pass_m cs a False = Some (a1, ch) \<Longrightarrow>
         length a1 = length a \<and> (\<forall>v < length a. a ! v \<noteq> None \<longrightarrow> a1 ! v = a ! v) \<and>
         dpll_nnone a1 \<le> dpll_nnone a \<and>
         (\<forall>\<sigma>. agrees a \<sigma> \<and> cnf_sem \<sigma> cs \<longrightarrow> agrees a1 \<sigma>) \<and>
         (ch \<longrightarrow> dpll_nnone a1 < dpll_nnone a) \<and> (\<not> ch \<longrightarrow> a1 = a \<and> dpll_quiet a cs)\<close>
proof -
  show \<open>pass_m cs a False = None \<Longrightarrow> \<not> (\<exists>\<sigma>. agrees a \<sigma> \<and> cnf_sem \<sigma> cs)\<close>
  proof clarify
    fix \<sigma> assume n: \<open>pass_m cs a False = None\<close> and g: \<open>agrees a \<sigma>\<close> \<open>cnf_sem \<sigma> cs\<close>
    show False using dpll_pass_sem[OF assms subset_refl g, of False] n by simp
  qed
  show \<open>pass_m cs a False = Some (a1, ch) \<Longrightarrow> length a1 = length a \<and>
         (\<forall>v < length a. a ! v \<noteq> None \<longrightarrow> a1 ! v = a ! v) \<and> dpll_nnone a1 \<le> dpll_nnone a \<and>
         (\<forall>\<sigma>. agrees a \<sigma> \<and> cnf_sem \<sigma> cs \<longrightarrow> agrees a1 \<sigma>) \<and>
         (ch \<longrightarrow> dpll_nnone a1 < dpll_nnone a) \<and> (\<not> ch \<longrightarrow> a1 = a \<and> dpll_quiet a cs)\<close>
  proof -
    assume p: \<open>pass_m cs a False = Some (a1, ch)\<close>
    have \<open>\<forall>\<sigma>. agrees a \<sigma> \<and> cnf_sem \<sigma> cs \<longrightarrow> agrees a1 \<sigma>\<close>
      using dpll_pass_sem[OF assms subset_refl, of _ False] p by fastforce
    then show ?thesis using dpll_pass_shape[OF assms p] by blast
  qed
qed

text \<open>One iteration of \<^verbatim>\<open>propagate\<close>: the loop invariant and the pass.\<close>
lemma dpll_prop_step:
  assumes wf: \<open>\<forall>c \<in> set cs. lits_lt (length a) c \<and> Q c\<close>
    and len: \<open>length r = length a\<close>
    and ext: \<open>\<forall>v < length a. a ! v \<noteq> None \<longrightarrow> r ! v = a ! v\<close>
    and nn: \<open>dpll_nnone r \<le> dpll_nnone a\<close>
    and ag: \<open>\<forall>\<sigma>. agrees a \<sigma> \<and> cnf_sem \<sigma> cs \<longrightarrow> agrees r \<sigma>\<close>
  shows \<open>pass_m cs r False = None \<Longrightarrow> \<forall>\<sigma>. agrees a \<sigma> \<longrightarrow> \<not> cnf_sem \<sigma> cs\<close>
    and \<open>pass_m cs r False = Some (aa, ch) \<Longrightarrow>
         length aa = length a \<and> (\<forall>v < length a. a ! v \<noteq> None \<longrightarrow> aa ! v = a ! v) \<and>
         dpll_nnone aa \<le> dpll_nnone a \<and> (\<forall>\<sigma>. agrees a \<sigma> \<and> cnf_sem \<sigma> cs \<longrightarrow> agrees aa \<sigma>) \<and>
         (ch \<longrightarrow> dpll_nnone aa < dpll_nnone r) \<and> (\<not> ch \<longrightarrow> aa = r \<and> dpll_quiet r cs)\<close>
proof -
  have w: \<open>dpll_wf (length r) cs\<close> using wf len by (auto simp: dpll_wf_def)
  show \<open>pass_m cs r False = None \<Longrightarrow> \<forall>\<sigma>. agrees a \<sigma> \<longrightarrow> \<not> cnf_sem \<sigma> cs\<close>
    using dpll_pass_props(1)[OF w] ag by blast
  assume p: \<open>pass_m cs r False = Some (aa, ch)\<close>
  note q = dpll_pass_props(2)[OF w p]
  show \<open>length aa = length a \<and> (\<forall>v < length a. a ! v \<noteq> None \<longrightarrow> aa ! v = a ! v) \<and>
         dpll_nnone aa \<le> dpll_nnone a \<and> (\<forall>\<sigma>. agrees a \<sigma> \<and> cnf_sem \<sigma> cs \<longrightarrow> agrees aa \<sigma>) \<and>
         (ch \<longrightarrow> dpll_nnone aa < dpll_nnone r) \<and> (\<not> ch \<longrightarrow> aa = r \<and> dpll_quiet r cs)\<close>
    using q len ext nn ag by (auto intro: le_trans)
qed

text \<open>The two branches of \<^verbatim>\<open>dpll\<close> on variable \<open>v\<close>.\<close>
lemma dpll_branch_unsat:
  assumes \<open>v < length r\<close>
    and \<open>\<forall>\<sigma>. agrees a \<sigma> \<and> cnf_sem \<sigma> cs \<longrightarrow> agrees r \<sigma>\<close>
    and \<open>\<forall>\<sigma>. agrees (r[v := Some True]) \<sigma> \<longrightarrow> \<not> cnf_sem \<sigma> cs\<close>
    and \<open>\<forall>\<sigma>. agrees (r[v := Some False]) \<sigma> \<longrightarrow> \<not> cnf_sem \<sigma> cs\<close>
  shows \<open>\<forall>\<sigma>. agrees a \<sigma> \<longrightarrow> \<not> cnf_sem \<sigma> cs\<close>
  using assms dpll_split by blast

lemma dpll_rec_post:
  assumes \<open>length x = length a\<close> \<open>unat v < length x\<close>
    \<open>\<forall>\<sigma>. agrees a \<sigma> \<and> cnf_sem \<sigma> cs \<longrightarrow> agrees x \<sigma>\<close>
    \<open>\<forall>\<sigma>. agrees (x[unat v := Some True]) \<sigma> \<longrightarrow> \<not> cnf_sem \<sigma> cs\<close>
    \<open>case r of None \<Rightarrow> \<forall>\<sigma>. agrees (x[unat v := Some False]) \<sigma> \<longrightarrow> \<not> cnf_sem \<sigma> cs
     | Some a' \<Rightarrow> length a' = length (x[unat v := Some False]) \<and> (\<forall>v<length a'. a' ! v \<noteq> None) \<and>
         cnf_sem (sigma_of a') cs\<close>
  shows \<open>case r of None \<Rightarrow> \<forall>\<sigma>. agrees a \<sigma> \<longrightarrow> \<not> cnf_sem \<sigma> cs
     | Some a' \<Rightarrow> length a' = length a \<and> (\<forall>v<length a'. a' ! v \<noteq> None) \<and> cnf_sem (sigma_of a') cs\<close>
proof (cases r)
  case None
  then show ?thesis
    using assms dpll_branch_unsat[of \<open>unat v\<close> x a cs] by simp
next
  case (Some a')
  then show ?thesis using assms by simp
qed

lemma read_model_sigma:
  \<open>(\<forall>ls \<in> set vs. lits_lt (length a) ls) \<Longrightarrow> (\<forall>v < length a. a ! v \<noteq> None) \<Longrightarrow>
   read_model_m a vs = map (map (lit_sem (sigma_of a))) vs\<close>
  by (fastforce simp: read_model_m_def read_bits_m_def lits_lt_def lit_value_m_def lit_sem_def
      sigma_of_def split: option.splits)

section \<open>DPLL: contracts\<close>

context BVSmt_ctx
begin

text \<open>The clauses mention only variables below \<open>n\<close> and are short enough for the fuel.\<close>
definition dpll_cs_ok :: \<open>Lit list list \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>dpll_cs_ok cs n \<equiv> \<forall>c \<in> set cs. lits_lt n c \<and> length c + 2 \<le> urust_fuel \<and> length c < 2 ^ 64\<close>

lemma dpll_total_sem:
  \<open>dpll_cs_ok cs n \<Longrightarrow> length x = n \<Longrightarrow> dpll_quiet x cs \<Longrightarrow> \<forall>v < n. \<exists>y. x ! v = Some y \<Longrightarrow>
   cnf_sem (sigma_of x) cs\<close>
  by (rule dpll_quiet_total) (auto simp: dpll_cs_ok_def dpll_wf_def)

definition dpll_lit_value_contract :: \<open>bool option list \<Rightarrow> Lit \<Rightarrow> ('s, bool option, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>dpll_lit_value_contract a l \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>unat (Lit_var l) < length a\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = lit_value_m a l\<rangle>)\<close>

lemma dpll_lit_value_spec [crush_specs]:
  shows \<open>\<Gamma>; lit_value a l \<Turnstile>\<^sub>F dpll_lit_value_contract a l\<close>
  apply (crush_boot f: lit_value_def contract: dpll_lit_value_contract_def)
  apply (crush_base simp add: lit_value_m_def word_less_nat_alt)
  apply (cases \<open>a ! unat (Lit_var l)\<close>; crush_base simp add: lit_value_m_def)
  done

definition dpll_clause_status_contract :: \<open>bool option list \<Rightarrow> Lit list \<Rightarrow> ('s, Status, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>dpll_clause_status_contract a c \<equiv>
     make_function_contract
       (can_alloc_reference \<star> \<langle>lits_lt (length a) c \<and> length c + 2 \<le> urust_fuel \<and> length c < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = status_m a c None False\<rangle>)\<close>

lemma dpll_clause_status_spec [crush_specs]:
  shows \<open>\<Gamma>; clause_status a c \<Turnstile>\<^sub>F dpll_clause_status_contract a c\<close>
  apply (crush_boot f: clause_status_def contract: dpll_clause_status_contract_def)
  apply (crush_base inline: len_def)
  subgoal for u_ref o_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gu u go op gi i. u_ref \<mapsto>\<langle>\<top>\<rangle> gu\<down>u \<star> o_ref \<mapsto>\<langle>\<top>\<rangle> go\<down>op \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
               can_alloc_reference \<star>
               \<langle>unat i \<le> length c \<and> status_m a c None False = status_m a (drop (unat i) c) u op \<and>
                length c - unat i \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gu u go op gi i. u_ref \<mapsto>\<langle>\<top>\<rangle> gu\<down>u \<star> o_ref \<mapsto>\<langle>\<top>\<rangle> go\<down>op \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
               can_alloc_reference \<star>
               \<langle>unat i < length c \<and> status_m a c None False = status_m a (drop (unat i) c) u op \<and>
                length c - unat i \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>r = status_m a c None False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base wp split: option.splits simp add: word_less_nat_alt unat_of_nat_eq dpll_unat_Suc)
    apply (auto simp add: dpll_status_drop ASSUMPTION_def Option.is_none_def intro: dpll_lits_lt_nth)
    done
  done

definition dpll_propagate_pass_contract ::
  \<open>bool option list \<Rightarrow> Lit list list \<Rightarrow> ('s, (bool option list \<times> bool \<times> tnil) option, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>dpll_propagate_pass_contract a cs \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
          \<langle>(\<forall>c \<in> set cs. lits_lt (length a) c \<and> length c + 2 \<le> urust_fuel \<and> length c < 2 ^ 64) \<and>
           length cs + 2 \<le> urust_fuel \<and> length cs < 2 ^ 64 \<and> length a < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>case r of None \<Rightarrow> pass_m cs a False = None
                   | Some (a1, ch, _) \<Rightarrow> pass_m cs a False = Some (a1, ch)\<rangle>)\<close>

lemma dpll_propagate_pass_spec [crush_specs]:
  shows \<open>\<Gamma>; propagate_pass a cs \<Turnstile>\<^sub>F dpll_propagate_pass_contract a cs\<close>
  apply (crush_boot f: propagate_pass_def contract: dpll_propagate_pass_contract_def)
  apply (crush_base inline: len_def)
  subgoal for a_ref c_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>ga a' gc ch gi i. a_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>a' \<star> c_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>ch \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
               can_alloc_reference \<star>
               \<langle>unat i \<le> length cs \<and> length a' = length a \<and>
                pass_m cs a False = pass_m (drop (unat i) cs) a' ch \<and> length cs - unat i \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>ga a' gc ch gi i. a_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>a' \<star> c_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>ch \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
               can_alloc_reference \<star>
               \<langle>unat i < length cs \<and> length a' = length a \<and>
                pass_m cs a False = pass_m (drop (unat i) cs) a' ch \<and> length cs - unat i \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star>
          \<langle>case r of None \<Rightarrow> pass_m cs a False = None
                   | Some (a1, ch, _) \<Rightarrow> pass_m cs a False = Some (a1, ch)\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base wp split: Status.splits simp add: word_less_nat_alt unat_of_nat_eq dpll_unat_Suc)
    apply (auto simp add: dpll_pass_drop ASSUMPTION_def intro: dpll_unit_var_nth)
    done
  done

definition dpll_propagate_contract ::
  \<open>bool option list \<Rightarrow> Lit list list \<Rightarrow> ('s, bool option list option, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>dpll_propagate_contract a cs \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
          \<langle>dpll_cs_ok cs (length a) \<and>
           length cs + 2 \<le> urust_fuel \<and> length cs < 2 ^ 64 \<and>
           length a + 2 \<le> urust_fuel \<and> length a < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>case r of
             None \<Rightarrow> \<not> (\<exists>\<sigma>. agrees a \<sigma> \<and> cnf_sem \<sigma> cs)
           | Some a' \<Rightarrow> length a = length a' \<and> (\<forall>v < length a. a ! v \<noteq> None \<longrightarrow> a' ! v = a ! v) \<and>
               dpll_nnone a' \<le> dpll_nnone a \<and> (\<forall>\<sigma>. agrees a \<sigma> \<and> cnf_sem \<sigma> cs \<longrightarrow> agrees a' \<sigma>) \<and>
               dpll_quiet a' cs \<and> dpll_cs_ok cs (length a') \<and>
               length a' + 2 \<le> urust_fuel \<and> length a' < 2 ^ 64\<rangle>)\<close>

lemma dpll_propagate_spec [crush_specs]:
  shows \<open>\<Gamma>; propagate a cs \<Turnstile>\<^sub>F dpll_propagate_contract a cs\<close>
  apply (crush_boot f: propagate_def contract: dpll_propagate_contract_def)
  apply (crush_base simp add: dpll_cs_ok_def)
  subgoal for a_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>ga a'. a_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>a' \<star> can_alloc_reference \<star>
               \<langle>length a' = length a \<and> (\<forall>v < length a. a ! v \<noteq> None \<longrightarrow> a' ! v = a ! v) \<and>
                dpll_nnone a' \<le> dpll_nnone a \<and> (\<forall>\<sigma>. agrees a \<sigma> \<and> cnf_sem \<sigma> cs \<longrightarrow> agrees a' \<sigma>) \<and>
                dpll_nnone a' < k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>ga a'. a_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>a' \<star> can_alloc_reference \<star>
               \<langle>length a' = length a \<and> (\<forall>v < length a. a ! v \<noteq> None \<longrightarrow> a' ! v = a ! v) \<and>
                dpll_nnone a' \<le> dpll_nnone a \<and> (\<forall>\<sigma>. agrees a \<sigma> \<and> cnf_sem \<sigma> cs \<longrightarrow> agrees a' \<sigma>) \<and>
                dpll_nnone a' < Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star>
          \<langle>case r of
             None \<Rightarrow> \<not> (\<exists>\<sigma>. agrees a \<sigma> \<and> cnf_sem \<sigma> cs)
           | Some a' \<Rightarrow> length a = length a' \<and> (\<forall>v < length a. a ! v \<noteq> None \<longrightarrow> a' ! v = a ! v) \<and>
               dpll_nnone a' \<le> dpll_nnone a \<and> (\<forall>\<sigma>. agrees a \<sigma> \<and> cnf_sem \<sigma> cs \<longrightarrow> agrees a' \<sigma>) \<and>
               dpll_quiet a' cs \<and> (\<forall>c \<in> set cs. lits_lt (length a') c \<and> length c + 2 \<le> urust_fuel \<and> length c < 2 ^ 64) \<and>
               length a' + 2 \<le> urust_fuel \<and> length a' < 2 ^ 64\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base wp split: option.splits prod.splits tnil.splits)
    apply (auto dest!: dpll_prop_step(1)[rotated 5] dpll_prop_step(2)[rotated 5] intro: dpll_nnone_fuel)
    done
  apply (auto simp: dpll_cs_ok_def split: option.splits)
  done

definition dpll_find_unassigned_contract ::
  \<open>bool option list \<Rightarrow> ('s, 64 word option, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>dpll_find_unassigned_contract a \<equiv>
     make_function_contract
       (can_alloc_reference \<star> \<langle>length a + 2 \<le> urust_fuel \<and> length a < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>case r of None \<Rightarrow> (\<forall>v < length a. a ! v \<noteq> None)
                   | Some v \<Rightarrow> unat v < length a \<and> a ! unat v = None\<rangle>)\<close>

lemma dpll_find_unassigned_spec [crush_specs]:
  shows \<open>\<Gamma>; find_unassigned a \<Turnstile>\<^sub>F dpll_find_unassigned_contract a\<close>
  apply (crush_boot f: find_unassigned_def contract: dpll_find_unassigned_contract_def)
  apply (crush_base inline: len_def)
  subgoal for i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gi i. i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i \<le> length a \<and> (\<forall>j < unat i. a ! j \<noteq> None) \<and> length a - unat i \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gi i. i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i < length a \<and> (\<forall>j < unat i. a ! j \<noteq> None) \<and> length a - unat i \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star>
          \<langle>case r of None \<Rightarrow> (\<forall>v < length a. a ! v \<noteq> None)
                   | Some v \<Rightarrow> unat v < length a \<and> a ! unat v = None\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: word_less_nat_alt unat_of_nat_eq dpll_unat_Suc)
    apply (auto simp add: less_Suc_eq Option.is_none_def)
    done
  done

text \<open>The \<open>k\<close>-th unfolding of \<^const>\<open>dpll\<close>: fewer than \<open>k\<close> variables are unassigned.\<close>
definition dpll_fuel_contract ::
  \<open>nat \<Rightarrow> Lit list list \<Rightarrow> bool option list \<Rightarrow> ('s, bool option list option, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>dpll_fuel_contract k cs a \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
          \<langle>(dpll_cs_ok cs (length a) \<and>
           length cs + 2 \<le> urust_fuel \<and> length cs < 2 ^ 64 \<and>
           length a + 2 \<le> urust_fuel \<and> length a < 2 ^ 64) \<and> dpll_nnone a < k\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>case r of
             None \<Rightarrow> \<not> (\<exists>\<sigma>. agrees a \<sigma> \<and> cnf_sem \<sigma> cs)
           | Some a' \<Rightarrow> length a' = length a \<and> (\<forall>v < length a'. a' ! v \<noteq> None) \<and> cnf_sem (sigma_of a') cs\<rangle>)\<close>

lemma dpll_rec_step_spec:
  assumes IH: \<open>\<And>cs' a'. \<Gamma>; R cs' a' \<Turnstile>\<^sub>F dpll_fuel_contract k cs' a'\<close>
  shows \<open>\<Gamma>; dpll_rec_step R cs a \<Turnstile>\<^sub>F dpll_fuel_contract (Suc k) cs a\<close>
  apply (crush_boot f: dpll_rec_step_def contract: dpll_fuel_contract_def)
  apply (crush_base wp split: option.splits specs add: IH contracts add: dpll_fuel_contract_def)
  subgoal by (rule dpll_rec_post) (assumption | (rule sym, assumption) | simp)+
  apply (auto intro: dpll_nnone_branch dpll_total_sem)
  done

lemma dpll_fuel_spec:
  shows \<open>\<Gamma>; (dpll_rec_step ^^ k) g cs a \<Turnstile>\<^sub>F dpll_fuel_contract k cs a\<close>
proof (rule satisfies_function_contract_funpow2[where \<C>=dpll_fuel_contract])
  fix cs a
  show \<open>\<Gamma>; g cs a \<Turnstile>\<^sub>F dpll_fuel_contract 0 cs a\<close>
    apply (ucincl_discharge\<open>intro satisfies_function_contractI\<close>)
    apply (subst wp_sstriple_iff)
    apply (simp add: dpll_fuel_contract_def apure_precise_False asepconj_bot_zero2 bot_aentails_all)
    done
next
  fix n R cs a
  assume \<open>\<And>cs a. \<Gamma>; R cs a \<Turnstile>\<^sub>F dpll_fuel_contract n cs a\<close>
  then show \<open>\<Gamma>; dpll_rec_step R cs a \<Turnstile>\<^sub>F dpll_fuel_contract (Suc n) cs a\<close>
    by (rule dpll_rec_step_spec)
qed

definition dpll_top_contract :: \<open>Lit list list \<Rightarrow> bool option list \<Rightarrow> ('s, bool option list option, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>dpll_top_contract cs a \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
          \<langle>(\<forall>c \<in> set cs. lits_lt (length a) c \<and> length c + 2 \<le> urust_fuel \<and> length c < 2 ^ 64) \<and>
           length cs + 2 \<le> urust_fuel \<and> length cs < 2 ^ 64 \<and>
           length a + 2 \<le> urust_fuel \<and> length a < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>case r of
             None \<Rightarrow> \<not> (\<exists>\<sigma>. agrees a \<sigma> \<and> cnf_sem \<sigma> cs)
           | Some a' \<Rightarrow> length a' = length a \<and> (\<forall>v < length a'. a' ! v \<noteq> None) \<and> cnf_sem (sigma_of a') cs\<rangle>)\<close>

lemma dpll_top_eq_fuel:
  \<open>dpll_fuel_contract urust_fuel cs a = dpll_top_contract cs a\<close>
proof -
  have \<open>(((\<forall>c \<in> set cs. lits_lt (length a) c \<and> length c + 2 \<le> urust_fuel \<and> length c < 2 ^ 64) \<and>
           length cs + 2 \<le> urust_fuel \<and> length cs < 2 ^ 64 \<and>
           length a + 2 \<le> urust_fuel \<and> length a < 2 ^ 64) \<and> dpll_nnone a < urust_fuel) =
        ((\<forall>c \<in> set cs. lits_lt (length a) c \<and> length c + 2 \<le> urust_fuel \<and> length c < 2 ^ 64) \<and>
           length cs + 2 \<le> urust_fuel \<and> length cs < 2 ^ 64 \<and>
           length a + 2 \<le> urust_fuel \<and> length a < 2 ^ 64)\<close>
    using dpll_nnone_le[of a] by auto
  then show ?thesis
    unfolding dpll_fuel_contract_def dpll_top_contract_def dpll_cs_ok_def by (simp only:)
qed

lemma dpll_top_spec [crush_specs]:
  shows \<open>\<Gamma>; dpll cs a \<Turnstile>\<^sub>F dpll_top_contract cs a\<close>
  unfolding dpll_def dpll_top_eq_fuel[symmetric] by (rule dpll_fuel_spec)

definition dpll_read_bits_contract :: \<open>bool option list \<Rightarrow> Lit list \<Rightarrow> ('s, bool list, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>dpll_read_bits_contract a ls \<equiv>
     make_function_contract
       (can_alloc_reference \<star> \<langle>lits_lt (length a) ls \<and> length ls + 2 \<le> urust_fuel \<and> length ls < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = read_bits_m a ls\<rangle>)\<close>

lemma dpll_read_bits_spec [crush_specs]:
  shows \<open>\<Gamma>; read_bits a ls \<Turnstile>\<^sub>F dpll_read_bits_contract a ls\<close>
  apply (crush_boot f: read_bits_def contract: dpll_read_bits_contract_def)
  apply (crush_base inline: len_def)
  subgoal for r_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gr r gi i. r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i \<le> length ls \<and> r = map (\<lambda>l. lit_value_m a l = Some True) (take (unat i) ls) \<and>
                length ls - unat i \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gr r gi i. r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i < length ls \<and> r = map (\<lambda>l. lit_value_m a l = Some True) (take (unat i) ls) \<and>
                length ls - unat i \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>r = read_bits_m a ls\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: vec_push_def simp add: word_less_nat_alt unat_of_nat_eq dpll_unat_Suc
        take_Suc_conv_app_nth read_bits_m_def)
    apply (auto simp add: lits_lt_def read_bits_m_def)
    done
  done

definition read_model_contract :: \<open>bool option list \<Rightarrow> Lit list list \<Rightarrow> ('s, bool list list, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>read_model_contract a vs \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
          \<langle>(\<forall>ls \<in> set vs. lits_lt (length a) ls \<and> length ls + 2 \<le> urust_fuel \<and> length ls < 2 ^ 64) \<and>
           length vs + 2 \<le> urust_fuel \<and> length vs < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = read_model_m a vs\<rangle>)\<close>

lemma read_model_spec [crush_specs]:
  shows \<open>\<Gamma>; read_model a vs \<Turnstile>\<^sub>F read_model_contract a vs\<close>
  apply (crush_boot f: read_model_def contract: read_model_contract_def)
  apply (crush_base inline: len_def)
  subgoal for m_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gm m gi i. m_ref \<mapsto>\<langle>\<top>\<rangle> gm\<down>m \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i \<le> length vs \<and> m = map (read_bits_m a) (take (unat i) vs) \<and>
                length vs - unat i \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gm m gi i. m_ref \<mapsto>\<langle>\<top>\<rangle> gm\<down>m \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i < length vs \<and> m = map (read_bits_m a) (take (unat i) vs) \<and>
                length vs - unat i \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>r = read_model_m a vs\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: vec_push_def simp add: word_less_nat_alt unat_of_nat_eq dpll_unat_Suc
        take_Suc_conv_app_nth read_model_m_def)
    done
  done

end

end
