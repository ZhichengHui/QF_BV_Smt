theory QFBV_DpllPure
  imports QFBV_Defs
begin

section \<open>DPLL: pure facts\<close>

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
proof -
  have \<open>unat x + unat (1 :: 64 word) < 2 ^ LENGTH(64)\<close> using assms by simp
  then have \<open>unat (x + 1) = unat x + unat (1 :: 64 word)\<close> using unat_add_lem by blast
  then show ?thesis by simp
qed

lemma dpll_status_drop:
  \<open>i < length c \<Longrightarrow> status_m a (drop i c) u op =
     (case lit_value_m a (c ! i) of
        Some True \<Rightarrow> Status_Satisfied
      | Some False \<Rightarrow> status_m a (drop (Suc i) c) u op
      | None \<Rightarrow> (if u \<noteq> None then status_m a (drop (Suc i) c) u True
                 else status_m a (drop (Suc i) c) (Some (c ! i)) op))\<close>
  by (simp add: Cons_nth_drop_Suc[symmetric])

lemma dpll_status_Sat:
  \<open>status_m a ls u op = Status_Satisfied \<Longrightarrow> \<exists>l \<in> set ls. lit_value_m a l = Some True\<close>
  by (induction a ls u op rule: status_m.induct) (auto split: option.splits bool.splits if_splits)

lemma dpll_status_Conflict:
  \<open>status_m a ls u op = Status_Conflict \<Longrightarrow> u = None \<and> \<not> op \<and> (\<forall>l \<in> set ls. lit_value_m a l = Some False)\<close>
proof (induction ls arbitrary: u op)
  case Nil
  then show ?case by (cases u; cases op) simp_all
next
  case (Cons x xs)
  consider (N) \<open>lit_value_m a x = None\<close> | (T) \<open>lit_value_m a x = Some True\<close>
    | (F) \<open>lit_value_m a x = Some False\<close>
    by (cases \<open>lit_value_m a x\<close>) auto
  then show ?case
  proof cases
    case N
    show ?thesis
    proof (cases u)
      case None
      then have \<open>status_m a xs (Some x) op = Status_Conflict\<close> using Cons.prems N by simp
      then show ?thesis using Cons.IH[of \<open>Some x\<close> op] by simp
    next
      case (Some y)
      then have \<open>status_m a xs u True = Status_Conflict\<close> using Cons.prems N by simp
      then show ?thesis using Cons.IH[of u True] by simp
    qed
  next
    case T
    then show ?thesis using Cons.prems by simp
  next
    case F
    then have \<open>status_m a xs u op = Status_Conflict\<close> using Cons.prems by simp
    then show ?thesis using Cons.IH[of u op] F by simp
  qed
qed

lemma dpll_status_opT:
  \<open>status_m a ls u True \<noteq> Status_Conflict \<and> status_m a ls u True \<noteq> Status_Unit l\<close>
proof (induction ls arbitrary: u)
  case Nil
  show ?case by (cases u) simp_all
next
  case (Cons x xs)
  consider (N) \<open>lit_value_m a x = None\<close> | (T) \<open>lit_value_m a x = Some True\<close>
    | (F) \<open>lit_value_m a x = Some False\<close>
    by (cases \<open>lit_value_m a x\<close>) auto
  then show ?case using Cons.IH by cases (cases u; simp)+
qed

lemma dpll_status_Unit:
  \<open>status_m a ls u op = Status_Unit l \<Longrightarrow>
     (\<forall>l' \<in> set ls. lit_value_m a l' = Some False \<or> (u = None \<and> l' = l)) \<and>
     (u = None \<longrightarrow> l \<in> set ls \<and> lit_value_m a l = None) \<and> (u \<noteq> None \<longrightarrow> u = Some l)\<close>
proof (induction ls arbitrary: u op)
  case Nil
  then show ?case by (cases u; cases op) simp_all
next
  case (Cons x xs)
  consider (N) \<open>lit_value_m a x = None\<close> | (T) \<open>lit_value_m a x = Some True\<close>
    | (F) \<open>lit_value_m a x = Some False\<close>
    by (cases \<open>lit_value_m a x\<close>) auto
  then show ?case
  proof cases
    case N
    show ?thesis
    proof (cases u)
      case None
      then have \<open>status_m a xs (Some x) op = Status_Unit l\<close> using Cons.prems N by simp
      then show ?thesis using Cons.IH[of \<open>Some x\<close> op] N None by auto
    next
      case (Some y)
      then have \<open>status_m a xs u True = Status_Unit l\<close> using Cons.prems N by simp
      then show ?thesis using dpll_status_opT[of a xs u l] by simp
    qed
  next
    case T
    then show ?thesis using Cons.prems by simp
  next
    case F
    then have \<open>status_m a xs u op = Status_Unit l\<close> using Cons.prems by simp
    then show ?thesis using Cons.IH[of u op] F by auto
  qed
qed

lemma dpll_status_Open:
  \<open>status_m a ls u op = Status_Open \<Longrightarrow> op \<or> (\<exists>l \<in> set ls. lit_value_m a l = None)\<close>
proof (induction ls arbitrary: u op)
  case Nil
  then show ?case by (cases u; cases op) simp_all
next
  case (Cons x xs)
  consider (N) \<open>lit_value_m a x = None\<close> | (T) \<open>lit_value_m a x = Some True\<close>
    | (F) \<open>lit_value_m a x = Some False\<close>
    by (cases \<open>lit_value_m a x\<close>) auto
  then show ?case
  proof cases
    case N
    then show ?thesis by auto
  next
    case T
    then show ?thesis using Cons.prems by simp
  next
    case F
    then have \<open>status_m a xs u op = Status_Open\<close> using Cons.prems by simp
    then show ?thesis using Cons.IH[of u op] by auto
  qed
qed

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

lemma read_model_sigma:
  \<open>(\<forall>ls \<in> set vs. lits_lt (length a) ls) \<Longrightarrow> (\<forall>v < length a. a ! v \<noteq> None) \<Longrightarrow>
   read_model_m a vs = map (map (lit_sem (sigma_of a))) vs\<close>
  by (fastforce simp: read_model_m_def read_bits_m_def lits_lt_def lit_value_m_def lit_sem_def
      sigma_of_def split: option.splits)


subsection \<open>The trail\<close>

text \<open>The trail \<open>t\<close> lists the true literals of the partial assignment \<open>a\<close> of \<open>n\<close> variables, in the
  order they were assigned, each variable at most once.\<close>
definition tr_ok :: \<open>nat \<Rightarrow> bool option list \<Rightarrow> Lit list \<Rightarrow> bool\<close> where
  \<open>tr_ok n a t \<equiv> length a = n \<and> distinct (map (\<lambda>l. unat (Lit_var l)) t) \<and>
     (\<forall>l \<in> set t. unat (Lit_var l) < n \<and> a ! unat (Lit_var l) = Some (\<not> Lit_neg l)) \<and>
     (\<forall>v < n. a ! v \<noteq> None \<longrightarrow> (\<exists>l \<in> set t. unat (Lit_var l) = v))\<close>

text \<open>The entry \<open>i\<close> of the trail follows from the clauses and the entries before it.\<close>
definition tr_imp :: \<open>Lit list list \<Rightarrow> Lit list \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>tr_imp cs t i \<equiv> \<forall>\<sigma>. cnf_sem \<sigma> cs \<and> (\<forall>k < i. lit_sem \<sigma> (t ! k)) \<longrightarrow> lit_sem \<sigma> (t ! i)\<close>

lemma tr_ok_length: \<open>tr_ok n a t \<Longrightarrow> length t \<le> n\<close>
proof -
  assume h: \<open>tr_ok n a t\<close>
  let ?m = \<open>map (\<lambda>l. unat (Lit_var l)) t\<close>
  have \<open>set ?m \<subseteq> {..<n}\<close> using h by (auto simp: tr_ok_def)
  moreover have \<open>distinct ?m\<close> using h by (simp add: tr_ok_def)
  ultimately show ?thesis using card_mono[of \<open>{..<n}\<close> \<open>set ?m\<close>] distinct_card[of ?m] by simp
qed

lemma tr_ok_agrees:
  assumes h0: \<open>tr_ok n a t\<close>
  shows \<open>agrees a \<sigma> \<longleftrightarrow> (\<forall>l \<in> set t. lit_sem \<sigma> l)\<close>
proof
  assume h: \<open>agrees a \<sigma>\<close>
  show \<open>\<forall>l \<in> set t. lit_sem \<sigma> l\<close>
  proof
    fix l assume l: \<open>l \<in> set t\<close>
    then have \<open>unat (Lit_var l) < length a\<close> \<open>a ! unat (Lit_var l) = Some (\<not> Lit_neg l)\<close>
      using h0 by (auto simp: tr_ok_def)
    then show \<open>lit_sem \<sigma> l\<close> using h by (auto simp: agrees_def lit_sem_def)
  qed
next
  assume h: \<open>\<forall>l \<in> set t. lit_sem \<sigma> l\<close>
  show \<open>agrees a \<sigma>\<close>
    unfolding agrees_def
  proof (intro allI impI)
    fix v b assume v: \<open>v < length a\<close> \<open>a ! v = Some b\<close>
    then obtain l where l: \<open>l \<in> set t\<close> \<open>unat (Lit_var l) = v\<close> using h0 by (auto simp: tr_ok_def)
    then have \<open>a ! v = Some (\<not> Lit_neg l)\<close> using h0 by (auto simp: tr_ok_def)
    then show \<open>\<sigma> v = b\<close> using v(2) h l by (auto simp: lit_sem_def)
  qed
qed

lemma tr_ok_agrees_nth: \<open>tr_ok n a t \<Longrightarrow> \<forall>k < length t. lit_sem \<sigma> (t ! k) \<Longrightarrow> agrees a \<sigma>\<close>
  using tr_ok_agrees by (metis in_set_conv_nth)

lemma tr_ok_init: \<open>tr_ok n (replicate n None) []\<close>
  by (simp add: tr_ok_def)

lemma tr_ok_push:
  assumes \<open>tr_ok n a t\<close> \<open>unat (Lit_var l) < n\<close> \<open>a ! unat (Lit_var l) = None\<close>
  shows \<open>tr_ok n (a[unat (Lit_var l) := Some (\<not> Lit_neg l)]) (t @ [l])\<close>
proof -
  have nv: \<open>\<forall>l' \<in> set t. unat (Lit_var l') \<noteq> unat (Lit_var l)\<close>
    using assms by (auto simp: tr_ok_def)
  then show ?thesis using assms by (auto simp: tr_ok_def nth_list_update)
qed

lemma tr_ok_pop:
  assumes \<open>tr_ok n a (t @ [l])\<close>
  shows \<open>tr_ok n (a[unat (Lit_var l) := None]) t\<close>
proof -
  have \<open>distinct (map (\<lambda>l. unat (Lit_var l)) (t @ [l]))\<close> using assms tr_ok_def by blast
  then have nv: \<open>\<forall>l' \<in> set t. unat (Lit_var l') \<noteq> unat (Lit_var l)\<close> by (auto simp: image_iff)
  have T: \<open>length a = n\<close> \<open>distinct (map (\<lambda>l. unat (Lit_var l)) (t @ [l]))\<close>
    \<open>\<forall>l' \<in> set (t @ [l]). unat (Lit_var l') < n \<and> a ! unat (Lit_var l') = Some (\<not> Lit_neg l')\<close>
    \<open>\<forall>v < n. a ! v \<noteq> None \<longrightarrow> (\<exists>l' \<in> set (t @ [l]). unat (Lit_var l') = v)\<close>
    using assms by (simp_all add: tr_ok_def)
  have x: \<open>unat (Lit_var l) < n\<close> using T(3) by simp
  let ?a = \<open>a[unat (Lit_var l) := None]\<close>
  have \<open>\<forall>l' \<in> set t. unat (Lit_var l') < n \<and> ?a ! unat (Lit_var l') = Some (\<not> Lit_neg l')\<close>
  proof
    fix l' assume l': \<open>l' \<in> set t\<close>
    have ne: \<open>unat (Lit_var l) \<noteq> unat (Lit_var l')\<close> using nv l' by metis
    show \<open>unat (Lit_var l') < n \<and> ?a ! unat (Lit_var l') = Some (\<not> Lit_neg l')\<close>
      using T(3) l' nth_list_update_neq[OF ne, of a None] by simp
  qed
  moreover have \<open>\<forall>v < n. ?a ! v \<noteq> None \<longrightarrow> (\<exists>l' \<in> set t. unat (Lit_var l') = v)\<close>
  proof (intro allI impI)
    fix v assume v: \<open>v < n\<close> \<open>?a ! v \<noteq> None\<close>
    then have vx: \<open>v \<noteq> unat (Lit_var l)\<close> using x T(1) by auto
    then have \<open>a ! v \<noteq> None\<close> using v(2) by simp
    then show \<open>\<exists>l' \<in> set t. unat (Lit_var l') = v\<close> using T(4) v(1) vx by auto
  qed
  ultimately show ?thesis using T(1,2) by (simp add: tr_ok_def)
qed

lemma tr_imp_append: \<open>i < length t \<Longrightarrow> tr_imp cs (t @ e) i = tr_imp cs t i\<close>
proof -
  assume i: \<open>i < length t\<close>
  have \<open>\<forall>k \<le> i. (t @ e) ! k = t ! k\<close> using i by (simp add: nth_append)
  then show ?thesis unfolding tr_imp_def by (metis less_imp_le_nat order_refl)
qed

lemma tr_all:
  assumes \<open>\<forall>j < length t. j \<notin> set L \<longrightarrow> tr_imp cs t j\<close> \<open>cnf_sem \<sigma> cs\<close>
    \<open>\<forall>k < q. lit_sem \<sigma> (t ! k)\<close> \<open>\<forall>j. q \<le> j \<longrightarrow> j \<notin> set L\<close>
  shows \<open>\<forall>k < length t. lit_sem \<sigma> (t ! k)\<close>
proof -
  have \<open>k < length t \<longrightarrow> lit_sem \<sigma> (t ! k)\<close> for k
  proof (induction k rule: less_induct)
    case (less k)
    show ?case
    proof (cases \<open>k < q\<close>)
      case True
      then show ?thesis using assms(3) by blast
    next
      case False
      show ?thesis
      proof
        assume k: \<open>k < length t\<close>
        have \<open>tr_imp cs t k\<close> using assms(1,4) False k by simp
        moreover have \<open>\<forall>k' < k. lit_sem \<sigma> (t ! k')\<close> using less k by simp
        ultimately show \<open>lit_sem \<sigma> (t ! k)\<close> using assms(2) by (simp add: tr_imp_def)
      qed
    qed
  qed
  then show ?thesis by blast
qed

subsection \<open>One pass of propagation\<close>

text \<open>One pass of unit propagation (\<^verbatim>\<open>propagate_pass\<close>): the assignment, the trail, and whether
  the pass met no conflict.\<close>
fun tpass_m :: \<open>Lit list list \<Rightarrow> bool option list \<Rightarrow> Lit list \<Rightarrow> bool option list \<times> Lit list \<times> bool\<close> where
  \<open>tpass_m [] a t = (a, t, True)\<close>
| \<open>tpass_m (c # cs) a t =
     (case status_m a c None False of
        Status_Conflict \<Rightarrow> (a, t, False)
      | Status_Unit l \<Rightarrow> tpass_m cs (a[unat (Lit_var l) := Some (\<not> Lit_neg l)]) (t @ [l])
      | Status_Satisfied \<Rightarrow> tpass_m cs a t
      | Status_Open \<Rightarrow> tpass_m cs a t)\<close>

lemma dpll_tpass_drop:
  \<open>i < length cs \<Longrightarrow> tpass_m (drop i cs) a t =
     (case status_m a (cs ! i) None False of
        Status_Conflict \<Rightarrow> (a, t, False)
      | Status_Unit l \<Rightarrow> tpass_m (drop (Suc i) cs) (a[unat (Lit_var l) := Some (\<not> Lit_neg l)]) (t @ [l])
      | Status_Satisfied \<Rightarrow> tpass_m (drop (Suc i) cs) a t
      | Status_Open \<Rightarrow> tpass_m (drop (Suc i) cs) a t)\<close>
  by (simp add: Cons_nth_drop_Suc[symmetric])

lemma dpll_conflict_unsat:
  assumes \<open>status_m a c None False = Status_Conflict\<close> \<open>lits_lt (length a) c\<close> \<open>c \<in> set cs\<close>
    \<open>agrees a \<sigma>\<close>
  shows \<open>\<not> cnf_sem \<sigma> cs\<close>
proof
  assume \<open>cnf_sem \<sigma> cs\<close>
  then obtain l' where l': \<open>l' \<in> set c\<close> \<open>lit_sem \<sigma> l'\<close> using assms(3) unfolding cnf_sem_def by blast
  have \<open>lit_value_m a l' = Some False\<close> using dpll_status_Conflict[OF assms(1)] l'(1) by blast
  moreover have \<open>unat (Lit_var l') < length a\<close> using assms(2) l'(1) by (simp add: lits_lt_def)
  ultimately have \<open>lit_sem \<sigma> l' = False\<close> using dpll_lit_value_sem[OF assms(4)] by blast
  then show False using l'(2) by simp
qed

lemma dpll_unit_imp:
  assumes \<open>status_m a c None False = Status_Unit l\<close> \<open>lits_lt n c\<close> \<open>c \<in> set cs\<close> \<open>tr_ok n a t\<close>
  shows \<open>tr_imp cs (t @ [l]) (length t)\<close>
  unfolding tr_imp_def
proof (intro allI impI)
  fix \<sigma> assume h: \<open>cnf_sem \<sigma> cs \<and> (\<forall>k < length t. lit_sem \<sigma> ((t @ [l]) ! k))\<close>
  have \<open>agrees a \<sigma>\<close> using tr_ok_agrees_nth[OF assms(4)] h by (simp add: nth_append)
  moreover have \<open>\<exists>l' \<in> set c. lit_sem \<sigma> l'\<close> using h assms(3) by (auto simp: cnf_sem_def)
  moreover have \<open>lits_lt (length a) c\<close> using assms(2,4) by (simp add: tr_ok_def)
  ultimately have \<open>agrees (a[unat (Lit_var l) := Some (\<not> Lit_neg l)]) \<sigma>\<close>
    using dpll_unit_assign[OF assms(1)] by blast
  moreover have \<open>unat (Lit_var l) < length a\<close> using dpll_status_Unit_var[OF assms(1)] \<open>lits_lt (length a) c\<close> .
  ultimately show \<open>lit_sem \<sigma> ((t @ [l]) ! length t)\<close> by (auto simp: agrees_def lit_sem_def)
qed

lemma dpll_tpass:
  assumes \<open>dpll_wf n cs\<close> \<open>set cs \<subseteq> set cs0\<close> \<open>tr_ok n a t\<close> \<open>tpass_m cs a t = (a', t', b)\<close>
  shows \<open>tr_ok n a' t' \<and> (\<exists>e. t' = t @ e) \<and>
         (\<forall>j. length t \<le> j \<and> j < length t' \<longrightarrow> tr_imp cs0 t' j) \<and>
         (\<not> b \<longrightarrow> (\<forall>\<sigma>. agrees a' \<sigma> \<longrightarrow> \<not> cnf_sem \<sigma> cs0)) \<and>
         (b \<and> length t' = length t \<longrightarrow> a' = a \<and> t' = t \<and> dpll_quiet a cs)\<close>
  using assms
proof (induction cs arbitrary: a t)
  case Nil
  then show ?case by (auto simp: dpll_quiet_def)
next
  case (Cons c cs)
  have wf: \<open>lits_lt n c\<close> \<open>dpll_wf n cs\<close> using Cons.prems(1) by (auto simp: dpll_wf_def)
  have sub: \<open>set cs \<subseteq> set cs0\<close> \<open>c \<in> set cs0\<close> using Cons.prems(2) by auto
  have la: \<open>length a = n\<close> using Cons.prems(3) by (simp add: tr_ok_def)
  show ?case
  proof (cases \<open>status_m a c None False\<close>)
    case Status_Conflict
    then have r: \<open>a' = a\<close> \<open>t' = t\<close> \<open>\<not> b\<close> using Cons.prems(4) by simp_all
    have \<open>\<forall>\<sigma>. agrees a \<sigma> \<longrightarrow> \<not> cnf_sem \<sigma> cs0\<close>
      using dpll_conflict_unsat[OF Status_Conflict _ sub(2)] wf(1) la by blast
    then show ?thesis using r Cons.prems(3) by auto
  next
    case (Status_Unit l)
    let ?i = \<open>unat (Lit_var l)\<close>
    let ?a1 = \<open>a[?i := Some (\<not> Lit_neg l)]\<close> and ?t1 = \<open>t @ [l]\<close>
    have i: \<open>?i < n\<close> using dpll_status_Unit_var[OF Status_Unit wf(1)] .
    have nn: \<open>a ! ?i = None\<close>
      using dpll_status_Unit[OF Status_Unit] by (auto simp: lit_value_m_def split: option.splits)
    have ok1: \<open>tr_ok n ?a1 ?t1\<close> using tr_ok_push[OF Cons.prems(3) i nn] .
    have imp1: \<open>tr_imp cs0 ?t1 (length t)\<close> using dpll_unit_imp[OF Status_Unit wf(1) sub(2) Cons.prems(3)] .
    have p: \<open>tpass_m cs ?a1 ?t1 = (a', t', b)\<close> using Cons.prems(4) Status_Unit by simp
    note IH = Cons.IH[OF wf(2) sub(1) ok1 p]
    then obtain e where e: \<open>t' = ?t1 @ e\<close> by blast
    have \<open>tr_imp cs0 t' (length t)\<close> using imp1 tr_imp_append[of \<open>length t\<close> ?t1 cs0 e] e by simp
    then have \<open>\<forall>j. length t \<le> j \<and> j < length t' \<longrightarrow> tr_imp cs0 t' j\<close>
      using IH by (metis Suc_leI le_neq_implies_less length_append_singleton)
    then show ?thesis using IH e by auto
  next
    case Status_Satisfied
    then have p: \<open>tpass_m cs a t = (a', t', b)\<close> using Cons.prems(4) by simp
    note IH = Cons.IH[OF wf(2) sub(1) Cons.prems(3) p]
    then show ?thesis using Status_Satisfied by (auto simp: dpll_quiet_def)
  next
    case Status_Open
    then have p: \<open>tpass_m cs a t = (a', t', b)\<close> using Cons.prems(4) by simp
    note IH = Cons.IH[OF wf(2) sub(1) Cons.prems(3) p]
    then show ?thesis using Status_Open by (auto simp: dpll_quiet_def)
  qed
qed

text \<open>One iteration of \<^verbatim>\<open>propagate\<close>: the loop invariant and the pass.\<close>
lemma dpll_prop_iter:
  assumes \<open>dpll_wf n cs\<close> \<open>tr_ok n a' t'\<close> \<open>\<exists>e. t' = t @ e\<close>
    \<open>\<forall>j. length t \<le> j \<and> j < length t' \<longrightarrow> tr_imp cs t' j\<close> \<open>tpass_m cs a' t' = (a1, t1, b)\<close>
  shows \<open>tr_ok n a1 t1 \<and> (\<exists>e. t1 = t @ e) \<and> (\<forall>j. length t \<le> j \<and> j < length t1 \<longrightarrow> tr_imp cs t1 j) \<and>
         length t' \<le> length t1 \<and> length t1 \<le> n \<and>
         (\<not> b \<longrightarrow> (\<forall>\<sigma>. agrees a1 \<sigma> \<longrightarrow> \<not> cnf_sem \<sigma> cs)) \<and> (b \<and> length t1 = length t' \<longrightarrow> dpll_quiet a1 cs)\<close>
proof -
  note P = dpll_tpass[OF assms(1) subset_refl assms(2) assms(5)]
  obtain e' where e': \<open>t1 = t' @ e'\<close> using P by blast
  obtain e where e: \<open>t' = t @ e\<close> using assms(3) by blast
  have \<open>\<forall>j. length t \<le> j \<and> j < length t1 \<longrightarrow> tr_imp cs t1 j\<close>
  proof (intro allI impI)
    fix j assume j: \<open>length t \<le> j \<and> j < length t1\<close>
    show \<open>tr_imp cs t1 j\<close>
    proof (cases \<open>j < length t'\<close>)
      case True
      then show ?thesis using assms(4) j e' tr_imp_append by simp
    qed (use P j in auto)
  qed
  then show ?thesis using P e e' tr_ok_length[of n a1 t1] by auto
qed

subsection \<open>The measure of the search\<close>

text \<open>The trail read as a number in base 3, its entry \<open>i\<close> a digit \<open>1\<close> for a decision (\<open>i \<in> L\<close>)
  and \<open>2\<close> otherwise, at position \<open>n - 1 - i\<close>; \<open>m\<close> is the length of the trail. Every iteration of
  the search loop increases it, and it stays below \<open>3 ^ n\<close>.\<close>
definition meas :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat\<close> where
  \<open>meas n m L \<equiv> (\<Sum>i<m. (if i \<in> set L then 1 else 2) * 3 ^ (n - Suc i))\<close>

lemma meas_geom:
  \<open>a \<le> m \<Longrightarrow> m \<le> n \<Longrightarrow> (\<Sum>i\<in>{a..<m}. 2 * 3 ^ (n - Suc i)) + 3 ^ (n - m) = (3::nat) ^ (n - a)\<close>
proof (induction m)
  case 0
  then show ?case by simp
next
  case (Suc m)
  show ?case
  proof (cases \<open>a = Suc m\<close>)
    case False
    then have am: \<open>a \<le> m\<close> using Suc.prems by simp
    have e: \<open>(3::nat) ^ (n - m) = 3 * 3 ^ (n - Suc m)\<close>
      using Suc.prems(2) by (metis Suc_diff_Suc Suc_le_lessD power_Suc)
    show ?thesis using Suc.IH[OF am] Suc.prems(2) am e by simp
  qed simp
qed

lemma meas_le_geom: \<open>meas n m L \<le> (\<Sum>i<m. 2 * 3 ^ (n - Suc i))\<close>
  unfolding meas_def by (rule sum_mono) simp

lemma meas_lt: \<open>m \<le> n \<Longrightarrow> meas n m L < 3 ^ n\<close>
proof -
  assume m: \<open>m \<le> n\<close>
  have \<open>(\<Sum>i<m. 2 * 3 ^ (n - Suc i)) + 3 ^ (n - m) = (3::nat) ^ n\<close>
    using meas_geom[of 0 m n] m by (simp add: lessThan_atLeast0)
  moreover have \<open>(0::nat) < 3 ^ (n - m)\<close> by simp
  ultimately show ?thesis using meas_le_geom[of n m L] by linarith
qed

lemma meas_mono: \<open>m \<le> m' \<Longrightarrow> meas n m L \<le> meas n m' L\<close>
  unfolding meas_def by (rule sum_mono2) auto

lemma meas_decide: \<open>\<forall>p \<in> set L. p < m \<Longrightarrow> meas n m L < meas n (Suc m) (L @ [m])\<close>
proof -
  assume h: \<open>\<forall>p \<in> set L. p < m\<close>
  have \<open>(\<Sum>i<m. (if i \<in> set (L @ [m]) then 1 else 2) * 3 ^ (n - Suc i)) = meas n m L\<close>
    unfolding meas_def by (rule sum.cong) auto
  then show ?thesis by (simp add: meas_def)
qed

lemma meas_split:
  \<open>Suc p \<le> m \<Longrightarrow> (\<Sum>i<m. f i) = (\<Sum>i<p. f i) + f p + (\<Sum>i\<in>{Suc p..<m}. (f i :: nat))\<close>
  by (metis lessThan_Suc_atMost atLeast0AtMost lessThan_atLeast0 sum.atLeastLessThan_concat
      sum.lessThan_Suc zero_le)

lemma meas_backtrack:
  assumes \<open>\<forall>q \<in> set L. q < p\<close> \<open>p < m\<close> \<open>m \<le> n\<close>
  shows \<open>meas n m (L @ [p]) < meas n (Suc p) L\<close>
proof -
  let ?d = \<open>\<lambda>L i. (if i \<in> set L then 1 else 2) * (3::nat) ^ (n - Suc i)\<close>
  have pre: \<open>(\<Sum>i<p. ?d (L @ [p]) i) = (\<Sum>i<p. ?d L i)\<close> by (rule sum.cong) auto
  have tail: \<open>(\<Sum>i\<in>{Suc p..<m}. ?d (L @ [p]) i) \<le> (\<Sum>i\<in>{Suc p..<m}. 2 * 3 ^ (n - Suc i))\<close>
    by (rule sum_mono) simp
  have g: \<open>(\<Sum>i\<in>{Suc p..<m}. 2 * 3 ^ (n - Suc i)) + 3 ^ (n - m) = (3::nat) ^ (n - Suc p)\<close>
    using meas_geom[of \<open>Suc p\<close> m n] assms(2,3) by simp
  have L: \<open>meas n m (L @ [p]) = (\<Sum>i<p. ?d L i) + 3 ^ (n - Suc p) + (\<Sum>i\<in>{Suc p..<m}. ?d (L @ [p]) i)\<close>
    unfolding meas_def using meas_split[of p m \<open>?d (L @ [p])\<close>] assms(2) pre by simp
  have pL: \<open>p \<notin> set L\<close> using assms(1) by blast
  have R: \<open>meas n (Suc p) L = (\<Sum>i<p. ?d L i) + 2 * 3 ^ (n - Suc p)\<close>
    unfolding meas_def using pL by simp
  have \<open>(0::nat) < 3 ^ (n - m)\<close> by simp
  then show ?thesis using L R tail g by linarith
qed

subsection \<open>The state of the search\<close>

text \<open>The state of \<^verbatim>\<open>dpll\<close>: \<open>L\<close> lists the trail positions of the decisions in increasing
  order, and every other entry follows from the clauses and the entries before it.\<close>
definition dstate :: \<open>Lit list list \<Rightarrow> nat \<Rightarrow> bool option list \<Rightarrow> Lit list \<Rightarrow> nat list \<Rightarrow> bool\<close> where
  \<open>dstate cs n a t L \<equiv> tr_ok n a t \<and> sorted_wrt (<) L \<and> (\<forall>p \<in> set L. p < length t) \<and>
     (\<forall>j < length t. j \<notin> set L \<longrightarrow> tr_imp cs t j)\<close>

lemma dstate_init: \<open>dstate cs n (replicate n None) [] []\<close>
  by (simp add: dstate_def tr_ok_init)

lemma dstate_prop:
  assumes \<open>dstate cs n a t L\<close> \<open>tr_ok n a1 t1\<close> \<open>\<exists>e. t1 = t @ e\<close>
    \<open>\<forall>j. length t \<le> j \<and> j < length t1 \<longrightarrow> tr_imp cs t1 j\<close>
  shows \<open>dstate cs n a1 t1 L \<and> meas n (length t) L \<le> meas n (length t1) L\<close>
proof -
  obtain e where e: \<open>t1 = t @ e\<close> using assms(3) by blast
  have \<open>\<forall>j < length t1. j \<notin> set L \<longrightarrow> tr_imp cs t1 j\<close>
  proof (intro allI impI)
    fix j assume j: \<open>j < length t1\<close> \<open>j \<notin> set L\<close>
    show \<open>tr_imp cs t1 j\<close>
    proof (cases \<open>j < length t\<close>)
      case True
      then show ?thesis using assms(1) j e tr_imp_append by (simp add: dstate_def)
    qed (use assms(4) j in auto)
  qed
  then show ?thesis using assms(1,2) e meas_mono[of \<open>length t\<close> \<open>length t1\<close> n L]
    by (auto simp: dstate_def)
qed

lemma dstate_decide:
  assumes \<open>dstate cs n a t L\<close> \<open>v < n\<close> \<open>a ! v = None\<close> \<open>unat (Lit_var l) = v\<close> \<open>\<not> Lit_neg l\<close>
  shows \<open>dstate cs n (a[v := Some True]) (t @ [l]) (L @ [length t]) \<and>
         meas n (length t) L < meas n (length (t @ [l])) (L @ [length t])\<close>
proof -
  have \<open>tr_ok n (a[v := Some True]) (t @ [l])\<close>
    using tr_ok_push[of n a t l] assms by (simp add: dstate_def)
  moreover have \<open>\<forall>j < length (t @ [l]). j \<notin> set (L @ [length t]) \<longrightarrow> tr_imp cs (t @ [l]) j\<close>
    using assms(1) tr_imp_append by (auto simp: dstate_def less_Suc_eq)
  moreover have \<open>sorted_wrt (<) (L @ [length t])\<close> using assms(1) by (auto simp: dstate_def sorted_wrt_append)
  ultimately show ?thesis using assms(1) meas_decide[of L \<open>length t\<close> n] by (auto simp: dstate_def)
qed

lemma dstate_backtrack:
  assumes \<open>dstate cs n a t (L @ [p])\<close> \<open>\<forall>\<sigma>. agrees a \<sigma> \<longrightarrow> \<not> cnf_sem \<sigma> cs\<close>
    \<open>tr_ok n a2 (take p t)\<close>
  shows \<open>dstate cs n (a2[unat (Lit_var (t ! p)) := Some (Lit_neg (t ! p))]) (take p t @ [lneg (t ! p)]) L \<and>
         meas n (length t) (L @ [p]) < meas n (length (take p t @ [lneg (t ! p)])) L\<close>
proof -
  let ?d = \<open>t ! p\<close>
  have D: \<open>tr_ok n a t\<close> \<open>sorted_wrt (<) (L @ [p])\<close> \<open>p < length t\<close>
    \<open>\<forall>j < length t. j \<notin> set (L @ [p]) \<longrightarrow> tr_imp cs t j\<close>
    using assms(1) by (auto simp: dstate_def)
  have Lp: \<open>\<forall>q \<in> set L. q < p\<close> using D(2) by (simp add: sorted_wrt_append)
  have dn: \<open>unat (Lit_var ?d) < n\<close> using D(1,3) by (simp add: tr_ok_def)
  have dnone: \<open>a2 ! unat (Lit_var ?d) = None\<close>
  proof (rule ccontr)
    assume \<open>a2 ! unat (Lit_var ?d) \<noteq> None\<close>
    then obtain l where l: \<open>l \<in> set (take p t)\<close> \<open>unat (Lit_var l) = unat (Lit_var ?d)\<close>
      using assms(3) dn by (auto simp: tr_ok_def)
    then obtain k where k: \<open>k < p\<close> \<open>l = t ! k\<close> using D(3) by (auto simp: in_set_conv_nth)
    have \<open>distinct (map (\<lambda>l. unat (Lit_var l)) t)\<close> using D(1) by (simp add: tr_ok_def)
    then have \<open>k = p\<close> using l(2) k D(3) by (auto simp: distinct_conv_nth)
    then show False using k by simp
  qed
  have ok: \<open>tr_ok n (a2[unat (Lit_var ?d) := Some (Lit_neg ?d)]) (take p t @ [lneg ?d])\<close>
    using tr_ok_push[of n a2 \<open>take p t\<close> \<open>lneg ?d\<close>] assms(3) dn dnone by (simp add: lneg_def)
  have tp: \<open>take p t @ [lneg ?d] = take p t @ [lneg ?d]\<close> ..
  have imp_new: \<open>tr_imp cs (take p t @ [lneg ?d]) p\<close>
    unfolding tr_imp_def
  proof (intro allI impI)
    fix \<sigma> assume h: \<open>cnf_sem \<sigma> cs \<and> (\<forall>k < p. lit_sem \<sigma> ((take p t @ [lneg ?d]) ! k))\<close>
    have pre: \<open>\<forall>k < p. lit_sem \<sigma> (t ! k)\<close> using h D(3) by (auto simp: nth_append)
    show \<open>lit_sem \<sigma> ((take p t @ [lneg ?d]) ! p)\<close>
    proof (rule ccontr)
      assume \<open>\<not> lit_sem \<sigma> ((take p t @ [lneg ?d]) ! p)\<close>
      then have \<open>lit_sem \<sigma> ?d\<close> using D(3) by (simp add: nth_append lit_sem_def lneg_def)
      then have \<open>\<forall>k < Suc p. lit_sem \<sigma> (t ! k)\<close> using pre less_Suc_eq by auto
      moreover have \<open>\<forall>j. Suc p \<le> j \<longrightarrow> j \<notin> set (L @ [p])\<close> using Lp by auto
      ultimately have \<open>\<forall>k < length t. lit_sem \<sigma> (t ! k)\<close> using tr_all[OF D(4)] h by blast
      then have \<open>agrees a \<sigma>\<close> using tr_ok_agrees_nth[OF D(1)] by blast
      then show False using assms(2) h by blast
    qed
  qed
  have imp: \<open>\<forall>j < length (take p t @ [lneg ?d]). j \<notin> set L \<longrightarrow> tr_imp cs (take p t @ [lneg ?d]) j\<close>
  proof (intro allI impI)
    fix j assume j: \<open>j < length (take p t @ [lneg ?d])\<close> \<open>j \<notin> set L\<close>
    show \<open>tr_imp cs (take p t @ [lneg ?d]) j\<close>
    proof (cases \<open>j = p\<close>)
      case False
      then have jp: \<open>j < p\<close> using j D(3) by simp
      have \<open>tr_imp cs t j\<close> using D(3,4) jp j(2) by simp
      moreover have \<open>t = take p t @ drop p t\<close> by simp
      ultimately have \<open>tr_imp cs (take p t) j\<close> using tr_imp_append[of j \<open>take p t\<close> cs \<open>drop p t\<close>] jp D(3) by simp
      then show ?thesis using tr_imp_append[of j \<open>take p t\<close> cs \<open>[lneg ?d]\<close>] jp D(3) by simp
    qed (use imp_new in simp)
  qed
  have sorted: \<open>sorted_wrt (<) L\<close> using D(2) by (simp add: sorted_wrt_append)
  have lt: \<open>\<forall>q \<in> set L. q < length (take p t @ [lneg ?d])\<close> using Lp D(3) by auto
  have m: \<open>meas n (length t) (L @ [p]) < meas n (Suc p) L\<close>
    using meas_backtrack[OF Lp D(3) tr_ok_length[OF D(1)]] .
  show ?thesis using ok sorted lt imp m D(3) by (simp add: dstate_def)
qed

lemma dstate_unsat:
  assumes \<open>dstate cs n a t []\<close> \<open>\<forall>\<sigma>. agrees a \<sigma> \<longrightarrow> \<not> cnf_sem \<sigma> cs\<close>
  shows \<open>\<not> (\<exists>\<sigma>. cnf_sem \<sigma> cs)\<close>
proof
  assume \<open>\<exists>\<sigma>. cnf_sem \<sigma> cs\<close>
  then obtain \<sigma> where s: \<open>cnf_sem \<sigma> cs\<close> by blast
  have \<open>\<forall>k < length t. lit_sem \<sigma> (t ! k)\<close> using tr_all[of t \<open>[]\<close> cs \<sigma> 0] assms(1) s by (simp add: dstate_def)
  then show False using tr_ok_agrees_nth assms s by (metis dstate_def)
qed

text \<open>The result of \<^verbatim>\<open>propagate\<close> from the trail \<open>t\<close> over \<open>n\<close> variables: the new entries follow
  from the clauses and the entries before them; on a conflict no assignment that agrees with \<open>a1\<close>
  satisfies the clauses, otherwise no clause is in conflict or unit.\<close>
definition dprop_post :: \<open>Lit list list \<Rightarrow> Lit list \<Rightarrow> nat \<Rightarrow> bool option list \<Rightarrow> Lit list \<Rightarrow> bool \<Rightarrow> bool\<close> where
  \<open>dprop_post cs t n a1 t1 b \<equiv> tr_ok n a1 t1 \<and> (\<exists>e. t1 = t @ e) \<and>
     (\<forall>j. length t \<le> j \<and> j < length t1 \<longrightarrow> tr_imp cs t1 j) \<and>
     (\<not> b \<longrightarrow> (\<forall>\<sigma>. agrees a1 \<sigma> \<longrightarrow> \<not> cnf_sem \<sigma> cs)) \<and> (b \<longrightarrow> dpll_quiet a1 cs)\<close>

lemma dpll_prop_loop:
  assumes \<open>dpll_wf n cs\<close> \<open>tr_ok n r (t @ e)\<close>
    \<open>\<forall>j. length t \<le> j \<and> j < length t + length e \<longrightarrow> tr_imp cs (t @ e) j\<close> \<open>tpass_m cs r (t @ e) = (a1, t1, b)\<close>
    \<open>n < 2 ^ 64\<close>
  shows \<open>(\<not> b \<or> (word_of_nat (length t1) :: 64 word) = word_of_nat (length t) + word_of_nat (length e) \<longrightarrow>
            dprop_post cs t n a1 t1 b) \<and>
         tr_ok n a1 t1 \<and> (\<exists>e. t1 = t @ e) \<and> (\<forall>j. length t \<le> j \<and> j < length t1 \<longrightarrow> tr_imp cs t1 j) \<and>
         ((word_of_nat (length t1) :: 64 word) \<noteq> word_of_nat (length t) + word_of_nat (length e) \<longrightarrow>
            length t + length e < length t1) \<and>
         length t1 \<le> n\<close>
proof -
  have i: \<open>\<forall>j. length t \<le> j \<and> j < length (t @ e) \<longrightarrow> tr_imp cs (t @ e) j\<close> using assms(3) by simp
  note P = dpll_prop_iter[OF assms(1,2) exI[of _ e] i assms(4)]
  have l1: \<open>length t1 < 2 ^ 64\<close> and l0: \<open>length t + length e < 2 ^ 64\<close>
    using P assms(5) by simp_all
  have u1: \<open>unat (word_of_nat (length t1) :: 64 word) = length t1\<close>
    using l1 by (simp add: unat_of_nat_eq)
  have u2: \<open>unat (word_of_nat (length t + length e) :: 64 word) = length t + length e\<close>
    by (rule unat_of_nat_eq) (use l0 in simp)
  note u = u1 u2
  have eq: \<open>(word_of_nat (length t1) :: 64 word) = word_of_nat (length t) + word_of_nat (length e) \<longleftrightarrow>
      length t1 = length t + length e\<close>
    using u by (metis of_nat_add)
  show ?thesis using P eq by (auto simp: dprop_post_def)
qed

lemma take_length_le:
  assumes \<open>r = take (length r) t\<close>
  shows \<open>length r \<le> length t\<close>
proof -
  have \<open>length r = length (take (length r) t)\<close> using arg_cong[OF assms, of length] .
  then show ?thesis by (simp add: min_def split: if_splits)
qed

lemma tr_ok_pop_take:
  assumes \<open>tr_ok n a t'\<close> \<open>t' = take (length t') t\<close> \<open>t' \<noteq> []\<close>
  shows \<open>tr_ok n (a[unat (Lit_var (last t')) := None]) (butlast t') \<and>
         butlast t' = take (length (butlast t')) t\<close>
proof -
  have \<open>t' = butlast t' @ [last t']\<close> using assms(3) by simp
  then have \<open>tr_ok n (a[unat (Lit_var (last t')) := None]) (butlast t')\<close>
    using tr_ok_pop[of n a \<open>butlast t'\<close> \<open>last t'\<close>] assms(1) by simp
  moreover have \<open>butlast t' = take (length (butlast t')) t\<close>
  proof -
    have b1: \<open>butlast t' = take (length t' - 1) t'\<close> by (rule butlast_conv_take)
    have b2: \<open>take (length t' - 1) t' = take (length t' - 1) t\<close>
      using arg_cong[OF assms(2), of \<open>take (length t' - 1)\<close>] by (simp add: min_def)
    show ?thesis unfolding length_butlast by (rule trans[OF b1 b2])
  qed
  ultimately show ?thesis by blast
qed

lemma dpll_bt_step:
  assumes \<open>tr_ok n a' r\<close> \<open>r = take (length r) t\<close> \<open>unat p < length r\<close>
  shows \<open>butlast r = take (length r - Suc 0) t \<and>
         tr_ok n (a'[unat (Lit_var (last r)) := None]) (butlast r) \<and> unat (Lit_var (last r)) < length a'\<close>
proof -
  have ne: \<open>r \<noteq> []\<close> using assms(3) by auto
  note P = tr_ok_pop_take[OF assms(1,2) ne]
  have \<open>unat (Lit_var (last r)) < length a'\<close>
    using assms(1) last_in_set[OF ne] by (auto simp: tr_ok_def)
  moreover have \<open>butlast r = take (length r - Suc 0) t\<close>
    using conjunct2[OF P] by (simp only: length_butlast One_nat_def)
  ultimately show ?thesis using conjunct1[OF P] by blast
qed


subsection \<open>The iterations of the search loop\<close>

lemma dstate_tr: \<open>dstate cs N r ra L \<Longrightarrow> tr_ok N r ra \<and> length r = N \<and> length ra \<le> N\<close>
  using tr_ok_length by (auto simp: dstate_def tr_ok_def)

lemma dpll_facts:
  assumes \<open>dstate cs N r ra L\<close> \<open>dprop_post cs ra (length r) a1 t1 b\<close>
  shows \<open>length r = N \<and> length a1 = N \<and> length t1 \<le> N \<and> tr_ok N a1 t1 \<and> dstate cs N a1 t1 L \<and>
         meas N (length ra) L \<le> meas N (length t1) L \<and> (b \<longrightarrow> dpll_quiet a1 cs) \<and>
         (\<not> b \<longrightarrow> (\<forall>\<sigma>. agrees a1 \<sigma> \<longrightarrow> \<not> cnf_sem \<sigma> cs))\<close>
proof -
  have r: \<open>length r = N\<close> using dstate_tr[OF assms(1)] by simp
  have P: \<open>tr_ok N a1 t1\<close> \<open>\<exists>e. t1 = ra @ e\<close> \<open>\<forall>j. length ra \<le> j \<and> j < length t1 \<longrightarrow> tr_imp cs t1 j\<close>
    \<open>\<not> b \<longrightarrow> (\<forall>\<sigma>. agrees a1 \<sigma> \<longrightarrow> \<not> cnf_sem \<sigma> cs)\<close> \<open>b \<longrightarrow> dpll_quiet a1 cs\<close>
    using assms(2) r by (simp_all add: dprop_post_def)
  note D = dstate_prop[OF assms(1) P(1-3)]
  show ?thesis using r P D tr_ok_length[OF P(1)] by (simp add: tr_ok_def)
qed

subsection \<open>Propagation over the watches\<close>

text \<open>The watches only choose which clauses propagation visits: every implied entry and every
  conflict is confirmed by the status of its clause. So the result of \<^verbatim>\<open>visit\<close> and
  \<^verbatim>\<open>wpropagate\<close> from the trail \<open>t\<close> is described without the watches: the new entries follow from
  the clauses and the entries before them, and on a conflict no assignment that agrees with \<open>a1\<close>
  satisfies the clauses.\<close>
definition wprop_inv :: \<open>Lit list list \<Rightarrow> Lit list \<Rightarrow> nat \<Rightarrow> bool option list \<Rightarrow> Lit list \<Rightarrow> bool\<close> where
  \<open>wprop_inv cs t n a1 t1 \<equiv> tr_ok n a1 t1 \<and> (\<exists>e. t1 = t @ e) \<and>
     (\<forall>j. length t \<le> j \<and> j < length t1 \<longrightarrow> tr_imp cs t1 j)\<close>

definition wprop_post :: \<open>Lit list list \<Rightarrow> Lit list \<Rightarrow> nat \<Rightarrow> bool option list \<Rightarrow> Lit list \<Rightarrow> bool \<Rightarrow> bool\<close> where
  \<open>wprop_post cs t n a1 t1 b \<equiv> wprop_inv cs t n a1 t1 \<and> (\<not> b \<longrightarrow> (\<forall>\<sigma>. agrees a1 \<sigma> \<longrightarrow> \<not> cnf_sem \<sigma> cs))\<close>

lemma wprop_refl: \<open>tr_ok n a t \<Longrightarrow> wprop_inv cs t n a t\<close>
  by (auto simp: wprop_inv_def)

lemma wprop_trans:
  assumes \<open>wprop_inv cs t n a1 t1\<close> \<open>wprop_inv cs t1 n a2 t2\<close>
  shows \<open>wprop_inv cs t n a2 t2\<close>
proof -
  obtain e1 where e1: \<open>t1 = t @ e1\<close> using assms(1) by (auto simp: wprop_inv_def)
  obtain e2 where e2: \<open>t2 = t1 @ e2\<close> using assms(2) by (auto simp: wprop_inv_def)
  have \<open>\<forall>j. length t \<le> j \<and> j < length t2 \<longrightarrow> tr_imp cs t2 j\<close>
  proof (intro allI impI)
    fix j assume j: \<open>length t \<le> j \<and> j < length t2\<close>
    show \<open>tr_imp cs t2 j\<close>
    proof (cases \<open>j < length t1\<close>)
      case True
      then have \<open>tr_imp cs t1 j\<close> using assms(1) j by (simp add: wprop_inv_def)
      then show ?thesis using tr_imp_append[OF True, of cs e2] e2 by simp
    qed (use assms(2) j in \<open>simp add: wprop_inv_def\<close>)
  qed
  then show ?thesis using assms(2) e1 e2 by (auto simp: wprop_inv_def)
qed

lemma wprop_unit:
  assumes \<open>wprop_inv cs t n a1 t1\<close> \<open>c \<in> set cs\<close> \<open>lits_lt n c\<close> \<open>status_m a1 c None False = Status_Unit l\<close>
  shows \<open>wprop_inv cs t n (a1[unat (Lit_var l) := Some (\<not> Lit_neg l)]) (t1 @ [l]) \<and>
         unat (Lit_var l) < length a1\<close>
proof -
  have ok: \<open>tr_ok n a1 t1\<close> using assms(1) by (simp add: wprop_inv_def)
  have i: \<open>unat (Lit_var l) < n\<close> using dpll_status_Unit_var[OF assms(4,3)] .
  have nn: \<open>a1 ! unat (Lit_var l) = None\<close>
    using dpll_status_Unit[OF assms(4)] by (auto simp: lit_value_m_def split: option.splits)
  have imp: \<open>tr_imp cs (t1 @ [l]) (length t1)\<close> using dpll_unit_imp[OF assms(4,3,2) ok] .
  have \<open>wprop_inv cs t1 n (a1[unat (Lit_var l) := Some (\<not> Lit_neg l)]) (t1 @ [l])\<close>
    using tr_ok_push[OF ok i nn] imp by (auto simp: wprop_inv_def less_Suc_eq)
  then show ?thesis using wprop_trans[OF assms(1)] i ok by (simp add: tr_ok_def)
qed

lemma wprop_conflict:
  assumes \<open>tr_ok n a1 t1\<close> \<open>c \<in> set cs\<close> \<open>lits_lt n c\<close> \<open>status_m a1 c None False = Status_Conflict\<close>
  shows \<open>\<forall>\<sigma>. agrees a1 \<sigma> \<longrightarrow> \<not> cnf_sem \<sigma> cs\<close>
  using dpll_conflict_unsat[OF assms(4) _ assms(2)] assms(1,3) by (simp add: tr_ok_def)

text \<open>The trail of a total assignment names every variable, so an extension of it is total too.\<close>
lemma tr_ok_total_ext:
  assumes \<open>tr_ok n a1 t1\<close> \<open>tr_ok n a2 (t1 @ e)\<close> \<open>\<forall>v < n. a1 ! v \<noteq> None\<close>
  shows \<open>\<forall>v < n. a2 ! v \<noteq> None\<close>
proof (intro allI impI)
  fix v assume v: \<open>v < n\<close>
  then obtain l where l: \<open>l \<in> set t1\<close> \<open>unat (Lit_var l) = v\<close> using assms(1,3) by (auto simp: tr_ok_def)
  then have \<open>a2 ! v = Some (\<not> Lit_neg l)\<close> using assms(2) by (auto simp: tr_ok_def)
  then show \<open>a2 ! v \<noteq> None\<close> by simp
qed

lemma unat64_dbl:
  fixes w :: \<open>64 word\<close>
  assumes \<open>unat w < 9223372036854775808\<close>
  shows \<open>unat (2 * w) = 2 * unat w\<close>
  using assms unat_mult_lem[of \<open>2 :: 64 word\<close> w] by simp

lemma unat64_dbl1:
  fixes w :: \<open>64 word\<close>
  assumes \<open>unat w < 9223372036854775808\<close>
  shows \<open>unat (2 * w + 1) = Suc (2 * unat w)\<close>
proof -
  have \<open>unat (2 * w) + unat (1 :: 64 word) < 2 ^ LENGTH(64)\<close> using assms unat64_dbl[OF assms] by simp
  then show ?thesis using unat_add_lem[of \<open>2 * w\<close> 1] unat64_dbl[OF assms] by simp
qed

lemma len2_0: \<open>2 \<le> length xs \<Longrightarrow> xs \<noteq> []\<close>
  by auto

lemma len2_1: \<open>2 \<le> length xs \<Longrightarrow> Suc 0 < length xs\<close>
  by simp

lemma unat64_lt: \<open>unat (x :: 64 word) < 2 ^ 64\<close>
  using unat_lt2p[of x] by simp
end
