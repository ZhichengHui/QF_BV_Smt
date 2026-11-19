theory QFBV_Dpll
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

section \<open>DPLL: contracts\<close>

context QFBV_ctx
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
  \<open>Lit list list \<Rightarrow> bool option list \<Rightarrow> Lit list \<Rightarrow> ('s, bool option list \<times> Lit list \<times> bool \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>dpll_propagate_pass_contract cs a t \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
          \<langle>(\<forall>c \<in> set cs. lits_lt (length a) c \<and> length c + 2 \<le> urust_fuel \<and> length c < 2 ^ 64) \<and>
           length cs + 2 \<le> urust_fuel \<and> length cs < 2 ^ 64 \<and> length a < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>case r of (a1, t1, b, _) \<Rightarrow> tpass_m cs a t = (a1, t1, b)\<rangle>)\<close>

lemma dpll_propagate_pass_spec [crush_specs]:
  shows \<open>\<Gamma>; propagate_pass cs a t \<Turnstile>\<^sub>F dpll_propagate_pass_contract cs a t\<close>
  apply (crush_boot f: propagate_pass_def contract: dpll_propagate_pass_contract_def)
  apply (crush_base inline: len_def)
  subgoal for a_ref t_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>ga a' gt t' gi i. a_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>a' \<star> t_ref \<mapsto>\<langle>\<top>\<rangle> gt\<down>t' \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
               can_alloc_reference \<star>
               \<langle>unat i \<le> length cs \<and> length a' = length a \<and>
                tpass_m cs a t = tpass_m (drop (unat i) cs) a' t' \<and> length cs - unat i \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>ga a' gt t' gi i. a_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>a' \<star> t_ref \<mapsto>\<langle>\<top>\<rangle> gt\<down>t' \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
               can_alloc_reference \<star>
               \<langle>unat i < length cs \<and> length a' = length a \<and>
                tpass_m cs a t = tpass_m (drop (unat i) cs) a' t' \<and> length cs - unat i \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>case r of (a1, t1, b, _) \<Rightarrow> tpass_m cs a t = (a1, t1, b)\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base wp split: Status.splits inline: vec_push_def
        simp add: word_less_nat_alt unat_of_nat_eq dpll_unat_Suc)
    apply (auto simp add: dpll_tpass_drop ASSUMPTION_def intro: dpll_unit_var_nth)
    done
  done

definition dpll_propagate_contract ::
  \<open>Lit list list \<Rightarrow> bool option list \<Rightarrow> Lit list \<Rightarrow> ('s, bool option list \<times> Lit list \<times> bool \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>dpll_propagate_contract cs a t \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
          \<langle>dpll_cs_ok cs (length a) \<and> length cs + 2 \<le> urust_fuel \<and> length cs < 2 ^ 64 \<and>
           length a + 2 \<le> urust_fuel \<and> length a < 2 ^ 64 \<and> tr_ok (length a) a t\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>case r of (a1, t1, b, _) \<Rightarrow> dprop_post cs t (length a) a1 t1 b\<rangle>)\<close>

lemma dpll_propagate_spec [crush_specs]:
  shows \<open>\<Gamma>; propagate cs a t \<Turnstile>\<^sub>F dpll_propagate_contract cs a t\<close>
  apply (crush_boot f: propagate_def contract: dpll_propagate_contract_def)
  apply (crush_base simp add: dpll_cs_ok_def)
  subgoal for a_ref t_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>ga a' gt t'. a_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>a' \<star> t_ref \<mapsto>\<langle>\<top>\<rangle> gt\<down>t' \<star> can_alloc_reference \<star>
               \<langle>tr_ok (length a) a' t' \<and> (\<exists>e. t' = t @ e) \<and>
                (\<forall>j. length t \<le> j \<and> j < length t' \<longrightarrow> tr_imp cs t' j) \<and> length a - length t' < k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>ga a' gt t'. a_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>a' \<star> t_ref \<mapsto>\<langle>\<top>\<rangle> gt\<down>t' \<star> can_alloc_reference \<star>
               \<langle>tr_ok (length a) a' t' \<and> (\<exists>e. t' = t @ e) \<and>
                (\<forall>j. length t \<le> j \<and> j < length t' \<longrightarrow> tr_imp cs t' j) \<and> length a - length t' < Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>case r of (a1, t1, b, _) \<Rightarrow> dprop_post cs t (length a) a1 t1 b\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base wp split: prod.splits tnil.splits)
    subgoal for k ga gt e r aa aaa ab
      using dpll_prop_loop[of \<open>length a\<close> cs r t e aa aaa ab] by (auto simp: dpll_wf_def)
    subgoal for k ga gt e r aa aaa ab
      using dpll_prop_loop[of \<open>length a\<close> cs r t e aa aaa ab] by (auto simp: dpll_wf_def)
    subgoal for k ga gt e r aa aaa ab
      using dpll_prop_loop[of \<open>length a\<close> cs r t e aa aaa ab] by (auto simp: dpll_wf_def)
    subgoal for k ga gt e r aa aaa ab
      using dpll_prop_loop[of \<open>length a\<close> cs r t e aa aaa ab] by (auto simp: dpll_wf_def)
    subgoal for k ga gt e r aa aaa ab
      using dpll_prop_loop[of \<open>length a\<close> cs r t e aa aaa ab] by (auto simp: dpll_wf_def)
    subgoal for k ga gt e r aa aaa ab
      using dpll_prop_loop[of \<open>length a\<close> cs r t e aa aaa ab] by (auto simp: dpll_wf_def)
    subgoal by (simp add: tr_ok_def)
    subgoal by (auto simp: tr_ok_def)
    done
  done

definition dpll_backtrack_contract ::
  \<open>bool option list \<Rightarrow> Lit list \<Rightarrow> 64 word \<Rightarrow> ('s, bool option list \<times> Lit list \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>dpll_backtrack_contract a t p \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
          \<langle>tr_ok (length a) a t \<and> unat p \<le> length t \<and> length t + 2 \<le> urust_fuel \<and> length t < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>case r of (a1, t1, _) \<Rightarrow> tr_ok (length a) a1 t1 \<and> t1 = take (unat p) t\<rangle>)\<close>

lemma dpll_backtrack_spec [crush_specs]:
  shows \<open>\<Gamma>; backtrack a t p \<Turnstile>\<^sub>F dpll_backtrack_contract a t p\<close>
  apply (crush_boot f: backtrack_def contract: dpll_backtrack_contract_def)
  apply (crush_base inline: len_def)
  subgoal for a_ref t_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>ga a' gt t'. a_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>a' \<star> t_ref \<mapsto>\<langle>\<top>\<rangle> gt\<down>t' \<star> can_alloc_reference \<star>
               \<langle>tr_ok (length a) a' t' \<and> t' = take (length t') t \<and> unat p \<le> length t' \<and>
                length t' - unat p \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>ga a' gt t'. a_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>a' \<star> t_ref \<mapsto>\<langle>\<top>\<rangle> gt\<down>t' \<star> can_alloc_reference \<star>
               \<langle>tr_ok (length a) a' t' \<and> t' = take (length t') t \<and> unat p < length t' \<and>
                length t' - unat p \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base wp split: option.splits inline: vec_pop_def simp add: word_less_nat_alt)
    subgoal for k ga a' gt r
      using dpll_bt_step[of \<open>length a\<close> a' r t p] by blast
    subgoal for k ga a' gt r
      using dpll_bt_step[of \<open>length a\<close> a' r t p] by blast
    subgoal for k ga a' gt r
      using dpll_bt_step[of \<open>length a\<close> a' r t p] by blast
    subgoal for k ga a' gt r
      using dpll_bt_step[of \<open>length a\<close> a' r t p] by blast
    subgoal for k ga a' gt r
      using take_length_le[of r t] by (simp add: unat_of_nat_eq)
    subgoal for k ga a' gt r
      using take_length_le[of r t] by (simp add: unat_of_nat_eq)
    done
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

definition dpll_lit_index_contract :: \<open>Lit \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>dpll_lit_index_contract l \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>2 * unat (Lit_var l) + 1 < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>unat r = 2 * unat (Lit_var l) + (if Lit_neg l then 1 else 0)\<rangle>)\<close>

lemma unat64_dbl_lt:
  fixes r :: \<open>64 word\<close>
  assumes \<open>unat r < m\<close> \<open>m < 9223372036854775808\<close>
  shows \<open>unat (2 * r) = 2 * unat r \<and> unat (2 * r + 1) = Suc (2 * unat r)\<close>
  using assms unat64_dbl[of r] unat64_dbl1[of r] by simp

lemma nth_var_lt:
  assumes \<open>\<forall>i < length cs. \<forall>j < length (cs ! i).
             2 * unat (Lit_var (cs ! i ! j)) < 18446744073709551615 \<and> unat (Lit_var (cs ! i ! j)) < m\<close>
    \<open>i < length cs\<close> \<open>j < length (cs ! i)\<close>
  shows \<open>Suc (2 * unat (Lit_var (cs ! i ! j))) < 2 * m\<close>
  using assms by fastforce

lemma div2_lt: \<open>x < 2 * L \<Longrightarrow> x div 2 < L\<close> for x L :: nat
  by linarith

lemma even_Suc_lt: \<open>x < 2 * L \<Longrightarrow> x mod 2 = 0 \<Longrightarrow> Suc x < 2 * L\<close> for x L :: nat
  by presburger

text \<open>The facts about the clauses that the loops over the watches use, one clause at a time.\<close>
definition wcs_ok :: \<open>Lit list list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>wcs_ok cs n F \<equiv> \<forall>i < length cs. lits_lt n (cs ! i) \<and> length (cs ! i) + 2 \<le> F \<and>
     length (cs ! i) < 18446744073709551616 \<and>
     (\<forall>j < length (cs ! i). 2 * unat (Lit_var (cs ! i ! j)) < 18446744073709551615 \<and>
        unat (Lit_var (cs ! i ! j)) < n)\<close>

lemma lits_lt_nth2:
  assumes \<open>\<forall>c \<in> set cs. lits_lt n c \<and> Q c\<close> \<open>i < length cs\<close> \<open>j < length (cs ! i)\<close>
  shows \<open>unat (Lit_var (cs ! i ! j)) < n\<close>
  using assms nth_mem by (fastforce simp: lits_lt_def)

lemma dpll_lit_index_spec [crush_specs]:
  shows \<open>\<Gamma>; lit_index l \<Turnstile>\<^sub>F dpll_lit_index_contract l\<close>
  apply (crush_boot f: lit_index_def contract: dpll_lit_index_contract_def)
  apply (crush_base)
  apply (auto simp add: unat64_dbl unat64_dbl1 is_sat_pure_precise elim!: is_sat_splitE)
  done

definition dpll_watch_init_contract ::
  \<open>Lit list list \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word list \<times> 64 word list \<times> 64 word list \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>dpll_watch_init_contract cs n \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
          \<langle>(\<forall>c \<in> set cs. lits_lt (unat n) c \<and> length c < 2 ^ 64) \<and> 2 * length cs < 2 ^ 64 \<and>
           2 * unat n < 2 ^ 64 \<and> length cs + 2 \<le> urust_fuel\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>case r of (p, nx, h, _) \<Rightarrow>
             length p = 2 * length cs \<and> length nx = 2 * length cs \<and> length h = 2 * unat n\<rangle>)\<close>

lemma dpll_watch_init_spec [crush_specs]:
  shows \<open>\<Gamma>; watch_init cs n \<Turnstile>\<^sub>F dpll_watch_init_contract cs n\<close>
  apply (crush_boot f: watch_init_def contract: dpll_watch_init_contract_def)
  apply (crush_base inline: len_def)
  subgoal for p_ref nx_ref h_ref c_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gp p gn nx gh h gc c. p_ref \<mapsto>\<langle>\<top>\<rangle> gp\<down>p \<star> nx_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>nx \<star>
               h_ref \<mapsto>\<langle>\<top>\<rangle> gh\<down>h \<star> c_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c \<star> can_alloc_reference \<star>
               \<langle>(\<forall>i < length cs. length (cs ! i) < 18446744073709551616 \<and>
                  (\<forall>j < length (cs ! i). 2 * unat (Lit_var (cs ! i ! j)) < 18446744073709551615 \<and>
                     unat (Lit_var (cs ! i ! j)) < unat n)) \<and>
                length p = 2 * length cs \<and> length nx = 2 * length cs \<and> length h = 2 * unat n \<and>
                unat c \<le> length cs \<and> length cs - unat c \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gp p gn nx gh h gc c. p_ref \<mapsto>\<langle>\<top>\<rangle> gp\<down>p \<star> nx_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>nx \<star>
               h_ref \<mapsto>\<langle>\<top>\<rangle> gh\<down>h \<star> c_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c \<star> can_alloc_reference \<star>
               \<langle>(\<forall>i < length cs. length (cs ! i) < 18446744073709551616 \<and>
                  (\<forall>j < length (cs ! i). 2 * unat (Lit_var (cs ! i ! j)) < 18446744073709551615 \<and>
                     unat (Lit_var (cs ! i ! j)) < unat n)) \<and>
                length p = 2 * length cs \<and> length nx = 2 * length cs \<and> length h = 2 * unat n \<and>
                unat c < length cs \<and> length cs - unat c \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: word_less_nat_alt unat_of_nat_eq dpll_unat_Suc word_le_nat_alt len2_0 len2_1)
    apply (all \<open>(frule unat64_dbl_lt, assumption)?\<close>)
    apply (auto simp add: unat_of_nat_eq unat64_dbl intro!: nth_var_lt)
    apply (all \<open>(frule lits_lt_nth2, assumption, assumption)?\<close>)
    apply auto
    done
  apply (auto simp add: unat_of_nat_eq)
  done

definition dpll_find_watch_contract ::
  \<open>bool option list \<Rightarrow> Lit list \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word option, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>dpll_find_watch_contract a c i j \<equiv>
     make_function_contract
       (can_alloc_reference \<star> \<langle>lits_lt (length a) c \<and> length c + 2 \<le> urust_fuel \<and> length c < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>case r of None \<Rightarrow> True | Some k \<Rightarrow> unat k < length c\<rangle>)\<close>

lemma dpll_find_watch_spec [crush_specs]:
  shows \<open>\<Gamma>; find_watch a c i j \<Turnstile>\<^sub>F dpll_find_watch_contract a c i j\<close>
  apply (crush_boot f: find_watch_def contract: dpll_find_watch_contract_def)
  apply (crush_base inline: len_def)
  subgoal for k_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>m. \<Squnion>gk k. k_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>k \<star> can_alloc_reference \<star>
               \<langle>unat k \<le> length c \<and> length c - unat k \<le> m\<rangle>\<close> and
        INV'=\<open>\<lambda>m. \<Squnion>gk k. k_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>k \<star> can_alloc_reference \<star>
               \<langle>unat k < length c \<and> length c - unat k \<le> Suc m\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>case r of None \<Rightarrow> True | Some k \<Rightarrow> unat k < length c\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: word_less_nat_alt unat_of_nat_eq dpll_unat_Suc)
    apply (auto simp add: ASSUMPTION_def intro: dpll_lits_lt_nth)
    done
  done

text \<open>The clauses mention only variables below \<open>n\<close>, the watch arrays have their lengths, and the
  fuel covers the loops over a clause and over the slots.\<close>
definition dpll_wpre :: \<open>Lit list list \<Rightarrow> nat \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> bool\<close> where
  \<open>dpll_wpre cs n p nx h \<equiv>
     wcs_ok cs n urust_fuel \<and> length p = 2 * length cs \<and> length nx = 2 * length cs \<and> length h = 2 * n \<and>
     2 * length cs \<le> urust_fuel \<and> 2 * length cs < 2 ^ 64 \<and> 2 * n < 2 ^ 64\<close>

lemma Suc2_lt: \<open>v < L \<Longrightarrow> Suc (2 * v) < 2 * L\<close> for v L :: nat
  by linarith

lemma tr_ok_TB:
  \<open>tr_ok n a t \<Longrightarrow> 2 * n < 2 ^ 64 \<Longrightarrow>
   \<forall>j < length t. 2 * unat (Lit_var (t ! j)) < 18446744073709551615 \<and> unat (Lit_var (t ! j)) < n\<close>
  by (fastforce simp: tr_ok_def dest: nth_mem)

lemma wprop_step:
  assumes \<open>wprop_inv cs t n a' t'\<close> \<open>wprop_post cs t' n a1 t1 b\<close>
  shows \<open>wprop_post cs t n a1 t1 b \<and> wprop_inv cs t n a1 t1 \<and> tr_ok n a1 t1 \<and> length t' \<le> length t1\<close>
  using wprop_trans[OF assms(1)] assms(2) by (auto simp: wprop_post_def wprop_inv_def)

lemma q_suc2:
  \<open>unat q < length t \<Longrightarrow> tr_ok n a t \<Longrightarrow> n < 9223372036854775808 \<Longrightarrow> unat (q + 1) = Suc (unat q)\<close>
  for q :: \<open>64 word\<close>
  using tr_ok_length[of n a t] by (intro dpll_unat_Suc) simp

lemma tb_var: \<open>tr_ok n a t \<Longrightarrow> j < length t \<Longrightarrow> unat (Lit_var (t ! j)) < n\<close>
  by (auto simp: tr_ok_def dest: nth_mem)

lemma tb_dbl:
  \<open>tr_ok n a t \<Longrightarrow> n < 9223372036854775808 \<Longrightarrow> j < length t \<Longrightarrow>
   2 * unat (Lit_var (t ! j)) < 18446744073709551615\<close>
  using tb_var[of n a t j] by simp

definition dpll_set_at_contract ::
  \<open>64 word list \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word list, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>dpll_set_at_contract v i e \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>unat i < length v\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = v[unat i := e]\<rangle>)\<close>

lemma dpll_set_at_spec [crush_specs]:
  shows \<open>\<Gamma>; set_at v i e \<Turnstile>\<^sub>F dpll_set_at_contract v i e\<close>
  apply (crush_boot f: set_at_def contract: dpll_set_at_contract_def)
  apply (crush_base simp add: word_less_nat_alt)
  done

definition dpll_move_watch_contract ::
  \<open>64 word list \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow>
   ('s, 64 word list \<times> 64 word list \<times> 64 word list \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>dpll_move_watch_contract p nx h s x y \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
          \<langle>unat s < length nx \<and> length p = length nx \<and> unat x < length h \<and> unat y < length h \<and>
           length nx < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>case r of (p1, nx1, h1, _) \<Rightarrow> length p1 = length p \<and> length nx1 = length nx \<and> length h1 = length h\<rangle>)\<close>

lemma dpll_move_watch_spec [crush_specs]:
  shows \<open>\<Gamma>; move_watch p nx h s prev x k y \<Turnstile>\<^sub>F dpll_move_watch_contract p nx h s x y\<close>
  apply (crush_boot f: move_watch_def contract: dpll_move_watch_contract_def)
  apply (crush_base inline: len_def simp add: word_less_nat_alt unat_of_nat_eq)
  done

lemma w_odd:
  fixes s :: \<open>64 word\<close>
  assumes \<open>s mod 2 = 1\<close> \<open>unat s < M\<close>
  shows \<open>1 \<le> s \<and> unat (s - 1) < M\<close>
proof -
  have \<open>unat s mod 2 = 1\<close> using assms(1) unat_mod[of s 2] by simp
  then have \<open>unat s \<noteq> 0\<close> by auto
  then have s1: \<open>1 \<le> s\<close> by (simp add: word_le_nat_alt)
  then have \<open>unat (s - 1) = unat s - 1\<close> by (simp add: unat_sub)
  then show ?thesis using s1 assms(2) by simp
qed

lemma w_even:
  fixes s :: \<open>64 word\<close>
  assumes \<open>even s\<close> \<open>unat s < 2 * L\<close> \<open>L < 9223372036854775808\<close>
  shows \<open>unat (s + 1) < 2 * L\<close>
proof -
  have \<open>s mod 2 = 0\<close> using assms(1) by (simp add: even_iff_mod_2_eq_zero)
  then have \<open>unat s mod 2 = 0\<close> using unat_mod[of s 2] by simp
  moreover have \<open>unat (s + 1) = Suc (unat s)\<close> using assms(2,3) by (intro dpll_unat_Suc) simp
  ultimately show ?thesis using even_Suc_lt assms(2) by simp
qed

lemma vs_refl: \<open>tr_ok n a t \<Longrightarrow> wprop_post cs t n a t True\<close>
  by (simp add: wprop_post_def wprop_refl)

lemma vs_conflict:
  \<open>tr_ok n a t \<Longrightarrow> i < length cs \<Longrightarrow> \<forall>i < length cs. lits_lt n (cs ! i) \<and> R i \<Longrightarrow>
   status_m a (cs ! i) None False = Status_Conflict \<Longrightarrow> wprop_post cs t n a t False\<close>
  using wprop_conflict[of n a t \<open>cs ! i\<close> cs] by (simp add: wprop_post_def wprop_refl)

lemma vs_unit:
  \<open>tr_ok n a t \<Longrightarrow> i < length cs \<Longrightarrow> \<forall>i < length cs. lits_lt n (cs ! i) \<and> R i \<Longrightarrow>
   status_m a (cs ! i) None False = Status_Unit l \<Longrightarrow>
   wprop_post cs t n (a[unat (Lit_var l) := Some (\<not> Lit_neg l)]) (t @ [l]) True\<close>
  using wprop_unit[OF wprop_refl, of n a t \<open>cs ! i\<close> cs l] by (simp add: wprop_post_def)

lemma vs_unit_var:
  \<open>i < length cs \<Longrightarrow> \<forall>i < length cs. lits_lt n (cs ! i) \<and> R i \<Longrightarrow>
   status_m a (cs ! i) None False = Status_Unit l \<Longrightarrow> unat (Lit_var l) < n\<close>
  using dpll_status_Unit_var by blast

definition dpll_visit_slot_contract ::
  \<open>Lit list list \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> bool option list \<Rightarrow> Lit list \<Rightarrow> 64 word \<Rightarrow>
   64 word \<Rightarrow> ('s, 64 word list \<times> 64 word list \<times> 64 word list \<times> bool option list \<times> Lit list \<times> bool \<times> bool \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>dpll_visit_slot_contract cs p nx h a t x s \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
          \<langle>dpll_wpre cs (length a) p nx h \<and> unat x < length h \<and> unat s < 2 * length cs \<and> tr_ok (length a) a t\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>case r of (p1, nx1, h1, a1, t1, _, b, _) \<Rightarrow>
             dpll_wpre cs (length a) p1 nx1 h1 \<and> length a1 = length a \<and> wprop_post cs t (length a) a1 t1 b\<rangle>)\<close>

lemma dpll_visit_slot_spec [crush_specs]:
  shows \<open>\<Gamma>; visit_slot cs p nx h a t x s prev \<Turnstile>\<^sub>F dpll_visit_slot_contract cs p nx h a t x s\<close>
  apply (crush_boot f: visit_slot_def contract: dpll_visit_slot_contract_def)
  apply (crush_base wp split: option.splits Status.splits inline: vec_push_def
      simp add: dpll_wpre_def wcs_ok_def word_less_nat_alt unat_of_nat_eq unat_div unat_mod div2_lt
        even_Suc_lt Suc2_lt)
  apply (all \<open>(frule div2_lt[where L=\<open>length cs\<close>])?\<close>)
  apply (auto intro: vs_refl vs_conflict vs_unit vs_unit_var w_odd[THEN conjunct1] w_odd[THEN conjunct2]
      w_even)
  done

definition dpll_visit_contract ::
  \<open>Lit list list \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> bool option list \<Rightarrow> Lit list \<Rightarrow> 64 word \<Rightarrow>
   ('s, 64 word list \<times> 64 word list \<times> 64 word list \<times> bool option list \<times> Lit list \<times> bool \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>dpll_visit_contract cs p nx h a t x \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
          \<langle>dpll_wpre cs (length a) p nx h \<and> unat x < length h \<and> tr_ok (length a) a t\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>case r of (p1, nx1, h1, a1, t1, b, _) \<Rightarrow>
             dpll_wpre cs (length a) p1 nx1 h1 \<and> length a1 = length a \<and> wprop_post cs t (length a) a1 t1 b\<rangle>)\<close>

lemma dpll_visit_spec [crush_specs]:
  shows \<open>\<Gamma>; visit cs p nx h a t x \<Turnstile>\<^sub>F dpll_visit_contract cs p nx h a t x\<close>
  apply (crush_boot f: visit_def contract: dpll_visit_contract_def)
  apply (crush_base inline: len_def simp add: dpll_wpre_def)
  subgoal for p_ref nx_ref h_ref a_ref t_ref s_ref pr_ref st_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gp p' gn nx' gh h' ga a' gt t' gs s' gr pr gq st.
               p_ref \<mapsto>\<langle>\<top>\<rangle> gp\<down>p' \<star> nx_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>nx' \<star> h_ref \<mapsto>\<langle>\<top>\<rangle> gh\<down>h' \<star>
               a_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>a' \<star> t_ref \<mapsto>\<langle>\<top>\<rangle> gt\<down>t' \<star>
               s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> pr_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>pr \<star> st_ref \<mapsto>\<langle>\<top>\<rangle> gq\<down>st \<star>
               can_alloc_reference \<star>
               \<langle>dpll_wpre cs (length a) p' nx' h' \<and> length nx' = length nx \<and> length h' = length h \<and>
                length a' = length a \<and> tr_ok (length a) a' t' \<and> wprop_inv cs t (length a) a' t' \<and>
                unat st \<le> length nx \<and> (unat s' < length nx \<longrightarrow> length nx - unat st \<le> k)\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gp p' gn nx' gh h' ga a' gt t' gs s' gr pr gq st.
               p_ref \<mapsto>\<langle>\<top>\<rangle> gp\<down>p' \<star> nx_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>nx' \<star> h_ref \<mapsto>\<langle>\<top>\<rangle> gh\<down>h' \<star>
               a_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>a' \<star> t_ref \<mapsto>\<langle>\<top>\<rangle> gt\<down>t' \<star>
               s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> pr_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>pr \<star> st_ref \<mapsto>\<langle>\<top>\<rangle> gq\<down>st \<star>
               can_alloc_reference \<star>
               \<langle>dpll_wpre cs (length a) p' nx' h' \<and> length nx' = length nx \<and> length h' = length h \<and>
                length a' = length a \<and> tr_ok (length a) a' t' \<and> wprop_inv cs t (length a) a' t' \<and>
                unat s' < length nx \<and> unat st < length nx \<and> length nx - unat st \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star>
          \<langle>case r of (p1, nx1, h1, a1, t1, b, _) \<Rightarrow>
             dpll_wpre cs (length a) p1 nx1 h1 \<and> length a1 = length a \<and> wprop_post cs t (length a) a1 t1 b\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base wp split: prod.splits tnil.splits simp add: word_less_nat_alt unat_of_nat_eq dpll_unat_Suc)
    apply (all \<open>(frule (1) wprop_step)?\<close>)
    apply (auto simp add: dpll_wpre_def unat64_dbl unat_of_nat_eq wprop_post_def intro: wprop_refl)
    done
  done

definition dpll_wpropagate_contract ::
  \<open>Lit list list \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> bool option list \<Rightarrow> Lit list \<Rightarrow> 64 word \<Rightarrow>
   ('s, 64 word list \<times> 64 word list \<times> 64 word list \<times> bool option list \<times> Lit list \<times> 64 word \<times> bool \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>dpll_wpropagate_contract cs p nx h a t q \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
          \<langle>dpll_wpre cs (length a) p nx h \<and> length a + 2 \<le> urust_fuel \<and> tr_ok (length a) a t \<and>
           unat q \<le> length t\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>case r of (p1, nx1, h1, a1, t1, q1, b, _) \<Rightarrow>
             dpll_wpre cs (length a) p1 nx1 h1 \<and> length a1 = length a \<and> wprop_post cs t (length a) a1 t1 b \<and>
             unat q1 \<le> length t1\<rangle>)\<close>

lemma dpll_wpropagate_spec [crush_specs]:
  shows \<open>\<Gamma>; wpropagate cs p nx h a t q \<Turnstile>\<^sub>F dpll_wpropagate_contract cs p nx h a t q\<close>
  apply (crush_boot f: wpropagate_def contract: dpll_wpropagate_contract_def)
  apply (crush_base inline: len_def simp add: dpll_wpre_def)
  subgoal for p_ref nx_ref h_ref a_ref t_ref q_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gp p' gn nx' gh h' ga a' gt t' gq q'.
               p_ref \<mapsto>\<langle>\<top>\<rangle> gp\<down>p' \<star> nx_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>nx' \<star> h_ref \<mapsto>\<langle>\<top>\<rangle> gh\<down>h' \<star>
               a_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>a' \<star> t_ref \<mapsto>\<langle>\<top>\<rangle> gt\<down>t' \<star> q_ref \<mapsto>\<langle>\<top>\<rangle> gq\<down>q' \<star>
               can_alloc_reference \<star>
               \<langle>dpll_wpre cs (length a) p' nx' h' \<and> length h' = length h \<and>
                length a' = length a \<and> tr_ok (length a) a' t' \<and> wprop_inv cs t (length a) a' t' \<and>
                (\<forall>j < length t'. 2 * unat (Lit_var (t' ! j)) < 18446744073709551615 \<and>
                   unat (Lit_var (t' ! j)) < length a) \<and>
                length t' \<le> length a \<and> unat q' \<le> length t' \<and>
                (unat q' < length t' \<longrightarrow> length a - unat q' \<le> k)\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gp p' gn nx' gh h' ga a' gt t' gq q'.
               p_ref \<mapsto>\<langle>\<top>\<rangle> gp\<down>p' \<star> nx_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>nx' \<star> h_ref \<mapsto>\<langle>\<top>\<rangle> gh\<down>h' \<star>
               a_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>a' \<star> t_ref \<mapsto>\<langle>\<top>\<rangle> gt\<down>t' \<star> q_ref \<mapsto>\<langle>\<top>\<rangle> gq\<down>q' \<star>
               can_alloc_reference \<star>
               \<langle>dpll_wpre cs (length a) p' nx' h' \<and> length h' = length h \<and>
                length a' = length a \<and> tr_ok (length a) a' t' \<and> wprop_inv cs t (length a) a' t' \<and>
                (\<forall>j < length t'. 2 * unat (Lit_var (t' ! j)) < 18446744073709551615 \<and>
                   unat (Lit_var (t' ! j)) < length a) \<and>
                length t' \<le> length a \<and> unat q' < length t' \<and> length a - unat q' \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star>
          \<langle>case r of (p1, nx1, h1, a1, t1, q1, b, _) \<Rightarrow>
             dpll_wpre cs (length a) p1 nx1 h1 \<and> length a1 = length a \<and> wprop_post cs t (length a) a1 t1 b \<and>
             unat q1 \<le> length t1\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base wp split: prod.splits tnil.splits inline: lit_neg_def
        simp add: word_less_nat_alt unat_of_nat_eq dpll_unat_Suc Suc2_lt)
    apply (all \<open>(frule (1) wprop_step)?\<close>)
    apply (all \<open>(frule q_suc2, assumption, assumption)?\<close>)
    apply (auto simp add: dpll_wpre_def wprop_post_def unat_of_nat_eq
        intro: tb_var tb_dbl tr_ok_length wprop_refl)
    done
  done

text \<open>The steps of the search loop of \<^verbatim>\<open>dpll\<close>, now with propagation over the watches.\<close>

lemma dpll_init:
  assumes \<open>dpll_wf N cs\<close> \<open>tpass_m cs (replicate N None) [] = (a0, t0, b)\<close>
  shows \<open>(b \<longrightarrow> dstate cs N a0 t0 [] \<and> length a0 = N \<and> tr_ok N a0 t0) \<and> (\<not> b \<longrightarrow> \<not> (\<exists>\<sigma>. cnf_sem \<sigma> cs))\<close>
proof -
  note P = dpll_tpass[OF assms(1) subset_refl tr_ok_init assms(2)]
  have D: \<open>dstate cs N a0 t0 []\<close> using P by (auto simp: dstate_def)
  have \<open>\<not> b \<longrightarrow> \<not> (\<exists>\<sigma>. cnf_sem \<sigma> cs)\<close> using dstate_unsat[OF D] P by blast
  then show ?thesis using D P by (auto simp: tr_ok_def)
qed

lemma dpll_w_facts:
  assumes \<open>dstate cs N r ra L\<close> \<open>wprop_post cs ra (length r) a1 t1 b\<close>
  shows \<open>length r = N \<and> length a1 = N \<and> tr_ok N a1 t1 \<and> dstate cs N a1 t1 L \<and>
         meas N (length ra) L \<le> meas N (length t1) L \<and> length ra \<le> length t1 \<and>
         (\<not> b \<longrightarrow> (\<forall>\<sigma>. agrees a1 \<sigma> \<longrightarrow> \<not> cnf_sem \<sigma> cs))\<close>
proof -
  have r: \<open>length r = N\<close> using dstate_tr[OF assms(1)] by simp
  have P: \<open>tr_ok N a1 t1\<close> \<open>\<exists>e. t1 = ra @ e\<close> \<open>\<forall>j. length ra \<le> j \<and> j < length t1 \<longrightarrow> tr_imp cs t1 j\<close>
    \<open>\<not> b \<longrightarrow> (\<forall>\<sigma>. agrees a1 \<sigma> \<longrightarrow> \<not> cnf_sem \<sigma> cs)\<close>
    using assms(2) r by (simp_all add: wprop_post_def wprop_inv_def)
  note D = dstate_prop[OF assms(1) P(1-3)]
  show ?thesis using r P D by (auto simp: tr_ok_def)
qed

lemma dpll_s_decide:
  assumes \<open>dstate cs N a1 t1 (map unat lim)\<close> \<open>3 ^ N - meas N (length t1) (map unat lim) < Suc k\<close>
    \<open>unat v < length a1\<close> \<open>a1 ! unat v = None\<close> \<open>N < 2 ^ 64\<close>
  shows \<open>3 ^ N - meas N (Suc (length t1)) (map unat lim @ [unat (word64_of_nat (length t1))]) < k \<and>
         dstate cs N (a1[unat v := Some True]) (t1 @ [make_Lit v False])
           (map unat lim @ [unat (word64_of_nat (length t1))])\<close>
proof -
  have T: \<open>tr_ok N a1 t1\<close> \<open>length a1 = N\<close> \<open>length t1 \<le> N\<close> using dstate_tr[OF assms(1)] by simp_all
  have u: \<open>unat (word64_of_nat (length t1)) = length t1\<close>
    using T assms(5) by (simp add: unat_of_nat_eq)
  have D: \<open>dstate cs N (a1[unat v := Some True]) (t1 @ [make_Lit v False]) (map unat lim @ [length t1]) \<and>
       meas N (length t1) (map unat lim) < meas N (length (t1 @ [make_Lit v False])) (map unat lim @ [length t1])\<close>
    by (rule dstate_decide) (use T assms(1,3,4) in auto)
  have l: \<open>length (t1 @ [make_Lit v False]) \<le> N\<close>
    using D unfolding dstate_def by (blast dest: tr_ok_length)
  have \<open>meas N (length t1) (map unat lim) < 3 ^ N\<close> using T meas_lt by auto
  moreover have \<open>meas N (Suc (length t1)) (map unat lim @ [length t1]) < 3 ^ N\<close> using l meas_lt by auto
  ultimately have \<open>3 ^ N - meas N (Suc (length t1)) (map unat lim @ [length t1]) < k\<close>
    using D assms(2) by auto
  then show ?thesis using D u by simp
qed

lemma dpll_s_backtrack:
  assumes \<open>dstate cs N rd re (map unat rb)\<close> \<open>3 ^ N - meas N (length re) (map unat rb) < Suc k\<close>
    \<open>\<forall>\<sigma>. agrees rd \<sigma> \<longrightarrow> \<not> cnf_sem \<sigma> cs\<close> \<open>rb \<noteq> []\<close>
    \<open>tr_ok (length rd) a (take (unat (last rb)) re)\<close>
  shows \<open>3 ^ N - meas N (Suc (min (length re) (unat (last rb)))) (map unat (butlast rb)) < k \<and>
         dstate cs N
          (a[unat (Lit_var (re ! unat (last rb))) := Some (Lit_neg (re ! unat (last rb)))])
          (take (unat (last rb)) re @
           [make_Lit (Lit_var (re ! unat (last rb))) (\<not> Lit_neg (re ! unat (last rb)))])
          (map unat (butlast rb)) \<and>
         unat (Lit_var (re ! unat (last rb))) < length a \<and> unat (last rb) < length re\<close>
proof -
  have T: \<open>tr_ok N rd re\<close> \<open>length rd = N\<close> \<open>length re \<le> N\<close> using dstate_tr[OF assms(1)] by simp_all
  let ?p = \<open>unat (last rb)\<close> and ?L = \<open>map unat (butlast rb)\<close>
  have rb: \<open>map unat rb = ?L @ [?p]\<close> using assms(4) by (metis append_butlast_last_id map_append list.simps(8,9))
  have Ds: \<open>dstate cs N rd re (?L @ [?p])\<close> using assms(1) rb by simp
  have a2: \<open>tr_ok N a (take ?p re)\<close> using assms(5) T by simp
  note B = dstate_backtrack[OF Ds assms(3) a2]
  have pl: \<open>?p < length re\<close> using Ds by (simp add: dstate_def)
  have mn: \<open>min (length re) ?p = ?p\<close> using pl by simp
  have D2: \<open>dstate cs N (a[unat (Lit_var (re ! ?p)) := Some (Lit_neg (re ! ?p))]) (take ?p re @ [lneg (re ! ?p)]) ?L\<close>
    and M: \<open>meas N (length re) (?L @ [?p]) < meas N (length (take ?p re @ [lneg (re ! ?p)])) ?L\<close>
    using B by blast+
  have l: \<open>length (take ?p re @ [lneg (re ! ?p)]) \<le> N\<close>
    using D2 unfolding dstate_def by (blast dest: tr_ok_length)
  have \<open>meas N (length re) (map unat rb) < 3 ^ N\<close> using T meas_lt by auto
  moreover have \<open>meas N (Suc ?p) ?L < 3 ^ N\<close> using l pl meas_lt by auto
  ultimately have m: \<open>3 ^ N - meas N (Suc ?p) ?L < k\<close> using M pl rb assms(2) by auto
  have v: \<open>unat (Lit_var (re ! ?p)) < length a\<close>
    using T pl a2 nth_mem[OF pl] by (auto simp: tr_ok_def)
  show ?thesis using m D2 v mn pl by (simp add: lneg_def)
qed

lemma dpll_s_sat:
  assumes \<open>dstate cs N a1 t1 L\<close> \<open>dprop_post cs t1 (length a1) a2 t2 True\<close>
    \<open>\<forall>v < length a1. a1 ! v \<noteq> None\<close> \<open>dpll_wf N cs\<close>
  shows \<open>length a2 = N \<and> (\<forall>v < length a2. a2 ! v \<noteq> None) \<and> cnf_sem (sigma_of a2) cs\<close>
proof -
  note F = dpll_facts[OF assms(1,2)]
  have T: \<open>tr_ok N a1 t1\<close> \<open>length a1 = N\<close> using dstate_tr[OF assms(1)] by simp_all
  obtain e where e: \<open>t2 = t1 @ e\<close> using assms(2) by (auto simp: dprop_post_def)
  have tot: \<open>\<forall>v < N. a2 ! v \<noteq> None\<close>
    using tr_ok_total_ext[OF T(1)] F e assms(3) T(2) by auto
  have \<open>cnf_sem (sigma_of a2) cs\<close>
    by (rule dpll_quiet_total) (use F tot assms(4) in auto)
  then show ?thesis using F tot by auto
qed

text \<open>A conflict found by the check of a total assignment: the facts of the state after it.\<close>
lemma dpll_s_leaf:
  assumes \<open>dstate cs N a1 t1 L\<close> \<open>dprop_post cs t1 (length a1) a2 t2 False\<close>
    \<open>3 ^ N - meas N (length t1) L < Suc k\<close>
  shows \<open>dstate cs N a2 t2 L \<and> 3 ^ N - meas N (length t2) L < Suc k \<and> length a2 = N \<and>
         tr_ok N a2 t2 \<and> (\<forall>\<sigma>. agrees a2 \<sigma> \<longrightarrow> \<not> cnf_sem \<sigma> cs)\<close>
  using dpll_facts[OF assms(1,2)] assms(3) by auto

lemma dpll_init':
  assumes \<open>\<forall>c \<in> set cs. lits_lt N c \<and> P c\<close> \<open>tpass_m cs (replicate N None) [] = (a0, t0, b)\<close>
  shows \<open>(b \<longrightarrow> dstate cs N a0 t0 [] \<and> length a0 = N \<and> tr_ok N a0 t0) \<and> (\<not> b \<longrightarrow> \<not> (\<exists>\<sigma>. cnf_sem \<sigma> cs))\<close>
  using assms by (intro dpll_init) (auto simp: dpll_wf_def)

lemma dpll_wbt:
  assumes \<open>dstate cs N r ra (map unat rb)\<close> \<open>3 ^ N - meas N (length ra) (map unat rb) < Suc k\<close>
    \<open>wprop_post cs ra N rd re False\<close> \<open>rb \<noteq> []\<close> \<open>tr_ok N a (take (unat (last rb)) re)\<close>
  shows \<open>3 ^ N - meas N (Suc (min (length re) (unat (last rb)))) (map unat (butlast rb)) < k \<and>
         dstate cs N
          (a[unat (Lit_var (re ! unat (last rb))) := Some (Lit_neg (re ! unat (last rb)))])
          (take (unat (last rb)) re @
           [make_Lit (Lit_var (re ! unat (last rb))) (\<not> Lit_neg (re ! unat (last rb)))])
          (map unat (butlast rb)) \<and>
         unat (Lit_var (re ! unat (last rb))) < length a \<and> unat (last rb) < length re\<close>
proof -
  have r: \<open>length r = N\<close> using dstate_tr[OF assms(1)] by simp
  note F = dpll_w_facts[OF assms(1), of rd re False] assms(3) r
  have m: \<open>3 ^ N - meas N (length re) (map unat rb) < Suc k\<close> using F assms(2) by auto
  show ?thesis by (rule dpll_s_backtrack) (use F m assms(4,5) in auto)
qed

lemma dpll_lbt:
  assumes \<open>dstate cs N r ra (map unat rb)\<close> \<open>3 ^ N - meas N (length ra) (map unat rb) < Suc k\<close>
    \<open>wprop_post cs ra N a1 t1 True\<close> \<open>dprop_post cs t1 N rd re False\<close> \<open>rb \<noteq> []\<close>
    \<open>tr_ok N a (take (unat (last rb)) re)\<close>
  shows \<open>3 ^ N - meas N (Suc (min (length re) (unat (last rb)))) (map unat (butlast rb)) < k \<and>
         dstate cs N
          (a[unat (Lit_var (re ! unat (last rb))) := Some (Lit_neg (re ! unat (last rb)))])
          (take (unat (last rb)) re @
           [make_Lit (Lit_var (re ! unat (last rb))) (\<not> Lit_neg (re ! unat (last rb)))])
          (map unat (butlast rb)) \<and>
         unat (Lit_var (re ! unat (last rb))) < length a \<and> unat (last rb) < length re\<close>
proof -
  have r: \<open>length r = N\<close> using dstate_tr[OF assms(1)] by simp
  note F = dpll_w_facts[OF assms(1), of a1 t1 True] assms(3) r
  have m1: \<open>3 ^ N - meas N (length t1) (map unat rb) < Suc k\<close> using F assms(2) by auto
  have d1: \<open>dstate cs N a1 t1 (map unat rb)\<close> and l1: \<open>length a1 = N\<close> using F by auto
  note L = dpll_s_leaf[OF d1 _ m1, of rd re] assms(4) l1
  show ?thesis by (rule dpll_s_backtrack) (use L assms(5,6) in auto)
qed

lemma dpll_wdec:
  assumes \<open>dstate cs N r ra (map unat lim)\<close> \<open>3 ^ N - meas N (length ra) (map unat lim) < Suc k\<close>
    \<open>wprop_post cs ra N a1 t1 b\<close> \<open>unat v < N\<close> \<open>a1 ! unat v = None\<close> \<open>N < 9223372036854775808\<close>
  shows \<open>3 ^ N - meas N (Suc (length t1)) (map unat lim @ [unat (word64_of_nat (length t1))]) < k \<and>
         dstate cs N (a1[unat v := Some True]) (t1 @ [make_Lit v False])
           (map unat lim @ [unat (word64_of_nat (length t1))]) \<and>
         tr_ok N (a1[unat v := Some True]) (t1 @ [make_Lit v False]) \<and> length a1 = N\<close>
proof -
  have r: \<open>length r = N\<close> using dstate_tr[OF assms(1)] by simp
  note F = dpll_w_facts[OF assms(1), of a1 t1 b] assms(3) r
  have m: \<open>3 ^ N - meas N (length t1) (map unat lim) < Suc k\<close> using F assms(2) by auto
  have D: \<open>3 ^ N - meas N (Suc (length t1)) (map unat lim @ [unat (word64_of_nat (length t1))]) < k \<and>
         dstate cs N (a1[unat v := Some True]) (t1 @ [make_Lit v False])
           (map unat lim @ [unat (word64_of_nat (length t1))])\<close>
    by (rule dpll_s_decide) (use F m assms(4-6) in auto)
  then show ?thesis using F dstate_tr by blast
qed

lemma dpll_wsat:
  assumes \<open>dstate cs N r ra L\<close> \<open>wprop_post cs ra N a1 t1 True\<close> \<open>\<forall>v < length a1. a1 ! v \<noteq> None\<close>
    \<open>dprop_post cs t1 N a2 t2 True\<close> \<open>\<forall>c \<in> set cs. lits_lt N c \<and> P c\<close>
  shows \<open>length a2 = N \<and> (\<forall>v < length a2. a2 ! v \<noteq> None) \<and> cnf_sem (sigma_of a2) cs\<close>
proof -
  have r: \<open>length r = N\<close> using dstate_tr[OF assms(1)] by simp
  note F = dpll_w_facts[OF assms(1), of a1 t1 True] assms(2) r
  show ?thesis by (rule dpll_s_sat[of cs N a1 t1 _ a2 t2]) (use F assms(3-5) in \<open>auto simp: dpll_wf_def\<close>)
qed

lemma dpll_wunsat1:
  assumes \<open>dstate cs N r ra []\<close> \<open>wprop_post cs ra N rd re False\<close> \<open>cnf_sem \<sigma> cs\<close>
  shows False
proof -
  have r: \<open>length r = N\<close> using dstate_tr[OF assms(1)] by simp
  note F = dpll_w_facts[OF assms(1), of rd re False] assms(2) r
  have D: \<open>dstate cs N rd re []\<close> and C: \<open>\<forall>\<sigma>. agrees rd \<sigma> \<longrightarrow> \<not> cnf_sem \<sigma> cs\<close>
    using F by blast+
  show False using dstate_unsat[OF D C] assms(3) by blast
qed

lemma dpll_wunsat2:
  assumes \<open>dstate cs N r ra []\<close> \<open>wprop_post cs ra N a1 t1 True\<close> \<open>dprop_post cs t1 N rd re False\<close>
    \<open>cnf_sem \<sigma> cs\<close>
  shows False
proof -
  have r: \<open>length r = N\<close> using dstate_tr[OF assms(1)] by simp
  note F = dpll_w_facts[OF assms(1), of a1 t1 True] assms(2) r
  have D1: \<open>dstate cs N a1 t1 []\<close> and l1: \<open>length a1 = N\<close> using F by blast+
  have P: \<open>dprop_post cs t1 (length a1) rd re False\<close> using assms(3) l1 by simp
  note L = dpll_facts[OF D1 P]
  have D: \<open>dstate cs N rd re []\<close> and C: \<open>\<forall>\<sigma>. agrees rd \<sigma> \<longrightarrow> \<not> cnf_sem \<sigma> cs\<close>
    using L by blast+
  show False using dstate_unsat[OF D C] assms(4) by blast
qed

lemma wprop_post_len: \<open>wprop_post cs t n a1 t1 b \<Longrightarrow> length t1 \<le> n \<and> length a1 = n \<and> tr_ok n a1 t1\<close>
  using tr_ok_length by (auto simp: wprop_post_def wprop_inv_def tr_ok_def)

lemma dprop_post_len: \<open>dprop_post cs t n a1 t1 b \<Longrightarrow> length t1 \<le> n \<and> length a1 = n \<and> tr_ok n a1 t1\<close>
  using tr_ok_length by (auto simp: dprop_post_def tr_ok_def)

lemma dpll_lbt':
  assumes \<open>dstate cs N r ra (map unat rb)\<close> \<open>3 ^ N - meas N (length ra) (map unat rb) < Suc k\<close>
    \<open>wprop_post cs ra N a1 t1 True\<close> \<open>dprop_post cs t1 (length a1) rd re False\<close> \<open>rb \<noteq> []\<close>
    \<open>tr_ok N a (take (unat (last rb)) re)\<close>
  shows \<open>3 ^ N - meas N (Suc (min (length re) (unat (last rb)))) (map unat (butlast rb)) < k \<and>
         dstate cs N
          (a[unat (Lit_var (re ! unat (last rb))) := Some (Lit_neg (re ! unat (last rb)))])
          (take (unat (last rb)) re @
           [make_Lit (Lit_var (re ! unat (last rb))) (\<not> Lit_neg (re ! unat (last rb)))])
          (map unat (butlast rb)) \<and>
         unat (Lit_var (re ! unat (last rb))) < length a \<and> unat (last rb) < length re\<close>
proof -
  have l: \<open>length a1 = N\<close> using wprop_post_len[OF assms(3)] by simp
  show ?thesis by (rule dpll_lbt[OF assms(1,2,3) _ assms(5,6)]) (use assms(4) l in simp)
qed

lemma dpll_wsat':
  assumes \<open>dstate cs N r ra L\<close> \<open>wprop_post cs ra N a1 t1 True\<close> \<open>\<forall>v < M. \<exists>y. a1 ! v = Some y\<close>
    \<open>dprop_post cs t1 M' a2 t2 True\<close> \<open>\<forall>c \<in> set cs. lits_lt N c \<and> P c\<close> \<open>M = N \<or> M = length a1\<close>
    \<open>M' = N \<or> M' = length a1\<close>
  shows \<open>length a2 = N \<and> (\<forall>v < length a2. a2 ! v \<noteq> None) \<and> cnf_sem (sigma_of a2) cs\<close>
proof -
  have l: \<open>length a1 = N\<close> using wprop_post_len[OF assms(2)] by simp
  show ?thesis by (rule dpll_wsat[OF assms(1,2) _ _ assms(5)]) (use assms(3,4,6,7) l in auto)
qed

lemma dpll_wunsat2':
  assumes \<open>dstate cs N r ra []\<close> \<open>wprop_post cs ra N a1 t1 True\<close> \<open>dprop_post cs t1 (length a1) rd re False\<close>
    \<open>cnf_sem \<sigma> cs\<close>
  shows False
  using dpll_wunsat2[OF assms(1,2) _ assms(4)] assms(3) wprop_post_len[OF assms(2)] by simp

lemma dpll_bt_idx:
  assumes \<open>dstate cs N r ra (map unat rb)\<close> \<open>rb \<noteq> []\<close> \<open>wprop_post cs ra N a1 t1 b\<close>
  shows \<open>unat (last rb) < length t1\<close>
proof -
  have \<open>unat (last rb) < length ra\<close> using assms(1,2) by (auto simp: dstate_def)
  moreover have \<open>length ra \<le> length t1\<close> using assms(3) by (auto simp: wprop_post_def wprop_inv_def)
  ultimately show ?thesis by simp
qed

lemma dpll_lbtG:
  assumes \<open>dstate cs N r ra (map unat rb)\<close> \<open>3 ^ N - meas N (length ra) (map unat rb) < Suc k\<close>
    \<open>wprop_post cs ra N a1 t1 True\<close> \<open>dprop_post cs t1 M rd re False\<close> \<open>rb \<noteq> []\<close>
    \<open>tr_ok M2 a (take (unat (last rb)) re)\<close> \<open>M = N \<or> M = length a1\<close> \<open>M2 = N \<or> M2 = length rd\<close>
  shows \<open>3 ^ N - meas N (Suc (min (length re) (unat (last rb)))) (map unat (butlast rb)) < k \<and>
         dstate cs N
          (a[unat (Lit_var (re ! unat (last rb))) := Some (Lit_neg (re ! unat (last rb)))])
          (take (unat (last rb)) re @
           [make_Lit (Lit_var (re ! unat (last rb))) (\<not> Lit_neg (re ! unat (last rb)))])
          (map unat (butlast rb)) \<and>
         unat (Lit_var (re ! unat (last rb))) < length a \<and> unat (last rb) < length re\<close>
proof -
  have l: \<open>length a1 = N\<close> using wprop_post_len[OF assms(3)] by simp
  have m: \<open>M = N\<close> using assms(7) l by auto
  have l2: \<open>length rd = N\<close> using dprop_post_len[OF assms(4)] m by simp
  have m2: \<open>M2 = N\<close> using assms(8) l2 by auto
  show ?thesis by (rule dpll_lbt[OF assms(1,2,3) _ assms(5)]) (use assms(4,6) m m2 in simp_all)
qed

lemma dpll_lbt0:
  assumes \<open>dstate cs N r ra (map unat rb)\<close> \<open>3 ^ N - meas N (length ra) (map unat rb) < Suc k\<close>
    \<open>wprop_post cs ra N a1 t1 True\<close> \<open>dprop_post cs t1 (N) rd re False\<close> \<open>rb \<noteq> []\<close>
    \<open>tr_ok (N) a (take (unat (last rb)) re)\<close>
  shows \<open>3 ^ N - meas N (Suc (min (length re) (unat (last rb)))) (map unat (butlast rb)) < k \<and>
         dstate cs N
          (a[unat (Lit_var (re ! unat (last rb))) := Some (Lit_neg (re ! unat (last rb)))])
          (take (unat (last rb)) re @
           [make_Lit (Lit_var (re ! unat (last rb))) (\<not> Lit_neg (re ! unat (last rb)))])
          (map unat (butlast rb)) \<and>
         unat (Lit_var (re ! unat (last rb))) < length a \<and> unat (last rb) < length re\<close>
  by (rule dpll_lbtG[OF assms]) simp_all

lemma dpll_lbt1:
  assumes \<open>dstate cs N r ra (map unat rb)\<close> \<open>3 ^ N - meas N (length ra) (map unat rb) < Suc k\<close>
    \<open>wprop_post cs ra N a1 t1 True\<close> \<open>dprop_post cs t1 (N) rd re False\<close> \<open>rb \<noteq> []\<close>
    \<open>tr_ok (length rd) a (take (unat (last rb)) re)\<close>
  shows \<open>3 ^ N - meas N (Suc (min (length re) (unat (last rb)))) (map unat (butlast rb)) < k \<and>
         dstate cs N
          (a[unat (Lit_var (re ! unat (last rb))) := Some (Lit_neg (re ! unat (last rb)))])
          (take (unat (last rb)) re @
           [make_Lit (Lit_var (re ! unat (last rb))) (\<not> Lit_neg (re ! unat (last rb)))])
          (map unat (butlast rb)) \<and>
         unat (Lit_var (re ! unat (last rb))) < length a \<and> unat (last rb) < length re\<close>
  by (rule dpll_lbtG[OF assms]) simp_all

lemma dpll_lbt2:
  assumes \<open>dstate cs N r ra (map unat rb)\<close> \<open>3 ^ N - meas N (length ra) (map unat rb) < Suc k\<close>
    \<open>wprop_post cs ra N a1 t1 True\<close> \<open>dprop_post cs t1 (length a1) rd re False\<close> \<open>rb \<noteq> []\<close>
    \<open>tr_ok (N) a (take (unat (last rb)) re)\<close>
  shows \<open>3 ^ N - meas N (Suc (min (length re) (unat (last rb)))) (map unat (butlast rb)) < k \<and>
         dstate cs N
          (a[unat (Lit_var (re ! unat (last rb))) := Some (Lit_neg (re ! unat (last rb)))])
          (take (unat (last rb)) re @
           [make_Lit (Lit_var (re ! unat (last rb))) (\<not> Lit_neg (re ! unat (last rb)))])
          (map unat (butlast rb)) \<and>
         unat (Lit_var (re ! unat (last rb))) < length a \<and> unat (last rb) < length re\<close>
  by (rule dpll_lbtG[OF assms]) simp_all

lemma dpll_lbt3:
  assumes \<open>dstate cs N r ra (map unat rb)\<close> \<open>3 ^ N - meas N (length ra) (map unat rb) < Suc k\<close>
    \<open>wprop_post cs ra N a1 t1 True\<close> \<open>dprop_post cs t1 (length a1) rd re False\<close> \<open>rb \<noteq> []\<close>
    \<open>tr_ok (length rd) a (take (unat (last rb)) re)\<close>
  shows \<open>3 ^ N - meas N (Suc (min (length re) (unat (last rb)))) (map unat (butlast rb)) < k \<and>
         dstate cs N
          (a[unat (Lit_var (re ! unat (last rb))) := Some (Lit_neg (re ! unat (last rb)))])
          (take (unat (last rb)) re @
           [make_Lit (Lit_var (re ! unat (last rb))) (\<not> Lit_neg (re ! unat (last rb)))])
          (map unat (butlast rb)) \<and>
         unat (Lit_var (re ! unat (last rb))) < length a \<and> unat (last rb) < length re\<close>
  by (rule dpll_lbtG[OF assms]) simp_all

lemma dpll_bt_idx2:
  assumes \<open>dstate cs N r ra (map unat rb)\<close> \<open>rb \<noteq> []\<close> \<open>wprop_post cs ra N a1 t1 b\<close>
    \<open>dprop_post cs t1 M rd re b'\<close>
  shows \<open>unat (last rb) < length re\<close>
proof -
  have \<open>unat (last rb) < length t1\<close> using dpll_bt_idx[OF assms(1-3)] .
  moreover have \<open>length t1 \<le> length re\<close> using assms(4) by (auto simp: dprop_post_def)
  ultimately show ?thesis by simp
qed

lemma tr_ok_lenA: \<open>tr_ok n a t \<Longrightarrow> length a = n\<close>
  by (simp add: tr_ok_def)

lemma dpll_cs_ok_wcs:
  \<open>dpll_cs_ok cs n \<Longrightarrow> 2 * n < 2 ^ 64 \<Longrightarrow> wcs_ok cs n urust_fuel\<close>
  unfolding dpll_cs_ok_def wcs_ok_def
  by (fastforce simp: lits_lt_def dest: nth_mem)

definition dpll_top_contract :: \<open>Lit list list \<Rightarrow> 64 word \<Rightarrow> ('s, bool option list option, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>dpll_top_contract cs n \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
          \<langle>dpll_cs_ok cs (unat n) \<and> length cs + 2 \<le> urust_fuel \<and> length cs < 2 ^ 64 \<and>
           unat n + 2 \<le> urust_fuel \<and> 3 ^ unat n < urust_fuel \<and>
           2 * length cs \<le> urust_fuel \<and> 2 * length cs < 2 ^ 64 \<and> 2 * unat n < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>case r of
             None \<Rightarrow> \<not> (\<exists>\<sigma>. cnf_sem \<sigma> cs)
           | Some a' \<Rightarrow> length a' = unat n \<and> (\<forall>v < length a'. a' ! v \<noteq> None) \<and> cnf_sem (sigma_of a') cs\<rangle>)\<close>

lemma dpll_top_spec [crush_specs]:
  shows \<open>\<Gamma>; dpll cs n \<Turnstile>\<^sub>F dpll_top_contract cs n\<close>
  apply (crush_boot f: dpll_def contract: dpll_top_contract_def)
  apply (crush_base split: prod.splits tnil.splits simp add: dpll_cs_ok_def)
  subgoal for p0 nx0 h0 p_ref nx_ref h_ref a0 t0 ok0 a_ref t_ref l_ref q_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gp p gn nx gh h ga a gt t gl lim gq q.
               p_ref \<mapsto>\<langle>\<top>\<rangle> gp\<down>p \<star> nx_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>nx \<star> h_ref \<mapsto>\<langle>\<top>\<rangle> gh\<down>h \<star>
               a_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>a \<star> t_ref \<mapsto>\<langle>\<top>\<rangle> gt\<down>t \<star> l_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>lim \<star>
               q_ref \<mapsto>\<langle>\<top>\<rangle> gq\<down>q \<star> can_alloc_reference \<star>
               \<langle>dstate cs (unat n) a t (map unat lim) \<and> 3 ^ unat n - meas (unat n) (length t) (map unat lim) < k \<and>
                dpll_wpre cs (unat n) p nx h \<and> length a = unat n \<and> tr_ok (unat n) a t \<and> unat q \<le> length t\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gp p gn nx gh h ga a gt t gl lim gq q.
               p_ref \<mapsto>\<langle>\<top>\<rangle> gp\<down>p \<star> nx_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>nx \<star> h_ref \<mapsto>\<langle>\<top>\<rangle> gh\<down>h \<star>
               a_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>a \<star> t_ref \<mapsto>\<langle>\<top>\<rangle> gt\<down>t \<star> l_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>lim \<star>
               q_ref \<mapsto>\<langle>\<top>\<rangle> gq\<down>q \<star> can_alloc_reference \<star>
               \<langle>dstate cs (unat n) a t (map unat lim) \<and> 3 ^ unat n - meas (unat n) (length t) (map unat lim) < Suc k \<and>
                dpll_wpre cs (unat n) p nx h \<and> length a = unat n \<and> tr_ok (unat n) a t \<and> unat q \<le> length t\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star>
          \<langle>case r of
             None \<Rightarrow> \<not> (\<exists>\<sigma>. cnf_sem \<sigma> cs)
           | Some a' \<Rightarrow> length a' = unat n \<and> (\<forall>v < length a'. a' ! v \<noteq> None) \<and> cnf_sem (sigma_of a') cs\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base wp split: prod.splits tnil.splits option.splits
        inline: lit_neg_def vec_push_def vec_pop_def simp add: dpll_cs_ok_def)
    apply (all \<open>(rule fst_conv)?\<close>)
    apply (all \<open>(frule (4) dpll_wbt)?\<close>)
    apply (all \<open>(frule (5) dpll_lbt)?\<close>)
    apply (all \<open>(frule (5) dpll_lbt')?\<close>)
    apply (all \<open>(frule (5) dpll_lbt0)?\<close>)
    apply (all \<open>(frule (5) dpll_lbt1)?\<close>)
    apply (all \<open>(frule (5) dpll_lbt2)?\<close>)
    apply (all \<open>(frule (5) dpll_lbt3)?\<close>)
    apply (all \<open>(frule (5) dpll_wdec)?\<close>)
    apply (all \<open>(frule (4) dpll_wsat)?\<close>)
    apply (all \<open>(frule (4) dpll_wsat', simp, simp)?\<close>)
    apply (all \<open>(frule (2) dpll_bt_idx)?\<close>)
    apply (all \<open>(frule (3) dpll_bt_idx2)?\<close>)
    apply (all \<open>(frule (1) dpll_init')?\<close>)
    apply (all \<open>(frule wprop_post_len)?\<close>)
    apply (all \<open>(frule dprop_post_len)?\<close>)
    apply (auto simp add: dpll_wpre_def intro: dpll_cs_ok_wcs[unfolded dpll_cs_ok_def] dstate_tr[THEN conjunct1]
        less_imp_diff_less tr_ok_lenA dest: dpll_wunsat1 dpll_wunsat2 dpll_wunsat2')
    done
  using dpll_init' by blast


end

end
