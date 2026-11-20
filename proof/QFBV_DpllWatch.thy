theory QFBV_DpllWatch
  imports QFBV_Cdcl
begin

section \<open>DPLL: contracts up to the visit of a watch list\<close>

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

text \<open>The reasons \<open>rs1\<close> extend the reasons \<open>rs\<close> of the trail \<open>t\<close> with a reason of every entry of
  \<open>t1\<close> after \<open>t\<close>.\<close>
definition rext :: \<open>Lit list list \<Rightarrow> Lit list \<Rightarrow> 64 word list \<Rightarrow> Lit list \<Rightarrow> 64 word list \<Rightarrow> bool\<close> where
  \<open>rext cs t rs t1 rs1 \<equiv> length rs1 = length t1 \<and> take (length t) rs1 = rs \<and>
     (\<forall>k. length t \<le> k \<and> k < length t1 \<longrightarrow> reason cs t1 k (unat (rs1 ! k)))\<close>

text \<open>The clause \<open>c\<close> is in conflict with the trail \<open>t\<close>: all its literals are false.\<close>
definition cfl :: \<open>Lit list list \<Rightarrow> Lit list \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>cfl cs t c \<equiv> c < length cs \<and> (\<forall>l \<in> set (cs ! c). lneg l \<in> set t)\<close>

lemma rext_refl: \<open>length rs = length t \<Longrightarrow> rext cs t rs t rs\<close>
  by (auto simp: rext_def)

lemma rext_len: \<open>rext cs t rs t1 rs1 \<Longrightarrow> length rs1 = length t1\<close>
  by (simp add: rext_def)

lemma rext_unit:
  assumes \<open>rext cs t rs t' rs'\<close> \<open>length t \<le> length t'\<close> \<open>status_m a (cs ! i) None False = Status_Unit l\<close>
    \<open>i < length cs\<close> \<open>lits_lt n (cs ! i)\<close> \<open>tr_ok n a t'\<close> \<open>unat w = i\<close>
  shows \<open>rext cs t rs (t' @ [l]) (rs' @ [w])\<close>
proof -
  have R: \<open>length rs' = length t'\<close> \<open>take (length t) rs' = rs\<close>
    \<open>\<forall>k. length t \<le> k \<and> k < length t' \<longrightarrow> reason cs t' k (unat (rs' ! k))\<close>
    using assms(1) by (simp_all add: rext_def)
  have u: \<open>reason cs (t' @ [l]) (length t') i\<close> using unit_reason[OF assms(3,4,5,6)] .
  have \<open>reason cs (t' @ [l]) k (unat ((rs' @ [w]) ! k))\<close> if \<open>length t \<le> k\<close> \<open>k < Suc (length t')\<close> for k
  proof (cases \<open>k < length t'\<close>)
    case True
    then show ?thesis using R(1,3) that reason_append[of cs t' k] by (simp add: nth_append)
  next
    case False
    then have \<open>k = length t'\<close> using that by simp
    then show ?thesis using u R(1) assms(7) by (simp add: nth_append)
  qed
  then show ?thesis using R assms(2) by (simp add: rext_def)
qed

lemma rext_trans:
  assumes \<open>rext cs t rs t1 rs1\<close> \<open>rext cs t1 rs1 t2 rs2\<close> \<open>\<exists>e. t1 = t @ e\<close> \<open>\<exists>e. t2 = t1 @ e\<close>
  shows \<open>rext cs t rs t2 rs2\<close>
proof -
  obtain e1 where e1: \<open>t1 = t @ e1\<close> using assms(3) by blast
  obtain e2 where e2: \<open>t2 = t1 @ e2\<close> using assms(4) by blast
  have A: \<open>length rs1 = length t1\<close> \<open>take (length t) rs1 = rs\<close>
    \<open>\<forall>k. length t \<le> k \<and> k < length t1 \<longrightarrow> reason cs t1 k (unat (rs1 ! k))\<close>
    using assms(1) by (simp_all add: rext_def)
  have B: \<open>length rs2 = length t2\<close> \<open>take (length t1) rs2 = rs1\<close>
    \<open>\<forall>k. length t1 \<le> k \<and> k < length t2 \<longrightarrow> reason cs t2 k (unat (rs2 ! k))\<close>
    using assms(2) by (simp_all add: rext_def)
  have \<open>take (length t) rs2 = take (length t) (take (length t1) rs2)\<close> using e1 by (simp add: min_def)
  then have tk: \<open>take (length t) rs2 = rs\<close> using A(2) B(2) by simp
  have \<open>reason cs t2 k (unat (rs2 ! k))\<close> if \<open>length t \<le> k\<close> \<open>k < length t2\<close> for k
  proof (cases \<open>k < length t1\<close>)
    case True
    have \<open>rs2 ! k = rs1 ! k\<close> using B(2) True by (metis nth_take)
    then show ?thesis using A(3) that(1) True reason_append[of cs t1 k \<open>unat (rs1 ! k)\<close> e2] e2 by simp
  next
    case False
    then show ?thesis using B(3) that(2) by simp
  qed
  then show ?thesis using B(1) tk by (simp add: rext_def)
qed

lemma cfl_status:
  \<open>status_m a (cs ! c) None False = Status_Conflict \<Longrightarrow> c < length cs \<Longrightarrow> lits_lt n (cs ! c) \<Longrightarrow>
   tr_ok n a t \<Longrightarrow> cfl cs t c\<close>
  using dpll_status_Conflict tr_false by (fastforce simp: cfl_def lits_lt_def)

lemma pp_unit:
  fixes i :: \<open>64 word\<close>
  assumes \<open>wprop_inv cs t n a' t'\<close> \<open>rext cs t rs t' rs'\<close> \<open>unat i < length cs\<close>
    \<open>\<forall>c \<in> set cs. lits_lt n c \<and> Q c\<close> \<open>status_m a' (cs ! unat i) None False = Status_Unit l\<close>
  shows \<open>wprop_inv cs t n (a'[unat (Lit_var l) := Some (\<not> Lit_neg l)]) (t' @ [l]) \<and>
         rext cs t rs (t' @ [l]) (rs' @ [i])\<close>
proof -
  have c: \<open>cs ! unat i \<in> set cs\<close> \<open>lits_lt n (cs ! unat i)\<close> using assms(3,4) nth_mem by auto
  have T: \<open>tr_ok n a' t'\<close> \<open>length t \<le> length t'\<close> using assms(1) by (auto simp: wprop_inv_def)
  show ?thesis using wprop_unit[OF assms(1) c(1,2) assms(5)] rext_unit[OF assms(2) T(2) assms(5,3) c(2) T(1)]
    by simp
qed

definition dpll_propagate_pass_contract ::
  \<open>Lit list list \<Rightarrow> bool option list \<Rightarrow> Lit list \<Rightarrow> 64 word list \<Rightarrow>
   ('s, bool option list \<times> Lit list \<times> 64 word list \<times> bool \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>dpll_propagate_pass_contract cs a t rs \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
          \<langle>(\<forall>c \<in> set cs. lits_lt (length a) c \<and> length c + 2 \<le> urust_fuel \<and> length c < 2 ^ 64) \<and>
           length cs + 2 \<le> urust_fuel \<and> length cs < 2 ^ 64 \<and> length a < 2 ^ 64 \<and>
           tr_ok (length a) a t \<and> length rs = length t\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>case r of (a1, t1, rs1, b, _) \<Rightarrow> tpass_m cs a t = (a1, t1, b) \<and> rext cs t rs t1 rs1\<rangle>)\<close>

lemma dpll_propagate_pass_spec [crush_specs]:
  shows \<open>\<Gamma>; propagate_pass cs a t rs \<Turnstile>\<^sub>F dpll_propagate_pass_contract cs a t rs\<close>
  apply (crush_boot f: propagate_pass_def contract: dpll_propagate_pass_contract_def)
  apply (crush_base inline: len_def)
  subgoal for a_ref t_ref r_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>ga a' gt t' gr rs' gi i. a_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>a' \<star> t_ref \<mapsto>\<langle>\<top>\<rangle> gt\<down>t' \<star>
               r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>rs' \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i \<le> length cs \<and> length a' = length a \<and>
                tpass_m cs a t = tpass_m (drop (unat i) cs) a' t' \<and> length cs - unat i \<le> k \<and>
                wprop_inv cs t (length a) a' t' \<and> rext cs t rs t' rs'\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>ga a' gt t' gr rs' gi i. a_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>a' \<star> t_ref \<mapsto>\<langle>\<top>\<rangle> gt\<down>t' \<star>
               r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>rs' \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i < length cs \<and> length a' = length a \<and>
                tpass_m cs a t = tpass_m (drop (unat i) cs) a' t' \<and> length cs - unat i \<le> Suc k \<and>
                wprop_inv cs t (length a) a' t' \<and> rext cs t rs t' rs'\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star>
          \<langle>case r of (a1, t1, rs1, b, _) \<Rightarrow> tpass_m cs a t = (a1, t1, b) \<and> rext cs t rs t1 rs1\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base wp split: Status.splits inline: vec_push_def
        simp add: word_less_nat_alt unat_of_nat_eq dpll_unat_Suc)
    apply (all \<open>(frule (4) pp_unit)?\<close>)
    apply (auto simp add: dpll_tpass_drop ASSUMPTION_def intro: dpll_unit_var_nth wprop_refl rext_refl)
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
             length p = 2 * length cs \<and> length nx = 2 * length cs \<and> length h = 2 * unat n \<and> wl_ok cs p nx h \<and>
             lends nx h\<rangle>)\<close>

text \<open>The loop of \<^verbatim>\<open>watch_init\<close> has set up the watches of the first \<open>c\<close> clauses.\<close>
definition wl_init :: \<open>Lit list list \<Rightarrow> nat \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> bool\<close> where
  \<open>wl_init cs c p nx h \<equiv> (\<exists>Ls. wl_lists cs c p nx h Ls) \<and> (\<forall>s. 2 * c \<le> s \<and> s < 2 * length cs \<longrightarrow> p ! s = 0)\<close>

lemma wl_init_0:
  assumes \<open>length cs < 9223372036854775808\<close>
  shows \<open>wl_init cs 0 (replicate (2 * length cs) 0) (replicate (2 * length cs) 18446744073709551615)
           (replicate (2 * m) 18446744073709551615)\<close>
proof -
  have \<open>wl_lists cs 0 (replicate (2 * length cs) 0) (replicate (2 * length cs) 18446744073709551615)
           (replicate (2 * m) 18446744073709551615) (replicate (2 * m) [])\<close>
    using wl_init_empty[of \<open>replicate (2 * length cs) 0\<close> cs
      \<open>replicate (2 * length cs) 18446744073709551615\<close> \<open>replicate (2 * m) 18446744073709551615\<close>] assms
    by simp
  then show ?thesis unfolding wl_init_def by auto
qed

lemma lends_init: \<open>lends (replicate k 18446744073709551615) (replicate m 18446744073709551615)\<close>
  unfolding lends_def by (auto simp: set_replicate_conv_if)

lemma lends_nth_nx: \<open>lends nx h \<Longrightarrow> i < length nx \<Longrightarrow> unat (nx ! i) < length nx \<or> unat (nx ! i) = 2 ^ 64 - 1\<close>
  by (simp add: lends_def)

lemma lends_nth_h: \<open>lends nx h \<Longrightarrow> i < length h \<Longrightarrow> unat (h ! i) < length nx \<or> unat (h ! i) = 2 ^ 64 - 1\<close>
  by (simp add: lends_def)

lemma lends_nx:
  assumes \<open>lends nx h\<close> \<open>unat v < length nx \<or> unat v = 2 ^ 64 - 1\<close>
  shows \<open>lends (nx[i := v]) h\<close>
proof -
  have \<open>set (nx[i := v]) \<subseteq> insert v (set nx)\<close> by (rule set_update_subset_insert)
  then show ?thesis using assms unfolding lends_def by auto
qed

lemma lends_h:
  assumes \<open>lends nx h\<close> \<open>unat v < length nx \<or> unat v = 2 ^ 64 - 1\<close>
  shows \<open>lends nx (h[i := v])\<close>
proof -
  have \<open>set (h[i := v]) \<subseteq> insert v (set h)\<close> by (rule set_update_subset_insert)
  then show ?thesis using assms unfolding lends_def by auto
qed

lemma lends_add:
  assumes \<open>lends nx h\<close> \<open>unat sw < length nx\<close> \<open>unat ow < length nx\<close> \<open>x0 < length h\<close> \<open>x1 < length h\<close>
  shows \<open>lends (nx[i := h ! x0, j := h[x0 := sw] ! x1]) (h[x0 := sw, x1 := ow])\<close>
proof -
  have a: \<open>lends (nx[i := h ! x0]) h\<close> using lends_nx[OF assms(1) lends_nth_h[OF assms(1,4)]] .
  have b: \<open>lends (nx[i := h ! x0]) (h[x0 := sw])\<close> by (rule lends_h[OF a]) (use assms(2) in simp)
  have c: \<open>unat (h[x0 := sw] ! x1) < length nx \<or> unat (h[x0 := sw] ! x1) = 2 ^ 64 - 1\<close>
    using lends_nth_h[OF assms(1,5)] assms(2,5) by (cases \<open>x0 = x1\<close>) simp_all
  have d: \<open>lends (nx[i := h ! x0, j := h[x0 := sw] ! x1]) (h[x0 := sw])\<close>
    by (rule lends_nx[OF b]) (use c in simp)
  show ?thesis by (rule lends_h[OF d]) (use assms(3) in simp)
qed

lemma lends_addw:
  fixes r :: \<open>64 word\<close>
  assumes \<open>lends nx h\<close> \<open>unat r < length cs\<close> \<open>length cs < 9223372036854775808\<close> \<open>length nx = 2 * length cs\<close>
    \<open>x0 < length h\<close> \<open>x1 < length h\<close>
  shows \<open>lends (nx[i := h ! x0, j := h[x0 := 2 * r] ! x1]) (h[x0 := 2 * r, x1 := 2 * r + 1])\<close>
  using lends_add[OF assms(1) _ _ assms(5,6)] unat64_dbl_lt[OF assms(2,3)] assms(2,4) by simp

lemma xlt:
  \<open>\<forall>i < length cs. \<forall>j < length (cs ! i). 2 * lv (cs ! i ! j) < M \<and> lv (cs ! i ! j) < N \<Longrightarrow>
   length h = 2 * N \<Longrightarrow> i < length cs \<Longrightarrow> j < length (cs ! i) \<Longrightarrow>
   2 * lv (cs ! i ! j) < length h \<and> Suc (2 * lv (cs ! i ! j)) < length h\<close>
  by fastforce

lemma wl_init_end: \<open>wl_init cs c p nx h \<Longrightarrow> c = length cs \<Longrightarrow> wl_ok cs p nx h\<close>
  by (auto simp: wl_init_def wl_ok_def)

lemma wl_init_skip:
  assumes \<open>wl_init cs c p nx h\<close> \<open>c < length cs\<close> \<open>\<not> 2 \<le> length (cs ! c)\<close>
  shows \<open>wl_init cs (Suc c) p nx h\<close>
proof -
  obtain Ls where L: \<open>wl_lists cs c p nx h Ls\<close> and z: \<open>\<forall>s. 2 * c \<le> s \<and> s < 2 * length cs \<longrightarrow> p ! s = 0\<close>
    using assms(1) by (auto simp: wl_init_def)
  have \<open>wl_lists cs (Suc c) p nx h Ls\<close> using wl_init_short[OF L assms(2,3)] .
  then show ?thesis using z unfolding wl_init_def by auto
qed

lemma wl_init_add:
  fixes sw ow :: \<open>64 word\<close>
  assumes \<open>wl_init cs c p nx h\<close> \<open>c < length cs\<close> \<open>2 \<le> length (cs ! c)\<close>
    \<open>lidx (cs ! c ! 0) = x0\<close> \<open>lidx (cs ! c ! 1) = x1\<close> \<open>x0 < length h\<close> \<open>x1 < length h\<close>
    \<open>2 * length cs < 2 ^ 64\<close> \<open>unat sw = 2 * c\<close> \<open>unat ow = Suc (2 * c)\<close>
  shows \<open>wl_init cs (Suc c) (p[Suc (2 * c) := 1]) ((nx[2 * c := h ! x0])[Suc (2 * c) := (h[x0 := sw]) ! x1])
           ((h[x0 := sw])[x1 := ow])\<close>
proof -
  obtain Ls where L: \<open>wl_lists cs c p nx h Ls\<close> and z: \<open>\<forall>s. 2 * c \<le> s \<and> s < 2 * length cs \<longrightarrow> p ! s = 0\<close>
    using assms(1) by (auto simp: wl_init_def)
  have w: \<open>sw = word_of_nat (2 * c)\<close> \<open>ow = word_of_nat (Suc (2 * c))\<close>
    using assms(9,10) by (metis word_unat.Rep_inverse)+
  note S = wl_init_step[OF L assms(2,3) z assms(4-8)]
  have \<open>\<forall>s. 2 * Suc c \<le> s \<and> s < 2 * length cs \<longrightarrow> p[Suc (2 * c) := 1] ! s = 0\<close> using z by auto
  then show ?thesis using S w unfolding wl_init_def by blast
qed

lemma wl_init_addw:
  fixes r :: \<open>64 word\<close>
  assumes \<open>wl_init cs (unat r) p nx h\<close> \<open>unat r < length cs\<close> \<open>2 \<le> length (cs ! unat r)\<close>
    \<open>lidx (cs ! unat r ! 0) = x0\<close> \<open>lidx (cs ! unat r ! Suc 0) = x1\<close>
    \<open>\<forall>i < length cs. length (cs ! i) < 18446744073709551616 \<and>
       (\<forall>j < length (cs ! i). 2 * unat (Lit_var (cs ! i ! j)) < 18446744073709551615 \<and>
          unat (Lit_var (cs ! i ! j)) < N)\<close>
    \<open>length h = 2 * N\<close> \<open>length cs < 9223372036854775808\<close>
  shows \<open>wl_init cs (Suc (unat r)) (p[unat (2 * r + 1) := 1])
           (nx[unat (2 * r) := h ! x0, unat (2 * r + 1) := h[x0 := 2 * r] ! x1]) (h[x0 := 2 * r, x1 := 2 * r + 1])\<close>
proof -
  have u: \<open>unat (2 * r) = 2 * unat r\<close> \<open>unat (2 * r + 1) = Suc (2 * unat r)\<close>
    using unat64_dbl_lt[OF assms(2,8)] by simp_all
  have l: \<open>0 < length (cs ! unat r)\<close> \<open>Suc 0 < length (cs ! unat r)\<close> using assms(3) by auto
  have v0: \<open>unat (Lit_var (cs ! unat r ! 0)) < N\<close> using assms(6)[rule_format, OF assms(2)] l(1) by blast
  have v1: \<open>unat (Lit_var (cs ! unat r ! Suc 0)) < N\<close> using assms(6)[rule_format, OF assms(2)] l(2) by blast
  have x: \<open>x0 < length h\<close> \<open>x1 < length h\<close> using v0 v1 assms(4,5,7) by (auto simp: lidx_def)
  have \<open>2 * length cs < 2 ^ 64\<close> using assms(8) by simp
  note A = wl_init_add[OF assms(1,2,3,4), of x1, OF _ x this, of \<open>2 * r\<close> \<open>2 * r + 1\<close>]
  show ?thesis using A assms(5) u by simp
qed

lemma wl_init_skipw:
  \<open>wl_init cs (unat r) p nx h \<Longrightarrow> unat r < length cs \<Longrightarrow> \<not> 2 \<le> length (cs ! unat r) \<Longrightarrow>
   wl_init cs (Suc (unat r)) p nx h\<close>
  by (rule wl_init_skip)

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
                unat c \<le> length cs \<and> length cs - unat c \<le> k \<and> wl_init cs (unat c) p nx h \<and> lends nx h\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gp p gn nx gh h gc c. p_ref \<mapsto>\<langle>\<top>\<rangle> gp\<down>p \<star> nx_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>nx \<star>
               h_ref \<mapsto>\<langle>\<top>\<rangle> gh\<down>h \<star> c_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c \<star> can_alloc_reference \<star>
               \<langle>(\<forall>i < length cs. length (cs ! i) < 18446744073709551616 \<and>
                  (\<forall>j < length (cs ! i). 2 * unat (Lit_var (cs ! i ! j)) < 18446744073709551615 \<and>
                     unat (Lit_var (cs ! i ! j)) < unat n)) \<and>
                length p = 2 * length cs \<and> length nx = 2 * length cs \<and> length h = 2 * unat n \<and>
                unat c < length cs \<and> length cs - unat c \<le> Suc k \<and> wl_init cs (unat c) p nx h \<and> lends nx h\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: word_less_nat_alt unat_of_nat_eq dpll_unat_Suc word_le_nat_alt len2_0 len2_1)
    apply (all \<open>(rule wl_init_skipw; (assumption | (simp; fail)))?\<close>)
    apply (all \<open>(rule wl_init_addw; (assumption | (simp add: lidx_def; fail)))?\<close>)
    apply (all \<open>(frule unat64_dbl_lt, assumption)?\<close>)
    apply (auto simp add: unat_of_nat_eq unat64_dbl intro!: nth_var_lt)
    apply (all \<open>(frule lits_lt_nth2, assumption, assumption)?\<close>)
    apply auto
    apply (all \<open>(rule wl_init_end, assumption, simp)?\<close>)
    apply (all \<open>(rule wl_init_0, simp)?\<close>)
    apply (all \<open>(rule lends_init)?\<close>)
    apply (all \<open>(rule lends_addw, assumption, assumption, assumption, assumption)?\<close>)
    apply (all \<open>((rule xlt[THEN conjunct1] xlt[THEN conjunct2]), assumption, assumption, assumption, simp)?\<close>)
    done
  apply (auto simp add: unat_of_nat_eq)
  done

lemma fw_step:
  \<open>\<forall>m < unat k. m \<noteq> unat i \<and> m \<noteq> unat j \<longrightarrow> lit_value_m a (c ! m) = Some False \<Longrightarrow>
   \<not> (k \<noteq> i \<and> k \<noteq> j \<and> lit_value_m a (c ! unat k) \<noteq> Some False) \<Longrightarrow>
   \<forall>m < Suc (unat k). m \<noteq> unat i \<and> m \<noteq> unat j \<longrightarrow> lit_value_m a (c ! m) = Some False\<close>
  by (metis less_Suc_eq unat_inj)

definition dpll_find_watch_contract ::
  \<open>bool option list \<Rightarrow> Lit list \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word option, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>dpll_find_watch_contract a c i j \<equiv>
     make_function_contract
       (can_alloc_reference \<star> \<langle>lits_lt (length a) c \<and> length c + 2 \<le> urust_fuel \<and> length c < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>fw_post a c i j r\<rangle>)\<close>

lemma dpll_find_watch_spec [crush_specs]:
  shows \<open>\<Gamma>; find_watch a c i j \<Turnstile>\<^sub>F dpll_find_watch_contract a c i j\<close>
  apply (crush_boot f: find_watch_def contract: dpll_find_watch_contract_def)
  apply (crush_base inline: len_def)
  subgoal for k_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>m. \<Squnion>gk k. k_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>k \<star> can_alloc_reference \<star>
               \<langle>unat k \<le> length c \<and> length c - unat k \<le> m \<and>
                (\<forall>m' < unat k. m' \<noteq> unat i \<and> m' \<noteq> unat j \<longrightarrow> lit_value_m a (c ! m') = Some False)\<rangle>\<close> and
        INV'=\<open>\<lambda>m. \<Squnion>gk k. k_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>k \<star> can_alloc_reference \<star>
               \<langle>unat k < length c \<and> length c - unat k \<le> Suc m \<and>
                (\<forall>m' < unat k. m' \<noteq> unat i \<and> m' \<noteq> unat j \<longrightarrow> lit_value_m a (c ! m') = Some False)\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>fw_post a c i j r\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: word_less_nat_alt unat_of_nat_eq dpll_unat_Suc)
    apply (all \<open>(frule (1) fw_step)?\<close>)
    apply (auto simp add: ASSUMPTION_def fw_post_def unat_inj less_Suc_eq intro: dpll_lits_lt_nth)
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
  \<open>64 word list \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow>
   ('s, 64 word list \<times> 64 word list \<times> 64 word list \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>dpll_move_watch_contract p nx h s prev x k y \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
          \<langle>unat s < length nx \<and> length p = length nx \<and> unat x < length h \<and> unat y < length h \<and>
           length nx < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>case r of (p1, nx1, h1, _) \<Rightarrow> length p1 = length p \<and> length nx1 = length nx \<and> length h1 = length h \<and>
             (p1, nx1, h1) = mw_m p nx h s prev x k y\<rangle>)\<close>

lemma dpll_move_watch_spec [crush_specs]:
  shows \<open>\<Gamma>; move_watch p nx h s prev x k y \<Turnstile>\<^sub>F dpll_move_watch_contract p nx h s prev x k y\<close>
  apply (crush_boot f: move_watch_def contract: dpll_move_watch_contract_def)
  apply (crush_base inline: len_def simp add: word_less_nat_alt unat_of_nat_eq mw_m_def Let_def)
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

lemma vs_unit_r:
  \<open>status_m a (cs ! i) None False = Status_Unit l \<Longrightarrow> i < length cs \<Longrightarrow>
   \<forall>i < length cs. lits_lt n (cs ! i) \<and> R i \<Longrightarrow> tr_ok n a t \<Longrightarrow> length rs = length t \<Longrightarrow> unat w = i \<Longrightarrow>
   rext cs t rs (t @ [l]) (rs @ [w])\<close>
  using rext_unit[OF rext_refl[of rs t cs], of a i l n w] by simp

lemma vs_cfl:
  \<open>status_m a (cs ! i) None False = Status_Conflict \<Longrightarrow> i < length cs \<Longrightarrow>
   \<forall>i < length cs. lits_lt n (cs ! i) \<and> R i \<Longrightarrow> tr_ok n a t \<Longrightarrow> cfl cs t i\<close>
  using cfl_status by blast

lemma lends_mw:
  assumes \<open>(p1, nx1, h1) = mw_m p nx h s prev x k y\<close> \<open>lends nx h\<close> \<open>unat s < length nx\<close> \<open>unat y < length h\<close>
  shows \<open>lends nx1 h1\<close>
proof (cases \<open>unat prev < length nx\<close>)
  case True
  have a: \<open>lends (nx[unat prev := nx ! unat s]) h\<close> by (rule lends_nx[OF assms(2) lends_nth_nx[OF assms(2,3)]])
  have b: \<open>lends ((nx[unat prev := nx ! unat s])[unat s := h ! unat y]) h\<close>
    by (rule lends_nx[OF a]) (use lends_nth_h[OF assms(2,4)] in simp)
  have c: \<open>lends ((nx[unat prev := nx ! unat s])[unat s := h ! unat y]) (h[unat y := s])\<close>
    by (rule lends_h[OF b]) (use assms(3) in simp)
  then show ?thesis using True assms(1) by (simp add: mw_m_def Let_def)
next
  case False
  let ?h1 = \<open>h[unat x := nx ! unat s]\<close>
  have a: \<open>lends nx ?h1\<close> by (rule lends_h[OF assms(2) lends_nth_nx[OF assms(2,3)]])
  have b: \<open>lends (nx[unat s := ?h1 ! unat y]) ?h1\<close>
    by (rule lends_nx[OF a]) (use lends_nth_h[OF a] assms(4) in simp)
  have c: \<open>lends (nx[unat s := ?h1 ! unat y]) (?h1[unat y := s])\<close>
    by (rule lends_h[OF b]) (use assms(3) in simp)
  then show ?thesis using False assms(1) by (simp add: mw_m_def Let_def)
qed

definition dpll_visit_slot_contract ::
  \<open>Lit list list \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> bool option list \<Rightarrow> Lit list \<Rightarrow>
   64 word list \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow>
   ('s, 64 word list \<times> 64 word list \<times> 64 word list \<times> bool option list \<times> Lit list \<times> 64 word list \<times> bool \<times> bool \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>dpll_visit_slot_contract cs p nx h a t rs x s prev \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
          \<langle>dpll_wpre cs (length a) p nx h \<and> unat x < length h \<and> unat s < 2 * length cs \<and> tr_ok (length a) a t \<and>
           length rs = length t \<and> lends nx h\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>case r of (p1, nx1, h1, a1, t1, rs1, keep, b, _) \<Rightarrow>
             dpll_wpre cs (length a) p1 nx1 h1 \<and> length a1 = length a \<and> wprop_post cs t (length a) a1 t1 b \<and>
             vslot_post cs p nx h a t x s prev p1 nx1 h1 a1 t1 keep b \<and>
             rext cs t rs t1 rs1 \<and> (\<not> b \<longrightarrow> cfl cs t1 (unat s div 2)) \<and> lends nx1 h1\<rangle>)\<close>

lemma oslot_even: \<open>even s \<Longrightarrow> oslot s (s + 1)\<close>
  by (simp add: oslot_def even_iff_mod_2_eq_zero)

lemma oslot_odd: \<open>s mod 2 = 1 \<Longrightarrow> oslot s (s - 1)\<close>
  by (simp add: oslot_def)

lemma var_bnd:
  \<open>\<forall>i < length cs. F1 i \<and> F2 i \<and> F3 i \<and>
     (\<forall>j < length (cs ! i). 2 * unat (Lit_var (cs ! i ! j)) < M \<and> unat (Lit_var (cs ! i ! j)) < N) \<Longrightarrow>
   i < length cs \<Longrightarrow> j < length (cs ! i) \<Longrightarrow> Suc (2 * unat (Lit_var (cs ! i ! j))) < 2 * N\<close>
  by fastforce

lemma var_bnd2:
  \<open>\<forall>i < length cs. F1 i \<and> F2 i \<and> F3 i \<and>
     (\<forall>j < length (cs ! i). 2 * unat (Lit_var (cs ! i ! j)) < M \<and> unat (Lit_var (cs ! i ! j)) < N) \<Longrightarrow>
   \<forall>i < length cs. \<forall>j < length (cs ! i). Suc (2 * unat (Lit_var (cs ! i ! j))) < 2 * N\<close>
  by fastforce

lemma dpll_visit_slot_spec [crush_specs]:
  shows \<open>\<Gamma>; visit_slot cs p nx h a t rs x s prev \<Turnstile>\<^sub>F dpll_visit_slot_contract cs p nx h a t rs x s prev\<close>
  apply (crush_boot f: visit_slot_def contract: dpll_visit_slot_contract_def)
  apply (crush_base wp split: option.splits Status.splits inline: vec_push_def
      simp add: dpll_wpre_def wcs_ok_def word_less_nat_alt unat_of_nat_eq unat_div unat_mod div2_lt
        even_Suc_lt Suc2_lt)
  apply (all \<open>(frule div2_lt[where L=\<open>length cs\<close>])?\<close>)
  apply (all \<open>(frule oslot_even)?\<close>)
  apply (all \<open>(frule oslot_odd)?\<close>)
  apply (all \<open>(rule vsp_skip_i; assumption)?\<close>)
  apply (all \<open>(rule vsp_skip_j; assumption)?\<close>)
  apply (all \<open>(rule vsp_skip_t; assumption)?\<close>)
  apply (all \<open>(rule vsp_move, assumption, assumption, assumption, (simp add: lidx_def; fail), assumption,
      assumption, assumption)?\<close>)
  apply (all \<open>(rule vsp_none(1); assumption)?\<close>)
  apply (all \<open>(rule vsp_none(2); assumption)?\<close>)
  apply (all \<open>(rule vsp_none(3); assumption)?\<close>)
  apply (all \<open>(rule vsp_none(4); assumption)?\<close>)
  apply (all \<open>(frule var_bnd2)?\<close>)
  apply (all \<open>(frule lends_mw, assumption, simp, (simp add: lidx_def; fail))?\<close>)
  apply (auto simp add: fw_post_def
      intro: vs_refl vs_conflict vs_unit vs_unit_var w_odd[THEN conjunct1] w_odd[THEN conjunct2] w_even
        rext_refl vs_unit_r vs_cfl)
  done

text \<open>The invariant of the loop of \<^verbatim>\<open>visit\<close> for the false literal of index \<open>x\<close>.\<close>
definition vinvx ::
  \<open>Lit list list \<Rightarrow> nat \<Rightarrow> 64 word list \<Rightarrow> Lit list \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow>
   Lit list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>vinvx cs x p t p' nx' h' t' s pr st \<equiv> \<exists>w. lidx w = x \<and> lneg w \<in> set t \<and> vinv cs x w p t p' nx' h' t' s pr st\<close>

lemma wpre_wf: \<open>dpll_wpre cs n p nx h \<Longrightarrow> dpll_wf n cs\<close>
  by (auto simp: dpll_wpre_def wcs_ok_def dpll_wf_def in_set_conv_nth)

lemma vx_entry:
  assumes \<open>wl_ok cs p nx h\<close> \<open>unat x < length h\<close> \<open>\<exists>w. lidx w = unat x \<and> lneg w \<in> set t\<close>
  shows \<open>vinvx cs (unat x) p t p nx h t (unat (h ! unat x)) (length nx) 0\<close>
  using vinv_entry[OF assms(1,2)] assms(3) by (auto simp: vinvx_def)

lemma vx_step:
  assumes \<open>vinvx cs (unat x) p t p' nx' h' t' (unat s) (unat pr) st\<close> \<open>unat s < length nx'\<close>
    \<open>vslot_post cs p' nx' h' a' t' x s pr p1 nx1 h1 a1 t1 keep True\<close>
    \<open>wprop_inv cs t n a' t'\<close> \<open>dpll_wpre cs n p' nx' h'\<close>
  shows \<open>vinvx cs (unat x) p t p1 nx1 h1 t1 (unat (nx' ! unat s)) (if keep then unat s else unat pr) (Suc st)\<close>
proof -
  obtain w where w: \<open>lidx w = unat x\<close> \<open>lneg w \<in> set t\<close> \<open>vinv cs (unat x) w p t p' nx' h' t' (unat s) (unat pr) st\<close>
    using assms(1) by (auto simp: vinvx_def)
  have T: \<open>tr_ok n a' t'\<close> \<open>\<exists>e. t' = t @ e\<close> using assms(4) by (auto simp: wprop_inv_def)
  have c: \<open>vctx cs n (unat x) w t h'\<close>
    using w(1,2) wpre_wf[OF assms(5)] assms(5) by (simp add: vctx_def dpll_wpre_def)
  show ?thesis using vinv_step[OF w(3) assms(2,3) T c] w(1,2) by (auto simp: vinvx_def)
qed

lemma vx_step2:
  assumes \<open>vinvx cs (unat x) p t p' nx' h' t' (unat s) (unat pr) st\<close> \<open>unat s < 2 * length cs\<close>
    \<open>length nx' = 2 * length cs\<close> \<open>vslot_post cs p' nx' h' a' t' x s pr p1 nx1 h1 a1 t1 keep True\<close>
    \<open>wprop_inv cs t n a' t'\<close> \<open>wcs_ok cs n F\<close> \<open>length h' = 2 * n\<close> \<open>length cs < 9223372036854775808\<close>
  shows \<open>vinvx cs (unat x) p t p1 nx1 h1 t1 (unat (nx' ! unat s)) (if keep then unat s else unat pr) (Suc st)\<close>
proof -
  obtain w where w: \<open>lidx w = unat x\<close> \<open>lneg w \<in> set t\<close> \<open>vinv cs (unat x) w p t p' nx' h' t' (unat s) (unat pr) st\<close>
    using assms(1) by (auto simp: vinvx_def)
  have T: \<open>tr_ok n a' t'\<close> \<open>\<exists>e. t' = t @ e\<close> using assms(5) by (auto simp: wprop_inv_def)
  have wf: \<open>dpll_wf n cs\<close> using assms(6) by (auto simp: wcs_ok_def dpll_wf_def in_set_conv_nth)
  have c: \<open>vctx cs n (unat x) w t h'\<close> using w(1,2) wf assms(7,8) by (simp add: vctx_def)
  show ?thesis using vinv_step[OF w(3) _ assms(4) T c] assms(2,3) w(1,2) by (auto simp: vinvx_def)
qed

lemma vx_entry2:
  \<open>wl_ok cs p nx h \<Longrightarrow> unat x < length h \<Longrightarrow> lidx w = unat x \<Longrightarrow> lneg w \<in> set t \<Longrightarrow>
   length nx = 2 * length cs \<Longrightarrow> vinvx cs (unat x) p t p nx h t (unat (h ! unat x)) (2 * length cs) 0\<close>
  using vx_entry[of cs p nx h x t] by auto

lemma vx_conflict:
  \<open>vinvx cs x p t p' nx' h' t' s pr st \<Longrightarrow> vslot_post cs p' nx' h' a' t' xw sw pw p1 nx1 h1 a1 t1 keep False \<Longrightarrow>
   visit_post cs x p t p1 nx1 h1 t1 False\<close>
  using visit_post_conflict by (auto simp: vinvx_def)

lemma vx_exit:
  \<open>vinvx cs x p t p' nx' h' t' s pr st \<Longrightarrow> \<not> (s < length nx' \<and> st < length nx') \<Longrightarrow>
   visit_post cs x p t p' nx' h' t' True\<close>
  using visit_post_exit vinv_bound by (fastforce simp: vinvx_def)

lemma vx_bound: \<open>vinvx cs x p t p' nx' h' t' s pr st \<Longrightarrow> s < length nx' \<Longrightarrow> st < length nx'\<close>
  using vinv_bound by (auto simp: vinvx_def)

lemma unat2_len: \<open>L < 9223372036854775808 \<Longrightarrow> unat (2 * word64_of_nat L) = 2 * L\<close>
  using unat64_dbl[of \<open>word64_of_nat L\<close>] by (simp add: unat_of_nat_eq)

lemma vx_entry':
  \<open>wl_ok cs p nx h \<Longrightarrow> unat x < length h \<Longrightarrow> lidx w = unat x \<Longrightarrow> lneg w \<in> set t \<Longrightarrow>
   length nx = 2 * length cs \<Longrightarrow> length cs < 9223372036854775808 \<Longrightarrow>
   vinvx cs (unat x) p t p nx h t (unat (h ! unat x)) (unat (2 * word64_of_nat (length cs))) 0\<close>
  using vx_entry[of cs p nx h x t] unat2_len[of \<open>length cs\<close>] by auto

lemma vx_exit2:
  assumes \<open>vinvx cs x p t p' nx' h' t' s pr st\<close> \<open>s < L \<longrightarrow> L = st\<close> \<open>length nx' = L\<close>
  shows \<open>visit_post cs x p t p' nx' h' t' True\<close>
proof (cases \<open>s < L\<close>)
  case True
  then show ?thesis using vx_bound[OF assms(1)] assms(2,3) by auto
next
  case False
  then show ?thesis using vx_exit[OF assms(1)] assms(3) by auto
qed

lemma rext_step:
  \<open>rext cs t rs t' rs' \<Longrightarrow> rext cs t' rs' t1 rs1 \<Longrightarrow> wprop_inv cs t n a' t' \<Longrightarrow> wprop_post cs t' n a1 t1 b \<Longrightarrow>
   rext cs t rs t1 rs1\<close>
  by (rule rext_trans) (auto simp: wprop_inv_def wprop_post_def)

definition dpll_visit_contract ::
  \<open>Lit list list \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> bool option list \<Rightarrow> Lit list \<Rightarrow>
   64 word list \<Rightarrow> 64 word \<Rightarrow>
   ('s, 64 word list \<times> 64 word list \<times> 64 word list \<times> bool option list \<times> Lit list \<times> 64 word list \<times> bool \<times>
     64 word \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>dpll_visit_contract cs p nx h a t rs x \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
          \<langle>dpll_wpre cs (length a) p nx h \<and> unat x < length h \<and> tr_ok (length a) a t \<and> wl_ok cs p nx h \<and>
           (\<exists>w. lidx w = unat x \<and> lneg w \<in> set t) \<and> length rs = length t \<and> lends nx h\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>case r of (p1, nx1, h1, a1, t1, rs1, b, cf, _) \<Rightarrow>
             dpll_wpre cs (length a) p1 nx1 h1 \<and> length a1 = length a \<and> wprop_post cs t (length a) a1 t1 b \<and>
             visit_post cs (unat x) p t p1 nx1 h1 t1 b \<and>
             rext cs t rs t1 rs1 \<and> (\<not> b \<longrightarrow> cfl cs t1 (unat cf)) \<and> lends nx1 h1\<rangle>)\<close>

lemma dpll_visit_spec [crush_specs]:
  shows \<open>\<Gamma>; visit cs p nx h a t rs x \<Turnstile>\<^sub>F dpll_visit_contract cs p nx h a t rs x\<close>
  apply (crush_boot f: visit_def contract: dpll_visit_contract_def)
  apply (crush_base inline: len_def simp add: dpll_wpre_def)
  subgoal for w p_ref nx_ref h_ref a_ref t_ref r_ref s_ref pr_ref st_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gp p' gn nx' gh h' ga a' gt t' gr' rs' gs s' gr pr gq st.
               p_ref \<mapsto>\<langle>\<top>\<rangle> gp\<down>p' \<star> nx_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>nx' \<star> h_ref \<mapsto>\<langle>\<top>\<rangle> gh\<down>h' \<star>
               a_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>a' \<star> t_ref \<mapsto>\<langle>\<top>\<rangle> gt\<down>t' \<star> r_ref \<mapsto>\<langle>\<top>\<rangle> gr'\<down>rs' \<star>
               s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> pr_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>pr \<star> st_ref \<mapsto>\<langle>\<top>\<rangle> gq\<down>st \<star>
               can_alloc_reference \<star>
               \<langle>dpll_wpre cs (length a) p' nx' h' \<and> length nx' = length nx \<and> length h' = length h \<and>
                length a' = length a \<and> tr_ok (length a) a' t' \<and> wprop_inv cs t (length a) a' t' \<and>
                unat st \<le> length nx \<and> (unat s' < length nx \<longrightarrow> length nx - unat st \<le> k) \<and>
                vinvx cs (unat x) p t p' nx' h' t' (unat s') (unat pr) (unat st) \<and>
                rext cs t rs t' rs' \<and> lends nx' h'\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gp p' gn nx' gh h' ga a' gt t' gr' rs' gs s' gr pr gq st.
               p_ref \<mapsto>\<langle>\<top>\<rangle> gp\<down>p' \<star> nx_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>nx' \<star> h_ref \<mapsto>\<langle>\<top>\<rangle> gh\<down>h' \<star>
               a_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>a' \<star> t_ref \<mapsto>\<langle>\<top>\<rangle> gt\<down>t' \<star> r_ref \<mapsto>\<langle>\<top>\<rangle> gr'\<down>rs' \<star>
               s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> pr_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>pr \<star> st_ref \<mapsto>\<langle>\<top>\<rangle> gq\<down>st \<star>
               can_alloc_reference \<star>
               \<langle>dpll_wpre cs (length a) p' nx' h' \<and> length nx' = length nx \<and> length h' = length h \<and>
                length a' = length a \<and> tr_ok (length a) a' t' \<and> wprop_inv cs t (length a) a' t' \<and>
                unat s' < length nx \<and> unat st < length nx \<and> length nx - unat st \<le> Suc k \<and>
                vinvx cs (unat x) p t p' nx' h' t' (unat s') (unat pr) (unat st) \<and>
                rext cs t rs t' rs' \<and> lends nx' h'\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star>
          \<langle>case r of (p1, nx1, h1, a1, t1, rs1, b, cf, _) \<Rightarrow>
             dpll_wpre cs (length a) p1 nx1 h1 \<and> length a1 = length a \<and> wprop_post cs t (length a) a1 t1 b \<and>
             visit_post cs (unat x) p t p1 nx1 h1 t1 b \<and>
             rext cs t rs t1 rs1 \<and> (\<not> b \<longrightarrow> cfl cs t1 (unat cf)) \<and> lends nx1 h1\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base wp split: prod.splits tnil.splits simp add: word_less_nat_alt unat_of_nat_eq dpll_unat_Suc)
    apply (all \<open>(frule (1) wprop_step)?\<close>)
    apply (all \<open>(frule (4) vx_step)?\<close>)
    apply (all \<open>(frule (7) vx_step2)?\<close>)
    apply (all \<open>(frule (1) vx_conflict)?\<close>)
    apply (all \<open>(frule (3) rext_step)?\<close>)
    apply (auto simp add: dpll_wpre_def unat64_dbl unat_of_nat_eq wprop_post_def unat2_len unat_div
        intro: wprop_refl vx_entry' vx_entry2 vx_exit2 rext_refl dest: vx_bound rext_len)
    done
  done

end

end
