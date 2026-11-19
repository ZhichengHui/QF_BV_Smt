theory QFBV_Dpll
  imports QFBV_Watch
begin

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
