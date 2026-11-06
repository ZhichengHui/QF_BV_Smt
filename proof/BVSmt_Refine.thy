theory BVSmt_Refine
  imports BVSmt_Defs
begin

section \<open>The Rust functions compute their models\<close>

lemma unat_word_Suc_simp:
  fixes x :: \<open>64 word\<close>
  assumes \<open>unat x < 18446744073709551615\<close>
  shows \<open>unat (x + 1) = Suc (unat x)\<close>
  using assms by (metis Suc_eq_plus1 add.commute unatSuc2 unat_minus_one_word word_less_nat_alt
      unsigned_less linorder_neq_iff word_of_nat_less)

lemma st_of_cnf_of [simp]:
  \<open>fst s < 2 ^ 64 \<Longrightarrow> st_of (cnf_of s) = s\<close>
  by (cases s) (simp add: st_of_def cnf_of_def unat_of_nat_eq)

context BVSmt_ctx
begin

subsection \<open>Literals, clauses, gates\<close>

definition lit_const_contract :: \<open>bool \<Rightarrow> ('s, Lit, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>lit_const_contract b \<equiv>
     make_function_contract can_alloc_reference (\<lambda>r. can_alloc_reference \<star> \<langle>r = lconst b\<rangle>)\<close>

lemma lit_const_spec [crush_specs]:
  shows \<open>\<Gamma>; lit_const b \<Turnstile>\<^sub>F lit_const_contract b\<close>
  by (crush_boot f: lit_const_def contract: lit_const_contract_def)
     (crush_base simp add: lconst_def)

definition lit_neg_contract :: \<open>Lit \<Rightarrow> ('s, Lit, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>lit_neg_contract l \<equiv>
     make_function_contract can_alloc_reference (\<lambda>r. can_alloc_reference \<star> \<langle>r = lneg l\<rangle>)\<close>

lemma lit_neg_spec [crush_specs]:
  shows \<open>\<Gamma>; lit_neg l \<Turnstile>\<^sub>F lit_neg_contract l\<close>
  by (crush_boot f: lit_neg_def contract: lit_neg_contract_def)
     (crush_base simp add: lneg_def)

lemma Cnf_num_vars_cnf_of [simp]: \<open>Cnf_num_vars (cnf_of s) = word_of_nat (fst s)\<close>
  by (simp add: cnf_of_def)

lemma Cnf_clauses_cnf_of [simp]: \<open>Cnf_clauses (cnf_of s) = snd s\<close>
  by (simp add: cnf_of_def)

definition fresh_fn_contract :: \<open>st \<Rightarrow> ('s, Cnf \<times> Lit \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>fresh_fn_contract s \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>Suc (fst s) < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = (cnf_of (fst (fresh_m s)), snd (fresh_m s), TNil)\<rangle>)\<close>

lemma fresh_fn_spec [crush_specs]:
  shows \<open>\<Gamma>; fresh_fn (cnf_of s) \<Turnstile>\<^sub>F fresh_fn_contract s\<close>
  apply (crush_boot f: fresh_fn_def contract: fresh_fn_contract_def)
  apply (crush_base simp add: fresh_m_def cnf_of_def unat_of_nat_eq)
  done

definition add_clause_contract :: \<open>st \<Rightarrow> Lit list \<Rightarrow> ('s, Cnf, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>add_clause_contract s cl \<equiv>
     make_function_contract can_alloc_reference
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = cnf_of (addc_m s cl)\<rangle>)\<close>

lemma add_clause_spec [crush_specs]:
  shows \<open>\<Gamma>; add_clause (cnf_of s) cl \<Turnstile>\<^sub>F add_clause_contract s cl\<close>
  apply (crush_boot f: add_clause_def contract: add_clause_contract_def)
  apply (crush_base inline: vec_push_def simp add: addc_m_def cnf_of_def)
  done

definition clause3_contract :: \<open>Lit \<Rightarrow> Lit \<Rightarrow> Lit \<Rightarrow> ('s, Lit list, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>clause3_contract a b d \<equiv>
     make_function_contract can_alloc_reference (\<lambda>r. can_alloc_reference \<star> \<langle>r = [a, b, d]\<rangle>)\<close>

lemma clause3_spec [crush_specs]:
  shows \<open>\<Gamma>; clause3 a b d \<Turnstile>\<^sub>F clause3_contract a b d\<close>
  apply (crush_boot f: clause3_def contract: clause3_contract_def)
  apply (crush_base inline: vec_push_def)
  done

definition clause2_contract :: \<open>Lit \<Rightarrow> Lit \<Rightarrow> ('s, Lit list, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>clause2_contract a b \<equiv>
     make_function_contract can_alloc_reference (\<lambda>r. can_alloc_reference \<star> \<langle>r = [a, b]\<rangle>)\<close>

lemma clause2_spec [crush_specs]:
  shows \<open>\<Gamma>; clause2 a b \<Turnstile>\<^sub>F clause2_contract a b\<close>
  apply (crush_boot f: clause2_def contract: clause2_contract_def)
  apply (crush_base inline: vec_push_def)
  done

definition gate_and_contract :: \<open>st \<Rightarrow> Lit \<Rightarrow> Lit \<Rightarrow> ('s, Cnf \<times> Lit \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>gate_and_contract s a b \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>Suc (fst s) < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = (cnf_of (fst (and_m s a b)), snd (and_m s a b), TNil)\<rangle>)\<close>

lemma gate_and_spec [crush_specs]:
  shows \<open>\<Gamma>; gate_and (cnf_of s) a b \<Turnstile>\<^sub>F gate_and_contract s a b\<close>
  apply (crush_boot f: gate_and_def contract: gate_and_contract_def)
  apply (crush_base simp add: and_m_def fresh_m_def addc_m_def)
  done

subsection \<open>A loop\<close>

definition bv_not_contract :: \<open>Lit list \<Rightarrow> ('s, Lit list, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>bv_not_contract a \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>length a \<le> urust_fuel \<and> length a < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = not_m a\<rangle>)\<close>

lemma bv_not_spec [crush_specs]:
  shows \<open>\<Gamma>; bv_not a \<Turnstile>\<^sub>F bv_not_contract a\<close>
  apply (crush_boot f: bv_not_def contract: bv_not_contract_def)
  apply (crush_base inline: len_def)
  subgoal for r_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gr r gi i. r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i \<le> length a \<and> r = map lneg (take (unat i) a) \<and> length a - unat i \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gr r gi i. r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i < length a \<and> r = map lneg (take (unat i) a) \<and> length a - unat i \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>r = not_m a\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: vec_push_def simp add: word_less_nat_alt unat_of_nat_eq unat_word_Suc_simp
        not_m_def take_Suc_conv_app_nth)
    done
  done

end

end
