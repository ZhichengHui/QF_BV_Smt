theory BVSmt_Proof
  imports BVSmt_Refine BVSmt_Encode BVSmt_Dpll
begin

section \<open>The top-level theorem\<close>

subsection \<open>The two answers\<close>

lemma fuel_bound_ge:
  assumes \<open>encode_m p = (s, vs)\<close>
  shows \<open>fst s + 2 \<le> fuel_bound p\<close> \<open>length (snd s) + 2 \<le> fuel_bound p\<close>
    \<open>\<forall>c \<in> set (snd s). length c + 2 \<le> fuel_bound p\<close>
    \<open>\<forall>w \<in> set (var_widths p). w + 2 \<le> fuel_bound p\<close>
    \<open>length (var_widths p) + 2 \<le> fuel_bound p\<close>
  using assms by (auto intro!: fb_ge simp: fb_set_def intro: rev_image_eqI)

text \<open>No assignment satisfies the CNF formula: no model satisfies the problem.\<close>
lemma unsat_answer:
  assumes \<open>problem_wt p\<close> \<open>encode_m p = (s, vs)\<close> \<open>fst s < 2 ^ 64\<close>
    \<open>\<not> (\<exists>\<sigma>. agrees (replicate (fst s) None) \<sigma> \<and> cnf_sem \<sigma> (snd s))\<close>
  shows \<open>\<forall>m. is_model p m \<longrightarrow> \<not> satisfies p m\<close>
  using assms encode_complete[OF assms(1-3)] by (auto simp add: agrees_def)

text \<open>A total assignment satisfies the CNF formula: the model read from it satisfies the problem.\<close>
lemma sat_answer:
  assumes \<open>problem_wt p\<close> \<open>encode_m p = (s, vs)\<close> \<open>fst s < 2 ^ 64\<close>
    \<open>length a = fst s\<close> \<open>\<forall>v < length a. a ! v \<noteq> None\<close> \<open>cnf_sem (sigma_of a) (snd s)\<close>
  shows \<open>is_model p (read_model_m a vs) \<and> satisfies p (read_model_m a vs)\<close>
proof -
  have \<open>\<forall>ls \<in> set vs. lits_lt (length a) ls\<close>
    using encode_wf[OF assms(1-3)] assms(4) by simp
  then have \<open>read_model_m a vs = map (map (lit_sem (sigma_of a))) vs\<close>
    using read_model_sigma assms(5) by blast
  then show ?thesis
    using encode_sound[OF assms(1-3) assms(6)] by simp
qed

context BVSmt_ctx
begin

subsection \<open>The solver meets its contract\<close>

text \<open>The theorem: \<^const>\<open>solve_contract\<close> holds whenever the translation's fuel covers
  \<^const>\<open>fuel_bound\<close> and the problem is small enough for \<^verbatim>\<open>usize\<close>. \<^const>\<open>fuel_bound\<close> is defined
  outside the locale, so it does not depend on \<^term>\<open>urust_fuel\<close>.\<close>
theorem solve_spec:
  assumes \<open>fuel_bound p \<le> urust_fuel\<close> \<open>fuel_bound p < 2 ^ 64\<close>
  shows \<open>\<Gamma>; solve p \<Turnstile>\<^sub>F solve_contract p\<close>
proof -
  obtain s vs where e: \<open>encode_m p = (s, vs)\<close>
    by (cases \<open>encode_m p\<close>)
  note fb = fuel_bound_ge[OF e]
  have s64: \<open>fst s < 2 ^ 64\<close>
    using fb(1) assms(2) by simp
  have nv: \<open>unat (word_of_nat (fst s) :: 64 word) = fst s\<close>
    using s64 by (simp add: unat_of_nat_eq)
  have dpll_pre: \<open>problem_wt p \<Longrightarrow>
      (\<forall>c \<in> set (snd s). lits_lt (fst s) c \<and> length c + 2 \<le> urust_fuel \<and> length c < 2 ^ 64) \<and>
      length (snd s) + 2 \<le> urust_fuel \<and> length (snd s) < 2 ^ 64 \<and>
      fst s + 2 \<le> urust_fuel \<and> fst s < 2 ^ 64\<close>
    using encode_wf[OF _ e s64] fb assms by fastforce
  have rm_pre: \<open>problem_wt p \<Longrightarrow>
      (\<forall>ls \<in> set vs. lits_lt (fst s) ls \<and> length ls + 2 \<le> urust_fuel \<and> length ls < 2 ^ 64) \<and>
      length vs + 2 \<le> urust_fuel \<and> length vs < 2 ^ 64\<close>
  proof -
    assume wt: \<open>problem_wt p\<close>
    note w = encode_wf[OF wt e s64]
    have \<open>\<forall>ls \<in> set vs. length ls + 2 \<le> fuel_bound p\<close>
      using w fb(4) by (auto simp add: in_set_conv_nth var_widths_def) (blast intro: nth_mem)
    moreover have \<open>length vs + 2 \<le> fuel_bound p\<close>
      using w fb(5) by (simp add: var_widths_def)
    ultimately show ?thesis
      using w assms by fastforce
  qed
  show ?thesis
    apply (crush_boot f: solve_def contract: solve_contract_def)
    apply (crush_base specs add: encode_spec dpll_top_spec read_model_spec
        contracts add: encode_contract_def dpll_top_contract_def read_model_contract_def
        simp add: e assms nv)
    using dpll_pre rm_pre unsat_answer[OF _ e s64] sat_answer[OF _ e s64]
    by (auto split: option.splits)
qed

end

end
