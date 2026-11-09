theory BVSmt_Proof
  imports BVSmt_Refine BVSmt_Encode BVSmt_Dpll BVSmt_Bound
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
  shows \<open>\<forall>m. is_assignment p m \<longrightarrow> \<not> satisfies p m\<close>
  using assms encode_complete[OF assms(1-3)] by (auto simp add: agrees_def)

text \<open>A total assignment satisfies the CNF formula: the model read from it satisfies the problem.\<close>
lemma sat_answer:
  assumes \<open>problem_wt p\<close> \<open>encode_m p = (s, vs)\<close> \<open>fst s < 2 ^ 64\<close>
    \<open>length a = fst s\<close> \<open>\<forall>v < length a. a ! v \<noteq> None\<close> \<open>cnf_sem (sigma_of a) (snd s)\<close>
  shows \<open>is_assignment p (read_model_m a vs) \<and> satisfies p (read_model_m a vs)\<close>
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
  \<^const>\<open>size_bound\<close> and \<^const>\<open>size_bound\<close> is small enough for \<^verbatim>\<open>usize\<close>. \<^const>\<open>size_bound\<close> is defined
  in the specification from the problem alone. For a well-sorted problem it is at least
  \<^const>\<open>fuel_bound\<close> (\<open>fuel_bound_le\<close>), which the proof uses; a problem that is not well-sorted
  makes the precondition of the contract false.\<close>
theorem solve_spec:
  assumes \<open>size_bound p \<le> urust_fuel\<close> \<open>size_bound p < 2 ^ 64\<close>
  shows \<open>\<Gamma>; solve p \<Turnstile>\<^sub>F solve_contract p\<close>
proof (cases \<open>problem_wt p\<close>)
  case True
  have assms2: \<open>fuel_bound p \<le> urust_fuel\<close> \<open>fuel_bound p < 2 ^ 64\<close>
    using fuel_bound_le[OF True] assms by simp_all
  obtain s vs where e: \<open>encode_m p = (s, vs)\<close>
    by (cases \<open>encode_m p\<close>)
  note fb = fuel_bound_ge[OF e]
  have s64: \<open>fst s < 2 ^ 64\<close>
    using fb(1) assms2(2) by simp
  have nv: \<open>unat (word_of_nat (fst s) :: 64 word) = fst s\<close>
    using s64 by (simp add: unat_of_nat_eq)
  have dpll_pre: \<open>problem_wt p \<Longrightarrow>
      (\<forall>c \<in> set (snd s). lits_lt (fst s) c \<and> length c + 2 \<le> urust_fuel \<and> length c < 2 ^ 64) \<and>
      length (snd s) + 2 \<le> urust_fuel \<and> length (snd s) < 2 ^ 64 \<and>
      fst s + 2 \<le> urust_fuel \<and> fst s < 2 ^ 64\<close>
    using encode_wf[OF _ e s64] fb assms2 by fastforce
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
      using w assms2 by fastforce
  qed
  show ?thesis
    apply (crush_boot f: solve_def contract: solve_contract_def)
    apply (crush_base specs add: encode_spec dpll_top_spec read_model_spec
        contracts add: encode_contract_def dpll_top_contract_def read_model_contract_def
        split: option.splits
        simp add: e assms2 nv Cnf_Cnf_clauses_lens_view_update_modify Cnf_Cnf_num_vars_lens_view_update_modify)
    using assms2 dpll_pre rm_pre unsat_answer[OF _ e s64] sat_answer[OF _ e s64]
    by (auto simp: is_model_def split: option.splits)
next
  case False
  show ?thesis
    apply (crush_boot f: solve_def contract: solve_contract_def)
    using False by simp
qed

end

end
