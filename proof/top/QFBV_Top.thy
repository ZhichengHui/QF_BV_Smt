theory QFBV_Top
  imports "QFBV_Proof.QFBV_Proof" QFBV_SmtSize QFBV_SmtBound QFBV_SmtRefine
begin

section \<open>The top-level theorem\<close>

text \<open>\<^verbatim>\<open>check_sat\<close> satisfies \<^const>\<open>QFBV_ctx.check_sat_contract\<close> for every fuel at least
  \<open>fuel_top\<close> of the problem. The proof composes the contracts of \<^verbatim>\<open>in_fragment\<close>,
  \<^verbatim>\<open>tr_size\<close>, \<^verbatim>\<open>tr_problem\<close>, \<^verbatim>\<open>size_ok\<close>, \<^verbatim>\<open>solve\<close> and \<^verbatim>\<open>tr_model\<close> with the
  semantic correctness of the translation (\<^verbatim>\<open>QFBV_SmtModel\<close>) and the size bound
  (\<^verbatim>\<open>QFBV_SmtBound\<close>).\<close>

lemma tr_asserts_count:
  \<open>length (snd (foldl (tr_asserts_step p dm) (S, acc) ts)) = length acc + length ts\<close>
  by (induction ts arbitrary: S acc) (auto simp: tr_asserts_step_def Let_def)

lemma asserts_length: \<open>length (Problem_asserts (tr_problem_m p)) = length (SmtProblem_asserts p)\<close>
  by (simp add: tr_problem_m_def tr_asserts_m_step Let_def tr_asserts_count)

lemma widths_length: \<open>length (Problem_widths (tr_problem_m p)) = length (SmtProblem_funs p)\<close>
  by (simp add: tr_problem_m_def Let_def)

lemma defs_length: \<open>length (Problem_defs (tr_problem_m p)) = tsize p\<close>
  using tsize_length[of p] by (simp add: tr_problem_m_def Let_def)

text \<open>A fuel sufficient for every loop and recursion of \<^verbatim>\<open>check_sat\<close> on \<open>p\<close>.\<close>
definition fuel_top :: \<open>SmtProblem \<Rightarrow> nat\<close> where
  \<open>fuel_top p \<equiv> N p + fuel_smt p + fuel_q (tr_problem_m p) + size_bound (tr_problem_m p)\<close>

lemma tsz_lt:
  fixes x xa :: \<open>64 word\<close>
  shows \<open>unat x = sat T \<Longrightarrow> unat xa = 9223372036854775808 \<Longrightarrow> \<not> xa \<le> x \<Longrightarrow> T < 2 ^ 63\<close>
  by (simp add: word_le_nat_alt sat_def min_def split: if_splits)

lemma tsz_ge:
  fixes x xa :: \<open>64 word\<close>
  shows \<open>unat x = sat T \<Longrightarrow> unat xa = 9223372036854775808 \<Longrightarrow> xa \<le> x \<Longrightarrow> \<not> T < 2 ^ 63\<close>
  by (simp add: word_le_nat_alt sat_def min_def split: if_splits)

context QFBV_ctx
begin

text \<open>The contract of \<^verbatim>\<open>solve\<close> with the size condition in the precondition, so that it
  holds for every problem given enough fuel.\<close>
definition solve_contract_b :: \<open>Problem \<Rightarrow> ('s, Answer, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>solve_contract_b q \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>problem_wt q \<and> size_bound q < 2 ^ 63\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>case r of Answer_Sat m \<Rightarrow> is_model q m | Answer_Unsat \<Rightarrow> (\<forall>m. \<not> is_model q m)\<rangle>)\<close>

lemma solve_spec_b:
  assumes \<open>size_bound q \<le> urust_fuel\<close>
  shows \<open>\<Gamma>; solve q \<Turnstile>\<^sub>F solve_contract_b q\<close>
proof (cases \<open>size_bound q < 2 ^ 63\<close>)
  case True
  then have b: \<open>size_bound q < 2 ^ 64\<close> by simp
  show ?thesis
    apply (rule satisfies_function_contract_weaken[OF solve_spec[OF assms b]])
      apply (simp_all add: solve_contract_b_def solve_contract_def Let_def)
      apply (crush_base)+
    done
next
  case False
  then show ?thesis
    apply -
    apply (ucincl_discharge\<open>intro satisfies_function_contractI\<close>)
    apply (subst wp_sstriple_iff)
    apply (simp add: solve_contract_b_def Let_def apure_precise_False asepconj_bot_zero2 bot_aentails_all)
    done
qed

lemma check_sat_spec:
  assumes F: \<open>fuel_top p \<le> urust_fuel\<close>
  shows \<open>\<Gamma>; check_sat p \<Turnstile>\<^sub>F check_sat_contract p\<close>
proof (cases \<open>smt_wf p \<and> smt_repr_ok p\<close>)
  case False
  then show ?thesis
    apply -
    apply (ucincl_discharge\<open>intro satisfies_function_contractI\<close>)
    apply (subst wp_sstriple_iff)
    apply (auto simp add: check_sat_contract_def Let_def apure_precise_False asepconj_bot_zero2 bot_aentails_all)
    done
next
  case True
  then have W: \<open>smt_wf p\<close> and R: \<open>smt_repr_ok p\<close> by simp_all
  let ?q = \<open>tr_problem_m p\<close>
  have NF: \<open>N p \<le> urust_fuel\<close> \<open>fuel_smt p \<le> urust_fuel\<close> \<open>fuel_q ?q \<le> urust_fuel\<close>
    \<open>size_bound ?q \<le> urust_fuel\<close> using F by (simp_all add: fuel_top_def)
  have IP: \<open>length (SmtProblem_funs p) < 2 ^ 64 \<and> length (SmtProblem_funs p) \<le> urust_fuel \<and>
            (\<forall>f \<in> set (SmtProblem_funs p). length (SmtFun_args f) < 2 ^ 64)\<close>
    using in_fragment_pre[OF R NF(1)] .
  have TS: \<open>tsize_pre urust_fuel p\<close> using tsize_pre_of_wf[OF W R NF(2)] .
  have TP: \<open>tr_pre urust_fuel p\<close> using tr_problem_pre[OF W R NF(1)] .
  have RL: \<open>length (SmtProblem_funs p) < 2 ^ 63\<close> \<open>length (SmtProblem_asserts p) < 2 ^ 63\<close>
    using R by (simp_all add: smt_repr_ok_def)
  have L64: \<open>length (fst (tr_asserts_m p (tr_defs_m p))) < 2 ^ 64\<close> if \<open>tsize p < 2 ^ 63\<close>
    using that tsize_length[of p] by simp
  have PW: \<open>problem_wt ?q\<close> if \<open>smt_fragment p\<close> \<open>tsize p < 2 ^ 63\<close>
    using problem_wt_tr[OF W that(1) L64[OF that(2)]] .
  have SP: \<open>size_pre urust_fuel ?q\<close> if \<open>smt_fragment p\<close> \<open>tsize p < 2 ^ 63\<close>
    using size_pre_of_wt[OF PW[OF that] cok_problem[OF R]] RL that(2) NF(3)
    by (simp add: widths_length defs_length asserts_length)
  have MC: \<open>smt_is_model p (tr_model_m p m)\<close>
    if \<open>smt_fragment p\<close> \<open>tsize p < 2 ^ 63\<close> \<open>is_model ?q m\<close> for m
    using tr_model_correct[OF W that(1) L64[OF that(2)] that(3)] .
  have UC: \<open>\<not> smt_satisfiable p\<close>
    if \<open>smt_fragment p\<close> \<open>tsize p < 2 ^ 63\<close> \<open>\<forall>m. \<not> is_model ?q m\<close>
    using tr_complete[OF W that(1) L64[OF that(2)]] that(3) by blast
  have B: \<open>tsize p < 2 ^ 63\<close> \<open>size_bound ?q < 2 ^ 63\<close> if \<open>smt_fragment p\<close> \<open>smt_sizes_ok p\<close>
    using tr_size_bound[OF W that] by simp_all
  show ?thesis
    apply (crush_boot f: check_sat_def contract: check_sat_contract_def)
    apply (crush_base specs add: solve_spec_b[OF NF(4)] simp add: IP TS TP W R)
    subgoal for x xa xb
      apply (cases xb; crush_base)
      apply (all \<open>frule tsz_lt, assumption, assumption\<close>)
      using UC MC tr_model_pre[OF _ R NF(1)] by auto
    subgoal using PW tsz_lt by blast
    subgoal using B(2) by simp
    subgoal using SP tsz_lt by blast
    subgoal using B(1) tsz_ge by blast
    subgoal using IP by auto
    subgoal using IP by auto
    done
qed

end

subsection \<open>The statement over all instances with enough fuel\<close>

context QFBV_heap
begin

text \<open>The top-level statement \<^const>\<open>check_sat_correct\<close> of \<^verbatim>\<open>QFBV_Spec\<close>: for every problem
  satisfying the precondition, \<^verbatim>\<open>check_sat\<close> satisfies its contract with any fuel at least
  \<^const>\<open>fuel_top\<close> of the problem.\<close>
theorem check_sat_correct:
  shows \<open>check_sat_correct \<Gamma>\<close>
proof (unfold check_sat_correct_def, intro allI impI)
  fix p :: SmtProblem
  assume \<open>smt_wf p \<and> smt_repr_ok p\<close>
  have \<open>\<Gamma>; check_sat fuel p \<Turnstile>\<^sub>F check_sat_contract p\<close> if \<open>fuel_top p \<le> fuel\<close> for fuel
    by (rule QFBV_ctx.check_sat_spec[OF QFBV_ctxI that])
  then show \<open>\<exists>N. \<forall>fuel \<ge> N. \<Gamma>; check_sat fuel p \<Turnstile>\<^sub>F check_sat_contract p\<close>
    by (intro exI[of _ \<open>fuel_top p\<close>]) simp
qed

end

end
