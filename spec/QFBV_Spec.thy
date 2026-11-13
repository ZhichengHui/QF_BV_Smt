theory QFBV_Spec
  imports SMT_Semantics
begin

section \<open>The top-level specification\<close>

text \<open>
  This theory, with \<^verbatim>\<open>SMT_Types\<close> and \<^verbatim>\<open>SMT_Semantics\<close> that it builds on, is the whole
  specification of the solver: the meaning of the top-level theorem depends on nothing outside
  \<^verbatim>\<open>spec/\<close>. The proofs (\<^verbatim>\<open>proof/\<close>) and the solver may change; this directory changes only
  when the specification does.

  The Rust entry point is \<^verbatim>\<open>pub fn check_sat(p: &SmtProblem) -> SmtAnswer\<close>
  (\<^verbatim>\<open>core/src/lib.rs\<close>), translated to \<^verbatim>\<open>QFBV_ctx.check_sat\<close>. The statement
  \<open>check_sat_correct\<close> at the end of this theory: for every well-sorted problem there is a bound
  \<open>N\<close> such that, with any fuel at least \<open>N\<close>, \<^verbatim>\<open>check_sat\<close> satisfies its contract. The
  contract allows the answer \<^verbatim>\<open>Sat\<close> only with a model, \<^verbatim>\<open>Unsat\<close> only for a problem without a
  model, and \<^verbatim>\<open>Unknown\<close> only for a problem outside the fragment of this solver or outside
  its input range (\<open>smt_in_range\<close>).

  Trusted, not proved here:
  \<^item> The translation (AutoCorrode) gives the Rust program its meaning. The theorem is about the
    translated function; that it carries over to the compiled Rust program rests on the
    translation.
  \<^item> The statement is made in the locale \<open>QFBV_heap\<close>, whose assumptions describe a heap with one
    kind of reference per type of mutable local. They are those of AutoCorrode's reference model,
    and the theorem holds for every heap that satisfies them.
  \<^item> The front end (\<^verbatim>\<open>frontend/\<close>), which turns SMT-LIB text into a \<^typ>\<open>SmtProblem\<close> and a
    \<^typ>\<open>SmtModel\<close> back into text, is not verified.
\<close>

subsection \<open>The fragment\<close>

text \<open>The fragment of this solver: no uninterpreted sort, and every declared symbol a constant.\<close>
definition smt_fragment :: \<open>SmtProblem \<Rightarrow> bool\<close> where
  \<open>smt_fragment p \<equiv> unat (SmtProblem_num_sorts p) = 0 \<and> (\<forall>f \<in> set (SmtProblem_funs p). SmtFun_args f = [])\<close>


subsection \<open>The input range\<close>

text \<open>The problems on which this solver promises an answer other than \<^verbatim>\<open>Unknown\<close> (besides
  being in its fragment). The range is part of the specification and fixed: it is stated with the
  measures of \<^verbatim>\<open>SMT_Semantics\<close>, which describe the problem as written, and does not depend on
  how the solver works. A change of the solver must keep answering every problem of the range.
  The range of this solver: \<^const>\<open>smt_size\<close> at most \<open>2^28\<close> (about \<open>2.7 \<cdot> 10^8\<close>), every
  bit-vector width at most \<open>2^20\<close>, and every multiplication, division and remainder of width at
  most \<open>2^12\<close> (\<^const>\<open>smt_max_mul_width\<close>), and every \<open>distinct\<close> of bit-vectors with at most
  \<open>2^8\<close> arguments (\<^const>\<open>smt_max_bv_distinct\<close>). The QF\_BV problems of the SMT-LIB 2025 release
  have size at most about \<open>1.5 \<cdot> 10^8\<close>, widths at most \<open>2^15\<close> and multiplications, divisions and
  remainders of width at most \<open>2^11\<close>, and \<open>distinct\<close> of bit-vectors with at most 10 arguments; the benchmarks of Kov\'asznai, Fr\"ohlich and Biere
  (\<^url>\<open>https://fmv.jku.at/smtbench\<close>) have widths at most \<open>29980\<close>.\<close>
definition smt_in_range :: \<open>SmtProblem \<Rightarrow> bool\<close> where
  \<open>smt_in_range p \<equiv>
     smt_size p \<le> 2 ^ 28 \<and> smt_max_width p \<le> 2 ^ 20 \<and> smt_max_mul_width p \<le> 2 ^ 12 \<and>
     smt_max_bv_distinct p \<le> 2 ^ 8\<close>

subsection \<open>The contract\<close>

context QFBV_ctx
begin

definition check_sat_contract :: \<open>SmtProblem \<Rightarrow> ('s, SmtAnswer, 'abort) function_contract\<close> where
  \<open>check_sat_contract p \<equiv>
     let pre = can_alloc_reference \<star> \<langle>smt_wf p \<and> smt_repr_ok p\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>case r of
           SmtAnswer_Sat m \<Rightarrow> smt_is_model p m
         | SmtAnswer_Unsat \<Rightarrow> \<not> smt_satisfiable p
         | SmtAnswer_Unknown \<Rightarrow> \<not> smt_fragment p \<or> \<not> smt_in_range p\<rangle> in
     make_function_contract pre post\<close>

text \<open>\<^const>\<open>check_sat_contract\<close> \<open>p\<close>:
  \<^item> Precondition: \<open>p\<close> is well-sorted (\<^const>\<open>smt_wf\<close>), and every list in it has fewer than
    \<open>2^63\<close> elements (\<^const>\<open>smt_repr_ok\<close>, which holds for every value of a Rust program).
  \<^item> \<^verbatim>\<open>Sat(m)\<close>: \<open>m\<close> is a model of \<open>p\<close>. \<^verbatim>\<open>Unsat\<close>: \<open>p\<close> has no model. \<^verbatim>\<open>Unknown\<close>: \<open>p\<close> is not in
    the fragment of this solver, or not in its range (\<^const>\<open>smt_in_range\<close>). For a problem in
    the fragment and in the range the answer is \<^verbatim>\<open>Sat\<close> or \<^verbatim>\<open>Unsat\<close>.
  \<^item> No panic (the abort postcondition is false). The program
    logic does not model the exhaustion of memory or of the stack, so the contract says nothing
    about them.\<close>

end

subsection \<open>The statement over all instances with enough fuel\<close>

text \<open>The translation bounds every loop without an iteration bound and every recursion by the
  fuel \<^verbatim>\<open>urust_fuel\<close>, the last parameter of \<^locale>\<open>QFBV_ctx\<close>, and panics when it runs out.
  A statement that quantifies over the fuel is therefore made outside that locale. The
  assumptions of \<^locale>\<open>QFBV_ctx\<close> do not mention the fuel, so its instances that differ only in
  the fuel share their assumptions. The locale \<open>QFBV_heap\<close> has the parameters and assumptions of
  \<^locale>\<open>QFBV_ctx\<close> except the fuel (it repeats \<^verbatim>\<open>urust/QFBV_Locale.thy\<close> without its last
  line); each value of the fuel gives an instance of \<^locale>\<open>QFBV_ctx\<close> with the parameters of
  \<open>QFBV_heap\<close>.\<close>

locale QFBV_heap =
  reference reference_types
  + ref_1: reference_allocatable reference_types _ _ _ _ _ _ _ prism_1 \<comment> \<open>(Lit list) list\<close>
  + ref_2: reference_allocatable reference_types _ _ _ _ _ _ _ prism_2 \<comment> \<open>Lit list\<close>
  + ref_3: reference_allocatable reference_types _ _ _ _ _ _ _ prism_3 \<comment> \<open>64 word\<close>
  + ref_4: reference_allocatable reference_types _ _ _ _ _ _ _ prism_4 \<comment> \<open>Cnf\<close>
  + ref_5: reference_allocatable reference_types _ _ _ _ _ _ _ prism_5 \<comment> \<open>Lit\<close>
  + ref_6: reference_allocatable reference_types _ _ _ _ _ _ _ prism_6 \<comment> \<open>Lit option\<close>
  + ref_7: reference_allocatable reference_types _ _ _ _ _ _ _ prism_7 \<comment> \<open>bool\<close>
  + ref_8: reference_allocatable reference_types _ _ _ _ _ _ _ prism_8 \<comment> \<open>(bool option) list\<close>
  + ref_9: reference_allocatable reference_types _ _ _ _ _ _ _ prism_9 \<comment> \<open>bool list\<close>
  + ref_10: reference_allocatable reference_types _ _ _ _ _ _ _ prism_10 \<comment> \<open>(bool list) list\<close>
  + ref_11: reference_allocatable reference_types _ _ _ _ _ _ _ prism_11 \<comment> \<open>CoreTerm list\<close>
  + ref_12: reference_allocatable reference_types _ _ _ _ _ _ _ prism_12 \<comment> \<open>(64 word) list\<close>
  + ref_13: reference_allocatable reference_types _ _ _ _ _ _ _ prism_13 \<comment> \<open>Lower\<close>
  + ref_14: reference_allocatable reference_types _ _ _ _ _ _ _ prism_14 \<comment> \<open>Term list\<close>
  + ref_15: reference_allocatable reference_types _ _ _ _ _ _ _ prism_15 \<comment> \<open>Term\<close>
  + ref_16: reference_allocatable reference_types _ _ _ _ _ _ _ prism_16 \<comment> \<open>Tr\<close>
  + ref_17: reference_allocatable reference_types _ _ _ _ _ _ _ prism_17 \<comment> \<open>SmtInterp list\<close>
  for reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow> 'o prompt_output \<Rightarrow> unit\<close>
  and prism_1 :: \<open>('gv, (Lit list) list) prism\<close>
  and prism_2 :: \<open>('gv, Lit list) prism\<close>
  and prism_3 :: \<open>('gv, 64 word) prism\<close>
  and prism_4 :: \<open>('gv, Cnf) prism\<close>
  and prism_5 :: \<open>('gv, Lit) prism\<close>
  and prism_6 :: \<open>('gv, Lit option) prism\<close>
  and prism_7 :: \<open>('gv, bool) prism\<close>
  and prism_8 :: \<open>('gv, (bool option) list) prism\<close>
  and prism_9 :: \<open>('gv, bool list) prism\<close>
  and prism_10 :: \<open>('gv, (bool list) list) prism\<close>
  and prism_11 :: \<open>('gv, CoreTerm list) prism\<close>
  and prism_12 :: \<open>('gv, (64 word) list) prism\<close>
  and prism_13 :: \<open>('gv, Lower) prism\<close>
  and prism_14 :: \<open>('gv, Term list) prism\<close>
  and prism_15 :: \<open>('gv, Term) prism\<close>
  and prism_16 :: \<open>('gv, Tr) prism\<close>
  and prism_17 :: \<open>('gv, SmtInterp list) prism\<close>
begin

abbreviation check_sat :: \<open>nat \<Rightarrow> SmtProblem \<Rightarrow> ('s, SmtAnswer, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>check_sat fuel \<equiv>
     QFBV_ctx.check_sat update_raw_fun dereference_raw_fun reference_raw_fun
       prism_1 prism_2 prism_3 prism_4 prism_5 prism_6 prism_7 prism_8 prism_9
       prism_10 prism_11 prism_12 prism_13 prism_14 prism_15 prism_16 prism_17 fuel\<close>

abbreviation check_sat_contract :: \<open>SmtProblem \<Rightarrow> ('s, SmtAnswer, 'abort) function_contract\<close> where
  \<open>check_sat_contract \<equiv> QFBV_ctx.check_sat_contract can_alloc_reference\<close>

definition check_sat_correct where
  \<open>check_sat_correct \<Gamma> \<equiv>
     \<forall>p. smt_wf p \<and> smt_repr_ok p \<longrightarrow> (\<exists>N. \<forall>fuel \<ge> N. \<Gamma>; check_sat fuel p \<Turnstile>\<^sub>F check_sat_contract p)\<close>

text \<open>\<^const>\<open>check_sat_correct\<close> \<open>\<Gamma>\<close> is the top-level statement: for every problem that satisfies the
  precondition of \<^const>\<open>QFBV_ctx.check_sat_contract\<close> there is a bound \<open>N\<close> such that, with any
  fuel at least \<open>N\<close>, \<^verbatim>\<open>check_sat\<close> satisfies the contract. \<^verbatim>\<open>QFBV_Top\<close> proves it as the theorem
  \<open>check_sat_correct\<close>.\<close>


end

end
