theory QFBV_Rvec
  imports "QFBV_Spec.QFBV_Spec"
begin

section \<open>Vectors\<close>

text \<open>
  The translation represents a \<^verbatim>\<open>Vec\<close> as an \<^typ>\<open>'a rvec\<close> (AutoCorrode's
  \<^verbatim>\<open>StdLib_Vec\<close>): the elements, a capacity and the layout of the elements. \<^verbatim>\<open>push\<close> and
  \<^verbatim>\<open>vec![x; n]\<close> panic when the capacity would exceed \<^const>\<open>rvec_cap_max\<close> of the layout, and
  the capacity after a growth or a clone is unspecified. The proofs therefore state facts about
  the elements and keep every vector the solver grows within \<open>vok\<close>: well-formed, and of
  a layout whose largest capacity is at least \<open>2^57\<close> (every element type of the solver is at most
  64 bytes). A \<^verbatim>\<open>push\<close> onto such a vector of fewer than \<open>2^56\<close> elements does not panic.
\<close>

definition vok :: \<open>'a rvec \<Rightarrow> bool\<close> where
  \<open>vok v \<equiv> rvec_wf v \<and> 2 ^ 57 \<le> rvec_cap_max (rvec_layout v)\<close>

text \<open>The largest capacity of a layout of a sized element, by evaluation.\<close>
lemma rvec_cap_max_layout [simp]:
  \<open>rvec_cap_max (make_elem_layout s a) =
     (if s = 0 then 2 ^ 64 - 1 else (2 ^ 63 - 1 - (a - 1)) div s)\<close>
  by (simp add: rvec_cap_max_def usize_max_def isize_max_def)

lemma vok_new [simp]: \<open>2 ^ 57 \<le> rvec_cap_max l \<Longrightarrow> vok (rvec_new_val l)\<close>
  by (simp add: vok_def rvec_new_val_wf)

lemma vok_length: \<open>vok v \<Longrightarrow> rvec_length v < 2 ^ 64\<close>
  using rvec_wf_length_bound(1)[of v] by (simp add: vok_def)

lemma vok_len_unat: \<open>vok v \<Longrightarrow> unat (of_nat (rvec_length v) :: 64 word) = rvec_length v\<close>
  by (simp add: vok_def rvec_len_unat)

subsection \<open>\<^verbatim>\<open>push\<close>\<close>

lemma push_not_None:
  assumes \<open>vok v\<close> \<open>rvec_length v < 2 ^ 56\<close>
  shows \<open>rvec_append_val v [x] \<noteq> None\<close>
proof -
  have wf: \<open>rvec_wf v\<close> and cm: \<open>2 ^ 57 \<le> rvec_cap_max (rvec_layout v)\<close> using assms(1) by (simp_all add: vok_def)
  have le: \<open>rvec_length v \<le> rvec_cap v\<close> using wf by (simp add: rvec_wf_def)
  have \<open>rvec_reserve_val v 1 \<noteq> None\<close>
  proof (rule rvec_reserve_val_not_None[OF wf])
    show \<open>rvec_length v + 1 \<le> rvec_cap v \<or>
        max (2 * rvec_cap v) (max (rvec_length v + 1) (rvec_min_non_zero_cap (rvec_layout v)))
          \<le> rvec_cap_max (rvec_layout v)\<close>
    proof (cases \<open>rvec_length v + 1 \<le> rvec_cap v\<close>)
      case False
      then have \<open>rvec_cap v = rvec_length v\<close> using le by simp
      moreover have \<open>rvec_min_non_zero_cap (rvec_layout v) \<le> 8\<close> by (simp add: rvec_min_non_zero_cap_def)
      ultimately show ?thesis using assms(2) cm by simp
    qed simp
  qed
  then show ?thesis by (simp add: rvec_append_val_def)
qed

lemma push_Some:
  assumes \<open>vok v\<close> \<open>rvec_length v < 2 ^ 56\<close>
  obtains w where \<open>rvec_append_val v [x] = Some w\<close> \<open>vok w\<close> \<open>rvec_elems w = rvec_elems v @ [x]\<close>
    \<open>rvec_layout w = rvec_layout v\<close>
proof -
  obtain w where w: \<open>rvec_append_val v [x] = Some w\<close> using push_not_None[OF assms] by blast
  note S = rvec_append_val_Some[OF w conjunct1[OF assms(1)[unfolded vok_def]]]
  show ?thesis using that[OF w] S assms(1) by (simp add: vok_def)
qed

text \<open>The condition of the contract of \<^verbatim>\<open>push\<close>, as the automation states it.\<close>
lemma push_ex [simp]:
  assumes \<open>vok v\<close> \<open>rvec_length v < 2 ^ 56\<close>
  shows \<open>\<exists>y. rvec_append_val v [x] = Some y\<close>
  using push_not_None[OF assms, of x] by blast

text \<open>The value after a \<^verbatim>\<open>push\<close>, as the contract of \<^verbatim>\<open>push\<close> states it.\<close>
lemma push_the [simp]:
  assumes \<open>vok v\<close> \<open>rvec_length v < 2 ^ 56\<close>
  shows \<open>rvec_elems (the (rvec_append_val v [x])) = rvec_elems v @ [x]\<close>
    and \<open>vok (the (rvec_append_val v [x]))\<close>
    and \<open>rvec_layout (the (rvec_append_val v [x])) = rvec_layout v\<close>
  by (rule push_Some[OF assms, of x]; simp)+

subsection \<open>\<^verbatim>\<open>vec![x; n]\<close>, \<^verbatim>\<open>clone\<close>\<close>

lemma from_elem_Some:
  assumes \<open>rvec_from_elem_val l x n = Some r\<close> \<open>2 ^ 57 \<le> rvec_cap_max l\<close>
  shows \<open>vok r\<close> \<open>rvec_elems r = replicate n x\<close> \<open>rvec_layout r = l\<close>
  using rvec_from_elem_val_Some[OF assms(1)] assms(2) by (simp_all add: vok_def)

lemma clone_elems [simp]: \<open>rvec_elems (rvec_clone_val v) = rvec_elems v\<close>
  by (simp add: rvec_clone_val_def)

lemma clone_vok [simp]: \<open>vok v \<Longrightarrow> vok (rvec_clone_val v)\<close>
  by (simp add: vok_def rvec_clone_val)

end
