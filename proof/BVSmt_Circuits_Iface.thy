theory BVSmt_Circuits_Iface
  imports BVSmt_Defs
begin

text \<open>
  The facts about the circuits that the proofs about \<^const>\<open>blast_m\<close> and \<^const>\<open>encode_m\<close> use.
  They are stated here without proof so that both can be worked on at the same time;
  \<^verbatim>\<open>BVSmt_Circuits\<close> proves exactly these statements. Once it does, \<^verbatim>\<open>BVSmt_Encode\<close> imports
  \<^verbatim>\<open>BVSmt_Circuits\<close> instead of this theory.
\<close>

lemma ext_refl: \<open>ext s s\<close>
  sorry

lemma ext_trans: \<open>ext s1 s2 \<Longrightarrow> ext s2 s3 \<Longrightarrow> ext s1 s3\<close>
  sorry

text \<open>A state's clauses include those of every state it extends.\<close>
lemma ext_cnf_sem: \<open>ext s s' \<Longrightarrow> cnf_sem \<sigma> (snd s') \<Longrightarrow> cnf_sem \<sigma> (snd s)\<close>
  sorry

lemma lits_lt_mono: \<open>lits_lt n a \<Longrightarrow> n \<le> m \<Longrightarrow> lits_lt m a\<close>
  sorry

lemma val_lt: \<open>val \<sigma> a < 2 ^ length a\<close>
  sorry

lemma const_correct:
  assumes \<open>wf_st s\<close>
  shows \<open>lits_lt (fst s) (const_m bs) \<and> length (const_m bs) = length bs \<and>
         (\<forall>\<sigma>. cnf_sem \<sigma> (snd s) \<longrightarrow> val \<sigma> (const_m bs) = bits_nat bs)\<close>
  sorry

lemma not_correct:
  shows \<open>(lits_lt n a \<longrightarrow> lits_lt n (not_m a)) \<and> length (not_m a) = length a \<and>
         val \<sigma> (not_m a) = 2 ^ length a - 1 - val \<sigma> a\<close>
  sorry

lemma extract_correct:
  assumes \<open>lo \<le> hi\<close> \<open>hi < length a\<close>
  shows \<open>(lits_lt n a \<longrightarrow> lits_lt n (extract_m a hi lo)) \<and>
         length (extract_m a hi lo) = hi - lo + 1 \<and>
         val \<sigma> (extract_m a hi lo) = (val \<sigma> a div 2 ^ lo) mod 2 ^ (hi - lo + 1)\<close>
  sorry

lemma ite_vec_correct:
  assumes \<open>wf_st s\<close> \<open>lits_lt (fst s) [c]\<close> \<open>lits_lt (fst s) a\<close> \<open>lits_lt (fst s) b\<close>
    \<open>length a = length b\<close> \<open>ite_vec_m s c a b = (s', r)\<close> \<open>fst s' < 2 ^ 64\<close>
  shows \<open>wf_st s' \<and> ext s s' \<and> lits_lt (fst s') r \<and> length r = length a \<and>
         (\<forall>\<sigma>. cnf_sem \<sigma> (snd s') \<longrightarrow> val \<sigma> r = (if lit_sem \<sigma> c then val \<sigma> a else val \<sigma> b))\<close>
  sorry

lemma blast_bin_correct:
  assumes \<open>wf_st s\<close> \<open>lits_lt (fst s) a\<close> \<open>lits_lt (fst s) b\<close>
    \<open>op \<noteq> BinOp_Concat \<longrightarrow> length a = length b\<close>
    \<open>blast_bin_m s op a b = (s', r)\<close> \<open>fst s' < 2 ^ 64\<close>
  shows \<open>wf_st s' \<and> ext s s' \<and> lits_lt (fst s') r \<and> length r = bin_width op (length a) (length b) \<and>
         (\<forall>\<sigma>. cnf_sem \<sigma> (snd s') \<longrightarrow>
            val \<sigma> r = bin_sem op (length a) (val \<sigma> a) (length b) (val \<sigma> b))\<close>
  sorry

text \<open>Fresh variables can take any values.\<close>
lemma fresh_vec_correct:
  assumes \<open>wf_st s\<close> \<open>fresh_vec_m s w = (s', r)\<close> \<open>fst s' < 2 ^ 64\<close>
  shows \<open>wf_st s' \<and> ext s s' \<and> lits_lt (fst s') r \<and> length r = w \<and>
         (\<forall>\<sigma> bs. cnf_sem \<sigma> (snd s) \<longrightarrow> length bs = w \<longrightarrow>
            (\<exists>\<sigma>'. (\<forall>v < fst s. \<sigma>' v = \<sigma> v) \<and> cnf_sem \<sigma>' (snd s') \<and> map (lit_sem \<sigma>') r = bs))\<close>
  sorry

end
