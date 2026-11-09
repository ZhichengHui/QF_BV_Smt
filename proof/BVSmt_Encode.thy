theory BVSmt_Encode
  imports BVSmt_Circuits
begin

text \<open>The proofs below were written against the statements of \<^verbatim>\<open>BVSmt_Circuits\<close> alone;
  its simplification rules change the shape of their goals, so they are not used here.\<close>
declare lits_lt_Nil lits_lt_Cons lits_lt_append Lit_var_lconst Lit_neg_lconst Lit_var_lneg
   Lit_neg_lneg lit_sem_lneg cnf_sem_Nil cnf_sem_Cons cnf_sem_append unat_won val_Nil
   bits_nat_replicate_False and_fst xor_fst ite_fst or_fst bitw_fst add_step_fst eq_step_fst
   fresh_vec_fst [simp del]

section \<open>Correctness of the encoding\<close>

subsection \<open>The number of variables only grows\<close>

lemma foldl_le_gen:
  fixes g :: \<open>'a \<Rightarrow> nat\<close>
  shows \<open>(\<And>x i. g x \<le> g (f x i)) \<Longrightarrow> n \<le> g x \<Longrightarrow> n \<le> g (foldl f x xs)\<close>
proof (induction xs arbitrary: x)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have h: \<open>n \<le> g (f x a)\<close> using Cons.prems(2) Cons.prems(1)[of x a] by (rule order_trans)
  show ?case using Cons.IH[OF Cons.prems(1) h] by simp
qed

lemmas foldl_le = foldl_le_gen[where g = \<open>\<lambda>x. fst (fst x)\<close>]
lemmas foldl_le' = foldl_le_gen[where g = \<open>fst\<close>]

lemma addc_m_simps [simp]:
  \<open>fst (addc_m s c) = fst s\<close> \<open>snd (addc_m s c) = snd s @ [c]\<close>
  by (simp_all add: addc_m_def)

lemma and_m_mono: \<open>n \<le> fst s \<Longrightarrow> n \<le> fst (fst (and_m s a b))\<close>
  by (simp add: and_m_def fresh_m_def split_def Let_def)

lemma xor_m_mono: \<open>n \<le> fst s \<Longrightarrow> n \<le> fst (fst (xor_m s a b))\<close>
  by (simp add: xor_m_def fresh_m_def split_def Let_def)

lemma ite_m_mono: \<open>n \<le> fst s \<Longrightarrow> n \<le> fst (fst (ite_m s c a b))\<close>
  by (simp add: ite_m_def fresh_m_def split_def Let_def)

lemma or_m_mono: \<open>n \<le> fst s \<Longrightarrow> n \<le> fst (fst (or_m s a b))\<close>
  by (simp add: or_m_def split_def Let_def and_m_mono)

lemma bitw_m_mono: \<open>n \<le> fst s \<Longrightarrow> n \<le> fst (fst (bitw_m op s a b))\<close>
  by (cases op) (simp_all add: bitw_m_def and_m_mono or_m_mono xor_m_mono)

lemma fresh_vec_m_mono: \<open>n \<le> fst s \<Longrightarrow> n \<le> fst (fst (fresh_vec_m s w))\<close>
  by (simp add: fresh_vec_m_def)

lemma bitwise_m_mono: \<open>n \<le> fst s \<Longrightarrow> n \<le> fst (fst (bitwise_m op s a b))\<close>
  unfolding bitwise_m_def
  by (rule foldl_le) (simp_all add: split_def Let_def bitw_m_mono)

lemma add_step_mono: \<open>n \<le> fst (fst x) \<Longrightarrow> n \<le> fst (fst (add_step a b x i))\<close>
  by (simp add: add_step_def split_def Let_def xor_m_mono ite_m_mono)

lemma add_m_mono_le: \<open>n \<le> fst s \<Longrightarrow> n \<le> fst (fst (add_m s a b c))\<close>
  unfolding add_m_def
  by (rule foldl_le) (simp_all add: add_step_mono)

lemma partial_m_mono_le: \<open>n \<le> fst s \<Longrightarrow> n \<le> fst (fst (partial_m s a bi i))\<close>
  unfolding partial_m_def
  by (rule foldl_le) (simp_all add: split_def Let_def and_m_mono split: if_split)

lemma mul_step_mono: \<open>n \<le> fst (fst x) \<Longrightarrow> n \<le> fst (fst (mul_step a b x i))\<close>
  by (simp add: mul_step_def split_def Let_def partial_m_mono_le add_m_mono_le)

lemma mul_m_mono_le: \<open>n \<le> fst s \<Longrightarrow> n \<le> fst (fst (mul_m s a b))\<close>
  unfolding mul_m_def
  by (rule foldl_le) (simp_all add: mul_step_mono)

lemma eq_step_mono: \<open>n \<le> fst (fst x) \<Longrightarrow> n \<le> fst (fst (eq_step a b x i))\<close>
  by (simp add: eq_step_def split_def Let_def xor_m_mono and_m_mono)

lemma eq_m_mono_le: \<open>n \<le> fst s \<Longrightarrow> n \<le> fst (fst (eq_m s a b))\<close>
  unfolding eq_m_def
  by (rule foldl_le) (simp_all add: eq_step_mono)

lemma ult_m_mono_le: \<open>n \<le> fst s \<Longrightarrow> n \<le> fst (fst (ult_m s a b))\<close>
  by (simp add: ult_m_def split_def Let_def add_m_mono_le)

lemma ite_vec_m_mono_le: \<open>n \<le> fst s \<Longrightarrow> n \<le> fst (fst (ite_vec_m s c a b))\<close>
  unfolding ite_vec_m_def
  by (rule foldl_le) (simp_all add: split_def Let_def ite_m_mono)

lemma shift_step_mono: \<open>n \<le> fst (fst x) \<Longrightarrow> n \<le> fst (fst (shift_step a b left x k))\<close>
  by (simp add: shift_step_def split_def Let_def eq_m_mono_le ite_vec_m_mono_le)

lemma shift_m_mono: \<open>n \<le> fst s \<Longrightarrow> n \<le> fst (fst (shift_m s a b left))\<close>
  unfolding shift_m_def
  by (rule foldl_le) (simp_all add: shift_step_mono)

lemma divrem_m_mono: \<open>n \<le> fst s \<Longrightarrow> n \<le> fst (fst (divrem_m s a b))\<close>
proof -
  assume n0: \<open>n \<le> fst s\<close>
  define w where \<open>w = length a\<close>
  obtain s1 q1 where 1: \<open>fresh_vec_m s w = (s1, q1)\<close> by (cases \<open>fresh_vec_m s w\<close>)
  obtain s2 r1 where 2: \<open>fresh_vec_m s1 w = (s2, r1)\<close> by (cases \<open>fresh_vec_m s1 w\<close>)
  obtain s3 bz where 3: \<open>eq_m s2 b (replicate w (lconst False)) = (s3, bz)\<close>
    by (cases \<open>eq_m s2 b (replicate w (lconst False))\<close>)
  obtain s4 qo where 4: \<open>eq_m s3 q1 (replicate w (lconst True)) = (s4, qo)\<close>
    by (cases \<open>eq_m s3 q1 (replicate w (lconst True))\<close>)
  obtain s5 ra where 5: \<open>eq_m s4 r1 a = (s5, ra)\<close> by (cases \<open>eq_m s4 r1 a\<close>)
  obtain s6 cz where 6: \<open>and_m s5 qo ra = (s6, cz)\<close> by (cases \<open>and_m s5 qo ra\<close>)
  obtain s7 pr where 7: \<open>mul_m s6 (zext_m q1 (w + w)) (zext_m b (w + w)) = (s7, pr)\<close>
    by (cases \<open>mul_m s6 (zext_m q1 (w + w)) (zext_m b (w + w))\<close>)
  obtain s8 sm c where 8: \<open>add_m s7 pr (zext_m r1 (w + w)) (lconst False) = (s8, sm, c)\<close>
    by (metis prod_cases3)
  obtain s9 sa where 9: \<open>eq_m s8 sm (zext_m a (w + w)) = (s9, sa)\<close> by (cases \<open>eq_m s8 sm (zext_m a (w + w))\<close>)
  obtain s10 rl where 10: \<open>ult_m s9 r1 b = (s10, rl)\<close> by (cases \<open>ult_m s9 r1 b\<close>)
  obtain s11 cn where 11: \<open>and_m s10 sa rl = (s11, cn)\<close> by (cases \<open>and_m s10 sa rl\<close>)
  obtain s12 ok where 12: \<open>ite_m s11 bz cz cn = (s12, ok)\<close> by (cases \<open>ite_m s11 bz cz cn\<close>)
  have n1: \<open>n \<le> fst s1\<close> using fresh_vec_m_mono[OF n0, of w] 1 by simp
  have n2: \<open>n \<le> fst s2\<close> using fresh_vec_m_mono[OF n1, of w] 2 by simp
  have n3: \<open>n \<le> fst s3\<close> using eq_m_mono_le[OF n2, of b \<open>replicate w (lconst False)\<close>] 3 by simp
  have n4: \<open>n \<le> fst s4\<close> using eq_m_mono_le[OF n3, of q1 \<open>replicate w (lconst True)\<close>] 4 by simp
  have n5: \<open>n \<le> fst s5\<close> using eq_m_mono_le[OF n4, of r1 a] 5 by simp
  have n6: \<open>n \<le> fst s6\<close> using and_m_mono[OF n5, of qo ra] 6 by simp
  have n7: \<open>n \<le> fst s7\<close> using mul_m_mono_le[OF n6, of \<open>zext_m q1 (w + w)\<close> \<open>zext_m b (w + w)\<close>] 7 by simp
  have n8: \<open>n \<le> fst s8\<close>
    using add_m_mono_le[OF n7, of pr \<open>zext_m r1 (w + w)\<close> \<open>lconst False\<close>] 8 by simp
  have n9: \<open>n \<le> fst s9\<close> using eq_m_mono_le[OF n8, of sm \<open>zext_m a (w + w)\<close>] 9 by simp
  have n10: \<open>n \<le> fst s10\<close> using ult_m_mono_le[OF n9, of r1 b] 10 by simp
  have n11: \<open>n \<le> fst s11\<close> using and_m_mono[OF n10, of sa rl] 11 by simp
  have n12: \<open>n \<le> fst s12\<close> using ite_m_mono[OF n11, of bz cz cn] 12 by simp
  have \<open>fst (fst (divrem_m s a b)) = fst s12\<close>
    using 1 2 3 4 5 6 7 8 9 10 11 12 by (simp add: divrem_m_def w_def[symmetric] Let_def)
  then show ?thesis using n12 by simp
qed

lemma blast_bin_m_mono: \<open>n \<le> fst s \<Longrightarrow> n \<le> fst (fst (blast_bin_m s op a b))\<close>
  by (cases op) (simp_all add: blast_bin_m_def split_def Let_def bitwise_m_mono add_m_mono_le
      mul_m_mono_le divrem_m_mono shift_m_mono eq_m_mono_le ult_m_mono_le)

lemma blast_m_mono: \<open>n \<le> fst s \<Longrightarrow> n \<le> fst (fst (blast_m vs dl s t))\<close>
  by (induction t arbitrary: n s) (simp_all add: split_def Let_def blast_bin_m_mono ite_vec_m_mono_le)

subsection \<open>Auxiliary facts\<close>

definition env_ok :: \<open>nat \<Rightarrow> nat list \<Rightarrow> Lit list list \<Rightarrow> bool\<close> where
  \<open>env_ok n ws vs \<equiv> length vs = length ws \<and> (\<forall>i < length ws. length (vs ! i) = ws ! i) \<and>
     (\<forall>ls \<in> set vs. lits_lt n ls)\<close>

lemma env_ok_mono: \<open>env_ok n ws vs \<Longrightarrow> n \<le> m \<Longrightarrow> env_ok m ws vs\<close>
  unfolding env_ok_def using lits_lt_mono by blast

lemma env_ok_snoc: \<open>env_ok n ws vs \<Longrightarrow> lits_lt n l \<Longrightarrow> env_ok n (ws @ [length l]) (vs @ [l])\<close>
  unfolding env_ok_def by (auto simp: nth_append less_Suc_eq)

lemma val_single_enc: \<open>length l = 1 \<Longrightarrow> val \<sigma> l = (if lit_sem \<sigma> (l ! 0) then 1 else 0)\<close>
  by (cases l) (auto simp: val_def)

lemma map_lit_agree:
  \<open>lits_lt n l \<Longrightarrow> \<forall>v < n. \<sigma>' v = \<sigma> v \<Longrightarrow> map (lit_sem \<sigma>') l = map (lit_sem \<sigma>) l\<close>
  by (rule map_cong) (auto simp: lits_lt_def lit_sem_def)

lemma val_agree_enc: \<open>lits_lt n l \<Longrightarrow> \<forall>v < n. \<sigma>' v = \<sigma> v \<Longrightarrow> val \<sigma>' l = val \<sigma> l\<close>
  unfolding val_def using map_lit_agree by metis

lemma map_val_agree:
  \<open>\<forall>l \<in> set L. lits_lt n l \<Longrightarrow> \<forall>v < n. \<sigma>' v = \<sigma> v \<Longrightarrow> map (val \<sigma>') L = map (val \<sigma>) L\<close>
  by (rule map_cong) (auto intro: val_agree_enc)

lemma map_map_lit_agree:
  \<open>\<forall>l \<in> set L. lits_lt n l \<Longrightarrow> \<forall>v < n. \<sigma>' v = \<sigma> v \<Longrightarrow>
   map (map (lit_sem \<sigma>')) L = map (map (lit_sem \<sigma>)) L\<close>
  apply (rule map_cong[OF refl])
  using map_lit_agree by blast

lemma map_val_bits: \<open>map (val \<sigma>) L = map bits_nat (map (map (lit_sem \<sigma>)) L)\<close>
  by (simp add: val_def)

lemma cnf_sem_append_enc: \<open>cnf_sem \<sigma> (a @ b) = (cnf_sem \<sigma> a \<and> cnf_sem \<sigma> b)\<close>
  by (auto simp: cnf_sem_def)

lemma cnf_sem_unit: \<open>cnf_sem \<sigma> [[x]] = lit_sem \<sigma> x\<close>
  by (simp add: cnf_sem_def)

lemma wf_addc: \<open>wf_st s \<Longrightarrow> lits_lt (fst s) c \<Longrightarrow> wf_st (addc_m s c)\<close>
  by (auto simp: wf_st_def)

lemma wf_init: \<open>wf_st init_st\<close>
  by (auto simp: wf_st_def init_st_def lits_lt_def lconst_def)

lemma sat_init: \<open>cnf_sem (\<lambda>_. True) (snd init_st)\<close>
  by (simp add: init_st_def cnf_sem_def lit_sem_def lconst_def)

subsection \<open>Definitions\<close>

lemma def_widths_snoc:
  \<open>def_widths ws ds (xs @ [x]) = def_widths ws ds xs @ [width ws (def_widths ws ds xs) x]\<close>
  by (induction xs arbitrary: ds) auto

lemma def_values_snoc:
  \<open>def_values ws ds vs dv (xs @ [x]) =
   def_values ws ds vs dv xs @ [eval ws (def_widths ws ds xs) vs (def_values ws ds vs dv xs) x]\<close>
  by (induction xs arbitrary: ds dv) auto

lemma defs_wt_append:
  \<open>defs_wt ws ds (xs @ ys) = (defs_wt ws ds xs \<and> defs_wt ws (def_widths ws ds xs) ys)\<close>
  by (induction xs arbitrary: ds) auto

lemma defs_wt_nth:
  assumes \<open>defs_wt ws [] D\<close> \<open>k < length D\<close>
  shows \<open>wt ws (def_widths ws [] (take k D)) (D ! k)\<close>
proof -
  have \<open>defs_wt ws [] (take k D @ drop k D)\<close> using assms(1) by simp
  then have \<open>defs_wt ws (def_widths ws [] (take k D)) (drop k D)\<close>
    by (simp only: defs_wt_append)
  then show ?thesis by (simp add: Cons_nth_drop_Suc[OF assms(2), symmetric])
qed

subsection \<open>Bit-blasting a term\<close>

lemma blast_correct:
  \<open>wt ws ds t \<Longrightarrow> wf_st s \<Longrightarrow> env_ok (fst s) ws vs \<Longrightarrow> env_ok (fst s) ds dl \<Longrightarrow>
   blast_m vs dl s t = (s', ls) \<Longrightarrow> fst s' < 2 ^ 64 \<Longrightarrow>
   wf_st s' \<and> ext s s' \<and> lits_lt (fst s') ls \<and> length ls = width ws ds t \<and>
   (\<forall>\<sigma>. cnf_sem \<sigma> (snd s') \<longrightarrow> val \<sigma> ls = eval ws ds (map (val \<sigma>) vs) (map (val \<sigma>) dl) t)\<close>
proof (induction t arbitrary: s s' ls)
  case (Term_Const bs)
  then show ?case using const_correct[of s bs] by (auto simp: ext_refl)
next
  case (Term_Var i)
  then show ?case using nth_mem[of \<open>unat i\<close> vs] by (auto simp: env_ok_def ext_refl)
next
  case (Term_Ref i)
  then show ?case using nth_mem[of \<open>unat i\<close> dl] by (auto simp: env_ok_def ext_refl)
next
  case (Term_Not a)
  obtain s1 la where A: \<open>blast_m vs dl s a = (s1, la)\<close> by (cases \<open>blast_m vs dl s a\<close>)
  have E: \<open>s' = s1\<close> \<open>ls = not_m la\<close> using Term_Not.prems(5) A by auto
  have wa: \<open>wt ws ds a\<close> using Term_Not.prems(1) by simp
  have b1: \<open>fst s1 < 2 ^ 64\<close> using Term_Not.prems(6) E by simp
  note IA = Term_Not.IH[OF wa Term_Not.prems(2-4) A b1]
  show ?case using IA not_correct[of \<open>fst s1\<close> la] by (auto simp: E)
next
  case (Term_Bin op a b)
  obtain s1 la where A: \<open>blast_m vs dl s a = (s1, la)\<close> by (cases \<open>blast_m vs dl s a\<close>)
  obtain s2 lb where B: \<open>blast_m vs dl s1 b = (s2, lb)\<close> by (cases \<open>blast_m vs dl s1 b\<close>)
  have C: \<open>blast_bin_m s2 op la lb = (s', ls)\<close> using Term_Bin.prems(5) A B by simp
  have le2: \<open>fst s2 \<le> fst s'\<close> using blast_bin_m_mono[of \<open>fst s2\<close> s2 op la lb] C by simp
  have le1: \<open>fst s1 \<le> fst s2\<close> using blast_m_mono[of \<open>fst s1\<close> s1 vs dl b] B by simp
  have wa: \<open>wt ws ds a\<close> and wb: \<open>wt ws ds b\<close>
    and weq: \<open>op \<noteq> BinOp_Concat \<longrightarrow> width ws ds a = width ws ds b\<close>
    using Term_Bin.prems(1) by simp_all
  have b1: \<open>fst s1 < 2 ^ 64\<close> and b2: \<open>fst s2 < 2 ^ 64\<close>
    using le1 le2 Term_Bin.prems(6) by linarith+
  note IA = Term_Bin.IH(1)[OF wa Term_Bin.prems(2-4) A b1]
  have e1: \<open>ext s s1\<close> and wf1: \<open>wf_st s1\<close> using IA by simp_all
  have env1: \<open>env_ok (fst s1) ws vs\<close> \<open>env_ok (fst s1) ds dl\<close>
    using Term_Bin.prems(3,4) ext_fst[OF e1] env_ok_mono by blast+
  note IB = Term_Bin.IH(2)[OF wb wf1 env1 B b2]
  have e2: \<open>ext s1 s2\<close> and wf2: \<open>wf_st s2\<close> using IB by simp_all
  have la2: \<open>lits_lt (fst s2) la\<close> using IA le1 lits_lt_mono by blast
  have lb2: \<open>lits_lt (fst s2) lb\<close> using IB by simp
  have len: \<open>op \<noteq> BinOp_Concat \<longrightarrow> length la = length lb\<close> using IA IB weq by simp
  note BB = blast_bin_correct[OF wf2 la2 lb2 len C Term_Bin.prems(6)]
  have e3: \<open>ext s2 s'\<close> using BB by simp
  show ?case
  proof (intro conjI allI impI)
    show \<open>wf_st s'\<close> \<open>lits_lt (fst s') ls\<close> using BB by simp_all
    show \<open>ext s s'\<close> using ext_trans[OF ext_trans[OF e1 e2] e3] .
    show \<open>length ls = width ws ds (Term_Bin op a b)\<close>
      using BB IA IB by (simp add: bin_width_def)
  next
    fix \<sigma> assume S: \<open>cnf_sem \<sigma> (snd s')\<close>
    have S2: \<open>cnf_sem \<sigma> (snd s2)\<close> using ext_cnf_sem[OF e3 S] .
    have S1: \<open>cnf_sem \<sigma> (snd s1)\<close> using ext_cnf_sem[OF e2 S2] .
    show \<open>val \<sigma> ls = eval ws ds (map (val \<sigma>) vs) (map (val \<sigma>) dl) (Term_Bin op a b)\<close>
      using BB IA IB S S1 S2 by simp
  qed
next
  case (Term_Extract hi lo a)
  obtain s1 la where A: \<open>blast_m vs dl s a = (s1, la)\<close> by (cases \<open>blast_m vs dl s a\<close>)
  have E: \<open>s' = s1\<close> \<open>ls = extract_m la (unat hi) (unat lo)\<close> using Term_Extract.prems(5) A by auto
  have wa: \<open>wt ws ds a\<close> and lohi: \<open>unat lo \<le> unat hi\<close> and hiw: \<open>unat hi < width ws ds a\<close>
    using Term_Extract.prems(1) by simp_all
  have b1: \<open>fst s1 < 2 ^ 64\<close> using Term_Extract.prems(6) E by simp
  note IA = Term_Extract.IH[OF wa Term_Extract.prems(2-4) A b1]
  have hil: \<open>unat hi < length la\<close> using IA hiw by simp
  show ?case using IA extract_correct[OF lohi hil, where n = \<open>fst s1\<close>] by (auto simp: E)
next
  case (Term_Ite c a b)
  obtain s1 lc where A: \<open>blast_m vs dl s c = (s1, lc)\<close> by (cases \<open>blast_m vs dl s c\<close>)
  obtain s2 la where B: \<open>blast_m vs dl s1 a = (s2, la)\<close> by (cases \<open>blast_m vs dl s1 a\<close>)
  obtain s3 lb where C: \<open>blast_m vs dl s2 b = (s3, lb)\<close> by (cases \<open>blast_m vs dl s2 b\<close>)
  have D: \<open>ite_vec_m s3 (lc ! 0) la lb = (s', ls)\<close> using Term_Ite.prems(5) A B C by simp
  have le3: \<open>fst s3 \<le> fst s'\<close> using ite_vec_m_mono_le[of \<open>fst s3\<close> s3 \<open>lc ! 0\<close> la lb] D by simp
  have le2: \<open>fst s2 \<le> fst s3\<close> using blast_m_mono[of \<open>fst s2\<close> s2 vs dl b] C by simp
  have le1: \<open>fst s1 \<le> fst s2\<close> using blast_m_mono[of \<open>fst s1\<close> s1 vs dl a] B by simp
  have wc: \<open>wt ws ds c\<close> and wa: \<open>wt ws ds a\<close> and wb: \<open>wt ws ds b\<close>
    and wc1: \<open>width ws ds c = 1\<close> and wab: \<open>width ws ds a = width ws ds b\<close>
    using Term_Ite.prems(1) by simp_all
  have b1: \<open>fst s1 < 2 ^ 64\<close> and b2: \<open>fst s2 < 2 ^ 64\<close> and b3: \<open>fst s3 < 2 ^ 64\<close>
    using le1 le2 le3 Term_Ite.prems(6) by linarith+
  note IC = Term_Ite.IH(1)[OF wc Term_Ite.prems(2-4) A b1]
  have e1: \<open>ext s s1\<close> and wf1: \<open>wf_st s1\<close> using IC by simp_all
  have env1: \<open>env_ok (fst s1) ws vs\<close> \<open>env_ok (fst s1) ds dl\<close>
    using Term_Ite.prems(3,4) ext_fst[OF e1] env_ok_mono by blast+
  note IA = Term_Ite.IH(2)[OF wa wf1 env1 B b2]
  have e2: \<open>ext s1 s2\<close> and wf2: \<open>wf_st s2\<close> using IA by simp_all
  have env2: \<open>env_ok (fst s2) ws vs\<close> \<open>env_ok (fst s2) ds dl\<close>
    using env1 le1 env_ok_mono by blast+
  note IB = Term_Ite.IH(3)[OF wb wf2 env2 C b3]
  have e3: \<open>ext s2 s3\<close> and wf3: \<open>wf_st s3\<close> using IB by simp_all
  have lc1: \<open>length lc = 1\<close> using IC wc1 by simp
  have \<open>lc ! 0 \<in> set lc\<close> using lc1 by (auto intro!: nth_mem)
  then have lc3: \<open>lits_lt (fst s3) [lc ! 0]\<close>
    using IC le2 le3 le1 unfolding lits_lt_def by fastforce
  have la3: \<open>lits_lt (fst s3) la\<close> using IA le2 lits_lt_mono by blast
  have lb3: \<open>lits_lt (fst s3) lb\<close> using IB by simp
  have len: \<open>length la = length lb\<close> using IA IB wab by simp
  note IV = ite_vec_correct[OF wf3 lc3 la3 lb3 len D Term_Ite.prems(6)]
  have e4: \<open>ext s3 s'\<close> using IV by simp
  show ?case
  proof (intro conjI allI impI)
    show \<open>wf_st s'\<close> \<open>lits_lt (fst s') ls\<close> using IV by simp_all
    show \<open>ext s s'\<close> using ext_trans[OF ext_trans[OF ext_trans[OF e1 e2] e3] e4] .
    show \<open>length ls = width ws ds (Term_Ite c a b)\<close> using IV IA by simp
  next
    fix \<sigma> assume S: \<open>cnf_sem \<sigma> (snd s')\<close>
    have S3: \<open>cnf_sem \<sigma> (snd s3)\<close> using ext_cnf_sem[OF e4 S] .
    have S2: \<open>cnf_sem \<sigma> (snd s2)\<close> using ext_cnf_sem[OF e3 S3] .
    have S1: \<open>cnf_sem \<sigma> (snd s1)\<close> using ext_cnf_sem[OF e2 S2] .
    have vc: \<open>val \<sigma> lc = (if lit_sem \<sigma> (lc ! 0) then 1 else 0)\<close> using val_single_enc[OF lc1] .
    show \<open>val \<sigma> ls = eval ws ds (map (val \<sigma>) vs) (map (val \<sigma>) dl) (Term_Ite c a b)\<close>
      using IV IA IB IC S S1 S2 S3 vc by auto
  qed
qed

subsection \<open>The three loops of the encoding\<close>

lemma vars_inv:
  \<open>k \<le> length W \<Longrightarrow> foldl (vars_step W) (init_st, []) [0..<k] = (s, vs) \<Longrightarrow> fst s < 2 ^ 64 \<Longrightarrow>
   wf_st s \<and> length vs = k \<and> (\<forall>i < k. length (vs ! i) = unat (W ! i)) \<and>
   (\<forall>ls \<in> set vs. lits_lt (fst s) ls) \<and>
   (\<forall>m. length m = k \<longrightarrow> (\<forall>i < k. length (m ! i) = unat (W ! i)) \<longrightarrow>
      (\<exists>\<sigma>. cnf_sem \<sigma> (snd s) \<and> map (map (lit_sem \<sigma>)) vs = m))\<close>
proof (induction k arbitrary: s vs)
  case 0
  then have E: \<open>s = init_st\<close> \<open>vs = []\<close> by auto
  show ?case using wf_init sat_init by (auto simp: E)
next
  case (Suc k)
  obtain s0 vs0 where A: \<open>foldl (vars_step W) (init_st, []) [0..<k] = (s0, vs0)\<close>
    by (cases \<open>foldl (vars_step W) (init_st, []) [0..<k]\<close>)
  obtain s1 r where F: \<open>fresh_vec_m s0 (unat (W ! k)) = (s1, r)\<close>
    by (cases \<open>fresh_vec_m s0 (unat (W ! k))\<close>)
  have E: \<open>s = s1\<close> \<open>vs = vs0 @ [r]\<close> using Suc.prems(2) A F by (simp_all add: vars_step_def)
  have \<open>fst s1 = fst s0 + unat (W ! k)\<close> using F by (auto simp: fresh_vec_m_def)
  then have b0: \<open>fst s0 < 2 ^ 64\<close> using Suc.prems(3) E by simp
  have kl: \<open>k \<le> length W\<close> using Suc.prems(1) by simp
  note IH = Suc.IH[OF kl A b0]
  have wf0: \<open>wf_st s0\<close> using IH by simp
  have b1: \<open>fst s1 < 2 ^ 64\<close> using Suc.prems(3) E by simp
  note FV = fresh_vec_correct[OF wf0 F b1]
  have le: \<open>fst s0 \<le> fst s1\<close> using FV ext_fst by blast
  show ?case
  proof (intro conjI allI impI)
    show \<open>wf_st s\<close> using FV E by simp
    show \<open>length vs = Suc k\<close> using IH E by simp
    show \<open>length (vs ! i) = unat (W ! i)\<close> if \<open>i < Suc k\<close> for i
      using that IH FV E by (auto simp: nth_append less_Suc_eq)
    show \<open>\<forall>ls \<in> set vs. lits_lt (fst s) ls\<close>
      using IH FV E le lits_lt_mono by auto
  next
    fix m :: \<open>bool list list\<close> assume M: \<open>length m = Suc k\<close> \<open>\<forall>i < Suc k. length (m ! i) = unat (W ! i)\<close>
    have \<open>length (take k m) = k\<close> \<open>\<forall>i < k. length (take k m ! i) = unat (W ! i)\<close> using M by auto
    then obtain \<sigma> where S: \<open>cnf_sem \<sigma> (snd s0)\<close> \<open>map (map (lit_sem \<sigma>)) vs0 = take k m\<close>
      using IH by blast
    have \<open>length (m ! k) = unat (W ! k)\<close> using M by simp
    then obtain \<sigma>' where S': \<open>\<forall>v < fst s0. \<sigma>' v = \<sigma> v\<close> \<open>cnf_sem \<sigma>' (snd s1)\<close>
      \<open>map (lit_sem \<sigma>') r = m ! k\<close>
      using FV S(1) by blast
    have \<open>map (map (lit_sem \<sigma>')) vs0 = map (map (lit_sem \<sigma>)) vs0\<close>
      using map_map_lit_agree IH S'(1) by blast
    then have \<open>map (map (lit_sem \<sigma>')) vs = take k m @ [m ! k]\<close> using S(2) S'(3) E by simp
    also have \<open>\<dots> = m\<close> using M(1) take_Suc_conv_app_nth[of k m] by simp
    finally show \<open>\<exists>\<sigma>. cnf_sem \<sigma> (snd s) \<and> map (map (lit_sem \<sigma>)) vs = m\<close> using S'(2) E by blast
  qed
qed

lemma defs_inv:
  assumes \<open>wf_st s0\<close> \<open>env_ok (fst s0) ws vs\<close> \<open>defs_wt ws [] D\<close>
  shows \<open>k \<le> length D \<Longrightarrow> foldl (defs_step vs D) (s0, []) [0..<k] = (s, dl) \<Longrightarrow> fst s < 2 ^ 64 \<Longrightarrow>
   wf_st s \<and> ext s0 s \<and> env_ok (fst s) (def_widths ws [] (take k D)) dl \<and>
   (\<forall>\<sigma>. cnf_sem \<sigma> (snd s) \<longrightarrow> map (val \<sigma>) dl = def_values ws [] (map (val \<sigma>) vs) [] (take k D))\<close>
proof (induction k arbitrary: s dl)
  case 0
  then have E: \<open>s = s0\<close> \<open>dl = []\<close> by auto
  show ?case using assms(1) by (simp add: E ext_refl env_ok_def)
next
  case (Suc k)
  obtain sp dp where A: \<open>foldl (defs_step vs D) (s0, []) [0..<k] = (sp, dp)\<close>
    by (cases \<open>foldl (defs_step vs D) (s0, []) [0..<k]\<close>)
  obtain s1 ls where B: \<open>blast_m vs dp sp (D ! k) = (s1, ls)\<close>
    by (cases \<open>blast_m vs dp sp (D ! k)\<close>)
  have E: \<open>s = s1\<close> \<open>dl = dp @ [ls]\<close> using Suc.prems(2) A B by (simp_all add: defs_step_def)
  have le: \<open>fst sp \<le> fst s1\<close> using blast_m_mono[of \<open>fst sp\<close> sp vs dp \<open>D ! k\<close>] B by simp
  have bp: \<open>fst sp < 2 ^ 64\<close> using le Suc.prems(3) E by simp
  have kl: \<open>k < length D\<close> using Suc.prems(1) by simp
  note IH = Suc.IH[OF _ A bp]
  have IH': \<open>wf_st sp \<and> ext s0 sp \<and> env_ok (fst sp) (def_widths ws [] (take k D)) dp \<and>
   (\<forall>\<sigma>. cnf_sem \<sigma> (snd sp) \<longrightarrow> map (val \<sigma>) dp = def_values ws [] (map (val \<sigma>) vs) [] (take k D))\<close>
    using IH kl by simp
  have envv: \<open>env_ok (fst sp) ws vs\<close> using assms(2) IH' ext_fst env_ok_mono by blast
  have wtk: \<open>wt ws (def_widths ws [] (take k D)) (D ! k)\<close> using defs_wt_nth[OF assms(3) kl] .
  have b1: \<open>fst s1 < 2 ^ 64\<close> using Suc.prems(3) E by simp
  have wfp: \<open>wf_st sp\<close> and envd: \<open>env_ok (fst sp) (def_widths ws [] (take k D)) dp\<close>
    using IH' by simp_all
  note BC = blast_correct[OF wtk wfp envv envd B b1]
  have tk: \<open>take (Suc k) D = take k D @ [D ! k]\<close> using take_Suc_conv_app_nth[OF kl] .
  show ?case
  proof (intro conjI allI impI)
    show \<open>wf_st s\<close> using BC E by simp
    show \<open>ext s0 s\<close> using ext_trans IH' BC E by blast
    have \<open>env_ok (fst s1) (def_widths ws [] (take k D)) dp\<close>
      using envd le env_ok_mono by blast
    then have \<open>env_ok (fst s1) (def_widths ws [] (take k D) @ [length ls]) (dp @ [ls])\<close>
      using env_ok_snoc BC by blast
    then show \<open>env_ok (fst s) (def_widths ws [] (take (Suc k) D)) dl\<close>
      using BC by (simp add: E tk def_widths_snoc)
  next
    fix \<sigma> assume S: \<open>cnf_sem \<sigma> (snd s)\<close>
    have Sp: \<open>cnf_sem \<sigma> (snd sp)\<close> using ext_cnf_sem S BC E by blast
    show \<open>map (val \<sigma>) dl = def_values ws [] (map (val \<sigma>) vs) [] (take (Suc k) D)\<close>
      using BC IH' S Sp by (simp add: E tk def_values_snoc def_widths_snoc)
  qed
qed

lemma asserts_inv:
  assumes \<open>wf_st s0\<close> \<open>env_ok (fst s0) ws vs\<close> \<open>env_ok (fst s0) ds dl\<close>
    \<open>\<forall>t \<in> set A. wt ws ds t \<and> width ws ds t = 1\<close>
  shows \<open>k \<le> length A \<Longrightarrow> foldl (asserts_step vs dl A) s0 [0..<k] = s \<Longrightarrow> fst s < 2 ^ 64 \<Longrightarrow>
   wf_st s \<and> fst s0 \<le> fst s \<and> (\<forall>\<sigma>. cnf_sem \<sigma> (snd s) \<longrightarrow> cnf_sem \<sigma> (snd s0)) \<and>
   (\<forall>\<sigma>. cnf_sem \<sigma> (snd s) \<longrightarrow>
      (\<forall>j < k. eval ws ds (map (val \<sigma>) vs) (map (val \<sigma>) dl) (A ! j) = 1)) \<and>
   (\<forall>\<sigma>. cnf_sem \<sigma> (snd s0) \<longrightarrow>
      (\<forall>j < k. eval ws ds (map (val \<sigma>) vs) (map (val \<sigma>) dl) (A ! j) = 1) \<longrightarrow>
      (\<exists>\<sigma>'. (\<forall>v < fst s0. \<sigma>' v = \<sigma> v) \<and> cnf_sem \<sigma>' (snd s)))\<close>
proof (induction k arbitrary: s)
  case 0
  then have E: \<open>s = s0\<close> by auto
  show ?case using assms(1) by (auto simp: E)
next
  case (Suc k)
  define sp where \<open>sp = foldl (asserts_step vs dl A) s0 [0..<k]\<close>
  obtain s1 ls where B: \<open>blast_m vs dl sp (A ! k) = (s1, ls)\<close>
    by (cases \<open>blast_m vs dl sp (A ! k)\<close>)
  have E: \<open>s = addc_m s1 [ls ! 0]\<close> using Suc.prems(2) B by (simp add: asserts_step_def sp_def)
  have le: \<open>fst sp \<le> fst s1\<close> using blast_m_mono[of \<open>fst sp\<close> sp vs dl \<open>A ! k\<close>] B by simp
  have b1: \<open>fst s1 < 2 ^ 64\<close> using Suc.prems(3) E by simp
  have bp: \<open>fst sp < 2 ^ 64\<close> using le b1 by simp
  have kl: \<open>k < length A\<close> using Suc.prems(1) by simp
  have IH: \<open>wf_st sp \<and> fst s0 \<le> fst sp \<and> (\<forall>\<sigma>. cnf_sem \<sigma> (snd sp) \<longrightarrow> cnf_sem \<sigma> (snd s0)) \<and>
   (\<forall>\<sigma>. cnf_sem \<sigma> (snd sp) \<longrightarrow>
      (\<forall>j < k. eval ws ds (map (val \<sigma>) vs) (map (val \<sigma>) dl) (A ! j) = 1)) \<and>
   (\<forall>\<sigma>. cnf_sem \<sigma> (snd s0) \<longrightarrow>
      (\<forall>j < k. eval ws ds (map (val \<sigma>) vs) (map (val \<sigma>) dl) (A ! j) = 1) \<longrightarrow>
      (\<exists>\<sigma>'. (\<forall>v < fst s0. \<sigma>' v = \<sigma> v) \<and> cnf_sem \<sigma>' (snd sp)))\<close>
    using Suc.IH[OF _ sp_def[symmetric] bp] kl by simp
  have wtk: \<open>wt ws ds (A ! k)\<close> and wk1: \<open>width ws ds (A ! k) = 1\<close>
    using assms(4) nth_mem[OF kl] by simp_all
  have envs: \<open>env_ok (fst sp) ws vs\<close> \<open>env_ok (fst sp) ds dl\<close>
    using assms(2,3) IH env_ok_mono by blast+
  have wfp: \<open>wf_st sp\<close> using IH by simp
  note BC = blast_correct[OF wtk wfp envs B b1]
  have l1: \<open>length ls = 1\<close> using BC wk1 by simp
  have \<open>ls ! 0 \<in> set ls\<close> using l1 by (auto intro!: nth_mem)
  then have ll: \<open>lits_lt (fst s1) [ls ! 0]\<close> using BC unfolding lits_lt_def by auto
  have e1: \<open>ext sp s1\<close> using BC by simp
  have envl: \<open>\<forall>l \<in> set vs. lits_lt (fst s0) l\<close> \<open>\<forall>l \<in> set dl. lits_lt (fst s0) l\<close>
    using assms(2,3) by (simp_all add: env_ok_def)
  show ?case
  proof (intro conjI allI impI)
    show \<open>wf_st s\<close> using wf_addc[of s1 \<open>[ls ! 0]\<close>] BC ll E by simp
    show \<open>fst s0 \<le> fst s\<close> using IH le E by simp
  next
    fix \<sigma> assume S: \<open>cnf_sem \<sigma> (snd s)\<close>
    have S1: \<open>cnf_sem \<sigma> (snd s1)\<close> and U: \<open>lit_sem \<sigma> (ls ! 0)\<close>
      using S E by (simp_all add: cnf_sem_append_enc cnf_sem_unit)
    have Sp: \<open>cnf_sem \<sigma> (snd sp)\<close> using ext_cnf_sem[OF e1 S1] .
    show \<open>cnf_sem \<sigma> (snd s0)\<close> using IH Sp by blast
  next
    fix \<sigma> j assume S: \<open>cnf_sem \<sigma> (snd s)\<close> and j: \<open>j < Suc k\<close>
    have S1: \<open>cnf_sem \<sigma> (snd s1)\<close> and U: \<open>lit_sem \<sigma> (ls ! 0)\<close>
      using S E by (simp_all add: cnf_sem_append_enc cnf_sem_unit)
    have Sp: \<open>cnf_sem \<sigma> (snd sp)\<close> using ext_cnf_sem[OF e1 S1] .
    show \<open>eval ws ds (map (val \<sigma>) vs) (map (val \<sigma>) dl) (A ! j) = 1\<close>
    proof (cases \<open>j < k\<close>)
      case True
      then show ?thesis using IH Sp by blast
    next
      case False
      then have \<open>j = k\<close> using j by simp
      then show ?thesis using BC S1 U val_single_enc[OF l1, of \<sigma>] by simp
    qed
  next
    fix \<sigma> assume S: \<open>cnf_sem \<sigma> (snd s0)\<close>
      and V: \<open>\<forall>j < Suc k. eval ws ds (map (val \<sigma>) vs) (map (val \<sigma>) dl) (A ! j) = 1\<close>
    obtain \<sigma>1 where T1: \<open>\<forall>v < fst s0. \<sigma>1 v = \<sigma> v\<close> \<open>cnf_sem \<sigma>1 (snd sp)\<close>
      using IH S V by auto
    obtain \<sigma>2 where T2: \<open>\<forall>v < fst sp. \<sigma>2 v = \<sigma>1 v\<close> \<open>cnf_sem \<sigma>2 (snd s1)\<close>
      using e1 T1(2) unfolding ext_def by blast
    have ag: \<open>\<forall>v < fst s0. \<sigma>2 v = \<sigma> v\<close> using T1(1) T2(1) IH by auto
    have \<open>val \<sigma>2 ls = eval ws ds (map (val \<sigma>2) vs) (map (val \<sigma>2) dl) (A ! k)\<close>
      using BC T2(2) by blast
    also have \<open>\<dots> = eval ws ds (map (val \<sigma>) vs) (map (val \<sigma>) dl) (A ! k)\<close>
    proof -
      have m1: \<open>map (val \<sigma>2) vs = map (val \<sigma>) vs\<close> by (rule map_val_agree[OF envl(1) ag])
      have m2: \<open>map (val \<sigma>2) dl = map (val \<sigma>) dl\<close> by (rule map_val_agree[OF envl(2) ag])
      show ?thesis by (simp only: m1 m2)
    qed
    also have \<open>\<dots> = 1\<close> using V by simp
    finally have \<open>lit_sem \<sigma>2 (ls ! 0)\<close> using val_single_enc[OF l1, of \<sigma>2]
      by (cases \<open>lit_sem \<sigma>2 (ls ! 0)\<close>) simp_all
    then have \<open>cnf_sem \<sigma>2 (snd s)\<close> using T2(2) E by (simp add: cnf_sem_append_enc cnf_sem_unit)
    then show \<open>\<exists>\<sigma>'. (\<forall>v < fst s0. \<sigma>' v = \<sigma> v) \<and> cnf_sem \<sigma>' (snd s)\<close> using ag by blast
  qed
qed

subsection \<open>The encoding\<close>

lemma vars_step_mono: \<open>fst (fst x) \<le> fst (fst (vars_step W x i))\<close>
  by (simp add: vars_step_def split_def Let_def fresh_vec_m_def)

lemma defs_step_mono: \<open>fst (fst x) \<le> fst (fst (defs_step vs D x i))\<close>
  by (simp add: defs_step_def split_def Let_def blast_m_mono)

lemma asserts_step_mono: \<open>fst x \<le> fst (asserts_step vs dl A x i)\<close>
  by (simp add: asserts_step_def split_def Let_def blast_m_mono)

lemma encode_main:
  assumes \<open>problem_wt p\<close> \<open>encode_m p = (s, vs)\<close> \<open>fst s < 2 ^ 64\<close>
  shows \<open>wf_st s \<and> length vs = length (Problem_widths p) \<and>
    (\<forall>i < length vs. length (vs ! i) = unat (Problem_widths p ! i)) \<and>
    (\<forall>ls \<in> set vs. lits_lt (fst s) ls) \<and>
    (\<forall>\<sigma>. cnf_sem \<sigma> (snd s) \<longrightarrow> satisfies p (map (map (lit_sem \<sigma>)) vs)) \<and>
    (\<forall>m. is_assignment p m \<longrightarrow> satisfies p m \<longrightarrow> (\<exists>\<sigma>. cnf_sem \<sigma> (snd s)))\<close>
proof -
  let ?W = \<open>Problem_widths p\<close>
  let ?D = \<open>Problem_defs p\<close>
  let ?A = \<open>Problem_asserts p\<close>
  let ?ws = \<open>var_widths p\<close>
  let ?ds = \<open>def_widths ?ws [] ?D\<close>
  obtain s1 vs1 where V: \<open>foldl (vars_step ?W) (init_st, []) [0..<length ?W] = (s1, vs1)\<close>
    by (cases \<open>foldl (vars_step ?W) (init_st, []) [0..<length ?W]\<close>)
  obtain s2 dl where Dl: \<open>foldl (defs_step vs1 ?D) (s1, []) [0..<length ?D] = (s2, dl)\<close>
    by (cases \<open>foldl (defs_step vs1 ?D) (s1, []) [0..<length ?D]\<close>)
  have X: \<open>encode_m p = (foldl (asserts_step vs1 dl ?A) s2 [0..<length ?A], vs1)\<close>
    by (simp add: encode_m_def V Dl)
  have S: \<open>foldl (asserts_step vs1 dl ?A) s2 [0..<length ?A] = s\<close>
    using X assms(2) by (metis prod.inject)
  have Evs: \<open>vs = vs1\<close> using X assms(2) by (metis prod.inject)
  have le2: \<open>fst s2 \<le> fst s\<close>
    using foldl_le'[of \<open>asserts_step vs1 dl ?A\<close> \<open>fst s2\<close> s2 \<open>[0..<length ?A]\<close>] asserts_step_mono S
    by simp
  have le1: \<open>fst s1 \<le> fst s2\<close>
    using foldl_le[of \<open>defs_step vs1 ?D\<close> \<open>fst s1\<close> \<open>(s1, [])\<close> \<open>[0..<length ?D]\<close>] defs_step_mono Dl
    by simp
  have b1: \<open>fst s1 < 2 ^ 64\<close> and b2: \<open>fst s2 < 2 ^ 64\<close> using le1 le2 assms(3) by linarith+
  note VI = vars_inv[OF order_refl V b1]
  have wf1: \<open>wf_st s1\<close> using VI by simp
  have env1: \<open>env_ok (fst s1) ?ws vs1\<close> using VI by (simp add: env_ok_def var_widths_def)
  have dwt: \<open>defs_wt ?ws [] ?D\<close> and awt: \<open>\<forall>t \<in> set ?A. wt ?ws ?ds t \<and> width ?ws ?ds t = 1\<close>
    using assms(1) by (simp_all add: problem_wt_def Let_def)
  have DI: \<open>wf_st s2 \<and> ext s1 s2 \<and> env_ok (fst s2) ?ds dl \<and>
    (\<forall>\<sigma>. cnf_sem \<sigma> (snd s2) \<longrightarrow> map (val \<sigma>) dl = def_values ?ws [] (map (val \<sigma>) vs1) [] ?D)\<close>
    using defs_inv[OF wf1 env1 dwt order_refl Dl b2] by simp
  have wf2: \<open>wf_st s2\<close> and e12: \<open>ext s1 s2\<close> and envd: \<open>env_ok (fst s2) ?ds dl\<close> using DI by simp_all
  have envv: \<open>env_ok (fst s2) ?ws vs1\<close> using env1 ext_fst[OF e12] env_ok_mono by blast
  note AI = asserts_inv[OF wf2 envv envd awt order_refl S assms(3)]
  have vl: \<open>\<forall>l \<in> set vs1. lits_lt (fst s1) l\<close> using VI by simp
  show ?thesis
  proof (intro conjI allI impI)
    show \<open>wf_st s\<close> using AI by simp
    show \<open>length vs = length ?W\<close> using VI Evs by simp
    show \<open>length (vs ! i) = unat (?W ! i)\<close> if \<open>i < length vs\<close> for i using that VI Evs by simp
    show \<open>\<forall>ls \<in> set vs. lits_lt (fst s) ls\<close>
      using vl le1 le2 Evs lits_lt_mono by (meson order_trans)
  next
    fix \<sigma> assume Sg: \<open>cnf_sem \<sigma> (snd s)\<close>
    have S2: \<open>cnf_sem \<sigma> (snd s2)\<close> using AI Sg by blast
    have ev: \<open>\<forall>j < length ?A. eval ?ws ?ds (map (val \<sigma>) vs1) (map (val \<sigma>) dl) (?A ! j) = 1\<close>
      using AI Sg by blast
    have dv: \<open>map (val \<sigma>) dl = def_values ?ws [] (map (val \<sigma>) vs1) [] ?D\<close> using DI S2 by blast
    show \<open>satisfies p (map (map (lit_sem \<sigma>)) vs)\<close>
    proof -
      have mv: \<open>map bits_nat (map (map (lit_sem \<sigma>)) vs1) = map (val \<sigma>) vs1\<close>
        by (simp add: val_def)
      show ?thesis
        unfolding satisfies_def Let_def Evs mv using ev dv by (auto simp: in_set_conv_nth)
    qed
  next
    fix m assume M: \<open>is_assignment p m\<close> and Sm: \<open>satisfies p m\<close>
    have mw: \<open>map length m = map unat ?W\<close> using M by (simp add: is_assignment_def var_widths_def)
    have lm: \<open>length m = length ?W\<close> using arg_cong[OF mw, of length] by simp
    have \<open>\<forall>i < length ?W. length (m ! i) = unat (?W ! i)\<close>
      using mw lm list_eq_iff_nth_eq[of \<open>map length m\<close> \<open>map unat ?W\<close>] by simp
    then have \<open>length m = length ?W\<close> \<open>\<forall>i < length ?W. length (m ! i) = unat (?W ! i)\<close>
      using lm by simp_all
    then obtain \<sigma>0 where T0: \<open>cnf_sem \<sigma>0 (snd s1)\<close> \<open>map (map (lit_sem \<sigma>0)) vs1 = m\<close>
      using VI by blast
    obtain \<sigma>1 where T1: \<open>\<forall>v < fst s1. \<sigma>1 v = \<sigma>0 v\<close> \<open>cnf_sem \<sigma>1 (snd s2)\<close>
      using e12 T0(1) unfolding ext_def by blast
    have m1: \<open>map (map (lit_sem \<sigma>1)) vs1 = m\<close>
      using map_map_lit_agree[OF vl T1(1)] T0(2) by simp
    have vv: \<open>map (val \<sigma>1) vs1 = map bits_nat m\<close> using m1 by (simp add: map_val_bits)
    have dv: \<open>map (val \<sigma>1) dl = def_values ?ws [] (map bits_nat m) [] ?D\<close>
      using DI T1(2) vv by simp
    have \<open>\<forall>t \<in> set ?A. eval ?ws ?ds (map bits_nat m) (def_values ?ws [] (map bits_nat m) [] ?D) t = 1\<close>
      using Sm by (simp add: satisfies_def Let_def)
    then have \<open>\<forall>j < length ?A. eval ?ws ?ds (map (val \<sigma>1) vs1) (map (val \<sigma>1) dl) (?A ! j) = 1\<close>
      using vv dv by simp
    then show \<open>\<exists>\<sigma>. cnf_sem \<sigma> (snd s)\<close> using AI T1(2) by blast
  qed
qed

theorem encode_sound:
  assumes \<open>problem_wt p\<close> \<open>encode_m p = (s, vs)\<close> \<open>fst s < 2 ^ 64\<close> \<open>cnf_sem \<sigma> (snd s)\<close>
  shows \<open>is_assignment p (map (map (lit_sem \<sigma>)) vs) \<and> satisfies p (map (map (lit_sem \<sigma>)) vs)\<close>
  using encode_main[OF assms(1-3)] assms(4)
  by (auto simp: is_assignment_def var_widths_def list_eq_iff_nth_eq)

theorem encode_complete:
  assumes \<open>problem_wt p\<close> \<open>encode_m p = (s, vs)\<close> \<open>fst s < 2 ^ 64\<close> \<open>is_assignment p m\<close> \<open>satisfies p m\<close>
  shows \<open>\<exists>\<sigma>. cnf_sem \<sigma> (snd s)\<close>
  using encode_main[OF assms(1-3)] assms(4,5) by blast

theorem encode_wf:
  assumes \<open>problem_wt p\<close> \<open>encode_m p = (s, vs)\<close> \<open>fst s < 2 ^ 64\<close>
  shows \<open>(\<forall>c \<in> set (snd s). lits_lt (fst s) c) \<and> (\<forall>ls \<in> set vs. lits_lt (fst s) ls) \<and>
         length vs = length (Problem_widths p) \<and>
         (\<forall>i < length vs. length (vs ! i) = unat (Problem_widths p ! i))\<close>
  using encode_main[OF assms(1-3)] by (simp add: wf_st_def)

end
