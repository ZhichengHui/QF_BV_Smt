theory QFBV_Circuits
  imports QFBV_Defs
begin

section \<open>Basic facts\<close>

subsection \<open>Literals, clauses, values\<close>

lemma lits_lt_Nil [simp]: \<open>lits_lt n []\<close>
  by (simp add: lits_lt_def)

lemma lits_lt_Cons [simp]: \<open>lits_lt n (x # xs) \<longleftrightarrow> unat (Lit_var x) < n \<and> lits_lt n xs\<close>
  by (simp add: lits_lt_def)

lemma lits_lt_append [simp]: \<open>lits_lt n (xs @ ys) \<longleftrightarrow> lits_lt n xs \<and> lits_lt n ys\<close>
  by (auto simp add: lits_lt_def)

lemma lits_lt_mono: \<open>lits_lt n a \<Longrightarrow> n \<le> m \<Longrightarrow> lits_lt m a\<close>
  by (auto simp add: lits_lt_def)

lemma lits_lt_Suc: \<open>lits_lt n a \<Longrightarrow> lits_lt (Suc n) a\<close>
  by (auto simp add: lits_lt_def)

lemma lits_lt_nth: \<open>lits_lt n a \<Longrightarrow> i < length a \<Longrightarrow> unat (Lit_var (a ! i)) < n\<close>
  by (simp add: lits_lt_def)

lemma Lit_var_lconst [simp]: \<open>Lit_var (lconst b) = 0\<close>
  by (simp add: lconst_def)

lemma Lit_neg_lconst [simp]: \<open>Lit_neg (lconst b) = (\<not> b)\<close>
  by (simp add: lconst_def)

lemma Lit_var_lneg [simp]: \<open>Lit_var (lneg l) = Lit_var l\<close>
  by (simp add: lneg_def)

lemma Lit_neg_lneg [simp]: \<open>Lit_neg (lneg l) = (\<not> Lit_neg l)\<close>
  by (simp add: lneg_def)

lemma lit_sem_lneg [simp]: \<open>lit_sem \<sigma> (lneg l) = (\<not> lit_sem \<sigma> l)\<close>
  by (simp add: lit_sem_def lneg_def)

lemma cnf_sem_Nil [simp]: \<open>cnf_sem \<sigma> []\<close>
  by (simp add: cnf_sem_def)

lemma cnf_sem_Cons [simp]: \<open>cnf_sem \<sigma> (c # cs) \<longleftrightarrow> (\<exists>l\<in>set c. lit_sem \<sigma> l) \<and> cnf_sem \<sigma> cs\<close>
  by (simp add: cnf_sem_def)

lemma cnf_sem_append [simp]: \<open>cnf_sem \<sigma> (xs @ ys) \<longleftrightarrow> cnf_sem \<sigma> xs \<and> cnf_sem \<sigma> ys\<close>
  by (auto simp add: cnf_sem_def)

lemma lit_sem_lconst_mem:
  assumes \<open>[lconst True] \<in> set cs\<close> \<open>cnf_sem \<sigma> cs\<close>
  shows \<open>lit_sem \<sigma> (lconst b) = b\<close>
proof -
  have \<open>\<exists>l\<in>set [lconst True]. lit_sem \<sigma> l\<close> using assms unfolding cnf_sem_def by blast
  then have \<open>\<sigma> 0\<close> by (simp add: lit_sem_def lconst_def)
  then show ?thesis by (simp add: lit_sem_def lconst_def)
qed

lemma lit_sem_lconst:
  \<open>wf_st s \<Longrightarrow> cnf_sem \<sigma> (snd s) \<Longrightarrow> lit_sem \<sigma> (lconst b) = b\<close>
  using lit_sem_lconst_mem by (auto simp: wf_st_def)

lemma wf_st_pos: \<open>wf_st s \<Longrightarrow> 0 < fst s\<close>
  by (simp add: wf_st_def)

lemma cnf_sem_agree:
  assumes \<open>\<forall>c\<in>set cs. lits_lt n c\<close> \<open>\<forall>v<n. \<sigma>' v = \<sigma> v\<close> \<open>cnf_sem \<sigma> cs\<close>
  shows \<open>cnf_sem \<sigma>' cs\<close>
  unfolding cnf_sem_def
proof
  fix c assume c: \<open>c \<in> set cs\<close>
  then obtain l where l: \<open>l \<in> set c\<close> \<open>lit_sem \<sigma> l\<close> using assms(3) by (auto simp: cnf_sem_def)
  have \<open>unat (Lit_var l) < n\<close> using assms(1) c l(1) by (auto simp: lits_lt_def)
  then have \<open>lit_sem \<sigma>' l\<close> using l(2) assms(2) by (simp add: lit_sem_def)
  then show \<open>\<exists>l\<in>set c. lit_sem \<sigma>' l\<close> using l(1) by blast
qed

lemma lit_sem_agree:
  \<open>unat (Lit_var l) < n \<Longrightarrow> \<forall>v<n. \<sigma>' v = \<sigma> v \<Longrightarrow> lit_sem \<sigma>' l = lit_sem \<sigma> l\<close>
  by (simp add: lit_sem_def)

lemma map_lit_sem_agree:
  \<open>lits_lt n a \<Longrightarrow> \<forall>v<n. \<sigma>' v = \<sigma> v \<Longrightarrow> map (lit_sem \<sigma>') a = map (lit_sem \<sigma>) a\<close>
  by (auto simp add: lits_lt_def lit_sem_def)

lemma val_agree:
  \<open>lits_lt n a \<Longrightarrow> \<forall>v<n. \<sigma>' v = \<sigma> v \<Longrightarrow> val \<sigma>' a = val \<sigma> a\<close>
  unfolding val_def using map_lit_sem_agree by metis

lemma unat_won [simp]: \<open>n < 2 ^ 64 \<Longrightarrow> unat (word_of_nat n :: 64 word) = n\<close>
  by (simp add: unat_of_nat_eq)

subsection \<open>Values\<close>

lemma bits_nat_append: \<open>bits_nat (xs @ ys) = bits_nat xs + 2 ^ length xs * bits_nat ys\<close>
  by (induct xs) (simp_all add: algebra_simps)

lemma bits_nat_lt: \<open>bits_nat xs < 2 ^ length xs\<close>
proof (induct xs)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  then show ?case by (cases x) simp_all
qed

lemma val_lt: \<open>val \<sigma> a < 2 ^ length a\<close>
  unfolding val_def using bits_nat_lt[of \<open>map (lit_sem \<sigma>) a\<close>] by simp

lemma val_Nil [simp]: \<open>val \<sigma> [] = 0\<close>
  by (simp add: val_def)

lemma val_snoc: \<open>val \<sigma> (xs @ [x]) = val \<sigma> xs + 2 ^ length xs * of_bool (lit_sem \<sigma> x)\<close>
  by (simp add: val_def bits_nat_append)

lemma val_append: \<open>val \<sigma> (xs @ ys) = val \<sigma> xs + 2 ^ length xs * val \<sigma> ys\<close>
  by (simp add: val_def bits_nat_append)

lemma val_single: \<open>val \<sigma> [x] = of_bool (lit_sem \<sigma> x)\<close>
  by (simp add: val_def)

lemma bit_bits_nat: \<open>bit (bits_nat xs) k \<longleftrightarrow> k < length xs \<and> xs ! k\<close>
proof (induct xs arbitrary: k)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  then show ?case by (cases k) (simp_all add: bit_0 bit_Suc)
qed

lemma bit_bits_nat_map: \<open>bit (bits_nat (map f [0..<n])) k \<longleftrightarrow> k < n \<and> f k\<close>
  by (auto simp add: bit_bits_nat)

lemma bit_val: \<open>bit (val \<sigma> a) k \<longleftrightarrow> k < length a \<and> lit_sem \<sigma> (a ! k)\<close>
  by (auto simp add: val_def bit_bits_nat)

lemma bits_nat_eq_iff:
  assumes \<open>length xs = length ys\<close>
  shows \<open>bits_nat xs = bits_nat ys \<longleftrightarrow> xs = ys\<close>
proof
  assume \<open>bits_nat xs = bits_nat ys\<close>
  then have \<open>\<forall>k. bit (bits_nat xs) k \<longleftrightarrow> bit (bits_nat ys) k\<close> by simp
  then have \<open>\<forall>k < length xs. xs ! k = ys ! k\<close> using assms by (auto simp add: bit_bits_nat)
  then show \<open>xs = ys\<close> using assms by (simp add: list_eq_iff_nth_eq)
qed simp

lemma val_eq_iff:
  assumes \<open>length a = length b\<close>
  shows \<open>val \<sigma> a = val \<sigma> b \<longleftrightarrow> (\<forall>j < length a. lit_sem \<sigma> (a ! j) = lit_sem \<sigma> (b ! j))\<close>
  using assms by (simp add: val_def bits_nat_eq_iff list_eq_iff_nth_eq)

lemma bit_shl_mod: \<open>bit ((x * 2 ^ i) mod 2 ^ n) k \<longleftrightarrow> k < n \<and> i \<le> k \<and> bit (x :: nat) (k - i)\<close>
  by (auto simp add: push_bit_eq_mult[symmetric] take_bit_eq_mod[symmetric] bit_take_bit_iff
      bit_push_bit_iff)

lemma bit_div_pow: \<open>bit ((x :: nat) div 2 ^ i) k \<longleftrightarrow> bit x (i + k)\<close>
  by (simp add: bit_iff_odd div_exp_eq)

lemma bit_mod_pow: \<open>bit ((x :: nat) mod 2 ^ n) k \<longleftrightarrow> k < n \<and> bit x k\<close>
  by (simp add: take_bit_eq_mod[symmetric] bit_take_bit_iff)

lemma bits_nat_replicate_False [simp]: \<open>bits_nat (replicate w False) = 0\<close>
  by (induct w) simp_all

lemma bits_nat_replicate_True: \<open>bits_nat (replicate w True) + 1 = 2 ^ w\<close>
  by (induct w) simp_all

lemma mod_of_carry:
  \<open>x + 2 ^ n * of_bool c = (y :: nat) \<Longrightarrow> x < 2 ^ n \<Longrightarrow> x = y mod 2 ^ n\<close>
  by (cases c) auto

subsection \<open>Extension\<close>

lemma ext_refl: \<open>ext s s\<close>
  unfolding ext_def by auto

lemma ext_trans: \<open>ext s1 s2 \<Longrightarrow> ext s2 s3 \<Longrightarrow> ext s1 s3\<close>
proof -
  assume 12: \<open>ext s1 s2\<close> and 23: \<open>ext s2 s3\<close>
  show \<open>ext s1 s3\<close> unfolding ext_def
  proof (intro conjI allI impI)
    have le: \<open>fst s1 \<le> fst s2\<close> using 12 by (simp add: ext_def)
    then show \<open>fst s1 \<le> fst s3\<close> using 23 by (simp add: ext_def)
    obtain cs1 where c1: \<open>snd s2 = snd s1 @ cs1\<close> using 12 by (auto simp: ext_def)
    obtain cs2 where c2: \<open>snd s3 = snd s2 @ cs2\<close> using 23 by (auto simp: ext_def)
    show \<open>\<exists>cs. snd s3 = snd s1 @ cs\<close> using c1 c2 by simp
    fix \<sigma> assume \<sigma>: \<open>cnf_sem \<sigma> (snd s1)\<close>
    obtain \<sigma>1 where h1: \<open>\<forall>v<fst s1. \<sigma>1 v = \<sigma> v\<close> \<open>cnf_sem \<sigma>1 (snd s2)\<close>
      using 12 \<sigma> unfolding ext_def by blast
    obtain \<sigma>2 where h2: \<open>\<forall>v<fst s2. \<sigma>2 v = \<sigma>1 v\<close> \<open>cnf_sem \<sigma>2 (snd s3)\<close>
      using 23 h1(2) unfolding ext_def by blast
    show \<open>\<exists>\<sigma>'. (\<forall>v<fst s1. \<sigma>' v = \<sigma> v) \<and> cnf_sem \<sigma>' (snd s3)\<close>
      using h1 h2 le by (intro exI[of _ \<sigma>2]) auto
  qed
qed

lemma ext_cnf_sem: \<open>ext s s' \<Longrightarrow> cnf_sem \<sigma> (snd s') \<Longrightarrow> cnf_sem \<sigma> (snd s)\<close>
  by (auto simp: ext_def)

lemma ext_fst: \<open>ext s s' \<Longrightarrow> fst s \<le> fst s'\<close>
  by (simp add: ext_def)

lemma ext_agree:
  assumes \<open>ext s s'\<close> \<open>cnf_sem \<sigma> (snd s)\<close>
  obtains \<sigma>' where \<open>\<forall>v<fst s. \<sigma>' v = \<sigma> v\<close> \<open>cnf_sem \<sigma>' (snd s')\<close>
  using assms unfolding ext_def by blast

section \<open>Gates\<close>

lemma gate_lemma:
  assumes wf: \<open>wf_st s\<close>
    and s': \<open>s' = (Suc (fst s), snd s @ cs)\<close>
    and lt: \<open>\<forall>c\<in>set cs. lits_lt (Suc (fst s)) c\<close>
    and vx: \<open>unat (Lit_var x) < Suc (fst s)\<close>
    and def: \<open>\<And>\<sigma>. cnf_sem \<sigma> (snd s) \<Longrightarrow> cnf_sem (\<sigma>(fst s := f \<sigma>)) cs\<close>
    and sound: \<open>\<And>\<sigma>. cnf_sem \<sigma> cs \<Longrightarrow> lit_sem \<sigma> x = g \<sigma>\<close>
  shows \<open>wf_st s' \<and> ext s s' \<and> unat (Lit_var x) < fst s' \<and>
         (\<forall>\<sigma>. cnf_sem \<sigma> (snd s') \<longrightarrow> lit_sem \<sigma> x = g \<sigma>)\<close>
proof (intro conjI)
  show \<open>wf_st s'\<close>
    using wf lt unfolding wf_st_def s' by (auto intro: lits_lt_Suc)
  show \<open>ext s s'\<close>
    unfolding ext_def
  proof (intro conjI allI impI)
    show \<open>fst s \<le> fst s'\<close> using s' by simp
    show \<open>\<exists>cs'. snd s' = snd s @ cs'\<close> using s' by simp
    fix \<sigma> assume \<sigma>: \<open>cnf_sem \<sigma> (snd s)\<close>
    let ?\<sigma>' = \<open>\<sigma>(fst s := f \<sigma>)\<close>
    have ag: \<open>\<forall>v<fst s. ?\<sigma>' v = \<sigma> v\<close> by simp
    have \<open>cnf_sem ?\<sigma>' (snd s)\<close> by (rule cnf_sem_agree[OF _ ag \<sigma>]) (use wf in \<open>simp add: wf_st_def\<close>)
    then show \<open>\<exists>\<sigma>'. (\<forall>v<fst s. \<sigma>' v = \<sigma> v) \<and> cnf_sem \<sigma>' (snd s')\<close>
      using ag def[OF \<sigma>] s' by (intro exI[of _ ?\<sigma>']) simp
  qed
  show \<open>unat (Lit_var x) < fst s'\<close> using vx s' by simp
  show \<open>\<forall>\<sigma>. cnf_sem \<sigma> (snd s') \<longrightarrow> lit_sem \<sigma> x = g \<sigma>\<close> using sound s' by simp
qed

lemma and_m_eq:
  \<open>and_m s a b =
    (let x = make_Lit (word_of_nat (fst s)) False in
     ((Suc (fst s), snd s @ [[lneg x, a], [lneg x, b], [x, lneg a, lneg b]]), x))\<close>
  by (simp add: and_m_def fresh_m_def addc_m_def Let_def)

lemma xor_m_eq:
  \<open>xor_m s a b =
    (let x = make_Lit (word_of_nat (fst s)) False in
     ((Suc (fst s), snd s @ [[lneg x, a, b], [lneg x, lneg a, lneg b], [x, lneg a, b], [x, a, lneg b]]), x))\<close>
  by (simp add: xor_m_def fresh_m_def addc_m_def Let_def)

lemma ite_m_eq:
  \<open>ite_m s c a b =
    (let x = make_Lit (word_of_nat (fst s)) False in
     ((Suc (fst s), snd s @ [[lneg c, lneg x, a], [lneg c, x, lneg a], [c, lneg x, b], [c, x, lneg b]]), x))\<close>
  by (simp add: ite_m_def fresh_m_def addc_m_def Let_def)

lemma and_fst [simp]: \<open>fst (fst (and_m s a b)) = Suc (fst s)\<close>
  by (simp add: and_m_eq Let_def)

lemma xor_fst [simp]: \<open>fst (fst (xor_m s a b)) = Suc (fst s)\<close>
  by (simp add: xor_m_eq Let_def)

lemma ite_fst [simp]: \<open>fst (fst (ite_m s c a b)) = Suc (fst s)\<close>
  by (simp add: ite_m_eq Let_def)

lemma or_fst [simp]: \<open>fst (fst (or_m s a b)) = Suc (fst s)\<close>
  by (simp add: or_m_def split_def Let_def)

lemma lit_sem_upd:
  \<open>lit_sem (\<sigma>(n := v)) l = (if unat (Lit_var l) = n then v \<noteq> Lit_neg l else lit_sem \<sigma> l)\<close>
  by (simp add: lit_sem_def)

lemma and_ok:
  assumes wf: \<open>wf_st s\<close> and a: \<open>unat (Lit_var a) < fst s\<close> and b: \<open>unat (Lit_var b) < fst s\<close>
    and d: \<open>and_m s a b = (s', x)\<close> and lt: \<open>fst s' < 2 ^ 64\<close>
  shows \<open>wf_st s' \<and> ext s s' \<and> unat (Lit_var x) < fst s' \<and>
         (\<forall>\<sigma>. cnf_sem \<sigma> (snd s') \<longrightarrow> lit_sem \<sigma> x = (lit_sem \<sigma> a \<and> lit_sem \<sigma> b))\<close>
proof -
  let ?x = \<open>make_Lit (word_of_nat (fst s)) False\<close>
  have e: \<open>s' = (Suc (fst s), snd s @ [[lneg ?x, a], [lneg ?x, b], [?x, lneg a, lneg b]])\<close> \<open>x = ?x\<close>
    using d by (auto simp: and_m_eq Let_def)
  have n: \<open>fst s < 2 ^ 64\<close> using lt e(1) by simp
  have vx: \<open>unat (word_of_nat (fst s) :: 64 word) = fst s\<close> using n by simp
  note ne = less_imp_neq[OF a] less_imp_neq[OF b]
  show ?thesis unfolding e(2)
    by (rule gate_lemma[OF wf e(1), where f = \<open>\<lambda>\<sigma>. lit_sem \<sigma> a \<and> lit_sem \<sigma> b\<close>])
      (use a b vx ne in \<open>auto simp: lit_sem_upd\<close>)
qed

lemma xor_ok:
  assumes wf: \<open>wf_st s\<close> and a: \<open>unat (Lit_var a) < fst s\<close> and b: \<open>unat (Lit_var b) < fst s\<close>
    and d: \<open>xor_m s a b = (s', x)\<close> and lt: \<open>fst s' < 2 ^ 64\<close>
  shows \<open>wf_st s' \<and> ext s s' \<and> unat (Lit_var x) < fst s' \<and>
         (\<forall>\<sigma>. cnf_sem \<sigma> (snd s') \<longrightarrow> lit_sem \<sigma> x = (lit_sem \<sigma> a \<noteq> lit_sem \<sigma> b))\<close>
proof -
  let ?x = \<open>make_Lit (word_of_nat (fst s)) False\<close>
  have e: \<open>s' = (Suc (fst s), snd s @ [[lneg ?x, a, b], [lneg ?x, lneg a, lneg b], [?x, lneg a, b], [?x, a, lneg b]])\<close>
    \<open>x = ?x\<close>
    using d by (auto simp: xor_m_eq Let_def)
  have n: \<open>fst s < 2 ^ 64\<close> using lt e(1) by simp
  have vx: \<open>unat (word_of_nat (fst s) :: 64 word) = fst s\<close> using n by simp
  note ne = less_imp_neq[OF a] less_imp_neq[OF b]
  show ?thesis unfolding e(2)
    by (rule gate_lemma[OF wf e(1), where f = \<open>\<lambda>\<sigma>. lit_sem \<sigma> a \<noteq> lit_sem \<sigma> b\<close>])
      (use a b vx ne in \<open>auto simp: lit_sem_upd\<close>)
qed

lemma ite_ok:
  assumes wf: \<open>wf_st s\<close> and c: \<open>unat (Lit_var c) < fst s\<close>
    and a: \<open>unat (Lit_var a) < fst s\<close> and b: \<open>unat (Lit_var b) < fst s\<close>
    and d: \<open>ite_m s c a b = (s', x)\<close> and lt: \<open>fst s' < 2 ^ 64\<close>
  shows \<open>wf_st s' \<and> ext s s' \<and> unat (Lit_var x) < fst s' \<and>
         (\<forall>\<sigma>. cnf_sem \<sigma> (snd s') \<longrightarrow>
            lit_sem \<sigma> x = (if lit_sem \<sigma> c then lit_sem \<sigma> a else lit_sem \<sigma> b))\<close>
proof -
  let ?x = \<open>make_Lit (word_of_nat (fst s)) False\<close>
  have e: \<open>s' = (Suc (fst s), snd s @ [[lneg c, lneg ?x, a], [lneg c, ?x, lneg a], [c, lneg ?x, b], [c, ?x, lneg b]])\<close>
    \<open>x = ?x\<close>
    using d by (auto simp: ite_m_eq Let_def)
  have n: \<open>fst s < 2 ^ 64\<close> using lt e(1) by simp
  have vx: \<open>unat (word_of_nat (fst s) :: 64 word) = fst s\<close> using n by simp
  note ne = less_imp_neq[OF a] less_imp_neq[OF b] less_imp_neq[OF c]
  show ?thesis unfolding e(2)
    by (rule gate_lemma[OF wf e(1), where f = \<open>\<lambda>\<sigma>. if lit_sem \<sigma> c then lit_sem \<sigma> a else lit_sem \<sigma> b\<close>])
      (use a b c vx ne in \<open>auto simp: lit_sem_upd\<close>)
qed

lemma or_ok:
  assumes wf: \<open>wf_st s\<close> and a: \<open>unat (Lit_var a) < fst s\<close> and b: \<open>unat (Lit_var b) < fst s\<close>
    and d: \<open>or_m s a b = (s', x)\<close> and lt: \<open>fst s' < 2 ^ 64\<close>
  shows \<open>wf_st s' \<and> ext s s' \<and> unat (Lit_var x) < fst s' \<and>
         (\<forall>\<sigma>. cnf_sem \<sigma> (snd s') \<longrightarrow> lit_sem \<sigma> x = (lit_sem \<sigma> a \<or> lit_sem \<sigma> b))\<close>
proof -
  obtain s1 y where d1: \<open>and_m s (lneg a) (lneg b) = (s1, y)\<close> by (cases \<open>and_m s (lneg a) (lneg b)\<close>)
  have e: \<open>s' = s1\<close> \<open>x = lneg y\<close> using d d1 by (simp_all add: or_m_def)
  show ?thesis using and_ok[of s \<open>lneg a\<close> \<open>lneg b\<close> s1 y] wf a b d1 lt e by auto
qed

definition bop :: \<open>BinOp \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool\<close> where
  \<open>bop op p q = (case op of BinOp_And \<Rightarrow> p \<and> q | BinOp_Or \<Rightarrow> p \<or> q | _ \<Rightarrow> p \<noteq> q)\<close>

lemma bitw_fst [simp]: \<open>fst (fst (bitw_m op s a b)) = Suc (fst s)\<close>
  by (cases op) (simp_all add: bitw_m_def)

lemma bitw_ok:
  assumes wf: \<open>wf_st s\<close> and a: \<open>unat (Lit_var a) < fst s\<close> and b: \<open>unat (Lit_var b) < fst s\<close>
    and d: \<open>bitw_m op s a b = (s', x)\<close> and lt: \<open>fst s' < 2 ^ 64\<close>
  shows \<open>wf_st s' \<and> ext s s' \<and> unat (Lit_var x) < fst s' \<and>
         (\<forall>\<sigma>. cnf_sem \<sigma> (snd s') \<longrightarrow> lit_sem \<sigma> x = bop op (lit_sem \<sigma> a) (lit_sem \<sigma> b))\<close>
proof -
  consider \<open>op = BinOp_And\<close> | \<open>op = BinOp_Or\<close> | \<open>bitw_m op = xor_m \<and> bop op = (\<noteq>)\<close>
    by (cases op) (auto simp: bitw_m_def bop_def fun_eq_iff)
  then show ?thesis
  proof cases
    case 1 then show ?thesis using and_ok[OF wf a b _ lt] d by (simp add: bitw_m_def bop_def)
  next
    case 2 then show ?thesis using or_ok[OF wf a b _ lt] d by (simp add: bitw_m_def bop_def)
  next
    case 3 then show ?thesis using xor_ok[OF wf a b _ lt] d by simp
  qed
qed

section \<open>Loops\<close>

lemma foldl_upt_inv:
  assumes \<open>P 0 x0\<close> \<open>\<And>i x. i < n \<Longrightarrow> P i x \<Longrightarrow> P (Suc i) (f x i)\<close>
  shows \<open>P n (foldl f x0 [0..<n])\<close>
proof -
  have \<open>m \<le> n \<Longrightarrow> P m (foldl f x0 [0..<m])\<close> for m
    by (induct m) (use assms in auto)
  then show ?thesis by simp
qed

lemma foldl_mono:
  fixes f :: \<open>st \<times> 'b \<Rightarrow> 'c \<Rightarrow> st \<times> 'b\<close>
  assumes \<open>\<And>x i. fst (fst x) \<le> fst (fst (f x i))\<close>
  shows \<open>fst s \<le> fst (fst (foldl f (s, r) xs))\<close>
proof (induct xs arbitrary: s r)
  case Nil then show ?case by simp
next
  case (Cons y ys)
  obtain s1 r1 where e: \<open>f (s, r) y = (s1, r1)\<close> by (cases \<open>f (s, r) y\<close>)
  have \<open>fst s \<le> fst s1\<close> using assms[of \<open>(s, r)\<close> y] e by simp
  moreover have \<open>fst s1 \<le> fst (fst (foldl f (s1, r1) ys))\<close> by (rule Cons)
  ultimately show ?case using e by simp
qed

text \<open>A loop that runs a gate per bit and collects the outputs.\<close>
lemma map_gate_loop:
  fixes g :: \<open>st \<Rightarrow> nat \<Rightarrow> st \<times> Lit\<close> and h :: \<open>(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bool\<close>
  assumes mono: \<open>\<And>s i. fst s \<le> fst (fst (g s i))\<close>
    and ok: \<open>\<And>s i s' x. wf_st s \<Longrightarrow> fst s0 \<le> fst s \<Longrightarrow> i < n \<Longrightarrow> g s i = (s', x) \<Longrightarrow> fst s' < 2 ^ 64 \<Longrightarrow>
       wf_st s' \<and> ext s s' \<and> unat (Lit_var x) < fst s' \<and> (\<forall>\<sigma>. cnf_sem \<sigma> (snd s') \<longrightarrow> lit_sem \<sigma> x = h \<sigma> i)\<close>
    and wf: \<open>wf_st s0\<close>
    and res: \<open>foldl (\<lambda>(s, r) i. let (s1, x) = g s i in (s1, r @ [x])) (s0, []) [0..<n] = (s', r)\<close>
    and lt: \<open>fst s' < 2 ^ 64\<close>
  shows \<open>wf_st s' \<and> ext s0 s' \<and> lits_lt (fst s') r \<and> length r = n \<and>
     (\<forall>\<sigma>. cnf_sem \<sigma> (snd s') \<longrightarrow> map (lit_sem \<sigma>) r = map (h \<sigma>) [0..<n])\<close>
proof -
  let ?f = \<open>\<lambda>(s, r) i. let (s1, x) = g s i in (s1, r @ [x])\<close>
  let ?P = \<open>\<lambda>i (s, r). fst s0 \<le> fst s \<and> (fst s < 2 ^ 64 \<longrightarrow> wf_st s \<and> ext s0 s \<and> lits_lt (fst s) r \<and>
     length r = i \<and> (\<forall>\<sigma>. cnf_sem \<sigma> (snd s) \<longrightarrow> map (lit_sem \<sigma>) r = map (h \<sigma>) [0..<i]))\<close>
  have \<open>?P n (foldl ?f (s0, []) [0..<n])\<close>
  proof (rule foldl_upt_inv[where P = ?P])
    show \<open>?P 0 (s0, [])\<close> using wf by (simp add: ext_refl)
  next
    fix i x assume i: \<open>i < n\<close> and P: \<open>?P i x\<close>
    obtain s r where x: \<open>x = (s, r)\<close> by (cases x)
    obtain s1 y where g: \<open>g s i = (s1, y)\<close> by (cases \<open>g s i\<close>)
    have m: \<open>fst s \<le> fst s1\<close> using mono[of s i] g by simp
    have P1: \<open>fst s0 \<le> fst s\<close> using P x by simp
    have P2: \<open>fst s < 2 ^ 64 \<Longrightarrow> wf_st s \<and> ext s0 s \<and> lits_lt (fst s) r \<and> length r = i \<and>
       (\<forall>\<sigma>. cnf_sem \<sigma> (snd s) \<longrightarrow> map (lit_sem \<sigma>) r = map (h \<sigma>) [0..<i])\<close> using P x by simp
    have B: \<open>wf_st s1 \<and> ext s0 s1 \<and> lits_lt (fst s1) (r @ [y]) \<and> length (r @ [y]) = Suc i \<and>
       (\<forall>\<sigma>. cnf_sem \<sigma> (snd s1) \<longrightarrow> map (lit_sem \<sigma>) (r @ [y]) = map (h \<sigma>) [0..<Suc i])\<close>
      if lt1: \<open>fst s1 < 2 ^ 64\<close>
    proof -
      have I: \<open>wf_st s\<close> \<open>ext s0 s\<close> \<open>lits_lt (fst s) r\<close> \<open>length r = i\<close>
        \<open>\<forall>\<sigma>. cnf_sem \<sigma> (snd s) \<longrightarrow> map (lit_sem \<sigma>) r = map (h \<sigma>) [0..<i]\<close>
        using P2 m lt1 by auto
      have G: \<open>wf_st s1\<close> \<open>ext s s1\<close> \<open>unat (Lit_var y) < fst s1\<close>
        \<open>\<forall>\<sigma>. cnf_sem \<sigma> (snd s1) \<longrightarrow> lit_sem \<sigma> y = h \<sigma> i\<close>
        using ok[OF I(1) P1 i g lt1] by auto
      have S: \<open>map (lit_sem \<sigma>) (r @ [y]) = map (h \<sigma>) [0..<Suc i]\<close> if \<open>cnf_sem \<sigma> (snd s1)\<close> for \<sigma>
        using I(5) G(4) ext_cnf_sem[OF G(2) that] that by simp
      show ?thesis using I G S ext_trans[OF I(2) G(2)] lits_lt_mono[OF I(3) m] by simp
    qed
    show \<open>?P (Suc i) (?f x i)\<close> using P1 m B x g by simp
  qed
  then show ?thesis using res lt by simp
qed

lemma map_gate_mono:
  fixes g :: \<open>st \<Rightarrow> nat \<Rightarrow> st \<times> Lit\<close>
  assumes \<open>\<And>s i. fst s \<le> fst (fst (g s i))\<close>
  shows \<open>fst s0 \<le> fst (fst (foldl (\<lambda>(s, r) i. let (s1, x) = g s i in (s1, r @ [x])) (s0, r0) xs))\<close>
  by (rule foldl_mono) (use assms in \<open>simp add: split_def Let_def\<close>)

section \<open>Bit-vector circuits\<close>

subsection \<open>Pure circuits\<close>

lemma const_correct:
  assumes \<open>wf_st s\<close>
  shows \<open>lits_lt (fst s) (const_m bs) \<and> length (const_m bs) = length bs \<and>
         (\<forall>\<sigma>. cnf_sem \<sigma> (snd s) \<longrightarrow> val \<sigma> (const_m bs) = bits_nat bs)\<close>
proof -
  have \<open>map (lit_sem \<sigma>) (map lconst bs) = bs\<close> if \<open>cnf_sem \<sigma> (snd s)\<close> for \<sigma>
    using lit_sem_lconst[OF assms that] by (induct bs) simp_all
  then show ?thesis using wf_st_pos[OF assms] by (simp add: const_m_def val_def lits_lt_def)
qed

lemma bits_nat_map_Not: \<open>bits_nat (map Not xs) + bits_nat xs + 1 = 2 ^ length xs\<close>
proof (induct xs)
  case Nil then show ?case by simp
next
  case (Cons x xs) then show ?case by (cases x) simp_all
qed

lemma not_correct:
  shows \<open>(lits_lt n a \<longrightarrow> lits_lt n (not_m a)) \<and> length (not_m a) = length a \<and>
         val \<sigma> (not_m a) = 2 ^ length a - 1 - val \<sigma> a\<close>
proof -
  have \<open>map (lit_sem \<sigma>) (not_m a) = map Not (map (lit_sem \<sigma>) a)\<close> by (simp add: not_m_def)
  then have \<open>val \<sigma> (not_m a) + val \<sigma> a + 1 = 2 ^ length a\<close>
    using bits_nat_map_Not[of \<open>map (lit_sem \<sigma>) a\<close>] by (simp add: val_def)
  then show ?thesis by (auto simp: not_m_def lits_lt_def)
qed

lemma extract_correct:
  assumes \<open>lo \<le> hi\<close> \<open>hi < length a\<close>
  shows \<open>(lits_lt n a \<longrightarrow> lits_lt n (extract_m a hi lo)) \<and>
         length (extract_m a hi lo) = hi - lo + 1 \<and>
         val \<sigma> (extract_m a hi lo) = (val \<sigma> a div 2 ^ lo) mod 2 ^ (hi - lo + 1)\<close>
proof (intro conjI)
  show \<open>lits_lt n a \<longrightarrow> lits_lt n (extract_m a hi lo)\<close>
    using assms by (auto simp: extract_m_def lits_lt_def)
  show \<open>length (extract_m a hi lo) = hi - lo + 1\<close> using assms by (simp add: extract_m_def)
  show \<open>val \<sigma> (extract_m a hi lo) = (val \<sigma> a div 2 ^ lo) mod 2 ^ (hi - lo + 1)\<close>
  proof (rule bit_eqI)
    fix k
    have m: \<open>map (lit_sem \<sigma>) (extract_m a hi lo) = map (\<lambda>k. lit_sem \<sigma> (a ! (lo + k))) [0..<hi - lo + 1]\<close>
      using assms by (intro nth_equalityI) (simp_all add: extract_m_def Suc_diff_le del: upt_Suc)
    show \<open>bit (val \<sigma> (extract_m a hi lo)) k = bit ((val \<sigma> a div 2 ^ lo) mod 2 ^ (hi - lo + 1)) k\<close>
      unfolding val_def[of \<sigma> \<open>extract_m a hi lo\<close>] m bit_mod_pow bit_div_pow bit_bits_nat_map bit_val
      using assms by auto
  qed
qed

subsection \<open>Bitwise operations and if-then-else\<close>

lemma bitwise_ok:
  assumes wf: \<open>wf_st s\<close> and la: \<open>lits_lt (fst s) a\<close> and lb: \<open>lits_lt (fst s) b\<close>
    and len: \<open>length a = length b\<close>
    and d: \<open>bitwise_m op s a b = (s', r)\<close> and lt: \<open>fst s' < 2 ^ 64\<close>
  shows \<open>wf_st s' \<and> ext s s' \<and> lits_lt (fst s') r \<and> length r = length a \<and>
         (\<forall>\<sigma>. cnf_sem \<sigma> (snd s') \<longrightarrow>
            map (lit_sem \<sigma>) r = map (\<lambda>i. bop op (lit_sem \<sigma> (a ! i)) (lit_sem \<sigma> (b ! i))) [0..<length a])\<close>
proof (rule map_gate_loop[where g = \<open>\<lambda>s i. bitw_m op s (a ! i) (b ! i)\<close>, OF _ _ wf _ lt])
  show \<open>fst s \<le> fst (fst (bitw_m op s (a ! i) (b ! i)))\<close> for s i by simp
  show \<open>foldl (\<lambda>(s, r) i. let (s1, x) = bitw_m op s (a ! i) (b ! i) in (s1, r @ [x])) (s, []) [0..<length a] = (s', r)\<close>
    using d by (simp add: bitwise_m_def)
  fix s1 i s2 x
  assume H: \<open>wf_st s1\<close> \<open>fst s \<le> fst s1\<close> \<open>i < length a\<close> \<open>bitw_m op s1 (a ! i) (b ! i) = (s2, x)\<close> \<open>fst s2 < 2 ^ 64\<close>
  have ai: \<open>unat (Lit_var (a ! i)) < fst s1\<close> using lits_lt_nth[OF lits_lt_mono[OF la H(2)] H(3)] .
  have bi: \<open>unat (Lit_var (b ! i)) < fst s1\<close> using lits_lt_nth[OF lits_lt_mono[OF lb H(2)]] H(3) len by simp
  show \<open>wf_st s2 \<and> ext s1 s2 \<and> unat (Lit_var x) < fst s2 \<and>
       (\<forall>\<sigma>. cnf_sem \<sigma> (snd s2) \<longrightarrow> lit_sem \<sigma> x = bop op (lit_sem \<sigma> (a ! i)) (lit_sem \<sigma> (b ! i)))\<close>
    by (rule bitw_ok[OF H(1) ai bi H(4) H(5)])
qed

lemma bits_bop:
  assumes \<open>op \<in> {BinOp_And, BinOp_Or, BinOp_Xor}\<close> \<open>length a = n\<close> \<open>length b = n\<close>
  shows \<open>bits_nat (map (\<lambda>i. bop op (lit_sem \<sigma> (a ! i)) (lit_sem \<sigma> (b ! i))) [0..<n]) =
         cbin_sem op n (val \<sigma> a) n (val \<sigma> b)\<close>
proof -
  have \<open>bit (bits_nat (map (\<lambda>i. bop op (lit_sem \<sigma> (a ! i)) (lit_sem \<sigma> (b ! i))) [0..<n])) k =
        bit (cbin_sem op n (val \<sigma> a) n (val \<sigma> b)) k\<close> for k
  proof -
    consider \<open>op = BinOp_And\<close> | \<open>op = BinOp_Or\<close> | \<open>op = BinOp_Xor\<close> using assms(1) by blast
    then show ?thesis
    proof cases
      case 1 then show ?thesis using assms(2,3) by (auto simp: bit_bits_nat_map bit_val bop_def bit_and_iff)
    next
      case 2 then show ?thesis using assms(2,3) by (auto simp: bit_bits_nat_map bit_val bop_def bit_or_iff)
    next
      case 3 then show ?thesis using assms(2,3) by (auto simp: bit_bits_nat_map bit_val bop_def bit_xor_iff)
    qed
  qed
  then show ?thesis by (rule bit_eqI)
qed

lemma ite_vec_correct:
  assumes \<open>wf_st s\<close> \<open>lits_lt (fst s) [c]\<close> \<open>lits_lt (fst s) a\<close> \<open>lits_lt (fst s) b\<close>
    \<open>length a = length b\<close> \<open>ite_vec_m s c a b = (s', r)\<close> \<open>fst s' < 2 ^ 64\<close>
  shows \<open>wf_st s' \<and> ext s s' \<and> lits_lt (fst s') r \<and> length r = length a \<and>
         (\<forall>\<sigma>. cnf_sem \<sigma> (snd s') \<longrightarrow> val \<sigma> r = (if lit_sem \<sigma> c then val \<sigma> a else val \<sigma> b))\<close>
proof -
  have L: \<open>wf_st s' \<and> ext s s' \<and> lits_lt (fst s') r \<and> length r = length a \<and>
         (\<forall>\<sigma>. cnf_sem \<sigma> (snd s') \<longrightarrow>
            map (lit_sem \<sigma>) r = map (\<lambda>i. if lit_sem \<sigma> c then lit_sem \<sigma> (a ! i) else lit_sem \<sigma> (b ! i)) [0..<length a])\<close>
  proof (rule map_gate_loop[where g = \<open>\<lambda>s i. ite_m s c (a ! i) (b ! i)\<close>, OF _ _ assms(1) _ assms(7)])
    show \<open>fst s \<le> fst (fst (ite_m s c (a ! i) (b ! i)))\<close> for s i by simp
    show \<open>foldl (\<lambda>(s, r) i. let (s1, x) = ite_m s c (a ! i) (b ! i) in (s1, r @ [x])) (s, []) [0..<length a] = (s', r)\<close>
      using assms(6) by (simp add: ite_vec_m_def)
    fix s1 i s2 x
    assume H: \<open>wf_st s1\<close> \<open>fst s \<le> fst s1\<close> \<open>i < length a\<close> \<open>ite_m s1 c (a ! i) (b ! i) = (s2, x)\<close> \<open>fst s2 < 2 ^ 64\<close>
    have ai: \<open>unat (Lit_var (a ! i)) < fst s1\<close> using lits_lt_nth[OF lits_lt_mono[OF assms(3) H(2)] H(3)] .
    have bi: \<open>unat (Lit_var (b ! i)) < fst s1\<close>
      using lits_lt_nth[OF lits_lt_mono[OF assms(4) H(2)]] H(3) assms(5) by simp
    have ci: \<open>unat (Lit_var c) < fst s1\<close> using lits_lt_mono[OF assms(2) H(2)] by simp
    show \<open>wf_st s2 \<and> ext s1 s2 \<and> unat (Lit_var x) < fst s2 \<and>
       (\<forall>\<sigma>. cnf_sem \<sigma> (snd s2) \<longrightarrow> lit_sem \<sigma> x = (if lit_sem \<sigma> c then lit_sem \<sigma> (a ! i) else lit_sem \<sigma> (b ! i)))\<close>
      by (rule ite_ok[OF H(1) ci ai bi H(4) H(5)])
  qed
  have V: \<open>val \<sigma> r = (if lit_sem \<sigma> c then val \<sigma> a else val \<sigma> b)\<close> if \<open>cnf_sem \<sigma> (snd s')\<close> for \<sigma>
  proof -
    have m: \<open>map (lit_sem \<sigma>) r = map (\<lambda>i. if lit_sem \<sigma> c then lit_sem \<sigma> (a ! i) else lit_sem \<sigma> (b ! i)) [0..<length a]\<close>
      using L that by blast
    have \<open>map (lit_sem \<sigma>) r = (if lit_sem \<sigma> c then map (lit_sem \<sigma>) a else map (lit_sem \<sigma>) b)\<close>
    proof (cases \<open>lit_sem \<sigma> c\<close>)
      case True then show ?thesis unfolding m by (intro nth_equalityI) simp_all
    next
      case False then show ?thesis unfolding m using assms(5) by (intro nth_equalityI) simp_all
    qed
    then show ?thesis by (simp add: val_def)
  qed
  show ?thesis using L V by blast
qed

lemma ite_vec_m_mono: \<open>fst s \<le> fst (fst (ite_vec_m s c a b))\<close>
  unfolding ite_vec_m_def by (rule map_gate_mono) simp


subsection \<open>Addition\<close>

lemma add_step_fst [simp]: \<open>fst (fst (add_step a b x i)) = fst (fst x) + 3\<close>
  by (cases x) (simp add: add_step_def split_def Let_def)

lemma full_add_arith:
  \<open>of_bool ((p \<noteq> q) \<noteq> c) + 2 * of_bool (if p \<noteq> q then c else p) = of_bool p + of_bool q + (of_bool c :: nat)\<close>
  by (cases p; cases q; cases c) simp_all

lemma add_step_ok:
  assumes wf: \<open>wf_st s\<close> and a: \<open>unat (Lit_var (a ! i)) < fst s\<close> and b: \<open>unat (Lit_var (b ! i)) < fst s\<close>
    and c: \<open>unat (Lit_var c) < fst s\<close>
    and d: \<open>add_step a b (s, r, c) i = (s', r', c')\<close> and lt: \<open>fst s' < 2 ^ 64\<close>
  shows \<open>\<exists>x. r' = r @ [x] \<and> wf_st s' \<and> ext s s' \<and> unat (Lit_var x) < fst s' \<and> unat (Lit_var c') < fst s' \<and>
     (\<forall>\<sigma>. cnf_sem \<sigma> (snd s') \<longrightarrow> of_bool (lit_sem \<sigma> x) + 2 * of_bool (lit_sem \<sigma> c') =
        of_bool (lit_sem \<sigma> (a ! i)) + of_bool (lit_sem \<sigma> (b ! i)) + (of_bool (lit_sem \<sigma> c) :: nat))\<close>
proof -
  obtain s1 t where 1: \<open>xor_m s (a ! i) (b ! i) = (s1, t)\<close> by (cases \<open>xor_m s (a ! i) (b ! i)\<close>)
  obtain s2 x where 2: \<open>xor_m s1 t c = (s2, x)\<close> by (cases \<open>xor_m s1 t c\<close>)
  obtain s3 c1 where 3: \<open>ite_m s2 t c (a ! i) = (s3, c1)\<close> by (cases \<open>ite_m s2 t c (a ! i)\<close>)
  have e: \<open>s' = s3\<close> \<open>r' = r @ [x]\<close> \<open>c' = c1\<close> using d 1 2 3 by (simp_all add: add_step_def)
  have f: \<open>fst s1 = Suc (fst s)\<close> \<open>fst s2 = Suc (fst s1)\<close> \<open>fst s3 = Suc (fst s2)\<close>
    using 1 2 3 xor_fst[of s \<open>a ! i\<close> \<open>b ! i\<close>] xor_fst[of s1 t c] ite_fst[of s2 t c \<open>a ! i\<close>] by simp_all
  have l: \<open>fst s1 < 2 ^ 64\<close> \<open>fst s2 < 2 ^ 64\<close> \<open>fst s3 < 2 ^ 64\<close> using lt e f by simp_all
  have G1: \<open>wf_st s1\<close> \<open>ext s s1\<close> \<open>unat (Lit_var t) < fst s1\<close>
    \<open>\<forall>\<sigma>. cnf_sem \<sigma> (snd s1) \<longrightarrow> lit_sem \<sigma> t = (lit_sem \<sigma> (a ! i) \<noteq> lit_sem \<sigma> (b ! i))\<close>
    using xor_ok[OF wf a b 1 l(1)] by auto
  have c1': \<open>unat (Lit_var c) < fst s1\<close> using c f by simp
  have G2: \<open>wf_st s2\<close> \<open>ext s1 s2\<close> \<open>unat (Lit_var x) < fst s2\<close>
    \<open>\<forall>\<sigma>. cnf_sem \<sigma> (snd s2) \<longrightarrow> lit_sem \<sigma> x = (lit_sem \<sigma> t \<noteq> lit_sem \<sigma> c)\<close>
    using xor_ok[OF G1(1) G1(3) c1' 2 l(2)] by auto
  have v2: \<open>unat (Lit_var t) < fst s2\<close> \<open>unat (Lit_var c) < fst s2\<close> \<open>unat (Lit_var (a ! i)) < fst s2\<close>
    using G1(3) c a f by simp_all
  have G3: \<open>wf_st s3\<close> \<open>ext s2 s3\<close> \<open>unat (Lit_var c1) < fst s3\<close>
    \<open>\<forall>\<sigma>. cnf_sem \<sigma> (snd s3) \<longrightarrow> lit_sem \<sigma> c1 = (if lit_sem \<sigma> t then lit_sem \<sigma> c else lit_sem \<sigma> (a ! i))\<close>
    using ite_ok[OF G2(1) v2 3 l(3)] by auto
  have S: \<open>of_bool (lit_sem \<sigma> x) + 2 * of_bool (lit_sem \<sigma> c1) =
        of_bool (lit_sem \<sigma> (a ! i)) + of_bool (lit_sem \<sigma> (b ! i)) + (of_bool (lit_sem \<sigma> c) :: nat)\<close>
    if \<sigma>: \<open>cnf_sem \<sigma> (snd s3)\<close> for \<sigma>
  proof -
    have \<sigma>2: \<open>cnf_sem \<sigma> (snd s2)\<close> using ext_cnf_sem[OF G3(2) \<sigma>] .
    have \<sigma>1: \<open>cnf_sem \<sigma> (snd s1)\<close> using ext_cnf_sem[OF G2(2) \<sigma>2] .
    have \<open>lit_sem \<sigma> t = (lit_sem \<sigma> (a ! i) \<noteq> lit_sem \<sigma> (b ! i))\<close> using G1(4) \<sigma>1 by blast
    moreover have \<open>lit_sem \<sigma> x = (lit_sem \<sigma> t \<noteq> lit_sem \<sigma> c)\<close> using G2(4) \<sigma>2 by blast
    moreover have \<open>lit_sem \<sigma> c1 = (if lit_sem \<sigma> t then lit_sem \<sigma> c else lit_sem \<sigma> (a ! i))\<close> using G3(4) \<sigma> by blast
    ultimately show ?thesis using full_add_arith by simp
  qed
  have \<open>ext s s3\<close> using ext_trans[OF ext_trans[OF G1(2) G2(2)] G3(2)] .
  then show ?thesis using e G3 S G2(3) f by auto
qed

lemma add_inv_arith:
  fixes R TA TB Ci Y C2 A B C1 p :: nat
  assumes h1: \<open>R + p * C1 = TA + TB + Ci\<close> and h2: \<open>Y + 2 * C2 = A + B + C1\<close>
  shows \<open>(R + p * Y) + (2 * p) * C2 = (TA + p * A) + (TB + p * B) + Ci\<close>
proof -
  have \<open>(R + p * Y) + (2 * p) * C2 = R + p * (Y + 2 * C2)\<close> by (simp add: algebra_simps)
  also have \<open>\<dots> = R + p * (A + B + C1)\<close> using h2 by simp
  also have \<open>\<dots> = (R + p * C1) + p * A + p * B\<close> by (simp add: algebra_simps)
  also have \<open>\<dots> = (TA + TB + Ci) + p * A + p * B\<close> using h1 by simp
  also have \<open>\<dots> = (TA + p * A) + (TB + p * B) + Ci\<close> by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma add_m_mono: \<open>fst s \<le> fst (fst (add_m s a b cin))\<close>
  unfolding add_m_def by (rule foldl_mono) simp

lemma add_ok:
  assumes wf: \<open>wf_st s\<close> and la: \<open>lits_lt (fst s) a\<close> and lb: \<open>lits_lt (fst s) b\<close>
    and len: \<open>length b = length a\<close> and lc: \<open>unat (Lit_var cin) < fst s\<close>
    and d: \<open>add_m s a b cin = (s', r, c)\<close> and lt: \<open>fst s' < 2 ^ 64\<close>
  shows \<open>wf_st s' \<and> ext s s' \<and> lits_lt (fst s') r \<and> unat (Lit_var c) < fst s' \<and> length r = length a \<and>
     (\<forall>\<sigma>. cnf_sem \<sigma> (snd s') \<longrightarrow>
        val \<sigma> r + 2 ^ length a * of_bool (lit_sem \<sigma> c) = val \<sigma> a + val \<sigma> b + of_bool (lit_sem \<sigma> cin))\<close>
proof -
  let ?P = \<open>\<lambda>i (s1, r, c). fst s1 < 2 ^ 64 \<longrightarrow> wf_st s1 \<and> ext s s1 \<and> lits_lt (fst s1) r \<and>
     unat (Lit_var c) < fst s1 \<and> length r = i \<and>
     (\<forall>\<sigma>. cnf_sem \<sigma> (snd s1) \<longrightarrow> val \<sigma> r + 2 ^ i * of_bool (lit_sem \<sigma> c) =
        val \<sigma> (take i a) + val \<sigma> (take i b) + of_bool (lit_sem \<sigma> cin))\<close>
  have \<open>?P (length a) (foldl (add_step a b) (s, [], cin) [0..<length a])\<close>
  proof (rule foldl_upt_inv[where P = ?P])
    show \<open>?P 0 (s, [], cin)\<close> using wf lc by (simp add: ext_refl)
  next
    fix i x assume i: \<open>i < length a\<close> and P: \<open>?P i x\<close>
    obtain s1 r1 c1 where x: \<open>x = (s1, r1, c1)\<close> by (metis prod_cases3)
    obtain s2 r2 c2 where st: \<open>add_step a b (s1, r1, c1) i = (s2, r2, c2)\<close> by (metis prod_cases3)
    have f: \<open>fst s2 = fst s1 + 3\<close> using add_step_fst[of a b \<open>(s1, r1, c1)\<close> i] st by simp
    have B: \<open>wf_st s2 \<and> ext s s2 \<and> lits_lt (fst s2) r2 \<and> unat (Lit_var c2) < fst s2 \<and> length r2 = Suc i \<and>
     (\<forall>\<sigma>. cnf_sem \<sigma> (snd s2) \<longrightarrow> val \<sigma> r2 + 2 ^ Suc i * of_bool (lit_sem \<sigma> c2) =
        val \<sigma> (take (Suc i) a) + val \<sigma> (take (Suc i) b) + of_bool (lit_sem \<sigma> cin))\<close>
      if lt2: \<open>fst s2 < 2 ^ 64\<close>
    proof -
      have I: \<open>wf_st s1\<close> \<open>ext s s1\<close> \<open>lits_lt (fst s1) r1\<close> \<open>unat (Lit_var c1) < fst s1\<close> \<open>length r1 = i\<close>
        \<open>\<forall>\<sigma>. cnf_sem \<sigma> (snd s1) \<longrightarrow> val \<sigma> r1 + 2 ^ i * of_bool (lit_sem \<sigma> c1) =
          val \<sigma> (take i a) + val \<sigma> (take i b) + of_bool (lit_sem \<sigma> cin)\<close>
        using P x f lt2 by auto
      have le: \<open>fst s \<le> fst s1\<close> using ext_fst[OF I(2)] .
      have ai: \<open>unat (Lit_var (a ! i)) < fst s1\<close> using lits_lt_nth[OF la i] le by simp
      have bi: \<open>unat (Lit_var (b ! i)) < fst s1\<close> using lits_lt_nth[OF lb] i len le by fastforce
      obtain y where G: \<open>r2 = r1 @ [y]\<close> \<open>wf_st s2\<close> \<open>ext s1 s2\<close> \<open>unat (Lit_var y) < fst s2\<close>
        \<open>unat (Lit_var c2) < fst s2\<close>
        \<open>\<forall>\<sigma>. cnf_sem \<sigma> (snd s2) \<longrightarrow> of_bool (lit_sem \<sigma> y) + 2 * of_bool (lit_sem \<sigma> c2) =
          of_bool (lit_sem \<sigma> (a ! i)) + of_bool (lit_sem \<sigma> (b ! i)) + (of_bool (lit_sem \<sigma> c1) :: nat)\<close>
        using add_step_ok[OF I(1) ai bi I(4) st lt2] by blast
      have V: \<open>val \<sigma> r2 + 2 ^ Suc i * of_bool (lit_sem \<sigma> c2) =
          val \<sigma> (take (Suc i) a) + val \<sigma> (take (Suc i) b) + of_bool (lit_sem \<sigma> cin)\<close>
        if \<sigma>: \<open>cnf_sem \<sigma> (snd s2)\<close> for \<sigma>
      proof -
        have h1: \<open>val \<sigma> r1 + 2 ^ i * of_bool (lit_sem \<sigma> c1) =
            val \<sigma> (take i a) + val \<sigma> (take i b) + of_bool (lit_sem \<sigma> cin)\<close>
          using I(6) ext_cnf_sem[OF G(3) \<sigma>] by blast
        have h2: \<open>of_bool (lit_sem \<sigma> y) + 2 * of_bool (lit_sem \<sigma> c2) =
            of_bool (lit_sem \<sigma> (a ! i)) + of_bool (lit_sem \<sigma> (b ! i)) + (of_bool (lit_sem \<sigma> c1) :: nat)\<close>
          using G(6) \<sigma> by blast
        have ta: \<open>take (Suc i) a = take i a @ [a ! i]\<close> using i by (simp add: take_Suc_conv_app_nth)
        have tb: \<open>take (Suc i) b = take i b @ [b ! i]\<close> using i len by (simp add: take_Suc_conv_app_nth)
        have \<open>val \<sigma> r2 + 2 ^ Suc i * of_bool (lit_sem \<sigma> c2) =
            (val \<sigma> r1 + 2 ^ i * of_bool (lit_sem \<sigma> y)) + (2 * 2 ^ i) * of_bool (lit_sem \<sigma> c2)\<close>
          using G(1) I(5) by (simp add: val_snoc)
        also have \<open>\<dots> = (val \<sigma> (take i a) + 2 ^ i * of_bool (lit_sem \<sigma> (a ! i))) +
            (val \<sigma> (take i b) + 2 ^ i * of_bool (lit_sem \<sigma> (b ! i))) + of_bool (lit_sem \<sigma> cin)\<close>
          by (rule add_inv_arith[OF h1 h2])
        also have \<open>\<dots> = val \<sigma> (take (Suc i) a) + val \<sigma> (take (Suc i) b) + of_bool (lit_sem \<sigma> cin)\<close>
          using i len by (simp add: ta tb val_snoc)
        finally show ?thesis .
      qed
      show ?thesis using I G V ext_trans[OF I(2) G(3)] lits_lt_mono[OF I(3)] f by auto
    qed
    show \<open>?P (Suc i) (add_step a b x i)\<close> using B x st by simp
  qed
  then show ?thesis using d lt len by (simp add: add_m_def)
qed

lemma ult_m_mono: \<open>fst s \<le> fst (fst (ult_m s a b))\<close>
  using add_m_mono[of s a \<open>not_m b\<close> \<open>lconst True\<close>]
  by (simp add: ult_m_def split_def Let_def)

lemma ult_ok:
  assumes wf: \<open>wf_st s\<close> and la: \<open>lits_lt (fst s) a\<close> and lb: \<open>lits_lt (fst s) b\<close>
    and len: \<open>length b = length a\<close>
    and d: \<open>ult_m s a b = (s', x)\<close> and lt: \<open>fst s' < 2 ^ 64\<close>
  shows \<open>wf_st s' \<and> ext s s' \<and> unat (Lit_var x) < fst s' \<and>
         (\<forall>\<sigma>. cnf_sem \<sigma> (snd s') \<longrightarrow> lit_sem \<sigma> x = (val \<sigma> a < val \<sigma> b))\<close>
proof -
  obtain s1 r c where 1: \<open>add_m s a (not_m b) (lconst True) = (s1, r, c)\<close> by (metis prod_cases3)
  have e: \<open>s' = s1\<close> \<open>x = lneg c\<close> using d 1 by (simp_all add: ult_m_def)
  have nb: \<open>lits_lt (fst s) (not_m b)\<close> \<open>length (not_m b) = length a\<close>
    using not_correct[of \<open>fst s\<close> b] lb len by auto
  have lc: \<open>unat (Lit_var (lconst True)) < fst s\<close> using wf_st_pos[OF wf] by simp
  have A: \<open>wf_st s1\<close> \<open>ext s s1\<close> \<open>lits_lt (fst s1) r\<close> \<open>unat (Lit_var c) < fst s1\<close> \<open>length r = length a\<close>
     \<open>\<forall>\<sigma>. cnf_sem \<sigma> (snd s1) \<longrightarrow>
        val \<sigma> r + 2 ^ length a * of_bool (lit_sem \<sigma> c) = val \<sigma> a + val \<sigma> (not_m b) + of_bool (lit_sem \<sigma> (lconst True))\<close>
    using add_ok[OF wf la nb lc 1] lt e by auto
  have S: \<open>(\<not> lit_sem \<sigma> c) = (val \<sigma> a < val \<sigma> b)\<close> if \<sigma>: \<open>cnf_sem \<sigma> (snd s1)\<close> for \<sigma>
  proof -
    have h: \<open>val \<sigma> r + 2 ^ length a * of_bool (lit_sem \<sigma> c) = val \<sigma> a + (2 ^ length a - 1 - val \<sigma> b) + 1\<close>
      using A(6) \<sigma> lit_sem_lconst[OF A(1) \<sigma>] not_correct[of _ b \<sigma>] len by auto
    have r: \<open>val \<sigma> r < 2 ^ length a\<close> using val_lt[of \<sigma> r] A(5) by simp
    have b: \<open>val \<sigma> b < 2 ^ length a\<close> using val_lt[of \<sigma> b] len by simp
    show ?thesis
    proof (cases \<open>lit_sem \<sigma> c\<close>)
      case True then show ?thesis using h r b by (simp; linarith)
    next
      case False then show ?thesis using h r b by (simp; linarith)
    qed
  qed
  show ?thesis using A e S by auto
qed

subsection \<open>Equality\<close>

lemma eq_step_fst [simp]: \<open>fst (fst (eq_step a b x i)) = fst (fst x) + 2\<close>
  by (cases x) (simp add: eq_step_def split_def Let_def)

lemma eq_m_mono: \<open>fst s \<le> fst (fst (eq_m s a b))\<close>
  unfolding eq_m_def by (rule foldl_mono) simp

lemma eq_ok:
  assumes wf: \<open>wf_st s\<close> and la: \<open>lits_lt (fst s) a\<close> and lb: \<open>lits_lt (fst s) b\<close>
    and len: \<open>length b = length a\<close>
    and d: \<open>eq_m s a b = (s', x)\<close> and lt: \<open>fst s' < 2 ^ 64\<close>
  shows \<open>wf_st s' \<and> ext s s' \<and> unat (Lit_var x) < fst s' \<and>
         (\<forall>\<sigma>. cnf_sem \<sigma> (snd s') \<longrightarrow> lit_sem \<sigma> x = (val \<sigma> a = val \<sigma> b))\<close>
proof -
  let ?P = \<open>\<lambda>i (s1, r). fst s1 < 2 ^ 64 \<longrightarrow> wf_st s1 \<and> ext s s1 \<and> unat (Lit_var r) < fst s1 \<and>
     (\<forall>\<sigma>. cnf_sem \<sigma> (snd s1) \<longrightarrow> lit_sem \<sigma> r = (\<forall>j<i. lit_sem \<sigma> (a ! j) = lit_sem \<sigma> (b ! j)))\<close>
  have \<open>?P (length a) (foldl (eq_step a b) (s, lconst True) [0..<length a])\<close>
  proof (rule foldl_upt_inv[where P = ?P])
    show \<open>?P 0 (s, lconst True)\<close> using wf wf_st_pos[OF wf] lit_sem_lconst[OF wf] by (simp add: ext_refl)
  next
    fix i x assume i: \<open>i < length a\<close> and P: \<open>?P i x\<close>
    obtain s1 r where x: \<open>x = (s1, r)\<close> by (cases x)
    obtain s2 y where 1: \<open>xor_m s1 (a ! i) (b ! i) = (s2, y)\<close> by (cases \<open>xor_m s1 (a ! i) (b ! i)\<close>)
    obtain s3 r' where 2: \<open>and_m s2 r (lneg y) = (s3, r')\<close> by (cases \<open>and_m s2 r (lneg y)\<close>)
    have st: \<open>eq_step a b x i = (s3, r')\<close> using x 1 2 by (simp add: eq_step_def)
    have f: \<open>fst s2 = Suc (fst s1)\<close> \<open>fst s3 = Suc (fst s2)\<close>
      using 1 2 xor_fst[of s1 \<open>a ! i\<close> \<open>b ! i\<close>] and_fst[of s2 r \<open>lneg y\<close>] by simp_all
    have B: \<open>wf_st s3 \<and> ext s s3 \<and> unat (Lit_var r') < fst s3 \<and>
     (\<forall>\<sigma>. cnf_sem \<sigma> (snd s3) \<longrightarrow> lit_sem \<sigma> r' = (\<forall>j<Suc i. lit_sem \<sigma> (a ! j) = lit_sem \<sigma> (b ! j)))\<close>
      if lt3: \<open>fst s3 < 2 ^ 64\<close>
    proof -
      have I: \<open>wf_st s1\<close> \<open>ext s s1\<close> \<open>unat (Lit_var r) < fst s1\<close>
        \<open>\<forall>\<sigma>. cnf_sem \<sigma> (snd s1) \<longrightarrow> lit_sem \<sigma> r = (\<forall>j<i. lit_sem \<sigma> (a ! j) = lit_sem \<sigma> (b ! j))\<close>
        using P x f lt3 by auto
      have le: \<open>fst s \<le> fst s1\<close> using ext_fst[OF I(2)] .
      have ai: \<open>unat (Lit_var (a ! i)) < fst s1\<close> using lits_lt_nth[OF la i] le by simp
      have bi: \<open>unat (Lit_var (b ! i)) < fst s1\<close> using lits_lt_nth[OF lb] i len le by fastforce
      have G1: \<open>wf_st s2\<close> \<open>ext s1 s2\<close> \<open>unat (Lit_var y) < fst s2\<close>
        \<open>\<forall>\<sigma>. cnf_sem \<sigma> (snd s2) \<longrightarrow> lit_sem \<sigma> y = (lit_sem \<sigma> (a ! i) \<noteq> lit_sem \<sigma> (b ! i))\<close>
        using xor_ok[OF I(1) ai bi 1] lt3 f by auto
      have rr: \<open>unat (Lit_var r) < fst s2\<close> \<open>unat (Lit_var (lneg y)) < fst s2\<close> using I(3) G1(3) f by simp_all
      have G2: \<open>wf_st s3\<close> \<open>ext s2 s3\<close> \<open>unat (Lit_var r') < fst s3\<close>
        \<open>\<forall>\<sigma>. cnf_sem \<sigma> (snd s3) \<longrightarrow> lit_sem \<sigma> r' = (lit_sem \<sigma> r \<and> lit_sem \<sigma> (lneg y))\<close>
        using and_ok[OF G1(1) rr 2 lt3] by auto
      have S: \<open>lit_sem \<sigma> r' = (\<forall>j<Suc i. lit_sem \<sigma> (a ! j) = lit_sem \<sigma> (b ! j))\<close>
        if \<sigma>: \<open>cnf_sem \<sigma> (snd s3)\<close> for \<sigma>
      proof -
        have \<sigma>2: \<open>cnf_sem \<sigma> (snd s2)\<close> using ext_cnf_sem[OF G2(2) \<sigma>] .
        have \<sigma>1: \<open>cnf_sem \<sigma> (snd s1)\<close> using ext_cnf_sem[OF G1(2) \<sigma>2] .
        have \<open>lit_sem \<sigma> r' = ((\<forall>j<i. lit_sem \<sigma> (a ! j) = lit_sem \<sigma> (b ! j)) \<and> lit_sem \<sigma> (a ! i) = lit_sem \<sigma> (b ! i))\<close>
          using G2(4) G1(4) I(4) \<sigma> \<sigma>2 \<sigma>1 by auto
        then show ?thesis by (auto simp: less_Suc_eq)
      qed
      show ?thesis using G2 S ext_trans[OF I(2) ext_trans[OF G1(2) G2(2)]] by auto
    qed
    show \<open>?P (Suc i) (eq_step a b x i)\<close> using B st by simp
  qed
  then have \<open>?P (length a) (s', x)\<close> using d by (simp add: eq_m_def)
  then show ?thesis using lt val_eq_iff[OF len[symmetric]] by auto
qed

subsection \<open>Multiplication\<close>

lemma partial_eq:
  \<open>partial_m s a bi i =
    foldl (\<lambda>(s, r) j. let (s1, x) = (if j < i then (s, lconst False) else and_m s (a ! (j - i)) bi) in (s1, r @ [x]))
      (s, []) [0..<length a]\<close>
proof -
  have \<open>(\<lambda>(s, r) j. if j < i then (s, r @ [lconst False])
          else let (s1, x) = and_m s (a ! (j - i)) bi in (s1, r @ [x])) =
        (\<lambda>(s, r) j. let (s1, x) = (if j < i then (s, lconst False) else and_m s (a ! (j - i)) bi) in (s1, r @ [x]))\<close>
    by (intro ext) (auto simp: split_def Let_def)
  then show ?thesis by (simp add: partial_m_def)
qed

lemma partial_m_mono: \<open>fst s \<le> fst (fst (partial_m s a bi i))\<close>
  unfolding partial_eq by (rule map_gate_mono) simp

lemma partial_ok:
  assumes wf: \<open>wf_st s\<close> and la: \<open>lits_lt (fst s) a\<close> and lbi: \<open>unat (Lit_var bi) < fst s\<close>
    and d: \<open>partial_m s a bi i = (s', p)\<close> and lt: \<open>fst s' < 2 ^ 64\<close>
  shows \<open>wf_st s' \<and> ext s s' \<and> lits_lt (fst s') p \<and> length p = length a \<and>
         (\<forall>\<sigma>. cnf_sem \<sigma> (snd s') \<longrightarrow>
            val \<sigma> p = (if lit_sem \<sigma> bi then (val \<sigma> a * 2 ^ i) mod 2 ^ length a else 0))\<close>
proof -
  have L: \<open>wf_st s' \<and> ext s s' \<and> lits_lt (fst s') p \<and> length p = length a \<and>
         (\<forall>\<sigma>. cnf_sem \<sigma> (snd s') \<longrightarrow>
            map (lit_sem \<sigma>) p = map (\<lambda>j. i \<le> j \<and> lit_sem \<sigma> (a ! (j - i)) \<and> lit_sem \<sigma> bi) [0..<length a])\<close>
  proof (rule map_gate_loop[where g = \<open>\<lambda>s j. if j < i then (s, lconst False) else and_m s (a ! (j - i)) bi\<close>,
        OF _ _ wf _ lt])
    show \<open>fst s \<le> fst (fst (if j < i then (s, lconst False) else and_m s (a ! (j - i)) bi))\<close> for s j by simp
    show \<open>foldl (\<lambda>(s, r) j. let (s1, x) = (if j < i then (s, lconst False) else and_m s (a ! (j - i)) bi) in (s1, r @ [x]))
      (s, []) [0..<length a] = (s', p)\<close> using d by (simp add: partial_eq)
    fix s1 j s2 x
    assume w1: \<open>wf_st s1\<close> and le: \<open>fst s \<le> fst s1\<close> and j: \<open>j < length a\<close>
      and g: \<open>(if j < i then (s1, lconst False) else and_m s1 (a ! (j - i)) bi) = (s2, x)\<close>
      and lt2: \<open>fst s2 < 2 ^ 64\<close>
    show \<open>wf_st s2 \<and> ext s1 s2 \<and> unat (Lit_var x) < fst s2 \<and>
       (\<forall>\<sigma>. cnf_sem \<sigma> (snd s2) \<longrightarrow> lit_sem \<sigma> x = (i \<le> j \<and> lit_sem \<sigma> (a ! (j - i)) \<and> lit_sem \<sigma> bi))\<close>
    proof (cases \<open>j < i\<close>)
      case True
      then have \<open>s2 = s1\<close> \<open>x = lconst False\<close> using g by simp_all
      then show ?thesis using True w1 wf_st_pos[OF w1] lit_sem_lconst[OF w1] by (auto simp: ext_refl)
    next
      case False
      then have g': \<open>and_m s1 (a ! (j - i)) bi = (s2, x)\<close> using g by simp
      have aj: \<open>unat (Lit_var (a ! (j - i))) < fst s1\<close> using lits_lt_nth[OF la less_imp_diff_less[OF j, of i]] le by simp
      show ?thesis using and_ok[OF w1 aj _ g' lt2] lbi le False by auto
    qed
  qed
  have V: \<open>val \<sigma> p = (if lit_sem \<sigma> bi then (val \<sigma> a * 2 ^ i) mod 2 ^ length a else 0)\<close>
    if \<sigma>: \<open>cnf_sem \<sigma> (snd s')\<close> for \<sigma>
  proof -
    have \<open>val \<sigma> p = bits_nat (map (\<lambda>j. i \<le> j \<and> lit_sem \<sigma> (a ! (j - i)) \<and> lit_sem \<sigma> bi) [0..<length a])\<close>
      using L \<sigma> by (simp add: val_def)
    then show ?thesis
      by (cases \<open>lit_sem \<sigma> bi\<close>) (auto intro!: bit_eqI simp: bit_bits_nat_map bit_shl_mod bit_val)
  qed
  show ?thesis using L V by blast
qed

lemma mul_arith:
  \<open>((x * y) mod m + (if c then (x * 2 ^ i) mod m else 0)) mod m = (x * (y + 2 ^ i * of_bool c)) mod (m :: nat)\<close>
proof (cases c)
  case True
  have \<open>((x * y) mod m + (x * 2 ^ i) mod m) mod m = (x * y + x * 2 ^ i) mod m\<close> by (rule mod_add_eq)
  then show ?thesis using True by (simp add: distrib_left)
next
  case False then show ?thesis by simp
qed

lemma mul_step_m_mono: \<open>fst (fst x) \<le> fst (fst (mul_step a b x i))\<close>
proof -
  obtain s acc where x: \<open>x = (s, acc)\<close> by (cases x)
  obtain s1 p where 1: \<open>partial_m s a (b ! i) i = (s1, p)\<close> by (cases \<open>partial_m s a (b ! i) i\<close>)
  obtain s2 sm c where 2: \<open>add_m s1 acc p (lconst False) = (s2, sm, c)\<close> by (metis prod_cases3)
  have \<open>mul_step a b x i = (s2, sm)\<close> using x 1 2 by (simp add: mul_step_def)
  moreover have \<open>fst s \<le> fst s1\<close> using partial_m_mono[of s a \<open>b ! i\<close> i] 1 by simp
  moreover have \<open>fst s1 \<le> fst s2\<close> using add_m_mono[of s1 acc p \<open>lconst False\<close>] 2 by simp
  ultimately show ?thesis using x by simp
qed

lemma mul_m_mono: \<open>fst s \<le> fst (fst (mul_m s a b))\<close>
  unfolding mul_m_def by (rule foldl_mono) (rule mul_step_m_mono)

lemma mul_ok:
  assumes wf: \<open>wf_st s\<close> and la: \<open>lits_lt (fst s) a\<close> and lb: \<open>lits_lt (fst s) b\<close>
    and len: \<open>length b = length a\<close>
    and d: \<open>mul_m s a b = (s', r)\<close> and lt: \<open>fst s' < 2 ^ 64\<close>
  shows \<open>wf_st s' \<and> ext s s' \<and> lits_lt (fst s') r \<and> length r = length a \<and>
         (\<forall>\<sigma>. cnf_sem \<sigma> (snd s') \<longrightarrow> val \<sigma> r = (val \<sigma> a * val \<sigma> b) mod 2 ^ length a)\<close>
proof -
  let ?n = \<open>length a\<close>
  let ?P = \<open>\<lambda>i (s1, acc). fst s1 < 2 ^ 64 \<longrightarrow> wf_st s1 \<and> ext s s1 \<and> lits_lt (fst s1) acc \<and> length acc = ?n \<and>
     (\<forall>\<sigma>. cnf_sem \<sigma> (snd s1) \<longrightarrow> val \<sigma> acc = (val \<sigma> a * val \<sigma> (take i b)) mod 2 ^ ?n)\<close>
  have \<open>?P ?n (foldl (mul_step a b) (s, replicate ?n (lconst False)) [0..<?n])\<close>
  proof (rule foldl_upt_inv[where P = ?P])
    have \<open>val \<sigma> (replicate ?n (lconst False)) = 0\<close> if \<open>cnf_sem \<sigma> (snd s)\<close> for \<sigma>
      using lit_sem_lconst[OF wf that] by (simp add: val_def)
    then show \<open>?P 0 (s, replicate ?n (lconst False))\<close>
      using wf wf_st_pos[OF wf] by (simp add: ext_refl lits_lt_def)
  next
    fix i x assume i: \<open>i < ?n\<close> and P: \<open>?P i x\<close>
    obtain s1 acc where x: \<open>x = (s1, acc)\<close> by (cases x)
    obtain s2 p where 1: \<open>partial_m s1 a (b ! i) i = (s2, p)\<close> by (cases \<open>partial_m s1 a (b ! i) i\<close>)
    obtain s3 sm c where 2: \<open>add_m s2 acc p (lconst False) = (s3, sm, c)\<close> by (metis prod_cases3)
    have st: \<open>mul_step a b x i = (s3, sm)\<close> using x 1 2 by (simp add: mul_step_def)
    have m1: \<open>fst s1 \<le> fst s2\<close> using partial_m_mono[of s1 a \<open>b ! i\<close> i] 1 by simp
    have m2: \<open>fst s2 \<le> fst s3\<close> using add_m_mono[of s2 acc p \<open>lconst False\<close>] 2 by simp
    have B: \<open>wf_st s3 \<and> ext s s3 \<and> lits_lt (fst s3) sm \<and> length sm = ?n \<and>
     (\<forall>\<sigma>. cnf_sem \<sigma> (snd s3) \<longrightarrow> val \<sigma> sm = (val \<sigma> a * val \<sigma> (take (Suc i) b)) mod 2 ^ ?n)\<close>
      if lt3: \<open>fst s3 < 2 ^ 64\<close>
    proof -
      have I: \<open>wf_st s1\<close> \<open>ext s s1\<close> \<open>lits_lt (fst s1) acc\<close> \<open>length acc = ?n\<close>
        \<open>\<forall>\<sigma>. cnf_sem \<sigma> (snd s1) \<longrightarrow> val \<sigma> acc = (val \<sigma> a * val \<sigma> (take i b)) mod 2 ^ ?n\<close>
        using P x m1 m2 lt3 by auto
      have le: \<open>fst s \<le> fst s1\<close> using ext_fst[OF I(2)] .
      have bi: \<open>unat (Lit_var (b ! i)) < fst s1\<close> using lits_lt_nth[OF lb] i len le by fastforce
      have G1: \<open>wf_st s2\<close> \<open>ext s1 s2\<close> \<open>lits_lt (fst s2) p\<close> \<open>length p = ?n\<close>
        \<open>\<forall>\<sigma>. cnf_sem \<sigma> (snd s2) \<longrightarrow>
            val \<sigma> p = (if lit_sem \<sigma> (b ! i) then (val \<sigma> a * 2 ^ i) mod 2 ^ ?n else 0)\<close>
        using partial_ok[OF I(1) lits_lt_mono[OF la le] bi 1] lt3 m2 by auto
      have lc: \<open>unat (Lit_var (lconst False)) < fst s2\<close> using wf_st_pos[OF G1(1)] by simp
      have G2: \<open>wf_st s3\<close> \<open>ext s2 s3\<close> \<open>lits_lt (fst s3) sm\<close> \<open>length sm = ?n\<close>
        \<open>\<forall>\<sigma>. cnf_sem \<sigma> (snd s3) \<longrightarrow>
          val \<sigma> sm + 2 ^ length acc * of_bool (lit_sem \<sigma> c) = val \<sigma> acc + val \<sigma> p + of_bool (lit_sem \<sigma> (lconst False))\<close>
        using add_ok[OF G1(1) lits_lt_mono[OF I(3) m1] G1(3) _ lc 2 lt3] G1(4) I(4) by auto
      have S: \<open>val \<sigma> sm = (val \<sigma> a * val \<sigma> (take (Suc i) b)) mod 2 ^ ?n\<close> if \<sigma>: \<open>cnf_sem \<sigma> (snd s3)\<close> for \<sigma>
      proof -
        have \<sigma>2: \<open>cnf_sem \<sigma> (snd s2)\<close> using ext_cnf_sem[OF G2(2) \<sigma>] .
        have \<sigma>1: \<open>cnf_sem \<sigma> (snd s1)\<close> using ext_cnf_sem[OF G1(2) \<sigma>2] .
        have h: \<open>val \<sigma> sm + 2 ^ ?n * of_bool (lit_sem \<sigma> c) = val \<sigma> acc + val \<sigma> p\<close>
          using G2(5) \<sigma> lit_sem_lconst[OF G2(1) \<sigma>] I(4) by simp
        have smlt: \<open>val \<sigma> sm < 2 ^ ?n\<close> using val_lt[of \<sigma> sm] G2(4) by simp
        have \<open>val \<sigma> sm = (val \<sigma> acc + val \<sigma> p) mod 2 ^ ?n\<close>
          by (rule mod_of_carry[OF h smlt])
        also have \<open>\<dots> = ((val \<sigma> a * val \<sigma> (take i b)) mod 2 ^ ?n +
            (if lit_sem \<sigma> (b ! i) then (val \<sigma> a * 2 ^ i) mod 2 ^ ?n else 0)) mod 2 ^ ?n\<close>
          using I(5) G1(5) \<sigma>1 \<sigma>2 by simp
        also have \<open>\<dots> = (val \<sigma> a * (val \<sigma> (take i b) + 2 ^ i * of_bool (lit_sem \<sigma> (b ! i)))) mod 2 ^ ?n\<close>
          by (rule mul_arith)
        also have \<open>\<dots> = (val \<sigma> a * val \<sigma> (take (Suc i) b)) mod 2 ^ ?n\<close>
          using i len by (simp add: take_Suc_conv_app_nth val_snoc)
        finally show ?thesis .
      qed
      show ?thesis using G2 S ext_trans[OF I(2) ext_trans[OF G1(2) G2(2)]] by auto
    qed
    show \<open>?P (Suc i) (mul_step a b x i)\<close> using B st by simp
  qed
  then show ?thesis using d lt len by (simp add: mul_m_def)
qed

subsection \<open>Shifts\<close>

lemma lconst_bit: \<open>(k div 2 ^ i mod 2 = 1) = bit (k :: nat) i\<close>
  by (simp only: bit_iff_odd odd_iff_mod_2_eq_one)

lemma of_nat_m_ok:
  assumes wf: \<open>wf_st s\<close>
  shows \<open>lits_lt (fst s) (of_nat_m k w) \<and> length (of_nat_m k w) = w \<and>
         (\<forall>\<sigma>. cnf_sem \<sigma> (snd s) \<longrightarrow> val \<sigma> (of_nat_m k w) = k mod 2 ^ w)\<close>
proof -
  have \<open>val \<sigma> (of_nat_m k w) = k mod 2 ^ w\<close> if \<sigma>: \<open>cnf_sem \<sigma> (snd s)\<close> for \<sigma>
  proof -
    have m: \<open>map (lit_sem \<sigma>) (of_nat_m k w) = map (bit k) [0..<w]\<close>
      unfolding of_nat_m_def map_map comp_def lconst_bit
      by (rule map_cong[OF refl]) (rule lit_sem_lconst[OF wf \<sigma>])
    show ?thesis unfolding val_def m
      by (rule bit_eqI) (simp add: bit_bits_nat_map bit_mod_pow)
  qed
  then show ?thesis using wf_st_pos[OF wf] by (simp add: of_nat_m_def lits_lt_def)
qed

definition shv :: \<open>bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>shv left n x y = (if left then (x * 2 ^ y) mod 2 ^ n else x div 2 ^ y)\<close>

lemma shift_const_ok:
  assumes wf: \<open>wf_st s\<close> and la: \<open>lits_lt (fst s) a\<close>
  shows \<open>lits_lt (fst s) (shift_const_m a k left) \<and> length (shift_const_m a k left) = length a \<and>
         (\<forall>\<sigma>. cnf_sem \<sigma> (snd s) \<longrightarrow> val \<sigma> (shift_const_m a k left) = shv left (length a) (val \<sigma> a) k)\<close>
proof (intro conjI allI impI)
  have n: \<open>unat (Lit_var (a ! m)) < fst s\<close> if \<open>m < length a\<close> for m using lits_lt_nth[OF la that] .
  have n1: \<open>unat (Lit_var (a ! (j - m))) < fst s\<close> if \<open>j < length a\<close> for j m
    using n[OF less_imp_diff_less[OF that]] .
  have n2: \<open>unat (Lit_var (a ! (j + k))) < fst s\<close> if \<open>k < length a - j\<close> for j
    using n[of \<open>j + k\<close>] that by simp
  show \<open>lits_lt (fst s) (shift_const_m a k left)\<close>
    unfolding lits_lt_def shift_const_m_def using n1 n2 wf_st_pos[OF wf] by auto
  show \<open>length (shift_const_m a k left) = length a\<close> by (simp add: shift_const_m_def)
  fix \<sigma> assume \<sigma>: \<open>cnf_sem \<sigma> (snd s)\<close>
  have m: \<open>map (lit_sem \<sigma>) (shift_const_m a k left) =
     map (\<lambda>j. if left then k \<le> j \<and> lit_sem \<sigma> (a ! (j - k)) else k + j < length a \<and> lit_sem \<sigma> (a ! (k + j)))
       [0..<length a]\<close>
    unfolding shift_const_m_def map_map comp_def
    by (rule map_cong[OF refl]) (use lit_sem_lconst[OF wf \<sigma>] in \<open>auto simp: less_diff_conv add.commute\<close>)
  show \<open>val \<sigma> (shift_const_m a k left) = shv left (length a) (val \<sigma> a) k\<close>
  proof (rule bit_eqI)
    fix j
    show \<open>bit (val \<sigma> (shift_const_m a k left)) j = bit (shv left (length a) (val \<sigma> a) k) j\<close>
      unfolding val_def[of _ \<open>shift_const_m a k left\<close>] m
      by (cases left) (auto simp: bit_bits_nat_map shv_def bit_shl_mod bit_div_pow bit_val)
  qed
qed

lemma shv_comp:
  \<open>x < 2 ^ n \<Longrightarrow> shv left n (shv left n x y1) y2 = shv left n x (y1 + y2)\<close>
  by (cases left) (simp_all add: shv_def mod_mult_left_eq power_add mult.assoc div_mult2_eq)

lemma shv_big: \<open>x < 2 ^ n \<Longrightarrow> n \<le> y \<Longrightarrow> shv left n x y = 0\<close>
proof (cases left)
  case True
  assume \<open>n \<le> y\<close>
  then have \<open>(2::nat) ^ n dvd 2 ^ y\<close> by (simp add: le_imp_power_dvd)
  then have \<open>(2::nat) ^ n dvd x * 2 ^ y\<close> by (rule dvd_mult)
  then show ?thesis using True by (simp add: shv_def dvd_eq_mod_eq_0)
next
  case False
  assume x: \<open>x < 2 ^ n\<close> and y: \<open>n \<le> y\<close>
  have \<open>(2::nat) ^ n \<le> 2 ^ y\<close> using y by simp
  then have \<open>x < 2 ^ y\<close> using x by linarith
  then show ?thesis using False by (simp add: shv_def div_less)
qed

lemma shv_lt: \<open>x < 2 ^ n \<Longrightarrow> shv left n x y < 2 ^ n\<close>
  by (cases left) (auto simp: shv_def intro: le_less_trans[OF div_le_dividend])

lemma val_eq_0_iff: \<open>val \<sigma> xs = 0 \<longleftrightarrow> (\<forall>l \<in> set xs. \<not> lit_sem \<sigma> l)\<close>
proof (induction xs rule: rev_induct)
  case (snoc x xs)
  then show ?case by (auto simp: val_snoc)
qed simp

lemma val_take_drop: \<open>val \<sigma> b = val \<sigma> (take m b) + 2 ^ min m (length b) * val \<sigma> (drop m b)\<close>
  using val_append[of \<sigma> \<open>take m b\<close> \<open>drop m b\<close>] by (simp add: min.commute)

lemma val_take_Suc:
  \<open>k < length b \<Longrightarrow> val \<sigma> (take (Suc k) b) = val \<sigma> (take k b) + 2 ^ k * of_bool (lit_sem \<sigma> (b ! k))\<close>
  by (simp add: take_Suc_conv_app_nth val_snoc min_def)

lemma shift_step_m_mono: \<open>fst (fst x) \<le> fst (fst (shift_step a b left x k))\<close>
proof -
  obtain s r g p where x: \<open>x = (s, r, g, p)\<close> by (cases x)
  show ?thesis
  proof (cases \<open>p < length a\<close>)
    case True
    then show ?thesis using x ite_vec_m_mono[of s \<open>b ! k\<close> \<open>shift_const_m r p left\<close> r]
      by (simp add: shift_step_def split_def Let_def)
  next
    case False
    then show ?thesis using x by (simp add: shift_step_def split_def Let_def or_m_def and_m_def fresh_m_def addc_m_def)
  qed
qed

lemma shift_ok:
  assumes wf: \<open>wf_st s\<close> and la: \<open>lits_lt (fst s) a\<close> and lb: \<open>lits_lt (fst s) b\<close>
    and len: \<open>length b = length a\<close>
    and d: \<open>shift_m s a b left = (s', r)\<close> and lt: \<open>fst s' < 2 ^ 64\<close>
  shows \<open>wf_st s' \<and> ext s s' \<and> lits_lt (fst s') r \<and> length r = length a \<and>
         (\<forall>\<sigma>. cnf_sem \<sigma> (snd s') \<longrightarrow>
            val \<sigma> r = (if val \<sigma> b < length a then shv left (length a) (val \<sigma> a) (val \<sigma> b) else 0))\<close>
proof -
  let ?n = \<open>length a\<close>
  define m where \<open>m = (LEAST i. ?n \<le> 2 ^ i)\<close>
  have nn: \<open>?n \<le> 2 ^ ?n\<close> using less_exp[of ?n] by simp
  have m_le: \<open>m \<le> ?n\<close> unfolding m_def using nn by (rule Least_le)
  have m_ge: \<open>?n \<le> 2 ^ m\<close> unfolding m_def using nn by (rule LeastI)
  have stage: \<open>2 ^ i < ?n \<longleftrightarrow> i < m\<close> for i
  proof
    assume \<open>2 ^ i < ?n\<close>
    then show \<open>i < m\<close> using m_ge by (metis le_less_trans not_less power_increasing_iff one_less_numeral_iff semiring_norm(76))
  next
    assume \<open>i < m\<close>
    then show \<open>2 ^ i < ?n\<close> unfolding m_def using not_less_Least by fastforce
  qed
  define lo where \<open>lo k = min k m\<close> for k
  let ?P = \<open>\<lambda>k (s1, r1, g1, p1). fst s1 < 2 ^ 64 \<longrightarrow>
     wf_st s1 \<and> ext s s1 \<and> lits_lt (fst s1) r1 \<and> length r1 = ?n \<and> lits_lt (fst s1) [g1] \<and>
     (2 ^ k < ?n \<longrightarrow> p1 = 2 ^ k) \<and> (\<not> 2 ^ k < ?n \<longrightarrow> ?n \<le> p1) \<and>
     (\<forall>\<sigma>. cnf_sem \<sigma> (snd s1) \<longrightarrow>
        val \<sigma> r1 = shv left ?n (val \<sigma> a) (val \<sigma> (take (lo k) b)) \<and>
        lit_sem \<sigma> g1 = (\<exists>i. lo k \<le> i \<and> i < k \<and> lit_sem \<sigma> (b ! i)))\<close>
  have F: \<open>?P ?n (foldl (shift_step a b left) (s, shift_const_m a 0 left, lconst False, 1) [0..<?n])\<close>
  proof (rule foldl_upt_inv[where P = ?P])
    have C0: \<open>lits_lt (fst s) (shift_const_m a 0 left)\<close> \<open>length (shift_const_m a 0 left) = ?n\<close>
      \<open>\<forall>\<sigma>. cnf_sem \<sigma> (snd s) \<longrightarrow> val \<sigma> (shift_const_m a 0 left) = shv left ?n (val \<sigma> a) 0\<close>
      using shift_const_ok[OF wf la] by auto
    have g0: \<open>lits_lt (fst s) [lconst False]\<close> using wf_st_pos[OF wf] by (simp add: lits_lt_def)
    have \<open>lit_sem \<sigma> (lconst False) = False\<close> if \<open>cnf_sem \<sigma> (snd s)\<close> for \<sigma> using lit_sem_lconst[OF wf that] .
    then show \<open>?P 0 (s, shift_const_m a 0 left, lconst False, 1)\<close>
      using wf C0 g0 by (auto simp: ext_refl lo_def)
  next
    fix k x assume k: \<open>k < ?n\<close> and P: \<open>?P k x\<close>
    obtain s1 r1 g1 p1 where x: \<open>x = (s1, r1, g1, p1)\<close> by (cases x)
    show \<open>?P (Suc k) (shift_step a b left x k)\<close>
    proof (cases \<open>2 ^ k < ?n\<close>)
      case True
      have km: \<open>k < m\<close> using stage True by blast
      show ?thesis
      proof (cases \<open>fst s1 < 2 ^ 64\<close>)
        case False
        have \<open>fst s1 \<le> fst (fst (shift_step a b left x k))\<close> using shift_step_m_mono[of x a b left k] x by simp
        then show ?thesis using False by (cases \<open>shift_step a b left x k\<close>) auto
      next
        case lt1: True
        have p1: \<open>p1 = 2 ^ k\<close> using P x True lt1 by simp
      obtain s3 r' where 2: \<open>ite_vec_m s1 (b ! k) (shift_const_m r1 p1 left) r1 = (s3, r')\<close>
        by (cases \<open>ite_vec_m s1 (b ! k) (shift_const_m r1 p1 left) r1\<close>)
      have m2: \<open>fst s1 \<le> fst s3\<close> using ite_vec_m_mono[of s1 \<open>b ! k\<close> \<open>shift_const_m r1 p1 left\<close> r1] 2 by simp
      define p' where \<open>p' = (if p1 \<le> ?n - p1 then p1 + p1 else ?n)\<close>
      have st: \<open>shift_step a b left x k = (s3, r', g1, p')\<close>
        using x 2 True p1 by (simp add: shift_step_def p'_def)
      show ?thesis unfolding st prod.case
      proof
        assume lt3: \<open>fst s3 < 2 ^ 64\<close>
        have I: \<open>wf_st s1\<close> \<open>ext s s1\<close> \<open>lits_lt (fst s1) r1\<close> \<open>length r1 = ?n\<close> \<open>lits_lt (fst s1) [g1]\<close>
          \<open>\<forall>\<sigma>. cnf_sem \<sigma> (snd s1) \<longrightarrow>
             val \<sigma> r1 = shv left ?n (val \<sigma> a) (val \<sigma> (take (lo k) b)) \<and>
             lit_sem \<sigma> g1 = (\<exists>i. lo k \<le> i \<and> i < k \<and> lit_sem \<sigma> (b ! i))\<close>
          using P x lt1 by auto
        have le: \<open>fst s \<le> fst s1\<close> using ext_fst[OF I(2)] .
        have bk: \<open>lits_lt (fst s1) [b ! k]\<close> using lits_lt_mono[OF lb le] k len by (auto simp: lits_lt_def)
        have C: \<open>lits_lt (fst s1) (shift_const_m r1 p1 left)\<close> \<open>length (shift_const_m r1 p1 left) = ?n\<close>
          \<open>\<forall>\<sigma>. cnf_sem \<sigma> (snd s1) \<longrightarrow> val \<sigma> (shift_const_m r1 p1 left) = shv left ?n (val \<sigma> r1) p1\<close>
          using shift_const_ok[OF I(1) I(3)] I(4) by auto
        have G: \<open>wf_st s3\<close> \<open>ext s1 s3\<close> \<open>lits_lt (fst s3) r'\<close> \<open>length r' = ?n\<close>
          \<open>\<forall>\<sigma>. cnf_sem \<sigma> (snd s3) \<longrightarrow>
             val \<sigma> r' = (if lit_sem \<sigma> (b ! k) then val \<sigma> (shift_const_m r1 p1 left) else val \<sigma> r1)\<close>
          using ite_vec_correct[OF I(1) bk C(1) I(3) _ 2 lt3] C(2) I(4) by auto
        have lok: \<open>lo k = k\<close> \<open>lo (Suc k) = Suc k\<close> using km by (simp_all add: lo_def)
        have S: \<open>val \<sigma> r' = shv left ?n (val \<sigma> a) (val \<sigma> (take (lo (Suc k)) b)) \<and>
                 lit_sem \<sigma> g1 = (\<exists>i. lo (Suc k) \<le> i \<and> i < Suc k \<and> lit_sem \<sigma> (b ! i))\<close>
          if \<sigma>: \<open>cnf_sem \<sigma> (snd s3)\<close> for \<sigma>
        proof -
          have \<sigma>1: \<open>cnf_sem \<sigma> (snd s1)\<close> using ext_cnf_sem[OF G(2) \<sigma>] .
          have r1: \<open>val \<sigma> r1 = shv left ?n (val \<sigma> a) (val \<sigma> (take k b))\<close>
            and g: \<open>lit_sem \<sigma> g1 = (\<exists>i. k \<le> i \<and> i < k \<and> lit_sem \<sigma> (b ! i))\<close> using I(6) \<sigma>1 lok by auto
          have tk: \<open>val \<sigma> (take (Suc k) b) = val \<sigma> (take k b) + 2 ^ k * of_bool (lit_sem \<sigma> (b ! k))\<close>
            using val_take_Suc[of k b \<sigma>] k len by simp
          have va: \<open>val \<sigma> a < 2 ^ ?n\<close> by (rule val_lt)
          have \<open>val \<sigma> r' = (if lit_sem \<sigma> (b ! k) then shv left ?n (val \<sigma> r1) (2 ^ k) else val \<sigma> r1)\<close>
            using G(5) C(3) \<sigma> \<sigma>1 p1 by simp
          then have \<open>val \<sigma> r' = shv left ?n (val \<sigma> a) (val \<sigma> (take (Suc k) b))\<close>
            using r1 tk shv_comp[OF va] by auto
          then show ?thesis using g lok by auto
        qed
        have pn: \<open>(2 ^ Suc k < ?n \<longrightarrow> p' = 2 ^ Suc k) \<and> (\<not> 2 ^ Suc k < ?n \<longrightarrow> ?n \<le> p')\<close>
          using p1 by (auto simp: p'_def)
        show \<open>wf_st s3 \<and> ext s s3 \<and> lits_lt (fst s3) r' \<and> length r' = ?n \<and> lits_lt (fst s3) [g1] \<and>
          (2 ^ Suc k < ?n \<longrightarrow> p' = 2 ^ Suc k) \<and> (\<not> 2 ^ Suc k < ?n \<longrightarrow> ?n \<le> p') \<and>
          (\<forall>\<sigma>. cnf_sem \<sigma> (snd s3) \<longrightarrow>
             val \<sigma> r' = shv left ?n (val \<sigma> a) (val \<sigma> (take (lo (Suc k)) b)) \<and>
             lit_sem \<sigma> g1 = (\<exists>i. lo (Suc k) \<le> i \<and> i < Suc k \<and> lit_sem \<sigma> (b ! i)))\<close>
          using G S pn ext_trans[OF I(2) G(2)] lits_lt_mono[OF I(5) m2] by auto
      qed
      qed
    next
      case False
      have km: \<open>m \<le> k\<close> using stage False by (meson not_less)
      have np: \<open>?n \<le> p1\<close> if \<open>fst s1 < 2 ^ 64\<close> using P x False that by simp
      obtain s3 h where 2: \<open>or_m s1 g1 (b ! k) = (s3, h)\<close> by (cases \<open>or_m s1 g1 (b ! k)\<close>)
      have m2: \<open>fst s1 \<le> fst s3\<close> using 2 by (auto simp: or_m_def and_m_def fresh_m_def addc_m_def split_def Let_def)
      have st: \<open>shift_step a b left x k = (s3, r1, h, p1)\<close> if \<open>fst s1 < 2 ^ 64\<close>
        using x 2 np[OF that] by (simp add: shift_step_def)
      have st': \<open>\<not> p1 < ?n\<close> if \<open>fst s1 < 2 ^ 64\<close> using np[OF that] by simp
      show ?thesis
      proof (cases \<open>fst s1 < 2 ^ 64\<close>)
        case False
        have \<open>fst s1 \<le> fst (fst (shift_step a b left x k))\<close> using shift_step_m_mono[of x a b left k] x by simp
        then show ?thesis using False by (cases \<open>shift_step a b left x k\<close>) auto
      next
        case lt1: True
        show ?thesis unfolding st[OF lt1] prod.case
        proof
          assume lt3: \<open>fst s3 < 2 ^ 64\<close>
          have I: \<open>wf_st s1\<close> \<open>ext s s1\<close> \<open>lits_lt (fst s1) r1\<close> \<open>length r1 = ?n\<close> \<open>lits_lt (fst s1) [g1]\<close>
            \<open>\<forall>\<sigma>. cnf_sem \<sigma> (snd s1) \<longrightarrow>
               val \<sigma> r1 = shv left ?n (val \<sigma> a) (val \<sigma> (take (lo k) b)) \<and>
               lit_sem \<sigma> g1 = (\<exists>i. lo k \<le> i \<and> i < k \<and> lit_sem \<sigma> (b ! i))\<close>
            using P x lt1 by auto
          have le: \<open>fst s \<le> fst s1\<close> using ext_fst[OF I(2)] .
          have bk: \<open>unat (Lit_var (b ! k)) < fst s1\<close> using lits_lt_mono[OF lb le] k len by (auto simp: lits_lt_def)
          have gk: \<open>unat (Lit_var g1) < fst s1\<close> using I(5) by (simp add: lits_lt_def)
          have O: \<open>wf_st s3\<close> \<open>ext s1 s3\<close> \<open>unat (Lit_var h) < fst s3\<close>
            \<open>\<forall>\<sigma>. cnf_sem \<sigma> (snd s3) \<longrightarrow> lit_sem \<sigma> h = (lit_sem \<sigma> g1 \<or> lit_sem \<sigma> (b ! k))\<close>
            using or_ok[OF I(1) gk bk 2 lt3] by auto
          have lok: \<open>lo (Suc k) = lo k\<close> \<open>lo k = m\<close> using km by (simp_all add: lo_def)
          have S: \<open>lit_sem \<sigma> h = (\<exists>i. lo (Suc k) \<le> i \<and> i < Suc k \<and> lit_sem \<sigma> (b ! i))\<close>
            if \<sigma>: \<open>cnf_sem \<sigma> (snd s3)\<close> for \<sigma>
          proof -
            have \<sigma>1: \<open>cnf_sem \<sigma> (snd s1)\<close> using ext_cnf_sem[OF O(2) \<sigma>] .
            have \<open>lit_sem \<sigma> g1 = (\<exists>i. m \<le> i \<and> i < k \<and> lit_sem \<sigma> (b ! i))\<close> using I(6) \<sigma>1 lok by auto
            then show ?thesis using O(4) \<sigma> lok km by (auto simp: less_Suc_eq)
          qed
          have pn: \<open>\<not> 2 ^ Suc k < ?n\<close> using stage[of \<open>Suc k\<close>] km by simp
          show \<open>wf_st s3 \<and> ext s s3 \<and> lits_lt (fst s3) r1 \<and> length r1 = ?n \<and> lits_lt (fst s3) [h] \<and>
            (2 ^ Suc k < ?n \<longrightarrow> p1 = 2 ^ Suc k) \<and> (\<not> 2 ^ Suc k < ?n \<longrightarrow> ?n \<le> p1) \<and>
            (\<forall>\<sigma>. cnf_sem \<sigma> (snd s3) \<longrightarrow>
               val \<sigma> r1 = shv left ?n (val \<sigma> a) (val \<sigma> (take (lo (Suc k)) b)) \<and>
               lit_sem \<sigma> h = (\<exists>i. lo (Suc k) \<le> i \<and> i < Suc k \<and> lit_sem \<sigma> (b ! i)))\<close>
            using O S pn np[OF lt1] I ext_trans[OF I(2) O(2)] lits_lt_mono[OF I(3) m2] lok
              ext_cnf_sem[OF O(2)] by (auto simp: lits_lt_def)
        qed
      qed
    qed
  qed
  obtain s1 r1 g1 p1 where f: \<open>foldl (shift_step a b left) (s, shift_const_m a 0 left, lconst False, 1) [0..<?n] = (s1, r1, g1, p1)\<close>
    by (cases \<open>foldl (shift_step a b left) (s, shift_const_m a 0 left, lconst False, 1) [0..<?n]\<close>)
  have d2: \<open>ite_vec_m s1 g1 (replicate ?n (lconst False)) r1 = (s', r)\<close>
    using d f len by (simp add: shift_m_def)
  have m3: \<open>fst s1 \<le> fst s'\<close> using ite_vec_m_mono[of s1 g1 \<open>replicate ?n (lconst False)\<close> r1] d2 by simp
  have lt1: \<open>fst s1 < 2 ^ 64\<close> using m3 lt by simp
  have I: \<open>wf_st s1\<close> \<open>ext s s1\<close> \<open>lits_lt (fst s1) r1\<close> \<open>length r1 = ?n\<close> \<open>lits_lt (fst s1) [g1]\<close>
    \<open>\<forall>\<sigma>. cnf_sem \<sigma> (snd s1) \<longrightarrow>
       val \<sigma> r1 = shv left ?n (val \<sigma> a) (val \<sigma> (take (lo ?n) b)) \<and>
       lit_sem \<sigma> g1 = (\<exists>i. lo ?n \<le> i \<and> i < ?n \<and> lit_sem \<sigma> (b ! i))\<close>
    using F f lt1 by auto
  have z: \<open>lits_lt (fst s1) (replicate ?n (lconst False))\<close> using wf_st_pos[OF I(1)] by (simp add: lits_lt_def)
  have G: \<open>wf_st s'\<close> \<open>ext s1 s'\<close> \<open>lits_lt (fst s') r\<close> \<open>length r = ?n\<close>
    \<open>\<forall>\<sigma>. cnf_sem \<sigma> (snd s') \<longrightarrow>
       val \<sigma> r = (if lit_sem \<sigma> g1 then val \<sigma> (replicate ?n (lconst False)) else val \<sigma> r1)\<close>
    using ite_vec_correct[OF I(1) I(5) z I(3) _ d2 lt] I(4) by auto
  have lon: \<open>lo ?n = m\<close> using m_le by (simp add: lo_def)
  have S: \<open>val \<sigma> r = (if val \<sigma> b < ?n then shv left ?n (val \<sigma> a) (val \<sigma> b) else 0)\<close>
    if \<sigma>: \<open>cnf_sem \<sigma> (snd s')\<close> for \<sigma>
  proof -
    have \<sigma>1: \<open>cnf_sem \<sigma> (snd s1)\<close> using ext_cnf_sem[OF G(2) \<sigma>] .
    have va: \<open>val \<sigma> a < 2 ^ ?n\<close> by (rule val_lt)
    have r1: \<open>val \<sigma> r1 = shv left ?n (val \<sigma> a) (val \<sigma> (take m b))\<close>
      and g: \<open>lit_sem \<sigma> g1 = (\<exists>i. m \<le> i \<and> i < ?n \<and> lit_sem \<sigma> (b ! i))\<close> using I(6) \<sigma>1 lon by auto
    have z0: \<open>val \<sigma> (replicate ?n (lconst False)) = 0\<close>
      using lit_sem_lconst[OF I(1) \<sigma>1] by (simp add: val_eq_0_iff)
    have vb: \<open>val \<sigma> b = val \<sigma> (take m b) + 2 ^ m * val \<sigma> (drop m b)\<close>
      using val_take_drop[of \<sigma> b m] m_le len by simp
    have A: \<open>b ! i \<in> set (drop m b)\<close> if \<open>m \<le> i\<close> \<open>i < ?n\<close> for i
    proof -
      have \<open>drop m b ! (i - m) = b ! i\<close> \<open>i - m < length (drop m b)\<close> using that len by simp_all
      then show ?thesis by (metis nth_mem)
    qed
    have B: \<open>\<exists>i. m \<le> i \<and> i < ?n \<and> b ! i = l\<close> if l: \<open>l \<in> set (drop m b)\<close> for l
    proof -
      obtain j where \<open>j < length (drop m b)\<close> \<open>drop m b ! j = l\<close> using l unfolding in_set_conv_nth by blast
      then show ?thesis using len by (intro exI[of _ \<open>m + j\<close>]) simp
    qed
    have hi: \<open>val \<sigma> (drop m b) = 0 \<longleftrightarrow> \<not> lit_sem \<sigma> g1\<close>
      unfolding val_eq_0_iff g using A B by blast
    show ?thesis
    proof (cases \<open>lit_sem \<sigma> g1\<close>)
      case True
      then have \<open>1 \<le> val \<sigma> (drop m b)\<close> using hi by simp
      then have \<open>2 ^ m \<le> val \<sigma> b\<close> using vb by (metis le_add2 mult.right_neutral mult_le_mono2 order_trans)
      then have \<open>\<not> val \<sigma> b < ?n\<close> using m_ge by simp
      then show ?thesis using G(5) \<sigma> True z0 by simp
    next
      case False
      then have vb': \<open>val \<sigma> b = val \<sigma> (take m b)\<close> using hi vb by simp
      show ?thesis using G(5) \<sigma> False r1 vb' shv_big[OF va] by auto
    qed
  qed
  show ?thesis using G S ext_trans[OF I(2) G(2)] by auto
qed

lemma shift_sem_shl:
  \<open>(if y < n then shv True n x y else 0) = cbin_sem BinOp_Shl n x v y\<close>
proof (cases \<open>y < n\<close>)
  case True then show ?thesis by (simp add: shv_def)
next
  case False
  then have \<open>(2::nat) ^ n dvd 2 ^ y\<close> by (simp add: le_imp_power_dvd)
  then have \<open>(2::nat) ^ n dvd x * 2 ^ y\<close> by (rule dvd_mult)
  then show ?thesis using False by (simp add: dvd_eq_mod_eq_0)
qed

lemma shift_sem_lshr:
  \<open>x < 2 ^ n \<Longrightarrow> (if y < n then shv False n x y else 0) = cbin_sem BinOp_Lshr n x v y\<close>
proof (cases \<open>y < n\<close>)
  case True then show ?thesis by (simp add: shv_def)
next
  case False
  assume x: \<open>x < 2 ^ n\<close>
  have \<open>(2::nat) ^ n \<le> 2 ^ y\<close> using False by simp
  then have \<open>x < 2 ^ y\<close> using x by linarith
  then show ?thesis using False by simp
qed

subsection \<open>Fresh variables, extension by zeros\<close>

lemma fresh_vec_fst [simp]: \<open>fst (fst (fresh_vec_m s w)) = fst s + w\<close>
  by (simp add: fresh_vec_m_def)

text \<open>Fresh variables can take any values.\<close>
lemma fresh_lit_var:
  \<open>v < 2 ^ 64 \<Longrightarrow> unat (Lit_var (make_Lit (word_of_nat v :: 64 word) b)) = v\<close>
  by simp

lemma fresh_lit_sem:
  \<open>v < 2 ^ 64 \<Longrightarrow> lit_sem \<sigma> (make_Lit (word_of_nat v :: 64 word) False) = \<sigma> v\<close>
  by (simp add: lit_sem_def)

lemma fresh_vec_eqs:
  assumes \<open>fresh_vec_m s w = (s', r)\<close>
  shows \<open>s' = (fst s + w, snd s)\<close> \<open>r = map (\<lambda>i. make_Lit (word_of_nat (fst s + i)) False) [0..<w]\<close>
  using assms unfolding fresh_vec_m_def by (simp_all only: prod.inject)

lemma fresh_vec_wf: \<open>wf_st s \<Longrightarrow> wf_st (fst s + w, snd s)\<close>
  unfolding wf_st_def by (auto intro: lits_lt_mono[OF _ le_add1])

lemma fresh_vec_ll:
  assumes sw: \<open>fst s + w < 2 ^ 64\<close>
  shows \<open>lits_lt (fst s + w) (map (\<lambda>i. make_Lit (word_of_nat (fst s + i)) False) [0..<w])\<close>
  unfolding lits_lt_def
proof
  fix l assume \<open>l \<in> set (map (\<lambda>i. make_Lit (word_of_nat (fst s + i)) False) [0..<w])\<close>
  then obtain i where i0: \<open>i \<in> {0..<w}\<close> and l: \<open>l = make_Lit (word_of_nat (fst s + i)) False\<close>
    unfolding set_map set_upt by blast
  have i: \<open>i < w\<close> using i0 by simp
  have v: \<open>fst s + i < 2 ^ 64\<close> using i sw by linarith
  have \<open>unat (Lit_var l) = fst s + i\<close> using fresh_lit_var[OF v] l by (simp only:)
  then show \<open>unat (Lit_var l) < fst s + w\<close> using i by linarith
qed

lemma fresh_vec_model:
  assumes sw: \<open>fst s + w < 2 ^ 64\<close> and bs: \<open>length bs = w\<close>
    and lt: \<open>\<forall>c \<in> set cs. lits_lt (fst s) c\<close> and \<sigma>: \<open>cnf_sem \<sigma> cs\<close>
  shows \<open>\<exists>\<sigma>'. (\<forall>v < fst s. \<sigma>' v = \<sigma> v) \<and> cnf_sem \<sigma>' cs \<and>
           map (lit_sem \<sigma>') (map (\<lambda>i. make_Lit (word_of_nat (fst s + i)) False) [0..<w]) = bs\<close>
proof -
  define \<sigma>' where \<open>\<sigma>' v = (if fst s \<le> v \<and> v < fst s + w then bs ! (v - fst s) else \<sigma> v)\<close> for v
  have ag: \<open>\<forall>v < fst s. \<sigma>' v = \<sigma> v\<close> by (simp add: \<sigma>'_def)
  have c: \<open>cnf_sem \<sigma>' cs\<close> by (rule cnf_sem_agree[OF lt ag \<sigma>])
  have \<open>map (lit_sem \<sigma>') (map (\<lambda>i. make_Lit (word_of_nat (fst s + i)) False) [0..<w]) = bs\<close>
  proof (rule nth_equalityI)
    show \<open>length (map (lit_sem \<sigma>') (map (\<lambda>i. make_Lit (word_of_nat (fst s + i)) False) [0..<w])) =
          length bs\<close> using bs by simp
    fix i assume \<open>i < length (map (lit_sem \<sigma>') (map (\<lambda>i. make_Lit (word_of_nat (fst s + i)) False) [0..<w]))\<close>
    then have i: \<open>i < w\<close> by simp
    have v: \<open>fst s + i < 2 ^ 64\<close> using i sw by linarith
    have \<open>map (lit_sem \<sigma>') (map (\<lambda>i. make_Lit (word_of_nat (fst s + i)) False) [0..<w]) ! i =
          lit_sem \<sigma>' (make_Lit (word_of_nat (fst s + i)) False)\<close>
      using i by (simp del: of_nat_add)
    also have \<open>\<dots> = \<sigma>' (fst s + i)\<close> by (rule fresh_lit_sem[OF v])
    also have \<open>\<dots> = bs ! i\<close> using i by (simp add: \<sigma>'_def)
    finally show \<open>map (lit_sem \<sigma>') (map (\<lambda>i. make_Lit (word_of_nat (fst s + i)) False) [0..<w]) ! i =
                  bs ! i\<close> .
  qed
  then show ?thesis using ag c by blast
qed

lemma fresh_vec_correct:
  assumes \<open>wf_st s\<close> \<open>fresh_vec_m s w = (s', r)\<close> \<open>fst s' < 2 ^ 64\<close>
  shows \<open>wf_st s' \<and> ext s s' \<and> lits_lt (fst s') r \<and> length r = w \<and>
         (\<forall>\<sigma> bs. cnf_sem \<sigma> (snd s) \<longrightarrow> length bs = w \<longrightarrow>
            (\<exists>\<sigma>'. (\<forall>v < fst s. \<sigma>' v = \<sigma> v) \<and> cnf_sem \<sigma>' (snd s') \<and> map (lit_sem \<sigma>') r = bs))\<close>
proof -
  note e = fresh_vec_eqs[OF assms(2)]
  have sw: \<open>fst s + w < 2 ^ 64\<close> using assms(3) unfolding e(1) fst_conv .
  have wf: \<open>wf_st s'\<close> unfolding e(1) by (rule fresh_vec_wf[OF assms(1)])
  have ex: \<open>ext s s'\<close> unfolding ext_def e(1) fst_conv snd_conv
  proof (intro conjI allI impI)
    show \<open>fst s \<le> fst s + w\<close> by simp
    show \<open>\<exists>cs. snd s = snd s @ cs\<close> by (rule exI[of _ \<open>[]\<close>]) simp
    fix \<sigma> assume \<open>cnf_sem \<sigma> (snd s)\<close>
    then show \<open>\<exists>\<sigma>'. (\<forall>v<fst s. \<sigma>' v = \<sigma> v) \<and> cnf_sem \<sigma>' (snd s)\<close> by blast
  qed
  have ll: \<open>lits_lt (fst s') r\<close> unfolding e fst_conv by (rule fresh_vec_ll[OF sw])
  have len: \<open>length r = w\<close> unfolding e(2) by simp
  have M: \<open>\<exists>\<sigma>'. (\<forall>v < fst s. \<sigma>' v = \<sigma> v) \<and> cnf_sem \<sigma>' (snd s') \<and> map (lit_sem \<sigma>') r = bs\<close>
    if \<open>cnf_sem \<sigma> (snd s)\<close> \<open>length bs = w\<close> for \<sigma> bs
    unfolding e snd_conv
    by (rule fresh_vec_model[OF sw that(2) _ that(1)]) (use assms(1) in \<open>simp add: wf_st_def\<close>)
  show ?thesis using wf ex ll len M by blast
qed

lemma zext_ok:
  assumes wf: \<open>wf_st s\<close> and la: \<open>lits_lt (fst s) a\<close> and w: \<open>length a \<le> w\<close>
  shows \<open>lits_lt (fst s) (zext_m a w) \<and> length (zext_m a w) = w \<and>
         (\<forall>\<sigma>. cnf_sem \<sigma> (snd s) \<longrightarrow> val \<sigma> (zext_m a w) = val \<sigma> a)\<close>
proof (intro conjI allI impI)
  show \<open>lits_lt (fst s) (zext_m a w)\<close>
    using lits_lt_nth[OF la] wf_st_pos[OF wf] by (auto simp: zext_m_def lits_lt_def)
  show \<open>length (zext_m a w) = w\<close> by (simp add: zext_m_def)
  fix \<sigma> assume \<sigma>: \<open>cnf_sem \<sigma> (snd s)\<close>
  have m: \<open>map (lit_sem \<sigma>) (zext_m a w) = map (\<lambda>i. i < length a \<and> lit_sem \<sigma> (a ! i)) [0..<w]\<close>
    unfolding zext_m_def map_map comp_def
    by (rule map_cong[OF refl]) (use lit_sem_lconst[OF wf \<sigma>] in auto)
  show \<open>val \<sigma> (zext_m a w) = val \<sigma> a\<close>
    unfolding val_def[of _ \<open>zext_m a w\<close>] m
    using w by (intro bit_eqI) (auto simp: bit_bits_nat_map bit_val)
qed

lemma val_replicate_lconst:
  assumes \<open>wf_st s\<close> \<open>cnf_sem \<sigma> (snd s)\<close>
  shows \<open>val \<sigma> (replicate w (lconst False)) = 0\<close> \<open>val \<sigma> (replicate w (lconst True)) = 2 ^ w - 1\<close>
proof -
  show \<open>val \<sigma> (replicate w (lconst False)) = 0\<close>
    using lit_sem_lconst[OF assms] by (simp add: val_def)
  have \<open>val \<sigma> (replicate w (lconst True)) = bits_nat (replicate w True)\<close>
    using lit_sem_lconst[OF assms] by (simp add: val_def)
  then show \<open>val \<sigma> (replicate w (lconst True)) = 2 ^ w - 1\<close>
    using bits_nat_replicate_True[of w] by simp
qed

lemma lits_lt_replicate_lconst: \<open>wf_st s \<Longrightarrow> fst s \<le> m \<Longrightarrow> lits_lt m (replicate w (lconst b))\<close>
  using wf_st_pos[of s] by (simp add: lits_lt_def)

subsection \<open>Division and remainder\<close>

lemma divrem_arith:
  fixes A B Q R w :: nat
  assumes B: \<open>B \<noteq> 0\<close> \<open>B < 2 ^ w\<close> and Q: \<open>Q < 2 ^ w\<close> and RB: \<open>R < B\<close>
  shows \<open>(((Q * B) mod 2 ^ (w + w) + R) mod 2 ^ (w + w) = A) \<longleftrightarrow> (A = Q * B + R)\<close>
proof -
  have \<open>(Q + 1) * B \<le> 2 ^ w * B\<close> using Q by (intro mult_le_mono1) simp
  then have 1: \<open>Q * B + R < 2 ^ w * B\<close> using RB by simp
  have 3: \<open>2 ^ w * B \<le> 2 ^ w * (2 ^ w :: nat)\<close> by (rule mult_le_mono2) (use B in simp)
  have \<open>Q * B + R < 2 ^ w * 2 ^ w\<close> using 1 3 by (rule less_le_trans)
  then have 2: \<open>Q * B + R < 2 ^ (w + w)\<close> by (simp add: power_add)
  then have \<open>(Q * B) mod 2 ^ (w + w) = Q * B\<close> by simp
  then show ?thesis using 2 by auto
qed

lemma divrem_ok:
  assumes wf: \<open>wf_st s\<close> and la: \<open>lits_lt (fst s) a\<close> and lb: \<open>lits_lt (fst s) b\<close>
    and len: \<open>length b = length a\<close>
    and d: \<open>divrem_m s a b = (s', q, r)\<close> and lt: \<open>fst s' < 2 ^ 64\<close>
  shows \<open>wf_st s' \<and> ext s s' \<and> lits_lt (fst s') q \<and> lits_lt (fst s') r \<and>
         length q = length a \<and> length r = length a \<and>
         (\<forall>\<sigma>. cnf_sem \<sigma> (snd s') \<longrightarrow>
            val \<sigma> q = (if val \<sigma> b = 0 then 2 ^ length a - 1 else val \<sigma> a div val \<sigma> b) \<and>
            val \<sigma> r = (if val \<sigma> b = 0 then val \<sigma> a else val \<sigma> a mod val \<sigma> b))\<close>
proof -
  define w where \<open>w = length a\<close>
  have lenb: \<open>length b = w\<close> using len w_def by simp
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
  have e: \<open>s' = (fst s12, snd s12 @ [[ok]])\<close> \<open>q = q1\<close> \<open>r = r1\<close>
    using d 1 2 3 4 5 6 7 8 9 10 11 12 by (simp_all add: divrem_m_def w_def[symmetric] Let_def addc_m_def)
  have m1: \<open>fst s1 = fst s + w\<close> using fresh_vec_fst[of s w] 1 by simp
  have m2: \<open>fst s2 = fst s1 + w\<close> using fresh_vec_fst[of s1 w] 2 by simp
  have m3: \<open>fst s2 \<le> fst s3\<close> using eq_m_mono[of s2 b \<open>replicate w (lconst False)\<close>] 3 by simp
  have m4: \<open>fst s3 \<le> fst s4\<close> using eq_m_mono[of s3 q1 \<open>replicate w (lconst True)\<close>] 4 by simp
  have m5: \<open>fst s4 \<le> fst s5\<close> using eq_m_mono[of s4 r1 a] 5 by simp
  have m6: \<open>fst s6 = Suc (fst s5)\<close> using and_fst[of s5 qo ra] 6 by simp
  have m7: \<open>fst s6 \<le> fst s7\<close> using mul_m_mono[of s6 \<open>zext_m q1 (w + w)\<close> \<open>zext_m b (w + w)\<close>] 7 by simp
  have m8: \<open>fst s7 \<le> fst s8\<close> using add_m_mono[of s7 pr \<open>zext_m r1 (w + w)\<close> \<open>lconst False\<close>] 8 by simp
  have m9: \<open>fst s8 \<le> fst s9\<close> using eq_m_mono[of s8 sm \<open>zext_m a (w + w)\<close>] 9 by simp
  have m10: \<open>fst s9 \<le> fst s10\<close> using ult_m_mono[of s9 r1 b] 10 by simp
  have m11: \<open>fst s11 = Suc (fst s10)\<close> using and_fst[of s10 sa rl] 11 by simp
  have m12: \<open>fst s12 = Suc (fst s11)\<close> using ite_fst[of s11 bz cz cn] 12 by simp
  have l12: \<open>fst s12 < 2 ^ 64\<close> using lt e(1) by simp
  have l11: \<open>fst s11 < 2 ^ 64\<close> using l12 m12 by simp
  have l10: \<open>fst s10 < 2 ^ 64\<close> using l11 m11 by simp
  have l9: \<open>fst s9 < 2 ^ 64\<close> using l10 m10 by simp
  have l8: \<open>fst s8 < 2 ^ 64\<close> using l9 m9 by simp
  have l7: \<open>fst s7 < 2 ^ 64\<close> using l8 m8 by simp
  have l6: \<open>fst s6 < 2 ^ 64\<close> using l7 m7 by simp
  have l5: \<open>fst s5 < 2 ^ 64\<close> using l6 m6 by simp
  have l4: \<open>fst s4 < 2 ^ 64\<close> using l5 m5 by simp
  have l3: \<open>fst s3 < 2 ^ 64\<close> using l4 m4 by simp
  have l2: \<open>fst s2 < 2 ^ 64\<close> using l3 m3 by simp
  have l1: \<open>fst s1 < 2 ^ 64\<close> using l2 m2 by simp
  note F1 = fresh_vec_correct[OF wf 1 l1]
  have W1: \<open>wf_st s1\<close> \<open>ext s s1\<close> \<open>lits_lt (fst s1) q1\<close> \<open>length q1 = w\<close> using F1 by auto
  note F2 = fresh_vec_correct[OF W1(1) 2 l2]
  have W2: \<open>wf_st s2\<close> \<open>ext s1 s2\<close> \<open>lits_lt (fst s2) r1\<close> \<open>length r1 = w\<close> using F2 by auto
  have le02: \<open>fst s \<le> fst s2\<close> using m1 m2 by simp
  have E3: \<open>wf_st s3\<close> \<open>ext s2 s3\<close> \<open>unat (Lit_var bz) < fst s3\<close>
    \<open>\<forall>\<sigma>. cnf_sem \<sigma> (snd s3) \<longrightarrow> lit_sem \<sigma> bz = (val \<sigma> b = val \<sigma> (replicate w (lconst False)))\<close>
    using eq_ok[OF W2(1) lits_lt_mono[OF lb le02] lits_lt_replicate_lconst[OF W2(1) order_refl] _ 3 l3] lenb
    by auto
  have E4: \<open>wf_st s4\<close> \<open>ext s3 s4\<close> \<open>unat (Lit_var qo) < fst s4\<close>
    \<open>\<forall>\<sigma>. cnf_sem \<sigma> (snd s4) \<longrightarrow> lit_sem \<sigma> qo = (val \<sigma> q1 = val \<sigma> (replicate w (lconst True)))\<close>
    using eq_ok[OF E3(1) lits_lt_mono[OF W1(3)] lits_lt_replicate_lconst[OF E3(1) order_refl] _ 4 l4]
      W1(4) m2 m3 by auto
  have E5: \<open>wf_st s5\<close> \<open>ext s4 s5\<close> \<open>unat (Lit_var ra) < fst s5\<close>
    \<open>\<forall>\<sigma>. cnf_sem \<sigma> (snd s5) \<longrightarrow> lit_sem \<sigma> ra = (val \<sigma> r1 = val \<sigma> a)\<close>
    using eq_ok[OF E4(1) lits_lt_mono[OF W2(3)] lits_lt_mono[OF la] _ 5 l5] W2(4) w_def le02 m3 m4
    by auto
  have A6: \<open>wf_st s6\<close> \<open>ext s5 s6\<close> \<open>unat (Lit_var cz) < fst s6\<close>
    \<open>\<forall>\<sigma>. cnf_sem \<sigma> (snd s6) \<longrightarrow> lit_sem \<sigma> cz = (lit_sem \<sigma> qo \<and> lit_sem \<sigma> ra)\<close>
    using and_ok[OF E5(1) _ E5(3) 6 l6] E4(3) m5 by auto
  have le16: \<open>fst s1 \<le> fst s6\<close> \<open>fst s \<le> fst s6\<close> \<open>fst s2 \<le> fst s6\<close> using m1 m2 m3 m4 m5 m6 by simp_all
  have ZQ: \<open>lits_lt (fst s6) (zext_m q1 (w + w))\<close> \<open>length (zext_m q1 (w + w)) = w + w\<close>
    \<open>\<forall>\<sigma>. cnf_sem \<sigma> (snd s6) \<longrightarrow> val \<sigma> (zext_m q1 (w + w)) = val \<sigma> q1\<close>
    using zext_ok[OF A6(1) lits_lt_mono[OF W1(3) le16(1)]] W1(4) by auto
  have ZB: \<open>lits_lt (fst s6) (zext_m b (w + w))\<close> \<open>length (zext_m b (w + w)) = w + w\<close>
    \<open>\<forall>\<sigma>. cnf_sem \<sigma> (snd s6) \<longrightarrow> val \<sigma> (zext_m b (w + w)) = val \<sigma> b\<close>
    using zext_ok[OF A6(1) lits_lt_mono[OF lb le16(2)]] lenb by auto
  have M7: \<open>wf_st s7\<close> \<open>ext s6 s7\<close> \<open>lits_lt (fst s7) pr\<close> \<open>length pr = w + w\<close>
    \<open>\<forall>\<sigma>. cnf_sem \<sigma> (snd s7) \<longrightarrow> val \<sigma> pr = (val \<sigma> (zext_m q1 (w + w)) * val \<sigma> (zext_m b (w + w))) mod 2 ^ (w + w)\<close>
    using mul_ok[OF A6(1) ZQ(1) ZB(1) _ 7 l7] ZQ(2) ZB(2) by auto
  have ZR: \<open>lits_lt (fst s7) (zext_m r1 (w + w))\<close> \<open>length (zext_m r1 (w + w)) = w + w\<close>
    \<open>\<forall>\<sigma>. cnf_sem \<sigma> (snd s7) \<longrightarrow> val \<sigma> (zext_m r1 (w + w)) = val \<sigma> r1\<close>
    using zext_ok[OF M7(1) lits_lt_mono[OF W2(3)]] W2(4) le16(3) m7 by auto
  have lc7: \<open>unat (Lit_var (lconst False)) < fst s7\<close> using wf_st_pos[OF M7(1)] by simp
  have A8: \<open>wf_st s8\<close> \<open>ext s7 s8\<close> \<open>lits_lt (fst s8) sm\<close> \<open>length sm = w + w\<close>
    \<open>\<forall>\<sigma>. cnf_sem \<sigma> (snd s8) \<longrightarrow> val \<sigma> sm + 2 ^ (w + w) * of_bool (lit_sem \<sigma> c) =
        val \<sigma> pr + val \<sigma> (zext_m r1 (w + w)) + of_bool (lit_sem \<sigma> (lconst False))\<close>
    using add_ok[OF M7(1) M7(3) ZR(1) _ lc7 8 l8] ZR(2) M7(4) by auto
  have le08: \<open>fst s \<le> fst s8\<close> using le16 m7 m8 by simp
  have ZA: \<open>lits_lt (fst s8) (zext_m a (w + w))\<close> \<open>length (zext_m a (w + w)) = w + w\<close>
    \<open>\<forall>\<sigma>. cnf_sem \<sigma> (snd s8) \<longrightarrow> val \<sigma> (zext_m a (w + w)) = val \<sigma> a\<close>
    using zext_ok[OF A8(1) lits_lt_mono[OF la le08]] w_def by auto
  have E9: \<open>wf_st s9\<close> \<open>ext s8 s9\<close> \<open>unat (Lit_var sa) < fst s9\<close>
    \<open>\<forall>\<sigma>. cnf_sem \<sigma> (snd s9) \<longrightarrow> lit_sem \<sigma> sa = (val \<sigma> sm = val \<sigma> (zext_m a (w + w)))\<close>
    using eq_ok[OF A8(1) A8(3) ZA(1) _ 9 l9] ZA(2) A8(4) by auto
  have le29: \<open>fst s2 \<le> fst s9\<close> \<open>fst s \<le> fst s9\<close> using le16 m7 m8 m9 by simp_all
  have U10: \<open>wf_st s10\<close> \<open>ext s9 s10\<close> \<open>unat (Lit_var rl) < fst s10\<close>
    \<open>\<forall>\<sigma>. cnf_sem \<sigma> (snd s10) \<longrightarrow> lit_sem \<sigma> rl = (val \<sigma> r1 < val \<sigma> b)\<close>
    using ult_ok[OF E9(1) lits_lt_mono[OF W2(3) le29(1)] lits_lt_mono[OF lb le29(2)] _ 10 l10] lenb W2(4)
    by auto
  have A11: \<open>wf_st s11\<close> \<open>ext s10 s11\<close> \<open>unat (Lit_var cn) < fst s11\<close>
    \<open>\<forall>\<sigma>. cnf_sem \<sigma> (snd s11) \<longrightarrow> lit_sem \<sigma> cn = (lit_sem \<sigma> sa \<and> lit_sem \<sigma> rl)\<close>
    using and_ok[OF U10(1) _ U10(3) 11 l11] E9(3) m10 by auto
  have v11: \<open>unat (Lit_var bz) < fst s11\<close> \<open>unat (Lit_var cz) < fst s11\<close>
    using E3(3) A6(3) m4 m5 m6 m7 m8 m9 m10 m11 by simp_all
  have I12: \<open>wf_st s12\<close> \<open>ext s11 s12\<close> \<open>unat (Lit_var ok) < fst s12\<close>
    \<open>\<forall>\<sigma>. cnf_sem \<sigma> (snd s12) \<longrightarrow> lit_sem \<sigma> ok = (if lit_sem \<sigma> bz then lit_sem \<sigma> cz else lit_sem \<sigma> cn)\<close>
    using ite_ok[OF A11(1) v11 A11(3) 12 l12] by auto
  have X212: \<open>ext s2 s12\<close>
    using ext_trans[OF E3(2) ext_trans[OF E4(2) ext_trans[OF E5(2) ext_trans[OF A6(2)
      ext_trans[OF M7(2) ext_trans[OF A8(2) ext_trans[OF E9(2) ext_trans[OF U10(2)
      ext_trans[OF A11(2) I12(2)]]]]]]]]] .
  text \<open>The meaning of \<open>ok\<close>.\<close>
  have OK: \<open>lit_sem \<sigma> ok = (if val \<sigma> b = 0 then val \<sigma> q1 = 2 ^ w - 1 \<and> val \<sigma> r1 = val \<sigma> a
      else ((val \<sigma> q1 * val \<sigma> b) mod 2 ^ (w + w) + val \<sigma> r1) mod 2 ^ (w + w) = val \<sigma> a \<and> val \<sigma> r1 < val \<sigma> b)\<close>
    if \<sigma>: \<open>cnf_sem \<sigma> (snd s12)\<close> for \<sigma>
  proof -
    have \<sigma>11: \<open>cnf_sem \<sigma> (snd s11)\<close> using ext_cnf_sem[OF I12(2) \<sigma>] .
    have \<sigma>10: \<open>cnf_sem \<sigma> (snd s10)\<close> using ext_cnf_sem[OF A11(2) \<sigma>11] .
    have \<sigma>9: \<open>cnf_sem \<sigma> (snd s9)\<close> using ext_cnf_sem[OF U10(2) \<sigma>10] .
    have \<sigma>8: \<open>cnf_sem \<sigma> (snd s8)\<close> using ext_cnf_sem[OF E9(2) \<sigma>9] .
    have \<sigma>7: \<open>cnf_sem \<sigma> (snd s7)\<close> using ext_cnf_sem[OF A8(2) \<sigma>8] .
    have \<sigma>6: \<open>cnf_sem \<sigma> (snd s6)\<close> using ext_cnf_sem[OF M7(2) \<sigma>7] .
    have \<sigma>5: \<open>cnf_sem \<sigma> (snd s5)\<close> using ext_cnf_sem[OF A6(2) \<sigma>6] .
    have \<sigma>4: \<open>cnf_sem \<sigma> (snd s4)\<close> using ext_cnf_sem[OF E5(2) \<sigma>5] .
    have \<sigma>3: \<open>cnf_sem \<sigma> (snd s3)\<close> using ext_cnf_sem[OF E4(2) \<sigma>4] .
    have bz: \<open>lit_sem \<sigma> bz = (val \<sigma> b = 0)\<close>
      using E3(4) \<sigma>3 val_replicate_lconst(1)[OF E3(1) \<sigma>3] by simp
    have qo: \<open>lit_sem \<sigma> qo = (val \<sigma> q1 = 2 ^ w - 1)\<close>
      using E4(4) \<sigma>4 val_replicate_lconst(2)[OF E4(1) \<sigma>4] by simp
    have cz: \<open>lit_sem \<sigma> cz = (val \<sigma> q1 = 2 ^ w - 1 \<and> val \<sigma> r1 = val \<sigma> a)\<close>
      using A6(4) E5(4) \<sigma>6 \<sigma>5 qo by simp
    have pr: \<open>val \<sigma> pr = (val \<sigma> q1 * val \<sigma> b) mod 2 ^ (w + w)\<close>
      using M7(5) ZQ(3) ZB(3) \<sigma>7 \<sigma>6 by simp
    have h8: \<open>val \<sigma> sm + 2 ^ (w + w) * of_bool (lit_sem \<sigma> c) = val \<sigma> pr + val \<sigma> r1\<close>
      using A8(5) ZR(3) \<sigma>8 \<sigma>7 lit_sem_lconst[OF A8(1) \<sigma>8] by simp
    have smlt: \<open>val \<sigma> sm < 2 ^ (w + w)\<close> using val_lt[of \<sigma> sm] A8(4) by simp
    have sm: \<open>val \<sigma> sm = (val \<sigma> pr + val \<sigma> r1) mod 2 ^ (w + w)\<close>
      by (rule mod_of_carry[OF h8 smlt])
    have sa: \<open>lit_sem \<sigma> sa = (val \<sigma> sm = val \<sigma> a)\<close> using E9(4) ZA(3) \<sigma>9 \<sigma>8 by simp
    have cn: \<open>lit_sem \<sigma> cn = (((val \<sigma> q1 * val \<sigma> b) mod 2 ^ (w + w) + val \<sigma> r1) mod 2 ^ (w + w) = val \<sigma> a \<and>
        val \<sigma> r1 < val \<sigma> b)\<close>
      using A11(4) U10(4) \<sigma>11 \<sigma>10 sa sm pr by simp
    show ?thesis using I12(4) \<sigma> bz cz cn by simp
  qed
  have ltw: \<open>val \<sigma> x < 2 ^ w\<close> if \<open>length x = w\<close> for \<sigma> x using val_lt[of \<sigma> x] that by simp
  have SOUND: \<open>val \<sigma> q1 = (if val \<sigma> b = 0 then 2 ^ w - 1 else val \<sigma> a div val \<sigma> b) \<and>
            val \<sigma> r1 = (if val \<sigma> b = 0 then val \<sigma> a else val \<sigma> a mod val \<sigma> b)\<close>
    if \<sigma>: \<open>cnf_sem \<sigma> (snd s12)\<close> \<open>lit_sem \<sigma> ok\<close> for \<sigma>
  proof (cases \<open>val \<sigma> b = 0\<close>)
    case True then show ?thesis using OK[OF \<sigma>(1)] \<sigma>(2) by simp
  next
    case False
    have h: \<open>((val \<sigma> q1 * val \<sigma> b) mod 2 ^ (w + w) + val \<sigma> r1) mod 2 ^ (w + w) = val \<sigma> a\<close>
      \<open>val \<sigma> r1 < val \<sigma> b\<close> using OK[OF \<sigma>(1)] \<sigma>(2) False by simp_all
    have \<open>val \<sigma> a = val \<sigma> q1 * val \<sigma> b + val \<sigma> r1\<close>
      using divrem_arith[OF False ltw[OF lenb] ltw[OF W1(4)] h(2)] h(1) by simp
    then show ?thesis using False h(2) by simp
  qed
  have EXT: \<open>ext s s'\<close>
    unfolding ext_def
  proof (intro conjI allI impI)
    have X: \<open>ext s s12\<close> using ext_trans[OF W1(2) ext_trans[OF W2(2) X212]] .
    show \<open>fst s \<le> fst s'\<close> using ext_fst[OF X] e(1) by simp
    show \<open>\<exists>cs. snd s' = snd s @ cs\<close> using X e(1) by (auto simp: ext_def)
    fix \<sigma> assume \<sigma>: \<open>cnf_sem \<sigma> (snd s)\<close>
    define A where \<open>A = val \<sigma> a\<close>
    define B where \<open>B = val \<sigma> b\<close>
    define Qv where \<open>Qv = (if B = 0 then 2 ^ w - 1 else A div B)\<close>
    define Rv where \<open>Rv = (if B = 0 then A else A mod B)\<close>
    have A: \<open>A < 2 ^ w\<close> using ltw[of a \<sigma>] w_def A_def by simp
    have Qv: \<open>Qv < 2 ^ w\<close> using A by (auto simp: Qv_def intro: le_less_trans[OF div_le_dividend])
    have Rv: \<open>Rv < 2 ^ w\<close> using A by (auto simp: Rv_def intro: le_less_trans[OF mod_less_eq_dividend])
    have bv: \<open>bits_nat (map (bit x) [0..<w]) = x\<close> if \<open>x < 2 ^ w\<close> for x
    proof -
      have \<open>bits_nat (map (bit x) [0..<w]) = x mod 2 ^ w\<close>
        by (auto intro!: bit_eqI simp: bit_bits_nat_map bit_mod_pow)
      then show ?thesis using that by simp
    qed
    have lq: \<open>length (map (bit Qv) [0..<w]) = w\<close> \<open>length (map (bit Rv) [0..<w]) = w\<close> by simp_all
    obtain \<sigma>1 where s1: \<open>\<forall>v<fst s. \<sigma>1 v = \<sigma> v\<close> \<open>cnf_sem \<sigma>1 (snd s1)\<close> \<open>map (lit_sem \<sigma>1) q1 = map (bit Qv) [0..<w]\<close>
      using F1 \<sigma> lq(1) by blast
    obtain \<sigma>2 where s2: \<open>\<forall>v<fst s1. \<sigma>2 v = \<sigma>1 v\<close> \<open>cnf_sem \<sigma>2 (snd s2)\<close> \<open>map (lit_sem \<sigma>2) r1 = map (bit Rv) [0..<w]\<close>
      using F2 s1(2) lq(2) by blast
    obtain \<sigma>' where s12: \<open>\<forall>v<fst s2. \<sigma>' v = \<sigma>2 v\<close> \<open>cnf_sem \<sigma>' (snd s12)\<close>
      using ext_agree[OF X212 s2(2)] by blast
    have ag: \<open>\<forall>v<fst s. \<sigma>' v = \<sigma> v\<close> using s1(1) s2(1) s12(1) m1 m2 by simp
    have vq: \<open>val \<sigma>' q1 = Qv\<close>
    proof -
      have \<open>val \<sigma>' q1 = val \<sigma>2 q1\<close> using val_agree[OF lits_lt_mono[OF W1(3)] s12(1)] m2 by simp
      also have \<open>\<dots> = val \<sigma>1 q1\<close> using val_agree[OF W1(3) s2(1)] .
      also have \<open>\<dots> = Qv\<close> using s1(3) bv[OF Qv] by (simp add: val_def)
      finally show ?thesis .
    qed
    have vr: \<open>val \<sigma>' r1 = Rv\<close>
    proof -
      have \<open>val \<sigma>' r1 = val \<sigma>2 r1\<close> using val_agree[OF W2(3) s12(1)] .
      also have \<open>\<dots> = Rv\<close> using s2(3) bv[OF Rv] by (simp add: val_def)
      finally show ?thesis .
    qed
    have va: \<open>val \<sigma>' a = A\<close> using val_agree[OF la ag] A_def by simp
    have vb: \<open>val \<sigma>' b = B\<close> using val_agree[OF lb ag] B_def by simp
    have \<open>lit_sem \<sigma>' ok\<close>
    proof (cases \<open>B = 0\<close>)
      case True then show ?thesis using OK[OF s12(2)] vq vr va vb Qv_def Rv_def by simp
    next
      case False
      have \<open>B < 2 ^ w\<close> using ltw[OF lenb, of \<sigma>] B_def by simp
      moreover have \<open>Rv < B\<close> using False by (simp add: Rv_def)
      moreover have \<open>A = Qv * B + Rv\<close> using False by (simp add: Qv_def Rv_def)
      ultimately have \<open>((Qv * B) mod 2 ^ (w + w) + Rv) mod 2 ^ (w + w) = A\<close>
        using divrem_arith[OF False _ Qv] by simp
      then show ?thesis using OK[OF s12(2)] vq vr va vb False \<open>Rv < B\<close> by simp
    qed
    then have \<open>cnf_sem \<sigma>' (snd s')\<close> using s12(2) e(1) by simp
    then show \<open>\<exists>\<sigma>'. (\<forall>v<fst s. \<sigma>' v = \<sigma> v) \<and> cnf_sem \<sigma>' (snd s')\<close> using ag by blast
  qed
  have WF: \<open>wf_st s'\<close> using I12(1) I12(3) e(1) by (auto simp: wf_st_def intro: lits_lt_mono)
  have LT: \<open>lits_lt (fst s') q\<close> \<open>lits_lt (fst s') r\<close>
  proof -
    have \<open>fst s1 \<le> fst s'\<close> \<open>fst s2 \<le> fst s'\<close> using le29 m2 m9 m10 m11 m12 e(1) le16 by simp_all
    then show \<open>lits_lt (fst s') q\<close> \<open>lits_lt (fst s') r\<close> using W1(3) W2(3) e lits_lt_mono by blast+
  qed
  have S: \<open>\<forall>\<sigma>. cnf_sem \<sigma> (snd s') \<longrightarrow>
            val \<sigma> q = (if val \<sigma> b = 0 then 2 ^ length a - 1 else val \<sigma> a div val \<sigma> b) \<and>
            val \<sigma> r = (if val \<sigma> b = 0 then val \<sigma> a else val \<sigma> a mod val \<sigma> b)\<close>
    using SOUND e w_def by simp
  show ?thesis using WF EXT LT S e W1(4) W2(4) w_def by simp
qed

section \<open>The binary operators\<close>

lemma bin_correct_bitwise:
  assumes wf: \<open>wf_st s\<close> and la: \<open>lits_lt (fst s) a\<close> and lb: \<open>lits_lt (fst s) b\<close>
    and len: \<open>length a = length b\<close> and op: \<open>op \<in> {BinOp_And, BinOp_Or, BinOp_Xor}\<close>
    and d: \<open>bitwise_m op s a b = (s', r)\<close> and lt: \<open>fst s' < 2 ^ 64\<close>
  shows \<open>wf_st s' \<and> ext s s' \<and> lits_lt (fst s') r \<and> length r = bin_width op (length a) (length b) \<and>
         (\<forall>\<sigma>. cnf_sem \<sigma> (snd s') \<longrightarrow>
            val \<sigma> r = cbin_sem op (length a) (val \<sigma> a) (length b) (val \<sigma> b))\<close>
proof -
  note L = bitwise_ok[OF wf la lb len d lt]
  have \<open>val \<sigma> r = cbin_sem op (length a) (val \<sigma> a) (length b) (val \<sigma> b)\<close> if \<open>cnf_sem \<sigma> (snd s')\<close> for \<sigma>
    using L that bits_bop[OF op refl len[symmetric], of \<sigma>] len by (simp add: val_def)
  moreover have \<open>bin_width op (length a) (length b) = length a\<close> using op by (auto simp: bin_width_def)
  ultimately show ?thesis using L by simp
qed

lemma blast_bin_correct:
  assumes \<open>wf_st s\<close> \<open>lits_lt (fst s) a\<close> \<open>lits_lt (fst s) b\<close>
    \<open>op \<noteq> BinOp_Concat \<longrightarrow> length a = length b\<close>
    \<open>blast_bin_m s op a b = (s', r)\<close> \<open>fst s' < 2 ^ 64\<close>
  shows \<open>wf_st s' \<and> ext s s' \<and> lits_lt (fst s') r \<and> length r = bin_width op (length a) (length b) \<and>
         (\<forall>\<sigma>. cnf_sem \<sigma> (snd s') \<longrightarrow>
            val \<sigma> r = cbin_sem op (length a) (val \<sigma> a) (length b) (val \<sigma> b))\<close>
proof (cases op)
  case BinOp_And
  have len: \<open>length a = length b\<close> using assms(4) BinOp_And by simp
  have d: \<open>bitwise_m op s a b = (s', r)\<close> using assms(5) BinOp_And by (simp add: blast_bin_m_def)
  show ?thesis by (rule bin_correct_bitwise[OF assms(1-3) len _ d assms(6)]) (simp add: BinOp_And)
next
  case BinOp_Or
  have len: \<open>length a = length b\<close> using assms(4) BinOp_Or by simp
  have d: \<open>bitwise_m op s a b = (s', r)\<close> using assms(5) BinOp_Or by (simp add: blast_bin_m_def)
  show ?thesis by (rule bin_correct_bitwise[OF assms(1-3) len _ d assms(6)]) (simp add: BinOp_Or)
next
  case BinOp_Xor
  have len: \<open>length a = length b\<close> using assms(4) BinOp_Xor by simp
  have d: \<open>bitwise_m op s a b = (s', r)\<close> using assms(5) BinOp_Xor by (simp add: blast_bin_m_def)
  show ?thesis by (rule bin_correct_bitwise[OF assms(1-3) len _ d assms(6)]) (simp add: BinOp_Xor)
next
  case BinOp_Add
  have len: \<open>length b = length a\<close> using assms(4) BinOp_Add by simp
  obtain c where d: \<open>add_m s a b (lconst False) = (s', r, c)\<close>
    using assms(5) BinOp_Add by (simp add: blast_bin_m_def split: prod.splits)
  have lc: \<open>unat (Lit_var (lconst False)) < fst s\<close> using wf_st_pos[OF assms(1)] by simp
  note L = add_ok[OF assms(1-3) len lc d assms(6)]
  have \<open>val \<sigma> r = (val \<sigma> a + val \<sigma> b) mod 2 ^ length a\<close> if \<sigma>: \<open>cnf_sem \<sigma> (snd s')\<close> for \<sigma>
  proof -
    have h: \<open>val \<sigma> r + 2 ^ length a * of_bool (lit_sem \<sigma> c) = val \<sigma> a + val \<sigma> b\<close>
      using L \<sigma> lit_sem_lconst[OF conjunct1[OF L] \<sigma>] by simp
    have rlt: \<open>val \<sigma> r < 2 ^ length a\<close> using val_lt[of \<sigma> r] L by simp
    show ?thesis by (rule mod_of_carry[OF h rlt])
  qed
  then show ?thesis using L BinOp_Add by (simp add: bin_width_def)
next
  case BinOp_Mul
  have len: \<open>length b = length a\<close> using assms(4) BinOp_Mul by simp
  have d: \<open>mul_m s a b = (s', r)\<close> using assms(5) BinOp_Mul by (simp add: blast_bin_m_def)
  show ?thesis using mul_ok[OF assms(1-3) len d assms(6)] BinOp_Mul by (simp add: bin_width_def)
next
  case BinOp_Udiv
  have len: \<open>length b = length a\<close> using assms(4) BinOp_Udiv by simp
  obtain r2 where d: \<open>divrem_m s a b = (s', r, r2)\<close>
    using assms(5) BinOp_Udiv by (simp add: blast_bin_m_def split: prod.splits)
  show ?thesis using divrem_ok[OF assms(1-3) len d assms(6)] BinOp_Udiv by (simp add: bin_width_def)
next
  case BinOp_Urem
  have len: \<open>length b = length a\<close> using assms(4) BinOp_Urem by simp
  obtain r1 where d: \<open>divrem_m s a b = (s', r1, r)\<close>
    using assms(5) BinOp_Urem by (simp add: blast_bin_m_def split: prod.splits)
  show ?thesis using divrem_ok[OF assms(1-3) len d assms(6)] BinOp_Urem by (simp add: bin_width_def)
next
  case BinOp_Shl
  have len: \<open>length b = length a\<close> using assms(4) BinOp_Shl by simp
  have d: \<open>shift_m s a b True = (s', r)\<close> using assms(5) BinOp_Shl by (simp add: blast_bin_m_def)
  show ?thesis using shift_ok[OF assms(1-3) len d assms(6)] BinOp_Shl shift_sem_shl
    by (simp add: bin_width_def)
next
  case BinOp_Lshr
  have len: \<open>length b = length a\<close> using assms(4) BinOp_Lshr by simp
  have d: \<open>shift_m s a b False = (s', r)\<close> using assms(5) BinOp_Lshr by (simp add: blast_bin_m_def)
  show ?thesis using shift_ok[OF assms(1-3) len d assms(6)] BinOp_Lshr shift_sem_lshr val_lt
    by (simp add: bin_width_def)
next
  case BinOp_Concat
  have e: \<open>s' = s\<close> \<open>r = b @ a\<close> using assms(5) BinOp_Concat by (simp_all add: blast_bin_m_def concat_m_def)
  show ?thesis using e assms(1-3) BinOp_Concat by (simp add: ext_refl bin_width_def val_append)
next
  case BinOp_Eq
  have len: \<open>length b = length a\<close> using assms(4) BinOp_Eq by simp
  obtain x where d: \<open>eq_m s a b = (s', x)\<close> \<open>r = [x]\<close>
    using assms(5) BinOp_Eq by (simp add: blast_bin_m_def split: prod.splits)
  show ?thesis using eq_ok[OF assms(1-3) len d(1) assms(6)] d(2) BinOp_Eq
    by (simp add: bin_width_def val_single)
next
  case BinOp_Ult
  have len: \<open>length b = length a\<close> using assms(4) BinOp_Ult by simp
  obtain x where d: \<open>ult_m s a b = (s', x)\<close> \<open>r = [x]\<close>
    using assms(5) BinOp_Ult by (simp add: blast_bin_m_def split: prod.splits)
  show ?thesis using ult_ok[OF assms(1-3) len d(1) assms(6)] d(2) BinOp_Ult
    by (simp add: bin_width_def val_single)
qed

end
