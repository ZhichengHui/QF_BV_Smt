theory QFBV_SmtRefine
  imports "QFBV_Smt.QFBV_SmtModel"
begin

section \<open>The Rust functions of the translation compute their models\<close>

subsection \<open>The precondition of the recursion\<close>

text \<open>The least number of arguments with which \<^verbatim>\<open>tr_app\<close> does not panic.\<close>
definition min_ar :: \<open>SmtOp \<Rightarrow> nat\<close> where
  \<open>min_ar op \<equiv>
     (case op of
        SmtOp_Not \<Rightarrow> 1
      | SmtOp_Bvnot \<Rightarrow> 1
      | SmtOp_Bvneg \<Rightarrow> 1
      | SmtOp_And \<Rightarrow> 1
      | SmtOp_Or \<Rightarrow> 1
      | SmtOp_Xor \<Rightarrow> 1
      | SmtOp_Bvand \<Rightarrow> 1
      | SmtOp_Bvor \<Rightarrow> 1
      | SmtOp_Bvadd \<Rightarrow> 1
      | SmtOp_Bvmul \<Rightarrow> 1
      | SmtOp_Implies \<Rightarrow> 1
      | SmtOp_Eq \<Rightarrow> 2
      | SmtOp_Distinct \<Rightarrow> 2
      | SmtOp_Ite \<Rightarrow> 3
      | SmtOp_Extract i j \<Rightarrow> 1
      | SmtOp_Repeat i \<Rightarrow> 1
      | SmtOp_ZeroExtend i \<Rightarrow> 1
      | SmtOp_SignExtend i \<Rightarrow> 1
      | SmtOp_RotateLeft i \<Rightarrow> 1
      | SmtOp_RotateRight i \<Rightarrow> 1
      | _ \<Rightarrow> 2)\<close>

lemma min_ar_simps [simp]:
  \<open>min_ar SmtOp_Not = 1\<close>
  \<open>min_ar SmtOp_Bvnot = 1\<close>
  \<open>min_ar SmtOp_Bvneg = 1\<close>
  \<open>min_ar SmtOp_And = 1\<close>
  \<open>min_ar SmtOp_Or = 1\<close>
  \<open>min_ar SmtOp_Xor = 1\<close>
  \<open>min_ar SmtOp_Bvand = 1\<close>
  \<open>min_ar SmtOp_Bvor = 1\<close>
  \<open>min_ar SmtOp_Bvadd = 1\<close>
  \<open>min_ar SmtOp_Bvmul = 1\<close>
  \<open>min_ar SmtOp_Implies = 1\<close>
  \<open>min_ar SmtOp_Eq = 2\<close>
  \<open>min_ar SmtOp_Distinct = 2\<close>
  \<open>min_ar SmtOp_Ite = 3\<close>
  \<open>min_ar (SmtOp_Extract i j) = 1\<close>
  \<open>min_ar (SmtOp_Repeat i) = 1\<close>
  \<open>min_ar (SmtOp_ZeroExtend i) = 1\<close>
  \<open>min_ar (SmtOp_SignExtend i) = 1\<close>
  \<open>min_ar (SmtOp_RotateLeft i) = 1\<close>
  \<open>min_ar (SmtOp_RotateRight i) = 1\<close>
  \<open>min_ar SmtOp_Concat = 2\<close>
  \<open>min_ar SmtOp_Bvudiv = 2\<close>
  \<open>min_ar SmtOp_Bvurem = 2\<close>
  \<open>min_ar SmtOp_Bvshl = 2\<close>
  \<open>min_ar SmtOp_Bvlshr = 2\<close>
  \<open>min_ar SmtOp_Bvult = 2\<close>
  \<open>min_ar SmtOp_Bvnand = 2\<close>
  \<open>min_ar SmtOp_Bvnor = 2\<close>
  \<open>min_ar SmtOp_Bvxor = 2\<close>
  \<open>min_ar SmtOp_Bvxnor = 2\<close>
  \<open>min_ar SmtOp_Bvcomp = 2\<close>
  \<open>min_ar SmtOp_Bvsub = 2\<close>
  \<open>min_ar SmtOp_Bvsdiv = 2\<close>
  \<open>min_ar SmtOp_Bvsrem = 2\<close>
  \<open>min_ar SmtOp_Bvsmod = 2\<close>
  \<open>min_ar SmtOp_Bvashr = 2\<close>
  \<open>min_ar SmtOp_Bvule = 2\<close>
  \<open>min_ar SmtOp_Bvugt = 2\<close>
  \<open>min_ar SmtOp_Bvuge = 2\<close>
  \<open>min_ar SmtOp_Bvslt = 2\<close>
  \<open>min_ar SmtOp_Bvsle = 2\<close>
  \<open>min_ar SmtOp_Bvsgt = 2\<close>
  \<open>min_ar SmtOp_Bvsge = 2\<close>
  by (simp_all add: min_ar_def)

text \<open>\<open>tok p F dl el n t\<close>: what \<^verbatim>\<open>tr_term\<close> needs not to panic and to compute
  \<^const>\<open>tr_term_m\<close> with the bound \<open>n\<close>, for \<open>dl\<close> entries of \<^verbatim>\<open>dm\<close> and \<open>el\<close> of \<^verbatim>\<open>env\<close>: indices in
  bounds, a definition with parameters expanded only below \<open>n\<close>, enough arguments for each theory
  function, and every argument list shorter than \<open>2^64\<close> and at most \<open>F\<close> (the loop fuel).\<close>
function (sequential) tok :: \<open>SmtProblem \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> SmtTerm \<Rightarrow> bool\<close>
  and toks :: \<open>SmtProblem \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> SmtTerm list \<Rightarrow> bool\<close>
  where
  \<open>tok p F dl el n (SmtTerm_Param k) = (unat k < el)\<close>
| \<open>tok p F dl el n (SmtTerm_Def d args) =
     (unat d < length (sdefs p) \<and> length (dpar (sdefs p ! unat d)) < 2 ^ 64 \<and>
      (if dpar (sdefs p ! unat d) = [] then unat d < dl
       else if unat d < n then length (rvec_elems args) < 2 ^ 64 \<and> length (rvec_elems args) \<le> F \<and> toks p F dl el n (rvec_elems args) \<and>
            tok p F dl (length (rvec_elems args)) (unat d) (SmtDef_body (sdefs p ! unat d))
       else False))\<close>
| \<open>tok p F dl el n (SmtTerm_App op args) =
     (length (rvec_elems args) < 2 ^ 64 \<and> length (rvec_elems args) \<le> F \<and> min_ar op \<le> length (rvec_elems args) \<and> toks p F dl el n (rvec_elems args))\<close>
| \<open>tok p F dl el n _ = True\<close>
| \<open>toks p F dl el n [] = True\<close>
| \<open>toks p F dl el n (a # rest) = (tok p F dl el n a \<and> toks p F dl el n rest)\<close>
  by pat_completeness auto
termination
  by (relation \<open>measures [\<lambda>x. case x of Inl (_, _, _, _, n, _) \<Rightarrow> n | Inr (_, _, _, _, n, _) \<Rightarrow> n,
                          \<lambda>x. case x of Inl (_, _, _, _, _, t) \<Rightarrow> size t | Inr (_, _, _, _, _, ts) \<Rightarrow> size_list size ts]\<close>)
     (auto simp: le_imp_less_Suc size_list_rvec_elems)

text \<open>The depth of the recursion of \<^verbatim>\<open>tr_term\<close> and \<^verbatim>\<open>tr_args\<close>.\<close>
function (sequential) dep :: \<open>SmtProblem \<Rightarrow> nat \<Rightarrow> SmtTerm \<Rightarrow> nat\<close>
  and deps :: \<open>SmtProblem \<Rightarrow> nat \<Rightarrow> SmtTerm list \<Rightarrow> nat\<close>
  where
  \<open>dep p n (SmtTerm_Def d args) =
     (if dpar (sdefs p ! unat d) = [] then 0
      else if unat d < n then Suc (max (deps p n (rvec_elems args)) (dep p (unat d) (SmtDef_body (sdefs p ! unat d))))
      else 0)\<close>
| \<open>dep p n (SmtTerm_App op args) = Suc (deps p n (rvec_elems args))\<close>
| \<open>dep p n _ = 0\<close>
| \<open>deps p n [] = 0\<close>
| \<open>deps p n (a # rest) = max (Suc (dep p n a)) (deps p n rest)\<close>
  by pat_completeness auto
termination
  by (relation \<open>measures [\<lambda>x. case x of Inl (_, n, _) \<Rightarrow> n | Inr (_, n, _) \<Rightarrow> n,
                          \<lambda>x. case x of Inl (_, _, t) \<Rightarrow> size t | Inr (_, _, ts) \<Rightarrow> size_list size ts]\<close>)
     (auto simp: le_imp_less_Suc size_list_rvec_elems)

lemma toks_iff: \<open>toks p F dl el n ts = (\<forall>a \<in> set ts. tok p F dl el n a)\<close>
  by (induction ts) auto

lemma deps_ge: \<open>a \<in> set ts \<Longrightarrow> Suc (dep p n a) \<le> deps p n ts\<close>
  by (induction ts) auto

lemma deps_le: \<open>deps p n ts \<le> k \<Longrightarrow> a \<in> set ts \<Longrightarrow> Suc (dep p n a) \<le> k\<close>
  using deps_ge[of a ts p n] by simp

lemma deps_nth: \<open>deps p n ts \<le> k \<Longrightarrow> i < length ts \<Longrightarrow> Suc (dep p n (ts ! i)) \<le> k\<close>
  using deps_le[of p n ts k \<open>ts ! i\<close>] by simp

lemma toks_nth: \<open>toks p F dl el n ts \<Longrightarrow> i < length ts \<Longrightarrow> tok p F dl el n (ts ! i)\<close>
  by (simp add: toks_iff)

text \<open>The bound \<open>n\<close> does not matter once the expanded definitions are below it.\<close>
lemma tok_n_indep:
  \<open>tok p F dl el n t \<Longrightarrow> n \<le> n' \<Longrightarrow>
     tok p F dl el n' t \<and> dep p n' t = dep p n t \<and> tr_term_m p dm env n' S t = tr_term_m p dm env n S t\<close>
  \<open>toks p F dl el n ts \<Longrightarrow> n \<le> n' \<Longrightarrow>
     toks p F dl el n' ts \<and> deps p n' ts = deps p n ts \<and> tr_args_m p dm env n' S ts = tr_args_m p dm env n S ts\<close>
proof (induction p F dl el n t and p F dl el n ts arbitrary: env S n' and env S n' rule: tok_toks.induct)
  case (2 p F dl el n d args)
  show ?case
  proof (cases \<open>dpar (sdefs p ! unat d) = []\<close>)
    case True
    then show ?thesis using 2(3) by simp
  next
    case False
    have a: \<open>unat d < n\<close> \<open>toks p F dl el n (rvec_elems args)\<close> using 2(3) False by (auto split: if_splits)
    note I = 2(1)[OF False a(1) a(2) 2(4)]
    show ?thesis using I 2(3) 2(4) False a by (auto simp: Let_def split: if_splits)
  qed
next
  case (3 p F dl el n op args)
  have a: \<open>toks p F dl el n (rvec_elems args)\<close> using 3(2) by simp
  show ?case using 3(1)[OF a 3(3)] 3(2) by (simp add: Let_def)
next
  case (6 p F dl el n a rest)
  have t: \<open>tok p F dl el n a\<close> \<open>toks p F dl el n rest\<close> using 6(3) by simp_all
  show ?case using 6(1)[OF t(1) 6(4)] 6(2)[OF t(2) 6(4)] by (simp add: Let_def)
qed simp_all

subsection \<open>The precondition holds for a well-sorted problem\<close>

lemma bin_width_len: \<open>smt_bin_width ss \<noteq> None \<Longrightarrow> length ss = 2\<close>
  by (auto simp: smt_bin_width_def split: list.splits SmtSort.splits)

lemma bin_width_len': \<open>smt_bin_width ss = Some y \<Longrightarrow> length ss = 2\<close>
  using bin_width_len by fastforce

lemma min_ar_sort: \<open>smt_op_sort op ss \<noteq> None \<Longrightarrow> min_ar op \<le> length ss\<close>
  by (cases op) (auto simp: smt_same_width_def dest: bin_width_len' split: list.splits SmtSort.splits if_splits)

text \<open>The largest number of arguments of a node of a term.\<close>
function (sequential) margs :: \<open>SmtTerm \<Rightarrow> nat\<close> and margss :: \<open>SmtTerm list \<Rightarrow> nat\<close> where
  \<open>margs (SmtTerm_Def d args) = max (length (rvec_elems args)) (margss (rvec_elems args))\<close>
| \<open>margs (SmtTerm_App op args) = max (length (rvec_elems args)) (margss (rvec_elems args))\<close>
| \<open>margs _ = 0\<close>
| \<open>margss [] = 0\<close>
| \<open>margss (a # rest) = max (margs a) (margss rest)\<close>
  by pat_completeness auto
termination
  by (relation \<open>measure (\<lambda>x. case x of Inl t \<Rightarrow> size t | Inr ts \<Rightarrow> size_list size ts)\<close>)
     (auto simp: le_imp_less_Suc size_list_rvec_elems)

text \<open>A bound on the fuel the translation of \<open>p\<close> needs: the lengths of the lists of \<open>p\<close>, the
  numbers of arguments, and the depths of the recursion.\<close>
definition N :: \<open>SmtProblem \<Rightarrow> nat\<close> where
  \<open>N p \<equiv>
     let ds = sdefs p; ts = sasserts p in
     length (sfuns p) + length ds + length ts +
     sum_list (map (\<lambda>d. margs (SmtDef_body d)) ds) + sum_list (map margs ts) +
     sum_list (map (\<lambda>d. Suc (dep p d (SmtDef_body (ds ! d)))) [0..<length ds]) +
     sum_list (map (\<lambda>t. Suc (dep p (length ds) t)) ts)\<close>

text \<open>What \<^verbatim>\<open>tr_problem\<close> needs, for the fuel \<open>F\<close>.\<close>
definition tr_pre :: \<open>nat \<Rightarrow> SmtProblem \<Rightarrow> bool\<close> where
  \<open>tr_pre F p \<equiv>
     let ds = sdefs p; L = length ds in
     length (sfuns p) < 2 ^ 64 \<and> length (sfuns p) \<le> F \<and> L < 2 ^ 64 \<and> L \<le> F \<and>
     length (sasserts p) < 2 ^ 64 \<and> length (sasserts p) \<le> F \<and>
     (\<forall>d < L. length (dpar (ds ! d)) < 2 ^ 64 \<and>
        (dpar (ds ! d) = [] \<longrightarrow> tok p F d 0 d (SmtDef_body (ds ! d)) \<and> Suc (dep p d (SmtDef_body (ds ! d))) \<le> F)) \<and>
     (\<forall>t \<in> set (sasserts p). tok p F L 0 L t \<and> Suc (dep p L t) \<le> F)\<close>

text \<open>What a well-sorted problem whose lists are within the bounds gives for each definition.\<close>
definition defs_ok :: \<open>SmtProblem \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>defs_ok p F \<equiv> \<forall>d < length (sdefs p).
      smt_tsort (sfuns p) (take d (sdefs p)) (dpar (sdefs p ! d))
        (SmtDef_body (sdefs p ! d)) \<noteq> None \<and>
      smt_term_repr (SmtDef_body (sdefs p ! d)) \<and> margs (SmtDef_body (sdefs p ! d)) \<le> F \<and>
      length (dpar (sdefs p ! d)) < 2 ^ 64\<close>

lemma tok_of_wf:
  shows \<open>defs_ok p F \<Longrightarrow> smt_tsort (sfuns p) (take n (sdefs p)) ps t \<noteq> None \<Longrightarrow> smt_term_repr t \<Longrightarrow>
           margs t \<le> F \<Longrightarrow> n \<le> length (sdefs p) \<Longrightarrow> n \<le> dl \<Longrightarrow> el = length ps \<Longrightarrow>
           tok p F dl el n t\<close>
    and \<open>defs_ok p F \<Longrightarrow> \<forall>a \<in> set ts. smt_tsort (sfuns p) (take n (sdefs p)) ps a \<noteq> None \<and> smt_term_repr a \<Longrightarrow>
           margss ts \<le> F \<Longrightarrow> n \<le> length (sdefs p) \<Longrightarrow> n \<le> dl \<Longrightarrow> el = length ps \<Longrightarrow>
           toks p F dl el n ts\<close>
proof (induction p F dl el n t and p F dl el n ts arbitrary: ps and ps rule: tok_toks.induct)
  case (2 p F dl el n d args)
  note P = 2(3-9)
  let ?ds = \<open>sdefs p\<close>
  let ?D = \<open>?ds ! unat d\<close>
  have d: \<open>unat d < n\<close> \<open>unat d < length ?ds\<close>
    and M: \<open>map (smt_tsort (sfuns p) (take n ?ds) ps) (rvec_elems args) = map Some (dpar ?D)\<close>
    using P(2) P(5) by (auto split: if_splits)
  have A: \<open>\<forall>a \<in> set (rvec_elems args). smt_tsort (sfuns p) (take n ?ds) ps a \<noteq> None \<and> smt_term_repr a\<close>
    using map_Some_ex[OF M] P(3) by fastforce
  have len: \<open>length (rvec_elems args) = length (dpar ?D)\<close> using M map_eq_imp_length_eq by fastforce
  have Wd: \<open>smt_tsort (sfuns p) (take (unat d) ?ds) (dpar ?D) (SmtDef_body ?D) \<noteq> None\<close>
    \<open>smt_term_repr (SmtDef_body ?D)\<close> \<open>margs (SmtDef_body ?D) \<le> F\<close> \<open>length (dpar ?D) < 2 ^ 64\<close>
    using P(1) d(2) by (simp_all add: defs_ok_def)
  show ?case
  proof (cases \<open>dpar ?D = []\<close>)
    case True
    then show ?thesis using d P(6) Wd by simp
  next
    case False
    have T: \<open>toks p F dl el n (rvec_elems args)\<close> using 2(1)[OF False d(1) P(1) A] P(4-7) by simp
    have B: \<open>tok p F dl (length (rvec_elems args)) (unat d) (SmtDef_body ?D)\<close>
      using 2(2)[OF False d(1) P(1) Wd(1-3)] len d P(5,6) by simp
    show ?thesis using d T B Wd False P(3) P(4) by simp
  qed
next
  case (3 p F dl el n op args)
  note P = 3(2-8)
  have A: \<open>\<forall>a \<in> set (rvec_elems args). smt_tsort (sfuns p) (take n (sdefs p)) ps a \<noteq> None \<and> smt_term_repr a\<close>
    using P(2) P(3) by (auto split: if_splits) (metis image_eqI option.exhaust)
  have S: \<open>smt_op_sort op (map (the \<circ> smt_tsort (sfuns p) (take n (sdefs p)) ps) (rvec_elems args)) \<noteq> None\<close>
    using P(2) by (auto split: if_splits)
  have T: \<open>toks p F dl el n (rvec_elems args)\<close> using 3(1)[OF P(1) A] P(4-7) by simp
  show ?case using min_ar_sort[OF S] T P(3) P(4) by simp
qed (auto split: if_splits)

lemma N_ge:
  \<open>length (sfuns p) \<le> N p\<close> \<open>length (sdefs p) \<le> N p\<close> \<open>length (sasserts p) \<le> N p\<close>
  \<open>e \<in> set (sdefs p) \<Longrightarrow> margs (SmtDef_body e) \<le> N p\<close>
  \<open>t \<in> set (sasserts p) \<Longrightarrow> margs t \<le> N p\<close>
  \<open>d < length (sdefs p) \<Longrightarrow> Suc (dep p d (SmtDef_body (sdefs p ! d))) \<le> N p\<close>
  \<open>t \<in> set (sasserts p) \<Longrightarrow> Suc (dep p (length (sdefs p)) t) \<le> N p\<close>
proof -
  have m: \<open>\<And>x xs. x \<in> set xs \<Longrightarrow> x \<le> sum_list (xs :: nat list)\<close> by (simp add: member_le_sum_list)
  show \<open>length (sfuns p) \<le> N p\<close> \<open>length (sdefs p) \<le> N p\<close> \<open>length (sasserts p) \<le> N p\<close>
    by (simp_all add: N_def Let_def)
  show \<open>margs (SmtDef_body e) \<le> N p\<close> if \<open>e \<in> set (sdefs p)\<close>
    using that m[of \<open>margs (SmtDef_body e)\<close> \<open>map (\<lambda>d. margs (SmtDef_body d)) (sdefs p)\<close>] by (simp add: N_def Let_def)
  show \<open>margs t \<le> N p\<close> if \<open>t \<in> set (sasserts p)\<close>
    using that m[of \<open>margs t\<close> \<open>map margs (sasserts p)\<close>] by (simp add: N_def Let_def)
  show \<open>Suc (dep p d (SmtDef_body (sdefs p ! d))) \<le> N p\<close> if \<open>d < length (sdefs p)\<close>
    using that m[of \<open>Suc (dep p d (SmtDef_body (sdefs p ! d)))\<close>
        \<open>map (\<lambda>d. Suc (dep p d (SmtDef_body (sdefs p ! d)))) [0..<length (sdefs p)]\<close>]
    by (simp add: N_def Let_def)
  show \<open>Suc (dep p (length (sdefs p)) t) \<le> N p\<close> if \<open>t \<in> set (sasserts p)\<close>
    using that m[of \<open>Suc (dep p (length (sdefs p)) t)\<close> \<open>map (\<lambda>t. Suc (dep p (length (sdefs p)) t)) (sasserts p)\<close>]
    by (simp add: N_def Let_def)
qed

text \<open>The facts the top-level proof supplies imply the precondition of \<^verbatim>\<open>tr_problem\<close>.\<close>
lemma tr_problem_pre:
  assumes W: \<open>smt_wf p\<close> and R: \<open>smt_repr_ok p\<close> and NF: \<open>N p \<le> F\<close>
  shows \<open>tr_pre F p\<close>
proof -
  let ?ds = \<open>sdefs p\<close>
  have D: \<open>defs_ok p F\<close>
    unfolding defs_ok_def
  proof (intro allI impI conjI)
    fix d assume d: \<open>d < length ?ds\<close>
    show \<open>smt_tsort (sfuns p) (take d ?ds) (dpar (?ds ! d)) (SmtDef_body (?ds ! d)) \<noteq> None\<close>
      using W d by (simp add: smt_wf_def Let_def)
    have r: \<open>length (dpar (?ds ! d)) < 2 ^ 63 \<and> smt_term_repr (SmtDef_body (?ds ! d))\<close>
      using R nth_mem[OF d] unfolding smt_repr_ok_def by blast
    then show \<open>smt_term_repr (SmtDef_body (?ds ! d))\<close> \<open>length (dpar (?ds ! d)) < 2 ^ 64\<close> by simp_all
    show \<open>margs (SmtDef_body (?ds ! d)) \<le> F\<close> using N_ge(4)[OF nth_mem[OF d]] NF by simp
  qed
  have defs: \<open>tok p F d 0 d (SmtDef_body (?ds ! d)) \<and> Suc (dep p d (SmtDef_body (?ds ! d))) \<le> F\<close>
    if d: \<open>d < length ?ds\<close> and e: \<open>dpar (?ds ! d) = []\<close> for d
  proof
    have \<open>smt_tsort (sfuns p) (take d ?ds) (dpar (?ds ! d)) (SmtDef_body (?ds ! d)) =
            Some (SmtDef_ret (?ds ! d))\<close>
      using W d unfolding smt_wf_def Let_def by blast
    then have t: \<open>smt_tsort (sfuns p) (take d ?ds) [] (SmtDef_body (?ds ! d)) \<noteq> None\<close>
      using e by simp
    show \<open>tok p F d 0 d (SmtDef_body (?ds ! d))\<close>
      using tok_of_wf(1)[OF D t] D d by (simp add: defs_ok_def)
    show \<open>Suc (dep p d (SmtDef_body (?ds ! d))) \<le> F\<close> using N_ge(6)[OF d] NF by simp
  qed
  have asserts: \<open>tok p F (length ?ds) 0 (length ?ds) t \<and> Suc (dep p (length ?ds) t) \<le> F\<close>
    if t: \<open>t \<in> set (sasserts p)\<close> for t
  proof
    have s: \<open>smt_tsort (sfuns p) (take (length ?ds) ?ds) [] t \<noteq> None\<close>
      using W t by (simp add: smt_wf_def Let_def)
    show \<open>tok p F (length ?ds) 0 (length ?ds) t\<close>
      using tok_of_wf(1)[OF D s] R t N_ge(5)[OF t] NF by (simp add: smt_repr_ok_def)
    show \<open>Suc (dep p (length ?ds) t) \<le> F\<close> using N_ge(7)[OF t] NF by simp
  qed
  show ?thesis
    unfolding tr_pre_def Let_def
    using defs asserts R N_ge(1-3)[of p] NF D by (auto simp: smt_repr_ok_def defs_ok_def)
qed

text \<open>The facts the top-level proof supplies imply the precondition of \<^verbatim>\<open>tr_model\<close>.\<close>
lemma tr_model_pre:
  assumes \<open>is_model (tr_problem_m p) m\<close> \<open>smt_repr_ok p\<close> \<open>N p \<le> F\<close>
  shows \<open>length (sfuns p) < 2 ^ 64 \<and> length (sfuns p) \<le> F \<and>
         length (sfuns p) \<le> length m \<and>
         (\<forall>i < length (sfuns p). SmtFun_ret (sfuns p ! i) = SmtSort_Bool \<longrightarrow> m ! i \<noteq> [])\<close>
proof -
  have M: \<open>map length m = map (\<lambda>f. unat (word_of_nat (sort_width_m (SmtFun_ret f)) :: 64 word)) (sfuns p)\<close>
    using assms(1) by (simp add: is_model_def is_assignment_def var_widths_def tr_problem_m_def Let_def)
  have l: \<open>length m = length (sfuns p)\<close> using map_eq_imp_length_eq[OF M] by simp
  have b: \<open>m ! i \<noteq> []\<close> if i: \<open>i < length (sfuns p)\<close> and r: \<open>SmtFun_ret (sfuns p ! i) = SmtSort_Bool\<close> for i
  proof -
    have \<open>map length m ! i = length (m ! i)\<close> using i l by simp
    then have \<open>length (m ! i) = 1\<close> using M i r by simp
    then show ?thesis by auto
  qed
  show ?thesis using l b assms(2,3) N_ge(1)[of p] by (simp add: smt_repr_ok_def)
qed

text \<open>The facts the top-level proof supplies imply the precondition of \<^verbatim>\<open>in_fragment\<close>.\<close>
lemma in_fragment_pre:
  assumes \<open>smt_repr_ok p\<close> \<open>N p \<le> F\<close>
  shows \<open>length (sfuns p) < 2 ^ 64 \<and> length (sfuns p) \<le> F \<and>
         (\<forall>f \<in> set (sfuns p). length (fargs f) < 2 ^ 64)\<close>
  using assms N_ge(1)[of p] by (auto simp: smt_repr_ok_def)

subsection \<open>Indices as words\<close>

text \<open>The translation uses the indices of definitions only through \<^const>\<open>tref\<close>, so taking them
  modulo \<open>2^64\<close> (a round trip through \<^typ>\<open>64 word\<close>) does not change it.\<close>
definition wr :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>wr k \<equiv> unat (word_of_nat k :: 64 word)\<close>

lemma map_unat_wn: \<open>map unat (map word_of_nat ks :: 64 word list) = map wr ks\<close>
  by (simp add: wr_def)

lemma tref_wr: \<open>tref (wr k) = tref k\<close>
  by (simp add: tref_def wr_def)

lemma tref_nth_wr: \<open>tref (map wr ks ! i) = tref (ks ! i)\<close>
proof (induction ks arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons k ks)
  then show ?case by (cases i) (simp_all add: tref_wr)
qed

lemma tr_app_wr: \<open>tr_app_m op (map wr ks) = tr_app_m op ks\<close>
proof (cases \<open>ks = []\<close>)
  case True
  then show ?thesis by simp
next
  case False
  then show ?thesis
    by (cases op) (simp_all add: fold_left_m_def chain_m_def pairwise_m_def implies_m_def hd_map last_map
        map_tl[symmetric] map_butlast[symmetric] foldl_map foldr_map tref_wr tref_nth_wr o_def)
qed

lemma tref_nth_wr_eq: \<open>map wr xs = map wr ys \<Longrightarrow> tref (xs ! i) = tref (ys ! i)\<close>
  by (metis tref_nth_wr)

lemma wr_wr: \<open>wr (wr k) = wr k\<close>
  by (simp add: wr_def)

lemma tr_term_wr_gen:
  \<open>map wr dm = map wr dm' \<Longrightarrow> map wr env = map wr env' \<Longrightarrow> tr_term_m p dm env n S t = tr_term_m p dm' env' n S t\<close>
  \<open>map wr dm = map wr dm' \<Longrightarrow> map wr env = map wr env' \<Longrightarrow> tr_args_m p dm env n S ts = tr_args_m p dm' env' n S ts\<close>
proof (induction p dm env n S t and p dm env n S ts arbitrary: dm' env' and dm' env' rule: tr_term_m_tr_args_m.induct)
  case (3 p dm env n S k)
  then show ?case using tref_nth_wr_eq[OF 3(2), of \<open>unat k\<close>] by simp
next
  case (5 p dm env n S d args)
  show ?case using 5(1)[OF _ _ 5(3) 5(4)] 5(2)[OF _ _ refl 5(3) refl] tref_nth_wr_eq[OF 5(3), of \<open>unat d\<close>]
    by (simp add: Let_def)
next
  case (6 p dm env n S op args)
  then show ?case by (simp add: Let_def)
next
  case (8 p dm env n S a rest)
  then show ?case by (simp add: Let_def)
qed simp_all

lemma wn_len_0: \<open>length xs < 2 ^ 64 \<Longrightarrow> (word_of_nat (length xs) = (0 :: 64 word)) = (xs = [])\<close>
  by (auto simp: word_of_nat_eq_0_iff dest: nat_dvd_not_less)

lemma tr_term_wr_env: \<open>tr_term_m p dm (map wr env) n S t = tr_term_m p dm env n S t\<close>
  by (rule tr_term_wr_gen) (simp_all add: wr_wr)

lemma map_wr_comp: \<open>map (unat \<circ> (word_of_nat :: nat \<Rightarrow> 64 word)) xs = map wr xs\<close>
  by (simp add: wr_def o_def)

lemma tr_term_wr:
  \<open>tr_term_m p (map wr dm) (map wr env) n S t = tr_term_m p dm env n S t\<close>
  by (rule tr_term_wr_gen) (simp_all add: wr_wr)


lemma tref_word: \<open>tref (unat (word_of_nat k :: 64 word)) = tref k\<close>
  by (simp add: tref_def)

lemma tr_args_snoc:
  \<open>tr_args_m p dm env n S (xs @ [a]) =
     (fst (tr_term_m p dm env n (fst (tr_args_m p dm env n S xs)) a) @ [snd (tr_term_m p dm env n (fst (tr_args_m p dm env n S xs)) a)],
      snd (tr_args_m p dm env n S xs) @ [length (fst (tr_term_m p dm env n (fst (tr_args_m p dm env n S xs)) a))])\<close>
  by (induction xs arbitrary: S) (simp_all add: Let_def)

lemma tr_args_take_Suc:
  \<open>i < length ts \<Longrightarrow> tr_args_m p dm env n S (take (Suc i) ts) =
     (fst (tr_term_m p dm env n (fst (tr_args_m p dm env n S (take i ts))) (ts ! i)) @
        [snd (tr_term_m p dm env n (fst (tr_args_m p dm env n S (take i ts))) (ts ! i))],
      snd (tr_args_m p dm env n S (take i ts)) @
        [length (fst (tr_term_m p dm env n (fst (tr_args_m p dm env n S (take i ts))) (ts ! i)))])\<close>
  by (simp add: take_Suc_conv_app_nth tr_args_snoc)

lemma tr_args_len: \<open>length (snd (tr_args_m p dm env n S ts)) = length ts\<close>
  by (induction ts arbitrary: S) (simp_all add: Let_def)

lemma make_Tr_defs: \<open>make_Tr (Tr_defs s) = s\<close>
  by (cases s) simp

subsection \<open>The loops of the builders in closed form\<close>

definition fl_acc :: \<open>SmtOp \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> TermL\<close> where
  \<open>fl_acc op ks m \<equiv> foldl (\<lambda>acc j. TermL_Bin (tr_op op) acc (tref (ks ! j))) (tref (ks ! 0)) [1..<m]\<close>

lemma fl_acc_Suc: \<open>1 \<le> m \<Longrightarrow> fl_acc op ks (Suc m) = TermL_Bin (tr_op op) (fl_acc op ks m) (tref (ks ! m))\<close>
  by (simp add: fl_acc_def)

lemma tl_nth_upt: \<open>tl ks = map ((!) ks) [1..<length ks]\<close>
  by (simp add: list_eq_iff_nth_eq nth_tl)

lemma fold_left_fl: \<open>ks \<noteq> [] \<Longrightarrow> fold_left_m op ks = fl_acc op ks (length ks)\<close>
  by (simp add: fold_left_m_def fl_acc_def hd_conv_nth tl_nth_upt foldl_map)

lemma fold_left_fl': \<open>1 \<le> length ks \<Longrightarrow> fold_left_m op ks = fl_acc op ks (length ks)\<close>
  by (cases ks) (simp_all add: fold_left_fl)

lemma fl_acc_1: \<open>fl_acc op ks (Suc 0) = tref (ks ! 0)\<close>
  by (simp add: fl_acc_def)

definition ch_acc :: \<open>SmtOp \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> TermL\<close> where
  \<open>ch_acc op ks m \<equiv>
     foldl (\<lambda>acc i. TermL_Bin Op_And acc (TermL_Bin (tr_op op) (tref (ks ! (i - 1))) (tref (ks ! i))))
       (TermL_Bin (tr_op op) (tref (ks ! 0)) (tref (ks ! 1))) [2..<m]\<close>

lemma ch_acc_Suc:
  \<open>2 \<le> m \<Longrightarrow> ch_acc op ks (Suc m) =
     TermL_Bin Op_And (ch_acc op ks m) (TermL_Bin (tr_op op) (tref (ks ! (m - 1))) (tref (ks ! m)))\<close>
  by (simp add: ch_acc_def)

lemma chain_ch: \<open>chain_m op ks = ch_acc op ks (length ks)\<close>
  by (simp add: chain_m_def ch_acc_def)

lemma ch_acc_2:
  \<open>2 \<le> length ksw \<Longrightarrow> ch_acc op (map unat ksw) 2 = TermL_Bin (tr_op op) (tref (unat (ksw ! 0))) (tref (unat (ksw ! 1)))\<close>
  by (cases ksw; cases \<open>tl ksw\<close>) (simp_all add: ch_acc_def)

lemma unat_minus_1': \<open>1 \<le> unat w \<Longrightarrow> unat (w - 1) = unat w - 1\<close> for w :: \<open>64 word\<close>
  by (simp add: unat_sub word_le_nat_alt)

definition pw_step :: \<open>nat list \<Rightarrow> TermL \<Rightarrow> nat \<times> nat \<Rightarrow> TermL\<close> where
  \<open>pw_step ks acc ij \<equiv> TermL_Bin Op_And acc (TermL_Bin Op_Distinct (tref (ks ! fst ij)) (tref (ks ! snd ij)))\<close>

definition pw_acc :: \<open>nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> TermL\<close> where
  \<open>pw_acc ks i j \<equiv>
     foldl (pw_step ks) (TermL_Bin Op_Distinct (tref (ks ! 0)) (tref (ks ! 1)))
       (filter (\<lambda>ij. ij \<noteq> (0, 1))
          (concat (map (\<lambda>i'. map (\<lambda>j'. (i', j')) [Suc i'..<length ks]) [0..<i]) @ map (\<lambda>j'. (i, j')) [Suc i..<j]))\<close>

lemma pw_acc_Suc:
  \<open>Suc i \<le> j \<Longrightarrow> pw_acc ks i (Suc j) = (if i \<noteq> 0 \<or> j \<noteq> 1 then pw_step ks (pw_acc ks i j) (i, j) else pw_acc ks i j)\<close>
  by (simp add: pw_acc_def)

lemma pw_acc_next: \<open>pw_acc ks i (length ks) = pw_acc ks (Suc i) (Suc (Suc i))\<close>
  by (simp add: pw_acc_def)

lemma pw_acc_next': \<open>pw_acc (map f xs) i (length xs) = pw_acc (map f xs) (Suc i) (Suc (Suc i))\<close>
  using pw_acc_next[of \<open>map f xs\<close> i] by simp

lemma pairwise_pw: \<open>pairwise_m ks = pw_acc ks (length ks) (Suc (length ks))\<close>
  by (simp add: pairwise_m_def pairs_m_def pw_acc_def pw_step_def[abs_def])

lemma pw_acc_0:
  \<open>2 \<le> length ksw \<Longrightarrow> pw_acc (map unat ksw) 0 (Suc 0) = TermL_Bin Op_Distinct (tref (unat (ksw ! 0))) (tref (unat (ksw ! Suc 0)))\<close>
  by (cases ksw; cases \<open>tl ksw\<close>) (simp_all add: pw_acc_def)

lemma unat_one_iff: \<open>(unat (j :: 64 word) = Suc 0) = (j = 1)\<close>
  by (metis One_nat_def unat_1 word_unat.Rep_inject)

lemma pw_acc_skip: \<open>pw_acc ks 0 2 = pw_acc ks 0 (Suc 0)\<close>
  by (simp add: pw_acc_def numeral_2_eq_2)

lemma unat_Suc_le: \<open>Suc (unat (r :: 64 word)) \<le> n \<Longrightarrow> n < 2 ^ 64 \<Longrightarrow> unat (r + 1) = Suc (unat r)\<close>
  by (rule unat_plus_one_of_less_bound) auto

definition im_acc :: \<open>nat list \<Rightarrow> nat \<Rightarrow> TermL\<close> where
  \<open>im_acc ks i \<equiv> foldr (\<lambda>k acc. TermL_Bin Op_Or (TermL_Not (tref k)) acc) (drop i (butlast ks)) (tref (last ks))\<close>

lemma implies_im: \<open>implies_m ks = im_acc ks 0\<close>
  by (simp add: implies_m_def im_acc_def)

lemma im_acc_last: \<open>ks \<noteq> [] \<Longrightarrow> im_acc ks (length ks - 1) = tref (ks ! (length ks - 1))\<close>
  by (simp add: im_acc_def last_conv_nth)

lemma im_acc_step:
  \<open>i < length ks - 1 \<Longrightarrow> im_acc ks i = TermL_Bin Op_Or (TermL_Not (tref (ks ! i))) (im_acc ks (Suc i))\<close>
  by (simp add: im_acc_def Cons_nth_drop_Suc[symmetric] nth_butlast)

lemma im_acc_pred:
  \<open>0 < i \<Longrightarrow> i \<le> length ks - 1 \<Longrightarrow> im_acc ks (i - 1) = TermL_Bin Op_Or (TermL_Not (tref (ks ! (i - 1)))) (im_acc ks i)\<close>
  using im_acc_step[of \<open>i - 1\<close> ks] by simp

lemma im_acc_pred':
  \<open>0 < i \<Longrightarrow> i \<le> length ksw - Suc 0 \<Longrightarrow>
     im_acc (map unat ksw) (i - Suc 0) = TermL_Bin Op_Or (TermL_Not (tref (unat (ksw ! (i - Suc 0))))) (im_acc (map unat ksw) i)\<close>
  using im_acc_pred[of i \<open>map unat ksw\<close>] by simp

lemma im_acc_last':
  \<open>1 \<le> length ksw \<Longrightarrow> im_acc (map unat ksw) (length ksw - Suc 0) = tref (unat (ksw ! (length ksw - Suc 0)))\<close>
proof -
  assume a: \<open>1 \<le> length ksw\<close>
  then have n: \<open>map unat ksw \<noteq> []\<close> by auto
  have l: \<open>length ksw - 1 < length ksw\<close> using a by simp
  show ?thesis using im_acc_last[OF n] nth_map[OF l, of unat] by simp
qed

subsection \<open>The loops of \<^verbatim>\<open>tr_problem\<close> in closed form\<close>

definition TD :: \<open>SmtProblem \<Rightarrow> nat \<Rightarrow> TermL list \<times> nat list\<close> where
  \<open>TD p j \<equiv> foldl (tr_defs_step p) ([], []) [0..<j]\<close>

lemma TD_0: \<open>TD p 0 = ([], [])\<close>
  by (simp add: TD_def)

lemma TD_Suc:
  \<open>TD p (Suc j) =
     (if dpar (sdefs p ! j) = []
      then (fst (tr_term_m p (snd (TD p j)) [] j (fst (TD p j)) (SmtDef_body (sdefs p ! j))) @
              [snd (tr_term_m p (snd (TD p j)) [] j (fst (TD p j)) (SmtDef_body (sdefs p ! j)))],
            snd (TD p j) @ [length (fst (tr_term_m p (snd (TD p j)) [] j (fst (TD p j)) (SmtDef_body (sdefs p ! j))))])
      else (fst (TD p j), snd (TD p j) @ [0]))\<close>
  by (simp add: TD_def tr_defs_step_def split_def Let_def)

lemma TD_len: \<open>length (snd (TD p j)) = j\<close>
  by (induction j) (simp_all add: TD_0 TD_Suc)

definition TA :: \<open>SmtProblem \<Rightarrow> nat \<Rightarrow> TermL list \<times> TermL list\<close> where
  \<open>TA p j \<equiv> foldl (tr_asserts_step p (snd (TD p (length (sdefs p)))))
     (fst (TD p (length (sdefs p))), []) (take j (sasserts p))\<close>

lemma TA_0: \<open>TA p 0 = (fst (TD p (length (sdefs p))), [])\<close>
  by (simp add: TA_def)

lemma TA_Suc:
  \<open>j < length (sasserts p) \<Longrightarrow> TA p (Suc j) =
     (fst (tr_term_m p (snd (TD p (length (sdefs p)))) [] (length (sdefs p)) (fst (TA p j)) (sasserts p ! j)),
      snd (TA p j) @
        [snd (tr_term_m p (snd (TD p (length (sdefs p)))) [] (length (sdefs p)) (fst (TA p j)) (sasserts p ! j))])\<close>
  by (simp add: TA_def take_Suc_conv_app_nth tr_asserts_step_def split_def Let_def)

lemma TA_final: \<open>TA p (length (sasserts p)) = tr_asserts_m p (tr_defs_m p)\<close>
  by (simp add: TA_def TD_def tr_asserts_m_step tr_defs_m_step)

lemma tr_problem_TA:
  \<open>tr_problem_m p =
     make_ProblemL (map (\<lambda>f. word_of_nat (sort_width_m (SmtFun_ret f))) (sfuns p))
       (fst (TA p (length (sasserts p)))) (snd (TA p (length (sasserts p))))\<close>
  by (simp add: tr_problem_m_def TA_final Let_def)

lemma tr_term_wr_dm: \<open>tr_term_m p (map wr dm) env n S t = tr_term_m p dm env n S t\<close>
  by (rule tr_term_wr_gen) (simp_all add: wr_wr)

text \<open>The facts \<^verbatim>\<open>tr_problem\<close> uses from \<^const>\<open>tr_pre\<close>.\<close>
lemma tr_pre_facts:
  assumes P: \<open>tr_pre F p\<close>
  shows \<open>length (sfuns p) < 2 ^ 64\<close> \<open>length (sfuns p) \<le> F\<close>
    \<open>length (sdefs p) < 2 ^ 64\<close> \<open>length (sdefs p) \<le> F\<close>
    \<open>length (sasserts p) < 2 ^ 64\<close> \<open>length (sasserts p) \<le> F\<close>
    \<open>\<And>d. d < length (sdefs p) \<Longrightarrow> length (dpar (sdefs p ! d)) < 2 ^ 64\<close>
    \<open>\<And>d. d < length (sdefs p) \<Longrightarrow> dpar (sdefs p ! d) = [] \<Longrightarrow>
        tok p F d 0 (length (sdefs p)) (SmtDef_body (sdefs p ! d))\<close>
    \<open>\<And>d. d < length (sdefs p) \<Longrightarrow> dpar (sdefs p ! d) = [] \<Longrightarrow>
        Suc (dep p (length (sdefs p)) (SmtDef_body (sdefs p ! d))) \<le> F\<close>
    \<open>\<And>d dm S. d < length (sdefs p) \<Longrightarrow> dpar (sdefs p ! d) = [] \<Longrightarrow>
        tr_term_m p dm [] (length (sdefs p)) S (SmtDef_body (sdefs p ! d)) =
        tr_term_m p dm [] d S (SmtDef_body (sdefs p ! d))\<close>
    \<open>\<And>j. j < length (sasserts p) \<Longrightarrow>
        tok p F (length (sdefs p)) 0 (length (sdefs p)) (sasserts p ! j)\<close>
    \<open>\<And>j. j < length (sasserts p) \<Longrightarrow> Suc (dep p (length (sdefs p)) (sasserts p ! j)) \<le> F\<close>
proof -
  note Q = P[unfolded tr_pre_def Let_def]
  show \<open>length (sfuns p) < 2 ^ 64\<close> \<open>length (sfuns p) \<le> F\<close>
    \<open>length (sdefs p) < 2 ^ 64\<close> \<open>length (sdefs p) \<le> F\<close>
    \<open>length (sasserts p) < 2 ^ 64\<close> \<open>length (sasserts p) \<le> F\<close>
    using Q by simp_all
  show \<open>length (dpar (sdefs p ! d)) < 2 ^ 64\<close> if \<open>d < length (sdefs p)\<close> for d
    using Q that by blast
  fix d dm S
  assume d: \<open>d < length (sdefs p)\<close> and e: \<open>dpar (sdefs p ! d) = []\<close>
  have t: \<open>tok p F d 0 d (SmtDef_body (sdefs p ! d))\<close> and u: \<open>Suc (dep p d (SmtDef_body (sdefs p ! d))) \<le> F\<close>
    using Q d e by blast+
  note I = tok_n_indep(1)[OF t, where n'=\<open>length (sdefs p)\<close> and dm=dm and env=\<open>[]\<close> and S=S]
  show \<open>tok p F d 0 (length (sdefs p)) (SmtDef_body (sdefs p ! d))\<close>
    \<open>Suc (dep p (length (sdefs p)) (SmtDef_body (sdefs p ! d))) \<le> F\<close>
    \<open>tr_term_m p dm [] (length (sdefs p)) S (SmtDef_body (sdefs p ! d)) =
        tr_term_m p dm [] d S (SmtDef_body (sdefs p ! d))\<close>
    using I d u by simp_all
next
  note Q = P[unfolded tr_pre_def Let_def]
  fix j assume j: \<open>j < length (sasserts p)\<close>
  show \<open>tok p F (length (sdefs p)) 0 (length (sdefs p)) (sasserts p ! j)\<close>
    \<open>Suc (dep p (length (sdefs p)) (sasserts p ! j)) \<le> F\<close>
    using Q nth_mem[OF j] by blast+
qed

subsection \<open>Vectors of the translation\<close>

text \<open>The definitions of a state of the translation, as the model sees them.\<close>
abbreviation tdefs :: \<open>Tr \<Rightarrow> TermL list\<close> where
  \<open>tdefs s \<equiv> map term_of (rvec_elems (Tr_defs s))\<close>

lemma tref_unat [simp]: \<open>QFBV_SmtModel.tref (unat k) = TermL_Ref k\<close>
  by (simp add: QFBV_SmtModel.tref_def)

lemma tr_term_len: \<open>length S \<le> length (fst (tr_term_m p dm env n S t))\<close>
  using tr_prefix(1)[of p dm env n S t] by (cases \<open>tr_term_m p dm env n S t\<close>) auto

lemma tr_args_len_ge: \<open>length S + length ts \<le> length (fst (tr_args_m p dm env n S ts))\<close>
proof (induction ts arbitrary: S)
  case Nil
  then show ?case by simp
next
  case (Cons a ts)
  let ?S1 = \<open>fst (tr_term_m p dm env n S a) @ [snd (tr_term_m p dm env n S a)]\<close>
  have \<open>length ?S1 + length ts \<le> length (fst (tr_args_m p dm env n ?S1 ts))\<close> using Cons.IH .
  moreover have \<open>length S < length ?S1\<close> using tr_term_len[of S p dm env n a] by simp
  ultimately show ?case by (simp add: Let_def)
qed

lemma tref_map_unat: \<open>i < length xs \<Longrightarrow> QFBV_SmtModel.tref (map unat xs ! i) = TermL_Ref (xs ! i)\<close>
  by simp

lemma tr_args_append:
  \<open>tr_args_m p dm env n S (xs @ ys) =
     (fst (tr_args_m p dm env n (fst (tr_args_m p dm env n S xs)) ys),
      snd (tr_args_m p dm env n S xs) @ snd (tr_args_m p dm env n (fst (tr_args_m p dm env n S xs)) ys))\<close>
  by (induction xs arbitrary: S) (simp_all add: Let_def)

lemma tr_args_take_le:
  \<open>length (fst (tr_args_m p dm env n S (take i ts))) + (length ts - i) \<le> length (fst (tr_args_m p dm env n S ts))\<close>
proof -
  have \<open>length (fst (tr_args_m p dm env n S (take i ts))) + length (drop i ts) \<le>
      length (fst (tr_args_m p dm env n (fst (tr_args_m p dm env n S (take i ts))) (drop i ts)))\<close>
    by (rule tr_args_len_ge)
  then show ?thesis using tr_args_append[of p dm env n S \<open>take i ts\<close> \<open>drop i ts\<close>] by simp
qed

lemma tr_args_step_bound:
  \<open>i < length ts \<Longrightarrow>
   Suc (length (fst (tr_term_m p dm env n (fst (tr_args_m p dm env n S (take i ts))) (ts ! i)))) \<le>
     length (fst (tr_args_m p dm env n S ts))\<close>
  using tr_args_take_le[of p dm env n S \<open>Suc i\<close> ts] tr_args_take_Suc[of i ts p dm env n S] by simp

lemma tr_args_idx_bound: \<open>i < length ts \<Longrightarrow> i < length (fst (tr_args_m p dm env n S ts))\<close>
  using tr_args_len_ge[of S ts p dm env n] by simp

lemma tr_args_bounds:
  \<open>i < length ts \<Longrightarrow> length (fst (tr_args_m p dm env n S ts)) < 72057594037927936 \<Longrightarrow>
   i < 72057594037927936 \<and>
   length (fst (tr_term_m p dm env n (fst (tr_args_m p dm env n S (take i ts))) (ts ! i))) < 72057594037927936\<close>
  using tr_args_step_bound[of i ts p dm env n S] tr_args_idx_bound[of i ts p dm env n S] by simp

lemma TD_mono: \<open>length (fst (TD p j)) \<le> length (fst (TD p (j + k)))\<close>
proof (induction k)
  case (Suc k)
  have \<open>length (fst (TD p (j + k))) \<le> length (fst (TD p (Suc (j + k))))\<close>
    using tr_term_len[of \<open>fst (TD p (j + k))\<close>] by (simp add: TD_Suc le_SucI)
  then show ?case using Suc.IH by simp
qed simp

lemma TA_le_final: \<open>length (fst (TA p j)) \<le> length (fst (TA p (length (sasserts p))))\<close>
proof (cases \<open>j \<le> length (sasserts p)\<close>)
  case True
  let ?dm = \<open>snd (TD p (length (sdefs p)))\<close>
  have e: \<open>take (length (sasserts p)) (sasserts p) = take j (sasserts p) @ drop j (sasserts p)\<close> by simp
  have f: \<open>TA p (length (sasserts p)) = foldl (tr_asserts_step p ?dm) (TA p j) (drop j (sasserts p))\<close>
    unfolding TA_def e foldl_append ..
  obtain S acc where s: \<open>TA p j = (S, acc)\<close> by (cases \<open>TA p j\<close>)
  obtain S' acc' where s': \<open>foldl (tr_asserts_step p ?dm) (S, acc) (drop j (sasserts p)) = (S', acc')\<close>
    by (cases \<open>foldl (tr_asserts_step p ?dm) (S, acc) (drop j (sasserts p))\<close>)
  show ?thesis using tr_prefix_asserts[OF s'] f s s' by auto
next
  case False
  then show ?thesis by (simp add: TA_def)
qed

lemma TD_le_final: \<open>d \<le> length (sdefs p) \<Longrightarrow> length (fst (TD p d)) \<le> length (fst (TA p (length (sasserts p))))\<close>
  using TD_mono[of p d \<open>length (sdefs p) - d\<close>] TA_le_final[of p 0] by (simp add: TA_0)

text \<open>The sizes \<^verbatim>\<open>tr_problem\<close> needs so that no vector it grows reaches \<open>2^56\<close> elements.\<close>
definition tr_sizes :: \<open>SmtProblem \<Rightarrow> bool\<close> where
  \<open>tr_sizes p \<equiv> length (sfuns p) < 2 ^ 56 \<and> length (sdefs p) < 2 ^ 56 \<and> length (sasserts p) < 2 ^ 56 \<and>
     length (fst (tr_asserts_m p (tr_defs_m p))) < 2 ^ 56\<close>

text \<open>\<open>tm_ok p m fs k\<close>: \<open>fs\<close> are the tables of the first \<open>k\<close> declared symbols of the model of \<open>p\<close> for
  the assignment \<open>m\<close>.\<close>
definition tm_ok :: \<open>SmtProblem \<Rightarrow> bool list list \<Rightarrow> SmtInterp list \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>tm_ok p m fs k \<equiv> length fs = k \<and>
     (\<forall>i < k. rvec_elems (SmtInterp_entries (fs ! i)) = [] \<and>
        mval_ok (SmtFun_ret (sfuns p ! i)) (m ! i) (SmtInterp_default (fs ! i)))\<close>

lemma tm_ok_len: \<open>tm_ok p m fs k \<Longrightarrow> length fs = k\<close>
  by (simp add: tm_ok_def)

lemma tm_ok_0: \<open>tm_ok p m [] 0\<close>
  by (simp add: tm_ok_def)

lemma tm_ok_snoc:
  \<open>tm_ok p m fs k \<Longrightarrow> rvec_elems (SmtInterp_entries x) = [] \<Longrightarrow> mval_ok (SmtFun_ret (sfuns p ! k)) (m ! k) (SmtInterp_default x) \<Longrightarrow>
   tm_ok p m (fs @ [x]) (Suc k)\<close>
  by (auto simp: tm_ok_def nth_append less_Suc_eq)

lemma tm_ok_final:
  \<open>tm_ok p m fs (length (sfuns p)) \<Longrightarrow> rvec_elems ds = [] \<Longrightarrow> rvec_elems fv = fs \<Longrightarrow>
   tr_model_ok p m (make_SmtModel ds fv)\<close>
  by (simp add: tm_ok_def tr_model_ok_def)

context QFBV_ctx
begin

subsection \<open>Small functions\<close>

definition bits1_contract :: \<open>bool \<Rightarrow> ('s, bool rvec, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>bits1_contract b \<equiv>
     make_function_contract can_alloc_reference (\<lambda>r. can_alloc_reference \<star> \<langle>rvec_elems r = [b]\<rangle>)\<close>

lemma bits1_spec [crush_specs]:
  shows \<open>\<Gamma>; bits1 b \<Turnstile>\<^sub>F bits1_contract b\<close>
  apply (crush_boot f: bits1_def contract: bits1_contract_def)
  apply (crush_base simp add: push_not_None)
  done

definition tr_push_contract :: \<open>Tr \<Rightarrow> Term \<Rightarrow> ('s, Tr \<times> 64 word \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>tr_push_contract s t \<equiv>
     make_function_contract
       (can_alloc_reference \<star> \<langle>vok (Tr_defs s) \<and> rvec_length (Tr_defs s) < 2 ^ 56\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>case r of (s', k, _) \<Rightarrow> rvec_elems (Tr_defs s') = rvec_elems (Tr_defs s) @ [t] \<and> vok (Tr_defs s') \<and>
              k = word_of_nat (rvec_length (Tr_defs s))\<rangle>)\<close>

lemma tr_push_spec [crush_specs]:
  shows \<open>\<Gamma>; tr_push s t \<Turnstile>\<^sub>F tr_push_contract s t\<close>
  apply (crush_boot f: tr_push_def contract: tr_push_contract_def)
  apply (crush_base simp add: push_not_None)
  done

definition tref_contract :: \<open>64 word \<Rightarrow> ('s, Term, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>tref_contract k \<equiv>
     make_function_contract can_alloc_reference (\<lambda>r. can_alloc_reference \<star> \<langle>r = Term_Ref k\<rangle>)\<close>

lemma tref_spec [crush_specs]:
  shows \<open>\<Gamma>; tref k \<Turnstile>\<^sub>F tref_contract k\<close>
  apply (crush_boot f: tref_def contract: tref_contract_def)
  apply crush_base
  done

definition tbin_contract :: \<open>Op \<Rightarrow> Term \<Rightarrow> Term \<Rightarrow> ('s, Term, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>tbin_contract op a b \<equiv>
     make_function_contract can_alloc_reference (\<lambda>r. can_alloc_reference \<star> \<langle>r = Term_Bin op a b\<rangle>)\<close>

lemma tbin_spec [crush_specs]:
  shows \<open>\<Gamma>; tbin op a b \<Turnstile>\<^sub>F tbin_contract op a b\<close>
  apply (crush_boot f: tbin_def contract: tbin_contract_def)
  apply crush_base
  done

definition sort_width_contract :: \<open>SmtSort \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>sort_width_contract s \<equiv>
     make_function_contract can_alloc_reference (\<lambda>r. can_alloc_reference \<star> \<langle>r = word_of_nat (sort_width_m s)\<rangle>)\<close>

lemma sort_width_spec [crush_specs]:
  shows \<open>\<Gamma>; sort_width s \<Turnstile>\<^sub>F sort_width_contract s\<close>
  apply (crush_boot f: sort_width_def contract: sort_width_contract_def)
  apply (crush_base split: SmtSort.splits)
  done

definition tr_op_contract :: \<open>SmtOp \<Rightarrow> ('s, Op, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>tr_op_contract op \<equiv>
     make_function_contract can_alloc_reference (\<lambda>r. can_alloc_reference \<star> \<langle>r = QFBV_SmtModel.tr_op op\<rangle>)\<close>

lemma tr_op_spec [crush_specs]:
  shows \<open>\<Gamma>; tr_op op \<Turnstile>\<^sub>F tr_op_contract op\<close>
  apply (crush_boot f: tr_op_def contract: tr_op_contract_def)
  apply (crush_base split: SmtOp.splits)
  done


subsection \<open>The builders of terms\<close>

definition fold_left_contract :: \<open>SmtOp \<Rightarrow> 64 word rvec \<Rightarrow> ('s, Term, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>fold_left_contract op ksw \<equiv>
     make_function_contract
       (can_alloc_reference \<star> \<langle>1 \<le> rvec_length ksw \<and> rvec_length ksw \<le> urust_fuel \<and> rvec_length ksw < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>term_of r = fold_left_m op (map unat (rvec_elems ksw))\<rangle>)\<close>

lemma fold_left_spec [crush_specs]:
  shows \<open>\<Gamma>; fold_left_fn op ksw \<Turnstile>\<^sub>F fold_left_contract op ksw\<close>
  apply (crush_boot f: fold_left_fn_def contract: fold_left_contract_def)
  apply (crush_base inline: len_def)
  subgoal for acc_ref i_ref
    apply (ucincl_discharge\<open>rule_tac
      INV=\<open>\<lambda>c. \<Squnion>ga acc gi i. acc_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>acc \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
           \<langle>1 \<le> unat i \<and> unat i \<le> rvec_length ksw \<and> term_of acc = fl_acc op (map unat (rvec_elems ksw)) (unat i) \<and> rvec_length ksw - unat i \<le> c\<rangle>\<close> and
      INV'=\<open>\<lambda>c. \<Squnion>ga acc gi i. acc_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>acc \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
           \<langle>1 \<le> unat i \<and> unat i < rvec_length ksw \<and> term_of acc = fl_acc op (map unat (rvec_elems ksw)) (unat i) \<and> rvec_length ksw - unat i \<le> Suc c\<rangle>\<close> and
      \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: word_less_nat_alt unat_of_nat_eq fl_acc_Suc unat_plus_one_of_less_bound fold_left_fl' fl_acc_1)
    apply (cases \<open>rvec_elems ksw\<close>; simp)
    done
  done


definition chain_contract :: \<open>SmtOp \<Rightarrow> 64 word rvec \<Rightarrow> ('s, Term, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>chain_contract op ksw \<equiv>
     make_function_contract
       (can_alloc_reference \<star> \<langle>2 \<le> rvec_length ksw \<and> rvec_length ksw \<le> urust_fuel \<and> rvec_length ksw < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>term_of r = chain_m op (map unat (rvec_elems ksw))\<rangle>)\<close>

lemma chain_spec [crush_specs]:
  shows \<open>\<Gamma>; chain op ksw \<Turnstile>\<^sub>F chain_contract op ksw\<close>
  apply (crush_boot f: chain_def contract: chain_contract_def)
  apply (crush_base inline: len_def)
  subgoal for acc_ref i_ref
    apply (ucincl_discharge\<open>rule_tac
      INV=\<open>\<lambda>c. \<Squnion>ga acc gi i. acc_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>acc \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
           \<langle>2 \<le> unat i \<and> unat i \<le> rvec_length ksw \<and> term_of acc = ch_acc op (map unat (rvec_elems ksw)) (unat i) \<and> rvec_length ksw - unat i \<le> c\<rangle>\<close> and
      INV'=\<open>\<lambda>c. \<Squnion>ga acc gi i. acc_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>acc \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
           \<langle>2 \<le> unat i \<and> unat i < rvec_length ksw \<and> term_of acc = ch_acc op (map unat (rvec_elems ksw)) (unat i) \<and> rvec_length ksw - unat i \<le> Suc c\<rangle>\<close> and
      \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: word_less_nat_alt unat_of_nat_eq ch_acc_Suc unat_plus_one_of_less_bound chain_ch ch_acc_2
        unat_minus_1')
    apply (simp_all add: word_le_nat_alt)
    done
  done

definition pairwise_contract :: \<open>64 word rvec \<Rightarrow> ('s, Term, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>pairwise_contract ksw \<equiv>
     make_function_contract
       (can_alloc_reference \<star> \<langle>2 \<le> rvec_length ksw \<and> rvec_length ksw \<le> urust_fuel \<and> rvec_length ksw < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>term_of r = pairwise_m (map unat (rvec_elems ksw))\<rangle>)\<close>

lemma pairwise_spec [crush_specs]:
  shows \<open>\<Gamma>; pairwise ksw \<Turnstile>\<^sub>F pairwise_contract ksw\<close>
  apply (crush_boot f: pairwise_def contract: pairwise_contract_def)
  apply (crush_base inline: len_def)
  subgoal for acc_ref i_ref
    apply (ucincl_discharge\<open>rule_tac
      INV=\<open>\<lambda>c. \<Squnion>ga acc gi i. acc_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>acc \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
           \<langle>unat i \<le> rvec_length ksw \<and> term_of acc = pw_acc (map unat (rvec_elems ksw)) (unat i) (Suc (unat i)) \<and> rvec_length ksw - unat i \<le> c\<rangle>\<close> and
      INV'=\<open>\<lambda>c. \<Squnion>ga acc gi i. acc_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>acc \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
           \<langle>unat i < rvec_length ksw \<and> term_of acc = pw_acc (map unat (rvec_elems ksw)) (unat i) (Suc (unat i)) \<and> rvec_length ksw - unat i \<le> Suc c\<rangle>\<close> and
      \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: word_less_nat_alt unat_of_nat_eq unat_plus_one_of_less_bound pairwise_pw pw_acc_0)
    subgoal for k ga acc gi r j_ref
      apply (ucincl_discharge\<open>rule_tac
        INV=\<open>\<lambda>c. \<Squnion>ga acc gi' gj j. acc_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>acc \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi'\<down>r \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star>
             can_alloc_reference \<star>
             \<langle>Suc (unat r) \<le> unat j \<and> unat j \<le> rvec_length ksw \<and> term_of acc = pw_acc (map unat (rvec_elems ksw)) (unat r) (unat j) \<and>
              rvec_length ksw - unat j \<le> c\<rangle>\<close> and
        INV'=\<open>\<lambda>c. \<Squnion>ga acc gi' gj j. acc_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>acc \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi'\<down>r \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star>
             can_alloc_reference \<star>
             \<langle>Suc (unat r) \<le> unat j \<and> unat j < rvec_length ksw \<and> term_of acc = pw_acc (map unat (rvec_elems ksw)) (unat r) (unat j) \<and>
              rvec_length ksw - unat j \<le> Suc c\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_bounded_while_framedI\<close>)
      apply (crush_base simp add: word_less_nat_alt unat_of_nat_eq unat_plus_one_of_less_bound pw_acc_Suc pw_step_def
          pw_acc_next unat_one_iff pw_acc_skip unat_Suc_le)
      apply (simp_all add: unat_eq_zero pw_acc_next')
      done
    done
  done

definition implies_contract :: \<open>64 word rvec \<Rightarrow> ('s, Term, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>implies_contract ksw \<equiv>
     make_function_contract
       (can_alloc_reference \<star> \<langle>1 \<le> rvec_length ksw \<and> rvec_length ksw \<le> urust_fuel \<and> rvec_length ksw < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>term_of r = implies_m (map unat (rvec_elems ksw))\<rangle>)\<close>

lemma implies_spec [crush_specs]:
  shows \<open>\<Gamma>; implies ksw \<Turnstile>\<^sub>F implies_contract ksw\<close>
  apply (crush_boot f: implies_def contract: implies_contract_def)
  apply (crush_base inline: len_def simp add: unat_minus_1' unat_of_nat_eq word_le_nat_alt)
  subgoal for acc_ref i_ref
    apply (ucincl_discharge\<open>rule_tac
      INV=\<open>\<lambda>c. \<Squnion>ga acc gi i. acc_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>acc \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
           \<langle>unat i \<le> rvec_length ksw - 1 \<and> term_of acc = im_acc (map unat (rvec_elems ksw)) (unat i) \<and> unat i \<le> c\<rangle>\<close> and
      INV'=\<open>\<lambda>c. \<Squnion>ga acc gi i. acc_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>acc \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
           \<langle>0 < unat i \<and> unat i \<le> rvec_length ksw - 1 \<and> term_of acc = im_acc (map unat (rvec_elems ksw)) (unat i) \<and> unat i \<le> Suc c\<rangle>\<close> and
      \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: word_less_nat_alt unat_of_nat_eq unat_minus_1' word_le_nat_alt im_acc_pred' im_acc_last'
        implies_im)
    done
  done

definition tr_app_contract :: \<open>SmtOp \<Rightarrow> 64 word rvec \<Rightarrow> ('s, Term, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>tr_app_contract op ksw \<equiv>
     make_function_contract
       (can_alloc_reference \<star> \<langle>min_ar op \<le> rvec_length ksw \<and> rvec_length ksw \<le> urust_fuel \<and> rvec_length ksw < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>term_of r = tr_app_m op (map unat (rvec_elems ksw))\<rangle>)\<close>

lemma tr_app_spec [crush_specs]:
  shows \<open>\<Gamma>; tr_app op ksw \<Turnstile>\<^sub>F tr_app_contract op ksw\<close>
  apply (crush_boot f: tr_app_def contract: tr_app_contract_def)
  apply (crush_base split: SmtOp.splits simp add: tref_map_unat)
  apply ((cases \<open>rvec_elems ksw\<close>; simp; cases \<open>tl (rvec_elems ksw)\<close>; simp; cases \<open>tl (tl (rvec_elems ksw))\<close>; simp); fail)+
  done


subsection \<open>\<^verbatim>\<open>tr_args\<close> and \<^verbatim>\<open>tr_term\<close>\<close>

text \<open>The \<open>k\<close>-th unfolding of the mutual recursion. The tables \<^verbatim>\<open>dm\<close> and \<^verbatim>\<open>env\<close> are given as
  vectors of words; definitions are expanded below the number of definitions of \<open>p\<close>. The
  definitions of the result must stay below \<open>2^56\<close>.\<close>
definition tr_args_contract ::
  \<open>nat \<Rightarrow> SmtProblem \<Rightarrow> 64 word rvec \<Rightarrow> 64 word rvec \<Rightarrow> Tr \<Rightarrow> SmtTerm rvec \<Rightarrow> ('s, Tr \<times> 64 word rvec \<times> tnil, 'abort) function_contract\<close>
  where
  [crush_contracts]: \<open>tr_args_contract k p dmw envw s ts \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
        \<langle>Suc (deps p (length (sdefs p)) (rvec_elems ts)) \<le> k \<and> rvec_length ts < 2 ^ 64 \<and> rvec_length ts \<le> urust_fuel \<and>
         toks p urust_fuel (rvec_length dmw) (rvec_length envw) (length (sdefs p)) (rvec_elems ts) \<and> vok (Tr_defs s) \<and>
         length (fst (tr_args_m p (map unat (rvec_elems dmw)) (map unat (rvec_elems envw)) (length (sdefs p)) (tdefs s) (rvec_elems ts))) < 2 ^ 56\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>case r of (s', ks, _) \<Rightarrow>
             tdefs s' = fst (tr_args_m p (map unat (rvec_elems dmw)) (map unat (rvec_elems envw)) (length (sdefs p)) (tdefs s) (rvec_elems ts)) \<and>
             rvec_elems ks = map word_of_nat (snd (tr_args_m p (map unat (rvec_elems dmw)) (map unat (rvec_elems envw)) (length (sdefs p)) (tdefs s) (rvec_elems ts))) \<and>
             vok (Tr_defs s')\<rangle>)\<close>

definition tr_term_contract ::
  \<open>nat \<Rightarrow> SmtProblem \<Rightarrow> 64 word rvec \<Rightarrow> 64 word rvec \<Rightarrow> Tr \<Rightarrow> SmtTerm \<Rightarrow> ('s, Tr \<times> Term \<times> tnil, 'abort) function_contract\<close>
  where
  [crush_contracts]: \<open>tr_term_contract k p dmw envw s t \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
        \<langle>Suc (dep p (length (sdefs p)) t) \<le> k \<and>
         tok p urust_fuel (rvec_length dmw) (rvec_length envw) (length (sdefs p)) t \<and> vok (Tr_defs s) \<and>
         length (fst (tr_term_m p (map unat (rvec_elems dmw)) (map unat (rvec_elems envw)) (length (sdefs p)) (tdefs s) t)) < 2 ^ 56\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>case r of (s', t', _) \<Rightarrow>
             tdefs s' = fst (tr_term_m p (map unat (rvec_elems dmw)) (map unat (rvec_elems envw)) (length (sdefs p)) (tdefs s) t) \<and>
             term_of t' = snd (tr_term_m p (map unat (rvec_elems dmw)) (map unat (rvec_elems envw)) (length (sdefs p)) (tdefs s) t) \<and>
             vok (Tr_defs s')\<rangle>)\<close>

lemma tr_args_step_spec:
  assumes IH2: \<open>\<And>p dmw envw s t. \<Gamma>; g p dmw envw s t \<Turnstile>\<^sub>F tr_term_contract k p dmw envw s t\<close>
  shows \<open>\<Gamma>; fst (tr_args_rec_step (f, g)) p dmw envw s ts \<Turnstile>\<^sub>F tr_args_contract (Suc k) p dmw envw s ts\<close>
  apply (crush_boot f: tr_args_rec_step_def contract: tr_args_contract_def)
  apply (crush_base specs add: IH2 contracts add: tr_term_contract_def)
  subgoal for s_ref ks_ref i_ref
    apply (ucincl_discharge\<open>rule_tac
      INV=\<open>\<lambda>c. \<Squnion>gs sv gk kv gi i. s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>sv \<star> ks_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>kv \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
           can_alloc_reference \<star>
           \<langle>unat i \<le> rvec_length ts \<and>
            tdefs sv = fst (tr_args_m p (map unat (rvec_elems dmw)) (map unat (rvec_elems envw)) (length (sdefs p)) (tdefs s) (take (unat i) (rvec_elems ts))) \<and>
            rvec_elems kv = map word_of_nat (snd (tr_args_m p (map unat (rvec_elems dmw)) (map unat (rvec_elems envw)) (length (sdefs p)) (tdefs s) (take (unat i) (rvec_elems ts)))) \<and>
            vok (Tr_defs sv) \<and> vok kv \<and> rvec_length kv = unat i \<and>
            rvec_length ts - unat i \<le> c\<rangle>\<close> and
      INV'=\<open>\<lambda>c. \<Squnion>gs sv gk kv gi i. s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>sv \<star> ks_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>kv \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
           can_alloc_reference \<star>
           \<langle>unat i < rvec_length ts \<and>
            tdefs sv = fst (tr_args_m p (map unat (rvec_elems dmw)) (map unat (rvec_elems envw)) (length (sdefs p)) (tdefs s) (take (unat i) (rvec_elems ts))) \<and>
            rvec_elems kv = map word_of_nat (snd (tr_args_m p (map unat (rvec_elems dmw)) (map unat (rvec_elems envw)) (length (sdefs p)) (tdefs s) (take (unat i) (rvec_elems ts)))) \<and>
            vok (Tr_defs sv) \<and> vok kv \<and> rvec_length kv = unat i \<and>
            rvec_length ts - unat i \<le> Suc c\<rangle>\<close> and
      \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base specs add: IH2 contracts add: tr_term_contract_def
        simp add: word_less_nat_alt unat_of_nat_eq unat_plus_one_of_less_bound tr_args_take_Suc deps_nth toks_nth push_not_None)
    apply (all \<open>(drule (1) tr_args_bounds)?\<close>)
    apply (auto simp: push_the dest: arg_cong[where f=length])
    done
  done

lemma tr_term_step_spec:
  assumes IH1: \<open>\<And>p dmw envw s ts. \<Gamma>; f p dmw envw s ts \<Turnstile>\<^sub>F tr_args_contract k p dmw envw s ts\<close>
      and IH2: \<open>\<And>p dmw envw s t. \<Gamma>; g p dmw envw s t \<Turnstile>\<^sub>F tr_term_contract k p dmw envw s t\<close>
  shows \<open>\<Gamma>; snd (tr_args_rec_step (f, g)) p dmw envw s t \<Turnstile>\<^sub>F tr_term_contract (Suc k) p dmw envw s t\<close>
proof (cases t)
  case (SmtTerm_Def d args)
  let ?b = \<open>SmtDef_body (sdefs p ! unat d)\<close>
  let ?L = \<open>length (sdefs p)\<close>
  have I: \<open>tok p urust_fuel (rvec_length dmw) (rvec_length args) ?L ?b \<and> dep p ?L ?b = dep p (unat d) ?b \<and>
           tr_term_m p (map unat (rvec_elems dmw)) env ?L S ?b = tr_term_m p (map unat (rvec_elems dmw)) env (unat d) S ?b\<close>
    if \<open>tok p urust_fuel (rvec_length dmw) (rvec_length args) (unat d) ?b\<close> \<open>unat d < ?L\<close> for env S
    using tok_n_indep(1)[OF that(1), of ?L] that(2) by simp
  have E: \<open>\<And>env S. tok p urust_fuel (rvec_length dmw) (rvec_length args) (unat d) ?b \<Longrightarrow> unat d < ?L \<Longrightarrow>
           tr_term_m p (map unat (rvec_elems dmw)) env ?L S ?b = tr_term_m p (map unat (rvec_elems dmw)) env (unat d) S ?b\<close>
    and Dp: \<open>tok p urust_fuel (rvec_length dmw) (rvec_length args) (unat d) ?b \<Longrightarrow> unat d < ?L \<Longrightarrow> dep p ?L ?b = dep p (unat d) ?b\<close>
    and T: \<open>tok p urust_fuel (rvec_length dmw) (rvec_length args) (unat d) ?b \<Longrightarrow> unat d < ?L \<Longrightarrow>
           tok p urust_fuel (rvec_length dmw) (rvec_length args) ?L ?b\<close>
    using I by blast+
  show ?thesis unfolding SmtTerm_Def
    apply (crush_boot f: tr_args_rec_step_def contract: tr_term_contract_def)
    apply (crush_base specs add: IH1 IH2 contracts add: tr_term_contract_def tr_args_contract_def
        simp add: E Dp T tr_args_len map_unat_wn tr_term_wr_env wn_len_0 tref_map_unat)
    apply (simp_all add: map_wr_comp tr_term_wr_env)
    apply (rule le_less_trans[OF tr_term_len], assumption)
    done
next
  case (SmtTerm_App op args)
  show ?thesis unfolding SmtTerm_App
    apply (crush_boot f: tr_args_rec_step_def contract: tr_term_contract_def)
    apply (crush_base specs add: IH1 IH2 contracts add: tr_term_contract_def tr_args_contract_def
        simp add: tr_args_len map_unat_wn tr_app_wr)
    apply (simp_all add: map_wr_comp tr_app_wr)
    done
qed (crush_boot f: tr_args_rec_step_def contract: tr_term_contract_def, crush_base simp add: tref_map_unat)+

lemma tr_step_spec:
  assumes IH1: \<open>\<And>p dmw envw s ts. \<Gamma>; f p dmw envw s ts \<Turnstile>\<^sub>F tr_args_contract k p dmw envw s ts\<close>
      and IH2: \<open>\<And>p dmw envw s t. \<Gamma>; g p dmw envw s t \<Turnstile>\<^sub>F tr_term_contract k p dmw envw s t\<close>
  shows \<open>\<Gamma>; fst (tr_args_rec_step (f, g)) p dmw envw s ts \<Turnstile>\<^sub>F tr_args_contract (Suc k) p dmw envw s ts\<close>
    and \<open>\<Gamma>; snd (tr_args_rec_step (f, g)) p dmw envw s t \<Turnstile>\<^sub>F tr_term_contract (Suc k) p dmw envw s t\<close>
  by (rule tr_args_step_spec[OF IH2]) (rule tr_term_step_spec[OF IH1 IH2])

lemma tr_rec_spec:
  shows \<open>(\<forall>p dmw envw s ts. \<Gamma>; fst ((tr_args_rec_step ^^ k) h) p dmw envw s ts \<Turnstile>\<^sub>F tr_args_contract k p dmw envw s ts) \<and>
         (\<forall>p dmw envw s t. \<Gamma>; snd ((tr_args_rec_step ^^ k) h) p dmw envw s t \<Turnstile>\<^sub>F tr_term_contract k p dmw envw s t)\<close>
proof (induction k)
  case 0
  show ?case
    apply (intro conjI allI)
     apply (ucincl_discharge\<open>intro satisfies_function_contractI\<close>; subst wp_sstriple_iff;
        simp add: tr_args_contract_def Let_def apure_precise_False asepconj_bot_zero2 bot_aentails_all)
    apply (ucincl_discharge\<open>intro satisfies_function_contractI\<close>; subst wp_sstriple_iff;
        simp add: tr_term_contract_def Let_def apure_precise_False asepconj_bot_zero2 bot_aentails_all)
    done
next
  case (Suc k)
  obtain f g where fg: \<open>(tr_args_rec_step ^^ k) h = (f, g)\<close> by (cases \<open>(tr_args_rec_step ^^ k) h\<close>)
  show ?case
    using tr_step_spec[where f=f and g=g and k=k] Suc.IH unfolding funpow.simps(2) comp_def fg by simp
qed

lemma tr_args_spec [crush_specs]:
  shows \<open>\<Gamma>; tr_args p dmw envw s ts \<Turnstile>\<^sub>F tr_args_contract urust_fuel p dmw envw s ts\<close>
  unfolding tr_args_def using tr_rec_spec by blast

lemma tr_term_spec [crush_specs]:
  shows \<open>\<Gamma>; tr_term p dmw envw s t \<Turnstile>\<^sub>F tr_term_contract urust_fuel p dmw envw s t\<close>
  unfolding tr_term_def using tr_rec_spec by blast

subsection \<open>\<^verbatim>\<open>tr_problem\<close>, \<^verbatim>\<open>tr_model\<close>, \<^verbatim>\<open>in_fragment\<close>\<close>

definition tr_problem_contract :: \<open>SmtProblem \<Rightarrow> ('s, Problem, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>tr_problem_contract p \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>tr_pre urust_fuel p \<and> tr_sizes p\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>prob_of r = tr_problem_m p\<rangle>)\<close>

lemma tr_problem_spec [crush_specs]:
  shows \<open>\<Gamma>; tr_problem p \<Turnstile>\<^sub>F tr_problem_contract p\<close>
proof (cases \<open>tr_pre urust_fuel p \<and> tr_sizes p\<close>)
  case True
  note P = tr_pre_facts[OF conjunct1[OF True], simplified]
  have Z: \<open>length (sfuns p) < 72057594037927936\<close> \<open>length (sdefs p) < 72057594037927936\<close>
    \<open>length (sasserts p) < 72057594037927936\<close>
    \<open>length (fst (TA p (length (sasserts p)))) < 72057594037927936\<close>
    using conjunct2[OF True] by (simp_all add: tr_sizes_def TA_final)
  have W: \<open>unat (word_of_nat (length (sfuns p)) :: 64 word) = length (sfuns p)\<close>
    \<open>unat (word_of_nat (length (sdefs p)) :: 64 word) = length (sdefs p)\<close>
    \<open>unat (word_of_nat (length (sasserts p)) :: 64 word) = length (sasserts p)\<close>
    using P(1,3,5) by (simp_all add: unat_of_nat_eq)
  have I: \<open>\<And>r :: 64 word. unat r < length (sfuns p) \<Longrightarrow> unat (r + 1) = Suc (unat r)\<close>
    \<open>\<And>r :: 64 word. unat r < length (sdefs p) \<Longrightarrow> unat (r + 1) = Suc (unat r)\<close>
    \<open>\<And>r :: 64 word. unat r < length (sasserts p) \<Longrightarrow> unat (r + 1) = Suc (unat r)\<close>
    using P(1) unat_plus_one_of_less_bound[where n=\<open>length (sfuns p)\<close> and 'a=64] apply simp
    using P(3) unat_plus_one_of_less_bound[where n=\<open>length (sdefs p)\<close> and 'a=64] apply simp
    using P(5) unat_plus_one_of_less_bound[where n=\<open>length (sasserts p)\<close> and 'a=64] apply simp
    done
  have B: \<open>\<And>r :: 64 word. unat r < length (sfuns p) \<Longrightarrow> unat r < 18446744073709551615\<close>
    \<open>\<And>r :: 64 word. unat r < length (sdefs p) \<Longrightarrow> unat r < 18446744073709551615\<close>
    \<open>\<And>r :: 64 word. unat r < length (sasserts p) \<Longrightarrow> unat r < 18446744073709551615\<close>
    using P(1,3,5) by simp_all
  have ZI: \<open>\<And>r :: 64 word. unat r < length (sfuns p) \<Longrightarrow> unat r < 72057594037927936\<close>
    \<open>\<And>r :: 64 word. unat r < length (sdefs p) \<Longrightarrow> unat r < 72057594037927936\<close>
    \<open>\<And>r :: 64 word. unat r < length (sasserts p) \<Longrightarrow> unat r < 72057594037927936\<close>
    using Z by simp_all
  have DB: \<open>length (fst (TD p (Suc d))) < 72057594037927936\<close> if \<open>d < length (sdefs p)\<close> for d
    using TD_le_final[of \<open>Suc d\<close> p] that Z(4) by simp
  have AB: \<open>length (fst (TA p (Suc j))) < 72057594037927936\<close> for j
    using TA_le_final[of p \<open>Suc j\<close>] Z(4) by simp
  have AB': \<open>length (fst (tr_term_m p (snd (TD p (length (sdefs p)))) [] (length (sdefs p)) (fst (TA p j)) (sasserts p ! j)))
      < 72057594037927936\<close> if \<open>j < length (sasserts p)\<close> for j
    using AB[of j] that by (simp add: TA_Suc)
  show ?thesis
    apply (crush_boot f: tr_problem_def contract: tr_problem_contract_def)
    apply (crush_base simp add: P)
    subgoal for widths_ref i_ref
      apply (ucincl_discharge\<open>rule_tac
        INV=\<open>\<lambda>c. \<Squnion>gw wv gi i. widths_ref \<mapsto>\<langle>\<top>\<rangle> gw\<down>wv \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
             \<langle>unat i \<le> length (sfuns p) \<and>
              rvec_elems wv = map (\<lambda>f. word_of_nat (sort_width_m (SmtFun_ret f))) (take (unat i) (sfuns p)) \<and> vok wv \<and>
              length (sfuns p) - unat i \<le> c\<rangle>\<close> and
        INV'=\<open>\<lambda>c. \<Squnion>gw wv gi i. widths_ref \<mapsto>\<langle>\<top>\<rangle> gw\<down>wv \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
             \<langle>unat i < length (sfuns p) \<and>
              rvec_elems wv = map (\<lambda>f. word_of_nat (sort_width_m (SmtFun_ret f))) (take (unat i) (sfuns p)) \<and> vok wv \<and>
              length (sfuns p) - unat i \<le> Suc c\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_bounded_while_framedI\<close>)
      apply (crush_base simp add: P W I B Z word_less_nat_alt take_Suc_conv_app_nth push_not_None)
      apply (all \<open>(frule ZI(1))?\<close>)
      apply (simp_all add: take_Suc_conv_app_nth)
      subgoal for gw wv gi i s_ref dm_ref d_ref
        apply (ucincl_discharge\<open>rule_tac
          INV=\<open>\<lambda>c. \<Squnion>gs sv gm mv gd d. s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>sv \<star> dm_ref \<mapsto>\<langle>\<top>\<rangle> gm\<down>mv \<star> d_ref \<mapsto>\<langle>\<top>\<rangle> gd\<down>d \<star>
               can_alloc_reference \<star>
               \<langle>unat d \<le> length (sdefs p) \<and> tdefs sv = fst (TD p (unat d)) \<and>
                rvec_elems mv = map word_of_nat (snd (TD p (unat d))) \<and> vok (Tr_defs sv) \<and> vok mv \<and>
                length (sdefs p) - unat d \<le> c\<rangle>\<close> and
          INV'=\<open>\<lambda>c. \<Squnion>gs sv gm mv gd d. s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>sv \<star> dm_ref \<mapsto>\<langle>\<top>\<rangle> gm\<down>mv \<star> d_ref \<mapsto>\<langle>\<top>\<rangle> gd\<down>d \<star>
               can_alloc_reference \<star>
               \<langle>unat d < length (sdefs p) \<and> tdefs sv = fst (TD p (unat d)) \<and>
                rvec_elems mv = map word_of_nat (snd (TD p (unat d))) \<and> vok (Tr_defs sv) \<and> vok mv \<and>
                length (sdefs p) - unat d \<le> Suc c\<rangle>\<close> and
          \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
          in wp_bounded_while_framedI\<close>)
        apply (crush_base simp add: P W I B Z word_less_nat_alt TD_0 TD_Suc TD_len wn_len_0
            map_unat_wn map_wr_comp tr_term_wr_dm push_not_None)
        apply (all \<open>(frule ZI(2))?\<close>)
        apply (all \<open>(frule DB)?\<close>)
        apply (auto simp: TD_Suc TD_len push_the dest: arg_cong[where f=length])[8]
        subgoal for gs sv gm mv gd d as_ref j_ref
          apply (ucincl_discharge\<open>rule_tac
            INV=\<open>\<lambda>c. \<Squnion>gs sv gm' ga av gj j. s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>sv \<star>
                 dm_ref \<mapsto>\<langle>\<top>\<rangle> gm'\<down>mv \<star> as_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>av \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star>
                 \<langle>unat j \<le> length (sasserts p) \<and> tdefs sv = fst (TA p (unat j)) \<and>
                  map term_of (rvec_elems av) = snd (TA p (unat j)) \<and> vok (Tr_defs sv) \<and> vok av \<and>
                  rvec_length av = unat j \<and> length (sasserts p) - unat j \<le> c\<rangle>\<close> and
            INV'=\<open>\<lambda>c. \<Squnion>gs sv gm' ga av gj j. s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>sv \<star>
                 dm_ref \<mapsto>\<langle>\<top>\<rangle> gm'\<down>mv \<star> as_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>av \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star>
                 \<langle>unat j < length (sasserts p) \<and> tdefs sv = fst (TA p (unat j)) \<and>
                  map term_of (rvec_elems av) = snd (TA p (unat j)) \<and> vok (Tr_defs sv) \<and> vok av \<and>
                  rvec_length av = unat j \<and> length (sasserts p) - unat j \<le> Suc c\<rangle>\<close> and
            \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
            in wp_bounded_while_framedI\<close>)
          apply (crush_base simp add: P W I B Z word_less_nat_alt TA_0 TA_Suc TD_len
              map_unat_wn map_wr_comp tr_term_wr_dm tr_problem_TA push_not_None)
          apply (all \<open>(frule ZI(3))?\<close>)
          apply (auto simp: TA_Suc push_the tr_problem_TA prob_of_def AB AB' dest: arg_cong[where f=length])
          done
        done
      done
    done
next
  case False
  then have F: \<open>(tr_pre urust_fuel p \<and> tr_sizes p) = False\<close> by simp
  show ?thesis
    apply (ucincl_discharge\<open>intro satisfies_function_contractI\<close>)
    apply (subst wp_sstriple_iff)
    apply (simp only: tr_problem_contract_def F)
    apply (simp add: Let_def apure_precise_False asepconj_bot_zero2 bot_aentails_all)
    done
qed

definition tr_model_contract :: \<open>SmtProblem \<Rightarrow> bool rvec rvec \<Rightarrow> ('s, SmtModel, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>tr_model_contract p m \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
        \<langle>length (sfuns p) < 2 ^ 56 \<and> length (sfuns p) \<le> urust_fuel \<and>
         length (sfuns p) \<le> rvec_length m \<and>
         (\<forall>i < length (sfuns p). SmtFun_ret (sfuns p ! i) = SmtSort_Bool \<longrightarrow> vecs_of m ! i \<noteq> [])\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>tr_model_ok p (vecs_of m) r\<rangle>)\<close>

lemma tr_model_spec [crush_specs]:
  shows \<open>\<Gamma>; tr_model p m \<Turnstile>\<^sub>F tr_model_contract p m\<close>
  apply (crush_boot f: tr_model_def contract: tr_model_contract_def)
  apply (crush_base)
  subgoal for funs_ref i_ref
    apply (ucincl_discharge\<open>rule_tac
      INV=\<open>\<lambda>c. \<Squnion>gf fv gi i. funs_ref \<mapsto>\<langle>\<top>\<rangle> gf\<down>fv \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
           \<langle>unat i \<le> length (sfuns p) \<and> tm_ok p (vecs_of m) (rvec_elems fv) (unat i) \<and> vok fv \<and>
            length (sfuns p) - unat i \<le> c\<rangle>\<close> and
      INV'=\<open>\<lambda>c. \<Squnion>gf fv gi i. funs_ref \<mapsto>\<langle>\<top>\<rangle> gf\<down>fv \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
           \<langle>unat i < length (sfuns p) \<and> tm_ok p (vecs_of m) (rvec_elems fv) (unat i) \<and> vok fv \<and>
            length (sfuns p) - unat i \<le> Suc c\<rangle>\<close> and
      \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: word_less_nat_alt unat_of_nat_eq unat_plus_one_of_less_bound push_not_None tm_ok_0
        split: SmtSort.splits)
    apply (all \<open>(frule tm_ok_len)?\<close>)
    apply (auto simp: push_the vecs_of_def mval_ok_def intro!: tm_ok_snoc tm_ok_final)
    done
  done

definition in_fragment_contract :: \<open>SmtProblem \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>in_fragment_contract p \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
        \<langle>length (sfuns p) < 2 ^ 64 \<and> length (sfuns p) \<le> urust_fuel \<and>
         (\<forall>f \<in> set (sfuns p). length (fargs f) < 2 ^ 64)\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = smt_fragment p\<rangle>)\<close>

lemma in_fragment_spec [crush_specs]:
  shows \<open>\<Gamma>; in_fragment p \<Turnstile>\<^sub>F in_fragment_contract p\<close>
  apply (crush_boot f: in_fragment_def contract: in_fragment_contract_def)
  apply (crush_base simp add: smt_fragment_def)
  subgoal for i_ref
    apply (ucincl_discharge\<open>rule_tac
      INV=\<open>\<lambda>c. \<Squnion>gi i. i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
           \<langle>unat i \<le> length (sfuns p) \<and> (\<forall>j < unat i. fargs (sfuns p ! j) = []) \<and>
            length (sfuns p) - unat i \<le> c\<rangle>\<close> and
      INV'=\<open>\<lambda>c. \<Squnion>gi i. i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
           \<langle>unat i < length (sfuns p) \<and> (\<forall>j < unat i. fargs (sfuns p ! j) = []) \<and>
            length (sfuns p) - unat i \<le> Suc c\<rangle>\<close> and
      \<tau>=\<open>\<lambda>r. \<Squnion>gi i. i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> \<langle>r = smt_fragment p\<rangle>\<close> and
      \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: word_less_nat_alt unat_of_nat_eq unat_plus_one_of_less_bound smt_fragment_def wn_len_0)
    apply (auto simp: less_Suc_eq in_set_conv_nth intro: nth_mem)
    done
  apply (simp add: unat_gt_0)
  done

end

end
