theory QFBV_Norm
  imports QFBV_Lower
begin

section \<open>Word-level normalization of a core problem\<close>

text \<open>
  A functional model \<open>normalize_m\<close> of the Rust function \<^verbatim>\<open>normalize\<close> (without the substitution
  of the assertions \<open>v = t\<close>), and the proof that it keeps the variables and their widths, the
  well-sortedness and the models of a well-sorted core problem.

  The definitions are rebuilt in order. Each old definition \<open>j\<close> is remapped to the new indices
  (\<open>remap_m\<close>), rewritten (\<open>x = x\<close> is 1, \<open>x + ~x\<close> is all ones, \<open>x * ones\<close> is \<open>-x\<close>), and then
  shared with an equal earlier definition of the same width (\<open>norm_eq_m\<close>), or, if it is a
  product of more than two factors (at most 16), rebuilt as the product of its sorted factors,
  from the left. The operands of the input keep their order.

  The model follows the Rust code, except for two points. The hash buckets of \<^verbatim>\<open>find_def\<close> are
  not modelled: \<open>find_def_m\<close> returns the first equal definition of the width, which the
  buckets find too, since no two new definitions of the same width are equal and equal terms
  have equal hashes; the buckets affect only the speed. And \<open>factors_m\<close> treats a product as a
  factor unless its operands are earlier definitions; in a well-sorted problem they always are,
  and the Rust code needs this for termination.

  As in \<^verbatim>\<open>QFBV_Lower\<close>, the indices of definitions are natural numbers, and the state is an
  \<^typ>\<open>lst\<close>: the new definitions and their widths.
\<close>

subsection \<open>Models of the functions\<close>

text \<open>\<^verbatim>\<open>commutative\<close>.\<close>
definition comm_op :: \<open>BinOp \<Rightarrow> bool\<close> where
  \<open>comm_op op \<equiv> op \<in> {BinOp_And, BinOp_Or, BinOp_Xor, BinOp_Add, BinOp_Mul, BinOp_Eq}\<close>

text \<open>\<^verbatim>\<open>norm_eq\<close>: equal up to the order of the operands of a commutative operator at the top.
  \<^verbatim>\<open>term_eq\<close> and \<^verbatim>\<open>same_bits\<close> are equality.\<close>
definition norm_eq_m :: \<open>CoreTermL \<Rightarrow> CoreTermL \<Rightarrow> bool\<close> where
  \<open>norm_eq_m a b \<equiv>
     (case a of
        CoreTermL_Bin op1 x1 x2 \<Rightarrow>
          (case b of
             CoreTermL_Bin op2 y1 y2 \<Rightarrow>
               op1 = op2 \<and> ((x1 = y1 \<and> x2 = y2) \<or> (comm_op op1 \<and> x1 = y2 \<and> x2 = y1))
           | _ \<Rightarrow> False)
      | _ \<Rightarrow> a = b)\<close>

text \<open>\<^verbatim>\<open>remap\<close>.\<close>
primrec remap_m :: \<open>nat list \<Rightarrow> CoreTermL \<Rightarrow> CoreTermL\<close> where
  \<open>remap_m M (CoreTermL_Const bs) = CoreTermL_Const bs\<close>
| \<open>remap_m M (CoreTermL_Var i) = CoreTermL_Var i\<close>
| \<open>remap_m M (CoreTermL_Ref i) = cr (M ! unat i)\<close>
| \<open>remap_m M (CoreTermL_Not a) = CoreTermL_Not (remap_m M a)\<close>
| \<open>remap_m M (CoreTermL_Bin op a b) = CoreTermL_Bin op (remap_m M a) (remap_m M b)\<close>
| \<open>remap_m M (CoreTermL_Extract hi lo a) = CoreTermL_Extract hi lo (remap_m M a)\<close>
| \<open>remap_m M (CoreTermL_Ite c a b) = CoreTermL_Ite (remap_m M c) (remap_m M a) (remap_m M b)\<close>

text \<open>\<^verbatim>\<open>ref_index(t, usize::MAX)\<close>, with \<^const>\<open>None\<close> for \<^verbatim>\<open>usize::MAX\<close>.\<close>
definition ref_of :: \<open>CoreTermL \<Rightarrow> nat option\<close> where
  \<open>ref_of t \<equiv> (case t of CoreTermL_Ref i \<Rightarrow> Some (unat i) | _ \<Rightarrow> None)\<close>

text \<open>\<^verbatim>\<open>is_ones\<close> (with \<^verbatim>\<open>all_ones\<close>).\<close>
definition is_ones_m :: \<open>CoreTermL list \<Rightarrow> CoreTermL \<Rightarrow> bool\<close> where
  \<open>is_ones_m D t \<equiv>
     (case t of
        CoreTermL_Const bs \<Rightarrow> (\<forall>b \<in> set bs. b)
      | CoreTermL_Ref k \<Rightarrow> (case D ! unat k of CoreTermL_Const bs \<Rightarrow> (\<forall>b \<in> set bs. b) | _ \<Rightarrow> False)
      | _ \<Rightarrow> False)\<close>

text \<open>\<^verbatim>\<open>not_of\<close>.\<close>
definition not_of_m :: \<open>CoreTermL list \<Rightarrow> CoreTermL \<Rightarrow> nat option\<close> where
  \<open>not_of_m D t \<equiv>
     (case t of
        CoreTermL_Ref k \<Rightarrow> (case D ! unat k of CoreTermL_Not a \<Rightarrow> ref_of a | _ \<Rightarrow> None)
      | _ \<Rightarrow> None)\<close>

text \<open>The operands of a product of two references.\<close>
definition mul_refs :: \<open>CoreTermL \<Rightarrow> (nat \<times> nat) option\<close> where
  \<open>mul_refs t \<equiv>
     (case t of
        CoreTermL_Bin op a b \<Rightarrow>
          (if op = BinOp_Mul then
             (case ref_of a of Some x \<Rightarrow> (case ref_of b of Some y \<Rightarrow> Some (x, y) | None \<Rightarrow> None) | None \<Rightarrow> None)
           else None)
      | _ \<Rightarrow> None)\<close>

text \<open>\<^verbatim>\<open>factors\<close>.\<close>
function factors_m :: \<open>CoreTermL list \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list \<times> bool\<close> where
  \<open>factors_m D k out cap =
     (if cap < length out then (out, False)
      else (case mul_refs (D ! k) of
              Some (x, y) \<Rightarrow>
                (if x < k \<and> y < k then
                   (let r = factors_m D x out cap in
                    if snd r then factors_m D y (fst r) cap else (fst r, False))
                 else (out @ [k], length (out @ [k]) \<le> cap))
            | None \<Rightarrow> (out @ [k], length (out @ [k]) \<le> cap)))\<close>
  by pat_completeness auto
termination by (relation \<open>measure (\<lambda>(D, k, out, cap). k)\<close>) auto

declare factors_m.simps [simp del]

text \<open>\<^verbatim>\<open>product_factors\<close>.\<close>
definition product_factors_m :: \<open>CoreTermL list \<Rightarrow> CoreTermL \<Rightarrow> nat list \<times> bool\<close> where
  \<open>product_factors_m D t \<equiv>
     (case mul_refs t of
        Some (ka, kb) \<Rightarrow>
          (let r = factors_m D ka [] 16 in if snd r then factors_m D kb (fst r) 16 else (fst r, False))
      | None \<Rightarrow> ([], False))\<close>

text \<open>\<^verbatim>\<open>rewrite\<close>: \<^verbatim>\<open>cneg\<close> is \<^const>\<open>neg_t\<close>.\<close>
definition rewrite_m :: \<open>CoreTermL list \<Rightarrow> CoreTermL \<Rightarrow> nat \<Rightarrow> CoreTermL\<close> where
  \<open>rewrite_m D t w \<equiv>
     (case t of
        CoreTermL_Bin op a b \<Rightarrow>
          (if op = BinOp_Eq \<and> a = b then CoreTermL_Const [True]
           else if op = BinOp_Add \<and> ((ref_of a \<noteq> None \<and> not_of_m D b = ref_of a) \<or>
                                     (ref_of b \<noteq> None \<and> not_of_m D a = ref_of b))
           then CoreTermL_Const (replicate w True)
           else if op = BinOp_Mul \<and> 0 < w \<and> ref_of a \<noteq> None \<and> is_ones_m D b then neg_t (the (ref_of a)) w
           else if op = BinOp_Mul \<and> 0 < w \<and> ref_of b \<noteq> None \<and> is_ones_m D a then neg_t (the (ref_of b)) w
           else t)
      | _ \<Rightarrow> t)\<close>

text \<open>\<^verbatim>\<open>find_def\<close>, without the buckets: the first definition of width \<open>w\<close> equal to \<open>t\<close>.\<close>
definition find_def_m :: \<open>lst \<Rightarrow> CoreTermL \<Rightarrow> nat \<Rightarrow> nat option\<close> where
  \<open>find_def_m L t w \<equiv> List.find (\<lambda>k. snd L ! k = w \<and> norm_eq_m (fst L ! k) t) [0..<length (fst L)]\<close>

text \<open>\<^verbatim>\<open>mk_raw\<close>.\<close>
definition mk_raw_m :: \<open>lst \<Rightarrow> CoreTermL \<Rightarrow> nat \<Rightarrow> lst \<times> nat\<close> where
  \<open>mk_raw_m L t w \<equiv>
     (case ref_of t of
        Some r \<Rightarrow> (L, r)
      | None \<Rightarrow> (case find_def_m L t w of Some f \<Rightarrow> (L, f) | None \<Rightarrow> push_m L t w))\<close>

text \<open>One iteration of the loop of \<^verbatim>\<open>mk\<close> over the sorted factors.\<close>
definition mul_step :: \<open>nat \<Rightarrow> lst \<times> nat \<Rightarrow> nat \<Rightarrow> lst \<times> nat\<close> where
  \<open>mul_step w \<equiv> \<lambda>(L, acc) f. mk_raw_m L (CoreTermL_Bin BinOp_Mul (cr acc) (cr f)) w\<close>

text \<open>\<^verbatim>\<open>mk\<close>; \<^verbatim>\<open>sort_usize\<close> is \<^const>\<open>sort\<close>.\<close>
definition mk_m :: \<open>lst \<Rightarrow> CoreTermL \<Rightarrow> nat \<Rightarrow> lst \<times> nat\<close> where
  \<open>mk_m L t w \<equiv>
     (let r = rewrite_m (fst L) t w in
      let (fs, ok) = product_factors_m (fst L) r in
      if ok \<and> 2 < length fs then (let fs = List.sort fs in foldl (mul_step w) (L, hd fs) (tl fs))
      else mk_raw_m L r w)\<close>

text \<open>The loop of \<^verbatim>\<open>normalize\<close> over the old definitions: the state is the new definitions and
  the new index \<open>M\<close> of each old definition so far; \<open>dw\<close> are the widths of the old definitions.\<close>
primrec norm_loop :: \<open>nat list \<Rightarrow> CoreTermL list \<Rightarrow> lst \<times> nat list \<Rightarrow> lst \<times> nat list\<close> where
  \<open>norm_loop dw [] S = S\<close>
| \<open>norm_loop dw (d # dd) S =
     (let (L, M) = S in
      let (L1, k) = mk_m L (remap_m M d) (dw ! length M) in
      norm_loop dw dd (L1, M @ [k]))\<close>

text \<open>\<^verbatim>\<open>normalize\<close> (\<^verbatim>\<open>def_widths\<close> is \<^const>\<open>cdef_widths\<close>), without the substitution.\<close>
definition normalize_m :: \<open>CoreProblemL \<Rightarrow> CoreProblemL\<close> where
  \<open>normalize_m q \<equiv>
     (let ws = cvar_widths q in
      let dw = cdef_widths ws [] (CoreProblemL_defs q) in
      let (L, M) = norm_loop dw (CoreProblemL_defs q) (([], []), []) in
      make_CoreProblemL (CoreProblemL_widths q) (fst L) (map (remap_m M) (CoreProblemL_asserts q)))\<close>

subsection \<open>Definitions in a well-formed state\<close>

lemma wt_ext:
  \<open>cwt ws ds t \<Longrightarrow> cwt ws (ds @ e) t \<and> cwidth ws (ds @ e) t = cwidth ws ds t\<close>
  by (induction t) (auto simp add: nth_append)

lemma eval_ext:
  \<open>cwt ws ds t \<Longrightarrow> length dv = length ds \<Longrightarrow> ceval ws (ds @ e) vs (dv @ f) t = ceval ws ds vs dv t\<close>
  by (induction t) (auto simp add: nth_append wt_ext)

text \<open>Definition \<open>k\<close> of a well-formed state is well-sorted over all the definitions, and its width
  and value are those of its term.\<close>
lemma lok_nth:
  assumes \<open>lok ws L\<close> \<open>k < length (fst L)\<close>
  shows \<open>cwt ws (snd L) (fst L ! k)\<close> \<open>snd L ! k = cwidth ws (snd L) (fst L ! k)\<close>
    \<open>CV ws vs L ! k = ceval ws (snd L) vs (CV ws vs L) (fst L ! k)\<close>
proof -
  let ?D = \<open>fst L\<close>
  let ?P = \<open>take k ?D\<close> and ?d = \<open>?D ! k\<close> and ?R = \<open>drop (Suc k) ?D\<close>
  let ?ds = \<open>cdef_widths ws [] ?P\<close> and ?dv = \<open>cdef_values ws [] vs [] ?P\<close>
  have D: \<open>?D = ?P @ [?d] @ ?R\<close> using assms(2) by (simp add: id_take_nth_drop)
  have wt: \<open>cwt ws ?ds ?d\<close>
    using assms(1) D by (simp add: lok_def) (metis cdefs_wt.simps(2) cdefs_wt_append)
  have l: \<open>length ?ds = k\<close> \<open>length ?dv = k\<close>
    using assms(2) by (simp_all add: cdef_widths_length cdef_values_length)
  have W: \<open>snd L = cdef_widths ws (?ds @ [cwidth ws ?ds ?d]) ?R\<close>
    using assms(1) D by (metis lok_def cdef_widths_append cdef_widths.simps)
  obtain e where e: \<open>snd L = (?ds @ [cwidth ws ?ds ?d]) @ e\<close>
    using W cdef_widths_prefix[of ws \<open>?ds @ [cwidth ws ?ds ?d]\<close> ?R] by metis
  obtain f where f: \<open>CV ws vs L = (?dv @ [ceval ws ?ds vs ?dv ?d]) @ f\<close>
    using D cdef_values_prefix[of ws \<open>?ds @ [cwidth ws ?ds ?d]\<close> vs \<open>?dv @ [ceval ws ?ds vs ?dv ?d]\<close> ?R]
    by (metis append.assoc cdef_values.simps cdef_values_append cdef_widths.simps)
  show \<open>cwt ws (snd L) (fst L ! k)\<close> using wt_ext[OF wt, of \<open>[cwidth ws ?ds ?d] @ e\<close>] e by simp
  show \<open>snd L ! k = cwidth ws (snd L) (fst L ! k)\<close>
    using wt_ext[OF wt, of \<open>[cwidth ws ?ds ?d] @ e\<close>] e l by (simp add: nth_append)
  show \<open>CV ws vs L ! k = ceval ws (snd L) vs (CV ws vs L) (fst L ! k)\<close>
    using eval_ext[OF wt, of ?dv \<open>[cwidth ws ?ds ?d] @ e\<close> vs \<open>[ceval ws ?ds vs ?dv ?d] @ f\<close>] e f l
    by (simp add: nth_append)
qed

subsection \<open>Remapping\<close>

text \<open>The new definition \<open>M ! j\<close> has the width and the value of the old definition \<open>j\<close>.\<close>
definition menv :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool\<close> where
  \<open>menv M cws ds \<equiv> \<forall>j < length ds. M ! j < length cws \<and> M ! j < 2 ^ 64 \<and> cws ! (M ! j) = ds ! j\<close>

definition venv :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool\<close> where
  \<open>venv M cdv ds dv \<equiv> \<forall>j < length ds. cdv ! (M ! j) = dv ! j\<close>

lemma remap_wt:
  \<open>menv M cws ds \<Longrightarrow> cwt ws ds t \<Longrightarrow>
   cwt ws cws (remap_m M t) \<and> cwidth ws cws (remap_m M t) = cwidth ws ds t\<close>
  by (induction t) (auto simp add: menv_def cr_def unat_wn)

lemma remap_eval:
  \<open>menv M cws ds \<Longrightarrow> venv M cdv ds dv \<Longrightarrow> cwt ws ds t \<Longrightarrow>
   ceval ws cws vs cdv (remap_m M t) = ceval ws ds vs dv t\<close>
  by (induction t) (auto simp add: menv_def venv_def cr_def unat_wn remap_wt)

subsection \<open>Equal definitions\<close>

lemma comm_op_not_concat: \<open>comm_op op \<Longrightarrow> op \<noteq> BinOp_Concat\<close>
  by (auto simp add: comm_op_def)

lemma cbin_sem_comm: \<open>comm_op op \<Longrightarrow> cbin_sem op w x v y = cbin_sem op w y u x\<close>
  by (auto simp add: comm_op_def ac_simps)

lemma norm_eq_sem:
  assumes \<open>norm_eq_m a b\<close> \<open>cwt ws ds a\<close>
  shows \<open>cwt ws ds b \<and> cwidth ws ds b = cwidth ws ds a \<and> ceval ws ds vs dv b = ceval ws ds vs dv a\<close>
  using assms by (cases a; cases b) (auto simp add: norm_eq_m_def comm_op_def ac_simps and.commute or.commute xor.commute)

subsection \<open>The rewrites\<close>

lemma ref_of_Some: \<open>ref_of t = Some k \<longleftrightarrow> (\<exists>i. t = CoreTermL_Ref i \<and> k = unat i)\<close>
  by (cases t) (auto simp add: ref_of_def)

lemma mul_refs_Some:
  \<open>mul_refs t = Some (x, y) \<longleftrightarrow>
   (\<exists>i j. t = CoreTermL_Bin BinOp_Mul (CoreTermL_Ref i) (CoreTermL_Ref j) \<and> x = unat i \<and> y = unat j)\<close>
  by (cases t) (auto simp add: mul_refs_def ref_of_def split: option.splits CoreTermL.splits)

lemma all_True: \<open>\<forall>b \<in> set bs. b \<Longrightarrow> bits_nat bs = 2 ^ length bs - 1\<close>
proof -
  assume \<open>\<forall>b \<in> set bs. b\<close>
  then have \<open>bs = replicate (length bs) True\<close> by (induction bs) auto
  then show ?thesis using bits_nat_replicate_True[of \<open>length bs\<close>] by (metis add_diff_cancel_right')
qed

lemma mul_ones: \<open>(x :: nat) < 2 ^ w \<Longrightarrow> (x * (2 ^ w - 1)) mod 2 ^ w = negv w x\<close>
proof (cases \<open>x = 0\<close>)
  case True
  then show ?thesis by (simp add: negv_def)
next
  case False
  assume x: \<open>x < 2 ^ w\<close>
  obtain n where n: \<open>x = Suc n\<close> using False by (cases x) auto
  obtain k where k: \<open>(2 :: nat) ^ w = Suc n + k\<close> using x n less_imp_add_positive by (metis add.commute less_imp_Suc_add plus_1_eq_Suc)
  have e: \<open>Suc n * (n + k) = k + n * (Suc n + k)\<close> by (simp add: algebra_simps)
  have \<open>(k + n * (Suc n + k)) mod (Suc n + k) = k\<close> by (simp only: mod_mult_self1) simp
  then have \<open>(Suc n * (n + k)) mod (Suc n + k) = k\<close> by (simp only: e)
  then show ?thesis unfolding negv_def n k by simp
qed

lemma is_ones_sem:
  assumes \<open>lok ws L\<close> \<open>cwt ws (snd L) b\<close> \<open>is_ones_m (fst L) b\<close>
  shows \<open>ceval ws (snd L) vs (CV ws vs L) b = 2 ^ cwidth ws (snd L) b - 1\<close>
proof (cases b)
  case (CoreTermL_Ref k)
  have kl: \<open>unat k < length (fst L)\<close> using assms(1,2) CoreTermL_Ref lok_length by fastforce
  obtain bs where d: \<open>fst L ! unat k = CoreTermL_Const bs\<close> \<open>\<forall>b \<in> set bs. b\<close>
    using assms(3) CoreTermL_Ref by (auto simp add: is_ones_m_def split: CoreTermL.splits)
  show ?thesis using lok_nth[OF assms(1) kl] d CoreTermL_Ref all_True by simp
qed (use assms(3) in \<open>simp_all add: is_ones_m_def all_True\<close>)

lemma not_of_sem:
  assumes \<open>lok ws L\<close> \<open>cwt ws (snd L) b\<close> \<open>not_of_m (fst L) b = Some x\<close>
  shows \<open>x < length (fst L) \<and> cwidth ws (snd L) b = snd L ! x \<and>
    ceval ws (snd L) vs (CV ws vs L) b = 2 ^ (snd L ! x) - 1 - CV ws vs L ! x\<close>
proof -
  obtain k where b: \<open>b = CoreTermL_Ref k\<close> using assms(3) by (cases b) (auto simp add: not_of_m_def)
  have kl: \<open>unat k < length (fst L)\<close> using assms(1,2) b lok_length by fastforce
  obtain i where d: \<open>fst L ! unat k = CoreTermL_Not (CoreTermL_Ref i)\<close> and xi: \<open>x = unat i\<close>
    using assms(3) b by (auto simp add: not_of_m_def ref_of_def split: CoreTermL.splits)
  show ?thesis using lok_nth[OF assms(1) kl] d xi b lok_length[OF assms(1)] by simp
qed

lemma rewrite_sem:
  assumes \<open>lok ws L\<close> \<open>cwt ws (snd L) t\<close> \<open>cwidth ws (snd L) t = w\<close>
  shows \<open>cwt ws (snd L) (rewrite_m (fst L) t w) \<and> cwidth ws (snd L) (rewrite_m (fst L) t w) = w \<and>
    (\<forall>vs. vs_ok ws vs \<longrightarrow>
       ceval ws (snd L) vs (CV ws vs L) (rewrite_m (fst L) t w) = ceval ws (snd L) vs (CV ws vs L) t)\<close>
proof (cases t)
  case (CoreTermL_Bin op a b)
  let ?D = \<open>fst L\<close> and ?W = \<open>snd L\<close>
  have wt: \<open>cwt ws ?W a\<close> \<open>cwt ws ?W b\<close> \<open>op \<noteq> BinOp_Concat \<longrightarrow> cwidth ws ?W a = cwidth ws ?W b\<close>
    using assms(2) CoreTermL_Bin by simp_all
  have lw: \<open>length ?W = length ?D\<close> using lok_length[OF assms(1)] .
  have refd: \<open>x < length ?D \<and> x < 2 ^ 64 \<and> cwidth ws ?W u = ?W ! x \<and>
      (\<forall>vs. ceval ws ?W vs (CV ws vs L) u = CV ws vs L ! x)\<close>
    if \<open>ref_of u = Some x\<close> \<open>cwt ws ?W u\<close> for u x
    using that lw unat_lt2p[where 'a=64] by (auto simp add: ref_of_Some)
  show ?thesis
  proof (cases \<open>op = BinOp_Eq \<and> a = b\<close>)
    case True
    then show ?thesis using CoreTermL_Bin assms(3) by (simp add: rewrite_m_def)
  next
    case n1: False
    show ?thesis
    proof (cases \<open>op = BinOp_Add \<and> ((ref_of a \<noteq> None \<and> not_of_m ?D b = ref_of a) \<or>
                                      (ref_of b \<noteq> None \<and> not_of_m ?D a = ref_of b))\<close>)
      case True
      have r: \<open>rewrite_m ?D t w = CoreTermL_Const (replicate w True)\<close>
        using True n1 CoreTermL_Bin by (simp add: rewrite_m_def)
      have val: \<open>ceval ws ?W vs (CV ws vs L) t = 2 ^ w - 1\<close> if vs: \<open>vs_ok ws vs\<close> for vs
      proof -
        let ?V = \<open>CV ws vs L\<close>
        from True obtain x u v where uv: \<open>(u = a \<and> v = b) \<or> (u = b \<and> v = a)\<close> \<open>ref_of u = Some x\<close>
          \<open>not_of_m ?D v = Some x\<close>
          by (metis option.collapse)
        have wuv: \<open>cwt ws ?W u\<close> \<open>cwt ws ?W v\<close> using uv(1) wt by auto
        note u = refd[OF uv(2) wuv(1)]
        note v = not_of_sem[OF assms(1) wuv(2) uv(3), of vs]
        have w: \<open>w = ?W ! x\<close> using assms(3) CoreTermL_Bin wt uv(1) u v True by auto
        have lt: \<open>?V ! x < 2 ^ w\<close> using lok_CV_lt[OF assms(1) vs conjunct1[OF u]] w by simp
        have \<open>ceval ws ?W vs ?V t = (ceval ws ?W vs ?V u + ceval ws ?W vs ?V v) mod 2 ^ w\<close>
          using uv(1) u v w CoreTermL_Bin True wt by (auto simp add: add.commute)
        also have \<open>\<dots> = (?V ! x + (2 ^ w - 1 - ?V ! x)) mod 2 ^ w\<close> using u v w by simp
        also have \<open>\<dots> = 2 ^ w - 1\<close> using lt by simp
        finally show ?thesis .
      qed
      show ?thesis using r val by (simp add: all_True)
    next
      case n2: False
      show ?thesis
      proof (cases \<open>op = BinOp_Mul \<and> 0 < w \<and> ref_of a \<noteq> None \<and> is_ones_m ?D b\<close>)
        case True
        obtain x where x: \<open>ref_of a = Some x\<close> using True by auto
        have r: \<open>rewrite_m ?D t w = neg_t x w\<close> using True n1 n2 x CoreTermL_Bin by (simp add: rewrite_m_def)
        note u = refd[OF x wt(1)]
        have w: \<open>?W ! x = w\<close> using assms(3) CoreTermL_Bin True u by simp
        have w1: \<open>1 \<le> w\<close> using True by simp
        have z: \<open>ref_ok ?W (replicate (length ?W) 0) x w 0\<close> using u w lw by (simp add: ref_ok_def)
        have val: \<open>ceval ws ?W vs (CV ws vs L) (neg_t x w) = ceval ws ?W vs (CV ws vs L) t\<close>
          if vs: \<open>vs_ok ws vs\<close> for vs
        proof -
          let ?V = \<open>CV ws vs L\<close>
          have lt: \<open>?V ! x < 2 ^ w\<close> using lok_CV_lt[OF assms(1) vs conjunct1[OF u]] w by simp
          have ro: \<open>ref_ok ?W ?V x w (?V ! x)\<close> using u w lt lw by (simp add: ref_ok_def)
          have b1: \<open>ceval ws ?W vs ?V b = 2 ^ w - 1\<close>
            using is_ones_sem[OF assms(1) wt(2)] True wt(3) u w by simp
          show ?thesis using neg_t_sem(3)[OF ro w1] mul_ones[OF lt] b1 u w CoreTermL_Bin True by simp
        qed
        show ?thesis using r neg_t_sem(1,2)[OF z w1] val by simp
      next
        case n3: False
        show ?thesis
        proof (cases \<open>op = BinOp_Mul \<and> 0 < w \<and> ref_of b \<noteq> None \<and> is_ones_m ?D a\<close>)
          case True
          obtain x where x: \<open>ref_of b = Some x\<close> using True by auto
          have r: \<open>rewrite_m ?D t w = neg_t x w\<close> using True n1 n2 n3 x CoreTermL_Bin by (auto simp add: rewrite_m_def)
          note u = refd[OF x wt(2)]
          have w: \<open>?W ! x = w\<close> using assms(3) CoreTermL_Bin True u wt(3) by simp
          have w1: \<open>1 \<le> w\<close> using True by simp
          have z: \<open>ref_ok ?W (replicate (length ?W) 0) x w 0\<close> using u w lw by (simp add: ref_ok_def)
          have val: \<open>ceval ws ?W vs (CV ws vs L) (neg_t x w) = ceval ws ?W vs (CV ws vs L) t\<close>
            if vs: \<open>vs_ok ws vs\<close> for vs
          proof -
            let ?V = \<open>CV ws vs L\<close>
            have lt: \<open>?V ! x < 2 ^ w\<close> using lok_CV_lt[OF assms(1) vs conjunct1[OF u]] w by simp
            have ro: \<open>ref_ok ?W ?V x w (?V ! x)\<close> using u w lt lw by (simp add: ref_ok_def)
            have a1: \<open>ceval ws ?W vs ?V a = 2 ^ w - 1\<close> \<open>cwidth ws ?W a = w\<close>
              using is_ones_sem[OF assms(1) wt(1)] True wt(3) u w by simp_all
            show ?thesis using neg_t_sem(3)[OF ro w1] mul_ones[OF lt] a1 u w CoreTermL_Bin True
              by (simp add: mult.commute)
          qed
          show ?thesis using r neg_t_sem(1,2)[OF z w1] val by simp
        next
          case False
          then have \<open>rewrite_m ?D t w = t\<close> using n1 n2 n3 CoreTermL_Bin by (auto simp add: rewrite_m_def)
          then show ?thesis using assms(2,3) by simp
        qed
      qed
    qed
  qed
qed (use assms in \<open>simp_all add: rewrite_m_def\<close>)

subsection \<open>Sharing\<close>

lemma mk_raw_ok:
  assumes \<open>lok ws L\<close> \<open>cwt ws (snd L) t\<close> \<open>cwidth ws (snd L) t = w\<close> \<open>mk_raw_m L t w = (L', k)\<close>
  shows \<open>lext ws L L' \<and> length (fst L') \<le> Suc (length (fst L)) \<and> k < length (fst L') \<and> snd L' ! k = w \<and>
    (\<forall>vs. CV ws vs L' ! k = ceval ws (snd L) vs (CV ws vs L) t)\<close>
proof (cases \<open>ref_of t\<close>)
  case (Some r)
  then obtain i where t: \<open>t = CoreTermL_Ref i\<close> \<open>r = unat i\<close> by (auto simp add: ref_of_Some)
  have e: \<open>L' = L\<close> \<open>k = r\<close> using assms(4) Some by (simp_all add: mk_raw_m_def)
  show ?thesis using e t assms(1-3) lok_length[OF assms(1)] by (auto simp add: lext_refl)
next
  case None
  show ?thesis
  proof (cases \<open>find_def_m L t w\<close>)
    case (Some f)
    have e: \<open>L' = L\<close> \<open>k = f\<close> using assms(4) None Some by (simp_all add: mk_raw_m_def)
    have f: \<open>f < length (fst L)\<close> \<open>snd L ! f = w\<close> \<open>norm_eq_m (fst L ! f) t\<close>
      using Some by (auto simp add: find_def_m_def find_Some_iff)
    note N = lok_nth[OF assms(1) f(1)]
    have \<open>ceval ws (snd L) vs (CV ws vs L) t = CV ws vs L ! f\<close> for vs
      using norm_eq_sem[OF f(3) N(1)] N(3) by simp
    then show ?thesis using e f lext_refl[OF assms(1)] by simp
  next
    case n2: None
    have p: \<open>push_m L t w = (L', k)\<close> using assms(4) None n2 by (simp add: mk_raw_m_def)
    note P = push_ok[OF assms(1-3) p]
    show ?thesis using P lext_push[OF assms(1-3) p] lok_length[OF assms(1)] lok_CV_length
      by (simp add: nth_append)
  qed
qed

subsection \<open>Products\<close>

text \<open>The product of the values of the factors \<open>fs\<close>.\<close>
definition pv :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> nat\<close> where
  \<open>pv V fs \<equiv> prod_list (map (\<lambda>f. V ! f) fs)\<close>

lemma factors_ok:
  assumes \<open>lok ws L\<close> \<open>D = fst L\<close> \<open>factors_m D k out cap = (out', True)\<close> \<open>k < length (fst L)\<close>
  shows \<open>\<exists>fs. out' = out @ fs \<and> length out' \<le> cap \<and>
    (\<forall>f \<in> set fs. f < length (fst L) \<and> snd L ! f = snd L ! k) \<and>
    (\<forall>vs. vs_ok ws vs \<longrightarrow> pv (CV ws vs L) fs mod 2 ^ (snd L ! k) = CV ws vs L ! k)\<close>
  using assms(2-4)
proof (induction D k out cap arbitrary: out' rule: factors_m.induct)
  case (1 D k out cap)
  let ?W = \<open>snd L\<close>
  note eq = factors_m.simps[of D k out cap]
  have nc: \<open>\<not> cap < length out\<close> using 1(4) eq by (auto split: if_splits)
  show ?case
  proof (cases \<open>\<exists>x y. mul_refs (D ! k) = Some (x, y) \<and> x < k \<and> y < k\<close>)
    case False
    then have o: \<open>out' = out @ [k]\<close> \<open>length (out @ [k]) \<le> cap\<close>
      using 1(4) nc eq by (auto split: option.splits if_splits)
    have \<open>pv (CV ws vs L) [k] mod 2 ^ (?W ! k) = CV ws vs L ! k\<close> if \<open>vs_ok ws vs\<close> for vs
      using lok_CV_lt[OF assms(1) that 1(5)] by (simp add: pv_def)
    then show ?thesis using o 1(5) by auto
  next
    case True
    then obtain x y where xy: \<open>mul_refs (D ! k) = Some (x, y)\<close> \<open>x < k\<close> \<open>y < k\<close> by blast
    obtain o1 ok1 where r1: \<open>factors_m D x out cap = (o1, ok1)\<close> by fastforce
    have ok1: ok1 and r2: \<open>factors_m D y o1 cap = (out', True)\<close>
      using 1(4) nc eq xy r1 by (auto simp add: Let_def split: if_splits)
    have xl: \<open>x < length (fst L)\<close> \<open>y < length (fst L)\<close> using xy 1(5) by simp_all
    have r1': \<open>factors_m D x out cap = (o1, True)\<close> using r1 ok1 by simp
    obtain fs1 where F1: \<open>o1 = out @ fs1\<close> \<open>length o1 \<le> cap\<close>
      \<open>\<forall>f \<in> set fs1. f < length (fst L) \<and> ?W ! f = ?W ! x\<close>
      \<open>\<forall>vs. vs_ok ws vs \<longrightarrow> pv (CV ws vs L) fs1 mod 2 ^ (?W ! x) = CV ws vs L ! x\<close>
      using 1(1)[OF nc xy(1) refl conjI[OF xy(2,3)] 1(3) r1' xl(1)] by blast
    obtain fs2 where F2: \<open>out' = o1 @ fs2\<close> \<open>length out' \<le> cap\<close>
      \<open>\<forall>f \<in> set fs2. f < length (fst L) \<and> ?W ! f = ?W ! y\<close>
      \<open>\<forall>vs. vs_ok ws vs \<longrightarrow> pv (CV ws vs L) fs2 mod 2 ^ (?W ! y) = CV ws vs L ! y\<close>
      using 1(2)[of \<open>(x, y)\<close> x y \<open>(o1, True)\<close> out', OF nc xy(1) refl conjI[OF xy(2,3)]] r1 ok1 1(3) r2 xl(2)
      by auto
    obtain i j where ij: \<open>D ! k = CoreTermL_Bin BinOp_Mul (CoreTermL_Ref i) (CoreTermL_Ref j)\<close>
      \<open>x = unat i\<close> \<open>y = unat j\<close>
      using xy(1) by (auto simp add: mul_refs_Some)
    note N = lok_nth[OF assms(1) 1(5)]
    have W: \<open>?W ! y = ?W ! x\<close> \<open>?W ! k = ?W ! x\<close> using N(1,2) ij 1(3) by simp_all
    have V: \<open>CV ws vs L ! k = (CV ws vs L ! x * CV ws vs L ! y) mod 2 ^ (?W ! x)\<close> for vs
      using N(3) ij 1(3) by simp
    have \<open>pv (CV ws vs L) (fs1 @ fs2) mod 2 ^ (?W ! k) = CV ws vs L ! k\<close> if \<open>vs_ok ws vs\<close> for vs
    proof -
      have \<open>pv (CV ws vs L) (fs1 @ fs2) mod 2 ^ (?W ! k) =
          (pv (CV ws vs L) fs1 mod 2 ^ (?W ! x) * (pv (CV ws vs L) fs2 mod 2 ^ (?W ! y))) mod 2 ^ (?W ! x)\<close>
        using W by (simp add: pv_def mod_mult_eq)
      then show ?thesis using F1(4) F2(4) that V by simp
    qed
    then show ?thesis using F1 F2 W by auto
  qed
qed

lemma product_ok:
  assumes \<open>lok ws L\<close> \<open>cwt ws (snd L) r\<close> \<open>product_factors_m (fst L) r = (fs, True)\<close>
  shows \<open>length fs \<le> 16 \<and> (\<forall>f \<in> set fs. f < length (fst L) \<and> snd L ! f = cwidth ws (snd L) r) \<and>
    (\<forall>vs. vs_ok ws vs \<longrightarrow>
       pv (CV ws vs L) fs mod 2 ^ cwidth ws (snd L) r = ceval ws (snd L) vs (CV ws vs L) r)\<close>
proof -
  let ?W = \<open>snd L\<close>
  obtain ka kb where m: \<open>mul_refs r = Some (ka, kb)\<close>
    using assms(3) by (auto simp add: product_factors_m_def split: option.splits)
  obtain i j where r: \<open>r = CoreTermL_Bin BinOp_Mul (CoreTermL_Ref i) (CoreTermL_Ref j)\<close>
    \<open>ka = unat i\<close> \<open>kb = unat j\<close>
    using m by (auto simp add: mul_refs_Some)
  obtain o1 ok1 where r1: \<open>factors_m (fst L) ka [] 16 = (o1, ok1)\<close> by fastforce
  have ok1: ok1 and r2: \<open>factors_m (fst L) kb o1 16 = (fs, True)\<close>
    using assms(3) m r1 by (auto simp add: product_factors_m_def Let_def split: if_splits)
  have r1': \<open>factors_m (fst L) ka [] 16 = (o1, True)\<close> using r1 ok1 by simp
  have kl: \<open>ka < length (fst L)\<close> \<open>kb < length (fst L)\<close> using assms(2) r lok_length[OF assms(1)] by simp_all
  obtain fs1 where F1: \<open>o1 = fs1\<close> \<open>\<forall>f \<in> set fs1. f < length (fst L) \<and> ?W ! f = ?W ! ka\<close>
    \<open>\<forall>vs. vs_ok ws vs \<longrightarrow> pv (CV ws vs L) fs1 mod 2 ^ (?W ! ka) = CV ws vs L ! ka\<close>
    using factors_ok[OF assms(1) refl r1' kl(1)] by auto
  obtain fs2 where F2: \<open>fs = o1 @ fs2\<close> \<open>length fs \<le> 16\<close> \<open>\<forall>f \<in> set fs2. f < length (fst L) \<and> ?W ! f = ?W ! kb\<close>
    \<open>\<forall>vs. vs_ok ws vs \<longrightarrow> pv (CV ws vs L) fs2 mod 2 ^ (?W ! kb) = CV ws vs L ! kb\<close>
    using factors_ok[OF assms(1) refl r2 kl(2)] by auto
  have W: \<open>?W ! kb = ?W ! ka\<close> \<open>cwidth ws ?W r = ?W ! ka\<close> using assms(2) r by simp_all
  have \<open>pv (CV ws vs L) fs mod 2 ^ cwidth ws ?W r = ceval ws ?W vs (CV ws vs L) r\<close> if \<open>vs_ok ws vs\<close> for vs
  proof -
    have \<open>pv (CV ws vs L) fs mod 2 ^ cwidth ws ?W r =
        (pv (CV ws vs L) fs1 mod 2 ^ (?W ! ka) * (pv (CV ws vs L) fs2 mod 2 ^ (?W ! kb))) mod 2 ^ (?W ! ka)\<close>
      using W F1(1) F2(1) by (simp add: pv_def mod_mult_eq)
    then show ?thesis using F1(3) F2(4) that r by simp
  qed
  then show ?thesis using F1 F2 W by auto
qed

lemma pv_lext: \<open>lext ws L L1 \<Longrightarrow> \<forall>f \<in> set fs. f < length (fst L) \<Longrightarrow> pv (CV ws vs L1) fs = pv (CV ws vs L) fs\<close>
proof -
  assume l: \<open>lext ws L L1\<close> and f: \<open>\<forall>f \<in> set fs. f < length (fst L)\<close>
  have \<open>map (\<lambda>f. CV ws vs L1 ! f) fs = map (\<lambda>f. CV ws vs L ! f) fs\<close>
    using f lext_nth_CV[OF l] by (induction fs) auto
  then show ?thesis unfolding pv_def by (simp only:)
qed

lemma mul_fold:
  assumes \<open>lok ws L\<close> \<open>length (fst L) + length fs < 2 ^ 64\<close> \<open>acc < length (fst L)\<close> \<open>snd L ! acc = w\<close>
    \<open>\<forall>f \<in> set fs. f < length (fst L) \<and> snd L ! f = w\<close> \<open>foldl (mul_step w) (L, acc) fs = (L', k)\<close>
  shows \<open>lext ws L L' \<and> length (fst L') \<le> length (fst L) + length fs \<and> k < length (fst L') \<and>
    snd L' ! k = w \<and>
    (\<forall>vs. vs_ok ws vs \<longrightarrow> CV ws vs L' ! k = (CV ws vs L ! acc * pv (CV ws vs L) fs) mod 2 ^ w)\<close>
  using assms
proof (induction fs arbitrary: L acc)
  case Nil
  then have e: \<open>L' = L\<close> \<open>k = acc\<close> by simp_all
  have \<open>CV ws vs L ! acc mod 2 ^ w = CV ws vs L ! acc\<close> if \<open>vs_ok ws vs\<close> for vs
    using lok_CV_lt[OF Nil(1) that Nil(3)] Nil(4) by simp
  then show ?case using e Nil lext_refl by (simp add: pv_def)
next
  case (Cons f fs)
  let ?t = \<open>CoreTermL_Bin BinOp_Mul (cr acc) (cr f)\<close>
  obtain L1 k1 where s: \<open>mk_raw_m L ?t w = (L1, k1)\<close> by fastforce
  have f: \<open>f < length (fst L)\<close> \<open>snd L ! f = w\<close> using Cons(6) by simp_all
  have lw: \<open>length (snd L) = length (fst L)\<close> using lok_length[OF Cons(2)] .
  have b: \<open>acc < 2 ^ 64\<close> \<open>f < 2 ^ 64\<close> using Cons(3,4) f(1) by simp_all
  have wt: \<open>cwt ws (snd L) ?t\<close> \<open>cwidth ws (snd L) ?t = w\<close>
    using cr_wt cr_width b Cons(4,5) f lw by simp_all
  note R = mk_raw_ok[OF Cons(2) wt s]
  have rest: \<open>foldl (mul_step w) (L1, k1) fs = (L', k)\<close> using Cons(7) s by (simp add: mul_step_def)
  have lok1: \<open>lok ws L1\<close> using R lext_lok by blast
  have fs1: \<open>\<forall>g \<in> set fs. g < length (fst L1) \<and> snd L1 ! g = w\<close>
    using Cons(6) lext_nth_snd[OF Cons(2) conjunct1[OF R]] lext_length[OF conjunct1[OF R]] by auto
  note IH = Cons(1)[OF lok1 _ _ _ fs1 rest]
  have I: \<open>lext ws L1 L' \<and> length (fst L') \<le> length (fst L1) + length fs \<and> k < length (fst L') \<and> snd L' ! k = w \<and>
      (\<forall>vs. vs_ok ws vs \<longrightarrow> CV ws vs L' ! k = (CV ws vs L1 ! k1 * pv (CV ws vs L1) fs) mod 2 ^ w)\<close>
    using IH R Cons(3) by simp
  have V: \<open>CV ws vs L' ! k = (CV ws vs L ! acc * pv (CV ws vs L) (f # fs)) mod 2 ^ w\<close> if \<open>vs_ok ws vs\<close> for vs
  proof -
    have p: \<open>pv (CV ws vs L1) fs = pv (CV ws vs L) fs\<close>
      using pv_lext[of ws L L1 fs vs] R Cons(6) by simp
    have \<open>CV ws vs L1 ! k1 = (CV ws vs L ! acc * CV ws vs L ! f) mod 2 ^ w\<close>
      using R wt b Cons(5) by (simp add: cr_eval cr_width)
    then show ?thesis using I that p by (simp add: pv_def mod_mult_left_eq mult.assoc)
  qed
  have lx: \<open>lext ws L L'\<close> using lext_trans conjunct1[OF R] conjunct1[OF I] by blast
  have ln: \<open>length (fst L') \<le> length (fst L) + length (f # fs)\<close> using I R by simp
  show ?case using lx ln I V by simp
qed

lemma pv_sort: \<open>pv V (List.sort fs) = pv V fs\<close>
  by (simp add: pv_def flip: prod_mset_prod_list)

lemma mk_ok:
  assumes \<open>lok ws L\<close> \<open>length (fst L) + 15 < 2 ^ 64\<close> \<open>cwt ws (snd L) t\<close> \<open>cwidth ws (snd L) t = w\<close>
    \<open>mk_m L t w = (L', k)\<close>
  shows \<open>lext ws L L' \<and> length (fst L') \<le> length (fst L) + 15 \<and> k < length (fst L') \<and> snd L' ! k = w \<and>
    (\<forall>vs. vs_ok ws vs \<longrightarrow> CV ws vs L' ! k = ceval ws (snd L) vs (CV ws vs L) t)\<close>
proof -
  let ?r = \<open>rewrite_m (fst L) t w\<close>
  have RW: \<open>cwt ws (snd L) ?r\<close> \<open>cwidth ws (snd L) ?r = w\<close>
    \<open>\<forall>vs. vs_ok ws vs \<longrightarrow> ceval ws (snd L) vs (CV ws vs L) ?r = ceval ws (snd L) vs (CV ws vs L) t\<close>
    using rewrite_sem[OF assms(1,3,4)] by simp_all
  obtain fs ok where pf: \<open>product_factors_m (fst L) ?r = (fs, ok)\<close> by fastforce
  show ?thesis
  proof (cases \<open>ok \<and> 2 < length fs\<close>)
    case True
    let ?s = \<open>List.sort fs\<close>
    have mk: \<open>foldl (mul_step w) (L, hd ?s) (tl ?s) = (L', k)\<close>
      using assms(5) pf True by (simp add: mk_m_def Let_def)
    have pf': \<open>product_factors_m (fst L) ?r = (fs, True)\<close> using pf True by simp
    note P = product_ok[OF assms(1) RW(1) pf']
    have ne: \<open>?s = hd ?s # tl ?s\<close> using True by (metis List.length_sort gr_implies_not0 list.collapse list.size(3))
    have st: \<open>set ?s = set fs\<close> by simp
    have h: \<open>hd ?s \<in> set fs\<close> \<open>\<forall>f \<in> set (tl ?s). f \<in> set fs\<close>
      using ne st by (metis list.set_intros(1), metis list.set_intros(2))
    have lt: \<open>length (tl ?s) \<le> 15\<close> using conjunct1[OF P] by simp
    have hw: \<open>hd ?s < length (fst L)\<close> \<open>snd L ! hd ?s = w\<close> using P h(1) RW(2) by simp_all
    have tw: \<open>\<forall>f \<in> set (tl ?s). f < length (fst L) \<and> snd L ! f = w\<close> using P h(2) RW(2) by simp
    note F = mul_fold[OF assms(1) _ hw tw mk]
    have F': \<open>lext ws L L' \<and> length (fst L') \<le> length (fst L) + length (tl ?s) \<and> k < length (fst L') \<and>
        snd L' ! k = w \<and>
        (\<forall>vs. vs_ok ws vs \<longrightarrow> CV ws vs L' ! k = (CV ws vs L ! hd ?s * pv (CV ws vs L) (tl ?s)) mod 2 ^ w)\<close>
      using F assms(2) lt by simp
    have V: \<open>CV ws vs L' ! k = ceval ws (snd L) vs (CV ws vs L) t\<close> if vs: \<open>vs_ok ws vs\<close> for vs
    proof -
      have \<open>(CV ws vs L ! hd ?s * pv (CV ws vs L) (tl ?s)) = pv (CV ws vs L) ?s\<close>
        using ne by (metis list.simps(9) pv_def prod_list.Cons)
      then show ?thesis using F' vs pv_sort P RW by simp
    qed
    show ?thesis using F' lt V by auto
  next
    case False
    have mk: \<open>mk_raw_m L ?r w = (L', k)\<close> using assms(5) pf False by (auto simp add: mk_m_def Let_def)
    note M = mk_raw_ok[OF assms(1) RW(1,2) mk]
    show ?thesis using M RW(3) by auto
  qed
qed

subsection \<open>The loop\<close>

text \<open>The invariant of the loop after the old definitions \<open>P\<close>.\<close>
definition ninv :: \<open>nat list \<Rightarrow> CoreTermL list \<Rightarrow> lst \<Rightarrow> nat list \<Rightarrow> bool\<close> where
  \<open>ninv ws P L M \<equiv>
     lok ws L \<and> length M = length P \<and> length (fst L) \<le> 15 * length P \<and>
     menv M (snd L) (cdef_widths ws [] P) \<and>
     (\<forall>vs. vs_ok ws vs \<longrightarrow> venv M (CV ws vs L) (cdef_widths ws [] P) (cdef_values ws [] vs [] P))\<close>

lemma ninv_init: \<open>ninv ws [] ([], []) []\<close>
  by (simp add: ninv_def lok_def menv_def venv_def)

text \<open>One iteration of the loop keeps the invariant.\<close>
lemma ninv_step:
  assumes \<open>ninv ws P L M\<close> \<open>cwt ws (cdef_widths ws [] P) d\<close> \<open>length (fst L) + 15 < 2 ^ 64\<close>
    \<open>mk_m L (remap_m M d) (cwidth ws (cdef_widths ws [] P) d) = (L1, k)\<close>
  shows \<open>ninv ws (P @ [d]) L1 (M @ [k])\<close>
proof -
  let ?ds = \<open>cdef_widths ws [] P\<close>
  have I: \<open>lok ws L\<close> \<open>length M = length P\<close> \<open>length (fst L) \<le> 15 * length P\<close> \<open>menv M (snd L) ?ds\<close>
    \<open>\<forall>vs. vs_ok ws vs \<longrightarrow> venv M (CV ws vs L) ?ds (cdef_values ws [] vs [] P)\<close>
    using assms(1) by (simp_all add: ninv_def)
  have lds: \<open>length ?ds = length P\<close> by (simp add: cdef_widths_length)
  note RM = remap_wt[OF I(4) assms(2)]
  note K = mk_ok[OF I(1) assms(3) conjunct1[OF RM] conjunct2[OF RM] assms(4)]
  have lx: \<open>lext ws L L1\<close> and kl: \<open>k < length (fst L1)\<close> and kw: \<open>snd L1 ! k = cwidth ws ?ds d\<close>
    and ln: \<open>length (fst L1) \<le> length (fst L) + 15\<close>
    and kv: \<open>\<forall>vs. vs_ok ws vs \<longrightarrow> CV ws vs L1 ! k = ceval ws (snd L) vs (CV ws vs L) (remap_m M d)\<close>
    using K by simp_all
  have lok1: \<open>lok ws L1\<close> using lx lext_lok by blast
  have len0: \<open>length (snd L) = length (fst L)\<close> using lok_length[OF I(1)] .
  have len1: \<open>length (snd L1) = length (fst L1)\<close> using lok_length[OF lok1] .
  have W: \<open>cdef_widths ws [] (P @ [d]) = ?ds @ [cwidth ws ?ds d]\<close> by (simp add: cdef_widths_append)
  have V: \<open>cdef_values ws [] vs [] (P @ [d]) =
      cdef_values ws [] vs [] P @ [ceval ws ?ds vs (cdef_values ws [] vs [] P) d]\<close> for vs
    by (simp add: cdef_values_append)
  have me: \<open>menv (M @ [k]) (snd L1) (cdef_widths ws [] (P @ [d]))\<close>
    unfolding menv_def W
  proof (intro allI impI)
    fix j assume j: \<open>j < length (?ds @ [cwidth ws ?ds d])\<close>
    show \<open>(M @ [k]) ! j < length (snd L1) \<and> (M @ [k]) ! j < 2 ^ 64 \<and>
        snd L1 ! ((M @ [k]) ! j) = (?ds @ [cwidth ws ?ds d]) ! j\<close>
    proof (cases \<open>j < length P\<close>)
      case True
      have m: \<open>M ! j < length (fst L)\<close> \<open>M ! j < 2 ^ 64\<close> \<open>snd L ! (M ! j) = ?ds ! j\<close>
        using I(4) True lds len0 by (simp_all add: menv_def)
      show ?thesis using m True I(2) lds lext_nth_snd[OF I(1) lx m(1)] lext_length[OF lx] len1
        by (simp add: nth_append)
    next
      case False
      then have jP: \<open>j = length P\<close> using j lds by simp
      show ?thesis using kl kw ln assms(3) len1 I(2) lds jP by (simp add: nth_append)
    qed
  qed
  have ve: \<open>venv (M @ [k]) (CV ws vs L1) (cdef_widths ws [] (P @ [d])) (cdef_values ws [] vs [] (P @ [d]))\<close>
    if vs: \<open>vs_ok ws vs\<close> for vs
    unfolding venv_def W V
  proof (intro allI impI)
    fix j assume j: \<open>j < length (?ds @ [cwidth ws ?ds d])\<close>
    show \<open>CV ws vs L1 ! ((M @ [k]) ! j) =
        (cdef_values ws [] vs [] P @ [ceval ws ?ds vs (cdef_values ws [] vs [] P) d]) ! j\<close>
    proof (cases \<open>j < length P\<close>)
      case True
      have m: \<open>M ! j < length (fst L)\<close> using I(4) True lds len0 by (simp add: menv_def)
      show ?thesis using lext_nth_CV[OF lx m] I(5) vs True I(2) lds
        by (simp add: nth_append venv_def cdef_values_length)
    next
      case False
      then have jP: \<open>j = length P\<close> using j lds by simp
      have \<open>ceval ws (snd L) vs (CV ws vs L) (remap_m M d) = ceval ws ?ds vs (cdef_values ws [] vs [] P) d\<close>
        using remap_eval[OF I(4) _ assms(2)] I(5) vs by blast
      then show ?thesis using kv vs jP I(2) by (simp add: nth_append cdef_values_length)
    qed
  qed
  show ?thesis unfolding ninv_def using lok1 I(2,3) ln me ve by simp
qed

lemma norm_loop_ok:
  assumes \<open>cdefs_wt ws [] (P @ R)\<close> \<open>ninv ws P L M\<close> \<open>15 * length (P @ R) < 2 ^ 64\<close>
    \<open>norm_loop (cdef_widths ws [] (P @ R)) R (L, M) = (L', M')\<close>
  shows \<open>ninv ws (P @ R) L' M'\<close>
  using assms
proof (induction R arbitrary: P L M)
  case Nil
  then show ?case by simp
next
  case (Cons d R)
  let ?ds = \<open>cdef_widths ws [] P\<close>
  have wtd: \<open>cwt ws ?ds d\<close> using Cons(2) by (simp add: cdefs_wt_append)
  have dwn: \<open>cdef_widths ws [] (P @ d # R) ! length M = cwidth ws ?ds d\<close>
  proof -
    have \<open>cdef_widths ws [] (P @ d # R) = cdef_widths ws (?ds @ [cwidth ws ?ds d]) R\<close>
      by (simp add: cdef_widths_append)
    moreover obtain e where \<open>cdef_widths ws (?ds @ [cwidth ws ?ds d]) R = (?ds @ [cwidth ws ?ds d]) @ e\<close>
      using cdef_widths_prefix by blast
    moreover have \<open>length M = length ?ds\<close> using Cons(3) by (simp add: ninv_def cdef_widths_length)
    ultimately show ?thesis by (simp add: nth_append)
  qed
  have bnd: \<open>length (fst L) + 15 < 2 ^ 64\<close> using Cons(3,4) by (simp add: ninv_def)
  obtain L1 k where mk: \<open>mk_m L (remap_m M d) (cwidth ws ?ds d) = (L1, k)\<close> by fastforce
  have N1: \<open>ninv ws (P @ [d]) L1 (M @ [k])\<close> using ninv_step[OF Cons(3) wtd bnd mk] .
  have rest: \<open>norm_loop (cdef_widths ws [] ((P @ [d]) @ R)) R (L1, M @ [k]) = (L', M')\<close>
    using Cons(5) mk dwn by simp
  show ?case using Cons.IH[of \<open>P @ [d]\<close> L1 \<open>M @ [k]\<close>] Cons(2,4) N1 rest by simp
qed

subsection \<open>The theorem\<close>

theorem normalize_correct:
  assumes \<open>cproblem_wt q\<close> \<open>15 * length (CoreProblemL_defs q) < 2 ^ 64\<close>
  shows \<open>CoreProblemL_widths (normalize_m q) = CoreProblemL_widths q\<close> \<open>cproblem_wt (normalize_m q)\<close>
    \<open>cis_model (normalize_m q) m \<longleftrightarrow> cis_model q m\<close>
proof -
  let ?ws = \<open>cvar_widths q\<close> and ?D = \<open>CoreProblemL_defs q\<close> and ?A = \<open>CoreProblemL_asserts q\<close>
  let ?dw = \<open>cdef_widths ?ws [] ?D\<close>
  obtain L M where nl: \<open>norm_loop ?dw ?D (([], []), []) = (L, M)\<close> by fastforce
  have nq: \<open>normalize_m q = make_CoreProblemL (CoreProblemL_widths q) (fst L) (map (remap_m M) ?A)\<close>
    using nl by (simp add: normalize_m_def)
  have wtD: \<open>cdefs_wt ?ws [] ?D\<close> and wtA: \<open>\<forall>t \<in> set ?A. cwt ?ws ?dw t \<and> cwidth ?ws ?dw t = 1\<close>
    using assms(1) by (simp_all add: cproblem_wt_def Let_def)
  have N: \<open>ninv ?ws ?D L M\<close>
    using norm_loop_ok[of ?ws \<open>[]\<close> ?D \<open>([], [])\<close> \<open>[]\<close> L M] wtD assms(2) ninv_init nl by simp
  have lok: \<open>lok ?ws L\<close> and me: \<open>menv M (snd L) ?dw\<close>
    and ve: \<open>\<forall>vs. vs_ok ?ws vs \<longrightarrow> venv M (CV ?ws vs L) ?dw (cdef_values ?ws [] vs [] ?D)\<close>
    using N by (simp_all add: ninv_def)
  have sL: \<open>cdef_widths ?ws [] (fst L) = snd L\<close> using lok by (simp add: lok_def)
  have cw: \<open>cvar_widths (normalize_m q) = ?ws\<close> by (simp add: nq cvar_widths_def)
  show \<open>CoreProblemL_widths (normalize_m q) = CoreProblemL_widths q\<close> by (simp add: nq)
  have At: \<open>\<forall>t \<in> set ?A. cwt ?ws (snd L) (remap_m M t) \<and> cwidth ?ws (snd L) (remap_m M t) = 1\<close>
    using remap_wt[OF me] wtA by auto
  show \<open>cproblem_wt (normalize_m q)\<close>
    using cw lok At sL by (simp add: cproblem_wt_def nq lok_def Let_def)
  have ca: \<open>cis_assignment (normalize_m q) m = cis_assignment q m\<close>
    by (simp add: cis_assignment_def cw)
  have cs: \<open>csatisfies (normalize_m q) m = csatisfies q m\<close> if a: \<open>cis_assignment q m\<close>
  proof -
    let ?vs = \<open>map bits_nat m\<close>
    have vs: \<open>vs_ok ?ws ?vs\<close>
    proof -
      have l: \<open>map length m = ?ws\<close> using a by (simp add: cis_assignment_def)
      then have \<open>length ?vs = length ?ws\<close> by (metis length_map)
      moreover have \<open>\<forall>i < length ?ws. ?vs ! i < 2 ^ (?ws ! i)\<close>
        using l bits_nat_lt by (metis length_map nth_map)
      ultimately show ?thesis by (simp add: vs_ok_def)
    qed
    have \<open>ceval ?ws (snd L) ?vs (CV ?ws ?vs L) (remap_m M t) = ceval ?ws ?dw ?vs (cdef_values ?ws [] ?vs [] ?D) t\<close>
      if \<open>t \<in> set ?A\<close> for t
      using remap_eval[OF me _ conjunct1[OF bspec[OF wtA that]]] ve vs by blast
    then show ?thesis using cw sL by (simp add: csatisfies_def nq Let_def)
  qed
  show \<open>cis_model (normalize_m q) m \<longleftrightarrow> cis_model q m\<close>
    using ca cs by (auto simp add: cis_model_def)
qed


text \<open>The number of definitions grows at most 15-fold: a flattened product adds at most 15.\<close>
lemma normalize_defs_length:
  assumes \<open>cproblem_wt q\<close> \<open>15 * length (CoreProblemL_defs q) < 2 ^ 64\<close>
  shows \<open>length (CoreProblemL_defs (normalize_m q)) \<le> 15 * length (CoreProblemL_defs q)\<close>
proof -
  let ?ws = \<open>cvar_widths q\<close> and ?D = \<open>CoreProblemL_defs q\<close>
  obtain L M where nl: \<open>norm_loop (cdef_widths ?ws [] ?D) ?D (([], []), []) = (L, M)\<close> by fastforce
  have wtD: \<open>cdefs_wt ?ws [] ?D\<close> using assms(1) by (simp add: cproblem_wt_def Let_def)
  have \<open>ninv ?ws ?D L M\<close>
    using norm_loop_ok[of ?ws \<open>[]\<close> ?D \<open>([], [])\<close> \<open>[]\<close> L M] wtD assms(2) ninv_init nl by simp
  then show ?thesis using nl by (simp add: normalize_m_def ninv_def)
qed

end
