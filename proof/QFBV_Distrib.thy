theory QFBV_Distrib
  imports QFBV_Norm
begin

section \<open>Distributivity of a product over a sum in the normalization\<close>

text \<open>
  A functional model \<open>distribute_m\<close> of the Rust function \<^verbatim>\<open>distribute\<close>, which \<^verbatim>\<open>mk\<close> applies to the
  rewritten term: a product \<open>a * (x + y)\<close> of two definitions, where the definition \<open>x + y\<close> is the
  sum of two definitions, becomes \<open>a * x + a * y\<close>, and \<open>(x + y) * b\<close> becomes \<open>x * b + y * b\<close>, but
  only if both products are earlier definitions of the width. The right operand is tried first.
  The rewrite keeps the well-sortedness, the width and the value of the term, and its result is
  the term itself or a sum of two references, so it adds no product. \<open>mk_d_m\<close> and \<open>normalize_d_m\<close>
  are \<open>mk_m\<close> and \<open>normalize_m\<close> with the rewrite, and \<open>normalize_d_correct\<close> is \<open>normalize_correct\<close>
  for them.

  \<open>lookup_m\<close> does not model the hash buckets, for the reason given in the header of
  \<^verbatim>\<open>QFBV_Norm\<close>: it is \<open>find_def_m\<close>.
\<close>

subsection \<open>Models of the functions\<close>

text \<open>\<^verbatim>\<open>lookup\<close>.\<close>
definition lookup_m :: \<open>lst \<Rightarrow> CoreTermL \<Rightarrow> nat \<Rightarrow> nat option\<close> where
  \<open>lookup_m L t w \<equiv> find_def_m L t w\<close>

text \<open>\<^verbatim>\<open>sum_of\<close> (\<^verbatim>\<open>op_code 3\<close> is \<^const>\<open>BinOp_Add\<close>), with \<^const>\<open>None\<close> for \<^verbatim>\<open>usize::MAX\<close>.\<close>
definition sum_of_m :: \<open>CoreTermL list \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) option\<close> where
  \<open>sum_of_m D k \<equiv>
     (case D ! k of
        CoreTermL_Bin op a b \<Rightarrow>
          (if op = BinOp_Add then
             (case ref_of a of Some x \<Rightarrow> (case ref_of b of Some y \<Rightarrow> Some (x, y) | None \<Rightarrow> None) | None \<Rightarrow> None)
           else None)
      | _ \<Rightarrow> None)\<close>

text \<open>The sum \<open>p + q\<close> of the earlier definitions \<open>p\<close>, \<open>q\<close> of width \<open>w\<close> equal to \<open>s\<close> and \<open>u\<close>, if both
  exist.\<close>
definition sum_lookup :: \<open>lst \<Rightarrow> CoreTermL \<Rightarrow> CoreTermL \<Rightarrow> nat \<Rightarrow> CoreTermL option\<close> where
  \<open>sum_lookup L s u w \<equiv>
     (case lookup_m L s w of
        Some p \<Rightarrow> (case lookup_m L u w of Some q \<Rightarrow> Some (CoreTermL_Bin BinOp_Add (cr p) (cr q)) | None \<Rightarrow> None)
      | None \<Rightarrow> None)\<close>

abbreviation mul_t :: \<open>nat \<Rightarrow> nat \<Rightarrow> CoreTermL\<close> where
  \<open>mul_t i j \<equiv> CoreTermL_Bin BinOp_Mul (cr i) (cr j)\<close>

text \<open>\<^verbatim>\<open>distribute\<close> (\<^verbatim>\<open>op_code 4\<close> is \<^const>\<open>BinOp_Mul\<close>).\<close>
definition distribute_m :: \<open>lst \<Rightarrow> CoreTermL \<Rightarrow> nat \<Rightarrow> CoreTermL\<close> where
  \<open>distribute_m L t w \<equiv>
     (case mul_refs t of
        None \<Rightarrow> t
      | Some (ka, kb) \<Rightarrow>
          (let r1 = (case sum_of_m (fst L) kb of
                       Some (x, y) \<Rightarrow> sum_lookup L (mul_t ka x) (mul_t ka y) w
                     | None \<Rightarrow> None) in
           case r1 of
             Some r \<Rightarrow> r
           | None \<Rightarrow>
               (let r2 = (case sum_of_m (fst L) ka of
                            Some (x, y) \<Rightarrow> sum_lookup L (mul_t x kb) (mul_t y kb) w
                          | None \<Rightarrow> None) in
                case r2 of Some r \<Rightarrow> r | None \<Rightarrow> t)))\<close>

text \<open>\<^verbatim>\<open>mk\<close> with \<^verbatim>\<open>distribute\<close>.\<close>
definition mk_d_m :: \<open>lst \<Rightarrow> CoreTermL \<Rightarrow> nat \<Rightarrow> lst \<times> nat\<close> where
  \<open>mk_d_m L t w \<equiv>
     (let r = distribute_m L (rewrite_m (fst L) t w) w in
      let (fs, ok) = product_factors_m (fst L) r in
      if ok \<and> 2 < length fs then (let fs = List.sort fs in foldl (mul_step w) (L, hd fs) (tl fs))
      else mk_raw_m L r w)\<close>

subsection \<open>The rewrite\<close>

lemma distribute_shape:
  \<open>distribute_m L t w = t \<or> (\<exists>p q. distribute_m L t w = CoreTermL_Bin BinOp_Add (cr p) (cr q))\<close>
  by (auto simp add: distribute_m_def sum_lookup_def Let_def split: option.splits prod.splits)

text \<open>So the result is a product of two references only if it is the term itself.\<close>
lemma distribute_mul_refs: \<open>mul_refs (distribute_m L t w) \<noteq> None \<Longrightarrow> distribute_m L t w = t\<close>
  using distribute_shape[of L t w] by (auto simp add: mul_refs_def)

lemma sum_of_sem:
  assumes \<open>lok ws L\<close> \<open>k < length (fst L)\<close> \<open>sum_of_m (fst L) k = Some (x, y)\<close>
  shows \<open>x < length (fst L) \<and> y < length (fst L) \<and> snd L ! x = snd L ! k \<and> snd L ! y = snd L ! k \<and>
    (\<forall>vs. CV ws vs L ! k = (CV ws vs L ! x + CV ws vs L ! y) mod 2 ^ (snd L ! k))\<close>
proof -
  obtain i j where d: \<open>fst L ! k = CoreTermL_Bin BinOp_Add (CoreTermL_Ref i) (CoreTermL_Ref j)\<close>
    \<open>x = unat i\<close> \<open>y = unat j\<close>
    using assms(3) by (auto simp add: sum_of_m_def ref_of_def split: CoreTermL.splits if_splits)
  note N = lok_nth[OF assms(1,2)]
  show ?thesis using N d lok_length[OF assms(1)] by simp
qed

lemma lookup_sem:
  assumes \<open>lok ws L\<close> \<open>lookup_m L t w = Some p\<close> \<open>cwt ws (snd L) t\<close>
  shows \<open>p < length (fst L) \<and> snd L ! p = w \<and> (\<forall>vs. CV ws vs L ! p = ceval ws (snd L) vs (CV ws vs L) t)\<close>
proof -
  have f: \<open>p < length (fst L)\<close> \<open>snd L ! p = w\<close> \<open>norm_eq_m (fst L ! p) t\<close>
    using assms(2) by (auto simp add: lookup_m_def find_def_m_def find_Some_iff)
  note N = lok_nth[OF assms(1) f(1)]
  show ?thesis using f N(3) norm_eq_sem[OF f(3) N(1)] by simp
qed

lemma mod_distrib: \<open>((a :: nat) * ((x + y) mod m)) mod m = ((a * x) mod m + (a * y) mod m) mod m\<close>
  by (simp add: mod_mult_right_eq mod_add_eq distrib_left)

lemma mod_distrib': \<open>(((x + y) mod m) * (b :: nat)) mod m = ((x * b) mod m + (y * b) mod m) mod m\<close>
  by (simp add: mod_mult_left_eq mod_add_eq distrib_right)

text \<open>A sum found by \<open>sum_lookup\<close> of two products of width \<open>w\<close>.\<close>
lemma sum_lookup_sem:
  assumes \<open>lok ws L\<close> \<open>length (fst L) \<le> 2 ^ 64\<close> \<open>sum_lookup L (mul_t i x) (mul_t j y) w = Some r\<close>
    \<open>i < length (fst L)\<close> \<open>x < length (fst L)\<close> \<open>j < length (fst L)\<close> \<open>y < length (fst L)\<close>
    \<open>snd L ! i = w\<close> \<open>snd L ! x = w\<close> \<open>snd L ! j = w\<close> \<open>snd L ! y = w\<close>
  shows \<open>cwt ws (snd L) r \<and> cwidth ws (snd L) r = w \<and>
    (\<forall>vs. ceval ws (snd L) vs (CV ws vs L) r =
       ((CV ws vs L ! i * CV ws vs L ! x) mod 2 ^ w + (CV ws vs L ! j * CV ws vs L ! y) mod 2 ^ w) mod 2 ^ w)\<close>
proof -
  let ?W = \<open>snd L\<close>
  have lw: \<open>length ?W = length (fst L)\<close> using lok_length[OF assms(1)] .
  obtain p q where pq: \<open>lookup_m L (mul_t i x) w = Some p\<close> \<open>lookup_m L (mul_t j y) w = Some q\<close>
    \<open>r = CoreTermL_Bin BinOp_Add (cr p) (cr q)\<close>
    using assms(3) by (auto simp add: sum_lookup_def split: option.splits)
  have b: \<open>i < 2 ^ 64\<close> \<open>x < 2 ^ 64\<close> \<open>j < 2 ^ 64\<close> \<open>y < 2 ^ 64\<close> using assms(2,4-7) by simp_all
  have wt: \<open>cwt ws ?W (mul_t i x)\<close> \<open>cwt ws ?W (mul_t j y)\<close>
    using cr_wt cr_width b assms(4-11) lw by simp_all
  note P = lookup_sem[OF assms(1) pq(1) wt(1)] and Q = lookup_sem[OF assms(1) pq(2) wt(2)]
  have b2: \<open>p < 2 ^ 64\<close> \<open>q < 2 ^ 64\<close> using P Q assms(2) by simp_all
  show ?thesis using pq(3) P Q b b2 lw assms(8-11) by (simp add: cr_wt cr_width cr_eval)
qed

lemma distribute_sem:
  assumes \<open>lok ws L\<close> \<open>length (fst L) \<le> 2 ^ 64\<close> \<open>cwt ws (snd L) t\<close> \<open>cwidth ws (snd L) t = w\<close>
  shows \<open>cwt ws (snd L) (distribute_m L t w) \<and> cwidth ws (snd L) (distribute_m L t w) = w \<and>
    (\<forall>vs. ceval ws (snd L) vs (CV ws vs L) (distribute_m L t w) = ceval ws (snd L) vs (CV ws vs L) t)\<close>
proof (cases \<open>mul_refs t\<close>)
  case None
  then show ?thesis using assms(3,4) by (simp add: distribute_m_def)
next
  case (Some m)
  let ?W = \<open>snd L\<close> and ?D = \<open>fst L\<close>
  obtain ka kb where m: \<open>m = (ka, kb)\<close> by fastforce
  obtain i j where t: \<open>t = CoreTermL_Bin BinOp_Mul (CoreTermL_Ref i) (CoreTermL_Ref j)\<close>
    \<open>ka = unat i\<close> \<open>kb = unat j\<close>
    using Some m by (auto simp add: mul_refs_Some)
  have lw: \<open>length ?W = length ?D\<close> using lok_length[OF assms(1)] .
  have k: \<open>ka < length ?D\<close> \<open>kb < length ?D\<close> \<open>?W ! ka = w\<close> \<open>?W ! kb = w\<close>
    using assms(3,4) t lw by simp_all
  have tv: \<open>ceval ws ?W vs (CV ws vs L) t = (CV ws vs L ! ka * CV ws vs L ! kb) mod 2 ^ w\<close> for vs
    using t k by simp
  define r1 where \<open>r1 = (case sum_of_m ?D kb of
      Some (x, y) \<Rightarrow> sum_lookup L (mul_t ka x) (mul_t ka y) w | None \<Rightarrow> None)\<close>
  define r2 where \<open>r2 = (case sum_of_m ?D ka of
      Some (x, y) \<Rightarrow> sum_lookup L (mul_t x kb) (mul_t y kb) w | None \<Rightarrow> None)\<close>
  have d: \<open>distribute_m L t w = (case r1 of Some r \<Rightarrow> r | None \<Rightarrow> (case r2 of Some r \<Rightarrow> r | None \<Rightarrow> t))\<close>
    using Some m unfolding distribute_m_def r1_def r2_def by simp
  let ?ok = \<open>\<lambda>r. cwt ws ?W r \<and> cwidth ws ?W r = w \<and>
    (\<forall>vs. ceval ws ?W vs (CV ws vs L) r = ceval ws ?W vs (CV ws vs L) t)\<close>
  have R1: \<open>?ok r\<close> if h: \<open>r1 = Some r\<close> for r
  proof -
    obtain x y where s: \<open>sum_of_m ?D kb = Some (x, y)\<close>
      and sl: \<open>sum_lookup L (mul_t ka x) (mul_t ka y) w = Some r\<close>
      using h by (cases \<open>sum_of_m ?D kb\<close>) (auto simp add: r1_def)
    note S = sum_of_sem[OF assms(1) k(2) s]
    note SL = sum_lookup_sem[OF assms(1,2) sl k(1) _ k(1) _ k(3) _ k(3)]
    have SL': \<open>cwt ws ?W r \<and> cwidth ws ?W r = w \<and>
      (\<forall>vs. ceval ws ?W vs (CV ws vs L) r =
         ((CV ws vs L ! ka * CV ws vs L ! x) mod 2 ^ w + (CV ws vs L ! ka * CV ws vs L ! y) mod 2 ^ w) mod 2 ^ w)\<close>
      using SL S k by simp
    show ?thesis using SL' S k tv by (simp add: mod_distrib)
  qed
  have R2: \<open>?ok r\<close> if h: \<open>r2 = Some r\<close> for r
  proof -
    obtain x y where s: \<open>sum_of_m ?D ka = Some (x, y)\<close>
      and sl: \<open>sum_lookup L (mul_t x kb) (mul_t y kb) w = Some r\<close>
      using h by (cases \<open>sum_of_m ?D ka\<close>) (auto simp add: r2_def)
    note S = sum_of_sem[OF assms(1) k(1) s]
    note SL = sum_lookup_sem[OF assms(1,2) sl _ k(2) _ k(2) _ k(4) _ k(4)]
    have SL': \<open>cwt ws ?W r \<and> cwidth ws ?W r = w \<and>
      (\<forall>vs. ceval ws ?W vs (CV ws vs L) r =
         ((CV ws vs L ! x * CV ws vs L ! kb) mod 2 ^ w + (CV ws vs L ! y * CV ws vs L ! kb) mod 2 ^ w) mod 2 ^ w)\<close>
      using SL S k by simp
    show ?thesis using SL' S k tv by (simp add: mod_distrib')
  qed
  show ?thesis using d R1 R2 assms(3,4) by (auto split: option.splits)
qed

text \<open>The term that \<^verbatim>\<open>mk\<close> passes on.\<close>
lemma distribute_rewrite_sem:
  assumes \<open>lok ws L\<close> \<open>length (fst L) \<le> 2 ^ 64\<close> \<open>cwt ws (snd L) t\<close> \<open>cwidth ws (snd L) t = w\<close>
  shows \<open>cwt ws (snd L) (distribute_m L (rewrite_m (fst L) t w) w) \<and>
    cwidth ws (snd L) (distribute_m L (rewrite_m (fst L) t w) w) = w \<and>
    (\<forall>vs. vs_ok ws vs \<longrightarrow>
       ceval ws (snd L) vs (CV ws vs L) (distribute_m L (rewrite_m (fst L) t w) w) =
       ceval ws (snd L) vs (CV ws vs L) t)\<close>
  using rewrite_sem[OF assms(1,3,4)] distribute_sem[OF assms(1,2)] by simp

subsection \<open>Sharing\<close>

text \<open>The part of \<^verbatim>\<open>mk\<close> after the rewrites, for any rewritten term \<open>r\<close>: the proof of \<open>mk_ok\<close>.\<close>
lemma mk_tail_ok:
  assumes \<open>lok ws L\<close> \<open>length (fst L) + 15 < 2 ^ 64\<close> \<open>cwt ws (snd L) r\<close> \<open>cwidth ws (snd L) r = w\<close>
    \<open>(let (fs, ok) = product_factors_m (fst L) r in
      if ok \<and> 2 < length fs then (let fs = List.sort fs in foldl (mul_step w) (L, hd fs) (tl fs))
      else mk_raw_m L r w) = (L', k)\<close>
  shows \<open>lext ws L L' \<and> length (fst L') \<le> length (fst L) + 15 \<and> k < length (fst L') \<and> snd L' ! k = w \<and>
    (\<forall>vs. vs_ok ws vs \<longrightarrow> CV ws vs L' ! k = ceval ws (snd L) vs (CV ws vs L) r)\<close>
proof -
  obtain fs ok where pf: \<open>product_factors_m (fst L) r = (fs, ok)\<close> by fastforce
  show ?thesis
  proof (cases \<open>ok \<and> 2 < length fs\<close>)
    case True
    let ?s = \<open>List.sort fs\<close>
    have mk: \<open>foldl (mul_step w) (L, hd ?s) (tl ?s) = (L', k)\<close>
      using assms(5) pf True by (simp add: Let_def)
    have pf': \<open>product_factors_m (fst L) r = (fs, True)\<close> using pf True by simp
    note P = product_ok[OF assms(1,3) pf']
    have ne: \<open>?s = hd ?s # tl ?s\<close> using True by (metis List.length_sort gr_implies_not0 list.collapse list.size(3))
    have st: \<open>set ?s = set fs\<close> by simp
    have h: \<open>hd ?s \<in> set fs\<close> \<open>\<forall>f \<in> set (tl ?s). f \<in> set fs\<close>
      using ne st by (metis list.set_intros(1), metis list.set_intros(2))
    have lt: \<open>length (tl ?s) \<le> 15\<close> using conjunct1[OF P] by simp
    have hw: \<open>hd ?s < length (fst L)\<close> \<open>snd L ! hd ?s = w\<close> using P h(1) assms(4) by simp_all
    have tw: \<open>\<forall>f \<in> set (tl ?s). f < length (fst L) \<and> snd L ! f = w\<close> using P h(2) assms(4) by simp
    note F = mul_fold[OF assms(1) _ hw tw mk]
    have F': \<open>lext ws L L' \<and> length (fst L') \<le> length (fst L) + length (tl ?s) \<and> k < length (fst L') \<and>
        snd L' ! k = w \<and>
        (\<forall>vs. vs_ok ws vs \<longrightarrow> CV ws vs L' ! k = (CV ws vs L ! hd ?s * pv (CV ws vs L) (tl ?s)) mod 2 ^ w)\<close>
      using F assms(2) lt by simp
    have V: \<open>CV ws vs L' ! k = ceval ws (snd L) vs (CV ws vs L) r\<close> if vs: \<open>vs_ok ws vs\<close> for vs
    proof -
      have \<open>(CV ws vs L ! hd ?s * pv (CV ws vs L) (tl ?s)) = pv (CV ws vs L) ?s\<close>
        using ne by (metis list.simps(9) pv_def prod_list.Cons)
      then show ?thesis using F' vs pv_sort P assms(4) by simp
    qed
    show ?thesis using F' lt V by auto
  next
    case False
    have mk: \<open>mk_raw_m L r w = (L', k)\<close> using assms(5) pf False by (auto simp add: Let_def)
    show ?thesis using mk_raw_ok[OF assms(1,3,4) mk] by auto
  qed
qed

lemma mk_d_ok:
  assumes \<open>lok ws L\<close> \<open>length (fst L) + 15 < 2 ^ 64\<close> \<open>cwt ws (snd L) t\<close> \<open>cwidth ws (snd L) t = w\<close>
    \<open>mk_d_m L t w = (L', k)\<close>
  shows \<open>lext ws L L' \<and> length (fst L') \<le> length (fst L) + 15 \<and> k < length (fst L') \<and> snd L' ! k = w \<and>
    (\<forall>vs. vs_ok ws vs \<longrightarrow> CV ws vs L' ! k = ceval ws (snd L) vs (CV ws vs L) t)\<close>
proof -
  let ?r = \<open>distribute_m L (rewrite_m (fst L) t w) w\<close>
  have b: \<open>length (fst L) \<le> 2 ^ 64\<close> using assms(2) by simp
  note RW = distribute_rewrite_sem[OF assms(1) b assms(3,4)]
  have m: \<open>(let (fs, ok) = product_factors_m (fst L) ?r in
      if ok \<and> 2 < length fs then (let fs = List.sort fs in foldl (mul_step w) (L, hd fs) (tl fs))
      else mk_raw_m L ?r w) = (L', k)\<close>
    using assms(5) by (simp add: mk_d_m_def Let_def)
  show ?thesis using mk_tail_ok[OF assms(1,2) conjunct1[OF RW] conjunct1[OF conjunct2[OF RW]] m] RW by auto
qed

subsection \<open>The normalization with \<^verbatim>\<open>distribute\<close>\<close>

text \<open>The loop of \<^verbatim>\<open>normalize\<close>, as \<open>norm_loop\<close>.\<close>
primrec norm_loop_d :: \<open>nat list \<Rightarrow> CoreTermL list \<Rightarrow> lst \<times> nat list \<Rightarrow> lst \<times> nat list\<close> where
  \<open>norm_loop_d dw [] S = S\<close>
| \<open>norm_loop_d dw (d # dd) S =
     (let (L, M) = S in
      let (L1, k) = mk_d_m L (remap_m M d) (dw ! length M) in
      norm_loop_d dw dd (L1, M @ [k]))\<close>

text \<open>\<^verbatim>\<open>normalize\<close> with \<^verbatim>\<open>distribute\<close> in \<^verbatim>\<open>mk\<close>, without the substitution.\<close>
definition normalize_d_m :: \<open>CoreProblemL \<Rightarrow> CoreProblemL\<close> where
  \<open>normalize_d_m q \<equiv>
     (let ws = cvar_widths q in
      let dw = cdef_widths ws [] (CoreProblemL_defs q) in
      let (L, M) = norm_loop_d dw (CoreProblemL_defs q) (([], []), []) in
      make_CoreProblemL (CoreProblemL_widths q) (fst L) (map (remap_m M) (CoreProblemL_asserts q)))\<close>

text \<open>One iteration of the loop keeps the invariant. This and the next proofs are those of
  \<^verbatim>\<open>QFBV_Norm\<close>, with \<open>mk_d_ok\<close> for \<open>mk_ok\<close>.\<close>
lemma ninv_d_step:
  assumes \<open>ninv ws P L M\<close> \<open>cwt ws (cdef_widths ws [] P) d\<close> \<open>length (fst L) + 15 < 2 ^ 64\<close>
    \<open>mk_d_m L (remap_m M d) (cwidth ws (cdef_widths ws [] P) d) = (L1, k)\<close>
  shows \<open>ninv ws (P @ [d]) L1 (M @ [k])\<close>
proof -
  let ?ds = \<open>cdef_widths ws [] P\<close>
  have I: \<open>lok ws L\<close> \<open>length M = length P\<close> \<open>length (fst L) \<le> 15 * length P\<close> \<open>menv M (snd L) ?ds\<close>
    \<open>\<forall>vs. vs_ok ws vs \<longrightarrow> venv M (CV ws vs L) ?ds (cdef_values ws [] vs [] P)\<close>
    using assms(1) by (simp_all add: ninv_def)
  have lds: \<open>length ?ds = length P\<close> by (simp add: cdef_widths_length)
  note RM = remap_wt[OF I(4) assms(2)]
  note K = mk_d_ok[OF I(1) assms(3) conjunct1[OF RM] conjunct2[OF RM] assms(4)]
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

lemma norm_loop_d_d_ok:
  assumes \<open>cdefs_wt ws [] (P @ R)\<close> \<open>ninv ws P L M\<close> \<open>15 * length (P @ R) < 2 ^ 64\<close>
    \<open>norm_loop_d (cdef_widths ws [] (P @ R)) R (L, M) = (L', M')\<close>
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
  obtain L1 k where mk: \<open>mk_d_m L (remap_m M d) (cwidth ws ?ds d) = (L1, k)\<close> by fastforce
  have N1: \<open>ninv ws (P @ [d]) L1 (M @ [k])\<close> using ninv_d_step[OF Cons(3) wtd bnd mk] .
  have rest: \<open>norm_loop_d (cdef_widths ws [] ((P @ [d]) @ R)) R (L1, M @ [k]) = (L', M')\<close>
    using Cons(5) mk dwn by simp
  show ?case using Cons.IH[of \<open>P @ [d]\<close> L1 \<open>M @ [k]\<close>] Cons(2,4) N1 rest by simp
qed

subsection \<open>The theorem\<close>

theorem normalize_d_correct:
  assumes \<open>cproblem_wt q\<close> \<open>15 * length (CoreProblemL_defs q) < 2 ^ 64\<close>
  shows \<open>CoreProblemL_widths (normalize_d_m q) = CoreProblemL_widths q\<close> \<open>cproblem_wt (normalize_d_m q)\<close>
    \<open>cis_model (normalize_d_m q) m \<longleftrightarrow> cis_model q m\<close>
proof -
  let ?ws = \<open>cvar_widths q\<close> and ?D = \<open>CoreProblemL_defs q\<close> and ?A = \<open>CoreProblemL_asserts q\<close>
  let ?dw = \<open>cdef_widths ?ws [] ?D\<close>
  obtain L M where nl: \<open>norm_loop_d ?dw ?D (([], []), []) = (L, M)\<close> by fastforce
  have nq: \<open>normalize_d_m q = make_CoreProblemL (CoreProblemL_widths q) (fst L) (map (remap_m M) ?A)\<close>
    using nl by (simp add: normalize_d_m_def)
  have wtD: \<open>cdefs_wt ?ws [] ?D\<close> and wtA: \<open>\<forall>t \<in> set ?A. cwt ?ws ?dw t \<and> cwidth ?ws ?dw t = 1\<close>
    using assms(1) by (simp_all add: cproblem_wt_def Let_def)
  have N: \<open>ninv ?ws ?D L M\<close>
    using norm_loop_d_d_ok[of ?ws \<open>[]\<close> ?D \<open>([], [])\<close> \<open>[]\<close> L M] wtD assms(2) ninv_init nl by simp
  have lok: \<open>lok ?ws L\<close> and me: \<open>menv M (snd L) ?dw\<close>
    and ve: \<open>\<forall>vs. vs_ok ?ws vs \<longrightarrow> venv M (CV ?ws vs L) ?dw (cdef_values ?ws [] vs [] ?D)\<close>
    using N by (simp_all add: ninv_def)
  have sL: \<open>cdef_widths ?ws [] (fst L) = snd L\<close> using lok by (simp add: lok_def)
  have cw: \<open>cvar_widths (normalize_d_m q) = ?ws\<close> by (simp add: nq cvar_widths_def)
  show \<open>CoreProblemL_widths (normalize_d_m q) = CoreProblemL_widths q\<close> by (simp add: nq)
  have At: \<open>\<forall>t \<in> set ?A. cwt ?ws (snd L) (remap_m M t) \<and> cwidth ?ws (snd L) (remap_m M t) = 1\<close>
    using remap_wt[OF me] wtA by auto
  show \<open>cproblem_wt (normalize_d_m q)\<close>
    using cw lok At sL by (simp add: cproblem_wt_def nq lok_def Let_def)
  have ca: \<open>cis_assignment (normalize_d_m q) m = cis_assignment q m\<close>
    by (simp add: cis_assignment_def cw)
  have cs: \<open>csatisfies (normalize_d_m q) m = csatisfies q m\<close> if a: \<open>cis_assignment q m\<close>
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
  show \<open>cis_model (normalize_d_m q) m \<longleftrightarrow> cis_model q m\<close>
    using ca cs by (auto simp add: cis_model_def)
qed


text \<open>The number of definitions grows at most 15-fold: a flattened product adds at most 15.\<close>
lemma normalize_d_defs_length:
  assumes \<open>cproblem_wt q\<close> \<open>15 * length (CoreProblemL_defs q) < 2 ^ 64\<close>
  shows \<open>length (CoreProblemL_defs (normalize_d_m q)) \<le> 15 * length (CoreProblemL_defs q)\<close>
proof -
  let ?ws = \<open>cvar_widths q\<close> and ?D = \<open>CoreProblemL_defs q\<close>
  obtain L M where nl: \<open>norm_loop_d (cdef_widths ?ws [] ?D) ?D (([], []), []) = (L, M)\<close> by fastforce
  have wtD: \<open>cdefs_wt ?ws [] ?D\<close> using assms(1) by (simp add: cproblem_wt_def Let_def)
  have \<open>ninv ?ws ?D L M\<close>
    using norm_loop_d_d_ok[of ?ws \<open>[]\<close> ?D \<open>([], [])\<close> \<open>[]\<close> L M] wtD assms(2) ninv_init nl by simp
  then show ?thesis using nl by (simp add: normalize_d_m_def ninv_def)
qed

end
