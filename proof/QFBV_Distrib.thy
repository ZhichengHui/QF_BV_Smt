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
  the term itself or a sum of two references, so it adds no product.

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

end
