theory QFBV_NormBudget
  imports QFBV_Distrib QFBV_Bound
begin

section \<open>A budget on the flattening of products in the normalization\<close>

text \<open>
  A functional model \<open>normalize_b_m\<close> of the Rust function \<^verbatim>\<open>normalize_k\<close> of the prototype
  \<^verbatim>\<open>844a971\<close> (\<^verbatim>\<open>normalize\<close> is \<^verbatim>\<open>normalize_k q 2\<close>): \<open>normalize_d_m\<close> with a budget on the
  flattening of products. The loop keeps two counters: \<open>seen\<close>, the sum of \<open>ccount\<close> of the old
  definitions so far (the current one included, with the widths of the old problem), and
  \<open>spent\<close>, the cost charged so far. A product of \<open>n > 2\<close> factors of width \<open>w\<close> is flattened only
  if \<open>0 < w\<close> and its \<open>n - 2\<close> extra products, of \<open>ccount\<close> \<open>19 * w * w\<close> each, cost at most
  \<open>(f - 1) * seen - spent\<close>; then their cost is added to \<open>spent\<close>.

  Statement by statement against \<^verbatim>\<open>844a971\<close>: \<open>mk_b_m\<close> is \<^verbatim>\<open>mk\<close> (\<^verbatim>\<open>bcost(4, w)\<close> is
  \<open>bcost BinOp_Mul w\<close>), \<open>norm_loop_b\<close> the loop of \<^verbatim>\<open>normalize_k\<close> (\<^verbatim>\<open>term_ccount\<close> is \<^const>\<open>ccount\<close>),
  with two differences besides those of \<^verbatim>\<open>QFBV_Norm\<close> and \<^verbatim>\<open>QFBV_Distrib\<close>. The counters are
  natural numbers: the Rust code saturates them at \<^verbatim>\<open>2^63\<close> (\<^verbatim>\<open>sat_add\<close>, \<^verbatim>\<open>sat_mul\<close>), which
  changes nothing when the \<open>ccount\<close> of the problem is below \<open>2 ^ 56\<close>, as \<open>fb_hyps\<close> requires.
  And without the substitution, \<open>seen\<close> grows at every definition; the Rust code skips the
  definitions that the substitution drops, which are variables, of \<open>ccount\<close> 0.

  \<open>normalize_b_correct\<close> is \<open>normalize_d_correct\<close> for every \<open>f\<close>: the guard only chooses between
  the two arms of \<^verbatim>\<open>mk\<close>. \<open>normalize_b_ccount\<close> bounds the \<open>ccount\<close> of the result by \<open>f\<close> times
  that of the problem, and \<open>normalize_b_defs_length\<close> the number of its definitions.
\<close>

subsection \<open>Models of the functions\<close>

text \<open>\<^verbatim>\<open>mk\<close> with the budget \<open>room\<close>: the new state, the definition, and the cost charged.\<close>
definition mk_b_m :: \<open>lst \<Rightarrow> CoreTermL \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> lst \<times> nat \<times> nat\<close> where
  \<open>mk_b_m L t w room \<equiv>
     (let r = distribute_m L (rewrite_m (fst L) t w) w in
      let (fs, ok) = product_factors_m (fst L) r in
      let extra = (if ok \<and> 2 < length fs then bcost BinOp_Mul w * (length fs - 2) else 0) in
      if ok \<and> 2 < length fs \<and> 0 < w \<and> extra \<le> room then
        (let fs = List.sort fs in let (L', k) = foldl (QFBV_Norm.mul_step w) (L, hd fs) (tl fs) in (L', k, extra))
      else (let (L', k) = mk_raw_m L r w in (L', k, 0)))\<close>

text \<open>The loop of \<^verbatim>\<open>normalize_k\<close>: the state is that of \<open>norm_loop_d\<close>, \<open>seen\<close> and \<open>spent\<close>; \<open>ws\<close> are
  the widths of the variables and \<open>dw\<close> those of the old definitions.\<close>
primrec norm_loop_b ::
  \<open>nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> CoreTermL list \<Rightarrow> (lst \<times> nat list) \<times> nat \<times> nat \<Rightarrow> (lst \<times> nat list) \<times> nat \<times> nat\<close>
where
  \<open>norm_loop_b f ws dw [] S = S\<close>
| \<open>norm_loop_b f ws dw (d # dd) S =
     (let ((L, M), seen, spent) = S in
      let seen = seen + ccount ws dw d in
      let room = (f - 1) * seen - spent in
      let (L1, k, c) = mk_b_m L (remap_m M d) (dw ! length M) room in
      norm_loop_b f ws dw dd ((L1, M @ [k]), seen, spent + c))\<close>

text \<open>\<^verbatim>\<open>normalize_k\<close>, without the substitution.\<close>
definition normalize_b_m :: \<open>nat \<Rightarrow> CoreProblemL \<Rightarrow> CoreProblemL\<close> where
  \<open>normalize_b_m f q \<equiv>
     (let ws = cvar_widths q in
      let dw = cdef_widths ws [] (CoreProblemL_defs q) in
      let ((L, M), _) = norm_loop_b f ws dw (CoreProblemL_defs q) ((([], []), []), 0, 0) in
      make_CoreProblemL (CoreProblemL_widths q) (fst L) (map (remap_m M) (CoreProblemL_asserts q)))\<close>

subsection \<open>The cost of terms\<close>

text \<open>The \<open>ccount\<close> of the definitions of a state.\<close>
definition ccs :: \<open>nat list \<Rightarrow> lst \<Rightarrow> nat\<close> where
  \<open>ccs ws L \<equiv> sum_list (map (ccount ws (snd L)) (fst L))\<close>

lemma ccount_Bin: \<open>ccount ws ds (CoreTermL_Bin op a b) = bcost op (cwidth ws ds a) + ccount ws ds a + ccount ws ds b\<close>
  by (simp add: ccount_def ncost_def)

lemma ccount_Ref: \<open>ccount ws ds (CoreTermL_Ref i) = 0\<close>
  by (simp add: ccount_def ncost_def)

lemma ccount_cr: \<open>ccount ws ds (cr k) = 0\<close>
  by (simp add: cr_def ccount_Ref)

lemma ccs_app: \<open>lok ws L \<Longrightarrow> sum_list (map (ccount ws (snd L @ e)) (fst L)) = ccs ws L\<close>
proof -
  assume l: \<open>lok ws L\<close>
  have \<open>ccount ws (snd L @ e) u = ccount ws (snd L) u\<close> if u: \<open>u \<in> set (fst L)\<close> for u
  proof -
    obtain k where k: \<open>k < length (fst L)\<close> \<open>u = fst L ! k\<close> using u in_set_conv_nth[of u \<open>fst L\<close>] by blast
    show ?thesis using ccount_app[OF lok_nth(1)[OF l k(1)]] k(2) by simp
  qed
  then have \<open>map (ccount ws (snd L @ e)) (fst L) = map (ccount ws (snd L)) (fst L)\<close> by (simp add: map_eq_conv)
  then show ?thesis unfolding ccs_def by (rule arg_cong[where f = sum_list])
qed

text \<open>A product of two references of width \<open>w\<close>.\<close>
lemma ccount_mul_refs:
  \<open>mul_refs r \<noteq> None \<Longrightarrow> cwidth ws ds r = w \<Longrightarrow> ccount ws ds r = bcost BinOp_Mul w\<close>
proof -
  assume h: \<open>mul_refs r \<noteq> None\<close> \<open>cwidth ws ds r = w\<close>
  obtain x y where \<open>mul_refs r = Some (x, y)\<close> using h(1) by auto
  then obtain i j where \<open>r = CoreTermL_Bin BinOp_Mul (CoreTermL_Ref i) (CoreTermL_Ref j)\<close>
    by (auto simp add: mul_refs_Some)
  then show ?thesis using h(2) by (simp add: ccount_Bin ccount_Ref)
qed

lemma bcost_mul_ge: \<open>15 * w \<le> bcost BinOp_Mul w\<close>
proof (cases w)
  case (Suc n)
  then have \<open>15 * w \<le> 19 * w * w\<close> by simp
  then show ?thesis by (simp add: bcost_def)
qed (simp add: bcost_def)

lemma ccount_neg_t: \<open>k < 2 ^ 64 \<Longrightarrow> ccount ws ds (neg_t k w) = 15 * (ds ! k)\<close>
  by (simp add: neg_t_def one_t_def ccount_def ncost_def bcost_def cr_def unat_of_nat_eq)

text \<open>The rewrites do not increase the cost.\<close>
lemma rewrite_cost:
  assumes \<open>cwt ws ds t\<close> \<open>cwidth ws ds t = w\<close>
  shows \<open>ccount ws ds (rewrite_m D t w) \<le> ccount ws ds t\<close>
proof (cases t)
  case (CoreTermL_Bin op a b)
  have wt: \<open>op \<noteq> BinOp_Concat \<longrightarrow> cwidth ws ds a = cwidth ws ds b\<close> using assms(1) CoreTermL_Bin by simp
  have ge: \<open>ccount ws ds t \<ge> bcost op (cwidth ws ds a)\<close> using CoreTermL_Bin by (simp add: ccount_Bin)
  have neg: \<open>ccount ws ds (neg_t x w) \<le> ccount ws ds t\<close>
    if h: \<open>op = BinOp_Mul\<close> \<open>ref_of u = Some x\<close> \<open>u = a \<or> u = b\<close> for u x
  proof -
    obtain i where i: \<open>u = CoreTermL_Ref i\<close> \<open>x = unat i\<close> using h(2) by (auto simp add: ref_of_Some)
    have \<open>cwidth ws ds u = w\<close> using h(1,3) wt assms(2) CoreTermL_Bin by auto
    then have \<open>ds ! x = w\<close> using i by simp
    moreover have \<open>cwidth ws ds a = w\<close> using h(1) assms(2) CoreTermL_Bin by simp
    ultimately show ?thesis
      using ccount_neg_t[of x ws ds w] i ge h(1) bcost_mul_ge[of w] unat_lt2p[of i] by simp
  qed
  show ?thesis
    using neg[of a] neg[of b] CoreTermL_Bin
    by (auto simp add: rewrite_m_def ccount_def ncost_def split: option.splits)
qed (simp_all add: rewrite_m_def)

text \<open>Nor does \<^verbatim>\<open>distribute\<close>: it replaces a product by a sum of two references.\<close>
lemma distribute_cases:
  \<open>distribute_m L t w = t \<or>
   (\<exists>p q. mul_refs t \<noteq> None \<and> p < length (fst L) \<and> snd L ! p = w \<and>
      distribute_m L t w = CoreTermL_Bin BinOp_Add (cr p) (cr q))\<close>
  by (auto simp add: distribute_m_def sum_lookup_def lookup_m_def find_def_m_def find_Some_iff Let_def
      split: option.splits prod.splits)

lemma distribute_cost:
  assumes \<open>length (fst L) \<le> 2 ^ 64\<close> \<open>cwidth ws (snd L) t = w\<close>
  shows \<open>ccount ws (snd L) (distribute_m L t w) \<le> ccount ws (snd L) t\<close>
proof -
  { fix p q assume h: \<open>mul_refs t \<noteq> None\<close> \<open>p < length (fst L)\<close> \<open>snd L ! p = w\<close>
    have \<open>ccount ws (snd L) (CoreTermL_Bin BinOp_Add (cr p) (cr q)) = 15 * w\<close>
      using h(2,3) assms(1) by (simp add: ccount_Bin cr_width bcost_def ccount_cr)
    moreover have \<open>ccount ws (snd L) t = bcost BinOp_Mul w\<close> using ccount_mul_refs[OF h(1) assms(2)] .
    ultimately have \<open>ccount ws (snd L) (CoreTermL_Bin BinOp_Add (cr p) (cr q)) \<le> ccount ws (snd L) t\<close>
      using bcost_mul_ge by simp }
  then show ?thesis using distribute_cases[of L t w] by auto
qed

subsection \<open>The cost of the new definitions\<close>

lemma mk_raw_cost:
  assumes \<open>lok ws L\<close> \<open>cwt ws (snd L) t\<close> \<open>mk_raw_m L t w = (L', k)\<close>
  shows \<open>ccs ws L' \<le> ccs ws L + ccount ws (snd L) t\<close>
proof (cases \<open>ref_of t = None \<and> find_def_m L t w = None\<close>)
  case True
  then have e: \<open>L' = (fst L @ [t], snd L @ [w])\<close> using assms(3) by (simp add: mk_raw_m_def push_m_def)
  show ?thesis using ccs_app[OF assms(1), of \<open>[w]\<close>] ccount_app[OF assms(2), of \<open>[w]\<close>] e
    by (simp add: ccs_def)
next
  case False
  then have \<open>L' = L\<close> using assms(3) by (auto simp add: mk_raw_m_def split: option.splits)
  then show ?thesis by simp
qed

text \<open>The products built by the loop of \<^verbatim>\<open>mk\<close>: \<open>bcost BinOp_Mul w\<close> each.\<close>
lemma mul_fold_cost:
  assumes \<open>lok ws L\<close> \<open>length (fst L) + length fs < 2 ^ 64\<close> \<open>acc < length (fst L)\<close> \<open>snd L ! acc = w\<close>
    \<open>\<forall>f \<in> set fs. f < length (fst L) \<and> snd L ! f = w\<close> \<open>foldl (QFBV_Norm.mul_step w) (L, acc) fs = (L', k)\<close>
  shows \<open>ccs ws L' \<le> ccs ws L + length fs * bcost BinOp_Mul w\<close>
  using assms
proof (induction fs arbitrary: L acc)
  case Nil
  then show ?case by simp
next
  case (Cons f fs)
  let ?t = \<open>CoreTermL_Bin BinOp_Mul (cr acc) (cr f)\<close>
  obtain L1 k1 where s: \<open>mk_raw_m L ?t w = (L1, k1)\<close> by fastforce
  have f: \<open>f < length (fst L)\<close> \<open>snd L ! f = w\<close> using Cons(6) by simp_all
  have lw: \<open>length (snd L) = length (fst L)\<close> using lok_length[OF Cons(2)] .
  have b: \<open>acc < 2 ^ 64\<close> \<open>f < 2 ^ 64\<close> using Cons(3,4) f(1) by simp_all
  have wt: \<open>cwt ws (snd L) ?t\<close> \<open>cwidth ws (snd L) ?t = w\<close>
    using cr_wt cr_width b Cons(4,5) f lw by simp_all
  have ct: \<open>ccount ws (snd L) ?t = bcost BinOp_Mul w\<close>
    using b Cons(5) by (simp add: ccount_Bin cr_width ccount_cr)
  note R = mk_raw_ok[OF Cons(2) wt s]
  have C1: \<open>ccs ws L1 \<le> ccs ws L + bcost BinOp_Mul w\<close> using mk_raw_cost[OF Cons(2) wt(1) s] ct by simp
  have rest: \<open>foldl (QFBV_Norm.mul_step w) (L1, k1) fs = (L', k)\<close> using Cons(7) s by (simp add: QFBV_Norm.mul_step_def)
  have lok1: \<open>lok ws L1\<close> using R lext_lok by blast
  have fs1: \<open>\<forall>g \<in> set fs. g < length (fst L1) \<and> snd L1 ! g = w\<close>
    using Cons(6) lext_nth_snd[OF Cons(2) conjunct1[OF R]] lext_length[OF conjunct1[OF R]] by auto
  have I: \<open>ccs ws L' \<le> ccs ws L1 + length fs * bcost BinOp_Mul w\<close>
    using Cons(1)[OF lok1 _ _ _ fs1 rest] R Cons(3) by simp
  show ?case using I C1 by simp
qed

subsection \<open>\<^verbatim>\<open>mk\<close> with the budget\<close>

lemma len_charge: \<open>(x :: nat) \<le> a + Suc m \<Longrightarrow> 19 * m \<le> e \<Longrightarrow> 19 * x \<le> 19 * Suc a + e\<close>
  by simp

text \<open>The arms are those of \<open>mk_d_ok\<close>; the cost of the new definitions is at most that of the
  term and the cost charged, which fits the budget; each definition beyond the first is charged at
  least 19.\<close>
lemma mk_b_ok:
  assumes \<open>lok ws L\<close> \<open>length (fst L) + 15 < 2 ^ 64\<close> \<open>cwt ws (snd L) t\<close> \<open>cwidth ws (snd L) t = w\<close>
    \<open>mk_b_m L t w room = (L', k, c)\<close>
  shows \<open>lext ws L L' \<and> length (fst L') \<le> length (fst L) + 15 \<and> k < length (fst L') \<and> snd L' ! k = w \<and>
    (\<forall>vs. vs_ok ws vs \<longrightarrow> CV ws vs L' ! k = ceval ws (snd L) vs (CV ws vs L) t)\<close>
    \<open>c \<le> room\<close> \<open>ccs ws L' \<le> ccs ws L + ccount ws (snd L) t + c\<close>
    \<open>19 * length (fst L') \<le> 19 * Suc (length (fst L)) + c\<close>
proof -
  let ?r = \<open>distribute_m L (rewrite_m (fst L) t w) w\<close>
  have b: \<open>length (fst L) \<le> 2 ^ 64\<close> using assms(2) by simp
  note RW = distribute_rewrite_sem[OF assms(1) b assms(3,4)]
  note RW1 = rewrite_sem[OF assms(1,3,4)]
  have rc: \<open>ccount ws (snd L) ?r \<le> ccount ws (snd L) t\<close>
    using distribute_cost[OF b conjunct1[OF conjunct2[OF RW1]]] rewrite_cost[OF assms(3,4)] by (rule order_trans)
  obtain fs ok where pf: \<open>product_factors_m (fst L) ?r = (fs, ok)\<close> by fastforce
  let ?e = \<open>bcost BinOp_Mul w * (length fs - 2)\<close>
  have all: \<open>(lext ws L L' \<and> length (fst L') \<le> length (fst L) + 15 \<and> k < length (fst L') \<and> snd L' ! k = w \<and>
    (\<forall>vs. vs_ok ws vs \<longrightarrow> CV ws vs L' ! k = ceval ws (snd L) vs (CV ws vs L) t)) \<and>
    c \<le> room \<and> ccs ws L' \<le> ccs ws L + ccount ws (snd L) t + c \<and>
    19 * length (fst L') \<le> 19 * Suc (length (fst L)) + c\<close>
  proof (cases \<open>ok \<and> 2 < length fs \<and> 0 < w \<and> ?e \<le> room\<close>)
    case True
    let ?s = \<open>List.sort fs\<close>
    have mk: \<open>foldl (QFBV_Norm.mul_step w) (L, hd ?s) (tl ?s) = (L', k)\<close> and ce: \<open>c = ?e\<close>
      using assms(5) pf True by (simp_all add: mk_b_m_def Let_def split: prod.splits)
    have tail: \<open>(let (fs, ok) = product_factors_m (fst L) ?r in
        if ok \<and> 2 < length fs then (let fs = List.sort fs in foldl (QFBV_Norm.mul_step w) (L, hd fs) (tl fs))
        else mk_raw_m L ?r w) = (L', k)\<close>
      using mk pf True by simp
    note T = mk_tail_ok[OF assms(1,2) conjunct1[OF RW] conjunct1[OF conjunct2[OF RW]] tail]
    have pf': \<open>product_factors_m (fst L) ?r = (fs, True)\<close> using pf True by simp
    note P = product_ok[OF assms(1) conjunct1[OF RW] pf']
    have ne: \<open>?s = hd ?s # tl ?s\<close> using True by (metis List.length_sort gr_implies_not0 list.collapse list.size(3))
    have st: \<open>set ?s = set fs\<close> by simp
    have h: \<open>hd ?s \<in> set fs\<close> \<open>\<forall>f \<in> set (tl ?s). f \<in> set fs\<close>
      using ne st by (metis list.set_intros(1), metis list.set_intros(2))
    have lt: \<open>length (tl ?s) \<le> 15\<close> using conjunct1[OF P] by simp
    have hw: \<open>hd ?s < length (fst L)\<close> \<open>snd L ! hd ?s = w\<close> using P h(1) RW by simp_all
    have tw: \<open>\<forall>f \<in> set (tl ?s). f < length (fst L) \<and> snd L ! f = w\<close> using P h(2) RW by simp
    have b2: \<open>length (fst L) + length (tl ?s) < 2 ^ 64\<close> using assms(2) lt by simp
    have C: \<open>ccs ws L' \<le> ccs ws L + length (tl ?s) * bcost BinOp_Mul w\<close>
      using mul_fold_cost[OF assms(1) b2 hw tw mk] .
    have Ln: \<open>length (fst L') \<le> length (fst L) + length (tl ?s)\<close>
      using mul_fold[OF assms(1) b2 hw tw mk] by simp
    have mr: \<open>mul_refs ?r \<noteq> None\<close> using pf' by (auto simp add: product_factors_m_def split: option.splits)
    have cr: \<open>ccount ws (snd L) ?r = bcost BinOp_Mul w\<close> using ccount_mul_refs[OF mr] RW by simp
    have n: \<open>length (tl ?s) = Suc (length fs - 2)\<close> using conjunct1[OF conjunct2[OF True]] by simp
    have \<open>length (tl ?s) * bcost BinOp_Mul w = ccount ws (snd L) ?r + ?e\<close> using cr n by (simp add: algebra_simps)
    then have c3: \<open>ccs ws L' \<le> ccs ws L + ccount ws (snd L) t + c\<close> using C rc ce by simp
    have \<open>19 * (length fs - 2) \<le> ?e\<close>
    proof -
      have \<open>19 \<le> bcost BinOp_Mul w\<close> using True by (simp add: bcost_def)
      then show ?thesis by simp
    qed
    then have c4: \<open>19 * length (fst L') \<le> 19 * Suc (length (fst L)) + c\<close>
      using len_charge[of \<open>length (fst L')\<close> \<open>length (fst L)\<close> \<open>length fs - 2\<close> c] Ln n ce by simp
    show ?thesis using T RW True ce c3 c4 by simp
  next
    case False
    have mk: \<open>mk_raw_m L ?r w = (L', k)\<close> and ce: \<open>c = 0\<close>
      using assms(5) pf False by (auto simp add: mk_b_m_def Let_def split: prod.splits if_splits)
    note M = mk_raw_ok[OF assms(1) conjunct1[OF RW] conjunct1[OF conjunct2[OF RW]] mk]
    have c3: \<open>ccs ws L' \<le> ccs ws L + ccount ws (snd L) t\<close>
      using mk_raw_cost[OF assms(1) conjunct1[OF RW] mk] rc by simp
    show ?thesis using M RW ce c3 by auto
  qed
  then show \<open>lext ws L L' \<and> length (fst L') \<le> length (fst L) + 15 \<and> k < length (fst L') \<and> snd L' ! k = w \<and>
    (\<forall>vs. vs_ok ws vs \<longrightarrow> CV ws vs L' ! k = ceval ws (snd L) vs (CV ws vs L) t)\<close>
    \<open>c \<le> room\<close> \<open>ccs ws L' \<le> ccs ws L + ccount ws (snd L) t + c\<close>
    \<open>19 * length (fst L') \<le> 19 * Suc (length (fst L)) + c\<close>
    by blast+
qed

subsection \<open>The loop\<close>

text \<open>One iteration of the loop keeps the invariant of \<^verbatim>\<open>QFBV_Norm\<close>, for any new definition \<open>k\<close>
  with the facts of \<open>mk_d_ok\<close>: the proof of \<open>ninv_d_step\<close>.\<close>
lemma ninv_step_of:
  assumes \<open>ninv ws P L M\<close> \<open>cwt ws (cdef_widths ws [] P) d\<close> \<open>length (fst L) + 15 < 2 ^ 64\<close>
    \<open>lext ws L L1\<close> \<open>length (fst L1) \<le> length (fst L) + 15\<close> \<open>k < length (fst L1)\<close>
    \<open>snd L1 ! k = cwidth ws (cdef_widths ws [] P) d\<close>
    \<open>\<forall>vs. vs_ok ws vs \<longrightarrow> CV ws vs L1 ! k = ceval ws (snd L) vs (CV ws vs L) (remap_m M d)\<close>
  shows \<open>ninv ws (P @ [d]) L1 (M @ [k])\<close>
proof -
  let ?ds = \<open>cdef_widths ws [] P\<close>
  have I: \<open>lok ws L\<close> \<open>length M = length P\<close> \<open>length (fst L) \<le> 15 * length P\<close> \<open>menv M (snd L) ?ds\<close>
    \<open>\<forall>vs. vs_ok ws vs \<longrightarrow> venv M (CV ws vs L) ?ds (cdef_values ws [] vs [] P)\<close>
    using assms(1) by (simp_all add: ninv_def)
  have lds: \<open>length ?ds = length P\<close> by (simp add: cdef_widths_length)
  note lx = assms(4) and ln = assms(5) and kl = assms(6) and kw = assms(7) and kv = assms(8)
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

text \<open>Remapping keeps the cost.\<close>
lemma remap_cost:
  \<open>menv M cws ds \<Longrightarrow> cwt ws ds t \<Longrightarrow> ccount ws cws (remap_m M t) = ccount ws ds t\<close>
proof (induction t)
  case (CoreTermL_Ref i)
  then show ?case by (simp add: cr_def ccount_Ref)
next
  case (CoreTermL_Bin op a b)
  then show ?case by (simp add: ccount_Bin remap_wt)
next
  case (CoreTermL_Ite c a b)
  then show ?case by (simp add: ccount_def ncost_def remap_wt)
qed (simp_all add: ccount_def ncost_def)

text \<open>The invariant of the loop, with that of the budget: \<open>seen\<close> is the cost of the old
  definitions so far, the new ones cost at most \<open>seen + spent\<close>, and \<open>spent \<le> (f - 1) * seen\<close>.\<close>
lemma norm_loop_b_ok:
  assumes \<open>cdefs_wt ws [] (P @ R)\<close> \<open>ninv ws P L M\<close> \<open>15 * length (P @ R) < 2 ^ 64\<close>
    \<open>seen = sum_list (map (ccount ws (cdef_widths ws [] (P @ R))) P)\<close>
    \<open>ccs ws L \<le> seen + spent\<close> \<open>spent \<le> (f - 1) * seen\<close> \<open>19 * length (fst L) \<le> 19 * length P + spent\<close>
    \<open>norm_loop_b f ws (cdef_widths ws [] (P @ R)) R ((L, M), seen, spent) = ((L', M'), seen', spent')\<close>
  shows \<open>ninv ws (P @ R) L' M' \<and> seen' = sum_list (map (ccount ws (cdef_widths ws [] (P @ R))) (P @ R)) \<and>
    ccs ws L' \<le> seen' + spent' \<and> spent' \<le> (f - 1) * seen' \<and> 19 * length (fst L') \<le> 19 * length (P @ R) + spent'\<close>
  using assms
proof (induction R arbitrary: P L M seen spent)
  case Nil
  then show ?case by simp
next
  case (Cons d R)
  let ?ds = \<open>cdef_widths ws [] P\<close> and ?DW = \<open>cdef_widths ws [] (P @ d # R)\<close>
  have wtd: \<open>cwt ws ?ds d\<close> using Cons(2) by (simp add: cdefs_wt_append)
  obtain e where DW: \<open>?DW = (?ds @ [cwidth ws ?ds d]) @ e\<close>
  proof -
    have \<open>?DW = cdef_widths ws (?ds @ [cwidth ws ?ds d]) R\<close> by (simp add: cdef_widths_append)
    then show ?thesis using cdef_widths_prefix that by metis
  qed
  have lM: \<open>length M = length ?ds\<close> using Cons(3) by (simp add: ninv_def cdef_widths_length)
  have dwn: \<open>?DW ! length M = cwidth ws ?ds d\<close> using DW lM by (simp add: nth_append)
  have bnd: \<open>length (fst L) + 15 < 2 ^ 64\<close> using Cons(3,4) by (simp add: ninv_def)
  have lok: \<open>lok ws L\<close> and me: \<open>menv M (snd L) ?ds\<close> using Cons(3) by (simp_all add: ninv_def)
  have Cd: \<open>ccount ws (snd L) (remap_m M d) = ccount ws ?DW d\<close>
    using remap_cost[OF me wtd] ccount_app[OF wtd, of \<open>[cwidth ws ?ds d] @ e\<close>] DW by simp
  define seen1 where \<open>seen1 = seen + ccount ws ?DW d\<close>
  define room where \<open>room = (f - 1) * seen1 - spent\<close>
  obtain L1 k c where mk: \<open>mk_b_m L (remap_m M d) (cwidth ws ?ds d) room = (L1, k, c)\<close>
    by (metis prod_cases3)
  note RM = remap_wt[OF me wtd]
  note K = mk_b_ok[OF lok bnd conjunct1[OF RM] conjunct2[OF RM] mk]
  have N1: \<open>ninv ws (P @ [d]) L1 (M @ [k])\<close>
    using ninv_step_of[OF Cons(3) wtd bnd] K(1) by blast
  have rest: \<open>norm_loop_b f ws (cdef_widths ws [] ((P @ [d]) @ R)) R ((L1, M @ [k]), seen1, spent + c) =
      ((L', M'), seen', spent')\<close>
    using Cons(9) mk dwn by (simp add: seen1_def room_def)
  have s1: \<open>seen1 = sum_list (map (ccount ws (cdef_widths ws [] ((P @ [d]) @ R))) (P @ [d]))\<close>
    using Cons(5) by (simp add: seen1_def)
  have m: \<open>(f - 1) * seen \<le> (f - 1) * seen1\<close> by (simp add: seen1_def)
  have s2: \<open>spent + c \<le> (f - 1) * seen1\<close> using K(2) Cons(7) m unfolding room_def by linarith
  have s3: \<open>ccs ws L1 \<le> seen1 + (spent + c)\<close> using K(3) Cons(6) Cd by (simp add: seen1_def)
  have s4: \<open>19 * length (fst L1) \<le> 19 * length (P @ [d]) + (spent + c)\<close> using K(4) Cons(8) by simp
  have wt': \<open>cdefs_wt ws [] ((P @ [d]) @ R)\<close> and b': \<open>15 * length ((P @ [d]) @ R) < 2 ^ 64\<close>
    using Cons(2,4) by simp_all
  show ?case using Cons.IH[OF wt' N1 b' s1 s3 s2 s4 rest] unfolding append_assoc append.simps by blast
qed

subsection \<open>The theorems\<close>

lemma norm_loop_b_init:
  assumes \<open>cproblem_wt q\<close> \<open>15 * length (CoreProblemL_defs q) < 2 ^ 64\<close>
    \<open>norm_loop_b f (cvar_widths q) (cdef_widths (cvar_widths q) [] (CoreProblemL_defs q)) (CoreProblemL_defs q)
       ((([], []), []), 0, 0) = ((L, M), seen, spent)\<close>
  shows \<open>ninv (cvar_widths q) (CoreProblemL_defs q) L M \<and>
    seen = sum_list (map (ccount (cvar_widths q) (cdef_widths (cvar_widths q) [] (CoreProblemL_defs q)))
                         (CoreProblemL_defs q)) \<and>
    ccs (cvar_widths q) L \<le> seen + spent \<and> spent \<le> (f - 1) * seen \<and>
    19 * length (fst L) \<le> 19 * length (CoreProblemL_defs q) + spent\<close>
proof -
  have wtD: \<open>cdefs_wt (cvar_widths q) [] (CoreProblemL_defs q)\<close>
    using assms(1) by (simp add: cproblem_wt_def Let_def)
  let ?ws = \<open>cvar_widths q\<close> and ?D = \<open>CoreProblemL_defs q\<close>
  have a1: \<open>cdefs_wt ?ws [] ([] @ ?D)\<close> and a3: \<open>15 * length ([] @ ?D) < 2 ^ 64\<close>
    using wtD assms(2) by simp_all
  have a4: \<open>0 = sum_list (map (ccount ?ws (cdef_widths ?ws [] ([] @ ?D))) [])\<close> by simp
  have a5: \<open>ccs ?ws ([], []) \<le> 0 + 0\<close> by (simp add: ccs_def)
  have a6: \<open>(0 :: nat) \<le> (f - 1) * 0\<close> and a7: \<open>19 * length (fst ([], [])) \<le> 19 * length [] + (0 :: nat)\<close>
    by simp_all
  have a8: \<open>norm_loop_b f ?ws (cdef_widths ?ws [] ([] @ ?D)) ?D ((([], []), []), 0, 0) = ((L, M), seen, spent)\<close>
    using assms(3) by simp
  show ?thesis using norm_loop_b_ok[OF a1 ninv_init a3 a4 a5 a6 a7 a8] unfolding append_Nil by blast
qed

theorem normalize_b_correct:
  assumes \<open>cproblem_wt q\<close> \<open>15 * length (CoreProblemL_defs q) < 2 ^ 64\<close>
  shows \<open>CoreProblemL_widths (normalize_b_m f q) = CoreProblemL_widths q\<close> \<open>cproblem_wt (normalize_b_m f q)\<close>
    \<open>cis_model (normalize_b_m f q) m \<longleftrightarrow> cis_model q m\<close>
proof -
  let ?ws = \<open>cvar_widths q\<close> and ?D = \<open>CoreProblemL_defs q\<close> and ?A = \<open>CoreProblemL_asserts q\<close>
  let ?dw = \<open>cdef_widths ?ws [] ?D\<close>
  obtain L M seen spent where nl: \<open>norm_loop_b f ?ws ?dw ?D ((([], []), []), 0, 0) = ((L, M), seen, spent)\<close>
    by (metis prod.exhaust)
  have nq: \<open>normalize_b_m f q = make_CoreProblemL (CoreProblemL_widths q) (fst L) (map (remap_m M) ?A)\<close>
    using nl by (simp add: normalize_b_m_def)
  have wtA: \<open>\<forall>t \<in> set ?A. cwt ?ws ?dw t \<and> cwidth ?ws ?dw t = 1\<close>
    using assms(1) by (simp_all add: cproblem_wt_def Let_def)
  have N: \<open>ninv ?ws ?D L M\<close> using norm_loop_b_init[OF assms nl] by simp
  have lok: \<open>lok ?ws L\<close> and me: \<open>menv M (snd L) ?dw\<close>
    and ve: \<open>\<forall>vs. vs_ok ?ws vs \<longrightarrow> venv M (CV ?ws vs L) ?dw (cdef_values ?ws [] vs [] ?D)\<close>
    using N by (simp_all add: ninv_def)
  have sL: \<open>cdef_widths ?ws [] (fst L) = snd L\<close> using lok by (simp add: lok_def)
  have cw: \<open>cvar_widths (normalize_b_m f q) = ?ws\<close> by (simp add: nq cvar_widths_def)
  show \<open>CoreProblemL_widths (normalize_b_m f q) = CoreProblemL_widths q\<close> by (simp add: nq)
  have At: \<open>\<forall>t \<in> set ?A. cwt ?ws (snd L) (remap_m M t) \<and> cwidth ?ws (snd L) (remap_m M t) = 1\<close>
    using remap_wt[OF me] wtA by auto
  show \<open>cproblem_wt (normalize_b_m f q)\<close>
    using cw lok At sL by (simp add: cproblem_wt_def nq lok_def Let_def)
  have ca: \<open>cis_assignment (normalize_b_m f q) m = cis_assignment q m\<close>
    by (simp add: cis_assignment_def cw)
  have cs: \<open>csatisfies (normalize_b_m f q) m = csatisfies q m\<close> if a: \<open>cis_assignment q m\<close>
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
  show \<open>cis_model (normalize_b_m f q) m \<longleftrightarrow> cis_model q m\<close>
    using ca cs by (auto simp add: cis_model_def)
qed

text \<open>The \<open>ccount\<close> of the definitions and assertions, with the widths of the problem, as in
  \<open>fb_hyps\<close>.\<close>
definition pcount :: \<open>CoreProblemL \<Rightarrow> nat\<close> where
  \<open>pcount p \<equiv> sum_list (map (ccount (cvar_widths p) (cdef_widths (cvar_widths p) [] (CoreProblemL_defs p)))
                            (CoreProblemL_defs p @ CoreProblemL_asserts p))\<close>

theorem normalize_b_ccount:
  assumes \<open>cproblem_wt q\<close> \<open>15 * length (CoreProblemL_defs q) < 2 ^ 64\<close> \<open>1 \<le> f\<close>
  shows \<open>pcount (normalize_b_m f q) \<le> f * pcount q\<close>
proof -
  let ?ws = \<open>cvar_widths q\<close> and ?D = \<open>CoreProblemL_defs q\<close> and ?A = \<open>CoreProblemL_asserts q\<close>
  let ?dw = \<open>cdef_widths ?ws [] ?D\<close>
  obtain L M seen spent where nl: \<open>norm_loop_b f ?ws ?dw ?D ((([], []), []), 0, 0) = ((L, M), seen, spent)\<close>
    by (metis prod.exhaust)
  have nq: \<open>normalize_b_m f q = make_CoreProblemL (CoreProblemL_widths q) (fst L) (map (remap_m M) ?A)\<close>
    using nl by (simp add: normalize_b_m_def)
  note B = norm_loop_b_init[OF assms(1,2) nl]
  have lok: \<open>lok ?ws L\<close> and me: \<open>menv M (snd L) ?dw\<close> using B by (simp_all add: ninv_def)
  have sL: \<open>cdef_widths ?ws [] (fst L) = snd L\<close> using lok by (simp add: lok_def)
  have cw: \<open>cvar_widths (normalize_b_m f q) = ?ws\<close> by (simp add: nq cvar_widths_def)
  have wtA: \<open>\<forall>t \<in> set ?A. cwt ?ws ?dw t\<close> using assms(1) by (simp add: cproblem_wt_def Let_def)
  have A: \<open>map (ccount ?ws (snd L) \<circ> remap_m M) ?A = map (ccount ?ws ?dw) ?A\<close>
    using remap_cost[OF me] wtA by simp
  have P: \<open>pcount (normalize_b_m f q) = ccs ?ws L + sum_list (map (ccount ?ws ?dw) ?A)\<close>
    using cw sL by (simp add: pcount_def nq ccs_def A)
  have Q: \<open>pcount q = seen + sum_list (map (ccount ?ws ?dw) ?A)\<close> using B by (simp add: pcount_def)
  have \<open>ccs ?ws L \<le> f * seen\<close>
  proof -
    have \<open>seen + (f - 1) * seen = f * seen\<close> using assms(3) by (simp add: algebra_simps)
    then show ?thesis using B by linarith
  qed
  moreover have \<open>sum_list (map (ccount ?ws ?dw) ?A) \<le> f * sum_list (map (ccount ?ws ?dw) ?A)\<close>
    using assms(3) by simp
  ultimately show ?thesis unfolding P Q distrib_left by (rule add_mono)
qed

text \<open>Each new definition beyond one per old definition was charged at least 19.\<close>
theorem normalize_b_defs_length:
  assumes \<open>cproblem_wt q\<close> \<open>15 * length (CoreProblemL_defs q) < 2 ^ 64\<close>
  shows \<open>19 * length (CoreProblemL_defs (normalize_b_m f q)) \<le>
    19 * length (CoreProblemL_defs q) +
    (f - 1) * sum_list (map (ccount (cvar_widths q) (cdef_widths (cvar_widths q) [] (CoreProblemL_defs q)))
                            (CoreProblemL_defs q))\<close>
proof -
  let ?ws = \<open>cvar_widths q\<close> and ?D = \<open>CoreProblemL_defs q\<close>
  obtain L M seen spent where
    nl: \<open>norm_loop_b f ?ws (cdef_widths ?ws [] ?D) ?D ((([], []), []), 0, 0) = ((L, M), seen, spent)\<close>
    by (metis prod.exhaust)
  note B = norm_loop_b_init[OF assms nl]
  have d: \<open>CoreProblemL_defs (normalize_b_m f q) = fst L\<close> using nl by (simp add: normalize_b_m_def)
  have s: \<open>seen = sum_list (map (ccount ?ws (cdef_widths ?ws [] ?D)) ?D)\<close>
    and l: \<open>19 * length (fst L) \<le> 19 * length ?D + spent\<close> and sp: \<open>spent \<le> (f - 1) * seen\<close>
    using B by blast+
  show ?thesis using l sp unfolding d s[symmetric] by linarith
qed

end
