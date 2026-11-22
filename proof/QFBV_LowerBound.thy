theory QFBV_LowerBound
  imports QFBV_Lower QFBV_Bound
begin

section \<open>The size bound of the specification covers the rewriting\<close>

text \<open>
  The size bound of the extended problem (\<^const>\<open>size_bound\<close>) covers the size bound of the core
  problem the rewriting builds (\<^const>\<open>csize_bound\<close>), and so the fuel of the core solver, and it
  also covers the counters and loops of the rewriting itself: the number of core definitions,
  every width, the recursion depth and the iterations of the loop for \<open>repeat\<close>.

  The cost of a state is the number of its definitions plus their weights. Rewriting a term \<open>t\<close>
  adds at most \<open>K\<close> times the weight of each subterm and of its operands (\<open>lower_m_cost\<close>).
\<close>

subsection \<open>Widths and weights of the built core terms\<close>

text \<open>Every subterm of a core term has width at most \<open>M\<close>.\<close>
definition cws_le :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> CoreTermL \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>cws_le ws cws t M \<equiv> \<forall>u \<in> set (csubterms t). cwidth ws cws u \<le> M\<close>

lemma csub_self: \<open>t \<in> set (csubterms t)\<close>
  by (cases t) simp_all

lemma cws_le_Const: \<open>length bs \<le> M \<Longrightarrow> cws_le ws cws (CoreTermL_Const bs) M\<close>
  by (simp add: cws_le_def)

lemma cws_le_cr: \<open>k < 2 ^ 64 \<Longrightarrow> cws ! k \<le> M \<Longrightarrow> cws_le ws cws (cr k) M\<close>
  by (simp add: cws_le_def cr_def unat_wn)

lemma cws_le_Not: \<open>cws_le ws cws a M \<Longrightarrow> cws_le ws cws (CoreTermL_Not a) M\<close>
  using csub_self[of a] by (auto simp add: cws_le_def)

lemma cws_le_Bin:
  \<open>cws_le ws cws a M \<Longrightarrow> cws_le ws cws b M \<Longrightarrow> 1 \<le> M \<Longrightarrow>
   (op = BinOp_Concat \<longrightarrow> cwidth ws cws a + cwidth ws cws b \<le> M) \<Longrightarrow>
   cws_le ws cws (CoreTermL_Bin op a b) M\<close>
  using csub_self[of a] csub_self[of b] by (cases op) (auto simp add: cws_le_def)

lemma cws_le_Extract:
  \<open>cws_le ws cws a M \<Longrightarrow> unat hi - unat lo + 1 \<le> M \<Longrightarrow> cws_le ws cws (CoreTermL_Extract hi lo a) M\<close>
  by (simp add: cws_le_def)

lemma cws_le_Ite:
  \<open>cws_le ws cws c M \<Longrightarrow> cws_le ws cws a M \<Longrightarrow> cws_le ws cws b M \<Longrightarrow> cws_le ws cws (CoreTermL_Ite c a b) M\<close>
  using csub_self[of a] by (auto simp add: cws_le_def)

lemma cws_le_mono: \<open>cws_le ws cws t M \<Longrightarrow> M \<le> M' \<Longrightarrow> cws_le ws cws t M'\<close>
  by (auto simp add: cws_le_def)

lemmas cws_le_intros = cws_le_Const cws_le_cr cws_le_Not cws_le_Bin cws_le_Extract cws_le_Ite

text \<open>The weight of a core term is bounded by its number of subterms times the square of the
  bound on their widths.\<close>
lemma cterm_weight_le:
  \<open>cws_le ws cws t M \<Longrightarrow> cterm_weight ws cws t \<le> length (csubterms t) * (M + 1) ^ 2\<close>
proof -
  have bounded: \<open>\<And>xs c. (\<forall>x \<in> set xs. x \<le> c) \<Longrightarrow> sum_list xs \<le> length xs * (c :: nat)\<close>
  proof -
    fix xs :: \<open>nat list\<close> and c :: nat
    show \<open>(\<forall>x \<in> set xs. x \<le> c) \<Longrightarrow> sum_list xs \<le> length xs * c\<close> by (induction xs) simp_all
  qed
  assume \<open>cws_le ws cws t M\<close>
  then have \<open>\<forall>x \<in> set (map (\<lambda>u. (cwidth ws cws u + 1) ^ 2) (csubterms t)). x \<le> (M + 1) ^ 2\<close>
    by (auto simp add: cws_le_def intro: power_mono)
  then have \<open>sum_list (map (\<lambda>u. (cwidth ws cws u + 1) ^ 2) (csubterms t)) \<le>
      length (map (\<lambda>u. (cwidth ws cws u + 1) ^ 2) (csubterms t)) * (M + 1) ^ 2\<close>
    by (rule bounded)
  then show ?thesis by (simp add: cterm_weight_def)
qed

text \<open>The built terms: widths at most the width \<open>w\<close> of their definitions.\<close>
lemma Suc_0_le: \<open>1 \<le> n \<Longrightarrow> Suc 0 \<le> n\<close> for n :: nat
  by simp

lemma one_le_add: \<open>1 \<le> a \<Longrightarrow> 1 \<le> a + b \<and> Suc 0 \<le> a + b \<and> 1 \<le> b + a \<and> Suc 0 \<le> b + a\<close> for a b :: nat
  by simp

lemma one_t_le: \<open>1 \<le> w \<Longrightarrow> w \<le> M \<Longrightarrow> cws_le ws cws (one_t w) M\<close>
  unfolding one_t_def by (intro cws_le_intros) simp_all

lemma neg_t_le: \<open>k < 2 ^ 64 \<Longrightarrow> cws ! k = w \<Longrightarrow> 1 \<le> w \<Longrightarrow> w \<le> M \<Longrightarrow> cws_le ws cws (neg_t k w) M\<close>
  unfolding neg_t_def by (intro cws_le_intros one_t_le) simp_all

lemma msb_t_le:
  \<open>k < 2 ^ 64 \<Longrightarrow> cws ! k = w \<Longrightarrow> 1 \<le> w \<Longrightarrow> w < 2 ^ 64 \<Longrightarrow> w \<le> M \<Longrightarrow> cws_le ws cws (msb_t k w) M\<close>
  unfolding msb_t_def by (intro cws_le_intros) (simp_all add: unat_wn)

lemma abs_t_le:
  \<open>k < 2 ^ 64 \<Longrightarrow> cws ! k = w \<Longrightarrow> 1 \<le> w \<Longrightarrow> w < 2 ^ 64 \<Longrightarrow> w \<le> M \<Longrightarrow> cws_le ws cws (abs_t k w) M\<close>
  unfolding abs_t_def by (intro cws_le_intros msb_t_le neg_t_le) simp_all

lemma slt_t_le:
  \<open>ka < 2 ^ 64 \<Longrightarrow> kb < 2 ^ 64 \<Longrightarrow> cws ! ka = w \<Longrightarrow> cws ! kb = w \<Longrightarrow> 1 \<le> w \<Longrightarrow> w < 2 ^ 64 \<Longrightarrow>
   w \<le> M \<Longrightarrow> cws_le ws cws (slt_t ka kb w) M\<close>
  unfolding slt_t_def by (intro cws_le_intros msb_t_le) simp_all

lemma sle_t_le:
  \<open>ka < 2 ^ 64 \<Longrightarrow> kb < 2 ^ 64 \<Longrightarrow> cws ! ka = w \<Longrightarrow> cws ! kb = w \<Longrightarrow> 1 \<le> w \<Longrightarrow> w < 2 ^ 64 \<Longrightarrow>
   w \<le> M \<Longrightarrow> cws_le ws cws (sle_t ka kb w) M\<close>
  unfolding sle_t_def by (intro cws_le_intros msb_t_le) simp_all

lemma csubterms_cr [simp]: \<open>csubterms (cr k) = [cr k]\<close> by (simp add: cr_def)
lemma one_t_len: \<open>length (csubterms (one_t w)) = 3\<close> by (simp add: one_t_def)
lemma neg_t_len: \<open>length (csubterms (neg_t k w)) = 6\<close> by (simp add: neg_t_def one_t_def cr_def)
lemma msb_t_len: \<open>length (csubterms (msb_t k w)) = 2\<close> by (simp add: msb_t_def cr_def)
lemma abs_t_len: \<open>length (csubterms (abs_t k w)) = 10\<close> by (simp add: abs_t_def msb_t_def neg_t_def one_t_def cr_def)
lemma slt_t_len: \<open>length (csubterms (slt_t ka kb w)) = 17\<close> by (simp add: slt_t_def msb_t_def cr_def)
lemma sle_t_len: \<open>length (csubterms (sle_t ka kb w)) = 18\<close> by (simp add: sle_t_def msb_t_def cr_def)

subsection \<open>The cost of a state\<close>

definition lcost :: \<open>nat list \<Rightarrow> lst \<Rightarrow> nat\<close> where
  \<open>lcost ws L \<equiv> length (fst L) + sum_list (map (cterm_weight ws (snd L)) (fst L))\<close>

lemma cwt_append: \<open>cwt ws ds t \<Longrightarrow> cwt ws (ds @ e) t\<close>
  by (induction t) (simp_all add: nth_append wt_width_app)

lemma cdefs_wt_each: \<open>cdefs_wt ws [] xs \<Longrightarrow> j < length xs \<Longrightarrow> cwt ws (cdef_widths ws [] xs) (xs ! j)\<close>
proof -
  assume A: \<open>cdefs_wt ws [] xs\<close> \<open>j < length xs\<close>
  have \<open>cdefs_wt ws [] (take j xs @ xs ! j # drop (Suc j) xs)\<close> using A by (simp add: id_take_nth_drop[symmetric])
  then have \<open>cwt ws (cdef_widths ws [] (take j xs)) (xs ! j)\<close> by (simp add: cdefs_wt_append)
  moreover have \<open>cdef_widths ws [] xs = cdef_widths ws (cdef_widths ws [] (take j xs)) (drop j xs)\<close>
    using cdef_widths_append[of ws \<open>[]\<close> \<open>take j xs\<close> \<open>drop j xs\<close>] by simp
  ultimately show ?thesis using cdef_widths_prefix cwt_append by metis
qed

text \<open>The weights of the definitions of a well-formed state do not change when widths are appended.\<close>
lemma lcost_widths:
  \<open>lok ws L \<Longrightarrow> map (cterm_weight ws (snd L @ e)) (fst L) = map (cterm_weight ws (snd L)) (fst L)\<close>
proof (intro map_cong refl)
  fix u assume \<open>lok ws L\<close> \<open>u \<in> set (fst L)\<close>
  then obtain j where \<open>j < length (fst L)\<close> \<open>u = fst L ! j\<close> by (auto simp add: in_set_conv_nth)
  then have \<open>cwt ws (snd L) u\<close> using cdefs_wt_each \<open>lok ws L\<close> by (simp add: lok_def)
  then show \<open>cterm_weight ws (snd L @ e) u = cterm_weight ws (snd L) u\<close> by (rule tw_app)
qed

lemma lcost_lext: \<open>lok ws L \<Longrightarrow> lext ws L L' \<Longrightarrow> lcost ws L \<le> lcost ws L'\<close>
proof -
  assume L: \<open>lok ws L\<close> and X: \<open>lext ws L L'\<close>
  obtain e where e: \<open>fst L' = fst L @ e\<close> using X by (auto simp add: lext_def)
  obtain e' where e': \<open>snd L' = snd L @ e'\<close> using lext_snd[OF L X] by blast
  note M = lcost_widths[OF L, of e']
  show ?thesis unfolding lcost_def e e' map_append sum_list_append M by simp
qed

text \<open>Pushing a term adds one definition and its weight.\<close>
lemma lcost_push:
  assumes \<open>lok ws L\<close> \<open>cwt ws (snd L) t\<close> \<open>cwidth ws (snd L) t = w\<close> \<open>push_m L t w = (L', k)\<close>
  shows \<open>lcost ws L' = lcost ws L + 1 + cterm_weight ws (snd L) t\<close>
proof -
  note P = push_ok[OF assms]
  have M: \<open>map (cterm_weight ws (snd L @ [w])) (fst L) = map (cterm_weight ws (snd L)) (fst L)\<close>
    using lcost_widths[OF assms(1), of \<open>[w]\<close>] .
  have T: \<open>cterm_weight ws (snd L @ [w]) t = cterm_weight ws (snd L) t\<close> by (rule tw_app[OF assms(2)])
  show ?thesis unfolding lcost_def P(2) P(3) map_append sum_list_append M by (simp add: T)
qed

text \<open>The cost of one push: the definition and its weight.\<close>
lemma push_cost:
  assumes \<open>lok ws L\<close> \<open>cwt ws (snd L) t\<close> \<open>cwidth ws (snd L) t = w\<close> \<open>push_m L t w = (L', k)\<close>
    \<open>cws_le ws (snd L) t M\<close> \<open>length (csubterms t) \<le> n\<close>
  shows \<open>lcost ws L' \<le> lcost ws L + 1 + n * (M + 1) ^ 2\<close>
proof -
  have \<open>cterm_weight ws (snd L) t \<le> n * (M + 1) ^ 2\<close>
    using cterm_weight_le[OF assms(5)] assms(6) by (meson le_trans mult_le_mono1)
  then show ?thesis using lcost_push[OF assms(1-4)] by simp
qed

subsection \<open>The cost of the operations\<close>

text \<open>Rewriting a binary operation adds at most \<open>3\<close> definitions, each of at most \<open>50\<close> nodes of
  widths at most \<open>wa + wb\<close>.\<close>
lemma lower_bin_cost:
  assumes EA: \<open>env_ok ws L ka wa\<close> and EB: \<open>env_ok ws L kb wb\<close>
    and eqw: \<open>op \<noteq> Op_Concat \<longrightarrow> wb = wa\<close>
    and R: \<open>lower_bin_m L op ka kb = (L', k)\<close>
    and B: \<open>length (fst L') < 2 ^ 56\<close>
  shows \<open>lcost ws L' \<le> lcost ws L + 3 + 150 * (wa + wb + 1) ^ 2\<close>
proof -
  let ?M = \<open>wa + wb\<close>
  have L: \<open>lok ws L\<close> and wa: \<open>snd L ! ka = wa\<close> and wb: \<open>snd L ! kb = wb\<close> and wa1: \<open>1 \<le> wa\<close> and wb1: \<open>1 \<le> wb\<close>
    and wa64: \<open>wa < 2 ^ 64\<close> and wb64: \<open>wb < 2 ^ 64\<close> and ka64: \<open>ka < 2 ^ 64\<close> and kb64: \<open>kb < 2 ^ 64\<close>
    and wa56: \<open>wa < 2 ^ 56\<close>
    using EA EB by (simp_all add: env_ok_def)
  have EBa: \<open>op \<noteq> Op_Concat \<Longrightarrow> env_ok ws L kb wa\<close> using EB eqw by simp
  note A = cr_env[OF EA] neg_t_env[OF EA] msb_t_env[OF EA] abs_t_env[OF EA]
    cr_env[OF EB] neg_t_env[OF EBa] msb_t_env[OF EBa] abs_t_env[OF EBa] slt_t_env[OF EA EBa] sle_t_env[OF EA EBa]
    slt_t_env[OF EBa EA] sle_t_env[OF EBa EA]
  note W = cws_le_intros neg_t_le msb_t_le abs_t_le slt_t_le sle_t_le
  note N = neg_t_len msb_t_len abs_t_len slt_t_len sle_t_len one_t_len
  have M1: \<open>1 \<le> ?M\<close> using wa1 by simp
  note M = M1 Suc_0_le[OF M1] one_le_add[OF wa1] one_le_add[OF wb1] Suc_0_le[OF wa1] Suc_0_le[OF wb1]
  \<comment> \<open>A single push of a term of at most 50 nodes.\<close>
  note ks = ka64[simplified] kb64[simplified] wa64[simplified] wb64[simplified]
  have one: \<open>\<And>t w. cws_le ws (snd L) t ?M \<Longrightarrow> lower_bin_m L op ka kb = push_m L t w \<Longrightarrow> cwt ws (snd L) t \<Longrightarrow>
      cwidth ws (snd L) t = w \<Longrightarrow> length (csubterms t) \<le> 50 \<Longrightarrow> lcost ws L' \<le> lcost ws L + 3 + 150 * (?M + 1) ^ 2\<close>
  proof -
    fix t w assume H: \<open>cws_le ws (snd L) t ?M\<close> \<open>lower_bin_m L op ka kb = push_m L t w\<close> \<open>cwt ws (snd L) t\<close>
      \<open>cwidth ws (snd L) t = w\<close> \<open>length (csubterms t) \<le> 50\<close>
    have p: \<open>push_m L t w = (L', k)\<close> using R H(2) by simp
    show \<open>lcost ws L' \<le> lcost ws L + 3 + 150 * (?M + 1) ^ 2\<close> using push_cost[OF L H(3,4) p H(1,5)] by simp
  qed
  show ?thesis
  proof (cases op)
    case Op_And
    show ?thesis by (rule one[of \<open>CoreTermL_Bin BinOp_And (cr ka) (cr kb)\<close> wa], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_And lower_bin_m_def wa wb A eqw)
  next
    case Op_Or
    show ?thesis by (rule one[of \<open>CoreTermL_Bin BinOp_Or (cr ka) (cr kb)\<close> wa], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Or lower_bin_m_def wa wb A eqw)
  next
    case Op_Xor
    show ?thesis by (rule one[of \<open>CoreTermL_Bin BinOp_Xor (cr ka) (cr kb)\<close> wa], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Xor lower_bin_m_def wa wb A eqw)
  next
    case Op_Nand
    show ?thesis by (rule one[of \<open>CoreTermL_Not (CoreTermL_Bin BinOp_And (cr ka) (cr kb))\<close> wa], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Nand lower_bin_m_def wa wb A eqw)
  next
    case Op_Nor
    show ?thesis by (rule one[of \<open>CoreTermL_Not (CoreTermL_Bin BinOp_Or (cr ka) (cr kb))\<close> wa], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Nor lower_bin_m_def wa wb A eqw)
  next
    case Op_Xnor
    show ?thesis by (rule one[of \<open>CoreTermL_Not (CoreTermL_Bin BinOp_Xor (cr ka) (cr kb))\<close> wa], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Xnor lower_bin_m_def wa wb A eqw)
  next
    case Op_Comp
    show ?thesis by (rule one[of \<open>CoreTermL_Bin BinOp_Eq (cr ka) (cr kb)\<close> 1], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Comp lower_bin_m_def wa wb A eqw)
  next
    case Op_Add
    show ?thesis by (rule one[of \<open>CoreTermL_Bin BinOp_Add (cr ka) (cr kb)\<close> wa], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Add lower_bin_m_def wa wb A eqw)
  next
    case Op_Sub
    show ?thesis by (rule one[of \<open>CoreTermL_Bin BinOp_Add (cr ka) (neg_t kb wa)\<close> wa], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Sub lower_bin_m_def wa wb A N eqw)
  next
    case Op_Mul
    show ?thesis by (rule one[of \<open>CoreTermL_Bin BinOp_Mul (cr ka) (cr kb)\<close> wa], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Mul lower_bin_m_def wa wb A eqw)
  next
    case Op_Udiv
    show ?thesis by (rule one[of \<open>CoreTermL_Bin BinOp_Udiv (cr ka) (cr kb)\<close> wa], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Udiv lower_bin_m_def wa wb A eqw)
  next
    case Op_Urem
    show ?thesis by (rule one[of \<open>CoreTermL_Bin BinOp_Urem (cr ka) (cr kb)\<close> wa], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Urem lower_bin_m_def wa wb A eqw)
  next
    case Op_Shl
    show ?thesis by (rule one[of \<open>CoreTermL_Bin BinOp_Shl (cr ka) (cr kb)\<close> wa], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Shl lower_bin_m_def wa wb A eqw)
  next
    case Op_Lshr
    show ?thesis by (rule one[of \<open>CoreTermL_Bin BinOp_Lshr (cr ka) (cr kb)\<close> wa], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Lshr lower_bin_m_def wa wb A eqw)
  next
    case Op_Ashr
    show ?thesis by (rule one[of \<open>CoreTermL_Ite (msb_t ka wa)
          (CoreTermL_Not (CoreTermL_Bin BinOp_Lshr (CoreTermL_Not (cr ka)) (cr kb)))
          (CoreTermL_Bin BinOp_Lshr (cr ka) (cr kb))\<close> wa])
        (simp_all add: Op_Ashr lower_bin_m_def wa wb A N eqw, (intro W; simp add: wa wb ks M wa1 unat_wn eqw[simplified Op_Ashr, simplified])?)
  next
    case Op_Concat
    show ?thesis by (rule one[of \<open>CoreTermL_Bin BinOp_Concat (cr ka) (cr kb)\<close> \<open>wa + wb\<close>], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Concat lower_bin_m_def wa wb A eqw)
  next
    case Op_Eq
    show ?thesis by (rule one[of \<open>CoreTermL_Bin BinOp_Eq (cr ka) (cr kb)\<close> 1], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Eq lower_bin_m_def wa wb A eqw)
  next
    case Op_Distinct
    show ?thesis by (rule one[of \<open>CoreTermL_Not (CoreTermL_Bin BinOp_Eq (cr ka) (cr kb))\<close> 1], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Distinct lower_bin_m_def wa wb A eqw)
  next
    case Op_Ult
    show ?thesis by (rule one[of \<open>CoreTermL_Bin BinOp_Ult (cr ka) (cr kb)\<close> 1], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Ult lower_bin_m_def wa wb A eqw)
  next
    case Op_Ule
    show ?thesis by (rule one[of \<open>CoreTermL_Not (CoreTermL_Bin BinOp_Ult (cr kb) (cr ka))\<close> 1], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Ule lower_bin_m_def wa wb A eqw)
  next
    case Op_Ugt
    show ?thesis by (rule one[of \<open>CoreTermL_Bin BinOp_Ult (cr kb) (cr ka)\<close> 1], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Ugt lower_bin_m_def wa wb A eqw)
  next
    case Op_Uge
    show ?thesis by (rule one[of \<open>CoreTermL_Not (CoreTermL_Bin BinOp_Ult (cr ka) (cr kb))\<close> 1], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Uge lower_bin_m_def wa wb A eqw)
  next
    case Op_Slt
    show ?thesis by (rule one[of \<open>slt_t ka kb wa\<close> 1], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Slt lower_bin_m_def wa wb A N eqw)
  next
    case Op_Sle
    show ?thesis by (rule one[of \<open>sle_t ka kb wa\<close> 1], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Sle lower_bin_m_def wa wb A N eqw)
  next
    case Op_Sgt
    show ?thesis by (rule one[of \<open>slt_t kb ka wa\<close> 1], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Sgt lower_bin_m_def wa wb A N eqw)
  next
    case Op_Sge
    show ?thesis by (rule one[of \<open>sle_t kb ka wa\<close> 1], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Sge lower_bin_m_def wa wb A N eqw)
  next
    case Op_Sdiv
    have wba: \<open>wb = wa\<close> using eqw Op_Sdiv by simp
    have ne: \<open>op \<noteq> Op_Concat\<close> using Op_Sdiv by simp
    note EB' = EBa[OF ne]
    let ?t1 = \<open>CoreTermL_Bin BinOp_Udiv (abs_t ka wa) (abs_t kb wa)\<close>
    obtain L1 q where p1: \<open>push_m L ?t1 wa = (L1, q)\<close> by (cases \<open>push_m L ?t1 wa\<close>)
    let ?t2 = \<open>CoreTermL_Ite (CoreTermL_Bin BinOp_Xor (msb_t ka wa) (msb_t kb wa)) (neg_t q wa) (cr q)\<close>
    have p2: \<open>push_m L1 ?t2 wa = (L', k)\<close> using R p1 by (simp add: Op_Sdiv lower_bin_m_def wa)
    have t1: \<open>cwt ws (snd L) ?t1\<close> \<open>cwidth ws (snd L) ?t1 = wa\<close> using abs_t_env[OF EA] abs_t_env[OF EB'] by simp_all
    have c1: \<open>cws_le ws (snd L) ?t1 ?M\<close> by (intro W) (simp_all add: wa wb ks M wa1 wba)
    have n1: \<open>length (csubterms ?t1) \<le> 50\<close> by (simp add: N)
    note C1 = push_cost[OF L t1 p1 c1 n1]
    note P1 = push_correct[OF L t1 p1, of \<open>\<lambda>vs. 0\<close>]
    have L1: \<open>lok ws L1\<close> using lext_push[OF L t1 p1] lext_lok by blast
    have EQ: \<open>env_ok ws L1 q wa\<close>
      using env_push[OF L t1 p1 wa1 wa56] B pfx_length[OF pfx_push[OF p2]] by simp
    have EA1: \<open>env_ok ws L1 ka wa\<close> and EB1: \<open>env_ok ws L1 kb wa\<close>
      using env_lext[OF EA lext_push[OF L t1 p1]] env_lext[OF EB' lext_push[OF L t1 p1]] by simp_all
    have t2: \<open>cwt ws (snd L1) ?t2\<close> \<open>cwidth ws (snd L1) ?t2 = wa\<close>
      using msb_t_env[OF EA1] msb_t_env[OF EB1] neg_t_env[OF EQ] cr_env[OF EQ] by simp_all
    have q64: \<open>q < 2 ^ 64\<close> and wq: \<open>snd L1 ! q = wa\<close> and wa1': \<open>snd L1 ! ka = wa\<close> and wb1': \<open>snd L1 ! kb = wa\<close>
      using EQ EA1 EB1 by (simp_all add: env_ok_def)
    have c2: \<open>cws_le ws (snd L1) ?t2 ?M\<close> by (intro W) (simp_all add: wq wa1' wb1' ks q64[simplified] M wa1)
    have n2: \<open>length (csubterms ?t2) \<le> 50\<close> by (simp add: N)
    note C2 = push_cost[OF L1 t2 p2 c2 n2]
    show ?thesis using C1 C2 by simp
  next
    case Op_Srem
    have wba: \<open>wb = wa\<close> using eqw Op_Srem by simp
    have ne: \<open>op \<noteq> Op_Concat\<close> using Op_Srem by simp
    note EB' = EBa[OF ne]
    let ?t1 = \<open>CoreTermL_Bin BinOp_Urem (abs_t ka wa) (abs_t kb wa)\<close>
    obtain L1 r where p1: \<open>push_m L ?t1 wa = (L1, r)\<close> by (cases \<open>push_m L ?t1 wa\<close>)
    let ?t2 = \<open>CoreTermL_Ite (msb_t ka wa) (neg_t r wa) (cr r)\<close>
    have p2: \<open>push_m L1 ?t2 wa = (L', k)\<close> using R p1 by (simp add: Op_Srem lower_bin_m_def wa)
    have t1: \<open>cwt ws (snd L) ?t1\<close> \<open>cwidth ws (snd L) ?t1 = wa\<close> using abs_t_env[OF EA] abs_t_env[OF EB'] by simp_all
    have c1: \<open>cws_le ws (snd L) ?t1 ?M\<close> by (intro W) (simp_all add: wa wb ks M wa1 wba)
    have n1: \<open>length (csubterms ?t1) \<le> 50\<close> by (simp add: N)
    note C1 = push_cost[OF L t1 p1 c1 n1]
    have L1: \<open>lok ws L1\<close> using lext_push[OF L t1 p1] lext_lok by blast
    have ER: \<open>env_ok ws L1 r wa\<close>
      using env_push[OF L t1 p1 wa1 wa56] B pfx_length[OF pfx_push[OF p2]] by simp
    have EA1: \<open>env_ok ws L1 ka wa\<close> using env_lext[OF EA lext_push[OF L t1 p1]] by simp
    have t2: \<open>cwt ws (snd L1) ?t2\<close> \<open>cwidth ws (snd L1) ?t2 = wa\<close>
      using msb_t_env[OF EA1] neg_t_env[OF ER] cr_env[OF ER] by simp_all
    have r64: \<open>r < 2 ^ 64\<close> and wr: \<open>snd L1 ! r = wa\<close> and wa1': \<open>snd L1 ! ka = wa\<close>
      using ER EA1 by (simp_all add: env_ok_def)
    have c2: \<open>cws_le ws (snd L1) ?t2 ?M\<close> by (intro W) (simp_all add: wr wa1' ks r64[simplified] M wa1)
    have n2: \<open>length (csubterms ?t2) \<le> 50\<close> by (simp add: N)
    note C2 = push_cost[OF L1 t2 p2 c2 n2]
    show ?thesis using C1 C2 by simp
  next
    case Op_Smod
    have wba: \<open>wb = wa\<close> using eqw Op_Smod by simp
    have ne: \<open>op \<noteq> Op_Concat\<close> using Op_Smod by simp
    note EB' = EBa[OF ne]
    let ?t1 = \<open>CoreTermL_Bin BinOp_Urem (abs_t ka wa) (abs_t kb wa)\<close>
    obtain L1 u where p1: \<open>push_m L ?t1 wa = (L1, u)\<close> by (cases \<open>push_m L ?t1 wa\<close>)
    obtain L2 nu where p2: \<open>push_m L1 (neg_t u wa) wa = (L2, nu)\<close> by (cases \<open>push_m L1 (neg_t u wa) wa\<close>)
    let ?t3 = \<open>CoreTermL_Ite (CoreTermL_Bin BinOp_Eq (cr u) (CoreTermL_Const (replicate wa False))) (cr u)
          (CoreTermL_Ite (msb_t ka wa)
             (CoreTermL_Ite (msb_t kb wa) (cr nu) (CoreTermL_Bin BinOp_Add (cr nu) (cr kb)))
             (CoreTermL_Ite (msb_t kb wa) (CoreTermL_Bin BinOp_Add (cr u) (cr kb)) (cr u)))\<close>
    have p3: \<open>push_m L2 ?t3 wa = (L', k)\<close> using R p1 p2 by (simp add: Op_Smod lower_bin_m_def wa)
    have t1: \<open>cwt ws (snd L) ?t1\<close> \<open>cwidth ws (snd L) ?t1 = wa\<close> using abs_t_env[OF EA] abs_t_env[OF EB'] by simp_all
    have c1: \<open>cws_le ws (snd L) ?t1 ?M\<close> by (intro W) (simp_all add: wa wb ks M wa1 wba)
    have n1: \<open>length (csubterms ?t1) \<le> 50\<close> by (simp add: N)
    note C1 = push_cost[OF L t1 p1 c1 n1]
    have X1: \<open>lext ws L L1\<close> using lext_push[OF L t1 p1] .
    have L1: \<open>lok ws L1\<close> using X1 lext_lok by blast
    have EU: \<open>env_ok ws L1 u wa\<close>
      using env_push[OF L t1 p1 wa1 wa56] B pfx_length[OF pfx_push[OF p2]] pfx_length[OF pfx_push[OF p3]] by simp
    have t2: \<open>cwt ws (snd L1) (neg_t u wa)\<close> \<open>cwidth ws (snd L1) (neg_t u wa) = wa\<close> using neg_t_env[OF EU] by simp_all
    have u64: \<open>u < 2 ^ 64\<close> and wu: \<open>snd L1 ! u = wa\<close> using EU by (simp_all add: env_ok_def)
    have c2: \<open>cws_le ws (snd L1) (neg_t u wa) ?M\<close> by (intro W neg_t_le) (simp_all add: wu u64[simplified] M wa1)
    have n2: \<open>length (csubterms (neg_t u wa)) \<le> 50\<close> by (simp add: N)
    note C2 = push_cost[OF L1 t2 p2 c2 n2]
    have X2: \<open>lext ws L1 L2\<close> using lext_push[OF L1 t2 p2] .
    have L2: \<open>lok ws L2\<close> using X2 lext_lok by blast
    have ENU: \<open>env_ok ws L2 nu wa\<close>
      using env_push[OF L1 t2 p2 wa1 wa56] B pfx_length[OF pfx_push[OF p3]] by simp
    have EU2: \<open>env_ok ws L2 u wa\<close> using env_lext[OF EU X2] .
    have EA2: \<open>env_ok ws L2 ka wa\<close> and EB2: \<open>env_ok ws L2 kb wa\<close>
      using env_lext[OF env_lext[OF EA X1] X2] env_lext[OF env_lext[OF EB' X1] X2] by simp_all
    have t3: \<open>cwt ws (snd L2) ?t3\<close> \<open>cwidth ws (snd L2) ?t3 = wa\<close>
      using msb_t_env[OF EA2] msb_t_env[OF EB2] cr_env[OF EU2] cr_env[OF ENU] cr_env[OF EB2] by simp_all
    have nu64: \<open>nu < 2 ^ 64\<close> and wnu: \<open>snd L2 ! nu = wa\<close> and wu2: \<open>snd L2 ! u = wa\<close> and wa2: \<open>snd L2 ! ka = wa\<close>
      and wb2: \<open>snd L2 ! kb = wa\<close>
      using ENU EU2 EA2 EB2 by (simp_all add: env_ok_def)
    have c3: \<open>cws_le ws (snd L2) ?t3 ?M\<close> by (intro W) (simp_all add: wnu wu2 wa2 wb2 ks u64[simplified] nu64[simplified] M wa1)
    have n3: \<open>length (csubterms ?t3) \<le> 50\<close> by (simp add: N)
    note C3 = push_cost[OF L2 t3 p3 c3 n3]
    show ?thesis using C1 C2 C3 by simp
  qed
qed

text \<open>The loop for \<open>repeat\<close>: each iteration pushes a concatenation of three nodes of widths at most
  the final width.\<close>
lemma repeat_loop_cost:
  assumes EA: \<open>env_ok ws L ka wa\<close>
  shows \<open>lext ws L Lj \<Longrightarrow> kj < length (fst Lj) \<Longrightarrow> snd Lj ! kj = acc0 \<Longrightarrow> acc0 = wa * j \<Longrightarrow>
    foldl (repeat_step ka wa) (Lj, kj, acc0) js = (L3, k3, acc) \<Longrightarrow> bnd L3 \<Longrightarrow>
    wa * (j + length js) \<le> W \<Longrightarrow>
    lcost ws L3 \<le> lcost ws Lj + length js * (1 + 3 * (W + 1) ^ 2)\<close>
proof (induction js arbitrary: Lj kj j acc0)
  case Nil
  then show ?case by simp
next
  case (Cons x js)
  let ?t = \<open>CoreTermL_Bin BinOp_Concat (cr ka) (cr kj)\<close>
  obtain Lj' kj' where p: \<open>push_m Lj ?t (acc0 + wa) = (Lj', kj')\<close> by (cases \<open>push_m Lj ?t (acc0 + wa)\<close>)
  have f: \<open>foldl (repeat_step ka wa) (Lj', kj', acc0 + wa) js = (L3, k3, acc)\<close>
    using Cons.prems(5) p by (simp add: repeat_step_def)
  have acc: \<open>acc0 + wa = wa * Suc j\<close> using Cons.prems(4) by (simp add: mult_Suc)
  have Lj: \<open>lok ws Lj\<close> using Cons.prems(1) lext_lok by blast
  have B': \<open>bnd Lj'\<close> using bnd_pfx[OF repeat_fold_pfx[OF f] Cons.prems(6)] .
  have kj64: \<open>kj < 2 ^ 64\<close> using Cons.prems(2) B' pfx_length[OF pfx_push[OF p]] by (simp add: bnd_def)
  have EAj: \<open>env_ok ws Lj ka wa\<close> using env_lext[OF EA Cons.prems(1)] .
  have ka64: \<open>ka < 2 ^ 64\<close> and waj: \<open>snd Lj ! ka = wa\<close> and wa1: \<open>1 \<le> wa\<close> using EAj by (simp_all add: env_ok_def)
  have kjl: \<open>kj < length (snd Lj)\<close> using Cons.prems(2) lok_length[OF Lj] by simp
  have t: \<open>cwt ws (snd Lj) ?t\<close> \<open>cwidth ws (snd Lj) ?t = acc0 + wa\<close>
    using cr_env[OF EAj] cr_wt[OF kjl kj64] cr_width[OF kj64] Cons.prems(3) by (simp_all add: add.commute)
  have m1: \<open>wa * (j + 1) \<le> wa * (j + length (x # js))\<close> by (rule mult_le_mono2) simp
  have m2: \<open>wa * (j + 1) = wa * j + wa\<close> by simp
  have Wb1: \<open>acc0 + wa \<le> W\<close> using m1 m2 Cons.prems(4,7) by linarith
  have Wb2: \<open>wa \<le> W\<close> using m1 m2 Cons.prems(7) by linarith
  have Wb3: \<open>acc0 \<le> W\<close> using m1 m2 Cons.prems(4,7) by linarith
  note Wb = Wb1 Wb2 Wb3
  have c: \<open>cws_le ws (snd Lj) ?t W\<close>
  proof (rule cws_le_Bin)
    show \<open>cws_le ws (snd Lj) (cr ka) W\<close> by (rule cws_le_cr[OF ka64]) (simp add: waj Wb2)
    show \<open>cws_le ws (snd Lj) (cr kj) W\<close> by (rule cws_le_cr[OF kj64]) (simp add: Cons.prems(3) Wb3)
    show \<open>1 \<le> W\<close> using wa1 Wb2 by linarith
    show \<open>BinOp_Concat = BinOp_Concat \<longrightarrow> cwidth ws (snd Lj) (cr ka) + cwidth ws (snd Lj) (cr kj) \<le> W\<close>
      using Wb1 by (simp add: cr_width[OF ka64] cr_width[OF kj64] waj Cons.prems(3) add.commute)
  qed
  have n: \<open>length (csubterms ?t) \<le> 3\<close> by simp
  note C = push_cost[OF Lj t p c n]
  have \<open>lext ws L Lj'\<close> using Cons.prems(1) lext_push[OF Lj t p] lext_trans by blast
  note IH = Cons.IH[OF this _ _ acc f Cons.prems(6)]
  note P = push_ok[OF Lj t p]
  have kj'l: \<open>kj' < length (fst Lj')\<close> and wkj': \<open>snd Lj' ! kj' = acc0 + wa\<close>
    using P(2-4) lok_length[OF Lj, symmetric] by simp_all
  have \<open>wa * (Suc j + length js) \<le> W\<close> using Cons.prems(7) by simp
  then show ?case using IH[OF kj'l wkj'] C by simp
qed

subsection \<open>The cost of a term\<close>

text \<open>The budget of a subterm of width \<open>w\<close> is \<open>K * (w + 1)^3\<close>; a term whose rewriting ends in \<open>L'\<close>
  has used at most twice its weight, leaving its own budget unused for the parent.\<close>
definition K :: nat where \<open>K \<equiv> 400\<close>

lemma sq_le_cube: \<open>(w + 1) ^ 2 \<le> (w + 1) ^ 3\<close> for w :: nat
  by (simp add: power_increasing)

lemma sum_sq_le: \<open>(a + b + 1) ^ 2 \<le> 2 * (a + 1) ^ 2 + 2 * (b + 1) ^ 2\<close> for a b :: nat
proof -
  have \<open>(a + b + 1) ^ 2 \<le> ((a + 1) + (b + 1)) ^ 2\<close> by (simp add: power_mono)
  also have \<open>\<dots> \<le> 2 * (a + 1) ^ 2 + 2 * (b + 1) ^ 2\<close>
  proof -
    have \<open>\<And>x y :: nat. x \<le> y \<Longrightarrow> (x + y) ^ 2 \<le> 2 * x ^ 2 + 2 * y ^ 2\<close>
    proof -
      fix x y :: nat assume \<open>x \<le> y\<close>
      then obtain d where \<open>y = x + d\<close> using le_Suc_ex by blast
      then show \<open>(x + y) ^ 2 \<le> 2 * x ^ 2 + 2 * y ^ 2\<close> by (simp add: power2_eq_square algebra_simps)
    qed
    note X = this
    show ?thesis
    proof (cases \<open>a + 1 \<le> b + 1\<close>)
      case True
      then show ?thesis using X[of \<open>a + 1\<close> \<open>b + 1\<close>] by simp
    next
      case False
      then have \<open>b + 1 \<le> a + 1\<close> by simp
      then show ?thesis using X[of \<open>b + 1\<close> \<open>a + 1\<close>] by (simp add: add.commute)
    qed
  qed
  finally show ?thesis .
qed

text \<open>The weight of a term is the cube of its width plus one, plus the weights of its operands.\<close>
lemma tw_leaf:
  \<open>term_weight ws ds (TermL_Const bs) = (width ws ds (TermL_Const bs) + 1) ^ 3\<close>
  \<open>term_weight ws ds (TermL_Var i) = (width ws ds (TermL_Var i) + 1) ^ 3\<close>
  \<open>term_weight ws ds (TermL_Ref j) = (width ws ds (TermL_Ref j) + 1) ^ 3\<close>
  by (simp_all add: term_weight_def)

lemma tw_un:
  \<open>term_weight ws ds (TermL_Not a) = (width ws ds (TermL_Not a) + 1) ^ 3 + term_weight ws ds a\<close>
  \<open>term_weight ws ds (TermL_Neg a) = (width ws ds (TermL_Neg a) + 1) ^ 3 + term_weight ws ds a\<close>
  \<open>term_weight ws ds (TermL_Extract hi lo a) = (width ws ds (TermL_Extract hi lo a) + 1) ^ 3 + term_weight ws ds a\<close>
  \<open>term_weight ws ds (TermL_Repeat i a) = (width ws ds (TermL_Repeat i a) + 1) ^ 3 + term_weight ws ds a\<close>
  \<open>term_weight ws ds (TermL_ZeroExtend i a) = (width ws ds (TermL_ZeroExtend i a) + 1) ^ 3 + term_weight ws ds a\<close>
  \<open>term_weight ws ds (TermL_SignExtend i a) = (width ws ds (TermL_SignExtend i a) + 1) ^ 3 + term_weight ws ds a\<close>
  \<open>term_weight ws ds (TermL_RotateLeft i a) = (width ws ds (TermL_RotateLeft i a) + 1) ^ 3 + term_weight ws ds a\<close>
  \<open>term_weight ws ds (TermL_RotateRight i a) = (width ws ds (TermL_RotateRight i a) + 1) ^ 3 + term_weight ws ds a\<close>
  by (simp_all add: term_weight_def)

lemma tw_Bin:
  \<open>term_weight ws ds (TermL_Bin op a b) = (width ws ds (TermL_Bin op a b) + 1) ^ 3 + term_weight ws ds a + term_weight ws ds b\<close>
  by (simp add: term_weight_def)

lemma tw_Ite:
  \<open>term_weight ws ds (TermL_Ite c a b) = (width ws ds (TermL_Ite c a b) + 1) ^ 3 + term_weight ws ds c + term_weight ws ds a + term_weight ws ds b\<close>
  by (simp add: term_weight_def)

lemma cube1: \<open>1 \<le> (w + 1) ^ 3\<close> for w :: nat
  by simp

lemma cube_mono: \<open>a \<le> b \<Longrightarrow> (a + 1) ^ 3 \<le> (b + 1) ^ 3\<close> for a b :: nat
  by (simp add: power_mono)

lemma lower_m_cost:
  assumes \<open>wt ws ds t\<close> \<open>lok ws L\<close> \<open>dm_ok ds dm L\<close> \<open>lower_m ws dm L t = (L', k)\<close> \<open>bnd L'\<close>
  shows \<open>lcost ws L' + K * (width ws ds t + 1) ^ 3 \<le> lcost ws L + 2 * K * term_weight ws ds t\<close>
  using assms
proof (induction t arbitrary: L L' k)
  case (TermL_Const bs)
  have p: \<open>push_m L (CoreTermL_Const bs) (length bs) = (L', k)\<close> using TermL_Const.prems(4) by simp
  have c: \<open>cws_le ws (snd L) (CoreTermL_Const bs) (length bs)\<close> by (simp add: cws_le_def)
  have C: \<open>lcost ws L' \<le> lcost ws L + 1 + 1 * (length bs + 1) ^ 2\<close> using push_cost[OF TermL_Const.prems(2) _ _ p c, of 1] by simp
  show ?case using C sq_le_cube[of \<open>length bs\<close>] cube1[of \<open>length bs\<close>] unfolding tw_leaf K_def width.simps by linarith
next
  case (TermL_Var i)
  have p: \<open>push_m L (CoreTermL_Var i) (ws ! unat i) = (L', k)\<close> using TermL_Var.prems(4) by simp
  have wt: \<open>unat i < length ws\<close> using TermL_Var.prems(1) by simp
  have c: \<open>cws_le ws (snd L) (CoreTermL_Var i) (ws ! unat i)\<close> by (simp add: cws_le_def)
  have C: \<open>lcost ws L' \<le> lcost ws L + 1 + 1 * (ws ! unat i + 1) ^ 2\<close> using push_cost[OF TermL_Var.prems(2) _ _ p c, of 1] wt by simp
  show ?case using C sq_le_cube[of \<open>ws ! unat i\<close>] cube1[of \<open>ws ! unat i\<close>] unfolding tw_leaf K_def width.simps by linarith
next
  case (TermL_Ref j)
  have \<open>L' = L\<close> using TermL_Ref.prems(4) by simp
  then show ?case unfolding tw_leaf K_def by simp
next
  case (TermL_Not a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  have p: \<open>push_m L1 (CoreTermL_Not (cr ka)) (snd L1 ! ka) = (L', k)\<close> using TermL_Not.prems(4) a by simp
  have B1: \<open>bnd L1\<close> using bnd_pfx[OF pfx_push[OF p] TermL_Not.prems(5)] .
  have wta: \<open>wt ws ds a\<close> using TermL_Not.prems(1) by simp
  note IH = TermL_Not.IH[OF wta TermL_Not.prems(2,3) a B1]
  note S = lower_m_correct[OF wta TermL_Not.prems(2,3) a B1]
  have EA: \<open>env_ok ws L1 ka (width ws ds a)\<close> using S by simp
  have L1: \<open>lok ws L1\<close> and wa: \<open>snd L1 ! ka = width ws ds a\<close> and ka64: \<open>ka < 2 ^ 64\<close> using EA by (simp_all add: env_ok_def)
  have t: \<open>cwt ws (snd L1) (CoreTermL_Not (cr ka))\<close> \<open>cwidth ws (snd L1) (CoreTermL_Not (cr ka)) = snd L1 ! ka\<close>
    using cr_env[OF EA] wa by simp_all
  have c: \<open>cws_le ws (snd L1) (CoreTermL_Not (cr ka)) (width ws ds a)\<close> by (intro cws_le_intros) (simp_all add: ka64[simplified] wa)
  have C: \<open>lcost ws L' \<le> lcost ws L1 + 1 + 2 * (width ws ds a + 1) ^ 2\<close> using push_cost[OF L1 t p c, of 2] by simp
  show ?case using IH[unfolded K_def] C sq_le_cube[of \<open>width ws ds a\<close>] cube1[of \<open>width ws ds a\<close>]
    unfolding tw_un K_def add_mult_distrib2 width.simps by linarith
next
  case (TermL_Neg a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  have p: \<open>push_m L1 (neg_t ka (snd L1 ! ka)) (snd L1 ! ka) = (L', k)\<close> using TermL_Neg.prems(4) a by simp
  have B1: \<open>bnd L1\<close> using bnd_pfx[OF pfx_push[OF p] TermL_Neg.prems(5)] .
  have wta: \<open>wt ws ds a\<close> using TermL_Neg.prems(1) by simp
  note IH = TermL_Neg.IH[OF wta TermL_Neg.prems(2,3) a B1]
  note S = lower_m_correct[OF wta TermL_Neg.prems(2,3) a B1]
  have EA: \<open>env_ok ws L1 ka (width ws ds a)\<close> using S by simp
  have L1: \<open>lok ws L1\<close> and wa: \<open>snd L1 ! ka = width ws ds a\<close> and ka64: \<open>ka < 2 ^ 64\<close> and wa1: \<open>1 \<le> width ws ds a\<close>
    using EA by (simp_all add: env_ok_def)
  have t: \<open>cwt ws (snd L1) (neg_t ka (snd L1 ! ka))\<close> \<open>cwidth ws (snd L1) (neg_t ka (snd L1 ! ka)) = snd L1 ! ka\<close>
    using neg_t_env[OF EA] wa by simp_all
  have c: \<open>cws_le ws (snd L1) (neg_t ka (snd L1 ! ka)) (width ws ds a)\<close> by (intro neg_t_le) (simp_all add: ka64[simplified] wa wa1 Suc_0_le[OF wa1])
  have C: \<open>lcost ws L' \<le> lcost ws L1 + 1 + 6 * (width ws ds a + 1) ^ 2\<close> using push_cost[OF L1 t p c, of 6] by (simp add: neg_t_len)
  show ?case using IH[unfolded K_def] C sq_le_cube[of \<open>width ws ds a\<close>] cube1[of \<open>width ws ds a\<close>]
    unfolding tw_un K_def add_mult_distrib2 width.simps by linarith
next
  case (TermL_Bin op a b)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  obtain L2 kb where b: \<open>lower_m ws dm L1 b = (L2, kb)\<close> by (cases \<open>lower_m ws dm L1 b\<close>)
  have R: \<open>lower_bin_m L2 op ka kb = (L', k)\<close> using TermL_Bin.prems(4) a b by simp
  have B2: \<open>bnd L2\<close> using bnd_pfx[OF lower_bin_m_pfx[OF R] TermL_Bin.prems(5)] .
  have B1: \<open>bnd L1\<close> using bnd_pfx[OF lower_m_pfx[OF b] B2] .
  have wt: \<open>wt ws ds a\<close> \<open>wt ws ds b\<close> \<open>op \<noteq> Op_Concat \<longrightarrow> width ws ds b = width ws ds a\<close>
    using TermL_Bin.prems(1) by simp_all
  note IHa = TermL_Bin.IH(1)[OF wt(1) TermL_Bin.prems(2,3) a B1]
  note Sa = lower_m_correct[OF wt(1) TermL_Bin.prems(2,3) a B1]
  have L1: \<open>lok ws L1\<close> and X1: \<open>lext ws L L1\<close> using Sa lext_lok by blast+
  note IHb = TermL_Bin.IH(2)[OF wt(2) L1 dm_ok_lext[OF TermL_Bin.prems(2,3) X1] b B2]
  note Sb = lower_m_correct[OF wt(2) L1 dm_ok_lext[OF TermL_Bin.prems(2,3) X1] b B2]
  have X2: \<open>lext ws L1 L2\<close> using Sb by blast
  have EA: \<open>env_ok ws L2 ka (width ws ds a)\<close> using Sa env_lext[OF _ X2] by blast
  have EB: \<open>env_ok ws L2 kb (width ws ds b)\<close> using Sb by blast
  note C = lower_bin_cost[OF EA EB wt(3) R TermL_Bin.prems(5)[unfolded bnd_def, THEN conjunct1]]
  let ?wa = \<open>width ws ds a\<close> and ?wb = \<open>width ws ds b\<close>
  have s: \<open>(?wa + ?wb + 1) ^ 2 \<le> 2 * (?wa + 1) ^ 3 + 2 * (?wb + 1) ^ 3\<close>
    using sum_sq_le[of ?wa ?wb] sq_le_cube[of ?wa] sq_le_cube[of ?wb] by linarith
  show ?case using IHa[unfolded K_def] IHb[unfolded K_def] C s cube1[of \<open>width ws ds (TermL_Bin op a b)\<close>]
    unfolding tw_Bin K_def add_mult_distrib2 by linarith
next
  case (TermL_Extract hi lo a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  let ?t = \<open>CoreTermL_Extract hi lo (cr ka)\<close> and ?w = \<open>unat hi - unat lo + 1\<close>
  have p: \<open>push_m L1 ?t ?w = (L', k)\<close> using TermL_Extract.prems(4) a by simp
  have B1: \<open>bnd L1\<close> using bnd_pfx[OF pfx_push[OF p] TermL_Extract.prems(5)] .
  have wt: \<open>wt ws ds a\<close> \<open>unat lo \<le> unat hi\<close> \<open>unat hi < width ws ds a\<close> using TermL_Extract.prems(1) by simp_all
  note IH = TermL_Extract.IH[OF wt(1) TermL_Extract.prems(2,3) a B1]
  note S = lower_m_correct[OF wt(1) TermL_Extract.prems(2,3) a B1]
  have EA: \<open>env_ok ws L1 ka (width ws ds a)\<close> using S by simp
  have L1: \<open>lok ws L1\<close> and wa: \<open>snd L1 ! ka = width ws ds a\<close> and ka64: \<open>ka < 2 ^ 64\<close> using EA by (simp_all add: env_ok_def)
  have t: \<open>cwt ws (snd L1) ?t\<close> \<open>cwidth ws (snd L1) ?t = ?w\<close> using cr_env[OF EA] wt(2,3) by simp_all
  have c: \<open>cws_le ws (snd L1) ?t (width ws ds a)\<close> using wt(3) by (intro cws_le_intros) (simp_all add: ka64[simplified] wa)
  have C: \<open>lcost ws L' \<le> lcost ws L1 + 1 + 3 * (width ws ds a + 1) ^ 2\<close> using push_cost[OF L1 t p c, of 3] by simp
  show ?case using IH[unfolded K_def] C sq_le_cube[of \<open>width ws ds a\<close>] cube1[of \<open>width ws ds a\<close>] cube1[of ?w]
    unfolding tw_un K_def add_mult_distrib2 width.simps by linarith
next
  case (TermL_Repeat i a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  let ?wa = \<open>snd L1 ! ka\<close>
  obtain L2 k0 where p: \<open>push_m L1 (CoreTermL_Const []) 0 = (L2, k0)\<close> by (cases \<open>push_m L1 (CoreTermL_Const []) 0\<close>)
  obtain L3 k3 acc where f: \<open>foldl (repeat_step ka ?wa) (L2, k0, 0) [0..<unat i] = (L3, k3, acc)\<close>
    by (cases \<open>foldl (repeat_step ka ?wa) (L2, k0, 0) [0..<unat i]\<close>)
  have R: \<open>L' = L3\<close> \<open>k = k3\<close> using TermL_Repeat.prems(4) a p f by (simp_all add: Let_def)
  have B2: \<open>bnd L2\<close> using bnd_pfx[OF repeat_fold_pfx[OF f] TermL_Repeat.prems(5)[unfolded R]] .
  have B1: \<open>bnd L1\<close> using bnd_pfx[OF pfx_push[OF p] B2] .
  have wt: \<open>wt ws ds a\<close> \<open>1 \<le> unat i\<close> using TermL_Repeat.prems(1) by simp_all
  note IH = TermL_Repeat.IH[OF wt(1) TermL_Repeat.prems(2,3) a B1]
  note S = lower_m_correct[OF wt(1) TermL_Repeat.prems(2,3) a B1]
  have EA: \<open>env_ok ws L1 ka (width ws ds a)\<close> using S by simp
  have L1: \<open>lok ws L1\<close> and wa: \<open>?wa = width ws ds a\<close> and wa1: \<open>1 \<le> width ws ds a\<close> using EA by (simp_all add: env_ok_def)
  have t0: \<open>cwt ws (snd L1) (CoreTermL_Const [])\<close> \<open>cwidth ws (snd L1) (CoreTermL_Const []) = 0\<close> by simp_all
  have c0: \<open>cws_le ws (snd L1) (CoreTermL_Const []) 0\<close> by (simp add: cws_le_def)
  note C0 = push_cost[OF L1 t0 p c0, of 1]
  note P0 = push_correct[OF L1 t0 p, of \<open>\<lambda>vs. 0\<close>]
  have X2: \<open>lext ws L1 L2\<close> and k0: \<open>k0 < length (fst L2)\<close> \<open>snd L2 ! k0 = 0\<close> using P0 by simp_all
  have EA': \<open>env_ok ws L1 ka ?wa\<close> using EA wa by simp
  let ?W = \<open>width ws ds (TermL_Repeat i a)\<close>
  have W: \<open>?wa * (0 + length [0..<unat i]) \<le> ?W\<close> by (simp add: wa mult.commute)
  have z0: \<open>(0 :: nat) = ?wa * 0\<close> by simp
  note LC = repeat_loop_cost[OF EA' X2 k0 z0 f TermL_Repeat.prems(5)[unfolded R] W]
  have iW: \<open>unat i \<le> ?W\<close> using wa1 by simp
  have \<open>lcost ws L3 \<le> lcost ws L1 + 2 + unat i * (1 + 3 * (?W + 1) ^ 2)\<close>
    using LC C0[simplified] unfolding length_upt diff_zero by linarith
  also have \<open>unat i * (1 + 3 * (?W + 1) ^ 2) \<le> ?W * (4 * (?W + 1) ^ 2)\<close>
    using iW by (intro mult_le_mono) simp_all
  also have \<open>?W * (4 * (?W + 1) ^ 2) \<le> 4 * (?W + 1) ^ 3\<close>
    by (simp add: power3_eq_cube power2_eq_square algebra_simps)
  finally have C: \<open>lcost ws L3 \<le> lcost ws L1 + 2 + 4 * (?W + 1) ^ 3\<close> by simp
  show ?case using IH[unfolded K_def] C cube1[of ?W] cube1[of \<open>width ws ds a\<close>] unfolding tw_un K_def add_mult_distrib2 R by linarith
next
  case (TermL_ZeroExtend i a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  let ?t = \<open>CoreTermL_Bin BinOp_Concat (CoreTermL_Const (replicate (unat i) False)) (cr ka)\<close>
  have p: \<open>push_m L1 ?t (snd L1 ! ka + unat i) = (L', k)\<close> using TermL_ZeroExtend.prems(4) a by (simp add: Let_def)
  have B1: \<open>bnd L1\<close> using bnd_pfx[OF pfx_push[OF p] TermL_ZeroExtend.prems(5)] .
  have wta: \<open>wt ws ds a\<close> using TermL_ZeroExtend.prems(1) by simp
  note IH = TermL_ZeroExtend.IH[OF wta TermL_ZeroExtend.prems(2,3) a B1]
  note S = lower_m_correct[OF wta TermL_ZeroExtend.prems(2,3) a B1]
  have EA: \<open>env_ok ws L1 ka (width ws ds a)\<close> using S by simp
  have L1: \<open>lok ws L1\<close> and wa: \<open>snd L1 ! ka = width ws ds a\<close> and ka64: \<open>ka < 2 ^ 64\<close> using EA by (simp_all add: env_ok_def)
  let ?W = \<open>width ws ds a + unat i\<close>
  have wa1: \<open>1 \<le> width ws ds a\<close> using EA by (simp add: env_ok_def)
  have t: \<open>cwt ws (snd L1) ?t\<close> \<open>cwidth ws (snd L1) ?t = snd L1 ! ka + unat i\<close> using cr_env[OF EA] by (simp_all add: add.commute wa)
  have c: \<open>cws_le ws (snd L1) ?t ?W\<close>
    by (intro cws_le_intros) (simp_all add: ka64[simplified] wa cr_width[OF ka64] one_le_add[OF wa1])
  have C: \<open>lcost ws L' \<le> lcost ws L1 + 1 + 3 * (?W + 1) ^ 2\<close> using push_cost[OF L1 t p c, of 3] by simp
  show ?case using IH[unfolded K_def] C sq_le_cube[of ?W] cube1[of ?W] unfolding tw_un K_def add_mult_distrib2 width.simps by linarith
next
  case (TermL_SignExtend i a)
  let ?wa = \<open>width ws ds a\<close>
  have wta: \<open>wt ws ds a\<close> using TermL_SignExtend.prems(1) by simp
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  let ?t = \<open>CoreTermL_Bin BinOp_Concat
             (CoreTermL_Ite (msb_t ka ?wa) (CoreTermL_Const (replicate (unat i) True)) (CoreTermL_Const (replicate (unat i) False)))
             (cr ka)\<close>
  have p0: \<open>push_m L1 (CoreTermL_Bin BinOp_Concat
             (CoreTermL_Ite (msb_t ka (snd L1 ! ka)) (CoreTermL_Const (replicate (unat i) True)) (CoreTermL_Const (replicate (unat i) False)))
             (cr ka)) (snd L1 ! ka + unat i) = (L', k)\<close>
    using TermL_SignExtend.prems(4) a by (simp add: Let_def)
  have B1: \<open>bnd L1\<close> using bnd_pfx[OF pfx_push[OF p0] TermL_SignExtend.prems(5)] .
  note IH = TermL_SignExtend.IH[OF wta TermL_SignExtend.prems(2,3) a B1]
  note S = lower_m_correct[OF wta TermL_SignExtend.prems(2,3) a B1]
  have EA: \<open>env_ok ws L1 ka ?wa\<close> using S by simp
  have L1: \<open>lok ws L1\<close> and wa: \<open>snd L1 ! ka = ?wa\<close> and ka64: \<open>ka < 2 ^ 64\<close> and wa1: \<open>1 \<le> ?wa\<close> and wa64: \<open>?wa < 2 ^ 64\<close>
    using EA by (simp_all add: env_ok_def)
  have p: \<open>push_m L1 ?t (?wa + unat i) = (L', k)\<close> using p0 unfolding wa .
  let ?W = \<open>?wa + unat i\<close>
  have t: \<open>cwt ws (snd L1) ?t\<close> \<open>cwidth ws (snd L1) ?t = ?W\<close> by (simp_all add: cr_env[OF EA] msb_t_env[OF EA] add.commute)
  have c: \<open>cws_le ws (snd L1) ?t ?W\<close>
    by (intro cws_le_intros msb_t_le)
       (simp_all add: ka64[simplified] wa wa1 wa64[simplified] cr_width[OF ka64] one_le_add[OF wa1] Suc_0_le[OF wa1])
  have C: \<open>lcost ws L' \<le> lcost ws L1 + 1 + 7 * (?W + 1) ^ 2\<close> using push_cost[OF L1 t p c, of 7] by (simp add: msb_t_len)
  show ?case using IH[unfolded K_def] C sq_le_cube[of ?W] cube1[of ?W] unfolding tw_un K_def add_mult_distrib2 width.simps by linarith
next
  case (TermL_RotateLeft i a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  let ?wa = \<open>width ws ds a\<close> and ?r = \<open>unat i mod width ws ds a\<close>
  have wta: \<open>wt ws ds a\<close> using TermL_RotateLeft.prems(1) by simp
  show ?case
  proof (cases \<open>unat i mod snd L1 ! ka = 0\<close>)
    case True
    have R: \<open>L' = L1\<close> using TermL_RotateLeft.prems(4) a True by (simp add: Let_def)
    note IH = TermL_RotateLeft.IH[OF wta TermL_RotateLeft.prems(2,3) a TermL_RotateLeft.prems(5)[unfolded R]]
    show ?thesis using IH[unfolded K_def] cube1[of \<open>width ws ds a\<close>] unfolding tw_un K_def add_mult_distrib2 R width.simps by linarith
  next
    case False
    let ?t = \<open>CoreTermL_Bin BinOp_Concat
               (CoreTermL_Extract (word_of_nat (?wa - 1 - ?r)) 0 (cr ka))
               (CoreTermL_Extract (word_of_nat (?wa - 1)) (word_of_nat (?wa - ?r)) (cr ka))\<close>
    have p0: \<open>push_m L1 (CoreTermL_Bin BinOp_Concat
               (CoreTermL_Extract (word_of_nat (snd L1 ! ka - 1 - unat i mod snd L1 ! ka)) 0 (cr ka))
               (CoreTermL_Extract (word_of_nat (snd L1 ! ka - 1)) (word_of_nat (snd L1 ! ka - unat i mod snd L1 ! ka)) (cr ka)))
               (snd L1 ! ka) = (L', k)\<close>
      using TermL_RotateLeft.prems(4) a False by (simp add: Let_def)
    have B1: \<open>bnd L1\<close> using bnd_pfx[OF pfx_push[OF p0] TermL_RotateLeft.prems(5)] .
    note IH = TermL_RotateLeft.IH[OF wta TermL_RotateLeft.prems(2,3) a B1]
    note S = lower_m_correct[OF wta TermL_RotateLeft.prems(2,3) a B1]
    have EA: \<open>env_ok ws L1 ka ?wa\<close> using S by simp
    have L1: \<open>lok ws L1\<close> and wa: \<open>snd L1 ! ka = ?wa\<close> and wa1: \<open>1 \<le> ?wa\<close> and ka64: \<open>ka < 2 ^ 64\<close> and wa64: \<open>?wa < 2 ^ 64\<close>
      using EA by (simp_all add: env_ok_def)
    have p: \<open>push_m L1 ?t ?wa = (L', k)\<close> using p0 unfolding wa .
    have r: \<open>1 \<le> ?r\<close> \<open>?r < ?wa\<close> using False wa wa1 by simp_all
    have sc: \<open>0 \<le> ?wa - 1 - ?r\<close> \<open>?wa - 1 - ?r < ?wa\<close> \<open>?wa - ?r \<le> ?wa - 1\<close> \<open>?wa - 1 < ?wa\<close> using r wa1 by arith+
    note F = concat_extract_env[where la = 0 and ha = \<open>?wa - 1 - ?r\<close> and lb = \<open>?wa - ?r\<close> and hb = \<open>?wa - 1\<close>, OF EA sc]
    have e: \<open>?wa - 1 - ?r - 0 + 1 + (?wa - 1 - (?wa - ?r) + 1) = ?wa\<close> using r by arith
    have z: \<open>word_of_nat 0 = (0 :: 64 word)\<close> by simp
    have t: \<open>cwt ws (snd L1) ?t\<close> \<open>cwidth ws (snd L1) ?t = ?wa\<close>
      using F[THEN conjunct1] F[THEN conjunct2, THEN conjunct1] e unfolding z by simp_all
    have u: \<open>unat (word_of_nat (?wa - 1 - ?r) :: 64 word) = ?wa - 1 - ?r\<close> \<open>unat (word_of_nat (?wa - 1) :: 64 word) = ?wa - 1\<close>
      \<open>unat (word_of_nat (?wa - ?r) :: 64 word) = ?wa - ?r\<close> using wa64 by (simp_all add: unat_wn)
    have c: \<open>cws_le ws (snd L1) ?t ?wa\<close> using sc r
      by (intro cws_le_intros) (simp_all add: ka64[simplified] wa u u[simplified] Suc_0_le[OF wa1] del: of_nat_diff)
    have C: \<open>lcost ws L' \<le> lcost ws L1 + 1 + 5 * (?wa + 1) ^ 2\<close> using push_cost[OF L1 t p c, of 5] by simp
    show ?thesis using IH[unfolded K_def] C sq_le_cube[of ?wa] cube1[of ?wa] unfolding tw_un K_def add_mult_distrib2 width.simps by linarith
  qed
next
  case (TermL_RotateRight i a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  let ?wa = \<open>width ws ds a\<close> and ?r = \<open>unat i mod width ws ds a\<close>
  have wta: \<open>wt ws ds a\<close> using TermL_RotateRight.prems(1) by simp
  show ?case
  proof (cases \<open>unat i mod snd L1 ! ka = 0\<close>)
    case True
    have R: \<open>L' = L1\<close> using TermL_RotateRight.prems(4) a True by (simp add: Let_def)
    note IH = TermL_RotateRight.IH[OF wta TermL_RotateRight.prems(2,3) a TermL_RotateRight.prems(5)[unfolded R]]
    show ?thesis using IH[unfolded K_def] cube1[of \<open>width ws ds a\<close>] unfolding tw_un K_def add_mult_distrib2 R width.simps by linarith
  next
    case False
    let ?t = \<open>CoreTermL_Bin BinOp_Concat
               (CoreTermL_Extract (word_of_nat (?r - 1)) 0 (cr ka))
               (CoreTermL_Extract (word_of_nat (?wa - 1)) (word_of_nat ?r) (cr ka))\<close>
    have p0: \<open>push_m L1 (CoreTermL_Bin BinOp_Concat
               (CoreTermL_Extract (word_of_nat (unat i mod snd L1 ! ka - 1)) 0 (cr ka))
               (CoreTermL_Extract (word_of_nat (snd L1 ! ka - 1)) (word_of_nat (unat i mod snd L1 ! ka)) (cr ka)))
               (snd L1 ! ka) = (L', k)\<close>
      using TermL_RotateRight.prems(4) a False by (simp add: Let_def)
    have B1: \<open>bnd L1\<close> using bnd_pfx[OF pfx_push[OF p0] TermL_RotateRight.prems(5)] .
    note IH = TermL_RotateRight.IH[OF wta TermL_RotateRight.prems(2,3) a B1]
    note S = lower_m_correct[OF wta TermL_RotateRight.prems(2,3) a B1]
    have EA: \<open>env_ok ws L1 ka ?wa\<close> using S by simp
    have L1: \<open>lok ws L1\<close> and wa: \<open>snd L1 ! ka = ?wa\<close> and wa1: \<open>1 \<le> ?wa\<close> and ka64: \<open>ka < 2 ^ 64\<close> and wa64: \<open>?wa < 2 ^ 64\<close>
      using EA by (simp_all add: env_ok_def)
    have p: \<open>push_m L1 ?t ?wa = (L', k)\<close> using p0 unfolding wa .
    have r: \<open>1 \<le> ?r\<close> \<open>?r < ?wa\<close> using False wa wa1 by simp_all
    have sc: \<open>0 \<le> ?r - 1\<close> \<open>?r - 1 < ?wa\<close> \<open>?r \<le> ?wa - 1\<close> \<open>?wa - 1 < ?wa\<close> using r wa1 by arith+
    note F = concat_extract_env[where la = 0 and ha = \<open>?r - 1\<close> and lb = ?r and hb = \<open>?wa - 1\<close>, OF EA sc]
    have e: \<open>?r - 1 - 0 + 1 + (?wa - 1 - ?r + 1) = ?wa\<close> using r by arith
    have z: \<open>word_of_nat 0 = (0 :: 64 word)\<close> by simp
    have t: \<open>cwt ws (snd L1) ?t\<close> \<open>cwidth ws (snd L1) ?t = ?wa\<close>
      using F[THEN conjunct1] F[THEN conjunct2, THEN conjunct1] e unfolding z by simp_all
    have u: \<open>unat (word_of_nat (?r - 1) :: 64 word) = ?r - 1\<close> \<open>unat (word_of_nat (?wa - 1) :: 64 word) = ?wa - 1\<close>
      \<open>unat (word_of_nat ?r :: 64 word) = ?r\<close> using wa64 r(2) by (simp_all add: unat_wn del: of_nat_diff)
    have c: \<open>cws_le ws (snd L1) ?t ?wa\<close> using sc r
      by (intro cws_le_intros) (simp_all add: ka64[simplified] wa u u[simplified] Suc_0_le[OF wa1] del: of_nat_diff)
    have C: \<open>lcost ws L' \<le> lcost ws L1 + 1 + 5 * (?wa + 1) ^ 2\<close> using push_cost[OF L1 t p c, of 5] by simp
    show ?thesis using IH[unfolded K_def] C sq_le_cube[of ?wa] cube1[of ?wa] unfolding tw_un K_def add_mult_distrib2 width.simps by linarith
  qed
next
  case (TermL_Ite c a b)
  obtain L1 kc where c: \<open>lower_m ws dm L c = (L1, kc)\<close> by (cases \<open>lower_m ws dm L c\<close>)
  obtain L2 ka where a: \<open>lower_m ws dm L1 a = (L2, ka)\<close> by (cases \<open>lower_m ws dm L1 a\<close>)
  obtain L3 kb where b: \<open>lower_m ws dm L2 b = (L3, kb)\<close> by (cases \<open>lower_m ws dm L2 b\<close>)
  let ?t = \<open>CoreTermL_Ite (cr kc) (cr ka) (cr kb)\<close>
  have p: \<open>push_m L3 ?t (snd L3 ! ka) = (L', k)\<close> using TermL_Ite.prems(4) c a b by simp
  have B3: \<open>bnd L3\<close> using bnd_pfx[OF pfx_push[OF p] TermL_Ite.prems(5)] .
  have B2: \<open>bnd L2\<close> using bnd_pfx[OF lower_m_pfx[OF b] B3] .
  have B1: \<open>bnd L1\<close> using bnd_pfx[OF lower_m_pfx[OF a] B2] .
  have wt: \<open>wt ws ds c\<close> \<open>wt ws ds a\<close> \<open>wt ws ds b\<close> \<open>width ws ds c = 1\<close> \<open>width ws ds a = width ws ds b\<close>
    using TermL_Ite.prems(1) by simp_all
  note IHc = TermL_Ite.IH(1)[OF wt(1) TermL_Ite.prems(2,3) c B1]
  note Sc = lower_m_correct[OF wt(1) TermL_Ite.prems(2,3) c B1]
  have L1: \<open>lok ws L1\<close> and X1: \<open>lext ws L L1\<close> using Sc lext_lok by blast+
  note D1 = dm_ok_lext[OF TermL_Ite.prems(2,3) X1]
  note IHa = TermL_Ite.IH(2)[OF wt(2) L1 D1 a B2]
  note Sa = lower_m_correct[OF wt(2) L1 D1 a B2]
  have L2: \<open>lok ws L2\<close> and X2: \<open>lext ws L1 L2\<close> using Sa lext_lok by blast+
  note D2 = dm_ok_lext[OF L1 D1 X2]
  note IHb = TermL_Ite.IH(3)[OF wt(3) L2 D2 b B3]
  note Sb = lower_m_correct[OF wt(3) L2 D2 b B3]
  have L3: \<open>lok ws L3\<close> and X3: \<open>lext ws L2 L3\<close> using Sb lext_lok by blast+
  have EC: \<open>env_ok ws L3 kc 1\<close> using Sc wt(4) env_lext[OF _ X2] env_lext[OF _ X3] by auto
  have EA: \<open>env_ok ws L3 ka (width ws ds a)\<close> using Sa env_lext[OF _ X3] by auto
  have EB: \<open>env_ok ws L3 kb (width ws ds a)\<close> using Sb wt(5) by auto
  let ?wa = \<open>width ws ds a\<close>
  have wa: \<open>snd L3 ! ka = ?wa\<close> and wb: \<open>snd L3 ! kb = ?wa\<close> and wc: \<open>snd L3 ! kc = 1\<close>
    and ka64: \<open>ka < 2 ^ 64\<close> and kb64: \<open>kb < 2 ^ 64\<close> and kc64: \<open>kc < 2 ^ 64\<close> and wa1: \<open>1 \<le> ?wa\<close>
    using EA EB EC by (simp_all add: env_ok_def)
  have t: \<open>cwt ws (snd L3) ?t\<close> \<open>cwidth ws (snd L3) ?t = snd L3 ! ka\<close>
    using cr_env[OF EC] cr_env[OF EA] cr_env[OF EB] by (simp_all add: wa)
  have c: \<open>cws_le ws (snd L3) ?t ?wa\<close>
    by (intro cws_le_intros) (simp_all add: ka64[simplified] kb64[simplified] kc64[simplified] wa wb wc wa1 Suc_0_le[OF wa1])
  have C: \<open>lcost ws L' \<le> lcost ws L3 + 1 + 4 * (?wa + 1) ^ 2\<close> using push_cost[OF L3 t p c, of 4] by simp
  show ?case using IHc[unfolded K_def] IHa[unfolded K_def] IHb[unfolded K_def] C sq_le_cube[of ?wa] cube1[of ?wa] wt(5)
    unfolding tw_Ite K_def add_mult_distrib2 width.simps by linarith
qed

subsection \<open>The size bound\<close>

text \<open>The weight of a well-sorted term does not depend on the widths of later definitions.\<close>
lemma wt_subterm: \<open>wt ws ds t \<Longrightarrow> u \<in> set (subterms t) \<Longrightarrow> wt ws ds u\<close>
  by (induction t) auto

lemma term_weight_append: \<open>wt ws ds t \<Longrightarrow> term_weight ws (ds @ e) t = term_weight ws ds t\<close>
  unfolding term_weight_def
  using wt_subterm wt_width_append by (auto intro!: arg_cong[where f = sum_list] map_cong)

lemma term_weight_take:
  assumes \<open>defs_wt ws [] D\<close> \<open>j < length D\<close>
  shows \<open>term_weight ws (def_widths ws [] (take j D)) (D ! j) = term_weight ws (def_widths ws [] D) (D ! j)\<close>
proof -
  have \<open>def_widths ws [] D = def_widths ws (def_widths ws [] (take j D)) (drop j D)\<close>
    using QFBV_Lower.def_widths_append[of ws \<open>[]\<close> \<open>take j D\<close> \<open>drop j D\<close>] by simp
  then obtain e where \<open>def_widths ws [] D = def_widths ws [] (take j D) @ e\<close>
    using QFBV_Lower.def_widths_prefix by metis
  then show ?thesis using term_weight_append[OF QFBV_Lower.defs_wt_nth[OF assms]] by simp
qed

lemma sum_list_const: \<open>(\<forall>x \<in> set xs. f x = c) \<Longrightarrow> sum_list (map f xs) = length xs * c\<close>
  by (induction xs) simp_all

text \<open>The loop over the definitions: the cost of the state is at most \<open>800\<close> times the weights of the
  definitions rewritten so far.\<close>
lemma ldefs_cost:
  assumes \<open>problem_wt p\<close> \<open>j \<le> length (ProblemL_defs p)\<close>
  shows \<open>foldl (ldefs_step p) (([], []), []) [0..<j] = (L', dm') \<Longrightarrow> bnd L' \<Longrightarrow>
     lcost (var_widths p) L' \<le>
       800 * sum_list (map (term_weight (var_widths p) (def_widths (var_widths p) [] (ProblemL_defs p))) (take j (ProblemL_defs p)))\<close>
  using assms(2)
proof (induction j arbitrary: L' dm')
  case 0
  have R0: \<open>L' = ([], [])\<close> using "0.prems"(1) by simp
  show ?case by (simp add: R0 lcost_def)
next
  case (Suc j)
  let ?ws = \<open>var_widths p\<close> and ?D = \<open>ProblemL_defs p\<close>
  let ?ds = \<open>def_widths ?ws [] ?D\<close>
  have dwt: \<open>defs_wt ?ws [] ?D\<close> using assms(1) by (simp add: problem_wt_def Let_def)
  obtain L dm where f: \<open>foldl (ldefs_step p) (([], []), []) [0..<j] = (L, dm)\<close>
    by (cases \<open>foldl (ldefs_step p) (([], []), []) [0..<j]\<close>)
  obtain L1 k where a: \<open>lower_m ?ws dm L (?D ! j) = (L1, k)\<close> by (cases \<open>lower_m ?ws dm L (?D ! j)\<close>)
  have R: \<open>L' = L1\<close> using Suc.prems(1) f a by (simp add: ldefs_step_def)
  have B: \<open>bnd L\<close> using bnd_pfx[OF lower_m_pfx[OF a]] Suc.prems(2) R by simp
  have jl: \<open>j < length ?D\<close> and jle: \<open>j \<le> length ?D\<close> using Suc.prems(3) by simp_all
  note IH = Suc.IH[OF f B jle]
  note I = ldefs_loop[OF dwt jle f B, unfolded ldefs_inv_def Let_def, simplified]
  have L: \<open>lok ?ws L\<close> and D: \<open>dm_ok (def_widths ?ws [] (take j ?D)) dm L\<close> using I by simp_all
  note C = lower_m_cost[OF QFBV_Lower.defs_wt_nth[OF dwt jl] L D a Suc.prems(2)[unfolded R],
      unfolded K_def term_weight_take[OF dwt jl]]
  have H: \<open>lcost ?ws L1 \<le> lcost ?ws L + 800 * term_weight ?ws ?ds (?D ! j)\<close> using C by linarith
  have S: \<open>sum_list (map (term_weight ?ws ?ds) (take (Suc j) ?D)) =
      sum_list (map (term_weight ?ws ?ds) (take j ?D)) + term_weight ?ws ?ds (?D ! j)\<close>
    by (simp add: take_Suc_conv_app_nth[OF jl])
  show ?case unfolding R S add_mult_distrib2 using IH H by linarith
qed

text \<open>The loop over the assertions.\<close>
lemma lasserts_cost:
  assumes \<open>problem_wt p\<close> \<open>i \<le> length (ProblemL_asserts p)\<close>
    and I1: \<open>ldefs_inv p (length (ProblemL_defs p)) (L1, dm)\<close>
  shows \<open>foldl (lasserts_step p dm) (L1, []) [0..<i] = (L', cs') \<Longrightarrow> bnd L' \<Longrightarrow>
     lcost (var_widths p) L' \<le> lcost (var_widths p) L1 +
       800 * sum_list (map (term_weight (var_widths p) (def_widths (var_widths p) [] (ProblemL_defs p))) (take i (ProblemL_asserts p)))\<close>
  using assms(2)
proof (induction i arbitrary: L' cs')
  case 0
  have R0: \<open>L' = L1\<close> using "0.prems"(1) by simp
  show ?case by (simp add: R0)
next
  case (Suc i)
  let ?ws = \<open>var_widths p\<close> and ?D = \<open>ProblemL_defs p\<close> and ?A = \<open>ProblemL_asserts p\<close>
  let ?ds = \<open>def_widths ?ws [] ?D\<close>
  obtain L cs where f: \<open>foldl (lasserts_step p dm) (L1, []) [0..<i] = (L, cs)\<close>
    by (cases \<open>foldl (lasserts_step p dm) (L1, []) [0..<i]\<close>)
  obtain L2 k where a: \<open>lower_m ?ws dm L (?A ! i) = (L2, k)\<close> by (cases \<open>lower_m ?ws dm L (?A ! i)\<close>)
  have R: \<open>L' = L2\<close> using Suc.prems(1) f a by (simp add: lasserts_step_def)
  have B: \<open>bnd L\<close> using bnd_pfx[OF lower_m_pfx[OF a]] Suc.prems(2) R by simp
  have il: \<open>i < length ?A\<close> and ile: \<open>i \<le> length ?A\<close> using Suc.prems(3) by simp_all
  note IH = Suc.IH[OF f B ile]
  note I = lasserts_loop[OF assms(1) ile I1 f B]
  have wtA: \<open>wt ?ws ?ds (?A ! i)\<close> using assms(1) il by (simp add: problem_wt_def Let_def)
  have L1: \<open>lok ?ws L1\<close> and D1: \<open>dm_ok ?ds dm L1\<close> using I1 by (simp_all add: ldefs_inv_def Let_def)
  have X1: \<open>lext ?ws L1 L\<close> using I by (simp add: lasserts_inv_def Let_def)
  have L: \<open>lok ?ws L\<close> using lext_lok[OF X1] .
  have D: \<open>dm_ok ?ds dm L\<close> using dm_ok_lext[OF L1 D1 X1] .
  note C = lower_m_cost[OF wtA L D a Suc.prems(2)[unfolded R], unfolded K_def]
  have H: \<open>lcost ?ws L2 \<le> lcost ?ws L + 800 * term_weight ?ws ?ds (?A ! i)\<close> using C by linarith
  have S: \<open>sum_list (map (term_weight ?ws ?ds) (take (Suc i) ?A)) =
      sum_list (map (term_weight ?ws ?ds) (take i ?A)) + term_weight ?ws ?ds (?A ! i)\<close>
    by (simp add: take_Suc_conv_app_nth[OF il])
  show ?case unfolding R S add_mult_distrib2 using IH H by linarith
qed

text \<open>The size bound of the core problem is at most the size bound of the problem: the core
  definitions cost at most \<open>800\<close> times the weights of the definitions and assertions, each core
  assertion weighs \<open>4\<close>, and the factor \<open>1000000\<close> of \<^const>\<open>size_bound\<close> absorbs both.\<close>
theorem lower_size_bound:
  assumes \<open>problem_wt p\<close> \<open>bnd (fst (lasserts_res p))\<close>
  shows \<open>csize_bound (lower_problem_m p) \<le> size_bound p\<close>
proof -
  let ?ws = \<open>var_widths p\<close> and ?D = \<open>ProblemL_defs p\<close> and ?A = \<open>ProblemL_asserts p\<close>
  let ?ds = \<open>def_widths ?ws [] ?D\<close>
  obtain L1 dm where d: \<open>ldefs_res p = (L1, dm)\<close> by (cases \<open>ldefs_res p\<close>)
  obtain L2 cs where a: \<open>lasserts_res p = (L2, cs)\<close> by (cases \<open>lasserts_res p\<close>)
  have B2: \<open>bnd L2\<close> using assms(2) a by simp
  have B1: \<open>bnd L1\<close> using bnd_pfx[OF ldefs_res_pfx[of p]] assms(2) d a by simp
  have dwt: \<open>defs_wt ?ws [] ?D\<close> using assms(1) by (simp add: problem_wt_def Let_def)
  have I1: \<open>ldefs_inv p (length ?D) (L1, dm)\<close>
    using ldefs_loop[OF dwt _ _ B1] d by (simp add: ldefs_res_def)
  have I2: \<open>lasserts_inv p dm L1 (length ?A) (L2, cs)\<close>
    using lasserts_loop[OF assms(1) _ I1 _ B2] a d by (simp add: lasserts_res_def)
  have C1: \<open>lcost ?ws L1 \<le> 800 * sum_list (map (term_weight ?ws ?ds) ?D)\<close>
    using ldefs_cost[OF assms(1) order_refl d[unfolded ldefs_res_def] B1] by simp
  have C2: \<open>lcost ?ws L2 \<le> lcost ?ws L1 + 800 * sum_list (map (term_weight ?ws ?ds) ?A)\<close>
    using lasserts_cost[OF assms(1) order_refl I1 a[unfolded lasserts_res_def d fst_conv snd_conv] B2] by simp
  have X12: \<open>lext ?ws L1 L2\<close> using I2 by (simp add: lasserts_inv_def Let_def)
  have L2: \<open>lok ?ws L2\<close> using lext_lok[OF X12] .
  have q: \<open>lower_problem_m p = make_CoreProblemL (ProblemL_widths p) (fst L2) cs\<close>
    using lower_problem_m_eq a by simp
  have cds: \<open>cdef_widths ?ws [] (fst L2) = snd L2\<close> using L2 by (simp add: lok_def)
  have len: \<open>length cs = length ?A\<close> using I2 by (simp add: lasserts_inv_def Let_def)
  have each: \<open>\<And>n. n < length ?A \<Longrightarrow> \<exists>k. cs ! n = cr k \<and> env_ok ?ws L2 k 1\<close>
    using I2 unfolding lasserts_inv_def Let_def fst_conv snd_conv by blast
  have cw4: \<open>\<forall>t \<in> set cs. cterm_weight ?ws (snd L2) t = 4\<close>
  proof
    fix t assume \<open>t \<in> set cs\<close>
    then obtain n where n: \<open>n < length ?A\<close> \<open>t = cs ! n\<close> using len by (auto simp add: in_set_conv_nth)
    then obtain k where k: \<open>cs ! n = cr k\<close> \<open>env_ok ?ws L2 k 1\<close> using each[OF n(1)] by blast
    have k64: \<open>k < 2 ^ 64\<close> and w1: \<open>snd L2 ! k = 1\<close> using k(2) by (simp_all add: env_ok_def)
    have four: \<open>Suc (Suc 0) ^ 2 = (4 :: nat)\<close> by (simp add: eval_nat_numeral)
    show \<open>cterm_weight ?ws (snd L2) t = 4\<close>
      using k(1) n(2) four by (simp add: cterm_weight_def cr_def unat_wn[OF k64] w1)
  qed
  have scs: \<open>sum_list (map (cterm_weight ?ws (snd L2)) cs) = 4 * length ?A\<close>
    using sum_list_const[OF cw4] len by simp
  have cws: \<open>cvar_widths (lower_problem_m p) = ?ws\<close> by (simp add: q cvar_widths_def var_widths_def)
  have E1: \<open>csize_bound (lower_problem_m p) =
      1000 * (1 + sum_list ?ws + length ?ws + lcost ?ws L2 + length ?A + 4 * length ?A)\<close>
    unfolding csize_bound_def Let_def cws q lcost_def
    by (simp add: cds[unfolded var_widths_def] scs[unfolded var_widths_def] len var_widths_def cvar_widths_def)
  have E2: \<open>size_bound p = 1000000 * (1 + sum_list ?ws + length ?ws + length ?D + length ?A +
      (sum_list (map (term_weight ?ws ?ds) ?D) + sum_list (map (term_weight ?ws ?ds) ?A)))\<close>
    by (simp add: size_bound_def Let_def)
  show ?thesis unfolding E1 E2 add_mult_distrib2 using C1 C2 by linarith
qed

end
