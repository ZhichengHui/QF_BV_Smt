theory QFBV_LowerCount
  imports QFBV_LowerBound
begin

section \<open>The CNF count of the rewritten problem\<close>

text \<open>
  The core solver needs no more fuel than \<^const>\<open>fuel_bound\<close> of the core problem, which
  \<open>fuel_bound_lt\<close> bounds by the CNF counts \<^const>\<open>ccount\<close> of the core terms, their number and
  their sizes and widths. Rewriting an extended term \<open>t\<close> adds core definitions whose CNF counts sum
  to at most \<^const>\<open>ecount\<close> of \<open>t\<close> (\<open>lower_m_count\<close>), and each added definition is small: at most
  \<open>50\<close> nodes, of widths at most twice the largest width of a subterm of \<open>t\<close>.
\<close>

subsection \<open>Counts of states and of the built terms\<close>

definition lcnt :: \<open>nat list \<Rightarrow> lst \<Rightarrow> nat\<close> where
  \<open>lcnt ws L \<equiv> sum_list (map (ccount ws (snd L)) (fst L))\<close>

definition lsmall :: \<open>nat list \<Rightarrow> nat \<Rightarrow> lst \<Rightarrow> bool\<close> where
  \<open>lsmall ws M L \<equiv> \<forall>t \<in> set (fst L). length (csubterms t) \<le> 50 \<and> cws_le ws (snd L) t M\<close>

lemma cc_simps:
  \<open>ccount ws ds (CoreTerm_Const bs) = 0\<close>
  \<open>ccount ws ds (CoreTerm_Var i) = 0\<close>
  \<open>ccount ws ds (CoreTerm_Ref j) = 0\<close>
  \<open>ccount ws ds (CoreTerm_Not a) = ccount ws ds a\<close>
  \<open>ccount ws ds (CoreTerm_Bin op a b) = bcost op (cwidth ws ds a) + ccount ws ds a + ccount ws ds b\<close>
  \<open>ccount ws ds (CoreTerm_Extract hi lo a) = ccount ws ds a\<close>
  \<open>ccount ws ds (CoreTerm_Ite c a b) = 5 * cwidth ws ds a + ccount ws ds c + ccount ws ds a + ccount ws ds b\<close>
  by (simp_all add: ccount_def ncost_def)

lemma cc_cr: \<open>ccount ws ds (cr k) = 0\<close>
  by (simp add: cr_def cc_simps)

lemma cc_one: \<open>ccount ws ds (one_t w) = 0\<close>
  by (simp add: one_t_def cc_simps bcost_def)

lemma cc_msb: \<open>ccount ws ds (msb_t k w) = 0\<close>
  by (simp add: msb_t_def cc_simps cc_cr)

lemma cc_neg: \<open>k < 2 ^ 64 \<Longrightarrow> ccount ws ds (neg_t k w) = 15 * (ds ! k)\<close>
  by (simp add: neg_t_def cc_simps cc_cr cc_one bcost_def cr_width)

lemma cc_abs: \<open>k < 2 ^ 64 \<Longrightarrow> ccount ws ds (abs_t k w) = 20 * (ds ! k)\<close>
  by (simp add: abs_t_def neg_t_def cc_simps cc_cr cc_one cc_msb bcost_def cr_width)

lemma cc_slt: \<open>ka < 2 ^ 64 \<Longrightarrow> ccount ws ds (slt_t ka kb w) = 20 + 15 * (ds ! ka)\<close>
  by (simp add: slt_t_def msb_t_def cc_simps cc_cr bcost_def cr_width)

lemma cc_sle: \<open>kb < 2 ^ 64 \<Longrightarrow> ccount ws ds (sle_t ka kb w) = 20 + 15 * (ds ! kb)\<close>
  by (simp add: sle_t_def msb_t_def cc_simps cc_cr bcost_def cr_width)

lemma cws_le_app: \<open>cwt ws ds t \<Longrightarrow> cws_le ws (ds @ e) t M = cws_le ws ds t M\<close>
  by (induction t) (auto simp: cws_le_def wt_width_app nth_append split: BinOp.splits)

lemma lcnt_widths:
  \<open>lok ws L \<Longrightarrow> map (ccount ws (snd L @ e)) (fst L) = map (ccount ws (snd L)) (fst L)\<close>
proof (intro map_cong refl)
  fix u assume \<open>lok ws L\<close> \<open>u \<in> set (fst L)\<close>
  then obtain j where \<open>j < length (fst L)\<close> \<open>u = fst L ! j\<close> by (auto simp add: in_set_conv_nth)
  then have \<open>cwt ws (snd L) u\<close> using cdefs_wt_each \<open>lok ws L\<close> by (simp add: lok_def)
  then show \<open>ccount ws (snd L @ e) u = ccount ws (snd L) u\<close> by (rule ccount_app)
qed

lemma lsmall_widths:
  \<open>lok ws L \<Longrightarrow> u \<in> set (fst L) \<Longrightarrow> cws_le ws (snd L @ e) u M = cws_le ws (snd L) u M\<close>
proof -
  assume \<open>lok ws L\<close> \<open>u \<in> set (fst L)\<close>
  then obtain j where \<open>j < length (fst L)\<close> \<open>u = fst L ! j\<close> by (auto simp add: in_set_conv_nth)
  then have \<open>cwt ws (snd L) u\<close> using cdefs_wt_each \<open>lok ws L\<close> by (simp add: lok_def)
  then show ?thesis by (rule cws_le_app)
qed

text \<open>One push: the count grows by the count of the pushed term, which keeps the state small when
  it is small itself.\<close>
lemma pstep:
  assumes \<open>lok ws L\<close> \<open>cwt ws (snd L) t\<close> \<open>cwidth ws (snd L) t = w\<close> \<open>push_m L t w = (L', k)\<close>
    \<open>ccount ws (snd L) t \<le> c\<close> \<open>length (csubterms t) \<le> 50\<close>
  shows \<open>lcnt ws L' \<le> lcnt ws L + c \<and> (\<forall>M. lsmall ws M L \<longrightarrow> cws_le ws (snd L) t M \<longrightarrow> lsmall ws M L')\<close>
proof -
  note P = push_ok[OF assms(1-4)]
  have M: \<open>map (ccount ws (snd L @ [w])) (fst L) = map (ccount ws (snd L)) (fst L)\<close>
    using lcnt_widths[OF assms(1), of \<open>[w]\<close>] .
  have T: \<open>ccount ws (snd L @ [w]) t = ccount ws (snd L) t\<close> by (rule ccount_app[OF assms(2)])
  have C: \<open>lcnt ws L' \<le> lcnt ws L + c\<close>
    unfolding lcnt_def P(2) P(3) map_append sum_list_append M using T assms(5) by simp
  have S: \<open>lsmall ws M L'\<close> if \<open>lsmall ws M L\<close> \<open>cws_le ws (snd L) t M\<close> for M
    unfolding lsmall_def P(2) P(3)
    using that assms(6) lsmall_widths[OF assms(1)] cws_le_app[OF assms(2)] by (auto simp: lsmall_def)
  show ?thesis using C S by blast
qed

subsection \<open>The count of the operations\<close>

lemma lower_bin_count:
  assumes EA: \<open>env_ok ws L ka wa\<close> and EB: \<open>env_ok ws L kb wb\<close>
    and eqw: \<open>op \<noteq> Op_Concat \<longrightarrow> wb = wa\<close>
    and R: \<open>lower_bin_m L op ka kb = (L', k)\<close>
    and B: \<open>length (fst L') < 2 ^ 64\<close>
  shows \<open>lcnt ws L' \<le> lcnt ws L + ebin op wa \<and> (\<forall>M. lsmall ws M L \<longrightarrow> wa + wb \<le> M \<longrightarrow> lsmall ws M L')\<close>
proof -
  let ?M = \<open>wa + wb\<close>
  have L: \<open>lok ws L\<close> and wa: \<open>snd L ! ka = wa\<close> and wb: \<open>snd L ! kb = wb\<close> and wa1: \<open>1 \<le> wa\<close> and wb1: \<open>1 \<le> wb\<close>
    and wa64: \<open>wa < 2 ^ 64\<close> and wb64: \<open>wb < 2 ^ 64\<close> and ka64: \<open>ka < 2 ^ 64\<close> and kb64: \<open>kb < 2 ^ 64\<close>
    using EA EB by (simp_all add: env_ok_def)
  have EBa: \<open>op \<noteq> Op_Concat \<Longrightarrow> env_ok ws L kb wa\<close> using EB eqw by simp
  note A = cr_env[OF EA] neg_t_env[OF EA] msb_t_env[OF EA] abs_t_env[OF EA]
    cr_env[OF EB] neg_t_env[OF EBa] msb_t_env[OF EBa] abs_t_env[OF EBa] slt_t_env[OF EA EBa] sle_t_env[OF EA EBa]
    slt_t_env[OF EBa EA] sle_t_env[OF EBa EA]
  note W = cws_le_intros neg_t_le msb_t_le abs_t_le slt_t_le sle_t_le
  note N = neg_t_len msb_t_len abs_t_len slt_t_len sle_t_len one_t_len
  have M1: \<open>1 \<le> ?M\<close> using wa1 by simp
  note M = M1 Suc_0_le[OF M1] one_le_add[OF wa1] one_le_add[OF wb1] Suc_0_le[OF wa1] Suc_0_le[OF wb1]
  note ks = ka64[simplified] kb64[simplified] wa64[simplified] wb64[simplified]
  note CC = cc_simps cc_cr cc_one cc_msb cc_neg cc_abs cc_slt cc_sle bcost_def ebin_def cr_width ks
  have mono: \<open>\<And>L1 t. (\<forall>M. lsmall ws M L1 \<longrightarrow> cws_le ws (snd L1) t M \<longrightarrow> lsmall ws M L') \<Longrightarrow> cws_le ws (snd L1) t ?M \<Longrightarrow>
      (\<forall>M. lsmall ws M L1 \<longrightarrow> ?M \<le> M \<longrightarrow> lsmall ws M L')\<close>
    using cws_le_mono by blast
  \<comment> \<open>A single push.\<close>
  have one: \<open>\<And>t w. cws_le ws (snd L) t ?M \<Longrightarrow> lower_bin_m L op ka kb = push_m L t w \<Longrightarrow> cwt ws (snd L) t \<Longrightarrow>
      cwidth ws (snd L) t = w \<Longrightarrow> length (csubterms t) \<le> 50 \<Longrightarrow> ccount ws (snd L) t \<le> ebin op wa \<Longrightarrow>
      lcnt ws L' \<le> lcnt ws L + ebin op wa \<and> (\<forall>M. lsmall ws M L \<longrightarrow> ?M \<le> M \<longrightarrow> lsmall ws M L')\<close>
  proof -
    fix t w assume H: \<open>cws_le ws (snd L) t ?M\<close> \<open>lower_bin_m L op ka kb = push_m L t w\<close> \<open>cwt ws (snd L) t\<close>
      \<open>cwidth ws (snd L) t = w\<close> \<open>length (csubterms t) \<le> 50\<close> \<open>ccount ws (snd L) t \<le> ebin op wa\<close>
    have p: \<open>push_m L t w = (L', k)\<close> using R H(2) by simp
    note S = pstep[OF L H(3,4) p H(6,5)]
    show \<open>lcnt ws L' \<le> lcnt ws L + ebin op wa \<and> (\<forall>M. lsmall ws M L \<longrightarrow> ?M \<le> M \<longrightarrow> lsmall ws M L')\<close>
      using S mono[OF _ H(1)] by blast
  qed
  show ?thesis
  proof (cases op)
    case Op_And
    show ?thesis by (rule one[of \<open>CoreTerm_Bin BinOp_And (cr ka) (cr kb)\<close> wa], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_And lower_bin_m_def wa wb A eqw CC)
  next
    case Op_Or
    show ?thesis by (rule one[of \<open>CoreTerm_Bin BinOp_Or (cr ka) (cr kb)\<close> wa], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Or lower_bin_m_def wa wb A eqw CC)
  next
    case Op_Xor
    show ?thesis by (rule one[of \<open>CoreTerm_Bin BinOp_Xor (cr ka) (cr kb)\<close> wa], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Xor lower_bin_m_def wa wb A eqw CC)
  next
    case Op_Nand
    show ?thesis by (rule one[of \<open>CoreTerm_Not (CoreTerm_Bin BinOp_And (cr ka) (cr kb))\<close> wa], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Nand lower_bin_m_def wa wb A eqw CC)
  next
    case Op_Nor
    show ?thesis by (rule one[of \<open>CoreTerm_Not (CoreTerm_Bin BinOp_Or (cr ka) (cr kb))\<close> wa], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Nor lower_bin_m_def wa wb A eqw CC)
  next
    case Op_Xnor
    show ?thesis by (rule one[of \<open>CoreTerm_Not (CoreTerm_Bin BinOp_Xor (cr ka) (cr kb))\<close> wa], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Xnor lower_bin_m_def wa wb A eqw CC)
  next
    case Op_Comp
    show ?thesis by (rule one[of \<open>CoreTerm_Bin BinOp_Eq (cr ka) (cr kb)\<close> 1], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Comp lower_bin_m_def wa wb A eqw CC)
  next
    case Op_Add
    show ?thesis by (rule one[of \<open>CoreTerm_Bin BinOp_Add (cr ka) (cr kb)\<close> wa], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Add lower_bin_m_def wa wb A eqw CC)
  next
    case Op_Sub
    show ?thesis by (rule one[of \<open>CoreTerm_Bin BinOp_Add (cr ka) (neg_t kb wa)\<close> wa], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Sub lower_bin_m_def wa wb A N eqw CC)
  next
    case Op_Mul
    show ?thesis by (rule one[of \<open>CoreTerm_Bin BinOp_Mul (cr ka) (cr kb)\<close> wa], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Mul lower_bin_m_def wa wb A eqw CC)
  next
    case Op_Udiv
    show ?thesis by (rule one[of \<open>CoreTerm_Bin BinOp_Udiv (cr ka) (cr kb)\<close> wa], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Udiv lower_bin_m_def wa wb A eqw CC)
  next
    case Op_Urem
    show ?thesis by (rule one[of \<open>CoreTerm_Bin BinOp_Urem (cr ka) (cr kb)\<close> wa], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Urem lower_bin_m_def wa wb A eqw CC)
  next
    case Op_Shl
    show ?thesis by (rule one[of \<open>CoreTerm_Bin BinOp_Shl (cr ka) (cr kb)\<close> wa], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Shl lower_bin_m_def wa wb A eqw CC)
  next
    case Op_Lshr
    show ?thesis by (rule one[of \<open>CoreTerm_Bin BinOp_Lshr (cr ka) (cr kb)\<close> wa], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Lshr lower_bin_m_def wa wb A eqw CC)
  next
    case Op_Ashr
    show ?thesis by (rule one[of \<open>CoreTerm_Ite (msb_t ka wa)
          (CoreTerm_Not (CoreTerm_Bin BinOp_Lshr (CoreTerm_Not (cr ka)) (cr kb)))
          (CoreTerm_Bin BinOp_Lshr (cr ka) (cr kb))\<close> wa])
        (simp_all add: Op_Ashr lower_bin_m_def wa wb A N eqw CC, (intro W; simp add: wa wb ks M wa1 unat_wn eqw[simplified Op_Ashr, simplified])?)
  next
    case Op_Concat
    show ?thesis by (rule one[of \<open>CoreTerm_Bin BinOp_Concat (cr ka) (cr kb)\<close> \<open>wa + wb\<close>], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Concat lower_bin_m_def wa wb A eqw CC)
  next
    case Op_Eq
    show ?thesis by (rule one[of \<open>CoreTerm_Bin BinOp_Eq (cr ka) (cr kb)\<close> 1], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Eq lower_bin_m_def wa wb A eqw CC)
  next
    case Op_Distinct
    show ?thesis by (rule one[of \<open>CoreTerm_Not (CoreTerm_Bin BinOp_Eq (cr ka) (cr kb))\<close> 1], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Distinct lower_bin_m_def wa wb A eqw CC)
  next
    case Op_Ult
    show ?thesis by (rule one[of \<open>CoreTerm_Bin BinOp_Ult (cr ka) (cr kb)\<close> 1], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Ult lower_bin_m_def wa wb A eqw CC)
  next
    case Op_Ule
    show ?thesis by (rule one[of \<open>CoreTerm_Not (CoreTerm_Bin BinOp_Ult (cr kb) (cr ka))\<close> 1], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Ule lower_bin_m_def wa wb A eqw CC)
  next
    case Op_Ugt
    show ?thesis by (rule one[of \<open>CoreTerm_Bin BinOp_Ult (cr kb) (cr ka)\<close> 1], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Ugt lower_bin_m_def wa wb A eqw CC)
  next
    case Op_Uge
    show ?thesis by (rule one[of \<open>CoreTerm_Not (CoreTerm_Bin BinOp_Ult (cr ka) (cr kb))\<close> 1], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Uge lower_bin_m_def wa wb A eqw CC)
  next
    case Op_Slt
    show ?thesis by (rule one[of \<open>slt_t ka kb wa\<close> 1], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Slt lower_bin_m_def wa wb A N eqw CC)
  next
    case Op_Sle
    show ?thesis by (rule one[of \<open>sle_t ka kb wa\<close> 1], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Sle lower_bin_m_def wa wb A N eqw CC)
  next
    case Op_Sgt
    show ?thesis by (rule one[of \<open>slt_t kb ka wa\<close> 1], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Sgt lower_bin_m_def wa wb A N eqw CC)
  next
    case Op_Sge
    show ?thesis by (rule one[of \<open>sle_t kb ka wa\<close> 1], (intro W; simp add: wa wb ks M wa1 unat_wn), simp_all add: Op_Sge lower_bin_m_def wa wb A N eqw CC)
  next
    case Op_Sdiv
    have wba: \<open>wb = wa\<close> using eqw Op_Sdiv by simp
    have ne: \<open>op \<noteq> Op_Concat\<close> using Op_Sdiv by simp
    note EB' = EBa[OF ne]
    let ?t1 = \<open>CoreTerm_Bin BinOp_Udiv (abs_t ka wa) (abs_t kb wa)\<close>
    obtain L1 q where p1: \<open>push_m L ?t1 wa = (L1, q)\<close> by (cases \<open>push_m L ?t1 wa\<close>)
    let ?t2 = \<open>CoreTerm_Ite (CoreTerm_Bin BinOp_Xor (msb_t ka wa) (msb_t kb wa)) (neg_t q wa) (cr q)\<close>
    have p2: \<open>push_m L1 ?t2 wa = (L', k)\<close> using R p1 by (simp add: Op_Sdiv lower_bin_m_def wa)
    have t1: \<open>cwt ws (snd L) ?t1\<close> \<open>cwidth ws (snd L) ?t1 = wa\<close> using abs_t_env[OF EA] abs_t_env[OF EB'] by simp_all
    have c1: \<open>cws_le ws (snd L) ?t1 ?M\<close> by (intro W) (simp_all add: wa wb ks M wa1 wba)
    have n1: \<open>length (csubterms ?t1) \<le> 50\<close> by (simp add: N)
    have k1: \<open>ccount ws (snd L) ?t1 \<le> 76 * wa * wa + 132 * wa + 14\<close> using abs_t_env[OF EA] by (simp add: CC wa wb wba)
    note C1 = pstep[OF L t1 p1 k1 n1]
    have L1: \<open>lok ws L1\<close> using lext_push[OF L t1 p1] lext_lok by blast
    have EQ: \<open>env_ok ws L1 q wa\<close>
      using env_push[OF L t1 p1 wa1 wa64] B pfx_length[OF pfx_push[OF p2]] by simp
    have EA1: \<open>env_ok ws L1 ka wa\<close> and EB1: \<open>env_ok ws L1 kb wa\<close>
      using env_lext[OF EA lext_push[OF L t1 p1]] env_lext[OF EB' lext_push[OF L t1 p1]] by simp_all
    have t2: \<open>cwt ws (snd L1) ?t2\<close> \<open>cwidth ws (snd L1) ?t2 = wa\<close>
      using msb_t_env[OF EA1] msb_t_env[OF EB1] neg_t_env[OF EQ] cr_env[OF EQ] by simp_all
    have q64: \<open>q < 2 ^ 64\<close> and wq: \<open>snd L1 ! q = wa\<close> and wa1': \<open>snd L1 ! ka = wa\<close> and wb1': \<open>snd L1 ! kb = wa\<close>
      using EQ EA1 EB1 by (simp_all add: env_ok_def)
    have c2: \<open>cws_le ws (snd L1) ?t2 ?M\<close> by (intro W) (simp_all add: wq wa1' wb1' ks q64[simplified] M wa1)
    have n2: \<open>length (csubterms ?t2) \<le> 50\<close> by (simp add: N)
    have k2: \<open>ccount ws (snd L1) ?t2 \<le> 20 * wa + 5\<close>
      using neg_t_env[OF EQ] msb_t_env[OF EA1] by (simp add: CC q64[simplified] wq)
    note C2 = pstep[OF L1 t2 p2 k2 n2]
    have e: \<open>ebin op wa = 76 * wa * wa + 300 * wa + 20\<close> by (simp add: Op_Sdiv ebin_def)
    have A: \<open>lcnt ws L' \<le> lcnt ws L + (76 * wa * wa + 300 * wa + 20)\<close>
      using C1[THEN conjunct1] C2[THEN conjunct1] by linarith
    have B: \<open>\<forall>M. lsmall ws M L \<longrightarrow> ?M \<le> M \<longrightarrow> lsmall ws M L'\<close>
      using C1[THEN conjunct2] C2[THEN conjunct2] cws_le_mono[OF c1] cws_le_mono[OF c2] by blast
    show ?thesis unfolding e using A B by blast
  next
    case Op_Srem
    have wba: \<open>wb = wa\<close> using eqw Op_Srem by simp
    have ne: \<open>op \<noteq> Op_Concat\<close> using Op_Srem by simp
    note EB' = EBa[OF ne]
    let ?t1 = \<open>CoreTerm_Bin BinOp_Urem (abs_t ka wa) (abs_t kb wa)\<close>
    obtain L1 r where p1: \<open>push_m L ?t1 wa = (L1, r)\<close> by (cases \<open>push_m L ?t1 wa\<close>)
    let ?t2 = \<open>CoreTerm_Ite (msb_t ka wa) (neg_t r wa) (cr r)\<close>
    have p2: \<open>push_m L1 ?t2 wa = (L', k)\<close> using R p1 by (simp add: Op_Srem lower_bin_m_def wa)
    have t1: \<open>cwt ws (snd L) ?t1\<close> \<open>cwidth ws (snd L) ?t1 = wa\<close> using abs_t_env[OF EA] abs_t_env[OF EB'] by simp_all
    have c1: \<open>cws_le ws (snd L) ?t1 ?M\<close> by (intro W) (simp_all add: wa wb ks M wa1 wba)
    have n1: \<open>length (csubterms ?t1) \<le> 50\<close> by (simp add: N)
    have k1: \<open>ccount ws (snd L) ?t1 \<le> 76 * wa * wa + 132 * wa + 14\<close> using abs_t_env[OF EA] by (simp add: CC wa wb wba)
    note C1 = pstep[OF L t1 p1 k1 n1]
    have L1: \<open>lok ws L1\<close> using lext_push[OF L t1 p1] lext_lok by blast
    have ER: \<open>env_ok ws L1 r wa\<close>
      using env_push[OF L t1 p1 wa1 wa64] B pfx_length[OF pfx_push[OF p2]] by simp
    have EA1: \<open>env_ok ws L1 ka wa\<close> using env_lext[OF EA lext_push[OF L t1 p1]] by simp
    have t2: \<open>cwt ws (snd L1) ?t2\<close> \<open>cwidth ws (snd L1) ?t2 = wa\<close>
      using msb_t_env[OF EA1] neg_t_env[OF ER] cr_env[OF ER] by simp_all
    have r64: \<open>r < 2 ^ 64\<close> and wr: \<open>snd L1 ! r = wa\<close> and wa1': \<open>snd L1 ! ka = wa\<close>
      using ER EA1 by (simp_all add: env_ok_def)
    have c2: \<open>cws_le ws (snd L1) ?t2 ?M\<close> by (intro W) (simp_all add: wr wa1' ks r64[simplified] M wa1)
    have n2: \<open>length (csubterms ?t2) \<le> 50\<close> by (simp add: N)
    have k2: \<open>ccount ws (snd L1) ?t2 \<le> 20 * wa\<close>
      using neg_t_env[OF ER] by (simp add: CC r64[simplified] wr)
    note C2 = pstep[OF L1 t2 p2 k2 n2]
    have e: \<open>ebin op wa = 76 * wa * wa + 300 * wa + 20\<close> by (simp add: Op_Srem ebin_def)
    have A: \<open>lcnt ws L' \<le> lcnt ws L + (76 * wa * wa + 300 * wa + 20)\<close>
      using C1[THEN conjunct1] C2[THEN conjunct1] by linarith
    have B: \<open>\<forall>M. lsmall ws M L \<longrightarrow> ?M \<le> M \<longrightarrow> lsmall ws M L'\<close>
      using C1[THEN conjunct2] C2[THEN conjunct2] cws_le_mono[OF c1] cws_le_mono[OF c2] by blast
    show ?thesis unfolding e using A B by blast
  next
    case Op_Smod
    have wba: \<open>wb = wa\<close> using eqw Op_Smod by simp
    have ne: \<open>op \<noteq> Op_Concat\<close> using Op_Smod by simp
    note EB' = EBa[OF ne]
    let ?t1 = \<open>CoreTerm_Bin BinOp_Urem (abs_t ka wa) (abs_t kb wa)\<close>
    obtain L1 u where p1: \<open>push_m L ?t1 wa = (L1, u)\<close> by (cases \<open>push_m L ?t1 wa\<close>)
    obtain L2 nu where p2: \<open>push_m L1 (neg_t u wa) wa = (L2, nu)\<close> by (cases \<open>push_m L1 (neg_t u wa) wa\<close>)
    let ?t3 = \<open>CoreTerm_Ite (CoreTerm_Bin BinOp_Eq (cr u) (CoreTerm_Const (replicate wa False))) (cr u)
          (CoreTerm_Ite (msb_t ka wa)
             (CoreTerm_Ite (msb_t kb wa) (cr nu) (CoreTerm_Bin BinOp_Add (cr nu) (cr kb)))
             (CoreTerm_Ite (msb_t kb wa) (CoreTerm_Bin BinOp_Add (cr u) (cr kb)) (cr u)))\<close>
    have p3: \<open>push_m L2 ?t3 wa = (L', k)\<close> using R p1 p2 by (simp add: Op_Smod lower_bin_m_def wa)
    have t1: \<open>cwt ws (snd L) ?t1\<close> \<open>cwidth ws (snd L) ?t1 = wa\<close> using abs_t_env[OF EA] abs_t_env[OF EB'] by simp_all
    have c1: \<open>cws_le ws (snd L) ?t1 ?M\<close> by (intro W) (simp_all add: wa wb ks M wa1 wba)
    have n1: \<open>length (csubterms ?t1) \<le> 50\<close> by (simp add: N)
    have k1: \<open>ccount ws (snd L) ?t1 \<le> 76 * wa * wa + 132 * wa + 14\<close> using abs_t_env[OF EA] by (simp add: CC wa wb wba)
    note C1 = pstep[OF L t1 p1 k1 n1]
    have X1: \<open>lext ws L L1\<close> using lext_push[OF L t1 p1] .
    have L1: \<open>lok ws L1\<close> using X1 lext_lok by blast
    have EU: \<open>env_ok ws L1 u wa\<close>
      using env_push[OF L t1 p1 wa1 wa64] B pfx_length[OF pfx_push[OF p2]] pfx_length[OF pfx_push[OF p3]] by simp
    have t2: \<open>cwt ws (snd L1) (neg_t u wa)\<close> \<open>cwidth ws (snd L1) (neg_t u wa) = wa\<close> using neg_t_env[OF EU] by simp_all
    have u64: \<open>u < 2 ^ 64\<close> and wu: \<open>snd L1 ! u = wa\<close> using EU by (simp_all add: env_ok_def)
    have c2: \<open>cws_le ws (snd L1) (neg_t u wa) ?M\<close> by (intro W neg_t_le) (simp_all add: wu u64[simplified] M wa1)
    have n2: \<open>length (csubterms (neg_t u wa)) \<le> 50\<close> by (simp add: N)
    have k2: \<open>ccount ws (snd L1) (neg_t u wa) \<le> 15 * wa\<close> by (simp add: CC u64[simplified] wu)
    note C2 = pstep[OF L1 t2 p2 k2 n2]
    have X2: \<open>lext ws L1 L2\<close> using lext_push[OF L1 t2 p2] .
    have L2: \<open>lok ws L2\<close> using X2 lext_lok by blast
    have ENU: \<open>env_ok ws L2 nu wa\<close>
      using env_push[OF L1 t2 p2 wa1 wa64] B pfx_length[OF pfx_push[OF p3]] by simp
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
    have k3: \<open>ccount ws (snd L2) ?t3 \<le> 59 * wa\<close> using msb_t_env[OF EA2] by (simp add: CC u64[simplified] nu64[simplified] wu2 wnu)
    note C3 = pstep[OF L2 t3 p3 k3 n3]
    have e: \<open>ebin op wa = 76 * wa * wa + 300 * wa + 20\<close> by (simp add: Op_Smod ebin_def)
    have A: \<open>lcnt ws L' \<le> lcnt ws L + (76 * wa * wa + 300 * wa + 20)\<close>
      using C1[THEN conjunct1] C2[THEN conjunct1] C3[THEN conjunct1] by linarith
    have B: \<open>\<forall>M. lsmall ws M L \<longrightarrow> ?M \<le> M \<longrightarrow> lsmall ws M L'\<close>
      using C1[THEN conjunct2] C2[THEN conjunct2] C3[THEN conjunct2]
        cws_le_mono[OF c1] cws_le_mono[OF c2] cws_le_mono[OF c3] by blast
    show ?thesis unfolding e using A B by blast
  qed
qed

lemma repeat_loop_count:
  assumes EA: \<open>env_ok ws L ka wa\<close>
  shows \<open>lext ws L Lj \<Longrightarrow> kj < length (fst Lj) \<Longrightarrow> snd Lj ! kj = acc0 \<Longrightarrow> acc0 = wa * j \<Longrightarrow>
    foldl (repeat_step ka wa) (Lj, kj, acc0) js = (L3, k3, acc) \<Longrightarrow> bnd L3 \<Longrightarrow>
    wa * (j + length js) \<le> W \<Longrightarrow>
    lcnt ws L3 \<le> lcnt ws Lj \<and> (\<forall>M. lsmall ws M Lj \<longrightarrow> W \<le> M \<longrightarrow> lsmall ws M L3)\<close>
proof (induction js arbitrary: Lj kj j acc0)
  case Nil
  then show ?case by simp
next
  case (Cons x js)
  let ?t = \<open>CoreTerm_Bin BinOp_Concat (cr ka) (cr kj)\<close>
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
  have c: \<open>cws_le ws (snd Lj) ?t W\<close>
  proof (rule cws_le_Bin)
    show \<open>cws_le ws (snd Lj) (cr ka) W\<close> by (rule cws_le_cr[OF ka64]) (simp add: waj Wb2)
    show \<open>cws_le ws (snd Lj) (cr kj) W\<close> by (rule cws_le_cr[OF kj64]) (simp add: Cons.prems(3) Wb3)
    show \<open>1 \<le> W\<close> using wa1 Wb2 by linarith
    show \<open>BinOp_Concat = BinOp_Concat \<longrightarrow> cwidth ws (snd Lj) (cr ka) + cwidth ws (snd Lj) (cr kj) \<le> W\<close>
      using Wb1 by (simp add: cr_width[OF ka64] cr_width[OF kj64] waj Cons.prems(3) add.commute)
  qed
  have n: \<open>length (csubterms ?t) \<le> 50\<close> by simp
  have k0: \<open>ccount ws (snd Lj) ?t \<le> 0\<close> by (simp add: cc_simps cc_cr bcost_def)
  note C = pstep[OF Lj t p k0 n]
  have \<open>lext ws L Lj'\<close> using Cons.prems(1) lext_push[OF Lj t p] lext_trans by blast
  note IH = Cons.IH[OF this _ _ acc f Cons.prems(6)]
  note P = push_ok[OF Lj t p]
  have kj'l: \<open>kj' < length (fst Lj')\<close> and wkj': \<open>snd Lj' ! kj' = acc0 + wa\<close>
    using P(2-4) lok_length[OF Lj, symmetric] by simp_all
  have \<open>wa * (Suc j + length js) \<le> W\<close> using Cons.prems(7) by simp
  note I = IH[OF kj'l wkj' this]
  have A: \<open>lcnt ws L3 \<le> lcnt ws Lj\<close> using I[THEN conjunct1] C[THEN conjunct1] by simp
  have B: \<open>\<forall>M. lsmall ws M Lj \<longrightarrow> W \<le> M \<longrightarrow> lsmall ws M L3\<close>
    using I[THEN conjunct2] C[THEN conjunct2] cws_le_mono[OF c] by blast
  show ?case using A B by blast
qed

subsection \<open>The count of a term\<close>

lemma ec_simps:
  \<open>ecount ws ds (Term_Const bs) = 0\<close>
  \<open>ecount ws ds (Term_Var i) = 0\<close>
  \<open>ecount ws ds (Term_Ref j) = 0\<close>
  \<open>ecount ws ds (Term_Not a) = ecount ws ds a\<close>
  \<open>ecount ws ds (Term_Neg a) = 15 * width ws ds a + ecount ws ds a\<close>
  \<open>ecount ws ds (Term_Bin op a b) = ebin op (width ws ds a) + ecount ws ds a + ecount ws ds b\<close>
  \<open>ecount ws ds (Term_Extract hi lo a) = ecount ws ds a\<close>
  \<open>ecount ws ds (Term_Repeat i a) = ecount ws ds a\<close>
  \<open>ecount ws ds (Term_ZeroExtend i a) = ecount ws ds a\<close>
  \<open>ecount ws ds (Term_SignExtend i a) = 5 * unat i + ecount ws ds a\<close>
  \<open>ecount ws ds (Term_RotateLeft i a) = ecount ws ds a\<close>
  \<open>ecount ws ds (Term_RotateRight i a) = ecount ws ds a\<close>
  \<open>ecount ws ds (Term_Ite c a b) = 5 * width ws ds a + ecount ws ds c + ecount ws ds a + ecount ws ds b\<close>
  by (simp_all add: ecount_def enode_def)

lemma sub_self: \<open>t \<in> set (subterms t)\<close>
  by (cases t) simp_all

definition wsmall :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> Term \<Rightarrow> bool\<close> where
  \<open>wsmall ws ds M t \<equiv> \<forall>u \<in> set (subterms t). 2 * width ws ds u \<le> M\<close>

lemma wsmall_simps:
  \<open>wsmall ws ds M (Term_Not a) \<Longrightarrow> wsmall ws ds M a \<and> 2 * width ws ds a \<le> M\<close>
  \<open>wsmall ws ds M (Term_Neg a) \<Longrightarrow> wsmall ws ds M a \<and> 2 * width ws ds a \<le> M\<close>
  \<open>wsmall ws ds M (Term_Bin op a b) \<Longrightarrow> wsmall ws ds M a \<and> wsmall ws ds M b \<and> 2 * width ws ds a \<le> M \<and>
     2 * width ws ds b \<le> M\<close>
  \<open>wsmall ws ds M (Term_Extract hi lo a) \<Longrightarrow> wsmall ws ds M a \<and> 2 * width ws ds a \<le> M\<close>
  \<open>wsmall ws ds M (Term_Repeat i a) \<Longrightarrow> wsmall ws ds M a \<and> 2 * width ws ds (Term_Repeat i a) \<le> M\<close>
  \<open>wsmall ws ds M (Term_ZeroExtend i a) \<Longrightarrow> wsmall ws ds M a \<and> 2 * (width ws ds a + unat i) \<le> M\<close>
  \<open>wsmall ws ds M (Term_SignExtend i a) \<Longrightarrow> wsmall ws ds M a \<and> 2 * (width ws ds a + unat i) \<le> M\<close>
  \<open>wsmall ws ds M (Term_RotateLeft i a) \<Longrightarrow> wsmall ws ds M a \<and> 2 * width ws ds a \<le> M\<close>
  \<open>wsmall ws ds M (Term_RotateRight i a) \<Longrightarrow> wsmall ws ds M a \<and> 2 * width ws ds a \<le> M\<close>
  \<open>wsmall ws ds M (Term_Ite c a b) \<Longrightarrow> wsmall ws ds M c \<and> wsmall ws ds M a \<and> wsmall ws ds M b \<and>
     2 * width ws ds a \<le> M\<close>
  \<open>wsmall ws ds M (Term_Const bs) \<Longrightarrow> 2 * length bs \<le> M\<close>
  \<open>wsmall ws ds M (Term_Var i) \<Longrightarrow> 2 * (ws ! unat i) \<le> M\<close>
  by (auto simp: wsmall_def intro: sub_self dest: bspec[OF _ sub_self])

lemma half: \<open>2 * w \<le> M \<Longrightarrow> w \<le> M\<close> for w M :: nat
  by linarith

lemma half2: \<open>2 * a \<le> M \<Longrightarrow> 2 * b \<le> M \<Longrightarrow> a + b \<le> M\<close> for a b M :: nat
  by linarith

lemma lower_m_count:
  assumes \<open>wt ws ds t\<close> \<open>lok ws L\<close> \<open>dm_ok ds dm L\<close> \<open>lower_m ws dm L t = (L', k)\<close> \<open>bnd L'\<close>
  shows \<open>lcnt ws L' \<le> lcnt ws L + ecount ws ds t \<and> (lsmall ws M L \<longrightarrow> wsmall ws ds M t \<longrightarrow> lsmall ws M L')\<close>
  using assms
proof (induction t arbitrary: L L' k)
  case (Term_Const bs)
  have p: \<open>push_m L (CoreTerm_Const bs) (length bs) = (L', k)\<close> using Term_Const.prems(4) by simp
  have c: \<open>cws_le ws (snd L) (CoreTerm_Const bs) (length bs)\<close> by (simp add: cws_le_def)
  note C = pstep[OF Term_Const.prems(2) _ _ p, of 0]
  have m: \<open>wsmall ws ds M (Term_Const bs) \<Longrightarrow> length bs \<le> M\<close> using wsmall_simps(11)[of ws ds M bs] by linarith
  show ?case using C cws_le_mono[OF c] m by (auto simp: cc_simps ec_simps)
next
  case (Term_Var i)
  have p: \<open>push_m L (CoreTerm_Var i) (ws ! unat i) = (L', k)\<close> using Term_Var.prems(4) by simp
  have wt: \<open>unat i < length ws\<close> using Term_Var.prems(1) by simp
  have c: \<open>cws_le ws (snd L) (CoreTerm_Var i) (ws ! unat i)\<close> by (simp add: cws_le_def)
  note C = pstep[OF Term_Var.prems(2) _ _ p, of 0]
  have m: \<open>wsmall ws ds M (Term_Var i) \<Longrightarrow> ws ! unat i \<le> M\<close> using wsmall_simps(12)[of ws ds M i] by linarith
  show ?case using C cws_le_mono[OF c] m wt by (auto simp: cc_simps ec_simps)
next
  case (Term_Ref j)
  have \<open>L' = L\<close> using Term_Ref.prems(4) by simp
  then show ?case by (simp add: ec_simps)
next
  case (Term_Not a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  have p: \<open>push_m L1 (CoreTerm_Not (cr ka)) (snd L1 ! ka) = (L', k)\<close> using Term_Not.prems(4) a by simp
  have B1: \<open>bnd L1\<close> using bnd_pfx[OF pfx_push[OF p] Term_Not.prems(5)] .
  have wta: \<open>wt ws ds a\<close> using Term_Not.prems(1) by simp
  note IH = Term_Not.IH[OF wta Term_Not.prems(2,3) a B1]
  note S = lower_m_correct[OF wta Term_Not.prems(2,3) a B1]
  have EA: \<open>env_ok ws L1 ka (width ws ds a)\<close> using S by simp
  have L1: \<open>lok ws L1\<close> and wa: \<open>snd L1 ! ka = width ws ds a\<close> and ka64: \<open>ka < 2 ^ 64\<close> using EA by (simp_all add: env_ok_def)
  have t: \<open>cwt ws (snd L1) (CoreTerm_Not (cr ka))\<close> \<open>cwidth ws (snd L1) (CoreTerm_Not (cr ka)) = snd L1 ! ka\<close>
    using cr_env[OF EA] wa by simp_all
  have c: \<open>cws_le ws (snd L1) (CoreTerm_Not (cr ka)) (width ws ds a)\<close> by (intro cws_le_intros) (simp_all add: ka64[simplified] wa)
  have k0: \<open>ccount ws (snd L1) (CoreTerm_Not (cr ka)) \<le> 0\<close> by (simp add: cc_simps cc_cr)
  note C = pstep[OF L1 t p k0]
  have n: \<open>length (csubterms (CoreTerm_Not (cr ka))) \<le> 50\<close> by (simp add: neg_t_len msb_t_len)
  note C' = C[OF n]
  have A: \<open>lcnt ws L' \<le> lcnt ws L + ecount ws ds (Term_Not a)\<close>
    using IH[THEN conjunct1] C'[THEN conjunct1] by (simp add: ec_simps)
  have B: \<open>lsmall ws M L \<longrightarrow> wsmall ws ds M (Term_Not a) \<longrightarrow> lsmall ws M L'\<close>
    using IH[THEN conjunct2] C'[THEN conjunct2] cws_le_mono[OF c] wsmall_simps(1) half by blast
  show ?case using A B by blast
next
  case (Term_Neg a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  have p: \<open>push_m L1 (neg_t ka (snd L1 ! ka)) (snd L1 ! ka) = (L', k)\<close> using Term_Neg.prems(4) a by simp
  have B1: \<open>bnd L1\<close> using bnd_pfx[OF pfx_push[OF p] Term_Neg.prems(5)] .
  have wta: \<open>wt ws ds a\<close> using Term_Neg.prems(1) by simp
  note IH = Term_Neg.IH[OF wta Term_Neg.prems(2,3) a B1]
  note S = lower_m_correct[OF wta Term_Neg.prems(2,3) a B1]
  have EA: \<open>env_ok ws L1 ka (width ws ds a)\<close> using S by simp
  have L1: \<open>lok ws L1\<close> and wa: \<open>snd L1 ! ka = width ws ds a\<close> and ka64: \<open>ka < 2 ^ 64\<close> and wa1: \<open>1 \<le> width ws ds a\<close>
    using EA by (simp_all add: env_ok_def)
  have t: \<open>cwt ws (snd L1) (neg_t ka (snd L1 ! ka))\<close> \<open>cwidth ws (snd L1) (neg_t ka (snd L1 ! ka)) = snd L1 ! ka\<close>
    using neg_t_env[OF EA] wa by simp_all
  have c: \<open>cws_le ws (snd L1) (neg_t ka (snd L1 ! ka)) (width ws ds a)\<close> by (intro neg_t_le) (simp_all add: ka64[simplified] wa wa1 Suc_0_le[OF wa1])
  have k0: \<open>ccount ws (snd L1) (neg_t ka (snd L1 ! ka)) \<le> 15 * width ws ds a\<close> by (simp add: cc_neg ka64[simplified] wa)
  note C = pstep[OF L1 t p k0]
  have n: \<open>length (csubterms (neg_t ka (snd L1 ! ka))) \<le> 50\<close> by (simp add: neg_t_len msb_t_len)
  note C' = C[OF n]
  have A: \<open>lcnt ws L' \<le> lcnt ws L + ecount ws ds (Term_Neg a)\<close>
    using IH[THEN conjunct1] C'[THEN conjunct1] by (simp add: ec_simps)
  have B: \<open>lsmall ws M L \<longrightarrow> wsmall ws ds M (Term_Neg a) \<longrightarrow> lsmall ws M L'\<close>
    using IH[THEN conjunct2] C'[THEN conjunct2] cws_le_mono[OF c] wsmall_simps(2) half by blast
  show ?case using A B by blast
next
  case (Term_Bin op a b)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  obtain L2 kb where b: \<open>lower_m ws dm L1 b = (L2, kb)\<close> by (cases \<open>lower_m ws dm L1 b\<close>)
  have R: \<open>lower_bin_m L2 op ka kb = (L', k)\<close> using Term_Bin.prems(4) a b by simp
  have B2: \<open>bnd L2\<close> using bnd_pfx[OF lower_bin_m_pfx[OF R] Term_Bin.prems(5)] .
  have B1: \<open>bnd L1\<close> using bnd_pfx[OF lower_m_pfx[OF b] B2] .
  have wt: \<open>wt ws ds a\<close> \<open>wt ws ds b\<close> \<open>op \<noteq> Op_Concat \<longrightarrow> width ws ds b = width ws ds a\<close>
    using Term_Bin.prems(1) by simp_all
  note IHa = Term_Bin.IH(1)[OF wt(1) Term_Bin.prems(2,3) a B1]
  note Sa = lower_m_correct[OF wt(1) Term_Bin.prems(2,3) a B1]
  have L1: \<open>lok ws L1\<close> and X1: \<open>lext ws L L1\<close> using Sa lext_lok by blast+
  note IHb = Term_Bin.IH(2)[OF wt(2) L1 dm_ok_lext[OF Term_Bin.prems(2,3) X1] b B2]
  note Sb = lower_m_correct[OF wt(2) L1 dm_ok_lext[OF Term_Bin.prems(2,3) X1] b B2]
  have X2: \<open>lext ws L1 L2\<close> using Sb by blast
  have EA: \<open>env_ok ws L2 ka (width ws ds a)\<close> using Sa env_lext[OF _ X2] by blast
  have EB: \<open>env_ok ws L2 kb (width ws ds b)\<close> using Sb by blast
  note C = lower_bin_count[OF EA EB wt(3) R Term_Bin.prems(5)[unfolded bnd_def, THEN conjunct1]]
  have A: \<open>lcnt ws L' \<le> lcnt ws L + ecount ws ds (Term_Bin op a b)\<close>
    using IHa[THEN conjunct1] IHb[THEN conjunct1] C[THEN conjunct1] by (simp add: ec_simps)
  have B: \<open>lsmall ws M L \<longrightarrow> wsmall ws ds M (Term_Bin op a b) \<longrightarrow> lsmall ws M L'\<close>
    using IHa[THEN conjunct2] IHb[THEN conjunct2] C[THEN conjunct2] wsmall_simps(3) half2 by blast
  show ?case using A B by blast
next
  case (Term_Extract hi lo a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  let ?t = \<open>CoreTerm_Extract hi lo (cr ka)\<close> and ?w = \<open>unat hi - unat lo + 1\<close>
  have p: \<open>push_m L1 ?t ?w = (L', k)\<close> using Term_Extract.prems(4) a by simp
  have B1: \<open>bnd L1\<close> using bnd_pfx[OF pfx_push[OF p] Term_Extract.prems(5)] .
  have wt: \<open>wt ws ds a\<close> \<open>unat lo \<le> unat hi\<close> \<open>unat hi < width ws ds a\<close> using Term_Extract.prems(1) by simp_all
  note IH = Term_Extract.IH[OF wt(1) Term_Extract.prems(2,3) a B1]
  note S = lower_m_correct[OF wt(1) Term_Extract.prems(2,3) a B1]
  have EA: \<open>env_ok ws L1 ka (width ws ds a)\<close> using S by simp
  have L1: \<open>lok ws L1\<close> and wa: \<open>snd L1 ! ka = width ws ds a\<close> and ka64: \<open>ka < 2 ^ 64\<close> using EA by (simp_all add: env_ok_def)
  have t: \<open>cwt ws (snd L1) ?t\<close> \<open>cwidth ws (snd L1) ?t = ?w\<close> using cr_env[OF EA] wt(2,3) by simp_all
  have c: \<open>cws_le ws (snd L1) ?t (width ws ds a)\<close> using wt(3) by (intro cws_le_intros) (simp_all add: ka64[simplified] wa)
  have k0: \<open>ccount ws (snd L1) ?t \<le> 0\<close> by (simp add: cc_simps cc_cr)
  note C = pstep[OF L1 t p k0]
  have n: \<open>length (csubterms (?t)) \<le> 50\<close> by (simp add: neg_t_len msb_t_len)
  note C' = C[OF n]
  have A: \<open>lcnt ws L' \<le> lcnt ws L + ecount ws ds (Term_Extract hi lo a)\<close>
    using IH[THEN conjunct1] C'[THEN conjunct1] by (simp add: ec_simps)
  have B: \<open>lsmall ws M L \<longrightarrow> wsmall ws ds M (Term_Extract hi lo a) \<longrightarrow> lsmall ws M L'\<close>
    using IH[THEN conjunct2] C'[THEN conjunct2] cws_le_mono[OF c] wsmall_simps(4) half by blast
  show ?case using A B by blast
next
  case (Term_Repeat i a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  let ?wa = \<open>snd L1 ! ka\<close>
  obtain L2 k0 where p: \<open>push_m L1 (CoreTerm_Const []) 0 = (L2, k0)\<close> by (cases \<open>push_m L1 (CoreTerm_Const []) 0\<close>)
  obtain L3 k3 acc where f: \<open>foldl (repeat_step ka ?wa) (L2, k0, 0) [0..<unat i] = (L3, k3, acc)\<close>
    by (cases \<open>foldl (repeat_step ka ?wa) (L2, k0, 0) [0..<unat i]\<close>)
  have R: \<open>L' = L3\<close> \<open>k = k3\<close> using Term_Repeat.prems(4) a p f by (simp_all add: Let_def)
  have B2: \<open>bnd L2\<close> using bnd_pfx[OF repeat_fold_pfx[OF f] Term_Repeat.prems(5)[unfolded R]] .
  have B1: \<open>bnd L1\<close> using bnd_pfx[OF pfx_push[OF p] B2] .
  have wt: \<open>wt ws ds a\<close> \<open>1 \<le> unat i\<close> using Term_Repeat.prems(1) by simp_all
  note IH = Term_Repeat.IH[OF wt(1) Term_Repeat.prems(2,3) a B1]
  note S = lower_m_correct[OF wt(1) Term_Repeat.prems(2,3) a B1]
  have EA: \<open>env_ok ws L1 ka (width ws ds a)\<close> using S by simp
  have L1: \<open>lok ws L1\<close> and wa: \<open>?wa = width ws ds a\<close> and wa1: \<open>1 \<le> width ws ds a\<close> using EA by (simp_all add: env_ok_def)
  have t0: \<open>cwt ws (snd L1) (CoreTerm_Const [])\<close> \<open>cwidth ws (snd L1) (CoreTerm_Const []) = 0\<close> by simp_all
  have c0: \<open>cws_le ws (snd L1) (CoreTerm_Const []) 0\<close> by (simp add: cws_le_def)
  have kk: \<open>ccount ws (snd L1) (CoreTerm_Const []) \<le> 0\<close> by (simp add: cc_simps)
  note C0 = pstep[OF L1 t0 p kk]
  note P0 = push_correct[OF L1 t0 p, of \<open>\<lambda>vs. 0\<close>]
  have X2: \<open>lext ws L1 L2\<close> and k0: \<open>k0 < length (fst L2)\<close> \<open>snd L2 ! k0 = 0\<close> using P0 by simp_all
  have EA': \<open>env_ok ws L1 ka ?wa\<close> using EA wa by simp
  let ?W = \<open>width ws ds (Term_Repeat i a)\<close>
  have W: \<open>?wa * (0 + length [0..<unat i]) \<le> ?W\<close> by (simp add: wa mult.commute)
  have z0: \<open>(0 :: nat) = ?wa * 0\<close> by simp
  note LC = repeat_loop_count[OF EA' X2 k0 z0 f Term_Repeat.prems(5)[unfolded R] W]
  have n: \<open>length (csubterms (CoreTerm_Const [])) \<le> 50\<close> by simp
  note C0' = C0[OF n]
  have A: \<open>lcnt ws L3 \<le> lcnt ws L + ecount ws ds (Term_Repeat i a)\<close>
    using IH[THEN conjunct1] C0'[THEN conjunct1] LC[THEN conjunct1] by (simp add: ec_simps)
  have B: \<open>lsmall ws M L \<longrightarrow> wsmall ws ds M (Term_Repeat i a) \<longrightarrow> lsmall ws M L3\<close>
    using IH[THEN conjunct2] C0'[THEN conjunct2] LC[THEN conjunct2] cws_le_mono[OF c0] wsmall_simps(5) half
    by (meson zero_le)
  show ?case unfolding R using A B by blast
next
  case (Term_ZeroExtend i a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  let ?t = \<open>CoreTerm_Bin BinOp_Concat (CoreTerm_Const (replicate (unat i) False)) (cr ka)\<close>
  have p: \<open>push_m L1 ?t (snd L1 ! ka + unat i) = (L', k)\<close> using Term_ZeroExtend.prems(4) a by (simp add: Let_def)
  have B1: \<open>bnd L1\<close> using bnd_pfx[OF pfx_push[OF p] Term_ZeroExtend.prems(5)] .
  have wta: \<open>wt ws ds a\<close> using Term_ZeroExtend.prems(1) by simp
  note IH = Term_ZeroExtend.IH[OF wta Term_ZeroExtend.prems(2,3) a B1]
  note S = lower_m_correct[OF wta Term_ZeroExtend.prems(2,3) a B1]
  have EA: \<open>env_ok ws L1 ka (width ws ds a)\<close> using S by simp
  have L1: \<open>lok ws L1\<close> and wa: \<open>snd L1 ! ka = width ws ds a\<close> and ka64: \<open>ka < 2 ^ 64\<close> using EA by (simp_all add: env_ok_def)
  let ?W = \<open>width ws ds a + unat i\<close>
  have wa1: \<open>1 \<le> width ws ds a\<close> using EA by (simp add: env_ok_def)
  have t: \<open>cwt ws (snd L1) ?t\<close> \<open>cwidth ws (snd L1) ?t = snd L1 ! ka + unat i\<close> using cr_env[OF EA] by (simp_all add: add.commute wa)
  have c: \<open>cws_le ws (snd L1) ?t ?W\<close>
    by (intro cws_le_intros) (simp_all add: ka64[simplified] wa cr_width[OF ka64] one_le_add[OF wa1])
  have k0: \<open>ccount ws (snd L1) ?t \<le> 0\<close> by (simp add: cc_simps cc_cr bcost_def)
  note C = pstep[OF L1 t p k0]
  have n: \<open>length (csubterms (?t)) \<le> 50\<close> by (simp add: neg_t_len msb_t_len)
  note C' = C[OF n]
  have A: \<open>lcnt ws L' \<le> lcnt ws L + ecount ws ds (Term_ZeroExtend i a)\<close>
    using IH[THEN conjunct1] C'[THEN conjunct1] by (simp add: ec_simps)
  have B: \<open>lsmall ws M L \<longrightarrow> wsmall ws ds M (Term_ZeroExtend i a) \<longrightarrow> lsmall ws M L'\<close>
    using IH[THEN conjunct2] C'[THEN conjunct2] cws_le_mono[OF c] wsmall_simps(6) half by blast
  show ?case using A B by blast
next
  case (Term_SignExtend i a)
  let ?wa = \<open>width ws ds a\<close>
  have wta: \<open>wt ws ds a\<close> using Term_SignExtend.prems(1) by simp
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  let ?t = \<open>CoreTerm_Bin BinOp_Concat
             (CoreTerm_Ite (msb_t ka ?wa) (CoreTerm_Const (replicate (unat i) True)) (CoreTerm_Const (replicate (unat i) False)))
             (cr ka)\<close>
  have p0: \<open>push_m L1 (CoreTerm_Bin BinOp_Concat
             (CoreTerm_Ite (msb_t ka (snd L1 ! ka)) (CoreTerm_Const (replicate (unat i) True)) (CoreTerm_Const (replicate (unat i) False)))
             (cr ka)) (snd L1 ! ka + unat i) = (L', k)\<close>
    using Term_SignExtend.prems(4) a by (simp add: Let_def)
  have B1: \<open>bnd L1\<close> using bnd_pfx[OF pfx_push[OF p0] Term_SignExtend.prems(5)] .
  note IH = Term_SignExtend.IH[OF wta Term_SignExtend.prems(2,3) a B1]
  note S = lower_m_correct[OF wta Term_SignExtend.prems(2,3) a B1]
  have EA: \<open>env_ok ws L1 ka ?wa\<close> using S by simp
  have L1: \<open>lok ws L1\<close> and wa: \<open>snd L1 ! ka = ?wa\<close> and ka64: \<open>ka < 2 ^ 64\<close> and wa1: \<open>1 \<le> ?wa\<close> and wa64: \<open>?wa < 2 ^ 64\<close>
    using EA by (simp_all add: env_ok_def)
  have p: \<open>push_m L1 ?t (?wa + unat i) = (L', k)\<close> using p0 unfolding wa .
  let ?W = \<open>?wa + unat i\<close>
  have t: \<open>cwt ws (snd L1) ?t\<close> \<open>cwidth ws (snd L1) ?t = ?W\<close> by (simp_all add: cr_env[OF EA] msb_t_env[OF EA] add.commute)
  have c: \<open>cws_le ws (snd L1) ?t ?W\<close>
    by (intro cws_le_intros msb_t_le)
       (simp_all add: ka64[simplified] wa wa1 wa64[simplified] cr_width[OF ka64] one_le_add[OF wa1] Suc_0_le[OF wa1])
  have k0: \<open>ccount ws (snd L1) ?t \<le> 5 * unat i\<close> by (simp add: cc_simps cc_cr cc_msb bcost_def)
  note C = pstep[OF L1 t p k0]
  have n: \<open>length (csubterms (?t)) \<le> 50\<close> by (simp add: neg_t_len msb_t_len)
  note C' = C[OF n]
  have A: \<open>lcnt ws L' \<le> lcnt ws L + ecount ws ds (Term_SignExtend i a)\<close>
    using IH[THEN conjunct1] C'[THEN conjunct1] by (simp add: ec_simps)
  have B: \<open>lsmall ws M L \<longrightarrow> wsmall ws ds M (Term_SignExtend i a) \<longrightarrow> lsmall ws M L'\<close>
    using IH[THEN conjunct2] C'[THEN conjunct2] cws_le_mono[OF c] wsmall_simps(7) half by blast
  show ?case using A B by blast
next
  case (Term_RotateLeft i a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  let ?wa = \<open>width ws ds a\<close> and ?r = \<open>unat i mod width ws ds a\<close>
  have wta: \<open>wt ws ds a\<close> using Term_RotateLeft.prems(1) by simp
  show ?case
  proof (cases \<open>unat i mod snd L1 ! ka = 0\<close>)
    case True
    have R: \<open>L' = L1\<close> using Term_RotateLeft.prems(4) a True by (simp add: Let_def)
    note IH = Term_RotateLeft.IH[OF wta Term_RotateLeft.prems(2,3) a Term_RotateLeft.prems(5)[unfolded R]]
    show ?thesis unfolding R using IH wsmall_simps(8) by (auto simp: ec_simps)
  next
    case False
    let ?t = \<open>CoreTerm_Bin BinOp_Concat
               (CoreTerm_Extract (word_of_nat (?wa - 1 - ?r)) 0 (cr ka))
               (CoreTerm_Extract (word_of_nat (?wa - 1)) (word_of_nat (?wa - ?r)) (cr ka))\<close>
    have p0: \<open>push_m L1 (CoreTerm_Bin BinOp_Concat
               (CoreTerm_Extract (word_of_nat (snd L1 ! ka - 1 - unat i mod snd L1 ! ka)) 0 (cr ka))
               (CoreTerm_Extract (word_of_nat (snd L1 ! ka - 1)) (word_of_nat (snd L1 ! ka - unat i mod snd L1 ! ka)) (cr ka)))
               (snd L1 ! ka) = (L', k)\<close>
      using Term_RotateLeft.prems(4) a False by (simp add: Let_def)
    have B1: \<open>bnd L1\<close> using bnd_pfx[OF pfx_push[OF p0] Term_RotateLeft.prems(5)] .
    note IH = Term_RotateLeft.IH[OF wta Term_RotateLeft.prems(2,3) a B1]
    note S = lower_m_correct[OF wta Term_RotateLeft.prems(2,3) a B1]
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
    have k0: \<open>ccount ws (snd L1) ?t \<le> 0\<close> by (simp add: cc_simps cc_cr bcost_def)
    note C = pstep[OF L1 t p k0]
  have n: \<open>length (csubterms (?t)) \<le> 50\<close> by (simp add: neg_t_len msb_t_len)
  note C' = C[OF n]
  have A: \<open>lcnt ws L' \<le> lcnt ws L + ecount ws ds (Term_RotateLeft i a)\<close>
    using IH[THEN conjunct1] C'[THEN conjunct1] by (simp add: ec_simps)
  have B: \<open>lsmall ws M L \<longrightarrow> wsmall ws ds M (Term_RotateLeft i a) \<longrightarrow> lsmall ws M L'\<close>
    using IH[THEN conjunct2] C'[THEN conjunct2] cws_le_mono[OF c] wsmall_simps(8) half by blast
  show ?thesis using A B by blast
  qed
next
  case (Term_RotateRight i a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  let ?wa = \<open>width ws ds a\<close> and ?r = \<open>unat i mod width ws ds a\<close>
  have wta: \<open>wt ws ds a\<close> using Term_RotateRight.prems(1) by simp
  show ?case
  proof (cases \<open>unat i mod snd L1 ! ka = 0\<close>)
    case True
    have R: \<open>L' = L1\<close> using Term_RotateRight.prems(4) a True by (simp add: Let_def)
    note IH = Term_RotateRight.IH[OF wta Term_RotateRight.prems(2,3) a Term_RotateRight.prems(5)[unfolded R]]
    show ?thesis unfolding R using IH wsmall_simps(9) by (auto simp: ec_simps)
  next
    case False
    let ?t = \<open>CoreTerm_Bin BinOp_Concat
               (CoreTerm_Extract (word_of_nat (?r - 1)) 0 (cr ka))
               (CoreTerm_Extract (word_of_nat (?wa - 1)) (word_of_nat ?r) (cr ka))\<close>
    have p0: \<open>push_m L1 (CoreTerm_Bin BinOp_Concat
               (CoreTerm_Extract (word_of_nat (unat i mod snd L1 ! ka - 1)) 0 (cr ka))
               (CoreTerm_Extract (word_of_nat (snd L1 ! ka - 1)) (word_of_nat (unat i mod snd L1 ! ka)) (cr ka)))
               (snd L1 ! ka) = (L', k)\<close>
      using Term_RotateRight.prems(4) a False by (simp add: Let_def)
    have B1: \<open>bnd L1\<close> using bnd_pfx[OF pfx_push[OF p0] Term_RotateRight.prems(5)] .
    note IH = Term_RotateRight.IH[OF wta Term_RotateRight.prems(2,3) a B1]
    note S = lower_m_correct[OF wta Term_RotateRight.prems(2,3) a B1]
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
    have k0: \<open>ccount ws (snd L1) ?t \<le> 0\<close> by (simp add: cc_simps cc_cr bcost_def)
    note C = pstep[OF L1 t p k0]
  have n: \<open>length (csubterms (?t)) \<le> 50\<close> by (simp add: neg_t_len msb_t_len)
  note C' = C[OF n]
  have A: \<open>lcnt ws L' \<le> lcnt ws L + ecount ws ds (Term_RotateRight i a)\<close>
    using IH[THEN conjunct1] C'[THEN conjunct1] by (simp add: ec_simps)
  have B: \<open>lsmall ws M L \<longrightarrow> wsmall ws ds M (Term_RotateRight i a) \<longrightarrow> lsmall ws M L'\<close>
    using IH[THEN conjunct2] C'[THEN conjunct2] cws_le_mono[OF c] wsmall_simps(9) half by blast
  show ?thesis using A B by blast
  qed
next
  case (Term_Ite c a b)
  obtain L1 kc where c: \<open>lower_m ws dm L c = (L1, kc)\<close> by (cases \<open>lower_m ws dm L c\<close>)
  obtain L2 ka where a: \<open>lower_m ws dm L1 a = (L2, ka)\<close> by (cases \<open>lower_m ws dm L1 a\<close>)
  obtain L3 kb where b: \<open>lower_m ws dm L2 b = (L3, kb)\<close> by (cases \<open>lower_m ws dm L2 b\<close>)
  let ?t = \<open>CoreTerm_Ite (cr kc) (cr ka) (cr kb)\<close>
  have p: \<open>push_m L3 ?t (snd L3 ! ka) = (L', k)\<close> using Term_Ite.prems(4) c a b by simp
  have B3: \<open>bnd L3\<close> using bnd_pfx[OF pfx_push[OF p] Term_Ite.prems(5)] .
  have B2: \<open>bnd L2\<close> using bnd_pfx[OF lower_m_pfx[OF b] B3] .
  have B1: \<open>bnd L1\<close> using bnd_pfx[OF lower_m_pfx[OF a] B2] .
  have wt: \<open>wt ws ds c\<close> \<open>wt ws ds a\<close> \<open>wt ws ds b\<close> \<open>width ws ds c = 1\<close> \<open>width ws ds a = width ws ds b\<close>
    using Term_Ite.prems(1) by simp_all
  note IHc = Term_Ite.IH(1)[OF wt(1) Term_Ite.prems(2,3) c B1]
  note Sc = lower_m_correct[OF wt(1) Term_Ite.prems(2,3) c B1]
  have L1: \<open>lok ws L1\<close> and X1: \<open>lext ws L L1\<close> using Sc lext_lok by blast+
  note D1 = dm_ok_lext[OF Term_Ite.prems(2,3) X1]
  note IHa = Term_Ite.IH(2)[OF wt(2) L1 D1 a B2]
  note Sa = lower_m_correct[OF wt(2) L1 D1 a B2]
  have L2: \<open>lok ws L2\<close> and X2: \<open>lext ws L1 L2\<close> using Sa lext_lok by blast+
  note D2 = dm_ok_lext[OF L1 D1 X2]
  note IHb = Term_Ite.IH(3)[OF wt(3) L2 D2 b B3]
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
  have cl: \<open>cws_le ws (snd L3) ?t ?wa\<close>
    by (intro cws_le_intros) (simp_all add: ka64[simplified] kb64[simplified] kc64[simplified] wa wb wc wa1 Suc_0_le[OF wa1])
  have k0: \<open>ccount ws (snd L3) ?t \<le> 5 * ?wa\<close> by (simp add: cc_simps cc_cr cr_width[OF ka64] wa)
  note C = pstep[OF L3 t p k0]
  have n: \<open>length (csubterms ?t) \<le> 50\<close> by simp
  note C' = C[OF n]
  have A: \<open>lcnt ws L' \<le> lcnt ws L + ecount ws ds (Term_Ite c a b)\<close>
    using IHc[THEN conjunct1] IHa[THEN conjunct1] IHb[THEN conjunct1] C'[THEN conjunct1] by (simp add: ec_simps)
  have B: \<open>lsmall ws M L \<longrightarrow> wsmall ws ds M (Term_Ite c a b) \<longrightarrow> lsmall ws M L'\<close>
    using IHc[THEN conjunct2] IHa[THEN conjunct2] IHb[THEN conjunct2] C'[THEN conjunct2] cws_le_mono[OF cl]
      wsmall_simps(10) half by blast
  show ?case using A B by blast
qed

subsection \<open>Facts for the loops\<close>

lemma ecount_append: \<open>wt ws ds t \<Longrightarrow> ecount ws (ds @ e) t = ecount ws ds t\<close>
proof -
  assume w: \<open>wt ws ds t\<close>
  have \<open>enode ws (ds @ e) u = enode ws ds u\<close> if \<open>u \<in> set (subterms t)\<close> for u
  proof -
    have \<open>wt ws ds u\<close> using wt_subterm[OF w that] .
    then show ?thesis by (cases u) (auto simp: enode_def wt_width_append)
  qed
  then show ?thesis unfolding ecount_def by (auto intro!: arg_cong[where f = sum_list] map_cong)
qed

lemma size_csub: \<open>Suc (size t) \<le> length (csubterms t)\<close>
  by (induction t) simp_all

lemma tbound_small:
  assumes \<open>length (csubterms t) \<le> n\<close> \<open>cws_le ws ds t M\<close>
  shows \<open>tbound ws ds t \<le> n + 2 * M + 2\<close>
proof -
  have ne: \<open>set (map (\<lambda>u. 2 * cwidth ws ds u + 2) (csubterms t)) \<noteq> {}\<close> by (cases t) simp_all
  have \<open>Max (set (map (\<lambda>u. 2 * cwidth ws ds u + 2) (csubterms t))) \<le> 2 * M + 2\<close>
    using assms(2) ne by (auto simp: cws_le_def intro!: Max.boundedI)
  then show ?thesis using size_csub[of t] assms(1) by (simp add: tbound_def)
qed

lemma lsmall_tbound: \<open>lsmall ws M L \<Longrightarrow> t \<in> set (fst L) \<Longrightarrow> tbound ws (snd L) t \<le> 2 * M + 52\<close>
  using tbound_small[of t 50 ws \<open>snd L\<close> M] by (auto simp: lsmall_def)

lemma lsmall_nil: \<open>lsmall ws M ([], [])\<close>
  by (simp add: lsmall_def)

end
