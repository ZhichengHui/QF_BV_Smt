theory QFBV_ElimSpec
  imports QFBV_LowerRefine QFBV_DpllWatch QFBV_Elim
begin

section \<open>The contracts of the elimination\<close>

text \<open>
  Every Rust function of the section ``Elimination of unconstrained definitions'' computes its
  functional model of \<^verbatim>\<open>QFBV_Elim\<close>. Lists of \<^verbatim>\<open>usize\<close> (counts, widths, kinds, marks) are
  related to the models through \<^term>\<open>map unat\<close>.
\<close>

subsection \<open>Indices in bounds\<close>

text \<open>The variables of \<open>t\<close> are below \<open>nv\<close> and its references below \<open>nr\<close>.\<close>
definition cidx :: \<open>nat \<Rightarrow> nat \<Rightarrow> CoreTerm \<Rightarrow> bool\<close> where
  \<open>cidx nv nr t \<equiv> \<forall>u \<in> set (csubterms t). (\<forall>x. is_var x u \<longrightarrow> x < nv) \<and> (\<forall>x. is_ref x u \<longrightarrow> x < nr)\<close>

lemma cidx_simps:
  \<open>cidx nv nr (CoreTerm_Var i) \<longleftrightarrow> unat i < nv\<close>
  \<open>cidx nv nr (CoreTerm_Ref i) \<longleftrightarrow> unat i < nr\<close>
  \<open>cidx nv nr (CoreTerm_Not a) \<longleftrightarrow> cidx nv nr a\<close>
  \<open>cidx nv nr (CoreTerm_Bin op a b) \<longleftrightarrow> cidx nv nr a \<and> cidx nv nr b\<close>
  \<open>cidx nv nr (CoreTerm_Extract hi lo a) \<longleftrightarrow> cidx nv nr a\<close>
  \<open>cidx nv nr (CoreTerm_Ite c a b) \<longleftrightarrow> cidx nv nr c \<and> cidx nv nr a \<and> cidx nv nr b\<close>
  by (auto simp: cidx_def is_var_def is_ref_def)

lemma cwt_cidx: \<open>cwt ws ds t \<Longrightarrow> cidx (length ws) (length ds) t\<close>
  using cwt_var_lt cwt_ref_lt by (auto simp: cidx_def)

lemma is_var_lt:
  assumes \<open>is_var x u\<close>
  shows \<open>x < 18446744073709551616\<close>
proof (cases u)
  case (CoreTerm_Var i)
  then show ?thesis using assms unat_lt2p[of i] by (simp add: is_var_def)
qed (use assms in \<open>simp_all add: is_var_def\<close>)

lemma cidx_64: \<open>cidx nv nr t \<Longrightarrow> cidx 18446744073709551616 nr t\<close>
  using is_var_lt by (auto simp: cidx_def)

text \<open>The widths of the subterms of \<open>t\<close> fit in a \<^verbatim>\<open>usize\<close>.\<close>
definition wfit :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> CoreTerm \<Rightarrow> bool\<close> where
  \<open>wfit ws ds t \<equiv> \<forall>u \<in> set (csubterms t). cwidth ws ds u < 2 ^ 64\<close>

lemma wfit_simps:
  \<open>wfit ws ds (CoreTerm_Not a) \<Longrightarrow> wfit ws ds a\<close>
  \<open>wfit ws ds (CoreTerm_Bin op a b) \<Longrightarrow> wfit ws ds a \<and> wfit ws ds b\<close>
  \<open>wfit ws ds (CoreTerm_Extract hi lo a) \<Longrightarrow> wfit ws ds a\<close>
  \<open>wfit ws ds (CoreTerm_Ite c a b) \<Longrightarrow> wfit ws ds c \<and> wfit ws ds a \<and> wfit ws ds b\<close>
  \<open>wfit ws ds t \<Longrightarrow> cwidth ws ds t < 2 ^ 64\<close>
  using csubterms_self[of t] by (auto simp: wfit_def)

lemma wfit_iff:
  \<open>wfit ws ds (CoreTerm_Not a) \<longleftrightarrow> cwidth ws ds a < 2 ^ 64 \<and> wfit ws ds a\<close>
  \<open>wfit ws ds (CoreTerm_Bin op a b) \<longleftrightarrow> cwidth ws ds (CoreTerm_Bin op a b) < 2 ^ 64 \<and> wfit ws ds a \<and> wfit ws ds b\<close>
  \<open>wfit ws ds (CoreTerm_Extract hi lo a) \<longleftrightarrow> unat hi - unat lo + 1 < 2 ^ 64 \<and> wfit ws ds a\<close>
  \<open>wfit ws ds (CoreTerm_Ite c a b) \<longleftrightarrow> cwidth ws ds a < 2 ^ 64 \<and> wfit ws ds c \<and> wfit ws ds a \<and> wfit ws ds b\<close>
  by (auto simp: wfit_def)

lemma unat_small:
  fixes w :: \<open>64 word\<close>
  shows \<open>unat w = 1 \<longleftrightarrow> w = 1\<close> \<open>unat w = 2 \<longleftrightarrow> w = 2\<close> \<open>unat w = 3 \<longleftrightarrow> w = 3\<close>
    \<open>unat w = 4 \<longleftrightarrow> w = 4\<close> \<open>unat w = Suc 0 \<longleftrightarrow> w = 1\<close>
  by (auto simp: word_unat_eq_iff)

text \<open>The constants of \<open>t\<close> have fewer than \<open>2 ^ 64\<close> bits.\<close>
definition cfit :: \<open>CoreTerm \<Rightarrow> bool\<close> where
  \<open>cfit t \<equiv> \<forall>bs. t = CoreTerm_Const bs \<longrightarrow> length bs < 2 ^ 64\<close>

lemma dce_steps:
  assumes \<open>\<forall>x \<in> set xs. d \<le> x\<close> \<open>length L = length Ds\<close>
  shows \<open>length (fst (foldl (dce_step DW) (L, Ds) xs)) = length L \<and> length (snd (foldl (dce_step DW) (L, Ds) xs)) = length Ds \<and>
    (\<forall>j<d. snd (foldl (dce_step DW) (L, Ds) xs) ! j = Ds ! j)\<close>
  using assms
proof (induction xs arbitrary: L Ds)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  obtain L1 Ds1 where st: \<open>dce_step DW (L, Ds) x = (L1, Ds1)\<close> by force
  have P: \<open>length L1 = length L\<close> \<open>length Ds1 = length Ds\<close> \<open>\<forall>j<d. Ds1 ! j = Ds ! j\<close>
    using st Cons.prems(1) by (auto simp: dce_step_def split: if_splits)
  have \<open>length L1 = length Ds1\<close> using P Cons.prems(2) by simp
  then show ?case using Cons.IH[of L1 Ds1] Cons.prems(1) P st by simp
qed

subsection \<open>Preconditions of the reconstruction\<close>

text \<open>What the body of \<^verbatim>\<open>invert\<close> needs: indices in bounds, the operand it evaluates within
  the precondition of \<^verbatim>\<open>eval_term\<close>, and lengths for the bit-list helpers.\<close>
definition invert_pre :: \<open>nat \<Rightarrow> CoreTerm \<Rightarrow> nat \<Rightarrow> bool list \<Rightarrow> bool list list \<Rightarrow> bool list list \<Rightarrow> bool list list \<Rightarrow> bool\<close> where
  \<open>invert_pre N t k v m dv dv2 \<equiv>
     length dv2 < 2 ^ 64 \<and> length v \<le> N \<and> length v < 2 ^ 64 \<and>
     (case t of
        CoreTerm_Extract hi lo a \<Rightarrow>
          (let ia = ref_index_m a (length dv2) in
           ia < length dv2 \<and> unat hi < length (dv2 ! ia) \<and> length (dv2 ! ia) \<le> N \<and> length (dv2 ! ia) < 2 ^ 64)
      | CoreTerm_Bin op a b \<Rightarrow>
          (let ov = (if k = 3 then a else b) in
           Suc (size ov) \<le> N \<and> eok N m dv ov \<and> length v \<le> length (eval_m m dv ov) \<and>
           (op = BinOp_Eq \<longrightarrow> 0 < length v))
      | CoreTerm_Ite c a b \<Rightarrow>
          (let ia = ref_index_m a (length dv2) in ia < length dv \<and> length v \<le> length (dv ! ia))
      | _ \<Rightarrow> True)\<close>

text \<open>What the loop of \<^verbatim>\<open>settle\<close> needs at each of its (at most \<open>f\<close>) iterations.\<close>
fun spre :: \<open>nat \<Rightarrow> CoreTerm list \<Rightarrow> nat list \<Rightarrow> bool list list \<Rightarrow> nat \<Rightarrow> bool list list \<Rightarrow> bool list list \<Rightarrow>
    nat \<Rightarrow> bool list \<Rightarrow> bool\<close> where
  \<open>spre N D kind dv2 0 dv m j v = True\<close>
| \<open>spre N D kind dv2 (Suc f) dv m j v =
     (j < length dv \<and> j < length kind \<and> j < length D \<and>
      (kind ! j = 1 \<longrightarrow> var_index_m (D ! j) < length m) \<and>
      (kind ! j \<noteq> 1 \<longrightarrow> invert_pre N (D ! j) (kind ! j) v m (dv[j := v]) dv2 \<and>
         (case invert_m (D ! j) (kind ! j) v m (dv[j := v]) dv2 of (a, va) \<Rightarrow> spre N D kind dv2 f (dv[j := v]) m a va)))\<close>

text \<open>What the loop of \<^verbatim>\<open>reconstruct\<close> needs at definition \<open>k\<close>, in the state \<open>(dv, m)\<close>.\<close>
definition rstep_pre :: \<open>nat \<Rightarrow> CoreTerm list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool list list \<Rightarrow>
    bool list list \<times> bool list list \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>rstep_pre N D kind mark dv2 st k \<equiv>
     (case st of (dv, m) \<Rightarrow>
       mark ! k \<noteq> 1 \<longrightarrow>
         (kind ! k = 0 \<longrightarrow> Suc (size (D ! k)) \<le> N \<and> eok N m dv (D ! k)) \<and>
         (kind ! k \<noteq> 0 \<longrightarrow> k < length dv2 \<and> length (dv2 ! k) < 2 ^ 64 \<and>
            spre N D kind dv2 (Suc k) (dv @ [[]]) m k
              (if mark ! k = 2 then bits_one_m (length (dv2 ! k)) else dv2 ! k)))\<close>

definition recon_pre :: \<open>nat \<Rightarrow> CoreProblem \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> CoreProblem \<Rightarrow> bool list list \<Rightarrow> bool\<close> where
  \<open>recon_pre N q kind mark q2 m2 \<equiv>
     let D = CoreProblem_defs q; dv2 = eval_defs_m q2 m2 in
     edefs_ok N q2 m2 \<and> length (CoreProblem_defs q2) \<le> N \<and> length (CoreProblem_defs q2) < 2 ^ 64 \<and>
     length D \<le> N \<and> Suc (length D) < 2 ^ 64 \<and> length kind = length D \<and> length mark = length D \<and>
     (\<forall>k < length D. rstep_pre N D kind mark dv2 (foldl (recon_step D kind mark dv2) ([], m2) [0..<k]) k)\<close>

subsection \<open>Facts on terms\<close>

lemma size_sub: \<open>u \<in> set (csubterms t) \<Longrightarrow> size u \<le> size t\<close>
  by (induction t) auto

lemma cw_cong_w:
  assumes \<open>\<forall>u \<in> set (csubterms t). \<forall>x. is_ref x u \<longrightarrow> x < length ds \<and> x < length ds' \<and> ds ! x = ds' ! x\<close>
  shows \<open>cwidth ws ds t = cwidth ws ds' t\<close>
  using assms
proof (induction t)
  case (CoreTerm_Bin op a b)
  then have \<open>cwidth ws ds a = cwidth ws ds' a\<close> \<open>cwidth ws ds b = cwidth ws ds' b\<close> by auto
  then show ?case by (cases op) simp_all
qed (auto simp: is_ref_def)

lemma cw_cong:
  assumes \<open>\<forall>u \<in> set (csubterms t). \<forall>x. is_ref x u \<longrightarrow> x < length ds \<and> x < length ds' \<and> ds ! x = ds' ! x\<close>
  shows \<open>cwt ws ds t = cwt ws ds' t \<and> cwidth ws ds t = cwidth ws ds' t\<close>
proof -
  have \<open>cwt ws ds t = cwt ws ds' t\<close>
    using assms
  proof (induction t)
    case (CoreTerm_Bin op a b)
    have \<open>cwidth ws ds a = cwidth ws ds' a\<close> \<open>cwidth ws ds b = cwidth ws ds' b\<close>
      using cw_cong_w[of a ds ds' ws] cw_cong_w[of b ds ds' ws] CoreTerm_Bin.prems by auto
    moreover have \<open>cwt ws ds a = cwt ws ds' a\<close> \<open>cwt ws ds b = cwt ws ds' b\<close> using CoreTerm_Bin by auto
    ultimately show ?case by simp
  next
    case (CoreTerm_Extract hi lo a)
    then show ?case using cw_cong_w[of a ds ds' ws] by auto
  next
    case (CoreTerm_Ite c a b)
    have \<open>cwidth ws ds c = cwidth ws ds' c\<close> \<open>cwidth ws ds a = cwidth ws ds' a\<close> \<open>cwidth ws ds b = cwidth ws ds' b\<close>
      using cw_cong_w[of c ds ds' ws] cw_cong_w[of a ds ds' ws] cw_cong_w[of b ds ds' ws] CoreTerm_Ite.prems by auto
    moreover have \<open>cwt ws ds c = cwt ws ds' c\<close> \<open>cwt ws ds a = cwt ws ds' a\<close> \<open>cwt ws ds b = cwt ws ds' b\<close>
      using CoreTerm_Ite by auto
    ultimately show ?case by simp
  qed (auto simp: is_ref_def)
  then show ?thesis using cw_cong_w[OF assms] by simp
qed

text \<open>A subterm \<open>u0\<close> of a term \<open>T\<close> within the fuel satisfies the precondition of
  \<^verbatim>\<open>eval_term\<close> if the values of the definitions it refers to have their widths.\<close>
lemma eok_I:
  assumes T: \<open>u0 \<in> set (csubterms T)\<close> and W: \<open>cwt ws ds u0\<close> and ml: \<open>map length vs = ws\<close>
    and R: \<open>\<forall>u \<in> set (csubterms u0). \<forall>x. is_ref x u \<longrightarrow> x < length dv \<and> length (dv ! x) = ds ! x\<close>
    and B: \<open>tbound ws ds T \<le> N\<close> \<open>tbound ws ds T < 2 ^ 64\<close>
  shows \<open>eok N vs dv u0 \<and> Suc (size u0) \<le> N\<close>
proof -
  have C: \<open>cwt ws ds v = cwt ws (map length dv) v \<and> cwidth ws ds v = cwidth ws (map length dv) v\<close>
    if v: \<open>v \<in> set (csubterms u0)\<close> for v
  proof (rule cw_cong, intro ballI allI impI)
    fix u x assume u: \<open>u \<in> set (csubterms v)\<close> and r: \<open>is_ref x u\<close>
    have u0: \<open>u \<in> set (csubterms u0)\<close> using csubterms_trans[OF u v] .
    show \<open>x < length ds \<and> x < length (map length dv) \<and> ds ! x = map length dv ! x\<close>
      using R u0 r cwt_ref_lt[OF W u0 r] by fastforce
  qed
  have wt: \<open>cwt ws (map length dv) u0\<close> using C[OF csubterms_self] W by simp
  have wd: \<open>2 * cwidth ws (map length dv) v + 2 \<le> N \<and> 2 * cwidth ws (map length dv) v + 2 < 2 ^ 64\<close>
    if v: \<open>v \<in> set (csubterms u0)\<close> for v
    using C[OF v] tbound_mem[OF csubterms_trans[OF v T], of ws ds] B by simp
  have \<open>Suc (size u0) \<le> N\<close> using size_sub[OF T] tbound_size[of T ws ds] B by simp
  then show ?thesis using wt wd ml by (simp add: eok_def)
qed

locale elim_fuel = elim_prob +
  fixes N :: nat
  assumes fbN: \<open>fuel_bound q \<le> N\<close> and fb64: \<open>fuel_bound q < 2 ^ 64\<close>
begin

lemma tb: \<open>t \<in> set eD \<or> t \<in> set eA \<Longrightarrow> tbound ews eds t \<le> N \<and> tbound ews eds t < 2 ^ 64\<close>
  using fb_tbound[of t q] fbN fb64 by (auto simp: ews_def eds_def eD_def eA_def)

lemma tbD: \<open>j < en \<Longrightarrow> tbound ews eds (eD ! j) \<le> N \<and> tbound ews eds (eD ! j) < 2 ^ 64\<close>
  using tb[of \<open>eD ! j\<close>] by (simp add: en_def)

lemma en_fb: \<open>en + 2 \<le> N\<close> \<open>en + 2 < 2 ^ 64\<close> \<open>length eA + 2 \<le> N\<close> \<open>length eA + 2 < 2 ^ 64\<close>
  \<open>length ews + 2 \<le> N\<close> \<open>length ews + 2 < 2 ^ 64\<close>
  using fb_facts[of q] fbN fb64 by (simp_all add: en_def eD_def eA_def ews_def cvar_widths_def)

lemma eds_fb: \<open>j < en \<Longrightarrow> 2 * eds ! j + 2 \<le> N \<and> 2 * eds ! j + 2 < 2 ^ 64\<close>
  using tbound_mem[OF csubterms_self[of \<open>eD ! j\<close>], of ews eds] cwidth_eD[of j] tbD[of j] by simp

lemma take_cw:
  assumes k: \<open>k < en\<close> and u: \<open>u \<in> set (csubterms (eD ! k))\<close>
  shows \<open>cwidth ews (take k eds) u = cwidth ews eds u\<close>
proof (rule conjunct2[OF cw_cong], intro ballI allI impI)
  fix v x assume v: \<open>v \<in> set (csubterms u)\<close> and r: \<open>is_ref x v\<close>
  have \<open>x < length (take k eds)\<close> using cwt_ref_lt[OF wt_D[OF k] csubterms_trans[OF v u] r] .
  then show \<open>x < length (take k eds) \<and> x < length eds \<and> take k eds ! x = eds ! x\<close> by simp
qed

text \<open>What the analysis loop needs at definition \<open>k\<close>.\<close>
lemma ana_step_pre:
  assumes k: \<open>k < en\<close>
    and F: \<open>foldl (elim_step ews eD evc erc) ([], [], replicate en 0, []) [0..<k] = (DWa, KDa, MKa, DSa)\<close>
  shows \<open>DWa = take k eds \<and> KDa = take k kd \<and> length MKa = en \<and> DSa = take k d1 \<and>
    Suc (size (eD ! k)) \<le> N \<and> cwt ews DWa (eD ! k) \<and> wfit ews DWa (eD ! k) \<and> cwidth ews DWa (eD ! k) = eds ! k \<and>
    (\<forall>i. eD ! k = CoreTerm_Var i \<longrightarrow> unat i < length ews) \<and>
    free_kind_m eD DWa evc erc KDa (eD ! k) = kd ! k \<and>
    (2 \<le> kd ! k \<longrightarrow> cons k < en \<and> cons k < k \<and> (kd ! k = 4 \<longrightarrow> sec k < en) \<and>
       (eds ! cons k \<noteq> eds ! k \<longrightarrow> 1 \<le> eds ! k))\<close>
proof -
  obtain M where P: \<open>foldl (elim_step ews eD evc erc) ([], [], replicate en 0, []) [0..<k] = (take k eds, take k kd, M, take k d1)\<close>
    using ana_prefix[of k] k by auto
  have E: \<open>DWa = take k eds\<close> \<open>KDa = take k kd\<close> \<open>MKa = M\<close> \<open>DSa = take k d1\<close> using F P by simp_all
  have lM: \<open>length M = en\<close> using ana_fold[of k eD ews evc erc] P k by (simp add: en_def)
  have wt: \<open>cwt ews (take k eds) (eD ! k)\<close> using wt_D[OF k] .
  have wf: \<open>wfit ews (take k eds) (eD ! k)\<close>
    unfolding wfit_def using take_cw[OF k] tbound_mem[of _ \<open>eD ! k\<close> ews eds] tbD[OF k] by fastforce
  have sz: \<open>Suc (size (eD ! k)) \<le> N\<close> using tbound_size[of \<open>eD ! k\<close> ews eds] tbD[OF k] by simp
  have var: \<open>eD ! k = CoreTerm_Var i \<Longrightarrow> unat i < length ews\<close> for i using wt by simp
  have fk: \<open>free_kind_m eD (take k eds) evc erc (take k kd) (eD ! k) = kd ! k\<close> using ana(5)[OF k] by simp
  have c: \<open>2 \<le> kd ! k \<Longrightarrow> cons k < en \<and> cons k < k \<and> (kd ! k = 4 \<longrightarrow> sec k < en) \<and>
       (eds ! cons k \<noteq> eds ! k \<longrightarrow> 1 \<le> eds ! k)\<close>
    using cons_lt[OF k] kd_sec[OF k] kd_width[OF k] k by fastforce
  show ?thesis using E lM wt wf sz var fk c eds_nth[OF k] by simp
qed

end

text \<open>The marks after the definition \<open>t\<close> of kind \<open>c\<close> (the loop of \<^const>\<open>elim_step\<close>).\<close>
definition mark_upd :: \<open>CoreTerm \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list\<close> where
  \<open>mark_upd t c n mark \<equiv>
     if 2 \<le> c then
       (let mark1 = mark[consumed_m t c n := 1] in if c = 4 then mark1[second_m t n := 2] else mark1)
     else mark\<close>

definition ana_st :: \<open>CoreProblem \<Rightarrow> nat \<Rightarrow> nat list \<times> nat list \<times> nat list \<times> CoreTerm list\<close> where
  \<open>ana_st q k \<equiv> foldl (elim_step (cvar_widths q) (CoreProblem_defs q) (fst (occ_res q)) (snd (occ_res q)))
     ([], [], replicate (length (CoreProblem_defs q)) 0, []) [0..<k]\<close>

lemma ana_st_0: \<open>ana_st q 0 = ([], [], replicate (length (CoreProblem_defs q)) 0, [])\<close>
  by (simp add: ana_st_def)

lemma ana_st_Suc: \<open>ana_st q (Suc k) =
    elim_step (cvar_widths q) (CoreProblem_defs q) (fst (occ_res q)) (snd (occ_res q)) (ana_st q k) k\<close>
  by (simp add: ana_st_def)

lemma ana_st_res: \<open>ana_st q (length (CoreProblem_defs q)) = ana_res q\<close>
  by (simp add: ana_st_def ana_res_def Let_def)

lemma elim_step_eq:
  \<open>elim_step ws D vc rc (dw, kind, mark, defs) k =
    (dw @ [cwidth ws dw (D ! k)], kind @ [free_kind_m D dw vc rc kind (D ! k)],
     mark_upd (D ! k) (free_kind_m D dw vc rc kind (D ! k)) (length D) mark,
     defs @ [if 2 \<le> free_kind_m D dw vc rc kind (D ! k)
             then rewrite_m dw (consumed_m (D ! k) (free_kind_m D dw vc rc kind (D ! k)) (length D)) (cwidth ws dw (D ! k))
             else D ! k])\<close>
  by (simp add: elim_step_def mark_upd_def Let_def)

lemma ana_st_Suc_parts:
  shows \<open>fst (ana_st q (Suc k)) = fst (ana_st q k) @ [cwidth (cvar_widths q) (fst (ana_st q k)) (CoreProblem_defs q ! k)]\<close>
    \<open>fst (snd (ana_st q (Suc k))) = fst (snd (ana_st q k)) @
       [free_kind_m (CoreProblem_defs q) (fst (ana_st q k)) (fst (occ_res q)) (snd (occ_res q)) (fst (snd (ana_st q k))) (CoreProblem_defs q ! k)]\<close>
    \<open>fst (snd (snd (ana_st q (Suc k)))) = mark_upd (CoreProblem_defs q ! k)
       (free_kind_m (CoreProblem_defs q) (fst (ana_st q k)) (fst (occ_res q)) (snd (occ_res q)) (fst (snd (ana_st q k))) (CoreProblem_defs q ! k))
       (length (CoreProblem_defs q)) (fst (snd (snd (ana_st q k))))\<close>
    \<open>snd (snd (snd (ana_st q (Suc k)))) = snd (snd (snd (ana_st q k))) @
       [if 2 \<le> free_kind_m (CoreProblem_defs q) (fst (ana_st q k)) (fst (occ_res q)) (snd (occ_res q)) (fst (snd (ana_st q k))) (CoreProblem_defs q ! k)
        then rewrite_m (fst (ana_st q k))
               (consumed_m (CoreProblem_defs q ! k)
                  (free_kind_m (CoreProblem_defs q) (fst (ana_st q k)) (fst (occ_res q)) (snd (occ_res q)) (fst (snd (ana_st q k))) (CoreProblem_defs q ! k))
                  (length (CoreProblem_defs q)))
               (cwidth (cvar_widths q) (fst (ana_st q k)) (CoreProblem_defs q ! k))
        else CoreProblem_defs q ! k]\<close>
  using ana_st_Suc[of q k] elim_step_eq[of \<open>cvar_widths q\<close> \<open>CoreProblem_defs q\<close> \<open>fst (occ_res q)\<close> \<open>snd (occ_res q)\<close>
      \<open>fst (ana_st q k)\<close> \<open>fst (snd (ana_st q k))\<close> \<open>fst (snd (snd (ana_st q k)))\<close> \<open>snd (snd (snd (ana_st q k)))\<close> k]
  by simp_all

context elim_fuel
begin

lemma cfit_D: \<open>d \<in> set eD \<Longrightarrow> cfit d\<close>
  using tb[of d] tbound_mem[OF csubterms_self[of d], of ews eds] by (auto simp: cfit_def)

lemma ana_pre:
  assumes k: \<open>k < en\<close> and F: \<open>ana_st q k = (DWa, KDa, MKa, DSa)\<close>
  shows \<open>length DWa = k \<and> length KDa = k \<and> length MKa = en \<and> length DSa = k \<and>
    Suc (size (eD ! k)) \<le> N \<and> cwt ews DWa (eD ! k) \<and> wfit ews DWa (eD ! k) \<and> cwidth ews DWa (eD ! k) = eds ! k \<and>
    (\<forall>i. eD ! k = CoreTerm_Var i \<longrightarrow> unat i < length ews) \<and>
    free_kind_m eD DWa evc erc KDa (eD ! k) = kd ! k \<and>
    (2 \<le> kd ! k \<longrightarrow> cons k < en \<and> cons k < k \<and> (kd ! k = 4 \<longrightarrow> sec k < en) \<and>
       (DWa ! cons k \<noteq> eds ! k \<longrightarrow> 1 \<le> eds ! k)) \<and> eds ! k < 2 ^ 64\<close>
proof -
  have F': \<open>foldl (elim_step ews eD evc erc) ([], [], replicate en 0, []) [0..<k] = (DWa, KDa, MKa, DSa)\<close>
    using F by (simp add: ana_st_def ews_def eD_def evc_def erc_def en_def)
  note A = ana_step_pre[OF k F']
  have l: \<open>length DWa = k\<close> \<open>length KDa = k\<close> \<open>length DSa = k\<close> using A k len_eds ana(2,4) by auto
  have c: \<open>2 \<le> kd ! k \<Longrightarrow> DWa ! cons k = eds ! cons k\<close> using A cons_lt[OF k] by simp
  show ?thesis using A l c eds_fb[OF k] by auto
qed

lemma ana_facts:
  assumes k: \<open>k < en\<close>
  shows \<open>length (fst (ana_st q k)) = k\<close> \<open>length (fst (snd (ana_st q k))) = k\<close>
    \<open>length (fst (snd (snd (ana_st q k)))) = en\<close>
    \<open>Suc (size (eD ! k)) \<le> N\<close> \<open>cwt ews (fst (ana_st q k)) (eD ! k)\<close> \<open>wfit ews (fst (ana_st q k)) (eD ! k)\<close>
    \<open>cwidth ews (fst (ana_st q k)) (eD ! k) = eds ! k\<close>
    \<open>free_kind_m eD (fst (ana_st q k)) evc erc (fst (snd (ana_st q k))) (eD ! k) = kd ! k\<close>
    \<open>2 \<le> kd ! k \<Longrightarrow> consumed_m (eD ! k) (kd ! k) en < k\<close>
    \<open>kd ! k = 4 \<Longrightarrow> second_m (eD ! k) en < k\<close>
    \<open>2 \<le> kd ! k \<Longrightarrow> fst (ana_st q k) ! consumed_m (eD ! k) (kd ! k) en \<noteq> eds ! k \<Longrightarrow> Suc 0 \<le> eds ! k\<close>
    \<open>eds ! k < 2 ^ 64\<close> \<open>eD ! k = CoreTerm_Var i \<Longrightarrow> unat i < length ews\<close>
    \<open>2 \<le> kd ! k \<Longrightarrow> consumed_m (eD ! k) (kd ! k) en < en\<close>
    \<open>kd ! k = 4 \<Longrightarrow> second_m (eD ! k) en < en\<close>
proof -
  obtain DWa KDa MKa DSa where F: \<open>ana_st q k = (DWa, KDa, MKa, DSa)\<close> by (cases \<open>ana_st q k\<close>) auto
  note A = ana_pre[OF k F]
  show \<open>length (fst (ana_st q k)) = k\<close> \<open>length (fst (snd (ana_st q k))) = k\<close>
    \<open>length (fst (snd (snd (ana_st q k)))) = en\<close>
    \<open>Suc (size (eD ! k)) \<le> N\<close> \<open>cwt ews (fst (ana_st q k)) (eD ! k)\<close> \<open>wfit ews (fst (ana_st q k)) (eD ! k)\<close>
    \<open>cwidth ews (fst (ana_st q k)) (eD ! k) = eds ! k\<close>
    \<open>free_kind_m eD (fst (ana_st q k)) evc erc (fst (snd (ana_st q k))) (eD ! k) = kd ! k\<close>
    \<open>eds ! k < 2 ^ 64\<close> \<open>eD ! k = CoreTerm_Var i \<Longrightarrow> unat i < length ews\<close>
    using A F by auto
  show \<open>2 \<le> kd ! k \<Longrightarrow> consumed_m (eD ! k) (kd ! k) en < k\<close> using A by (simp add: cons_def)
  show \<open>kd ! k = 4 \<Longrightarrow> second_m (eD ! k) en < k\<close> using kd_sec[OF k] by (simp add: sec_def)
  show \<open>2 \<le> kd ! k \<Longrightarrow> fst (ana_st q k) ! consumed_m (eD ! k) (kd ! k) en \<noteq> eds ! k \<Longrightarrow> Suc 0 \<le> eds ! k\<close>
    using A F kd_width[OF k] by (auto simp: cons_def)
  show \<open>2 \<le> kd ! k \<Longrightarrow> consumed_m (eD ! k) (kd ! k) en < en\<close> using A k by (simp add: cons_def)
  show \<open>kd ! k = 4 \<Longrightarrow> second_m (eD ! k) en < en\<close> using kd_sec[OF k] k by (simp add: sec_def)
qed


end

locale recon_fuel = recon_prob q m2 + elim_fuel q N for q m2 N
begin

text \<open>The inversion of a free definition within the fuel meets the precondition of \<^verbatim>\<open>invert\<close>.\<close>
lemma inv_pre_ok:
  assumes j: \<open>j < en\<close> and k2: \<open>2 \<le> kd ! j\<close> and P: \<open>invpre j v m dv m dv dv2\<close>
  shows \<open>invert_pre N (eD ! j) (kd ! j) v m dv dv2\<close>
proof -
  have lv: \<open>length v = eds ! j\<close> and ml: \<open>map length m = ews\<close> and d2: \<open>map length dv2 = eds\<close>
    and O: \<open>\<forall>u \<in> set (csubterms (eD ! j)). \<forall>x. is_ref x u \<and> x \<noteq> cons j \<longrightarrow>
        x < length dv \<and> x < length dv \<and> dv ! x = dv ! x \<and> length (dv ! x) = eds ! x \<and> dv ! x = eval_m m dv (eD ! x)\<close>
    using P unfolding invpre_def by blast+
  have n2: \<open>length dv2 = en\<close> using d2 len_eds by (metis length_map)
  have d2n: \<open>x < en \<Longrightarrow> length (dv2 ! x) = eds ! x\<close> for x using d2 n2 by (metis nth_map)
  have wtj: \<open>cwt ews eds (eD ! j)\<close> using wt_D'[OF j] .
  have E: \<open>cwidth ews eds (eD ! j) = eds ! j\<close> using cwidth_eD[OF j] .
  have once: \<open>rcnt [eD ! j] (cons j) = 1\<close> using cons_once[OF j k2] .
  have cj: \<open>cons j < j\<close> using cons_lt[OF j k2] .
  note TB = tbD[OF j]
  have lvN: \<open>length v \<le> N\<close> \<open>length v < 2 ^ 64\<close> using eds_fb[OF j] lv by simp_all
  have n64: \<open>length dv2 < 2 ^ 64\<close> using n2 en_fb by simp
  have OK: \<open>eok N m dv ob \<and> Suc (size ob) \<le> N \<and> length (eval_m m dv ob) = cwidth ews eds ob\<close>
    if ob: \<open>ob \<in> set (csubterms (eD ! j))\<close> and nr: \<open>\<forall>u \<in> set (csubterms ob). \<not> is_ref (cons j) u\<close> for ob
  proof -
    have tr: \<open>u \<in> set (csubterms ob) \<Longrightarrow> u \<in> set (csubterms (eD ! j))\<close> for u using csubterms_trans ob by blast
    have R: \<open>\<forall>u \<in> set (csubterms ob). \<forall>x. is_ref x u \<longrightarrow> x < length dv \<and> length (dv ! x) = eds ! x\<close>
      using O tr nr by fastforce
    have \<open>eok N m dv ob \<and> Suc (size ob) \<le> N\<close> using eok_I[OF ob wsub[OF wtj ob] ml R] TB by blast
    moreover have \<open>length (eval_m m dv ob) = cwidth ews eds ob\<close> by (rule eval_m_len[OF wsub[OF wtj ob] ml R])
    ultimately show ?thesis by simp
  qed
  note sh = free_kind_shape[OF ana(5)[OF j] k2]
  have tk: \<open>x < j \<Longrightarrow> take j eds ! x = eds ! x\<close> for x using j len_eds by simp
  have fo: \<open>free_once_m (take j kd) erc x \<Longrightarrow> x < j\<close> for x using fo_take j by blast
  consider
      (Not) a where \<open>eD ! j = CoreTerm_Not (CoreTerm_Ref a)\<close> \<open>kd ! j = 2\<close>
    | (Ext) hi lo a where \<open>eD ! j = CoreTerm_Extract hi lo (CoreTerm_Ref a)\<close> \<open>kd ! j = 2\<close>
    | (AX2) op i b where \<open>eD ! j = CoreTerm_Bin op (CoreTerm_Ref i) b\<close> \<open>op = BinOp_Add \<or> op = BinOp_Xor\<close> \<open>kd ! j = 2\<close>
    | (AX3) op a i where \<open>eD ! j = CoreTerm_Bin op a (CoreTerm_Ref i)\<close> \<open>op = BinOp_Add \<or> op = BinOp_Xor\<close> \<open>kd ! j = 3\<close>
    | (Eq2) i b where \<open>eD ! j = CoreTerm_Bin BinOp_Eq (CoreTerm_Ref i) b\<close> \<open>kd ! j = 2\<close> \<open>0 < eds ! unat i\<close>
    | (Eq3) a i where \<open>eD ! j = CoreTerm_Bin BinOp_Eq a (CoreTerm_Ref i)\<close> \<open>kd ! j = 3\<close> \<open>0 < eds ! unat i\<close>
    | (MD) op a b where \<open>eD ! j = CoreTerm_Bin op (CoreTerm_Ref a) (CoreTerm_Ref b)\<close> \<open>op = BinOp_Mul \<or> op = BinOp_Udiv\<close>
        \<open>kd ! j = 4\<close> \<open>unat a \<noteq> unat b\<close>
    | (Ite) x a b where \<open>eD ! j = CoreTerm_Ite (CoreTerm_Ref x) (CoreTerm_Ref a) (CoreTerm_Ref b)\<close> \<open>kd ! j = 2\<close>
        \<open>bit_const_m (eD ! unat a) < 2\<close> \<open>bit_const_m (eD ! unat b) < 2\<close> \<open>bit_const_m (eD ! unat a) \<noteq> bit_const_m (eD ! unat b)\<close>
    using sh fo tk by (elim disjE exE conjE) (blast | metis)+
  then show ?thesis
  proof cases
    case (Not a)
    then show ?thesis using n64 lvN by (simp add: invert_pre_def)
  next
    case (Ext hi lo a)
    have c: \<open>cons j = unat a\<close> using Ext by (simp add: cons_def consumed_m_def ref_index_m_def)
    have al: \<open>unat a < en\<close> using c cj j by simp
    have wa: \<open>unat hi < eds ! unat a\<close> using wtj Ext by simp
    show ?thesis using Ext n64 lvN n2 al wa d2n[OF al] eds_fb[OF al] by (simp add: invert_pre_def ref_index_m_def)
  next
    case (AX2 op i b)
    have c: \<open>cons j = unat i\<close> using AX2 by (auto simp: cons_def consumed_m_def ref_index_m_def)
    have \<open>rcnt [b] (unat i) = 0\<close> using once AX2 c by (simp add: rcnt_Bin rcnt_Ref)
    then have S: \<open>eok N m dv b \<and> Suc (size b) \<le> N \<and> length (eval_m m dv b) = cwidth ews eds b\<close>
      using OK[of b] AX2 c no_ref_of_rcnt0 by auto
    have w: \<open>cwidth ews eds b = eds ! j\<close> using wtj E AX2 by auto
    show ?thesis using AX2 S w lv n64 lvN by (auto simp: invert_pre_def)
  next
    case (AX3 op a i)
    have c: \<open>cons j = unat i\<close> using AX3 by (auto simp: cons_def consumed_m_def ref_index_m_def)
    have \<open>rcnt [a] (unat i) = 0\<close> using once AX3 c by (simp add: rcnt_Bin rcnt_Ref)
    then have S: \<open>eok N m dv a \<and> Suc (size a) \<le> N \<and> length (eval_m m dv a) = cwidth ews eds a\<close>
      using OK[of a] AX3 c no_ref_of_rcnt0 by auto
    have nc: \<open>op \<noteq> BinOp_Concat\<close> \<open>op \<noteq> BinOp_Eq\<close> \<open>op \<noteq> BinOp_Ult\<close> using AX3(2) by auto
    have we: \<open>cwidth ews eds (eD ! j) = cwidth ews eds a\<close> using AX3(1) nc by (cases op) simp_all
    show ?thesis using AX3 S we E lv n64 lvN by (auto simp: invert_pre_def)
  next
    case (Eq2 i b)
    have c: \<open>cons j = unat i\<close> using Eq2 by (simp add: cons_def consumed_m_def ref_index_m_def)
    have \<open>rcnt [b] (unat i) = 0\<close> using once Eq2 c by (simp add: rcnt_Bin rcnt_Ref)
    then have S: \<open>eok N m dv b \<and> Suc (size b) \<le> N \<and> length (eval_m m dv b) = cwidth ews eds b\<close>
      using OK[of b] Eq2 c no_ref_of_rcnt0 by auto
    have w: \<open>cwidth ews eds b = eds ! unat i\<close> \<open>eds ! j = 1\<close> using wtj E Eq2 by auto
    show ?thesis using Eq2 S w lv n64 lvN by (auto simp: invert_pre_def)
  next
    case (Eq3 a i)
    have c: \<open>cons j = unat i\<close> using Eq3 by (simp add: cons_def consumed_m_def ref_index_m_def)
    have \<open>rcnt [a] (unat i) = 0\<close> using once Eq3 c by (simp add: rcnt_Bin rcnt_Ref)
    then have S: \<open>eok N m dv a \<and> Suc (size a) \<le> N \<and> length (eval_m m dv a) = cwidth ews eds a\<close>
      using OK[of a] Eq3 c no_ref_of_rcnt0 by auto
    have w: \<open>cwidth ews eds a = eds ! unat i\<close> \<open>eds ! j = 1\<close> using wtj E Eq3 by auto
    show ?thesis using Eq3 S w lv n64 lvN by (auto simp: invert_pre_def)
  next
    case (MD op a b)
    have c: \<open>cons j = unat a\<close> using MD by (simp add: cons_def consumed_m_def ref_index_m_def)
    have rb: \<open>CoreTerm_Ref b \<in> set (csubterms (eD ! j))\<close> using MD by simp
    have nr: \<open>\<forall>u \<in> set (csubterms (CoreTerm_Ref b)). \<not> is_ref (cons j) u\<close> using c MD(4) by (simp add: is_ref_def)
    note S = OK[OF rb nr]
    have nc: \<open>op \<noteq> BinOp_Concat\<close> \<open>op \<noteq> BinOp_Eq\<close> \<open>op \<noteq> BinOp_Ult\<close> using MD(2) by auto
    have ww: \<open>eds ! unat a = eds ! unat b\<close> using wtj MD(1) nc by simp
    have we: \<open>cwidth ews eds (eD ! j) = eds ! unat a\<close> using MD(1) nc by (cases op) simp_all
    show ?thesis using MD S ww we E lv n64 lvN by (auto simp: invert_pre_def)
  next
    case (Ite x a b)
    have c: \<open>cons j = unat x\<close> using Ite by (simp add: cons_def consumed_m_def ref_index_m_def)
    have \<open>rcnt [CoreTerm_Ref a] (unat x) = 0\<close> using once Ite(1) c by (simp_all add: rcnt_Ite rcnt_Ref)
    then have ne: \<open>unat a \<noteq> unat x\<close> by (simp add: rcnt_Ref split: if_splits)
    have ra: \<open>unat a < length dv\<close> \<open>length (dv ! unat a) = eds ! unat a\<close>
      using O Ite ne c by (auto simp: is_ref_def)
    have w: \<open>eds ! j = eds ! unat a\<close> using wtj E Ite by auto
    show ?thesis using Ite ra w lv n64 lvN by (simp add: invert_pre_def ref_index_m_def)
  qed
qed

text \<open>The hypotheses of \<open>settle_ok\<close> carry over to the next iteration of the loop.\<close>
lemma settle_hyps:
  assumes j: \<open>j < en\<close> and k2: \<open>2 \<le> kd ! j\<close> and lv: \<open>length v = eds ! j\<close> and ld: \<open>length dv = L\<close>
    and jN: \<open>j < L\<close> and Ne: \<open>L \<le> en\<close> and ml: \<open>map length m = ews\<close>
    and S: \<open>\<forall>i<L. tp i < tp j \<longrightarrow> dv ! i = eval_m m dv (eD ! i) \<and> length (dv ! i) = eds ! i\<close>
    and T: \<open>\<forall>i<L. tp i < tp j \<and> tp i = i \<and> mk ! i = 2 \<longrightarrow> dv ! i = bits_one_m (eds ! i)\<close>
  shows \<open>invpre j v m (dv[j := v]) m (dv[j := v]) dv2 \<and>
    fst (invert_m (eD ! j) (kd ! j) v m (dv[j := v]) dv2) = cons j \<and>
    length (snd (invert_m (eD ! j) (kd ! j) v m (dv[j := v]) dv2)) = eds ! cons j \<and>
    cons j < en \<and> kd ! cons j \<noteq> 0 \<and> length (dv[j := v]) = L \<and> cons j < L \<and>
    (\<forall>i<L. tp i < tp (cons j) \<longrightarrow> dv[j := v] ! i = eval_m m (dv[j := v]) (eD ! i) \<and> length (dv[j := v] ! i) = eds ! i) \<and>
    (\<forall>i<L. tp i < tp (cons j) \<and> tp i = i \<and> mk ! i = 2 \<longrightarrow> dv[j := v] ! i = bits_one_m (eds ! i))\<close>
proof -
  let ?dv1 = \<open>dv[j := v]\<close>
  have cj: \<open>cons j < j\<close> \<open>kd ! cons j \<noteq> 0\<close> using kd_cons[OF j k2] by simp_all
  have tj: \<open>j \<le> tp j\<close> using tp_props[OF j] by simp
  have tc: \<open>tp (cons j) = tp j\<close> using tp_par[of \<open>cons j\<close>] mk_cons par_cons j k2 cj by simp
  have lj: \<open>leaf j < j\<close> using leaf_step[OF j k2] leaf_props[of \<open>cons j\<close>] cj j by simp
  have k0: \<open>kd ! j \<noteq> 0\<close> using k2 by simp
  have pre0: \<open>invpre j v m ?dv1 m ?dv1 dv2\<close>
  proof -
    have c1: \<open>\<forall>u \<in> set (csubterms (eD ! j)). \<forall>x. is_ref x u \<and> x \<noteq> cons j \<longrightarrow>
      x < length ?dv1 \<and> x < length ?dv1 \<and> ?dv1 ! x = ?dv1 ! x \<and> length (?dv1 ! x) = eds ! x \<and>
      ?dv1 ! x = eval_m m ?dv1 (eD ! x)\<close>
    proof (intro ballI allI impI)
      fix u x assume u: \<open>u \<in> set (csubterms (eD ! j))\<close> and rx: \<open>is_ref x u \<and> x \<noteq> cons j\<close>
      have x: \<open>x < j\<close> using ref_lt_D[OF j u] rx by simp
      have xm: \<open>mk ! x \<noteq> 1\<close>
      proof
        assume mx: \<open>mk ! x = 1\<close>
        then have \<open>j = par x\<close> using member_ref[of x j u] x j u rx by simp
        then show False using par[of x] mx x j rx by auto
      qed
      have tx: \<open>tp x = x\<close> using tp_non[of x] xm x j by simp
      have xN: \<open>x < L\<close> using x jN by simp
      have tlt: \<open>tp x < tp j\<close> using tx x tj by simp
      have Sx: \<open>dv ! x = eval_m m dv (eD ! x)\<close> \<open>length (dv ! x) = eds ! x\<close> using S xN tlt by blast+
      have e1: \<open>eval_m m ?dv1 (eD ! x) = eval_m m dv (eD ! x)\<close>
        by (rule eval_m_cong) (use ref_lt_D[of x] x j in fastforce)+
      have d1x: \<open>?dv1 ! x = dv ! x\<close> using x by simp
      show \<open>x < length ?dv1 \<and> x < length ?dv1 \<and> ?dv1 ! x = ?dv1 ! x \<and> length (?dv1 ! x) = eds ! x \<and>
          ?dv1 ! x = eval_m m ?dv1 (eD ! x)\<close>
        using Sx e1 xN ld d1x by simp
    qed
    have c3: \<open>kd ! j = 4 \<longrightarrow> ?dv1 ! sec j = bits_one_m (eds ! sec j)\<close>
    proof
      assume k4: \<open>kd ! j = 4\<close>
      have sj: \<open>sec j < j\<close> \<open>mk ! sec j = 2\<close> using kd_sec[OF j k4] mk_char(2)[of \<open>sec j\<close>] j k4 by auto
      have ts: \<open>tp (sec j) = sec j\<close> using tp_non[of \<open>sec j\<close>] sj j by simp
      have \<open>sec j < L\<close> \<open>tp (sec j) < tp j\<close> using sj ts tj jN by simp_all
      then have \<open>dv ! sec j = bits_one_m (eds ! sec j)\<close> using T ts sj by blast
      then show \<open>?dv1 ! sec j = bits_one_m (eds ! sec j)\<close> using sj by simp
    qed
    have c0: \<open>cons j < length ?dv1\<close> using cj jN ld by simp
    show ?thesis unfolding invpre_def by (intro conjI lv ml dv2P(1) c0 c1 c3) simp_all
  qed
  note I0 = inv_def[OF j k2 pre0]
  have S': \<open>\<forall>i<L. tp i < tp (cons j) \<longrightarrow> ?dv1 ! i = eval_m m ?dv1 (eD ! i) \<and> length (?dv1 ! i) = eds ! i\<close>
  proof (intro allI impI)
    fix i assume i: \<open>i < L\<close> \<open>tp i < tp (cons j)\<close>
    have ij: \<open>i \<noteq> j\<close> using i tc by auto
    have il: \<open>i < en\<close> using i Ne by simp
    have nr: \<open>\<not> is_ref j u\<close> if u: \<open>u \<in> set (csubterms (eD ! i))\<close> for u
    proof
      assume r: \<open>is_ref j u\<close>
      show False
      proof (cases \<open>mk ! j = 1\<close>)
        case True
        then have \<open>i = par j\<close> using member_ref[OF j True il u r] by simp
        then show False using tp_par[OF j True] i tc by simp
      next
        case False
        then have \<open>tp j = j\<close> using tp_non j by simp
        moreover have \<open>j < i\<close> using ref_lt_D[OF il u r] .
        ultimately show False using tp_props[OF il] i tc by simp
      qed
    qed
    have rr: \<open>\<forall>u \<in> set (csubterms (eD ! i)). \<forall>x. is_ref x u \<longrightarrow> ?dv1 ! x = dv ! x\<close>
    proof (intro ballI allI impI)
      fix u x assume u: \<open>u \<in> set (csubterms (eD ! i))\<close> and r: \<open>is_ref x u\<close>
      have \<open>x \<noteq> j\<close> using nr[OF u] r by auto
      then show \<open>?dv1 ! x = dv ! x\<close> by simp
    qed
    have e: \<open>eval_m m ?dv1 (eD ! i) = eval_m m dv (eD ! i)\<close> by (rule eval_m_cong) (use rr in simp_all)
    have tl: \<open>tp i < tp j\<close> using i tc by simp
    have Si: \<open>dv ! i = eval_m m dv (eD ! i)\<close> \<open>length (dv ! i) = eds ! i\<close> using S i(1) tl by blast+
    show \<open>?dv1 ! i = eval_m m ?dv1 (eD ! i) \<and> length (?dv1 ! i) = eds ! i\<close> using Si e ij by simp
  qed
  have T': \<open>\<forall>i<L. tp i < tp (cons j) \<and> tp i = i \<and> mk ! i = 2 \<longrightarrow> ?dv1 ! i = bits_one_m (eds ! i)\<close>
  proof (intro allI impI)
    fix i assume i: \<open>i < L\<close> \<open>tp i < tp (cons j) \<and> tp i = i \<and> mk ! i = 2\<close>
    then have ij: \<open>i \<noteq> j\<close> using tc by auto
    have \<open>dv ! i = bits_one_m (eds ! i)\<close> using T i tc by simp
    then show \<open>?dv1 ! i = bits_one_m (eds ! i)\<close> using ij by simp
  qed
  have L1: \<open>length (dv[j := v]) = L\<close> using ld by simp
  have c2: \<open>cons j < en\<close> \<open>cons j < L\<close> using cj j jN by simp_all
  show ?thesis using pre0 I0 S' T' cj(2) L1 c2 by blast
qed

text \<open>The loop of \<^verbatim>\<open>settle\<close> meets the preconditions of its iterations.\<close>
lemma settle_pre_ok:
  assumes \<open>j < en\<close> \<open>kd ! j \<noteq> 0\<close> \<open>length v = eds ! j\<close> \<open>length dv = L\<close> \<open>j < L\<close> \<open>L \<le> en\<close>
    \<open>map length m = ews\<close>
    \<open>\<forall>i<L. tp i < tp j \<longrightarrow> dv ! i = eval_m m dv (eD ! i) \<and> length (dv ! i) = eds ! i\<close>
    \<open>\<forall>i<L. tp i < tp j \<and> tp i = i \<and> mk ! i = 2 \<longrightarrow> dv ! i = bits_one_m (eds ! i)\<close>
  shows \<open>spre N eD kd dv2 f dv m j v\<close>
  using assms
proof (induction f arbitrary: j v dv m)
  case 0
  then show ?case by simp
next
  case (Suc g)
  note j = Suc.prems(1) and k0 = Suc.prems(2) and lv = Suc.prems(3) and ld = Suc.prems(4)
    and jN = Suc.prems(5) and Ne = Suc.prems(6) and ml = Suc.prems(7) and S = Suc.prems(8) and T = Suc.prems(9)
  have base: \<open>j < length dv\<close> \<open>j < length kd\<close> \<open>j < length eD\<close> using j jN ld ana(2) by (simp_all add: en_def)
  show ?case
  proof (cases \<open>kd ! j = 1\<close>)
    case True
    obtain i where i: \<open>eD ! j = CoreTerm_Var i\<close> \<open>unat i < length ews\<close> using kd_1[OF j True] by blast
    have \<open>var_index_m (eD ! j) < length m\<close> using i ml by (simp add: var_index_m_def) (metis length_map)
    then show ?thesis using base True by simp
  next
    case False
    then have k2: \<open>2 \<le> kd ! j\<close> using k0 by simp
    note H = settle_hyps[OF j k2 lv ld jN Ne ml S T]
    obtain c va where inv: \<open>invert_m (eD ! j) (kd ! j) v m (dv[j := v]) dv2 = (c, va)\<close> by force
    have ip: \<open>invert_pre N (eD ! j) (kd ! j) v m (dv[j := v]) dv2\<close> using inv_pre_ok[OF j k2] H by blast
    have cv: \<open>c = cons j\<close> \<open>length va = eds ! cons j\<close> using H inv by simp_all
    have IH: \<open>spre N eD kd dv2 g (dv[j := v]) m c va\<close>
      unfolding cv(1) by (rule Suc.IH) (use H cv(2) Ne ml in blast)+
    show ?thesis using base False ip inv IH by simp
  qed
qed

lemma rstep_ok:
  assumes k: \<open>k < en\<close> and I: \<open>rinv k dv m\<close>
  shows \<open>rstep_pre N eD kd mk dv2 (dv, m) k\<close>
proof -
  have L: \<open>length dv = k\<close> and Mlen: \<open>map length m = ews\<close>
    and LC: \<open>\<forall>i<k. tp i < k \<longrightarrow> dv ! i = eval_m m dv (eD ! i) \<and> length (dv ! i) = eds ! i\<close>
    and TO: \<open>\<forall>i<k. tp i = i \<and> kd ! i \<noteq> 0 \<longrightarrow> dv ! i = target i\<close>
    using I unfolding rinv_def by blast+
  have ke: \<open>Suc k \<le> en\<close> using k by simp
  have A: \<open>Suc (size (eD ! k)) \<le> N \<and> eok N m dv (eD ! k)\<close> if B: \<open>mk ! k \<noteq> 1\<close> \<open>kd ! k = 0\<close>
  proof -
    have R: \<open>\<forall>u \<in> set (csubterms (eD ! k)). \<forall>x. is_ref x u \<longrightarrow> x < length dv \<and> length (dv ! x) = eds ! x\<close>
    proof (intro ballI allI impI)
      fix u x assume u: \<open>u \<in> set (csubterms (eD ! k))\<close> and r: \<open>is_ref x u\<close>
      have x: \<open>x < k\<close> using ref_lt_D[OF k u r] .
      have \<open>mk ! x \<noteq> 1\<close>
      proof
        assume mx: \<open>mk ! x = 1\<close>
        then have \<open>k = par x\<close> using member_ref[of x k u] x k u r by simp
        then show False using par[of x] mx x k B by auto
      qed
      then have \<open>tp x = x\<close> using tp_non x k by simp
      then show \<open>x < length dv \<and> length (dv ! x) = eds ! x\<close> using LC x L by auto
    qed
    show ?thesis using eok_I[OF csubterms_self wt_D'[OF k] Mlen R] tbD[OF k] by blast
  qed
  have C: \<open>spre N eD kd dv2 (Suc k) (dv @ [[]]) m k (target k)\<close> if B: \<open>mk ! k \<noteq> 1\<close> \<open>kd ! k \<noteq> 0\<close>
  proof -
    have tkk: \<open>tp k = k\<close> using tp_non k B by simp
    have S: \<open>\<forall>i<Suc k. tp i < tp k \<longrightarrow> (dv @ [[]]) ! i = eval_m m (dv @ [[]]) (eD ! i) \<and> length ((dv @ [[]]) ! i) = eds ! i\<close>
    proof (intro allI impI)
      fix i assume i: \<open>i < Suc k\<close> \<open>tp i < tp k\<close>
      then have ik: \<open>i < k\<close> using tkk by (auto simp: less_Suc_eq)
      have tl: \<open>tp i < k\<close> using i tkk by simp
      have Li: \<open>dv ! i = eval_m m dv (eD ! i)\<close> \<open>length (dv ! i) = eds ! i\<close> using LC ik tl by blast+
      show \<open>(dv @ [[]]) ! i = eval_m m (dv @ [[]]) (eD ! i) \<and> length ((dv @ [[]]) ! i) = eds ! i\<close>
        using Li app_eval[of i dv m \<open>[]\<close>] k L ik by (simp add: nth_append)
    qed
    have T: \<open>\<forall>i<Suc k. tp i < tp k \<and> tp i = i \<and> mk ! i = 2 \<longrightarrow> (dv @ [[]]) ! i = bits_one_m (eds ! i)\<close>
    proof (intro allI impI)
      fix i assume i: \<open>i < Suc k\<close> \<open>tp i < tp k \<and> tp i = i \<and> mk ! i = 2\<close>
      then have ik: \<open>i < k\<close> using tkk by auto
      obtain p where p: \<open>p < en\<close> \<open>kd ! p = 4\<close> \<open>sec p = i\<close> using mk_char(2)[of i] i ik k by auto
      have ki: \<open>kd ! i \<noteq> 0\<close> using kd_sec[OF p(1,2)] p(3) by simp
      have \<open>dv ! i = target i\<close> using TO ik i ki by simp
      have l2: \<open>length (dv2 ! i) = eds ! i\<close> using dv2P(1,2) ik k by (metis nth_map less_trans)
      show \<open>(dv @ [[]]) ! i = bits_one_m (eds ! i)\<close>
        using \<open>dv ! i = target i\<close> ik L i l2 by (simp add: nth_append target_def)
    qed
    show ?thesis by (rule settle_pre_ok[OF k B(2) target_len[OF k] _ lessI ke Mlen S T]) (use L in simp)
  qed
  have l2: \<open>k < length dv2\<close> using dv2P(2) k by simp
  have l3: \<open>length (dv2 ! k) = eds ! k\<close> using dv2P(1) l2 by (metis nth_map)
  have l4: \<open>length (dv2 ! k) < 2 ^ 64\<close> using l3 eds_fb[OF k] by simp
  show ?thesis using A C l2 l4 by (simp add: rstep_pre_def target_def)
qed

lemma recon_pre_ok: \<open>recon_pre N q kd mk q2 m2\<close>
proof -
  have D: \<open>CoreProblem_defs q2 = D2\<close> by (simp add: q2_parts)
  have W: \<open>cdefs_wt ews [] D2\<close> \<open>cdef_widths ews [] D2 = eds\<close> using D2_defs by simp_all
  have cw: \<open>cdef_widths ews [] (take j D2) = take j eds\<close> if j: \<open>j < en\<close> for j
  proof -
    obtain e where \<open>cdef_widths ews [] D2 = cdef_widths ews [] (take j D2) @ e\<close>
      using cdef_widths_append[of ews \<open>[]\<close> \<open>take j D2\<close> \<open>drop j D2\<close>] cdef_widths_prefix by fastforce
    then have \<open>eds = cdef_widths ews [] (take j D2) @ e\<close> using W(2) by simp
    moreover have \<open>length (cdef_widths ews [] (take j D2)) = j\<close> using j D2(1) by (simp add: cdef_widths_length)
    ultimately show ?thesis by simp
  qed
  have B: \<open>2 * cwidth ews (take j eds) u + 2 \<le> N \<and> 2 * cwidth ews (take j eds) u + 2 < 2 ^ 64\<close>
    if j: \<open>j < en\<close> and u: \<open>u \<in> set (csubterms (D2 ! j))\<close> for j u
  proof -
    have wt: \<open>cwt ews (take j eds) (D2 ! j)\<close> using D2_wt[OF j] by simp
    have \<open>cwidth ews (take j eds) u = cwidth ews eds u\<close>
    proof (rule conjunct2[OF cw_cong], intro ballI allI impI)
      fix v x assume v: \<open>v \<in> set (csubterms u)\<close> and r: \<open>is_ref x v\<close>
      have \<open>x < length (take j eds)\<close> using cwt_ref_lt[OF wt csubterms_trans[OF v u] r] .
      then show \<open>x < length (take j eds) \<and> x < length eds \<and> take j eds ! x = eds ! x\<close> by simp
    qed
    then show ?thesis using tbound_mem[OF u, of ews eds] D2_size[OF j] tbD[OF j] by simp
  qed
  have Sz: \<open>Suc (size (D2 ! j)) \<le> N\<close> if j: \<open>j < en\<close> for j
    using tbound_size[of \<open>D2 ! j\<close> ews eds] D2_size[OF j] tbD[OF j] by simp
  have E: \<open>edefs_ok N q2 m2\<close>
    unfolding edefs_ok_def Let_def using ml2 D W(1) cw B Sz D2(1) en_fb by auto
  have R: \<open>rstep_pre N eD kd mk dv2 (foldl (recon_step eD kd mk dv2) ([], m2) [0..<k]) k\<close> if k: \<open>k < en\<close> for k
  proof -
    obtain dv m where f: \<open>foldl (recon_step eD kd mk dv2) ([], m2) [0..<k] = (dv, m)\<close> by force
    have \<open>rinv k dv m\<close> using rinv_fold[of k] k f by simp
    then show ?thesis using rstep_ok[OF k] f by simp
  qed
  show ?thesis
    unfolding recon_pre_def Let_def using E R D D2(1) en_fb ana(2,3)
    by (simp add: dv2_def eD_def en_def)
qed

end

subsection \<open>The facts \<^verbatim>\<open>solve\<close> needs\<close>

text \<open>The hypotheses of \<open>fuel_bound_lt\<close>.\<close>
definition fb_hyps :: \<open>CoreProblem \<Rightarrow> bool\<close> where
  \<open>fb_hyps p \<equiv>
     2 + sum_list (cvar_widths p) + length (CoreProblem_asserts p) +
       sum_list (map (ccount (cvar_widths p) (cdef_widths (cvar_widths p) [] (CoreProblem_defs p)))
                     (CoreProblem_defs p @ CoreProblem_asserts p)) < 2 ^ 63 \<and>
     length (cvar_widths p) < 2 ^ 63 \<and> length (CoreProblem_defs p) < 2 ^ 63 \<and>
     length (CoreProblem_asserts p) < 2 ^ 63 \<and>
     (\<forall>t \<in> set (CoreProblem_defs p @ CoreProblem_asserts p).
        tbound (cvar_widths p) (cdef_widths (cvar_widths p) [] (CoreProblem_defs p)) t < 2 ^ 63)\<close>

lemma fb_hyps_lt: \<open>cproblem_wt p \<Longrightarrow> fb_hyps p \<Longrightarrow> fuel_bound p < 2 ^ 64\<close>
  unfolding fb_hyps_def by (rule fuel_bound_lt) blast+

text \<open>The elimination keeps the problem within the bounds of the core solver; a model of the
  problem gives one of the result, and the reconstruction from a model of the result meets the
  precondition of \<^verbatim>\<open>reconstruct\<close> and is a model of the problem.\<close>
theorem elim_facts:
  assumes wt: \<open>cproblem_wt q\<close> and H: \<open>fb_hyps q\<close> and fN: \<open>fuel_bound q \<le> N\<close> and e: \<open>elim_m q = (q2, kd, mk)\<close>
  shows \<open>fuel_bound q < 2 ^ 64\<close> \<open>cproblem_wt q2\<close> \<open>csize_bound q2 \<le> csize_bound q\<close> \<open>fuel_bound q2 < 2 ^ 64\<close>
    \<open>cis_model q m \<Longrightarrow> cis_model q2 (elim_prob.m2_of q m)\<close>
    \<open>cis_model q2 m2 \<Longrightarrow> recon_pre N q kd mk q2 m2 \<and> cis_model q (reconstruct_m q kd mk q2 m2)\<close>
proof -
  show f64: \<open>fuel_bound q < 2 ^ 64\<close> using fb_hyps_lt[OF wt H] .
  have nlt: \<open>length (CoreProblem_defs q) < 2 ^ 64\<close> using fb_facts(3)[of q] f64 by simp
  interpret E: elim_fuel q N by unfold_locales (use wt nlt fN f64 in simp_all)
  have q2: \<open>q2 = E.q2\<close> \<open>kd = E.kd\<close> \<open>mk = E.mk\<close> using E.elim_parts e by simp_all
  show \<open>cproblem_wt q2\<close> using E.q2_wt q2 by simp
  show \<open>csize_bound q2 \<le> csize_bound q\<close> using E.elim_csize q2 by simp
  show \<open>fuel_bound q2 < 2 ^ 64\<close> using E.elim_fuel_lt H q2 unfolding fb_hyps_def by blast
  show \<open>cis_model q m \<Longrightarrow> cis_model q2 (elim_prob.m2_of q m)\<close> using E.elim_complete q2 by simp
  assume M: \<open>cis_model q2 m2\<close>
  have ml2: \<open>map length m2 = E.ews\<close> using M by (simp add: cis_model_def cis_assignment_def E.q2_ws q2)
  interpret R: recon_fuel q m2 N by unfold_locales (rule ml2)
  show \<open>recon_pre N q kd mk q2 m2 \<and> cis_model q (reconstruct_m q kd mk q2 m2)\<close>
    using R.recon_pre_ok E.recon_sound M q2 by simp
qed

context QFBV_ctx
begin

subsection \<open>Occurrence counts\<close>

definition bump_contract :: \<open>64 word list \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word list, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>bump_contract c i \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>unat i < length c\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>map unat r = bump_m (map unat c) (unat i) \<and> length r = length c\<rangle>)\<close>

lemma bump_spec [crush_specs]:
  shows \<open>\<Gamma>; bump c i \<Turnstile>\<^sub>F bump_contract c i\<close>
  apply (crush_boot f: bump_def contract: bump_contract_def)
  apply (crush_base simp add: word_less_nat_alt)
  apply (auto simp: bump_m_def map_update unat_word_ariths nth_map)
  done

definition count_occ_contract ::
  \<open>nat \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> CoreTerm \<Rightarrow> ('s, 64 word list \<times> 64 word list \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>count_occ_contract k vc rc t \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>Suc (size t) \<le> k \<and> cidx (length vc) (length rc) t\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>(map unat (fst r), map unat (fst (snd r))) = count_occ_m (map unat vc, map unat rc) t \<and>
           length (fst r) = length vc \<and> length (fst (snd r)) = length rc\<rangle>)\<close>

lemma count_occ_rec_step_spec:
  assumes IH: \<open>\<And>vc rc t. \<Gamma>; R vc rc t \<Turnstile>\<^sub>F count_occ_contract k vc rc t\<close>
  shows \<open>\<Gamma>; count_occ_rec_step R vc rc t \<Turnstile>\<^sub>F count_occ_contract (Suc k) vc rc t\<close>
proof (cases t)
  case (CoreTerm_Const bs)
  show ?thesis unfolding CoreTerm_Const
    apply (crush_boot f: count_occ_rec_step_def contract: count_occ_contract_def)
    apply (crush_base specs add: IH simp add: cidx_simps)
    done
next
  case (CoreTerm_Var i)
  show ?thesis unfolding CoreTerm_Var
    apply (crush_boot f: count_occ_rec_step_def contract: count_occ_contract_def)
    apply (crush_base specs add: IH simp add: cidx_simps)
    done
next
  case (CoreTerm_Ref i)
  show ?thesis unfolding CoreTerm_Ref
    apply (crush_boot f: count_occ_rec_step_def contract: count_occ_contract_def)
    apply (crush_base specs add: IH simp add: cidx_simps)
    done
next
  case (CoreTerm_Not a)
  show ?thesis unfolding CoreTerm_Not
    apply (crush_boot f: count_occ_rec_step_def contract: count_occ_contract_def)
    apply (crush_base specs add: IH simp add: cidx_simps)
    done
next
  case (CoreTerm_Bin op a b)
  show ?thesis unfolding CoreTerm_Bin
    apply (crush_boot f: count_occ_rec_step_def contract: count_occ_contract_def)
    apply (crush_base specs add: IH simp add: cidx_simps)
    done
next
  case (CoreTerm_Extract hi lo a)
  show ?thesis unfolding CoreTerm_Extract
    apply (crush_boot f: count_occ_rec_step_def contract: count_occ_contract_def)
    apply (crush_base specs add: IH simp add: cidx_simps)
    done
next
  case (CoreTerm_Ite c a b)
  show ?thesis unfolding CoreTerm_Ite
    apply (crush_boot f: count_occ_rec_step_def contract: count_occ_contract_def)
    apply (crush_base specs add: IH simp add: cidx_simps)
    done
qed

lemma count_occ_rec_spec:
  shows \<open>\<Gamma>; (count_occ_rec_step ^^ k) g vc rc t \<Turnstile>\<^sub>F count_occ_contract k vc rc t\<close>
proof (induction k arbitrary: vc rc t)
  case 0
  show ?case
    apply (ucincl_discharge\<open>intro satisfies_function_contractI\<close>)
    apply (subst wp_sstriple_iff)
    apply (simp add: count_occ_contract_def Let_def apure_precise_False asepconj_bot_zero2 bot_aentails_all)
    done
next
  case (Suc k)
  show ?case
    unfolding funpow.simps(2) comp_def by (rule count_occ_rec_step_spec) (rule Suc.IH)
qed

lemma count_occ_spec [crush_specs]:
  shows \<open>\<Gamma>; count_occ vc rc t \<Turnstile>\<^sub>F count_occ_contract urust_fuel vc rc t\<close>
  unfolding count_occ_def by (rule count_occ_rec_spec)

definition term_width_contract ::
  \<open>nat \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> CoreTerm \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>term_width_contract k ws dw t \<equiv>
     make_function_contract
       (can_alloc_reference \<star> \<langle>Suc (size t) \<le> k \<and> cwt (map unat ws) (map unat dw) t \<and> wfit (map unat ws) (map unat dw) t\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>unat r = cwidth (map unat ws) (map unat dw) t\<rangle>)\<close>

lemma term_width_rec_step_spec:
  assumes IH: \<open>\<And>ws dw t. \<Gamma>; R ws dw t \<Turnstile>\<^sub>F term_width_contract k ws dw t\<close>
  shows \<open>\<Gamma>; term_width_rec_step R ws dw t \<Turnstile>\<^sub>F term_width_contract (Suc k) ws dw t\<close>
proof (cases t)
  case (CoreTerm_Const bs)
  show ?thesis unfolding CoreTerm_Const
  proof (crush_boot f: term_width_rec_step_def contract: term_width_contract_def, goal_cases)
    case 1
    have L: \<open>length bs < 2 ^ 64\<close> using 1 wfit_simps(5)[of \<open>map unat ws\<close> \<open>map unat dw\<close> \<open>CoreTerm_Const bs\<close>] by simp
    note 1 L
    then show ?case by (crush_base inline: len_def simp add: unat_of_nat_eq)
  qed
next
  case (CoreTerm_Var i)
  show ?thesis unfolding CoreTerm_Var
    apply (crush_boot f: term_width_rec_step_def contract: term_width_contract_def)
    apply (crush_base simp add: nth_map)
    done
next
  case (CoreTerm_Ref i)
  show ?thesis unfolding CoreTerm_Ref
    apply (crush_boot f: term_width_rec_step_def contract: term_width_contract_def)
    apply (crush_base simp add: nth_map)
    done
next
  case (CoreTerm_Not a)
  show ?thesis unfolding CoreTerm_Not
  proof (crush_boot f: term_width_rec_step_def contract: term_width_contract_def, goal_cases)
    case 1
    have W: \<open>wfit (map unat ws) (map unat dw) a\<close> using 1 wfit_simps(1) by blast
    note 1 W
    then show ?case by (crush_base specs add: IH)
  qed
next
  case (CoreTerm_Bin op a b)
  show ?thesis unfolding CoreTerm_Bin
    apply (cases op)
    apply (all \<open>crush_boot f: term_width_rec_step_def contract: term_width_contract_def\<close>)
    apply (all \<open>crush_base specs add: IH simp add: wfit_iff unat_word_ariths\<close>)
    done
next
  case (CoreTerm_Extract hi lo a)
  show ?thesis unfolding CoreTerm_Extract
  proof (crush_boot f: term_width_rec_step_def contract: term_width_contract_def, goal_cases)
    case 1
    have W: \<open>cwidth (map unat ws) (map unat dw) a < 2 ^ 64\<close> using 1 wfit_simps(3,5) by blast
    have E: \<open>unat lo \<le> unat hi\<close> \<open>unat hi < cwidth (map unat ws) (map unat dw) a\<close> using 1 by simp_all
    have U: \<open>unat (hi - lo) = unat hi - unat lo\<close> using E(1) by (simp add: unat_sub word_le_nat_alt)
    have V: \<open>unat (hi - lo + 1) = unat hi - unat lo + 1\<close> using U E W by (simp add: unat_word_ariths)
    have X: \<open>unat hi - unat lo < 18446744073709551615\<close> using E W by simp
    note 1 E U V X
    then show ?case by (crush_base simp add: word_le_nat_alt)
  qed
next
  case (CoreTerm_Ite c a b)
  show ?thesis unfolding CoreTerm_Ite
  proof (crush_boot f: term_width_rec_step_def contract: term_width_contract_def, goal_cases)
    case 1
    have W: \<open>wfit (map unat ws) (map unat dw) a\<close> using 1 wfit_simps(4) by blast
    note 1 W
    then show ?case by (crush_base specs add: IH)
  qed
qed

lemma term_width_rec_spec:
  shows \<open>\<Gamma>; (term_width_rec_step ^^ k) g ws dw t \<Turnstile>\<^sub>F term_width_contract k ws dw t\<close>
proof (induction k arbitrary: ws dw t)
  case 0
  show ?case
    apply (ucincl_discharge\<open>intro satisfies_function_contractI\<close>)
    apply (subst wp_sstriple_iff)
    apply (simp add: term_width_contract_def Let_def apure_precise_False asepconj_bot_zero2 bot_aentails_all)
    done
next
  case (Suc k)
  show ?case
    unfolding funpow.simps(2) comp_def by (rule term_width_rec_step_spec) (rule Suc.IH)
qed

lemma term_width_spec [crush_specs]:
  shows \<open>\<Gamma>; term_width ws dw t \<Turnstile>\<^sub>F term_width_contract urust_fuel ws dw t\<close>
  unfolding term_width_def by (rule term_width_rec_spec)

subsection \<open>The small helpers\<close>

definition ref_index_contract :: \<open>CoreTerm \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>ref_index_contract t n \<equiv>
     make_function_contract can_alloc_reference
       (\<lambda>r. can_alloc_reference \<star> \<langle>unat r = ref_index_m t (unat n)\<rangle>)\<close>

lemma ref_index_spec [crush_specs]:
  shows \<open>\<Gamma>; ref_index t n \<Turnstile>\<^sub>F ref_index_contract t n\<close>
  by (cases t; crush_boot f: ref_index_def contract: ref_index_contract_def; crush_base simp add: ref_index_m_def)

definition bit_const_contract :: \<open>CoreTerm \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>bit_const_contract t \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>cfit t\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>unat r = bit_const_m t\<rangle>)\<close>

lemma bit_const_spec [crush_specs]:
  shows \<open>\<Gamma>; bit_const t \<Turnstile>\<^sub>F bit_const_contract t\<close>
  by (cases t; crush_boot f: bit_const_def contract: bit_const_contract_def;
      crush_base inline: len_def simp add: bit_const_m_def cfit_def unat_of_nat_eq word_unat_eq_iff)

definition free_once_contract :: \<open>64 word list \<Rightarrow> 64 word list \<Rightarrow> 64 word \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>free_once_contract kind rc i \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>length kind \<le> length rc \<and> length kind < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = free_once_m (map unat kind) (map unat rc) (unat i)\<rangle>)\<close>

lemma free_once_spec [crush_specs]:
  shows \<open>\<Gamma>; free_once kind rc i \<Turnstile>\<^sub>F free_once_contract kind rc i\<close>
  apply (crush_boot f: free_once_def contract: free_once_contract_def)
  apply (crush_base inline: len_def simp add: free_once_m_def word_less_nat_alt unat_of_nat_eq unat_small unat_gt_0)
  done

definition consumed_contract :: \<open>CoreTerm \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>consumed_contract t k n \<equiv>
     make_function_contract can_alloc_reference
       (\<lambda>r. can_alloc_reference \<star> \<langle>unat r = consumed_m t (unat k) (unat n)\<rangle>)\<close>

lemma consumed_spec [crush_specs]:
  shows \<open>\<Gamma>; consumed t k n \<Turnstile>\<^sub>F consumed_contract t k n\<close>
  by (cases t; crush_boot f: consumed_def contract: consumed_contract_def; crush_base simp add: consumed_m_def unat_small)

definition second_contract :: \<open>CoreTerm \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>second_contract t n \<equiv>
     make_function_contract can_alloc_reference
       (\<lambda>r. can_alloc_reference \<star> \<langle>unat r = second_m t (unat n)\<rangle>)\<close>

lemma second_spec [crush_specs]:
  shows \<open>\<Gamma>; second t n \<Turnstile>\<^sub>F second_contract t n\<close>
  by (cases t; crush_boot f: second_def contract: second_contract_def; crush_base simp add: second_m_def)

definition copy_op_contract :: \<open>BinOp \<Rightarrow> ('s, BinOp, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>copy_op_contract op \<equiv>
     make_function_contract can_alloc_reference (\<lambda>r. can_alloc_reference \<star> \<langle>r = op\<rangle>)\<close>

lemma copy_op_spec [crush_specs]:
  shows \<open>\<Gamma>; copy_op op \<Turnstile>\<^sub>F copy_op_contract op\<close>
  by (cases op; crush_boot f: copy_op_def contract: copy_op_contract_def; crush_base)

definition var_index_contract :: \<open>CoreTerm \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>var_index_contract t \<equiv>
     make_function_contract can_alloc_reference
       (\<lambda>r. can_alloc_reference \<star> \<langle>unat r = var_index_m t\<rangle>)\<close>

lemma var_index_spec [crush_specs]:
  shows \<open>\<Gamma>; var_index t \<Turnstile>\<^sub>F var_index_contract t\<close>
  by (cases t; crush_boot f: var_index_def contract: var_index_contract_def; crush_base simp add: var_index_m_def)

definition bits_one_contract :: \<open>64 word \<Rightarrow> ('s, bool list, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>bits_one_contract w \<equiv>
     make_function_contract can_alloc_reference
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = bits_one_m (unat w)\<rangle>)\<close>

lemma bits_one_spec [crush_specs]:
  shows \<open>\<Gamma>; bits_one w \<Turnstile>\<^sub>F bits_one_contract w\<close>
  apply (crush_boot f: bits_one_def contract: bits_one_contract_def)
  apply (crush_base simp add: bits_one_m_def word_less_nat_alt)
  done

definition copy_term_contract :: \<open>nat \<Rightarrow> CoreTerm \<Rightarrow> ('s, CoreTerm, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>copy_term_contract k t \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>Suc (size t) \<le> k\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = t\<rangle>)\<close>

lemma copy_term_rec_step_spec:
  assumes IH: \<open>\<And>t. \<Gamma>; R t \<Turnstile>\<^sub>F copy_term_contract k t\<close>
  shows \<open>\<Gamma>; copy_term_rec_step R t \<Turnstile>\<^sub>F copy_term_contract (Suc k) t\<close>
proof (cases t)
  case (CoreTerm_Const bs)
  show ?thesis unfolding CoreTerm_Const
    apply (crush_boot f: copy_term_rec_step_def contract: copy_term_contract_def)
    apply (crush_base specs add: IH)
    done
next
  case (CoreTerm_Var i)
  show ?thesis unfolding CoreTerm_Var
    apply (crush_boot f: copy_term_rec_step_def contract: copy_term_contract_def)
    apply (crush_base specs add: IH)
    done
next
  case (CoreTerm_Ref i)
  show ?thesis unfolding CoreTerm_Ref
    apply (crush_boot f: copy_term_rec_step_def contract: copy_term_contract_def)
    apply (crush_base specs add: IH)
    done
next
  case (CoreTerm_Not a)
  show ?thesis unfolding CoreTerm_Not
    apply (crush_boot f: copy_term_rec_step_def contract: copy_term_contract_def)
    apply (crush_base specs add: IH)
    done
next
  case (CoreTerm_Bin op a b)
  show ?thesis unfolding CoreTerm_Bin
    apply (crush_boot f: copy_term_rec_step_def contract: copy_term_contract_def)
    apply (crush_base specs add: IH)
    done
next
  case (CoreTerm_Extract hi lo a)
  show ?thesis unfolding CoreTerm_Extract
    apply (crush_boot f: copy_term_rec_step_def contract: copy_term_contract_def)
    apply (crush_base specs add: IH)
    done
next
  case (CoreTerm_Ite c a b)
  show ?thesis unfolding CoreTerm_Ite
    apply (crush_boot f: copy_term_rec_step_def contract: copy_term_contract_def)
    apply (crush_base specs add: IH)
    done
qed

lemma copy_term_rec_spec:
  shows \<open>\<Gamma>; (copy_term_rec_step ^^ k) g t \<Turnstile>\<^sub>F copy_term_contract k t\<close>
proof (induction k arbitrary: t)
  case 0
  show ?case
    apply (ucincl_discharge\<open>intro satisfies_function_contractI\<close>)
    apply (subst wp_sstriple_iff)
    apply (simp add: copy_term_contract_def Let_def apure_precise_False asepconj_bot_zero2 bot_aentails_all)
    done
next
  case (Suc k)
  show ?case
    unfolding funpow.simps(2) comp_def by (rule copy_term_rec_step_spec) (rule Suc.IH)
qed

lemma copy_term_spec [crush_specs]:
  shows \<open>\<Gamma>; copy_term t \<Turnstile>\<^sub>F copy_term_contract urust_fuel t\<close>
  unfolding copy_term_def by (rule copy_term_rec_spec)

definition mark_live_contract :: \<open>nat \<Rightarrow> bool list \<Rightarrow> CoreTerm \<Rightarrow> ('s, bool list, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>mark_live_contract k live t \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>Suc (size t) \<le> k \<and> cidx (2 ^ 64) (length live) t\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = mark_live_m live t\<rangle>)\<close>

lemma mark_live_rec_step_spec:
  assumes IH: \<open>\<And>live t. \<Gamma>; R live t \<Turnstile>\<^sub>F mark_live_contract k live t\<close>
  shows \<open>\<Gamma>; mark_live_rec_step R live t \<Turnstile>\<^sub>F mark_live_contract (Suc k) live t\<close>
proof (cases t)
  case (CoreTerm_Const bs)
  show ?thesis unfolding CoreTerm_Const
    apply (crush_boot f: mark_live_rec_step_def contract: mark_live_contract_def)
    apply (crush_base specs add: IH simp add: cidx_simps)
    done
next
  case (CoreTerm_Var i)
  show ?thesis unfolding CoreTerm_Var
    apply (crush_boot f: mark_live_rec_step_def contract: mark_live_contract_def)
    apply (crush_base specs add: IH simp add: cidx_simps)
    done
next
  case (CoreTerm_Ref i)
  show ?thesis unfolding CoreTerm_Ref
    apply (crush_boot f: mark_live_rec_step_def contract: mark_live_contract_def)
    apply (crush_base specs add: IH simp add: cidx_simps)
    done
next
  case (CoreTerm_Not a)
  show ?thesis unfolding CoreTerm_Not
    apply (crush_boot f: mark_live_rec_step_def contract: mark_live_contract_def)
    apply (crush_base specs add: IH simp add: cidx_simps)
    done
next
  case (CoreTerm_Bin op a b)
  show ?thesis unfolding CoreTerm_Bin
    apply (crush_boot f: mark_live_rec_step_def contract: mark_live_contract_def)
    apply (crush_base specs add: IH simp add: cidx_simps)
    done
next
  case (CoreTerm_Extract hi lo a)
  show ?thesis unfolding CoreTerm_Extract
    apply (crush_boot f: mark_live_rec_step_def contract: mark_live_contract_def)
    apply (crush_base specs add: IH simp add: cidx_simps)
    done
next
  case (CoreTerm_Ite c a b)
  show ?thesis unfolding CoreTerm_Ite
    apply (crush_boot f: mark_live_rec_step_def contract: mark_live_contract_def)
    apply (crush_base specs add: IH simp add: cidx_simps)
    done
qed

lemma mark_live_rec_spec:
  shows \<open>\<Gamma>; (mark_live_rec_step ^^ k) g live t \<Turnstile>\<^sub>F mark_live_contract k live t\<close>
proof (induction k arbitrary: live t)
  case 0
  show ?case
    apply (ucincl_discharge\<open>intro satisfies_function_contractI\<close>)
    apply (subst wp_sstriple_iff)
    apply (simp add: mark_live_contract_def Let_def apure_precise_False asepconj_bot_zero2 bot_aentails_all)
    done
next
  case (Suc k)
  show ?case
    unfolding funpow.simps(2) comp_def by (rule mark_live_rec_step_spec) (rule Suc.IH)
qed

lemma mark_live_spec [crush_specs]:
  shows \<open>\<Gamma>; mark_live live t \<Turnstile>\<^sub>F mark_live_contract urust_fuel live t\<close>
  unfolding mark_live_def by (rule mark_live_rec_spec)

subsection \<open>The loops of the elimination\<close>

definition count_terms_contract :: \<open>64 word list \<Rightarrow> 64 word list \<Rightarrow> CoreTerm list \<Rightarrow>
    ('s, 64 word list \<times> 64 word list \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>count_terms_contract vc rc ts \<equiv>
     make_function_contract
       (can_alloc_reference \<star> \<langle>length ts \<le> urust_fuel \<and> length ts < 2 ^ 64 \<and>
          (\<forall>t \<in> set ts. Suc (size t) \<le> urust_fuel \<and> cidx (length vc) (length rc) t)\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>(map unat (fst r), map unat (fst (snd r))) = foldl count_occ_m (map unat vc, map unat rc) ts \<and>
           length (fst r) = length vc \<and> length (fst (snd r)) = length rc\<rangle>)\<close>

lemma count_terms_spec [crush_specs]:
  shows \<open>\<Gamma>; count_terms vc rc ts \<Turnstile>\<^sub>F count_terms_contract vc rc ts\<close>
  apply (crush_boot f: count_terms_def contract: count_terms_contract_def)
  apply (crush_base inline: len_def)
  subgoal for vc_ref rc_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gv v gr r gi i. vc_ref \<mapsto>\<langle>\<top>\<rangle> gv\<down>v \<star> rc_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i \<le> length ts \<and> (map unat v, map unat r) = foldl count_occ_m (map unat vc, map unat rc) (take (unat i) ts) \<and>
                length v = length vc \<and> length r = length rc \<and> length ts - unat i \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gv v gr r gi i. vc_ref \<mapsto>\<langle>\<top>\<rangle> gv\<down>v \<star> rc_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i < length ts \<and> (map unat v, map unat r) = foldl count_occ_m (map unat vc, map unat rc) (take (unat i) ts) \<and>
                length v = length vc \<and> length r = length rc \<and> length ts - unat i \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: len_def simp add: word_less_nat_alt unat_of_nat_eq unat_of_nat_64 unat_word_Suc_simp unat_Suc_len antisym_conv take_Suc_conv_app_nth)
    done
  done

definition free_kind_contract :: \<open>CoreTerm list \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow>
    CoreTerm \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>free_kind_contract D dw vc rc kind t \<equiv>
     make_function_contract
       (can_alloc_reference \<star> \<langle>length kind \<le> length rc \<and> length kind < 2 ^ 64 \<and> length dw = length kind \<and>
          length kind \<le> length D \<and> (\<forall>i. t = CoreTerm_Var i \<longrightarrow> unat i < length vc) \<and> (\<forall>d \<in> set D. cfit d)\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>unat r = free_kind_m D (map unat dw) (map unat vc) (map unat rc) (map unat kind) t\<rangle>)\<close>

lemma free_kind_spec [crush_specs]:
  shows \<open>\<Gamma>; free_kind D dw vc rc kind t \<Turnstile>\<^sub>F free_kind_contract D dw vc rc kind t\<close>
proof (cases t)
  case (CoreTerm_Var i)
  show ?thesis unfolding CoreTerm_Var
    apply (crush_boot f: free_kind_def contract: free_kind_contract_def)
    apply (crush_base inline: len_def simp add: free_kind_m_def unat_small nth_map)
    done
next
  case (CoreTerm_Not a)
  show ?thesis unfolding CoreTerm_Not
    apply (crush_boot f: free_kind_def contract: free_kind_contract_def)
    apply (crush_base inline: len_def simp add: free_kind_m_def unat_small nth_map unat_of_nat_eq)
    done
next
  case (CoreTerm_Const bs)
  show ?thesis unfolding CoreTerm_Const
    apply (crush_boot f: free_kind_def contract: free_kind_contract_def)
    apply (crush_base inline: len_def simp add: free_kind_m_def)
    done
next
  case (CoreTerm_Ref i)
  show ?thesis unfolding CoreTerm_Ref
    apply (crush_boot f: free_kind_def contract: free_kind_contract_def)
    apply (crush_base inline: len_def simp add: free_kind_m_def)
    done
next
  case (CoreTerm_Bin op a b)
  show ?thesis unfolding CoreTerm_Bin
    apply (cases op)
    apply (all \<open>crush_boot f: free_kind_def contract: free_kind_contract_def\<close>)
    apply (all \<open>crush_base inline: len_def simp add: free_kind_m_def unat_small nth_map unat_of_nat_eq word_less_nat_alt\<close>)
    apply (auto simp: free_once_m_def nth_map word_unat_eq_iff)
    done
next
  case (CoreTerm_Extract hi lo a)
  show ?thesis unfolding CoreTerm_Extract
    apply (crush_boot f: free_kind_def contract: free_kind_contract_def)
    apply (crush_base inline: len_def simp add: free_kind_m_def unat_small nth_map unat_of_nat_eq word_less_nat_alt)
    done
next
  case (CoreTerm_Ite c a b)
  show ?thesis unfolding CoreTerm_Ite
    apply (crush_boot f: free_kind_def contract: free_kind_contract_def)
    apply (crush_base inline: len_def simp add: free_kind_m_def unat_small nth_map unat_of_nat_eq word_less_nat_alt)
    apply (auto simp: free_once_m_def nth_map word_unat_eq_iff)
    done
qed

definition rewrite_def_contract :: \<open>CoreTerm \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word list \<Rightarrow> 64 word \<Rightarrow> 64 word list \<Rightarrow>
    ('s, CoreTerm \<times> 64 word list \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>rewrite_def_contract t c w dw n mark \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
        \<langle>if 2 \<le> unat c then
           consumed_m t (unat c) (unat n) < length mark \<and> consumed_m t (unat c) (unat n) < length dw \<and>
           (unat c = 4 \<longrightarrow> second_m t (unat n) < length mark) \<and>
           (map unat dw ! consumed_m t (unat c) (unat n) \<noteq> unat w \<longrightarrow> Suc 0 \<le> unat w)
         else Suc (size t) \<le> urust_fuel\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>fst r = (if 2 \<le> unat c then rewrite_m (map unat dw) (consumed_m t (unat c) (unat n)) (unat w) else t) \<and>
           map unat (fst (snd r)) = mark_upd t (unat c) (unat n) (map unat mark) \<and> length (fst (snd r)) = length mark\<rangle>)\<close>

lemma rewrite_def_spec [crush_specs]:
  shows \<open>\<Gamma>; rewrite_def t c w dw n mark \<Turnstile>\<^sub>F rewrite_def_contract t c w dw n mark\<close>
  apply (crush_boot f: rewrite_def_def contract: rewrite_def_contract_def)
  apply (crush_base simp add: mark_upd_def rewrite_m_def map_update word_le_nat_alt unat_small nth_map)
  apply (simp_all add: cr_def)
  apply (metis word_unat.Rep_inverse)+
  done

definition ana_ok :: \<open>nat \<Rightarrow> CoreProblem \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> bool\<close> where
  \<open>ana_ok N q vc rc \<equiv> elim_fuel q N \<and> map unat vc = fst (occ_res q) \<and> map unat rc = snd (occ_res q)\<close>

definition analyse_contract :: \<open>CoreProblem \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow>
    ('s, 64 word list \<times> 64 word list \<times> 64 word list \<times> CoreTerm list \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>analyse_contract q vc rc \<equiv>
     make_function_contract
       (can_alloc_reference \<star> \<langle>ana_ok urust_fuel q vc rc\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>(map unat (fst r), map unat (fst (snd r)), map unat (fst (snd (snd r))), fst (snd (snd (snd r)))) = ana_res q\<rangle>)\<close>

lemma analyse_spec [crush_specs]:
  shows \<open>\<Gamma>; analyse q vc rc \<Turnstile>\<^sub>F analyse_contract q vc rc\<close>
proof (cases \<open>ana_ok urust_fuel q vc rc\<close>)
  case True
  then interpret E: elim_fuel q urust_fuel by (simp add: ana_ok_def)
  have V: \<open>map unat vc = E.evc\<close> \<open>map unat rc = E.erc\<close> \<open>fst (occ_res q) = E.evc\<close> \<open>snd (occ_res q) = E.erc\<close>
    using True by (simp_all add: ana_ok_def E.evc_def E.erc_def)
  have LV: \<open>length vc = length E.ews\<close> \<open>length rc = E.en\<close>
    using occ_res(1,2)[of q] arg_cong[OF V(1), of length] arg_cong[OF V(2), of length]
    by (simp_all add: E.evc_def E.erc_def E.ews_def E.en_def E.eD_def cvar_widths_def)
  have W: \<open>map unat (CoreProblem_widths q) = E.ews\<close> \<open>cvar_widths q = E.ews\<close> by (simp_all add: E.ews_def cvar_widths_def)
  have N: \<open>E.en < 2 ^ 64\<close> \<open>E.en \<le> urust_fuel\<close> \<open>E.en < 18446744073709551615\<close> using E.en_fb by simp_all
  have U: \<open>unat (word64_of_nat E.en) = E.en\<close> using N by (simp add: unat_of_nat_eq)
  have D: \<open>CoreProblem_defs q = E.eD\<close> \<open>length E.eD = E.en\<close> by (simp_all add: E.eD_def E.en_def)
  have CF: \<open>\<forall>d \<in> set E.eD. cfit d\<close> using E.cfit_D by blast
  have UP: \<open>unat r < E.en \<Longrightarrow> unat (r + 1) = Suc (unat r)\<close> for r :: \<open>64 word\<close>
    using N(1) by (intro unat_plus_one_of_less_bound[of _ E.en]) simp_all
  have N4: \<open>unat r < E.en \<Longrightarrow> unat r < 18446744073709551615\<close> for r :: \<open>64 word\<close> using N(3) by simp
  have U64: \<open>unat r < 18446744073709551616\<close> for r :: \<open>64 word\<close> using unat_lt2p[of r] by simp
  have S0: \<open>fst (ana_st q 0) = []\<close> \<open>fst (snd (ana_st q 0)) = []\<close> \<open>fst (snd (snd (ana_st q 0))) = replicate E.en 0\<close>
    \<open>snd (snd (snd (ana_st q 0))) = []\<close> by (simp_all add: ana_st_0 D)
  have SE: \<open>ana_st q E.en = ana_res q\<close> using ana_st_res[of q] D by simp
  note AF = E.ana_facts
  have UN: \<open>map unat xs = ys \<Longrightarrow> j < length xs \<Longrightarrow> unat (xs ! j) = ys ! j\<close> for xs :: \<open>64 word list\<close> and ys j
    by auto
  show ?thesis
    apply (crush_boot f: analyse_def contract: analyse_contract_def)
    apply (crush_base inline: len_def)
    subgoal for dw_ref kind_ref mark_ref defs_ref k_ref
      apply (ucincl_discharge\<open>
        rule_tac
          INV=\<open>\<lambda>c. \<Squnion>gw dwv gk kv gm mv gd dsv gi i. dw_ref \<mapsto>\<langle>\<top>\<rangle> gw\<down>dwv \<star> kind_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>kv \<star>
                 mark_ref \<mapsto>\<langle>\<top>\<rangle> gm\<down>mv \<star> defs_ref \<mapsto>\<langle>\<top>\<rangle> gd\<down>dsv \<star> k_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
                 \<langle>unat i \<le> E.en \<and> map unat dwv = fst (ana_st q (unat i)) \<and> map unat kv = fst (snd (ana_st q (unat i))) \<and>
                  map unat mv = fst (snd (snd (ana_st q (unat i)))) \<and> dsv = snd (snd (snd (ana_st q (unat i)))) \<and>
                  length dwv = unat i \<and> length kv = unat i \<and> length mv = E.en \<and> E.en - unat i \<le> c\<rangle>\<close> and
          INV'=\<open>\<lambda>c. \<Squnion>gw dwv gk kv gm mv gd dsv gi i. dw_ref \<mapsto>\<langle>\<top>\<rangle> gw\<down>dwv \<star> kind_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>kv \<star>
                 mark_ref \<mapsto>\<langle>\<top>\<rangle> gm\<down>mv \<star> defs_ref \<mapsto>\<langle>\<top>\<rangle> gd\<down>dsv \<star> k_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
                 \<langle>unat i < E.en \<and> map unat dwv = fst (ana_st q (unat i)) \<and> map unat kv = fst (snd (ana_st q (unat i))) \<and>
                  map unat mv = fst (snd (snd (ana_st q (unat i)))) \<and> dsv = snd (snd (snd (ana_st q (unat i)))) \<and>
                  length dwv = unat i \<and> length kv = unat i \<and> length mv = E.en \<and> E.en - unat i \<le> Suc c\<rangle>\<close> and
          \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_bounded_while_framedI\<close>)
      apply (crush_base inline: vec_push_def len_def simp add: D U N W V LV CF UP S0 SE AF ana_st_Suc_parts word_less_nat_alt N4 U64)
      done
    done
next
  case False
  then have F: \<open>ana_ok urust_fuel q vc rc = False\<close> by simp
  show ?thesis
    apply (ucincl_discharge\<open>intro satisfies_function_contractI\<close>)
    apply (subst wp_sstriple_iff)
    apply (simp add: analyse_contract_def F apure_precise_False asepconj_bot_zero2 bot_aentails_all)
    done
qed

definition mark_terms_contract :: \<open>bool list \<Rightarrow> CoreTerm list \<Rightarrow> ('s, bool list, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>mark_terms_contract live ts \<equiv>
     make_function_contract
       (can_alloc_reference \<star> \<langle>length ts \<le> urust_fuel \<and> length ts < 2 ^ 64 \<and>
          (\<forall>t \<in> set ts. Suc (size t) \<le> urust_fuel \<and> cidx (2 ^ 64) (length live) t)\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = foldl mark_live_m live ts\<rangle>)\<close>

lemma mark_terms_spec [crush_specs]:
  shows \<open>\<Gamma>; mark_terms live ts \<Turnstile>\<^sub>F mark_terms_contract live ts\<close>
  apply (crush_boot f: mark_terms_def contract: mark_terms_contract_def)
  apply (crush_base inline: len_def)
  subgoal for live_ref l_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gv v gi i. live_ref \<mapsto>\<langle>\<top>\<rangle> gv\<down>v \<star> l_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i \<le> length ts \<and> v = foldl mark_live_m live (take (unat i) ts) \<and> length ts - unat i \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gv v gi i. live_ref \<mapsto>\<langle>\<top>\<rangle> gv\<down>v \<star> l_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i < length ts \<and> v = foldl mark_live_m live (take (unat i) ts) \<and> length ts - unat i \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: len_def simp add: word_less_nat_alt unat_of_nat_eq unat_of_nat_64 unat_word_Suc_simp unat_Suc_len antisym_conv take_Suc_conv_app_nth mark_live_fold(1))
    done
  done

lemma nz: \<open>(r :: 64 word) \<noteq> 0 \<Longrightarrow> 0 < unat r\<close>
  by (simp add: unat_gt_0)

lemma dce_back:
  assumes \<open>0 < d\<close> \<open>d \<le> length defs\<close>
  shows \<open>foldl (dce_step DW) (live, defs) (rev [d - Suc 0..<length defs]) =
    dce_step DW (foldl (dce_step DW) (live, defs) (rev [d..<length defs])) (d - Suc 0)\<close>
proof -
  have \<open>[d - Suc 0..<length defs] = (d - Suc 0) # [d..<length defs]\<close> using assms by (simp add: upt_conv_Cons)
  then show ?thesis by simp
qed

definition dce_contract :: \<open>bool list \<Rightarrow> 64 word list \<Rightarrow> CoreTerm list \<Rightarrow> ('s, CoreTerm list, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>dce_contract live dw defs \<equiv>
     make_function_contract
       (can_alloc_reference \<star> \<langle>length live = length defs \<and> length dw = length defs \<and> length defs \<le> urust_fuel \<and>
          length defs < 2 ^ 64 \<and>
          (\<forall>j < length defs. Suc (size (defs ! j)) \<le> urust_fuel \<and> cidx (2 ^ 64) (length defs) (defs ! j))\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = snd (foldl (dce_step (map unat dw)) (live, defs) (rev [0..<length defs]))\<rangle>)\<close>

lemma dce_spec [crush_specs]:
  shows \<open>\<Gamma>; dce live dw defs \<Turnstile>\<^sub>F dce_contract live dw defs\<close>
  apply (crush_boot f: dce_def contract: dce_contract_def)
  apply (crush_base inline: len_def)
  subgoal for live_ref defs_ref d_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gl l gs ds gd d. live_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>l \<star> defs_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>ds \<star> d_ref \<mapsto>\<langle>\<top>\<rangle> gd\<down>d \<star> can_alloc_reference \<star>
               \<langle>unat d \<le> length defs \<and> foldl (dce_step (map unat dw)) (live, defs) (rev [unat d..<length defs]) = (l, ds) \<and>
                length l = length defs \<and> length ds = length defs \<and> (\<forall>j < unat d. ds ! j = defs ! j) \<and> unat d \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gl l gs ds gd d. live_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>l \<star> defs_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>ds \<star> d_ref \<mapsto>\<langle>\<top>\<rangle> gd\<down>d \<star> can_alloc_reference \<star>
               \<langle>0 < unat d \<and> unat d \<le> length defs \<and> foldl (dce_step (map unat dw)) (live, defs) (rev [unat d..<length defs]) = (l, ds) \<and>
                length l = length defs \<and> length ds = length defs \<and> (\<forall>j < unat d. ds ! j = defs ! j) \<and> unat d \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: len_def simp add: word_less_nat_alt unat_of_nat_eq unat_of_nat_64 unat_gt_0 unat_minus_one dce_back)
    apply (auto simp: dce_back dce_step_def nth_map word_le_nat_alt dest!: nz)
    done
  done

definition copy_terms_contract :: \<open>CoreTerm list \<Rightarrow> ('s, CoreTerm list, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>copy_terms_contract ts \<equiv>
     make_function_contract
       (can_alloc_reference \<star> \<langle>length ts \<le> urust_fuel \<and> length ts < 2 ^ 64 \<and> (\<forall>t \<in> set ts. Suc (size t) \<le> urust_fuel)\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = ts\<rangle>)\<close>

lemma copy_terms_spec [crush_specs]:
  shows \<open>\<Gamma>; copy_terms ts \<Turnstile>\<^sub>F copy_terms_contract ts\<close>
  apply (crush_boot f: copy_terms_def contract: copy_terms_contract_def)
  apply (crush_base inline: len_def)
  subgoal for r_ref a_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gv v gi i. r_ref \<mapsto>\<langle>\<top>\<rangle> gv\<down>v \<star> a_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i \<le> length ts \<and> v = take (unat i) ts \<and> length ts - unat i \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gv v gi i. r_ref \<mapsto>\<langle>\<top>\<rangle> gv\<down>v \<star> a_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i < length ts \<and> v = take (unat i) ts \<and> length ts - unat i \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: vec_push_def len_def simp add: word_less_nat_alt unat_of_nat_eq unat_of_nat_64 unat_word_Suc_simp unat_Suc_len antisym_conv take_Suc_conv_app_nth)
    done
  done

end

context elim_fuel
begin

lemma d1_facts:
  assumes j: \<open>j < en\<close>
  shows \<open>Suc (size (d1 ! j)) \<le> N\<close> \<open>cidx (2 ^ 64) en (d1 ! j)\<close>
proof -
  have e2: \<open>en + 2 \<le> N\<close> using en_fb by simp
  show \<open>Suc (size (d1 ! j)) \<le> N\<close>
  proof (cases \<open>2 \<le> kd ! j\<close>)
    case True
    then show ?thesis using ana(6)[OF j] e2 by (simp add: rewrite_m_def)
  next
    case False
    then show ?thesis using ana(6)[OF j] tbound_size[of \<open>eD ! j\<close> ews eds] tbD[OF j] by simp
  qed
  show \<open>cidx (2 ^ 64) en (d1 ! j)\<close>
    unfolding cidx_def using d1_refs[OF j] j is_var_lt by fastforce
qed

lemma occ_two: \<open>foldl count_occ_m (foldl count_occ_m (replicate (length ews) 0, replicate en 0) eD) eA = occ_res q\<close>
  by (simp add: occ_res_def ews_def eD_def eA_def en_def cvar_widths_def)

lemma dce_two: \<open>snd (foldl (dce_step eds) (L0, d1) (rev [0..<en])) = snd (dce_res q)\<close>
  using dce_DS by (simp add: DS_def)

lemma elim_m_eq: \<open>elim_m q = (make_CoreProblem (CoreProblem_widths q) (snd (dce_res q)) eA, kd, mk)\<close>
  by (simp add: elim_m_def kd_def mk_def eA_def)

end

context QFBV_ctx
begin

definition elim_contract :: \<open>CoreProblem \<Rightarrow> ('s, CoreProblem \<times> 64 word list \<times> 64 word list \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>elim_contract q \<equiv>
     make_function_contract
       (can_alloc_reference \<star> \<langle>cproblem_wt q \<and> fuel_bound q \<le> urust_fuel \<and> fuel_bound q < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>(fst r, map unat (fst (snd r)), map unat (fst (snd (snd r)))) = elim_m q\<rangle>)\<close>

lemma elim_spec [crush_specs]:
  shows \<open>\<Gamma>; elim q \<Turnstile>\<^sub>F elim_contract q\<close>
proof (cases \<open>cproblem_wt q \<and> fuel_bound q \<le> urust_fuel \<and> fuel_bound q < 2 ^ 64\<close>)
  case True
  have nlt: \<open>length (CoreProblem_defs q) < 2 ^ 64\<close> using fb_facts(3)[of q] True by simp
  interpret E: elim_fuel q urust_fuel by unfold_locales (use True nlt in simp_all)
  have EF: \<open>elim_fuel q urust_fuel\<close> by unfold_locales (use True nlt in simp_all)
  have D: \<open>CoreProblem_defs q = E.eD\<close> \<open>length E.eD = E.en\<close> \<open>CoreProblem_asserts q = E.eA\<close>
    by (simp_all add: E.eD_def E.en_def E.eA_def)
  have W: \<open>length (CoreProblem_widths q) = length E.ews\<close> by (simp add: E.ews_def cvar_widths_def)
  have N: \<open>E.en < 18446744073709551616\<close> \<open>E.en \<le> urust_fuel\<close> \<open>length E.eA \<le> urust_fuel\<close>
    \<open>length E.eA < 18446744073709551616\<close> \<open>length E.ews < 18446744073709551616\<close> using E.en_fb by simp_all
  have OR: \<open>occ_res q = (E.evc, E.erc)\<close> by (simp add: E.evc_def E.erc_def)
  have LL0: \<open>length E.L0 = E.en\<close> by (simp add: E.L0_def mark_live_fold(1))
  have U: \<open>unat (word64_of_nat E.en) = E.en\<close> \<open>unat (word64_of_nat (length E.ews)) = length E.ews\<close>
    using N by (simp_all add: unat_of_nat_eq)
  have PD: \<open>\<forall>t \<in> set E.eD. Suc (size t) \<le> urust_fuel \<and> cidx (length E.ews) E.en t\<close>
  proof
    fix t assume t: \<open>t \<in> set E.eD\<close>
    then obtain j where j: \<open>j < E.en\<close> \<open>t = E.eD ! j\<close> by (auto simp: in_set_conv_nth E.en_def)
    show \<open>Suc (size t) \<le> urust_fuel \<and> cidx (length E.ews) E.en t\<close>
      using j E.tbD[OF j(1)] tbound_size[of t E.ews E.eds] cwt_cidx[OF E.wt_D'[OF j(1)]] E.len_eds by simp
  qed
  have PA: \<open>\<forall>t \<in> set E.eA. Suc (size t) \<le> urust_fuel \<and> cidx (length E.ews) E.en t \<and> cidx 18446744073709551616 E.en t\<close>
  proof
    fix t assume t: \<open>t \<in> set E.eA\<close>
    have c: \<open>cidx (length E.ews) E.en t\<close> using cwt_cidx[OF conjunct1[OF E.wt_A[OF t]]] E.len_eds by simp
    have \<open>cidx 18446744073709551616 E.en t\<close> using cidx_64[OF c] .
    then show \<open>Suc (size t) \<le> urust_fuel \<and> cidx (length E.ews) E.en t \<and> cidx 18446744073709551616 E.en t\<close>
      using c E.tb[of t] t tbound_size[of t E.ews E.eds] by simp
  qed
  have PD1: \<open>\<forall>j < E.en. Suc (size (E.d1 ! j)) \<le> urust_fuel \<and> cidx 18446744073709551616 E.en (E.d1 ! j)\<close>
    using E.d1_facts by simp
  have AP: \<open>ana_res q = (E.eds, E.kd, E.mk, E.d1)\<close> by (rule E.ana_parts)
  have LL: \<open>length E.eds = E.en\<close> \<open>length E.kd = E.en\<close> \<open>length E.mk = E.en\<close> \<open>length E.d1 = E.en\<close>
    using E.len_eds E.ana(2,3,4) by simp_all
  have LM: \<open>map unat xs = ys \<Longrightarrow> length xs = length ys\<close> for xs :: \<open>64 word list\<close> and ys by auto
  show ?thesis
    apply (crush_boot f: elim_def contract: elim_contract_def)
    apply (crush_base inline: len_def
        simp add: D W N U PD PA PD1 AP LL LL0 OR ana_ok_def EF E.occ_two E.dce_two E.elim_m_eq mark_live_fold(1) E.L0_def[symmetric])
    apply (auto dest!: arg_cong[where f=length] simp: LL)
    done
next
  case False
  then have F: \<open>(cproblem_wt q \<and> fuel_bound q \<le> urust_fuel \<and> fuel_bound q < 2 ^ 64) = False\<close> by simp
  show ?thesis
    apply (ucincl_discharge\<open>intro satisfies_function_contractI\<close>)
    apply (subst wp_sstriple_iff)
    apply (simp only: elim_contract_def F)
    apply (simp add: apure_precise_False asepconj_bot_zero2 bot_aentails_all)
    done
qed

subsection \<open>Reconstruction\<close>

end

lemma eok_len_le: \<open>eok N vs dv t \<Longrightarrow> length (eval_m vs dv t) \<le> N \<and> length (eval_m vs dv t) < 18446744073709551616\<close>
  using eok_len[of N vs dv t] eok_self[of N vs dv t] by simp

lemma ext_word:
  fixes h :: \<open>64 word\<close>
  assumes \<open>L < 18446744073709551616\<close> \<open>unat h < L\<close>
  shows \<open>h \<le> word_of_nat L - 1\<close> \<open>1 \<le> (word_of_nat L :: 64 word)\<close>
    \<open>unat (word_of_nat L - 1 - h) = L - 1 - unat h\<close>
proof -
  have u: \<open>unat (word_of_nat L :: 64 word) = L\<close> using assms(1) by (simp add: unat_of_nat_eq)
  show \<open>1 \<le> (word_of_nat L :: 64 word)\<close> using u assms(2) by (simp add: word_le_nat_alt)
  then have a: \<open>unat (word_of_nat L - 1 :: 64 word) = L - 1\<close> using u by (simp add: unat_sub)
  show \<open>h \<le> word_of_nat L - 1\<close> using a assms(2) by (simp add: word_le_nat_alt)
  then show \<open>unat (word_of_nat L - 1 - h) = L - 1 - unat h\<close> using a by (simp add: unat_sub)
qed

lemma unat_inc_le:
  fixes i k :: \<open>64 word\<close>
  assumes \<open>unat i \<le> unat k\<close> \<open>Suc (unat k) < 18446744073709551616\<close>
  shows \<open>unat (i + 1) = Suc (unat i)\<close>
  using assms by (intro unat_plus_one_of_less_bound[of _ \<open>Suc (unat k)\<close>]) simp_all

lemma unat_sub_sub:
  fixes w h :: \<open>64 word\<close>
  assumes \<open>unat h < unat w\<close>
  shows \<open>unat (w - 1 - h) = unat w - 1 - unat h\<close>
proof -
  have \<open>1 \<le> w\<close> using assms by (simp add: word_le_nat_alt)
  then have a: \<open>unat (w - 1) = unat w - 1\<close> by (simp add: unat_sub)
  have \<open>h \<le> w - 1\<close> using assms a by (simp add: word_le_nat_alt)
  then show ?thesis using a by (simp add: unat_sub)
qed

context QFBV_ctx
begin

definition invert_contract :: \<open>CoreTerm \<Rightarrow> 64 word \<Rightarrow> bool list \<Rightarrow> bool list list \<Rightarrow> bool list list \<Rightarrow> bool list list \<Rightarrow>
    ('s, 64 word \<times> bool list \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>invert_contract t k v m dv dv2 \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>invert_pre urust_fuel t (unat k) v m dv dv2\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>unat (fst r) = fst (invert_m t (unat k) v m dv dv2) \<and> fst (snd r) = snd (invert_m t (unat k) v m dv dv2)\<rangle>)\<close>

lemma invert_spec [crush_specs]:
  shows \<open>\<Gamma>; invert t k v m dv dv2 \<Turnstile>\<^sub>F invert_contract t k v m dv dv2\<close>
proof (cases t)
  case (CoreTerm_Const bs)
  show ?thesis unfolding CoreTerm_Const
    apply (crush_boot f: invert_def contract: invert_contract_def)
    apply (crush_base inline: len_def simp add: invert_pre_def invert_m_def unat_of_nat_eq)
    done
next
  case (CoreTerm_Var i)
  show ?thesis unfolding CoreTerm_Var
    apply (crush_boot f: invert_def contract: invert_contract_def)
    apply (crush_base inline: len_def simp add: invert_pre_def invert_m_def unat_of_nat_eq)
    done
next
  case (CoreTerm_Ref i)
  show ?thesis unfolding CoreTerm_Ref
    apply (crush_boot f: invert_def contract: invert_contract_def)
    apply (crush_base inline: len_def simp add: invert_pre_def invert_m_def unat_of_nat_eq)
    done
next
  case (CoreTerm_Not a)
  show ?thesis unfolding CoreTerm_Not
    apply (crush_boot f: invert_def contract: invert_contract_def)
    apply (crush_base inline: len_def simp add: invert_pre_def invert_m_def unat_of_nat_eq)
    done
next
  case (CoreTerm_Extract hi lo a)
  show ?thesis unfolding CoreTerm_Extract
    apply (crush_boot f: invert_def contract: invert_contract_def)
    apply (crush_base inline: len_def simp add: invert_pre_def invert_m_def unat_of_nat_eq Let_def ext_word)
    done
next
  case (CoreTerm_Bin op a b)
  show ?thesis unfolding CoreTerm_Bin
    apply (cases op)
    apply (all \<open>crush_boot f: invert_def contract: invert_contract_def\<close>)
    apply (all \<open>crush_base inline: len_def simp add: invert_pre_def invert_m_def unat_of_nat_eq Let_def eok_len_le unat_small\<close>)
    done
next
  case (CoreTerm_Ite c a b)
  show ?thesis unfolding CoreTerm_Ite
    apply (crush_boot f: invert_def contract: invert_contract_def)
    apply (crush_base inline: vec_push_def len_def simp add: invert_pre_def invert_m_def unat_of_nat_eq Let_def)
    done
qed

end

text \<open>The precondition and the result of \<^verbatim>\<open>settle\<close>, kept folded in its contract.\<close>
definition settle_pre :: \<open>nat \<Rightarrow> CoreTerm list \<Rightarrow> nat list \<Rightarrow> bool list list \<Rightarrow> bool list list \<Rightarrow> bool list list \<Rightarrow>
    nat \<Rightarrow> bool list \<Rightarrow> bool\<close> where
  \<open>settle_pre Nf Ds Ks dvs dvv mv kx vv \<equiv> spre Nf Ds Ks dvs (Suc kx) dvv mv kx vv\<close>

definition settle_res :: \<open>CoreTerm list \<Rightarrow> nat list \<Rightarrow> bool list list \<Rightarrow> bool list list \<Rightarrow> bool list list \<Rightarrow>
    nat \<Rightarrow> bool list \<Rightarrow> bool list list \<times> bool list list\<close> where
  \<open>settle_res Ds Ks dvs dvv mv kx vv \<equiv> settle_m Ds Ks dvs (Suc kx) dvv mv kx vv\<close>

context QFBV_ctx
begin

definition settle_contract :: \<open>CoreTerm list \<Rightarrow> 64 word list \<Rightarrow> bool list list \<Rightarrow> bool list list \<Rightarrow> bool list list \<Rightarrow>
    64 word \<Rightarrow> bool list \<Rightarrow> ('s, bool list list \<times> bool list list \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>settle_contract D kind dv2 dv m k v \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
        \<langle>settle_pre urust_fuel D (map unat kind) dv2 dv m (unat k) v \<and> unat k < urust_fuel \<and> Suc (unat k) < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>(fst r, fst (snd r)) = settle_res D (map unat kind) dv2 dv m (unat k) v\<rangle>)\<close>

lemma settle_spec [crush_specs]:
  shows \<open>\<Gamma>; settle D kind dv2 dv m k v \<Turnstile>\<^sub>F settle_contract D kind dv2 dv m k v\<close>
  apply (crush_boot f: settle_def contract: settle_contract_def)
  apply (simp only: settle_pre_def settle_res_def)
  apply (crush_base)
  subgoal for dv_ref m_ref j_ref v_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>c. \<Squnion>gd dvv gm mv gj j gv vv gi i. dv_ref \<mapsto>\<langle>\<top>\<rangle> gd\<down>dvv \<star> m_ref \<mapsto>\<langle>\<top>\<rangle> gm\<down>mv \<star>
               j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> v_ref \<mapsto>\<langle>\<top>\<rangle> gv\<down>vv \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i \<le> Suc (unat k) \<and>
                settle_m D (map unat kind) dv2 (Suc (unat k) - unat i) dvv mv (unat j) vv =
                  settle_m D (map unat kind) dv2 (Suc (unat k)) dv m (unat k) v \<and>
                spre urust_fuel D (map unat kind) dv2 (Suc (unat k) - unat i) dvv mv (unat j) vv \<and>
                Suc (unat k) - unat i \<le> c\<rangle>\<close> and
        INV'=\<open>\<lambda>c. \<Squnion>gd dvv gm mv gj j gv vv gi i. dv_ref \<mapsto>\<langle>\<top>\<rangle> gd\<down>dvv \<star> m_ref \<mapsto>\<langle>\<top>\<rangle> gm\<down>mv \<star>
               j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> v_ref \<mapsto>\<langle>\<top>\<rangle> gv\<down>vv \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i \<le> unat k \<and>
                settle_m D (map unat kind) dv2 (Suc (unat k) - unat i) dvv mv (unat j) vv =
                  settle_m D (map unat kind) dv2 (Suc (unat k)) dv m (unat k) v \<and>
                spre urust_fuel D (map unat kind) dv2 (Suc (unat k) - unat i) dvv mv (unat j) vv \<and>
                Suc (unat k) - unat i \<le> Suc c\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>(fst r, fst (snd r)) = settle_m D (map unat kind) dv2 (Suc (unat k)) dv m (unat k) v\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: word_le_nat_alt Suc_diff_le nth_map unat_small split_def unat_inc_le)
    done
  done

end

definition rec_st :: \<open>CoreTerm list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool list list \<Rightarrow> bool list list \<Rightarrow> nat \<Rightarrow>
    bool list list \<times> bool list list\<close> where
  \<open>rec_st Ds Ks Ms dvs ms k \<equiv> foldl (recon_step Ds Ks Ms dvs) ([], ms) [0..<k]\<close>

lemma rec_st_0: \<open>fst (rec_st Ds Ks Ms dvs ms 0) = []\<close> \<open>snd (rec_st Ds Ks Ms dvs ms 0) = ms\<close>
  by (simp_all add: rec_st_def)

lemma rec_st_Suc:
  \<open>rec_st Ds Ks Ms dvs ms (Suc k) =
    (if Ms ! k = 1 then (fst (rec_st Ds Ks Ms dvs ms k) @ [[]], snd (rec_st Ds Ks Ms dvs ms k))
     else if Ks ! k = 0 then (fst (rec_st Ds Ks Ms dvs ms k) @ [eval_m (snd (rec_st Ds Ks Ms dvs ms k)) (fst (rec_st Ds Ks Ms dvs ms k)) (Ds ! k)],
                             snd (rec_st Ds Ks Ms dvs ms k))
     else settle_res Ds Ks dvs (fst (rec_st Ds Ks Ms dvs ms k) @ [[]]) (snd (rec_st Ds Ks Ms dvs ms k)) k
            (if Ms ! k = 2 then bits_one_m (length (dvs ! k)) else dvs ! k))\<close>
  by (simp add: rec_st_def recon_step_def split_def settle_res_def del: settle_m.simps)

context QFBV_ctx
begin

definition reconstruct_contract :: \<open>CoreProblem \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> CoreProblem \<Rightarrow> bool list list \<Rightarrow>
    ('s, bool list list, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>reconstruct_contract q kind mark q2 m2 \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>recon_pre urust_fuel q (map unat kind) (map unat mark) q2 m2\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = reconstruct_m q (map unat kind) (map unat mark) q2 m2\<rangle>)\<close>

lemma reconstruct_spec [crush_specs]:
  shows \<open>\<Gamma>; reconstruct q kind mark q2 m2 \<Turnstile>\<^sub>F reconstruct_contract q kind mark q2 m2\<close>
proof (cases \<open>recon_pre urust_fuel q (map unat kind) (map unat mark) q2 m2\<close>)
  case True
  let ?D = \<open>CoreProblem_defs q\<close> and ?K = \<open>map unat kind\<close> and ?M = \<open>map unat mark\<close>
    and ?dv2 = \<open>eval_defs_m q2 m2\<close>
  let ?S = \<open>rec_st ?D ?K ?M ?dv2 m2\<close>
  have P: \<open>edefs_ok urust_fuel q2 m2\<close> \<open>length (CoreProblem_defs q2) \<le> urust_fuel\<close>
    \<open>length (CoreProblem_defs q2) < 18446744073709551616\<close> \<open>length ?D \<le> urust_fuel\<close> \<open>Suc (length ?D) < 18446744073709551616\<close>
    \<open>length kind = length ?D\<close> \<open>length mark = length ?D\<close>
    using True by (simp_all add: recon_pre_def Let_def)
  have RP: \<open>k < length ?D \<Longrightarrow> rstep_pre urust_fuel ?D ?K ?M ?dv2 (?S k) k\<close> for k
    using True by (simp add: recon_pre_def Let_def rec_st_def)
  have NM: \<open>k < length ?D \<Longrightarrow> ?M ! k = unat (mark ! k)\<close> \<open>k < length ?D \<Longrightarrow> ?K ! k = unat (kind ! k)\<close> for k
    using P(6,7) by simp_all
  have RA: \<open>k < length ?D \<Longrightarrow> mark ! k \<noteq> 1 \<Longrightarrow> kind ! k = 0 \<Longrightarrow>
      Suc (size (?D ! k)) \<le> urust_fuel \<and> eok urust_fuel (snd (?S k)) (fst (?S k)) (?D ! k)\<close> for k
    using RP[of k] NM[of k] by (auto simp: rstep_pre_def split_def unat_small)
  have ME: \<open>k < length ?D \<Longrightarrow> (?M ! k = 1) = (mark ! k = 1)\<close> \<open>k < length ?D \<Longrightarrow> (?M ! k = 2) = (mark ! k = 2)\<close>
    \<open>k < length ?D \<Longrightarrow> (?K ! k = 0) = (kind ! k = 0)\<close> for k
    using NM[of k] by (simp_all add: unat_small unat_eq_zero)
  have RC: \<open>k < length ?D \<Longrightarrow> mark ! k \<noteq> 1 \<Longrightarrow> kind ! k \<noteq> 0 \<Longrightarrow>
      k < length ?dv2 \<and> length (?dv2 ! k) < 18446744073709551616 \<and>
      settle_pre urust_fuel ?D ?K ?dv2 (fst (?S k) @ [[]]) (snd (?S k)) k
        (if mark ! k = 2 then bits_one_m (length (?dv2 ! k)) else ?dv2 ! k)\<close> for k
  proof -
    assume k: \<open>k < length ?D\<close> and m1: \<open>mark ! k \<noteq> 1\<close> and k0: \<open>kind ! k \<noteq> 0\<close>
    have R: \<open>rstep_pre urust_fuel ?D ?K ?M ?dv2 (?S k) k\<close> using RP[OF k] .
    have \<open>?M ! k \<noteq> 1\<close> \<open>?K ! k \<noteq> 0\<close> using ME[OF k] m1 k0 by simp_all
    then have \<open>k < length ?dv2 \<and> length (?dv2 ! k) < 2 ^ 64 \<and>
      spre urust_fuel ?D ?K ?dv2 (Suc k) (fst (?S k) @ [[]]) (snd (?S k)) k
        (if ?M ! k = 2 then bits_one_m (length (?dv2 ! k)) else ?dv2 ! k)\<close>
      using R unfolding rstep_pre_def split_def by (simp only: prod.case) blast
    then show ?thesis unfolding settle_pre_def ME(2)[OF k] by (simp del: spre.simps)
  qed
  have RC2: \<open>k < length ?D \<Longrightarrow> mark ! k \<noteq> 1 \<Longrightarrow> kind ! k \<noteq> 0 \<Longrightarrow> mark ! k = 2 \<Longrightarrow>
      settle_pre urust_fuel ?D ?K ?dv2 (fst (?S k) @ [[]]) (snd (?S k)) k (bits_one_m (length (?dv2 ! k)))\<close>
    \<open>k < length ?D \<Longrightarrow> mark ! k \<noteq> 1 \<Longrightarrow> kind ! k \<noteq> 0 \<Longrightarrow> mark ! k \<noteq> 2 \<Longrightarrow>
      settle_pre urust_fuel ?D ?K ?dv2 (fst (?S k) @ [[]]) (snd (?S k)) k (?dv2 ! k)\<close> for k
    using RC[of k] by simp_all
  have SS: \<open>k < length ?D \<Longrightarrow> ?S (Suc k) =
    (if mark ! k = 1 then (fst (?S k) @ [[]], snd (?S k))
     else if kind ! k = 0 then (fst (?S k) @ [eval_m (snd (?S k)) (fst (?S k)) (?D ! k)], snd (?S k))
     else settle_res ?D ?K ?dv2 (fst (?S k) @ [[]]) (snd (?S k)) k
            (if mark ! k = 2 then bits_one_m (length (?dv2 ! k)) else ?dv2 ! k))\<close> for k
    using rec_st_Suc[of ?D ?K ?M ?dv2 m2 k] ME[of k] by (simp only:)
  have N64: \<open>length ?D < 18446744073709551615\<close> \<open>length ?D \<le> urust_fuel\<close> \<open>length ?D < 18446744073709551616\<close>
    using P(4,5) by simp_all
  have N65: \<open>unat r < length ?D \<Longrightarrow> unat r < 18446744073709551615\<close> \<open>unat r < length ?D \<Longrightarrow> unat r < urust_fuel\<close>
    for r :: \<open>64 word\<close> using N64(1,2) by simp_all
  have PE: \<open>((a, b) = p) = (a = fst p \<and> b = snd p)\<close> for a b and p :: \<open>'x \<times> 'y\<close> by auto
  have UK: \<open>unat r < length ?D \<Longrightarrow> unat (r + 1) = Suc (unat r)\<close> for r :: \<open>64 word\<close>
    using N64(1) by (intro unat_plus_one_of_less_bound[of _ \<open>length ?D\<close>]) simp_all
  have RES: \<open>snd (?S (length ?D)) = reconstruct_m q ?K ?M q2 m2\<close>
    by (simp add: rec_st_def reconstruct_m_def)
  show ?thesis
    apply (crush_boot f: reconstruct_def contract: reconstruct_contract_def)
    apply (crush_base inline: len_def simp add: P)
    subgoal for m_ref dv_ref k_ref
      apply (ucincl_discharge\<open>
        rule_tac
          INV=\<open>\<lambda>c. \<Squnion>gm mv gd dvv gk k. m_ref \<mapsto>\<langle>\<top>\<rangle> gm\<down>mv \<star> dv_ref \<mapsto>\<langle>\<top>\<rangle> gd\<down>dvv \<star> k_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>k \<star>
                 can_alloc_reference \<star>
                 \<langle>unat k \<le> length ?D \<and> dvv = fst (?S (unat k)) \<and> mv = snd (?S (unat k)) \<and> length ?D - unat k \<le> c\<rangle>\<close> and
          INV'=\<open>\<lambda>c. \<Squnion>gm mv gd dvv gk k. m_ref \<mapsto>\<langle>\<top>\<rangle> gm\<down>mv \<star> dv_ref \<mapsto>\<langle>\<top>\<rangle> gd\<down>dvv \<star> k_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>k \<star>
                 can_alloc_reference \<star>
                 \<langle>unat k < length ?D \<and> dvv = fst (?S (unat k)) \<and> mv = snd (?S (unat k)) \<and> length ?D - unat k \<le> Suc c\<rangle>\<close> and
          \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_bounded_while_framedI\<close>)
      apply (crush_base inline: vec_push_def len_def
          simp add: P N64 N65 UK RA RC RC2 SS RES PE rec_st_0 word_less_nat_alt unat_of_nat_eq unat_small)
      done
    done
next
  case False
  then have F: \<open>recon_pre urust_fuel q (map unat kind) (map unat mark) q2 m2 = False\<close> by simp
  show ?thesis
    apply (ucincl_discharge\<open>intro satisfies_function_contractI\<close>)
    apply (subst wp_sstriple_iff)
    apply (simp add: reconstruct_contract_def F apure_precise_False asepconj_bot_zero2 bot_aentails_all)
    done
qed

end


text \<open>The rewriting rules of \<^verbatim>\<open>QFBV_LowerRefine\<close> for \<^const>\<open>lower_m\<close>, as the theories importing this
  one expect them (the merge with \<^verbatim>\<open>QFBV_Elim\<close> brings back the equations it removes).\<close>
declare lower_m.simps(4-13) [simp del]
declare lower_m_simps' [simp]

end
