theory QFBV_Eval
  imports QFBV_Refine QFBV_Circuits
begin

section \<open>Evaluation of core terms\<close>

text \<open>
  \<^verbatim>\<open>eval_term\<close> computes the value of a core term from the values of the variables and of the
  definitions, as bit lists (least significant bit first); \<^verbatim>\<open>eval_defs\<close> the values of all
  definitions of a problem. This theory gives the functional models of these functions and of
  their helpers, proves that the models compute \<^const>\<open>ceval\<close> and \<^const>\<open>cdef_values\<close>, and that
  the Rust functions compute their models.
\<close>

subsection \<open>Functional models\<close>

definition bnot_m :: \<open>bool list \<Rightarrow> bool list\<close> where
  \<open>bnot_m a \<equiv> map Not a\<close>

definition bbitw_m :: \<open>BinOp \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> bool list\<close> where
  \<open>bbitw_m op a b \<equiv> map (\<lambda>i. bop op (a ! i) (b ! i)) [0..<length a]\<close>

text \<open>The sum bit and the carry of \<open>x + y + c\<close> (\<^verbatim>\<open>full_add\<close>).\<close>
definition fa :: \<open>bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<times> bool\<close> where
  \<open>fa x y c \<equiv> (x \<noteq> (y \<noteq> c), if x = y then x else c)\<close>

text \<open>One step of the ripple-carry adder on bit \<open>i\<close>: the bits so far and the carry.\<close>
definition badd_step :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> bool list \<times> bool \<Rightarrow> nat \<Rightarrow> bool list \<times> bool\<close> where
  \<open>badd_step a b \<equiv> \<lambda>X i. (fst X @ [fst (fa (a ! i) (b ! i) (snd X))], snd (fa (a ! i) (b ! i) (snd X)))\<close>

definition badd_m :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> bool \<Rightarrow> bool list \<times> bool\<close> where
  \<open>badd_m a b cin \<equiv> foldl (badd_step a b) ([], cin) [0..<length a]\<close>

definition bshift_const_m :: \<open>bool list \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> bool list\<close> where
  \<open>bshift_const_m a s left \<equiv>
     map (\<lambda>j. if left then (if j < s then False else a ! (j - s))
               else (if s < length a - j then a ! (j + s) else False))
       [0..<length a]\<close>

definition bmul_step :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> bool list\<close> where
  \<open>bmul_step a b acc i \<equiv> if b ! i then fst (badd_m acc (bshift_const_m a i True) False) else acc\<close>

definition bmul_m :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> bool list\<close> where
  \<open>bmul_m a b \<equiv> foldl (bmul_step a b) (replicate (length a) False) [0..<length a]\<close>

definition beq_m :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> bool\<close> where
  \<open>beq_m a b \<equiv> foldl (\<lambda>r i. r \<and> a ! i = b ! i) True [0..<length a]\<close>

definition bult_m :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> bool\<close> where
  \<open>bult_m a b \<equiv> \<not> snd (badd_m a (bnot_m b) True)\<close>

definition bzext_m :: \<open>bool list \<Rightarrow> nat \<Rightarrow> bool list\<close> where
  \<open>bzext_m a w \<equiv> map (\<lambda>i. if i < length a then a ! i else False) [0..<w]\<close>

definition bshl1_m :: \<open>bool list \<Rightarrow> bool \<Rightarrow> bool list\<close> where
  \<open>bshl1_m r x \<equiv> x # take (length r - 1) r\<close>

text \<open>One step of the long division of \<open>a\<close>: bit \<open>i = w - 1 - j\<close> of \<open>a\<close> enters the remainder,
  and \<open>b\<close> (given as \<open>nb\<close>, the complement of \<open>b\<close> in one bit more than \<open>w\<close>) is subtracted if
  it fits.\<close>
definition bdiv_step :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> bool list \<times> bool list \<Rightarrow> nat \<Rightarrow> bool list \<times> bool list\<close> where
  \<open>bdiv_step a nb \<equiv> \<lambda>(q, r) j.
     let i = length a - 1 - j in
     let r1 = bshl1_m r (a ! i) in
     let (d, c) = badd_m r1 nb True in
     if c then (q[i := True], d) else (q, r1)\<close>

definition bdivrem_m :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> bool list \<times> bool list\<close> where
  \<open>bdivrem_m a b \<equiv>
     let w = length a in
     if beq_m b (replicate w False) then (replicate w True, a)
     else let (q, r) = foldl (bdiv_step a (bnot_m (bzext_m b (w + 1))))
                         (replicate w False, replicate (w + 1) False) [0..<w] in
          (q, bzext_m r w)\<close>

text \<open>One step of the computation of the shift amount, from the highest bit of \<open>b\<close> down, kept at
  most the width \<open>w\<close>.\<close>
definition bshift_step :: \<open>nat \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>bshift_step w b s j \<equiv>
     let i = length b - 1 - j in
     if s < w then (let s2 = (if b ! i then s + s + 1 else s + s) in if w < s2 then w else s2) else s\<close>

definition bshift_m :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> bool \<Rightarrow> bool list\<close> where
  \<open>bshift_m a b left \<equiv> bshift_const_m a (foldl (bshift_step (length a) b) 0 [0..<length b]) left\<close>

definition bextract_m :: \<open>bool list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool list\<close> where
  \<open>bextract_m a hi lo \<equiv> map ((!) a) [lo..<Suc hi]\<close>

definition bconcat_m :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> bool list\<close> where
  \<open>bconcat_m hi lo \<equiv> lo @ hi\<close>

definition eval_bin_m :: \<open>BinOp \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> bool list\<close> where
  \<open>eval_bin_m op a b \<equiv>
     (case op of
        BinOp_And \<Rightarrow> bbitw_m op a b
      | BinOp_Or \<Rightarrow> bbitw_m op a b
      | BinOp_Xor \<Rightarrow> bbitw_m op a b
      | BinOp_Add \<Rightarrow> fst (badd_m a b False)
      | BinOp_Mul \<Rightarrow> bmul_m a b
      | BinOp_Udiv \<Rightarrow> fst (bdivrem_m a b)
      | BinOp_Urem \<Rightarrow> snd (bdivrem_m a b)
      | BinOp_Shl \<Rightarrow> bshift_m a b True
      | BinOp_Lshr \<Rightarrow> bshift_m a b False
      | BinOp_Concat \<Rightarrow> bconcat_m a b
      | BinOp_Eq \<Rightarrow> [beq_m a b]
      | BinOp_Ult \<Rightarrow> [bult_m a b])\<close>

primrec eval_m :: \<open>bool list list \<Rightarrow> bool list list \<Rightarrow> CoreTermL \<Rightarrow> bool list\<close> where
  \<open>eval_m vs dv (CoreTermL_Const bs) = bs\<close>
| \<open>eval_m vs dv (CoreTermL_Var i) = vs ! unat i\<close>
| \<open>eval_m vs dv (CoreTermL_Ref i) = dv ! unat i\<close>
| \<open>eval_m vs dv (CoreTermL_Not a) = bnot_m (eval_m vs dv a)\<close>
| \<open>eval_m vs dv (CoreTermL_Bin op a b) = eval_bin_m op (eval_m vs dv a) (eval_m vs dv b)\<close>
| \<open>eval_m vs dv (CoreTermL_Extract hi lo a) = bextract_m (eval_m vs dv a) (unat hi) (unat lo)\<close>
| \<open>eval_m vs dv (CoreTermL_Ite c a b) = (if eval_m vs dv c ! 0 then eval_m vs dv a else eval_m vs dv b)\<close>

text \<open>The values of the definitions \<open>ds\<close>, appended to \<open>dv\<close>.\<close>
definition eval_defs_from :: \<open>bool list list \<Rightarrow> bool list list \<Rightarrow> CoreTermL list \<Rightarrow> bool list list\<close> where
  \<open>eval_defs_from vs dv ds \<equiv> foldl (\<lambda>dv d. dv @ [eval_m vs dv d]) dv ds\<close>

definition eval_defs_m :: \<open>CoreProblemL \<Rightarrow> bool list list \<Rightarrow> bool list list\<close> where
  \<open>eval_defs_m p m \<equiv> eval_defs_from m [] (CoreProblemL_defs p)\<close>

subsection \<open>The models compute the semantics\<close>

lemma bits_nat_take: \<open>bits_nat (take n xs) = bits_nat xs mod 2 ^ n\<close>
  by (rule bit_eqI) (auto simp add: bit_bits_nat bit_mod_pow)

lemma bits_nat_eqI:
  assumes \<open>\<And>k. bit (bits_nat xs) k \<longleftrightarrow> bit y k\<close>
  shows \<open>bits_nat xs = y\<close>
  using assms by (rule bit_eqI)

lemma length_bnot [simp]: \<open>length (bnot_m a) = length a\<close>
  by (simp add: bnot_m_def)

lemma bits_nat_bnot_add: \<open>bits_nat (bnot_m a) + bits_nat a + 1 = 2 ^ length a\<close>
  by (induct a) (auto simp add: bnot_m_def)

lemma bits_nat_bnot: \<open>bits_nat (bnot_m a) = 2 ^ length a - 1 - bits_nat a\<close>
  using bits_nat_bnot_add[of a] by simp

lemma length_bbitw [simp]: \<open>length (bbitw_m op a b) = length a\<close>
  by (simp add: bbitw_m_def)

lemma nth_bbitw: \<open>n < length a \<Longrightarrow> bbitw_m op a b ! n = bop op (a ! n) (b ! n)\<close>
  by (simp add: bbitw_m_def)

lemma bits_nat_bbitw:
  assumes \<open>length a = length b\<close>
  shows \<open>bits_nat (bbitw_m BinOp_And a b) = Bit_Operations.and (bits_nat a) (bits_nat b)\<close>
    \<open>bits_nat (bbitw_m BinOp_Or a b) = Bit_Operations.or (bits_nat a) (bits_nat b)\<close>
    \<open>bits_nat (bbitw_m BinOp_Xor a b) = Bit_Operations.xor (bits_nat a) (bits_nat b)\<close>
  using assms by (auto intro!: bit_eqI simp add: nth_bbitw bop_def bit_bits_nat bit_and_iff bit_or_iff bit_xor_iff)

lemma badd_fold:
  assumes \<open>n \<le> length a\<close> \<open>n \<le> length b\<close>
  shows \<open>length (fst (foldl (badd_step a b) ([], cin) [0..<n])) = n \<and>
    bits_nat (fst (foldl (badd_step a b) ([], cin) [0..<n])) +
      2 ^ n * of_bool (snd (foldl (badd_step a b) ([], cin) [0..<n])) =
    bits_nat (take n a) + bits_nat (take n b) + of_bool cin\<close>
  using assms
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  obtain r c where rc: \<open>foldl (badd_step a b) ([], cin) [0..<n] = (r, c)\<close> by fastforce
  have IH: \<open>length r = n\<close> \<open>bits_nat r + 2 ^ n * of_bool c = bits_nat (take n a) + bits_nat (take n b) + of_bool cin\<close>
    using Suc rc by simp_all
  have ta: \<open>take (Suc n) a = take n a @ [a ! n]\<close> and tb: \<open>take (Suc n) b = take n b @ [b ! n]\<close>
    using Suc.prems by (simp_all add: take_Suc_conv_app_nth)
  have st: \<open>foldl (badd_step a b) ([], cin) [0..<Suc n] =
      (r @ [a ! n \<noteq> (b ! n \<noteq> c)], if a ! n = b ! n then a ! n else c)\<close>
    using rc by (simp add: badd_step_def fa_def)
  have ln: \<open>min (length a) n = n\<close> \<open>min (length b) n = n\<close> using Suc.prems by simp_all
  show ?case
    unfolding st ta tb using IH
    by (cases \<open>a ! n\<close>; cases \<open>b ! n\<close>; cases c; simp add: bits_nat_append ln)
qed

lemma badd_m:
  assumes \<open>length a = length b\<close>
  shows \<open>length (fst (badd_m a b cin)) = length a\<close>
    \<open>bits_nat (fst (badd_m a b cin)) + 2 ^ length a * of_bool (snd (badd_m a b cin)) =
       bits_nat a + bits_nat b + of_bool cin\<close>
  using badd_fold[of \<open>length a\<close> a b cin] assms by (simp_all add: badd_m_def)

lemma bits_nat_badd:
  assumes \<open>length a = length b\<close>
  shows \<open>bits_nat (fst (badd_m a b cin)) = (bits_nat a + bits_nat b + of_bool cin) mod 2 ^ length a\<close>
  using mod_of_carry[OF badd_m(2)[OF assms]] bits_nat_lt[of \<open>fst (badd_m a b cin)\<close>] badd_m(1)[OF assms]
  by simp

lemma length_bshift_const [simp]: \<open>length (bshift_const_m a s left) = length a\<close>
  by (simp add: bshift_const_m_def)

lemma bits_nat_bshift_left: \<open>bits_nat (bshift_const_m a s True) = (bits_nat a * 2 ^ s) mod 2 ^ length a\<close>
  by (rule bit_eqI) (auto simp add: bshift_const_m_def bit_bits_nat bit_shl_mod)

lemma bits_nat_bshift_right: \<open>bits_nat (bshift_const_m a s False) = bits_nat a div 2 ^ s\<close>
  by (rule bit_eqI) (auto simp add: bshift_const_m_def bit_bits_nat bit_div_pow add.commute)

lemma bmul_fold:
  assumes \<open>n \<le> length a\<close> \<open>length a \<le> length b\<close>
  shows \<open>length (foldl (bmul_step a b) (replicate (length a) False) [0..<n]) = length a \<and>
    bits_nat (foldl (bmul_step a b) (replicate (length a) False) [0..<n]) =
      (bits_nat a * bits_nat (take n b)) mod 2 ^ length a\<close>
  using assms
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  let ?acc = \<open>foldl (bmul_step a b) (replicate (length a) False) [0..<n]\<close>
  have IH: \<open>length ?acc = length a\<close> \<open>bits_nat ?acc = (bits_nat a * bits_nat (take n b)) mod 2 ^ length a\<close>
    using Suc by simp_all
  have tb: \<open>bits_nat (take (Suc n) b) = bits_nat (take n b) + 2 ^ n * of_bool (b ! n)\<close>
    using Suc.prems by (simp add: take_Suc_conv_app_nth bits_nat_append)
  have st: \<open>foldl (bmul_step a b) (replicate (length a) False) [0..<Suc n] = bmul_step a b ?acc n\<close>
    by simp
  show ?case
  proof (cases \<open>b ! n\<close>)
    case True
    have l: \<open>length ?acc = length (bshift_const_m a n True)\<close> using IH by simp
    have \<open>bits_nat (fst (badd_m ?acc (bshift_const_m a n True) False)) =
        ((bits_nat a * bits_nat (take n b)) mod 2 ^ length a + (bits_nat a * 2 ^ n) mod 2 ^ length a) mod 2 ^ length a\<close>
      using bits_nat_badd[OF l] IH by (simp add: bits_nat_bshift_left)
    also have \<open>\<dots> = (bits_nat a * bits_nat (take (Suc n) b)) mod 2 ^ length a\<close>
      using True by (simp add: tb mod_add_eq algebra_simps)
    finally show ?thesis
      unfolding st using True IH badd_m(1)[OF l] by (simp add: bmul_step_def)
  next
    case False
    then show ?thesis unfolding st using IH by (simp add: bmul_step_def tb)
  qed
qed

lemma bmul_m:
  assumes \<open>length a = length b\<close>
  shows \<open>length (bmul_m a b) = length a\<close> \<open>bits_nat (bmul_m a b) = (bits_nat a * bits_nat b) mod 2 ^ length a\<close>
  using bmul_fold[of \<open>length a\<close> a b] assms by (simp_all add: bmul_m_def)

lemma foldl_and_all: \<open>foldl (\<lambda>r i. r \<and> P i) r0 [0..<n] \<longleftrightarrow> r0 \<and> (\<forall>i < n. P i)\<close>
  by (induction n) (auto simp add: less_Suc_eq)

lemma beq_m:
  assumes \<open>length a = length b\<close>
  shows \<open>beq_m a b \<longleftrightarrow> bits_nat a = bits_nat b\<close>
  unfolding beq_m_def foldl_and_all bits_nat_eq_iff[OF assms] using assms
  by (auto simp add: list_eq_iff_nth_eq)

lemma bult_m:
  assumes \<open>length a = length b\<close>
  shows \<open>bult_m a b \<longleftrightarrow> bits_nat a < bits_nat b\<close>
proof -
  have l: \<open>length a = length (bnot_m b)\<close> using assms by simp
  note A = badd_m(2)[OF l, of True]
  have n: \<open>bits_nat (bnot_m b) + 1 = 2 ^ length a - bits_nat b\<close>
    using bits_nat_bnot_add[of b] assms by simp
  have lt: \<open>bits_nat (fst (badd_m a (bnot_m b) True)) < 2 ^ length a\<close>
    using bits_nat_lt[of \<open>fst (badd_m a (bnot_m b) True)\<close>] badd_m(1)[OF l] by simp
  have yb: \<open>bits_nat b < 2 ^ length a\<close> using bits_nat_lt[of b] assms by simp
  show ?thesis
    using A n lt yb by (cases \<open>snd (badd_m a (bnot_m b) True)\<close>) (auto simp add: bult_m_def)
qed

lemma length_bzext [simp]: \<open>length (bzext_m a w) = w\<close>
  by (simp add: bzext_m_def)

lemma bits_nat_bzext: \<open>bits_nat (bzext_m a w) = bits_nat a mod 2 ^ w\<close>
  by (rule bit_eqI) (auto simp add: bzext_m_def bit_bits_nat bit_mod_pow)

lemma length_bshl1 [simp]: \<open>0 < length r \<Longrightarrow> length (bshl1_m r x) = length r\<close>
  by (simp add: bshl1_m_def)

lemma bits_nat_bshl1:
  assumes \<open>0 < length r\<close>
  shows \<open>bits_nat (bshl1_m r x) = (2 * bits_nat r + of_bool x) mod 2 ^ length r\<close>
proof -
  obtain m where m: \<open>length r = Suc m\<close> using assms by (cases \<open>length r\<close>) simp_all
  have \<open>(2 * bits_nat r + of_bool x) mod 2 ^ Suc m =
      2 * ((2 * bits_nat r + of_bool x) div 2 mod 2 ^ m) + (2 * bits_nat r + of_bool x) mod 2\<close>
    using mod_mult2_eq[of \<open>2 * bits_nat r + of_bool x\<close> 2 \<open>2 ^ m\<close>] by (simp add: mult.commute)
  also have \<open>\<dots> = of_bool x + 2 * (bits_nat r mod 2 ^ m)\<close> by (cases x) simp_all
  finally show ?thesis using m by (simp add: bshl1_m_def bits_nat_take)
qed

lemma length_bextract [simp]: \<open>length (bextract_m a hi lo) = Suc hi - lo\<close>
  by (simp add: bextract_m_def del: upt_Suc)

lemma nth_bextract: \<open>n < Suc hi - lo \<Longrightarrow> bextract_m a hi lo ! n = a ! (lo + n)\<close>
  unfolding bextract_m_def by (rule nth_map_upt)

lemma bits_nat_bextract:
  assumes \<open>hi < length a\<close>
  shows \<open>bits_nat (bextract_m a hi lo) = (bits_nat a div 2 ^ lo) mod 2 ^ (Suc hi - lo)\<close>
  using assms by (intro bit_eqI) (auto simp add: nth_bextract bit_bits_nat bit_mod_pow bit_div_pow)

lemma length_bconcat [simp]: \<open>length (bconcat_m hi lo) = length lo + length hi\<close>
  by (simp add: bconcat_m_def)

lemma bits_nat_bconcat: \<open>bits_nat (bconcat_m hi lo) = bits_nat hi * 2 ^ length lo + bits_nat lo\<close>
  by (simp add: bconcat_m_def bits_nat_append)


subsection \<open>Long division\<close>

lemma bits_nat_update_True:
  \<open>i < length xs \<Longrightarrow> \<not> xs ! i \<Longrightarrow> bits_nat (xs[i := True]) = bits_nat xs + 2 ^ i\<close>
proof (induction xs arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case by (cases i) simp_all
qed

lemma div_pow_step: \<open>(n::nat) div 2 ^ i = 2 * (n div 2 ^ Suc i) + of_bool (bit n i)\<close>
proof -
  have \<open>n div 2 ^ i = 2 * (n div 2 ^ i div 2) + n div 2 ^ i mod 2\<close> by simp
  then show ?thesis by (simp add: div_2_pow_Suc bit_iff_odd odd_iff_mod_2_eq_one)
qed

lemma bdiv_fold:
  assumes la: \<open>length a = w\<close> and lb: \<open>length b = w\<close> and y: \<open>0 < bits_nat b\<close> and j: \<open>j \<le> w\<close>
    and nb: \<open>nb = bnot_m (bzext_m b (w + 1))\<close>
    and f: \<open>foldl (bdiv_step a nb) (replicate w False, replicate (w + 1) False) [0..<j] = (q, r)\<close>
  shows \<open>length q = w \<and> length r = Suc w \<and> bits_nat r < bits_nat b \<and>
    (\<exists>Q. bits_nat q = Q * 2 ^ (w - j) \<and> bits_nat a div 2 ^ (w - j) = Q * bits_nat b + bits_nat r)\<close>
  using j f
proof (induction j arbitrary: q r)
  case 0
  have \<open>bits_nat a div 2 ^ w = 0\<close> using bits_nat_lt[of a] la by simp
  moreover have \<open>q = replicate w False\<close> \<open>r = replicate (w + 1) False\<close> using 0 by auto
  ultimately show ?case using y by simp
next
  case (Suc j)
  obtain q0 r0 where f0: \<open>foldl (bdiv_step a nb) (replicate w False, replicate (w + 1) False) [0..<j] = (q0, r0)\<close>
    by fastforce
  have IH: \<open>length q0 = w\<close> \<open>length r0 = Suc w\<close> \<open>bits_nat r0 < bits_nat b\<close>
    \<open>\<exists>Q. bits_nat q0 = Q * 2 ^ (w - j) \<and> bits_nat a div 2 ^ (w - j) = Q * bits_nat b + bits_nat r0\<close>
    using Suc.IH[OF _ f0] Suc.prems(1) by simp_all
  then obtain Q where Q: \<open>bits_nat q0 = Q * 2 ^ (w - j)\<close> \<open>bits_nat a div 2 ^ (w - j) = Q * bits_nat b + bits_nat r0\<close>
    by blast
  define i where \<open>i = w - 1 - j\<close>
  have i: \<open>i < w\<close> \<open>w - j = Suc i\<close> \<open>w - Suc j = i\<close> using Suc.prems(1) by (simp_all add: i_def)
  define r1 where \<open>r1 = bshl1_m r0 (a ! i)\<close>
  have yb: \<open>bits_nat b < 2 ^ w\<close> using bits_nat_lt[of b] lb by simp
  have lr1: \<open>length r1 = Suc w\<close> using IH(2) by (simp add: r1_def)
  have r1v: \<open>bits_nat r1 = 2 * bits_nat r0 + of_bool (a ! i)\<close>
  proof -
    have \<open>2 * bits_nat r0 + of_bool (a ! i) < 2 ^ Suc w\<close> using IH(3) yb by simp
    then show ?thesis using bits_nat_bshl1[of r0 \<open>a ! i\<close>] IH(2) by (simp add: r1_def)
  qed
  have lnb: \<open>length nb = Suc w\<close> by (simp add: nb)
  have nbv: \<open>bits_nat nb + 1 + bits_nat b = 2 ^ Suc w\<close>
  proof -
    have \<open>bits_nat (bzext_m b (w + 1)) = bits_nat b\<close> using yb by (simp add: bits_nat_bzext)
    then show ?thesis using bits_nat_bnot_add[of \<open>bzext_m b (w + 1)\<close>] by (simp add: nb)
  qed
  obtain d c where dc: \<open>badd_m r1 nb True = (d, c)\<close> by fastforce
  have ld: \<open>length d = Suc w\<close> using badd_m(1)[of r1 nb True] lr1 lnb dc by simp
  have A: \<open>bits_nat d + 2 ^ Suc w * of_bool c = bits_nat r1 + bits_nat nb + 1\<close>
    using badd_m(2)[of r1 nb True] lr1 lnb dc by simp
  have dlt: \<open>bits_nat d < 2 ^ Suc w\<close> using bits_nat_lt[of d] ld by simp
  have ai: \<open>bits_nat a div 2 ^ i = 2 * (bits_nat a div 2 ^ Suc i) + of_bool (a ! i)\<close>
    using div_pow_step[of \<open>bits_nat a\<close> i] i(1) la by (simp add: bit_bits_nat)
  have stp: \<open>foldl (bdiv_step a nb) (replicate w False, replicate (w + 1) False) [0..<Suc j] =
      (if c then (q0[i := True], d) else (q0, r1))\<close>
    using f0 dc la by (simp add: bdiv_step_def Let_def r1_def i_def)
  show ?case
  proof (cases c)
    case True
    then have e: \<open>q = q0[i := True]\<close> \<open>r = d\<close> using stp Suc.prems(2) by simp_all
    have cge: \<open>bits_nat b \<le> bits_nat r1\<close> and dv: \<open>bits_nat d = bits_nat r1 - bits_nat b\<close>
      using A nbv dlt True by simp_all
    have qi: \<open>\<not> q0 ! i\<close>
    proof -
      have \<open>\<not> bit (Q * 2 ^ Suc i) i\<close> using bit_push_bit_iff[of \<open>Suc i\<close> Q i] by (simp add: push_bit_eq_mult)
      moreover have \<open>bit (bits_nat q0) i \<longleftrightarrow> q0 ! i\<close> using i IH(1) by (simp add: bit_bits_nat)
      ultimately show ?thesis using Q(1) i(2) by simp
    qed
    have qv: \<open>bits_nat q = (2 * Q + 1) * 2 ^ i\<close>
      using bits_nat_update_True[of i q0] qi IH(1) i(1) Q(1) e(1) i(2) by (simp add: algebra_simps)
    have X: \<open>bits_nat a div 2 ^ (w - Suc j) = (2 * Q + 1) * bits_nat b + bits_nat d\<close>
      using ai Q(2) i r1v dv cge by (simp add: algebra_simps)
    have Y: \<open>bits_nat d < bits_nat b\<close> using dv r1v IH(3) by (cases \<open>a ! i\<close>) simp_all
    have Z: \<open>bits_nat q = (2 * Q + 1) * 2 ^ (w - Suc j)\<close> using qv i(3) by simp
    have L: \<open>length q = w\<close> using e(1) IH(1) by simp
    show ?thesis using X Y Z L e(2) ld by blast
  next
    case False
    then have e: \<open>q = q0\<close> \<open>r = r1\<close> using stp Suc.prems(2) by simp_all
    have clt: \<open>bits_nat r1 < bits_nat b\<close> using A nbv dlt False by simp
    have Z: \<open>bits_nat q = (2 * Q) * 2 ^ (w - Suc j)\<close> using Q(1) e(1) i(2,3) by simp
    have X: \<open>bits_nat a div 2 ^ (w - Suc j) = (2 * Q) * bits_nat b + bits_nat r1\<close>
      using ai Q(2) i r1v by (simp add: algebra_simps)
    show ?thesis using X Z e lr1 IH(1) clt by blast
  qed
qed

lemma bdivrem_m_all:
  assumes \<open>length a = length b\<close>
  shows \<open>length (fst (bdivrem_m a b)) = length a \<and> length (snd (bdivrem_m a b)) = length a \<and>
    bits_nat (fst (bdivrem_m a b)) = (if bits_nat b = 0 then 2 ^ length a - 1 else bits_nat a div bits_nat b) \<and>
    bits_nat (snd (bdivrem_m a b)) = (if bits_nat b = 0 then bits_nat a else bits_nat a mod bits_nat b)\<close>
proof -
  let ?w = \<open>length a\<close>
  have z: \<open>beq_m b (replicate ?w False) \<longleftrightarrow> bits_nat b = 0\<close>
    using beq_m[of b \<open>replicate ?w False\<close>] assms by simp
  have ones: \<open>bits_nat (replicate ?w True) = 2 ^ ?w - 1\<close>
    using bits_nat_replicate_True[of ?w] by simp
  show ?thesis
  proof (cases \<open>bits_nat b = 0\<close>)
    case True
    then show ?thesis using z ones by (simp add: bdivrem_m_def)
  next
    case False
    obtain q r where f: \<open>foldl (bdiv_step a (bnot_m (bzext_m b (?w + 1)))) (replicate ?w False, replicate (?w + 1) False)
        [0..<?w] = (q, r)\<close> by fastforce
    have F: \<open>length q = ?w\<close> \<open>length r = Suc ?w\<close> \<open>bits_nat r < bits_nat b\<close>
      \<open>\<exists>Q. bits_nat q = Q * 2 ^ (?w - ?w) \<and> bits_nat a div 2 ^ (?w - ?w) = Q * bits_nat b + bits_nat r\<close>
      using bdiv_fold[OF refl assms[symmetric] _ order_refl refl f] False by simp_all
    have Q: \<open>bits_nat a = bits_nat q * bits_nat b + bits_nat r\<close> using F(4) by simp
    have yb: \<open>bits_nat b < 2 ^ ?w\<close> using bits_nat_lt[of b] assms by simp
    have dv: \<open>bits_nat a div bits_nat b = bits_nat q\<close> \<open>bits_nat a mod bits_nat b = bits_nat r\<close>
      using Q F(3) by simp_all
    have e: \<open>bdivrem_m a b = (q, bzext_m r ?w)\<close>
      unfolding bdivrem_m_def Let_def using f z False by simp
    show ?thesis using e F dv yb by (simp add: bits_nat_bzext)
  qed
qed

lemma bdivrem_m:
  assumes \<open>length a = length b\<close>
  shows \<open>length (fst (bdivrem_m a b)) = length a\<close> \<open>length (snd (bdivrem_m a b)) = length a\<close>
    \<open>bits_nat (fst (bdivrem_m a b)) = (if bits_nat b = 0 then 2 ^ length a - 1 else bits_nat a div bits_nat b)\<close>
    \<open>bits_nat (snd (bdivrem_m a b)) = (if bits_nat b = 0 then bits_nat a else bits_nat a mod bits_nat b)\<close>
  using bdivrem_m_all[OF assms] by simp_all

subsection \<open>Shifts by a bit-vector\<close>

lemma bshift_fold:
  \<open>j \<le> length b \<Longrightarrow> foldl (bshift_step w b) 0 [0..<j] = min (bits_nat b div 2 ^ (length b - j)) w\<close>
proof (induction j)
  case 0
  have \<open>bits_nat b div 2 ^ length b = 0\<close> using bits_nat_lt[of b] by simp
  then show ?case by simp
next
  case (Suc j)
  define i where \<open>i = length b - 1 - j\<close>
  have i: \<open>i < length b\<close> \<open>length b - j = Suc i\<close> \<open>length b - Suc j = i\<close> using Suc.prems by (simp_all add: i_def)
  define P where \<open>P = bits_nat b div 2 ^ Suc i\<close>
  have P': \<open>bits_nat b div 2 ^ i = 2 * P + of_bool (b ! i)\<close>
    using div_pow_step[of \<open>bits_nat b\<close> i] i(1) by (simp add: P_def bit_bits_nat)
  have IH: \<open>foldl (bshift_step w b) 0 [0..<j] = min P w\<close> using Suc i by (simp add: P_def)
  have stp: \<open>foldl (bshift_step w b) 0 [0..<Suc j] = bshift_step w b (min P w) j\<close> using IH by simp
  have bi: \<open>length b - 1 - j = i\<close> by (simp add: i_def)
  show ?case
    unfolding stp i(3) P' using bi by (simp add: bshift_step_def Let_def min_def)
qed

lemma bshift_m:
  assumes \<open>length a = length b\<close>
  shows \<open>length (bshift_m a b left) = length a\<close>
    \<open>bits_nat (bshift_m a b True) = (bits_nat a * 2 ^ bits_nat b) mod 2 ^ length a\<close>
    \<open>bits_nat (bshift_m a b False) = bits_nat a div 2 ^ bits_nat b\<close>
proof -
  have s: \<open>foldl (bshift_step (length a) b) 0 [0..<length b] = min (bits_nat b) (length a)\<close>
    using bshift_fold[of \<open>length b\<close> b \<open>length a\<close>] by simp
  show \<open>length (bshift_m a b left) = length a\<close> by (simp add: bshift_m_def)
  have xa: \<open>bits_nat a < 2 ^ length a\<close> by (rule bits_nat_lt)
  show \<open>bits_nat (bshift_m a b True) = (bits_nat a * 2 ^ bits_nat b) mod 2 ^ length a\<close>
  proof (cases \<open>bits_nat b \<le> length a\<close>)
    case True
    then show ?thesis using s by (simp add: bshift_m_def bits_nat_bshift_left)
  next
    case False
    then have \<open>(2::nat) ^ length a dvd 2 ^ bits_nat b\<close> by (simp add: le_imp_power_dvd)
    then show ?thesis using s False by (simp add: bshift_m_def bits_nat_bshift_left)
  qed
  show \<open>bits_nat (bshift_m a b False) = bits_nat a div 2 ^ bits_nat b\<close>
  proof (cases \<open>bits_nat b \<le> length a\<close>)
    case True
    then show ?thesis using s by (simp add: bshift_m_def bits_nat_bshift_right)
  next
    case False
    have \<open>(2::nat) ^ length a \<le> 2 ^ bits_nat b\<close> using False by simp
    then have \<open>bits_nat a div 2 ^ bits_nat b = 0\<close> using xa by (metis div_less less_le_trans)
    then show ?thesis using s False xa by (simp add: bshift_m_def bits_nat_bshift_right)
  qed
qed

subsection \<open>Terms\<close>

lemma eval_bin_m:
  assumes \<open>op \<noteq> BinOp_Concat \<longrightarrow> length a = length b\<close>
  shows \<open>length (eval_bin_m op a b) = bin_width op (length a) (length b) \<and>
    bits_nat (eval_bin_m op a b) = cbin_sem op (length a) (bits_nat a) (length b) (bits_nat b)\<close>
  using assms
  by (cases op)
    (simp_all add: eval_bin_m_def bin_width_def bits_nat_bbitw bits_nat_badd badd_m(1) bmul_m
      bdivrem_m bshift_m bits_nat_bconcat beq_m bult_m)

theorem eval_m_correct:
  assumes \<open>cwt ws ds t\<close> \<open>ws = map length vs\<close> \<open>ds = map length dv\<close>
  shows \<open>length (eval_m vs dv t) = cwidth ws ds t \<and>
    bits_nat (eval_m vs dv t) = ceval ws ds (map bits_nat vs) (map bits_nat dv) t\<close>
  using assms(1)
proof (induction t)
  case (CoreTermL_Const bs)
  then show ?case by simp
next
  case (CoreTermL_Var i)
  then show ?case using assms(2) by simp
next
  case (CoreTermL_Ref i)
  then show ?case using assms(3) by simp
next
  case (CoreTermL_Not a)
  then show ?case by (simp add: bits_nat_bnot)
next
  case (CoreTermL_Bin op a b)
  then have \<open>op \<noteq> BinOp_Concat \<longrightarrow> length (eval_m vs dv a) = length (eval_m vs dv b)\<close> by simp
  note E = eval_bin_m[OF this]
  show ?case using E CoreTermL_Bin by (simp add: bin_width_def)
next
  case (CoreTermL_Extract hi lo a)
  then show ?case by (simp add: bits_nat_bextract Suc_diff_le)
next
  case (CoreTermL_Ite c a b)
  then have \<open>length (eval_m vs dv c) = 1\<close> by simp
  then obtain x where x: \<open>eval_m vs dv c = [x]\<close> by (cases \<open>eval_m vs dv c\<close>) simp_all
  have cv: \<open>ceval ws ds (map bits_nat vs) (map bits_nat dv) c = of_bool x\<close> using CoreTermL_Ite x by simp
  have Ia: \<open>length (eval_m vs dv a) = cwidth ws ds a \<and>
      bits_nat (eval_m vs dv a) = ceval ws ds (map bits_nat vs) (map bits_nat dv) a\<close>
    and Ib: \<open>length (eval_m vs dv b) = cwidth ws ds b \<and>
      bits_nat (eval_m vs dv b) = ceval ws ds (map bits_nat vs) (map bits_nat dv) b\<close>
    and W: \<open>cwidth ws ds a = cwidth ws ds b\<close>
    using CoreTermL_Ite by simp_all
  show ?case using Ia Ib W x cv by (cases x) simp_all
qed

lemma eval_defs_from:
  assumes \<open>cdefs_wt ws ds dd\<close> \<open>ws = map length vs\<close> \<open>ds = map length dv\<close>
  shows \<open>map length (eval_defs_from vs dv dd) = cdef_widths ws ds dd \<and>
    map bits_nat (eval_defs_from vs dv dd) = cdef_values ws ds (map bits_nat vs) (map bits_nat dv) dd\<close>
  using assms
proof (induction dd arbitrary: ds dv)
  case Nil
  then show ?case by (simp add: eval_defs_from_def)
next
  case (Cons d dd)
  note E = eval_m_correct[OF _ Cons.prems(2,3)]
  have \<open>cdefs_wt ws (ds @ [cwidth ws ds d]) dd\<close> \<open>ds @ [cwidth ws ds d] = map length (dv @ [eval_m vs dv d])\<close>
    using Cons.prems E by simp_all
  note IH = Cons.IH[OF this(1) Cons.prems(2) this(2)]
  then show ?case using Cons.prems E by (simp add: eval_defs_from_def)
qed

theorem eval_defs_m_correct:
  assumes \<open>cdefs_wt ws [] (CoreProblemL_defs p)\<close> \<open>ws = map length m\<close>
  shows \<open>map length (eval_defs_m p m) = cdef_widths ws [] (CoreProblemL_defs p) \<and>
    map bits_nat (eval_defs_m p m) = cdef_values ws [] (map bits_nat m) [] (CoreProblemL_defs p)\<close>
  using eval_defs_from[OF assms(1,2), of \<open>[]\<close>] by (simp add: eval_defs_m_def)


subsection \<open>Facts for the loops\<close>

lemma badd_step_eq:
  \<open>badd_step a b X i = (fst X @ [fst (fa (a ! i) (b ! i) (snd X))], snd (fa (a ! i) (b ! i) (snd X)))\<close>
  by (simp add: badd_step_def)

lemma badd_fold_len: \<open>length (fst (foldl (badd_step a b) X [0..<n])) = length (fst X) + n\<close>
  by (induction n) (simp_all add: badd_step_eq)

lemma length_badd [simp]: \<open>length (fst (badd_m a b c)) = length a\<close>
  using badd_fold_len[of a b \<open>([], c)\<close> \<open>length a\<close>] by (simp add: badd_m_def)

lemma bmul_fold_len: \<open>length (foldl (bmul_step a b) acc [0..<n]) = length acc\<close>
  by (induction n) (simp_all add: bmul_step_def)

lemma bdiv_step_eq:
  \<open>bdiv_step a nb X j =
     (if snd (badd_m (bshl1_m (snd X) (a ! (length a - 1 - j))) nb True)
      then ((fst X)[length a - 1 - j := True], fst (badd_m (bshl1_m (snd X) (a ! (length a - 1 - j))) nb True))
      else (fst X, bshl1_m (snd X) (a ! (length a - 1 - j))))\<close>
  by (simp add: bdiv_step_def split_def Let_def)

lemma bdiv_fold_len:
  \<open>0 < length (snd X) \<Longrightarrow> length (fst (foldl (bdiv_step a nb) X [0..<n])) = length (fst X) \<and>
     length (snd (foldl (bdiv_step a nb) X [0..<n])) = length (snd X)\<close>
  by (induction n) (simp_all add: bdiv_step_eq)

definition bdiv_run :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> bool list \<times> bool list\<close> where
  \<open>bdiv_run a b n \<equiv> foldl (bdiv_step a (bnot_m (bzext_m b (length a + 1))))
     (replicate (length a) False, replicate (length a + 1) False) [0..<n]\<close>

lemma bdiv_run_0: \<open>bdiv_run a b 0 = (replicate (length a) False, replicate (length a + 1) False)\<close>
  by (simp add: bdiv_run_def)

lemma bdiv_run_Suc: \<open>bdiv_run a b (Suc n) = bdiv_step a (bnot_m (bzext_m b (length a + 1))) (bdiv_run a b n) n\<close>
  by (simp add: bdiv_run_def)

lemma bdiv_run_len: \<open>length (fst (bdiv_run a b n)) = length a\<close> \<open>length (snd (bdiv_run a b n)) = Suc (length a)\<close>
  using bdiv_fold_len[of \<open>(replicate (length a) False, replicate (length a + 1) False)\<close> a
      \<open>bnot_m (bzext_m b (length a + 1))\<close> n]
  by (simp_all add: bdiv_run_def)

lemma bdivrem_m_zero:
  \<open>beq_m b (replicate (length a) False) \<Longrightarrow> bdivrem_m a b = (replicate (length a) True, a)\<close>
  by (simp add: bdivrem_m_def)

lemma bdivrem_m_nz:
  \<open>\<not> beq_m b (replicate (length a) False) \<Longrightarrow>
     bdivrem_m a b = (fst (bdiv_run a b (length a)), bzext_m (snd (bdiv_run a b (length a))) (length a))\<close>
  by (simp add: bdivrem_m_def bdiv_run_def split_def Let_def)

lemma unat_idx:
  fixes j :: \<open>64 word\<close>
  assumes \<open>unat j < n\<close> \<open>n < 2 ^ 64\<close>
  shows \<open>unat (word_of_nat n - 1 - j) = n - 1 - unat j\<close>
proof -
  have u: \<open>unat (word_of_nat n :: 64 word) = n\<close> using assms(2) by (simp add: unat_of_nat_eq)
  have j1: \<open>unat (1 + j) = Suc (unat j)\<close> using unat_word_Suc_simp[of j] assms by (simp add: add.commute)
  have le: \<open>1 + j \<le> word_of_nat n\<close> using j1 u assms(1) by (simp add: word_le_nat_alt)
  have \<open>unat (word_of_nat n - (1 + j)) = n - Suc (unat j)\<close> using unat_sub[OF le] u j1 by simp
  then show ?thesis by (simp add: diff_diff_eq)
qed

lemma unat_dbl:
  fixes s :: \<open>64 word\<close>
  assumes \<open>unat s < n\<close> \<open>2 * n + 1 < 2 ^ 64\<close>
  shows \<open>unat (s + s) = unat s + unat s\<close>
proof -
  have \<open>unat s + unat s < 2 ^ LENGTH(64)\<close> using assms by simp
  then show ?thesis using unat_add_lem by blast
qed

lemma bshift_step_le: \<open>s \<le> w \<Longrightarrow> bshift_step w b s j \<le> w\<close>
  by (simp add: bshift_step_def Let_def)

lemma bshift_fold_le: \<open>foldl (bshift_step w b) 0 [0..<n] \<le> w\<close>
  by (induction n) (simp_all add: bshift_step_le)

lemma cdefs_wt_app_eval:
  \<open>cdefs_wt ws ds (xs @ ys) \<longleftrightarrow> cdefs_wt ws ds xs \<and> cdefs_wt ws (cdef_widths ws ds xs) ys\<close>
  by (induction xs arbitrary: ds) simp_all

lemma cdefs_wt_nth:
  assumes \<open>cdefs_wt ws ds D\<close> \<open>j < length D\<close>
  shows \<open>cwt ws (cdef_widths ws ds (take j D)) (D ! j)\<close>
proof -
  have \<open>D = take j D @ D ! j # drop (Suc j) D\<close> using assms(2) by (simp add: id_take_nth_drop)
  then have \<open>cdefs_wt ws ds (take j D @ D ! j # drop (Suc j) D)\<close> using assms(1) by simp
  then show ?thesis by (simp only: cdefs_wt_app_eval) simp
qed

lemma eval_defs_from_snoc:
  \<open>eval_defs_from vs dv (xs @ [d]) = eval_defs_from vs dv xs @ [eval_m vs (eval_defs_from vs dv xs) d]\<close>
  by (simp add: eval_defs_from_def)

text \<open>The precondition of \<^verbatim>\<open>eval_term\<close> besides the recursion depth: the term is well-sorted
  over the widths of the values, and every subterm is narrow enough for the loops of the helpers
  and their counters.\<close>
definition eok :: \<open>nat \<Rightarrow> bool list list \<Rightarrow> bool list list \<Rightarrow> CoreTermL \<Rightarrow> bool\<close> where
  \<open>eok N vs dv t \<equiv>
     cwt (map length vs) (map length dv) t \<and>
     (\<forall>u \<in> set (csubterms t). 2 * cwidth (map length vs) (map length dv) u + 2 \<le> N \<and>
                                2 * cwidth (map length vs) (map length dv) u + 2 < 2 ^ 56)\<close>

lemma eok_simps:
  \<open>eok N vs dv (CoreTermL_Not a) \<Longrightarrow> eok N vs dv a\<close>
  \<open>eok N vs dv (CoreTermL_Bin op a b) \<Longrightarrow> eok N vs dv a \<and> eok N vs dv b\<close>
  \<open>eok N vs dv (CoreTermL_Extract hi lo a) \<Longrightarrow> eok N vs dv a\<close>
  \<open>eok N vs dv (CoreTermL_Ite c a b) \<Longrightarrow> eok N vs dv c \<and> eok N vs dv a \<and> eok N vs dv b\<close>
  by (simp_all add: eok_def)

lemma eok_len: \<open>eok N vs dv t \<Longrightarrow> length (eval_m vs dv t) = cwidth (map length vs) (map length dv) t\<close>
  using eval_m_correct[of \<open>map length vs\<close> \<open>map length dv\<close> t vs dv] by (simp add: eok_def)

lemma eok_width: \<open>eok N vs dv t \<Longrightarrow> 2 * cwidth (map length vs) (map length dv) t + 2 \<le> N \<and>
    2 * cwidth (map length vs) (map length dv) t + 2 < 2 ^ 56\<close>
  by (cases t) (auto simp add: eok_def)

lemma nth_bmodels [simp]:
  \<open>j < length a \<Longrightarrow> bshift_const_m a n left ! j =
     (if left then (if j < n then False else a ! (j - n)) else (if n < length a - j then a ! (j + n) else False))\<close>
  \<open>i < w \<Longrightarrow> bzext_m a w ! i = (if i < length a then a ! i else False)\<close>
  \<open>lo + j < Suc hi \<Longrightarrow> bextract_m a hi lo ! j = a ! (lo + j)\<close>
  by (simp_all add: bshift_const_m_def bzext_m_def bextract_m_def del: upt_Suc)

definition ebin_ok :: \<open>nat \<Rightarrow> BinOp \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> bool\<close> where
  \<open>ebin_ok N op a b \<equiv>
     (op \<noteq> BinOp_Concat \<longrightarrow> length a = length b) \<and> length a + 1 \<le> N \<and> length b \<le> N \<and>
     2 * length a + 1 < 2 ^ 56 \<and> length b < 2 ^ 56\<close>

lemma csubterms_self: \<open>t \<in> set (csubterms t)\<close>
  by (cases t) simp_all

lemma eok_self: \<open>eok N vs dv t \<Longrightarrow> 2 * cwidth (map length vs) (map length dv) t + 2 \<le> N \<and>
    2 * cwidth (map length vs) (map length dv) t + 2 < 2 ^ 56\<close>
  using csubterms_self[of t] by (auto simp add: eok_def)

lemma eok_pre:
  \<open>eok N vs dv (CoreTermL_Var i) \<Longrightarrow> unat i < length vs\<close>
  \<open>eok N vs dv (CoreTermL_Ref i) \<Longrightarrow> unat i < length dv\<close>
  \<open>eok N vs dv (CoreTermL_Not a) \<Longrightarrow> eok N vs dv a\<close>
  \<open>eok N vs dv (CoreTermL_Not a) \<Longrightarrow> length (eval_m vs dv a) \<le> N\<close>
  \<open>eok N vs dv (CoreTermL_Not a) \<Longrightarrow> length (eval_m vs dv a) < 2 ^ 56\<close>
  \<open>eok N vs dv (CoreTermL_Bin op a b) \<Longrightarrow> eok N vs dv a\<close>
  \<open>eok N vs dv (CoreTermL_Bin op a b) \<Longrightarrow> eok N vs dv b\<close>
  \<open>eok N vs dv (CoreTermL_Bin op a b) \<Longrightarrow> ebin_ok N op (eval_m vs dv a) (eval_m vs dv b)\<close>
  \<open>eok N vs dv (CoreTermL_Extract hi lo a) \<Longrightarrow> eok N vs dv a\<close>
  \<open>eok N vs dv (CoreTermL_Extract hi lo a) \<Longrightarrow> unat lo \<le> unat hi\<close>
  \<open>eok N vs dv (CoreTermL_Extract hi lo a) \<Longrightarrow> unat hi < length (eval_m vs dv a)\<close>
  \<open>eok N vs dv (CoreTermL_Extract hi lo a) \<Longrightarrow> length (eval_m vs dv a) < 2 ^ 56\<close>
  \<open>eok N vs dv (CoreTermL_Extract hi lo a) \<Longrightarrow> unat hi - unat lo + 1 \<le> N\<close>
  \<open>eok N vs dv (CoreTermL_Ite c a b) \<Longrightarrow> eok N vs dv c\<close>
  \<open>eok N vs dv (CoreTermL_Ite c a b) \<Longrightarrow> eok N vs dv a\<close>
  \<open>eok N vs dv (CoreTermL_Ite c a b) \<Longrightarrow> eok N vs dv b\<close>
  \<open>eok N vs dv (CoreTermL_Ite c a b) \<Longrightarrow> 0 < length (eval_m vs dv c)\<close>
proof -
  show \<open>eok N vs dv (CoreTermL_Var i) \<Longrightarrow> unat i < length vs\<close> by (simp add: eok_def)
  show \<open>eok N vs dv (CoreTermL_Ref i) \<Longrightarrow> unat i < length dv\<close> by (simp add: eok_def)
  show \<open>eok N vs dv (CoreTermL_Not a) \<Longrightarrow> eok N vs dv a\<close> by (simp add: eok_def)
  show \<open>eok N vs dv (CoreTermL_Not a) \<Longrightarrow> length (eval_m vs dv a) \<le> N\<close>
    using eok_len[of N vs dv a] eok_width[of N vs dv a] by (simp add: eok_def)
  show \<open>eok N vs dv (CoreTermL_Not a) \<Longrightarrow> length (eval_m vs dv a) < 2 ^ 56\<close>
    using eok_len[of N vs dv a] eok_width[of N vs dv a] by (simp add: eok_def)
  show \<open>eok N vs dv (CoreTermL_Bin op a b) \<Longrightarrow> eok N vs dv a\<close> by (simp add: eok_def)
  show \<open>eok N vs dv (CoreTermL_Bin op a b) \<Longrightarrow> eok N vs dv b\<close> by (simp add: eok_def)
  show \<open>eok N vs dv (CoreTermL_Bin op a b) \<Longrightarrow> ebin_ok N op (eval_m vs dv a) (eval_m vs dv b)\<close>
  proof -
    assume e: \<open>eok N vs dv (CoreTermL_Bin op a b)\<close>
    then have ea: \<open>eok N vs dv a\<close> and eb: \<open>eok N vs dv b\<close> by (simp_all add: eok_def)
    have wa: \<open>2 * cwidth (map length vs) (map length dv) a + 2 \<le> N \<and>
        2 * cwidth (map length vs) (map length dv) a + 2 < 2 ^ 56\<close> using eok_self[OF ea] .
    have wb: \<open>2 * cwidth (map length vs) (map length dv) b + 2 \<le> N \<and>
        2 * cwidth (map length vs) (map length dv) b + 2 < 2 ^ 56\<close> using eok_self[OF eb] .
    have \<open>op \<noteq> BinOp_Concat \<longrightarrow> cwidth (map length vs) (map length dv) a = cwidth (map length vs) (map length dv) b\<close>
      using e by (simp add: eok_def)
    then show ?thesis using eok_len[OF ea] eok_len[OF eb] wa wb by (simp add: ebin_ok_def)
  qed
  show \<open>eok N vs dv (CoreTermL_Extract hi lo a) \<Longrightarrow> eok N vs dv a\<close> by (simp add: eok_def)
  show \<open>eok N vs dv (CoreTermL_Extract hi lo a) \<Longrightarrow> unat lo \<le> unat hi\<close> by (simp add: eok_def)
  show \<open>eok N vs dv (CoreTermL_Extract hi lo a) \<Longrightarrow> unat hi < length (eval_m vs dv a)\<close>
    using eok_len[of N vs dv a] by (simp add: eok_def)
  show \<open>eok N vs dv (CoreTermL_Extract hi lo a) \<Longrightarrow> length (eval_m vs dv a) < 2 ^ 56\<close>
  proof -
    assume e: \<open>eok N vs dv (CoreTermL_Extract hi lo a)\<close>
    then have ea: \<open>eok N vs dv a\<close> by (simp add: eok_def)
    show ?thesis using eok_len[OF ea] eok_self[OF ea] by simp
  qed
  show \<open>eok N vs dv (CoreTermL_Extract hi lo a) \<Longrightarrow> unat hi - unat lo + 1 \<le> N\<close>
    using eok_width[of N vs dv \<open>CoreTermL_Extract hi lo a\<close>] by simp
  show \<open>eok N vs dv (CoreTermL_Ite c a b) \<Longrightarrow> eok N vs dv c\<close> by (simp add: eok_def)
  show \<open>eok N vs dv (CoreTermL_Ite c a b) \<Longrightarrow> eok N vs dv a\<close> by (simp add: eok_def)
  show \<open>eok N vs dv (CoreTermL_Ite c a b) \<Longrightarrow> eok N vs dv b\<close> by (simp add: eok_def)
  show \<open>eok N vs dv (CoreTermL_Ite c a b) \<Longrightarrow> 0 < length (eval_m vs dv c)\<close>
    using eok_len[of N vs dv c] by (simp add: eok_def)
qed

definition edefs_ok :: \<open>nat \<Rightarrow> CoreProblemL \<Rightarrow> bool list list \<Rightarrow> bool\<close> where
  \<open>edefs_ok N p m \<equiv>
     let ws = map length m in let D = CoreProblemL_defs p in
     cdefs_wt ws [] D \<and> length D \<le> N \<and> length D < 2 ^ 56 \<and>
     (\<forall>j < length D. Suc (size (D ! j)) \<le> N \<and>
        (\<forall>u \<in> set (csubterms (D ! j)).
           2 * cwidth ws (cdef_widths ws [] (take j D)) u + 2 \<le> N \<and>
           2 * cwidth ws (cdef_widths ws [] (take j D)) u + 2 < 2 ^ 56))\<close>

lemma edefs_step:
  assumes \<open>edefs_ok N p m\<close> \<open>j < length (CoreProblemL_defs p)\<close>
  shows \<open>eok N m (eval_defs_from m [] (take j (CoreProblemL_defs p))) (CoreProblemL_defs p ! j)\<close>
    \<open>Suc (size (CoreProblemL_defs p ! j)) \<le> N\<close>
proof -
  let ?D = \<open>CoreProblemL_defs p\<close> and ?ws = \<open>map length m\<close>
  have wt: \<open>cdefs_wt ?ws [] ?D\<close> using assms(1) by (simp add: edefs_ok_def Let_def)
  have \<open>cdefs_wt ?ws [] (take j ?D @ drop j ?D)\<close> using wt by simp
  then have wtj: \<open>cdefs_wt ?ws [] (take j ?D)\<close> by (simp only: cdefs_wt_app_eval)
  have ml: \<open>map length (eval_defs_from m [] (take j ?D)) = cdef_widths ?ws [] (take j ?D)\<close>
    using eval_defs_from[OF wtj refl, of \<open>[]\<close>] by simp
  show \<open>eok N m (eval_defs_from m [] (take j ?D)) (?D ! j)\<close>
    using assms cdefs_wt_nth[OF wt assms(2)] by (simp add: eok_def ml edefs_ok_def Let_def)
  show \<open>Suc (size (?D ! j)) \<le> N\<close> using assms by (simp add: edefs_ok_def Let_def)
qed

lemma edefs_len: \<open>edefs_ok N p m \<Longrightarrow> length (CoreProblemL_defs p) \<le> N\<close>
  \<open>edefs_ok N p m \<Longrightarrow> length (CoreProblemL_defs p) < 2 ^ 56\<close>
  by (simp_all add: edefs_ok_def Let_def)

context QFBV_ctx
begin

subsection \<open>The contracts of the helpers\<close>

definition bits_not_contract :: \<open>bool rvec \<Rightarrow> ('s, bool rvec, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>bits_not_contract a \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>rvec_length a \<le> urust_fuel \<and> rvec_length a < 2 ^ 56\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>rvec_elems r = bnot_m (rvec_elems a) \<and> vok r\<rangle>)\<close>

lemma bits_not_spec [crush_specs]:
  shows \<open>\<Gamma>; bits_not a \<Turnstile>\<^sub>F bits_not_contract a\<close>
  apply (crush_boot f: bits_not_def contract: bits_not_contract_def)
  apply (crush_base)
  subgoal for r_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gr r gi i. r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i \<le> rvec_length a \<and> rvec_elems r = map Not (take (unat i) (rvec_elems a)) \<and> vok r \<and> rvec_length a - unat i \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gr r gi i. r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i < rvec_length a \<and> rvec_elems r = map Not (take (unat i) (rvec_elems a)) \<and> vok r \<and> rvec_length a - unat i \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>rvec_elems r = bnot_m (rvec_elems a) \<and> vok r\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: push_not_None from_elem_Some word_less_nat_alt unat_of_nat_eq unat_of_nat_64 unat_word_Suc_simp
        bnot_m_def take_Suc_conv_app_nth)
    done
  done

definition bit_op_contract :: \<open>BinOp \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>bit_op_contract op x y \<equiv>
     make_function_contract can_alloc_reference (\<lambda>r. can_alloc_reference \<star> \<langle>r = bop op x y\<rangle>)\<close>

lemma bit_op_spec [crush_specs]:
  shows \<open>\<Gamma>; bit_op op x y \<Turnstile>\<^sub>F bit_op_contract op x y\<close>
  apply (crush_boot f: bit_op_def contract: bit_op_contract_def)
  apply (cases op; simp only: BinOp_case_simps)
             apply (crush_base simp add: bop_def)+
  done

definition bits_bitwise_contract :: \<open>BinOp \<Rightarrow> bool rvec \<Rightarrow> bool rvec \<Rightarrow> ('s, bool rvec, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>bits_bitwise_contract op a b \<equiv>
     make_function_contract
       (can_alloc_reference \<star> \<langle>rvec_length a \<le> urust_fuel \<and> rvec_length a < 2 ^ 56 \<and> rvec_length a \<le> rvec_length b\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>rvec_elems r = bbitw_m op (rvec_elems a) (rvec_elems b) \<and> vok r\<rangle>)\<close>

lemma bits_bitwise_spec [crush_specs]:
  shows \<open>\<Gamma>; bits_bitwise op a b \<Turnstile>\<^sub>F bits_bitwise_contract op a b\<close>
  apply (crush_boot f: bits_bitwise_def contract: bits_bitwise_contract_def)
  apply (crush_base)
  subgoal for r_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gr r gi i. r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i \<le> rvec_length a \<and> rvec_elems r = take (unat i) (bbitw_m op (rvec_elems a) (rvec_elems b)) \<and> vok r \<and> rvec_length a - unat i \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gr r gi i. r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i < rvec_length a \<and> rvec_elems r = take (unat i) (bbitw_m op (rvec_elems a) (rvec_elems b)) \<and> vok r \<and> rvec_length a - unat i \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>rvec_elems r = bbitw_m op (rvec_elems a) (rvec_elems b) \<and> vok r\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: push_not_None from_elem_Some word_less_nat_alt unat_of_nat_eq unat_of_nat_64 unat_word_Suc_simp
        take_Suc_conv_app_nth nth_bbitw)
    done
  done

definition full_add_contract :: \<open>bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> ('s, bool \<times> bool \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>full_add_contract x y c \<equiv>
     make_function_contract can_alloc_reference
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = (fst (fa x y c), snd (fa x y c), TNil)\<rangle>)\<close>

lemma full_add_spec [crush_specs]:
  shows \<open>\<Gamma>; full_add x y c \<Turnstile>\<^sub>F full_add_contract x y c\<close>
  apply (crush_boot f: full_add_def contract: full_add_contract_def)
  apply (cases x; cases y; cases c; crush_base simp add: fa_def)
  done

definition bits_add_contract :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> bool \<Rightarrow> ('s, bool list \<times> bool \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>bits_add_contract a b cin \<equiv>
     make_function_contract
       (can_alloc_reference \<star> \<langle>length a \<le> urust_fuel \<and> length a < 2 ^ 64 \<and> length a \<le> length b\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = (fst (badd_m a b cin), snd (badd_m a b cin), TNil)\<rangle>)\<close>

lemma bits_add_spec [crush_specs]:
  shows \<open>\<Gamma>; bits_add a b cin \<Turnstile>\<^sub>F bits_add_contract a b cin\<close>
  apply (crush_boot f: bits_add_def contract: bits_add_contract_def)
  apply (crush_base inline: len_def)
  subgoal for carry_ref r_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gy y gr r gi i. carry_ref \<mapsto>\<langle>\<top>\<rangle> gy\<down>y \<star> r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
               can_alloc_reference \<star>
               \<langle>unat i \<le> length a \<and> r = fst (foldl (badd_step a b) ([], cin) [0..<unat i]) \<and>
                y = snd (foldl (badd_step a b) ([], cin) [0..<unat i]) \<and> length a - unat i \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gy y gr r gi i. carry_ref \<mapsto>\<langle>\<top>\<rangle> gy\<down>y \<star> r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
               can_alloc_reference \<star>
               \<langle>unat i < length a \<and> r = fst (foldl (badd_step a b) ([], cin) [0..<unat i]) \<and>
                y = snd (foldl (badd_step a b) ([], cin) [0..<unat i]) \<and> length a - unat i \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>r = (fst (badd_m a b cin), snd (badd_m a b cin), TNil)\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: vec_push_def simp add: word_less_nat_alt unat_of_nat_eq unat_of_nat_64 unat_word_Suc_simp
        antisym_conv badd_m_def badd_step_eq)
    done
  done

end


subsection \<open>Facts for the remaining loops\<close>

lemma unat_Suc_len:
  fixes r :: \<open>64 word\<close>
  shows \<open>unat r < length xs \<Longrightarrow> length xs < 2 ^ 64 \<Longrightarrow> unat (r + 1) = Suc (unat r)\<close>
  by (rule unat_word_Suc_simp) simp

definition beq_step :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>beq_step a b r i \<equiv> if a ! i \<noteq> b ! i then False else r\<close>

lemma beq_m_fold: \<open>beq_m a b = foldl (beq_step a b) True [0..<length a]\<close>
proof -
  have \<open>foldl (beq_step a b) r0 [0..<n] = foldl (\<lambda>r i. r \<and> a ! i = b ! i) r0 [0..<n]\<close> for r0 n
    by (induction n) (simp_all add: beq_step_def)
  then show ?thesis by (simp add: beq_m_def)
qed

lemma shl1_exit: \<open>length r \<le> Suc k \<Longrightarrow> k < length r \<Longrightarrow> length r - Suc 0 = k\<close>
  by simp

lemma unat_dec: \<open>1 \<le> unat w \<Longrightarrow> unat (w - 1) = unat w - 1\<close> for w :: \<open>64 word\<close>
  by (simp add: unat_sub word_le_nat_alt)

lemma unat_Suc_word: \<open>unat r < unat w \<Longrightarrow> unat (r + 1) = Suc (unat r)\<close> for r w :: \<open>64 word\<close>
  using unat_lt2p[of w] by (intro unat_word_Suc_simp) simp

lemma bdiv_run_down:
  assumes \<open>0 < i\<close> \<open>i \<le> length a\<close>
  shows \<open>bdiv_run a b (Suc (length a) - i) =
    (if snd (badd_m (bshl1_m (snd (bdiv_run a b (length a - i))) (a ! (i - Suc 0))) (bnot_m (bzext_m b (Suc (length a)))) True)
     then ((fst (bdiv_run a b (length a - i)))[i - Suc 0 := True],
           fst (badd_m (bshl1_m (snd (bdiv_run a b (length a - i))) (a ! (i - Suc 0))) (bnot_m (bzext_m b (Suc (length a)))) True))
     else (fst (bdiv_run a b (length a - i)), bshl1_m (snd (bdiv_run a b (length a - i))) (a ! (i - Suc 0))))\<close>
proof -
  have e: \<open>Suc (length a) - i = Suc (length a - i)\<close> using assms by simp
  have j: \<open>length a - 1 - (length a - i) = i - Suc 0\<close> using assms by simp
  show ?thesis unfolding e bdiv_run_Suc bdiv_step_eq j by simp
qed

lemma unat_lt_word: \<open>unat r < unat w \<Longrightarrow> unat r < 18446744073709551615\<close> for r w :: \<open>64 word\<close>
  using unat_lt2p[of w] by simp

definition bstep_nat :: \<open>nat \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>bstep_nat s x w \<equiv>
     if s < w then (let s2 = (if x then s + s + 1 else s + s) in if w < s2 then w else s2) else s\<close>

lemma bshift_fold_down:
  assumes \<open>0 < i\<close> \<open>i \<le> length b\<close>
  shows \<open>foldl (bshift_step w b) 0 [0..<Suc (length b) - i] =
    bstep_nat (foldl (bshift_step w b) 0 [0..<length b - i]) (b ! (i - Suc 0)) w\<close>
proof -
  have \<open>Suc (length b) - i = Suc (length b - i)\<close> using assms by simp
  moreover have \<open>length b - 1 - (length b - i) = i - Suc 0\<close> using assms by simp
  ultimately show ?thesis by (simp add: bshift_step_def bstep_nat_def)
qed

lemma eval_defs_from_Nil [simp]: \<open>eval_defs_from vs dv [] = dv\<close>
  by (simp add: eval_defs_from_def)

context QFBV_ctx
begin

definition bits_shift_const_contract :: \<open>bool rvec \<Rightarrow> 64 word \<Rightarrow> bool \<Rightarrow> ('s, bool rvec, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>bits_shift_const_contract a s left \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>rvec_length a \<le> urust_fuel \<and> rvec_length a < 2 ^ 56\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>rvec_elems r = bshift_const_m (rvec_elems a) (unat s) left \<and> vok r\<rangle>)\<close>

lemma bits_shift_const_spec [crush_specs]:
  shows \<open>\<Gamma>; bits_shift_const a s left \<Turnstile>\<^sub>F bits_shift_const_contract a s left\<close>
  apply (crush_boot f: bits_shift_const_def contract: bits_shift_const_contract_def)
  apply (crush_base)
  subgoal for r_ref j_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gr r gj j. r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star>
               \<langle>unat j \<le> rvec_length a \<and> rvec_elems r = take (unat j) (bshift_const_m (rvec_elems a) (unat s) left) \<and>
                rvec_length a - unat j \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gr r gj j. r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star>
               \<langle>unat j < rvec_length a \<and> rvec_elems r = take (unat j) (bshift_const_m (rvec_elems a) (unat s) left) \<and>
                rvec_length a - unat j \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>rvec_elems r = bshift_const_m (rvec_elems a) (unat s) left \<and> vok r\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: push_not_None from_elem_Some word_less_nat_alt unat_of_nat_eq unat_of_nat_64 unat_word_Suc_simp unat_Suc_len
        take_Suc_conv_app_nth unat_sub_not_less unat_len_minus unat_add_less_len word_le_nat_alt )
    done
  done

definition bits_mul_contract :: \<open>bool rvec \<Rightarrow> bool rvec \<Rightarrow> ('s, bool rvec, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>bits_mul_contract a b \<equiv>
     make_function_contract
       (can_alloc_reference \<star> \<langle>rvec_length a \<le> urust_fuel \<and> rvec_length a < 2 ^ 56 \<and> rvec_length a \<le> rvec_length b\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>rvec_elems r = bmul_m (rvec_elems a) (rvec_elems b) \<and> vok r\<rangle>)\<close>

lemma bits_mul_spec [crush_specs]:
  shows \<open>\<Gamma>; bits_mul a b \<Turnstile>\<^sub>F bits_mul_contract a b\<close>
  apply (crush_boot f: bits_mul_def contract: bits_mul_contract_def)
  apply (crush_base simp add: push_not_None from_elem_Some unat_of_nat_eq unat_of_nat_64)
  subgoal for acc_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gr r gi i. acc_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i \<le> rvec_length a \<and> rvec_elems r = foldl (bmul_step (rvec_elems a) (rvec_elems b)) (replicate (rvec_length a) False) [0..<unat i] \<and>
                rvec_length a - unat i \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gr r gi i. acc_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i < rvec_length a \<and> rvec_elems r = foldl (bmul_step (rvec_elems a) (rvec_elems b)) (replicate (rvec_length a) False) [0..<unat i] \<and>
                rvec_length a - unat i \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>rvec_elems r = bmul_m (rvec_elems a) (rvec_elems b) \<and> vok r\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: word_less_nat_alt unat_of_nat_eq unat_of_nat_64 unat_word_Suc_simp unat_Suc_len
        antisym_conv bmul_fold_len bmul_m_def bmul_step_def)
    done
  done

definition bits_eq_contract :: \<open>bool rvec \<Rightarrow> bool rvec \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>bits_eq_contract a b \<equiv>
     make_function_contract
       (can_alloc_reference \<star> \<langle>rvec_length a \<le> urust_fuel \<and> rvec_length a < 2 ^ 56 \<and> rvec_length a \<le> rvec_length b\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>rvec_elems r = beq_m (rvec_elems a) (rvec_elems b)\<rangle>)\<close>

lemma bits_eq_spec [crush_specs]:
  shows \<open>\<Gamma>; bits_eq a b \<Turnstile>\<^sub>F bits_eq_contract a b\<close>
  apply (crush_boot f: bits_eq_def contract: bits_eq_contract_def)
  apply (crush_base)
  subgoal for r_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gr r gi i. r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i \<le> rvec_length a \<and> rvec_elems r = foldl (beq_step (rvec_elems a) (rvec_elems b)) True [0..<unat i] \<and>
                rvec_length a - unat i \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gr r gi i. r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i < rvec_length a \<and> rvec_elems r = foldl (beq_step (rvec_elems a) (rvec_elems b)) True [0..<unat i] \<and>
                rvec_length a - unat i \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>rvec_elems r = beq_m (rvec_elems a) (rvec_elems b)\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: push_not_None from_elem_Some word_less_nat_alt unat_of_nat_eq unat_of_nat_64 unat_word_Suc_simp unat_Suc_len
        antisym_conv beq_m_fold beq_step_def)
    done
  done

definition bits_ult_contract :: \<open>bool rvec \<Rightarrow> bool rvec \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>bits_ult_contract a b \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
        \<langle>rvec_length a \<le> urust_fuel \<and> rvec_length a < 2 ^ 56 \<and> rvec_length b \<le> urust_fuel \<and> rvec_length b < 2 ^ 56 \<and>
         rvec_length a \<le> rvec_length b\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>rvec_elems r = bult_m (rvec_elems a) (rvec_elems b)\<rangle>)\<close>

lemma bits_ult_spec [crush_specs]:
  shows \<open>\<Gamma>; bits_ult a b \<Turnstile>\<^sub>F bits_ult_contract a b\<close>
  apply (crush_boot f: bits_ult_def contract: bits_ult_contract_def)
  apply (crush_base simp add: push_not_None from_elem_Some bult_m_def)
  done

definition bits_zext_contract :: \<open>bool rvec \<Rightarrow> 64 word \<Rightarrow> ('s, bool rvec, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>bits_zext_contract a w \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>unat w \<le> urust_fuel \<and> rvec_length a < 2 ^ 56\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>rvec_elems r = bzext_m (rvec_elems a) (unat w) \<and> vok r\<rangle>)\<close>

lemma bits_zext_spec [crush_specs]:
  shows \<open>\<Gamma>; bits_zext a w \<Turnstile>\<^sub>F bits_zext_contract a w\<close>
  apply (crush_boot f: bits_zext_def contract: bits_zext_contract_def)
  apply (crush_base)
  subgoal for r_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gr r gi i. r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i \<le> unat w \<and> unat w < 2 ^ 64 \<and> rvec_elems r = take (unat i) (bzext_m (rvec_elems a) (unat w)) \<and> unat w - unat i \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gr r gi i. r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i < unat w \<and> unat w < 2 ^ 64 \<and> rvec_elems r = take (unat i) (bzext_m (rvec_elems a) (unat w)) \<and> unat w - unat i \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>rvec_elems r = bzext_m (rvec_elems a) (unat w) \<and> vok r\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: push_not_None from_elem_Some word_less_nat_alt unat_of_nat_eq unat_of_nat_64 unat_word_Suc_simp unat_Suc_len
        take_Suc_conv_app_nth unat_lt_2p64 unat_Suc_word unat_lt_word)
    done
  done

definition bits_shl1_contract :: \<open>bool rvec \<Rightarrow> bool \<Rightarrow> ('s, bool rvec, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>bits_shl1_contract r x \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>rvec_length r \<le> urust_fuel \<and> rvec_length r < 2 ^ 56\<rangle>)
       (\<lambda>s. can_alloc_reference \<star> \<langle>s = bshl1_m (rvec_elems r) x\<rangle>)\<close>

lemma bits_shl1_spec [crush_specs]:
  shows \<open>\<Gamma>; bits_shl1 r x \<Turnstile>\<^sub>F bits_shl1_contract r x\<close>
  apply (crush_boot f: bits_shl1_def contract: bits_shl1_contract_def)
  apply (crush_base vec_push_def)
  subgoal for s_ref k_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>c. \<Squnion>gs s gk k. s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>s \<star> k_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>k \<star> can_alloc_reference \<star>
               \<langle>(unat k = 0 \<or> unat k < rvec_length r) \<and> s = x # take (unat k) (rvec_elems r) \<and> rvec_length r - Suc (unat k) \<le> c\<rangle>\<close> and
        INV'=\<open>\<lambda>c. \<Squnion>gs s gk k. s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>s \<star> k_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>k \<star> can_alloc_reference \<star>
               \<langle>Suc (unat k) < rvec_length r \<and> s = x # take (unat k) (rvec_elems r) \<and> rvec_length r - Suc (unat k) \<le> Suc c\<rangle>\<close> and
        \<tau>=\<open>\<lambda>s. can_alloc_reference \<star> \<langle>s = bshl1_m (rvec_elems r) x\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: push_not_None from_elem_Some word_less_nat_alt unat_of_nat_eq unat_of_nat_64 unat_word_Suc_simp unat_Suc_len
        take_Suc_conv_app_nth bshl1_m_def shl1_exit)
    done
  done

definition bits_extract_contract :: \<open>bool rvec \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, bool rvec, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>bits_extract_contract a hi lo \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
        \<langle>unat lo \<le> unat hi \<and> unat hi < rvec_length a \<and> rvec_length a < 2 ^ 56 \<and> unat hi - unat lo + 1 \<le> urust_fuel\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>rvec_elems r = bextract_m (rvec_elems a) (unat hi) (unat lo) \<and> vok r\<rangle>)\<close>

lemma bits_extract_spec [crush_specs]:
  shows \<open>\<Gamma>; bits_extract a hi lo \<Turnstile>\<^sub>F bits_extract_contract a hi lo\<close>
  apply (crush_boot f: bits_extract_def contract: bits_extract_contract_def)
  apply (crush_base)
  subgoal for r_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gr r gi i. r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat lo \<le> unat i \<and> unat i \<le> Suc (unat hi) \<and>
                r = take (unat i - unat lo) (bextract_m (rvec_elems a) (unat hi) (unat lo)) \<and> Suc (unat hi) - unat i \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gr r gi i. r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat lo \<le> unat i \<and> unat i \<le> unat hi \<and>
                r = take (unat i - unat lo) (bextract_m (rvec_elems a) (unat hi) (unat lo)) \<and> Suc (unat hi) - unat i \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>rvec_elems r = bextract_m (rvec_elems a) (unat hi) (unat lo) \<and> vok r\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: push_not_None from_elem_Some word_le_nat_alt unat_of_nat_eq unat_of_nat_64 unat_word_Suc_simp unat_Suc_len
        take_Suc_conv_app_nth Suc_diff_le)
    done
  done

definition bits_concat_contract :: \<open>bool rvec \<Rightarrow> bool rvec \<Rightarrow> ('s, bool rvec, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>bits_concat_contract hi lo \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>rvec_length hi \<le> urust_fuel \<and> rvec_length hi < 2 ^ 56\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>rvec_elems r = bconcat_m (rvec_elems hi) (rvec_elems lo) \<and> vok r\<rangle>)\<close>

lemma bits_concat_spec [crush_specs]:
  shows \<open>\<Gamma>; bits_concat hi lo \<Turnstile>\<^sub>F bits_concat_contract hi lo\<close>
  apply (crush_boot f: bits_concat_def contract: bits_concat_contract_def)
  apply (crush_base)
  subgoal for r_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gr r gi i. r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i \<le> rvec_length hi \<and> rvec_elems r = (rvec_elems lo) @ take (unat i) (rvec_elems hi) \<and> vok r \<and> rvec_length hi - unat i \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gr r gi i. r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i < rvec_length hi \<and> rvec_elems r = (rvec_elems lo) @ take (unat i) (rvec_elems hi) \<and> vok r \<and> rvec_length hi - unat i \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>rvec_elems r = bconcat_m (rvec_elems hi) (rvec_elems lo) \<and> vok r\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: push_not_None from_elem_Some word_less_nat_alt unat_of_nat_eq unat_of_nat_64 unat_word_Suc_simp unat_Suc_len
        take_Suc_conv_app_nth bconcat_m_def)
    done
  done

definition bits_divrem_contract :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> ('s, bool list \<times> bool list \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>bits_divrem_contract a b \<equiv>
     make_function_contract
       (can_alloc_reference \<star> \<langle>length b = length a \<and> length a + 1 \<le> urust_fuel \<and> length a + 1 < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = (fst (bdivrem_m a b), snd (bdivrem_m a b), TNil)\<rangle>)\<close>

lemma bits_divrem_spec [crush_specs]:
  shows \<open>\<Gamma>; bits_divrem a b \<Turnstile>\<^sub>F bits_divrem_contract a b\<close>
  apply (crush_boot f: bits_divrem_def contract: bits_divrem_contract_def)
  apply (crush_base inline: len_def vec_from_elem_def
      simp add: unat_of_nat_eq unat_of_nat_64 unat_word_Suc_simp bdivrem_m_zero)
  subgoal for q_ref r_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>c. \<Squnion>gq qq gr rr gi i. q_ref \<mapsto>\<langle>\<top>\<rangle> gq\<down>qq \<star> r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>rr \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
               can_alloc_reference \<star>
               \<langle>unat i \<le> length a \<and> qq = fst (bdiv_run a b (length a - unat i)) \<and>
                rr = snd (bdiv_run a b (length a - unat i)) \<and> unat i \<le> c\<rangle>\<close> and
        INV'=\<open>\<lambda>c. \<Squnion>gq qq gr rr gi i. q_ref \<mapsto>\<langle>\<top>\<rangle> gq\<down>qq \<star> r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>rr \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
               can_alloc_reference \<star>
               \<langle>0 < unat i \<and> unat i \<le> length a \<and> qq = fst (bdiv_run a b (length a - unat i)) \<and>
                rr = snd (bdiv_run a b (length a - unat i)) \<and> unat i \<le> Suc c\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>r = (fst (bdivrem_m a b), snd (bdivrem_m a b), TNil)\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: len_def simp add: word_less_nat_alt unat_of_nat_eq unat_of_nat_64 unat_dec
        word_le_nat_alt bdiv_run_down bdiv_run_len bdiv_run_0 bdivrem_m_nz)
    done
  done

definition shift_amount_step_contract :: \<open>64 word \<Rightarrow> bool \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>shift_amount_step_contract s x w \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>unat s \<le> unat w \<and> 2 * unat w + 1 < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>unat r = bstep_nat (unat s) x (unat w)\<rangle>)\<close>

lemma shift_amount_step_spec [crush_specs]:
  shows \<open>\<Gamma>; shift_amount_step s x w \<Turnstile>\<^sub>F shift_amount_step_contract s x w\<close>
proof (crush_boot f: shift_amount_step_def contract: shift_amount_step_contract_def, goal_cases)
  case 1
  have u1: \<open>unat (s + s) = unat s + unat s\<close>
  proof -
    have \<open>unat s + unat s < 2 ^ LENGTH(64)\<close> using 1 by simp
    then show ?thesis using unat_add_lem by blast
  qed
  have u2: \<open>unat (s + s + 1) = unat s + unat s + 1\<close>
  proof -
    have \<open>unat (s + s) < 18446744073709551615\<close> using 1 u1 by simp
    then show ?thesis using unat_word_Suc_simp[of \<open>s + s\<close>] u1 by simp
  qed
  note 1 u1 u2
  then show ?case by (crush_base simp add: bstep_nat_def word_less_nat_alt Let_def)
qed

definition bits_shift_contract :: \<open>bool rvec \<Rightarrow> bool rvec \<Rightarrow> bool \<Rightarrow> ('s, bool rvec, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>bits_shift_contract a b left \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
        \<langle>rvec_length a \<le> urust_fuel \<and> rvec_length b \<le> urust_fuel \<and> rvec_length b < 2 ^ 56 \<and> 2 * rvec_length a + 1 < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>rvec_elems r = bshift_m (rvec_elems a) (rvec_elems b) left \<and> vok r\<rangle>)\<close>

lemma bits_shift_spec [crush_specs]:
  shows \<open>\<Gamma>; bits_shift a b left \<Turnstile>\<^sub>F bits_shift_contract a b left\<close>
  apply (crush_boot f: bits_shift_def contract: bits_shift_contract_def)
  apply (crush_base simp add: push_not_None from_elem_Some unat_of_nat_eq unat_of_nat_64)
  subgoal for s_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>c. \<Squnion>gs s gi i. s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>s \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i \<le> rvec_length b \<and> unat s = foldl (bshift_step (rvec_length a) (rvec_elems b)) 0 [0..<rvec_length b - unat i] \<and>
                unat i \<le> c\<rangle>\<close> and
        INV'=\<open>\<lambda>c. \<Squnion>gs s gi i. s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>s \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>0 < unat i \<and> unat i \<le> rvec_length b \<and> unat s = foldl (bshift_step (rvec_length a) (rvec_elems b)) 0 [0..<rvec_length b - unat i] \<and>
                unat i \<le> Suc c\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>rvec_elems r = bshift_m (rvec_elems a) (rvec_elems b) left \<and> vok r\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: word_less_nat_alt unat_of_nat_eq unat_of_nat_64 unat_dec
        word_le_nat_alt bshift_fold_down bshift_fold_le bshift_m_def)
    done
  done

definition eval_bin_contract :: \<open>BinOp \<Rightarrow> bool rvec \<Rightarrow> bool rvec \<Rightarrow> ('s, bool rvec, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>eval_bin_contract op a b \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>ebin_ok urust_fuel op (rvec_elems a) (rvec_elems b)\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>rvec_elems r = eval_bin_m op (rvec_elems a) (rvec_elems b) \<and> vok r\<rangle>)\<close>

lemma eval_bin_spec [crush_specs]:
  shows \<open>\<Gamma>; eval_bin op a b \<Turnstile>\<^sub>F eval_bin_contract op a b\<close>
  apply (crush_boot f: eval_bin_def contract: eval_bin_contract_def)
  apply (cases op; simp only: BinOp_case_simps)
             apply (crush_base simp add: push_not_None from_elem_Some ebin_ok_def eval_bin_m_def)+
  done

subsection \<open>\<^verbatim>\<open>eval_term\<close>\<close>

text \<open>The \<open>k\<close>-th unfolding of \<^verbatim>\<open>eval_term\<close>: its precondition requires the recursion depth
  \<open>size t + 1\<close> to be at most \<open>k\<close>, so the innermost function is never called.\<close>
definition eval_term_contract ::
  \<open>nat \<Rightarrow> bool rvec rvec \<Rightarrow> bool rvec rvec \<Rightarrow> CoreTerm \<Rightarrow> ('s, bool rvec, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>eval_term_contract k vs dv t \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
        \<langle>Suc (size t) \<le> k \<and> allvok vs \<and> allvok dv \<and> eok urust_fuel (vecs_of vs) (vecs_of dv) (ct_of t)\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>rvec_elems r = eval_m (vecs_of vs) (vecs_of dv) (ct_of t) \<and> vok r\<rangle>)\<close>

lemma eval_term_rec_step_spec:
  assumes IH: \<open>\<And>vs dv t. \<Gamma>; R vs dv t \<Turnstile>\<^sub>F eval_term_contract k vs dv t\<close>
  shows \<open>\<Gamma>; eval_term_rec_step R vs dv t \<Turnstile>\<^sub>F eval_term_contract (Suc k) vs dv t\<close>
proof (cases t)
  case (CoreTerm_Const bs)
  show ?thesis unfolding CoreTerm_Const
  proof (crush_boot f: eval_term_rec_step_def contract: eval_term_contract_def, goal_cases)
    case 1
    note 1
    then show ?case by (crush_base specs add: IH simp add: allvok_nth)
  qed
next
  case (CoreTerm_Var i)
  show ?thesis unfolding CoreTerm_Var
  proof (crush_boot f: eval_term_rec_step_def contract: eval_term_contract_def, goal_cases)
    case 1
    have E0: \<open>unat i < rvec_length vs\<close> using 1 by (meson eok_pre(1))
    note 1 E0
    then show ?case by (crush_base specs add: IH simp add: allvok_nth)
  qed
next
  case (CoreTerm_Ref i)
  show ?thesis unfolding CoreTerm_Ref
  proof (crush_boot f: eval_term_rec_step_def contract: eval_term_contract_def, goal_cases)
    case 1
    have E0: \<open>unat i < rvec_length dv\<close> using 1 by (meson eok_pre(2))
    note 1 E0
    then show ?case by (crush_base specs add: IH simp add: allvok_nth)
  qed
next
  case (CoreTerm_Not a)
  show ?thesis unfolding CoreTerm_Not
  proof (crush_boot f: eval_term_rec_step_def contract: eval_term_contract_def, goal_cases)
    case 1
    have E0: \<open>eok urust_fuel (vecs_of vs) (vecs_of dv) (ct_of a)\<close> using 1 by (meson eok_pre(3))
    have E1: \<open>length (eval_m (vecs_of vs) (vecs_of dv) (ct_of a)) \<le> urust_fuel\<close> using 1 by (meson eok_pre(4))
    have E2: \<open>length (eval_m (vecs_of vs) (vecs_of dv) (ct_of a)) < 2 ^ 56\<close> using 1 by (meson eok_pre(5))
    note 1 E0 E1 E2
    then show ?case by (crush_base specs add: IH simp add: allvok_nth)
  qed
next
  case (CoreTerm_Bin op a b)
  show ?thesis unfolding CoreTerm_Bin
  proof (crush_boot f: eval_term_rec_step_def contract: eval_term_contract_def, goal_cases)
    case 1
    have E0: \<open>eok urust_fuel (vecs_of vs) (vecs_of dv) (ct_of a)\<close> using 1 by (meson eok_pre(6))
    have E1: \<open>eok urust_fuel (vecs_of vs) (vecs_of dv) (ct_of b)\<close> using 1 by (meson eok_pre(7))
    have E2: \<open>ebin_ok urust_fuel op (eval_m (vecs_of vs) (vecs_of dv) (ct_of a)) (eval_m (vecs_of vs) (vecs_of dv) (ct_of b))\<close> using 1 by (meson eok_pre(8))
    have E3: \<open>Suc (size a) \<le> k\<close> using 1 by simp
    have E4: \<open>Suc (size b) \<le> k\<close> using 1 by simp
    note 1 E0 E1 E2 E3 E4
    then show ?case by (crush_base specs add: IH simp add: allvok_nth)
  qed
next
  case (CoreTerm_Extract hi lo a)
  show ?thesis unfolding CoreTerm_Extract
  proof (crush_boot f: eval_term_rec_step_def contract: eval_term_contract_def, goal_cases)
    case 1
    have E0: \<open>eok urust_fuel (vecs_of vs) (vecs_of dv) (ct_of a)\<close> using 1 by (meson eok_pre(9))
    have E1: \<open>unat lo \<le> unat hi\<close> using 1 by (meson eok_pre(10))
    have E2: \<open>unat hi < length (eval_m (vecs_of vs) (vecs_of dv) (ct_of a))\<close> using 1 by (meson eok_pre(11))
    have E3: \<open>length (eval_m (vecs_of vs) (vecs_of dv) (ct_of a)) < 2 ^ 56\<close> using 1 by (meson eok_pre(12))
    have E4: \<open>unat hi - unat lo + 1 \<le> urust_fuel\<close> using 1 by (meson eok_pre(13))
    note 1 E0 E1 E2 E3 E4
    then show ?case by (crush_base specs add: IH simp add: allvok_nth)
  qed
next
  case (CoreTerm_Ite c a b)
  show ?thesis
  proof (crush_boot f: eval_term_rec_step_def contract: eval_term_contract_def, goal_cases)
    case 1
    have E0: \<open>eok urust_fuel (vecs_of vs) (vecs_of dv) (ct_of c)\<close> using 1 CoreTerm_Ite by (meson eok_pre(14))
    have E1: \<open>eok urust_fuel (vecs_of vs) (vecs_of dv) (ct_of a)\<close> using 1 CoreTerm_Ite by (meson eok_pre(15))
    have E2: \<open>eok urust_fuel (vecs_of vs) (vecs_of dv) (ct_of b)\<close> using 1 CoreTerm_Ite by (meson eok_pre(16))
    have E3: \<open>0 < length (eval_m (vecs_of vs) (vecs_of dv) (ct_of c))\<close> using 1 CoreTerm_Ite by (meson eok_pre(17))
    have S0: \<open>Suc (size c) \<le> k\<close> using 1 CoreTerm_Ite by simp
    have S1: \<open>Suc (size a) \<le> k\<close> using 1 CoreTerm_Ite by simp
    have S2: \<open>Suc (size b) \<le> k\<close> using 1 CoreTerm_Ite by simp
    note 1 E0 E1 E2 E3 S0 S1 S2 CoreTerm_Ite
    then show ?case by (crush_base specs add: IH simp add: allvok_nth)
  qed
qed

lemma eval_term_rec_spec:
  shows \<open>\<Gamma>; (eval_term_rec_step ^^ k) g vs dv t \<Turnstile>\<^sub>F eval_term_contract k vs dv t\<close>
proof (induction k arbitrary: vs dv t)
  case 0
  show ?case
    apply (ucincl_discharge\<open>intro satisfies_function_contractI\<close>)
    apply (subst wp_sstriple_iff)
    apply (simp add: eval_term_contract_def Let_def apure_precise_False asepconj_bot_zero2 bot_aentails_all)
    done
next
  case (Suc k)
  show ?case
    unfolding funpow.simps(2) comp_def by (rule eval_term_rec_step_spec) (rule Suc.IH)
qed

lemma eval_term_spec [crush_specs]:
  shows \<open>\<Gamma>; eval_term vs dv t \<Turnstile>\<^sub>F eval_term_contract urust_fuel vs dv t\<close>
  unfolding eval_term_def by (rule eval_term_rec_spec)

subsection \<open>\<^verbatim>\<open>eval_defs\<close>\<close>

definition eval_defs_contract :: \<open>CoreProblem \<Rightarrow> bool rvec rvec \<Rightarrow> ('s, bool rvec rvec, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>eval_defs_contract p m \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
        \<langle>rvec_length (CoreProblem_defs p) \<le> urust_fuel \<and> rvec_length (CoreProblem_defs p) < 2 ^ 56 \<and>
         allvok m \<and> edefs_ok urust_fuel (cprob_of p) (vecs_of m)\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>vecs_of r = eval_defs_m (cprob_of p) (vecs_of m) \<and> vok r \<and> allvok r\<rangle>)\<close>

lemma eval_defs_spec [crush_specs]:
  shows \<open>\<Gamma>; eval_defs p m \<Turnstile>\<^sub>F eval_defs_contract p m\<close>
  apply (crush_boot f: eval_defs_def contract: eval_defs_contract_def)
  apply (crush_base)
  subgoal for d_ref j_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gd d gj j. d_ref \<mapsto>\<langle>\<top>\<rangle> gd\<down>d \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star>
               \<langle>unat j \<le> rvec_length (CoreProblem_defs p) \<and>
                vecs_of d = eval_defs_from (vecs_of m) [] (take (unat j) (CoreProblemL_defs (cprob_of p))) \<and>
                vok d \<and> allvok d \<and> rvec_length (CoreProblem_defs p) - unat j \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gd d gj j. d_ref \<mapsto>\<langle>\<top>\<rangle> gd\<down>d \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star>
               \<langle>unat j < rvec_length (CoreProblem_defs p) \<and>
                vecs_of d = eval_defs_from (vecs_of m) [] (take (unat j) (CoreProblemL_defs (cprob_of p))) \<and>
                vok d \<and> allvok d \<and> rvec_length (CoreProblem_defs p) - unat j \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>vecs_of r = eval_defs_m (cprob_of p) (vecs_of m) \<and> vok r \<and> allvok r\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: push_not_None word_less_nat_alt unat_of_nat_eq unat_of_nat_64 unat_word_Suc_simp unat_Suc_len
        antisym_conv edefs_step take_Suc_conv_app_nth eval_defs_from_snoc eval_defs_m_def)
    done
  done

end

end
