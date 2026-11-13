theory QFBV_Lower
  imports QFBV_Core
begin

section \<open>The rewriting into the core language\<close>

text \<open>
  Functional models of the Rust functions that rewrite a problem of the extended language into
  the core language (\<^verbatim>\<open>push_def\<close>, \<^verbatim>\<open>lower_bin\<close>, \<^verbatim>\<open>lower\<close>, \<^verbatim>\<open>lower_problem\<close>), and the proof
  that the rewriting preserves the semantics: the core problem is well-sorted and has the same
  models as the extended problem. \<^verbatim>\<open>QFBV_LowerRefine\<close> proves that the Rust functions compute
  these models.

  The state of the rewriting (\<^verbatim>\<open>Lower\<close>) is modelled by \<open>lst\<close>: the core definitions built so far
  and their widths, as natural numbers.
\<close>

type_synonym lst = \<open>CoreTerm list \<times> nat list\<close>

text \<open>The Rust \<^verbatim>\<open>Lower\<close> of a state.\<close>
definition lower_of :: \<open>lst \<Rightarrow> Lower\<close> where
  \<open>lower_of L \<equiv> make_Lower (fst L) (map word_of_nat (snd L))\<close>

subsection \<open>Models of the functions\<close>

definition push_m :: \<open>lst \<Rightarrow> CoreTerm \<Rightarrow> nat \<Rightarrow> lst \<times> nat\<close> where
  \<open>push_m L t w \<equiv> ((fst L @ [t], snd L @ [w]), length (fst L))\<close>

text \<open>A reference to the core definition \<open>k\<close>.\<close>
definition cr :: \<open>nat \<Rightarrow> CoreTerm\<close> where
  \<open>cr k \<equiv> CoreTerm_Ref (word_of_nat k)\<close>

text \<open>The core terms built by \<^verbatim>\<open>cone\<close>, \<^verbatim>\<open>cneg\<close>, \<^verbatim>\<open>cmsb\<close>, \<^verbatim>\<open>cabs\<close>, \<^verbatim>\<open>cslt\<close>, \<^verbatim>\<open>csle\<close>.\<close>
definition one_t :: \<open>nat \<Rightarrow> CoreTerm\<close> where
  \<open>one_t w \<equiv> CoreTerm_Bin BinOp_Concat (CoreTerm_Const (replicate (w - 1) False)) (CoreTerm_Const [True])\<close>

definition neg_t :: \<open>nat \<Rightarrow> nat \<Rightarrow> CoreTerm\<close> where
  \<open>neg_t k w \<equiv> CoreTerm_Bin BinOp_Add (CoreTerm_Not (cr k)) (one_t w)\<close>

definition msb_t :: \<open>nat \<Rightarrow> nat \<Rightarrow> CoreTerm\<close> where
  \<open>msb_t k w \<equiv> CoreTerm_Extract (word_of_nat (w - 1)) (word_of_nat (w - 1)) (cr k)\<close>

definition abs_t :: \<open>nat \<Rightarrow> nat \<Rightarrow> CoreTerm\<close> where
  \<open>abs_t k w \<equiv> CoreTerm_Ite (msb_t k w) (neg_t k w) (cr k)\<close>

definition slt_t :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> CoreTerm\<close> where
  \<open>slt_t ka kb w \<equiv>
     CoreTerm_Bin BinOp_Or
       (CoreTerm_Bin BinOp_And (msb_t ka w) (CoreTerm_Not (msb_t kb w)))
       (CoreTerm_Bin BinOp_And (CoreTerm_Not (CoreTerm_Bin BinOp_Xor (msb_t ka w) (msb_t kb w)))
          (CoreTerm_Bin BinOp_Ult (cr ka) (cr kb)))\<close>

definition sle_t :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> CoreTerm\<close> where
  \<open>sle_t ka kb w \<equiv>
     CoreTerm_Bin BinOp_Or
       (CoreTerm_Bin BinOp_And (msb_t ka w) (CoreTerm_Not (msb_t kb w)))
       (CoreTerm_Bin BinOp_And (CoreTerm_Not (CoreTerm_Bin BinOp_Xor (msb_t ka w) (msb_t kb w)))
          (CoreTerm_Not (CoreTerm_Bin BinOp_Ult (cr kb) (cr ka))))\<close>

text \<open>\<^verbatim>\<open>lower_bin\<close>.\<close>
definition lower_bin_m :: \<open>lst \<Rightarrow> Op \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> lst \<times> nat\<close> where
  \<open>lower_bin_m L op ka kb \<equiv>
     let w = snd L ! ka in
     case op of
       Op_And \<Rightarrow> push_m L (CoreTerm_Bin BinOp_And (cr ka) (cr kb)) w
     | Op_Or \<Rightarrow> push_m L (CoreTerm_Bin BinOp_Or (cr ka) (cr kb)) w
     | Op_Xor \<Rightarrow> push_m L (CoreTerm_Bin BinOp_Xor (cr ka) (cr kb)) w
     | Op_Nand \<Rightarrow> push_m L (CoreTerm_Not (CoreTerm_Bin BinOp_And (cr ka) (cr kb))) w
     | Op_Nor \<Rightarrow> push_m L (CoreTerm_Not (CoreTerm_Bin BinOp_Or (cr ka) (cr kb))) w
     | Op_Xnor \<Rightarrow> push_m L (CoreTerm_Not (CoreTerm_Bin BinOp_Xor (cr ka) (cr kb))) w
     | Op_Comp \<Rightarrow> push_m L (CoreTerm_Bin BinOp_Eq (cr ka) (cr kb)) 1
     | Op_Add \<Rightarrow> push_m L (CoreTerm_Bin BinOp_Add (cr ka) (cr kb)) w
     | Op_Sub \<Rightarrow> push_m L (CoreTerm_Bin BinOp_Add (cr ka) (neg_t kb w)) w
     | Op_Mul \<Rightarrow> push_m L (CoreTerm_Bin BinOp_Mul (cr ka) (cr kb)) w
     | Op_Udiv \<Rightarrow> push_m L (CoreTerm_Bin BinOp_Udiv (cr ka) (cr kb)) w
     | Op_Urem \<Rightarrow> push_m L (CoreTerm_Bin BinOp_Urem (cr ka) (cr kb)) w
     | Op_Sdiv \<Rightarrow>
         (let (L1, q) = push_m L (CoreTerm_Bin BinOp_Udiv (abs_t ka w) (abs_t kb w)) w in
          push_m L1 (CoreTerm_Ite (CoreTerm_Bin BinOp_Xor (msb_t ka w) (msb_t kb w)) (neg_t q w) (cr q)) w)
     | Op_Srem \<Rightarrow>
         (let (L1, r) = push_m L (CoreTerm_Bin BinOp_Urem (abs_t ka w) (abs_t kb w)) w in
          push_m L1 (CoreTerm_Ite (msb_t ka w) (neg_t r w) (cr r)) w)
     | Op_Smod \<Rightarrow>
         (let (L1, u) = push_m L (CoreTerm_Bin BinOp_Urem (abs_t ka w) (abs_t kb w)) w in
          let (L2, nu) = push_m L1 (neg_t u w) w in
          let zero = CoreTerm_Bin BinOp_Eq (cr u) (CoreTerm_Const (replicate w False)) in
          let neg_a = CoreTerm_Ite (msb_t kb w) (cr nu) (CoreTerm_Bin BinOp_Add (cr nu) (cr kb)) in
          let pos_a = CoreTerm_Ite (msb_t kb w) (CoreTerm_Bin BinOp_Add (cr u) (cr kb)) (cr u) in
          push_m L2 (CoreTerm_Ite zero (cr u) (CoreTerm_Ite (msb_t ka w) neg_a pos_a)) w)
     | Op_Shl \<Rightarrow> push_m L (CoreTerm_Bin BinOp_Shl (cr ka) (cr kb)) w
     | Op_Lshr \<Rightarrow> push_m L (CoreTerm_Bin BinOp_Lshr (cr ka) (cr kb)) w
     | Op_Ashr \<Rightarrow>
         push_m L (CoreTerm_Ite (msb_t ka w)
                     (CoreTerm_Not (CoreTerm_Bin BinOp_Lshr (CoreTerm_Not (cr ka)) (cr kb)))
                     (CoreTerm_Bin BinOp_Lshr (cr ka) (cr kb))) w
     | Op_Concat \<Rightarrow> push_m L (CoreTerm_Bin BinOp_Concat (cr ka) (cr kb)) (w + snd L ! kb)
     | Op_Eq \<Rightarrow> push_m L (CoreTerm_Bin BinOp_Eq (cr ka) (cr kb)) 1
     | Op_Distinct \<Rightarrow> push_m L (CoreTerm_Not (CoreTerm_Bin BinOp_Eq (cr ka) (cr kb))) 1
     | Op_Ult \<Rightarrow> push_m L (CoreTerm_Bin BinOp_Ult (cr ka) (cr kb)) 1
     | Op_Ule \<Rightarrow> push_m L (CoreTerm_Not (CoreTerm_Bin BinOp_Ult (cr kb) (cr ka))) 1
     | Op_Ugt \<Rightarrow> push_m L (CoreTerm_Bin BinOp_Ult (cr kb) (cr ka)) 1
     | Op_Uge \<Rightarrow> push_m L (CoreTerm_Not (CoreTerm_Bin BinOp_Ult (cr ka) (cr kb))) 1
     | Op_Slt \<Rightarrow> push_m L (slt_t ka kb w) 1
     | Op_Sle \<Rightarrow> push_m L (sle_t ka kb w) 1
     | Op_Sgt \<Rightarrow> push_m L (slt_t kb ka w) 1
     | Op_Sge \<Rightarrow> push_m L (sle_t kb ka w) 1\<close>

text \<open>One iteration of the loop of \<^verbatim>\<open>lower\<close> for \<open>repeat\<close>: the state is the definitions, the
  definition of the copies so far and their width.\<close>
definition repeat_step :: \<open>nat \<Rightarrow> nat \<Rightarrow> lst \<times> nat \<times> nat \<Rightarrow> nat \<Rightarrow> lst \<times> nat \<times> nat\<close> where
  \<open>repeat_step ka w \<equiv> \<lambda>(L, k, acc) j.
     let (L1, k1) = push_m L (CoreTerm_Bin BinOp_Concat (cr ka) (cr k)) (acc + w) in (L1, k1, acc + w)\<close>

text \<open>\<^verbatim>\<open>lower\<close>.\<close>
primrec lower_m :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> lst \<Rightarrow> Term \<Rightarrow> lst \<times> nat\<close> where
  \<open>lower_m ws dm L (Term_Const bs) = push_m L (CoreTerm_Const bs) (length bs)\<close>
| \<open>lower_m ws dm L (Term_Var i) = push_m L (CoreTerm_Var i) (ws ! unat i)\<close>
| \<open>lower_m ws dm L (Term_Ref j) = (L, dm ! unat j)\<close>
| \<open>lower_m ws dm L (Term_Not a) =
     (let (L1, ka) = lower_m ws dm L a in push_m L1 (CoreTerm_Not (cr ka)) (snd L1 ! ka))\<close>
| \<open>lower_m ws dm L (Term_Neg a) =
     (let (L1, ka) = lower_m ws dm L a in push_m L1 (neg_t ka (snd L1 ! ka)) (snd L1 ! ka))\<close>
| \<open>lower_m ws dm L (Term_Bin op a b) =
     (let (L1, ka) = lower_m ws dm L a in
      let (L2, kb) = lower_m ws dm L1 b in
      lower_bin_m L2 op ka kb)\<close>
| \<open>lower_m ws dm L (Term_Extract hi lo a) =
     (let (L1, ka) = lower_m ws dm L a in
      push_m L1 (CoreTerm_Extract hi lo (cr ka)) (unat hi - unat lo + 1))\<close>
| \<open>lower_m ws dm L (Term_Repeat i a) =
     (let (L1, ka) = lower_m ws dm L a in
      let w = snd L1 ! ka in
      let (L2, k0) = push_m L1 (CoreTerm_Const []) 0 in
      let (L3, k3, acc) = foldl (repeat_step ka w) (L2, k0, 0) [0..<unat i] in
      (L3, k3))\<close>
| \<open>lower_m ws dm L (Term_ZeroExtend i a) =
     (let (L1, ka) = lower_m ws dm L a in
      let w = snd L1 ! ka in
      push_m L1 (CoreTerm_Bin BinOp_Concat (CoreTerm_Const (replicate (unat i) False)) (cr ka)) (w + unat i))\<close>
| \<open>lower_m ws dm L (Term_SignExtend i a) =
     (let (L1, ka) = lower_m ws dm L a in
      let w = snd L1 ! ka in
      push_m L1 (CoreTerm_Bin BinOp_Concat
                   (CoreTerm_Ite (msb_t ka w) (CoreTerm_Const (replicate (unat i) True))
                      (CoreTerm_Const (replicate (unat i) False)))
                   (cr ka)) (w + unat i))\<close>
| \<open>lower_m ws dm L (Term_RotateLeft i a) =
     (let (L1, ka) = lower_m ws dm L a in
      let w = snd L1 ! ka in
      let r = unat i mod w in
      if r = 0 then (L1, ka)
      else push_m L1 (CoreTerm_Bin BinOp_Concat
                        (CoreTerm_Extract (word_of_nat (w - 1 - r)) 0 (cr ka))
                        (CoreTerm_Extract (word_of_nat (w - 1)) (word_of_nat (w - r)) (cr ka))) w)\<close>
| \<open>lower_m ws dm L (Term_RotateRight i a) =
     (let (L1, ka) = lower_m ws dm L a in
      let w = snd L1 ! ka in
      let r = unat i mod w in
      if r = 0 then (L1, ka)
      else push_m L1 (CoreTerm_Bin BinOp_Concat
                        (CoreTerm_Extract (word_of_nat (r - 1)) 0 (cr ka))
                        (CoreTerm_Extract (word_of_nat (w - 1)) (word_of_nat r) (cr ka))) w)\<close>
| \<open>lower_m ws dm L (Term_Ite c a b) =
     (let (L1, kc) = lower_m ws dm L c in
      let (L2, ka) = lower_m ws dm L1 a in
      let (L3, kb) = lower_m ws dm L2 b in
      push_m L3 (CoreTerm_Ite (cr kc) (cr ka) (cr kb)) (snd L3 ! ka))\<close>

text \<open>The two loops of \<^verbatim>\<open>lower_problem\<close>: rewrite the definitions, recording the core definition of
  each; rewrite the assertions into references.\<close>
definition ldefs_step :: \<open>Problem \<Rightarrow> lst \<times> nat list \<Rightarrow> nat \<Rightarrow> lst \<times> nat list\<close> where
  \<open>ldefs_step p \<equiv> \<lambda>(L, dm) j.
     let (L1, k) = lower_m (var_widths p) dm L (Problem_defs p ! j) in (L1, dm @ [k])\<close>

definition lasserts_step :: \<open>Problem \<Rightarrow> nat list \<Rightarrow> lst \<times> CoreTerm list \<Rightarrow> nat \<Rightarrow> lst \<times> CoreTerm list\<close> where
  \<open>lasserts_step p dm \<equiv> \<lambda>(L, cs) i.
     let (L1, k) = lower_m (var_widths p) dm L (Problem_asserts p ! i) in (L1, cs @ [cr k])\<close>

definition lower_problem_m :: \<open>Problem \<Rightarrow> CoreProblem\<close> where
  \<open>lower_problem_m p \<equiv>
     let (L1, dm) = foldl (ldefs_step p) (([], []), []) [0..<length (Problem_defs p)] in
     let (L2, cs) = foldl (lasserts_step p dm) (L1, []) [0..<length (Problem_asserts p)] in
     make_CoreProblem (Problem_widths p) (fst L2) cs\<close>

subsection \<open>Values of core terms are bounded by their widths\<close>

lemma bits_nat_lt: \<open>bits_nat bs < 2 ^ length bs\<close>
  by (induction bs) auto

lemma take_bit_eq_self_nat: \<open>x < 2 ^ w \<Longrightarrow> take_bit w (x :: nat) = x\<close>
  by (simp add: take_bit_nat_eq_self_iff)

lemma and_lt_pow: \<open>x < 2 ^ w \<Longrightarrow> y < 2 ^ w \<Longrightarrow> Bit_Operations.and (x :: nat) y < 2 ^ w\<close>
proof -
  assume \<open>x < 2 ^ w\<close> \<open>y < 2 ^ w\<close>
  then have \<open>Bit_Operations.and x y = take_bit w (Bit_Operations.and x y)\<close>
    by (simp add: take_bit_and take_bit_eq_self_nat)
  then show ?thesis using take_bit_nat_less_exp[of w \<open>Bit_Operations.and x y\<close>] by simp
qed

lemma or_lt_pow: \<open>x < 2 ^ w \<Longrightarrow> y < 2 ^ w \<Longrightarrow> Bit_Operations.or (x :: nat) y < 2 ^ w\<close>
proof -
  assume \<open>x < 2 ^ w\<close> \<open>y < 2 ^ w\<close>
  then have \<open>Bit_Operations.or x y = take_bit w (Bit_Operations.or x y)\<close>
    by (simp add: take_bit_or take_bit_eq_self_nat)
  then show ?thesis using take_bit_nat_less_exp[of w \<open>Bit_Operations.or x y\<close>] by simp
qed

lemma xor_lt_pow: \<open>x < 2 ^ w \<Longrightarrow> y < 2 ^ w \<Longrightarrow> Bit_Operations.xor (x :: nat) y < 2 ^ w\<close>
proof -
  assume \<open>x < 2 ^ w\<close> \<open>y < 2 ^ w\<close>
  then have \<open>Bit_Operations.xor x y = take_bit w (Bit_Operations.xor x y)\<close>
    by (simp add: take_bit_xor take_bit_eq_self_nat)
  then show ?thesis using take_bit_nat_less_exp[of w \<open>Bit_Operations.xor x y\<close>] by simp
qed

lemma concat_lt_pow: \<open>(x :: nat) < 2 ^ w \<Longrightarrow> y < 2 ^ v \<Longrightarrow> x * 2 ^ v + y < 2 ^ (w + v)\<close>
proof -
  assume \<open>x < 2 ^ w\<close> \<open>y < 2 ^ v\<close>
  have \<open>x + 1 \<le> 2 ^ w\<close> using \<open>x < 2 ^ w\<close> by linarith
  then have \<open>(x + 1) * 2 ^ v \<le> 2 ^ w * 2 ^ v\<close> by (rule mult_le_mono1)
  then have \<open>x * 2 ^ v + 2 ^ v \<le> 2 ^ (w + v)\<close> by (simp add: power_add)
  then show ?thesis using \<open>y < 2 ^ v\<close> by linarith
qed

lemma cbin_sem_lt:
  assumes \<open>x < 2 ^ w\<close> \<open>y < 2 ^ v\<close> \<open>op \<noteq> BinOp_Concat \<longrightarrow> v = w\<close>
  shows \<open>cbin_sem op w x v y <
     2 ^ (case op of BinOp_Concat \<Rightarrow> w + v | BinOp_Eq \<Rightarrow> 1 | BinOp_Ult \<Rightarrow> 1 | _ \<Rightarrow> w)\<close>
  using assms
proof (cases op)
  case BinOp_And then show ?thesis using assms by (simp add: and_lt_pow)
next
  case BinOp_Or then show ?thesis using assms by (simp add: or_lt_pow)
next
  case BinOp_Xor then show ?thesis using assms by (simp add: xor_lt_pow)
next
  case BinOp_Udiv
  then show ?thesis using assms by (auto intro: le_less_trans[OF div_le_dividend])
next
  case BinOp_Urem
  then show ?thesis using assms by (auto intro: le_less_trans[OF mod_le_divisor])
next
  case BinOp_Lshr
  then show ?thesis using assms by (auto intro: le_less_trans[OF div_le_dividend])
next
  case BinOp_Concat then show ?thesis using assms by (simp add: concat_lt_pow)
qed simp_all

lemma ceval_lt:
  assumes \<open>cwt ws ds t\<close> \<open>\<forall>i < length ws. vs ! i < 2 ^ (ws ! i)\<close> \<open>\<forall>j < length ds. dv ! j < 2 ^ (ds ! j)\<close>
  shows \<open>ceval ws ds vs dv t < 2 ^ cwidth ws ds t\<close>
  using assms(1)
proof (induction t)
  case (CoreTerm_Const bs)
  then show ?case by (simp add: bits_nat_lt)
next
  case (CoreTerm_Var i)
  then show ?case using assms(2) by simp
next
  case (CoreTerm_Ref j)
  then show ?case using assms(3) by simp
next
  case (CoreTerm_Not a)
  then show ?case by simp
next
  case (CoreTerm_Bin op a b)
  then have \<open>ceval ws ds vs dv a < 2 ^ cwidth ws ds a\<close> \<open>ceval ws ds vs dv b < 2 ^ cwidth ws ds b\<close>
    \<open>op \<noteq> BinOp_Concat \<longrightarrow> cwidth ws ds b = cwidth ws ds a\<close> by simp_all
  then have \<open>cbin_sem op (cwidth ws ds a) (ceval ws ds vs dv a) (cwidth ws ds b) (ceval ws ds vs dv b)
      < 2 ^ (case op of BinOp_Concat \<Rightarrow> cwidth ws ds a + cwidth ws ds b | BinOp_Eq \<Rightarrow> 1 | BinOp_Ult \<Rightarrow> 1
             | _ \<Rightarrow> cwidth ws ds a)\<close>
    by (rule cbin_sem_lt)
  then show ?case by simp
next
  case (CoreTerm_Extract hi lo a)
  then show ?case by simp
next
  case (CoreTerm_Ite c a b)
  then show ?case by simp
qed

subsection \<open>The invariant of the rewriting\<close>

text \<open>The widths of the core definitions, and their values under the values \<open>vs\<close> of the variables.\<close>
abbreviation CW :: \<open>nat list \<Rightarrow> lst \<Rightarrow> nat list\<close> where
  \<open>CW ws L \<equiv> cdef_widths ws [] (fst L)\<close>

abbreviation CV :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> lst \<Rightarrow> nat list\<close> where
  \<open>CV ws vs L \<equiv> cdef_values ws [] vs [] (fst L)\<close>

text \<open>A state is well-formed: its definitions are well-sorted and its widths are theirs.\<close>
definition lok :: \<open>nat list \<Rightarrow> lst \<Rightarrow> bool\<close> where
  \<open>lok ws L \<equiv> cdefs_wt ws [] (fst L) \<and> snd L = CW ws L\<close>

text \<open>The values of the variables are bounded by their widths.\<close>
definition vs_ok :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> bool\<close> where
  \<open>vs_ok ws vs \<equiv> length vs = length ws \<and> (\<forall>i < length ws. vs ! i < 2 ^ (ws ! i))\<close>

lemma cdef_widths_append: \<open>cdef_widths ws ds (xs @ ys) = cdef_widths ws (cdef_widths ws ds xs) ys\<close>
  by (induction xs arbitrary: ds) simp_all

lemma cdef_values_append:
  \<open>cdef_values ws ds vs dv (xs @ ys) = cdef_values ws (cdef_widths ws ds xs) vs (cdef_values ws ds vs dv xs) ys\<close>
  by (induction xs arbitrary: ds dv) simp_all

lemma cdefs_wt_append: \<open>cdefs_wt ws ds (xs @ ys) = (cdefs_wt ws ds xs \<and> cdefs_wt ws (cdef_widths ws ds xs) ys)\<close>
  by (induction xs arbitrary: ds) simp_all

lemma cdef_widths_prefix: \<open>\<exists>e. cdef_widths ws ds xs = ds @ e\<close>
proof (induction xs arbitrary: ds)
  case Nil
  show ?case by simp
next
  case (Cons d dd)
  obtain e where \<open>cdef_widths ws (ds @ [cwidth ws ds d]) dd = (ds @ [cwidth ws ds d]) @ e\<close>
    using Cons.IH by blast
  then show ?case by simp
qed

lemma cdef_values_prefix: \<open>\<exists>e. cdef_values ws ds vs dv xs = dv @ e\<close>
proof (induction xs arbitrary: ds dv)
  case Nil
  show ?case by simp
next
  case (Cons d dd)
  obtain e where \<open>cdef_values ws (ds @ [cwidth ws ds d]) vs (dv @ [ceval ws ds vs dv d]) dd =
      (dv @ [ceval ws ds vs dv d]) @ e\<close>
    using Cons.IH by blast
  then show ?case by simp
qed

lemma cdef_widths_length: \<open>length (cdef_widths ws ds xs) = length ds + length xs\<close>
  by (induction xs arbitrary: ds) simp_all

lemma cdef_values_length: \<open>length (cdef_values ws ds vs dv xs) = length dv + length xs\<close>
  by (induction xs arbitrary: ds dv) simp_all

lemma cdef_values_lt:
  assumes \<open>cdefs_wt ws ds xs\<close> \<open>vs_ok ws vs\<close> \<open>length dv = length ds\<close> \<open>\<forall>j < length ds. dv ! j < 2 ^ (ds ! j)\<close>
  shows \<open>\<forall>j < length ds + length xs. cdef_values ws ds vs dv xs ! j < 2 ^ (cdef_widths ws ds xs ! j)\<close>
  using assms
proof (induction xs arbitrary: ds dv)
  case Nil
  then show ?case by simp
next
  case (Cons d dd)
  have \<open>ceval ws ds vs dv d < 2 ^ cwidth ws ds d\<close>
    using Cons.prems by (intro ceval_lt) (simp_all add: vs_ok_def)
  then have \<open>\<forall>j < length (ds @ [cwidth ws ds d]). (dv @ [ceval ws ds vs dv d]) ! j < 2 ^ ((ds @ [cwidth ws ds d]) ! j)\<close>
    using Cons.prems(3,4) by (auto simp add: nth_append)
  then show ?case
    using Cons.IH[of \<open>ds @ [cwidth ws ds d]\<close> \<open>dv @ [ceval ws ds vs dv d]\<close>] Cons.prems by simp
qed

text \<open>Facts about a well-formed state.\<close>
lemma lok_length: \<open>lok ws L \<Longrightarrow> length (snd L) = length (fst L)\<close>
  by (simp add: lok_def cdef_widths_length)

lemma lok_CV_length: \<open>length (CV ws vs L) = length (fst L)\<close>
  by (simp add: cdef_values_length)

lemma lok_CV_lt: \<open>lok ws L \<Longrightarrow> vs_ok ws vs \<Longrightarrow> k < length (fst L) \<Longrightarrow> CV ws vs L ! k < 2 ^ (snd L ! k)\<close>
  using cdef_values_lt[of ws \<open>[]\<close> \<open>fst L\<close> vs \<open>[]\<close>] by (simp add: lok_def)

text \<open>Pushing a well-sorted core term keeps the state well-formed; the new definition has the
  term's width and value.\<close>
lemma push_ok:
  assumes \<open>lok ws L\<close> \<open>cwt ws (snd L) t\<close> \<open>cwidth ws (snd L) t = w\<close> \<open>push_m L t w = (L', k)\<close>
  shows \<open>lok ws L'\<close> \<open>fst L' = fst L @ [t]\<close> \<open>snd L' = snd L @ [w]\<close> \<open>k = length (fst L)\<close>
    \<open>CV ws vs L' = CV ws vs L @ [ceval ws (snd L) vs (CV ws vs L) t]\<close>
proof -
  have Lk: \<open>L' = (fst L @ [t], snd L @ [w])\<close> \<open>k = length (fst L)\<close>
    using assms(4) by (simp_all add: push_m_def)
  show \<open>lok ws L'\<close>
    using assms(1-3) by (simp add: Lk lok_def cdef_widths_append cdefs_wt_append)
  show \<open>fst L' = fst L @ [t]\<close> \<open>snd L' = snd L @ [w]\<close> \<open>k = length (fst L)\<close>
    by (simp_all add: Lk)
  show \<open>CV ws vs L' = CV ws vs L @ [ceval ws (snd L) vs (CV ws vs L) t]\<close>
    using assms(1) by (simp add: Lk lok_def cdef_values_append)
qed

text \<open>An extension of a state: the definitions, widths and values of the old state are prefixes.\<close>
definition lext :: \<open>nat list \<Rightarrow> lst \<Rightarrow> lst \<Rightarrow> bool\<close> where
  \<open>lext ws L L' \<equiv> lok ws L' \<and> (\<exists>e. fst L' = fst L @ e)\<close>

lemma lext_refl: \<open>lok ws L \<Longrightarrow> lext ws L L\<close>
  by (simp add: lext_def)

lemma lext_trans: \<open>lext ws L L1 \<Longrightarrow> lext ws L1 L2 \<Longrightarrow> lext ws L L2\<close>
  by (auto simp add: lext_def)

lemma lext_push: \<open>lok ws L \<Longrightarrow> cwt ws (snd L) t \<Longrightarrow> cwidth ws (snd L) t = w \<Longrightarrow> push_m L t w = (L', k) \<Longrightarrow> lext ws L L'\<close>
  using push_ok(1,2)[of ws L t w L' k] by (auto simp add: lext_def)

lemma lext_lok: \<open>lext ws L L' \<Longrightarrow> lok ws L'\<close>
  by (simp add: lext_def)

lemma lext_snd: \<open>lok ws L \<Longrightarrow> lext ws L L' \<Longrightarrow> \<exists>e. snd L' = snd L @ e\<close>
  using cdef_widths_prefix by (auto simp add: lext_def lok_def cdef_widths_append)

lemma lext_CV: \<open>lext ws L L' \<Longrightarrow> \<exists>e. CV ws vs L' = CV ws vs L @ e\<close>
  using cdef_values_prefix by (auto simp add: lext_def cdef_values_append)

lemma lext_nth_snd: \<open>lok ws L \<Longrightarrow> lext ws L L' \<Longrightarrow> k < length (fst L) \<Longrightarrow> snd L' ! k = snd L ! k\<close>
  using lext_snd[of ws L L'] lok_length[of ws L] by (auto simp add: nth_append)

lemma lext_nth_CV: \<open>lext ws L L' \<Longrightarrow> k < length (fst L) \<Longrightarrow> CV ws vs L' ! k = CV ws vs L ! k\<close>
  using lext_CV[of ws L L' vs] by (auto simp add: nth_append lok_CV_length)

lemma lext_length: \<open>lext ws L L' \<Longrightarrow> length (fst L) \<le> length (fst L')\<close>
  by (auto simp add: lext_def)

subsection \<open>Two's complement arithmetic\<close>

text \<open>The sign bit of a value of width \<open>w \<ge> 1\<close>, and its magnitude.\<close>
definition sbit :: \<open>nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>sbit w x \<equiv> 2 ^ (w - 1) \<le> x\<close>

definition absv :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>absv w x \<equiv> if sbit w x then 2 ^ w - x else x\<close>

lemma pow_w_split: \<open>1 \<le> w \<Longrightarrow> (2 :: nat) ^ w = 2 * 2 ^ (w - 1)\<close>
  by (cases w) simp_all

lemma pow_w_split_int: \<open>1 \<le> w \<Longrightarrow> (2 :: int) ^ w = 2 * 2 ^ (w - 1)\<close>
  by (cases w) simp_all

lemma sint_cases: \<open>sint w x = (if sbit w x then int x - 2 ^ w else int x)\<close>
  by (simp add: sint_def sbit_def)

lemma sint_neg_iff: \<open>1 \<le> w \<Longrightarrow> x < 2 ^ w \<Longrightarrow> (sint w x < 0) = sbit w x\<close>
  by (simp add: sint_cases)

lemma sint_nonneg_iff: \<open>1 \<le> w \<Longrightarrow> x < 2 ^ w \<Longrightarrow> (0 \<le> sint w x) = (\<not> sbit w x)\<close>
  by (simp add: sint_cases)

lemma abs_sint: \<open>1 \<le> w \<Longrightarrow> x < 2 ^ w \<Longrightarrow> \<bar>sint w x\<bar> = int (absv w x)\<close>
  by (simp add: sint_cases absv_def)

lemma absv_lt: \<open>1 \<le> w \<Longrightarrow> x < 2 ^ w \<Longrightarrow> absv w x < 2 ^ w\<close>
  by (simp add: absv_def sbit_def pow_w_split)

lemma absv_le_half: \<open>1 \<le> w \<Longrightarrow> x < 2 ^ w \<Longrightarrow> absv w x \<le> 2 ^ (w - 1)\<close>
  unfolding absv_def sbit_def using pow_w_split[of w] by (cases \<open>2 ^ (w - 1) \<le> x\<close>) simp_all

lemma absv_0_iff: \<open>1 \<le> w \<Longrightarrow> x < 2 ^ w \<Longrightarrow> (absv w x = 0) = (x = 0)\<close>
  by (simp add: absv_def sbit_def pow_w_split)

lemma int_lt_pow: \<open>x < 2 ^ w \<Longrightarrow> int x < 2 ^ w\<close>
  by simp

lemma sint_lt_iff:
  \<open>1 \<le> w \<Longrightarrow> x < 2 ^ w \<Longrightarrow> y < 2 ^ w \<Longrightarrow>
   (sint w x < sint w y) = ((sbit w x \<and> \<not> sbit w y) \<or> (sbit w x = sbit w y \<and> x < y))\<close>
proof -
  assume \<open>1 \<le> w\<close> \<open>x < 2 ^ w\<close> \<open>y < 2 ^ w\<close>
  then have \<open>int x - 2 ^ w < int y\<close> \<open>\<not> int x < int y - 2 ^ w\<close>
    using int_lt_pow[of x w] int_lt_pow[of y w] by linarith+
  then show ?thesis by (auto simp add: sint_cases)
qed

lemma sint_le_iff:
  \<open>1 \<le> w \<Longrightarrow> x < 2 ^ w \<Longrightarrow> y < 2 ^ w \<Longrightarrow>
   (sint w x \<le> sint w y) = ((sbit w x \<and> \<not> sbit w y) \<or> (sbit w x = sbit w y \<and> x \<le> y))\<close>
proof -
  assume \<open>1 \<le> w\<close> \<open>x < 2 ^ w\<close> \<open>y < 2 ^ w\<close>
  then have \<open>int x - 2 ^ w \<le> int y\<close> \<open>\<not> int x \<le> int y - 2 ^ w\<close>
    using int_lt_pow[of x w] int_lt_pow[of y w] by linarith+
  then show ?thesis by (auto simp add: sint_cases)
qed

text \<open>The value of a width-\<open>w\<close> negation.\<close>
definition negv :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>negv w x \<equiv> (2 ^ w - x) mod 2 ^ w\<close>

lemma negv_lt: \<open>negv w x < 2 ^ w\<close>
  by (simp add: negv_def)

lemma negv_0 [simp]: \<open>negv w 0 = 0\<close>
  by (simp add: negv_def)

lemma negv_pos: \<open>0 < x \<Longrightarrow> x < 2 ^ w \<Longrightarrow> negv w x = 2 ^ w - x\<close>
  by (simp add: negv_def)

lemma to_bv_nat: \<open>v < 2 ^ w \<Longrightarrow> to_bv w (int v) = v\<close>
  by (simp add: to_bv_def nat_mod_as_int)

lemma nat_pow_diff: \<open>v < 2 ^ w \<Longrightarrow> nat (2 ^ w - int v) = 2 ^ w - v\<close>
proof -
  assume \<open>v < 2 ^ w\<close>
  then have \<open>(2 :: int) ^ w - int v = int (2 ^ w - v)\<close> by (simp add: of_nat_diff)
  then show ?thesis by simp
qed

lemma to_bv_neg: \<open>v < 2 ^ w \<Longrightarrow> to_bv w (- int v) = negv w v\<close>
  by (cases \<open>v = 0\<close>) (simp_all add: to_bv_def negv_pos zmod_zminus1_eq_if nat_mod_as_int nat_pow_diff)

lemma absv_sbit: \<open>1 \<le> w \<Longrightarrow> x < 2 ^ w \<Longrightarrow> absv w x = (if sbit w x then negv w x else x)\<close>
proof -
  assume \<open>1 \<le> w\<close> \<open>x < 2 ^ w\<close>
  have \<open>0 < (2 :: nat) ^ (w - 1)\<close> by simp
  then have \<open>sbit w x \<Longrightarrow> 0 < x\<close> unfolding sbit_def by linarith
  then show ?thesis using \<open>x < 2 ^ w\<close> by (simp add: absv_def negv_pos)
qed

lemma negv_negv: \<open>x < 2 ^ w \<Longrightarrow> negv w (negv w x) = x\<close>
  by (cases \<open>x = 0\<close>) (simp_all add: negv_pos)

lemma sint_absv_sbit:
  \<open>1 \<le> w \<Longrightarrow> x < 2 ^ w \<Longrightarrow> sint w x = (if sbit w x then - int (absv w x) else int (absv w x))\<close>
  by (simp add: sint_cases absv_def)

subsection \<open>The semantics of the built core terms\<close>

text \<open>The core definition \<open>k\<close> has width \<open>w\<close> and value \<open>x\<close> in the environment \<open>cws\<close>, \<open>cdv\<close>.\<close>
definition ref_ok :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>ref_ok cws cdv k w x \<equiv> k < length cws \<and> k < 2 ^ 64 \<and> cws ! k = w \<and> cdv ! k = x \<and> x < 2 ^ w\<close>

lemma unat_wn: \<open>k < 2 ^ 64 \<Longrightarrow> unat (word_of_nat k :: 64 word) = k\<close>
  by (simp add: unat_of_nat_eq)

lemma cr_sem:
  assumes \<open>ref_ok cws cdv k w x\<close>
  shows \<open>cwt ws cws (cr k)\<close> \<open>cwidth ws cws (cr k) = w\<close> \<open>ceval ws cws vs cdv (cr k) = x\<close>
  using assms by (simp_all add: ref_ok_def cr_def unat_wn)

lemma bits_nat_replicate_False: \<open>bits_nat (replicate n False) = 0\<close>
  by (induction n) simp_all

lemma bits_nat_replicate_True: \<open>bits_nat (replicate n True) + 1 = 2 ^ n\<close>
  by (induction n) simp_all

lemma one_t_sem:
  assumes \<open>1 \<le> w\<close>
  shows \<open>cwt ws cws (one_t w)\<close> \<open>cwidth ws cws (one_t w) = w\<close> \<open>ceval ws cws vs cdv (one_t w) = 1\<close>
  using assms by (simp_all add: one_t_def bits_nat_replicate_False)

lemma neg_t_sem:
  assumes \<open>ref_ok cws cdv k w x\<close> \<open>1 \<le> w\<close>
  shows \<open>cwt ws cws (neg_t k w)\<close> \<open>cwidth ws cws (neg_t k w) = w\<close>
    \<open>ceval ws cws vs cdv (neg_t k w) = negv w x\<close>
proof -
  have x: \<open>x < 2 ^ w\<close> using assms(1) by (simp add: ref_ok_def)
  show \<open>cwt ws cws (neg_t k w)\<close> \<open>cwidth ws cws (neg_t k w) = w\<close>
    using cr_sem[OF assms(1)] one_t_sem[OF assms(2)] by (simp_all add: neg_t_def)
  have \<open>2 ^ w - 1 - x + 1 = 2 ^ w - x\<close> using x by simp
  then show \<open>ceval ws cws vs cdv (neg_t k w) = negv w x\<close>
    using cr_sem[OF assms(1)] one_t_sem[OF assms(2)] by (simp add: neg_t_def negv_def)
qed

lemma div_pow_sbit: \<open>1 \<le> w \<Longrightarrow> x < 2 ^ w \<Longrightarrow> x div 2 ^ (w - 1) = of_bool (sbit w x)\<close>
proof -
  assume \<open>1 \<le> w\<close> \<open>x < 2 ^ w\<close>
  then have \<open>x < 2 * 2 ^ (w - 1)\<close> by (simp add: pow_w_split)
  then have \<open>x div 2 ^ (w - 1) < 2\<close> by (simp add: less_mult_imp_div_less)
  moreover have \<open>(x div 2 ^ (w - 1) = 0) = (x < 2 ^ (w - 1))\<close> by (simp add: div_eq_0_iff)
  ultimately show ?thesis by (auto simp add: sbit_def)
qed

lemma msb_t_sem:
  assumes \<open>ref_ok cws cdv k w x\<close> \<open>1 \<le> w\<close> \<open>w < 2 ^ 64\<close>
  shows \<open>cwt ws cws (msb_t k w)\<close> \<open>cwidth ws cws (msb_t k w) = 1\<close>
    \<open>ceval ws cws vs cdv (msb_t k w) = of_bool (sbit w x)\<close>
proof -
  have x: \<open>x < 2 ^ w\<close> using assms(1) by (simp add: ref_ok_def)
  have u: \<open>unat (word_of_nat (w - 1) :: 64 word) = w - 1\<close> using assms(3) by (simp add: unat_wn)
  have u': \<open>unat (word_of_nat w - 1 :: 64 word) = w - 1\<close>
    using u assms(2) by (metis of_nat_1 of_nat_diff)
  have u'': \<open>unat (word_of_nat (w - Suc 0) :: 64 word) = w - Suc 0\<close> using u by simp
  have d: \<open>x div 2 ^ (w - 1) mod 2 = of_bool (sbit w x)\<close>
    using div_pow_sbit[OF assms(2) x] by simp
  show \<open>cwt ws cws (msb_t k w)\<close> \<open>cwidth ws cws (msb_t k w) = 1\<close>
    using cr_sem[OF assms(1)] assms(2) by (simp_all add: msb_t_def u u')
  show \<open>ceval ws cws vs cdv (msb_t k w) = of_bool (sbit w x)\<close>
    using cr_sem[OF assms(1)] d by (simp add: msb_t_def u u' u'')
qed

lemma abs_t_sem:
  assumes \<open>ref_ok cws cdv k w x\<close> \<open>1 \<le> w\<close> \<open>w < 2 ^ 64\<close>
  shows \<open>cwt ws cws (abs_t k w)\<close> \<open>cwidth ws cws (abs_t k w) = w\<close>
    \<open>ceval ws cws vs cdv (abs_t k w) = absv w x\<close>
proof -
  have x: \<open>x < 2 ^ w\<close> using assms(1) by (simp add: ref_ok_def)
  show \<open>cwt ws cws (abs_t k w)\<close> \<open>cwidth ws cws (abs_t k w) = w\<close>
    using cr_sem[OF assms(1)] msb_t_sem[OF assms] neg_t_sem[OF assms(1,2)] by (simp_all add: abs_t_def)
  show \<open>ceval ws cws vs cdv (abs_t k w) = absv w x\<close>
    using cr_sem[OF assms(1)] msb_t_sem[OF assms] neg_t_sem[OF assms(1,2)] absv_sbit[OF assms(2) x]
    by (simp add: abs_t_def)
qed

text \<open>The Boolean connectives on values 0 and 1.\<close>
lemma and_bool: \<open>Bit_Operations.and (of_bool a) (of_bool b) = (of_bool (a \<and> b) :: nat)\<close>
  by (cases a; cases b) simp_all

lemma or_bool: \<open>Bit_Operations.or (of_bool a) (of_bool b) = (of_bool (a \<or> b) :: nat)\<close>
  by (cases a; cases b) simp_all

lemma xor_bool: \<open>Bit_Operations.xor (of_bool a) (of_bool b) = (of_bool (a \<noteq> b) :: nat)\<close>
  by (cases a; cases b) simp_all

lemma not_bool: \<open>2 ^ 1 - 1 - of_bool a = (of_bool (\<not> a) :: nat)\<close>
  by (cases a) simp_all

lemma slt_t_sem:
  assumes \<open>ref_ok cws cdv ka w x\<close> \<open>ref_ok cws cdv kb w y\<close> \<open>1 \<le> w\<close> \<open>w < 2 ^ 64\<close>
  shows \<open>cwt ws cws (slt_t ka kb w)\<close> \<open>cwidth ws cws (slt_t ka kb w) = 1\<close>
    \<open>ceval ws cws vs cdv (slt_t ka kb w) = of_bool (sint w x < sint w y)\<close>
proof -
  have x: \<open>x < 2 ^ w\<close> \<open>y < 2 ^ w\<close> using assms(1,2) by (simp_all add: ref_ok_def)
  show \<open>cwt ws cws (slt_t ka kb w)\<close> \<open>cwidth ws cws (slt_t ka kb w) = 1\<close>
    using cr_sem[OF assms(1)] cr_sem[OF assms(2)] msb_t_sem[OF assms(1,3,4)] msb_t_sem[OF assms(2,3,4)]
    by (simp_all add: slt_t_def)
  show \<open>ceval ws cws vs cdv (slt_t ka kb w) = of_bool (sint w x < sint w y)\<close>
    using cr_sem[OF assms(1)] cr_sem[OF assms(2)] msb_t_sem[OF assms(1,3,4)] msb_t_sem[OF assms(2,3,4)]
    by (simp add: slt_t_def sint_lt_iff[OF assms(3) x] not_bool xor_bool and_bool or_bool)
qed

lemma sle_t_sem:
  assumes \<open>ref_ok cws cdv ka w x\<close> \<open>ref_ok cws cdv kb w y\<close> \<open>1 \<le> w\<close> \<open>w < 2 ^ 64\<close>
  shows \<open>cwt ws cws (sle_t ka kb w)\<close> \<open>cwidth ws cws (sle_t ka kb w) = 1\<close>
    \<open>ceval ws cws vs cdv (sle_t ka kb w) = of_bool (sint w x \<le> sint w y)\<close>
proof -
  have x: \<open>x < 2 ^ w\<close> \<open>y < 2 ^ w\<close> using assms(1,2) by (simp_all add: ref_ok_def)
  show \<open>cwt ws cws (sle_t ka kb w)\<close> \<open>cwidth ws cws (sle_t ka kb w) = 1\<close>
    using cr_sem[OF assms(1)] cr_sem[OF assms(2)] msb_t_sem[OF assms(1,3,4)] msb_t_sem[OF assms(2,3,4)]
    by (simp_all add: sle_t_def)
  have \<open>(2 ^ 1 - 1 - of_bool (y < x) :: nat) = of_bool (x \<le> y)\<close> by simp
  then show \<open>ceval ws cws vs cdv (sle_t ka kb w) = of_bool (sint w x \<le> sint w y)\<close>
    using cr_sem[OF assms(1)] cr_sem[OF assms(2)] msb_t_sem[OF assms(1,3,4)] msb_t_sem[OF assms(2,3,4)]
    by (simp add: sle_t_def sint_le_iff[OF assms(3) x] not_bool xor_bool and_bool or_bool)
qed

subsection \<open>The rewriting only appends definitions\<close>

text \<open>\<open>L'\<close> extends \<open>L\<close> as lists, whatever the well-formedness.\<close>
definition pfx :: \<open>lst \<Rightarrow> lst \<Rightarrow> bool\<close> where
  \<open>pfx L L' \<equiv> (\<exists>e. fst L' = fst L @ e) \<and> (\<exists>e. snd L' = snd L @ e)\<close>

lemma pfx_refl: \<open>pfx L L\<close>
  by (simp add: pfx_def)

lemma pfx_trans: \<open>pfx L L1 \<Longrightarrow> pfx L1 L2 \<Longrightarrow> pfx L L2\<close>
  by (auto simp add: pfx_def)

lemma pfx_push: \<open>push_m L t w = (L', k) \<Longrightarrow> pfx L L'\<close>
  by (auto simp add: pfx_def push_m_def)

lemma pfx_length: \<open>pfx L L' \<Longrightarrow> length (fst L) \<le> length (fst L') \<and> length (snd L) \<le> length (snd L')\<close>
  by (auto simp add: pfx_def)

lemma pfx_set: \<open>pfx L L' \<Longrightarrow> set (snd L) \<subseteq> set (snd L')\<close>
  by (auto simp add: pfx_def)

lemma pfx_nth: \<open>pfx L L' \<Longrightarrow> k < length (snd L) \<Longrightarrow> snd L' ! k = snd L ! k\<close>
  by (auto simp add: pfx_def nth_append)

lemma pfx_push_trans: \<open>pfx L L1 \<Longrightarrow> push_m L1 t w = (L', k) \<Longrightarrow> pfx L L'\<close>
  using pfx_push pfx_trans by blast

lemma lower_bin_m_pfx:
  assumes R: \<open>lower_bin_m L op ka kb = (L', k)\<close>
  shows \<open>pfx L L'\<close>
proof (cases op)
  case Op_Sdiv
  let ?w = \<open>snd L ! ka\<close>
  obtain L1 q where p: \<open>push_m L (CoreTerm_Bin BinOp_Udiv (abs_t ka ?w) (abs_t kb ?w)) ?w = (L1, q)\<close>
    by (cases \<open>push_m L (CoreTerm_Bin BinOp_Udiv (abs_t ka ?w) (abs_t kb ?w)) ?w\<close>)
  have \<open>push_m L1 (CoreTerm_Ite (CoreTerm_Bin BinOp_Xor (msb_t ka ?w) (msb_t kb ?w)) (neg_t q ?w) (cr q)) ?w = (L', k)\<close>
    using Op_Sdiv R p by (simp add: lower_bin_m_def Let_def)
  then show ?thesis using pfx_push[OF p] pfx_push_trans by blast
next
  case Op_Srem
  let ?w = \<open>snd L ! ka\<close>
  obtain L1 r where p: \<open>push_m L (CoreTerm_Bin BinOp_Urem (abs_t ka ?w) (abs_t kb ?w)) ?w = (L1, r)\<close>
    by (cases \<open>push_m L (CoreTerm_Bin BinOp_Urem (abs_t ka ?w) (abs_t kb ?w)) ?w\<close>)
  have \<open>push_m L1 (CoreTerm_Ite (msb_t ka ?w) (neg_t r ?w) (cr r)) ?w = (L', k)\<close>
    using Op_Srem R p by (simp add: lower_bin_m_def Let_def)
  then show ?thesis using pfx_push[OF p] pfx_push_trans by blast
next
  case Op_Smod
  let ?w = \<open>snd L ! ka\<close>
  obtain L1 u where p: \<open>push_m L (CoreTerm_Bin BinOp_Urem (abs_t ka ?w) (abs_t kb ?w)) ?w = (L1, u)\<close>
    by (cases \<open>push_m L (CoreTerm_Bin BinOp_Urem (abs_t ka ?w) (abs_t kb ?w)) ?w\<close>)
  obtain L2 nu where p2: \<open>push_m L1 (neg_t u ?w) ?w = (L2, nu)\<close>
    by (cases \<open>push_m L1 (neg_t u ?w) ?w\<close>)
  have \<open>push_m L2 (CoreTerm_Ite (CoreTerm_Bin BinOp_Eq (cr u) (CoreTerm_Const (replicate ?w False))) (cr u)
          (CoreTerm_Ite (msb_t ka ?w)
             (CoreTerm_Ite (msb_t kb ?w) (cr nu) (CoreTerm_Bin BinOp_Add (cr nu) (cr kb)))
             (CoreTerm_Ite (msb_t kb ?w) (CoreTerm_Bin BinOp_Add (cr u) (cr kb)) (cr u)))) ?w = (L', k)\<close>
    using Op_Smod R p p2 by (simp add: lower_bin_m_def Let_def)
  then show ?thesis using pfx_push[OF p] pfx_push_trans[OF _ p2] pfx_push_trans by blast
qed (use R in \<open>auto simp add: lower_bin_m_def Let_def intro: pfx_push\<close>)

lemma repeat_fold_pfx:
  \<open>foldl (repeat_step ka w) (L, k, acc) js = (L', k', acc') \<Longrightarrow> pfx L L'\<close>
proof (induction js arbitrary: L k acc)
  case Nil
  then show ?case by (simp add: pfx_refl)
next
  case (Cons j js)
  obtain L1 k1 where s: \<open>push_m L (CoreTerm_Bin BinOp_Concat (cr ka) (cr k)) (acc + w) = (L1, k1)\<close>
    by (cases \<open>push_m L (CoreTerm_Bin BinOp_Concat (cr ka) (cr k)) (acc + w)\<close>)
  have \<open>foldl (repeat_step ka w) (L1, k1, acc + w) js = (L', k', acc')\<close>
    using Cons.prems s by (simp add: repeat_step_def)
  then show ?case using Cons.IH pfx_push[OF s] pfx_trans by blast
qed

lemma lower_m_pfx: \<open>lower_m ws dm L t = (L', k) \<Longrightarrow> pfx L L'\<close>
proof (induction t arbitrary: L L' k)
  case (Term_Const bs)
  then show ?case by (simp add: pfx_push)
next
  case (Term_Var i)
  then show ?case by (simp add: pfx_push)
next
  case (Term_Ref j)
  then show ?case by (simp add: pfx_refl)
next
  case (Term_Not a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  have \<open>push_m L1 (CoreTerm_Not (cr ka)) (snd L1 ! ka) = (L', k)\<close> using Term_Not.prems a by simp
  then show ?case using Term_Not.IH[OF a] pfx_push_trans by blast
next
  case (Term_Neg a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  have \<open>push_m L1 (neg_t ka (snd L1 ! ka)) (snd L1 ! ka) = (L', k)\<close> using Term_Neg.prems a by simp
  then show ?case using Term_Neg.IH[OF a] pfx_push_trans by blast
next
  case (Term_Bin op a b)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  obtain L2 kb where b: \<open>lower_m ws dm L1 b = (L2, kb)\<close> by (cases \<open>lower_m ws dm L1 b\<close>)
  have \<open>lower_bin_m L2 op ka kb = (L', k)\<close> using Term_Bin.prems a b by simp
  then show ?case using Term_Bin.IH(1)[OF a] Term_Bin.IH(2)[OF b] lower_bin_m_pfx pfx_trans by blast
next
  case (Term_Extract hi lo a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  have \<open>push_m L1 (CoreTerm_Extract hi lo (cr ka)) (unat hi - unat lo + 1) = (L', k)\<close>
    using Term_Extract.prems a by simp
  then show ?case using Term_Extract.IH[OF a] pfx_push_trans by blast
next
  case (Term_Repeat i a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  obtain L2 k0 where p: \<open>push_m L1 (CoreTerm_Const []) 0 = (L2, k0)\<close> by (cases \<open>push_m L1 (CoreTerm_Const []) 0\<close>)
  obtain L3 k3 acc where f: \<open>foldl (repeat_step ka (snd L1 ! ka)) (L2, k0, 0) [0..<unat i] = (L3, k3, acc)\<close>
    by (cases \<open>foldl (repeat_step ka (snd L1 ! ka)) (L2, k0, 0) [0..<unat i]\<close>)
  have \<open>L' = L3\<close> using Term_Repeat.prems a p f by (simp add: Let_def)
  then show ?case using Term_Repeat.IH[OF a] pfx_push[OF p] repeat_fold_pfx[OF f] pfx_trans by blast
next
  case (Term_ZeroExtend i a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  have \<open>push_m L1 (CoreTerm_Bin BinOp_Concat (CoreTerm_Const (replicate (unat i) False)) (cr ka))
          (snd L1 ! ka + unat i) = (L', k)\<close>
    using Term_ZeroExtend.prems a by (simp add: Let_def)
  then show ?case using Term_ZeroExtend.IH[OF a] pfx_push_trans by blast
next
  case (Term_SignExtend i a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  have \<open>push_m L1 (CoreTerm_Bin BinOp_Concat
                   (CoreTerm_Ite (msb_t ka (snd L1 ! ka)) (CoreTerm_Const (replicate (unat i) True))
                      (CoreTerm_Const (replicate (unat i) False)))
                   (cr ka)) (snd L1 ! ka + unat i) = (L', k)\<close>
    using Term_SignExtend.prems a by (simp add: Let_def)
  then show ?case using Term_SignExtend.IH[OF a] pfx_push_trans by blast
next
  case (Term_RotateLeft i a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  let ?w = \<open>snd L1 ! ka\<close> and ?r = \<open>unat i mod snd L1 ! ka\<close>
  show ?case
  proof (cases \<open>?r = 0\<close>)
    case True
    then have \<open>L' = L1\<close> using Term_RotateLeft.prems a by (simp add: Let_def)
    then show ?thesis using Term_RotateLeft.IH[OF a] by simp
  next
    case False
    then have \<open>push_m L1 (CoreTerm_Bin BinOp_Concat
                        (CoreTerm_Extract (word_of_nat (?w - 1 - ?r)) 0 (cr ka))
                        (CoreTerm_Extract (word_of_nat (?w - 1)) (word_of_nat (?w - ?r)) (cr ka))) ?w = (L', k)\<close>
      using Term_RotateLeft.prems a by (simp add: Let_def)
    then show ?thesis using Term_RotateLeft.IH[OF a] pfx_push_trans by blast
  qed
next
  case (Term_RotateRight i a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  let ?w = \<open>snd L1 ! ka\<close> and ?r = \<open>unat i mod snd L1 ! ka\<close>
  show ?case
  proof (cases \<open>?r = 0\<close>)
    case True
    then have \<open>L' = L1\<close> using Term_RotateRight.prems a by (simp add: Let_def)
    then show ?thesis using Term_RotateRight.IH[OF a] by simp
  next
    case False
    then have \<open>push_m L1 (CoreTerm_Bin BinOp_Concat
                        (CoreTerm_Extract (word_of_nat (?r - 1)) 0 (cr ka))
                        (CoreTerm_Extract (word_of_nat (?w - 1)) (word_of_nat ?r) (cr ka))) ?w = (L', k)\<close>
      using Term_RotateRight.prems a by (simp add: Let_def)
    then show ?thesis using Term_RotateRight.IH[OF a] pfx_push_trans by blast
  qed
next
  case (Term_Ite c a b)
  obtain L1 kc where c: \<open>lower_m ws dm L c = (L1, kc)\<close> by (cases \<open>lower_m ws dm L c\<close>)
  obtain L2 ka where a: \<open>lower_m ws dm L1 a = (L2, ka)\<close> by (cases \<open>lower_m ws dm L1 a\<close>)
  obtain L3 kb where b: \<open>lower_m ws dm L2 b = (L3, kb)\<close> by (cases \<open>lower_m ws dm L2 b\<close>)
  have \<open>push_m L3 (CoreTerm_Ite (cr kc) (cr ka) (cr kb)) (snd L3 ! ka) = (L', k)\<close>
    using Term_Ite.prems c a b by simp
  then show ?case
    using Term_Ite.IH(1)[OF c] Term_Ite.IH(2)[OF a] Term_Ite.IH(3)[OF b] pfx_push_trans pfx_trans by blast
qed

subsection \<open>Pushing a term with a known value\<close>

lemma push_correct:
  assumes \<open>lok ws L\<close> \<open>cwt ws (snd L) t\<close> \<open>cwidth ws (snd L) t = w\<close> \<open>push_m L t w = (L', k)\<close>
    \<open>\<And>vs. vs_ok ws vs \<Longrightarrow> ceval ws (snd L) vs (CV ws vs L) t = f vs\<close>
  shows \<open>lext ws L L' \<and> k < length (fst L') \<and> snd L' ! k = w \<and> (\<forall>vs. vs_ok ws vs \<longrightarrow> CV ws vs L' ! k = f vs)\<close>
proof -
  note P = push_ok[OF assms(1-4)]
  have \<open>lext ws L L'\<close> using lext_push[OF assms(1-4)] .
  moreover have \<open>k < length (fst L')\<close> using P(2) P(4) by simp
  moreover have \<open>snd L' ! k = w\<close> using P(3) P(4) lok_length[OF assms(1)] by (simp add: nth_append)
  moreover have \<open>\<forall>vs. vs_ok ws vs \<longrightarrow> CV ws vs L' ! k = f vs\<close>
    using P(5) P(4) assms(5) by (simp add: nth_append lok_CV_length)
  ultimately show ?thesis by blast
qed

lemma cr_wt: \<open>k < length cws \<Longrightarrow> k < 2 ^ 64 \<Longrightarrow> cwt ws cws (cr k)\<close>
  by (simp add: cr_def unat_wn)

lemma cr_width: \<open>k < 2 ^ 64 \<Longrightarrow> cwidth ws cws (cr k) = cws ! k\<close>
  by (simp add: cr_def unat_wn)

lemma cr_eval: \<open>k < 2 ^ 64 \<Longrightarrow> ceval ws cws vs cdv (cr k) = cdv ! k\<close>
  by (simp add: cr_def unat_wn)

lemma ref_ok_of_lok:
  \<open>lok ws L \<Longrightarrow> vs_ok ws vs \<Longrightarrow> k < length (fst L) \<Longrightarrow> k < 2 ^ 64 \<Longrightarrow>
   ref_ok (snd L) (CV ws vs L) k (snd L ! k) (CV ws vs L ! k)\<close>
  by (simp add: ref_ok_def lok_length lok_CV_lt)

text \<open>The width of a binary operation of the extended language.\<close>
definition op_width :: \<open>Op \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>op_width op wa wb \<equiv>
     (case op of
        Op_Concat \<Rightarrow> wa + wb
      | Op_Comp \<Rightarrow> 1 | Op_Eq \<Rightarrow> 1 | Op_Distinct \<Rightarrow> 1
      | Op_Ult \<Rightarrow> 1 | Op_Ule \<Rightarrow> 1 | Op_Ugt \<Rightarrow> 1 | Op_Uge \<Rightarrow> 1
      | Op_Slt \<Rightarrow> 1 | Op_Sle \<Rightarrow> 1 | Op_Sgt \<Rightarrow> 1 | Op_Sge \<Rightarrow> 1
      | _ \<Rightarrow> wa)\<close>

lemma width_Bin_op: \<open>width ws ds (Term_Bin op a b) = op_width op (width ws ds a) (width ws ds b)\<close>
  by (cases op) (simp_all add: op_width_def)

subsection \<open>The arithmetic of the rewritten operations\<close>

text \<open>Each lemma states that the value computed by the core terms of an operation (left) is the
  value the specification gives it (right), for operands \<open>x\<close>, \<open>y\<close> of width \<open>w \<ge> 1\<close>.\<close>

lemma sub_arith: \<open>x < 2 ^ w \<Longrightarrow> y < 2 ^ w \<Longrightarrow> (x + negv w y) mod 2 ^ w = bin_sem Op_Sub w x w y\<close>
  by (simp add: negv_def mod_add_right_eq)

lemma udiv_absv: \<open>1 \<le> w \<Longrightarrow> x < 2 ^ w \<Longrightarrow> y < 2 ^ w \<Longrightarrow>
   cbin_sem BinOp_Udiv w (absv w x) w (absv w y) = (if y = 0 then 2 ^ w - 1 else absv w x div absv w y)\<close>
  by (simp add: absv_0_iff)

lemma urem_absv: \<open>1 \<le> w \<Longrightarrow> x < 2 ^ w \<Longrightarrow> y < 2 ^ w \<Longrightarrow>
   cbin_sem BinOp_Urem w (absv w x) w (absv w y) = (if y = 0 then absv w x else absv w x mod absv w y)\<close>
  by (simp add: absv_0_iff)

text \<open>Facts about \<^const>\<open>to_bv\<close> and about truncated division.\<close>
lemma to_bv_int_mod: \<open>to_bv w (int n) = n mod 2 ^ w\<close>
  by (simp add: to_bv_def nat_mod_distrib nat_power_eq)

lemma to_bv_sub_pow: \<open>to_bv w (z - 2 ^ w) = to_bv w z\<close>
  by (simp add: to_bv_def)

lemma to_bv_add_pow: \<open>to_bv w (z + 2 ^ w) = to_bv w z\<close>
  by (simp add: to_bv_def)

lemma to_bv_diff: \<open>u \<le> 2 ^ w \<Longrightarrow> to_bv w (int y - int u) = (y + (2 ^ w - u)) mod 2 ^ w\<close>
proof -
  assume \<open>u \<le> 2 ^ w\<close>
  then have E0: \<open>(2 ^ w - u) + u = (2 :: nat) ^ w\<close> by simp
  have E: \<open>int (2 ^ w - u) + int u = 2 ^ w\<close> using arg_cong[OF E0, of int] by simp
  have 1: \<open>int y - int u + 2 ^ w = int (y + (2 ^ w - u))\<close> using E unfolding of_nat_add by linarith
  have \<open>to_bv w (int y - int u) = to_bv w (int y - int u + 2 ^ w)\<close> by (rule to_bv_add_pow[symmetric])
  also have \<open>\<dots> = to_bv w (int (y + (2 ^ w - u)))\<close> by (rule arg_cong[OF 1])
  also have \<open>\<dots> = (y + (2 ^ w - u)) mod 2 ^ w\<close> by (rule to_bv_int_mod)
  finally show ?thesis .
qed

lemma tmod_abs:
  assumes \<open>b \<noteq> 0\<close>
  shows \<open>tmod a b = (if a < 0 then - (\<bar>a\<bar> mod \<bar>b\<bar>) else \<bar>a\<bar> mod \<bar>b\<bar>)\<close>
proof (cases \<open>a < 0\<close>; cases \<open>b < 0\<close>)
  assume A: \<open>\<not> a < 0\<close> \<open>\<not> b < 0\<close>
  have \<open>tmod a b = a - b * (a div b)\<close> using A by (simp add: tmod_def tdiv_def)
  also have \<open>\<dots> = a mod b\<close> using mult_div_mod_eq[of b a] by linarith
  finally show ?thesis using A by simp
next
  assume A: \<open>\<not> a < 0\<close> \<open>b < 0\<close>
  have \<open>tmod a b = a + b * (a div (- b))\<close> using A by (simp add: tmod_def tdiv_def)
  also have \<open>\<dots> = a mod (- b)\<close> using mult_div_mod_eq[of \<open>- b\<close> a] by (simp add: mult_minus_left)
  finally show ?thesis using A by simp
next
  assume A: \<open>a < 0\<close> \<open>\<not> b < 0\<close>
  have \<open>tmod a b = a + b * (- a div b)\<close> using A by (simp add: tmod_def tdiv_def)
  also have \<open>\<dots> = - (- a mod b)\<close> using mult_div_mod_eq[of b \<open>- a\<close>] by linarith
  finally show ?thesis using A by simp
next
  assume A: \<open>a < 0\<close> \<open>b < 0\<close>
  have \<open>tmod a b = a - b * (- a div - b)\<close> using A by (simp add: tmod_def tdiv_def)
  also have \<open>\<dots> = - (- a mod - b)\<close> using mult_div_mod_eq[of \<open>- b\<close> \<open>- a\<close>] by (simp add: mult_minus_left)
  finally show ?thesis using A by simp
qed

lemma absv_pos_iff: \<open>1 \<le> w \<Longrightarrow> x < 2 ^ w \<Longrightarrow> (0 < absv w x) = (0 < x)\<close>
  using absv_0_iff[of w x] by auto

lemma sdiv_arith:
  assumes \<open>1 \<le> w\<close> \<open>x < 2 ^ w\<close> \<open>y < 2 ^ w\<close>
  shows \<open>(let q = (if y = 0 then 2 ^ w - 1 else absv w x div absv w y) in
          if sbit w x \<noteq> sbit w y then negv w q else q) = bin_sem Op_Sdiv w x w y\<close>
proof (cases \<open>y = 0\<close>)
  case True
  have \<open>\<not> sbit w 0\<close> by (simp add: sbit_def)
  moreover have \<open>negv w (2 ^ w - 1) = 1\<close>
  proof -
    have \<open>(2 :: nat) ^ 1 \<le> 2 ^ w\<close> using assms(1) by (intro power_increasing) simp_all
    then show ?thesis by (simp add: negv_pos)
  qed
  ultimately show ?thesis using True sint_neg_iff[OF assms(1,2)] by (simp add: Let_def)
next
  case False
  let ?q = \<open>absv w x div absv w y\<close>
  have ay: \<open>0 < absv w y\<close> using False absv_pos_iff[OF assms(1,3)] by simp
  have td: \<open>tdiv (sint w x) (sint w y) = (if sbit w x = sbit w y then int ?q else - int ?q)\<close>
    using sint_neg_iff[OF assms(1,2)] sint_neg_iff[OF assms(1,3)] abs_sint[OF assms(1,2)] abs_sint[OF assms(1,3)]
    by (simp add: tdiv_def zdiv_int)
  have \<open>?q \<le> absv w x\<close> by (rule div_le_dividend)
  then have q: \<open>?q < 2 ^ w\<close> using absv_lt[OF assms(1,2)] by (rule le_less_trans)
  show ?thesis using False td to_bv_nat[OF q] to_bv_neg[OF q] by (simp add: Let_def)
qed

lemma srem_arith:
  assumes \<open>1 \<le> w\<close> \<open>x < 2 ^ w\<close> \<open>y < 2 ^ w\<close>
  shows \<open>(let r = (if y = 0 then absv w x else absv w x mod absv w y) in
          if sbit w x then negv w r else r) = bin_sem Op_Srem w x w y\<close>
proof (cases \<open>y = 0\<close>)
  case True
  then show ?thesis
    using absv_sbit[OF assms(1,2)] negv_negv[OF assms(2)] by (simp add: Let_def)
next
  case False
  let ?r = \<open>absv w x mod absv w y\<close>
  have sy: \<open>sint w y \<noteq> 0\<close>
    using False assms(1,3) by (simp add: sint_cases pow_w_split sbit_def)
  have tm: \<open>tmod (sint w x) (sint w y) = (if sbit w x then - int ?r else int ?r)\<close>
    using tmod_abs[OF sy] sint_neg_iff[OF assms(1,2)] abs_sint[OF assms(1,2)] abs_sint[OF assms(1,3)]
    by (simp add: zmod_int)
  have \<open>?r \<le> absv w x\<close> by (rule mod_less_eq_dividend)
  then have r: \<open>?r < 2 ^ w\<close> using absv_lt[OF assms(1,2)] by (rule le_less_trans)
  show ?thesis using False tm to_bv_nat[OF r] to_bv_neg[OF r] by (simp add: Let_def)
qed

lemma smod_arith:
  assumes \<open>1 \<le> w\<close> \<open>x < 2 ^ w\<close> \<open>y < 2 ^ w\<close>
  shows \<open>(let u = (if y = 0 then absv w x else absv w x mod absv w y) in
          if u = 0 then u
          else if sbit w x then (if sbit w y then negv w u else (negv w u + y) mod 2 ^ w)
          else (if sbit w y then (u + y) mod 2 ^ w else u)) = bin_sem Op_Smod w x w y\<close>
proof (cases \<open>y = 0\<close>)
  case True
  have \<open>\<not> sbit w 0\<close> by (simp add: sbit_def)
  moreover have \<open>sbit w x \<Longrightarrow> negv w (absv w x) = x\<close>
    using absv_sbit[OF assms(1,2)] negv_negv[OF assms(2)] by simp
  ultimately show ?thesis
    using True absv_0_iff[OF assms(1,2)] absv_sbit[OF assms(1,2)] assms(2) by (simp add: Let_def)
next
  case False
  let ?ax = \<open>absv w x\<close> and ?ay = \<open>absv w y\<close>
  let ?u = \<open>absv w x mod absv w y\<close>
  have ay: \<open>0 < ?ay\<close> using False absv_pos_iff[OF assms(1,3)] by simp
  have \<open>?u \<le> absv w x\<close> by (rule mod_less_eq_dividend)
  then have u: \<open>?u < 2 ^ w\<close> using absv_lt[OF assms(1,2)] by (rule le_less_trans)
  have sx: \<open>sint w x = (if sbit w x then - int ?ax else int ?ax)\<close> by (rule sint_absv_sbit[OF assms(1,2)])
  have sy: \<open>sint w y = (if sbit w y then - int ?ay else int ?ay)\<close> by (rule sint_absv_sbit[OF assms(1,3)])
  have m: \<open>int ?ax mod int ?ay = int ?u\<close> by (simp add: zmod_int)
  have ayy: \<open>sbit w y \<Longrightarrow> ?ay = 2 ^ w - y\<close> by (simp add: absv_def)
  have y0: \<open>sbit w y \<Longrightarrow> 0 < y\<close> using absv_pos_iff[OF assms(1,3)] ay by (simp add: absv_def)
  show ?thesis
  proof (cases \<open>sbit w x\<close>; cases \<open>sbit w y\<close>)
    assume \<open>\<not> sbit w x\<close> \<open>\<not> sbit w y\<close>
    then show ?thesis using False sx sy m to_bv_nat[OF u] by (simp add: Let_def)
  next
    assume A: \<open>sbit w x\<close> \<open>\<not> sbit w y\<close>
    have \<open>sint w x mod sint w y = (if ?u = 0 then 0 else int ?ay - int ?u)\<close>
      using A sx sy m by (simp add: zmod_zminus1_eq_if)
    moreover have \<open>?ay = y\<close> using A by (simp add: absv_def)
    moreover have \<open>?u \<noteq> 0 \<Longrightarrow> (negv w ?u + y) mod 2 ^ w = to_bv w (int y - int ?u)\<close>
      using u negv_pos[OF _ u] to_bv_diff[of ?u w y] by (simp add: add.commute)
    ultimately show ?thesis using False A by (simp add: Let_def to_bv_def)
  next
    assume A: \<open>\<not> sbit w x\<close> \<open>sbit w y\<close>
    have \<open>sint w x mod sint w y = (if ?u = 0 then 0 else int ?u - int ?ay)\<close>
      using A sx sy m by (simp add: zmod_zminus2_eq_if)
    moreover have \<open>?u \<noteq> 0 \<Longrightarrow> to_bv w (int ?u - int ?ay) = (?u + y) mod 2 ^ w\<close>
    proof -
      have E0: \<open>?ay + y = 2 ^ w\<close> using ayy[OF A(2)] assms(3) by simp
      have E: \<open>int ?ay + int y = 2 ^ w\<close> using arg_cong[OF E0, of int] by simp
      have E2: \<open>int ?u - int ?ay = int (?u + y) - 2 ^ w\<close> using E unfolding of_nat_add by linarith
      have \<open>to_bv w (int ?u - int ?ay) = to_bv w (int (?u + y) - 2 ^ w)\<close> by (rule arg_cong[OF E2])
      also have \<open>\<dots> = to_bv w (int (?u + y))\<close> by (rule to_bv_sub_pow)
      also have \<open>\<dots> = (?u + y) mod 2 ^ w\<close> by (rule to_bv_int_mod)
      finally show ?thesis .
    qed
    ultimately show ?thesis using False A by (simp add: Let_def to_bv_def)
  next
    assume A: \<open>sbit w x\<close> \<open>sbit w y\<close>
    have \<open>sint w x mod sint w y = - int ?u\<close> using A sx sy m by (simp add: mod_minus_minus)
    then show ?thesis using False A to_bv_neg[OF u] by (simp add: Let_def)
  qed
qed

lemma int_div_neg1: \<open>0 < d \<Longrightarrow> (- int n - 1) div d = - int (n div nat d) - 1\<close> for d :: int
proof -
  assume \<open>0 < d\<close>
  define m where \<open>m = nat d\<close>
  have d: \<open>d = int m\<close> using \<open>0 < d\<close> m_def by simp
  have m0: \<open>0 < m\<close> using \<open>0 < d\<close> m_def by simp
  have nm: \<open>int (n div m) * int m + int (n mod m) = int n\<close>
    by (simp flip: of_nat_add of_nat_mult)
  have eq: \<open>- int n - 1 = (- int (n div m) - 1) * d + (d - 1 - int (n mod m))\<close>
    using nm unfolding d by (simp add: algebra_simps)
  have r: \<open>0 \<le> d - 1 - int (n mod m)\<close> \<open>d - 1 - int (n mod m) < d\<close>
    using mod_less_divisor[OF m0, of n] d by simp_all
  have \<open>(- int n - 1) div d = (- int (n div m) - 1) + (d - 1 - int (n mod m)) div d\<close>
    using \<open>0 < d\<close> by (subst eq) (simp add: div_mult_self3)
  also have \<open>(d - 1 - int (n mod m)) div d = 0\<close> using r by (rule div_pos_pos_trivial)
  finally show ?thesis using m_def by simp
qed

lemma ashr_arith:
  assumes \<open>1 \<le> w\<close> \<open>x < 2 ^ w\<close>
  shows \<open>(if sbit w x then 2 ^ w - 1 - (2 ^ w - 1 - x) div 2 ^ y else x div 2 ^ y) = bin_sem Op_Ashr w x w y\<close>
proof (cases \<open>sbit w x\<close>)
  case False
  have \<open>x div 2 ^ y \<le> x\<close> by (rule div_le_dividend)
  then have lt: \<open>x div 2 ^ y < 2 ^ w\<close> using assms(2) by (rule le_less_trans)
  have \<open>int x div 2 ^ y = int (x div 2 ^ y)\<close> by (simp add: zdiv_int)
  then show ?thesis using False lt by (simp add: sint_cases to_bv_nat)
next
  case True
  let ?n = \<open>2 ^ w - 1 - x\<close> and ?m = \<open>(2 ^ w - 1 - x) div 2 ^ y\<close>
  have \<open>1 \<le> (2 :: nat) ^ (w - 1)\<close> by simp
  then have x1: \<open>1 \<le> x\<close> using True unfolding sbit_def by linarith
  have s: \<open>sint w x = - int ?n - 1\<close> using True assms(2) x1 by (simp add: sint_cases of_nat_diff)
  have d: \<open>sint w x div 2 ^ y = - int ?m - 1\<close>
    using int_div_neg1[of \<open>2 ^ y\<close> ?n] by (simp add: s nat_power_eq)
  have \<open>?m \<le> ?n\<close> by (rule div_le_dividend)
  moreover have \<open>?n + 1 < 2 ^ w\<close> using x1 assms(2) by arith
  ultimately have m: \<open>?m + 1 < 2 ^ w\<close> by linarith
  have eq: \<open>- int ?m - 1 = - int (?m + 1)\<close> by simp
  have \<open>to_bv w (- int ?m - 1) = negv w (?m + 1)\<close> by (subst eq) (rule to_bv_neg[OF m])
  also have \<open>\<dots> = 2 ^ w - (?m + 1)\<close> using m by (simp add: negv_pos)
  finally show ?thesis using True d by simp
qed

lemma sext_arith:
  assumes \<open>1 \<le> w\<close> \<open>x < 2 ^ w\<close>
  shows \<open>(if sbit w x then 2 ^ i - 1 else 0) * 2 ^ w + x = to_bv (w + i) (sint w x)\<close>
proof (cases \<open>sbit w x\<close>)
  case False
  have \<open>(2 :: nat) ^ w \<le> 2 ^ (w + i)\<close> by (simp add: power_increasing)
  with assms(2) have \<open>x < 2 ^ (w + i)\<close> by (rule less_le_trans)
  then show ?thesis using False by (simp add: sint_cases to_bv_nat)
next
  case True
  have lt: \<open>(2 ^ i - 1) * 2 ^ w + x < 2 ^ (w + i)\<close>
  proof -
    have \<open>(2 ^ i - 1) * 2 ^ w + 1 * 2 ^ w = (2 :: nat) ^ i * 2 ^ w\<close>
      by (simp only: distrib_right[symmetric]) simp
    then have \<open>(2 ^ i - 1) * 2 ^ w + 2 ^ w = (2 :: nat) ^ (w + i)\<close> by (simp add: power_add mult.commute)
    then show ?thesis using assms(2) by linarith
  qed
  have e: \<open>int x - 2 ^ w = int ((2 ^ i - 1) * 2 ^ w + x) - 2 ^ (w + i)\<close>
  proof -
    have \<open>int ((2 ^ i - 1) * 2 ^ w + x) = (2 ^ i - 1) * 2 ^ w + int x\<close> by (simp add: of_nat_diff)
    then show ?thesis by (simp add: power_add algebra_simps)
  qed
  have s: \<open>sint w x = int x - 2 ^ w\<close> using True by (simp add: sint_cases)
  have \<open>to_bv (w + i) (sint w x) = to_bv (w + i) (int ((2 ^ i - 1) * 2 ^ w + x) - 2 ^ (w + i))\<close>
    unfolding s by (rule arg_cong[OF e])
  also have \<open>\<dots> = to_bv (w + i) (int ((2 ^ i - 1) * 2 ^ w + x))\<close> by (rule to_bv_sub_pow)
  also have \<open>\<dots> = ((2 ^ i - 1) * 2 ^ w + x) mod 2 ^ (w + i)\<close> by (rule to_bv_int_mod)
  also have \<open>\<dots> = (2 ^ i - 1) * 2 ^ w + x\<close> using lt by (rule mod_less)
  finally show ?thesis using True by simp
qed

lemma rotl_arith: \<open>r < w \<Longrightarrow> (x :: nat) < 2 ^ w \<Longrightarrow> (x div 2 ^ (w - r)) mod 2 ^ r = x div 2 ^ (w - r)\<close>
proof -
  assume \<open>r < w\<close> \<open>x < 2 ^ w\<close>
  have \<open>r + (w - r) = w\<close> using \<open>r < w\<close> by simp
  then have \<open>(2 :: nat) ^ w = 2 ^ r * 2 ^ (w - r)\<close> by (metis power_add)
  then have \<open>x div 2 ^ (w - r) < 2 ^ r\<close> using \<open>x < 2 ^ w\<close> by (simp add: div_less_iff_less_mult)
  then show ?thesis by simp
qed

lemma rotr_arith: \<open>r < w \<Longrightarrow> (x :: nat) < 2 ^ w \<Longrightarrow> (x div 2 ^ r) mod 2 ^ (w - r) = x div 2 ^ r\<close>
proof -
  assume \<open>r < w\<close> \<open>x < 2 ^ w\<close>
  have \<open>(w - r) + r = w\<close> using \<open>r < w\<close> by simp
  then have \<open>(2 :: nat) ^ w = 2 ^ (w - r) * 2 ^ r\<close> by (metis power_add)
  then have \<open>x div 2 ^ r < 2 ^ (w - r)\<close> using \<open>x < 2 ^ w\<close> by (simp add: div_less_iff_less_mult)
  then show ?thesis by simp
qed

subsection \<open>The environment of a core definition\<close>

text \<open>The core definition \<open>k\<close> of the well-formed state \<open>L\<close> has the width \<open>w\<close>, with the bounds the
  built terms need.\<close>
definition env_ok :: \<open>nat list \<Rightarrow> lst \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>env_ok ws L k w \<equiv> lok ws L \<and> k < length (fst L) \<and> k < 2 ^ 64 \<and> snd L ! k = w \<and> 1 \<le> w \<and> w < 2 ^ 64\<close>

definition vs0 :: \<open>nat list \<Rightarrow> nat list\<close> where
  \<open>vs0 ws \<equiv> map (\<lambda>_. 0) ws\<close>

lemma vs0_ok: \<open>vs_ok ws (vs0 ws)\<close>
  by (simp add: vs_ok_def vs0_def)

lemma env_ref_ok:
  assumes \<open>env_ok ws L k w\<close> \<open>vs_ok ws vs\<close>
  shows \<open>ref_ok (snd L) (CV ws vs L) k w (CV ws vs L ! k)\<close>
  using ref_ok_of_lok[OF _ assms(2), of L k] assms(1) by (simp add: env_ok_def)

lemma env_lext:
  assumes \<open>env_ok ws L k w\<close> \<open>lext ws L L'\<close>
  shows \<open>env_ok ws L' k w\<close>
proof -
  have L: \<open>lok ws L\<close> and k: \<open>k < length (fst L)\<close> using assms(1) by (simp_all add: env_ok_def)
  show ?thesis
    using assms(1) lext_lok[OF assms(2)] lext_length[OF assms(2)] lext_nth_snd[OF L assms(2) k]
    by (simp add: env_ok_def)
qed

lemma env_CV: \<open>env_ok ws L k w \<Longrightarrow> lext ws L L' \<Longrightarrow> CV ws vs L' ! k = CV ws vs L ! k\<close>
  using lext_nth_CV[of ws L L' k vs] by (simp add: env_ok_def)

lemma env_lt:
  assumes \<open>env_ok ws L k w\<close> \<open>vs_ok ws vs\<close>
  shows \<open>CV ws vs L ! k < 2 ^ w\<close>
  using lok_CV_lt[OF _ assms(2), of L k] assms(1) by (simp add: env_ok_def)

lemma env_push:
  assumes \<open>lok ws L\<close> \<open>cwt ws (snd L) t\<close> \<open>cwidth ws (snd L) t = w\<close> \<open>push_m L t w = (L', k)\<close>
    \<open>1 \<le> w\<close> \<open>w < 2 ^ 64\<close> \<open>length (fst L') < 2 ^ 64\<close>
  shows \<open>env_ok ws L' k w\<close>
  using push_ok[OF assms(1-4)] lok_length[OF assms(1)] assms(5-7) by (simp add: env_ok_def nth_append)

text \<open>The built terms, in the environment of their definitions.\<close>
lemma cr_env:
  assumes \<open>env_ok ws L k w\<close>
  shows \<open>cwt ws (snd L) (cr k) \<and> cwidth ws (snd L) (cr k) = w \<and>
     (\<forall>vs. ceval ws (snd L) vs (CV ws vs L) (cr k) = CV ws vs L ! k)\<close>
proof -
  have \<open>k < length (snd L)\<close> using assms lok_length[of ws L] by (simp add: env_ok_def)
  then show ?thesis using assms cr_wt[of k \<open>snd L\<close> ws] cr_width[of k ws \<open>snd L\<close>] cr_eval[of k ws \<open>snd L\<close>]
    by (simp add: env_ok_def)
qed

lemma neg_t_env:
  assumes \<open>env_ok ws L k w\<close>
  shows \<open>cwt ws (snd L) (neg_t k w) \<and> cwidth ws (snd L) (neg_t k w) = w \<and>
     (\<forall>vs. vs_ok ws vs \<longrightarrow> ceval ws (snd L) vs (CV ws vs L) (neg_t k w) = negv w (CV ws vs L ! k))\<close>
  using neg_t_sem[OF env_ref_ok[OF assms vs0_ok]] neg_t_sem(3)[OF env_ref_ok[OF assms]] assms
  by (simp add: env_ok_def)

lemma msb_t_env:
  assumes \<open>env_ok ws L k w\<close>
  shows \<open>cwt ws (snd L) (msb_t k w) \<and> cwidth ws (snd L) (msb_t k w) = 1 \<and>
     (\<forall>vs. vs_ok ws vs \<longrightarrow> ceval ws (snd L) vs (CV ws vs L) (msb_t k w) = of_bool (sbit w (CV ws vs L ! k)))\<close>
  using msb_t_sem[OF env_ref_ok[OF assms vs0_ok]] msb_t_sem(3)[OF env_ref_ok[OF assms]] assms
  by (simp add: env_ok_def)

lemma abs_t_env:
  assumes \<open>env_ok ws L k w\<close>
  shows \<open>cwt ws (snd L) (abs_t k w) \<and> cwidth ws (snd L) (abs_t k w) = w \<and>
     (\<forall>vs. vs_ok ws vs \<longrightarrow> ceval ws (snd L) vs (CV ws vs L) (abs_t k w) = absv w (CV ws vs L ! k))\<close>
  using abs_t_sem[OF env_ref_ok[OF assms vs0_ok]] abs_t_sem(3)[OF env_ref_ok[OF assms]] assms
  by (simp add: env_ok_def)

lemma slt_t_env:
  assumes \<open>env_ok ws L ka w\<close> \<open>env_ok ws L kb w\<close>
  shows \<open>cwt ws (snd L) (slt_t ka kb w) \<and> cwidth ws (snd L) (slt_t ka kb w) = 1 \<and>
     (\<forall>vs. vs_ok ws vs \<longrightarrow> ceval ws (snd L) vs (CV ws vs L) (slt_t ka kb w) =
        of_bool (sint w (CV ws vs L ! ka) < sint w (CV ws vs L ! kb)))\<close>
  using slt_t_sem[OF env_ref_ok[OF assms(1) vs0_ok] env_ref_ok[OF assms(2) vs0_ok]]
    slt_t_sem(3)[OF env_ref_ok[OF assms(1)] env_ref_ok[OF assms(2)]] assms
  by (simp add: env_ok_def)

lemma sle_t_env:
  assumes \<open>env_ok ws L ka w\<close> \<open>env_ok ws L kb w\<close>
  shows \<open>cwt ws (snd L) (sle_t ka kb w) \<and> cwidth ws (snd L) (sle_t ka kb w) = 1 \<and>
     (\<forall>vs. vs_ok ws vs \<longrightarrow> ceval ws (snd L) vs (CV ws vs L) (sle_t ka kb w) =
        of_bool (sint w (CV ws vs L ! ka) \<le> sint w (CV ws vs L ! kb)))\<close>
  using sle_t_sem[OF env_ref_ok[OF assms(1) vs0_ok] env_ref_ok[OF assms(2) vs0_ok]]
    sle_t_sem(3)[OF env_ref_ok[OF assms(1)] env_ref_ok[OF assms(2)]] assms
  by (simp add: env_ok_def)

subsection \<open>The binary operations\<close>

text \<open>The result of \<^verbatim>\<open>lower_bin\<close> for an operation rewritten by one push.\<close>
lemma bin1:
  assumes \<open>lok ws L\<close> \<open>lower_bin_m L op ka kb = (L', k)\<close> \<open>lower_bin_m L op ka kb = push_m L t w\<close>
    \<open>cwt ws (snd L) t\<close> \<open>cwidth ws (snd L) t = w\<close> \<open>w = op_width op (snd L ! ka) (snd L ! kb)\<close>
    \<open>\<And>vs. vs_ok ws vs \<Longrightarrow> ceval ws (snd L) vs (CV ws vs L) t =
       bin_sem op (snd L ! ka) (CV ws vs L ! ka) (snd L ! kb) (CV ws vs L ! kb)\<close>
  shows \<open>lext ws L L' \<and> k < length (fst L') \<and> snd L' ! k = op_width op (snd L ! ka) (snd L ! kb) \<and>
     (\<forall>vs. vs_ok ws vs \<longrightarrow> CV ws vs L' ! k = bin_sem op (snd L ! ka) (CV ws vs L ! ka) (snd L ! kb) (CV ws vs L ! kb))\<close>
proof -
  have p: \<open>push_m L t w = (L', k)\<close> using assms(2,3) by simp
  show ?thesis using push_correct[OF assms(1,4,5) p assms(7)] assms(6) by simp
qed

lemma lower_bin_correct:
  assumes EA: \<open>env_ok ws L ka wa\<close> and EB: \<open>env_ok ws L kb wb\<close>
    and eqw: \<open>op \<noteq> Op_Concat \<longrightarrow> wb = wa\<close>
    and R: \<open>lower_bin_m L op ka kb = (L', k)\<close>
    and B: \<open>length (fst L') < 2 ^ 64\<close>
  shows \<open>lext ws L L' \<and> k < length (fst L') \<and> snd L' ! k = op_width op wa wb \<and>
     (\<forall>vs. vs_ok ws vs \<longrightarrow> CV ws vs L' ! k = bin_sem op wa (CV ws vs L ! ka) wb (CV ws vs L ! kb))\<close>
proof -
  have L: \<open>lok ws L\<close> and wa: \<open>snd L ! ka = wa\<close> and wb: \<open>snd L ! kb = wb\<close> and wa1: \<open>1 \<le> wa\<close>
    and wa64: \<open>wa < 2 ^ 64\<close>
    using EA EB by (simp_all add: env_ok_def)
  have EBa: \<open>op \<noteq> Op_Concat \<Longrightarrow> env_ok ws L kb wa\<close> using EB eqw by simp
  note A = cr_env[OF EA] neg_t_env[OF EA] msb_t_env[OF EA] abs_t_env[OF EA]
    cr_env[OF EB] neg_t_env[OF EBa] msb_t_env[OF EBa] abs_t_env[OF EBa] slt_t_env[OF EA EBa] sle_t_env[OF EA EBa]
    slt_t_env[OF EBa EA] sle_t_env[OF EBa EA]
  have lta: \<open>\<And>vs. vs_ok ws vs \<Longrightarrow> CV ws vs L ! ka < 2 ^ wa\<close> by (rule env_lt[OF EA])
  have ltb: \<open>\<And>vs. op \<noteq> Op_Concat \<Longrightarrow> vs_ok ws vs \<Longrightarrow> CV ws vs L ! kb < 2 ^ wa\<close> by (rule env_lt[OF EBa])
  note B1 = bin1[OF L R, unfolded wa wb]
  show ?thesis
  proof (cases op)
    case Op_And
    show ?thesis by (rule B1[of \<open>CoreTerm_Bin BinOp_And (cr ka) (cr kb)\<close> wa])
        (simp_all add: Op_And lower_bin_m_def op_width_def wa wb A eqw)
  next
    case Op_Or
    show ?thesis by (rule B1[of \<open>CoreTerm_Bin BinOp_Or (cr ka) (cr kb)\<close> wa])
        (simp_all add: Op_Or lower_bin_m_def op_width_def wa wb A eqw)
  next
    case Op_Xor
    show ?thesis by (rule B1[of \<open>CoreTerm_Bin BinOp_Xor (cr ka) (cr kb)\<close> wa])
        (simp_all add: Op_Xor lower_bin_m_def op_width_def wa wb A eqw)
  next
    case Op_Nand
    show ?thesis by (rule B1[of \<open>CoreTerm_Not (CoreTerm_Bin BinOp_And (cr ka) (cr kb))\<close> wa])
        (simp_all add: Op_Nand lower_bin_m_def op_width_def wa wb A eqw)
  next
    case Op_Nor
    show ?thesis by (rule B1[of \<open>CoreTerm_Not (CoreTerm_Bin BinOp_Or (cr ka) (cr kb))\<close> wa])
        (simp_all add: Op_Nor lower_bin_m_def op_width_def wa wb A eqw)
  next
    case Op_Xnor
    show ?thesis by (rule B1[of \<open>CoreTerm_Not (CoreTerm_Bin BinOp_Xor (cr ka) (cr kb))\<close> wa])
        (simp_all add: Op_Xnor lower_bin_m_def op_width_def wa wb A eqw)
  next
    case Op_Comp
    show ?thesis by (rule B1[of \<open>CoreTerm_Bin BinOp_Eq (cr ka) (cr kb)\<close> 1])
        (simp_all add: Op_Comp lower_bin_m_def op_width_def wa wb A eqw)
  next
    case Op_Add
    show ?thesis by (rule B1[of \<open>CoreTerm_Bin BinOp_Add (cr ka) (cr kb)\<close> wa])
        (simp_all add: Op_Add lower_bin_m_def op_width_def wa wb A eqw)
  next
    case Op_Sub
    show ?thesis by (rule B1[of \<open>CoreTerm_Bin BinOp_Add (cr ka) (neg_t kb wa)\<close> wa])
        (simp_all add: Op_Sub lower_bin_m_def op_width_def wa wb A eqw sub_arith lta ltb)
  next
    case Op_Mul
    show ?thesis by (rule B1[of \<open>CoreTerm_Bin BinOp_Mul (cr ka) (cr kb)\<close> wa])
        (simp_all add: Op_Mul lower_bin_m_def op_width_def wa wb A eqw)
  next
    case Op_Udiv
    show ?thesis by (rule B1[of \<open>CoreTerm_Bin BinOp_Udiv (cr ka) (cr kb)\<close> wa])
        (simp_all add: Op_Udiv lower_bin_m_def op_width_def wa wb A eqw)
  next
    case Op_Urem
    show ?thesis by (rule B1[of \<open>CoreTerm_Bin BinOp_Urem (cr ka) (cr kb)\<close> wa])
        (simp_all add: Op_Urem lower_bin_m_def op_width_def wa wb A eqw)
  next
    case Op_Shl
    show ?thesis by (rule B1[of \<open>CoreTerm_Bin BinOp_Shl (cr ka) (cr kb)\<close> wa])
        (simp_all add: Op_Shl lower_bin_m_def op_width_def wa wb A eqw)
  next
    case Op_Lshr
    show ?thesis by (rule B1[of \<open>CoreTerm_Bin BinOp_Lshr (cr ka) (cr kb)\<close> wa])
        (simp_all add: Op_Lshr lower_bin_m_def op_width_def wa wb A eqw)
  next
    case Op_Ashr
    let ?t = \<open>CoreTerm_Ite (msb_t ka wa)
          (CoreTerm_Not (CoreTerm_Bin BinOp_Lshr (CoreTerm_Not (cr ka)) (cr kb)))
          (CoreTerm_Bin BinOp_Lshr (cr ka) (cr kb))\<close>
    have v: \<open>\<And>vs. vs_ok ws vs \<Longrightarrow> ceval ws (snd L) vs (CV ws vs L) ?t =
        bin_sem op wa (CV ws vs L ! ka) wb (CV ws vs L ! kb)\<close>
    proof -
      fix vs assume V: \<open>vs_ok ws vs\<close>
      have \<open>ceval ws (snd L) vs (CV ws vs L) ?t =
          (if sbit wa (CV ws vs L ! ka)
           then 2 ^ wa - 1 - (2 ^ wa - 1 - CV ws vs L ! ka) div 2 ^ (CV ws vs L ! kb)
           else CV ws vs L ! ka div 2 ^ (CV ws vs L ! kb))\<close>
        using A V eqw by (simp add: wa wb Op_Ashr)
      also have \<open>\<dots> = bin_sem Op_Ashr wa (CV ws vs L ! ka) wa (CV ws vs L ! kb)\<close>
        by (rule ashr_arith[OF wa1 lta[OF V]])
      finally show \<open>ceval ws (snd L) vs (CV ws vs L) ?t = bin_sem op wa (CV ws vs L ! ka) wb (CV ws vs L ! kb)\<close>
        using eqw Op_Ashr by simp
    qed
    show ?thesis
    proof (rule B1[of ?t wa])
      show \<open>lower_bin_m L op ka kb = push_m L ?t wa\<close> by (simp add: Op_Ashr lower_bin_m_def wa)
      show \<open>cwt ws (snd L) ?t\<close> using A eqw Op_Ashr by simp
      show \<open>cwidth ws (snd L) ?t = wa\<close> using A eqw Op_Ashr by simp
      show \<open>wa = op_width op wa wb\<close> by (simp add: Op_Ashr op_width_def)
    qed (rule v)
  next
    case Op_Concat
    show ?thesis by (rule B1[of \<open>CoreTerm_Bin BinOp_Concat (cr ka) (cr kb)\<close> \<open>wa + wb\<close>])
        (simp_all add: Op_Concat lower_bin_m_def op_width_def wa wb A)
  next
    case Op_Eq
    show ?thesis by (rule B1[of \<open>CoreTerm_Bin BinOp_Eq (cr ka) (cr kb)\<close> 1])
        (simp_all add: Op_Eq lower_bin_m_def op_width_def wa wb A eqw)
  next
    case Op_Distinct
    show ?thesis by (rule B1[of \<open>CoreTerm_Not (CoreTerm_Bin BinOp_Eq (cr ka) (cr kb))\<close> 1])
        (simp_all add: Op_Distinct lower_bin_m_def op_width_def wa wb A eqw)
  next
    case Op_Ult
    show ?thesis by (rule B1[of \<open>CoreTerm_Bin BinOp_Ult (cr ka) (cr kb)\<close> 1])
        (simp_all add: Op_Ult lower_bin_m_def op_width_def wa wb A eqw)
  next
    case Op_Ule
    show ?thesis by (rule B1[of \<open>CoreTerm_Not (CoreTerm_Bin BinOp_Ult (cr kb) (cr ka))\<close> 1])
        (simp_all add: Op_Ule lower_bin_m_def op_width_def wa wb A eqw)
  next
    case Op_Ugt
    show ?thesis by (rule B1[of \<open>CoreTerm_Bin BinOp_Ult (cr kb) (cr ka)\<close> 1])
        (simp_all add: Op_Ugt lower_bin_m_def op_width_def wa wb A eqw)
  next
    case Op_Uge
    show ?thesis by (rule B1[of \<open>CoreTerm_Not (CoreTerm_Bin BinOp_Ult (cr ka) (cr kb))\<close> 1])
        (simp_all add: Op_Uge lower_bin_m_def op_width_def wa wb A eqw)
  next
    case Op_Slt
    show ?thesis by (rule B1[of \<open>slt_t ka kb wa\<close> 1])
        (simp_all add: Op_Slt lower_bin_m_def op_width_def wa wb A eqw)
  next
    case Op_Sle
    show ?thesis by (rule B1[of \<open>sle_t ka kb wa\<close> 1])
        (simp_all add: Op_Sle lower_bin_m_def op_width_def wa wb A eqw)
  next
    case Op_Sgt
    show ?thesis by (rule B1[of \<open>slt_t kb ka wa\<close> 1])
        (simp_all add: Op_Sgt lower_bin_m_def op_width_def wa wb A eqw)
  next
    case Op_Sge
    show ?thesis by (rule B1[of \<open>sle_t kb ka wa\<close> 1])
        (simp_all add: Op_Sge lower_bin_m_def op_width_def wa wb A eqw)
  next
    case Op_Sdiv
    have wba: \<open>wb = wa\<close> using eqw Op_Sdiv by simp
    have ne: \<open>op \<noteq> Op_Concat\<close> using Op_Sdiv by simp
    note EB' = EBa[OF ne]
    let ?t1 = \<open>CoreTerm_Bin BinOp_Udiv (abs_t ka wa) (abs_t kb wa)\<close>
    obtain L1 q where p1: \<open>push_m L ?t1 wa = (L1, q)\<close> by (cases \<open>push_m L ?t1 wa\<close>)
    let ?t2 = \<open>CoreTerm_Ite (CoreTerm_Bin BinOp_Xor (msb_t ka wa) (msb_t kb wa)) (neg_t q wa) (cr q)\<close>
    have p2: \<open>push_m L1 ?t2 wa = (L', k)\<close> using R p1 by (simp add: Op_Sdiv lower_bin_m_def wa)
    have t1: \<open>cwt ws (snd L) ?t1\<close> \<open>cwidth ws (snd L) ?t1 = wa\<close>
      using abs_t_env[OF EA] abs_t_env[OF EB'] by simp_all
    define f where \<open>f = (\<lambda>vs. if CV ws vs L ! kb = 0 then 2 ^ wa - 1
                             else absv wa (CV ws vs L ! ka) div absv wa (CV ws vs L ! kb))\<close>
    have v1: \<open>\<And>vs. vs_ok ws vs \<Longrightarrow> ceval ws (snd L) vs (CV ws vs L) ?t1 = f vs\<close>
      using abs_t_env[OF EA] abs_t_env[OF EB'] udiv_absv[OF wa1 lta ltb[OF ne]]
      by (simp add: f_def)
    note P1 = push_correct[OF L t1 p1 v1]
    have L1: \<open>lok ws L1\<close> using P1 lext_lok by blast
    have EQ: \<open>env_ok ws L1 q wa\<close>
      using env_push[OF L t1 p1 wa1 wa64] P1 B pfx_length[OF pfx_push[OF p2]] by simp
    have EA1: \<open>env_ok ws L1 ka wa\<close> and EB1: \<open>env_ok ws L1 kb wa\<close> using env_lext[OF EA] env_lext[OF EB'] P1 by simp_all
    have t2: \<open>cwt ws (snd L1) ?t2\<close> \<open>cwidth ws (snd L1) ?t2 = wa\<close>
      using msb_t_env[OF EA1] msb_t_env[OF EB1] neg_t_env[OF EQ] cr_env[OF EQ] by simp_all
    have v2: \<open>\<And>vs. vs_ok ws vs \<Longrightarrow> ceval ws (snd L1) vs (CV ws vs L1) ?t2 =
        bin_sem Op_Sdiv wa (CV ws vs L ! ka) wb (CV ws vs L ! kb)\<close>
    proof -
      fix vs assume V: \<open>vs_ok ws vs\<close>
      have c: \<open>CV ws vs L1 ! ka = CV ws vs L ! ka\<close> \<open>CV ws vs L1 ! kb = CV ws vs L ! kb\<close> \<open>CV ws vs L1 ! q = f vs\<close>
        using env_CV[OF EA] env_CV[OF EB'] P1 V by simp_all
      have \<open>ceval ws (snd L1) vs (CV ws vs L1) ?t2 =
          (let q = f vs in if sbit wa (CV ws vs L ! ka) \<noteq> sbit wa (CV ws vs L ! kb) then negv wa q else q)\<close>
        using msb_t_env[OF EA1] msb_t_env[OF EB1] neg_t_env[OF EQ] cr_env[OF EQ] V c by (simp add: xor_bool Let_def)
      also have \<open>\<dots> = bin_sem Op_Sdiv wa (CV ws vs L ! ka) wa (CV ws vs L ! kb)\<close>
        unfolding f_def by (rule sdiv_arith[OF wa1 lta[OF V] ltb[OF ne V]])
      finally show \<open>ceval ws (snd L1) vs (CV ws vs L1) ?t2 = bin_sem Op_Sdiv wa (CV ws vs L ! ka) wb (CV ws vs L ! kb)\<close>
        by (simp add: wba)
    qed
    note P2 = push_correct[OF L1 t2 p2 v2]
    show ?thesis using P1 P2 lext_trans by (simp add: Op_Sdiv op_width_def) blast
  next
    case Op_Srem
    have wba: \<open>wb = wa\<close> using eqw Op_Srem by simp
    have ne: \<open>op \<noteq> Op_Concat\<close> using Op_Srem by simp
    note EB' = EBa[OF ne]
    let ?t1 = \<open>CoreTerm_Bin BinOp_Urem (abs_t ka wa) (abs_t kb wa)\<close>
    obtain L1 r where p1: \<open>push_m L ?t1 wa = (L1, r)\<close> by (cases \<open>push_m L ?t1 wa\<close>)
    let ?t2 = \<open>CoreTerm_Ite (msb_t ka wa) (neg_t r wa) (cr r)\<close>
    have p2: \<open>push_m L1 ?t2 wa = (L', k)\<close> using R p1 by (simp add: Op_Srem lower_bin_m_def wa)
    have t1: \<open>cwt ws (snd L) ?t1\<close> \<open>cwidth ws (snd L) ?t1 = wa\<close>
      using abs_t_env[OF EA] abs_t_env[OF EB'] by simp_all
    define f where \<open>f = (\<lambda>vs. if CV ws vs L ! kb = 0 then absv wa (CV ws vs L ! ka)
                             else absv wa (CV ws vs L ! ka) mod absv wa (CV ws vs L ! kb))\<close>
    have v1: \<open>\<And>vs. vs_ok ws vs \<Longrightarrow> ceval ws (snd L) vs (CV ws vs L) ?t1 = f vs\<close>
      using abs_t_env[OF EA] abs_t_env[OF EB'] urem_absv[OF wa1 lta ltb[OF ne]] by (simp add: f_def)
    note P1 = push_correct[OF L t1 p1 v1]
    have L1: \<open>lok ws L1\<close> using P1 lext_lok by blast
    have ER: \<open>env_ok ws L1 r wa\<close>
      using env_push[OF L t1 p1 wa1 wa64] P1 B pfx_length[OF pfx_push[OF p2]] by simp
    have EA1: \<open>env_ok ws L1 ka wa\<close> using env_lext[OF EA] P1 by simp
    have t2: \<open>cwt ws (snd L1) ?t2\<close> \<open>cwidth ws (snd L1) ?t2 = wa\<close>
      using msb_t_env[OF EA1] neg_t_env[OF ER] cr_env[OF ER] by simp_all
    have v2: \<open>\<And>vs. vs_ok ws vs \<Longrightarrow> ceval ws (snd L1) vs (CV ws vs L1) ?t2 =
        bin_sem Op_Srem wa (CV ws vs L ! ka) wb (CV ws vs L ! kb)\<close>
    proof -
      fix vs assume V: \<open>vs_ok ws vs\<close>
      have c: \<open>CV ws vs L1 ! ka = CV ws vs L ! ka\<close> \<open>CV ws vs L1 ! r = f vs\<close>
        using env_CV[OF EA] P1 V by simp_all
      have \<open>ceval ws (snd L1) vs (CV ws vs L1) ?t2 =
          (let r = f vs in if sbit wa (CV ws vs L ! ka) then negv wa r else r)\<close>
        using msb_t_env[OF EA1] neg_t_env[OF ER] cr_env[OF ER] V c by (simp add: Let_def)
      also have \<open>\<dots> = bin_sem Op_Srem wa (CV ws vs L ! ka) wa (CV ws vs L ! kb)\<close>
        unfolding f_def by (rule srem_arith[OF wa1 lta[OF V] ltb[OF ne V]])
      finally show \<open>ceval ws (snd L1) vs (CV ws vs L1) ?t2 = bin_sem Op_Srem wa (CV ws vs L ! ka) wb (CV ws vs L ! kb)\<close>
        by (simp add: wba)
    qed
    note P2 = push_correct[OF L1 t2 p2 v2]
    show ?thesis using P1 P2 lext_trans by (simp add: Op_Srem op_width_def) blast
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
    have t1: \<open>cwt ws (snd L) ?t1\<close> \<open>cwidth ws (snd L) ?t1 = wa\<close>
      using abs_t_env[OF EA] abs_t_env[OF EB'] by simp_all
    define f where \<open>f = (\<lambda>vs. if CV ws vs L ! kb = 0 then absv wa (CV ws vs L ! ka)
                             else absv wa (CV ws vs L ! ka) mod absv wa (CV ws vs L ! kb))\<close>
    have v1: \<open>\<And>vs. vs_ok ws vs \<Longrightarrow> ceval ws (snd L) vs (CV ws vs L) ?t1 = f vs\<close>
      using abs_t_env[OF EA] abs_t_env[OF EB'] urem_absv[OF wa1 lta ltb[OF ne]] by (simp add: f_def)
    note P1 = push_correct[OF L t1 p1 v1]
    have L1: \<open>lok ws L1\<close> using P1 lext_lok by blast
    have EU: \<open>env_ok ws L1 u wa\<close>
      using env_push[OF L t1 p1 wa1 wa64] P1 B pfx_length[OF pfx_push[OF p2]] pfx_length[OF pfx_push[OF p3]] by simp
    have t2: \<open>cwt ws (snd L1) (neg_t u wa)\<close> \<open>cwidth ws (snd L1) (neg_t u wa) = wa\<close>
      using neg_t_env[OF EU] by simp_all
    have v2: \<open>\<And>vs. vs_ok ws vs \<Longrightarrow> ceval ws (snd L1) vs (CV ws vs L1) (neg_t u wa) = negv wa (f vs)\<close>
      using neg_t_env[OF EU] P1 by simp
    note P2 = push_correct[OF L1 t2 p2 v2]
    have L2: \<open>lok ws L2\<close> using P2 lext_lok by blast
    have ENU: \<open>env_ok ws L2 nu wa\<close>
      using env_push[OF L1 t2 p2 wa1 wa64] P2 B pfx_length[OF pfx_push[OF p3]] by simp
    have EU2: \<open>env_ok ws L2 u wa\<close> using env_lext[OF EU] P2 by simp
    have EA1: \<open>env_ok ws L1 ka wa\<close> and EB1: \<open>env_ok ws L1 kb wa\<close> using env_lext[OF EA] env_lext[OF EB'] P1 by simp_all
    have EA2: \<open>env_ok ws L2 ka wa\<close> and EB2: \<open>env_ok ws L2 kb wa\<close> using env_lext[OF EA1] env_lext[OF EB1] P2 by simp_all
    have LL2: \<open>lext ws L L2\<close> using P1 P2 lext_trans by blast
    have t3: \<open>cwt ws (snd L2) ?t3\<close> \<open>cwidth ws (snd L2) ?t3 = wa\<close>
      using msb_t_env[OF EA2] msb_t_env[OF EB2] cr_env[OF EU2] cr_env[OF ENU] cr_env[OF EB2] by simp_all
    have v3: \<open>\<And>vs. vs_ok ws vs \<Longrightarrow> ceval ws (snd L2) vs (CV ws vs L2) ?t3 =
        bin_sem Op_Smod wa (CV ws vs L ! ka) wb (CV ws vs L ! kb)\<close>
    proof -
      fix vs assume V: \<open>vs_ok ws vs\<close>
      have c: \<open>CV ws vs L2 ! ka = CV ws vs L ! ka\<close> \<open>CV ws vs L2 ! kb = CV ws vs L ! kb\<close>
        \<open>CV ws vs L2 ! u = f vs\<close> \<open>CV ws vs L2 ! nu = negv wa (f vs)\<close>
        using env_CV[OF EA LL2] env_CV[OF EB' LL2] env_CV[OF EU] P1 P2 V by simp_all
      have \<open>ceval ws (snd L2) vs (CV ws vs L2) ?t3 =
          (let u = f vs in
           if u = 0 then u
           else if sbit wa (CV ws vs L ! ka)
                then (if sbit wa (CV ws vs L ! kb) then negv wa u else (negv wa u + CV ws vs L ! kb) mod 2 ^ wa)
                else (if sbit wa (CV ws vs L ! kb) then (u + CV ws vs L ! kb) mod 2 ^ wa else u))\<close>
        using msb_t_env[OF EA2] msb_t_env[OF EB2] cr_env[OF EU2] cr_env[OF ENU] cr_env[OF EB2] V c
        by (simp add: Let_def bits_nat_replicate_False)
      also have \<open>\<dots> = bin_sem Op_Smod wa (CV ws vs L ! ka) wa (CV ws vs L ! kb)\<close>
        unfolding f_def by (rule smod_arith[OF wa1 lta[OF V] ltb[OF ne V]])
      finally show \<open>ceval ws (snd L2) vs (CV ws vs L2) ?t3 = bin_sem Op_Smod wa (CV ws vs L ! ka) wb (CV ws vs L ! kb)\<close>
        by (simp add: wba)
    qed
    note P3 = push_correct[OF L2 t3 p3 v3]
    show ?thesis using P1 P2 P3 lext_trans by (simp add: Op_Smod op_width_def) blast
  qed
qed

subsection \<open>Terms\<close>

text \<open>The bounds the rewriting of a term needs: every index and every width fits in a word.\<close>
definition bnd :: \<open>lst \<Rightarrow> bool\<close> where
  \<open>bnd L \<equiv> length (fst L) < 2 ^ 64 \<and> (\<forall>w \<in> set (snd L). w < 2 ^ 64)\<close>

lemma bnd_pfx: \<open>pfx L L' \<Longrightarrow> bnd L' \<Longrightarrow> bnd L\<close>
  using pfx_length[of L L'] pfx_set[of L L'] by (auto simp add: bnd_def)

text \<open>\<open>dm\<close> maps the definitions of widths \<open>ds\<close> to core definitions of the same widths; under
  \<open>vs\<close>, those have the values \<open>dv\<close>.\<close>
definition dm_ok :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> lst \<Rightarrow> bool\<close> where
  \<open>dm_ok ds dm L \<equiv> length dm = length ds \<and> (\<forall>j < length ds. dm ! j < length (fst L) \<and> snd L ! (dm ! j) = ds ! j)\<close>

definition dmv :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> lst \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool\<close> where
  \<open>dmv ws ds dm L vs dv \<equiv> length dv = length ds \<and> (\<forall>j < length ds. CV ws vs L ! (dm ! j) = dv ! j)\<close>

lemma dm_ok_lext: \<open>lok ws L \<Longrightarrow> dm_ok ds dm L \<Longrightarrow> lext ws L L' \<Longrightarrow> dm_ok ds dm L'\<close>
  using lext_length[of ws L L'] lext_nth_snd[of ws L L'] by (fastforce simp add: dm_ok_def)

lemma dmv_lext: \<open>dm_ok ds dm L \<Longrightarrow> lext ws L L' \<Longrightarrow> dmv ws ds dm L vs dv \<Longrightarrow> dmv ws ds dm L' vs dv\<close>
  using lext_nth_CV[of ws L L'] by (fastforce simp add: dm_ok_def dmv_def)

lemma wt_width_pos: \<open>wt ws ds t \<Longrightarrow> 1 \<le> width ws ds t\<close>
proof (induction t)
  case (Term_Bin op a b)
  then show ?case by (cases op) simp_all
next
  case (Term_Repeat i a)
  then show ?case by (simp add: Suc_le_eq)
qed (simp_all add: Suc_le_eq)

text \<open>A term rewritten by one push on top of the rewriting of its operand.\<close>
lemma un_push:
  assumes IH: \<open>env_ok ws L1 ka wa \<and> lext ws L L1 \<and>
      (\<forall>vs dv. vs_ok ws vs \<and> dmv ws ds dm L vs dv \<longrightarrow> CV ws vs L1 ! ka = ea vs dv)\<close>
    and t: \<open>cwt ws (snd L1) t\<close> \<open>cwidth ws (snd L1) t = w\<close> and p: \<open>push_m L1 t w = (L', k)\<close>
    and v: \<open>\<And>vs. vs_ok ws vs \<Longrightarrow> ceval ws (snd L1) vs (CV ws vs L1) t = f (CV ws vs L1 ! ka)\<close>
    and w1: \<open>1 \<le> w\<close> and B: \<open>bnd L'\<close>
  shows \<open>env_ok ws L' k w \<and> lext ws L L' \<and>
     (\<forall>vs dv. vs_ok ws vs \<and> dmv ws ds dm L vs dv \<longrightarrow> CV ws vs L' ! k = f (ea vs dv))\<close>
proof -
  have L1: \<open>lok ws L1\<close> using IH by (simp add: env_ok_def)
  note P = push_correct[OF L1 t p v]
  have \<open>snd L' ! k \<in> set (snd L')\<close> using P lok_length[OF lext_lok[of ws L1 L']] by (intro nth_mem) simp
  then have w64: \<open>w < 2 ^ 64\<close> using P B by (auto simp add: bnd_def)
  have E: \<open>env_ok ws L' k w\<close> using env_push[OF L1 t p w1 w64] B by (simp add: bnd_def)
  have X: \<open>lext ws L L'\<close> using IH P lext_trans by blast
  have V: \<open>\<forall>vs dv. vs_ok ws vs \<and> dmv ws ds dm L vs dv \<longrightarrow> CV ws vs L' ! k = f (ea vs dv)\<close>
  proof (intro allI impI)
    fix vs dv assume H: \<open>vs_ok ws vs \<and> dmv ws ds dm L vs dv\<close>
    have \<open>CV ws vs L1 ! ka = ea vs dv\<close> using IH H by blast
    then show \<open>CV ws vs L' ! k = f (ea vs dv)\<close> using P H by simp
  qed
  show ?thesis using E X V by simp
qed

text \<open>The concatenation of two extractions of one definition, as built for the rotations.\<close>
lemma concat_extract_env:
  assumes \<open>env_ok ws L k w\<close> \<open>la \<le> ha\<close> \<open>ha < w\<close> \<open>lb \<le> hb\<close> \<open>hb < w\<close>
  shows \<open>cwt ws (snd L) (CoreTerm_Bin BinOp_Concat (CoreTerm_Extract (word_of_nat ha) (word_of_nat la) (cr k))
            (CoreTerm_Extract (word_of_nat hb) (word_of_nat lb) (cr k))) \<and>
     cwidth ws (snd L) (CoreTerm_Bin BinOp_Concat (CoreTerm_Extract (word_of_nat ha) (word_of_nat la) (cr k))
            (CoreTerm_Extract (word_of_nat hb) (word_of_nat lb) (cr k))) = (ha - la + 1) + (hb - lb + 1) \<and>
     (\<forall>vs. ceval ws (snd L) vs (CV ws vs L) (CoreTerm_Bin BinOp_Concat
            (CoreTerm_Extract (word_of_nat ha) (word_of_nat la) (cr k))
            (CoreTerm_Extract (word_of_nat hb) (word_of_nat lb) (cr k))) =
        ((CV ws vs L ! k div 2 ^ la) mod 2 ^ (ha - la + 1)) * 2 ^ (hb - lb + 1) +
        (CV ws vs L ! k div 2 ^ lb) mod 2 ^ (hb - lb + 1))\<close>
proof -
  have w64: \<open>w < 2 ^ 64\<close> using assms(1) by (simp add: env_ok_def)
  have u: \<open>unat (word_of_nat ha :: 64 word) = ha\<close> \<open>unat (word_of_nat la :: 64 word) = la\<close>
    \<open>unat (word_of_nat hb :: 64 word) = hb\<close> \<open>unat (word_of_nat lb :: 64 word) = lb\<close>
    using assms(2-5) w64 by (simp_all add: unat_wn)
  show ?thesis using cr_env[OF assms(1)] assms(2-5) by (simp add: u)
qed

lemma bits_nat_replicate_True': \<open>bits_nat (replicate n True) = 2 ^ n - 1\<close>
  using bits_nat_replicate_True[of n] by simp

text \<open>The loop of \<^verbatim>\<open>lower\<close> for \<open>repeat\<close>: after \<open>j\<close> iterations, the current definition holds \<open>j\<close> copies.\<close>
lemma repeat_loop:
  assumes EA: \<open>env_ok ws L ka wa\<close>
  shows \<open>lext ws L Lj \<Longrightarrow> kj < length (fst Lj) \<Longrightarrow> snd Lj ! kj = acc0 \<Longrightarrow> acc0 = wa * j \<Longrightarrow>
    (\<forall>vs. vs_ok ws vs \<longrightarrow> CV ws vs Lj ! kj = repeat_val wa j (CV ws vs L ! ka)) \<Longrightarrow>
    foldl (repeat_step ka wa) (Lj, kj, acc0) js = (L3, k3, acc) \<Longrightarrow> bnd L3 \<Longrightarrow>
    lext ws Lj L3 \<and> k3 < length (fst L3) \<and> snd L3 ! k3 = wa * (j + length js) \<and>
    (\<forall>vs. vs_ok ws vs \<longrightarrow> CV ws vs L3 ! k3 = repeat_val wa (j + length js) (CV ws vs L ! ka))\<close>
proof (induction js arbitrary: Lj kj j acc0)
  case Nil
  then show ?case using lext_refl lext_lok by auto
next
  case (Cons x js)
  let ?t = \<open>CoreTerm_Bin BinOp_Concat (cr ka) (cr kj)\<close>
  obtain Lj' kj' where p: \<open>push_m Lj ?t (acc0 + wa) = (Lj', kj')\<close> by (cases \<open>push_m Lj ?t (acc0 + wa)\<close>)
  have f: \<open>foldl (repeat_step ka wa) (Lj', kj', acc0 + wa) js = (L3, k3, acc)\<close>
    using Cons.prems(6) p by (simp add: repeat_step_def)
  have acc: \<open>acc0 + wa = wa * Suc j\<close> using Cons.prems(4) by (simp add: mult_Suc)
  have Lj: \<open>lok ws Lj\<close> using Cons.prems(1) lext_lok by blast
  have B': \<open>bnd Lj'\<close> using bnd_pfx[OF repeat_fold_pfx[OF f] Cons.prems(7)] .
  have kj64: \<open>kj < 2 ^ 64\<close> using Cons.prems(2) B' pfx_length[OF pfx_push[OF p]] by (simp add: bnd_def)
  have EAj: \<open>env_ok ws Lj ka wa\<close> using env_lext[OF EA Cons.prems(1)] .
  have kjl: \<open>kj < length (snd Lj)\<close> using Cons.prems(2) lok_length[OF Lj] by simp
  have t: \<open>cwt ws (snd Lj) ?t\<close> \<open>cwidth ws (snd Lj) ?t = acc0 + wa\<close>
    using cr_env[OF EAj] cr_wt[OF kjl kj64] cr_width[OF kj64] Cons.prems(3) by (simp_all add: add.commute)
  have v: \<open>\<And>vs. vs_ok ws vs \<Longrightarrow> ceval ws (snd Lj) vs (CV ws vs Lj) ?t =
      CV ws vs Lj ! ka * 2 ^ (wa * j) + CV ws vs Lj ! kj\<close>
    using cr_env[OF EAj] cr_eval[OF kj64] cr_width[OF kj64] Cons.prems(3,4) by simp
  note P = push_correct[OF Lj t p v]
  have v': \<open>\<forall>vs. vs_ok ws vs \<longrightarrow> CV ws vs Lj' ! kj' = repeat_val wa (Suc j) (CV ws vs L ! ka)\<close>
    using P Cons.prems(5) env_CV[OF EA Cons.prems(1)] by simp
  have \<open>lext ws L Lj'\<close> using Cons.prems(1) P lext_trans by blast
  note IH = Cons.IH[OF this _ _ acc v' f Cons.prems(7)]
  show ?case using IH P lext_trans by simp blast
qed

lemma lower_m_correct:
  assumes \<open>wt ws ds t\<close> \<open>lok ws L\<close> \<open>dm_ok ds dm L\<close> \<open>lower_m ws dm L t = (L', k)\<close> \<open>bnd L'\<close>
  shows \<open>env_ok ws L' k (width ws ds t) \<and> lext ws L L' \<and>
     (\<forall>vs dv. vs_ok ws vs \<and> dmv ws ds dm L vs dv \<longrightarrow> CV ws vs L' ! k = eval ws ds vs dv t)\<close>
  using assms
proof (induction t arbitrary: L L' k)
  case (Term_Const bs)
  note L = Term_Const.prems(2)
  have p: \<open>push_m L (CoreTerm_Const bs) (length bs) = (L', k)\<close> using Term_Const.prems(4) by simp
  have t: \<open>cwt ws (snd L) (CoreTerm_Const bs)\<close> \<open>cwidth ws (snd L) (CoreTerm_Const bs) = length bs\<close> by simp_all
  have v: \<open>\<And>vs. vs_ok ws vs \<Longrightarrow> ceval ws (snd L) vs (CV ws vs L) (CoreTerm_Const bs) = bits_nat bs\<close> by simp
  note P = push_correct[OF L t p v]
  have \<open>snd L' ! k \<in> set (snd L')\<close> using P lok_length[OF lext_lok[of ws L L']] by (intro nth_mem) simp
  then have w64: \<open>length bs < 2 ^ 64\<close> using P Term_Const.prems(5) by (auto simp add: bnd_def)
  have \<open>1 \<le> length bs\<close> using Term_Const.prems(1) by (simp add: Suc_le_eq)
  then have \<open>env_ok ws L' k (length bs)\<close>
    using env_push[OF L t p _ w64] Term_Const.prems(5) by (simp add: bnd_def)
  then show ?case using P by simp
next
  case (Term_Var i)
  note L = Term_Var.prems(2)
  have wt: \<open>unat i < length ws\<close> \<open>1 \<le> ws ! unat i\<close> using Term_Var.prems(1) by simp_all
  have p: \<open>push_m L (CoreTerm_Var i) (ws ! unat i) = (L', k)\<close> using Term_Var.prems(4) by simp
  have t: \<open>cwt ws (snd L) (CoreTerm_Var i)\<close> \<open>cwidth ws (snd L) (CoreTerm_Var i) = ws ! unat i\<close> using wt by simp_all
  have v: \<open>\<And>vs. vs_ok ws vs \<Longrightarrow> ceval ws (snd L) vs (CV ws vs L) (CoreTerm_Var i) = vs ! unat i\<close> by simp
  note P = push_correct[OF L t p v]
  have \<open>snd L' ! k \<in> set (snd L')\<close> using P lok_length[OF lext_lok[of ws L L']] by (intro nth_mem) simp
  then have w64: \<open>ws ! unat i < 2 ^ 64\<close> using P Term_Var.prems(5) by (auto simp add: bnd_def)
  have \<open>env_ok ws L' k (ws ! unat i)\<close>
    using env_push[OF L t p wt(2) w64] Term_Var.prems(5) by (simp add: bnd_def)
  then show ?case using P by simp
next
  case (Term_Ref j)
  have R: \<open>L' = L\<close> \<open>k = dm ! unat j\<close> using Term_Ref.prems(4) by simp_all
  have wt: \<open>unat j < length ds\<close> \<open>1 \<le> ds ! unat j\<close> using Term_Ref.prems(1) by simp_all
  have k: \<open>k < length (fst L)\<close> \<open>snd L ! k = ds ! unat j\<close>
    using Term_Ref.prems(3) wt(1) by (simp_all add: dm_ok_def R)
  have \<open>snd L ! k \<in> set (snd L)\<close> using k(1) lok_length[OF Term_Ref.prems(2)] by (simp add: nth_mem)
  then have \<open>env_ok ws L' k (ds ! unat j)\<close>
    using Term_Ref.prems(2,5) k wt(2) by (auto simp add: env_ok_def bnd_def R)
  then show ?case using lext_refl[OF Term_Ref.prems(2)] k wt(1) by (auto simp add: R dmv_def)
next
  case (Term_Not a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  have p: \<open>push_m L1 (CoreTerm_Not (cr ka)) (snd L1 ! ka) = (L', k)\<close> using Term_Not.prems(4) a by simp
  have B1: \<open>bnd L1\<close> using bnd_pfx[OF pfx_push[OF p] Term_Not.prems(5)] .
  have wta: \<open>wt ws ds a\<close> using Term_Not.prems(1) by simp
  note IH = Term_Not.IH[OF wta Term_Not.prems(2,3) a B1]
  have EA: \<open>env_ok ws L1 ka (width ws ds a)\<close> using IH by simp
  have wa: \<open>snd L1 ! ka = width ws ds a\<close> using EA by (simp add: env_ok_def)
  note A = cr_env[OF EA]
  have t: \<open>cwt ws (snd L1) (CoreTerm_Not (cr ka))\<close> \<open>cwidth ws (snd L1) (CoreTerm_Not (cr ka)) = width ws ds a\<close>
    using A by simp_all
  have v: \<open>\<And>vs. vs_ok ws vs \<Longrightarrow> ceval ws (snd L1) vs (CV ws vs L1) (CoreTerm_Not (cr ka)) =
      (\<lambda>x. 2 ^ width ws ds a - 1 - x) (CV ws vs L1 ! ka)\<close> using A by simp
  show ?case
    using un_push[where f = \<open>\<lambda>x. 2 ^ width ws ds a - 1 - x\<close>, OF IH t p[unfolded wa] v wt_width_pos[OF wta] Term_Not.prems(5)]
    by simp
next
  case (Term_Neg a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  have p: \<open>push_m L1 (neg_t ka (snd L1 ! ka)) (snd L1 ! ka) = (L', k)\<close> using Term_Neg.prems(4) a by simp
  have B1: \<open>bnd L1\<close> using bnd_pfx[OF pfx_push[OF p] Term_Neg.prems(5)] .
  have wta: \<open>wt ws ds a\<close> using Term_Neg.prems(1) by simp
  note IH = Term_Neg.IH[OF wta Term_Neg.prems(2,3) a B1]
  have EA: \<open>env_ok ws L1 ka (width ws ds a)\<close> using IH by simp
  have wa: \<open>snd L1 ! ka = width ws ds a\<close> using EA by (simp add: env_ok_def)
  note A = neg_t_env[OF EA]
  have t: \<open>cwt ws (snd L1) (neg_t ka (width ws ds a))\<close> \<open>cwidth ws (snd L1) (neg_t ka (width ws ds a)) = width ws ds a\<close>
    using A by simp_all
  have v: \<open>\<And>vs. vs_ok ws vs \<Longrightarrow> ceval ws (snd L1) vs (CV ws vs L1) (neg_t ka (width ws ds a)) =
      negv (width ws ds a) (CV ws vs L1 ! ka)\<close> using A by simp
  show ?case
    using un_push[where f = \<open>negv (width ws ds a)\<close>, OF IH t p[unfolded wa] v wt_width_pos[OF wta] Term_Neg.prems(5)]
    by (simp add: negv_def)
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
  have L1: \<open>lok ws L1\<close> and X1: \<open>lext ws L L1\<close> using IHa lext_lok by blast+
  note IHb = Term_Bin.IH(2)[OF wt(2) L1 dm_ok_lext[OF Term_Bin.prems(2,3) X1] b B2]
  have X2: \<open>lext ws L1 L2\<close> using IHb by blast
  have EA1: \<open>env_ok ws L1 ka (width ws ds a)\<close> using IHa by blast
  have EA: \<open>env_ok ws L2 ka (width ws ds a)\<close> using env_lext[OF EA1 X2] .
  have EB: \<open>env_ok ws L2 kb (width ws ds b)\<close> using IHb by blast
  note C = lower_bin_correct[OF EA EB wt(3) R Term_Bin.prems(5)[unfolded bnd_def, THEN conjunct1]]
  have X3: \<open>lext ws L2 L'\<close> using C by blast
  have wk: \<open>snd L' ! k = width ws ds (Term_Bin op a b)\<close> using C by (simp add: width_Bin_op op_width_def)
  have \<open>snd L' ! k \<in> set (snd L')\<close> using C lok_length[OF lext_lok[OF X3]] by (intro nth_mem) simp
  then have E: \<open>env_ok ws L' k (width ws ds (Term_Bin op a b))\<close>
    using C wk Term_Bin.prems(5) wt_width_pos[OF Term_Bin.prems(1)] lext_lok[OF X3]
    by (auto simp add: env_ok_def bnd_def)
  have X: \<open>lext ws L L'\<close> using X1 X2 X3 lext_trans by blast
  have V: \<open>\<forall>vs dv. vs_ok ws vs \<and> dmv ws ds dm L vs dv \<longrightarrow> CV ws vs L' ! k = eval ws ds vs dv (Term_Bin op a b)\<close>
  proof (intro allI impI)
    fix vs dv assume H: \<open>vs_ok ws vs \<and> dmv ws ds dm L vs dv\<close>
    have a1: \<open>CV ws vs L1 ! ka = eval ws ds vs dv a\<close> using IHa H by blast
    have ca: \<open>CV ws vs L2 ! ka = eval ws ds vs dv a\<close> using a1 env_CV[OF EA1 X2] by simp
    have cb: \<open>CV ws vs L2 ! kb = eval ws ds vs dv b\<close>
      using IHb H dmv_lext[OF Term_Bin.prems(3) X1] by blast
    show \<open>CV ws vs L' ! k = eval ws ds vs dv (Term_Bin op a b)\<close> using C H ca cb by simp
  qed
  show ?case using E X V by simp
next
  case (Term_Extract hi lo a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  let ?t = \<open>CoreTerm_Extract hi lo (cr ka)\<close> and ?w = \<open>unat hi - unat lo + 1\<close>
  have p: \<open>push_m L1 ?t ?w = (L', k)\<close> using Term_Extract.prems(4) a by simp
  have B1: \<open>bnd L1\<close> using bnd_pfx[OF pfx_push[OF p] Term_Extract.prems(5)] .
  have wt: \<open>wt ws ds a\<close> \<open>unat lo \<le> unat hi\<close> \<open>unat hi < width ws ds a\<close> using Term_Extract.prems(1) by simp_all
  note IH = Term_Extract.IH[OF wt(1) Term_Extract.prems(2,3) a B1]
  have EA: \<open>env_ok ws L1 ka (width ws ds a)\<close> using IH by simp
  note A = cr_env[OF EA]
  have t: \<open>cwt ws (snd L1) ?t\<close> \<open>cwidth ws (snd L1) ?t = ?w\<close> using A wt(2,3) by simp_all
  have v: \<open>\<And>vs. vs_ok ws vs \<Longrightarrow> ceval ws (snd L1) vs (CV ws vs L1) ?t =
      (\<lambda>x. (x div 2 ^ unat lo) mod 2 ^ ?w) (CV ws vs L1 ! ka)\<close> using A by simp
  show ?case
    using un_push[where f = \<open>\<lambda>x. (x div 2 ^ unat lo) mod 2 ^ ?w\<close>, OF IH t p v _ Term_Extract.prems(5)] by simp
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
  have EA: \<open>env_ok ws L1 ka (width ws ds a)\<close> and X1: \<open>lext ws L L1\<close> using IH by simp_all
  have wa: \<open>?wa = width ws ds a\<close> using EA by (simp add: env_ok_def)
  have L1: \<open>lok ws L1\<close> using EA by (simp add: env_ok_def)
  have t0: \<open>cwt ws (snd L1) (CoreTerm_Const [])\<close> \<open>cwidth ws (snd L1) (CoreTerm_Const []) = 0\<close> by simp_all
  have v0: \<open>\<And>vs. vs_ok ws vs \<Longrightarrow> ceval ws (snd L1) vs (CV ws vs L1) (CoreTerm_Const []) = 0\<close> by simp
  note P0 = push_correct[OF L1 t0 p v0]
  have X2: \<open>lext ws L1 L2\<close> using P0 by simp
  have inv: \<open>\<forall>vs. vs_ok ws vs \<longrightarrow> CV ws vs L2 ! k0 = repeat_val ?wa 0 (CV ws vs L1 ! ka)\<close> using P0 by simp
  have EA': \<open>env_ok ws L1 ka ?wa\<close> using EA wa by simp
  have k0: \<open>k0 < length (fst L2)\<close> \<open>snd L2 ! k0 = 0\<close> using P0 by simp_all
  have acc: \<open>(0 :: nat) = ?wa * 0\<close> by simp
  note LP = repeat_loop[OF EA' X2 k0 acc inv f Term_Repeat.prems(5)[unfolded R]]
  have X3: \<open>lext ws L2 L3\<close> and k3: \<open>k3 < length (fst L3)\<close> and w3: \<open>snd L3 ! k3 = ?wa * unat i\<close>
    and V3: \<open>\<forall>vs. vs_ok ws vs \<longrightarrow> CV ws vs L3 ! k3 = repeat_val ?wa (unat i) (CV ws vs L1 ! ka)\<close>
    using LP P0 by simp_all
  have wk: \<open>snd L' ! k = width ws ds (Term_Repeat i a)\<close> using w3 wa R by (simp add: mult.commute)
  have \<open>snd L3 ! k3 \<in> set (snd L3)\<close> using k3 lok_length[OF lext_lok[OF X3]] by (intro nth_mem) simp
  then have E: \<open>env_ok ws L' k (width ws ds (Term_Repeat i a))\<close>
    using wk k3 Term_Repeat.prems(5) wt_width_pos[OF Term_Repeat.prems(1)] lext_lok[OF X3]
    by (auto simp add: env_ok_def bnd_def R)
  have X: \<open>lext ws L L'\<close> using X1 X2 X3 lext_trans R by blast
  have V: \<open>\<forall>vs dv. vs_ok ws vs \<and> dmv ws ds dm L vs dv \<longrightarrow> CV ws vs L' ! k = eval ws ds vs dv (Term_Repeat i a)\<close>
  proof (intro allI impI)
    fix vs dv assume H: \<open>vs_ok ws vs \<and> dmv ws ds dm L vs dv\<close>
    have \<open>CV ws vs L1 ! ka = eval ws ds vs dv a\<close> using IH H by blast
    then show \<open>CV ws vs L' ! k = eval ws ds vs dv (Term_Repeat i a)\<close> using V3 H wa R by simp
  qed
  show ?case using E X V by simp
next
  case (Term_ZeroExtend i a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  let ?t = \<open>CoreTerm_Bin BinOp_Concat (CoreTerm_Const (replicate (unat i) False)) (cr ka)\<close>
  have p: \<open>push_m L1 ?t (snd L1 ! ka + unat i) = (L', k)\<close> using Term_ZeroExtend.prems(4) a by (simp add: Let_def)
  have B1: \<open>bnd L1\<close> using bnd_pfx[OF pfx_push[OF p] Term_ZeroExtend.prems(5)] .
  have wta: \<open>wt ws ds a\<close> using Term_ZeroExtend.prems(1) by simp
  note IH = Term_ZeroExtend.IH[OF wta Term_ZeroExtend.prems(2,3) a B1]
  have EA: \<open>env_ok ws L1 ka (width ws ds a)\<close> using IH by simp
  have wa: \<open>snd L1 ! ka = width ws ds a\<close> using EA by (simp add: env_ok_def)
  note A = cr_env[OF EA]
  have t: \<open>cwt ws (snd L1) ?t\<close> \<open>cwidth ws (snd L1) ?t = width ws ds a + unat i\<close> using A by (simp_all add: add.commute)
  have v: \<open>\<And>vs. vs_ok ws vs \<Longrightarrow> ceval ws (snd L1) vs (CV ws vs L1) ?t = (\<lambda>x. x) (CV ws vs L1 ! ka)\<close>
    using A by (simp add: bits_nat_replicate_False)
  show ?case
    using un_push[where f = \<open>\<lambda>x. x\<close>, OF IH t p[unfolded wa] v _ Term_ZeroExtend.prems(5)] wt_width_pos[OF wta] by simp
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
  have EA: \<open>env_ok ws L1 ka ?wa\<close> using IH by simp
  have wa: \<open>snd L1 ! ka = ?wa\<close> using EA by (simp add: env_ok_def)
  have p: \<open>push_m L1 ?t (?wa + unat i) = (L', k)\<close> using p0 unfolding wa .
  note A = cr_env[OF EA] msb_t_env[OF EA]
  have t: \<open>cwt ws (snd L1) ?t\<close> \<open>cwidth ws (snd L1) ?t = ?wa + unat i\<close> by (simp_all add: A add.commute)
  have v: \<open>\<And>vs. vs_ok ws vs \<Longrightarrow> ceval ws (snd L1) vs (CV ws vs L1) ?t =
      (\<lambda>x. to_bv (?wa + unat i) (sint ?wa x)) (CV ws vs L1 ! ka)\<close>
  proof -
    fix vs assume V: \<open>vs_ok ws vs\<close>
    have \<open>ceval ws (snd L1) vs (CV ws vs L1) ?t =
        (if sbit ?wa (CV ws vs L1 ! ka) then 2 ^ unat i - 1 else 0) * 2 ^ ?wa + CV ws vs L1 ! ka\<close>
      using V by (simp add: A bits_nat_replicate_False bits_nat_replicate_True')
    also have \<open>\<dots> = to_bv (?wa + unat i) (sint ?wa (CV ws vs L1 ! ka))\<close>
      using sext_arith[OF wt_width_pos[OF wta] env_lt[OF EA V]] .
    finally show \<open>ceval ws (snd L1) vs (CV ws vs L1) ?t = (\<lambda>x. to_bv (?wa + unat i) (sint ?wa x)) (CV ws vs L1 ! ka)\<close>
      by simp
  qed
  show ?case
    using un_push[where f = \<open>\<lambda>x. to_bv (?wa + unat i) (sint ?wa x)\<close>, OF IH t p v _ Term_SignExtend.prems(5)]
      wt_width_pos[OF wta] by simp
next
  case (Term_RotateLeft i a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  let ?wa = \<open>width ws ds a\<close> and ?r = \<open>unat i mod width ws ds a\<close>
  have wta: \<open>wt ws ds a\<close> using Term_RotateLeft.prems(1) by simp
  show ?case
  proof (cases \<open>unat i mod snd L1 ! ka = 0\<close>)
    case True
    have R: \<open>L' = L1\<close> \<open>k = ka\<close> using Term_RotateLeft.prems(4) a True by (simp_all add: Let_def)
    note IH = Term_RotateLeft.IH[OF wta Term_RotateLeft.prems(2,3) a Term_RotateLeft.prems(5)[unfolded R]]
    have EA: \<open>env_ok ws L1 ka ?wa\<close> using IH by simp
    have r0: \<open>?r = 0\<close> using True EA by (simp add: env_ok_def)
    have V: \<open>\<forall>vs dv. vs_ok ws vs \<and> dmv ws ds dm L vs dv \<longrightarrow> CV ws vs L' ! k = eval ws ds vs dv (Term_RotateLeft i a)\<close>
    proof (intro allI impI)
      fix vs dv assume H: \<open>vs_ok ws vs \<and> dmv ws ds dm L vs dv\<close>
      have e: \<open>CV ws vs L1 ! ka = eval ws ds vs dv a\<close> using IH H by blast
      have \<open>eval ws ds vs dv a < 2 ^ ?wa\<close> using env_lt[OF EA conjunct1[OF H]] e by simp
      then show \<open>CV ws vs L' ! k = eval ws ds vs dv (Term_RotateLeft i a)\<close> using e by (simp add: R r0 Let_def)
    qed
    show ?thesis using IH V by (simp add: R)
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
    have EA: \<open>env_ok ws L1 ka ?wa\<close> using IH by simp
    have wa: \<open>snd L1 ! ka = ?wa\<close> and wa1: \<open>1 \<le> ?wa\<close> using EA by (simp_all add: env_ok_def)
    have p: \<open>push_m L1 ?t ?wa = (L', k)\<close> using p0 unfolding wa .
    have r: \<open>1 \<le> ?r\<close> \<open>?r < ?wa\<close> using False wa wa1 by simp_all
    have e1: \<open>?wa - 1 - ?r - 0 + 1 = ?wa - ?r\<close> and e2: \<open>?wa - 1 - (?wa - ?r) + 1 = ?r\<close> using r by arith+
    have z: \<open>word_of_nat 0 = (0 :: 64 word)\<close> by simp
    have sc: \<open>0 \<le> ?wa - 1 - ?r\<close> \<open>?wa - 1 - ?r < ?wa\<close> \<open>?wa - ?r \<le> ?wa - 1\<close> \<open>?wa - 1 < ?wa\<close> using r wa1 by arith+
    note F = concat_extract_env[where la = 0 and ha = \<open>?wa - 1 - ?r\<close> and lb = \<open>?wa - ?r\<close> and hb = \<open>?wa - 1\<close>,
        OF EA sc, unfolded z e1 e2]
    note F1 = F[THEN conjunct1]
    note F2 = F[THEN conjunct2, THEN conjunct1]
    note F3 = F[THEN conjunct2, THEN conjunct2, THEN spec]
    have t2: \<open>cwidth ws (snd L1) ?t = ?wa\<close> using r(2) by (subst F2) simp
    have v: \<open>\<And>vs. vs_ok ws vs \<Longrightarrow> ceval ws (snd L1) vs (CV ws vs L1) ?t =
        (\<lambda>x. (x mod 2 ^ (?wa - ?r)) * 2 ^ ?r + x div 2 ^ (?wa - ?r)) (CV ws vs L1 ! ka)\<close>
    proof -
      fix vs assume V: \<open>vs_ok ws vs\<close>
      show \<open>ceval ws (snd L1) vs (CV ws vs L1) ?t =
          (\<lambda>x. (x mod 2 ^ (?wa - ?r)) * 2 ^ ?r + x div 2 ^ (?wa - ?r)) (CV ws vs L1 ! ka)\<close>
        by (subst F3) (simp add: rotl_arith[OF r(2) env_lt[OF EA V]])
    qed
    show ?thesis
      using un_push[where f = \<open>\<lambda>x. (x mod 2 ^ (?wa - ?r)) * 2 ^ ?r + x div 2 ^ (?wa - ?r)\<close>, OF IH F1 t2 p v wa1 Term_RotateLeft.prems(5)]
      by (simp add: Let_def)
  qed
next
  case (Term_RotateRight i a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  let ?wa = \<open>width ws ds a\<close> and ?r = \<open>unat i mod width ws ds a\<close>
  have wta: \<open>wt ws ds a\<close> using Term_RotateRight.prems(1) by simp
  show ?case
  proof (cases \<open>unat i mod snd L1 ! ka = 0\<close>)
    case True
    have R: \<open>L' = L1\<close> \<open>k = ka\<close> using Term_RotateRight.prems(4) a True by (simp_all add: Let_def)
    note IH = Term_RotateRight.IH[OF wta Term_RotateRight.prems(2,3) a Term_RotateRight.prems(5)[unfolded R]]
    have EA: \<open>env_ok ws L1 ka ?wa\<close> using IH by simp
    have r0: \<open>?r = 0\<close> using True EA by (simp add: env_ok_def)
    have V: \<open>\<forall>vs dv. vs_ok ws vs \<and> dmv ws ds dm L vs dv \<longrightarrow> CV ws vs L' ! k = eval ws ds vs dv (Term_RotateRight i a)\<close>
    proof (intro allI impI)
      fix vs dv assume H: \<open>vs_ok ws vs \<and> dmv ws ds dm L vs dv\<close>
      have e: \<open>CV ws vs L1 ! ka = eval ws ds vs dv a\<close> using IH H by blast
      have \<open>eval ws ds vs dv a < 2 ^ ?wa\<close> using env_lt[OF EA conjunct1[OF H]] e by simp
      then show \<open>CV ws vs L' ! k = eval ws ds vs dv (Term_RotateRight i a)\<close> using e by (simp add: R r0 Let_def)
    qed
    show ?thesis using IH V by (simp add: R)
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
    have EA: \<open>env_ok ws L1 ka ?wa\<close> using IH by simp
    have wa: \<open>snd L1 ! ka = ?wa\<close> and wa1: \<open>1 \<le> ?wa\<close> using EA by (simp_all add: env_ok_def)
    have p: \<open>push_m L1 ?t ?wa = (L', k)\<close> using p0 unfolding wa .
    have r: \<open>1 \<le> ?r\<close> \<open>?r < ?wa\<close> using False wa wa1 by simp_all
    have e1: \<open>?r - 1 - 0 + 1 = ?r\<close> and e2: \<open>?wa - 1 - ?r + 1 = ?wa - ?r\<close> using r by arith+
    have z: \<open>word_of_nat 0 = (0 :: 64 word)\<close> by simp
    have sc: \<open>0 \<le> ?r - 1\<close> \<open>?r - 1 < ?wa\<close> \<open>?r \<le> ?wa - 1\<close> \<open>?wa - 1 < ?wa\<close> using r wa1 by arith+
    note F = concat_extract_env[where la = 0 and ha = \<open>?r - 1\<close> and lb = ?r and hb = \<open>?wa - 1\<close>,
        OF EA sc, unfolded z e1 e2]
    note F1 = F[THEN conjunct1]
    note F2 = F[THEN conjunct2, THEN conjunct1]
    note F3 = F[THEN conjunct2, THEN conjunct2, THEN spec]
    have t2: \<open>cwidth ws (snd L1) ?t = ?wa\<close> using r(2) by (subst F2) simp
    have v: \<open>\<And>vs. vs_ok ws vs \<Longrightarrow> ceval ws (snd L1) vs (CV ws vs L1) ?t =
        (\<lambda>x. (x mod 2 ^ ?r) * 2 ^ (?wa - ?r) + x div 2 ^ ?r) (CV ws vs L1 ! ka)\<close>
    proof -
      fix vs assume V: \<open>vs_ok ws vs\<close>
      show \<open>ceval ws (snd L1) vs (CV ws vs L1) ?t =
          (\<lambda>x. (x mod 2 ^ ?r) * 2 ^ (?wa - ?r) + x div 2 ^ ?r) (CV ws vs L1 ! ka)\<close>
        by (subst F3) (simp add: rotr_arith[OF r(2) env_lt[OF EA V]])
    qed
    show ?thesis
      using un_push[where f = \<open>\<lambda>x. (x mod 2 ^ ?r) * 2 ^ (?wa - ?r) + x div 2 ^ ?r\<close>, OF IH F1 t2 p v wa1 Term_RotateRight.prems(5)]
      by (simp add: Let_def)
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
  have L1: \<open>lok ws L1\<close> and X1: \<open>lext ws L L1\<close> using IHc lext_lok by blast+
  note IHa = Term_Ite.IH(2)[OF wt(2) L1 dm_ok_lext[OF Term_Ite.prems(2,3) X1] a B2]
  have L2: \<open>lok ws L2\<close> and X2: \<open>lext ws L1 L2\<close> using IHa lext_lok by blast+
  note IHb = Term_Ite.IH(3)[OF wt(3) L2 dm_ok_lext[OF L1 dm_ok_lext[OF Term_Ite.prems(2,3) X1] X2] b B3]
  have L3: \<open>lok ws L3\<close> and X3: \<open>lext ws L2 L3\<close> using IHb lext_lok by blast+
  have EC1: \<open>env_ok ws L1 kc 1\<close> using IHc wt(4) by simp
  have EC2: \<open>env_ok ws L2 kc 1\<close> using env_lext[OF EC1 X2] .
  have EC: \<open>env_ok ws L3 kc 1\<close> using env_lext[OF EC2 X3] .
  have EA2: \<open>env_ok ws L2 ka (width ws ds a)\<close> using IHa by simp
  have EA: \<open>env_ok ws L3 ka (width ws ds a)\<close> using env_lext[OF EA2 X3] .
  have EB: \<open>env_ok ws L3 kb (width ws ds a)\<close> using IHb wt(5) by simp
  have wa: \<open>snd L3 ! ka = width ws ds a\<close> using EA by (simp add: env_ok_def)
  note A = cr_env[OF EC] cr_env[OF EA] cr_env[OF EB]
  have t: \<open>cwt ws (snd L3) ?t\<close> \<open>cwidth ws (snd L3) ?t = width ws ds a\<close> using A by simp_all
  have v: \<open>\<And>vs. vs_ok ws vs \<Longrightarrow> ceval ws (snd L3) vs (CV ws vs L3) ?t =
      (if CV ws vs L3 ! kc = 1 then CV ws vs L3 ! ka else CV ws vs L3 ! kb)\<close> using A by simp
  note P = push_correct[OF L3 t p[unfolded wa] v]
  have X4: \<open>lext ws L3 L'\<close> using P by simp
  have \<open>snd L' ! k \<in> set (snd L')\<close> using P lok_length[OF lext_lok[OF X4]] by (intro nth_mem) simp
  then have E: \<open>env_ok ws L' k (width ws ds (Term_Ite c a b))\<close>
    using P Term_Ite.prems(5) wt_width_pos[OF wt(2)] lext_lok[OF X4] by (auto simp add: env_ok_def bnd_def)
  have X: \<open>lext ws L L'\<close> using X1 X2 X3 X4 lext_trans by blast
  have V: \<open>\<forall>vs dv. vs_ok ws vs \<and> dmv ws ds dm L vs dv \<longrightarrow> CV ws vs L' ! k = eval ws ds vs dv (Term_Ite c a b)\<close>
  proof (intro allI impI)
    fix vs dv assume H: \<open>vs_ok ws vs \<and> dmv ws ds dm L vs dv\<close>
    have c1: \<open>CV ws vs L1 ! kc = eval ws ds vs dv c\<close> using IHc H by blast
    have cc: \<open>CV ws vs L3 ! kc = eval ws ds vs dv c\<close> using c1 env_CV[OF EC1 X2] env_CV[OF EC2 X3] by simp
    have H1: \<open>dmv ws ds dm L1 vs dv\<close> using dmv_lext[OF Term_Ite.prems(3) X1] H by blast
    have a2: \<open>CV ws vs L2 ! ka = eval ws ds vs dv a\<close> using IHa H H1 by blast
    have ca: \<open>CV ws vs L3 ! ka = eval ws ds vs dv a\<close> using a2 env_CV[OF EA2 X3] by simp
    have H2: \<open>dmv ws ds dm L2 vs dv\<close> using dmv_lext[OF dm_ok_lext[OF Term_Ite.prems(2,3) X1] X2 H1] .
    have cb: \<open>CV ws vs L3 ! kb = eval ws ds vs dv b\<close> using IHb H H2 by blast
    show \<open>CV ws vs L' ! k = eval ws ds vs dv (Term_Ite c a b)\<close> using P H cc ca cb by simp
  qed
  show ?case using E X V by simp
qed

subsection \<open>Problems\<close>

text \<open>Definitions of the extended language, in order.\<close>
lemma def_widths_append: \<open>def_widths ws ds (xs @ ys) = def_widths ws (def_widths ws ds xs) ys\<close>
  by (induction xs arbitrary: ds) simp_all

lemma def_values_append:
  \<open>def_values ws ds vs dv (xs @ ys) = def_values ws (def_widths ws ds xs) vs (def_values ws ds vs dv xs) ys\<close>
  by (induction xs arbitrary: ds dv) simp_all

lemma defs_wt_append: \<open>defs_wt ws ds (xs @ ys) = (defs_wt ws ds xs \<and> defs_wt ws (def_widths ws ds xs) ys)\<close>
  by (induction xs arbitrary: ds) simp_all

lemma def_widths_length: \<open>length (def_widths ws ds xs) = length ds + length xs\<close>
  by (induction xs arbitrary: ds) simp_all

lemma def_values_length: \<open>length (def_values ws ds vs dv xs) = length dv + length xs\<close>
  by (induction xs arbitrary: ds dv) simp_all

lemma def_widths_take_Suc:
  \<open>j < length D \<Longrightarrow> def_widths ws [] (take (Suc j) D) =
     def_widths ws [] (take j D) @ [width ws (def_widths ws [] (take j D)) (D ! j)]\<close>
  by (simp add: take_Suc_conv_app_nth def_widths_append)

lemma def_values_take_Suc:
  \<open>j < length D \<Longrightarrow> def_values ws [] vs [] (take (Suc j) D) =
     def_values ws [] vs [] (take j D) @
     [eval ws (def_widths ws [] (take j D)) vs (def_values ws [] vs [] (take j D)) (D ! j)]\<close>
  by (simp add: take_Suc_conv_app_nth def_values_append)

lemma defs_wt_nth: \<open>defs_wt ws [] D \<Longrightarrow> j < length D \<Longrightarrow> wt ws (def_widths ws [] (take j D)) (D ! j)\<close>
  using defs_wt_append[of ws \<open>[]\<close> \<open>take j D\<close> \<open>D ! j # drop (Suc j) D\<close>] by (simp add: id_take_nth_drop[symmetric])

lemma def_widths_prefix: \<open>\<exists>e. def_widths ws ds xs = ds @ e\<close>
proof (induction xs arbitrary: ds)
  case Nil
  show ?case by simp
next
  case (Cons d dd)
  obtain e where \<open>def_widths ws (ds @ [width ws ds d]) dd = (ds @ [width ws ds d]) @ e\<close> using Cons.IH by blast
  then show ?case by simp
qed

lemma def_values_prefix: \<open>\<exists>e. def_values ws ds vs dv xs = dv @ e\<close>
proof (induction xs arbitrary: ds dv)
  case Nil
  show ?case by simp
next
  case (Cons d dd)
  obtain e where \<open>def_values ws (ds @ [width ws ds d]) vs (dv @ [eval ws ds vs dv d]) dd = (dv @ [eval ws ds vs dv d]) @ e\<close>
    using Cons.IH by blast
  then show ?case by simp
qed

text \<open>A well-sorted term keeps its width and value when later definitions are appended.\<close>
lemma wt_width_append: \<open>wt ws ds t \<Longrightarrow> width ws (ds @ e) t = width ws ds t\<close>
proof (induction t)
  case (Term_Bin op a b)
  then show ?case by (cases op) simp_all
qed (simp_all add: nth_append)

lemma wt_eval_append:
  \<open>wt ws ds t \<Longrightarrow> length dv = length ds \<Longrightarrow> eval ws (ds @ e) vs (dv @ e') t = eval ws ds vs dv t\<close>
  by (induction t) (simp_all add: nth_append wt_width_append)

lemma wt_append: \<open>wt ws ds t \<Longrightarrow> wt ws (ds @ e) t\<close>
  by (induction t) (simp_all add: nth_append wt_width_append)

text \<open>The loop of \<^verbatim>\<open>lower_problem\<close> over the definitions: after \<open>j\<close> iterations, \<open>dm\<close> maps the first \<open>j\<close>
  definitions to core definitions of their widths and values.\<close>
definition ldefs_inv :: \<open>Problem \<Rightarrow> nat \<Rightarrow> lst \<times> nat list \<Rightarrow> bool\<close> where
  \<open>ldefs_inv p j X \<equiv>
     let ws = var_widths p; D = Problem_defs p in
     lok ws (fst X) \<and> dm_ok (def_widths ws [] (take j D)) (snd X) (fst X) \<and>
     (\<forall>vs. vs_ok ws vs \<longrightarrow> dmv ws (def_widths ws [] (take j D)) (snd X) (fst X) vs (def_values ws [] vs [] (take j D)))\<close>

lemma ldefs_fold_pfx: \<open>foldl (ldefs_step p) (L, dm) js = (L', dm') \<Longrightarrow> pfx L L'\<close>
proof (induction js arbitrary: L dm)
  case Nil
  then show ?case by (simp add: pfx_refl)
next
  case (Cons j js)
  obtain L1 k where a: \<open>lower_m (var_widths p) dm L (Problem_defs p ! j) = (L1, k)\<close>
    by (cases \<open>lower_m (var_widths p) dm L (Problem_defs p ! j)\<close>)
  have \<open>foldl (ldefs_step p) (L1, dm @ [k]) js = (L', dm')\<close> using Cons.prems a by (simp add: ldefs_step_def)
  then show ?case using Cons.IH lower_m_pfx[OF a] pfx_trans by blast
qed

lemma ldefs_loop:
  assumes \<open>defs_wt (var_widths p) [] (Problem_defs p)\<close> \<open>j \<le> length (Problem_defs p)\<close>
  shows \<open>foldl (ldefs_step p) (([], []), []) [0..<j] = (L', dm') \<Longrightarrow> bnd L' \<Longrightarrow> ldefs_inv p j (L', dm')\<close>
  using assms(2)
proof (induction j arbitrary: L' dm')
  case 0
  have R0: \<open>L' = ([], [])\<close> \<open>dm' = []\<close> using "0.prems"(1) by simp_all
  show ?case by (simp add: R0 ldefs_inv_def lok_def dm_ok_def dmv_def)
next
  case (Suc j)
  let ?ws = \<open>var_widths p\<close> and ?D = \<open>Problem_defs p\<close>
  obtain L dm where f: \<open>foldl (ldefs_step p) (([], []), []) [0..<j] = (L, dm)\<close>
    by (cases \<open>foldl (ldefs_step p) (([], []), []) [0..<j]\<close>)
  obtain L1 k where a: \<open>lower_m ?ws dm L (?D ! j) = (L1, k)\<close> by (cases \<open>lower_m ?ws dm L (?D ! j)\<close>)
  have R: \<open>L' = L1\<close> \<open>dm' = dm @ [k]\<close> using Suc.prems(1) f a by (simp_all add: ldefs_step_def)
  have B: \<open>bnd L\<close> using bnd_pfx[OF lower_m_pfx[OF a]] Suc.prems(2) R by simp
  have jl: \<open>j < length ?D\<close> and jle: \<open>j \<le> length ?D\<close> using Suc.prems(3) by simp_all
  note I = Suc.IH[OF f B jle, unfolded ldefs_inv_def Let_def, simplified]
  note C = lower_m_correct[OF defs_wt_nth[OF assms(1) jl] _ _ a Suc.prems(2)[unfolded R(1)]]
  have L: \<open>lok ?ws L\<close> and D: \<open>dm_ok (def_widths ?ws [] (take j ?D)) dm L\<close> using I by simp_all
  note C' = C[OF L D]
  have E: \<open>env_ok ?ws L1 k (width ?ws (def_widths ?ws [] (take j ?D)) (?D ! j))\<close> and X: \<open>lext ?ws L L1\<close>
    using C' by simp_all
  have lenD: \<open>length dm = j\<close> using D jle by (simp add: dm_ok_def def_widths_length)
  have D': \<open>dm_ok (def_widths ?ws [] (take (Suc j) ?D)) (dm @ [k]) L1\<close>
    using dm_ok_lext[OF L D X] E lenD by (auto simp add: dm_ok_def def_widths_take_Suc[OF jl] nth_append env_ok_def def_widths_length)
  have V': \<open>\<forall>vs. vs_ok ?ws vs \<longrightarrow> dmv ?ws (def_widths ?ws [] (take (Suc j) ?D)) (dm @ [k]) L1 vs
      (def_values ?ws [] vs [] (take (Suc j) ?D))\<close>
  proof (intro allI impI)
    fix vs assume V: \<open>vs_ok ?ws vs\<close>
    have M: \<open>dmv ?ws (def_widths ?ws [] (take j ?D)) dm L vs (def_values ?ws [] vs [] (take j ?D))\<close>
      using I V by simp
    have M1: \<open>dmv ?ws (def_widths ?ws [] (take j ?D)) dm L1 vs (def_values ?ws [] vs [] (take j ?D))\<close>
      using dmv_lext[OF D X M] .
    have val: \<open>CV ?ws vs L1 ! k = eval ?ws (def_widths ?ws [] (take j ?D)) vs (def_values ?ws [] vs [] (take j ?D)) (?D ! j)\<close>
      using C' V M by blast
    show \<open>dmv ?ws (def_widths ?ws [] (take (Suc j) ?D)) (dm @ [k]) L1 vs (def_values ?ws [] vs [] (take (Suc j) ?D))\<close>
      using M1 val lenD jl by (auto simp add: dmv_def def_widths_take_Suc[OF jl] def_values_take_Suc[OF jl] nth_append def_values_length def_widths_length)
  qed
  show ?case using E D' V' R by (simp add: ldefs_inv_def Let_def env_ok_def)
qed

text \<open>The loop over the assertions: each core assertion is a reference to a core definition of width 1
  whose value is the value of the assertion.\<close>
definition lasserts_inv :: \<open>Problem \<Rightarrow> nat list \<Rightarrow> lst \<Rightarrow> nat \<Rightarrow> lst \<times> CoreTerm list \<Rightarrow> bool\<close> where
  \<open>lasserts_inv p dm L1 i X \<equiv>
     let ws = var_widths p; D = Problem_defs p; A = Problem_asserts p;
         ds = def_widths ws [] D in
     lext ws L1 (fst X) \<and> length (snd X) = i \<and>
     (\<forall>n < i. \<exists>k. snd X ! n = cr k \<and> env_ok ws (fst X) k 1 \<and>
        (\<forall>vs. vs_ok ws vs \<longrightarrow> CV ws vs (fst X) ! k = eval ws ds vs (def_values ws [] vs [] D) (A ! n)))\<close>

lemma lasserts_fold_pfx: \<open>foldl (lasserts_step p dm) (L, cs) js = (L', cs') \<Longrightarrow> pfx L L'\<close>
proof (induction js arbitrary: L cs)
  case Nil
  then show ?case by (simp add: pfx_refl)
next
  case (Cons j js)
  obtain L1 k where a: \<open>lower_m (var_widths p) dm L (Problem_asserts p ! j) = (L1, k)\<close>
    by (cases \<open>lower_m (var_widths p) dm L (Problem_asserts p ! j)\<close>)
  have \<open>foldl (lasserts_step p dm) (L1, cs @ [cr k]) js = (L', cs')\<close> using Cons.prems a by (simp add: lasserts_step_def)
  then show ?case using Cons.IH lower_m_pfx[OF a] pfx_trans by blast
qed

lemma lasserts_loop:
  assumes \<open>problem_wt p\<close> \<open>i \<le> length (Problem_asserts p)\<close>
    and I1: \<open>ldefs_inv p (length (Problem_defs p)) (L1, dm)\<close>
  shows \<open>foldl (lasserts_step p dm) (L1, []) [0..<i] = (L', cs') \<Longrightarrow> bnd L' \<Longrightarrow> lasserts_inv p dm L1 i (L', cs')\<close>
  using assms(2)
proof (induction i arbitrary: L' cs')
  case 0
  have R0: \<open>L' = L1\<close> \<open>cs' = []\<close> using "0.prems"(1) by simp_all
  show ?case using I1 lext_refl by (simp add: R0 lasserts_inv_def ldefs_inv_def Let_def)
next
  case (Suc i)
  let ?ws = \<open>var_widths p\<close> and ?D = \<open>Problem_defs p\<close> and ?A = \<open>Problem_asserts p\<close>
  let ?ds = \<open>def_widths ?ws [] ?D\<close>
  obtain L cs where f: \<open>foldl (lasserts_step p dm) (L1, []) [0..<i] = (L, cs)\<close>
    by (cases \<open>foldl (lasserts_step p dm) (L1, []) [0..<i]\<close>)
  obtain L2 k where a: \<open>lower_m ?ws dm L (?A ! i) = (L2, k)\<close> by (cases \<open>lower_m ?ws dm L (?A ! i)\<close>)
  have R: \<open>L' = L2\<close> \<open>cs' = cs @ [cr k]\<close> using Suc.prems(1) f a by (simp_all add: lasserts_step_def)
  have B: \<open>bnd L\<close> using bnd_pfx[OF lower_m_pfx[OF a]] Suc.prems(2) R by simp
  have il: \<open>i < length ?A\<close> and ile: \<open>i \<le> length ?A\<close> using Suc.prems(3) by simp_all
  note I = Suc.IH[OF f B ile]
  have wtA: \<open>wt ?ws ?ds (?A ! i)\<close> \<open>width ?ws ?ds (?A ! i) = 1\<close>
    using assms(1) il by (simp_all add: problem_wt_def Let_def)
  have L1: \<open>lok ?ws L1\<close> and D1: \<open>dm_ok ?ds dm L1\<close> using I1 by (simp_all add: ldefs_inv_def Let_def)
  have X1: \<open>lext ?ws L1 L\<close> using I by (simp add: lasserts_inv_def Let_def)
  have L: \<open>lok ?ws L\<close> using lext_lok[OF X1] .
  have D: \<open>dm_ok ?ds dm L\<close> using dm_ok_lext[OF L1 D1 X1] .
  note C = lower_m_correct[OF wtA(1) L D a Suc.prems(2)[unfolded R(1)]]
  have E: \<open>env_ok ?ws L2 k 1\<close> and X: \<open>lext ?ws L L2\<close> using C wtA(2) by simp_all
  have old: \<open>\<forall>n < i. \<exists>k. cs ! n = cr k \<and> env_ok ?ws L2 k 1 \<and>
      (\<forall>vs. vs_ok ?ws vs \<longrightarrow> CV ?ws vs L2 ! k = eval ?ws ?ds vs (def_values ?ws [] vs [] ?D) (?A ! n))\<close>
  proof (intro allI impI)
    fix n assume \<open>n < i\<close>
    then obtain k' where k': \<open>cs ! n = cr k'\<close> \<open>env_ok ?ws L k' 1\<close>
      \<open>\<forall>vs. vs_ok ?ws vs \<longrightarrow> CV ?ws vs L ! k' = eval ?ws ?ds vs (def_values ?ws [] vs [] ?D) (?A ! n)\<close>
      using I by (auto simp add: lasserts_inv_def Let_def)
    show \<open>\<exists>k. cs ! n = cr k \<and> env_ok ?ws L2 k 1 \<and>
        (\<forall>vs. vs_ok ?ws vs \<longrightarrow> CV ?ws vs L2 ! k = eval ?ws ?ds vs (def_values ?ws [] vs [] ?D) (?A ! n))\<close>
      using k' env_lext[OF k'(2) X] env_CV[OF k'(2) X] by auto
  qed
  have new: \<open>\<forall>vs. vs_ok ?ws vs \<longrightarrow> CV ?ws vs L2 ! k = eval ?ws ?ds vs (def_values ?ws [] vs [] ?D) (?A ! i)\<close>
  proof (intro allI impI)
    fix vs assume V: \<open>vs_ok ?ws vs\<close>
    have M1: \<open>dmv ?ws ?ds dm L1 vs (def_values ?ws [] vs [] ?D)\<close> using I1 V by (simp add: ldefs_inv_def Let_def)
    have M: \<open>dmv ?ws ?ds dm L vs (def_values ?ws [] vs [] ?D)\<close> using dmv_lext[OF D1 X1 M1] .
    show \<open>CV ?ws vs L2 ! k = eval ?ws ?ds vs (def_values ?ws [] vs [] ?D) (?A ! i)\<close> using C V M by blast
  qed
  have len: \<open>length cs = i\<close> using I by (simp add: lasserts_inv_def Let_def)
  have \<open>lext ?ws L1 L2\<close> using X1 X lext_trans by blast
  then show ?case using old new E len R by (auto simp add: lasserts_inv_def Let_def nth_append less_Suc_eq)
qed

text \<open>The result of \<^verbatim>\<open>lower_problem\<close> as the results of its two loops.\<close>
definition ldefs_res :: \<open>Problem \<Rightarrow> lst \<times> nat list\<close> where
  \<open>ldefs_res p \<equiv> foldl (ldefs_step p) (([], []), []) [0..<length (Problem_defs p)]\<close>

definition lasserts_res :: \<open>Problem \<Rightarrow> lst \<times> CoreTerm list\<close> where
  \<open>lasserts_res p \<equiv> foldl (lasserts_step p (snd (ldefs_res p))) (fst (ldefs_res p), []) [0..<length (Problem_asserts p)]\<close>

lemma lower_problem_m_eq:
  \<open>lower_problem_m p = make_CoreProblem (Problem_widths p) (fst (fst (lasserts_res p))) (snd (lasserts_res p))\<close>
  by (simp add: lower_problem_m_def ldefs_res_def lasserts_res_def split_def Let_def)

lemma ldefs_res_pfx: \<open>pfx (fst (ldefs_res p)) (fst (lasserts_res p))\<close>
  unfolding lasserts_res_def by (metis lasserts_fold_pfx prod.collapse)

text \<open>The values of the variables of a model are bounded by their widths.\<close>
lemma vs_ok_of_assignment: \<open>is_assignment p m \<Longrightarrow> vs_ok (var_widths p) (map bits_nat m)\<close>
proof -
  assume \<open>is_assignment p m\<close>
  then have \<open>var_widths p = map length m\<close> by (simp add: is_assignment_def)
  then show ?thesis by (simp add: vs_ok_def bits_nat_lt)
qed

theorem lower_problem_correct:
  assumes \<open>problem_wt p\<close> \<open>bnd (fst (lasserts_res p))\<close>
  shows \<open>cproblem_wt (lower_problem_m p)\<close> \<open>cis_model (lower_problem_m p) m = is_model p m\<close>
proof -
  let ?ws = \<open>var_widths p\<close> and ?D = \<open>Problem_defs p\<close> and ?A = \<open>Problem_asserts p\<close>
  let ?ds = \<open>def_widths ?ws [] ?D\<close>
  obtain L1 dm where d: \<open>ldefs_res p = (L1, dm)\<close> by (cases \<open>ldefs_res p\<close>)
  obtain L2 cs where a: \<open>lasserts_res p = (L2, cs)\<close> by (cases \<open>lasserts_res p\<close>)
  have B2: \<open>bnd L2\<close> using assms(2) a by simp
  have B1: \<open>bnd L1\<close> using bnd_pfx[OF ldefs_res_pfx[of p]] assms(2) d a by simp
  have I1: \<open>ldefs_inv p (length ?D) (L1, dm)\<close>
    using ldefs_loop[OF _ _ _ B1] assms(1) d by (simp add: problem_wt_def Let_def ldefs_res_def)
  have I2: \<open>lasserts_inv p dm L1 (length ?A) (L2, cs)\<close>
    using lasserts_loop[OF assms(1) _ I1 _ B2] a d by (simp add: lasserts_res_def)
  have X12: \<open>lext ?ws L1 L2\<close> using I2 by (simp add: lasserts_inv_def Let_def)
  have L2: \<open>lok ?ws L2\<close> using lext_lok[OF X12] .
  have q: \<open>lower_problem_m p = make_CoreProblem (Problem_widths p) (fst L2) cs\<close>
    using lower_problem_m_eq a by simp
  have cws: \<open>cvar_widths (lower_problem_m p) = ?ws\<close> by (simp add: q cvar_widths_def var_widths_def)
  have cds: \<open>cdef_widths ?ws [] (fst L2) = snd L2\<close> using L2 by (simp add: lok_def)
  have len: \<open>length cs = length ?A\<close> using I2 by (simp add: lasserts_inv_def Let_def)
  have each: \<open>\<And>n. n < length ?A \<Longrightarrow> \<exists>k. cs ! n = cr k \<and> env_ok ?ws L2 k 1 \<and>
      (\<forall>vs. vs_ok ?ws vs \<longrightarrow> CV ?ws vs L2 ! k = eval ?ws ?ds vs (def_values ?ws [] vs [] ?D) (?A ! n))\<close>
    using I2 by (simp add: lasserts_inv_def Let_def)
  show \<open>cproblem_wt (lower_problem_m p)\<close>
  proof -
    have \<open>\<forall>t \<in> set cs. cwt ?ws (snd L2) t \<and> cwidth ?ws (snd L2) t = 1\<close>
    proof
      fix t assume \<open>t \<in> set cs\<close>
      then obtain n where n: \<open>n < length ?A\<close> \<open>t = cs ! n\<close> using len by (auto simp add: in_set_conv_nth)
      then obtain k where k: \<open>cs ! n = cr k\<close> \<open>env_ok ?ws L2 k 1\<close> using each[OF n(1)] by blast
      then show \<open>cwt ?ws (snd L2) t \<and> cwidth ?ws (snd L2) t = 1\<close> using cr_env[OF k(2)] n(2) by simp
    qed
    then show ?thesis using L2 by (simp add: cproblem_wt_def Let_def q cvar_widths_def cds[unfolded var_widths_def] lok_def var_widths_def)
  qed
  show \<open>cis_model (lower_problem_m p) m = is_model p m\<close>
  proof -
    have asg: \<open>cis_assignment (lower_problem_m p) m = is_assignment p m\<close>
      by (simp add: cis_assignment_def is_assignment_def cws)
    have \<open>is_assignment p m \<Longrightarrow> csatisfies (lower_problem_m p) m = satisfies p m\<close>
    proof -
      assume \<open>is_assignment p m\<close>
      then have V: \<open>vs_ok ?ws (map bits_nat m)\<close> by (rule vs_ok_of_assignment)
      let ?vs = \<open>map bits_nat m\<close>
      have \<open>(\<forall>t \<in> set cs. ceval ?ws (snd L2) ?vs (CV ?ws ?vs L2) t = 1) =
          (\<forall>t \<in> set ?A. eval ?ws ?ds ?vs (def_values ?ws [] ?vs [] ?D) t = 1)\<close>
      proof -
        have \<open>\<And>n. n < length ?A \<Longrightarrow> ceval ?ws (snd L2) ?vs (CV ?ws ?vs L2) (cs ! n) =
            eval ?ws ?ds ?vs (def_values ?ws [] ?vs [] ?D) (?A ! n)\<close>
        proof -
          fix n assume \<open>n < length ?A\<close>
          then obtain k where k: \<open>cs ! n = cr k\<close> \<open>env_ok ?ws L2 k 1\<close>
            \<open>CV ?ws ?vs L2 ! k = eval ?ws ?ds ?vs (def_values ?ws [] ?vs [] ?D) (?A ! n)\<close>
            using each V by blast
          then show \<open>ceval ?ws (snd L2) ?vs (CV ?ws ?vs L2) (cs ! n) = eval ?ws ?ds ?vs (def_values ?ws [] ?vs [] ?D) (?A ! n)\<close>
            using cr_env[OF k(2)] by simp
        qed
        then show ?thesis using len by (simp add: all_set_conv_all_nth)
      qed
      then show ?thesis by (simp add: csatisfies_def satisfies_def Let_def q cvar_widths_def cds[unfolded var_widths_def] var_widths_def)
    qed
    then show ?thesis using asg by (auto simp add: cis_model_def is_model_def)
  qed
qed

end
