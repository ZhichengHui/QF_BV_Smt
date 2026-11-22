theory QFBV_SmtSize
  imports "QFBV_Smt.QFBV_SmtModel"
begin

section \<open>The size checks of \<^verbatim>\<open>check_sat\<close>\<close>

text \<open>The Rust functions \<^verbatim>\<open>tr_size\<close> and \<^verbatim>\<open>size_ok\<close> compute, with additions and multiplications
  that saturate at \<open>2^63\<close>, the number of definitions of the translation of a problem and the
  \<^const>\<open>size_bound\<close> of the translated problem. Each Rust function computes \<open>sat\<close> of an
  exact value defined here.\<close>

subsection \<open>Saturation\<close>

definition sat :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>sat x \<equiv> min x (2 ^ 56)\<close>

lemma sat_0: \<open>sat 0 = 0\<close>
  by (simp add: sat_def)

lemma word_eq_of_unat: \<open>unat x = y \<Longrightarrow> x = (word_of_nat y :: 64 word)\<close>
  by auto

lemma sat_le: \<open>sat x \<le> 2 ^ 56\<close>
  by (simp add: sat_def)

lemma sat_lt_iff: \<open>(sat x < 2 ^ 56) = (x < 2 ^ 56)\<close>
  by (simp add: sat_def min_less_iff_disj)

lemma sat_add_sat: \<open>sat (sat x + sat y) = sat (x + y)\<close>
  by (simp add: sat_def)

lemma sat_mul_sat: \<open>sat (sat x * sat y) = sat (x * y)\<close>
proof (cases \<open>x = 0 \<or> y = 0\<close>)
  case True
  then show ?thesis by (auto simp: sat_def)
next
  case False
  then have x1: \<open>1 \<le> x\<close> and y1: \<open>1 \<le> y\<close> by auto
  show ?thesis
  proof (cases \<open>x * y < 2 ^ 56\<close>)
    case True
    have xc: \<open>x < 2 ^ 56\<close> using True y1 by (metis le_less_trans mult_le_mono2 nat_mult_1_right)
    have yc: \<open>y < 2 ^ 56\<close> using True x1 by (metis le_less_trans mult_le_mono1 nat_mult_1)
    show ?thesis using True xc yc by (simp add: sat_def)
  next
    case False
    have \<open>2 ^ 56 \<le> min x (2 ^ 56) * min y (2 ^ 56)\<close>
    proof (cases \<open>x < 2 ^ 56\<close>; cases \<open>y < 2 ^ 56\<close>)
    qed (use False x1 y1 in \<open>auto simp: min_def intro: order.trans[OF _ mult_le_mono1] order.trans[OF _ mult_le_mono2]\<close>)
    then show ?thesis using False by (simp add: sat_def)
  qed
qed

lemma sat_sat: \<open>sat (sat x) = sat x\<close>
  by (simp add: sat_def)

lemma sat_add_cong: \<open>sat x = sat y \<Longrightarrow> sat u = sat v \<Longrightarrow> sat (x + u) = sat (y + v)\<close>
  by (metis sat_add_sat)

lemma sat_mul_cong: \<open>sat x = sat y \<Longrightarrow> sat u = sat v \<Longrightarrow> sat (x * u) = sat (y * v)\<close>
  by (metis sat_mul_sat)

lemma sat_cube_cong: \<open>sat x = sat y \<Longrightarrow> sat ((x + 1) ^ 3) = sat ((y + 1) ^ 3)\<close>
proof -
  assume e: \<open>sat x = sat y\<close>
  have e1: \<open>sat (x + 1) = sat (y + 1)\<close> using e by (rule sat_add_cong) simp
  show ?thesis unfolding power3_eq_cube by (intro sat_mul_cong e1)
qed

lemma sat_add_sat_l: \<open>sat (sat x + y) = sat (x + y)\<close>
  by (metis sat_add_sat sat_sat)

lemma sat_add_sat_r: \<open>sat (x + sat y) = sat (x + y)\<close>
  by (metis sat_add_sat sat_sat)

lemma sat_1: \<open>sat (Suc 0) = Suc 0\<close>
  by (simp add: sat_def)

lemma le_div_iff_mul: \<open>0 < (a :: nat) \<Longrightarrow> (b \<le> c div a) = (a * b \<le> c)\<close>
  by (simp add: less_eq_div_iff_mult_less_eq mult.commute)

lemma ge_mul_left: \<open>1 \<le> (a :: nat) \<Longrightarrow> c \<le> b \<Longrightarrow> c \<le> a * b\<close>
  by (metis mult_le_mono nat_mult_1)

lemma ge_mul_right: \<open>1 \<le> (b :: nat) \<Longrightarrow> c \<le> a \<Longrightarrow> c \<le> a * b\<close>
  by (metis mult_le_mono nat_mult_1_right)

lemma big_mul_word:
  fixes a b :: \<open>64 word\<close>
  shows \<open>a \<noteq> 0 \<Longrightarrow> 72057594037927936 \<le> unat b \<Longrightarrow> 72057594037927936 \<le> unat a * unat b\<close>
    and \<open>b \<noteq> 0 \<Longrightarrow> 72057594037927936 \<le> unat a \<Longrightarrow> 72057594037927936 \<le> unat a * unat b\<close>
    and \<open>a \<noteq> 0 \<Longrightarrow> 72057594037927935 div unat a < unat b \<Longrightarrow> 72057594037927936 \<le> unat a * unat b\<close>
proof -
  show \<open>a \<noteq> 0 \<Longrightarrow> 72057594037927936 \<le> unat b \<Longrightarrow> 72057594037927936 \<le> unat a * unat b\<close>
    by (rule ge_mul_left) (simp_all add: Suc_le_eq unat_gt_0)
  show \<open>b \<noteq> 0 \<Longrightarrow> 72057594037927936 \<le> unat a \<Longrightarrow> 72057594037927936 \<le> unat a * unat b\<close>
    by (rule ge_mul_right) (simp_all add: Suc_le_eq unat_gt_0)
  assume a0: \<open>a \<noteq> 0\<close> and lt: \<open>72057594037927935 div unat a < unat b\<close>
  have \<open>0 < unat a\<close> using a0 by (simp add: unat_gt_0)
  then have \<open>\<not> unat a * unat b \<le> 72057594037927935\<close> using lt le_div_iff_mul[of \<open>unat a\<close> \<open>unat b\<close> 72057594037927935] by (meson not_le)
  then show \<open>72057594037927936 \<le> unat a * unat b\<close> by simp
qed

subsection \<open>The number of definitions of the translation\<close>

text \<open>The number of definitions the translation of a term adds, with the definitions below \<open>n\<close>
  expanded (as \<^const>\<open>tr_term_m\<close>).\<close>
function (sequential) cnt :: \<open>SmtProblem \<Rightarrow> nat \<Rightarrow> SmtTerm \<Rightarrow> nat\<close>
  and cnt_args :: \<open>SmtProblem \<Rightarrow> nat \<Rightarrow> SmtTerm list \<Rightarrow> nat\<close>
  where
  \<open>cnt p n (SmtTerm_Def d args) =
     (if dpar (sdefs p ! unat d) = [] then 0
      else if unat d < n then cnt_args p n args + cnt p (unat d) (SmtDef_body (sdefs p ! unat d))
      else 0)\<close>
| \<open>cnt p n (SmtTerm_App op args) = cnt_args p n args\<close>
| \<open>cnt p n _ = 0\<close>
| \<open>cnt_args p n [] = 0\<close>
| \<open>cnt_args p n (a # rest) = Suc (cnt p n a) + cnt_args p n rest\<close>
  by pat_completeness auto
termination
  by (relation \<open>measures [\<lambda>x. case x of Inl (_, n, _) \<Rightarrow> n | Inr (_, n, _) \<Rightarrow> n,
                          \<lambda>x. case x of Inl (_, _, t) \<Rightarrow> size t | Inr (_, _, ts) \<Rightarrow> size_list size ts]\<close>)
     auto

lemma tr_term_args_length:
  \<open>length (fst (tr_term_m p dm env n S t)) = length S + cnt p n t\<close>
  \<open>length (fst (tr_args_m p dm env n S ts)) = length S + cnt_args p n ts\<close>
  \<open>length (snd (tr_args_m p dm env n S ts)) = length ts\<close>
  by (induction p dm env n S t and p dm env n S ts rule: tr_term_m_tr_args_m.induct)
     (auto simp: Let_def)

text \<open>The number of definitions of the translation of \<open>p\<close>.\<close>
definition tsize :: \<open>SmtProblem \<Rightarrow> nat\<close> where
  \<open>tsize p \<equiv>
     sum_list (map (\<lambda>d. if dpar (sdefs p ! d) = []
                         then Suc (cnt p d (SmtDef_body (sdefs p ! d))) else 0)
                [0..<length (sdefs p)]) +
     sum_list (map (cnt p (length (sdefs p))) (sasserts p))\<close>

text \<open>The definitions part of \<^const>\<open>tsize\<close> for the first \<open>d\<close> definitions.\<close>
definition dsum :: \<open>SmtProblem \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>dsum p d \<equiv> sum_list (map (\<lambda>i. if dpar (sdefs p ! i) = []
                                   then Suc (cnt p i (SmtDef_body (sdefs p ! i))) else 0) [0..<d])\<close>

lemma dsum_0: \<open>dsum p 0 = 0\<close>
  by (simp add: dsum_def)

lemma dsum_Suc: \<open>dsum p (Suc d) = dsum p d +
  (if dpar (sdefs p ! d) = [] then Suc (cnt p d (SmtDef_body (sdefs p ! d))) else 0)\<close>
  by (simp add: dsum_def)

lemma tsize_dsum: \<open>tsize p = dsum p (length (sdefs p)) +
  sum_list (map (cnt p (length (sdefs p))) (sasserts p))\<close>
  by (simp add: tsize_def dsum_def)

lemma tr_defs_length:
  \<open>length (fst (foldl (tr_defs_step p) (S, dm) ds)) =
     length S + sum_list (map (\<lambda>d. if dpar (sdefs p ! d) = []
                                    then Suc (cnt p d (SmtDef_body (sdefs p ! d))) else 0) ds)\<close>
  by (induction ds arbitrary: S dm) (auto simp: tr_defs_step_def Let_def tr_term_args_length)

lemma tr_asserts_length:
  \<open>length (fst (foldl (tr_asserts_step p dm) (S, acc) ts)) =
     length S + sum_list (map (cnt p (length (sdefs p))) ts)\<close>
  by (induction ts arbitrary: S acc) (auto simp: tr_asserts_step_def Let_def tr_term_args_length)

lemma tsize_length: \<open>length (fst (tr_asserts_m p (tr_defs_m p))) = tsize p\<close>
proof -
  obtain S dm where d: \<open>tr_defs_m p = (S, dm)\<close> by (cases \<open>tr_defs_m p\<close>)
  have \<open>length S = sum_list (map (\<lambda>d. if dpar (sdefs p ! d) = []
                                    then Suc (cnt p d (SmtDef_body (sdefs p ! d))) else 0)
                         [0..<length (sdefs p)])\<close>
    using tr_defs_length[of p \<open>[]\<close> \<open>[]\<close> \<open>[0..<length (sdefs p)]\<close>] d by (simp add: tr_defs_m_step)
  then show ?thesis by (simp add: tsize_def tr_asserts_m_step d tr_asserts_length)
qed

subsection \<open>The precondition of the counting\<close>

text \<open>\<open>dok n F t\<close>: every definition \<open>t\<close> applies is below \<open>n\<close>, and every argument list in \<open>t\<close> has
  fewer than \<open>2^63\<close> and at most \<open>F\<close> elements (\<open>F\<close> is the fuel, which bounds the iterations of
  a loop).\<close>
fun dok :: \<open>nat \<Rightarrow> nat \<Rightarrow> SmtTerm \<Rightarrow> bool\<close> where
  \<open>dok n F (SmtTerm_Def d args) =
     (unat d < n \<and> length args < 2 ^ 63 \<and> length args \<le> F \<and> (\<forall>a \<in> set args. dok n F a))\<close>
| \<open>dok n F (SmtTerm_App op args) = (length args < 2 ^ 63 \<and> length args \<le> F \<and> (\<forall>a \<in> set args. dok n F a))\<close>
| \<open>dok n F _ = True\<close>

text \<open>Every definition has fewer than \<open>2^64\<close> parameters (so that \<^verbatim>\<open>len\<close> reads their
  number exactly).\<close>
definition params_ok :: \<open>SmtProblem \<Rightarrow> bool\<close> where
  \<open>params_ok p \<equiv> \<forall>e \<in> set (sdefs p). length (dpar e) < 2 ^ 64\<close>

lemma params_ok_nth: \<open>params_ok p \<Longrightarrow> d < length (sdefs p) \<Longrightarrow>
  ((word_of_nat (length (dpar (sdefs p ! d))) :: 64 word) = 0) = (dpar (sdefs p ! d) = [])\<close>
proof -
  assume a: \<open>params_ok p\<close> and b: \<open>d < length (sdefs p)\<close>
  have L: \<open>length (dpar (sdefs p ! d)) < 2 ^ 64\<close> using a b by (simp add: params_ok_def)
  show ?thesis using L by (auto simp: word_of_nat_eq_0_iff dest: nat_dvd_not_less)
qed

lemma nth_size_lt: \<open>i < length ts \<Longrightarrow> size (ts ! i) < size_list size ts\<close>
proof (induction ts arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons a ts)
  then show ?case by (cases i) fastforce+
qed

lemma sat_step: \<open>sat (sat x + sat (1 + sat c)) = sat (x + Suc c)\<close>
proof -
  have \<open>sat (1 :: nat) = 1\<close> by (simp add: sat_def)
  then have \<open>sat (1 + sat c) = sat (1 + c)\<close> by (metis sat_add_sat)
  then show ?thesis by (metis sat_add_sat plus_1_eq_Suc)
qed

lemma sat_step': \<open>sat (sat x + sat (Suc (sat c))) = sat (Suc (x + c))\<close>
  using sat_step[of x c] by simp

lemma nth_size_le: \<open>i < length ts \<Longrightarrow> size_list size ts \<le> k \<Longrightarrow> Suc (size (ts ! i)) \<le> k\<close>
  using nth_size_lt[of i ts] by simp

lemma unat_inc: \<open>unat (i :: 64 word) < n \<Longrightarrow> n < 2 ^ 64 \<Longrightarrow> unat (i + 1) = Suc (unat i)\<close>
  by (rule unat_plus_one_of_less_bound) simp_all

lemma cnt_args_sum: \<open>cnt_args p n ts = sum_list (map (\<lambda>a. Suc (cnt p n a)) ts)\<close>
  by (induction ts) auto

lemma cnt_args_take_Suc:
  \<open>i < length ts \<Longrightarrow> cnt_args p n (take (Suc i) ts) = cnt_args p n (take i ts) + Suc (cnt p n (ts ! i))\<close>
  by (simp add: cnt_args_sum take_Suc_conv_app_nth)

text \<open>The table \<^verbatim>\<open>dc\<close> of \<^verbatim>\<open>tr_size\<close> for the first \<open>n\<close> definitions: for a definition with
  parameters, the number of definitions its body adds where it is expanded.\<close>
definition dcv :: \<open>SmtProblem \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>dcv p d \<equiv> if dpar (sdefs p ! d) = [] then 0 else sat (cnt p d (SmtDef_body (sdefs p ! d)))\<close>

definition dcw :: \<open>SmtProblem \<Rightarrow> nat \<Rightarrow> 64 word list\<close> where
  \<open>dcw p n \<equiv> map (\<lambda>d. word_of_nat (dcv p d)) [0..<n]\<close>

lemma dcv_le: \<open>dcv p d \<le> 2 ^ 56\<close>
  by (simp add: dcv_def sat_def min_le_iff_disj)

lemma unat_dcw: \<open>d < n \<Longrightarrow> unat (dcw p n ! d) = dcv p d\<close>
  using dcv_le[of p d] by (simp add: dcw_def unat_of_nat_eq)

lemma dcw_Suc: \<open>dcw p (Suc d) = dcw p d @ [word_of_nat (dcv p d)]\<close>
  by (simp add: dcw_def)

lemma dcw_0: \<open>dcw p 0 = []\<close>
  by (simp add: dcw_def)

lemma dc_unat: \<open>dc = dcw p (length dc) \<Longrightarrow> d < length dc \<Longrightarrow> unat (dc ! d) = dcv p d\<close>
  by (metis unat_dcw)

lemma length_dcw: \<open>length (dcw p n) = n\<close>
  by (simp add: dcw_def)

subsection \<open>Widths and weights of terms of the extended language\<close>

text \<open>\<open>tix nw nd t\<close>: the variables and definitions \<open>t\<close> refers to are below \<open>nw\<close> and \<open>nd\<close>, every
  \<open>extract\<close> has \<open>lo \<le> hi\<close>, and every constant has fewer than \<open>2^64\<close> bits: what
  \<^verbatim>\<open>term_size\<close> needs not to panic and to read the lengths of constants exactly.\<close>
fun tix :: \<open>nat \<Rightarrow> nat \<Rightarrow> TermL \<Rightarrow> bool\<close> where
  \<open>tix nw nd (TermL_Const bs) = (length bs < 2 ^ 64)\<close>
| \<open>tix nw nd (TermL_Var i) = (unat i < nw)\<close>
| \<open>tix nw nd (TermL_Ref i) = (unat i < nd)\<close>
| \<open>tix nw nd (TermL_Not a) = tix nw nd a\<close>
| \<open>tix nw nd (TermL_Neg a) = tix nw nd a\<close>
| \<open>tix nw nd (TermL_Bin op a b) = (tix nw nd a \<and> tix nw nd b)\<close>
| \<open>tix nw nd (TermL_Extract hi lo a) = (unat lo \<le> unat hi \<and> tix nw nd a)\<close>
| \<open>tix nw nd (TermL_Repeat i a) = tix nw nd a\<close>
| \<open>tix nw nd (TermL_ZeroExtend i a) = tix nw nd a\<close>
| \<open>tix nw nd (TermL_SignExtend i a) = tix nw nd a\<close>
| \<open>tix nw nd (TermL_RotateLeft i a) = tix nw nd a\<close>
| \<open>tix nw nd (TermL_RotateRight i a) = tix nw nd a\<close>
| \<open>tix nw nd (TermL_Ite c a b) = (tix nw nd c \<and> tix nw nd a \<and> tix nw nd b)\<close>

text \<open>The saturated width and weight of a term depend only on the saturated widths of the
  definitions.\<close>
definition sat_eq :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> bool\<close> where
  \<open>sat_eq A B \<equiv> length A = length B \<and> (\<forall>i < length A. sat (A ! i) = sat (B ! i))\<close>

lemma sat_width_cong: \<open>sat_eq A B \<Longrightarrow> tix nw (length A) t \<Longrightarrow> sat (width ws A t) = sat (width ws B t)\<close>
  by (induction t) (auto simp: sat_eq_def split: Op_splits intro: sat_add_cong sat_mul_cong)

lemma sat_sum_cong:
  \<open>(\<forall>x \<in> set xs. sat (f x) = sat (g x)) \<Longrightarrow> sat (sum_list (map f xs)) = sat (sum_list (map g xs))\<close>
  by (induction xs) (auto intro: sat_add_cong)

text \<open>The width of a binary operation from the widths of its operands.\<close>
definition opw :: \<open>Op \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>opw op x y \<equiv>
     (case op of
        Op_Concat \<Rightarrow> x + y
      | Op_Comp \<Rightarrow> 1
      | Op_Eq \<Rightarrow> 1 | Op_Distinct \<Rightarrow> 1
      | Op_Ult \<Rightarrow> 1 | Op_Ule \<Rightarrow> 1 | Op_Ugt \<Rightarrow> 1 | Op_Uge \<Rightarrow> 1
      | Op_Slt \<Rightarrow> 1 | Op_Sle \<Rightarrow> 1 | Op_Sgt \<Rightarrow> 1 | Op_Sge \<Rightarrow> 1
      | _ \<Rightarrow> x)\<close>

lemma width_Bin_opw: \<open>width ws ds (TermL_Bin op a b) = opw op (width ws ds a) (width ws ds b)\<close>
  by (simp add: opw_def)

lemma sat_opw_cong: \<open>sat x = sat x' \<Longrightarrow> sat y = sat y' \<Longrightarrow> sat (opw op x y) = sat (opw op x' y')\<close>
  by (cases op) (auto simp: opw_def intro: sat_add_cong)

text \<open>The cost of a term in \<^const>\<open>ovf_bound\<close>: \<open>4\<close> times its linear weight plus its CNF count.\<close>
definition ow :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> TermL \<Rightarrow> nat\<close> where
  \<open>ow ws ds t \<equiv> 4 * lweight ws ds t + ecount ws ds t\<close>

text \<open>The cost of one node of width \<open>x\<close> in the linear weight, kept folded in proofs.\<close>
definition fw :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>fw x \<equiv> 4 * (x + 1)\<close>

lemma ow_eqs:
  \<open>ow ws ds (TermL_Const bs) = fw (length bs)\<close>
  \<open>ow ws ds (TermL_Var i) = fw (width ws ds (TermL_Var i))\<close>
  \<open>ow ws ds (TermL_Ref i) = fw (width ws ds (TermL_Ref i))\<close>
  \<open>ow ws ds (TermL_Not a) = fw (width ws ds a) + ow ws ds a\<close>
  \<open>ow ws ds (TermL_Neg a) = fw (width ws ds a) + (15 * width ws ds a + ow ws ds a)\<close>
  \<open>ow ws ds (TermL_Bin op a b) =
     fw (opw op (width ws ds a) (width ws ds b)) + (ebin op (width ws ds a) + (ow ws ds a + ow ws ds b))\<close>
  \<open>ow ws ds (TermL_Extract hi lo a) = fw (unat hi - unat lo + 1) + ow ws ds a\<close>
  \<open>ow ws ds (TermL_Repeat i a) = fw (unat i * width ws ds a) + ow ws ds a\<close>
  \<open>ow ws ds (TermL_ZeroExtend i a) = fw (width ws ds a + unat i) + ow ws ds a\<close>
  \<open>ow ws ds (TermL_SignExtend i a) = fw (width ws ds a + unat i) + (5 * unat i + ow ws ds a)\<close>
  \<open>ow ws ds (TermL_RotateLeft i a) = fw (width ws ds a) + ow ws ds a\<close>
  \<open>ow ws ds (TermL_RotateRight i a) = fw (width ws ds a) + ow ws ds a\<close>
  \<open>ow ws ds (TermL_Ite c a b) =
     fw (width ws ds a) + (5 * width ws ds a + (ow ws ds c + (ow ws ds a + ow ws ds b)))\<close>
  by (simp_all add: ow_def fw_def lweight_def ecount_def enode_def opw_def algebra_simps)

text \<open>A function at least the identity keeps saturated equality.\<close>
lemma sat_cong_ge: \<open>sat x = sat y \<Longrightarrow> (\<And>z. z \<le> f z) \<Longrightarrow> sat (f x) = sat (f y)\<close>
proof -
  assume e: \<open>sat x = sat y\<close> and g: \<open>\<And>z. z \<le> f z\<close>
  show ?thesis
  proof (cases \<open>x < 2 ^ 56\<close>)
    case True
    then have \<open>y = x\<close> using e by (simp add: sat_def min_def split: if_splits)
    then show ?thesis by simp
  next
    case False
    then have \<open>\<not> y < 2 ^ 56\<close> using e by (simp add: sat_def min_def split: if_splits)
    then have \<open>2 ^ 56 \<le> f y\<close> \<open>2 ^ 56 \<le> f x\<close> using False g[of x] g[of y] by linarith+
    then show ?thesis by (simp add: sat_def)
  qed
qed

lemma ebin_ge: \<open>z \<le> ebin op z\<close>
  by (auto simp: ebin_def)

lemma sat_mul_sat_l: \<open>sat (sat x * y) = sat (x * y)\<close>
proof (cases \<open>x < 2 ^ 56 \<or> y = 0\<close>)
  case True
  then show ?thesis by (auto simp: sat_def)
next
  case False
  then have x: \<open>2 ^ 56 \<le> x\<close> and y: \<open>1 \<le> y\<close> by auto
  have xy: \<open>x * 1 \<le> x * y\<close> using y by (rule mult_le_mono2)
  have a: \<open>2 ^ 56 \<le> x * y\<close> using order_trans[OF x] xy by simp
  have \<open>sat x = 2 ^ 56\<close> using x by (simp add: sat_def)
  moreover have \<open>(2 ^ 56) * 1 \<le> (2 ^ 56 :: nat) * y\<close> using y by (rule mult_le_mono2)
  ultimately show ?thesis using a by (simp add: sat_def)
qed

lemma sat_four: \<open>sat x = sat X \<Longrightarrow> sat (4 * sat (x + 1)) = sat (4 * (X + 1))\<close>
proof -
  assume e: \<open>sat x = sat X\<close>
  have \<open>sat (x + 1) = sat (X + 1)\<close> using e by (rule sat_add_cong) simp
  moreover have \<open>sat (4 * sat (x + 1)) = sat (4 * (x + 1))\<close>
    using sat_mul_sat[of 4 \<open>x + 1\<close>] by (simp add: sat_def)
  moreover have \<open>sat (4 * sat (X + 1)) = sat (4 * (X + 1))\<close>
    using sat_mul_sat[of 4 \<open>X + 1\<close>] by (simp add: sat_def)
  ultimately show ?thesis by (metis sat_sat)
qed

lemma fw_one: \<open>sat x = sat X \<Longrightarrow> sat (4 * sat (Suc x)) = sat (fw X)\<close>
  using sat_four by (simp add: fw_def)

lemma fw_plus: \<open>sat x = sat X \<Longrightarrow> sat G = sat G' \<Longrightarrow> sat (4 * sat (Suc x) + G) = sat (fw X + G')\<close>
proof -
  assume e: \<open>sat x = sat X\<close> and g: \<open>sat G = sat G'\<close>
  have \<open>sat (4 * sat (Suc x)) = sat (fw X)\<close> using sat_four[OF e] by (simp add: fw_def)
  then show ?thesis by (metis g sat_add_cong sat_add_sat sat_sat)
qed

text \<open>The last step of every case of \<^verbatim>\<open>term_size\<close>: the cost is \<open>4\<close> times the width plus one,
  plus the cost of the operands.\<close>
lemma final4: \<open>sat x = sat X \<Longrightarrow> g = sat G \<Longrightarrow> sat (sat (4 * sat (x + 1)) + g) = sat (4 * (X + 1) + G)\<close>
  by (metis sat_add_sat sat_four sat_sat)

lemma opw_chain: \<open>sat y = sat (opw op x1 x2) \<Longrightarrow> sat x1 = sat X1 \<Longrightarrow> sat x2 = sat X2 \<Longrightarrow> sat y = sat (opw op X1 X2)\<close>
  by (metis sat_opw_cong)

lemma unat_sub_le: \<open>unat lo \<le> unat hi \<Longrightarrow> unat (hi - lo) = unat hi - unat (lo :: 64 word)\<close>
  by (simp add: unat_sub word_le_nat_alt)

lemma sat_eq_snoc: \<open>sat_eq A B \<Longrightarrow> sat a = sat b \<Longrightarrow> sat_eq (A @ [a]) (B @ [b])\<close>
  by (auto simp: sat_eq_def nth_append)

lemma sat_eq_Nil: \<open>sat_eq [] []\<close>
  by (simp add: sat_eq_def)

lemma sat_eq_length: \<open>sat_eq A B \<Longrightarrow> length A = length B\<close>
  by (simp add: sat_eq_def)

lemma tix_mono: \<open>tix nw nd t \<Longrightarrow> nd \<le> nd' \<Longrightarrow> tix nw nd' t\<close>
  by (induction t) auto

lemma def_widths_take_Suc:
  \<open>d < length xs \<Longrightarrow> def_widths ws [] (take (Suc d) xs) =
     def_widths ws [] (take d xs) @ [width ws (def_widths ws [] (take d xs)) (xs ! d)]\<close>
  by (simp add: take_Suc_conv_app_nth def_widths_append')

lemma length_def_widths_take: \<open>length (def_widths ws [] (take d xs)) = min d (length xs)\<close>
  by (simp add: def_widths_length')

lemma width_step:
  \<open>sat_eq (map unat rb) D \<Longrightarrow> tix nw (length rb) t \<Longrightarrow> sat (unat a) = sat (width ws (map unat rb) t) \<Longrightarrow>
   sat_eq (map unat rb @ [unat a]) (D @ [width ws D t])\<close>
  by (metis sat_eq_snoc sat_width_cong length_map)

lemma sat_eq_len_take:
  \<open>sat_eq (map unat rb) (def_widths ws [] (take r xs)) \<Longrightarrow> r \<le> length xs \<Longrightarrow> length rb = r\<close>
  by (drule sat_eq_length) (simp add: def_widths_length')

text \<open>The parts of \<^const>\<open>ovf_bound\<close>.\<close>
definition base :: \<open>ProblemL \<Rightarrow> nat\<close> where
  \<open>base q \<equiv> Suc (sum_list (map unat (ProblemL_widths q)) + length (ProblemL_widths q) + length (ProblemL_defs q) +
                 length (ProblemL_asserts q))\<close>

definition DSq :: \<open>ProblemL \<Rightarrow> nat list\<close> where
  \<open>DSq q \<equiv> def_widths (map unat (ProblemL_widths q)) [] (ProblemL_defs q)\<close>

lemma ow_fun: \<open>ow ws ds = (\<lambda>t. 4 * lweight ws ds t + ecount ws ds t)\<close>
  by (rule ext) (simp add: ow_def)

lemma ovf_bound_eq:
  \<open>ovf_bound q = 4 * (base q + sum_list (map (ow (map unat (ProblemL_widths q)) (DSq q)) (ProblemL_defs q)) +
     sum_list (map (ow (map unat (ProblemL_widths q)) (DSq q)) (ProblemL_asserts q)))\<close>
  by (simp add: ovf_bound_def var_widths_def base_def DSq_def ow_fun Let_def)

lemma tix_subterms: \<open>tix nw nd t \<Longrightarrow> u \<in> set (subterms t) \<Longrightarrow> tix nw nd u\<close>
  by (induction t) auto

lemma sat_ow_cong: \<open>sat_eq A B \<Longrightarrow> tix nw (length A) t \<Longrightarrow> sat (ow ws A t) = sat (ow ws B t)\<close>
proof (induction t)
  case (TermL_Bin op a b)
  have wa: \<open>sat (width ws A a) = sat (width ws B a)\<close> and wb: \<open>sat (width ws A b) = sat (width ws B b)\<close>
    using sat_width_cong[OF TermL_Bin.prems(1)] TermL_Bin.prems(2) by auto
  have e: \<open>sat (ebin op (width ws A a)) = sat (ebin op (width ws B a))\<close> by (rule sat_cong_ge[OF wa ebin_ge])
  have o: \<open>sat (opw op (width ws A a) (width ws A b) + 1) = sat (opw op (width ws B a) (width ws B b) + 1)\<close>
    by (rule sat_add_cong, rule sat_opw_cong[OF wa wb]) simp
  have f: \<open>sat (fw (opw op (width ws A a) (width ws A b))) = sat (fw (opw op (width ws B a) (width ws B b)))\<close>
    unfolding fw_def by (rule sat_mul_cong[OF refl o])
  show ?case unfolding ow_eqs
    using TermL_Bin f e by (auto intro!: sat_add_cong)
next
  case (TermL_Ite c a b)
  have wa: \<open>sat (width ws A a) = sat (width ws B a)\<close> using sat_width_cong[OF TermL_Ite.prems(1)] TermL_Ite.prems(2) by auto
  have f: \<open>sat (fw (width ws A a)) = sat (fw (width ws B a))\<close> unfolding fw_def by (rule sat_mul_cong[OF refl sat_add_cong[OF wa refl]])
  have g: \<open>sat (5 * width ws A a) = sat (5 * width ws B a)\<close> by (rule sat_mul_cong[OF refl wa])
  have h: \<open>sat (9 * width ws A a) = sat (9 * width ws B a)\<close> by (rule sat_mul_cong[OF refl wa])
  show ?case unfolding ow_eqs using TermL_Ite f g h by (auto intro!: sat_add_cong)
qed (auto simp: ow_eqs fw_def sat_eq_def intro!: sat_add_cong sat_mul_cong sat_width_cong)

lemma ow_add:
  \<open>sat_eq (map unat ds) D \<Longrightarrow> tix nw (length ds) t \<Longrightarrow>
   sat (sat X + sat (ow ws (map unat ds) t)) = sat (X + ow ws D t)\<close>
  by (metis sat_add_sat sat_ow_cong length_map)

lemma final_cmp4: \<open>(sat (4 * sat X) < 72057594037927936) = (4 * X < 72057594037927936)\<close>
proof -
  have \<open>sat (4 :: nat) = 4\<close> by (simp add: sat_def)
  then have \<open>sat (4 * sat X) = sat (4 * X)\<close> by (metis sat_mul_sat)
  then show ?thesis by (simp add: sat_def min_less_iff_disj)
qed

lemma tix_full_asserts:
  \<open>sat_eq (map unat ds) (def_widths ws [] xs) \<Longrightarrow> (\<forall>t \<in> set ts. tix nw (length xs) t \<and> P t) \<Longrightarrow>
   \<forall>t \<in> set ts. tix nw (length ds) t\<close>
proof -
  assume e: \<open>sat_eq (map unat ds) (def_widths ws [] xs)\<close> and a: \<open>\<forall>t \<in> set ts. tix nw (length xs) t \<and> P t\<close>
  have l: \<open>length ds = length xs\<close> using sat_eq_length[OF e] by (simp add: def_widths_length')
  show ?thesis using a l by auto
qed

lemma tix_assert_q:
  \<open>sat_eq (map unat ds) (DSq q) \<Longrightarrow>
   (\<forall>t \<in> set (ProblemL_asserts q). tix nw (length (ProblemL_defs q)) t \<and> P t) \<Longrightarrow>
   t \<in> set (ProblemL_asserts q) \<Longrightarrow> tix nw (length ds) t\<close>
  unfolding DSq_def using tix_full_asserts by blast

lemma tix_full:
  \<open>sat_eq (map unat ds) (def_widths ws [] xs) \<Longrightarrow> (\<forall>d < length xs. tix nw d (xs ! d) \<and> P d) \<Longrightarrow>
   \<forall>k < length xs. tix nw (length ds) (xs ! k)\<close>
proof -
  assume e: \<open>sat_eq (map unat ds) (def_widths ws [] xs)\<close> and a: \<open>\<forall>d < length xs. tix nw d (xs ! d) \<and> P d\<close>
  have l: \<open>length ds = length xs\<close> using sat_eq_length[OF e] by (simp add: def_widths_length')
  show ?thesis using a l by (auto intro: tix_mono)
qed

lemma nst_le_iff: \<open>(nst n \<le> i) = (n \<le> 2 ^ i)\<close>
proof
  assume \<open>nst n \<le> i\<close>
  moreover have \<open>n \<le> 2 ^ nst n\<close> unfolding nst_def by (rule LeastI[of _ n]) (simp add: less_imp_le)
  ultimately show \<open>n \<le> 2 ^ i\<close> by (meson order_trans power_increasing one_le_numeral)
next
  assume \<open>n \<le> 2 ^ i\<close>
  then show \<open>nst n \<le> i\<close> unfolding nst_def by (rule Least_le)
qed

lemma nst_le64: \<open>unat (n :: 64 word) \<le> 2 ^ 64\<close>
  using unat_lt2p[of n] by simp

text \<open>The loop of \<^verbatim>\<open>stages\<close>: \<open>p\<close> is \<open>2^i\<close> saturated, and \<open>i\<close> stays at most \<^const>\<open>nst\<close>.\<close>
lemma stages_step:
  \<open>p = sat (2 ^ i) \<Longrightarrow> p < n \<Longrightarrow> i < 64 \<Longrightarrow> Suc i \<le> nst n \<and> sat (p * 2) = sat (2 ^ Suc i)\<close>
proof -
  assume a: \<open>p = sat (2 ^ i)\<close> \<open>p < n\<close> \<open>i < 64\<close>
  have \<open>(2::nat) ^ i \<le> 2 ^ 56\<close> using a(3) by (intro power_increasing) simp_all
  then have \<open>p = 2 ^ i\<close> using a(1) by (simp add: sat_def)
  then have \<open>\<not> n \<le> 2 ^ i\<close> using a(2) by simp
  then have \<open>Suc i \<le> nst n\<close> using nst_le_iff[of n i] by simp
  moreover have \<open>sat (p * 2) = sat (2 ^ Suc i)\<close>
    using sat_mul_sat[of \<open>2 ^ i\<close> 2] a(1) by (simp add: sat_def mult.commute)
  ultimately show ?thesis by simp
qed

lemma sat2a: \<open>sat (sat x * 2) = sat (2 * x)\<close>
  using sat_mul_sat_l[of x 2] by (simp add: mult.commute)

lemma sat2b: \<open>sat (2 * sat x) = sat (2 * x)\<close>
  using sat_mul_sat_l[of x 2] by (simp add: mult.commute)

lemma stages_exit:
  \<open>p = sat (2 ^ i) \<Longrightarrow> i \<le> 64 \<Longrightarrow> i \<le> nst n \<Longrightarrow> n \<le> 2 ^ 64 \<Longrightarrow> \<not> (p < n \<and> i < 64) \<Longrightarrow> i = nst n\<close>
proof -
  assume a: \<open>p = sat (2 ^ i)\<close> \<open>i \<le> 64\<close> \<open>i \<le> nst n\<close> \<open>n \<le> 2 ^ 64\<close> \<open>\<not> (p < n \<and> i < 64)\<close>
  have \<open>nst n \<le> i\<close>
  proof (cases \<open>i < 64\<close>)
    case True
    then have \<open>n \<le> p\<close> using a(5) by simp
    moreover have \<open>p \<le> 2 ^ i\<close> using a(1) by (simp add: sat_def)
    ultimately show ?thesis using nst_le_iff by (meson order_trans)
  next
    case False
    then show ?thesis using a(2,4) nst_le_iff[of n 64] by simp
  qed
  then show ?thesis using a(3) by simp
qed

context QFBV_ctx
begin

subsection \<open>Saturating arithmetic\<close>

definition cap_contract :: \<open>('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>cap_contract \<equiv>
     make_function_contract can_alloc_reference (\<lambda>r. can_alloc_reference \<star> \<langle>unat r = 2 ^ 56\<rangle>)\<close>

lemma cap_spec [crush_specs]:
  shows \<open>\<Gamma>; cap \<Turnstile>\<^sub>F cap_contract\<close>
  by (crush_boot f: cap_def contract: cap_contract_def) crush_base

definition sat_add_contract :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>sat_add_contract a b \<equiv>
     make_function_contract can_alloc_reference
       (\<lambda>r. can_alloc_reference \<star> \<langle>unat r = sat (unat a + unat b)\<rangle>)\<close>

lemma sat_add_spec [crush_specs]:
  shows \<open>\<Gamma>; sat_add a b \<Turnstile>\<^sub>F sat_add_contract a b\<close>
  apply (crush_boot f: sat_add_def contract: sat_add_contract_def)
  apply (crush_base simp add: sat_def word_le_nat_alt word_less_nat_alt unat_sub)
  apply (rule unat_add_s; simp)
  done

definition sat_mul_contract :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>sat_mul_contract a b \<equiv>
     make_function_contract can_alloc_reference
       (\<lambda>r. can_alloc_reference \<star> \<langle>unat r = sat (unat a * unat b)\<rangle>)\<close>

lemma sat_mul_spec [crush_specs]:
  shows \<open>\<Gamma>; sat_mul a b \<Turnstile>\<^sub>F sat_mul_contract a b\<close>
  apply (crush_boot f: sat_mul_def contract: sat_mul_contract_def)
  apply (crush_base simp add: sat_def word_le_nat_alt word_less_nat_alt unat_sub unat_div)
  apply (auto simp: le_div_iff_mul unat_gt_0 not_less min_def unat_mult_s Suc_le_eq
      intro: antisym big_mul_word)
  done

subsection \<open>\<^verbatim>\<open>tr_count\<close> and \<^verbatim>\<open>tr_count_args\<close>\<close>

text \<open>The \<open>k\<close>-th unfolding of the mutual recursion: its precondition requires the recursion depth
  to be at most \<open>k\<close>. The table \<open>dc\<close> is \<^const>\<open>dcw\<close> of its length \<open>n\<close>, and definitions are expanded
  below \<open>n\<close>.\<close>
definition tr_count_contract :: \<open>nat \<Rightarrow> SmtProblem \<Rightarrow> 64 word list \<Rightarrow> SmtTerm \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>tr_count_contract k p dc t \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
        \<langle>Suc (size t) \<le> k \<and> dc = dcw p (length dc) \<and> length dc \<le> length (sdefs p) \<and>
         params_ok p \<and> dok (length dc) urust_fuel t\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>unat r = sat (cnt p (length dc) t)\<rangle>)\<close>

definition tr_count_args_contract :: \<open>nat \<Rightarrow> SmtProblem \<Rightarrow> 64 word list \<Rightarrow> SmtTerm list \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>tr_count_args_contract k p dc ts \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
        \<langle>Suc (size_list size ts) \<le> k \<and> dc = dcw p (length dc) \<and> length dc \<le> length (sdefs p) \<and>
         params_ok p \<and> length ts < 2 ^ 63 \<and> length ts \<le> urust_fuel \<and> (\<forall>a \<in> set ts. dok (length dc) urust_fuel a)\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>unat r = sat (cnt_args p (length dc) ts)\<rangle>)\<close>

lemma tr_count_step_spec:
  assumes IH1: \<open>\<And>p dc t. \<Gamma>; f p dc t \<Turnstile>\<^sub>F tr_count_contract k p dc t\<close>
      and IH2: \<open>\<And>p dc ts. \<Gamma>; g p dc ts \<Turnstile>\<^sub>F tr_count_args_contract k p dc ts\<close>
  shows \<open>\<Gamma>; fst (tr_count_rec_step (f, g)) p dc t \<Turnstile>\<^sub>F tr_count_contract (Suc k) p dc t\<close>
    and \<open>\<Gamma>; snd (tr_count_rec_step (f, g)) p dc ts \<Turnstile>\<^sub>F tr_count_args_contract (Suc k) p dc ts\<close>
proof -
  show \<open>\<Gamma>; fst (tr_count_rec_step (f, g)) p dc t \<Turnstile>\<^sub>F tr_count_contract (Suc k) p dc t\<close>
  proof (cases t)
    case (SmtTerm_Def d args)
    show ?thesis unfolding SmtTerm_Def tr_count_rec_step_def prod.case fst_conv
      apply (crush_boot contract: tr_count_contract_def)
      apply (crush_base specs add: IH2 contracts add: tr_count_args_contract_def)
        apply (auto simp: dc_unat dcv_def sat_add_sat params_ok_nth)
      apply (simp add: sat_def)
      done
  next
    case (SmtTerm_App op args)
    show ?thesis unfolding SmtTerm_App tr_count_rec_step_def prod.case fst_conv
      apply (crush_boot contract: tr_count_contract_def)
      apply (crush_base specs add: IH2 contracts add: tr_count_args_contract_def)
      done
  next
    case (SmtTerm_BoolConst b)
    show ?thesis unfolding SmtTerm_BoolConst tr_count_rec_step_def prod.case fst_conv
      apply (crush_boot contract: tr_count_contract_def)
      apply (crush_base simp add: sat_def)
      done
  next
    case (SmtTerm_BvConst bs)
    show ?thesis unfolding SmtTerm_BvConst tr_count_rec_step_def prod.case fst_conv
      apply (crush_boot contract: tr_count_contract_def)
      apply (crush_base simp add: sat_def)
      done
  next
    case (SmtTerm_Param i)
    show ?thesis unfolding SmtTerm_Param tr_count_rec_step_def prod.case fst_conv
      apply (crush_boot contract: tr_count_contract_def)
      apply (crush_base simp add: sat_def)
      done
  next
    case (SmtTerm_Fun i args)
    show ?thesis unfolding SmtTerm_Fun tr_count_rec_step_def prod.case fst_conv
      apply (crush_boot contract: tr_count_contract_def)
      apply (crush_base simp add: sat_def)
      done
  qed
  show \<open>\<Gamma>; snd (tr_count_rec_step (f, g)) p dc ts \<Turnstile>\<^sub>F tr_count_args_contract (Suc k) p dc ts\<close>
    unfolding tr_count_rec_step_def prod.case snd_conv
    apply (crush_boot contract: tr_count_args_contract_def)
    apply (crush_base)
    subgoal for n_ref i_ref
      apply (ucincl_discharge\<open>
        rule_tac
          INV=\<open>\<lambda>j. \<Squnion>gn n gi i. n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
                 \<langle>unat i \<le> length ts \<and> unat n = sat (cnt_args p (length dc) (take (unat i) ts)) \<and>
                  length ts - unat i \<le> j\<rangle>\<close> and
          INV'=\<open>\<lambda>j. \<Squnion>gn n gi i. n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
                 \<langle>unat i < length ts \<and> unat n = sat (cnt_args p (length dc) (take (unat i) ts)) \<and>
                  length ts - unat i \<le> Suc j\<rangle>\<close> and
          \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
          \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_bounded_while_framedI\<close>)
      apply (crush_base specs add: IH1 contracts add: tr_count_contract_def
          simp add: word_less_nat_alt unat_inc cnt_args_take_Suc sat_step)
      apply (auto simp: unat_of_nat_eq sat_step' intro: nth_size_le)
      apply (simp add: sat_def)
      done
    done
qed

lemma tr_count_rec_spec:
  shows \<open>(\<forall>p dc t. \<Gamma>; fst ((tr_count_rec_step ^^ k) h) p dc t \<Turnstile>\<^sub>F tr_count_contract k p dc t) \<and>
         (\<forall>p dc ts. \<Gamma>; snd ((tr_count_rec_step ^^ k) h) p dc ts \<Turnstile>\<^sub>F tr_count_args_contract k p dc ts)\<close>
proof (induction k)
  case 0
  show ?case
    apply (intro conjI allI)
     apply (ucincl_discharge\<open>intro satisfies_function_contractI\<close>; subst wp_sstriple_iff;
        simp add: tr_count_contract_def Let_def apure_precise_False asepconj_bot_zero2 bot_aentails_all)
    apply (ucincl_discharge\<open>intro satisfies_function_contractI\<close>; subst wp_sstriple_iff;
        simp add: tr_count_args_contract_def Let_def apure_precise_False asepconj_bot_zero2 bot_aentails_all)
    done
next
  case (Suc k)
  obtain f g where fg: \<open>(tr_count_rec_step ^^ k) h = (f, g)\<close> by (cases \<open>(tr_count_rec_step ^^ k) h\<close>)
  show ?case
    using tr_count_step_spec[where f=f and g=g and k=k] Suc.IH unfolding funpow.simps(2) comp_def fg by simp
qed

lemma tr_count_spec [crush_specs]:
  shows \<open>\<Gamma>; tr_count p dc t \<Turnstile>\<^sub>F tr_count_contract urust_fuel p dc t\<close>
  unfolding tr_count_def using tr_count_rec_spec by blast

subsection \<open>\<^verbatim>\<open>tr_size\<close>\<close>

text \<open>What \<^verbatim>\<open>tr_size\<close> needs: the definitions refer to earlier ones and the assertions to
  definitions; every term and list is within the fuel and below \<open>2^63\<close>.\<close>
definition tsize_pre :: \<open>nat \<Rightarrow> SmtProblem \<Rightarrow> bool\<close> where
  \<open>tsize_pre F p \<equiv>
     let ds = sdefs p in
     params_ok p \<and> length ds < 2 ^ 63 \<and> length ds \<le> F \<and>
     length (sasserts p) < 2 ^ 63 \<and> length (sasserts p) \<le> F \<and>
     (\<forall>d < length ds. dok d F (SmtDef_body (ds ! d)) \<and> Suc (size (SmtDef_body (ds ! d))) \<le> F) \<and>
     (\<forall>t \<in> set (sasserts p). dok (length ds) F t \<and> Suc (size t) \<le> F)\<close>

definition tr_size_contract :: \<open>SmtProblem \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>tr_size_contract p \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>tsize_pre urust_fuel p\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>unat r = sat (tsize p)\<rangle>)\<close>

lemma tr_size_spec [crush_specs]:
  shows \<open>\<Gamma>; tr_size p \<Turnstile>\<^sub>F tr_size_contract p\<close>
  apply (crush_boot f: tr_size_def contract: tr_size_contract_def)
  apply (crush_base simp add: tsize_pre_def Let_def)
  subgoal for dc_ref n_ref d_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>j. \<Squnion>gc c gn n gd d. dc_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c \<star> n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star> d_ref \<mapsto>\<langle>\<top>\<rangle> gd\<down>d \<star>
               can_alloc_reference \<star>
               \<langle>unat d \<le> length (sdefs p) \<and> c = dcw p (unat d) \<and> unat n = sat (dsum p (unat d)) \<and>
                length (sdefs p) - unat d \<le> j\<rangle>\<close> and
        INV'=\<open>\<lambda>j. \<Squnion>gc c gn n gd d. dc_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c \<star> n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star> d_ref \<mapsto>\<langle>\<top>\<rangle> gd\<down>d \<star>
               can_alloc_reference \<star>
               \<langle>unat d < length (sdefs p) \<and> c = dcw p (unat d) \<and> unat n = sat (dsum p (unat d)) \<and>
                length (sdefs p) - unat d \<le> Suc j\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: vec_push_def contracts add: tr_count_contract_def
        simp add: word_less_nat_alt unat_inc dsum_Suc dsum_0 dcw_Suc dcw_0 length_dcw sat_step sat_step'
          unat_of_nat_eq params_ok_nth sat_0)
    prefer 3
    subgoal for gc gn n gd d j_ref
      apply (ucincl_discharge\<open>
        rule_tac
          INV=\<open>\<lambda>j. \<Squnion>gc gn n gj jj. dc_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>dcw p (length (sdefs p)) \<star>
                 n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>jj \<star> can_alloc_reference \<star>
                 \<langle>unat jj \<le> length (sasserts p) \<and>
                  unat n = sat (dsum p (length (sdefs p)) +
                     sum_list (map (cnt p (length (sdefs p))) (take (unat jj) (sasserts p)))) \<and>
                  length (sasserts p) - unat jj \<le> j\<rangle>\<close> and
          INV'=\<open>\<lambda>j. \<Squnion>gc gn n gj jj. dc_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>dcw p (length (sdefs p)) \<star>
                 n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>jj \<star> can_alloc_reference \<star>
                 \<langle>unat jj < length (sasserts p) \<and>
                  unat n = sat (dsum p (length (sdefs p)) +
                     sum_list (map (cnt p (length (sdefs p))) (take (unat jj) (sasserts p)))) \<and>
                  length (sasserts p) - unat jj \<le> Suc j\<rangle>\<close> and
          \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
          \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_bounded_while_framedI\<close>)
      apply (crush_base contracts add: tr_count_contract_def
          simp add: word_less_nat_alt unat_inc length_dcw unat_of_nat_eq sat_add_sat take_Suc_conv_app_nth tsize_dsum)
      apply (auto simp: add.assoc sat_0)
      done
    apply (auto intro: word_eq_of_unat simp: dcv_def)
    done
  done

subsection \<open>\<^verbatim>\<open>term_size\<close>\<close>

definition stages_contract :: \<open>64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>stages_contract n \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>64 \<le> urust_fuel\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>unat r = nst (unat n)\<rangle>)\<close>

lemma stages_spec [crush_specs]:
  shows \<open>\<Gamma>; stages n \<Turnstile>\<^sub>F stages_contract n\<close>
  apply (crush_boot f: stages_def contract: stages_contract_def)
  apply (crush_base)
  subgoal for i_ref p_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>j. \<Squnion>gi i gp p. i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> p_ref \<mapsto>\<langle>\<top>\<rangle> gp\<down>p \<star> can_alloc_reference \<star>
               \<langle>unat p = sat (2 ^ unat i) \<and> unat i \<le> 64 \<and> unat i \<le> nst (unat n) \<and>
                (if unat p < unat n \<and> unat i < 64 then 64 - unat i else 0) \<le> j\<rangle>\<close> and
        INV'=\<open>\<lambda>j. \<Squnion>gi i gp p. i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> p_ref \<mapsto>\<langle>\<top>\<rangle> gp\<down>p \<star> can_alloc_reference \<star>
               \<langle>unat p = sat (2 ^ unat i) \<and> unat i < 64 \<and> unat p < unat n \<and> unat i \<le> nst (unat n) \<and>
                64 - unat i \<le> Suc j\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: word_less_nat_alt unat_inc)
    apply (all \<open>(simp only: sat2a sat2b sat_1; fail)?\<close>)
    apply (all \<open>(rule stages_step[OF refl, THEN conjunct1]; (assumption | simp))?\<close>)
    apply (rule stages_exit[OF _ _ _ nst_le64]; auto split: if_splits)
    done
  done

definition bin_cost_contract :: \<open>Op \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>bin_cost_contract op w \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>64 \<le> urust_fuel\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>unat r = sat (ebin op (unat w))\<rangle>)\<close>

lemma bin_cost_spec [crush_specs]:
  shows \<open>\<Gamma>; bin_cost op w \<Turnstile>\<^sub>F bin_cost_contract op w\<close>
  apply (crush_boot f: bin_cost_def contract: bin_cost_contract_def)
  apply (cases op; simp only: Op_case_simps)
  apply (crush_base simp add: ebin_def sat_mul_sat_l sat_add_sat_l sat_add_sat_r)+
  done

definition op_width_contract :: \<open>Op \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>op_width_contract op a b \<equiv>
     make_function_contract can_alloc_reference
       (\<lambda>r. can_alloc_reference \<star> \<langle>sat (unat r) = sat (opw op (unat a) (unat b))\<rangle>)\<close>

lemma op_width_spec [crush_specs]:
  shows \<open>\<Gamma>; op_width op a b \<Turnstile>\<^sub>F op_width_contract op a b\<close>
  apply (crush_boot f: op_width_def contract: op_width_contract_def)
  apply (cases op; simp only: Op_case_simps)
  apply (crush_base simp add: opw_def sat_sat)+
  done

text \<open>The \<open>k\<close>-th unfolding of \<^verbatim>\<open>term_size\<close>. The width it returns is exact up to saturation
  (for a variable it is the declared width itself), the cost is saturated.\<close>
definition term_size_contract ::
  \<open>nat \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> TermL \<Rightarrow> ('s, 64 word \<times> 64 word \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>term_size_contract k ws ds t \<equiv>
     make_function_contract
       (can_alloc_reference \<star> \<langle>Suc (size t) \<le> k \<and> tix (length ws) (length ds) t \<and> 64 \<le> urust_fuel\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>sat (unat (fst r)) = sat (width (map unat ws) (map unat ds) t) \<and>
           unat (fst (snd r)) = sat (ow (map unat ws) (map unat ds) t)\<rangle>)\<close>

lemma term_size_step_spec:
  assumes IH: \<open>\<And>ws ds t. \<Gamma>; R ws ds t \<Turnstile>\<^sub>F term_size_contract k ws ds t\<close>
  shows \<open>\<Gamma>; term_size_rec_step R ws ds t \<Turnstile>\<^sub>F term_size_contract (Suc k) ws ds t\<close>
proof (cases t)
  case (TermL_Const bs)
  show ?thesis unfolding TermL_Const
    apply (crush_boot f: term_size_rec_step_def contract: term_size_contract_def)
    apply (crush_base specs add: IH simp add: ow_eqs sat_add_sat sat_sat)
    apply (auto simp: unat_of_nat_eq sat_sat intro!: fw_one fw_plus sat_add_cong sat_mul_cong sat_cong_ge[OF _ ebin_ge])
    done
next
  case (TermL_Var i)
  show ?thesis unfolding TermL_Var
    apply (crush_boot f: term_size_rec_step_def contract: term_size_contract_def)
    apply (crush_base specs add: IH simp add: ow_eqs sat_add_sat sat_sat)
    apply (auto simp: unat_of_nat_eq sat_sat intro!: fw_one fw_plus sat_add_cong sat_mul_cong sat_cong_ge[OF _ ebin_ge])
    done
next
  case (TermL_Ref i)
  show ?thesis unfolding TermL_Ref
    apply (crush_boot f: term_size_rec_step_def contract: term_size_contract_def)
    apply (crush_base specs add: IH simp add: ow_eqs sat_add_sat sat_sat)
    apply (auto simp: unat_of_nat_eq sat_sat intro!: fw_one fw_plus sat_add_cong sat_mul_cong sat_cong_ge[OF _ ebin_ge])
    done
next
  case (TermL_Not a)
  show ?thesis unfolding TermL_Not
    apply (crush_boot f: term_size_rec_step_def contract: term_size_contract_def)
    apply (crush_base specs add: IH simp add: ow_eqs sat_add_sat sat_sat)
    apply (auto simp: unat_of_nat_eq sat_sat intro!: fw_one fw_plus sat_add_cong sat_mul_cong sat_cong_ge[OF _ ebin_ge])
    done
next
  case (TermL_Neg a)
  show ?thesis unfolding TermL_Neg
    apply (crush_boot f: term_size_rec_step_def contract: term_size_contract_def)
    apply (crush_base specs add: IH simp add: ow_eqs sat_add_sat sat_sat)
    apply (auto simp: unat_of_nat_eq sat_sat intro!: fw_one fw_plus sat_add_cong sat_mul_cong sat_cong_ge[OF _ ebin_ge])
    done
next
  case (TermL_Bin op a b)
  show ?thesis unfolding TermL_Bin
    apply (crush_boot f: term_size_rec_step_def contract: term_size_contract_def)
    apply (crush_base specs add: IH simp add: ow_eqs sat_add_sat sat_sat width_Bin_opw simp del: width.simps)
     apply (rule fw_plus, rule opw_chain, assumption+)
     apply (auto intro!: sat_add_cong sat_cong_ge[OF _ ebin_ge])[1]
    apply (cases op; auto simp: opw_def intro: sat_add_cong)
    done
next
  case (TermL_Extract hi lo a)
  show ?thesis unfolding TermL_Extract
    apply (crush_boot f: term_size_rec_step_def contract: term_size_contract_def)
    apply (crush_base specs add: IH simp add: ow_eqs sat_add_sat sat_sat word_le_nat_alt)
    apply (auto simp: unat_sub_le sat_sat intro!: fw_one fw_plus sat_add_cong sat_mul_cong)
    done
next
  case (TermL_Repeat i a)
  show ?thesis unfolding TermL_Repeat
    apply (crush_boot f: term_size_rec_step_def contract: term_size_contract_def)
    apply (crush_base specs add: IH simp add: ow_eqs sat_add_sat sat_sat)
    apply (auto simp: unat_of_nat_eq sat_sat intro!: fw_one fw_plus sat_add_cong sat_mul_cong sat_cong_ge[OF _ ebin_ge])
    done
next
  case (TermL_ZeroExtend i a)
  show ?thesis unfolding TermL_ZeroExtend
    apply (crush_boot f: term_size_rec_step_def contract: term_size_contract_def)
    apply (crush_base specs add: IH simp add: ow_eqs sat_add_sat sat_sat)
    apply (auto simp: unat_of_nat_eq sat_sat intro!: fw_one fw_plus sat_add_cong sat_mul_cong sat_cong_ge[OF _ ebin_ge])
    done
next
  case (TermL_SignExtend i a)
  show ?thesis unfolding TermL_SignExtend
    apply (crush_boot f: term_size_rec_step_def contract: term_size_contract_def)
    apply (crush_base specs add: IH simp add: ow_eqs sat_add_sat sat_sat)
    apply (auto simp: unat_of_nat_eq sat_sat intro!: fw_one fw_plus sat_add_cong sat_mul_cong sat_cong_ge[OF _ ebin_ge])
    done
next
  case (TermL_RotateLeft i a)
  show ?thesis unfolding TermL_RotateLeft
    apply (crush_boot f: term_size_rec_step_def contract: term_size_contract_def)
    apply (crush_base specs add: IH simp add: ow_eqs sat_add_sat sat_sat)
    apply (auto simp: unat_of_nat_eq sat_sat intro!: fw_one fw_plus sat_add_cong sat_mul_cong sat_cong_ge[OF _ ebin_ge])
    done
next
  case (TermL_RotateRight i a)
  show ?thesis unfolding TermL_RotateRight
    apply (crush_boot f: term_size_rec_step_def contract: term_size_contract_def)
    apply (crush_base specs add: IH simp add: ow_eqs sat_add_sat sat_sat)
    apply (auto simp: unat_of_nat_eq sat_sat intro!: fw_one fw_plus sat_add_cong sat_mul_cong sat_cong_ge[OF _ ebin_ge])
    done
next
  case (TermL_Ite c a b)
  show ?thesis unfolding TermL_Ite
    apply (crush_boot f: term_size_rec_step_def contract: term_size_contract_def)
    apply (crush_base specs add: IH simp add: ow_eqs sat_add_sat sat_sat)
    apply (auto simp: unat_of_nat_eq sat_sat intro!: fw_one fw_plus sat_add_cong sat_mul_cong sat_cong_ge[OF _ ebin_ge])
    done
qed

lemma term_size_rec_spec:
  shows \<open>\<Gamma>; (term_size_rec_step ^^ k) h ws ds t \<Turnstile>\<^sub>F term_size_contract k ws ds t\<close>
proof (induction k arbitrary: ws ds t)
  case 0
  show ?case
    apply (ucincl_discharge\<open>intro satisfies_function_contractI\<close>)
    apply (subst wp_sstriple_iff)
    apply (simp add: term_size_contract_def Let_def apure_precise_False asepconj_bot_zero2 bot_aentails_all)
    done
next
  case (Suc k)
  show ?case
    unfolding funpow.simps(2) comp_def by (rule term_size_step_spec) (rule Suc.IH)
qed

lemma term_size_spec [crush_specs]:
  shows \<open>\<Gamma>; term_size ws ds t \<Turnstile>\<^sub>F term_size_contract urust_fuel ws ds t\<close>
  unfolding term_size_def by (rule term_size_rec_spec)

subsection \<open>\<^verbatim>\<open>size_ok\<close>\<close>

text \<open>What \<^verbatim>\<open>size_ok\<close> needs: indices in bounds (as in a well-sorted problem), and the terms and
  lists within the fuel and below \<open>2^63\<close>.\<close>
definition size_pre :: \<open>nat \<Rightarrow> ProblemL \<Rightarrow> bool\<close> where
  \<open>size_pre F q \<equiv>
     let ws = ProblemL_widths q; ds = ProblemL_defs q; ts = ProblemL_asserts q in
     64 \<le> F \<and> length ws < 2 ^ 63 \<and> length ws \<le> F \<and> length ds < 2 ^ 63 \<and> length ds \<le> F \<and>
     length ts < 2 ^ 63 \<and> length ts \<le> F \<and>
     (\<forall>d < length ds. tix (length ws) d (ds ! d) \<and> Suc (size (ds ! d)) \<le> F) \<and>
     (\<forall>t \<in> set ts. tix (length ws) (length ds) t \<and> Suc (size t) \<le> F)\<close>

definition size_ok_contract :: \<open>ProblemL \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>size_ok_contract q \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>size_pre urust_fuel q\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = sizes_ok q\<rangle>)\<close>

lemma size_ok_spec [crush_specs]:
  shows \<open>\<Gamma>; size_ok q \<Turnstile>\<^sub>F size_ok_contract q\<close>
  apply (crush_boot f: size_ok_def contract: size_ok_contract_def)
  apply (crush_base simp add: size_pre_def Let_def)
  subgoal for ds_ref d_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>j. \<Squnion>gs ds gd d. ds_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>ds \<star> d_ref \<mapsto>\<langle>\<top>\<rangle> gd\<down>d \<star> can_alloc_reference \<star>
               \<langle>unat d \<le> length (ProblemL_defs q) \<and>
                sat_eq (map unat ds) (def_widths (map unat (ProblemL_widths q)) [] (take (unat d) (ProblemL_defs q))) \<and>
                length (ProblemL_defs q) - unat d \<le> j\<rangle>\<close> and
        INV'=\<open>\<lambda>j. \<Squnion>gs ds gd d. ds_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>ds \<star> d_ref \<mapsto>\<langle>\<top>\<rangle> gd\<down>d \<star> can_alloc_reference \<star>
               \<langle>unat d < length (ProblemL_defs q) \<and>
                sat_eq (map unat ds) (def_widths (map unat (ProblemL_widths q)) [] (take (unat d) (ProblemL_defs q))) \<and>
                length (ProblemL_defs q) - unat d \<le> Suc j\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: vec_push_def contracts add: term_size_contract_def
        simp add: word_less_nat_alt unat_inc unat_of_nat_eq sat_eq_Nil def_widths_take_Suc)
    prefer 3
    subgoal for gs ds gd d n_ref i_ref
      apply (ucincl_discharge\<open>
        rule_tac
          INV=\<open>\<lambda>j. \<Squnion>gn n gi i. n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
                 \<langle>unat i \<le> length (ProblemL_widths q) \<and>
                  unat n = sat (1 + sum_list (map unat (take (unat i) (ProblemL_widths q)))) \<and>
                  length (ProblemL_widths q) - unat i \<le> j\<rangle>\<close> and
          INV'=\<open>\<lambda>j. \<Squnion>gn n gi i. n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
                 \<langle>unat i < length (ProblemL_widths q) \<and>
                  unat n = sat (1 + sum_list (map unat (take (unat i) (ProblemL_widths q)))) \<and>
                  length (ProblemL_widths q) - unat i \<le> Suc j\<rangle>\<close> and
          \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
          \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_bounded_while_framedI\<close>)
      apply (crush_base simp add: word_less_nat_alt unat_inc unat_of_nat_eq sat_add_sat sat_add_sat_l sat_add_sat_r
          sat_1 take_Suc_conv_app_nth)
      subgoal for gn gi i r ra rb x k_ref
        apply (ucincl_discharge\<open>
          rule_tac
            INV=\<open>\<lambda>j. \<Squnion>gs' gn n gk k. ds_ref \<mapsto>\<langle>\<top>\<rangle> gs'\<down>ds \<star> n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star> k_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>k \<star>
                   can_alloc_reference \<star>
                   \<langle>unat k \<le> length (ProblemL_defs q) \<and> sat_eq (map unat ds) (DSq q) \<and>
                    (\<forall>k' < length (ProblemL_defs q). tix (length (ProblemL_widths q)) (length ds) (ProblemL_defs q ! k')) \<and>
                    unat n = sat (base q + sum_list (map (ow (map unat (ProblemL_widths q)) (DSq q))
                                                      (take (unat k) (ProblemL_defs q)))) \<and>
                    length (ProblemL_defs q) - unat k \<le> j\<rangle>\<close> and
            INV'=\<open>\<lambda>j. \<Squnion>gs' gn n gk k. ds_ref \<mapsto>\<langle>\<top>\<rangle> gs'\<down>ds \<star> n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star> k_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>k \<star>
                   can_alloc_reference \<star>
                   \<langle>unat k < length (ProblemL_defs q) \<and> sat_eq (map unat ds) (DSq q) \<and>
                    (\<forall>k' < length (ProblemL_defs q). tix (length (ProblemL_widths q)) (length ds) (ProblemL_defs q ! k')) \<and>
                    unat n = sat (base q + sum_list (map (ow (map unat (ProblemL_widths q)) (DSq q))
                                                      (take (unat k) (ProblemL_defs q)))) \<and>
                    length (ProblemL_defs q) - unat k \<le> Suc j\<rangle>\<close> and
            BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
            \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
            \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
          in wp_bounded_while_framedI\<close>)
        apply (crush_base contracts add: term_size_contract_def
            simp add: word_less_nat_alt unat_inc unat_of_nat_eq take_Suc_conv_app_nth base_def ow_add add.assoc)
        prefer 2
        subgoal for gs' gna n gk k j_ref
          apply (ucincl_discharge\<open>
            rule_tac
              INV=\<open>\<lambda>j. \<Squnion>gs' gn n gj jj. ds_ref \<mapsto>\<langle>\<top>\<rangle> gs'\<down>ds \<star> n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>jj \<star>
                     can_alloc_reference \<star>
                     \<langle>unat jj \<le> length (ProblemL_asserts q) \<and> sat_eq (map unat ds) (DSq q) \<and>
                      (\<forall>t \<in> set (ProblemL_asserts q). tix (length (ProblemL_widths q)) (length ds) t) \<and>
                      unat n = sat (base q +
                        sum_list (map (ow (map unat (ProblemL_widths q)) (DSq q)) (ProblemL_defs q)) +
                        sum_list (map (ow (map unat (ProblemL_widths q)) (DSq q))
                                   (take (unat jj) (ProblemL_asserts q)))) \<and>
                      length (ProblemL_asserts q) - unat jj \<le> j\<rangle>\<close> and
              INV'=\<open>\<lambda>j. \<Squnion>gs' gn n gj jj. ds_ref \<mapsto>\<langle>\<top>\<rangle> gs'\<down>ds \<star> n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>jj \<star>
                     can_alloc_reference \<star>
                     \<langle>unat jj < length (ProblemL_asserts q) \<and> sat_eq (map unat ds) (DSq q) \<and>
                      (\<forall>t \<in> set (ProblemL_asserts q). tix (length (ProblemL_widths q)) (length ds) t) \<and>
                      unat n = sat (base q +
                        sum_list (map (ow (map unat (ProblemL_widths q)) (DSq q)) (ProblemL_defs q)) +
                        sum_list (map (ow (map unat (ProblemL_widths q)) (DSq q))
                                   (take (unat jj) (ProblemL_asserts q)))) \<and>
                      length (ProblemL_asserts q) - unat jj \<le> Suc j\<rangle>\<close> and
              BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
              \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
              \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
            in wp_bounded_while_framedI\<close>)
          apply (crush_base contracts add: term_size_contract_def
              simp add: word_less_nat_alt unat_inc unat_of_nat_eq take_Suc_conv_app_nth base_def ow_add add.assoc)
          subgoal by (subst ow_add[where D=\<open>DSq q\<close>]) (auto simp: add.assoc)
          subgoal by (simp add: final_cmp4 sizes_ok_def ovf_bound_eq base_def add.assoc)
          subgoal by (blast intro: tix_assert_q)
          done
        subgoal by (subst ow_add[where D=\<open>DSq q\<close>]) (auto simp: add.assoc)
        subgoal using tix_full by blast
        subgoal by (simp add: DSq_def)
        done
      done
     apply (auto simp: sat_eq_len_take intro!: width_step)
    done
  done

end

subsection \<open>The preconditions from well-sortedness\<close>

lemma size_args_le: \<open>length args \<le> size_list size args\<close>
  by (induction args) auto

lemma size_arg_le: \<open>a \<in> set args \<Longrightarrow> size a \<le> size_list size args\<close>
  by (induction args) auto

lemma tsort_dok:
  \<open>smt_tsort fs ds ps t \<noteq> None \<Longrightarrow> smt_term_repr t \<Longrightarrow> size t \<le> F \<Longrightarrow> dok (length ds) F t\<close>
proof (induction t arbitrary: ps)
  case (SmtTerm_Def d args)
  have a: \<open>smt_tsort fs ds ps x \<noteq> None\<close> if \<open>x \<in> set args\<close> for x
  proof -
    have m: \<open>map (smt_tsort fs ds ps) args = map Some (dpar (ds ! unat d))\<close>
      using SmtTerm_Def.prems(1) by (auto split: if_splits)
    then have \<open>smt_tsort fs ds ps x \<in> set (map Some (dpar (ds ! unat d)))\<close>
      using that by (metis image_eqI list.set_map)
    then show ?thesis by auto
  qed
  have s: \<open>size x \<le> F\<close> if \<open>x \<in> set args\<close> for x
    using size_arg_le[OF that] SmtTerm_Def.prems(3) by simp
  have d: \<open>dok (length ds) F x\<close> if \<open>x \<in> set args\<close> for x
    using SmtTerm_Def.IH[OF that a[OF that]] SmtTerm_Def.prems(2) s[OF that] that by simp
  have u: \<open>unat d < length ds\<close> using SmtTerm_Def.prems(1) by (auto split: if_splits)
  show ?case using SmtTerm_Def.prems(2,3) size_args_le[of args] d u by auto
next
  case (SmtTerm_App op args)
  have a: \<open>smt_tsort fs ds ps x \<noteq> None\<close> if \<open>x \<in> set args\<close> for x
    using SmtTerm_App.prems(1) that by (auto split: if_splits) (metis image_eqI not_None_eq)
  have s: \<open>size x \<le> F\<close> if \<open>x \<in> set args\<close> for x
    using size_arg_le[OF that] SmtTerm_App.prems(3) by simp
  have d: \<open>dok (length ds) F x\<close> if \<open>x \<in> set args\<close> for x
    using SmtTerm_App.IH[OF that a[OF that]] SmtTerm_App.prems(2) s[OF that] that by simp
  show ?case using SmtTerm_App.prems(2,3) size_args_le[of args] d by auto
qed auto

text \<open>Every constant in \<open>t\<close> has fewer than \<open>2^64\<close> bits.\<close>
fun cok :: \<open>TermL \<Rightarrow> bool\<close> where
  \<open>cok (TermL_Const bs) = (length bs < 2 ^ 64)\<close>
| \<open>cok (TermL_Var i) = True\<close>
| \<open>cok (TermL_Ref i) = True\<close>
| \<open>cok (TermL_Not a) = cok a\<close>
| \<open>cok (TermL_Neg a) = cok a\<close>
| \<open>cok (TermL_Bin op a b) = (cok a \<and> cok b)\<close>
| \<open>cok (TermL_Extract hi lo a) = cok a\<close>
| \<open>cok (TermL_Repeat i a) = cok a\<close>
| \<open>cok (TermL_ZeroExtend i a) = cok a\<close>
| \<open>cok (TermL_SignExtend i a) = cok a\<close>
| \<open>cok (TermL_RotateLeft i a) = cok a\<close>
| \<open>cok (TermL_RotateRight i a) = cok a\<close>
| \<open>cok (TermL_Ite c a b) = (cok c \<and> cok a \<and> cok b)\<close>

lemma wt_tix: \<open>wt ws ds t \<Longrightarrow> cok t \<Longrightarrow> tix (length ws) (length ds) t\<close>
  by (induction t) auto

lemma defs_wt_nth:
  \<open>defs_wt ws [] xs \<Longrightarrow> d < length xs \<Longrightarrow> wt ws (def_widths ws [] (take d xs)) (xs ! d)\<close>
proof -
  assume a: \<open>defs_wt ws [] xs\<close> and d: \<open>d < length xs\<close>
  have \<open>xs = take d xs @ [xs ! d] @ drop (Suc d) xs\<close> using d by (simp add: id_take_nth_drop)
  then have \<open>defs_wt ws [] (take d xs @ [xs ! d] @ drop (Suc d) xs)\<close> using a by simp
  then show ?thesis by (simp add: defs_wt_append')
qed

lemma cok_foldl: \<open>cok a \<Longrightarrow> (\<And>acc x. cok acc \<Longrightarrow> cok (f acc x)) \<Longrightarrow> cok (foldl f a xs)\<close>
  by (induction xs arbitrary: a) auto

lemma cok_foldr: \<open>cok b \<Longrightarrow> (\<And>x acc. cok acc \<Longrightarrow> cok (f x acc)) \<Longrightarrow> cok (foldr f xs b)\<close>
  by (induction xs) auto

lemma cok_tr_app: \<open>cok (tr_app_m op ks)\<close>
  by (cases op) (auto simp: fold_left_m_def chain_m_def pairwise_m_def implies_m_def tref_def intro!: cok_foldl cok_foldr)

text \<open>The constants of the translation come from the bit-vector constants of the problem, or are
  one-bit constants for Boolean constants.\<close>
lemma cok_tr:
  \<open>smt_term_repr t \<Longrightarrow> n \<le> length (sdefs p) \<Longrightarrow>
   (\<forall>d < length (sdefs p). smt_term_repr (SmtDef_body (sdefs p ! d))) \<Longrightarrow> (\<forall>u \<in> set S. cok u) \<Longrightarrow>
   (\<forall>u \<in> set (fst (tr_term_m p dm env n S t)). cok u) \<and> cok (snd (tr_term_m p dm env n S t))\<close>
  \<open>(\<forall>a \<in> set ts. smt_term_repr a) \<Longrightarrow> n \<le> length (sdefs p) \<Longrightarrow>
   (\<forall>d < length (sdefs p). smt_term_repr (SmtDef_body (sdefs p ! d))) \<Longrightarrow> (\<forall>u \<in> set S. cok u) \<Longrightarrow>
   (\<forall>u \<in> set (fst (tr_args_m p dm env n S ts)). cok u)\<close>
proof (induction p dm env n S t and p dm env n S ts rule: tr_term_m_tr_args_m.induct)
  case (5 p dm env n S d args)
  show ?case
  proof (cases \<open>dpar (sdefs p ! unat d) = []\<close>)
    case True
    then show ?thesis using 5(3-6) by (simp add: tref_def)
  next
    case F: False
    show ?thesis
    proof (cases \<open>unat d < n\<close>)
      case True
      have A: \<open>\<forall>a \<in> set (fst (tr_args_m p dm env n S args)). cok a\<close>
        using 5(1)[OF F True] 5(3-6) by simp
      have r: \<open>smt_term_repr (SmtDef_body (sdefs p ! unat d))\<close> using 5(4,5) True by simp
      have B: \<open>(\<forall>a \<in> set (fst (tr_term_m p dm (snd (tr_args_m p dm env n S args)) (unat d) (fst (tr_args_m p dm env n S args))
                   (SmtDef_body (sdefs p ! unat d)))). cok a) \<and>
              cok (snd (tr_term_m p dm (snd (tr_args_m p dm env n S args)) (unat d) (fst (tr_args_m p dm env n S args))
                   (SmtDef_body (sdefs p ! unat d))))\<close>
        using 5(2)[OF F True refl r _ 5(5) A] 5(4) True by simp
      show ?thesis using F True B by (simp add: Let_def)
    next
      case False
      then show ?thesis using F 5(6) by simp
    qed
  qed
next
  case (6 p dm env n S op args)
  then show ?case by (simp add: Let_def cok_tr_app)
next
  case (8 p dm env n S a rest)
  have A: \<open>(\<forall>u \<in> set (fst (tr_term_m p dm env n S a)). cok u) \<and> cok (snd (tr_term_m p dm env n S a))\<close>
    using 8(1) 8(3-6) by simp
  have B: \<open>\<forall>u \<in> set (fst (tr_args_m p dm env n (fst (tr_term_m p dm env n S a) @ [snd (tr_term_m p dm env n S a)]) rest)). cok u\<close>
    using 8(2)[OF refl] 8(3-5) A by simp
  then show ?case by (simp add: Let_def)
qed (simp_all add: tref_def)

lemma cok_defs_fold:
  \<open>(\<forall>d \<in> set ds. d < length (sdefs p)) \<Longrightarrow>
   (\<forall>d < length (sdefs p). smt_term_repr (SmtDef_body (sdefs p ! d))) \<Longrightarrow>
   (\<forall>u \<in> set S. cok u) \<Longrightarrow> \<forall>u \<in> set (fst (foldl (tr_defs_step p) (S, dm) ds)). cok u\<close>
proof (induction ds arbitrary: S dm)
  case Nil
  then show ?case by simp
next
  case (Cons d ds)
  have dl: \<open>d < length (sdefs p)\<close> using Cons.prems(1) by simp
  have c: \<open>\<forall>u \<in> set (fst (tr_defs_step p (S, dm) d)). cok u\<close>
    using cok_tr(1)[of _ d p S dm \<open>[]\<close>] Cons.prems(2,3) dl by (auto simp: tr_defs_step_def Let_def)
  obtain S' dm' where e: \<open>tr_defs_step p (S, dm) d = (S', dm')\<close> by (cases \<open>tr_defs_step p (S, dm) d\<close>)
  show ?case using Cons.IH[of S' dm'] Cons.prems(1,2) c e by simp
qed

lemma cok_asserts_fold:
  \<open>(\<forall>t \<in> set ts. smt_term_repr t) \<Longrightarrow>
   (\<forall>d < length (sdefs p). smt_term_repr (SmtDef_body (sdefs p ! d))) \<Longrightarrow>
   (\<forall>u \<in> set S. cok u) \<Longrightarrow> (\<forall>u \<in> set acc. cok u) \<Longrightarrow>
   (\<forall>u \<in> set (fst (foldl (tr_asserts_step p dm) (S, acc) ts)). cok u) \<and>
   (\<forall>u \<in> set (snd (foldl (tr_asserts_step p dm) (S, acc) ts)). cok u)\<close>
proof (induction ts arbitrary: S acc)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  have c: \<open>(\<forall>u \<in> set (fst (tr_asserts_step p dm (S, acc) t)). cok u) \<and> (\<forall>u \<in> set (snd (tr_asserts_step p dm (S, acc) t)). cok u)\<close>
    using cok_tr(1)[of t \<open>length (sdefs p)\<close> p S dm \<open>[]\<close>] Cons.prems by (auto simp: tr_asserts_step_def Let_def)
  obtain S' acc' where e: \<open>tr_asserts_step p dm (S, acc) t = (S', acc')\<close> by (cases \<open>tr_asserts_step p dm (S, acc) t\<close>)
  show ?case using Cons.IH[of S' acc'] Cons.prems(1,2) c e by simp
qed

lemma cok_problem:
  assumes \<open>smt_repr_ok p\<close>
  shows \<open>\<forall>t \<in> set (ProblemL_defs (tr_problem_m p) @ ProblemL_asserts (tr_problem_m p)). cok t\<close>
proof -
  have rd: \<open>\<forall>d < length (sdefs p). smt_term_repr (SmtDef_body (sdefs p ! d))\<close>
    using assms by (auto simp: smt_repr_ok_def)
  have ra: \<open>\<forall>t \<in> set (sasserts p). smt_term_repr t\<close> using assms by (simp add: smt_repr_ok_def)
  obtain S0 dm where d: \<open>tr_defs_m p = (S0, dm)\<close> by (cases \<open>tr_defs_m p\<close>)
  have c0: \<open>\<forall>u \<in> set S0. cok u\<close>
    using cok_defs_fold[of \<open>[0..<length (sdefs p)]\<close> p \<open>[]\<close> \<open>[]\<close>] rd d by (simp add: tr_defs_m_step)
  note c1 = cok_asserts_fold[OF ra rd c0, of \<open>[]\<close> dm]
  show ?thesis using c1 d by (simp add: tr_problem_m_def tr_asserts_m_step Let_def) blast
qed

text \<open>A value of each sort, for an interpretation of the declared constants.\<close>
definition sdef :: \<open>SmtSort \<Rightarrow> sval\<close> where
  \<open>sdef srt \<equiv>
     (case srt of
        SmtSort_Bool \<Rightarrow> (VBool False)
      | SmtSort_BitVec w \<Rightarrow> (VBv (unat w) 0)
      | SmtSort_Uninterpreted s \<Rightarrow> (VElem 0))\<close>

lemma sdef_simps [simp]:
  \<open>sdef SmtSort_Bool = VBool False\<close>
  \<open>sdef (SmtSort_BitVec w) = VBv (unat w) 0\<close>
  \<open>sdef (SmtSort_Uninterpreted s) = VElem 0\<close>
  by (simp_all add: sdef_def)

lemma sdef_has_sort: \<open>smt_has_sort s (sdef s)\<close>
  by (cases s) auto

lemma problem_wt_tr:
  assumes \<open>smt_wf p\<close> \<open>smt_fragment p\<close> \<open>length (fst (tr_asserts_m p (tr_defs_m p))) < 2 ^ 64\<close>
  shows \<open>problem_wt (tr_problem_m p)\<close>
proof -
  let ?fs = \<open>sfuns p\<close>
  let ?I = \<open>\<lambda>f xs. sdef (SmtFun_ret (?fs ! f))\<close>
  have i: \<open>interp_sound ?fs ?I\<close> by (simp add: interp_sound_def sdef_has_sort)
  show ?thesis
    using tr_problem_sem[OF assms(1,2) i, of \<open>map (\<lambda>f. enc (?I f [])) [0..<length ?fs]\<close>] assms(3) by simp
qed

text \<open>A fuel sufficient for \<^verbatim>\<open>size_ok\<close>.\<close>
definition fuel_q :: \<open>ProblemL \<Rightarrow> nat\<close> where
  \<open>fuel_q q \<equiv> 64 + Suc (length (ProblemL_widths q) + length (ProblemL_defs q) + length (ProblemL_asserts q) +
     sum_list (map size (ProblemL_defs q)) + sum_list (map size (ProblemL_asserts q)))\<close>

text \<open>A fuel sufficient for \<^verbatim>\<open>tr_size\<close>.\<close>
definition fuel_smt :: \<open>SmtProblem \<Rightarrow> nat\<close> where
  \<open>fuel_smt p \<equiv> Suc (length (sdefs p) + length (sasserts p) +
     sum_list (map (size \<circ> SmtDef_body) (sdefs p)) + sum_list (map size (sasserts p)))\<close>

context QFBV_ctx
begin

lemma size_pre_of_wt:
  assumes \<open>problem_wt q\<close> \<open>\<forall>t \<in> set (ProblemL_defs q @ ProblemL_asserts q). cok t\<close>
    \<open>length (ProblemL_widths q) < 2 ^ 63\<close> \<open>length (ProblemL_defs q) < 2 ^ 63\<close>
    \<open>length (ProblemL_asserts q) < 2 ^ 63\<close> \<open>fuel_q q \<le> F\<close>
  shows \<open>size_pre F q\<close>
proof -
  let ?ws = \<open>map unat (ProblemL_widths q)\<close> and ?ds = \<open>ProblemL_defs q\<close> and ?as = \<open>ProblemL_asserts q\<close>
  have dw: \<open>defs_wt ?ws [] ?ds\<close> and aw: \<open>\<forall>t \<in> set ?as. wt ?ws (def_widths ?ws [] ?ds) t\<close>
    using assms(1) by (auto simp: problem_wt_def var_widths_def Let_def)
  have td: \<open>tix (length (ProblemL_widths q)) d (?ds ! d)\<close> if \<open>d < length ?ds\<close> for d
    using wt_tix[OF defs_wt_nth[OF dw that]] assms(2) that by (simp add: def_widths_length')
  have ta: \<open>tix (length (ProblemL_widths q)) (length ?ds) t\<close> if \<open>t \<in> set ?as\<close> for t
    using wt_tix[of ?ws \<open>def_widths ?ws [] ?ds\<close> t] aw assms(2) that by (simp add: def_widths_length')
  have sd: \<open>Suc (size (?ds ! d)) \<le> F\<close> if \<open>d < length ?ds\<close> for d
  proof -
    have m: \<open>size (?ds ! d) \<in> set (map size ?ds)\<close> using that by simp
    have \<open>size (?ds ! d) \<le> sum_list (map size ?ds)\<close> by (meson m member_le_sum_list zero_le)
    then show ?thesis using assms(6) by (simp add: fuel_q_def)
  qed
  have sa: \<open>Suc (size t) \<le> F\<close> if \<open>t \<in> set ?as\<close> for t
  proof -
    have m: \<open>size t \<in> set (map size ?as)\<close> using that by simp
    have \<open>size t \<le> sum_list (map size ?as)\<close> by (meson m member_le_sum_list zero_le)
    then show ?thesis using assms(6) by (simp add: fuel_q_def)
  qed
  show ?thesis using td ta sd sa assms(3-6) by (simp add: size_pre_def Let_def fuel_q_def)
qed

lemma tsize_pre_of_wf:
  assumes \<open>smt_wf p\<close> \<open>smt_repr_ok p\<close> \<open>fuel_smt p \<le> F\<close>
  shows \<open>tsize_pre F p\<close>
proof -
  let ?fs = \<open>sfuns p\<close> and ?ds = \<open>sdefs p\<close> and ?as = \<open>sasserts p\<close>
  have sd: \<open>Suc (size (SmtDef_body (?ds ! d))) \<le> F\<close> if \<open>d < length ?ds\<close> for d
  proof -
    have m: \<open>size (SmtDef_body (?ds ! d)) \<in> set (map (size \<circ> SmtDef_body) ?ds)\<close>
      using that by (metis (no_types) image_eqI comp_apply list.set_map nth_mem)
    have \<open>size (SmtDef_body (?ds ! d)) \<le> sum_list (map (size \<circ> SmtDef_body) ?ds)\<close>
      by (meson m member_le_sum_list zero_le)
    then show ?thesis using assms(3) by (simp add: fuel_smt_def)
  qed
  have sa: \<open>Suc (size t) \<le> F\<close> if \<open>t \<in> set ?as\<close> for t
  proof -
    have m: \<open>size t \<in> set (map size ?as)\<close> using that by simp
    have \<open>size t \<le> sum_list (map size ?as)\<close> by (meson m member_le_sum_list zero_le)
    then show ?thesis using assms(3) by (simp add: fuel_smt_def)
  qed
  have rd: \<open>smt_term_repr (SmtDef_body (?ds ! d))\<close> if \<open>d < length ?ds\<close> for d
    using assms(2) that by (auto simp: smt_repr_ok_def)
  have ra: \<open>smt_term_repr t\<close> if \<open>t \<in> set ?as\<close> for t
    using assms(2) that by (auto simp: smt_repr_ok_def)
  have td: \<open>smt_tsort ?fs (take d ?ds) (dpar (?ds ! d)) (SmtDef_body (?ds ! d)) \<noteq> None\<close>
    if \<open>d < length ?ds\<close> for d
    using assms(1) that by (auto simp: smt_wf_def Let_def)
  have ta: \<open>smt_tsort ?fs ?ds [] t \<noteq> None\<close> if \<open>t \<in> set ?as\<close> for t
    using assms(1) that by (auto simp: smt_wf_def Let_def)
  have dd: \<open>dok d F (SmtDef_body (?ds ! d))\<close> if \<open>d < length ?ds\<close> for d
    using tsort_dok[OF td[OF that] rd[OF that]] sd[OF that] that by simp
  have da: \<open>dok (length ?ds) F t\<close> if \<open>t \<in> set ?as\<close> for t
    using tsort_dok[OF ta[OF that] ra[OF that]] sa[OF that] by simp
  have po: \<open>params_ok p\<close> using assms(2) by (auto simp: smt_repr_ok_def params_ok_def)
  have ln: \<open>length ?ds < 2 ^ 63\<close> \<open>length ?as < 2 ^ 63\<close> using assms(2) by (simp_all add: smt_repr_ok_def)
  have lf: \<open>length ?ds \<le> F\<close> \<open>length ?as \<le> F\<close> using assms(3) by (simp_all add: fuel_smt_def)
  show ?thesis using sd sa dd da po ln lf by (simp add: tsize_pre_def Let_def)
qed


end

end
