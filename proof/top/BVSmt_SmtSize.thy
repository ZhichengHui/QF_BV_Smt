theory BVSmt_SmtSize
  imports "BVSmt_Smt.BVSmt_SmtModel"
begin

section \<open>The size checks of \<^verbatim>\<open>check_sat\<close>\<close>

text \<open>The Rust functions \<^verbatim>\<open>tr_size\<close> and \<^verbatim>\<open>size_ok\<close> compute, with additions and multiplications
  that saturate at \<open>2^63\<close>, the number of definitions of the translation of a problem and the
  \<^const>\<open>size_bound\<close> of the translated problem. Each Rust function computes \<open>sat\<close> of an
  exact value defined here.\<close>

subsection \<open>Saturation\<close>

definition sat :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>sat x \<equiv> min x (2 ^ 63)\<close>

lemma sat_0: \<open>sat 0 = 0\<close>
  by (simp add: sat_def)

lemma word_eq_of_unat: \<open>unat x = y \<Longrightarrow> x = (word_of_nat y :: 64 word)\<close>
  by auto

lemma sat_le: \<open>sat x \<le> 2 ^ 63\<close>
  by (simp add: sat_def)

lemma sat_lt_iff: \<open>(sat x < 2 ^ 63) = (x < 2 ^ 63)\<close>
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
  proof (cases \<open>x * y < 2 ^ 63\<close>)
    case True
    have xc: \<open>x < 2 ^ 63\<close> using True y1 by (metis le_less_trans mult_le_mono2 nat_mult_1_right)
    have yc: \<open>y < 2 ^ 63\<close> using True x1 by (metis le_less_trans mult_le_mono1 nat_mult_1)
    show ?thesis using True xc yc by (simp add: sat_def)
  next
    case False
    have \<open>2 ^ 63 \<le> min x (2 ^ 63) * min y (2 ^ 63)\<close>
    proof (cases \<open>x < 2 ^ 63\<close>; cases \<open>y < 2 ^ 63\<close>)
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
  shows \<open>a \<noteq> 0 \<Longrightarrow> 9223372036854775808 \<le> unat b \<Longrightarrow> 9223372036854775808 \<le> unat a * unat b\<close>
    and \<open>b \<noteq> 0 \<Longrightarrow> 9223372036854775808 \<le> unat a \<Longrightarrow> 9223372036854775808 \<le> unat a * unat b\<close>
    and \<open>a \<noteq> 0 \<Longrightarrow> 9223372036854775807 div unat a < unat b \<Longrightarrow> 9223372036854775808 \<le> unat a * unat b\<close>
proof -
  show \<open>a \<noteq> 0 \<Longrightarrow> 9223372036854775808 \<le> unat b \<Longrightarrow> 9223372036854775808 \<le> unat a * unat b\<close>
    by (rule ge_mul_left) (simp_all add: Suc_le_eq unat_gt_0)
  show \<open>b \<noteq> 0 \<Longrightarrow> 9223372036854775808 \<le> unat a \<Longrightarrow> 9223372036854775808 \<le> unat a * unat b\<close>
    by (rule ge_mul_right) (simp_all add: Suc_le_eq unat_gt_0)
  assume a0: \<open>a \<noteq> 0\<close> and lt: \<open>9223372036854775807 div unat a < unat b\<close>
  have \<open>0 < unat a\<close> using a0 by (simp add: unat_gt_0)
  then have \<open>\<not> unat a * unat b \<le> 9223372036854775807\<close> using lt le_div_iff_mul[of \<open>unat a\<close> \<open>unat b\<close> 9223372036854775807] by (meson not_le)
  then show \<open>9223372036854775808 \<le> unat a * unat b\<close> by simp
qed

subsection \<open>The number of definitions of the translation\<close>

text \<open>The number of definitions the translation of a term adds, with the definitions below \<open>n\<close>
  expanded (as \<^const>\<open>tr_term_m\<close>).\<close>
function (sequential) cnt :: \<open>SmtProblem \<Rightarrow> nat \<Rightarrow> SmtTerm \<Rightarrow> nat\<close>
  and cnt_args :: \<open>SmtProblem \<Rightarrow> nat \<Rightarrow> SmtTerm list \<Rightarrow> nat\<close>
  where
  \<open>cnt p n (SmtTerm_Def d args) =
     (if SmtDef_params (SmtProblem_defs p ! unat d) = [] then 0
      else if unat d < n then cnt_args p n args + cnt p (unat d) (SmtDef_body (SmtProblem_defs p ! unat d))
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
     sum_list (map (\<lambda>d. if SmtDef_params (SmtProblem_defs p ! d) = []
                         then Suc (cnt p d (SmtDef_body (SmtProblem_defs p ! d))) else 0)
                [0..<length (SmtProblem_defs p)]) +
     sum_list (map (cnt p (length (SmtProblem_defs p))) (SmtProblem_asserts p))\<close>

text \<open>The definitions part of \<^const>\<open>tsize\<close> for the first \<open>d\<close> definitions.\<close>
definition dsum :: \<open>SmtProblem \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>dsum p d \<equiv> sum_list (map (\<lambda>i. if SmtDef_params (SmtProblem_defs p ! i) = []
                                   then Suc (cnt p i (SmtDef_body (SmtProblem_defs p ! i))) else 0) [0..<d])\<close>

lemma dsum_0: \<open>dsum p 0 = 0\<close>
  by (simp add: dsum_def)

lemma dsum_Suc: \<open>dsum p (Suc d) = dsum p d +
  (if SmtDef_params (SmtProblem_defs p ! d) = [] then Suc (cnt p d (SmtDef_body (SmtProblem_defs p ! d))) else 0)\<close>
  by (simp add: dsum_def)

lemma tsize_dsum: \<open>tsize p = dsum p (length (SmtProblem_defs p)) +
  sum_list (map (cnt p (length (SmtProblem_defs p))) (SmtProblem_asserts p))\<close>
  by (simp add: tsize_def dsum_def)

lemma tr_defs_length:
  \<open>length (fst (foldl (tr_defs_step p) (S, dm) ds)) =
     length S + sum_list (map (\<lambda>d. if SmtDef_params (SmtProblem_defs p ! d) = []
                                    then Suc (cnt p d (SmtDef_body (SmtProblem_defs p ! d))) else 0) ds)\<close>
  by (induction ds arbitrary: S dm) (auto simp: tr_defs_step_def Let_def tr_term_args_length)

lemma tr_asserts_length:
  \<open>length (fst (foldl (tr_asserts_step p dm) (S, acc) ts)) =
     length S + sum_list (map (cnt p (length (SmtProblem_defs p))) ts)\<close>
  by (induction ts arbitrary: S acc) (auto simp: tr_asserts_step_def Let_def tr_term_args_length)

lemma tsize_length: \<open>length (fst (tr_asserts_m p (tr_defs_m p))) = tsize p\<close>
proof -
  obtain S dm where d: \<open>tr_defs_m p = (S, dm)\<close> by (cases \<open>tr_defs_m p\<close>)
  have \<open>length S = sum_list (map (\<lambda>d. if SmtDef_params (SmtProblem_defs p ! d) = []
                                    then Suc (cnt p d (SmtDef_body (SmtProblem_defs p ! d))) else 0)
                         [0..<length (SmtProblem_defs p)])\<close>
    using tr_defs_length[of p \<open>[]\<close> \<open>[]\<close> \<open>[0..<length (SmtProblem_defs p)]\<close>] d by (simp add: tr_defs_m_step)
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
  \<open>params_ok p \<equiv> \<forall>e \<in> set (SmtProblem_defs p). length (SmtDef_params e) < 2 ^ 64\<close>

lemma params_ok_nth: \<open>params_ok p \<Longrightarrow> d < length (SmtProblem_defs p) \<Longrightarrow>
  ((word_of_nat (length (SmtDef_params (SmtProblem_defs p ! d))) :: 64 word) = 0) = (SmtDef_params (SmtProblem_defs p ! d) = [])\<close>
proof -
  assume a: \<open>params_ok p\<close> and b: \<open>d < length (SmtProblem_defs p)\<close>
  have L: \<open>length (SmtDef_params (SmtProblem_defs p ! d)) < 2 ^ 64\<close> using a b by (simp add: params_ok_def)
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
  \<open>dcv p d \<equiv> if SmtDef_params (SmtProblem_defs p ! d) = [] then 0 else sat (cnt p d (SmtDef_body (SmtProblem_defs p ! d)))\<close>

definition dcw :: \<open>SmtProblem \<Rightarrow> nat \<Rightarrow> 64 word list\<close> where
  \<open>dcw p n \<equiv> map (\<lambda>d. word_of_nat (dcv p d)) [0..<n]\<close>

lemma dcv_le: \<open>dcv p d \<le> 2 ^ 63\<close>
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
fun tix :: \<open>nat \<Rightarrow> nat \<Rightarrow> Term \<Rightarrow> bool\<close> where
  \<open>tix nw nd (Term_Const bs) = (length bs < 2 ^ 64)\<close>
| \<open>tix nw nd (Term_Var i) = (unat i < nw)\<close>
| \<open>tix nw nd (Term_Ref i) = (unat i < nd)\<close>
| \<open>tix nw nd (Term_Not a) = tix nw nd a\<close>
| \<open>tix nw nd (Term_Neg a) = tix nw nd a\<close>
| \<open>tix nw nd (Term_Bin op a b) = (tix nw nd a \<and> tix nw nd b)\<close>
| \<open>tix nw nd (Term_Extract hi lo a) = (unat lo \<le> unat hi \<and> tix nw nd a)\<close>
| \<open>tix nw nd (Term_Repeat i a) = tix nw nd a\<close>
| \<open>tix nw nd (Term_ZeroExtend i a) = tix nw nd a\<close>
| \<open>tix nw nd (Term_SignExtend i a) = tix nw nd a\<close>
| \<open>tix nw nd (Term_RotateLeft i a) = tix nw nd a\<close>
| \<open>tix nw nd (Term_RotateRight i a) = tix nw nd a\<close>
| \<open>tix nw nd (Term_Ite c a b) = (tix nw nd c \<and> tix nw nd a \<and> tix nw nd b)\<close>

lemma term_weight_simps:
  \<open>term_weight ws ds t =
     (width ws ds t + 1) ^ 3 +
     (case t of Term_Not a \<Rightarrow> term_weight ws ds a | Term_Neg a \<Rightarrow> term_weight ws ds a
      | Term_Bin op a b \<Rightarrow> term_weight ws ds a + term_weight ws ds b
      | Term_Extract hi lo a \<Rightarrow> term_weight ws ds a | Term_Repeat i a \<Rightarrow> term_weight ws ds a
      | Term_ZeroExtend i a \<Rightarrow> term_weight ws ds a | Term_SignExtend i a \<Rightarrow> term_weight ws ds a
      | Term_RotateLeft i a \<Rightarrow> term_weight ws ds a | Term_RotateRight i a \<Rightarrow> term_weight ws ds a
      | Term_Ite c a b \<Rightarrow> term_weight ws ds c + term_weight ws ds a + term_weight ws ds b
      | _ \<Rightarrow> 0)\<close>
  by (cases t) (simp_all add: term_weight_def)

text \<open>The saturated width and weight of a term depend only on the saturated widths of the
  definitions.\<close>
definition sat_eq :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> bool\<close> where
  \<open>sat_eq A B \<equiv> length A = length B \<and> (\<forall>i < length A. sat (A ! i) = sat (B ! i))\<close>

lemma sat_width_cong: \<open>sat_eq A B \<Longrightarrow> tix nw (length A) t \<Longrightarrow> sat (width ws A t) = sat (width ws B t)\<close>
  by (induction t) (auto simp: sat_eq_def split: Op.splits intro: sat_add_cong sat_mul_cong)

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

lemma width_Bin_opw: \<open>width ws ds (Term_Bin op a b) = opw op (width ws ds a) (width ws ds b)\<close>
  by (simp add: opw_def)

lemma sat_opw_cong: \<open>sat x = sat x' \<Longrightarrow> sat y = sat y' \<Longrightarrow> sat (opw op x y) = sat (opw op x' y')\<close>
  by (cases op) (auto simp: opw_def intro: sat_add_cong)

lemma term_weight_eqs:
  \<open>term_weight ws ds (Term_Const bs) = (length bs + 1) ^ 3\<close>
  \<open>term_weight ws ds (Term_Var i) = (width ws ds (Term_Var i) + 1) ^ 3\<close>
  \<open>term_weight ws ds (Term_Ref i) = (width ws ds (Term_Ref i) + 1) ^ 3\<close>
  \<open>term_weight ws ds (Term_Not a) = (width ws ds a + 1) ^ 3 + term_weight ws ds a\<close>
  \<open>term_weight ws ds (Term_Neg a) = (width ws ds a + 1) ^ 3 + term_weight ws ds a\<close>
  \<open>term_weight ws ds (Term_Bin op a b) =
     (opw op (width ws ds a) (width ws ds b) + 1) ^ 3 + (term_weight ws ds a + term_weight ws ds b)\<close>
  \<open>term_weight ws ds (Term_Extract hi lo a) = (unat hi - unat lo + 1 + 1) ^ 3 + term_weight ws ds a\<close>
  \<open>term_weight ws ds (Term_Repeat i a) = (unat i * width ws ds a + 1) ^ 3 + term_weight ws ds a\<close>
  \<open>term_weight ws ds (Term_ZeroExtend i a) = (width ws ds a + unat i + 1) ^ 3 + term_weight ws ds a\<close>
  \<open>term_weight ws ds (Term_SignExtend i a) = (width ws ds a + unat i + 1) ^ 3 + term_weight ws ds a\<close>
  \<open>term_weight ws ds (Term_RotateLeft i a) = (width ws ds a + 1) ^ 3 + term_weight ws ds a\<close>
  \<open>term_weight ws ds (Term_RotateRight i a) = (width ws ds a + 1) ^ 3 + term_weight ws ds a\<close>
  \<open>term_weight ws ds (Term_Ite c a b) =
     (width ws ds a + 1) ^ 3 + (term_weight ws ds c + (term_weight ws ds a + term_weight ws ds b))\<close>
  by (simp_all add: term_weight_def opw_def)

text \<open>The last step of every case of \<^verbatim>\<open>term_size\<close>: the weight is the cube of the width plus one,
  plus the weights of the operands.\<close>
lemma final_step:
  \<open>sat (unat w) = sat W \<Longrightarrow> unat c = sat ((unat w + 1) ^ 3) \<Longrightarrow> unat g = sat G \<Longrightarrow>
   sat (unat c + unat g) = sat ((W + 1) ^ 3 + G)\<close>
  by (metis sat_add_sat sat_cube_cong)

lemma final_eq: \<open>sat x = sat X \<Longrightarrow> sat (sat (Suc x ^ 3) + sat G) = sat ((X + 1) ^ 3 + G)\<close>
  by (metis Suc_eq_plus1 sat_add_sat sat_cube_cong)

lemma cube_plus: \<open>sat x = sat X \<Longrightarrow> sat (Suc x ^ 3 + G) = sat (Suc X ^ 3 + G)\<close>
  by (metis Suc_eq_plus1 sat_add_cong sat_cube_cong)

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

text \<open>The parts of \<^const>\<open>size_bound\<close>.\<close>
definition base :: \<open>Problem \<Rightarrow> nat\<close> where
  \<open>base q \<equiv> Suc (sum_list (map unat (Problem_widths q)) + length (Problem_widths q) + length (Problem_defs q) +
                 length (Problem_asserts q))\<close>

definition DSq :: \<open>Problem \<Rightarrow> nat list\<close> where
  \<open>DSq q \<equiv> def_widths (map unat (Problem_widths q)) [] (Problem_defs q)\<close>

lemma size_bound_eq:
  \<open>size_bound q = 1000000 * (base q + sum_list (map (term_weight (map unat (Problem_widths q)) (DSq q)) (Problem_defs q)) +
     sum_list (map (term_weight (map unat (Problem_widths q)) (DSq q)) (Problem_asserts q)))\<close>
  by (simp add: size_bound_def var_widths_def base_def DSq_def Let_def)

lemma tix_subterms: \<open>tix nw nd t \<Longrightarrow> u \<in> set (subterms t) \<Longrightarrow> tix nw nd u\<close>
  by (induction t) auto

lemma sat_weight_cong: \<open>sat_eq A B \<Longrightarrow> tix nw (length A) t \<Longrightarrow> sat (term_weight ws A t) = sat (term_weight ws B t)\<close>
proof -
  assume E: \<open>sat_eq A B\<close> and T: \<open>tix nw (length A) t\<close>
  show ?thesis unfolding term_weight_def
  proof (rule sat_sum_cong, intro ballI)
    fix u assume \<open>u \<in> set (subterms t)\<close>
    then have \<open>tix nw (length A) u\<close> using T tix_subterms by blast
    then show \<open>sat ((width ws A u + 1) ^ 3) = sat ((width ws B u + 1) ^ 3)\<close>
      using sat_width_cong[OF E] by (blast intro: sat_cube_cong)
  qed
qed

lemma weight_add:
  \<open>sat_eq (map unat ds) D \<Longrightarrow> tix nw (length ds) t \<Longrightarrow> unat g = sat (term_weight ws (map unat ds) t) \<Longrightarrow>
   sat (sat X + unat g) = sat (X + term_weight ws D t)\<close>
  by (metis sat_add_sat sat_weight_cong length_map)

lemma final_cmp: \<open>(sat (1000000 * sat X) < 9223372036854775808) = (1000000 * X < 9223372036854775808)\<close>
proof -
  have \<open>sat (1000000 :: nat) = 1000000\<close> by (simp add: sat_def)
  then have \<open>sat (1000000 * sat X) = sat (1000000 * X)\<close> by (metis sat_mul_sat)
  then show ?thesis by (simp add: sat_def min_less_iff_disj)
qed

lemma weight_add':
  \<open>sat_eq (map unat ds) D \<Longrightarrow> tix nw (length ds) t \<Longrightarrow>
   sat (sat X + sat (term_weight ws (map unat ds) t)) = sat (X + term_weight ws D t)\<close>
  by (metis sat_add_sat sat_weight_cong length_map)

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
   (\<forall>t \<in> set (Problem_asserts q). tix nw (length (Problem_defs q)) t \<and> P t) \<Longrightarrow>
   t \<in> set (Problem_asserts q) \<Longrightarrow> tix nw (length ds) t\<close>
  unfolding DSq_def using tix_full_asserts by blast

lemma tix_full:
  \<open>sat_eq (map unat ds) (def_widths ws [] xs) \<Longrightarrow> (\<forall>d < length xs. tix nw d (xs ! d) \<and> P d) \<Longrightarrow>
   \<forall>k < length xs. tix nw (length ds) (xs ! k)\<close>
proof -
  assume e: \<open>sat_eq (map unat ds) (def_widths ws [] xs)\<close> and a: \<open>\<forall>d < length xs. tix nw d (xs ! d) \<and> P d\<close>
  have l: \<open>length ds = length xs\<close> using sat_eq_length[OF e] by (simp add: def_widths_length')
  show ?thesis using a l by (auto intro: tix_mono)
qed

context BVSmt_ctx
begin

subsection \<open>Saturating arithmetic\<close>

definition cap_contract :: \<open>('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>cap_contract \<equiv>
     make_function_contract can_alloc_reference (\<lambda>r. can_alloc_reference \<star> \<langle>unat r = 2 ^ 63\<rangle>)\<close>

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
        \<langle>Suc (size t) \<le> k \<and> dc = dcw p (length dc) \<and> length dc \<le> length (SmtProblem_defs p) \<and>
         params_ok p \<and> dok (length dc) urust_fuel t\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>unat r = sat (cnt p (length dc) t)\<rangle>)\<close>

definition tr_count_args_contract :: \<open>nat \<Rightarrow> SmtProblem \<Rightarrow> 64 word list \<Rightarrow> SmtTerm list \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>tr_count_args_contract k p dc ts \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
        \<langle>Suc (size_list size ts) \<le> k \<and> dc = dcw p (length dc) \<and> length dc \<le> length (SmtProblem_defs p) \<and>
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
     let ds = SmtProblem_defs p in
     params_ok p \<and> length ds < 2 ^ 63 \<and> length ds \<le> F \<and>
     length (SmtProblem_asserts p) < 2 ^ 63 \<and> length (SmtProblem_asserts p) \<le> F \<and>
     (\<forall>d < length ds. dok d F (SmtDef_body (ds ! d)) \<and> Suc (size (SmtDef_body (ds ! d))) \<le> F) \<and>
     (\<forall>t \<in> set (SmtProblem_asserts p). dok (length ds) F t \<and> Suc (size t) \<le> F)\<close>

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
               \<langle>unat d \<le> length (SmtProblem_defs p) \<and> c = dcw p (unat d) \<and> unat n = sat (dsum p (unat d)) \<and>
                length (SmtProblem_defs p) - unat d \<le> j\<rangle>\<close> and
        INV'=\<open>\<lambda>j. \<Squnion>gc c gn n gd d. dc_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c \<star> n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star> d_ref \<mapsto>\<langle>\<top>\<rangle> gd\<down>d \<star>
               can_alloc_reference \<star>
               \<langle>unat d < length (SmtProblem_defs p) \<and> c = dcw p (unat d) \<and> unat n = sat (dsum p (unat d)) \<and>
                length (SmtProblem_defs p) - unat d \<le> Suc j\<rangle>\<close> and
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
          INV=\<open>\<lambda>j. \<Squnion>gc gn n gj jj. dc_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>dcw p (length (SmtProblem_defs p)) \<star>
                 n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>jj \<star> can_alloc_reference \<star>
                 \<langle>unat jj \<le> length (SmtProblem_asserts p) \<and>
                  unat n = sat (dsum p (length (SmtProblem_defs p)) +
                     sum_list (map (cnt p (length (SmtProblem_defs p))) (take (unat jj) (SmtProblem_asserts p)))) \<and>
                  length (SmtProblem_asserts p) - unat jj \<le> j\<rangle>\<close> and
          INV'=\<open>\<lambda>j. \<Squnion>gc gn n gj jj. dc_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>dcw p (length (SmtProblem_defs p)) \<star>
                 n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>jj \<star> can_alloc_reference \<star>
                 \<langle>unat jj < length (SmtProblem_asserts p) \<and>
                  unat n = sat (dsum p (length (SmtProblem_defs p)) +
                     sum_list (map (cnt p (length (SmtProblem_defs p))) (take (unat jj) (SmtProblem_asserts p)))) \<and>
                  length (SmtProblem_asserts p) - unat jj \<le> Suc j\<rangle>\<close> and
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

definition cube1_contract :: \<open>64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>cube1_contract w \<equiv>
     make_function_contract can_alloc_reference
       (\<lambda>r. can_alloc_reference \<star> \<langle>unat r = sat ((unat w + 1) ^ 3)\<rangle>)\<close>

lemma cube1_spec [crush_specs]:
  shows \<open>\<Gamma>; cube1 w \<Turnstile>\<^sub>F cube1_contract w\<close>
  apply (crush_boot f: cube1_def contract: cube1_contract_def)
  apply (crush_base)
  apply (simp only: sat_mul_sat power3_eq_cube mult.assoc)
  done

definition op_width_contract :: \<open>Op \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>op_width_contract op a b \<equiv>
     make_function_contract can_alloc_reference
       (\<lambda>r. can_alloc_reference \<star> \<langle>sat (unat r) = sat (opw op (unat a) (unat b))\<rangle>)\<close>

lemma op_width_spec [crush_specs]:
  shows \<open>\<Gamma>; op_width op a b \<Turnstile>\<^sub>F op_width_contract op a b\<close>
  apply (crush_boot f: op_width_def contract: op_width_contract_def)
  apply (cases op; simp only: Op.case)
  apply (crush_base simp add: opw_def sat_sat)+
  done

text \<open>The \<open>k\<close>-th unfolding of \<^verbatim>\<open>term_size\<close>. The width it returns is exact up to saturation
  (for a variable it is the declared width itself), the weight is saturated.\<close>
definition term_size_contract ::
  \<open>nat \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> Term \<Rightarrow> ('s, 64 word \<times> 64 word \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>term_size_contract k ws ds t \<equiv>
     make_function_contract
       (can_alloc_reference \<star> \<langle>Suc (size t) \<le> k \<and> tix (length ws) (length ds) t\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>sat (unat (fst r)) = sat (width (map unat ws) (map unat ds) t) \<and>
           unat (fst (snd r)) = sat (term_weight (map unat ws) (map unat ds) t)\<rangle>)\<close>

lemma term_size_step_spec:
  assumes IH: \<open>\<And>ws ds t. \<Gamma>; R ws ds t \<Turnstile>\<^sub>F term_size_contract k ws ds t\<close>
  shows \<open>\<Gamma>; term_size_rec_step R ws ds t \<Turnstile>\<^sub>F term_size_contract (Suc k) ws ds t\<close>
proof (cases t)
  case (Term_Const bs)
  show ?thesis unfolding Term_Const
    apply (crush_boot f: term_size_rec_step_def contract: term_size_contract_def)
    apply (crush_base specs add: IH simp add: term_weight_eqs sat_add_sat sat_sat)
    apply (auto simp: unat_of_nat_eq)
    done
next
  case (Term_Var i)
  show ?thesis unfolding Term_Var
    apply (crush_boot f: term_size_rec_step_def contract: term_size_contract_def)
    apply (crush_base specs add: IH simp add: term_weight_eqs sat_add_sat sat_sat)
    done
next
  case (Term_Ref i)
  show ?thesis unfolding Term_Ref
    apply (crush_boot f: term_size_rec_step_def contract: term_size_contract_def)
    apply (crush_base specs add: IH simp add: term_weight_eqs sat_add_sat sat_sat)
    done
next
  case (Term_Not a)
  show ?thesis unfolding Term_Not
    apply (crush_boot f: term_size_rec_step_def contract: term_size_contract_def)
    apply (crush_base specs add: IH simp add: term_weight_eqs sat_add_sat sat_sat)
    apply (auto intro!: cube_plus)
    done
next
  case (Term_Neg a)
  show ?thesis unfolding Term_Neg
    apply (crush_boot f: term_size_rec_step_def contract: term_size_contract_def)
    apply (crush_base specs add: IH simp add: term_weight_eqs sat_add_sat sat_sat)
    apply (auto intro!: cube_plus)
    done
next
  case (Term_Bin op a b)
  show ?thesis unfolding Term_Bin
    apply (crush_boot f: term_size_rec_step_def contract: term_size_contract_def)
    apply (crush_base specs add: IH simp add: term_weight_eqs sat_add_sat sat_sat width_Bin_opw simp del: width.simps)
     apply (rule cube_plus, rule opw_chain, assumption+)
    apply (unfold opw_def[symmetric])
    apply (rule sat_opw_cong; assumption)
    done
next
  case (Term_Extract hi lo a)
  show ?thesis unfolding Term_Extract
    apply (crush_boot f: term_size_rec_step_def contract: term_size_contract_def)
    apply (crush_base specs add: IH simp add: term_weight_eqs sat_add_sat sat_sat word_le_nat_alt)
    apply (auto simp: sat_sat unat_sub_le intro!: cube_plus)
    done
next
  case (Term_Repeat i a)
  show ?thesis unfolding Term_Repeat
    apply (crush_boot f: term_size_rec_step_def contract: term_size_contract_def)
    apply (crush_base specs add: IH simp add: term_weight_eqs sat_add_sat sat_sat)
    apply (auto simp: sat_sat intro!: cube_plus sat_mul_cong)
    done
next
  case (Term_ZeroExtend i a)
  show ?thesis unfolding Term_ZeroExtend
    apply (crush_boot f: term_size_rec_step_def contract: term_size_contract_def)
    apply (crush_base specs add: IH simp add: term_weight_eqs sat_add_sat sat_sat)
    apply (auto simp: sat_sat intro!: cube_plus sat_add_cong)
    done
next
  case (Term_SignExtend i a)
  show ?thesis unfolding Term_SignExtend
    apply (crush_boot f: term_size_rec_step_def contract: term_size_contract_def)
    apply (crush_base specs add: IH simp add: term_weight_eqs sat_add_sat sat_sat)
    apply (auto simp: sat_sat intro!: cube_plus sat_add_cong)
    done
next
  case (Term_RotateLeft i a)
  show ?thesis unfolding Term_RotateLeft
    apply (crush_boot f: term_size_rec_step_def contract: term_size_contract_def)
    apply (crush_base specs add: IH simp add: term_weight_eqs sat_add_sat sat_sat)
    apply (auto intro!: cube_plus)
    done
next
  case (Term_RotateRight i a)
  show ?thesis unfolding Term_RotateRight
    apply (crush_boot f: term_size_rec_step_def contract: term_size_contract_def)
    apply (crush_base specs add: IH simp add: term_weight_eqs sat_add_sat sat_sat)
    apply (auto intro!: cube_plus)
    done
next
  case (Term_Ite c a b)
  show ?thesis unfolding Term_Ite
    apply (crush_boot f: term_size_rec_step_def contract: term_size_contract_def)
    apply (crush_base specs add: IH simp add: term_weight_eqs sat_add_sat sat_sat)
    apply (auto intro!: cube_plus)
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
definition size_pre :: \<open>nat \<Rightarrow> Problem \<Rightarrow> bool\<close> where
  \<open>size_pre F q \<equiv>
     let ws = Problem_widths q; ds = Problem_defs q; ts = Problem_asserts q in
     length ws < 2 ^ 63 \<and> length ws \<le> F \<and> length ds < 2 ^ 63 \<and> length ds \<le> F \<and>
     length ts < 2 ^ 63 \<and> length ts \<le> F \<and>
     (\<forall>d < length ds. tix (length ws) d (ds ! d) \<and> Suc (size (ds ! d)) \<le> F) \<and>
     (\<forall>t \<in> set ts. tix (length ws) (length ds) t \<and> Suc (size t) \<le> F)\<close>

definition size_ok_contract :: \<open>Problem \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>size_ok_contract q \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>size_pre urust_fuel q\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = (size_bound q < 2 ^ 63)\<rangle>)\<close>

lemma size_ok_spec [crush_specs]:
  shows \<open>\<Gamma>; size_ok q \<Turnstile>\<^sub>F size_ok_contract q\<close>
  apply (crush_boot f: size_ok_def contract: size_ok_contract_def)
  apply (crush_base simp add: size_pre_def Let_def)
  subgoal for ds_ref d_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>j. \<Squnion>gs ds gd d. ds_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>ds \<star> d_ref \<mapsto>\<langle>\<top>\<rangle> gd\<down>d \<star> can_alloc_reference \<star>
               \<langle>unat d \<le> length (Problem_defs q) \<and>
                sat_eq (map unat ds) (def_widths (map unat (Problem_widths q)) [] (take (unat d) (Problem_defs q))) \<and>
                length (Problem_defs q) - unat d \<le> j\<rangle>\<close> and
        INV'=\<open>\<lambda>j. \<Squnion>gs ds gd d. ds_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>ds \<star> d_ref \<mapsto>\<langle>\<top>\<rangle> gd\<down>d \<star> can_alloc_reference \<star>
               \<langle>unat d < length (Problem_defs q) \<and>
                sat_eq (map unat ds) (def_widths (map unat (Problem_widths q)) [] (take (unat d) (Problem_defs q))) \<and>
                length (Problem_defs q) - unat d \<le> Suc j\<rangle>\<close> and
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
                 \<langle>unat i \<le> length (Problem_widths q) \<and>
                  unat n = sat (1 + sum_list (map unat (take (unat i) (Problem_widths q)))) \<and>
                  length (Problem_widths q) - unat i \<le> j\<rangle>\<close> and
          INV'=\<open>\<lambda>j. \<Squnion>gn n gi i. n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
                 \<langle>unat i < length (Problem_widths q) \<and>
                  unat n = sat (1 + sum_list (map unat (take (unat i) (Problem_widths q)))) \<and>
                  length (Problem_widths q) - unat i \<le> Suc j\<rangle>\<close> and
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
                   \<langle>unat k \<le> length (Problem_defs q) \<and> sat_eq (map unat ds) (DSq q) \<and>
                    (\<forall>k' < length (Problem_defs q). tix (length (Problem_widths q)) (length ds) (Problem_defs q ! k')) \<and>
                    unat n = sat (base q + sum_list (map (term_weight (map unat (Problem_widths q)) (DSq q))
                                                      (take (unat k) (Problem_defs q)))) \<and>
                    length (Problem_defs q) - unat k \<le> j\<rangle>\<close> and
            INV'=\<open>\<lambda>j. \<Squnion>gs' gn n gk k. ds_ref \<mapsto>\<langle>\<top>\<rangle> gs'\<down>ds \<star> n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star> k_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>k \<star>
                   can_alloc_reference \<star>
                   \<langle>unat k < length (Problem_defs q) \<and> sat_eq (map unat ds) (DSq q) \<and>
                    (\<forall>k' < length (Problem_defs q). tix (length (Problem_widths q)) (length ds) (Problem_defs q ! k')) \<and>
                    unat n = sat (base q + sum_list (map (term_weight (map unat (Problem_widths q)) (DSq q))
                                                      (take (unat k) (Problem_defs q)))) \<and>
                    length (Problem_defs q) - unat k \<le> Suc j\<rangle>\<close> and
            BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
            \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
            \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
          in wp_bounded_while_framedI\<close>)
        apply (crush_base contracts add: term_size_contract_def
            simp add: word_less_nat_alt unat_inc unat_of_nat_eq take_Suc_conv_app_nth base_def weight_add' add.assoc)
        prefer 2
        subgoal for gs' gna n gk k j_ref
          apply (ucincl_discharge\<open>
            rule_tac
              INV=\<open>\<lambda>j. \<Squnion>gs' gn n gj jj. ds_ref \<mapsto>\<langle>\<top>\<rangle> gs'\<down>ds \<star> n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>jj \<star>
                     can_alloc_reference \<star>
                     \<langle>unat jj \<le> length (Problem_asserts q) \<and> sat_eq (map unat ds) (DSq q) \<and>
                      (\<forall>t \<in> set (Problem_asserts q). tix (length (Problem_widths q)) (length ds) t) \<and>
                      unat n = sat (base q +
                        sum_list (map (term_weight (map unat (Problem_widths q)) (DSq q)) (Problem_defs q)) +
                        sum_list (map (term_weight (map unat (Problem_widths q)) (DSq q))
                                   (take (unat jj) (Problem_asserts q)))) \<and>
                      length (Problem_asserts q) - unat jj \<le> j\<rangle>\<close> and
              INV'=\<open>\<lambda>j. \<Squnion>gs' gn n gj jj. ds_ref \<mapsto>\<langle>\<top>\<rangle> gs'\<down>ds \<star> n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>jj \<star>
                     can_alloc_reference \<star>
                     \<langle>unat jj < length (Problem_asserts q) \<and> sat_eq (map unat ds) (DSq q) \<and>
                      (\<forall>t \<in> set (Problem_asserts q). tix (length (Problem_widths q)) (length ds) t) \<and>
                      unat n = sat (base q +
                        sum_list (map (term_weight (map unat (Problem_widths q)) (DSq q)) (Problem_defs q)) +
                        sum_list (map (term_weight (map unat (Problem_widths q)) (DSq q))
                                   (take (unat jj) (Problem_asserts q)))) \<and>
                      length (Problem_asserts q) - unat jj \<le> Suc j\<rangle>\<close> and
              BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
              \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
              \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
            in wp_bounded_while_framedI\<close>)
          apply (crush_base contracts add: term_size_contract_def
              simp add: word_less_nat_alt unat_inc unat_of_nat_eq take_Suc_conv_app_nth base_def weight_add' add.assoc)
          subgoal by (subst weight_add'[where D=\<open>DSq q\<close>]) (auto simp: add.assoc)
          subgoal by (simp add: final_cmp size_bound_eq base_def add.assoc)
          subgoal by (blast intro: tix_assert_q)
          done
        subgoal by (subst weight_add'[where D=\<open>DSq q\<close>]) (auto simp: add.assoc)
        subgoal using tix_full by blast
        subgoal by (simp add: DSq_def)
        done
      done
     apply (auto simp: sat_eq_len_take intro!: width_step)
    done
  done

end

end
