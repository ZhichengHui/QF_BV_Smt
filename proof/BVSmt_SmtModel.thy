theory BVSmt_SmtModel
  imports "BVSmt_Spec.BVSmt_Spec"
begin

section \<open>The translation of general problems: functional model\<close>

text \<open>HOL functions that compute what the Rust functions of the translation (\<^verbatim>\<open>check_sat\<close> and
  its callees in \<^verbatim>\<open>core/src/lib.rs\<close>) compute, with indices as natural numbers. The state of the
  translation is the list of definitions of the extended problem built so far.\<close>

definition tref :: \<open>nat \<Rightarrow> Term\<close> where
  \<open>tref k \<equiv> Term_Ref (word_of_nat k)\<close>

fun tr_op :: \<open>SmtOp \<Rightarrow> Op\<close> where
  \<open>tr_op SmtOp_And = Op_And\<close>
| \<open>tr_op SmtOp_Bvand = Op_And\<close>
| \<open>tr_op SmtOp_Or = Op_Or\<close>
| \<open>tr_op SmtOp_Bvor = Op_Or\<close>
| \<open>tr_op SmtOp_Xor = Op_Xor\<close>
| \<open>tr_op SmtOp_Bvxor = Op_Xor\<close>
| \<open>tr_op SmtOp_Bvnand = Op_Nand\<close>
| \<open>tr_op SmtOp_Bvnor = Op_Nor\<close>
| \<open>tr_op SmtOp_Bvxnor = Op_Xnor\<close>
| \<open>tr_op SmtOp_Bvcomp = Op_Comp\<close>
| \<open>tr_op SmtOp_Bvadd = Op_Add\<close>
| \<open>tr_op SmtOp_Bvsub = Op_Sub\<close>
| \<open>tr_op SmtOp_Bvmul = Op_Mul\<close>
| \<open>tr_op SmtOp_Bvudiv = Op_Udiv\<close>
| \<open>tr_op SmtOp_Bvurem = Op_Urem\<close>
| \<open>tr_op SmtOp_Bvsdiv = Op_Sdiv\<close>
| \<open>tr_op SmtOp_Bvsrem = Op_Srem\<close>
| \<open>tr_op SmtOp_Bvsmod = Op_Smod\<close>
| \<open>tr_op SmtOp_Bvshl = Op_Shl\<close>
| \<open>tr_op SmtOp_Bvlshr = Op_Lshr\<close>
| \<open>tr_op SmtOp_Bvashr = Op_Ashr\<close>
| \<open>tr_op SmtOp_Concat = Op_Concat\<close>
| \<open>tr_op SmtOp_Eq = Op_Eq\<close>
| \<open>tr_op SmtOp_Distinct = Op_Distinct\<close>
| \<open>tr_op SmtOp_Bvult = Op_Ult\<close>
| \<open>tr_op SmtOp_Bvule = Op_Ule\<close>
| \<open>tr_op SmtOp_Bvugt = Op_Ugt\<close>
| \<open>tr_op SmtOp_Bvuge = Op_Uge\<close>
| \<open>tr_op SmtOp_Bvslt = Op_Slt\<close>
| \<open>tr_op SmtOp_Bvsle = Op_Sle\<close>
| \<open>tr_op SmtOp_Bvsgt = Op_Sgt\<close>
| \<open>tr_op SmtOp_Bvsge = Op_Sge\<close>
| \<open>tr_op _ = Op_Eq\<close>

definition fold_left_m :: \<open>SmtOp \<Rightarrow> nat list \<Rightarrow> Term\<close> where
  \<open>fold_left_m op ks \<equiv> foldl (\<lambda>acc k. Term_Bin (tr_op op) acc (tref k)) (tref (hd ks)) (tl ks)\<close>

definition chain_m :: \<open>SmtOp \<Rightarrow> nat list \<Rightarrow> Term\<close> where
  \<open>chain_m op ks \<equiv>
     foldl (\<lambda>acc i. Term_Bin Op_And acc (Term_Bin (tr_op op) (tref (ks ! (i - 1))) (tref (ks ! i))))
       (Term_Bin (tr_op op) (tref (ks ! 0)) (tref (ks ! 1))) [2..<length ks]\<close>

text \<open>The pairs \<open>(i, j)\<close>, \<open>i < j < n\<close>, other than \<open>(0, 1)\<close>, in the order of the two loops of
  \<^verbatim>\<open>pairwise\<close>.\<close>
definition pairs_m :: \<open>nat \<Rightarrow> (nat \<times> nat) list\<close> where
  \<open>pairs_m n \<equiv> filter (\<lambda>ij. ij \<noteq> (0, 1)) (concat (map (\<lambda>i. map (\<lambda>j. (i, j)) [Suc i..<n]) [0..<n]))\<close>

definition pairwise_m :: \<open>nat list \<Rightarrow> Term\<close> where
  \<open>pairwise_m ks \<equiv>
     foldl (\<lambda>acc ij. Term_Bin Op_And acc (Term_Bin Op_Distinct (tref (ks ! fst ij)) (tref (ks ! snd ij))))
       (Term_Bin Op_Distinct (tref (ks ! 0)) (tref (ks ! 1))) (pairs_m (length ks))\<close>

definition implies_m :: \<open>nat list \<Rightarrow> Term\<close> where
  \<open>implies_m ks \<equiv> foldr (\<lambda>k acc. Term_Bin Op_Or (Term_Not (tref k)) acc) (butlast ks) (tref (last ks))\<close>

fun tr_app_m :: \<open>SmtOp \<Rightarrow> nat list \<Rightarrow> Term\<close> where
  \<open>tr_app_m SmtOp_Not ks = Term_Not (tref (ks ! 0))\<close>
| \<open>tr_app_m SmtOp_Bvnot ks = Term_Not (tref (ks ! 0))\<close>
| \<open>tr_app_m SmtOp_Bvneg ks = Term_Neg (tref (ks ! 0))\<close>
| \<open>tr_app_m SmtOp_And ks = fold_left_m SmtOp_And ks\<close>
| \<open>tr_app_m SmtOp_Or ks = fold_left_m SmtOp_Or ks\<close>
| \<open>tr_app_m SmtOp_Xor ks = fold_left_m SmtOp_Xor ks\<close>
| \<open>tr_app_m SmtOp_Bvand ks = fold_left_m SmtOp_Bvand ks\<close>
| \<open>tr_app_m SmtOp_Bvor ks = fold_left_m SmtOp_Bvor ks\<close>
| \<open>tr_app_m SmtOp_Bvadd ks = fold_left_m SmtOp_Bvadd ks\<close>
| \<open>tr_app_m SmtOp_Bvmul ks = fold_left_m SmtOp_Bvmul ks\<close>
| \<open>tr_app_m SmtOp_Implies ks = implies_m ks\<close>
| \<open>tr_app_m SmtOp_Eq ks = chain_m SmtOp_Eq ks\<close>
| \<open>tr_app_m SmtOp_Distinct ks = pairwise_m ks\<close>
| \<open>tr_app_m SmtOp_Ite ks = Term_Ite (tref (ks ! 0)) (tref (ks ! 1)) (tref (ks ! 2))\<close>
| \<open>tr_app_m (SmtOp_Extract i j) ks = Term_Extract i j (tref (ks ! 0))\<close>
| \<open>tr_app_m (SmtOp_Repeat i) ks = Term_Repeat i (tref (ks ! 0))\<close>
| \<open>tr_app_m (SmtOp_ZeroExtend i) ks = Term_ZeroExtend i (tref (ks ! 0))\<close>
| \<open>tr_app_m (SmtOp_SignExtend i) ks = Term_SignExtend i (tref (ks ! 0))\<close>
| \<open>tr_app_m (SmtOp_RotateLeft i) ks = Term_RotateLeft i (tref (ks ! 0))\<close>
| \<open>tr_app_m (SmtOp_RotateRight i) ks = Term_RotateRight i (tref (ks ! 0))\<close>
| \<open>tr_app_m op ks = Term_Bin (tr_op op) (tref (ks ! 0)) (tref (ks ! 1))\<close>

text \<open>The translation of a term and of a list of arguments (each added as a definition). \<open>dm\<close>: the
  definition of each definition without parameters of \<open>p\<close>; \<open>env\<close>: the definitions of the
  parameters in scope; \<open>n\<close>: only definitions below \<open>n\<close> are expanded (the Rust function has no such
  bound; in a well-sorted problem a definition refers only to earlier ones, so the bound is never
  reached).\<close>
function (sequential) tr_term_m :: \<open>SmtProblem \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> Term list \<Rightarrow> SmtTerm \<Rightarrow> Term list \<times> Term\<close>
  and tr_args_m :: \<open>SmtProblem \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> Term list \<Rightarrow> SmtTerm list \<Rightarrow> Term list \<times> nat list\<close>
  where
  \<open>tr_term_m p dm env n S (SmtTerm_BoolConst b) = (S, Term_Const [b])\<close>
| \<open>tr_term_m p dm env n S (SmtTerm_BvConst bs) = (S, Term_Const bs)\<close>
| \<open>tr_term_m p dm env n S (SmtTerm_Param k) = (S, tref (env ! unat k))\<close>
| \<open>tr_term_m p dm env n S (SmtTerm_Fun i args) = (S, Term_Var i)\<close>
| \<open>tr_term_m p dm env n S (SmtTerm_Def d args) =
     (if SmtDef_params (SmtProblem_defs p ! unat d) = [] then (S, tref (dm ! unat d))
      else if unat d < n then
        (let r = tr_args_m p dm env n S args in
         tr_term_m p dm (snd r) (unat d) (fst r) (SmtDef_body (SmtProblem_defs p ! unat d)))
      else (S, Term_Const []))\<close>
| \<open>tr_term_m p dm env n S (SmtTerm_App op args) =
     (let r = tr_args_m p dm env n S args in (fst r, tr_app_m op (snd r)))\<close>
| \<open>tr_args_m p dm env n S [] = (S, [])\<close>
| \<open>tr_args_m p dm env n S (a # rest) =
     (let r1 = tr_term_m p dm env n S a;
          r2 = tr_args_m p dm env n (fst r1 @ [snd r1]) rest in
      (fst r2, length (fst r1) # snd r2))\<close>
  by pat_completeness auto
termination
  by (relation \<open>measures [\<lambda>x. case x of Inl (_, _, _, n, _, _) \<Rightarrow> n | Inr (_, _, _, n, _, _) \<Rightarrow> n,
                          \<lambda>x. case x of Inl (_, _, _, _, _, t) \<Rightarrow> size t | Inr (_, _, _, _, _, ts) \<Rightarrow> size_list size ts]\<close>)
     auto

text \<open>The definitions of the extended problem for the definitions of \<open>p\<close>, in order, and the
  definition of each definition without parameters (0 for one with parameters, which is expanded
  where it is applied).\<close>
definition tr_defs_m :: \<open>SmtProblem \<Rightarrow> Term list \<times> nat list\<close> where
  \<open>tr_defs_m p \<equiv>
     foldl (\<lambda>(S, dm) d.
        if SmtDef_params (SmtProblem_defs p ! d) = [] then
          (let r = tr_term_m p dm [] d S (SmtDef_body (SmtProblem_defs p ! d)) in
           (fst r @ [snd r], dm @ [length (fst r)]))
        else (S, dm @ [0]))
       ([], []) [0..<length (SmtProblem_defs p)]\<close>

definition tr_asserts_m :: \<open>SmtProblem \<Rightarrow> Term list \<times> nat list \<Rightarrow> Term list \<times> Term list\<close> where
  \<open>tr_asserts_m p Sd \<equiv>
     foldl (\<lambda>(S, ts) t. let r = tr_term_m p (snd Sd) [] (length (SmtProblem_defs p)) S t in (fst r, ts @ [snd r]))
       (fst Sd, []) (SmtProblem_asserts p)\<close>

fun sort_width_m :: \<open>SmtSort \<Rightarrow> nat\<close> where
  \<open>sort_width_m SmtSort_Bool = 1\<close>
| \<open>sort_width_m (SmtSort_BitVec w) = unat w\<close>
| \<open>sort_width_m (SmtSort_Uninterpreted s) = 0\<close>

definition tr_problem_m :: \<open>SmtProblem \<Rightarrow> Problem\<close> where
  \<open>tr_problem_m p \<equiv>
     let ra = tr_asserts_m p (tr_defs_m p) in
     make_Problem (map (\<lambda>f. word_of_nat (sort_width_m (SmtFun_ret f))) (SmtProblem_funs p)) (fst ra) (snd ra)\<close>

text \<open>The model of \<open>p\<close> for the assignment \<open>m\<close> of the variables of the translation.\<close>
definition tr_model_m :: \<open>SmtProblem \<Rightarrow> bool list list \<Rightarrow> SmtModel\<close> where
  \<open>tr_model_m p m \<equiv>
     make_SmtModel []
       (map (\<lambda>i. make_SmtInterp []
                   (case SmtFun_ret (SmtProblem_funs p ! i) of SmtSort_Bool \<Rightarrow> SmtValue_Bool (m ! i ! 0)
                    | _ \<Rightarrow> SmtValue_Bv (m ! i)))
          [0..<length (SmtProblem_funs p)])\<close>

section \<open>Facts about the definitions of the extended language\<close>

lemma def_widths_append': \<open>def_widths ws ds (xs @ ys) = def_widths ws (def_widths ws ds xs) ys\<close>
  by (induction xs arbitrary: ds) simp_all

lemma def_values_append':
  \<open>def_values ws ds vs dv (xs @ ys) = def_values ws (def_widths ws ds xs) vs (def_values ws ds vs dv xs) ys\<close>
  by (induction xs arbitrary: ds dv) simp_all

lemma defs_wt_append': \<open>defs_wt ws ds (xs @ ys) = (defs_wt ws ds xs \<and> defs_wt ws (def_widths ws ds xs) ys)\<close>
  by (induction xs arbitrary: ds) simp_all

lemma def_widths_length': \<open>length (def_widths ws ds xs) = length ds + length xs\<close>
  by (induction xs arbitrary: ds) simp_all

lemma def_values_length': \<open>length (def_values ws ds vs dv xs) = length dv + length xs\<close>
  by (induction xs arbitrary: ds dv) simp_all

lemma def_widths_prefix': \<open>\<exists>e. def_widths ws ds xs = ds @ e\<close>
proof (induction xs arbitrary: ds)
  case Nil
  show ?case by simp
next
  case (Cons d dd)
  obtain e where \<open>def_widths ws (ds @ [width ws ds d]) dd = (ds @ [width ws ds d]) @ e\<close>
    using Cons.IH by blast
  then show ?case by simp
qed

lemma def_values_prefix': \<open>\<exists>e. def_values ws ds vs dv xs = dv @ e\<close>
proof (induction xs arbitrary: ds dv)
  case Nil
  show ?case by simp
next
  case (Cons d dd)
  obtain e where \<open>def_values ws (ds @ [width ws ds d]) vs (dv @ [eval ws ds vs dv d]) dd =
      (dv @ [eval ws ds vs dv d]) @ e\<close>
    using Cons.IH by blast
  then show ?case by simp
qed

text \<open>A well-sorted term keeps its width and value when definitions are added after the ones it
  refers to.\<close>
lemma wt_width_eval_append:
  \<open>wt ws ds t \<Longrightarrow> length dv = length ds \<Longrightarrow>
     wt ws (ds @ e) t \<and> width ws (ds @ e) t = width ws ds t \<and> eval ws (ds @ e) vs (dv @ ev) t = eval ws ds vs dv t\<close>
  by (induction t) (auto simp: nth_append split: Op.splits)

section \<open>Correctness of the translation\<close>

subsection \<open>Bounds of bit-vector operations\<close>

lemma smt_bits_nat_lt_s: \<open>smt_bits_nat bs < 2 ^ length bs\<close>
  by (induction bs) auto

lemma take_bit_eq_self_nat_s: \<open>x < 2 ^ w \<Longrightarrow> take_bit w (x :: nat) = x\<close>
  by (simp add: take_bit_nat_eq_self_iff)

lemma and_lt_pow_s: \<open>x < 2 ^ w \<Longrightarrow> y < 2 ^ w \<Longrightarrow> Bit_Operations.and (x :: nat) y < 2 ^ w\<close>
proof -
  assume \<open>x < 2 ^ w\<close> \<open>y < 2 ^ w\<close>
  then have \<open>Bit_Operations.and x y = take_bit w (Bit_Operations.and x y)\<close>
    by (simp add: take_bit_and take_bit_eq_self_nat_s)
  then show ?thesis using take_bit_nat_less_exp[of w \<open>Bit_Operations.and x y\<close>] by simp
qed

lemma or_lt_pow_s: \<open>x < 2 ^ w \<Longrightarrow> y < 2 ^ w \<Longrightarrow> Bit_Operations.or (x :: nat) y < 2 ^ w\<close>
proof -
  assume \<open>x < 2 ^ w\<close> \<open>y < 2 ^ w\<close>
  then have \<open>Bit_Operations.or x y = take_bit w (Bit_Operations.or x y)\<close>
    by (simp add: take_bit_or take_bit_eq_self_nat_s)
  then show ?thesis using take_bit_nat_less_exp[of w \<open>Bit_Operations.or x y\<close>] by simp
qed

lemma xor_lt_pow_s: \<open>x < 2 ^ w \<Longrightarrow> y < 2 ^ w \<Longrightarrow> Bit_Operations.xor (x :: nat) y < 2 ^ w\<close>
proof -
  assume \<open>x < 2 ^ w\<close> \<open>y < 2 ^ w\<close>
  then have \<open>Bit_Operations.xor x y = take_bit w (Bit_Operations.xor x y)\<close>
    by (simp add: take_bit_xor take_bit_eq_self_nat_s)
  then show ?thesis using take_bit_nat_less_exp[of w \<open>Bit_Operations.xor x y\<close>] by simp
qed

lemma concat_lt_pow_s: \<open>(x :: nat) < 2 ^ w \<Longrightarrow> y < 2 ^ v \<Longrightarrow> x * 2 ^ v + y < 2 ^ (w + v)\<close>
proof -
  assume \<open>x < 2 ^ w\<close> \<open>y < 2 ^ v\<close>
  have \<open>x + 1 \<le> 2 ^ w\<close> using \<open>x < 2 ^ w\<close> by linarith
  then have \<open>(x + 1) * 2 ^ v \<le> 2 ^ w * 2 ^ v\<close> by (rule mult_le_mono1)
  then have \<open>x * 2 ^ v + 2 ^ v \<le> 2 ^ (w + v)\<close> by (simp add: power_add)
  then show ?thesis using \<open>y < 2 ^ v\<close> by linarith
qed

lemma smt_to_bv_lt: \<open>smt_to_bv w z < 2 ^ w\<close>
  by (simp add: smt_to_bv_def nat_less_iff)

lemma smt_repeat_val_lt: \<open>x < 2 ^ w \<Longrightarrow> smt_repeat_val w j x < 2 ^ (w * j)\<close>
proof (induction j)
  case 0
  then show ?case by simp
next
  case (Suc j)
  have \<open>smt_repeat_val w (Suc j) x = x * 2 ^ (w * j) + smt_repeat_val w j x\<close> by simp
  also have \<open>\<dots> < 2 ^ (w + w * j)\<close> using concat_lt_pow_s[OF Suc.prems Suc.IH[OF Suc.prems]] .
  finally show ?case by (simp add: algebra_simps)
qed

subsection \<open>Sorts of values\<close>

text \<open>The number of the extended language for a value of the fragment: a truth value is 0 or 1.\<close>
fun enc :: \<open>sval \<Rightarrow> nat\<close> where
  \<open>enc (VBool b) = of_bool b\<close>
| \<open>enc (VBv w x) = x\<close>
| \<open>enc (VElem e) = 0\<close>

lemma unat_add_s: \<open>unat a + unat b < 2 ^ 64 \<Longrightarrow> unat (a + b) = unat a + unat (b :: 64 word)\<close>
  using unat_add_lem[of a b] by simp

lemma unat_mult_s: \<open>unat a * unat b < 2 ^ 64 \<Longrightarrow> unat (a * b) = unat a * unat (b :: 64 word)\<close>
  using unat_mult_lem[of a b] by simp

lemma unat_extract_s:
  fixes i j m :: \<open>64 word\<close>
  assumes \<open>unat j \<le> unat i\<close> \<open>unat i < unat m\<close>
  shows \<open>unat (i - j + 1) = unat i - unat j + 1\<close>
proof -
  have s: \<open>unat (i - j) = unat i - unat j\<close> using assms(1) by (simp add: unat_sub word_le_nat_alt)
  have \<open>unat (i - j) + unat (1 :: 64 word) < 2 ^ 64\<close> using s assms unat_lt2p[of m] by simp
  then show ?thesis using s unat_add_s by simp
qed

lemma pow2_gt1_s: \<open>1 \<le> w \<Longrightarrow> Suc 0 < (2 :: nat) ^ w\<close>
  using power_increasing[of 1 w \<open>2::nat\<close>] by simp

lemma smt_bv_bin_lt: \<open>1 \<le> w \<Longrightarrow> x < 2 ^ w \<Longrightarrow> y < 2 ^ w \<Longrightarrow> smt_bv_bin op w x y < 2 ^ w\<close>
  by (cases op) (auto simp: and_lt_pow_s or_lt_pow_s xor_lt_pow_s smt_to_bv_lt le_less_trans[OF div_le_dividend]
      le_less_trans[OF mod_less_eq_dividend] pow2_gt1_s)

lemma foldl_bv_lt:
  assumes \<open>\<forall>x \<in> set (y # ys). \<exists>v. x = VBv w v \<and> v < 2 ^ w\<close> \<open>\<And>a b. a < 2 ^ w \<Longrightarrow> b < 2 ^ w \<Longrightarrow> g a b < 2 ^ w\<close>
  shows \<open>\<exists>v. foldl (\<lambda>a b. VBv w (g (smt_bv_val a) (smt_bv_val b))) y ys = VBv w v \<and> v < 2 ^ w\<close>
  using assms(1)
proof (induction ys arbitrary: y)
  case Nil
  then show ?case by simp
next
  case (Cons z zs)
  obtain a where a: \<open>y = VBv w a\<close> \<open>a < 2 ^ w\<close> using Cons.prems by auto
  obtain b where b: \<open>z = VBv w b\<close> \<open>b < 2 ^ w\<close> using Cons.prems by auto
  have \<open>\<forall>x \<in> set (VBv w (g a b) # zs). \<exists>v. x = VBv w v \<and> v < 2 ^ w\<close>
    using Cons.prems assms(2)[OF a(2) b(2)] by auto
  then show ?case using Cons.IH a b by simp
qed

lemma foldl_VBv:
  \<open>foldl (\<lambda>a b. VBv w (g (smt_bv_val a) (smt_bv_val b))) (VBv w x) ys = VBv w (foldl (\<lambda>a b. g a (smt_bv_val b)) x ys)\<close>
  by (induction ys arbitrary: x) auto

lemma foldl_lt:
  \<open>x < 2 ^ w \<Longrightarrow> \<forall>b \<in> set ys. smt_bv_val b < 2 ^ w \<Longrightarrow> (\<And>a c. a < 2 ^ w \<Longrightarrow> c < 2 ^ w \<Longrightarrow> g a c < (2 :: nat) ^ w) \<Longrightarrow>
     foldl (\<lambda>a b. g a (smt_bv_val b)) x ys < 2 ^ w\<close>
  by (induction ys arbitrary: x) auto

lemma la2_bv:
  \<open>list_all2 smt_has_sort ss zs \<Longrightarrow> \<forall>s \<in> set ss. s = SmtSort_BitVec w \<Longrightarrow> \<forall>z \<in> set zs. smt_bv_val z < 2 ^ unat w\<close>
  by (induction ss zs rule: list_all2_induct) (auto split: sval.splits)

lemma smt_bin_width_Some:
  \<open>smt_bin_width ss = Some y \<Longrightarrow> \<exists>a. ss = [SmtSort_BitVec a, SmtSort_BitVec a] \<and> y = unat a\<close>
  by (cases ss rule: smt_bin_width.cases) (auto split: if_splits)

lemma smt_same_width_Some:
  \<open>smt_same_width ss = Some y \<Longrightarrow> \<exists>a. ss \<noteq> [] \<and> (\<forall>s \<in> set ss. s = SmtSort_BitVec a) \<and> y = unat a\<close>
  by (auto simp: smt_same_width_def split: list.splits SmtSort.splits if_splits)

lemma fold_sort:
  assumes \<open>list_all2 smt_has_sort ss xs\<close> \<open>ss \<noteq> []\<close> \<open>\<forall>s \<in> set ss. s = SmtSort_BitVec m\<close> \<open>1 \<le> unat m\<close>
  shows \<open>smt_has_sort (SmtSort_BitVec m)
     (VBv (smt_bv_width (hd xs)) (foldl (\<lambda>x v. smt_bv_bin op (smt_bv_width (hd xs)) x (smt_bv_val v)) (smt_bv_val (hd xs)) (tl xs)))\<close>
proof -
  obtain s0 ss' x0 xs' where e: \<open>ss = s0 # ss'\<close> \<open>xs = x0 # xs'\<close>
    using assms(1,2) by (cases ss; cases xs) auto
  have s0: \<open>s0 = SmtSort_BitVec m\<close> using assms(3) e by simp
  obtain v0 where v0: \<open>x0 = VBv (unat m) v0\<close> \<open>v0 < 2 ^ unat m\<close>
    using assms(1) e s0 by (auto split: sval.splits)
  have \<open>\<forall>z \<in> set xs'. smt_bv_val z < 2 ^ unat m\<close>
    using la2_bv[of ss' xs' m] assms(1,3) e by auto
  then have \<open>foldl (\<lambda>x v. smt_bv_bin op (unat m) x (smt_bv_val v)) v0 xs' < 2 ^ unat m\<close>
    using v0(2) by (intro foldl_lt) (auto intro: smt_bv_bin_lt[OF assms(4)])
  then show ?thesis using e v0 by simp
qed

text \<open>The bit-vector functions whose value is a fold of \<^const>\<open>smt_bv_bin\<close>.\<close>
fun fold_op :: \<open>SmtOp \<Rightarrow> bool\<close> where
  \<open>fold_op SmtOp_Bvand = True\<close>
| \<open>fold_op SmtOp_Bvor = True\<close>
| \<open>fold_op SmtOp_Bvadd = True\<close>
| \<open>fold_op SmtOp_Bvmul = True\<close>
| \<open>fold_op SmtOp_Bvudiv = True\<close>
| \<open>fold_op SmtOp_Bvurem = True\<close>
| \<open>fold_op SmtOp_Bvshl = True\<close>
| \<open>fold_op SmtOp_Bvlshr = True\<close>
| \<open>fold_op SmtOp_Bvnand = True\<close>
| \<open>fold_op SmtOp_Bvnor = True\<close>
| \<open>fold_op SmtOp_Bvxor = True\<close>
| \<open>fold_op SmtOp_Bvxnor = True\<close>
| \<open>fold_op SmtOp_Bvsub = True\<close>
| \<open>fold_op SmtOp_Bvsdiv = True\<close>
| \<open>fold_op SmtOp_Bvsrem = True\<close>
| \<open>fold_op SmtOp_Bvsmod = True\<close>
| \<open>fold_op SmtOp_Bvashr = True\<close>
| \<open>fold_op _ = False\<close>

lemma fold_op_sem:
  \<open>fold_op op \<Longrightarrow> smt_op_sem op xs =
     VBv (smt_bv_width (hd xs)) (foldl (\<lambda>x v. smt_bv_bin op (smt_bv_width (hd xs)) x (smt_bv_val v)) (smt_bv_val (hd xs)) (tl xs))\<close>
  by (cases op) (simp_all add: Let_def del: smt_bv_bin.simps)

lemma fold_op_sort:
  \<open>fold_op op \<Longrightarrow> smt_op_sort op ss = Some s \<Longrightarrow> \<exists>a. ss \<noteq> [] \<and> (\<forall>x \<in> set ss. x = SmtSort_BitVec a) \<and> s = SmtSort_BitVec a\<close>
  by (cases op) (auto dest!: smt_bin_width_Some smt_same_width_Some split: if_splits)

lemma lt_pow_add_s: \<open>(x :: nat) < 2 ^ w \<Longrightarrow> x < 2 ^ (w + i)\<close>
  using less_le_trans[OF _ power_increasing[of w \<open>w + i\<close> \<open>2::nat\<close>]] by simp

lemma div_pow_lt_s: \<open>(x :: nat) < 2 ^ w \<Longrightarrow> r \<le> w \<Longrightarrow> x div 2 ^ (w - r) < 2 ^ r\<close>
proof -
  assume \<open>x < 2 ^ w\<close> \<open>r \<le> w\<close>
  then have \<open>x < 2 ^ r * 2 ^ (w - r)\<close> by (simp add: power_add[symmetric])
  then show ?thesis by (simp add: less_mult_imp_div_less)
qed

lemma rotl_lt_s:
  \<open>(x :: nat) < 2 ^ w \<Longrightarrow> r \<le> w \<Longrightarrow> (x mod 2 ^ (w - r)) * 2 ^ r + x div 2 ^ (w - r) < 2 ^ w\<close>
  using concat_lt_pow_s[of \<open>x mod 2 ^ (w - r)\<close> \<open>w - r\<close> \<open>x div 2 ^ (w - r)\<close> r] div_pow_lt_s[of x w r] by simp

lemma rotr_lt_s:
  \<open>(x :: nat) < 2 ^ w \<Longrightarrow> r \<le> w \<Longrightarrow> (x mod 2 ^ r) * 2 ^ (w - r) + x div 2 ^ r < 2 ^ w\<close>
  using concat_lt_pow_s[of \<open>x mod 2 ^ r\<close> r \<open>x div 2 ^ r\<close> \<open>w - r\<close>] div_pow_lt_s[of x w \<open>w - r\<close>] by simp

text \<open>The value of a theory function has the result sort.\<close>
lemma smt_op_sem_sort:
  assumes \<open>smt_op_sort op ss = Some s\<close> \<open>list_all2 smt_has_sort ss xs\<close> \<open>\<forall>x \<in> set ss. smt_wf_sort ns x\<close>
  shows \<open>smt_has_sort s (smt_op_sem op xs)\<close>
proof (cases \<open>fold_op op\<close>)
  case True
  obtain a where a: \<open>ss \<noteq> []\<close> \<open>\<forall>x \<in> set ss. x = SmtSort_BitVec a\<close> \<open>s = SmtSort_BitVec a\<close>
    using fold_op_sort[OF True assms(1)] by blast
  have \<open>1 \<le> unat a\<close> using a(1,2) assms(3) by (cases ss) auto
  then show ?thesis using fold_sort[OF assms(2) a(1,2), of op] fold_op_sem[OF True, of xs] a(3)
    by (auto simp del: smt_bv_bin.simps)
next
  case False
  then show ?thesis
    using assms
    by (cases op) (auto simp: list_all2_Cons1 list_all2_Cons2 Let_def smt_to_bv_lt
      concat_lt_pow_s smt_repeat_val_lt unat_add_s unat_mult_s unat_extract_s lt_pow_add_s rotl_lt_s rotr_lt_s
      dest!: smt_bin_width_Some split: if_splits list.splits SmtSort.splits sval.splits option.splits)
qed

lemma smt_op_sort_wf:
  assumes \<open>smt_op_sort op ss = Some s\<close> \<open>\<forall>x \<in> set ss. smt_wf_sort ns x\<close>
  shows \<open>smt_wf_sort ns s\<close>
proof (cases \<open>fold_op op\<close>)
  case True
  then show ?thesis using fold_op_sort[OF True assms(1)] assms(2) by (cases ss) auto
next
  case False
  then show ?thesis using assms
    by (cases op) (auto simp: unat_add_s unat_mult_s unat_extract_s dest!: smt_bin_width_Some
        split: if_splits list.splits SmtSort.splits)
qed

lemma smt_tsort_wf:
  assumes \<open>smt_tsort fs ds ps t = Some s\<close> \<open>\<forall>x \<in> set ps. smt_wf_sort ns x\<close>
    \<open>\<forall>f \<in> set fs. smt_wf_sort ns (SmtFun_ret f)\<close> \<open>\<forall>d \<in> set ds. smt_wf_sort ns (SmtDef_ret d)\<close>
  shows \<open>smt_wf_sort ns s\<close>
  using assms(1)
proof (induction t arbitrary: s)
  case (SmtTerm_App op args)
  then have \<open>None \<notin> set (map (smt_tsort fs ds ps) args)\<close>
    and o: \<open>smt_op_sort op (map (the \<circ> smt_tsort fs ds ps) args) = Some s\<close>
    by (auto split: if_splits)
  then have \<open>\<forall>x \<in> set (map (the \<circ> smt_tsort fs ds ps) args). smt_wf_sort ns x\<close>
    using SmtTerm_App.IH by (force simp: image_iff)
  then show ?case using smt_op_sort_wf[OF o] by blast
qed (use assms in \<open>auto simp: unat_of_nat_eq Suc_le_eq split: if_splits\<close>)

text \<open>The meanings of definitions respect their sorts.\<close>
definition defs_sound :: \<open>SmtFun list \<Rightarrow> SmtDef list \<Rightarrow> (sval list \<Rightarrow> sval) list \<Rightarrow> bool\<close> where
  \<open>defs_sound fs ds dv \<equiv> length dv = length ds \<and>
     (\<forall>d < length ds. \<forall>xs. list_all2 smt_has_sort (SmtDef_params (ds ! d)) xs \<longrightarrow> smt_has_sort (SmtDef_ret (ds ! d)) ((dv ! d) xs))\<close>

definition interp_sound :: \<open>SmtFun list \<Rightarrow> (nat \<Rightarrow> sval list \<Rightarrow> sval) \<Rightarrow> bool\<close> where
  \<open>interp_sound fs I \<equiv>
     \<forall>f < length fs. \<forall>xs. list_all2 smt_has_sort (SmtFun_args (fs ! f)) xs \<longrightarrow> smt_has_sort (SmtFun_ret (fs ! f)) (I f xs)\<close>

lemma map_Some_la2:
  \<open>map g args = map Some ss \<Longrightarrow> (\<And>a s. a \<in> set args \<Longrightarrow> g a = Some s \<Longrightarrow> P s (h a)) \<Longrightarrow> list_all2 P ss (map h args)\<close>
  by (induction args arbitrary: ss) auto

lemma smt_eval_sort:
  assumes \<open>smt_tsort fs ds ps t = Some s\<close> \<open>interp_sound fs I\<close> \<open>defs_sound fs ds dv\<close>
    \<open>list_all2 smt_has_sort ps xs\<close> \<open>\<forall>x \<in> set ps. smt_wf_sort ns x\<close>
    \<open>\<forall>f \<in> set fs. \<forall>x \<in> set (SmtFun_args f). smt_wf_sort ns x\<close>
    \<open>\<forall>f \<in> set fs. smt_wf_sort ns (SmtFun_ret f)\<close>
    \<open>\<forall>d \<in> set ds. smt_wf_sort ns (SmtDef_ret d) \<and> (\<forall>x \<in> set (SmtDef_params d). smt_wf_sort ns x)\<close>
  shows \<open>smt_has_sort s (smt_eval I dv xs t)\<close>
  using assms(1)
proof (induction t arbitrary: s)
  case (SmtTerm_BvConst bs)
  then show ?case by (auto simp: unat_of_nat_eq smt_bits_nat_lt_s split: if_splits)
next
  case (SmtTerm_Param k)
  then show ?case using assms(4) by (auto simp: list_all2_conv_all_nth split: if_splits)
next
  case (SmtTerm_Fun f args)
  then have f: \<open>unat f < length fs\<close> and m: \<open>map (smt_tsort fs ds ps) args = map Some (SmtFun_args (fs ! unat f))\<close>
    and e: \<open>s = SmtFun_ret (fs ! unat f)\<close> by (auto split: if_splits)
  have \<open>list_all2 smt_has_sort (SmtFun_args (fs ! unat f)) (map (smt_eval I dv xs) args)\<close>
    using map_Some_la2[OF m] SmtTerm_Fun.IH by blast
  then show ?case using assms(2) f e by (simp add: interp_sound_def)
next
  case (SmtTerm_Def d args)
  then have d: \<open>unat d < length ds\<close> and m: \<open>map (smt_tsort fs ds ps) args = map Some (SmtDef_params (ds ! unat d))\<close>
    and e: \<open>s = SmtDef_ret (ds ! unat d)\<close> by (auto split: if_splits)
  have \<open>list_all2 smt_has_sort (SmtDef_params (ds ! unat d)) (map (smt_eval I dv xs) args)\<close>
    using map_Some_la2[OF m] SmtTerm_Def.IH by blast
  then show ?case using assms(3) d e by (simp add: defs_sound_def)
next
  case (SmtTerm_App op args)
  then have n: \<open>None \<notin> set (map (smt_tsort fs ds ps) args)\<close>
    and o: \<open>smt_op_sort op (map (the \<circ> smt_tsort fs ds ps) args) = Some s\<close>
    by (auto split: if_splits)
  have m: \<open>map (smt_tsort fs ds ps) args = map Some (map (the \<circ> smt_tsort fs ds ps) args)\<close>
    using n by (induction args) auto
  have \<open>list_all2 smt_has_sort (map (the \<circ> smt_tsort fs ds ps) args) (map (smt_eval I dv xs) args)\<close>
    using map_Some_la2[OF m] SmtTerm_App.IH by blast
  moreover have \<open>\<forall>x \<in> set (map (the \<circ> smt_tsort fs ds ps) args). smt_wf_sort ns x\<close>
    using m smt_tsort_wf[of fs ds ps _ _ ns] assms(5,7,8) by (force simp: image_iff)
  ultimately show ?case using smt_op_sem_sort[OF o] by simp
qed auto

subsection \<open>The translation of a theory function\<close>

text \<open>Definition \<open>k\<close> of the state \<open>S\<close> stands for the value \<open>v\<close> of sort \<open>s\<close>: its index fits in a
  word (the translation writes it as one), its width is that of \<open>s\<close> and its value the number of
  \<open>v\<close>.\<close>
definition ref_ok :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> Term list \<Rightarrow> nat \<Rightarrow> SmtSort \<Rightarrow> sval \<Rightarrow> bool\<close> where
  \<open>ref_ok ws vs S k s v \<equiv>
     k < length S \<and> k < 2 ^ 64 \<and> def_widths ws [] S ! k = sort_width_m s \<and>
     def_values ws [] vs [] S ! k = enc v \<and> smt_has_sort s v\<close>

text \<open>A sort of the fragment: Bool or a bit-vector sort of width at least 1.\<close>
fun frag_sort :: \<open>SmtSort \<Rightarrow> bool\<close> where
  \<open>frag_sort SmtSort_Bool = True\<close>
| \<open>frag_sort (SmtSort_BitVec w) = (1 \<le> unat w)\<close>
| \<open>frag_sort (SmtSort_Uninterpreted s) = False\<close>

lemma sort_width_frag: \<open>frag_sort s \<Longrightarrow> 1 \<le> sort_width_m s\<close>
  by (cases s) auto

lemma tref_ok:
  assumes \<open>ref_ok ws vs S k s v\<close> \<open>frag_sort s\<close>
  shows \<open>wt ws (def_widths ws [] S) (tref k) \<and> width ws (def_widths ws [] S) (tref k) = sort_width_m s \<and>
         eval ws (def_widths ws [] S) vs (def_values ws [] vs [] S) (tref k) = enc v\<close>
  using assms sort_width_frag[OF assms(2)]
  by (auto simp: ref_ok_def tref_def unat_of_nat_eq def_widths_length')

lemma helper_defs_eq:
  \<open>sint = smt_sint\<close> \<open>to_bv = smt_to_bv\<close> \<open>tdiv = smt_tdiv\<close> \<open>tmod = smt_tmod\<close> \<open>repeat_val = smt_repeat_val\<close>
  \<open>bits_nat = smt_bits_nat\<close>
proof -
  show \<open>sint = smt_sint\<close> by (simp add: fun_eq_iff sint_def smt_sint_def)
  show \<open>to_bv = smt_to_bv\<close> by (simp add: fun_eq_iff to_bv_def smt_to_bv_def)
  show \<open>tdiv = smt_tdiv\<close> by (simp add: fun_eq_iff tdiv_def smt_tdiv_def)
  show \<open>tmod = smt_tmod\<close> by (simp add: fun_eq_iff tmod_def smt_tmod_def tdiv_def smt_tdiv_def)
  have \<open>repeat_val w j x = smt_repeat_val w j x\<close> for w j x by (induction j) auto
  then show \<open>repeat_val = smt_repeat_val\<close> by (simp add: fun_eq_iff)
  have \<open>bits_nat bs = smt_bits_nat bs\<close> for bs by (induction bs) auto
  then show \<open>bits_nat = smt_bits_nat\<close> by (simp add: fun_eq_iff)
qed

text \<open>The binary functions of the extended language compute those of the general semantics.\<close>
lemma bin_sem_fold: \<open>fold_op op \<Longrightarrow> bin_sem (tr_op op) w x w y = smt_bv_bin op w x y\<close>
  by (cases op) (simp_all add: helper_defs_eq)

lemma bin_sem_cmp:
  \<open>op \<in> {SmtOp_Bvult, SmtOp_Bvule, SmtOp_Bvugt, SmtOp_Bvuge, SmtOp_Bvslt, SmtOp_Bvsle, SmtOp_Bvsgt, SmtOp_Bvsge} \<Longrightarrow>
     bin_sem (tr_op op) w x w y = of_bool (smt_bv_cmp op w x y)\<close>
  by (auto simp: helper_defs_eq)

text \<open>A chain of binary operations that keep the width of their operands.\<close>
lemma fold_left_eval:
  assumes \<open>bop \<in> {Op_And, Op_Or, Op_Xor, Op_Add, Op_Mul}\<close>
    \<open>\<forall>k \<in> set ks. wt ws dw (tref k) \<and> width ws dw (tref k) = w\<close> \<open>wt ws dw acc\<close> \<open>width ws dw acc = w\<close>
  shows \<open>wt ws dw (foldl (\<lambda>acc k. Term_Bin bop acc (tref k)) acc ks) \<and>
         width ws dw (foldl (\<lambda>acc k. Term_Bin bop acc (tref k)) acc ks) = w \<and>
         eval ws dw vs dv (foldl (\<lambda>acc k. Term_Bin bop acc (tref k)) acc ks) =
           foldl (\<lambda>a k. bin_sem bop w a w (eval ws dw vs dv (tref k))) (eval ws dw vs dv acc) ks\<close>
  using assms(2-4)
proof (induction ks arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons k ks)
  have \<open>wt ws dw (Term_Bin bop acc (tref k)) \<and> width ws dw (Term_Bin bop acc (tref k)) = w\<close>
    using Cons.prems assms(1) by auto
  then show ?case using Cons.IH[of \<open>Term_Bin bop acc (tref k)\<close>] Cons.prems assms(1) by auto
qed

lemma and_bool_s: \<open>Bit_Operations.and (of_bool a) (of_bool b) = (of_bool (a \<and> b) :: nat)\<close>
  by (cases a; cases b) auto

lemma or_bool_s: \<open>Bit_Operations.or (of_bool a) (of_bool b) = (of_bool (a \<or> b) :: nat)\<close>
  by (cases a; cases b) auto

lemma xor_bool_s: \<open>Bit_Operations.xor (of_bool a) (of_bool b) = (of_bool (a \<noteq> b) :: nat)\<close>
  by (cases a; cases b) auto

lemma fold_and_bool: \<open>foldl (\<lambda>a b. Bit_Operations.and a (of_bool b)) (of_bool x) ys = (of_bool (x \<and> (\<forall>y \<in> set ys. y)) :: nat)\<close>
  by (induction ys arbitrary: x) (auto simp: and_bool_s)

lemma fold_or_bool: \<open>foldl (\<lambda>a b. Bit_Operations.or a (of_bool b)) (of_bool x) ys = (of_bool (x \<or> (\<exists>y \<in> set ys. y)) :: nat)\<close>
proof (induction ys arbitrary: x)
  case (Cons y ys)
  have \<open>Bit_Operations.or (of_bool x) (of_bool y) = (of_bool (x \<or> y) :: nat)\<close> by (rule or_bool_s)
  then show ?case using Cons.IH[of \<open>x \<or> y\<close>] by simp
qed simp

lemma fold_xor_bool: \<open>foldl (\<lambda>a b. Bit_Operations.xor a (of_bool b)) (of_bool x) ys = (of_bool (odd (length (filter id (x # ys)))) :: nat)\<close>
  by (induction ys arbitrary: x) (auto simp: xor_bool_s)

lemma enc_inj: \<open>smt_has_sort s a \<Longrightarrow> smt_has_sort s b \<Longrightarrow> frag_sort s \<Longrightarrow> (enc a = enc b) = (a = b)\<close>
  by (cases s) (auto split: sval.splits)

lemma pairs_m_set: \<open>2 \<le> n \<Longrightarrow> insert (0, 1) (set (pairs_m n)) = {(i, j). i < j \<and> j < n}\<close>
  by (auto simp: pairs_m_def image_iff)

text \<open>The \<open>=\<close>, \<open>distinct\<close> and \<open>and\<close> of the extended language on truth values (width 1) and on
  references of one width.\<close>
lemma eq_ref_eval:
  \<open>wt ws dw (tref a) \<Longrightarrow> wt ws dw (tref b) \<Longrightarrow> width ws dw (tref a) = width ws dw (tref b) \<Longrightarrow>
     wt ws dw (Term_Bin op (tref a) (tref b)) \<and>
     (op \<in> {Op_Eq, Op_Distinct} \<longrightarrow> width ws dw (Term_Bin op (tref a) (tref b)) = 1)\<close>
  by auto

lemma chain_idx:
  assumes \<open>2 \<le> n\<close>
  shows \<open>(e 0 = e 1 \<and> (\<forall>i \<in> set [2..<n]. e (i - 1) = e i)) = (\<forall>i. Suc i < n \<longrightarrow> e i = e (Suc i))\<close>
proof
  assume a: \<open>e 0 = e 1 \<and> (\<forall>i \<in> set [2..<n]. e (i - 1) = e i)\<close>
  show \<open>\<forall>i. Suc i < n \<longrightarrow> e i = e (Suc i)\<close>
  proof (intro allI impI)
    fix i assume i: \<open>Suc i < n\<close>
    show \<open>e i = e (Suc i)\<close>
    proof (cases i)
      case 0
      then show ?thesis using a by simp
    next
      case (Suc j)
      have \<open>Suc i \<in> set [2..<n]\<close> using i Suc by auto
      then show ?thesis using a by fastforce
    qed
  qed
next
  assume a: \<open>\<forall>i. Suc i < n \<longrightarrow> e i = e (Suc i)\<close>
  have \<open>e 0 = e 1\<close> using a assms by auto
  moreover have \<open>\<forall>i \<in> set [2..<n]. e (i - 1) = e i\<close>
  proof
    fix i assume \<open>i \<in> set [2..<n]\<close>
    then have \<open>Suc (i - 1) < n\<close> \<open>Suc (i - 1) = i\<close> by auto
    then show \<open>e (i - 1) = e i\<close> using a by metis
  qed
  ultimately show \<open>e 0 = e 1 \<and> (\<forall>i \<in> set [2..<n]. e (i - 1) = e i)\<close> by blast
qed

lemma chain_eval:
  assumes \<open>2 \<le> length ks\<close> \<open>\<forall>k \<in> set ks. wt ws dw (tref k) \<and> width ws dw (tref k) = w\<close>
  shows \<open>wt ws dw (chain_m SmtOp_Eq ks) \<and> width ws dw (chain_m SmtOp_Eq ks) = 1 \<and>
     eval ws dw vs dv (chain_m SmtOp_Eq ks) =
       of_bool (\<forall>i. Suc i < length ks \<longrightarrow> eval ws dw vs dv (tref (ks ! i)) = eval ws dw vs dv (tref (ks ! Suc i)))\<close>
proof -
  let ?e = \<open>\<lambda>i. eval ws dw vs dv (tref (ks ! i))\<close>
  let ?f = \<open>\<lambda>acc i. Term_Bin Op_And acc (Term_Bin Op_Eq (tref (ks ! (i - 1))) (tref (ks ! i)))\<close>
  have g: \<open>\<forall>i \<in> set ix. 1 \<le> i \<and> i < length ks \<Longrightarrow> wt ws dw acc \<Longrightarrow> width ws dw acc = 1 \<Longrightarrow> eval ws dw vs dv acc = of_bool A \<Longrightarrow>
      wt ws dw (foldl ?f acc ix) \<and> width ws dw (foldl ?f acc ix) = 1 \<and>
      eval ws dw vs dv (foldl ?f acc ix) = of_bool (A \<and> (\<forall>i \<in> set ix. ?e (i - 1) = ?e i))\<close> for ix acc A
  proof (induction ix arbitrary: acc A)
    case Nil
    then show ?case by simp
  next
    case (Cons i ix)
    have i: \<open>i - 1 < length ks\<close> \<open>i < length ks\<close> using Cons.prems by auto
    then have r: \<open>wt ws dw (tref (ks ! (i - 1))) \<and> width ws dw (tref (ks ! (i - 1))) = w\<close>
      \<open>wt ws dw (tref (ks ! i)) \<and> width ws dw (tref (ks ! i)) = w\<close> using assms(2) by auto
    have \<open>eval ws dw vs dv (?f acc i) = of_bool (A \<and> ?e (i - 1) = ?e i)\<close>
      using Cons.prems by (simp add: and_bool_s)
    moreover have \<open>wt ws dw (?f acc i) \<and> width ws dw (?f acc i) = 1\<close> using Cons.prems r by simp
    ultimately show ?case using Cons.IH[of \<open>?f acc i\<close> \<open>A \<and> ?e (i - 1) = ?e i\<close>] Cons.prems by auto
  qed
  have l: \<open>0 < length ks\<close> \<open>1 < length ks\<close> using assms(1) by linarith+
  have m: \<open>ks ! 0 \<in> set ks\<close> \<open>ks ! 1 \<in> set ks\<close> using nth_mem[OF l(1)] nth_mem[OF l(2)] .
  have k01: \<open>wt ws dw (tref (ks ! 0)) \<and> width ws dw (tref (ks ! 0)) = w\<close>
    \<open>wt ws dw (tref (ks ! 1)) \<and> width ws dw (tref (ks ! 1)) = w\<close>
    using assms(2) m by blast+
  have \<open>(?e 0 = ?e 1 \<and> (\<forall>i \<in> set [2..<length ks]. ?e (i - 1) = ?e i)) = (\<forall>i. Suc i < length ks \<longrightarrow> ?e i = ?e (Suc i))\<close>
    using chain_idx[OF assms(1)] .
  then show ?thesis using g[of \<open>[2..<length ks]\<close> \<open>Term_Bin Op_Eq (tref (ks ! 0)) (tref (ks ! 1))\<close> \<open>?e 0 = ?e 1\<close>] k01
    by (simp add: chain_m_def)
qed

lemma tr_app_correct:
  assumes \<open>smt_op_sort op ss = Some s\<close> \<open>\<forall>x \<in> set ss. frag_sort x\<close>
    \<open>length ks = length ss\<close> \<open>length xs = length ss\<close>
    \<open>\<forall>i < length ss. ref_ok ws vs S (ks ! i) (ss ! i) (xs ! i)\<close>
  shows \<open>wt ws (def_widths ws [] S) (tr_app_m op ks) \<and>
         width ws (def_widths ws [] S) (tr_app_m op ks) = sort_width_m s \<and>
         eval ws (def_widths ws [] S) vs (def_values ws [] vs [] S) (tr_app_m op ks) = enc (smt_op_sem op xs)\<close>
  sorry

subsection \<open>The translation of terms\<close>

text \<open>The context of the translation of the definitions below \<open>n\<close> and of the assertions:
  \<open>vs\<close> are the values of the variables (the declared constants) under \<open>I\<close>, and the definitions
  without parameters below \<open>n\<close> are translated in \<open>S\<close>.\<close>
definition ctx_ok :: \<open>SmtProblem \<Rightarrow> (nat \<Rightarrow> sval list \<Rightarrow> sval) \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> Term list \<Rightarrow> bool\<close> where
  \<open>ctx_ok p I ws vs n dm S \<equiv>
     let fs = SmtProblem_funs p; ds = SmtProblem_defs p; dv = smt_def_sems I ds in
     smt_wf p \<and> smt_fragment p \<and> n \<le> length ds \<and>
     ws = map (\<lambda>f. sort_width_m (SmtFun_ret f)) fs \<and>
     length vs = length fs \<and> (\<forall>f < length fs. vs ! f = enc (I f [])) \<and> interp_sound fs I \<and>
     length dm \<ge> n \<and>
     (\<forall>d < n. SmtDef_params (ds ! d) = [] \<longrightarrow> ref_ok ws vs S (dm ! d) (SmtDef_ret (ds ! d)) ((dv ! d) []))\<close>

lemma tr_term_args_correct:
  shows \<open>tr_term_m p dm env n S t = (S', t') \<Longrightarrow> ctx_ok p I ws vs n dm S \<Longrightarrow>
     smt_tsort (SmtProblem_funs p) (take n (SmtProblem_defs p)) ps t = Some s \<Longrightarrow>
     \<forall>x \<in> set ps. frag_sort x \<Longrightarrow> length env = length ps \<Longrightarrow> length xs = length ps \<Longrightarrow>
     (\<forall>i < length ps. ref_ok ws vs S (env ! i) (ps ! i) (xs ! i)) \<Longrightarrow>
     defs_wt ws [] S \<Longrightarrow> length S' < 2 ^ 64 \<Longrightarrow>
     (\<exists>E. S' = S @ E) \<and> defs_wt ws [] S' \<and> wt ws (def_widths ws [] S') t' \<and>
     width ws (def_widths ws [] S') t' = sort_width_m s \<and>
     eval ws (def_widths ws [] S') vs (def_values ws [] vs [] S') t' =
       enc (smt_eval I (smt_def_sems I (SmtProblem_defs p)) xs t)\<close>
    and \<open>tr_args_m p dm env n S ts = (S', ks) \<Longrightarrow> ctx_ok p I ws vs n dm S \<Longrightarrow>
     map (smt_tsort (SmtProblem_funs p) (take n (SmtProblem_defs p)) ps) ts = map Some ss \<Longrightarrow>
     \<forall>x \<in> set ps. frag_sort x \<Longrightarrow> length env = length ps \<Longrightarrow> length xs = length ps \<Longrightarrow>
     (\<forall>i < length ps. ref_ok ws vs S (env ! i) (ps ! i) (xs ! i)) \<Longrightarrow>
     defs_wt ws [] S \<Longrightarrow> length S' < 2 ^ 64 \<Longrightarrow>
     (\<exists>E. S' = S @ E) \<and> defs_wt ws [] S' \<and> length ks = length ts \<and>
     (\<forall>i < length ts. ref_ok ws vs S' (ks ! i) (ss ! i)
        (smt_eval I (smt_def_sems I (SmtProblem_defs p)) xs (ts ! i)))\<close>
  sorry

end
