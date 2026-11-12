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
| \<open>tr_app_m SmtOp_Bvxor ks = fold_left_m SmtOp_Bvxor ks\<close>
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
text \<open>The binary operators of the extended language whose result has the width of the operands.\<close>
definition width_pres :: \<open>Op \<Rightarrow> bool\<close> where
  \<open>width_pres bop \<equiv> bop \<notin> {Op_Concat, Op_Comp, Op_Eq, Op_Distinct, Op_Ult, Op_Ule, Op_Ugt, Op_Uge,
     Op_Slt, Op_Sle, Op_Sgt, Op_Sge}\<close>

lemma fold_left_eval:
  assumes \<open>width_pres bop\<close>
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
    using Cons.prems assms(1) by (cases bop) (auto simp: width_pres_def)
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

lemma pairwise_eval:
  assumes \<open>2 \<le> length ks\<close> \<open>\<forall>k \<in> set ks. wt ws dw (tref k) \<and> width ws dw (tref k) = w\<close>
  shows \<open>wt ws dw (pairwise_m ks) \<and> width ws dw (pairwise_m ks) = 1 \<and>
     eval ws dw vs dv (pairwise_m ks) =
       of_bool (\<forall>i j. i < j \<and> j < length ks \<longrightarrow> eval ws dw vs dv (tref (ks ! i)) \<noteq> eval ws dw vs dv (tref (ks ! j)))\<close>
proof -
  let ?e = \<open>\<lambda>i. eval ws dw vs dv (tref (ks ! i))\<close>
  let ?f = \<open>\<lambda>acc ij. Term_Bin Op_And acc (Term_Bin Op_Distinct (tref (ks ! fst ij)) (tref (ks ! snd ij)))\<close>
  have g: \<open>\<forall>ij \<in> set ix. fst ij < length ks \<and> snd ij < length ks \<Longrightarrow> wt ws dw acc \<Longrightarrow> width ws dw acc = 1 \<Longrightarrow>
      eval ws dw vs dv acc = of_bool A \<Longrightarrow>
      wt ws dw (foldl ?f acc ix) \<and> width ws dw (foldl ?f acc ix) = 1 \<and>
      eval ws dw vs dv (foldl ?f acc ix) = of_bool (A \<and> (\<forall>ij \<in> set ix. ?e (fst ij) \<noteq> ?e (snd ij)))\<close> for ix acc A
  proof (induction ix arbitrary: acc A)
    case Nil
    then show ?case by simp
  next
    case (Cons ij ix)
    have m: \<open>ks ! fst ij \<in> set ks\<close> \<open>ks ! snd ij \<in> set ks\<close> using Cons.prems(1) by (simp_all add: nth_mem)
    then have r: \<open>wt ws dw (tref (ks ! fst ij)) \<and> width ws dw (tref (ks ! fst ij)) = w\<close>
      \<open>wt ws dw (tref (ks ! snd ij)) \<and> width ws dw (tref (ks ! snd ij)) = w\<close> using assms(2) by blast+
    have \<open>eval ws dw vs dv (?f acc ij) = of_bool (A \<and> ?e (fst ij) \<noteq> ?e (snd ij))\<close>
      using Cons.prems by (simp add: and_bool_s)
    moreover have \<open>wt ws dw (?f acc ij) \<and> width ws dw (?f acc ij) = 1\<close> using Cons.prems r by simp
    ultimately show ?case using Cons.IH[of \<open>?f acc ij\<close> \<open>A \<and> ?e (fst ij) \<noteq> ?e (snd ij)\<close>] Cons.prems by auto
  qed
  have l: \<open>0 < length ks\<close> \<open>1 < length ks\<close> using assms(1) by linarith+
  have m: \<open>ks ! 0 \<in> set ks\<close> \<open>ks ! 1 \<in> set ks\<close> using nth_mem[OF l(1)] nth_mem[OF l(2)] .
  have k01: \<open>wt ws dw (tref (ks ! 0)) \<and> width ws dw (tref (ks ! 0)) = w\<close>
    \<open>wt ws dw (tref (ks ! 1)) \<and> width ws dw (tref (ks ! 1)) = w\<close>
    using assms(2) m by blast+
  have p: \<open>\<forall>ij \<in> set (pairs_m (length ks)). fst ij < length ks \<and> snd ij < length ks\<close>
    by (auto simp: pairs_m_def)
  have \<open>(?e 0 \<noteq> ?e 1 \<and> (\<forall>ij \<in> set (pairs_m (length ks)). ?e (fst ij) \<noteq> ?e (snd ij))) =
        (\<forall>ij \<in> insert (0, 1) (set (pairs_m (length ks))). ?e (fst ij) \<noteq> ?e (snd ij))\<close> by simp
  also have \<open>\<dots> = (\<forall>i j. i < j \<and> j < length ks \<longrightarrow> ?e i \<noteq> ?e j)\<close>
    by (simp only: pairs_m_set[OF assms(1)]) auto
  finally show ?thesis
    using g[OF p, of \<open>Term_Bin Op_Distinct (tref (ks ! 0)) (tref (ks ! 1))\<close> \<open>?e 0 \<noteq> ?e 1\<close>] k01
    by (simp add: pairwise_m_def)
qed

lemma implies_eval:
  assumes \<open>ks \<noteq> []\<close> \<open>\<forall>k \<in> set ks. wt ws dw (tref k) \<and> width ws dw (tref k) = 1 \<and> eval ws dw vs dv (tref k) \<in> {0, 1}\<close>
  shows \<open>wt ws dw (implies_m ks) \<and> width ws dw (implies_m ks) = 1 \<and>
     eval ws dw vs dv (implies_m ks) =
       of_bool ((\<exists>k \<in> set (butlast ks). eval ws dw vs dv (tref k) = 0) \<or> eval ws dw vs dv (tref (last ks)) = 1)\<close>
  using assms
proof (induction ks rule: induct_list012)
  case (2 k)
  then show ?case by (auto simp: implies_m_def)
next
  case (3 k1 k2 ks)
  let ?r = \<open>foldr (\<lambda>k acc. Term_Bin Op_Or (Term_Not (tref k)) acc) (butlast (k2 # ks)) (tref (last (k2 # ks)))\<close>
  have ih: \<open>wt ws dw ?r \<and> width ws dw ?r = 1 \<and>
     eval ws dw vs dv ?r = of_bool ((\<exists>k \<in> set (butlast (k2 # ks)). eval ws dw vs dv (tref k) = 0) \<or>
       eval ws dw vs dv (tref (last (k2 # ks))) = 1)\<close>
    using 3 by (simp add: implies_m_def)
  have k1: \<open>wt ws dw (tref k1) \<and> width ws dw (tref k1) = 1 \<and> eval ws dw vs dv (tref k1) \<in> {0, 1}\<close> using 3 by simp
  have e: \<open>implies_m (k1 # k2 # ks) = Term_Bin Op_Or (Term_Not (tref k1)) ?r\<close> by (simp add: implies_m_def)
  show ?case using ih k1 unfolding e
    by (cases \<open>eval ws dw vs dv (tref k1) = 0\<close>) (auto simp: Bit_Operations.or_eq_0_iff)
qed simp

lemma fold_op_width_pres: \<open>fold_op op \<Longrightarrow> width_pres (tr_op op)\<close>
  by (cases op) (auto simp: width_pres_def)

text \<open>The translation of a fold function is a chain from the left (one step for a binary one).\<close>
lemma tr_app_fold:
  \<open>fold_op op \<Longrightarrow> smt_op_sort op ss = Some s \<Longrightarrow> length ks = length ss \<Longrightarrow>
     tr_app_m op ks = foldl (\<lambda>acc k. Term_Bin (tr_op op) acc (tref k)) (tref (hd ks)) (tl ks)\<close>
  by (cases op) (auto simp: fold_left_m_def dest!: smt_bin_width_Some split: if_splits;
      cases ks; auto simp: numeral_2_eq_2 length_Suc_conv)+

lemma foldl_map_h: \<open>foldl (\<lambda>a k. f a (h k)) a ks = foldl f a (map h ks)\<close>
  by (induction ks arbitrary: a) auto

lemma la2_one_bv: \<open>list_all2 smt_has_sort [SmtSort_BitVec m] xs \<Longrightarrow> \<exists>v. xs = [VBv (unat m) v] \<and> v < 2 ^ unat m\<close>
  by (cases xs) (auto split: sval.splits)

lemma la2_two_bv:
  \<open>list_all2 smt_has_sort [SmtSort_BitVec a, SmtSort_BitVec b] xs \<Longrightarrow>
     \<exists>x y. xs = [VBv (unat a) x, VBv (unat b) y] \<and> x < 2 ^ unat a \<and> y < 2 ^ unat b\<close>
  by (cases xs; cases \<open>tl xs\<close>) (auto split: sval.splits)

lemma la2_bools: \<open>list_all2 smt_has_sort ss xs \<Longrightarrow> set ss \<subseteq> {SmtSort_Bool} \<Longrightarrow> \<exists>bs. xs = map VBool bs\<close>
proof (induction ss xs rule: list_all2_induct)
  case Nil
  then show ?case by simp
next
  case (Cons s ss x xs)
  then obtain bs where \<open>xs = map VBool bs\<close> by auto
  moreover obtain b where \<open>x = VBool b\<close> using Cons by (cases x) auto
  ultimately show ?case by (metis list.simps(9))
qed

lemma bool_fold_eval:
  assumes \<open>width_pres bop\<close> \<open>ks \<noteq> []\<close> \<open>length ks = length bs\<close>
    \<open>\<forall>i < length ks. wt ws dw (tref (ks ! i)) \<and> width ws dw (tref (ks ! i)) = 1 \<and> eval ws dw vs dv (tref (ks ! i)) = of_bool (bs ! i)\<close>
  shows \<open>wt ws dw (foldl (\<lambda>acc k. Term_Bin bop acc (tref k)) (tref (hd ks)) (tl ks)) \<and>
     width ws dw (foldl (\<lambda>acc k. Term_Bin bop acc (tref k)) (tref (hd ks)) (tl ks)) = 1 \<and>
     eval ws dw vs dv (foldl (\<lambda>acc k. Term_Bin bop acc (tref k)) (tref (hd ks)) (tl ks)) =
       foldl (\<lambda>a b. bin_sem bop 1 a 1 (of_bool b)) (of_bool (hd bs)) (tl bs)\<close>
proof -
  have K: \<open>\<forall>k \<in> set ks. wt ws dw (tref k) \<and> width ws dw (tref k) = 1\<close>
    using assms(4) by (auto simp: in_set_conv_nth)
  have E: \<open>map (\<lambda>k. eval ws dw vs dv (tref k)) ks = map of_bool bs\<close>
    using assms(3,4) by (auto intro!: nth_equalityI)
  have h: \<open>eval ws dw vs dv (tref (hd ks)) = of_bool (hd bs)\<close>
    using E assms(2,3) by (metis hd_map list.map_disc_iff)
  have tl: \<open>map (\<lambda>k. eval ws dw vs dv (tref k)) (tl ks) = map of_bool (tl bs)\<close> using E by (metis map_tl)
  have hk: \<open>hd ks \<in> set ks\<close> \<open>\<forall>k \<in> set (tl ks). k \<in> set ks\<close> using assms(2) by (auto simp: list.set_sel)
  show ?thesis
    using fold_left_eval[OF assms(1), where ws=ws and dw=dw and ks=\<open>tl ks\<close> and w=1 and acc=\<open>tref (hd ks)\<close> and vs=vs and dv=dv]
      K hk h tl foldl_map_h[of \<open>\<lambda>a. bin_sem bop 1 a 1\<close> \<open>\<lambda>k. eval ws dw vs dv (tref k)\<close>]
      foldl_map_h[of \<open>\<lambda>a. bin_sem bop 1 a 1\<close> of_bool]
    by auto
qed

lemma la2_one_bool: \<open>list_all2 smt_has_sort [SmtSort_Bool] xs \<Longrightarrow> \<exists>b. xs = [VBool b]\<close>
  by (cases xs) (auto split: sval.splits)

lemma smt_true_VBool: \<open>smt_true \<circ> VBool = id\<close>
  by (simp add: fun_eq_iff)

lemma la2_ite:
  \<open>list_all2 smt_has_sort [SmtSort_Bool, a, a] xs \<Longrightarrow>
     \<exists>c x y. xs = [VBool c, x, y] \<and> smt_has_sort a x \<and> smt_has_sort a y\<close>
  by (cases xs; cases \<open>tl xs\<close>; cases \<open>tl (tl xs)\<close>) (auto split: sval.splits)

lemma ex_zero_map: \<open>map f ks = map of_bool bs \<Longrightarrow> (\<exists>k \<in> set ks. f k = (0 :: nat)) = (\<exists>b \<in> set bs. \<not> b)\<close>
proof (induction ks arbitrary: bs)
  case Nil
  then show ?case by simp
next
  case (Cons k ks)
  then obtain b bs' where \<open>bs = b # bs'\<close> \<open>f k = of_bool b\<close> \<open>map f ks = map of_bool bs'\<close> by (cases bs) auto
  then show ?case using Cons.IH by auto
qed

lemma distinct_lt: \<open>distinct xs = (\<forall>i j. i < j \<and> j < length xs \<longrightarrow> xs ! i \<noteq> xs ! j)\<close>
proof -
  have \<open>(\<forall>i < length xs. \<forall>j < length xs. i \<noteq> j \<longrightarrow> xs ! i \<noteq> xs ! j) = (\<forall>i j. i < j \<and> j < length xs \<longrightarrow> xs ! i \<noteq> xs ! j)\<close>
  proof
    assume \<open>\<forall>i j. i < j \<and> j < length xs \<longrightarrow> xs ! i \<noteq> xs ! j\<close>
    then show \<open>\<forall>i < length xs. \<forall>j < length xs. i \<noteq> j \<longrightarrow> xs ! i \<noteq> xs ! j\<close>
      by (metis linorder_neqE_nat)
  qed auto
  then show ?thesis by (simp add: distinct_conv_nth)
qed

lemma tr_app_correct:
  assumes \<open>smt_op_sort op ss = Some s\<close> \<open>\<forall>x \<in> set ss. frag_sort x\<close>
    \<open>length ks = length ss\<close> \<open>length xs = length ss\<close>
    \<open>\<forall>i < length ss. ref_ok ws vs S (ks ! i) (ss ! i) (xs ! i)\<close>
  shows \<open>wt ws (def_widths ws [] S) (tr_app_m op ks) \<and>
         width ws (def_widths ws [] S) (tr_app_m op ks) = sort_width_m s \<and>
         eval ws (def_widths ws [] S) vs (def_values ws [] vs [] S) (tr_app_m op ks) = enc (smt_op_sem op xs)\<close>
proof -
  let ?dw = \<open>def_widths ws [] S\<close> and ?dv = \<open>def_values ws [] vs [] S\<close>
  have T: \<open>wt ws ?dw (tref (ks ! i)) \<and> width ws ?dw (tref (ks ! i)) = sort_width_m (ss ! i) \<and>
      eval ws ?dw vs ?dv (tref (ks ! i)) = enc (xs ! i)\<close> if \<open>i < length ss\<close> for i
    using tref_ok[OF assms(5)[rule_format, OF that]] assms(2) that by (meson nth_mem)
  have H: \<open>list_all2 smt_has_sort ss xs\<close> using assms(4,5) by (auto simp: list_all2_conv_all_nth ref_ok_def)
  show ?thesis
  proof (cases \<open>fold_op op\<close>)
    case True
    obtain a where a: \<open>ss \<noteq> []\<close> \<open>\<forall>x \<in> set ss. x = SmtSort_BitVec a\<close> \<open>s = SmtSort_BitVec a\<close>
      using fold_op_sort[OF True assms(1)] by blast
    have w1: \<open>1 \<le> unat a\<close> using assms(2) a(1,2) by (cases ss) auto
    have K: \<open>\<forall>k \<in> set ks. wt ws ?dw (tref k) \<and> width ws ?dw (tref k) = unat a\<close>
    proof
      fix k assume \<open>k \<in> set ks\<close>
      then obtain i where \<open>i < length ss\<close> \<open>k = ks ! i\<close> using assms(3) by (auto simp: in_set_conv_nth)
      then show \<open>wt ws ?dw (tref k) \<and> width ws ?dw (tref k) = unat a\<close> using T a(2) by (metis nth_mem sort_width_m.simps(2))
    qed
    have X: \<open>xs ! i = VBv (unat a) (smt_bv_val (xs ! i))\<close> if \<open>i < length xs\<close> for i
    proof -
      have h: \<open>smt_has_sort (ss ! i) (xs ! i)\<close> and i: \<open>i < length ss\<close>
        using H that by (simp_all add: list_all2_conv_all_nth)
      have \<open>ss ! i = SmtSort_BitVec a\<close> using a(2) i by (meson nth_mem)
      then show ?thesis using h by (cases \<open>xs ! i\<close>) auto
    qed
    have E: \<open>map (\<lambda>k. eval ws ?dw vs ?dv (tref k)) ks = map smt_bv_val xs\<close>
    proof (rule nth_equalityI)
      show \<open>length (map (\<lambda>k. eval ws ?dw vs ?dv (tref k)) ks) = length (map smt_bv_val xs)\<close> using assms(3,4) by simp
    next
      fix i assume \<open>i < length (map (\<lambda>k. eval ws ?dw vs ?dv (tref k)) ks)\<close>
      then have i: \<open>i < length ss\<close> using assms(3) by simp
      then show \<open>map (\<lambda>k. eval ws ?dw vs ?dv (tref k)) ks ! i = map smt_bv_val xs ! i\<close>
        using T[OF i] X[of i] assms(3,4) by (metis enc.simps(2) nth_map)
    qed
    have ks0: \<open>ks \<noteq> []\<close> using a(1) assms(3) by auto
    have hk: \<open>hd ks \<in> set ks\<close> \<open>set (tl ks) \<subseteq> set ks\<close> using ks0 by (auto simp: list.set_sel)
    have xs0: \<open>0 < length xs\<close> \<open>0 < length ks\<close> using ks0 assms(3,4) by auto
    have hx: \<open>smt_bv_width (hd xs) = unat a\<close> \<open>smt_bv_val (hd xs) = eval ws ?dw vs ?dv (tref (hd ks))\<close>
    proof -
      have \<open>hd xs = xs ! 0\<close> \<open>hd ks = ks ! 0\<close> using xs0 by (simp_all add: hd_conv_nth)
      moreover have \<open>map (\<lambda>k. eval ws ?dw vs ?dv (tref k)) ks ! 0 = map smt_bv_val xs ! 0\<close> using E by simp
      ultimately show \<open>smt_bv_width (hd xs) = unat a\<close> \<open>smt_bv_val (hd xs) = eval ws ?dw vs ?dv (tref (hd ks))\<close>
        using X[OF xs0(1)] xs0 by (metis smt_bv_width.simps(1), simp)
    qed
    have tlE: \<open>map (\<lambda>k. eval ws ?dw vs ?dv (tref k)) (tl ks) = map smt_bv_val (tl xs)\<close>
      using E by (metis map_tl)
    have F: \<open>wt ws ?dw (tr_app_m op ks) \<and> width ws ?dw (tr_app_m op ks) = unat a \<and>
        eval ws ?dw vs ?dv (tr_app_m op ks) =
          foldl (\<lambda>x k. bin_sem (tr_op op) (unat a) x (unat a) k) (eval ws ?dw vs ?dv (tref (hd ks)))
            (map (\<lambda>k. eval ws ?dw vs ?dv (tref k)) (tl ks))\<close>
      using fold_left_eval[OF fold_op_width_pres[OF True], where ws=ws and dw=\<open>?dw\<close> and ks=\<open>tl ks\<close>
          and w=\<open>unat a\<close> and acc=\<open>tref (hd ks)\<close> and vs=vs and dv=\<open>?dv\<close>] K hk subsetD[OF hk(2)]
        tr_app_fold[OF True assms(1)] assms(3)
        foldl_map_h[of \<open>\<lambda>x. bin_sem (tr_op op) (unat a) x (unat a)\<close> \<open>\<lambda>k. eval ws ?dw vs ?dv (tref k)\<close>]
      by auto
    show ?thesis using F a(3) hx tlE fold_op_sem[OF True, of xs] bin_sem_fold[OF True]
      by (simp add: foldl_map_h del: smt_bv_bin.simps)
  next
    case False
    then show ?thesis
    proof (cases op)
      case (SmtOp_Bvnot)
      then obtain m where ss: \<open>ss = [SmtSort_BitVec m]\<close> and sx: \<open>s \<noteq> SmtSort_Bool\<close>
        using assms(1) by (auto split: list.splits SmtSort.splits if_splits)
      obtain v where xs: \<open>xs = [VBv (unat m) v]\<close> \<open>v < 2 ^ unat m\<close>
        using la2_one_bv H ss by blast
      have t: \<open>wt ws ?dw (tref (ks ! 0))\<close> \<open>width ws ?dw (tref (ks ! 0)) = unat m\<close> \<open>eval ws ?dw vs ?dv (tref (ks ! 0)) = v\<close>
        using T[of 0] ss xs by auto
      have m1: \<open>1 \<le> unat m\<close> using assms(2) ss by auto
      show ?thesis using t ss xs m1 assms(1) SmtOp_Bvnot
        by (auto simp: Let_def  split: if_splits)
    next
      case (SmtOp_Bvneg)
      then obtain m where ss: \<open>ss = [SmtSort_BitVec m]\<close> and sx: \<open>s \<noteq> SmtSort_Bool\<close>
        using assms(1) by (auto split: list.splits SmtSort.splits if_splits)
      obtain v where xs: \<open>xs = [VBv (unat m) v]\<close> \<open>v < 2 ^ unat m\<close>
        using la2_one_bv H ss by blast
      have t: \<open>wt ws ?dw (tref (ks ! 0))\<close> \<open>width ws ?dw (tref (ks ! 0)) = unat m\<close> \<open>eval ws ?dw vs ?dv (tref (ks ! 0)) = v\<close>
        using T[of 0] ss xs by auto
      have m1: \<open>1 \<le> unat m\<close> using assms(2) ss by auto
      show ?thesis using t ss xs m1 assms(1) SmtOp_Bvneg
        by (auto simp: Let_def  split: if_splits)
    next
      case (SmtOp_Extract i j)
      then obtain m where ss: \<open>ss = [SmtSort_BitVec m]\<close> and sx: \<open>s \<noteq> SmtSort_Bool\<close>
        using assms(1) by (auto split: list.splits SmtSort.splits if_splits)
      obtain v where xs: \<open>xs = [VBv (unat m) v]\<close> \<open>v < 2 ^ unat m\<close>
        using la2_one_bv H ss by blast
      have t: \<open>wt ws ?dw (tref (ks ! 0))\<close> \<open>width ws ?dw (tref (ks ! 0)) = unat m\<close> \<open>eval ws ?dw vs ?dv (tref (ks ! 0)) = v\<close>
        using T[of 0] ss xs by auto
      have m1: \<open>1 \<le> unat m\<close> using assms(2) ss by auto
      show ?thesis using t ss xs m1 assms(1) SmtOp_Extract
        by (auto simp: Let_def unat_extract_s split: if_splits)
    next
      case (SmtOp_Repeat i)
      then obtain m where ss: \<open>ss = [SmtSort_BitVec m]\<close> and sx: \<open>s \<noteq> SmtSort_Bool\<close>
        using assms(1) by (auto split: list.splits SmtSort.splits if_splits)
      obtain v where xs: \<open>xs = [VBv (unat m) v]\<close> \<open>v < 2 ^ unat m\<close>
        using la2_one_bv H ss by blast
      have t: \<open>wt ws ?dw (tref (ks ! 0))\<close> \<open>width ws ?dw (tref (ks ! 0)) = unat m\<close> \<open>eval ws ?dw vs ?dv (tref (ks ! 0)) = v\<close>
        using T[of 0] ss xs by auto
      have m1: \<open>1 \<le> unat m\<close> using assms(2) ss by auto
      show ?thesis using t ss xs m1 assms(1) SmtOp_Repeat
        by (auto simp: Let_def unat_mult_s mult.commute helper_defs_eq split: if_splits)
    next
      case (SmtOp_ZeroExtend i)
      then obtain m where ss: \<open>ss = [SmtSort_BitVec m]\<close> and sx: \<open>s \<noteq> SmtSort_Bool\<close>
        using assms(1) by (auto split: list.splits SmtSort.splits if_splits)
      obtain v where xs: \<open>xs = [VBv (unat m) v]\<close> \<open>v < 2 ^ unat m\<close>
        using la2_one_bv H ss by blast
      have t: \<open>wt ws ?dw (tref (ks ! 0))\<close> \<open>width ws ?dw (tref (ks ! 0)) = unat m\<close> \<open>eval ws ?dw vs ?dv (tref (ks ! 0)) = v\<close>
        using T[of 0] ss xs by auto
      have m1: \<open>1 \<le> unat m\<close> using assms(2) ss by auto
      show ?thesis using t ss xs m1 assms(1) SmtOp_ZeroExtend
        by (auto simp: Let_def unat_add_s split: if_splits)
    next
      case (SmtOp_SignExtend i)
      then obtain m where ss: \<open>ss = [SmtSort_BitVec m]\<close> and sx: \<open>s \<noteq> SmtSort_Bool\<close>
        using assms(1) by (auto split: list.splits SmtSort.splits if_splits)
      obtain v where xs: \<open>xs = [VBv (unat m) v]\<close> \<open>v < 2 ^ unat m\<close>
        using la2_one_bv H ss by blast
      have t: \<open>wt ws ?dw (tref (ks ! 0))\<close> \<open>width ws ?dw (tref (ks ! 0)) = unat m\<close> \<open>eval ws ?dw vs ?dv (tref (ks ! 0)) = v\<close>
        using T[of 0] ss xs by auto
      have m1: \<open>1 \<le> unat m\<close> using assms(2) ss by auto
      show ?thesis using t ss xs m1 assms(1) SmtOp_SignExtend
        by (auto simp: Let_def unat_add_s helper_defs_eq split: if_splits)
    next
      case (SmtOp_RotateLeft i)
      then obtain m where ss: \<open>ss = [SmtSort_BitVec m]\<close> and sx: \<open>s \<noteq> SmtSort_Bool\<close>
        using assms(1) by (auto split: list.splits SmtSort.splits if_splits)
      obtain v where xs: \<open>xs = [VBv (unat m) v]\<close> \<open>v < 2 ^ unat m\<close>
        using la2_one_bv H ss by blast
      have t: \<open>wt ws ?dw (tref (ks ! 0))\<close> \<open>width ws ?dw (tref (ks ! 0)) = unat m\<close> \<open>eval ws ?dw vs ?dv (tref (ks ! 0)) = v\<close>
        using T[of 0] ss xs by auto
      have m1: \<open>1 \<le> unat m\<close> using assms(2) ss by auto
      show ?thesis using t ss xs m1 assms(1) SmtOp_RotateLeft
        by (auto simp: Let_def split: if_splits)
    next
      case (SmtOp_RotateRight i)
      then obtain m where ss: \<open>ss = [SmtSort_BitVec m]\<close> and sx: \<open>s \<noteq> SmtSort_Bool\<close>
        using assms(1) by (auto split: list.splits SmtSort.splits if_splits)
      obtain v where xs: \<open>xs = [VBv (unat m) v]\<close> \<open>v < 2 ^ unat m\<close>
        using la2_one_bv H ss by blast
      have t: \<open>wt ws ?dw (tref (ks ! 0))\<close> \<open>width ws ?dw (tref (ks ! 0)) = unat m\<close> \<open>eval ws ?dw vs ?dv (tref (ks ! 0)) = v\<close>
        using T[of 0] ss xs by auto
      have m1: \<open>1 \<le> unat m\<close> using assms(2) ss by auto
      show ?thesis using t ss xs m1 assms(1) SmtOp_RotateRight
        by (auto simp: Let_def split: if_splits)
    next
      case SmtOp_Concat
      then obtain a b where ss: \<open>ss = [SmtSort_BitVec a, SmtSort_BitVec b]\<close>
        using assms(1) by (auto dest!: smt_bin_width_Some split: list.splits SmtSort.splits if_splits)
      obtain x y where xs: \<open>xs = [VBv (unat a) x, VBv (unat b) y]\<close> \<open>x < 2 ^ unat a\<close> \<open>y < 2 ^ unat b\<close>
        using la2_two_bv H ss by blast
      have t: \<open>wt ws ?dw (tref (ks ! 0))\<close> \<open>width ws ?dw (tref (ks ! 0)) = unat a\<close> \<open>eval ws ?dw vs ?dv (tref (ks ! 0)) = x\<close>
        \<open>wt ws ?dw (tref (ks ! 1))\<close> \<open>width ws ?dw (tref (ks ! 1)) = unat b\<close> \<open>eval ws ?dw vs ?dv (tref (ks ! 1)) = y\<close>
        using T[of 0] T[of 1] ss xs by auto
      show ?thesis using t ss xs assms(1) SmtOp_Concat
        by (auto simp: Let_def unat_add_s dest!: smt_bin_width_Some split: if_splits)
    next
      case SmtOp_Bvcomp
      then obtain a b where ss: \<open>ss = [SmtSort_BitVec a, SmtSort_BitVec b]\<close>
        using assms(1) by (auto dest!: smt_bin_width_Some split: list.splits SmtSort.splits if_splits)
      obtain x y where xs: \<open>xs = [VBv (unat a) x, VBv (unat b) y]\<close> \<open>x < 2 ^ unat a\<close> \<open>y < 2 ^ unat b\<close>
        using la2_two_bv H ss by blast
      have t: \<open>wt ws ?dw (tref (ks ! 0))\<close> \<open>width ws ?dw (tref (ks ! 0)) = unat a\<close> \<open>eval ws ?dw vs ?dv (tref (ks ! 0)) = x\<close>
        \<open>wt ws ?dw (tref (ks ! 1))\<close> \<open>width ws ?dw (tref (ks ! 1)) = unat b\<close> \<open>eval ws ?dw vs ?dv (tref (ks ! 1)) = y\<close>
        using T[of 0] T[of 1] ss xs by auto
      show ?thesis using t ss xs assms(1) SmtOp_Bvcomp
        by (auto simp: Let_def  dest!: smt_bin_width_Some split: if_splits)
    next
      case SmtOp_Bvult
      then obtain a b where ss: \<open>ss = [SmtSort_BitVec a, SmtSort_BitVec b]\<close>
        using assms(1) by (auto dest!: smt_bin_width_Some split: list.splits SmtSort.splits if_splits)
      obtain x y where xs: \<open>xs = [VBv (unat a) x, VBv (unat b) y]\<close> \<open>x < 2 ^ unat a\<close> \<open>y < 2 ^ unat b\<close>
        using la2_two_bv H ss by blast
      have t: \<open>wt ws ?dw (tref (ks ! 0))\<close> \<open>width ws ?dw (tref (ks ! 0)) = unat a\<close> \<open>eval ws ?dw vs ?dv (tref (ks ! 0)) = x\<close>
        \<open>wt ws ?dw (tref (ks ! 1))\<close> \<open>width ws ?dw (tref (ks ! 1)) = unat b\<close> \<open>eval ws ?dw vs ?dv (tref (ks ! 1)) = y\<close>
        using T[of 0] T[of 1] ss xs by auto
      show ?thesis using t ss xs assms(1) SmtOp_Bvult
        by (auto simp: Let_def helper_defs_eq dest!: smt_bin_width_Some split: if_splits)
    next
      case SmtOp_Bvule
      then obtain a b where ss: \<open>ss = [SmtSort_BitVec a, SmtSort_BitVec b]\<close>
        using assms(1) by (auto dest!: smt_bin_width_Some split: list.splits SmtSort.splits if_splits)
      obtain x y where xs: \<open>xs = [VBv (unat a) x, VBv (unat b) y]\<close> \<open>x < 2 ^ unat a\<close> \<open>y < 2 ^ unat b\<close>
        using la2_two_bv H ss by blast
      have t: \<open>wt ws ?dw (tref (ks ! 0))\<close> \<open>width ws ?dw (tref (ks ! 0)) = unat a\<close> \<open>eval ws ?dw vs ?dv (tref (ks ! 0)) = x\<close>
        \<open>wt ws ?dw (tref (ks ! 1))\<close> \<open>width ws ?dw (tref (ks ! 1)) = unat b\<close> \<open>eval ws ?dw vs ?dv (tref (ks ! 1)) = y\<close>
        using T[of 0] T[of 1] ss xs by auto
      show ?thesis using t ss xs assms(1) SmtOp_Bvule
        by (auto simp: Let_def helper_defs_eq dest!: smt_bin_width_Some split: if_splits)
    next
      case SmtOp_Bvugt
      then obtain a b where ss: \<open>ss = [SmtSort_BitVec a, SmtSort_BitVec b]\<close>
        using assms(1) by (auto dest!: smt_bin_width_Some split: list.splits SmtSort.splits if_splits)
      obtain x y where xs: \<open>xs = [VBv (unat a) x, VBv (unat b) y]\<close> \<open>x < 2 ^ unat a\<close> \<open>y < 2 ^ unat b\<close>
        using la2_two_bv H ss by blast
      have t: \<open>wt ws ?dw (tref (ks ! 0))\<close> \<open>width ws ?dw (tref (ks ! 0)) = unat a\<close> \<open>eval ws ?dw vs ?dv (tref (ks ! 0)) = x\<close>
        \<open>wt ws ?dw (tref (ks ! 1))\<close> \<open>width ws ?dw (tref (ks ! 1)) = unat b\<close> \<open>eval ws ?dw vs ?dv (tref (ks ! 1)) = y\<close>
        using T[of 0] T[of 1] ss xs by auto
      show ?thesis using t ss xs assms(1) SmtOp_Bvugt
        by (auto simp: Let_def helper_defs_eq dest!: smt_bin_width_Some split: if_splits)
    next
      case SmtOp_Bvuge
      then obtain a b where ss: \<open>ss = [SmtSort_BitVec a, SmtSort_BitVec b]\<close>
        using assms(1) by (auto dest!: smt_bin_width_Some split: list.splits SmtSort.splits if_splits)
      obtain x y where xs: \<open>xs = [VBv (unat a) x, VBv (unat b) y]\<close> \<open>x < 2 ^ unat a\<close> \<open>y < 2 ^ unat b\<close>
        using la2_two_bv H ss by blast
      have t: \<open>wt ws ?dw (tref (ks ! 0))\<close> \<open>width ws ?dw (tref (ks ! 0)) = unat a\<close> \<open>eval ws ?dw vs ?dv (tref (ks ! 0)) = x\<close>
        \<open>wt ws ?dw (tref (ks ! 1))\<close> \<open>width ws ?dw (tref (ks ! 1)) = unat b\<close> \<open>eval ws ?dw vs ?dv (tref (ks ! 1)) = y\<close>
        using T[of 0] T[of 1] ss xs by auto
      show ?thesis using t ss xs assms(1) SmtOp_Bvuge
        by (auto simp: Let_def helper_defs_eq dest!: smt_bin_width_Some split: if_splits)
    next
      case SmtOp_Bvslt
      then obtain a b where ss: \<open>ss = [SmtSort_BitVec a, SmtSort_BitVec b]\<close>
        using assms(1) by (auto dest!: smt_bin_width_Some split: list.splits SmtSort.splits if_splits)
      obtain x y where xs: \<open>xs = [VBv (unat a) x, VBv (unat b) y]\<close> \<open>x < 2 ^ unat a\<close> \<open>y < 2 ^ unat b\<close>
        using la2_two_bv H ss by blast
      have t: \<open>wt ws ?dw (tref (ks ! 0))\<close> \<open>width ws ?dw (tref (ks ! 0)) = unat a\<close> \<open>eval ws ?dw vs ?dv (tref (ks ! 0)) = x\<close>
        \<open>wt ws ?dw (tref (ks ! 1))\<close> \<open>width ws ?dw (tref (ks ! 1)) = unat b\<close> \<open>eval ws ?dw vs ?dv (tref (ks ! 1)) = y\<close>
        using T[of 0] T[of 1] ss xs by auto
      show ?thesis using t ss xs assms(1) SmtOp_Bvslt
        by (auto simp: Let_def helper_defs_eq dest!: smt_bin_width_Some split: if_splits)
    next
      case SmtOp_Bvsle
      then obtain a b where ss: \<open>ss = [SmtSort_BitVec a, SmtSort_BitVec b]\<close>
        using assms(1) by (auto dest!: smt_bin_width_Some split: list.splits SmtSort.splits if_splits)
      obtain x y where xs: \<open>xs = [VBv (unat a) x, VBv (unat b) y]\<close> \<open>x < 2 ^ unat a\<close> \<open>y < 2 ^ unat b\<close>
        using la2_two_bv H ss by blast
      have t: \<open>wt ws ?dw (tref (ks ! 0))\<close> \<open>width ws ?dw (tref (ks ! 0)) = unat a\<close> \<open>eval ws ?dw vs ?dv (tref (ks ! 0)) = x\<close>
        \<open>wt ws ?dw (tref (ks ! 1))\<close> \<open>width ws ?dw (tref (ks ! 1)) = unat b\<close> \<open>eval ws ?dw vs ?dv (tref (ks ! 1)) = y\<close>
        using T[of 0] T[of 1] ss xs by auto
      show ?thesis using t ss xs assms(1) SmtOp_Bvsle
        by (auto simp: Let_def helper_defs_eq dest!: smt_bin_width_Some split: if_splits)
    next
      case SmtOp_Bvsgt
      then obtain a b where ss: \<open>ss = [SmtSort_BitVec a, SmtSort_BitVec b]\<close>
        using assms(1) by (auto dest!: smt_bin_width_Some split: list.splits SmtSort.splits if_splits)
      obtain x y where xs: \<open>xs = [VBv (unat a) x, VBv (unat b) y]\<close> \<open>x < 2 ^ unat a\<close> \<open>y < 2 ^ unat b\<close>
        using la2_two_bv H ss by blast
      have t: \<open>wt ws ?dw (tref (ks ! 0))\<close> \<open>width ws ?dw (tref (ks ! 0)) = unat a\<close> \<open>eval ws ?dw vs ?dv (tref (ks ! 0)) = x\<close>
        \<open>wt ws ?dw (tref (ks ! 1))\<close> \<open>width ws ?dw (tref (ks ! 1)) = unat b\<close> \<open>eval ws ?dw vs ?dv (tref (ks ! 1)) = y\<close>
        using T[of 0] T[of 1] ss xs by auto
      show ?thesis using t ss xs assms(1) SmtOp_Bvsgt
        by (auto simp: Let_def helper_defs_eq dest!: smt_bin_width_Some split: if_splits)
    next
      case SmtOp_Bvsge
      then obtain a b where ss: \<open>ss = [SmtSort_BitVec a, SmtSort_BitVec b]\<close>
        using assms(1) by (auto dest!: smt_bin_width_Some split: list.splits SmtSort.splits if_splits)
      obtain x y where xs: \<open>xs = [VBv (unat a) x, VBv (unat b) y]\<close> \<open>x < 2 ^ unat a\<close> \<open>y < 2 ^ unat b\<close>
        using la2_two_bv H ss by blast
      have t: \<open>wt ws ?dw (tref (ks ! 0))\<close> \<open>width ws ?dw (tref (ks ! 0)) = unat a\<close> \<open>eval ws ?dw vs ?dv (tref (ks ! 0)) = x\<close>
        \<open>wt ws ?dw (tref (ks ! 1))\<close> \<open>width ws ?dw (tref (ks ! 1)) = unat b\<close> \<open>eval ws ?dw vs ?dv (tref (ks ! 1)) = y\<close>
        using T[of 0] T[of 1] ss xs by auto
      show ?thesis using t ss xs assms(1) SmtOp_Bvsge
        by (auto simp: Let_def helper_defs_eq dest!: smt_bin_width_Some split: if_splits)
    next
      case SmtOp_Not
      then have ss: \<open>ss = [SmtSort_Bool]\<close> \<open>s = SmtSort_Bool\<close> using assms(1) by (auto split: if_splits)
      obtain b where xs: \<open>xs = [VBool b]\<close> using la2_one_bool H ss(1) by blast
      have t: \<open>wt ws ?dw (tref (ks ! 0))\<close> \<open>width ws ?dw (tref (ks ! 0)) = 1\<close> \<open>eval ws ?dw vs ?dv (tref (ks ! 0)) = of_bool b\<close>
        using T[of 0] ss xs by auto
      show ?thesis using t ss xs SmtOp_Not by (cases b) auto
    next
      case SmtOp_And
      then have ss: \<open>2 \<le> length ss\<close> \<open>set ss \<subseteq> {SmtSort_Bool}\<close> \<open>s = SmtSort_Bool\<close>
        using assms(1) by (auto split: if_splits)
      obtain bs where xs: \<open>xs = map VBool bs\<close> using la2_bools H ss(2) by blast
      have l: \<open>length bs = length ks\<close> \<open>ks \<noteq> []\<close> using xs assms(3,4) ss(1) by auto
      have t: \<open>\<forall>i < length ks. wt ws ?dw (tref (ks ! i)) \<and> width ws ?dw (tref (ks ! i)) = 1 \<and>
          eval ws ?dw vs ?dv (tref (ks ! i)) = of_bool (bs ! i)\<close>
      proof (intro allI impI)
        fix i assume i: \<open>i < length ks\<close>
        then have \<open>ss ! i \<in> set ss\<close> using assms(3) by simp
        then have \<open>ss ! i = SmtSort_Bool\<close> using ss(2) by blast
        moreover have \<open>xs ! i = VBool (bs ! i)\<close> using i xs l by simp
        ultimately show \<open>wt ws ?dw (tref (ks ! i)) \<and> width ws ?dw (tref (ks ! i)) = 1 \<and>
            eval ws ?dw vs ?dv (tref (ks ! i)) = of_bool (bs ! i)\<close> using T[of i] i assms(3) by simp
      qed
      have bs: \<open>bs = hd bs # tl bs\<close> using l by (cases bs) auto
      have sb: \<open>set bs = insert (hd bs) (set (tl bs))\<close> using bs by (metis list.simps(15))
      have fb: \<open>filter id bs = filter id (hd bs # tl bs)\<close> using bs by metis
      have r: \<open>foldl (\<lambda>a b. Bit_Operations.and a (of_bool b)) (of_bool (hd bs)) (tl bs) = (of_bool (\<forall>b \<in> set bs. b) :: nat)\<close>
        unfolding sb ball_simps by (rule fold_and_bool)
      show ?thesis
        using bool_fold_eval[OF _ l(2) l(1)[symmetric] t, of Op_And] r ss(3) xs SmtOp_And bs
        by (auto simp: fold_left_m_def width_pres_def)
    next
      case SmtOp_Or
      then have ss: \<open>2 \<le> length ss\<close> \<open>set ss \<subseteq> {SmtSort_Bool}\<close> \<open>s = SmtSort_Bool\<close>
        using assms(1) by (auto split: if_splits)
      obtain bs where xs: \<open>xs = map VBool bs\<close> using la2_bools H ss(2) by blast
      have l: \<open>length bs = length ks\<close> \<open>ks \<noteq> []\<close> using xs assms(3,4) ss(1) by auto
      have t: \<open>\<forall>i < length ks. wt ws ?dw (tref (ks ! i)) \<and> width ws ?dw (tref (ks ! i)) = 1 \<and>
          eval ws ?dw vs ?dv (tref (ks ! i)) = of_bool (bs ! i)\<close>
      proof (intro allI impI)
        fix i assume i: \<open>i < length ks\<close>
        then have \<open>ss ! i \<in> set ss\<close> using assms(3) by simp
        then have \<open>ss ! i = SmtSort_Bool\<close> using ss(2) by blast
        moreover have \<open>xs ! i = VBool (bs ! i)\<close> using i xs l by simp
        ultimately show \<open>wt ws ?dw (tref (ks ! i)) \<and> width ws ?dw (tref (ks ! i)) = 1 \<and>
            eval ws ?dw vs ?dv (tref (ks ! i)) = of_bool (bs ! i)\<close> using T[of i] i assms(3) by simp
      qed
      have bs: \<open>bs = hd bs # tl bs\<close> using l by (cases bs) auto
      have sb: \<open>set bs = insert (hd bs) (set (tl bs))\<close> using bs by (metis list.simps(15))
      have fb: \<open>filter id bs = filter id (hd bs # tl bs)\<close> using bs by metis
      have r: \<open>foldl (\<lambda>a b. Bit_Operations.or a (of_bool b)) (of_bool (hd bs)) (tl bs) = (of_bool (\<exists>b \<in> set bs. b) :: nat)\<close>
        unfolding sb bex_simps by (rule fold_or_bool)
      show ?thesis
        using bool_fold_eval[OF _ l(2) l(1)[symmetric] t, of Op_Or] r ss(3) xs SmtOp_Or bs
        by (auto simp: fold_left_m_def width_pres_def)
    next
      case SmtOp_Xor
      then have ss: \<open>2 \<le> length ss\<close> \<open>set ss \<subseteq> {SmtSort_Bool}\<close> \<open>s = SmtSort_Bool\<close>
        using assms(1) by (auto split: if_splits)
      obtain bs where xs: \<open>xs = map VBool bs\<close> using la2_bools H ss(2) by blast
      have l: \<open>length bs = length ks\<close> \<open>ks \<noteq> []\<close> using xs assms(3,4) ss(1) by auto
      have t: \<open>\<forall>i < length ks. wt ws ?dw (tref (ks ! i)) \<and> width ws ?dw (tref (ks ! i)) = 1 \<and>
          eval ws ?dw vs ?dv (tref (ks ! i)) = of_bool (bs ! i)\<close>
      proof (intro allI impI)
        fix i assume i: \<open>i < length ks\<close>
        then have \<open>ss ! i \<in> set ss\<close> using assms(3) by simp
        then have \<open>ss ! i = SmtSort_Bool\<close> using ss(2) by blast
        moreover have \<open>xs ! i = VBool (bs ! i)\<close> using i xs l by simp
        ultimately show \<open>wt ws ?dw (tref (ks ! i)) \<and> width ws ?dw (tref (ks ! i)) = 1 \<and>
            eval ws ?dw vs ?dv (tref (ks ! i)) = of_bool (bs ! i)\<close> using T[of i] i assms(3) by simp
      qed
      have bs: \<open>bs = hd bs # tl bs\<close> using l by (cases bs) auto
      have sb: \<open>set bs = insert (hd bs) (set (tl bs))\<close> using bs by (metis list.simps(15))
      have fb: \<open>filter id bs = filter id (hd bs # tl bs)\<close> using bs by metis
      have r: \<open>foldl (\<lambda>a b. Bit_Operations.xor a (of_bool b)) (of_bool (hd bs)) (tl bs) = (of_bool (odd (length (filter id bs))) :: nat)\<close>
        unfolding fb by (rule fold_xor_bool)
      show ?thesis
        using bool_fold_eval[OF _ l(2) l(1)[symmetric] t, of Op_Xor] r ss(3) xs SmtOp_Xor
        by (simp add: fold_left_m_def width_pres_def smt_true_VBool)
    next
      case SmtOp_Implies
      then have ss: \<open>2 \<le> length ss\<close> \<open>set ss \<subseteq> {SmtSort_Bool}\<close> \<open>s = SmtSort_Bool\<close>
        using assms(1) by (auto split: if_splits)
      obtain bs where xs: \<open>xs = map VBool bs\<close> using la2_bools H ss(2) by blast
      have l: \<open>length bs = length ks\<close> \<open>ks \<noteq> []\<close> using xs assms(3,4) ss(1) by auto
      have t: \<open>\<forall>i < length ks. wt ws ?dw (tref (ks ! i)) \<and> width ws ?dw (tref (ks ! i)) = 1 \<and>
          eval ws ?dw vs ?dv (tref (ks ! i)) = of_bool (bs ! i)\<close>
      proof (intro allI impI)
        fix i assume i: \<open>i < length ks\<close>
        then have \<open>ss ! i \<in> set ss\<close> using assms(3) by simp
        then have \<open>ss ! i = SmtSort_Bool\<close> using ss(2) by blast
        moreover have \<open>xs ! i = VBool (bs ! i)\<close> using i xs l by simp
        ultimately show \<open>wt ws ?dw (tref (ks ! i)) \<and> width ws ?dw (tref (ks ! i)) = 1 \<and>
            eval ws ?dw vs ?dv (tref (ks ! i)) = of_bool (bs ! i)\<close> using T[of i] i assms(3) by simp
      qed
      have K: \<open>\<forall>k \<in> set ks. wt ws ?dw (tref k) \<and> width ws ?dw (tref k) = 1 \<and> eval ws ?dw vs ?dv (tref k) \<in> {0, 1}\<close>
        using t by (auto simp: in_set_conv_nth)
      have E: \<open>map (\<lambda>k. eval ws ?dw vs ?dv (tref k)) ks = map of_bool bs\<close> using t l by (auto intro!: nth_equalityI)
      have Eb: \<open>map (\<lambda>k. eval ws ?dw vs ?dv (tref k)) (butlast ks) = map of_bool (butlast bs)\<close> using E by (metis map_butlast)
      have c1: \<open>(\<exists>k \<in> set (butlast ks). eval ws ?dw vs ?dv (tref k) = 0) = (\<exists>b \<in> set (butlast bs). \<not> b)\<close>
        using ex_zero_map[OF Eb] .
      have c2: \<open>eval ws ?dw vs ?dv (tref (last ks)) = of_bool (last bs)\<close>
        using E l by (metis last_map list.map_disc_iff)
      have bs0: \<open>bs \<noteq> []\<close> using l by auto
      show ?thesis using implies_eval[OF l(2) K] c1 c2 ss(3) xs SmtOp_Implies bs0
        by (simp add: map_butlast[symmetric] last_map)
    next
      case SmtOp_Eq
      then have ss: \<open>2 \<le> length ss\<close> \<open>set ss \<subseteq> {hd ss}\<close> \<open>s = SmtSort_Bool\<close>
        using assms(1) by (auto split: if_splits)
      define s0 where \<open>s0 = hd ss\<close>
      have s00: \<open>s0 \<in> set ss\<close> using ss(1) unfolding s0_def by (cases ss) auto
      have fs0: \<open>frag_sort s0\<close> using assms(2) s00 by blast
      have all: \<open>ss ! i = s0\<close> if \<open>i < length ss\<close> for i using ss(2) that nth_mem[OF that] unfolding s0_def by blast
      have t: \<open>wt ws ?dw (tref (ks ! i)) \<and> width ws ?dw (tref (ks ! i)) = sort_width_m s0 \<and>
          eval ws ?dw vs ?dv (tref (ks ! i)) = enc (xs ! i)\<close> if \<open>i < length ks\<close> for i
        using T[of i] all[of i] that assms(3) by simp
      have hs: \<open>smt_has_sort s0 (xs ! i)\<close> if \<open>i < length xs\<close> for i
        using H all[of i] that assms(4) by (auto simp: list_all2_conv_all_nth)
      have K: \<open>\<forall>k \<in> set ks. wt ws ?dw (tref k) \<and> width ws ?dw (tref k) = sort_width_m s0\<close>
        using t by (auto simp: in_set_conv_nth)
      have ev: \<open>(eval ws ?dw vs ?dv (tref (ks ! i)) = eval ws ?dw vs ?dv (tref (ks ! j))) = (xs ! i = xs ! j)\<close>
        if \<open>i < length ks\<close> \<open>j < length ks\<close> for i j
        using t[OF that(1)] t[OF that(2)] enc_inj[OF hs hs fs0] that assms(3,4) by simp
      have c: \<open>(\<forall>i. Suc i < length ks \<longrightarrow> eval ws ?dw vs ?dv (tref (ks ! i)) = eval ws ?dw vs ?dv (tref (ks ! Suc i))) =
          (\<forall>i. Suc i < length xs \<longrightarrow> xs ! i = xs ! Suc i)\<close>
        using ev assms(3,4) by (metis Suc_lessD)
      show ?thesis using chain_eval[OF _ K] c ss SmtOp_Eq assms(3) by simp
    next
      case SmtOp_Distinct
      then have ss: \<open>2 \<le> length ss\<close> \<open>set ss \<subseteq> {hd ss}\<close> \<open>s = SmtSort_Bool\<close>
        using assms(1) by (auto split: if_splits)
      define s0 where \<open>s0 = hd ss\<close>
      have s00: \<open>s0 \<in> set ss\<close> using ss(1) unfolding s0_def by (cases ss) auto
      have fs0: \<open>frag_sort s0\<close> using assms(2) s00 by blast
      have all: \<open>ss ! i = s0\<close> if \<open>i < length ss\<close> for i using ss(2) that nth_mem[OF that] unfolding s0_def by blast
      have t: \<open>wt ws ?dw (tref (ks ! i)) \<and> width ws ?dw (tref (ks ! i)) = sort_width_m s0 \<and>
          eval ws ?dw vs ?dv (tref (ks ! i)) = enc (xs ! i)\<close> if \<open>i < length ks\<close> for i
        using T[of i] all[of i] that assms(3) by simp
      have hs: \<open>smt_has_sort s0 (xs ! i)\<close> if \<open>i < length xs\<close> for i
        using H all[of i] that assms(4) by (auto simp: list_all2_conv_all_nth)
      have K: \<open>\<forall>k \<in> set ks. wt ws ?dw (tref k) \<and> width ws ?dw (tref k) = sort_width_m s0\<close>
        using t by (auto simp: in_set_conv_nth)
      have ev: \<open>(eval ws ?dw vs ?dv (tref (ks ! i)) = eval ws ?dw vs ?dv (tref (ks ! j))) = (xs ! i = xs ! j)\<close>
        if \<open>i < length ks\<close> \<open>j < length ks\<close> for i j
        using t[OF that(1)] t[OF that(2)] enc_inj[OF hs hs fs0] that assms(3,4) by simp
      have c: \<open>(\<forall>i j. i < j \<and> j < length ks \<longrightarrow> eval ws ?dw vs ?dv (tref (ks ! i)) \<noteq> eval ws ?dw vs ?dv (tref (ks ! j))) =
          distinct xs\<close>
      proof -
        have \<open>(eval ws ?dw vs ?dv (tref (ks ! i)) \<noteq> eval ws ?dw vs ?dv (tref (ks ! j))) = (xs ! i \<noteq> xs ! j)\<close>
          if \<open>i < j\<close> \<open>j < length ks\<close> for i j using ev that by simp
        then show ?thesis unfolding distinct_lt using assms(3,4) by metis
      qed
      show ?thesis using pairwise_eval[OF _ K] c ss SmtOp_Distinct assms(3) by simp
    next
      case SmtOp_Ite
      then obtain s' where ss: \<open>ss = [SmtSort_Bool, s', s']\<close> \<open>s = s'\<close>
        using assms(1) by (auto split: list.splits if_splits)
      have fs: \<open>frag_sort s'\<close> using assms(2) ss by auto
      obtain c x y where xs: \<open>xs = [VBool c, x, y]\<close> \<open>smt_has_sort s' x\<close> \<open>smt_has_sort s' y\<close>
        using la2_ite H ss(1) by blast
      have t: \<open>wt ws ?dw (tref (ks ! 0))\<close> \<open>width ws ?dw (tref (ks ! 0)) = 1\<close> \<open>eval ws ?dw vs ?dv (tref (ks ! 0)) = of_bool c\<close>
        \<open>wt ws ?dw (tref (ks ! 1))\<close> \<open>width ws ?dw (tref (ks ! 1)) = sort_width_m s'\<close> \<open>eval ws ?dw vs ?dv (tref (ks ! 1)) = enc x\<close>
        \<open>wt ws ?dw (tref (ks ! 2))\<close> \<open>width ws ?dw (tref (ks ! 2)) = sort_width_m s'\<close> \<open>eval ws ?dw vs ?dv (tref (ks ! 2)) = enc y\<close>
        using T[of 0] T[of 1] T[of 2] ss xs by auto
      show ?thesis using t ss xs SmtOp_Ite by (cases c) auto
    qed (use False in simp_all)
  qed
qed

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

lemma ref_ok_ext: \<open>ref_ok ws vs S k s v \<Longrightarrow> ref_ok ws vs (S @ E) k s v\<close>
proof -
  assume r: \<open>ref_ok ws vs S k s v\<close>
  obtain e where e: \<open>def_widths ws [] (S @ E) = def_widths ws [] S @ e\<close>
    using def_widths_append'[of ws \<open>[]\<close> S E] def_widths_prefix'[of ws \<open>def_widths ws [] S\<close> E] by auto
  obtain f where f: \<open>def_values ws [] vs [] (S @ E) = def_values ws [] vs [] S @ f\<close>
    using def_values_append'[of ws \<open>[]\<close> vs \<open>[]\<close> S E] def_values_prefix'[of ws _ vs \<open>def_values ws [] vs [] S\<close> E] by auto
  have \<open>k < length (def_widths ws [] S)\<close> \<open>k < length (def_values ws [] vs [] S)\<close>
    using r by (simp_all add: ref_ok_def def_widths_length' def_values_length')
  then show ?thesis using r e f by (auto simp: ref_ok_def nth_append)
qed

lemma def_snoc:
  \<open>def_widths ws [] (S @ [t]) ! length S = width ws (def_widths ws [] S) t\<close>
  \<open>def_values ws [] vs [] (S @ [t]) ! length S = eval ws (def_widths ws [] S) vs (def_values ws [] vs [] S) t\<close>
  \<open>defs_wt ws [] (S @ [t]) = (defs_wt ws [] S \<and> wt ws (def_widths ws [] S) t)\<close>
  by (simp_all add: def_widths_append' def_values_append' defs_wt_append' nth_append def_widths_length' def_values_length')

lemma smt_def_sems_snoc:
  \<open>smt_def_sems I (ds @ [d]) = smt_def_sems I ds @ [\<lambda>vs. smt_eval I (smt_def_sems I ds) vs (SmtDef_body d)]\<close>
  by (simp add: smt_def_sems_def)

lemma smt_def_sems_length: \<open>length (smt_def_sems I ds) = length ds\<close>
  by (induction ds rule: rev_induct) (simp_all add: smt_def_sems_snoc, simp add: smt_def_sems_def)

lemma smt_def_sems_nth:
  \<open>d < length ds \<Longrightarrow> smt_def_sems I ds ! d = (\<lambda>vs. smt_eval I (take d (smt_def_sems I ds)) vs (SmtDef_body (ds ! d)))\<close>
proof (induction ds rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x ds)
  show ?case
  proof (cases \<open>d < length ds\<close>)
    case True
    then show ?thesis using snoc.IH by (simp add: smt_def_sems_snoc nth_append smt_def_sems_length)
  next
    case False
    then have \<open>d = length ds\<close> using snoc.prems by simp
    then show ?thesis by (simp add: smt_def_sems_snoc nth_append smt_def_sems_length)
  qed
qed

lemma map_Some_ex: \<open>map g args = map Some L \<Longrightarrow> a \<in> set args \<Longrightarrow> \<exists>y. g a = Some y\<close>
  by (induction args arbitrary: L) auto

lemma smt_eval_take:
  \<open>smt_tsort fs (take d ds) ps t \<noteq> None \<Longrightarrow> length dv = length ds \<Longrightarrow>
     smt_eval I (take d dv) xs t = smt_eval I dv xs t\<close>
proof (induction t)
  case (SmtTerm_Fun f args)
  have \<open>\<forall>a \<in> set args. \<exists>y. smt_tsort fs (take d ds) ps a = Some y\<close>
    using SmtTerm_Fun.prems(1) by (auto split: if_splits intro: map_Some_ex)
  then have e: \<open>\<forall>a \<in> set args. smt_eval I (take d dv) xs a = smt_eval I dv xs a\<close>
    using SmtTerm_Fun.IH SmtTerm_Fun.prems(2) by blast
  have \<open>map (smt_eval I (take d dv) xs) args = map (smt_eval I dv xs) args\<close> using e by (intro map_cong) auto
  then show ?case by (metis smt_eval.simps(4))
next
  case (SmtTerm_Def d' args)
  have \<open>\<forall>a \<in> set args. \<exists>y. smt_tsort fs (take d ds) ps a = Some y\<close> and u: \<open>unat d' < length (take d ds)\<close>
    using SmtTerm_Def.prems(1) by (auto split: if_splits intro: map_Some_ex)
  then have e: \<open>\<forall>a \<in> set args. smt_eval I (take d dv) xs a = smt_eval I dv xs a\<close>
    using SmtTerm_Def.IH SmtTerm_Def.prems(2) by blast
  have \<open>map (smt_eval I (take d dv) xs) args = map (smt_eval I dv xs) args\<close> using e by (intro map_cong) auto
  moreover have \<open>take d dv ! unat d' = dv ! unat d'\<close> using u SmtTerm_Def.prems(2) by simp
  ultimately show ?case by (metis smt_eval.simps(5))
next
  case (SmtTerm_App op args)
  have \<open>\<forall>a \<in> set args. \<exists>y. smt_tsort fs (take d ds) ps a = Some y\<close>
    using SmtTerm_App.prems(1) by (auto split: if_splits) (metis image_eqI option.exhaust)
  then have e: \<open>\<forall>a \<in> set args. smt_eval I (take d dv) xs a = smt_eval I dv xs a\<close>
    using SmtTerm_App.IH SmtTerm_App.prems(2) by blast
  have \<open>map (smt_eval I (take d dv) xs) args = map (smt_eval I dv xs) args\<close> using e by (intro map_cong) auto
  then show ?case by (metis smt_eval.simps(6))
qed auto

lemma frag_of_wf: \<open>smt_fragment p \<Longrightarrow> smt_wf_sort (unat (SmtProblem_num_sorts p)) s \<Longrightarrow> frag_sort s\<close>
  by (cases s) (auto simp: smt_fragment_def)

lemma defs_sound_sems:
  assumes \<open>\<forall>d < length ds. smt_tsort fs (take d ds) (SmtDef_params (ds ! d)) (SmtDef_body (ds ! d)) = Some (SmtDef_ret (ds ! d))\<close>
    \<open>\<forall>d \<in> set ds. smt_wf_sort ns (SmtDef_ret d) \<and> (\<forall>x \<in> set (SmtDef_params d). smt_wf_sort ns x)\<close>
    \<open>\<forall>f \<in> set fs. \<forall>x \<in> set (SmtFun_args f). smt_wf_sort ns x\<close>
    \<open>\<forall>f \<in> set fs. smt_wf_sort ns (SmtFun_ret f)\<close> \<open>interp_sound fs I\<close>
  shows \<open>defs_sound fs ds (smt_def_sems I ds)\<close>
  using assms(1,2)
proof (induction ds rule: rev_induct)
  case Nil
  then show ?case by (simp add: defs_sound_def smt_def_sems_def)
next
  case (snoc x ds)
  have p: \<open>\<forall>d < length ds. smt_tsort fs (take d ds) (SmtDef_params (ds ! d)) (SmtDef_body (ds ! d)) = Some (SmtDef_ret (ds ! d))\<close>
  proof (intro allI impI)
    fix d assume d: \<open>d < length ds\<close>
    then have \<open>take d (ds @ [x]) = take d ds\<close> \<open>(ds @ [x]) ! d = ds ! d\<close> by (simp_all add: nth_append)
    then show \<open>smt_tsort fs (take d ds) (SmtDef_params (ds ! d)) (SmtDef_body (ds ! d)) = Some (SmtDef_ret (ds ! d))\<close>
      using snoc.prems(1)[rule_format, of d] d by simp
  qed
  have ih: \<open>defs_sound fs ds (smt_def_sems I ds)\<close> using snoc.IH p snoc.prems(2) by simp
  have x: \<open>smt_tsort fs ds (SmtDef_params x) (SmtDef_body x) = Some (SmtDef_ret x)\<close>
    using snoc.prems(1)[rule_format, of \<open>length ds\<close>] by simp
  have \<open>smt_has_sort (SmtDef_ret x) (smt_eval I (smt_def_sems I ds) xs (SmtDef_body x))\<close>
    if \<open>list_all2 smt_has_sort (SmtDef_params x) xs\<close> for xs
    using smt_eval_sort[OF x assms(5) ih that, of ns] snoc.prems(2) assms(3,4) by simp
  then show ?case using ih
    by (auto simp: defs_sound_def smt_def_sems_snoc nth_append smt_def_sems_length less_Suc_eq)
qed

lemma tr_prefix:
  shows \<open>tr_term_m p dm env n S t = (S', t') \<Longrightarrow> \<exists>E. S' = S @ E\<close>
    and \<open>tr_args_m p dm env n S ts = (S', ks) \<Longrightarrow> \<exists>E. S' = S @ E \<and> length ks = length ts\<close>
proof (induction p dm env n S t and p dm env n S ts arbitrary: S' t' and S' ks rule: tr_term_m_tr_args_m.induct)
  case (5 p dm env n S d args)
  then show ?case by (auto simp: Let_def split: if_splits prod.splits) (metis append.assoc prod.collapse)
next
  case (6 p dm env n S op args)
  then show ?case by (auto simp: Let_def split: prod.splits) (metis prod.collapse)
next
  case (8 p dm env n S a rest)
  obtain S1 t1 where r1: \<open>tr_term_m p dm env n S a = (S1, t1)\<close> by (cases \<open>tr_term_m p dm env n S a\<close>)
  obtain S2 ks2 where r2: \<open>tr_args_m p dm env n (S1 @ [t1]) rest = (S2, ks2)\<close>
    by (cases \<open>tr_args_m p dm env n (S1 @ [t1]) rest\<close>)
  have \<open>\<exists>E. S1 = S @ E\<close> using 8(1) r1 by blast
  moreover have \<open>\<exists>E. S2 = (S1 @ [t1]) @ E \<and> length ks2 = length rest\<close> using 8(2)[OF r1[symmetric]] r1 r2 by simp
  ultimately show ?case using 8(3) r1 r2 by (auto simp: Let_def)
qed auto

lemma ctx_ok_ext: \<open>ctx_ok p I ws vs n dm S \<Longrightarrow> ctx_ok p I ws vs n dm (S @ E)\<close>
  by (auto simp: ctx_ok_def Let_def intro: ref_ok_ext)

lemma ctx_ok_mono: \<open>ctx_ok p I ws vs n dm S \<Longrightarrow> m \<le> n \<Longrightarrow> ctx_ok p I ws vs m dm S\<close>
  by (auto simp: ctx_ok_def Let_def)

lemma ctx_ok_wf_sorts:
  assumes \<open>ctx_ok p I ws vs n dm S\<close>
  shows \<open>\<forall>f \<in> set (SmtProblem_funs p). (\<forall>x \<in> set (SmtFun_args f). smt_wf_sort (unat (SmtProblem_num_sorts p)) x) \<and>
           smt_wf_sort (unat (SmtProblem_num_sorts p)) (SmtFun_ret f)\<close>
    and \<open>\<forall>d \<in> set (SmtProblem_defs p). smt_wf_sort (unat (SmtProblem_num_sorts p)) (SmtDef_ret d) \<and>
           (\<forall>x \<in> set (SmtDef_params d). smt_wf_sort (unat (SmtProblem_num_sorts p)) x)\<close>
    and \<open>\<forall>d < length (SmtProblem_defs p). smt_tsort (SmtProblem_funs p) (take d (SmtProblem_defs p))
           (SmtDef_params (SmtProblem_defs p ! d)) (SmtDef_body (SmtProblem_defs p ! d)) = Some (SmtDef_ret (SmtProblem_defs p ! d))\<close>
proof -
  from assms have w: \<open>smt_wf p\<close> by (simp add: ctx_ok_def Let_def)
  then show \<open>\<forall>f \<in> set (SmtProblem_funs p). (\<forall>x \<in> set (SmtFun_args f). smt_wf_sort (unat (SmtProblem_num_sorts p)) x) \<and>
           smt_wf_sort (unat (SmtProblem_num_sorts p)) (SmtFun_ret f)\<close> by (simp add: smt_wf_def Let_def)
  from w have \<open>\<forall>d < length (SmtProblem_defs p). smt_wf_sort (unat (SmtProblem_num_sorts p)) (SmtDef_ret (SmtProblem_defs p ! d)) \<and>
           (\<forall>x \<in> set (SmtDef_params (SmtProblem_defs p ! d)). smt_wf_sort (unat (SmtProblem_num_sorts p)) x)\<close>
    by (simp add: smt_wf_def Let_def)
  then show \<open>\<forall>d \<in> set (SmtProblem_defs p). smt_wf_sort (unat (SmtProblem_num_sorts p)) (SmtDef_ret d) \<and>
           (\<forall>x \<in> set (SmtDef_params d). smt_wf_sort (unat (SmtProblem_num_sorts p)) x)\<close>
    by (metis in_set_conv_nth)
  from w show \<open>\<forall>d < length (SmtProblem_defs p). smt_tsort (SmtProblem_funs p) (take d (SmtProblem_defs p))
           (SmtDef_params (SmtProblem_defs p ! d)) (SmtDef_body (SmtProblem_defs p ! d)) = Some (SmtDef_ret (SmtProblem_defs p ! d))\<close>
    by (simp add: smt_wf_def Let_def)
qed

lemma defs_sound_take: \<open>defs_sound fs ds dv \<Longrightarrow> defs_sound fs (take n ds) (take n dv)\<close>
  by (auto simp: defs_sound_def)

lemma val_sort:
  assumes \<open>ctx_ok p I ws vs n dm S\<close> \<open>smt_tsort (SmtProblem_funs p) (take n (SmtProblem_defs p)) ps t = Some s\<close>
    \<open>\<forall>x \<in> set ps. smt_wf_sort (unat (SmtProblem_num_sorts p)) x\<close> \<open>list_all2 smt_has_sort ps xs\<close>
  shows \<open>smt_has_sort s (smt_eval I (smt_def_sems I (SmtProblem_defs p)) xs t)\<close>
proof -
  let ?fs = \<open>SmtProblem_funs p\<close> and ?ds = \<open>SmtProblem_defs p\<close> and ?ns = \<open>unat (SmtProblem_num_sorts p)\<close>
  note w = ctx_ok_wf_sorts[OF assms(1)]
  have isd: \<open>interp_sound ?fs I\<close> using assms(1) by (simp add: ctx_ok_def Let_def)
  have ds: \<open>defs_sound ?fs ?ds (smt_def_sems I ?ds)\<close>
    using defs_sound_sems[OF w(3), of ?ns] w(1,2) isd by auto
  have \<open>smt_has_sort s (smt_eval I (take n (smt_def_sems I ?ds)) xs t)\<close>
    using smt_eval_sort[OF assms(2) isd defs_sound_take[OF ds] assms(4) assms(3)] w(1,2)
      set_take_subset[of n ?ds] by blast
  then show ?thesis using smt_eval_take[of ?fs n ?ds ps t \<open>smt_def_sems I ?ds\<close> I xs] assms(2)
    by (simp add: smt_def_sems_length)
qed

lemma wf_of_frag: \<open>frag_sort s \<Longrightarrow> smt_wf_sort ns s\<close>
  by (cases s) auto

lemma la2_of_refs:
  \<open>length xs = length ps \<Longrightarrow> \<forall>i < length ps. ref_ok ws vs S (env ! i) (ps ! i) (xs ! i) \<Longrightarrow> list_all2 smt_has_sort ps xs\<close>
  by (auto simp: list_all2_conv_all_nth ref_ok_def)

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
proof (induction p dm env n S t and p dm env n S ts arbitrary: S' t' ps s xs and S' ks ps ss xs
    rule: tr_term_m_tr_args_m.induct)
  case (1 p dm env n S b S' t' ps s xs)
  then show ?case by auto
next
  case (2 p dm env n S bs S' t' ps s xs)
  then show ?case by (auto simp: unat_of_nat_eq helper_defs_eq split: if_splits)
next
  case (3 p dm env n S k S' t' ps s xs)
  then have k: \<open>unat k < length ps\<close> \<open>s = ps ! unat k\<close> by (auto split: if_splits)
  then have \<open>frag_sort (ps ! unat k)\<close> using 3 by simp
  then show ?case using 3 k tref_ok[OF 3(7)[rule_format, OF k(1)]] by auto
next
  case (4 p dm env n S i args S' t' ps s xs)
  let ?fs = \<open>SmtProblem_funs p\<close>
  have i: \<open>unat i < length ?fs\<close> \<open>map (smt_tsort ?fs (take n (SmtProblem_defs p)) ps) args = map Some (SmtFun_args (?fs ! unat i))\<close>
    \<open>s = SmtFun_ret (?fs ! unat i)\<close> using 4(3) by (auto split: if_splits)
  have fr: \<open>smt_fragment p\<close> \<open>ws = map (\<lambda>f. sort_width_m (SmtFun_ret f)) ?fs\<close> \<open>length vs = length ?fs\<close>
    \<open>vs ! unat i = enc (I (unat i) [])\<close> using 4(2) i(1) by (auto simp: ctx_ok_def Let_def)
  have na: \<open>SmtFun_args (?fs ! unat i) = []\<close> using fr(1) i(1) by (auto simp: smt_fragment_def)
  then have a: \<open>args = []\<close> using i(2) by simp
  have \<open>frag_sort s\<close> using frag_of_wf[OF fr(1)] ctx_ok_wf_sorts(1)[OF 4(2)] i(1,3) by (metis nth_mem)
  then show ?case using 4(1,8) i fr a sort_width_frag[of s] by auto
next
  case (5 p dm env n S d args S' t' ps s xs)
  let ?fs = \<open>SmtProblem_funs p\<close> and ?ds = \<open>SmtProblem_defs p\<close> and ?dv = \<open>smt_def_sems I (SmtProblem_defs p)\<close>
  have d: \<open>unat d < length (take n ?ds)\<close> \<open>map (smt_tsort ?fs (take n ?ds) ps) args = map Some (SmtDef_params (?ds ! unat d))\<close>
    \<open>s = SmtDef_ret (?ds ! unat d)\<close> using 5(5) by (auto split: if_splits)
  have dn: \<open>unat d < n\<close> \<open>unat d < length ?ds\<close> using d(1) by auto
  have fr: \<open>smt_fragment p\<close> using 5(4) by (simp add: ctx_ok_def Let_def)
  have wfr: \<open>frag_sort (SmtDef_ret (?ds ! unat d))\<close> \<open>\<forall>x \<in> set (SmtDef_params (?ds ! unat d)). frag_sort x\<close>
    using ctx_ok_wf_sorts(2)[OF 5(4)] frag_of_wf[OF fr] dn(2) by (meson nth_mem)+
  show ?case
  proof (cases \<open>SmtDef_params (?ds ! unat d) = []\<close>)
    case True
    then have a: \<open>args = []\<close> using d(2) by simp
    have res: \<open>S' = S\<close> \<open>t' = tref (dm ! unat d)\<close> using 5(3) True by auto
    have r: \<open>ref_ok ws vs S (dm ! unat d) (SmtDef_ret (?ds ! unat d)) ((?dv ! unat d) [])\<close>
      using 5(4) dn True unfolding ctx_ok_def Let_def by blast
    show ?thesis using tref_ok[OF r wfr(1)] res a d(3) 5(10) by simp
  next
    case False
    obtain S1 ks1 where r: \<open>tr_args_m p dm env n S args = (S1, ks1)\<close> by (cases \<open>tr_args_m p dm env n S args\<close>)
    have res: \<open>tr_term_m p dm ks1 (unat d) S1 (SmtDef_body (?ds ! unat d)) = (S', t')\<close>
      using 5(3) False dn(1) r by (simp add: Let_def)
    obtain E2 where E2: \<open>S' = S1 @ E2\<close> using tr_prefix(1)[OF res] by blast
    have len1: \<open>length S1 < 2 ^ 64\<close> using 5(11) E2 by simp
    let ?xs' = \<open>map (smt_eval I ?dv xs) args\<close>
    have A: \<open>(\<exists>E. S1 = S @ E) \<and> defs_wt ws [] S1 \<and> length ks1 = length args \<and>
        (\<forall>i < length args. ref_ok ws vs S1 (ks1 ! i) (SmtDef_params (?ds ! unat d) ! i) (smt_eval I ?dv xs (args ! i)))\<close>
      using 5(1)[OF False dn(1) r 5(4) d(2) 5(6,7,8,9,10) len1] .
    obtain E1 where E1: \<open>S1 = S @ E1\<close> using A by blast
    have la: \<open>length args = length (SmtDef_params (?ds ! unat d))\<close> using d(2) by (metis length_map)
    have ctx1: \<open>ctx_ok p I ws vs (unat d) dm S1\<close> using ctx_ok_mono[OF ctx_ok_ext[OF 5(4), of E1]] E1 dn(1) by simp
    have tb: \<open>smt_tsort ?fs (take (unat d) ?ds) (SmtDef_params (?ds ! unat d)) (SmtDef_body (?ds ! unat d)) = Some (SmtDef_ret (?ds ! unat d))\<close>
      using ctx_ok_wf_sorts(3)[OF 5(4)] dn(2) by blast
    have B: \<open>(\<exists>E. S' = S1 @ E) \<and> defs_wt ws [] S' \<and> wt ws (def_widths ws [] S') t' \<and>
        width ws (def_widths ws [] S') t' = sort_width_m (SmtDef_ret (?ds ! unat d)) \<and>
        eval ws (def_widths ws [] S') vs (def_values ws [] vs [] S') t' = enc (smt_eval I ?dv ?xs' (SmtDef_body (?ds ! unat d)))\<close>
      using 5(2)[of \<open>(S1, ks1)\<close> S' t' \<open>SmtDef_params (?ds ! unat d)\<close> \<open>SmtDef_ret (?ds ! unat d)\<close> ?xs'] False dn(1) r res ctx1 tb wfr(2)
        A la 5(11) by auto
    have v: \<open>smt_eval I ?dv xs (SmtTerm_Def d args) = smt_eval I ?dv ?xs' (SmtDef_body (?ds ! unat d))\<close>
      using smt_def_sems_nth[OF dn(2), of I] tb
        smt_eval_take[of ?fs \<open>unat d\<close> ?ds \<open>SmtDef_params (?ds ! unat d)\<close> \<open>SmtDef_body (?ds ! unat d)\<close> ?dv I ?xs']
      by (simp add: smt_def_sems_length)
    show ?thesis using B v d(3) E1 E2 by auto
  qed
next
  case (6 p dm env n S op args S' t' ps s xs)
  let ?fs = \<open>SmtProblem_funs p\<close> and ?ds = \<open>SmtProblem_defs p\<close> and ?dv = \<open>smt_def_sems I (SmtProblem_defs p)\<close>
  let ?ss = \<open>map (the \<circ> smt_tsort ?fs (take n ?ds) ps) args\<close>
  obtain S1 ks1 where r: \<open>tr_args_m p dm env n S args = (S1, ks1)\<close> by (cases \<open>tr_args_m p dm env n S args\<close>)
  have res: \<open>S' = S1\<close> \<open>t' = tr_app_m op ks1\<close> using 6(2) r by (auto simp: Let_def)
  have o: \<open>None \<notin> set (map (smt_tsort ?fs (take n ?ds) ps) args)\<close> \<open>smt_op_sort op ?ss = Some s\<close>
    using 6(4) by (auto split: if_splits)
  have m: \<open>map (smt_tsort ?fs (take n ?ds) ps) args = map Some ?ss\<close> using o(1) by (induction args) auto
  have A: \<open>(\<exists>E. S1 = S @ E) \<and> defs_wt ws [] S1 \<and> length ks1 = length args \<and>
      (\<forall>i < length args. ref_ok ws vs S1 (ks1 ! i) (?ss ! i) (smt_eval I ?dv xs (args ! i)))\<close>
    using 6(1)[OF r 6(3) m 6(5,6,7,8,9)] res 6(10) by simp
  have fr: \<open>smt_fragment p\<close> using 6(3) by (simp add: ctx_ok_def Let_def)
  note w = ctx_ok_wf_sorts[OF 6(3)]
  have frs: \<open>\<forall>x \<in> set ?ss. frag_sort x\<close>
  proof
    fix x assume \<open>x \<in> set ?ss\<close>
    then obtain a where a: \<open>a \<in> set args\<close> \<open>x = the (smt_tsort ?fs (take n ?ds) ps a)\<close> by auto
    then have \<open>smt_tsort ?fs (take n ?ds) ps a = Some x\<close> using o(1) by (metis image_eqI option.collapse set_map)
    then have \<open>smt_wf_sort (unat (SmtProblem_num_sorts p)) x\<close>
      using smt_tsort_wf[of ?fs \<open>take n ?ds\<close> ps a x] 6(5) wf_of_frag w(1,2) set_take_subset[of n ?ds] by blast
    then show \<open>frag_sort x\<close> using frag_of_wf[OF fr] by blast
  qed
  have C: \<open>wt ws (def_widths ws [] S1) (tr_app_m op ks1) \<and> width ws (def_widths ws [] S1) (tr_app_m op ks1) = sort_width_m s \<and>
      eval ws (def_widths ws [] S1) vs (def_values ws [] vs [] S1) (tr_app_m op ks1) =
        enc (smt_op_sem op (map (smt_eval I ?dv xs) args))\<close>
    using tr_app_correct[OF o(2) frs, of ks1 \<open>map (smt_eval I ?dv xs) args\<close> ws vs S1] A by simp
  show ?case using A C res by simp
next
  case (7 p dm env n S S' ks ps ss xs)
  then show ?case by auto
next
  case (8 p dm env n S a rest S' ks ps ss xs)
  obtain S1 t1 where r1: \<open>tr_term_m p dm env n S a = (S1, t1)\<close> by (cases \<open>tr_term_m p dm env n S a\<close>)
  obtain S2 ks2 where r2: \<open>tr_args_m p dm env n (S1 @ [t1]) rest = (S2, ks2)\<close>
    by (cases \<open>tr_args_m p dm env n (S1 @ [t1]) rest\<close>)
  have res: \<open>S' = S2\<close> \<open>ks = length S1 # ks2\<close> using 8(3) r1 r2 by (auto simp: Let_def)
  obtain s0 ss' where ss: \<open>ss = s0 # ss'\<close> \<open>smt_tsort (SmtProblem_funs p) (take n (SmtProblem_defs p)) ps a = Some s0\<close>
    \<open>map (smt_tsort (SmtProblem_funs p) (take n (SmtProblem_defs p)) ps) rest = map Some ss'\<close>
    using 8(5) by (cases ss) auto
  obtain E2 where E2: \<open>S2 = (S1 @ [t1]) @ E2\<close> using tr_prefix(2)[OF r2] by blast
  have len1: \<open>length S1 < 2 ^ 64\<close> using 8(11) res E2 by simp
  have A: \<open>(\<exists>E. S1 = S @ E) \<and> defs_wt ws [] S1 \<and> wt ws (def_widths ws [] S1) t1 \<and>
      width ws (def_widths ws [] S1) t1 = sort_width_m s0 \<and>
      eval ws (def_widths ws [] S1) vs (def_values ws [] vs [] S1) t1 =
        enc (smt_eval I (smt_def_sems I (SmtProblem_defs p)) xs a)\<close>
    using 8(1)[OF r1 8(4) ss(2) 8(6,7,8,9,10) len1] .
  have hs: \<open>smt_has_sort s0 (smt_eval I (smt_def_sems I (SmtProblem_defs p)) xs a)\<close>
    using val_sort[OF 8(4) ss(2)] 8(6) la2_of_refs[OF 8(8,9)] wf_of_frag by blast
  have refa: \<open>ref_ok ws vs (S1 @ [t1]) (length S1) s0 (smt_eval I (smt_def_sems I (SmtProblem_defs p)) xs a)\<close>
    using A hs len1 by (simp add: ref_ok_def def_snoc)
  have dw1: \<open>defs_wt ws [] (S1 @ [t1])\<close> using A by (simp add: def_snoc)
  obtain E1 where E1: \<open>S1 = S @ E1\<close> using A by blast
  have ctx1: \<open>ctx_ok p I ws vs n dm (S1 @ [t1])\<close> using ctx_ok_ext[OF 8(4), of \<open>E1 @ [t1]\<close>] E1 by simp
  have env1: \<open>\<forall>i < length ps. ref_ok ws vs (S1 @ [t1]) (env ! i) (ps ! i) (xs ! i)\<close>
    using 8(9) ref_ok_ext[of ws vs S _ _ _ \<open>E1 @ [t1]\<close>] E1 by simp
  have B: \<open>(\<exists>E. S2 = (S1 @ [t1]) @ E) \<and> defs_wt ws [] S2 \<and> length ks2 = length rest \<and>
      (\<forall>i < length rest. ref_ok ws vs S2 (ks2 ! i) (ss' ! i)
        (smt_eval I (smt_def_sems I (SmtProblem_defs p)) xs (rest ! i)))\<close>
    using 8(2)[of \<open>(S1, t1)\<close> S2 ks2 ps ss' xs] r1 r2 ctx1 ss(3) 8(6,7,8) env1 dw1 res 8(11) by auto
  have r0: \<open>ref_ok ws vs S2 (length S1) s0 (smt_eval I (smt_def_sems I (SmtProblem_defs p)) xs a)\<close>
    using ref_ok_ext[OF refa, of E2] E2 by simp
  show ?case
  proof (intro conjI)
    show \<open>\<exists>E. S' = S @ E\<close> using res E1 E2 by simp
    show \<open>defs_wt ws [] S'\<close> using B res by simp
    show \<open>length ks = length (a # rest)\<close> using B res by simp
    show \<open>\<forall>i < length (a # rest). ref_ok ws vs S' (ks ! i) (ss ! i)
        (smt_eval I (smt_def_sems I (SmtProblem_defs p)) xs ((a # rest) ! i))\<close>
    proof (intro allI impI)
      fix i assume \<open>i < length (a # rest)\<close>
      then show \<open>ref_ok ws vs S' (ks ! i) (ss ! i) (smt_eval I (smt_def_sems I (SmtProblem_defs p)) xs ((a # rest) ! i))\<close>
        using r0 B res ss(1) by (cases i) auto
    qed
  qed
qed

subsection \<open>The translation of the definitions and of the assertions\<close>

definition tr_defs_step :: \<open>SmtProblem \<Rightarrow> Term list \<times> nat list \<Rightarrow> nat \<Rightarrow> Term list \<times> nat list\<close> where
  \<open>tr_defs_step p \<equiv> \<lambda>(S, dm) d.
     if SmtDef_params (SmtProblem_defs p ! d) = [] then
       (let r = tr_term_m p dm [] d S (SmtDef_body (SmtProblem_defs p ! d)) in (fst r @ [snd r], dm @ [length (fst r)]))
     else (S, dm @ [0])\<close>

lemma tr_defs_m_step: \<open>tr_defs_m p = foldl (tr_defs_step p) ([], []) [0..<length (SmtProblem_defs p)]\<close>
  by (simp add: tr_defs_m_def tr_defs_step_def)

lemma tr_defs_step_prefix: \<open>\<exists>E. fst (tr_defs_step p (S, dm) d) = S @ E\<close> \<open>length (snd (tr_defs_step p (S, dm) d)) = Suc (length dm)\<close>
proof -
  obtain S1 t1 where r: \<open>tr_term_m p dm [] d S (SmtDef_body (SmtProblem_defs p ! d)) = (S1, t1)\<close>
    by (cases \<open>tr_term_m p dm [] d S (SmtDef_body (SmtProblem_defs p ! d))\<close>)
  obtain E where \<open>S1 = S @ E\<close> using tr_prefix(1)[OF r] by blast
  then show \<open>\<exists>E. fst (tr_defs_step p (S, dm) d) = S @ E\<close> using r by (auto simp: tr_defs_step_def)
  show \<open>length (snd (tr_defs_step p (S, dm) d)) = Suc (length dm)\<close> by (simp add: tr_defs_step_def Let_def)
qed

lemma ctx_ok_Suc:
  assumes \<open>ctx_ok p I ws vs k dm S\<close> \<open>length dm = k\<close> \<open>k < length (SmtProblem_defs p)\<close> \<open>S' = S @ E\<close>
    \<open>SmtDef_params (SmtProblem_defs p ! k) = [] \<Longrightarrow>
       ref_ok ws vs S' x (SmtDef_ret (SmtProblem_defs p ! k)) ((smt_def_sems I (SmtProblem_defs p) ! k) [])\<close>
  shows \<open>ctx_ok p I ws vs (Suc k) (dm @ [x]) S'\<close>
  using assms unfolding ctx_ok_def Let_def
  by (auto simp: nth_append less_Suc_eq intro: ref_ok_ext)

lemma tr_defs_prefix:
  \<open>\<exists>E. fst (foldl (tr_defs_step p) (S, dm) ks) = S @ E\<close>
proof (induction ks arbitrary: S dm)
  case Nil
  then show ?case by simp
next
  case (Cons k ks)
  obtain S1 dm1 where r: \<open>tr_defs_step p (S, dm) k = (S1, dm1)\<close> by (cases \<open>tr_defs_step p (S, dm) k\<close>)
  obtain E1 where \<open>S1 = S @ E1\<close> using tr_defs_step_prefix(1)[of p S dm k] r by auto
  moreover obtain E2 where \<open>fst (foldl (tr_defs_step p) (S1, dm1) ks) = S1 @ E2\<close> using Cons.IH by blast
  ultimately show ?case using r by auto
qed

text \<open>After the first \<open>k\<close> definitions: the context of the translation for the definitions below
  \<open>k\<close> holds, the state is well-sorted, and there is an entry of \<open>dm\<close> for each definition.\<close>
lemma tr_defs_correct:
  assumes \<open>ctx_ok p I ws vs 0 [] []\<close> \<open>k \<le> length (SmtProblem_defs p)\<close>
    \<open>length (fst (tr_defs_m p)) < 2 ^ 64\<close>
  shows \<open>ctx_ok p I ws vs k (snd (foldl (tr_defs_step p) ([], []) [0..<k])) (fst (foldl (tr_defs_step p) ([], []) [0..<k])) \<and>
         defs_wt ws [] (fst (foldl (tr_defs_step p) ([], []) [0..<k])) \<and>
         length (snd (foldl (tr_defs_step p) ([], []) [0..<k])) = k\<close>
  using assms(2)
proof (induction k)
  case 0
  then show ?case using assms(1) by simp
next
  case (Suc k)
  let ?ds = \<open>SmtProblem_defs p\<close> and ?fs = \<open>SmtProblem_funs p\<close> and ?dv = \<open>smt_def_sems I (SmtProblem_defs p)\<close>
  obtain S dm where st: \<open>foldl (tr_defs_step p) ([], []) [0..<k] = (S, dm)\<close>
    by (cases \<open>foldl (tr_defs_step p) ([], []) [0..<k]\<close>)
  have kd: \<open>k < length ?ds\<close> using Suc.prems by simp
  have IH: \<open>ctx_ok p I ws vs k dm S\<close> \<open>defs_wt ws [] S\<close> \<open>length dm = k\<close> using Suc st kd by auto
  have un: \<open>foldl (tr_defs_step p) ([], []) [0..<Suc k] = tr_defs_step p (S, dm) k\<close> using st by simp
  have fin: \<open>\<exists>E. fst (tr_defs_m p) = fst (tr_defs_step p (S, dm) k) @ E\<close>
  proof -
    have \<open>[0..<length ?ds] = [0..<Suc k] @ [Suc k..<length ?ds]\<close> using kd by (metis Suc_leI le_add_diff_inverse upt_add_eq_append zero_le)
    then have \<open>tr_defs_m p = foldl (tr_defs_step p) (tr_defs_step p (S, dm) k) [Suc k..<length ?ds]\<close>
      using un by (simp add: tr_defs_m_step)
    then show ?thesis using tr_defs_prefix[of p \<open>fst (tr_defs_step p (S, dm) k)\<close> \<open>snd (tr_defs_step p (S, dm) k)\<close>] by simp
  qed
  show ?case
  proof (cases \<open>SmtDef_params (?ds ! k) = []\<close>)
    case True
    obtain S1 t1 where r: \<open>tr_term_m p dm [] k S (SmtDef_body (?ds ! k)) = (S1, t1)\<close>
      by (cases \<open>tr_term_m p dm [] k S (SmtDef_body (?ds ! k))\<close>)
    have stp: \<open>tr_defs_step p (S, dm) k = (S1 @ [t1], dm @ [length S1])\<close> using True r by (simp add: tr_defs_step_def)
    have len: \<open>length S1 < 2 ^ 64\<close> using fin stp assms(3) by auto
    have tb: \<open>smt_tsort ?fs (take k ?ds) [] (SmtDef_body (?ds ! k)) = Some (SmtDef_ret (?ds ! k))\<close>
      using ctx_ok_wf_sorts(3)[OF IH(1)] kd True by metis
    have A: \<open>(\<exists>E. S1 = S @ E) \<and> defs_wt ws [] S1 \<and> wt ws (def_widths ws [] S1) t1 \<and>
        width ws (def_widths ws [] S1) t1 = sort_width_m (SmtDef_ret (?ds ! k)) \<and>
        eval ws (def_widths ws [] S1) vs (def_values ws [] vs [] S1) t1 = enc (smt_eval I ?dv [] (SmtDef_body (?ds ! k)))\<close>
      using tr_term_args_correct(1)[OF r IH(1) tb, of \<open>[]\<close>] IH(2) len by simp
    have v: \<open>(?dv ! k) [] = smt_eval I ?dv [] (SmtDef_body (?ds ! k))\<close>
      using smt_def_sems_nth[OF kd, of I] tb smt_eval_take[of ?fs k ?ds \<open>[]\<close> \<open>SmtDef_body (?ds ! k)\<close> ?dv I \<open>[]\<close>]
      by (simp add: smt_def_sems_length)
    have hs: \<open>smt_has_sort (SmtDef_ret (?ds ! k)) ((?dv ! k) [])\<close> using val_sort[OF IH(1) tb] v by simp
    obtain E1 where E1: \<open>S1 = S @ E1\<close> using A by blast
    have refk: \<open>ref_ok ws vs (S1 @ [t1]) (length S1) (SmtDef_ret (?ds ! k)) ((?dv ! k) [])\<close>
      using A hs v len by (simp add: ref_ok_def def_snoc)
    have \<open>ctx_ok p I ws vs (Suc k) (dm @ [length S1]) (S1 @ [t1])\<close>
      using ctx_ok_Suc[OF IH(1) IH(3) kd, of \<open>S1 @ [t1]\<close> \<open>E1 @ [t1]\<close> \<open>length S1\<close>] E1 refk by simp
    then show ?thesis using un stp A IH(3) by (simp add: def_snoc)
  next
    case False
    have stp: \<open>tr_defs_step p (S, dm) k = (S, dm @ [0])\<close> using False by (simp add: tr_defs_step_def)
    have \<open>ctx_ok p I ws vs (Suc k) (dm @ [0]) S\<close> using ctx_ok_Suc[OF IH(1) IH(3) kd, of S \<open>[]\<close> 0] False by simp
    then show ?thesis using un stp IH by simp
  qed
qed

text \<open>Term \<open>t\<close> of the state \<open>S\<close> translates assertion \<open>a\<close>.\<close>
definition aok :: \<open>SmtProblem \<Rightarrow> (nat \<Rightarrow> sval list \<Rightarrow> sval) \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> Term list \<Rightarrow> Term \<Rightarrow> SmtTerm \<Rightarrow> bool\<close> where
  \<open>aok p I ws vs S t a \<equiv>
     wt ws (def_widths ws [] S) t \<and> width ws (def_widths ws [] S) t = 1 \<and>
     eval ws (def_widths ws [] S) vs (def_values ws [] vs [] S) t = enc (smt_eval I (smt_def_sems I (SmtProblem_defs p)) [] a)\<close>

lemma aok_ext: \<open>aok p I ws vs S t a \<Longrightarrow> aok p I ws vs (S @ E) t a\<close>
proof -
  assume h: \<open>aok p I ws vs S t a\<close>
  obtain e where e: \<open>def_widths ws [] (S @ E) = def_widths ws [] S @ e\<close>
    using def_widths_append'[of ws \<open>[]\<close> S E] def_widths_prefix'[of ws \<open>def_widths ws [] S\<close> E] by auto
  obtain f where f: \<open>def_values ws [] vs [] (S @ E) = def_values ws [] vs [] S @ f\<close>
    using def_values_append'[of ws \<open>[]\<close> vs \<open>[]\<close> S E] def_values_prefix'[of ws _ vs \<open>def_values ws [] vs [] S\<close> E] by auto
  have l: \<open>length (def_values ws [] vs [] S) = length (def_widths ws [] S)\<close> by (simp add: def_widths_length' def_values_length')
  show ?thesis using h wt_width_eval_append[OF _ l, of ws t e vs f] e f by (simp add: aok_def)
qed

definition tr_asserts_step :: \<open>SmtProblem \<Rightarrow> nat list \<Rightarrow> Term list \<times> Term list \<Rightarrow> SmtTerm \<Rightarrow> Term list \<times> Term list\<close> where
  \<open>tr_asserts_step p dm \<equiv> \<lambda>(S, ts) t. let r = tr_term_m p dm [] (length (SmtProblem_defs p)) S t in (fst r, ts @ [snd r])\<close>

lemma tr_asserts_m_step: \<open>tr_asserts_m p Sd = foldl (tr_asserts_step p (snd Sd)) (fst Sd, []) (SmtProblem_asserts p)\<close>
  by (simp add: tr_asserts_m_def tr_asserts_step_def)

lemma tr_prefix_asserts: \<open>foldl (tr_asserts_step p dm) (S, acc) ass = (S', acc') \<Longrightarrow> \<exists>E. S' = S @ E\<close>
proof (induction ass arbitrary: S acc)
  case Nil
  then show ?case by simp
next
  case (Cons a ass)
  obtain S1 t1 where r: \<open>tr_term_m p dm [] (length (SmtProblem_defs p)) S a = (S1, t1)\<close>
    by (cases \<open>tr_term_m p dm [] (length (SmtProblem_defs p)) S a\<close>)
  have \<open>foldl (tr_asserts_step p dm) (S1, acc @ [t1]) ass = (S', acc')\<close>
    using Cons.prems r by (simp add: tr_asserts_step_def)
  then obtain E2 where \<open>S' = S1 @ E2\<close> using Cons.IH by blast
  moreover obtain E1 where \<open>S1 = S @ E1\<close> using tr_prefix(1)[OF r] by blast
  ultimately show ?case by auto
qed

lemma tr_asserts_gen:
  assumes \<open>ctx_ok p I ws vs (length (SmtProblem_defs p)) dm S\<close> \<open>defs_wt ws [] S\<close>
    \<open>\<forall>a \<in> set ass. smt_tsort (SmtProblem_funs p) (SmtProblem_defs p) [] a = Some SmtSort_Bool\<close>
    \<open>foldl (tr_asserts_step p dm) (S, acc) ass = (S', acc')\<close> \<open>length S' < 2 ^ 64\<close>
  shows \<open>(\<exists>E. S' = S @ E) \<and> defs_wt ws [] S' \<and> (\<exists>new. acc' = acc @ new \<and> length new = length ass \<and>
           (\<forall>i < length ass. aok p I ws vs S' (new ! i) (ass ! i)))\<close>
  using assms
proof (induction ass arbitrary: S acc)
  case Nil
  then show ?case by simp
next
  case (Cons a ass)
  obtain S1 t1 where r: \<open>tr_term_m p dm [] (length (SmtProblem_defs p)) S a = (S1, t1)\<close>
    by (cases \<open>tr_term_m p dm [] (length (SmtProblem_defs p)) S a\<close>)
  have f: \<open>foldl (tr_asserts_step p dm) (S1, acc @ [t1]) ass = (S', acc')\<close>
    using Cons.prems(4) r by (simp add: tr_asserts_step_def)
  obtain E1 where E1: \<open>S1 = S @ E1\<close> using tr_prefix(1)[OF r] by blast
  have ta: \<open>smt_tsort (SmtProblem_funs p) (take (length (SmtProblem_defs p)) (SmtProblem_defs p)) [] a = Some SmtSort_Bool\<close>
    using Cons.prems(3) by simp
  have ctx1: \<open>ctx_ok p I ws vs (length (SmtProblem_defs p)) dm S1\<close> using ctx_ok_ext[OF Cons.prems(1)] E1 by simp
  have IH0: \<open>(\<exists>E. S' = S1 @ E) \<and> defs_wt ws [] S' \<and> (\<exists>new. acc' = (acc @ [t1]) @ new \<and> length new = length ass \<and>
           (\<forall>i < length ass. aok p I ws vs S' (new ! i) (ass ! i)))\<close>
    if \<open>defs_wt ws [] S1\<close> using Cons.IH[OF ctx1 that _ f Cons.prems(5)] Cons.prems(3) by simp
  obtain E2 where E2: \<open>S' = S1 @ E2\<close> using tr_prefix_asserts[OF f] by blast
  have len1: \<open>length S1 < 2 ^ 64\<close> using E2 Cons.prems(5) by simp
  have A: \<open>(\<exists>E. S1 = S @ E) \<and> defs_wt ws [] S1 \<and> wt ws (def_widths ws [] S1) t1 \<and>
      width ws (def_widths ws [] S1) t1 = sort_width_m SmtSort_Bool \<and>
      eval ws (def_widths ws [] S1) vs (def_values ws [] vs [] S1) t1 = enc (smt_eval I (smt_def_sems I (SmtProblem_defs p)) [] a)\<close>
    using tr_term_args_correct(1)[OF r Cons.prems(1) ta, of \<open>[]\<close>] Cons.prems(2) len1 by simp
  have a0: \<open>aok p I ws vs S' t1 a\<close> using aok_ext[of p I ws vs S1 t1 a E2] A E2 by (simp add: aok_def)
  obtain new where new: \<open>acc' = (acc @ [t1]) @ new\<close> \<open>length new = length ass\<close>
    \<open>\<forall>i < length ass. aok p I ws vs S' (new ! i) (ass ! i)\<close> \<open>defs_wt ws [] S'\<close> using IH0 A by blast
  show ?case
  proof (intro conjI exI)
    show \<open>S' = S @ (E1 @ E2)\<close> using E1 E2 by simp
    show \<open>defs_wt ws [] S'\<close> using new(4) .
    show \<open>acc' = acc @ (t1 # new)\<close> using new(1) by simp
    show \<open>length (t1 # new) = length (a # ass)\<close> using new(2) by simp
    show \<open>\<forall>i < length (a # ass). aok p I ws vs S' ((t1 # new) ! i) ((a # ass) ! i)\<close>
      using a0 new(3) by (auto simp: nth_Cons split: nat.splits)
  qed
qed

subsection \<open>The translated problem\<close>

lemma sort_width_lt: \<open>frag_sort s \<Longrightarrow> sort_width_m s < 2 ^ 64\<close>
  by (cases s) (auto intro: unat_lt2p[THEN less_le_trans])

text \<open>For an interpretation \<open>I\<close> of the constants and the values \<open>vs\<close> of the variables of the
  translation that agree, the translation is well-sorted and its assertions hold exactly when those
  of \<open>p\<close> hold under \<open>I\<close>.\<close>
lemma tr_problem_sem:
  assumes \<open>smt_wf p\<close> \<open>smt_fragment p\<close> \<open>interp_sound (SmtProblem_funs p) I\<close>
    \<open>length vs = length (SmtProblem_funs p)\<close> \<open>\<forall>f < length (SmtProblem_funs p). vs ! f = enc (I f [])\<close>
    \<open>length (fst (tr_asserts_m p (tr_defs_m p))) < 2 ^ 64\<close>
  shows \<open>problem_wt (tr_problem_m p) \<and>
    var_widths (tr_problem_m p) = map (\<lambda>f. sort_width_m (SmtFun_ret f)) (SmtProblem_funs p) \<and>
    ((\<forall>t \<in> set (Problem_asserts (tr_problem_m p)).
        eval (var_widths (tr_problem_m p)) (def_widths (var_widths (tr_problem_m p)) [] (Problem_defs (tr_problem_m p))) vs
          (def_values (var_widths (tr_problem_m p)) [] vs [] (Problem_defs (tr_problem_m p))) t = 1) =
     smt_satisfies p I)\<close>
proof -
  let ?fs = \<open>SmtProblem_funs p\<close> and ?ds = \<open>SmtProblem_defs p\<close>
  let ?ws = \<open>map (\<lambda>f. sort_width_m (SmtFun_ret f)) ?fs\<close>
  have frs: \<open>\<forall>f \<in> set ?fs. frag_sort (SmtFun_ret f)\<close>
    using assms(1,2) frag_of_wf by (auto simp: smt_wf_def Let_def)
  have vw: \<open>var_widths (tr_problem_m p) = ?ws\<close>
    using frs sort_width_lt by (auto simp: var_widths_def tr_problem_m_def Let_def unat_of_nat_eq)
  have c0: \<open>ctx_ok p I ?ws vs 0 [] []\<close> using assms(1-5) by (simp add: ctx_ok_def Let_def)
  obtain S0 dm where d: \<open>tr_defs_m p = (S0, dm)\<close> by (cases \<open>tr_defs_m p\<close>)
  obtain S' ts where a: \<open>tr_asserts_m p (S0, dm) = (S', ts)\<close> by (cases \<open>tr_asserts_m p (S0, dm)\<close>)
  have af: \<open>foldl (tr_asserts_step p dm) (S0, []) (SmtProblem_asserts p) = (S', ts)\<close>
    using a by (simp add: tr_asserts_m_step)
  have len0: \<open>length S0 < 2 ^ 64\<close> using tr_prefix_asserts[OF af] assms(6) a d by auto
  have D: \<open>ctx_ok p I ?ws vs (length ?ds) dm S0 \<and> defs_wt ?ws [] S0\<close>
    using tr_defs_correct[OF c0, of \<open>length ?ds\<close>] len0 d by (simp add: tr_defs_m_step)
  have ta: \<open>\<forall>t \<in> set (SmtProblem_asserts p). smt_tsort ?fs ?ds [] t = Some SmtSort_Bool\<close>
    using assms(1) by (simp add: smt_wf_def Let_def)
  have A: \<open>(\<exists>E. S' = S0 @ E) \<and> defs_wt ?ws [] S' \<and> (\<exists>new. ts = [] @ new \<and> length new = length (SmtProblem_asserts p) \<and>
           (\<forall>i < length (SmtProblem_asserts p). aok p I ?ws vs S' (new ! i) (SmtProblem_asserts p ! i)))\<close>
    using tr_asserts_gen[OF conjunct1[OF D] conjunct2[OF D] ta af] assms(6) a d by simp
  have tp: \<open>tr_problem_m p = make_Problem (map (\<lambda>f. word_of_nat (sort_width_m (SmtFun_ret f))) ?fs) S' ts\<close>
    using a d by (simp add: tr_problem_m_def)
  have hs: \<open>smt_has_sort SmtSort_Bool (smt_eval I (smt_def_sems I ?ds) [] t)\<close> if \<open>t \<in> set (SmtProblem_asserts p)\<close> for t
    using val_sort[OF conjunct1[OF D], of \<open>[]\<close> t SmtSort_Bool \<open>[]\<close>] ta that by simp
  have ev: \<open>(enc (smt_eval I (smt_def_sems I ?ds) [] t) = 1) = (smt_eval I (smt_def_sems I ?ds) [] t = VBool True)\<close>
    if \<open>t \<in> set (SmtProblem_asserts p)\<close> for t
    using hs[OF that] by (cases \<open>smt_eval I (smt_def_sems I ?ds) [] t\<close>) auto
  obtain new where nw: \<open>ts = new\<close> \<open>length new = length (SmtProblem_asserts p)\<close>
    \<open>\<forall>i < length (SmtProblem_asserts p). aok p I ?ws vs S' (new ! i) (SmtProblem_asserts p ! i)\<close>
    using A by auto
  have pf: \<open>Problem_defs (tr_problem_m p) = S'\<close> \<open>Problem_asserts (tr_problem_m p) = ts\<close> using tp by simp_all
  let ?E = \<open>\<lambda>t. eval ?ws (def_widths ?ws [] S') vs (def_values ?ws [] vs [] S') t\<close>
  have eqv: \<open>(\<forall>t \<in> set ts. ?E t = 1) = smt_satisfies p I\<close>
  proof -
    have \<open>(\<forall>t \<in> set ts. ?E t = 1) = (\<forall>i < length ts. ?E (ts ! i) = 1)\<close> by (rule all_set_conv_all_nth)
    also have \<open>\<dots> = (\<forall>i < length (SmtProblem_asserts p).
        smt_eval I (smt_def_sems I ?ds) [] (SmtProblem_asserts p ! i) = VBool True)\<close>
      using nw ev by (auto simp: aok_def)
    also have \<open>\<dots> = (\<forall>t \<in> set (SmtProblem_asserts p). smt_eval I (smt_def_sems I ?ds) [] t = VBool True)\<close>
      by (rule all_set_conv_all_nth[symmetric])
    finally show ?thesis by (simp add: smt_satisfies_def Let_def)
  qed
  show ?thesis
  proof (intro conjI)
    show \<open>problem_wt (tr_problem_m p)\<close>
      using A nw vw pf unfolding problem_wt_def Let_def by (auto simp: aok_def all_set_conv_all_nth)
    show \<open>var_widths (tr_problem_m p) = ?ws\<close> using vw .
    show \<open>(\<forall>t \<in> set (Problem_asserts (tr_problem_m p)).
        eval (var_widths (tr_problem_m p)) (def_widths (var_widths (tr_problem_m p)) [] (Problem_defs (tr_problem_m p))) vs
          (def_values (var_widths (tr_problem_m p)) [] vs [] (Problem_defs (tr_problem_m p))) t = 1) = smt_satisfies p I\<close>
      using eqv vw pf by simp
  qed
qed

subsection \<open>Models\<close>

fun bits_of :: \<open>nat \<Rightarrow> nat \<Rightarrow> bool list\<close> where
  \<open>bits_of 0 x = []\<close>
| \<open>bits_of (Suc w) x = odd x # bits_of w (x div 2)\<close>

lemma bits_of_length: \<open>length (bits_of w x) = w\<close>
  by (induction w arbitrary: x) auto

lemma bits_of_nat: \<open>smt_bits_nat (bits_of w x) = x mod 2 ^ w\<close>
proof (induction w arbitrary: x)
  case 0
  then show ?case by simp
next
  case (Suc w)
  have \<open>of_bool (odd x) + 2 * (x div 2 mod 2 ^ w) = x mod 2 ^ Suc w\<close>
    by (cases \<open>odd x\<close>) (simp_all add: mod_mult2_eq mult.commute odd_iff_mod_2_eq_one even_iff_mod_2_eq_zero)
  then show ?case using Suc.IH by simp
qed

lemma interp_sound_iff: \<open>interp_sound (SmtProblem_funs p) I = smt_interp_ok p I\<close>
  by (simp add: interp_sound_def smt_interp_ok_def)

lemma tr_model_correct:
  assumes \<open>smt_wf p\<close> \<open>smt_fragment p\<close> \<open>length (fst (tr_asserts_m p (tr_defs_m p))) < 2 ^ 64\<close>
    \<open>is_model (tr_problem_m p) m\<close>
  shows \<open>smt_is_model p (tr_model_m p m)\<close>
proof -
  let ?fs = \<open>SmtProblem_funs p\<close> and ?I = \<open>smt_model_interp (tr_model_m p m)\<close>
  let ?ws = \<open>map (\<lambda>f. sort_width_m (SmtFun_ret f)) ?fs\<close>
  have frs: \<open>\<forall>f \<in> set ?fs. frag_sort (SmtFun_ret f)\<close> and na: \<open>\<forall>f \<in> set ?fs. SmtFun_args f = []\<close>
    and ns: \<open>unat (SmtProblem_num_sorts p) = 0\<close>
    using assms(1,2) frag_of_wf by (auto simp: smt_wf_def smt_fragment_def Let_def)
  have vw: \<open>var_widths (tr_problem_m p) = ?ws\<close>
    using frs sort_width_lt by (auto simp: var_widths_def tr_problem_m_def Let_def unat_of_nat_eq)
  have ml: \<open>map length m = ?ws\<close> using assms(4) vw by (simp add: is_model_def is_assignment_def)
  have lm0: \<open>length m = length ?fs\<close> using ml by (metis length_map)
  have lm: \<open>length m = length ?fs\<close> \<open>\<forall>f < length ?fs. length (m ! f) = sort_width_m (SmtFun_ret (?fs ! f))\<close>
    using lm0 ml by (auto, metis nth_map)
  have Iv: \<open>?I f [] = (case SmtFun_ret (?fs ! f) of SmtSort_Bool \<Rightarrow> VBool (m ! f ! 0)
      | _ \<Rightarrow> VBv (length (m ! f)) (smt_bits_nat (m ! f)))\<close> if \<open>f < length ?fs\<close> for f
    using that by (auto simp: smt_model_interp_def smt_interp_of_def tr_model_m_def split: SmtSort.splits)
  have one: \<open>length (m ! f) = 1 \<Longrightarrow> smt_bits_nat (m ! f) = of_bool (m ! f ! 0)\<close> for f
    by (cases \<open>m ! f\<close>) auto
  have isd: \<open>interp_sound ?fs ?I\<close>
    unfolding interp_sound_def
  proof (intro allI impI)
    fix f xs assume f: \<open>f < length ?fs\<close> and la: \<open>list_all2 smt_has_sort (SmtFun_args (?fs ! f)) xs\<close>
    then have \<open>xs = []\<close> using na by (metis list.rel_sel nth_mem)
    moreover have \<open>frag_sort (SmtFun_ret (?fs ! f))\<close> using frs f by simp
    ultimately show \<open>smt_has_sort (SmtFun_ret (?fs ! f)) (?I f xs)\<close>
      using Iv[OF f] lm f smt_bits_nat_lt_s[of \<open>m ! f\<close>] by (cases \<open>SmtFun_ret (?fs ! f)\<close>) auto
  qed
  have vs: \<open>\<forall>f < length ?fs. map smt_bits_nat m ! f = enc (?I f [])\<close>
  proof (intro allI impI)
    fix f assume f: \<open>f < length ?fs\<close>
    then show \<open>map smt_bits_nat m ! f = enc (?I f [])\<close>
      using Iv[OF f] lm one[of f] frs by (cases \<open>SmtFun_ret (?fs ! f)\<close>) auto
  qed
  have S: \<open>smt_satisfies p ?I\<close>
    using tr_problem_sem[OF assms(1,2) isd _ vs assms(3)] assms(4) lm vw
    by (simp add: is_model_def satisfies_def Let_def helper_defs_eq)
  have W: \<open>smt_model_wf p (tr_model_m p m)\<close>
    unfolding smt_model_wf_def Let_def
    using ns lm frs[unfolded all_set_conv_all_nth] by (auto simp: tr_model_m_def split: SmtSort.splits)
  show ?thesis using S W by (simp add: smt_is_model_def)
qed

lemma tr_complete:
  assumes \<open>smt_wf p\<close> \<open>smt_fragment p\<close> \<open>length (fst (tr_asserts_m p (tr_defs_m p))) < 2 ^ 64\<close>
    \<open>smt_satisfiable p\<close>
  shows \<open>\<exists>m. is_model (tr_problem_m p) m\<close>
proof -
  obtain I where I: \<open>smt_interp_ok p I\<close> \<open>smt_satisfies p I\<close> using assms(4) by (auto simp: smt_satisfiable_def)
  let ?fs = \<open>SmtProblem_funs p\<close>
  let ?ws = \<open>map (\<lambda>f. sort_width_m (SmtFun_ret f)) ?fs\<close>
  have frs: \<open>\<forall>f < length ?fs. frag_sort (SmtFun_ret (?fs ! f))\<close> and na: \<open>\<forall>f < length ?fs. SmtFun_args (?fs ! f) = []\<close>
    using assms(1,2) frag_of_wf by (auto simp: smt_wf_def smt_fragment_def Let_def)
  have vw: \<open>var_widths (tr_problem_m p) = ?ws\<close>
    using frs sort_width_lt by (auto simp: var_widths_def tr_problem_m_def Let_def unat_of_nat_eq all_set_conv_all_nth)
  define m where \<open>m = map (\<lambda>f. bits_of (sort_width_m (SmtFun_ret (?fs ! f))) (enc (I f []))) [0..<length ?fs]\<close>
  have hs: \<open>smt_has_sort (SmtFun_ret (?fs ! f)) (I f [])\<close> if \<open>f < length ?fs\<close> for f
    using I(1) na that by (simp add: smt_interp_ok_def)
  have lt: \<open>enc (I f []) < 2 ^ sort_width_m (SmtFun_ret (?fs ! f))\<close> if \<open>f < length ?fs\<close> for f
    using hs[OF that] frs that by (cases \<open>SmtFun_ret (?fs ! f)\<close>; cases \<open>I f []\<close>) auto
  have vs: \<open>\<forall>f < length ?fs. map smt_bits_nat m ! f = enc (I f [])\<close>
    using lt by (simp add: m_def bits_of_nat)
  have isd: \<open>interp_sound ?fs I\<close> using I(1) interp_sound_iff by blast
  have lmm: \<open>length (map smt_bits_nat m) = length ?fs\<close> by (simp add: m_def)
  note T = tr_problem_sem[OF assms(1,2) isd lmm vs assms(3)]
  note T3 = conjunct2[OF conjunct2[OF T], unfolded conjunct1[OF conjunct2[OF T]]]
  have ml: \<open>map length m = ?ws\<close> by (auto simp: m_def bits_of_length intro: nth_equalityI)
  have \<open>is_model (tr_problem_m p) m\<close>
    using T3 I(2) vw ml by (simp add: is_model_def is_assignment_def satisfies_def Let_def helper_defs_eq)
  then show ?thesis by blast
qed

end
