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
| \<open>tr_args_m p dm env n S (a # as) =
     (let r1 = tr_term_m p dm env n S a;
          r2 = tr_args_m p dm env n (fst r1 @ [snd r1]) as in
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
     Problem_mk (map (\<lambda>f. word_of_nat (sort_width_m (SmtFun_ret f))) (SmtProblem_funs p)) (fst ra) (snd ra)\<close>

text \<open>The model of \<open>p\<close> for the assignment \<open>m\<close> of the variables of the translation.\<close>
definition tr_model_m :: \<open>SmtProblem \<Rightarrow> bool list list \<Rightarrow> SmtModel\<close> where
  \<open>tr_model_m p m \<equiv>
     SmtModel_mk []
       (map (\<lambda>i. SmtInterp_mk []
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
  by (induction t) (auto simp: nth_append)

end
