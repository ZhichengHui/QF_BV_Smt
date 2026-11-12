theory BVSmt_SmtBound
  imports BVSmt_SmtSize
begin

section \<open>A bound on the size of the translation\<close>

text \<open>For a well-sorted problem of the fragment whose size fits in 64 bits, the translation has
  fewer than \<open>2^63\<close> definitions and its size is below \<open>2^63\<close>. Every node of the problem (an
  application of a definition with parameters counted at each application, as in
  \<^const>\<open>smt_weight\<close>) adds at most as many definitions as it has arguments, and terms whose
  weight is at most \<open>40\<close> times its weight \<^const>\<open>smt_node_weight\<close>.\<close>

subsection \<open>Weights of terms of the extended language\<close>

text \<open>The operands of a term.\<close>
fun bkids :: \<open>Term \<Rightarrow> Term list\<close> where
  \<open>bkids (Term_Not a) = [a]\<close>
| \<open>bkids (Term_Neg a) = [a]\<close>
| \<open>bkids (Term_Bin op a b) = [a, b]\<close>
| \<open>bkids (Term_Extract hi lo a) = [a]\<close>
| \<open>bkids (Term_Repeat i a) = [a]\<close>
| \<open>bkids (Term_ZeroExtend i a) = [a]\<close>
| \<open>bkids (Term_SignExtend i a) = [a]\<close>
| \<open>bkids (Term_RotateLeft i a) = [a]\<close>
| \<open>bkids (Term_RotateRight i a) = [a]\<close>
| \<open>bkids (Term_Ite c a b) = [c, a, b]\<close>
| \<open>bkids _ = []\<close>

lemma subterms_bkids: \<open>subterms u = u # concat (map subterms (bkids u))\<close>
  by (cases u) simp_all

lemma term_weight_bkids:
  \<open>term_weight ws D u = (width ws D u + 1) ^ 3 + sum_list (map (term_weight ws D) (bkids u))\<close>
  by (cases u) (simp_all add: term_weight_def)

text \<open>\<open>bsw D B u\<close>: \<open>u\<close> is built from references to definitions of width at most \<open>B\<close> by
  operations whose width is \<open>1\<close> or that of their first operand; so every subterm has width at most
  \<open>B\<close> (for \<open>1 \<le> B\<close>).\<close>
fun bsw :: \<open>nat list \<Rightarrow> nat \<Rightarrow> Term \<Rightarrow> bool\<close> where
  \<open>bsw D B (Term_Ref i) = (D ! unat i \<le> B)\<close>
| \<open>bsw D B (Term_Not a) = bsw D B a\<close>
| \<open>bsw D B (Term_Neg a) = bsw D B a\<close>
| \<open>bsw D B (Term_Bin op a b) =
     (op \<in> {Op_And, Op_Or, Op_Xor, Op_Add, Op_Mul, Op_Eq, Op_Distinct} \<and> bsw D B a \<and> bsw D B b)\<close>
| \<open>bsw D B (Term_Ite c a b) = (bsw D B c \<and> bsw D B a \<and> bsw D B b)\<close>
| \<open>bsw D B _ = False\<close>

lemma bsw_width: \<open>bsw D B u \<Longrightarrow> 1 \<le> B \<Longrightarrow> width ws D u \<le> B\<close>
  by (induction u) auto

lemma bsw_sub: \<open>bsw D B u \<Longrightarrow> v \<in> set (subterms u) \<Longrightarrow> bsw D B v\<close>
  by (induction u) auto

lemma bsw_kids: \<open>bsw D B u \<Longrightarrow> \<forall>c \<in> set (bkids u). bsw D B c\<close>
  by (cases u) auto

lemma bsw_weight: \<open>bsw D B u \<Longrightarrow> 1 \<le> B \<Longrightarrow> term_weight ws D u \<le> length (subterms u) * (B + 1) ^ 3\<close>
proof -
  assume a: \<open>bsw D B u\<close> \<open>1 \<le> B\<close>
  have \<open>sum_list (map (\<lambda>v. (width ws D v + 1) ^ 3) (subterms u)) \<le> sum_list (map (\<lambda>v. (B + 1) ^ 3) (subterms u))\<close>
  proof (rule sum_list_mono)
    fix v assume \<open>v \<in> set (subterms u)\<close>
    then have \<open>width ws D v \<le> B\<close> using a bsw_sub bsw_width by blast
    then show \<open>(width ws D v + 1) ^ 3 \<le> (B + 1) ^ 3\<close> by (simp add: power_mono)
  qed
  then show ?thesis by (simp add: term_weight_def sum_list_triv)
qed

lemma kids_weight:
  assumes \<open>\<forall>c \<in> set (bkids u). bsw D B c\<close> \<open>1 \<le> B\<close>
  shows \<open>term_weight ws D u \<le> (width ws D u + 1) ^ 3 + length (subterms u) * (B + 1) ^ 3\<close>
proof -
  have \<open>sum_list (map (term_weight ws D) (bkids u)) \<le> sum_list (map (\<lambda>c. length (subterms c) * (B + 1) ^ 3) (bkids u))\<close>
    by (rule sum_list_mono) (use assms bsw_weight in blast)
  also have \<open>\<dots> = sum_list (map (\<lambda>c. length (subterms c)) (bkids u)) * (B + 1) ^ 3\<close>
    by (simp add: sum_list_mult_const)
  also have \<open>\<dots> \<le> length (subterms u) * (B + 1) ^ 3\<close>
  proof -
    have \<open>sum_list (map (\<lambda>c. length (subterms c)) (bkids u)) \<le> length (subterms u)\<close>
      using arg_cong[OF subterms_bkids[of u], of length] by (simp add: length_concat comp_def)
    then show ?thesis by (rule mult_le_mono1)
  qed
  finally show ?thesis by (simp add: term_weight_bkids[of ws D u])
qed

subsection \<open>The terms of the theory functions\<close>

text \<open>The least number of arguments of a well-sorted application of \<open>op\<close>.\<close>
fun bar :: \<open>SmtOp \<Rightarrow> nat\<close> where
  \<open>bar SmtOp_Not = 1\<close>
| \<open>bar SmtOp_Bvnot = 1\<close>
| \<open>bar SmtOp_Bvneg = 1\<close>
| \<open>bar (SmtOp_Extract i j) = 1\<close>
| \<open>bar (SmtOp_Repeat i) = 1\<close>
| \<open>bar (SmtOp_ZeroExtend i) = 1\<close>
| \<open>bar (SmtOp_SignExtend i) = 1\<close>
| \<open>bar (SmtOp_RotateLeft i) = 1\<close>
| \<open>bar (SmtOp_RotateRight i) = 1\<close>
| \<open>bar SmtOp_Ite = 3\<close>
| \<open>bar _ = 2\<close>

lemma smt_bin_width_len: \<open>smt_bin_width ss \<noteq> None \<Longrightarrow> length ss = 2\<close>
  using smt_bin_width_Some by fastforce

lemma bar_sort: \<open>smt_op_sort op ss = Some s \<Longrightarrow> bar op \<le> length ss\<close>
  by (cases op) (auto split: if_splits list.splits SmtSort.splits dest: smt_bin_width_len)

lemma bsw_tref: \<open>k < 2 ^ 64 \<Longrightarrow> bsw D B (tref k) = (D ! k \<le> B)\<close>
  by (simp add: tref_def unat_of_nat_eq)

lemma bsw_foldl_ref:
  \<open>bsw D B a \<Longrightarrow> (\<forall>k \<in> set xs. bsw D B (tref k)) \<Longrightarrow> bo \<in> {Op_And, Op_Or, Op_Xor, Op_Add, Op_Mul, Op_Eq, Op_Distinct} \<Longrightarrow>
   bsw D B (foldl (\<lambda>acc k. Term_Bin bo acc (tref k)) a xs)\<close>
  by (induction xs arbitrary: a) auto

lemma len_foldl_ref:
  \<open>length (subterms (foldl (\<lambda>acc k. Term_Bin bo acc (tref k)) a xs)) = length (subterms a) + 2 * length xs\<close>
  by (induction xs arbitrary: a) (auto simp: tref_def)

lemma bsw_foldl_and:
  \<open>bsw D B a \<Longrightarrow> (\<forall>x \<in> set xs. bsw D B (g x)) \<Longrightarrow> bsw D B (foldl (\<lambda>acc x. Term_Bin Op_And acc (g x)) a xs)\<close>
  by (induction xs arbitrary: a) auto

lemma len_foldl_and:
  \<open>(\<forall>x \<in> set xs. length (subterms (g x)) = 3) \<Longrightarrow>
   length (subterms (foldl (\<lambda>acc x. Term_Bin Op_And acc (g x)) a xs)) = length (subterms a) + 4 * length xs\<close>
  by (induction xs arbitrary: a) auto

lemma bsw_foldr_imp:
  \<open>bsw D B a \<Longrightarrow> (\<forall>k \<in> set xs. bsw D B (tref k)) \<Longrightarrow>
   bsw D B (foldr (\<lambda>k acc. Term_Bin Op_Or (Term_Not (tref k)) acc) xs a)\<close>
  by (induction xs) auto

lemma len_foldr_imp:
  \<open>length (subterms (foldr (\<lambda>k acc. Term_Bin Op_Or (Term_Not (tref k)) acc) xs a)) = length (subterms a) + 3 * length xs\<close>
  by (induction xs) (auto simp: tref_def)

lemma len_pairs_m: \<open>length (pairs_m n) \<le> n * n\<close>
proof -
  have \<open>length (pairs_m n) \<le> length (concat (map (\<lambda>i. map (\<lambda>j. (i, j)) [Suc i..<n]) [0..<n]))\<close>
    unfolding pairs_m_def by (rule length_filter_le)
  also have \<open>\<dots> = sum_list (map (\<lambda>i. n - Suc i) [0..<n])\<close> by (simp add: length_concat comp_def)
  also have \<open>\<dots> \<le> sum_list (map (\<lambda>i. n) [0..<n])\<close> by (rule sum_list_mono) simp
  also have \<open>\<dots> = n * n\<close> by (simp add: sum_list_triv)
  finally show ?thesis .
qed

lemma pairs_m_lt: \<open>2 \<le> n \<Longrightarrow> ij \<in> set (pairs_m n) \<Longrightarrow> fst ij < n \<and> snd ij < n\<close>
  using pairs_m_set[of n] by (cases ij) auto

lemma sq_mono: \<open>(a :: nat) \<le> 4 * (n + 1) ^ 2 \<Longrightarrow> a \<le> 4 * (n + 1) ^ 2\<close>
  by simp

lemma app_kids_bsw:
  assumes \<open>bar op \<le> length ks\<close> \<open>\<forall>k \<in> set ks. bsw D B (tref k)\<close>
  shows \<open>\<forall>c \<in> set (bkids (tr_app_m op ks)). bsw D B c\<close>
proof -
  have n: \<open>i < length ks \<Longrightarrow> bsw D B (tref (ks ! i))\<close> for i using assms(2) by simp
  have ne: \<open>ks \<noteq> []\<close> using assms(1) by (cases op) auto
  have fl: \<open>bsw D B (fold_left_m op' ks)\<close> if \<open>tr_op op' \<in> {Op_And, Op_Or, Op_Xor, Op_Add, Op_Mul, Op_Eq, Op_Distinct}\<close> for op'
    unfolding fold_left_m_def
    by (rule bsw_foldl_ref) (use assms(2) ne that in \<open>auto dest: list.set_sel(2)\<close>)
  have im: \<open>bsw D B (implies_m ks)\<close>
    unfolding implies_m_def by (rule bsw_foldr_imp) (use assms(2) ne in \<open>auto dest: in_set_butlastD\<close>)
  have ch: \<open>bsw D B (chain_m SmtOp_Eq ks)\<close> if \<open>2 \<le> length ks\<close>
    unfolding chain_m_def by (rule bsw_foldl_and) (use n that in auto)
  have pw: \<open>bsw D B (pairwise_m ks)\<close> if \<open>2 \<le> length ks\<close>
    unfolding pairwise_m_def by (rule bsw_foldl_and) (use n that pairs_m_lt in auto)
  show ?thesis
    using assms(1) n bsw_kids[OF fl] bsw_kids[OF im] bsw_kids[OF ch] bsw_kids[OF pw]
    by (cases op) simp_all
qed

lemma app_len:
  assumes \<open>bar op \<le> length ks\<close>
  shows \<open>length (subterms (tr_app_m op ks)) \<le> 4 * (length ks + 1) ^ 2\<close>
proof -
  let ?n = \<open>length ks\<close>
  have ne: \<open>ks \<noteq> []\<close> using assms(1) by (cases op) auto
  have sq: \<open>4 * ?n + 4 \<le> 4 * (?n + 1) ^ 2\<close> by (simp add: power2_eq_square)
  have fl: \<open>length (subterms (fold_left_m op' ks)) \<le> 4 * (?n + 1) ^ 2\<close> for op'
    using len_foldl_ref[of \<open>tr_op op'\<close> \<open>tref (hd ks)\<close> \<open>tl ks\<close>] sq by (simp add: fold_left_m_def tref_def)
  have im: \<open>length (subterms (implies_m ks)) \<le> 4 * (?n + 1) ^ 2\<close>
    using len_foldr_imp[of \<open>butlast ks\<close> \<open>tref (last ks)\<close>] sq by (simp add: implies_m_def tref_def)
  have ch: \<open>length (subterms (chain_m SmtOp_Eq ks)) \<le> 4 * (?n + 1) ^ 2\<close>
    using len_foldl_and[of \<open>[2..<?n]\<close> \<open>\<lambda>i. Term_Bin (tr_op SmtOp_Eq) (tref (ks ! (i - 1))) (tref (ks ! i))\<close>
        \<open>Term_Bin (tr_op SmtOp_Eq) (tref (ks ! 0)) (tref (ks ! 1))\<close>] sq
    by (simp add: chain_m_def tref_def)
  have pw: \<open>length (subterms (pairwise_m ks)) \<le> 4 * (?n + 1) ^ 2\<close>
  proof -
    have \<open>length (subterms (pairwise_m ks)) = 3 + 4 * length (pairs_m ?n)\<close>
      using len_foldl_and[of \<open>pairs_m ?n\<close> \<open>\<lambda>ij. Term_Bin Op_Distinct (tref (ks ! fst ij)) (tref (ks ! snd ij))\<close>
          \<open>Term_Bin Op_Distinct (tref (ks ! 0)) (tref (ks ! 1))\<close>]
      by (simp add: pairwise_m_def tref_def)
    also have \<open>\<dots> \<le> 3 + 4 * (?n * ?n)\<close> using len_pairs_m[of ?n] by simp
    also have \<open>\<dots> \<le> 4 * (?n + 1) ^ 2\<close> by (simp add: power2_eq_square algebra_simps)
    finally show ?thesis .
  qed
  show ?thesis
    using assms(1) fl im ch pw sq by (cases op) (simp_all add: tref_def)
qed

lemma app_weight:
  assumes \<open>bar op \<le> length ks\<close> \<open>\<forall>k \<in> set ks. k < 2 ^ 64\<close>
  shows \<open>term_weight ws D (tr_app_m op ks) \<le>
    (width ws D (tr_app_m op ks) + 1) ^ 3 + 4 * (length ks + 1) ^ 2 * (8 + sum_list (map (\<lambda>k. (D ! k + 1) ^ 3) ks))\<close>
proof -
  define B where \<open>B = Max (insert 1 (set (map (\<lambda>k. D ! k) ks)))\<close>
  have B1: \<open>1 \<le> B\<close> by (simp add: B_def)
  have Bk: \<open>\<forall>k \<in> set ks. bsw D B (tref k)\<close> using assms(2) by (simp add: B_def bsw_tref)
  have Bc: \<open>(B + 1) ^ 3 \<le> 8 + sum_list (map (\<lambda>k. (D ! k + 1) ^ 3) ks)\<close>
  proof -
    have \<open>B \<in> insert 1 (set (map (\<lambda>k. D ! k) ks))\<close> unfolding B_def by (rule Max_in) simp_all
    then consider \<open>B = 1\<close> | k where \<open>k \<in> set ks\<close> \<open>B = D ! k\<close> by auto
    then show ?thesis
    proof cases
      case 1
      then show ?thesis by simp
    next
      case 2
      then have \<open>(B + 1) ^ 3 \<in> set (map (\<lambda>k. (D ! k + 1) ^ 3) ks)\<close> by simp
      then show ?thesis using member_le_sum_list by fastforce
    qed
  qed
  have \<open>term_weight ws D (tr_app_m op ks) \<le> (width ws D (tr_app_m op ks) + 1) ^ 3 + length (subterms (tr_app_m op ks)) * (B + 1) ^ 3\<close>
    using kids_weight[OF app_kids_bsw[OF assms(1) Bk] B1] .
  also have \<open>\<dots> \<le> (width ws D (tr_app_m op ks) + 1) ^ 3 + 4 * (length ks + 1) ^ 2 * (B + 1) ^ 3\<close>
    using app_len[OF assms(1)] by simp
  also have \<open>\<dots> \<le> (width ws D (tr_app_m op ks) + 1) ^ 3 + 4 * (length ks + 1) ^ 2 * (8 + sum_list (map (\<lambda>k. (D ! k + 1) ^ 3) ks))\<close>
    using Bc by simp
  finally show ?thesis .
qed

subsection \<open>Widths\<close>

lemma cube8: \<open>(sort_width_m s + 1) ^ 3 \<le> 8 * (smt_width s + 1) ^ 3\<close>
proof -
  have \<open>sort_width_m s + 1 \<le> 2 * (smt_width s + 1)\<close> by (cases s) auto
  then have \<open>(sort_width_m s + 1) ^ 3 \<le> (2 * (smt_width s + 1)) ^ 3\<close> by (rule power_mono) simp
  then show ?thesis by (simp add: power_mult_distrib)
qed

lemma wcube_ge1: \<open>1 \<le> smt_wcube s ^ 3\<close>
  by (simp add: smt_wcube_def)

lemma node_weight_ge: \<open>length args \<le> smt_node_weight fs ds ps t args\<close>
proof -
  have \<open>Suc (length args) ^ 2 * 1 \<le> smt_node_weight fs ds ps t args\<close>
    unfolding smt_node_weight_def by (rule mult_le_mono2) (use wcube_ge1 in \<open>simp add: le_add1 order_trans\<close>)
  moreover have \<open>length args \<le> Suc (length args) ^ 2 * 1\<close> by (simp add: power2_eq_square)
  ultimately show ?thesis by linarith
qed

lemma node_weight_leaf: \<open>smt_tsort fs ds ps t = Some s \<Longrightarrow> (smt_width s + 1) ^ 3 \<le> smt_node_weight fs ds ps t args\<close>
  by (simp add: smt_node_weight_def smt_wcube_def)

subsection \<open>The number of definitions\<close>

lemma cnt_le_weight:
  \<open>n \<le> length (SmtProblem_defs p) \<Longrightarrow> cnt p n t \<le> smt_weight (SmtProblem_funs p) (take n (SmtProblem_defs p)) ps t\<close>
  \<open>n \<le> length (SmtProblem_defs p) \<Longrightarrow>
   cnt_args p n ts \<le> length ts + sum_list (map (smt_weight (SmtProblem_funs p) (take n (SmtProblem_defs p)) ps) ts)\<close>
proof (induction p n t and p n ts arbitrary: ps and ps rule: cnt_cnt_args.induct)
  case (1 p n d args)
  let ?ds = \<open>SmtProblem_defs p\<close> and ?fs = \<open>SmtProblem_funs p\<close>
  show ?case
  proof (cases \<open>SmtDef_params (?ds ! unat d) = [] \<or> \<not> unat d < n\<close>)
    case True
    then show ?thesis by auto
  next
    case False
    then have nd: \<open>unat d < n\<close> \<open>SmtDef_params (?ds ! unat d) \<noteq> []\<close> by auto
    have a: \<open>cnt_args p n args \<le> length args + sum_list (map (smt_weight ?fs (take n ?ds) ps) args)\<close>
      using 1(1) nd 1(3) by simp
    have b: \<open>cnt p (unat d) (SmtDef_body (?ds ! unat d)) \<le>
        smt_weight ?fs (take (unat d) ?ds) (SmtDef_params (?ds ! unat d)) (SmtDef_body (?ds ! unat d))\<close>
      using 1(2) nd 1(3) by simp
    have c: \<open>length args \<le> smt_node_weight ?fs (take n ?ds) ps (SmtTerm_Def d args) args\<close> by (rule node_weight_ge)
    show ?thesis using a b c nd 1(3) by (simp add: min_def)
  qed
next
  case (2 p n op args)
  have \<open>length args \<le> smt_node_weight (SmtProblem_funs p) (take n (SmtProblem_defs p)) ps (SmtTerm_App op args) args\<close>
    by (rule node_weight_ge)
  then show ?case using 2 by simp
qed simp_all

end
