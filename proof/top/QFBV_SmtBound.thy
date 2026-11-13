theory QFBV_SmtBound
  imports QFBV_SmtSize
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
fun sop_ar :: \<open>SmtOp \<Rightarrow> nat\<close> where
  \<open>sop_ar SmtOp_Not = 1\<close>
| \<open>sop_ar SmtOp_Bvnot = 1\<close>
| \<open>sop_ar SmtOp_Bvneg = 1\<close>
| \<open>sop_ar (SmtOp_Extract i j) = 1\<close>
| \<open>sop_ar (SmtOp_Repeat i) = 1\<close>
| \<open>sop_ar (SmtOp_ZeroExtend i) = 1\<close>
| \<open>sop_ar (SmtOp_SignExtend i) = 1\<close>
| \<open>sop_ar (SmtOp_RotateLeft i) = 1\<close>
| \<open>sop_ar (SmtOp_RotateRight i) = 1\<close>
| \<open>sop_ar SmtOp_Ite = 3\<close>
| \<open>sop_ar _ = 2\<close>

lemma smt_bin_width_len: \<open>smt_bin_width ss \<noteq> None \<Longrightarrow> length ss = 2\<close>
  using smt_bin_width_Some by fastforce

lemma sop_ar_sort: \<open>smt_op_sort op ss = Some s \<Longrightarrow> sop_ar op \<le> length ss\<close>
  by (cases op) (auto split: if_splits list.splits SmtSort.splits dest!: smt_bin_width_Some)

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

lemma pairs_m_lt:
  assumes \<open>2 \<le> n\<close> \<open>ij \<in> set (pairs_m n)\<close>
  shows \<open>fst ij < n \<and> snd ij < n\<close>
proof -
  have \<open>ij \<in> {(i, j). i < j \<and> j < n}\<close> using pairs_m_set[OF assms(1)] assms(2) by blast
  then show ?thesis by (cases ij) simp
qed

lemma sq_mono: \<open>(a :: nat) \<le> 4 * (n + 1) ^ 2 \<Longrightarrow> a \<le> 4 * (n + 1) ^ 2\<close>
  by simp

lemma app_kids_bsw:
  assumes \<open>sop_ar op \<le> length ks\<close> \<open>\<forall>k \<in> set ks. bsw D B (tref k)\<close>
  shows \<open>\<forall>c \<in> set (bkids (tr_app_m op ks)). bsw D B c\<close>
proof -
  have n: \<open>i < length ks \<Longrightarrow> bsw D B (tref (ks ! i))\<close> for i using assms(2) nth_mem by blast
  have ne: \<open>ks \<noteq> []\<close> using assms(1) by (cases op) auto
  have tl: \<open>\<forall>k \<in> set (tl ks). k \<in> set ks\<close> by (cases ks) auto
  have k0: \<open>bsw D B (tref (ks ! 0))\<close> using n ne by simp
  have k1: \<open>bsw D B (tref (ks ! Suc 0))\<close> if \<open>2 \<le> length ks\<close> using n that by simp
  have k2: \<open>bsw D B (tref (ks ! 2))\<close> if \<open>3 \<le> length ks\<close> using n that by simp
  have fl: \<open>bsw D B (fold_left_m op' ks)\<close> if \<open>tr_op op' \<in> {Op_And, Op_Or, Op_Xor, Op_Add, Op_Mul, Op_Eq, Op_Distinct}\<close> for op'
    unfolding fold_left_m_def
    by (rule bsw_foldl_ref) (use assms(2) hd_in_set[OF ne] tl that in auto)
  have kF: \<open>\<forall>c \<in> set (bkids (fold_left_m op' ks)). bsw D B c\<close>
    if \<open>tr_op op' \<in> {Op_And, Op_Or, Op_Xor, Op_Add, Op_Mul, Op_Eq, Op_Distinct}\<close> for op'
    using bsw_kids[OF fl[OF that]] .
  have im: \<open>\<forall>c \<in> set (bkids (implies_m ks)). bsw D B c\<close>
    unfolding implies_m_def by (rule bsw_kids, rule bsw_foldr_imp) (use assms(2) ne in \<open>auto dest: in_set_butlastD\<close>)
  have ch: \<open>\<forall>c \<in> set (bkids (chain_m SmtOp_Eq ks)). bsw D B c\<close> if \<open>2 \<le> length ks\<close>
  proof -
    have \<open>bsw D B (chain_m SmtOp_Eq ks)\<close>
      unfolding chain_m_def by (rule bsw_foldl_and) (use n k0 k1[OF that] in auto)
    then show ?thesis by (rule bsw_kids)
  qed
  have pw: \<open>\<forall>c \<in> set (bkids (pairwise_m ks)). bsw D B c\<close> if \<open>2 \<le> length ks\<close>
  proof -
    have \<open>bsw D B (pairwise_m ks)\<close>
      unfolding pairwise_m_def by (rule bsw_foldl_and) (use n k0 k1[OF that] in \<open>auto dest: pairs_m_lt[OF that]\<close>)
    then show ?thesis by (rule bsw_kids)
  qed
  show ?thesis
    using assms(1) by (cases op) (simp_all add: k0 k1 k2 im ch pw, (rule kF, simp)+)
qed

lemma app_len:
  assumes \<open>sop_ar op \<le> length ks\<close>
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
  assumes \<open>sop_ar op \<le> length ks\<close> \<open>\<forall>k \<in> set ks. k < 2 ^ 64\<close>
  shows \<open>term_weight ws D (tr_app_m op ks) \<le>
    (width ws D (tr_app_m op ks) + 1) ^ 3 + 4 * (length ks + 1) ^ 2 * (8 + sum_list (map (\<lambda>k. (D ! k + 1) ^ 3) ks))\<close>
proof -
  define B where \<open>B = Max (insert 1 (set (map (\<lambda>k. D ! k) ks)))\<close>
  have B1: \<open>1 \<le> B\<close> by (auto simp: B_def intro!: Max_ge)
  have Bk: \<open>\<forall>k \<in> set ks. bsw D B (tref k)\<close> using assms(2) by (auto simp: B_def bsw_tref intro!: Max_ge)
  have Bc: \<open>(B + 1) ^ 3 \<le> 8 + sum_list (map (\<lambda>k. (D ! k + 1) ^ 3) ks)\<close>
  proof -
    have \<open>B \<in> insert 1 (set (map (\<lambda>k. D ! k) ks))\<close> unfolding B_def by (rule Max_in) simp_all
    then consider \<open>B = 1\<close> | k where \<open>k \<in> set ks\<close> \<open>B = D ! k\<close> by auto
    then show ?thesis
    proof cases
      case 1
      then show ?thesis by (simp add: power3_eq_cube)
    next
      case 2
      then have \<open>(B + 1) ^ 3 \<in> set (map (\<lambda>k. (D ! k + 1) ^ 3) ks)\<close> by auto
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
  have a: \<open>sort_width_m s + 1 \<le> 2 * (smt_width s + 1)\<close> by (cases s) auto
  have \<open>(sort_width_m s + 1) ^ 3 \<le> (2 * (smt_width s + 1)) ^ 3\<close> by (rule power_mono[OF a]) simp
  also have \<open>\<dots> = 8 * (smt_width s + 1) ^ 3\<close> unfolding power_mult_distrib by simp
  finally show ?thesis .
qed

lemma wcube_ge1: \<open>1 \<le> smt_wcube s ^ 3\<close>
  by (simp add: smt_wcube_def)

lemma node_weight_ge: \<open>length args \<le> smt_node_weight fs ds ps t args\<close>
proof -
  have \<open>Suc (length args) ^ 2 * 1 \<le> smt_node_weight fs ds ps t args\<close>
    unfolding smt_node_weight_def by (rule mult_le_mono2) (use wcube_ge1[of \<open>smt_tsort fs ds ps t\<close>] in linarith)
  moreover have \<open>length args \<le> Suc (length args) ^ 2 * 1\<close> by (simp add: power2_eq_square)
  ultimately show ?thesis by linarith
qed

lemma sum_list_Suc: \<open>sum_list (map (\<lambda>x. Suc (f x)) xs) = length xs + sum_list (map f xs)\<close>
  by (induction xs) auto

lemma wcube_Some: \<open>smt_wcube (Some s) = smt_width s + 1\<close>
  by (simp add: smt_wcube_def)

lemma sort_width_le: \<open>sort_width_m s \<le> smt_width s + 1\<close>
  by (cases s) auto

lemma map_some_eq: \<open>map g xs = map Some ys \<Longrightarrow> map (\<lambda>a. f (g a)) xs = map (\<lambda>y. f (Some y)) ys\<close>
  by (induction xs arbitrary: ys) auto

lemma node_weight_leaf:
  assumes \<open>smt_tsort fs ds ps t = Some s\<close>
  shows \<open>(smt_width s + 1) ^ 3 \<le> smt_node_weight fs ds ps t args\<close>
proof -
  have a: \<open>(smt_width s + 1) ^ 3 \<le> smt_wcube (smt_tsort fs ds ps t) ^ 3 + sum_list (map (\<lambda>a. smt_wcube (smt_tsort fs ds ps a) ^ 3) args)\<close>
    using assms by (simp add: wcube_Some)
  have b: \<open>1 \<le> Suc (length args) ^ 2\<close> by simp
  show ?thesis unfolding smt_node_weight_def using mult_le_mono[OF b a] by simp
qed

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
  then show ?case using 2(1)[OF 2(2), of ps] by simp
qed (simp_all, metis (no_types, lifting) add.left_commute add_le_mono)

subsection \<open>The weight of the translation of a term\<close>

lemma df_prefix: \<open>\<exists>e. Df = def_widths ws [] S' @ e \<Longrightarrow> S' = S1 @ E \<Longrightarrow> \<exists>e. Df = def_widths ws [] S1 @ e\<close>
  by (metis append.assoc def_widths_append' def_widths_prefix')

lemma df_width: \<open>\<exists>e. Df = def_widths ws [] S @ e \<Longrightarrow> wt ws (def_widths ws [] S) t \<Longrightarrow>
  width ws Df t = width ws (def_widths ws [] S) t\<close>
  using wt_width_eval_append[of ws \<open>def_widths ws [] S\<close> t \<open>replicate (length (def_widths ws [] S)) 0\<close>] by auto

lemma df_nth: \<open>\<exists>e. Df = def_widths ws [] S @ e \<Longrightarrow> k < length S \<Longrightarrow> Df ! k = def_widths ws [] S ! k\<close>
  by (auto simp: nth_append def_widths_length')

lemma tw_ref: \<open>ref_ok ws vs S k s v \<Longrightarrow> \<exists>e. Df = def_widths ws [] S @ e \<Longrightarrow>
  term_weight ws Df (tref k) = (sort_width_m s + 1) ^ 3\<close>
  by (auto simp: ref_ok_def tref_def term_weight_def unat_of_nat_eq nth_append def_widths_length')

lemma arith_app:
  assumes \<open>(a :: nat) \<le> 8 * c\<close> \<open>1 \<le> c\<close> \<open>1 \<le> N\<close> \<open>X \<le> 8 * Y\<close>
  shows \<open>a + 4 * N * (8 + X) \<le> 40 * (N * (c + Y))\<close>
proof -
  have 1: \<open>4 * N * (8 + X) \<le> 4 * N * (8 * c + 8 * Y)\<close> using assms by (intro mult_le_mono2) linarith
  have 2: \<open>8 * c \<le> 8 * (N * c)\<close> using assms by simp
  have 3: \<open>4 * N * (8 * c + 8 * Y) = 32 * (N * c) + 32 * (N * Y)\<close> by (simp add: algebra_simps)
  have 4: \<open>40 * (N * (c + Y)) = 40 * (N * c) + 40 * (N * Y)\<close> by (simp add: algebra_simps)
  show ?thesis using assms(1) 1 2 3 4 by linarith
qed

lemma tr_weight:
  shows \<open>tr_term_m p dm env n S t = (S', t') \<Longrightarrow> ctx_ok p I ws vs n dm S \<Longrightarrow>
     smt_tsort (SmtProblem_funs p) (take n (SmtProblem_defs p)) ps t = Some s \<Longrightarrow>
     \<forall>x \<in> set ps. frag_sort x \<Longrightarrow> length env = length ps \<Longrightarrow> length xs = length ps \<Longrightarrow>
     (\<forall>i < length ps. ref_ok ws vs S (env ! i) (ps ! i) (xs ! i)) \<Longrightarrow>
     defs_wt ws [] S \<Longrightarrow> length S' < 2 ^ 64 \<Longrightarrow> \<exists>e. Df = def_widths ws [] S' @ e \<Longrightarrow>
     sum_list (map (term_weight ws Df) (drop (length S) S')) + term_weight ws Df t' \<le>
       40 * smt_weight (SmtProblem_funs p) (take n (SmtProblem_defs p)) ps t\<close>
    and \<open>tr_args_m p dm env n S ts = (S', ks) \<Longrightarrow> ctx_ok p I ws vs n dm S \<Longrightarrow>
     map (smt_tsort (SmtProblem_funs p) (take n (SmtProblem_defs p)) ps) ts = map Some ss \<Longrightarrow>
     \<forall>x \<in> set ps. frag_sort x \<Longrightarrow> length env = length ps \<Longrightarrow> length xs = length ps \<Longrightarrow>
     (\<forall>i < length ps. ref_ok ws vs S (env ! i) (ps ! i) (xs ! i)) \<Longrightarrow>
     defs_wt ws [] S \<Longrightarrow> length S' < 2 ^ 64 \<Longrightarrow> \<exists>e. Df = def_widths ws [] S' @ e \<Longrightarrow>
     sum_list (map (term_weight ws Df) (drop (length S) S')) \<le>
       40 * sum_list (map (smt_weight (SmtProblem_funs p) (take n (SmtProblem_defs p)) ps) ts)\<close>
proof (induction p dm env n S t and p dm env n S ts arbitrary: S' t' ps s xs and S' ks ps ss xs
    rule: tr_term_m_tr_args_m.induct)
  case (1 p dm env n S b S' t' ps s xs)
  have res: \<open>S' = S\<close> \<open>t' = Term_Const [b]\<close> using 1(1) by auto
  then show ?case using 1(3) by (simp add: term_weight_def smt_node_weight_def smt_wcube_def power3_eq_cube)
next
  case (2 p dm env n S bs S' t' ps s xs)
  have s: \<open>s = SmtSort_BitVec (of_nat (length bs))\<close> \<open>length bs < 2 ^ 64\<close> using 2(3) by (auto split: if_splits)
  have \<open>(length bs + 1) ^ 3 \<le> smt_node_weight (SmtProblem_funs p) (take n (SmtProblem_defs p)) ps (SmtTerm_BvConst bs) []\<close>
    using node_weight_leaf[OF 2(3)] s by (simp add: unat_of_nat_eq)
  moreover have res: \<open>S' = S\<close> \<open>t' = Term_Const bs\<close> using 2(1) by auto
  ultimately show ?case by (simp add: term_weight_def)
next
  case (3 p dm env n S k S' t' ps s xs)
  then have k: \<open>unat k < length ps\<close> \<open>s = ps ! unat k\<close> by (auto split: if_splits)
  have r: \<open>ref_ok ws vs S (env ! unat k) s (xs ! unat k)\<close> using 3(7) k by simp
  have res: \<open>S' = S\<close> \<open>t' = tref (env ! unat k)\<close> using 3(1) by auto
  have Df3: \<open>\<exists>e. Df = def_widths ws [] S @ e\<close> using 3(10) res by simp
  have \<open>term_weight ws Df t' = (sort_width_m s + 1) ^ 3\<close> using tw_ref[OF r Df3] res by simp
  then show ?case using node_weight_leaf[OF 3(3), of \<open>[]\<close>] cube8[of s] res by simp
next
  case (4 p dm env n S i args S' t' ps s xs)
  let ?fs = \<open>SmtProblem_funs p\<close>
  have i: \<open>unat i < length ?fs\<close> \<open>s = SmtFun_ret (?fs ! unat i)\<close> using 4(3) by (auto split: if_splits)
  have wsd: \<open>ws = map (\<lambda>f. sort_width_m (SmtFun_ret f)) ?fs\<close> using 4(2) by (simp add: ctx_ok_def Let_def)
  have res: \<open>S' = S\<close> \<open>t' = Term_Var i\<close> using 4(1) by auto
  have \<open>term_weight ws Df t' = (sort_width_m s + 1) ^ 3\<close> using res wsd i by (simp add: term_weight_def)
  then show ?case using node_weight_leaf[OF 4(3), of args] cube8[of s] res by simp
next
  case (5 p dm env n S d args S' t' ps s xs)
  let ?fs = \<open>SmtProblem_funs p\<close> and ?ds = \<open>SmtProblem_defs p\<close> and ?dv = \<open>smt_def_sems I (SmtProblem_defs p)\<close>
  have d: \<open>unat d < length (take n ?ds)\<close> \<open>map (smt_tsort ?fs (take n ?ds) ps) args = map Some (SmtDef_params (?ds ! unat d))\<close>
    \<open>s = SmtDef_ret (?ds ! unat d)\<close> using 5(5) by (auto split: if_splits)
  have dn: \<open>unat d < n\<close> \<open>unat d < length ?ds\<close> using d(1) by auto
  have fr: \<open>smt_fragment p\<close> using 5(4) by (simp add: ctx_ok_def Let_def)
  have wfr: \<open>frag_sort (SmtDef_ret (?ds ! unat d))\<close> \<open>\<forall>x \<in> set (SmtDef_params (?ds ! unat d)). frag_sort x\<close>
    using ctx_ok_wf_sorts(2)[OF 5(4)] frag_of_wf[OF fr] dn(2) by (meson nth_mem)+
  have nw: \<open>(smt_width s + 1) ^ 3 \<le> smt_node_weight ?fs (take n ?ds) ps (SmtTerm_Def d args) args\<close>
    by (rule node_weight_leaf[OF 5(5)])
  show ?case
  proof (cases \<open>SmtDef_params (?ds ! unat d) = []\<close>)
    case True
    have res: \<open>S' = S\<close> \<open>t' = tref (dm ! unat d)\<close> using 5(3) True by auto
    have r: \<open>ref_ok ws vs S (dm ! unat d) (SmtDef_ret (?ds ! unat d)) ((?dv ! unat d) [])\<close>
      using 5(4) dn True unfolding ctx_ok_def Let_def by blast
    have Df5: \<open>\<exists>e. Df = def_widths ws [] S @ e\<close> using 5(12) res by simp
    have \<open>term_weight ws Df t' = (sort_width_m s + 1) ^ 3\<close> using tw_ref[OF r Df5] res d(3) by simp
    then show ?thesis using nw cube8[of s] res by simp
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
      using tr_term_args_correct(2)[OF r 5(4) d(2) 5(6,7,8,9,10) len1] .
    obtain E1 where E1: \<open>S1 = S @ E1\<close> using A by blast
    have la: \<open>length args = length (SmtDef_params (?ds ! unat d))\<close> using d(2) by (metis length_map)
    have ctx1: \<open>ctx_ok p I ws vs (unat d) dm S1\<close> using ctx_ok_mono[OF ctx_ok_ext[OF 5(4), of E1]] E1 dn(1) by simp
    have tb: \<open>smt_tsort ?fs (take (unat d) ?ds) (SmtDef_params (?ds ! unat d)) (SmtDef_body (?ds ! unat d)) = Some (SmtDef_ret (?ds ! unat d))\<close>
      using ctx_ok_wf_sorts(3)[OF 5(4)] dn(2) by blast
    have Df1: \<open>\<exists>e. Df = def_widths ws [] S1 @ e\<close> using df_prefix[OF 5(12) E2] .
    have IA: \<open>sum_list (map (term_weight ws Df) (drop (length S) S1)) \<le> 40 * sum_list (map (smt_weight ?fs (take n ?ds) ps) args)\<close>
      using 5(1)[OF False dn(1) r 5(4) d(2) 5(6,7,8,9,10) len1 Df1] .
    have IB: \<open>sum_list (map (term_weight ws Df) (drop (length S1) S')) + term_weight ws Df t' \<le>
        40 * smt_weight ?fs (take (unat d) ?ds) (SmtDef_params (?ds ! unat d)) (SmtDef_body (?ds ! unat d))\<close>
      using 5(2)[of \<open>(S1, ks1)\<close> S' t' \<open>SmtDef_params (?ds ! unat d)\<close> \<open>SmtDef_ret (?ds ! unat d)\<close> ?xs'] False dn(1) r res ctx1 tb wfr(2)
        A la 5(11,12) by auto
    have sp: \<open>drop (length S) S' = drop (length S) S1 @ drop (length S1) S'\<close> using E1 E2 by simp
    have W: \<open>smt_weight ?fs (take n ?ds) ps (SmtTerm_Def d args) =
        smt_node_weight ?fs (take n ?ds) ps (SmtTerm_Def d args) args + sum_list (map (smt_weight ?fs (take n ?ds) ps) args) +
        smt_weight ?fs (take (unat d) ?ds) (SmtDef_params (?ds ! unat d)) (SmtDef_body (?ds ! unat d))\<close>
      using dn False by (simp add: min_def)
    show ?thesis using IA IB sp W by simp
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
    using tr_term_args_correct(2)[OF r 6(3) m 6(5,6,7,8,9)] res 6(10) by simp
  have C: \<open>(\<exists>E. S' = S @ E) \<and> defs_wt ws [] S' \<and> wt ws (def_widths ws [] S') t' \<and>
     width ws (def_widths ws [] S') t' = sort_width_m s \<and>
     eval ws (def_widths ws [] S') vs (def_values ws [] vs [] S') t' = enc (smt_eval I ?dv xs (SmtTerm_App op args))\<close>
    using tr_term_args_correct(1)[OF 6(2,3,4,5,6,7,8,9,10)] .
  have wd: \<open>width ws Df t' = sort_width_m s\<close> using df_width[OF 6(11)] C by simp
  have len6: \<open>length S1 < 2 ^ 64\<close> using 6(10) res by simp
  have Df6: \<open>\<exists>e. Df = def_widths ws [] S1 @ e\<close> using 6(11) res by simp
  have IA: \<open>sum_list (map (term_weight ws Df) (drop (length S) S1)) \<le> 40 * sum_list (map (smt_weight ?fs (take n ?ds) ps) args)\<close>
    using 6(1)[OF r 6(3) m 6(5,6,7,8,9) len6 Df6] .
  have lk: \<open>length ks1 = length ?ss\<close> using A by simp
  have kw: \<open>\<forall>k \<in> set ks1. k < 2 ^ 64\<close> using A by (auto simp: in_set_conv_nth ref_ok_def)
  have D: \<open>map (\<lambda>k. (Df ! k + 1) ^ 3) ks1 = map (\<lambda>x. (sort_width_m x + 1) ^ 3) ?ss\<close>
  proof (rule nth_equalityI)
    show \<open>length (map (\<lambda>k. (Df ! k + 1) ^ 3) ks1) = length (map (\<lambda>x. (sort_width_m x + 1) ^ 3) ?ss)\<close> using lk by simp
  next
    fix i assume \<open>i < length (map (\<lambda>k. (Df ! k + 1) ^ 3) ks1)\<close>
    then have i: \<open>i < length args\<close> using A by simp
    then have \<open>ref_ok ws vs S1 (ks1 ! i) (?ss ! i) (smt_eval I ?dv xs (args ! i))\<close> using A by blast
    then have \<open>Df ! (ks1 ! i) = sort_width_m (?ss ! i)\<close> using df_nth[OF 6(11)] res by (simp add: ref_ok_def)
    then show \<open>map (\<lambda>k. (Df ! k + 1) ^ 3) ks1 ! i = map (\<lambda>x. (sort_width_m x + 1) ^ 3) ?ss ! i\<close> using i A by simp
  qed
  have L: \<open>term_weight ws Df t' \<le> (sort_width_m s + 1) ^ 3 + 4 * (length args + 1) ^ 2 * (8 + sum_list (map (\<lambda>x. (sort_width_m x + 1) ^ 3) ?ss))\<close>
    using app_weight[OF _ kw, of op ws Df] sop_ar_sort[OF o(2)] lk wd res D A by simp
  have Ws: \<open>map (\<lambda>a. smt_wcube (smt_tsort ?fs (take n ?ds) ps a) ^ 3) args = map (\<lambda>y. smt_wcube (Some y) ^ 3) ?ss\<close>
    using map_some_eq[OF m, of \<open>\<lambda>z. smt_wcube z ^ 3\<close>] .
  have NW: \<open>smt_node_weight ?fs (take n ?ds) ps (SmtTerm_App op args) args =
      (length args + 1) ^ 2 * ((smt_width s + 1) ^ 3 + sum_list (map (\<lambda>x. (smt_width x + 1) ^ 3) ?ss))\<close>
    unfolding smt_node_weight_def Ws using 6(4) by (simp add: wcube_Some)
  have X: \<open>sum_list (map (\<lambda>x. (sort_width_m x + 1) ^ 3) ?ss) \<le> 8 * sum_list (map (\<lambda>x. (smt_width x + 1) ^ 3) ?ss)\<close>
  proof -
    have \<open>sum_list (map (\<lambda>x. (sort_width_m x + 1) ^ 3) ?ss) \<le> sum_list (map (\<lambda>x. 8 * (smt_width x + 1) ^ 3) ?ss)\<close>
      by (rule sum_list_mono) (rule cube8)
    then show ?thesis by (simp add: sum_list_const_mult comp_def)
  qed
  have c1: \<open>1 \<le> (smt_width s + 1) ^ 3\<close> by simp
  have n1: \<open>1 \<le> (length args + 1) ^ 2\<close> by simp
  have \<open>term_weight ws Df t' \<le> 40 * ((length args + 1) ^ 2 * ((smt_width s + 1) ^ 3 + sum_list (map (\<lambda>x. (smt_width x + 1) ^ 3) ?ss)))\<close>
    using order_trans[OF L arith_app[OF cube8[of s] c1 n1 X]] .
  then have \<open>term_weight ws Df t' \<le> 40 * smt_node_weight ?fs (take n ?ds) ps (SmtTerm_App op args) args\<close>
    using NW by simp
  then show ?case using IA res by simp
next
  case (7 p dm env n S S' ks ps ss xs)
  then show ?case by simp
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
    using tr_term_args_correct(1)[OF r1 8(4) ss(2) 8(6,7,8,9,10) len1] .
  have hs: \<open>smt_has_sort s0 (smt_eval I (smt_def_sems I (SmtProblem_defs p)) xs a)\<close>
    using val_sort[OF 8(4) ss(2)] 8(6) la2_of_refs[OF 8(8,9)] wf_of_frag by blast
  have refa: \<open>ref_ok ws vs (S1 @ [t1]) (length S1) s0 (smt_eval I (smt_def_sems I (SmtProblem_defs p)) xs a)\<close>
    using A hs len1 by (simp add: ref_ok_def def_snoc)
  have dw1: \<open>defs_wt ws [] (S1 @ [t1])\<close> using A by (simp add: def_snoc)
  obtain E1 where E1: \<open>S1 = S @ E1\<close> using A by blast
  have ctx1: \<open>ctx_ok p I ws vs n dm (S1 @ [t1])\<close> using ctx_ok_ext[OF 8(4), of \<open>E1 @ [t1]\<close>] E1 by simp
  have env1: \<open>\<forall>i < length ps. ref_ok ws vs (S1 @ [t1]) (env ! i) (ps ! i) (xs ! i)\<close>
    using 8(9) ref_ok_ext[of ws vs S _ _ _ \<open>E1 @ [t1]\<close>] E1 by simp
  have Df1: \<open>\<exists>e. Df = def_widths ws [] S1 @ e\<close> using df_prefix[OF 8(12)] res E2 by simp
  have IA: \<open>sum_list (map (term_weight ws Df) (drop (length S) S1)) + term_weight ws Df t1 \<le>
      40 * smt_weight (SmtProblem_funs p) (take n (SmtProblem_defs p)) ps a\<close>
    using 8(1)[OF r1 8(4) ss(2) 8(6,7,8,9,10) len1 Df1] .
  have IB: \<open>sum_list (map (term_weight ws Df) (drop (length (S1 @ [t1])) S2)) \<le>
      40 * sum_list (map (smt_weight (SmtProblem_funs p) (take n (SmtProblem_defs p)) ps) rest)\<close>
    using 8(2)[of \<open>(S1, t1)\<close> S2 ks2 ps ss' xs] r1 r2 ctx1 ss(3) 8(6,7,8) env1 dw1 res 8(11,12) by auto
  have sp: \<open>drop (length S) S2 = drop (length S) S1 @ [t1] @ drop (length (S1 @ [t1])) S2\<close> using E1 E2 by simp
  show ?case using IA IB sp res by simp
qed

subsection \<open>The whole translation\<close>

text \<open>\<^const>\<open>smt_size_bound\<close> without the factor \<open>10^9\<close>, and its weights of the definitions and of
  the assertions.\<close>
definition smt_dw :: \<open>SmtProblem \<Rightarrow> nat\<close> where
  \<open>smt_dw p \<equiv> sum_list (map (\<lambda>d. if SmtDef_params (SmtProblem_defs p ! d) = []
                              then smt_weight (SmtProblem_funs p) (take d (SmtProblem_defs p)) [] (SmtDef_body (SmtProblem_defs p ! d))
                              else 0) [0..<length (SmtProblem_defs p)])\<close>

definition smt_aw :: \<open>SmtProblem \<Rightarrow> nat\<close> where
  \<open>smt_aw p \<equiv> sum_list (map (smt_weight (SmtProblem_funs p) (SmtProblem_defs p) []) (SmtProblem_asserts p))\<close>

definition smt_sx :: \<open>SmtProblem \<Rightarrow> nat\<close> where
  \<open>smt_sx p \<equiv> 1 + length (SmtProblem_funs p) + length (SmtProblem_defs p) + length (SmtProblem_asserts p) +
     sum_list (map (\<lambda>f. smt_width (SmtFun_ret f) + 1) (SmtProblem_funs p)) + smt_dw p + smt_aw p\<close>

lemma smt_sx_lt: \<open>smt_sizes_ok p \<Longrightarrow> smt_sx p < 18446744074\<close>
proof -
  assume \<open>smt_sizes_ok p\<close>
  moreover have \<open>smt_size_bound p = 1000000000 * smt_sx p\<close>
    by (simp add: smt_size_bound_def smt_sx_def smt_dw_def smt_aw_def Let_def)
  ultimately show ?thesis by (simp add: smt_sizes_ok_def)
qed

lemma tsize_le: \<open>tsize p \<le> length (SmtProblem_defs p) + smt_dw p + smt_aw p\<close>
proof -
  let ?ds = \<open>SmtProblem_defs p\<close> and ?fs = \<open>SmtProblem_funs p\<close>
  let ?g = \<open>\<lambda>d. if SmtDef_params (?ds ! d) = [] then smt_weight ?fs (take d ?ds) [] (SmtDef_body (?ds ! d)) else 0\<close>
  have 1: \<open>sum_list (map (\<lambda>d. if SmtDef_params (?ds ! d) = [] then Suc (cnt p d (SmtDef_body (?ds ! d))) else 0) [0..<length ?ds])
      \<le> sum_list (map (\<lambda>d. 1 + ?g d) [0..<length ?ds])\<close>
  proof (rule sum_list_mono)
    fix d assume \<open>d \<in> set [0..<length ?ds]\<close>
    then have \<open>d \<le> length ?ds\<close> by simp
    then show \<open>(if SmtDef_params (?ds ! d) = [] then Suc (cnt p d (SmtDef_body (?ds ! d))) else 0) \<le> 1 + ?g d\<close>
      using cnt_le_weight(1)[of d p \<open>SmtDef_body (?ds ! d)\<close> \<open>[]\<close>] by simp
  qed
  have 2: \<open>sum_list (map (cnt p (length ?ds)) (SmtProblem_asserts p)) \<le> sum_list (map (smt_weight ?fs ?ds []) (SmtProblem_asserts p))\<close>
    by (rule sum_list_mono) (use cnt_le_weight(1)[of \<open>length ?ds\<close> p] in simp)
  have 3: \<open>sum_list (map (\<lambda>d. 1 + ?g d) [0..<length ?ds]) = length ?ds + sum_list (map ?g [0..<length ?ds])\<close>
    by (simp add: sum_list_Suc)
  show ?thesis using 1 2 3 by (simp add: tsize_def smt_dw_def smt_aw_def)
qed

definition dflt :: \<open>SmtSort \<Rightarrow> sval\<close> where
  \<open>dflt s \<equiv> case s of SmtSort_Bool \<Rightarrow> VBool False | SmtSort_BitVec w \<Rightarrow> VBv (unat w) 0 | SmtSort_Uninterpreted u \<Rightarrow> VElem 0\<close>

lemma dflt_sort: \<open>smt_has_sort s (dflt s)\<close>
  by (cases s) (simp_all add: dflt_def)

lemma defs_weight:
  assumes c0: \<open>ctx_ok p I ws vs 0 [] []\<close> and len: \<open>length (fst (tr_defs_m p)) < 2 ^ 64\<close>
    and Df: \<open>\<exists>e. Df = def_widths ws [] (fst (tr_defs_m p)) @ e\<close>
  shows \<open>k \<le> length (SmtProblem_defs p) \<Longrightarrow>
    sum_list (map (term_weight ws Df) (fst (foldl (tr_defs_step p) ([], []) [0..<k]))) \<le>
    40 * sum_list (map (\<lambda>d. if SmtDef_params (SmtProblem_defs p ! d) = []
      then smt_weight (SmtProblem_funs p) (take d (SmtProblem_defs p)) [] (SmtDef_body (SmtProblem_defs p ! d)) else 0) [0..<k])\<close>
proof (induction k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  let ?ds = \<open>SmtProblem_defs p\<close> and ?fs = \<open>SmtProblem_funs p\<close>
  obtain S dm where st: \<open>foldl (tr_defs_step p) ([], []) [0..<k] = (S, dm)\<close>
    by (cases \<open>foldl (tr_defs_step p) ([], []) [0..<k]\<close>)
  have kd: \<open>k < length ?ds\<close> using Suc.prems by simp
  have IH: \<open>sum_list (map (term_weight ws Df) S) \<le> 40 * sum_list (map (\<lambda>d. if SmtDef_params (?ds ! d) = []
      then smt_weight ?fs (take d ?ds) [] (SmtDef_body (?ds ! d)) else 0) [0..<k])\<close> using Suc kd st by simp
  have C: \<open>ctx_ok p I ws vs k dm S\<close> \<open>defs_wt ws [] S\<close> using tr_defs_correct[OF c0 _ len, of k] kd st by auto
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
    obtain E where E: \<open>fst (tr_defs_m p) = S1 @ ([t1] @ E)\<close> using fin stp by auto
    have len1: \<open>length S1 < 2 ^ 64\<close> using E len by simp
    have tb: \<open>smt_tsort ?fs (take k ?ds) [] (SmtDef_body (?ds ! k)) = Some (SmtDef_ret (?ds ! k))\<close>
      using ctx_ok_wf_sorts(3)[OF C(1)] kd True by metis
    have Df1: \<open>\<exists>e. Df = def_widths ws [] S1 @ e\<close> using df_prefix[OF Df E] .
    have W: \<open>sum_list (map (term_weight ws Df) (drop (length S) S1)) + term_weight ws Df t1 \<le>
        40 * smt_weight ?fs (take k ?ds) [] (SmtDef_body (?ds ! k))\<close>
      using tr_weight(1)[where xs = \<open>[]\<close>, OF r C(1) tb _ _ _ _ C(2) len1 Df1] by simp
    obtain E1 where E1: \<open>S1 = S @ E1\<close> using tr_prefix(1)[OF r] by blast
    show ?thesis using IH W un stp E1 True by simp
  next
    case False
    have stp: \<open>tr_defs_step p (S, dm) k = (S, dm @ [0])\<close> using False by (simp add: tr_defs_step_def)
    show ?thesis using IH un stp False by simp
  qed
qed

lemma asserts_weight:
  assumes \<open>ctx_ok p I ws vs (length (SmtProblem_defs p)) dm S\<close> \<open>defs_wt ws [] S\<close>
    \<open>\<forall>a \<in> set ass. smt_tsort (SmtProblem_funs p) (SmtProblem_defs p) [] a = Some SmtSort_Bool\<close>
    \<open>foldl (tr_asserts_step p dm) (S, acc) ass = (S', acc')\<close> \<open>length S' < 2 ^ 64\<close>
    \<open>\<exists>e. Df = def_widths ws [] S' @ e\<close>
  shows \<open>sum_list (map (term_weight ws Df) S') + sum_list (map (term_weight ws Df) acc') \<le>
    sum_list (map (term_weight ws Df) S) + sum_list (map (term_weight ws Df) acc) +
    40 * sum_list (map (smt_weight (SmtProblem_funs p) (SmtProblem_defs p) []) ass)\<close>
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
  obtain E2 where E2: \<open>S' = S1 @ E2\<close> using tr_prefix_asserts[OF f] by blast
  have len1: \<open>length S1 < 2 ^ 64\<close> using E2 Cons.prems(5) by simp
  have A: \<open>defs_wt ws [] S1\<close>
    using tr_term_args_correct(1)[OF r Cons.prems(1) ta, of \<open>[]\<close>] Cons.prems(2) len1 by simp
  have ctx1: \<open>ctx_ok p I ws vs (length (SmtProblem_defs p)) dm S1\<close> using ctx_ok_ext[OF Cons.prems(1)] E1 by simp
  have Df1: \<open>\<exists>e. Df = def_widths ws [] S1 @ e\<close> using df_prefix[OF Cons.prems(6) E2] .
  have W: \<open>sum_list (map (term_weight ws Df) (drop (length S) S1)) + term_weight ws Df t1 \<le>
      40 * smt_weight (SmtProblem_funs p) (take (length (SmtProblem_defs p)) (SmtProblem_defs p)) [] a\<close>
    using tr_weight(1)[where xs = \<open>[]\<close>, OF r Cons.prems(1) ta _ _ _ _ Cons.prems(2) len1 Df1] by simp
  have IH: \<open>sum_list (map (term_weight ws Df) S') + sum_list (map (term_weight ws Df) acc') \<le>
      sum_list (map (term_weight ws Df) S1) + sum_list (map (term_weight ws Df) (acc @ [t1])) +
      40 * sum_list (map (smt_weight (SmtProblem_funs p) (SmtProblem_defs p) []) ass)\<close>
    using Cons.IH[OF ctx1 A _ f Cons.prems(5,6)] Cons.prems(3) by simp
  show ?case using IH W E1 by simp
qed

lemma tr_asserts_len: \<open>length (snd (foldl (tr_asserts_step p dm) (S, acc) ass)) = length acc + length ass\<close>
  by (induction ass arbitrary: S acc) (simp_all add: tr_asserts_step_def Let_def)

theorem tr_size_bound:
  assumes \<open>smt_wf p\<close> \<open>smt_fragment p\<close> \<open>smt_sizes_ok p\<close>
  shows \<open>tsize p < 2 ^ 63\<close> and \<open>size_bound (tr_problem_m p) < 2 ^ 63\<close>
proof -
  let ?fs = \<open>SmtProblem_funs p\<close> and ?ds = \<open>SmtProblem_defs p\<close> and ?as = \<open>SmtProblem_asserts p\<close>
  have smt_sx: \<open>smt_sx p < 18446744074\<close> using smt_sx_lt assms(3) .
  have ts: \<open>tsize p \<le> length ?ds + smt_dw p + smt_aw p\<close> by (rule tsize_le)
  show T: \<open>tsize p < 2 ^ 63\<close> using ts smt_sx by (simp add: smt_sx_def)
  define I0 where \<open>I0 = (\<lambda>f (xs :: sval list). dflt (SmtFun_ret (?fs ! f)))\<close>
  define vs0 where \<open>vs0 = map (\<lambda>f. enc (I0 f [])) [0..<length ?fs]\<close>
  define ws0 where \<open>ws0 = map (\<lambda>f. sort_width_m (SmtFun_ret f)) ?fs\<close>
  have isd: \<open>interp_sound ?fs I0\<close> by (simp add: interp_sound_def I0_def dflt_sort)
  have lvs: \<open>length vs0 = length ?fs\<close> \<open>\<forall>f < length ?fs. vs0 ! f = enc (I0 f [])\<close> by (simp_all add: vs0_def)
  have lenT: \<open>length (fst (tr_asserts_m p (tr_defs_m p))) < 2 ^ 64\<close> using T tsize_length[of p] by simp
  have c0: \<open>ctx_ok p I0 ws0 vs0 0 [] []\<close> using assms(1,2) isd lvs by (simp add: ctx_ok_def Let_def ws0_def)
  have vw: \<open>var_widths (tr_problem_m p) = ws0\<close>
    using tr_problem_sem[OF assms(1,2) isd lvs lenT] by (simp add: ws0_def)
  obtain S0 dm where d: \<open>tr_defs_m p = (S0, dm)\<close> by (cases \<open>tr_defs_m p\<close>)
  obtain S' ts where a: \<open>tr_asserts_m p (S0, dm) = (S', ts)\<close> by (cases \<open>tr_asserts_m p (S0, dm)\<close>)
  have af: \<open>foldl (tr_asserts_step p dm) (S0, []) ?as = (S', ts)\<close> using a by (simp add: tr_asserts_m_step)
  have lenS': \<open>length S' < 2 ^ 64\<close> using lenT d a by simp
  obtain E where E: \<open>S' = S0 @ E\<close> using tr_prefix_asserts[OF af] by blast
  have len0: \<open>length (fst (tr_defs_m p)) < 2 ^ 64\<close> using lenS' E d by simp
  have D: \<open>ctx_ok p I0 ws0 vs0 (length ?ds) dm S0 \<and> defs_wt ws0 [] S0\<close>
    using tr_defs_correct[OF c0 le_refl len0] d by (simp add: tr_defs_m_step)
  define Df where \<open>Df = def_widths ws0 [] S'\<close>
  have Dfa: \<open>\<exists>e. Df = def_widths ws0 [] S' @ e\<close> by (simp add: Df_def)
  have Df0: \<open>\<exists>e. Df = def_widths ws0 [] (fst (tr_defs_m p)) @ e\<close> using df_prefix[OF Dfa E] d by simp
  have wsA: \<open>\<forall>a \<in> set ?as. smt_tsort ?fs ?ds [] a = Some SmtSort_Bool\<close> using assms(1) by (simp add: smt_wf_def Let_def)
  have AW: \<open>sum_list (map (term_weight ws0 Df) S') + sum_list (map (term_weight ws0 Df) ts) \<le>
      sum_list (map (term_weight ws0 Df) S0) + 40 * smt_aw p\<close>
    using asserts_weight[OF conjunct1[OF D] conjunct2[OF D] wsA af lenS' Dfa] by (simp add: smt_aw_def)
  have DW: \<open>sum_list (map (term_weight ws0 Df) S0) \<le> 40 * smt_dw p\<close>
    using defs_weight[OF c0 len0 Df0, of \<open>length ?ds\<close>] d by (simp add: tr_defs_m_step smt_dw_def)
  have q: \<open>Problem_defs (tr_problem_m p) = S'\<close> \<open>Problem_asserts (tr_problem_m p) = ts\<close>
    by (simp_all add: tr_problem_m_def d a Let_def)
  have lts: \<open>length ts = length ?as\<close> using tr_asserts_len[of p dm S0 \<open>[]\<close> ?as] af by simp
  have lS: \<open>length S' = tsize p\<close> using tsize_length[of p] d a by simp
  have sws: \<open>sum_list ws0 \<le> sum_list (map (\<lambda>f. smt_width (SmtFun_ret f) + 1) ?fs)\<close>
    unfolding ws0_def by (rule sum_list_mono) (rule sort_width_le)
  have lws: \<open>length ws0 = length ?fs\<close> by (simp add: ws0_def)
  have sb: \<open>size_bound (tr_problem_m p) = 1000000 * (1 + sum_list ws0 + length ws0 + length S' + length ts +
      (sum_list (map (term_weight ws0 Df) S') + sum_list (map (term_weight ws0 Df) ts)))\<close>
    by (simp add: size_bound_def vw q Df_def Let_def)
  have \<open>1 + sum_list ws0 + length ws0 + length S' + length ts +
      (sum_list (map (term_weight ws0 Df) S') + sum_list (map (term_weight ws0 Df) ts)) \<le> 41 * smt_sx p\<close>
    using AW DW sws lws lS lts ts by (simp add: smt_sx_def)
  then show \<open>size_bound (tr_problem_m p) < 2 ^ 63\<close> using sb smt_sx by simp
qed

end
