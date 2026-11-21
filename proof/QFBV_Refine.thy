theory QFBV_Refine
  imports QFBV_Defs
begin

section \<open>The Rust functions compute their models\<close>

lemma unat_word_Suc_simp:
  fixes x :: \<open>64 word\<close>
  assumes \<open>unat x < 18446744073709551615\<close>
  shows \<open>unat (x + 1) = Suc (unat x)\<close>
proof -
  have \<open>unat x + unat (1 :: 64 word) < 2 ^ LENGTH(64)\<close> using assms by simp
  then have \<open>unat (x + 1) = unat x + unat (1 :: 64 word)\<close> using unat_add_lem by blast
  then show ?thesis by simp
qed

section \<open>Pure facts about the models\<close>

subsection \<open>Words\<close>

lemma word_mod2_eq1:
  fixes x :: \<open>64 word\<close>
  shows \<open>(x mod 2 = 1) = (unat x mod 2 = 1)\<close>
  by (simp add: word_unat_eq_iff unat_mod)

lemma div_2_pow_Suc: \<open>(n::nat) div 2 ^ i div 2 = n div 2 ^ Suc i\<close>
  by (metis div_mult2_eq power_Suc2)

lemma unat_sub_not_less:
  fixes i j :: \<open>64 word\<close>
  shows \<open>\<not> unat j < unat i \<Longrightarrow> unat (j - i) = unat j - unat i\<close>
  by (simp add: unat_sub word_le_nat_alt)

lemma unat_add_less_len:
  fixes j s :: \<open>64 word\<close>
  assumes \<open>unat s < n - unat j\<close> \<open>n < 2 ^ 64\<close>
  shows \<open>unat (j + s) = unat j + unat s\<close>
proof -
  have \<open>unat j + unat s < 2 ^ LENGTH(64)\<close> using assms by simp
  then show ?thesis using unat_add_lem by blast
qed

lemma unat_len_minus:
  fixes j :: \<open>64 word\<close>
  shows \<open>unat j < n \<Longrightarrow> n < 2 ^ 64 \<Longrightarrow> unat (word_of_nat n - j) = n - unat j\<close>
  by (subst unat_sub) (simp_all add: word_le_nat_alt unat_of_nat_eq)

lemma unat_double:
  \<open>n + n < 2 ^ 64 \<Longrightarrow> unat (word_of_nat n + word_of_nat n :: 64 word) = n + n\<close>
  by (simp add: unat_of_nat_eq flip: of_nat_add)

lemma unat_lt_2p64: \<open>unat (x :: 64 word) < 18446744073709551616\<close>
  using unat_lt2p[of x] by simp

lemma unat_of_nat_64: \<open>n < 18446744073709551616 \<Longrightarrow> unat (word_of_nat n :: 64 word) = n\<close>
  by (simp add: unat_of_nat_eq)

lemma unat_double2:
  assumes \<open>n < 9223372036854775808\<close>
  shows \<open>unat (2 * word_of_nat n :: 64 word) = n + n\<close>
proof -
  have \<open>n + n < 18446744073709551616\<close> using assms by linarith
  then have u: \<open>unat (word_of_nat (n + n) :: 64 word) = n + n\<close> by (rule unat_of_nat_64)
  have \<open>(2 * word_of_nat n :: 64 word) = word_of_nat (n + n)\<close> by (simp only: of_nat_add mult_2)
  then show ?thesis using u by (simp only:)
qed

subsection \<open>Folds over \<open>[0..<n]\<close>\<close>

lemma foldl_upt_mono:
  assumes \<open>\<And>x i. g x \<le> (g (f x i) :: nat)\<close> \<open>m \<le> n\<close>
  shows \<open>g (foldl f x [0..<m]) \<le> g (foldl f x [0..<n])\<close>
  using assms(2)
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases \<open>m = Suc n\<close>)
    case True
    then show ?thesis by simp
  next
    case False
    with Suc.prems have \<open>m \<le> n\<close> by simp
    then have \<open>g (foldl f x [0..<m]) \<le> g (foldl f x [0..<n])\<close> by (rule Suc.IH)
    also have \<open>\<dots> \<le> g (foldl f x [0..<Suc n])\<close> using assms(1) by simp
    finally show ?thesis .
  qed
qed

subsection \<open>Gates\<close>

text \<open>The size of a state: its variables and its clauses. Every model only adds variables and
  clauses, so the size of the final state bounds the counter of variables and the vector of
  clauses at every step before it.\<close>
definition sz :: \<open>st \<Rightarrow> nat\<close> where
  \<open>sz s \<equiv> fst s + length (snd s)\<close>

lemma sz_simps [simp]:
  \<open>sz (n, cs) = n + length cs\<close>
  \<open>sz (addc_m s c) = Suc (sz s)\<close>
  by (simp_all add: sz_def addc_m_def)

text \<open>A state whose variables and clauses fit: its size is below \<open>2^56\<close>.\<close>
definition room :: \<open>st \<Rightarrow> bool\<close> where
  \<open>room s \<equiv> sz s < 2 ^ 56\<close>

lemma room_mono: \<open>sz s \<le> sz s' \<Longrightarrow> room s' \<Longrightarrow> room s\<close>
  by (simp add: room_def)

lemma room_bounds:
  \<open>room s \<Longrightarrow> fst s < 18446744073709551616\<close>
  \<open>room s \<Longrightarrow> Suc (fst s) < 18446744073709551616\<close>
  \<open>room s \<Longrightarrow> length (snd s) < 72057594037927936\<close>
  by (simp_all add: room_def sz_def)

lemma fresh_m_fst [simp]: \<open>fst (fresh_m s) = (Suc (fst s), snd s)\<close>
  by (simp add: fresh_m_def)

lemma fresh_m_snd [simp]: \<open>snd (fresh_m s) = make_Lit (word_of_nat (fst s)) False\<close>
  by (simp add: fresh_m_def)

lemma addc_m_simps [simp]: \<open>fst (addc_m s c) = fst s\<close> \<open>snd (addc_m s c) = snd s @ [c]\<close>
  by (simp_all add: addc_m_def)

lemma and_t_count [simp]: \<open>fst (fst (and_t s a b)) = Suc (fst s)\<close> \<open>sz (fst (and_t s a b)) = sz s + 4\<close>
  by (simp_all add: and_t_def fresh_m_def sz_def)

lemma xor_t_count [simp]: \<open>fst (fst (xor_t s a b)) = Suc (fst s)\<close> \<open>sz (fst (xor_t s a b)) = sz s + 5\<close>
  by (simp_all add: xor_t_def fresh_m_def sz_def)

lemma ite_t_count [simp]: \<open>fst (fst (ite_t s c a b)) = Suc (fst s)\<close> \<open>sz (fst (ite_t s c a b)) = sz s + 5\<close>
  by (simp_all add: ite_t_def fresh_m_def sz_def)

lemma or_m_fst [simp]: \<open>fst (or_m s a b) = fst (and_m s (lneg a) (lneg b))\<close>
  by (simp add: or_m_def split_def Let_def)

lemma or_m_snd [simp]: \<open>snd (or_m s a b) = lneg (snd (and_m s (lneg a) (lneg b)))\<close>
  by (simp add: or_m_def split_def Let_def)

text \<open>The gates do not decrease the number of variables.\<close>

lemma and_m_count [simp]: \<open>sz s \<le> sz (fst (and_m s a b))\<close>
  by (simp add: and_m_def)

lemma xor_m_count [simp]: \<open>sz s \<le> sz (fst (xor_m s a b))\<close>
  by (simp add: xor_m_def)

lemma ite_m_count [simp]: \<open>sz s \<le> sz (fst (ite_m s c a b))\<close>
  using and_m_count[of s] xor_m_count[of s] by (auto simp: ite_m_def split_def Let_def intro: order_trans)

lemma bitw_m_count [simp]: \<open>sz s \<le> sz (fst (bitw_m op s a b))\<close>
  by (cases op) (simp_all add: bitw_m_def)

text \<open>A loop whose steps do not decrease the number of variables.\<close>

lemma foldl_count_mono:
  fixes f :: \<open>st \<times> 'b \<Rightarrow> 'c \<Rightarrow> st \<times> 'b\<close>
  assumes \<open>\<And>X k. sz (fst X) \<le> sz (fst (f X k))\<close>
  shows \<open>sz (fst X) \<le> sz (fst (foldl f X xs))\<close>
proof (induction xs arbitrary: X)
  case (Cons y ys)
  show ?case using order_trans[OF assms[of X y] Cons.IH[of \<open>f X y\<close>]] by simp
qed simp

lemma foldl_upt_count_mono:
  fixes f :: \<open>st \<times> 'b \<Rightarrow> nat \<Rightarrow> st \<times> 'b\<close>
  assumes \<open>\<And>X k. sz (fst X) \<le> sz (fst (f X k))\<close> \<open>i \<le> j\<close>
  shows \<open>sz (fst (foldl f X [0..<i])) \<le> sz (fst (foldl f X [0..<j]))\<close>
  using assms(2)
proof (induction j)
  case (Suc j)
  show ?case
  proof (cases \<open>i = Suc j\<close>)
    case False
    then have \<open>i \<le> j\<close> using Suc.prems by simp
    then show ?thesis using order_trans[OF Suc.IH assms(1)[of \<open>foldl f X [0..<j]\<close> j]] by simp
  qed simp
qed simp

subsection \<open>Circuits: the loops as folds of named steps\<close>

lemma const_m_length [simp]: \<open>length (const_m bs) = length bs\<close>
  by (simp add: const_m_def)

lemma of_nat_m_length [simp]: \<open>length (of_nat_m v w) = w\<close>
  by (simp add: of_nat_m_def)

lemma not_m_length [simp]: \<open>length (not_m a) = length a\<close>
  by (simp add: not_m_def)

lemma zext_m_length [simp]: \<open>length (zext_m a w) = w\<close>
  by (simp add: zext_m_def)

lemma shift_const_m_length [simp]: \<open>length (shift_const_m a s left) = length a\<close>
  by (simp add: shift_const_m_def)

lemma extract_m_length [simp]: \<open>length (extract_m a hi lo) = Suc hi - lo\<close>
  by (simp add: extract_m_def del: upt_Suc)

lemma concat_m_length [simp]: \<open>length (concat_m a b) = length a + length b\<close>
  by (simp add: concat_m_def)

lemma fresh_vec_m_simps [simp]:
  \<open>fst (fresh_vec_m s w) = (fst s + w, snd s)\<close>
  \<open>length (snd (fresh_vec_m s w)) = w\<close>
  by (simp_all add: fresh_vec_m_def)

lemma nth_models [simp]:
  \<open>i < w \<Longrightarrow> of_nat_m v w ! i = lconst (v div 2 ^ i mod 2 = 1)\<close>
  \<open>i < w \<Longrightarrow> snd (fresh_vec_m s w) ! i = make_Lit (word_of_nat (fst s + i)) False\<close>
  \<open>i < length bs \<Longrightarrow> const_m bs ! i = lconst (bs ! i)\<close>
  \<open>i < w \<Longrightarrow> zext_m a w ! i = (if i < length a then a ! i else lconst False)\<close>
  \<open>j < length a \<Longrightarrow> shift_const_m a n left ! j =
     (if left then (if j < n then lconst False else a ! (j - n))
      else (if n < length a - j then a ! (j + n) else lconst False))\<close>
  \<open>lo + j < Suc hi \<Longrightarrow> extract_m a hi lo ! j = a ! (lo + j)\<close>
  by (simp_all add: of_nat_m_def fresh_vec_m_def const_m_def zext_m_def shift_const_m_def extract_m_def
      del: upt_Suc)

text \<open>\<^const>\<open>bitwise_m\<close>\<close>

definition bitwise_step :: \<open>BinOp \<Rightarrow> Lit list \<Rightarrow> Lit list \<Rightarrow> st \<times> Lit list \<Rightarrow> nat \<Rightarrow> st \<times> Lit list\<close> where
  \<open>bitwise_step op a b X i \<equiv>
     (fst (bitw_m op (fst X) (a ! i) (b ! i)), snd X @ [snd (bitw_m op (fst X) (a ! i) (b ! i))])\<close>

lemma bitwise_m_foldl: \<open>bitwise_m op s a b = foldl (bitwise_step op a b) (s, []) [0..<length a]\<close>
proof -
  have \<open>(\<lambda>(s, r) i. let (s1, x) = bitw_m op s (a ! i) (b ! i) in (s1, r @ [x])) = bitwise_step op a b\<close>
    by (simp add: fun_eq_iff bitwise_step_def split_def Let_def)
  then show ?thesis by (simp add: bitwise_m_def)
qed

lemma bitwise_step_count: \<open>sz (fst X) \<le> sz (fst (bitwise_step op a b X i))\<close>
  by (simp add: bitwise_step_def)

lemma bitwise_fold_count:
  \<open>length (snd (foldl (bitwise_step op a b) X [0..<n])) = length (snd X) + n\<close>
  by (induction n) (simp_all add: bitwise_step_def)

lemma bitwise_m_count [simp]:
  \<open>sz s \<le> sz (fst (bitwise_m op s a b))\<close>
  \<open>length (snd (bitwise_m op s a b)) = length a\<close>
  using foldl_count_mono[OF bitwise_step_count, where X = \<open>(s, [])\<close>]
  by (simp_all add: bitwise_m_foldl bitwise_fold_count)

lemma bitwise_step_lt:
  \<open>k < length a \<Longrightarrow> sz (fst (foldl (bitwise_step op a b) (s, []) [0..<length a])) < 72057594037927936 \<Longrightarrow>
   sz (fst (bitw_m op (fst (foldl (bitwise_step op a b) (s, []) [0..<k])) (a ! k) (b ! k))) < 72057594037927936\<close>
  using foldl_upt_count_mono[where f = \<open>bitwise_step op a b\<close> and i = \<open>Suc k\<close> and j = \<open>length a\<close> and X = \<open>(s, [])\<close>, OF bitwise_step_count]
  by (simp add: bitwise_step_def)

text \<open>\<^const>\<open>add_m\<close>\<close>

lemma add_step_eq:
  \<open>add_step a b X i =
     (fst (ite_m (fst (xor_m (fst (xor_m (fst X) (a ! i) (b ! i))) (snd (xor_m (fst X) (a ! i) (b ! i)))
                     (snd (snd X))))
            (snd (xor_m (fst X) (a ! i) (b ! i))) (snd (snd X)) (a ! i)),
      fst (snd X) @ [snd (xor_m (fst (xor_m (fst X) (a ! i) (b ! i))) (snd (xor_m (fst X) (a ! i) (b ! i)))
                     (snd (snd X)))],
      snd (ite_m (fst (xor_m (fst (xor_m (fst X) (a ! i) (b ! i))) (snd (xor_m (fst X) (a ! i) (b ! i)))
                     (snd (snd X))))
            (snd (xor_m (fst X) (a ! i) (b ! i))) (snd (snd X)) (a ! i)))\<close>
  by (simp add: add_step_def split_def Let_def)

lemma add_step_count: \<open>sz (fst X) \<le> sz (fst (add_step a b X i))\<close>
  unfolding add_step_eq fst_conv by (meson order_trans xor_m_count ite_m_count)

lemma add_fold_count:
  \<open>length (fst (snd (foldl (add_step a b) X [0..<n]))) = length (fst (snd X)) + n\<close>
  by (induction n) (simp_all add: add_step_eq)

lemma add_m_count [simp]:
  \<open>sz s \<le> sz (fst (add_m s a b c))\<close>
  \<open>length (fst (snd (add_m s a b c))) = length a\<close>
  using foldl_count_mono[OF add_step_count, where X = \<open>(s, [], c)\<close>]
  by (simp_all add: add_m_def add_fold_count)

lemma add_step_lt:
  assumes \<open>k < length a\<close> \<open>sz (fst (foldl (add_step a b) (s, [], c) [0..<length a])) < 72057594037927936\<close>
  shows \<open>sz (fst (ite_m (fst (xor_m (fst (xor_m (fst (foldl (add_step a b) (s, [], c) [0..<k])) (a ! k) (b ! k))) (snd (xor_m (fst (foldl (add_step a b) (s, [], c) [0..<k])) (a ! k) (b ! k))) (snd (snd (foldl (add_step a b) (s, [], c) [0..<k]))))) (snd (xor_m (fst (foldl (add_step a b) (s, [], c) [0..<k])) (a ! k) (b ! k))) (snd (snd (foldl (add_step a b) (s, [], c) [0..<k]))) (a ! k))) < 72057594037927936\<close>
    \<open>sz (fst (xor_m (fst (xor_m (fst (foldl (add_step a b) (s, [], c) [0..<k])) (a ! k) (b ! k))) (snd (xor_m (fst (foldl (add_step a b) (s, [], c) [0..<k])) (a ! k) (b ! k))) (snd (snd (foldl (add_step a b) (s, [], c) [0..<k]))))) < 72057594037927936\<close>
    \<open>sz (fst (xor_m (fst (foldl (add_step a b) (s, [], c) [0..<k])) (a ! k) (b ! k))) < 72057594037927936\<close>
proof -
  have \<open>sz (fst (add_step a b (foldl (add_step a b) (s, [], c) [0..<k]) k)) < 72057594037927936\<close>
    using foldl_upt_count_mono[where f = \<open>add_step a b\<close> and i = \<open>Suc k\<close> and j = \<open>length a\<close>
        and X = \<open>(s, [], c)\<close>, OF add_step_count] assms
    by simp
  then show c3: \<open>sz (fst (ite_m (fst (xor_m (fst (xor_m (fst (foldl (add_step a b) (s, [], c) [0..<k])) (a ! k) (b ! k))) (snd (xor_m (fst (foldl (add_step a b) (s, [], c) [0..<k])) (a ! k) (b ! k))) (snd (snd (foldl (add_step a b) (s, [], c) [0..<k]))))) (snd (xor_m (fst (foldl (add_step a b) (s, [], c) [0..<k])) (a ! k) (b ! k))) (snd (snd (foldl (add_step a b) (s, [], c) [0..<k]))) (a ! k))) < 72057594037927936\<close>
    by (simp add: add_step_eq)
  show c2: \<open>sz (fst (xor_m (fst (xor_m (fst (foldl (add_step a b) (s, [], c) [0..<k])) (a ! k) (b ! k))) (snd (xor_m (fst (foldl (add_step a b) (s, [], c) [0..<k])) (a ! k) (b ! k))) (snd (snd (foldl (add_step a b) (s, [], c) [0..<k]))))) < 72057594037927936\<close> using le_less_trans[OF ite_m_count c3] .
  show \<open>sz (fst (xor_m (fst (foldl (add_step a b) (s, [], c) [0..<k])) (a ! k) (b ! k))) < 72057594037927936\<close> using le_less_trans[OF xor_m_count c2] .
qed

text \<open>\<^const>\<open>partial_m\<close>\<close>

definition partial_step :: \<open>Lit list \<Rightarrow> Lit \<Rightarrow> nat \<Rightarrow> st \<times> Lit list \<Rightarrow> nat \<Rightarrow> st \<times> Lit list\<close> where
  \<open>partial_step a bi i X j \<equiv>
     if j < i then (fst X, snd X @ [lconst False])
     else (fst (and_m (fst X) (a ! (j - i)) bi), snd X @ [snd (and_m (fst X) (a ! (j - i)) bi)])\<close>

lemma partial_m_foldl: \<open>partial_m s a bi i = foldl (partial_step a bi i) (s, []) [0..<length a]\<close>
proof -
  have \<open>(\<lambda>(s, r) j. if j < i then (s, r @ [lconst False])
                    else let (s1, x) = and_m s (a ! (j - i)) bi in (s1, r @ [x])) = partial_step a bi i\<close>
    by (simp add: fun_eq_iff partial_step_def split_def Let_def)
  then show ?thesis by (simp add: partial_m_def)
qed

lemma partial_step_count: \<open>sz (fst X) \<le> sz (fst (partial_step a bi i X j))\<close>
  by (simp add: partial_step_def)

lemma partial_fold_count:
  \<open>length (snd (foldl (partial_step a bi i) X [0..<n])) = length (snd X) + n\<close>
  by (induction n) (auto simp add: partial_step_def)

lemma partial_m_count [simp]:
  \<open>sz s \<le> sz (fst (partial_m s a bi i))\<close>
  \<open>length (snd (partial_m s a bi i)) = length a\<close>
  using foldl_count_mono[OF partial_step_count, where X = \<open>(s, [])\<close>]
  by (simp_all add: partial_m_foldl partial_fold_count)

lemma partial_step_lt:
  assumes \<open>k < length a\<close> \<open>\<not> k < i\<close>
    \<open>sz (fst (foldl (partial_step a bi i) (s, []) [0..<length a])) < 72057594037927936\<close>
  shows \<open>sz (fst (and_m (fst (foldl (partial_step a bi i) (s, []) [0..<k])) (a ! (k - i)) bi)) < 72057594037927936\<close>
  using foldl_upt_count_mono[where f = \<open>partial_step a bi i\<close> and i = \<open>Suc k\<close> and j = \<open>length a\<close>
      and X = \<open>(s, [])\<close>, OF partial_step_count] assms
  by (simp add: partial_step_def)

text \<open>\<^const>\<open>mul_m\<close>\<close>

lemma mul_step_eq:
  \<open>mul_step a b X i =
     (fst (add_m (fst (partial_m (fst X) a (b ! i) i)) (snd X) (snd (partial_m (fst X) a (b ! i) i)) (lconst False)),
      fst (snd (add_m (fst (partial_m (fst X) a (b ! i) i)) (snd X) (snd (partial_m (fst X) a (b ! i) i))
             (lconst False))))\<close>
  by (simp add: mul_step_def split_def Let_def)

lemma mul_step_count: \<open>sz (fst X) \<le> sz (fst (mul_step a b X i))\<close>
  unfolding mul_step_eq fst_conv by (meson order_trans partial_m_count(1) add_m_count(1))

lemma mul_fold_count:
  assumes \<open>length (snd X) = length a\<close>
  shows \<open>length (snd (foldl (mul_step a b) X [0..<m])) = length a\<close>
  by (induction m) (simp_all add: mul_step_eq assms)

lemma mul_fold_count' [simp]:
  \<open>length (snd (foldl (mul_step a b) (s, replicate (length a) x) [0..<m])) = length a\<close>
  using mul_fold_count[of \<open>(s, replicate (length a) x)\<close> a b m] by simp_all

lemma mul_m_count [simp]:
  \<open>sz s \<le> sz (fst (mul_m s a b))\<close>
  \<open>length (snd (mul_m s a b)) = length a\<close>
  using foldl_count_mono[OF mul_step_count, where X = \<open>(s, replicate (length a) (lconst False))\<close>]
  by (simp_all add: mul_m_def)

lemma mul_m_fold:
  \<open>foldl (mul_step a b) (s, replicate (length a) (lconst False)) [0..<length a] = mul_m s a b\<close>
  by (simp add: mul_m_def)

lemma mul_step_lt:
  assumes \<open>k < length a\<close> \<open>sz (fst (mul_m s a b)) < 72057594037927936\<close>
  shows \<open>sz (fst (add_m (fst (partial_m (fst (foldl (mul_step a b) (s, replicate (length a) (lconst False)) [0..<k])) a (b ! k) k)) (snd (foldl (mul_step a b) (s, replicate (length a) (lconst False)) [0..<k])) (snd (partial_m (fst (foldl (mul_step a b) (s, replicate (length a) (lconst False)) [0..<k])) a (b ! k) k)) (lconst False))) < 72057594037927936\<close>
    \<open>sz (fst (partial_m (fst (foldl (mul_step a b) (s, replicate (length a) (lconst False)) [0..<k])) a (b ! k) k)) < 72057594037927936\<close>
proof -
  have \<open>sz (fst (mul_step a b (foldl (mul_step a b) (s, replicate (length a) (lconst False)) [0..<k]) k)) < 72057594037927936\<close>
    using foldl_upt_count_mono[where f = \<open>mul_step a b\<close> and i = \<open>Suc k\<close> and j = \<open>length a\<close>
        and X = \<open>(s, replicate (length a) (lconst False))\<close>, OF mul_step_count] assms
    by (simp add: mul_m_def)
  then show c2: \<open>sz (fst (add_m (fst (partial_m (fst (foldl (mul_step a b) (s, replicate (length a) (lconst False)) [0..<k])) a (b ! k) k)) (snd (foldl (mul_step a b) (s, replicate (length a) (lconst False)) [0..<k])) (snd (partial_m (fst (foldl (mul_step a b) (s, replicate (length a) (lconst False)) [0..<k])) a (b ! k) k)) (lconst False))) < 72057594037927936\<close>
    by (simp add: mul_step_eq)
  show \<open>sz (fst (partial_m (fst (foldl (mul_step a b) (s, replicate (length a) (lconst False)) [0..<k])) a (b ! k) k)) < 72057594037927936\<close> using le_less_trans[OF add_m_count(1) c2] .
qed

text \<open>\<^const>\<open>eq_m\<close>, \<^const>\<open>ult_m\<close>\<close>

lemma eq_step_eq:
  \<open>eq_step a b X i =
     and_m (fst (xor_m (fst X) (a ! i) (b ! i))) (snd X) (lneg (snd (xor_m (fst X) (a ! i) (b ! i))))\<close>
  by (simp add: eq_step_def split_def Let_def)

lemma eq_step_count: \<open>sz (fst X) \<le> sz (fst (eq_step a b X i))\<close>
  unfolding eq_step_eq by (meson order_trans xor_m_count and_m_count)

lemma eq_m_count [simp]: \<open>sz s \<le> sz (fst (eq_m s a b))\<close>
  using foldl_count_mono[OF eq_step_count, where X = \<open>(s, lconst True)\<close>] by (simp add: eq_m_def)

lemma eq_step_lt:
  assumes \<open>k < length a\<close> \<open>sz (fst (foldl (eq_step a b) (s, lconst True) [0..<length a])) < 72057594037927936\<close>
  shows \<open>sz (fst (and_m (fst (xor_m (fst (foldl (eq_step a b) (s, lconst True) [0..<k])) (a ! k) (b ! k))) (snd (foldl (eq_step a b) (s, lconst True) [0..<k])) (lneg (snd (xor_m (fst (foldl (eq_step a b) (s, lconst True) [0..<k])) (a ! k) (b ! k)))))) < 72057594037927936\<close>
    \<open>sz (fst (xor_m (fst (foldl (eq_step a b) (s, lconst True) [0..<k])) (a ! k) (b ! k))) < 72057594037927936\<close>
proof -
  have \<open>sz (fst (eq_step a b (foldl (eq_step a b) (s, lconst True) [0..<k]) k)) < 72057594037927936\<close>
    using foldl_upt_count_mono[where f = \<open>eq_step a b\<close> and i = \<open>Suc k\<close> and j = \<open>length a\<close>
        and X = \<open>(s, lconst True)\<close>, OF eq_step_count] assms
    by simp
  then show c2: \<open>sz (fst (and_m (fst (xor_m (fst (foldl (eq_step a b) (s, lconst True) [0..<k])) (a ! k) (b ! k))) (snd (foldl (eq_step a b) (s, lconst True) [0..<k])) (lneg (snd (xor_m (fst (foldl (eq_step a b) (s, lconst True) [0..<k])) (a ! k) (b ! k)))))) < 72057594037927936\<close>
    by (simp add: eq_step_eq)
  show \<open>sz (fst (xor_m (fst (foldl (eq_step a b) (s, lconst True) [0..<k])) (a ! k) (b ! k))) < 72057594037927936\<close> using le_less_trans[OF and_m_count c2] .
qed

lemma ult_m_fst [simp]: \<open>fst (ult_m s a b) = fst (add_m s a (not_m b) (lconst True))\<close>
  by (simp add: ult_m_def split_def Let_def)

lemma ult_m_snd [simp]: \<open>snd (ult_m s a b) = lneg (snd (snd (add_m s a (not_m b) (lconst True))))\<close>
  by (simp add: ult_m_def split_def Let_def)

text \<open>\<^const>\<open>ite_vec_m\<close>\<close>

definition ite_step :: \<open>Lit \<Rightarrow> Lit list \<Rightarrow> Lit list \<Rightarrow> st \<times> Lit list \<Rightarrow> nat \<Rightarrow> st \<times> Lit list\<close> where
  \<open>ite_step c a b X i \<equiv>
     (fst (ite_m (fst X) c (a ! i) (b ! i)), snd X @ [snd (ite_m (fst X) c (a ! i) (b ! i))])\<close>

lemma ite_vec_m_foldl: \<open>ite_vec_m s c a b = foldl (ite_step c a b) (s, []) [0..<length a]\<close>
proof -
  have \<open>(\<lambda>(s, r) i. let (s1, x) = ite_m s c (a ! i) (b ! i) in (s1, r @ [x])) = ite_step c a b\<close>
    by (simp add: fun_eq_iff ite_step_def split_def Let_def)
  then show ?thesis by (simp add: ite_vec_m_def)
qed

lemma ite_step_count: \<open>sz (fst X) \<le> sz (fst (ite_step c a b X i))\<close>
  by (simp add: ite_step_def)

lemma ite_fold_count:
  \<open>length (snd (foldl (ite_step c a b) X [0..<n])) = length (snd X) + n\<close>
  by (induction n) (simp_all add: ite_step_def)

lemma ite_vec_m_count [simp]:
  \<open>sz s \<le> sz (fst (ite_vec_m s c a b))\<close>
  \<open>length (snd (ite_vec_m s c a b)) = length a\<close>
  using foldl_count_mono[OF ite_step_count, where X = \<open>(s, [])\<close>]
  by (simp_all add: ite_vec_m_foldl ite_fold_count)

lemma ite_step_lt:
  \<open>k < length a \<Longrightarrow> sz (fst (foldl (ite_step c a b) (s, []) [0..<length a])) < 72057594037927936 \<Longrightarrow>
   sz (fst (ite_m (fst (foldl (ite_step c a b) (s, []) [0..<k])) c (a ! k) (b ! k))) < 72057594037927936\<close>
  using foldl_upt_count_mono[where f = \<open>ite_step c a b\<close> and i = \<open>Suc k\<close> and j = \<open>length a\<close> and X = \<open>(s, [])\<close>, OF ite_step_count]
  by (simp add: ite_step_def)

text \<open>\<^const>\<open>shift_m\<close>. \<open>shF s i\<close>: the state after the first \<open>i\<close> stages.\<close>

definition shF :: \<open>Lit list \<Rightarrow> Lit list \<Rightarrow> bool \<Rightarrow> st \<Rightarrow> nat \<Rightarrow> st \<times> Lit list \<times> Lit \<times> nat\<close> where
  \<open>shF a b left s i \<equiv> foldl (shift_step a b left) (s, shift_const_m a 0 left, lconst False, 1) [0..<i]\<close>

lemma shF_0 [simp]: \<open>shF a b left s 0 = (s, shift_const_m a 0 left, lconst False, 1)\<close>
  by (simp add: shF_def)

lemma shF_Suc: \<open>shF a b left s (Suc i) = shift_step a b left (shF a b left s i) i\<close>
  by (simp add: shF_def)

lemma shift_step_count_mono: \<open>sz (fst X) \<le> sz (fst (shift_step a b left X k))\<close>
  by (cases X) (auto simp: shift_step_def split_def Let_def)

lemma shF_mono: \<open>i \<le> j \<Longrightarrow> sz (fst (shF a b left s i)) \<le> sz (fst (shF a b left s j))\<close>
proof (induction j)
  case (Suc j)
  then show ?case
    using shift_step_count_mono[of \<open>shF a b left s j\<close> a b left j]
    by (auto simp: shF_Suc le_Suc_eq)
qed simp

lemma shift_m_shF: \<open>shift_m s a b left =
  ite_vec_m (fst (shF a b left s (length b))) (fst (snd (snd (shF a b left s (length b)))))
    (replicate (length a) (lconst False)) (fst (snd (shF a b left s (length b))))\<close>
  by (simp add: shift_m_def shF_def split_def Let_def)

lemma shF_le_final: \<open>i \<le> length b \<Longrightarrow> sz (fst (shF a b left s i)) \<le> sz (fst (shift_m s a b left))\<close>
  using order_trans[OF shF_mono[of i \<open>length b\<close> a b left s]
      ite_vec_m_count(1)[of \<open>fst (shF a b left s (length b))\<close>]]
  by (simp add: shift_m_shF)

lemma shF_step_le_final:
  \<open>i < length b \<Longrightarrow> sz (fst (shift_step a b left (shF a b left s i) i)) \<le> sz (fst (shift_m s a b left))\<close>
  using shF_le_final[of \<open>Suc i\<close> b a left s] by (simp add: shF_Suc)

lemma shF_len: \<open>length (fst (snd (shF a b left s i))) = length a\<close>
proof (induction i)
  case (Suc i)
  then show ?case by (cases \<open>shF a b left s i\<close>) (simp add: shF_Suc shift_step_def split_def Let_def shift_const_m_def)
qed (simp add: shift_const_m_def)

lemma shF_p: \<open>snd (snd (snd (shF a b left s i))) \<le> max 1 (length a)\<close>
proof (induction i)
  case (Suc i)
  then show ?case by (cases \<open>shF a b left s i\<close>) (auto simp: shF_Suc shift_step_def split_def Let_def)
qed simp

lemma shF_Suc_stage:
  \<open>snd (snd (snd (shF a b left s i))) < length a \<Longrightarrow> shF a b left s (Suc i) =
    (fst (ite_vec_m (fst (shF a b left s i)) (b ! i)
            (shift_const_m (fst (snd (shF a b left s i))) (snd (snd (snd (shF a b left s i)))) left)
            (fst (snd (shF a b left s i)))),
     snd (ite_vec_m (fst (shF a b left s i)) (b ! i)
            (shift_const_m (fst (snd (shF a b left s i))) (snd (snd (snd (shF a b left s i)))) left)
            (fst (snd (shF a b left s i)))),
     fst (snd (snd (shF a b left s i))),
     if snd (snd (snd (shF a b left s i))) \<le> length a - snd (snd (snd (shF a b left s i)))
     then snd (snd (snd (shF a b left s i))) + snd (snd (snd (shF a b left s i))) else length a)\<close>
  by (cases \<open>shF a b left s i\<close>) (simp add: shF_Suc shift_step_def split_def Let_def)

lemma shF_Suc_or:
  \<open>\<not> snd (snd (snd (shF a b left s i))) < length a \<Longrightarrow> shF a b left s (Suc i) =
    (fst (or_m (fst (shF a b left s i)) (fst (snd (snd (shF a b left s i)))) (b ! i)),
     fst (snd (shF a b left s i)),
     snd (or_m (fst (shF a b left s i)) (fst (snd (snd (shF a b left s i)))) (b ! i)),
     snd (snd (snd (shF a b left s i))))\<close>
  by (cases \<open>shF a b left s i\<close>) (simp add: shF_Suc shift_step_def split_def Let_def)

lemma shF_count_stage:
  \<open>i < length b \<Longrightarrow> snd (snd (snd (shF a b left s i))) < length a \<Longrightarrow>
   sz (fst (ite_vec_m (fst (shF a b left s i)) (b ! i)
            (shift_const_m (fst (snd (shF a b left s i))) (snd (snd (snd (shF a b left s i)))) left)
            (fst (snd (shF a b left s i))))) \<le> sz (fst (shift_m s a b left))\<close>
  using shF_le_final[of \<open>Suc i\<close> b a left s] by (simp add: shF_Suc_stage)

lemma shF_count_or:
  \<open>i < length b \<Longrightarrow> \<not> snd (snd (snd (shF a b left s i))) < length a \<Longrightarrow>
   sz (fst (and_m (fst (shF a b left s i)) (lneg (fst (snd (snd (shF a b left s i))))) (lneg (b ! i))))
   \<le> sz (fst (shift_m s a b left))\<close>
  using shF_le_final[of \<open>Suc i\<close> b a left s] by (simp add: shF_Suc_or)

lemma unat_len_sub: \<open>unat p < n \<Longrightarrow> n < 2 ^ 64 \<Longrightarrow> unat (word_of_nat n - (p :: 64 word)) = n - unat p\<close>
  by (simp add: unat_sub word_le_nat_alt unat_of_nat_eq)

lemma unat_double_p: \<open>unat p \<le> n - unat p \<Longrightarrow> n < 2 ^ 64 \<Longrightarrow> unat (2 * (p :: 64 word)) = unat p + unat p\<close>
  by (subst unat_mult_lem[THEN iffD1]) simp_all

lemma shF_or_lt:
  \<open>i < length b \<Longrightarrow> \<not> snd (snd (snd (shF a b left s i))) < length a \<Longrightarrow>
   sz (fst (ite_vec_m (fst (shF a b left s (length b))) (fst (snd (snd (shF a b left s (length b)))))
     (replicate (length a) (lconst False)) (fst (snd (shF a b left s (length b)))))) < 72057594037927936 \<Longrightarrow>
   sz (fst (and_m (fst (shF a b left s i)) (lneg (fst (snd (snd (shF a b left s i))))) (lneg (b ! i))))
   < 72057594037927936\<close>
  using shF_count_or[of i b a left s] by (simp add: shift_m_shF)

lemma shF_stage_lt:
  \<open>i < length b \<Longrightarrow> snd (snd (snd (shF a b left s i))) < length a \<Longrightarrow>
   sz (fst (ite_vec_m (fst (shF a b left s (length b))) (fst (snd (snd (shF a b left s (length b)))))
     (replicate (length a) (lconst False)) (fst (snd (shF a b left s (length b)))))) < 72057594037927936 \<Longrightarrow>
   sz (fst (ite_vec_m (fst (shF a b left s i)) (b ! i)
            (shift_const_m (fst (snd (shF a b left s i))) (snd (snd (snd (shF a b left s i)))) left)
            (fst (snd (shF a b left s i))))) < 72057594037927936\<close>
  using shF_count_stage[of i b a left s] by (simp add: shift_m_shF)

lemma shift_m_ge [simp]: \<open>sz s \<le> sz (fst (shift_m s a b left))\<close>
  using shF_le_final[of 0 b a left s] by simp

lemma shift_m_len [simp]: \<open>length (snd (shift_m s a b left)) = length a\<close>
  by (simp add: shift_m_shF)

text \<open>\<^const>\<open>divrem_m\<close>\<close>

text \<open>The intermediate states of \<^const>\<open>divrem_m\<close>, named so that the terms in the proof of
  \<^verbatim>\<open>bv_divrem\<close> stay small.\<close>

definition dr3 :: \<open>st \<Rightarrow> Lit list \<Rightarrow> Lit list \<Rightarrow> st \<times> Lit\<close> where
  \<open>dr3 s a b = eq_m (fst s + length a + length a, snd s) b (replicate (length a) (lconst False))\<close>
definition dr4 :: \<open>st \<Rightarrow> Lit list \<Rightarrow> Lit list \<Rightarrow> st \<times> Lit\<close> where
  \<open>dr4 s a b = eq_m (fst (dr3 s a b)) (snd (fresh_vec_m s (length a))) (replicate (length a) (lconst True))\<close>
definition dr5 :: \<open>st \<Rightarrow> Lit list \<Rightarrow> Lit list \<Rightarrow> st \<times> Lit\<close> where
  \<open>dr5 s a b = eq_m (fst (dr4 s a b)) (snd (fresh_vec_m (fst s + length a, snd s) (length a))) a\<close>
definition dr6 :: \<open>st \<Rightarrow> Lit list \<Rightarrow> Lit list \<Rightarrow> st \<times> Lit\<close> where
  \<open>dr6 s a b = and_m (fst (dr5 s a b)) (snd (dr4 s a b)) (snd (dr5 s a b))\<close>
definition dr7 :: \<open>st \<Rightarrow> Lit list \<Rightarrow> Lit list \<Rightarrow> st \<times> Lit list\<close> where
  \<open>dr7 s a b = mul_m (fst (dr6 s a b)) (zext_m (snd (fresh_vec_m s (length a))) (length a + length a))
     (zext_m b (length a + length a))\<close>
definition dr8 :: \<open>st \<Rightarrow> Lit list \<Rightarrow> Lit list \<Rightarrow> st \<times> Lit list \<times> Lit\<close> where
  \<open>dr8 s a b = add_m (fst (dr7 s a b)) (snd (dr7 s a b))
     (zext_m (snd (fresh_vec_m (fst s + length a, snd s) (length a))) (length a + length a)) (lconst False)\<close>
definition dr9 :: \<open>st \<Rightarrow> Lit list \<Rightarrow> Lit list \<Rightarrow> st \<times> Lit\<close> where
  \<open>dr9 s a b = eq_m (fst (dr8 s a b)) (fst (snd (dr8 s a b))) (zext_m a (length a + length a))\<close>
definition dr10 :: \<open>st \<Rightarrow> Lit list \<Rightarrow> Lit list \<Rightarrow> st \<times> Lit list \<times> Lit\<close> where
  \<open>dr10 s a b = add_m (fst (dr9 s a b)) (snd (fresh_vec_m (fst s + length a, snd s) (length a))) (not_m b)
     (lconst True)\<close>
definition dr11 :: \<open>st \<Rightarrow> Lit list \<Rightarrow> Lit list \<Rightarrow> st \<times> Lit\<close> where
  \<open>dr11 s a b = and_m (fst (dr10 s a b)) (snd (dr9 s a b)) (lneg (snd (snd (dr10 s a b))))\<close>
definition dr12 :: \<open>st \<Rightarrow> Lit list \<Rightarrow> Lit list \<Rightarrow> st \<times> Lit\<close> where
  \<open>dr12 s a b = ite_m (fst (dr11 s a b)) (snd (dr3 s a b)) (snd (dr6 s a b)) (snd (dr11 s a b))\<close>

lemmas dr_fold = dr3_def[symmetric] dr4_def[symmetric] dr5_def[symmetric] dr6_def[symmetric]
  dr7_def[symmetric] dr8_def[symmetric] dr9_def[symmetric] dr10_def[symmetric] dr11_def[symmetric]
  dr12_def[symmetric]

lemma dr_counts [simp]:
  \<open>sz s + length a + length a \<le> sz (fst (dr3 s a b))\<close>
  \<open>sz (fst (dr3 s a b)) \<le> sz (fst (dr4 s a b))\<close>
  \<open>sz (fst (dr4 s a b)) \<le> sz (fst (dr5 s a b))\<close>
  \<open>sz (fst (dr5 s a b)) \<le> sz (fst (dr6 s a b))\<close>
  \<open>sz (fst (dr6 s a b)) \<le> sz (fst (dr7 s a b))\<close>
  \<open>length (snd (dr7 s a b)) = length a + length a\<close>
  \<open>sz (fst (dr7 s a b)) \<le> sz (fst (dr8 s a b))\<close>
  \<open>length (fst (snd (dr8 s a b))) = length a + length a\<close>
  \<open>sz (fst (dr8 s a b)) \<le> sz (fst (dr9 s a b))\<close>
  \<open>sz (fst (dr9 s a b)) \<le> sz (fst (dr10 s a b))\<close>
  \<open>sz (fst (dr10 s a b)) \<le> sz (fst (dr11 s a b))\<close>
  \<open>sz (fst (dr11 s a b)) \<le> sz (fst (dr12 s a b))\<close>
  using eq_m_count[of \<open>(fst s + length a + length a, snd s)\<close> b \<open>replicate (length a) (lconst False)\<close>] sz_def[of s]
  by (simp_all add: dr3_def dr4_def dr5_def dr6_def dr7_def dr8_def dr9_def dr10_def dr11_def dr12_def
      split_def)

lemma divrem_m_dr:
  \<open>divrem_m s a b =
     (addc_m (fst (dr12 s a b)) [snd (dr12 s a b)], snd (fresh_vec_m s (length a)),
      snd (fresh_vec_m (fst s + length a, snd s) (length a)))\<close>
  by (simp add: divrem_m_def Let_def split_def dr3_def dr4_def dr5_def dr6_def dr7_def dr8_def dr9_def
      dr10_def dr11_def dr12_def)

lemma divrem_m_count [simp]:
  \<open>sz (fst (divrem_m s a b)) = Suc (sz (fst (dr12 s a b)))\<close>
  \<open>length (fst (snd (divrem_m s a b))) = length a\<close>
  \<open>length (snd (snd (divrem_m s a b))) = length a\<close>
  by (simp_all add: divrem_m_dr addc_m_def sz_def)

lemma dr12_ge [simp]: \<open>sz s \<le> sz (fst (dr12 s a b))\<close>
  using dr_counts[of s a b] by linarith

text \<open>The bound on the number of variables of \<^const>\<open>divrem_m\<close> bounds its intermediate states.\<close>

lemma dr_lt:
  assumes \<open>room (fst (divrem_m s a b))\<close>
  shows \<open>fst s + length a < 18446744073709551616\<close>
    \<open>fst s + length a + length a < 18446744073709551616\<close>
    \<open>room (fst (fresh_vec_m s (length a)))\<close>
    \<open>room (fst (fresh_vec_m (fst s + length a, snd s) (length a)))\<close>
    \<open>room (fst (dr3 s a b))\<close> \<open>room (fst (dr4 s a b))\<close> \<open>room (fst (dr5 s a b))\<close>
    \<open>room (fst (dr6 s a b))\<close> \<open>room (fst (dr7 s a b))\<close> \<open>room (fst (dr8 s a b))\<close>
    \<open>room (fst (dr9 s a b))\<close> \<open>room (fst (dr10 s a b))\<close> \<open>room (fst (dr11 s a b))\<close>
    \<open>room (fst (dr12 s a b))\<close> \<open>length (snd (fst (dr12 s a b))) < 72057594037927936\<close>
  using assms dr_counts[of s a b] divrem_m_count(1)[of s a b] by (simp_all add: room_def sz_def)

context QFBV_ctx
begin

subsection \<open>Literals, clauses, gates\<close>

definition lit_const_contract :: \<open>bool \<Rightarrow> ('s, Lit, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>lit_const_contract b \<equiv>
     make_function_contract can_alloc_reference (\<lambda>r. can_alloc_reference \<star> \<langle>r = lconst b\<rangle>)\<close>

lemma lit_const_spec [crush_specs]:
  shows \<open>\<Gamma>; lit_const b \<Turnstile>\<^sub>F lit_const_contract b\<close>
  by (crush_boot f: lit_const_def contract: lit_const_contract_def)
     (crush_base simp add: lconst_def)

definition lit_neg_contract :: \<open>Lit \<Rightarrow> ('s, Lit, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>lit_neg_contract l \<equiv>
     make_function_contract can_alloc_reference (\<lambda>r. can_alloc_reference \<star> \<langle>r = lneg l\<rangle>)\<close>

lemma lit_neg_spec [crush_specs]:
  shows \<open>\<Gamma>; lit_neg l \<Turnstile>\<^sub>F lit_neg_contract l\<close>
  by (crush_boot f: lit_neg_def contract: lit_neg_contract_def)
     (crush_base simp add: lneg_def)

lemma cnf_make_simps [simp]:
  \<open>cnf_ok (make_Cnf n v) = vok v\<close>
  \<open>st_of (make_Cnf n v) = (unat n, vecs_of v)\<close>
  by (simp_all add: cnf_ok_def st_of_def)

lemma st_of_simps [simp]:
  \<open>fst (st_of c) = unat (Cnf_num_vars c)\<close>
  \<open>snd (st_of c) = vecs_of (Cnf_clauses c)\<close>
  by (simp_all add: st_of_def)

text \<open>A function on a \<^verbatim>\<open>Cnf\<close> computes the model \<open>m\<close> of the state: the result is a well-formed
  \<^verbatim>\<open>Cnf\<close> of the state that \<open>m\<close> gives, and the literal that \<open>m\<close> gives.\<close>
definition cnf_res :: \<open>Cnf \<times> 'a \<times> tnil \<Rightarrow> st \<times> 'a \<Rightarrow> bool\<close> where
  \<open>cnf_res r m \<equiv> cnf_ok (fst r) \<and> st_of (fst r) = fst m \<and> snd r = (snd m, TNil)\<close>

definition fresh_fn_contract :: \<open>Cnf \<Rightarrow> ('s, Cnf \<times> Lit \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>fresh_fn_contract c \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>cnf_ok c \<and> Suc (fst (st_of c)) < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>cnf_res r (fresh_m (st_of c))\<rangle>)\<close>

lemma fresh_fn_spec [crush_specs]:
  shows \<open>\<Gamma>; fresh_fn c \<Turnstile>\<^sub>F fresh_fn_contract c\<close>
  apply (crush_boot f: fresh_fn_def contract: fresh_fn_contract_def)
  apply (crush_base simp add: fresh_m_def cnf_res_def cnf_ok_def unat_word_Suc_simp)
  done

definition add_clause_contract :: \<open>Cnf \<Rightarrow> Lit rvec \<Rightarrow> ('s, Cnf, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>add_clause_contract c cl \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>cnf_ok c \<and> length (snd (st_of c)) < 2 ^ 56\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>cnf_ok r \<and> st_of r = addc_m (st_of c) (rvec_elems cl)\<rangle>)\<close>

lemma add_clause_spec [crush_specs]:
  shows \<open>\<Gamma>; add_clause c cl \<Turnstile>\<^sub>F add_clause_contract c cl\<close>
  apply (crush_boot f: add_clause_def contract: add_clause_contract_def)
  apply (crush_base simp add: cnf_ok_def push_not_None addc_m_def)
  done

definition clause3_contract :: \<open>Lit \<Rightarrow> Lit \<Rightarrow> Lit \<Rightarrow> ('s, Lit rvec, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>clause3_contract a b d \<equiv>
     make_function_contract can_alloc_reference (\<lambda>r. can_alloc_reference \<star> \<langle>rvec_elems r = [a, b, d] \<and> vok r\<rangle>)\<close>

lemma clause3_spec [crush_specs]:
  shows \<open>\<Gamma>; clause3 a b d \<Turnstile>\<^sub>F clause3_contract a b d\<close>
  apply (crush_boot f: clause3_def contract: clause3_contract_def)
  apply (crush_base simp add: push_not_None)
  done

definition clause2_contract :: \<open>Lit \<Rightarrow> Lit \<Rightarrow> ('s, Lit rvec, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>clause2_contract a b \<equiv>
     make_function_contract can_alloc_reference (\<lambda>r. can_alloc_reference \<star> \<langle>rvec_elems r = [a, b] \<and> vok r\<rangle>)\<close>

lemma clause2_spec [crush_specs]:
  shows \<open>\<Gamma>; clause2 a b \<Turnstile>\<^sub>F clause2_contract a b\<close>
  apply (crush_boot f: clause2_def contract: clause2_contract_def)
  apply (crush_base simp add: push_not_None)
  done

definition clause1_contract :: \<open>Lit \<Rightarrow> ('s, Lit rvec, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>clause1_contract a \<equiv>
     make_function_contract can_alloc_reference (\<lambda>r. can_alloc_reference \<star> \<langle>rvec_elems r = [a] \<and> vok r\<rangle>)\<close>

lemma clause1_spec [crush_specs]:
  shows \<open>\<Gamma>; clause1 a \<Turnstile>\<^sub>F clause1_contract a\<close>
  apply (crush_boot f: clause1_def contract: clause1_contract_def)
  apply (crush_base simp add: push_not_None)
  done

text \<open>The same for a function that also returns a vector of literals.\<close>
definition cnfv_res :: \<open>Cnf \<times> Lit rvec \<times> tnil \<Rightarrow> st \<times> Lit list \<Rightarrow> bool\<close> where
  \<open>cnfv_res r m \<equiv> cnf_ok (fst r) \<and> st_of (fst r) = fst m \<and> rvec_elems (fst (snd r)) = snd m \<and>
     vok (fst (snd r)) \<and> snd (snd r) = TNil\<close>

definition tseitin_and_contract :: \<open>Cnf \<Rightarrow> Lit \<Rightarrow> Lit \<Rightarrow> ('s, Cnf \<times> Lit \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>tseitin_and_contract c a b \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>cnf_ok c \<and> room (fst (and_t (st_of c) a b))\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>cnf_res r (and_t (st_of c) a b)\<rangle>)\<close>

lemma tseitin_and_spec [crush_specs]:
  shows \<open>\<Gamma>; tseitin_and c a b \<Turnstile>\<^sub>F tseitin_and_contract c a b\<close>
  apply (crush_boot f: tseitin_and_def contract: tseitin_and_contract_def)
  apply (crush_base simp add: and_t_def fresh_m_def addc_m_def room_def cnf_res_def sz_def)
  done

definition tseitin_xor_contract :: \<open>Cnf \<Rightarrow> Lit \<Rightarrow> Lit \<Rightarrow> ('s, Cnf \<times> Lit \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>tseitin_xor_contract c a b \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>cnf_ok c \<and> room (fst (xor_t (st_of c) a b))\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>cnf_res r (xor_t (st_of c) a b)\<rangle>)\<close>

lemma tseitin_xor_spec [crush_specs]:
  shows \<open>\<Gamma>; tseitin_xor c a b \<Turnstile>\<^sub>F tseitin_xor_contract c a b\<close>
  apply (crush_boot f: tseitin_xor_def contract: tseitin_xor_contract_def)
  apply (crush_base simp add: xor_t_def fresh_m_def addc_m_def room_def cnf_res_def sz_def)
  done

definition tseitin_ite_contract :: \<open>Cnf \<Rightarrow> Lit \<Rightarrow> Lit \<Rightarrow> Lit \<Rightarrow> ('s, Cnf \<times> Lit \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>tseitin_ite_contract c x a b \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>cnf_ok c \<and> room (fst (ite_t (st_of c) x a b))\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>cnf_res r (ite_t (st_of c) x a b)\<rangle>)\<close>

lemma tseitin_ite_spec [crush_specs]:
  shows \<open>\<Gamma>; tseitin_ite c x a b \<Turnstile>\<^sub>F tseitin_ite_contract c x a b\<close>
  apply (crush_boot f: tseitin_ite_def contract: tseitin_ite_contract_def)
  apply (crush_base simp add: ite_t_def fresh_m_def addc_m_def room_def cnf_res_def sz_def)
  done

definition gate_and_contract :: \<open>Cnf \<Rightarrow> Lit \<Rightarrow> Lit \<Rightarrow> ('s, Cnf \<times> Lit \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>gate_and_contract c a b \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>cnf_ok c \<and> room (fst (and_m (st_of c) a b))\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>cnf_res r (and_m (st_of c) a b)\<rangle>)\<close>

lemma gate_and_spec [crush_specs]:
  shows \<open>\<Gamma>; gate_and c a b \<Turnstile>\<^sub>F gate_and_contract c a b\<close>
  apply (crush_boot f: gate_and_def contract: gate_and_contract_def)
  apply (crush_base simp add: and_m_def lconst_def cnf_res_def)
  done

definition gate_or_contract :: \<open>Cnf \<Rightarrow> Lit \<Rightarrow> Lit \<Rightarrow> ('s, Cnf \<times> Lit \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>gate_or_contract c a b \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>cnf_ok c \<and> room (fst (or_m (st_of c) a b))\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>cnf_res r (or_m (st_of c) a b)\<rangle>)\<close>

lemma gate_or_spec [crush_specs]:
  shows \<open>\<Gamma>; gate_or c a b \<Turnstile>\<^sub>F gate_or_contract c a b\<close>
  apply (crush_boot f: gate_or_def contract: gate_or_contract_def)
  apply (crush_base simp add: cnf_res_def)
  done

definition gate_xor_contract :: \<open>Cnf \<Rightarrow> Lit \<Rightarrow> Lit \<Rightarrow> ('s, Cnf \<times> Lit \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>gate_xor_contract c a b \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>cnf_ok c \<and> room (fst (xor_m (st_of c) a b))\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>cnf_res r (xor_m (st_of c) a b)\<rangle>)\<close>

lemma gate_xor_spec [crush_specs]:
  shows \<open>\<Gamma>; gate_xor c a b \<Turnstile>\<^sub>F gate_xor_contract c a b\<close>
  apply (crush_boot f: gate_xor_def contract: gate_xor_contract_def)
  apply (crush_base simp add: xor_m_def lconst_def cnf_res_def)
  done

definition gate_ite_contract :: \<open>Cnf \<Rightarrow> Lit \<Rightarrow> Lit \<Rightarrow> Lit \<Rightarrow> ('s, Cnf \<times> Lit \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>gate_ite_contract c x a b \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>cnf_ok c \<and> room (fst (ite_m (st_of c) x a b))\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>cnf_res r (ite_m (st_of c) x a b)\<rangle>)\<close>

lemma gate_ite_spec [crush_specs]:
  shows \<open>\<Gamma>; gate_ite c x a b \<Turnstile>\<^sub>F gate_ite_contract c x a b\<close>
  apply (crush_boot f: gate_ite_def contract: gate_ite_contract_def)
  apply (crush_base simp add: ite_m_def split_def cnf_res_def)
  done

definition gate_bitwise_contract :: \<open>Cnf \<Rightarrow> BinOp \<Rightarrow> Lit \<Rightarrow> Lit \<Rightarrow> ('s, Cnf \<times> Lit \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>gate_bitwise_contract c op a b \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>cnf_ok c \<and> room (fst (bitw_m op (st_of c) a b))\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>cnf_res r (bitw_m op (st_of c) a b)\<rangle>)\<close>

lemma gate_bitwise_spec [crush_specs]:
  shows \<open>\<Gamma>; gate_bitwise c op a b \<Turnstile>\<^sub>F gate_bitwise_contract c op a b\<close>
  apply (crush_boot f: gate_bitwise_def contract: gate_bitwise_contract_def)
  apply (cases op; simp only: BinOp_case_simps)
         apply (crush_base simp add: bitw_m_def)+
  done

subsection \<open>A loop\<close>

definition bv_not_contract :: \<open>Lit rvec \<Rightarrow> ('s, Lit rvec, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>bv_not_contract a \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>rvec_length a \<le> urust_fuel \<and> rvec_length a < 2 ^ 56\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>rvec_elems r = not_m (rvec_elems a) \<and> vok r\<rangle>)\<close>

lemma bv_not_spec [crush_specs]:
  shows \<open>\<Gamma>; bv_not a \<Turnstile>\<^sub>F bv_not_contract a\<close>
  apply (crush_boot f: bv_not_def contract: bv_not_contract_def)
  apply (crush_base)
  subgoal for r_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gr r gi i. r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i \<le> rvec_length a \<and> rvec_elems r = map lneg (take (unat i) (rvec_elems a)) \<and> vok r \<and>
                rvec_length a - unat i \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gr r gi i. r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i < rvec_length a \<and> rvec_elems r = map lneg (take (unat i) (rvec_elems a)) \<and> vok r \<and>
                rvec_length a - unat i \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>rvec_elems r = not_m (rvec_elems a) \<and> vok r\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: push_not_None vok_len_unat word_less_nat_alt unat_of_nat_eq unat_of_nat_64 unat_word_Suc_simp
        not_m_def take_Suc_conv_app_nth)
    done
  done

subsection \<open>Circuits without clauses\<close>

definition bv_const_contract :: \<open>bool rvec \<Rightarrow> ('s, Lit rvec, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>bv_const_contract bs \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>rvec_length bs \<le> urust_fuel \<and> rvec_length bs < 2 ^ 56\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>rvec_elems r = const_m (rvec_elems bs) \<and> vok r\<rangle>)\<close>

lemma bv_const_spec [crush_specs]:
  shows \<open>\<Gamma>; bv_const bs \<Turnstile>\<^sub>F bv_const_contract bs\<close>
  apply (crush_boot f: bv_const_def contract: bv_const_contract_def)
  apply (crush_base)
  subgoal for r_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gr r gi i. r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i \<le> rvec_length bs \<and> rvec_elems r = take (unat i) (const_m (rvec_elems bs)) \<and> vok r \<and>
                rvec_length bs - unat i \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gr r gi i. r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i < rvec_length bs \<and> rvec_elems r = take (unat i) (const_m (rvec_elems bs)) \<and> vok r \<and>
                rvec_length bs - unat i \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>rvec_elems r = const_m (rvec_elems bs) \<and> vok r\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: push_not_None vok_len_unat word_less_nat_alt unat_of_nat_eq unat_of_nat_64 unat_word_Suc_simp
        take_Suc_conv_app_nth)
    done
  done

definition bv_of_nat_contract :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> ('s, Lit rvec, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>bv_of_nat_contract v w \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>unat w \<le> urust_fuel \<and> unat w < 2 ^ 56\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>rvec_elems r = of_nat_m (unat v) (unat w) \<and> vok r\<rangle>)\<close>

lemma bv_of_nat_spec [crush_specs]:
  shows \<open>\<Gamma>; bv_of_nat v w \<Turnstile>\<^sub>F bv_of_nat_contract v w\<close>
  apply (crush_boot f: bv_of_nat_def contract: bv_of_nat_contract_def)
  apply (crush_base)
  subgoal for r_ref x_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gr r gx x gi i. r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> x_ref \<mapsto>\<langle>\<top>\<rangle> gx\<down>x \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
               can_alloc_reference \<star>
               \<langle>unat i \<le> unat w \<and> unat w < 2 ^ 56 \<and> rvec_elems r = take (unat i) (of_nat_m (unat v) (unat w)) \<and> vok r \<and>
                unat x = unat v div 2 ^ unat i \<and> unat w - unat i \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gr r gx x gi i. r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> x_ref \<mapsto>\<langle>\<top>\<rangle> gx\<down>x \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
               can_alloc_reference \<star>
               \<langle>unat i < unat w \<and> unat w < 2 ^ 56 \<and> rvec_elems r = take (unat i) (of_nat_m (unat v) (unat w)) \<and> vok r \<and>
                unat x = unat v div 2 ^ unat i \<and> unat w - unat i \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>rvec_elems r = of_nat_m (unat v) (unat w) \<and> vok r\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: push_not_None vok_len_unat word_less_nat_alt unat_of_nat_eq unat_of_nat_64 unat_word_Suc_simp
        take_Suc_conv_app_nth word_mod2_eq1 unat_div div_2_pow_Suc)
    done
  done

definition bv_shift_const_contract :: \<open>Lit rvec \<Rightarrow> 64 word \<Rightarrow> bool \<Rightarrow> ('s, Lit rvec, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>bv_shift_const_contract a s left \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>rvec_length a \<le> urust_fuel \<and> rvec_length a < 2 ^ 56\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>rvec_elems r = shift_const_m (rvec_elems a) (unat s) left \<and> vok r\<rangle>)\<close>

lemma bv_shift_const_spec [crush_specs]:
  shows \<open>\<Gamma>; bv_shift_const a s left \<Turnstile>\<^sub>F bv_shift_const_contract a s left\<close>
  apply (crush_boot f: bv_shift_const_def contract: bv_shift_const_contract_def)
  apply (crush_base)
  subgoal for r_ref j_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gr r gj j. r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star>
               \<langle>unat j \<le> rvec_length a \<and> rvec_elems r = take (unat j) (shift_const_m (rvec_elems a) (unat s) left) \<and> vok r \<and>
                rvec_length a - unat j \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gr r gj j. r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star>
               \<langle>unat j < rvec_length a \<and> rvec_elems r = take (unat j) (shift_const_m (rvec_elems a) (unat s) left) \<and> vok r \<and>
                rvec_length a - unat j \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>rvec_elems r = shift_const_m (rvec_elems a) (unat s) left \<and> vok r\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: push_not_None vok_len_unat word_less_nat_alt unat_of_nat_eq unat_of_nat_64 unat_word_Suc_simp
        take_Suc_conv_app_nth unat_sub_not_less unat_len_minus unat_add_less_len word_le_nat_alt)
    done
  done

definition bv_zext_contract :: \<open>Lit rvec \<Rightarrow> 64 word \<Rightarrow> ('s, Lit rvec, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>bv_zext_contract a w \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>unat w \<le> urust_fuel \<and> unat w < 2 ^ 56 \<and> rvec_length a < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>rvec_elems r = zext_m (rvec_elems a) (unat w) \<and> vok r\<rangle>)\<close>

lemma bv_zext_spec [crush_specs]:
  shows \<open>\<Gamma>; bv_zext a w \<Turnstile>\<^sub>F bv_zext_contract a w\<close>
  apply (crush_boot f: bv_zext_def contract: bv_zext_contract_def)
  apply (crush_base)
  subgoal for r_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gr r gi i. r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i \<le> unat w \<and> unat w < 2 ^ 56 \<and> rvec_elems r = take (unat i) (zext_m (rvec_elems a) (unat w)) \<and> vok r \<and>
                unat w - unat i \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gr r gi i. r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i < unat w \<and> unat w < 2 ^ 56 \<and> rvec_elems r = take (unat i) (zext_m (rvec_elems a) (unat w)) \<and> vok r \<and>
                unat w - unat i \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>rvec_elems r = zext_m (rvec_elems a) (unat w) \<and> vok r\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: push_not_None vok_len_unat word_less_nat_alt unat_of_nat_eq unat_of_nat_64 unat_word_Suc_simp
        take_Suc_conv_app_nth)
    done
  done

definition bv_extract_contract :: \<open>Lit rvec \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, Lit rvec, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>bv_extract_contract a hi lo \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
        \<langle>unat lo \<le> unat hi \<and> unat hi < rvec_length a \<and> rvec_length a < 2 ^ 56 \<and> unat hi - unat lo + 1 \<le> urust_fuel\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>rvec_elems r = extract_m (rvec_elems a) (unat hi) (unat lo) \<and> vok r\<rangle>)\<close>

lemma bv_extract_spec [crush_specs]:
  shows \<open>\<Gamma>; bv_extract a hi lo \<Turnstile>\<^sub>F bv_extract_contract a hi lo\<close>
  apply (crush_boot f: bv_extract_def contract: bv_extract_contract_def)
  apply (crush_base)
  subgoal for r_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gr r gi i. r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat lo \<le> unat i \<and> unat i \<le> Suc (unat hi) \<and>
                rvec_elems r = take (unat i - unat lo) (extract_m (rvec_elems a) (unat hi) (unat lo)) \<and> vok r \<and>
                Suc (unat hi) - unat i \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gr r gi i. r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat lo \<le> unat i \<and> unat i \<le> unat hi \<and>
                rvec_elems r = take (unat i - unat lo) (extract_m (rvec_elems a) (unat hi) (unat lo)) \<and> vok r \<and>
                Suc (unat hi) - unat i \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>rvec_elems r = extract_m (rvec_elems a) (unat hi) (unat lo) \<and> vok r\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: push_not_None vok_len_unat word_le_nat_alt unat_of_nat_eq unat_of_nat_64 unat_word_Suc_simp
        take_Suc_conv_app_nth Suc_diff_le)
    done
  done

definition bv_concat_contract :: \<open>Lit rvec \<Rightarrow> Lit rvec \<Rightarrow> ('s, Lit rvec, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>bv_concat_contract hi lo \<equiv>
     make_function_contract
       (can_alloc_reference \<star> \<langle>rvec_length hi \<le> urust_fuel \<and> vok lo \<and> rvec_length lo + rvec_length hi < 2 ^ 56\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>rvec_elems r = concat_m (rvec_elems hi) (rvec_elems lo) \<and> vok r\<rangle>)\<close>

lemma bv_concat_spec [crush_specs]:
  shows \<open>\<Gamma>; bv_concat hi lo \<Turnstile>\<^sub>F bv_concat_contract hi lo\<close>
  apply (crush_boot f: bv_concat_def contract: bv_concat_contract_def)
  apply (crush_base)
  subgoal for r_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gr r gi i. r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i \<le> rvec_length hi \<and> rvec_elems r = rvec_elems lo @ take (unat i) (rvec_elems hi) \<and> vok r \<and>
                rvec_length hi - unat i \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gr r gi i. r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i < rvec_length hi \<and> rvec_elems r = rvec_elems lo @ take (unat i) (rvec_elems hi) \<and> vok r \<and>
                rvec_length hi - unat i \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>rvec_elems r = concat_m (rvec_elems hi) (rvec_elems lo) \<and> vok r\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: push_not_None vok_len_unat word_less_nat_alt unat_of_nat_eq unat_of_nat_64 unat_word_Suc_simp
        take_Suc_conv_app_nth concat_m_def)
    done
  done

subsection \<open>Circuits that add clauses\<close>

definition bv_fresh_contract :: \<open>Cnf \<Rightarrow> 64 word \<Rightarrow> ('s, Cnf \<times> Lit rvec \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>bv_fresh_contract c w \<equiv>
     make_function_contract
       (can_alloc_reference \<star> \<langle>unat w \<le> urust_fuel \<and> cnf_ok c \<and> room (fst (fresh_vec_m (st_of c) (unat w)))\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>cnfv_res r (fresh_vec_m (st_of c) (unat w))\<rangle>)\<close>

lemma bv_fresh_spec [crush_specs]:
  shows \<open>\<Gamma>; bv_fresh c w \<Turnstile>\<^sub>F bv_fresh_contract c w\<close>
  apply (crush_boot f: bv_fresh_def contract: bv_fresh_contract_def)
  apply (crush_base)
  subgoal for cnf_ref r_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gc cn gr r gi i. cnf_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>cn \<star> r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
               can_alloc_reference \<star>
               \<langle>unat i \<le> unat w \<and> cnf_ok cn \<and> st_of cn = (fst (st_of c) + unat i, snd (st_of c)) \<and>
                rvec_elems r = take (unat i) (snd (fresh_vec_m (st_of c) (unat w))) \<and> vok r \<and>
                unat w - unat i \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gc cn gr r gi i. cnf_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>cn \<star> r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
               can_alloc_reference \<star>
               \<langle>unat i < unat w \<and> cnf_ok cn \<and> st_of cn = (fst (st_of c) + unat i, snd (st_of c)) \<and>
                rvec_elems r = take (unat i) (snd (fresh_vec_m (st_of c) (unat w))) \<and> vok r \<and>
                unat w - unat i \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>cnfv_res r (fresh_vec_m (st_of c) (unat w))\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base)
    apply (auto simp add: cnf_res_def room_def st_of_def word_less_nat_alt unat_of_nat_eq unat_of_nat_64 unat_word_Suc_simp take_Suc_conv_app_nth antisym_conv)
    apply (clarsimp simp add: cnfv_res_def st_of_def)
    done
  done

definition bv_bitwise_contract ::
  \<open>Cnf \<Rightarrow> BinOp \<Rightarrow> Lit rvec \<Rightarrow> Lit rvec \<Rightarrow> ('s, Cnf \<times> Lit rvec \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>bv_bitwise_contract c op a b \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
        \<langle>rvec_length a \<le> urust_fuel \<and> rvec_length a < 2 ^ 56 \<and> rvec_length a \<le> rvec_length b \<and> cnf_ok c \<and>
         room (fst (bitwise_m op (st_of c) (rvec_elems a) (rvec_elems b)))\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>cnfv_res r (bitwise_m op (st_of c) (rvec_elems a) (rvec_elems b))\<rangle>)\<close>

lemma bv_bitwise_spec [crush_specs]:
  shows \<open>\<Gamma>; bv_bitwise c op a b \<Turnstile>\<^sub>F bv_bitwise_contract c op a b\<close>
  apply (crush_boot f: bv_bitwise_def contract: bv_bitwise_contract_def)
  apply (crush_base)
  subgoal for cnf_ref r_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gc cn gr r gi i. cnf_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>cn \<star> r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
               can_alloc_reference \<star>
               \<langle>unat i \<le> rvec_length a \<and> cnf_ok cn \<and>
                st_of cn = fst (foldl (bitwise_step op (rvec_elems a) (rvec_elems b)) (st_of c, []) [0..<unat i]) \<and>
                rvec_elems r = snd (foldl (bitwise_step op (rvec_elems a) (rvec_elems b)) (st_of c, []) [0..<unat i]) \<and>
                vok r \<and> rvec_length a - unat i \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gc cn gr r gi i. cnf_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>cn \<star> r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
               can_alloc_reference \<star>
               \<langle>unat i < rvec_length a \<and> cnf_ok cn \<and>
                st_of cn = fst (foldl (bitwise_step op (rvec_elems a) (rvec_elems b)) (st_of c, []) [0..<unat i]) \<and>
                rvec_elems r = snd (foldl (bitwise_step op (rvec_elems a) (rvec_elems b)) (st_of c, []) [0..<unat i]) \<and>
                vok r \<and> rvec_length a - unat i \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>cnfv_res r (bitwise_m op (st_of c) (rvec_elems a) (rvec_elems b))\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: cnfv_res_def)
    apply (auto simp add: word_less_nat_alt unat_of_nat_eq unat_of_nat_64 unat_word_Suc_simp antisym_conv bitwise_m_foldl bitwise_fold_count bitwise_step_def bitwise_step_lt cnf_res_def room_def)
    done
  done

definition bv_add_contract ::
  \<open>Cnf \<Rightarrow> Lit rvec \<Rightarrow> Lit rvec \<Rightarrow> Lit \<Rightarrow> ('s, Cnf \<times> Lit rvec \<times> Lit \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>bv_add_contract c a b cin \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
        \<langle>rvec_length a \<le> urust_fuel \<and> rvec_length a < 2 ^ 56 \<and> rvec_length a \<le> rvec_length b \<and> cnf_ok c \<and>
         room (fst (add_m (st_of c) (rvec_elems a) (rvec_elems b) cin))\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>cnf_ok (fst r) \<and> st_of (fst r) = fst (add_m (st_of c) (rvec_elems a) (rvec_elems b) cin) \<and>
           rvec_elems (fst (snd r)) = fst (snd (add_m (st_of c) (rvec_elems a) (rvec_elems b) cin)) \<and>
           vok (fst (snd r)) \<and> snd (snd r) = (snd (snd (add_m (st_of c) (rvec_elems a) (rvec_elems b) cin)), TNil)\<rangle>)\<close>

lemma bv_add_spec [crush_specs]:
  shows \<open>\<Gamma>; bv_add c a b cin \<Turnstile>\<^sub>F bv_add_contract c a b cin\<close>
  apply (crush_boot f: bv_add_def contract: bv_add_contract_def)
  apply (crush_base)
  subgoal for cnf_ref carry_ref r_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gc cn gy y gr r gi i. cnf_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>cn \<star> carry_ref \<mapsto>\<langle>\<top>\<rangle> gy\<down>y \<star>
               r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i \<le> rvec_length a \<and> cnf_ok cn \<and>
                st_of cn = fst (foldl (add_step (rvec_elems a) (rvec_elems b)) (st_of c, [], cin) [0..<unat i]) \<and>
                rvec_elems r = fst (snd (foldl (add_step (rvec_elems a) (rvec_elems b)) (st_of c, [], cin) [0..<unat i])) \<and>
                vok r \<and>
                y = snd (snd (foldl (add_step (rvec_elems a) (rvec_elems b)) (st_of c, [], cin) [0..<unat i])) \<and>
                rvec_length a - unat i \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gc cn gy y gr r gi i. cnf_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>cn \<star> carry_ref \<mapsto>\<langle>\<top>\<rangle> gy\<down>y \<star>
               r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i < rvec_length a \<and> cnf_ok cn \<and>
                st_of cn = fst (foldl (add_step (rvec_elems a) (rvec_elems b)) (st_of c, [], cin) [0..<unat i]) \<and>
                rvec_elems r = fst (snd (foldl (add_step (rvec_elems a) (rvec_elems b)) (st_of c, [], cin) [0..<unat i])) \<and>
                vok r \<and>
                y = snd (snd (foldl (add_step (rvec_elems a) (rvec_elems b)) (st_of c, [], cin) [0..<unat i])) \<and>
                rvec_length a - unat i \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star>
          \<langle>cnf_ok (fst r) \<and> st_of (fst r) = fst (add_m (st_of c) (rvec_elems a) (rvec_elems b) cin) \<and>
           rvec_elems (fst (snd r)) = fst (snd (add_m (st_of c) (rvec_elems a) (rvec_elems b) cin)) \<and>
           vok (fst (snd r)) \<and> snd (snd r) = (snd (snd (add_m (st_of c) (rvec_elems a) (rvec_elems b) cin)), TNil)\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base)
    apply (auto simp add: word_less_nat_alt unat_of_nat_eq unat_of_nat_64 unat_word_Suc_simp antisym_conv add_m_def add_fold_count add_step_eq add_step_lt cnf_res_def room_def)
    done
  done

definition bv_partial_contract ::
  \<open>Cnf \<Rightarrow> Lit rvec \<Rightarrow> Lit \<Rightarrow> 64 word \<Rightarrow> ('s, Cnf \<times> Lit rvec \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>bv_partial_contract c a bi i \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
        \<langle>rvec_length a \<le> urust_fuel \<and> rvec_length a < 2 ^ 56 \<and> cnf_ok c \<and>
         room (fst (partial_m (st_of c) (rvec_elems a) bi (unat i)))\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>cnfv_res r (partial_m (st_of c) (rvec_elems a) bi (unat i))\<rangle>)\<close>

lemma bv_partial_spec [crush_specs]:
  shows \<open>\<Gamma>; bv_partial c a bi i \<Turnstile>\<^sub>F bv_partial_contract c a bi i\<close>
  apply (crush_boot f: bv_partial_def contract: bv_partial_contract_def)
  apply (crush_base)
  subgoal for cnf_ref r_ref j_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gc cn gr r gj j. cnf_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>cn \<star> r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star>
               can_alloc_reference \<star>
               \<langle>unat j \<le> rvec_length a \<and> cnf_ok cn \<and>
                st_of cn = fst (foldl (partial_step (rvec_elems a) bi (unat i)) (st_of c, []) [0..<unat j]) \<and>
                rvec_elems r = snd (foldl (partial_step (rvec_elems a) bi (unat i)) (st_of c, []) [0..<unat j]) \<and>
                vok r \<and> rvec_length a - unat j \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gc cn gr r gj j. cnf_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>cn \<star> r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star>
               can_alloc_reference \<star>
               \<langle>unat j < rvec_length a \<and> cnf_ok cn \<and>
                st_of cn = fst (foldl (partial_step (rvec_elems a) bi (unat i)) (st_of c, []) [0..<unat j]) \<and>
                rvec_elems r = snd (foldl (partial_step (rvec_elems a) bi (unat i)) (st_of c, []) [0..<unat j]) \<and>
                vok r \<and> rvec_length a - unat j \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>cnfv_res r (partial_m (st_of c) (rvec_elems a) bi (unat i))\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: cnfv_res_def)
    apply (auto simp add: word_less_nat_alt unat_of_nat_eq unat_of_nat_64 unat_word_Suc_simp antisym_conv partial_m_foldl partial_fold_count partial_step_def partial_step_lt unat_sub_not_less word_le_nat_alt cnf_res_def room_def)
    done
  done

text \<open>\<^verbatim>\<open>vec![x; n]\<close> of literals.\<close>
lemma from_elem_lit:
  \<open>rvec_from_elem_val (make_elem_layout 16 8) x n = Some r \<Longrightarrow> vok r \<and> rvec_elems r = replicate n x\<close>
  using from_elem_Some[of \<open>make_elem_layout 16 8\<close> x n r] by simp

definition bv_mul_contract ::
  \<open>Cnf \<Rightarrow> Lit rvec \<Rightarrow> Lit rvec \<Rightarrow> ('s, Cnf \<times> Lit rvec \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>bv_mul_contract c a b \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
        \<langle>rvec_length a \<le> urust_fuel \<and> rvec_length a < 2 ^ 56 \<and> rvec_length a \<le> rvec_length b \<and> cnf_ok c \<and>
         room (fst (mul_m (st_of c) (rvec_elems a) (rvec_elems b)))\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>cnfv_res r (mul_m (st_of c) (rvec_elems a) (rvec_elems b))\<rangle>)\<close>

lemma bv_mul_spec [crush_specs]:
  shows \<open>\<Gamma>; bv_mul c a b \<Turnstile>\<^sub>F bv_mul_contract c a b\<close>
  apply (crush_boot f: bv_mul_def contract: bv_mul_contract_def)
  apply (crush_base simp add: unat_of_nat_eq unat_of_nat_64 from_elem_Some)
  subgoal for cnf_ref acc0 acc_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gc cn gr r gi i. cnf_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>cn \<star> acc_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
               can_alloc_reference \<star>
               \<langle>unat i \<le> rvec_length a \<and> cnf_ok cn \<and>
                st_of cn = fst (foldl (mul_step (rvec_elems a) (rvec_elems b))
                  (st_of c, replicate (rvec_length a) (lconst False)) [0..<unat i]) \<and>
                rvec_elems r = snd (foldl (mul_step (rvec_elems a) (rvec_elems b))
                  (st_of c, replicate (rvec_length a) (lconst False)) [0..<unat i]) \<and> vok r \<and>
                room (fst (mul_m (st_of c) (rvec_elems a) (rvec_elems b))) \<and>
                rvec_length a - unat i \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gc cn gr r gi i. cnf_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>cn \<star> acc_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
               can_alloc_reference \<star>
               \<langle>unat i < rvec_length a \<and> cnf_ok cn \<and>
                st_of cn = fst (foldl (mul_step (rvec_elems a) (rvec_elems b))
                  (st_of c, replicate (rvec_length a) (lconst False)) [0..<unat i]) \<and>
                rvec_elems r = snd (foldl (mul_step (rvec_elems a) (rvec_elems b))
                  (st_of c, replicate (rvec_length a) (lconst False)) [0..<unat i]) \<and> vok r \<and>
                room (fst (mul_m (st_of c) (rvec_elems a) (rvec_elems b))) \<and>
                rvec_length a - unat i \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>cnfv_res r (mul_m (st_of c) (rvec_elems a) (rvec_elems b))\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: cnfv_res_def)
    apply (auto simp add: word_less_nat_alt unat_of_nat_eq unat_of_nat_64 unat_word_Suc_simp mul_step_eq mul_step_lt mul_m_fold room_def dest!: from_elem_lit)
    done
  done

definition bv_eq_contract ::
  \<open>Cnf \<Rightarrow> Lit rvec \<Rightarrow> Lit rvec \<Rightarrow> ('s, Cnf \<times> Lit \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>bv_eq_contract c a b \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
        \<langle>rvec_length a \<le> urust_fuel \<and> rvec_length a < 2 ^ 56 \<and> rvec_length a \<le> rvec_length b \<and> cnf_ok c \<and>
         room (fst (eq_m (st_of c) (rvec_elems a) (rvec_elems b)))\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>cnf_res r (eq_m (st_of c) (rvec_elems a) (rvec_elems b))\<rangle>)\<close>

lemma bv_eq_spec [crush_specs]:
  shows \<open>\<Gamma>; bv_eq c a b \<Turnstile>\<^sub>F bv_eq_contract c a b\<close>
  apply (crush_boot f: bv_eq_def contract: bv_eq_contract_def)
  apply (crush_base)
  subgoal for cnf_ref r_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gc cn gr r gi i. cnf_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>cn \<star> r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
               can_alloc_reference \<star>
               \<langle>unat i \<le> rvec_length a \<and> cnf_ok cn \<and>
                st_of cn = fst (foldl (eq_step (rvec_elems a) (rvec_elems b)) (st_of c, lconst True) [0..<unat i]) \<and>
                r = snd (foldl (eq_step (rvec_elems a) (rvec_elems b)) (st_of c, lconst True) [0..<unat i]) \<and>
                rvec_length a - unat i \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gc cn gr r gi i. cnf_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>cn \<star> r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
               can_alloc_reference \<star>
               \<langle>unat i < rvec_length a \<and> cnf_ok cn \<and>
                st_of cn = fst (foldl (eq_step (rvec_elems a) (rvec_elems b)) (st_of c, lconst True) [0..<unat i]) \<and>
                r = snd (foldl (eq_step (rvec_elems a) (rvec_elems b)) (st_of c, lconst True) [0..<unat i]) \<and>
                rvec_length a - unat i \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>cnf_res r (eq_m (st_of c) (rvec_elems a) (rvec_elems b))\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: cnf_res_def)
    apply (auto simp add: word_less_nat_alt unat_of_nat_eq unat_of_nat_64 unat_word_Suc_simp antisym_conv eq_m_def eq_step_eq eq_step_lt room_def)
    done
  done

definition bv_ult_contract ::
  \<open>Cnf \<Rightarrow> Lit rvec \<Rightarrow> Lit rvec \<Rightarrow> ('s, Cnf \<times> Lit \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>bv_ult_contract c a b \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
        \<langle>rvec_length a \<le> urust_fuel \<and> rvec_length a < 2 ^ 56 \<and> rvec_length b \<le> urust_fuel \<and>
         rvec_length b < 2 ^ 56 \<and> rvec_length a \<le> rvec_length b \<and> cnf_ok c \<and>
         room (fst (ult_m (st_of c) (rvec_elems a) (rvec_elems b)))\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>cnf_res r (ult_m (st_of c) (rvec_elems a) (rvec_elems b))\<rangle>)\<close>

lemma bv_ult_spec [crush_specs]:
  shows \<open>\<Gamma>; bv_ult c a b \<Turnstile>\<^sub>F bv_ult_contract c a b\<close>
  apply (crush_boot f: bv_ult_def contract: bv_ult_contract_def)
  apply (crush_base simp add: cnf_res_def)
  done

definition bv_ite_contract ::
  \<open>Cnf \<Rightarrow> Lit \<Rightarrow> Lit rvec \<Rightarrow> Lit rvec \<Rightarrow> ('s, Cnf \<times> Lit rvec \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>bv_ite_contract cn x a b \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
        \<langle>rvec_length a \<le> urust_fuel \<and> rvec_length a < 2 ^ 56 \<and> rvec_length a \<le> rvec_length b \<and> cnf_ok cn \<and>
         room (fst (ite_vec_m (st_of cn) x (rvec_elems a) (rvec_elems b)))\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>cnfv_res r (ite_vec_m (st_of cn) x (rvec_elems a) (rvec_elems b))\<rangle>)\<close>

lemma bv_ite_spec [crush_specs]:
  shows \<open>\<Gamma>; bv_ite cn x a b \<Turnstile>\<^sub>F bv_ite_contract cn x a b\<close>
  apply (crush_boot f: bv_ite_def contract: bv_ite_contract_def)
  apply (crush_base)
  subgoal for cnf_ref r_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gc cc gr r gi i. cnf_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>cc \<star> r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
               can_alloc_reference \<star>
               \<langle>unat i \<le> rvec_length a \<and> cnf_ok cc \<and>
                st_of cc = fst (foldl (ite_step x (rvec_elems a) (rvec_elems b)) (st_of cn, []) [0..<unat i]) \<and>
                rvec_elems r = snd (foldl (ite_step x (rvec_elems a) (rvec_elems b)) (st_of cn, []) [0..<unat i]) \<and>
                vok r \<and> rvec_length a - unat i \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gc cc gr r gi i. cnf_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>cc \<star> r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
               can_alloc_reference \<star>
               \<langle>unat i < rvec_length a \<and> cnf_ok cc \<and>
                st_of cc = fst (foldl (ite_step x (rvec_elems a) (rvec_elems b)) (st_of cn, []) [0..<unat i]) \<and>
                rvec_elems r = snd (foldl (ite_step x (rvec_elems a) (rvec_elems b)) (st_of cn, []) [0..<unat i]) \<and>
                vok r \<and> rvec_length a - unat i \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>cnfv_res r (ite_vec_m (st_of cn) x (rvec_elems a) (rvec_elems b))\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: cnfv_res_def)
    apply (auto simp add: word_less_nat_alt unat_of_nat_eq unat_of_nat_64 unat_word_Suc_simp antisym_conv ite_vec_m_foldl ite_fold_count ite_step_def ite_step_lt cnf_res_def room_def)
    done
  done

definition bv_shift_contract ::
  \<open>Cnf \<Rightarrow> Lit rvec \<Rightarrow> Lit rvec \<Rightarrow> bool \<Rightarrow> ('s, Cnf \<times> Lit rvec \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>bv_shift_contract c a b left \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
        \<langle>rvec_length a \<le> urust_fuel \<and> rvec_length a < 2 ^ 56 \<and> rvec_length b \<le> rvec_length a \<and> cnf_ok c \<and>
         room (fst (shift_m (st_of c) (rvec_elems a) (rvec_elems b) left))\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>cnfv_res r (shift_m (st_of c) (rvec_elems a) (rvec_elems b) left)\<rangle>)\<close>

lemma bv_shift_spec [crush_specs]:
  shows \<open>\<Gamma>; bv_shift c a b left \<Turnstile>\<^sub>F bv_shift_contract c a b left\<close>
  apply (crush_boot f: bv_shift_def contract: bv_shift_contract_def)
  apply (crush_base simp add: unat_of_nat_eq unat_of_nat_64)
  subgoal for cnf_ref r0 r_ref g_ref p_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gc cn gr r gg g gp p gi i. cnf_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>cn \<star> r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star>
               g_ref \<mapsto>\<langle>\<top>\<rangle> gg\<down>g \<star> p_ref \<mapsto>\<langle>\<top>\<rangle> gp\<down>p \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i \<le> rvec_length b \<and> cnf_ok cn \<and>
                st_of cn = fst (shF (rvec_elems a) (rvec_elems b) left (st_of c) (unat i)) \<and>
                rvec_elems r = fst (snd (shF (rvec_elems a) (rvec_elems b) left (st_of c) (unat i))) \<and>
                g = fst (snd (snd (shF (rvec_elems a) (rvec_elems b) left (st_of c) (unat i)))) \<and>
                unat p = snd (snd (snd (shF (rvec_elems a) (rvec_elems b) left (st_of c) (unat i)))) \<and>
                rvec_length b - unat i \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gc cn gr r gg g gp p gi i. cnf_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>cn \<star> r_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>r \<star>
               g_ref \<mapsto>\<langle>\<top>\<rangle> gg\<down>g \<star> p_ref \<mapsto>\<langle>\<top>\<rangle> gp\<down>p \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i < rvec_length b \<and> cnf_ok cn \<and>
                st_of cn = fst (shF (rvec_elems a) (rvec_elems b) left (st_of c) (unat i)) \<and>
                rvec_elems r = fst (snd (shF (rvec_elems a) (rvec_elems b) left (st_of c) (unat i))) \<and>
                g = fst (snd (snd (shF (rvec_elems a) (rvec_elems b) left (st_of c) (unat i)))) \<and>
                unat p = snd (snd (snd (shF (rvec_elems a) (rvec_elems b) left (st_of c) (unat i)))) \<and>
                rvec_length b - unat i \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>cnfv_res r (shift_m (st_of c) (rvec_elems a) (rvec_elems b) left)\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: cnfv_res_def)
    apply (auto simp add: word_less_nat_alt word_le_nat_alt unat_of_nat_eq unat_of_nat_64 unat_word_Suc_simp shF_len
        shF_Suc_stage shF_Suc_or unat_len_sub cnf_res_def room_def dest!: from_elem_lit)
    apply (auto intro: shF_or_lt shF_stage_lt simp: unat_double_p)
    apply ((simp_all add: shift_m_shF)?)
    apply ((rule le_less_trans[rotated], assumption, simp add: shF_mono)+)?
    apply (all \<open>(rule shF_or_lt shF_stage_lt; assumption)?\<close>)
    done
  done

definition bv_divrem_contract ::
  \<open>Cnf \<Rightarrow> Lit rvec \<Rightarrow> Lit rvec \<Rightarrow> ('s, Cnf \<times> Lit rvec \<times> Lit rvec \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>bv_divrem_contract c a b \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
        \<langle>rvec_length b = rvec_length a \<and> 2 * rvec_length a \<le> urust_fuel \<and> 2 * rvec_length a < 2 ^ 56 \<and>
         cnf_ok c \<and> room (fst (divrem_m (st_of c) (rvec_elems a) (rvec_elems b)))\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>cnf_ok (fst r) \<and> st_of (fst r) = fst (divrem_m (st_of c) (rvec_elems a) (rvec_elems b)) \<and>
           rvec_elems (fst (snd r)) = fst (snd (divrem_m (st_of c) (rvec_elems a) (rvec_elems b))) \<and>
           vok (fst (snd r)) \<and>
           rvec_elems (fst (snd (snd r))) = snd (snd (divrem_m (st_of c) (rvec_elems a) (rvec_elems b))) \<and>
           vok (fst (snd (snd r))) \<and> snd (snd (snd r)) = TNil\<rangle>)\<close>

lemma bv_divrem_spec [crush_specs]:
  shows \<open>\<Gamma>; bv_divrem c a b \<Turnstile>\<^sub>F bv_divrem_contract c a b\<close>
  apply (crush_boot f: bv_divrem_def contract: bv_divrem_contract_def)
  apply (crush_base simp add: cnfv_res_def)
  apply (auto simp add: unat_of_nat_eq unat_of_nat_64 unat_double unat_double2 divrem_m_dr dr_fold dr_lt cnf_res_def room_def dest!: from_elem_lit)
  done

end

section \<open>Blasting terms: pure facts\<close>

lemma blast_bin_m_simps [simp]:
  \<open>blast_bin_m s BinOp_And a b = bitwise_m BinOp_And s a b\<close>
  \<open>blast_bin_m s BinOp_Or a b = bitwise_m BinOp_Or s a b\<close>
  \<open>blast_bin_m s BinOp_Xor a b = bitwise_m BinOp_Xor s a b\<close>
  \<open>blast_bin_m s BinOp_Add a b = (fst (add_m s a b (lconst False)), fst (snd (add_m s a b (lconst False))))\<close>
  \<open>blast_bin_m s BinOp_Mul a b = mul_m s a b\<close>
  \<open>blast_bin_m s BinOp_Udiv a b = (fst (divrem_m s a b), fst (snd (divrem_m s a b)))\<close>
  \<open>blast_bin_m s BinOp_Urem a b = (fst (divrem_m s a b), snd (snd (divrem_m s a b)))\<close>
  \<open>blast_bin_m s BinOp_Shl a b = shift_m s a b True\<close>
  \<open>blast_bin_m s BinOp_Lshr a b = shift_m s a b False\<close>
  \<open>blast_bin_m s BinOp_Concat a b = (s, concat_m a b)\<close>
  \<open>blast_bin_m s BinOp_Eq a b = (fst (eq_m s a b), [snd (eq_m s a b)])\<close>
  \<open>blast_bin_m s BinOp_Ult a b = (fst (ult_m s a b), [snd (ult_m s a b)])\<close>
  by (simp_all add: blast_bin_m_def split_def Let_def)

text \<open>The precondition of \<^verbatim>\<open>blast_bin\<close>.\<close>
definition bin_ok :: \<open>nat \<Rightarrow> st \<Rightarrow> BinOp \<Rightarrow> Lit list \<Rightarrow> Lit list \<Rightarrow> bool\<close> where
  \<open>bin_ok N s op a b \<equiv>
     length a \<le> N \<and> length a < 2 ^ 56 \<and> (op \<noteq> BinOp_Concat \<longrightarrow> length b = length a) \<and>
     ((op = BinOp_Udiv \<or> op = BinOp_Urem) \<longrightarrow> 2 * length a \<le> N \<and> 2 * length a < 2 ^ 56) \<and>
     (op = BinOp_Concat \<longrightarrow> length b + length a < 2 ^ 56) \<and> room (fst (blast_bin_m s op a b))\<close>

lemma blast_bin_m_mono: \<open>sz s \<le> sz (fst (blast_bin_m s op a b))\<close>
  by (cases op) (auto intro: le_SucI)

lemma blast_bin_m_length:
  \<open>(op \<noteq> BinOp_Concat \<longrightarrow> length b = length a) \<Longrightarrow>
   length (snd (blast_bin_m s op a b)) = bin_width op (length a) (length b)\<close>
  by (cases op) (simp_all add: bin_width_def)

lemma blast_m_simps':
  \<open>blast_m vs dl s (CoreTermL_Not a) = (fst (blast_m vs dl s a), not_m (snd (blast_m vs dl s a)))\<close>
  \<open>blast_m vs dl s (CoreTermL_Bin op a b) =
     blast_bin_m (fst (blast_m vs dl (fst (blast_m vs dl s a)) b)) op (snd (blast_m vs dl s a))
       (snd (blast_m vs dl (fst (blast_m vs dl s a)) b))\<close>
  \<open>blast_m vs dl s (CoreTermL_Extract hi lo a) =
     (fst (blast_m vs dl s a), extract_m (snd (blast_m vs dl s a)) (unat hi) (unat lo))\<close>
  \<open>blast_m vs dl s (CoreTermL_Ite c a b) =
     ite_vec_m (fst (blast_m vs dl (fst (blast_m vs dl (fst (blast_m vs dl s c)) a)) b))
       (snd (blast_m vs dl s c) ! 0) (snd (blast_m vs dl (fst (blast_m vs dl s c)) a))
       (snd (blast_m vs dl (fst (blast_m vs dl (fst (blast_m vs dl s c)) a)) b))\<close>
  by (simp_all add: split_def Let_def)

declare blast_m.simps(4-7) [simp del]
declare blast_m_simps' [simp]

lemma blast_m_mono: \<open>sz s \<le> sz (fst (blast_m vs dl s t))\<close>
proof (induction t arbitrary: s)
  case (CoreTermL_Not a)
  then show ?case by simp
next
  case (CoreTermL_Bin op a b)
  have \<open>sz s \<le> sz (fst (blast_m vs dl s a))\<close> by (rule CoreTermL_Bin.IH(1))
  also have \<open>\<dots> \<le> sz (fst (blast_m vs dl (fst (blast_m vs dl s a)) b))\<close> by (rule CoreTermL_Bin.IH(2))
  also have \<open>\<dots> \<le> sz (fst (blast_m vs dl s (CoreTermL_Bin op a b)))\<close> by (simp add: blast_bin_m_mono)
  finally show ?case .
next
  case (CoreTermL_Extract hi lo a)
  then show ?case by simp
next
  case (CoreTermL_Ite c a b)
  have \<open>sz s \<le> sz (fst (blast_m vs dl s c))\<close> by (rule CoreTermL_Ite.IH(1))
  also have \<open>\<dots> \<le> sz (fst (blast_m vs dl (fst (blast_m vs dl s c)) a))\<close> by (rule CoreTermL_Ite.IH(2))
  also have \<open>\<dots> \<le> sz (fst (blast_m vs dl (fst (blast_m vs dl (fst (blast_m vs dl s c)) a)) b))\<close>
    by (rule CoreTermL_Ite.IH(3))
  also have \<open>\<dots> \<le> sz (fst (blast_m vs dl s (CoreTermL_Ite c a b)))\<close> by simp
  finally show ?case .
qed simp_all

lemma blast_m_length:
  \<open>cwt (map length vs) (map length dl) t \<Longrightarrow>
   length (snd (blast_m vs dl s t)) = cwidth (map length vs) (map length dl) t\<close>
proof (induction t arbitrary: s)
  case (CoreTermL_Bin op a b)
  then have \<open>length (snd (blast_m vs dl s a)) = cwidth (map length vs) (map length dl) a\<close>
    \<open>length (snd (blast_m vs dl (fst (blast_m vs dl s a)) b)) = cwidth (map length vs) (map length dl) b\<close>
    by simp_all
  then show ?case using CoreTermL_Bin.prems
    by (cases \<open>op = BinOp_Concat\<close>) (simp_all add: blast_bin_m_length bin_width_def split: BinOp_splits)
next
  case (CoreTermL_Extract hi lo a)
  then show ?case by (simp add: Suc_diff_le)
qed simp_all

lemma subterms_self [simp]: \<open>t \<in> set (csubterms t)\<close>
  by (cases t) simp_all

text \<open>The precondition of \<^verbatim>\<open>blast\<close>: what each call of the recursion needs.\<close>
primrec bok :: \<open>nat \<Rightarrow> Lit list list \<Rightarrow> Lit list list \<Rightarrow> st \<Rightarrow> CoreTermL \<Rightarrow> bool\<close> where
  \<open>bok N vs dl s (CoreTermL_Const bs) = (length bs \<le> N \<and> length bs < 2 ^ 56)\<close>
| \<open>bok N vs dl s (CoreTermL_Var i) = (unat i < length vs)\<close>
| \<open>bok N vs dl s (CoreTermL_Ref i) = (unat i < length dl)\<close>
| \<open>bok N vs dl s (CoreTermL_Not a) =
     (bok N vs dl s a \<and> length (snd (blast_m vs dl s a)) \<le> N \<and> length (snd (blast_m vs dl s a)) < 2 ^ 56)\<close>
| \<open>bok N vs dl s (CoreTermL_Bin op a b) =
     (bok N vs dl s a \<and> bok N vs dl (fst (blast_m vs dl s a)) b \<and>
      bin_ok N (fst (blast_m vs dl (fst (blast_m vs dl s a)) b)) op (snd (blast_m vs dl s a))
        (snd (blast_m vs dl (fst (blast_m vs dl s a)) b)))\<close>
| \<open>bok N vs dl s (CoreTermL_Extract hi lo a) =
     (bok N vs dl s a \<and> unat lo \<le> unat hi \<and> unat hi < length (snd (blast_m vs dl s a)) \<and>
      length (snd (blast_m vs dl s a)) < 2 ^ 56 \<and> unat hi - unat lo + 1 \<le> N)\<close>
| \<open>bok N vs dl s (CoreTermL_Ite c a b) =
     (bok N vs dl s c \<and> bok N vs dl (fst (blast_m vs dl s c)) a \<and>
      bok N vs dl (fst (blast_m vs dl (fst (blast_m vs dl s c)) a)) b \<and>
      0 < length (snd (blast_m vs dl s c)) \<and>
      length (snd (blast_m vs dl (fst (blast_m vs dl s c)) a)) \<le> N \<and>
      length (snd (blast_m vs dl (fst (blast_m vs dl s c)) a)) < 2 ^ 56 \<and>
      length (snd (blast_m vs dl (fst (blast_m vs dl s c)) a)) \<le>
        length (snd (blast_m vs dl (fst (blast_m vs dl (fst (blast_m vs dl s c)) a)) b)) \<and>
      room (fst (ite_vec_m (fst (blast_m vs dl (fst (blast_m vs dl (fst (blast_m vs dl s c)) a)) b))
        (snd (blast_m vs dl s c) ! 0) (snd (blast_m vs dl (fst (blast_m vs dl s c)) a))
        (snd (blast_m vs dl (fst (blast_m vs dl (fst (blast_m vs dl s c)) a)) b)))))\<close>

lemma divrem_len: \<open>room (fst (divrem_m s a b)) \<Longrightarrow> 2 * length a < 2 ^ 56\<close>
  using dr_counts[of s a b] divrem_m_count(1)[of s a b] unfolding room_def by linarith

lemma bok_intro:
  assumes \<open>cwt (map length vs) (map length dl) t\<close>
    \<open>\<forall>u \<in> set (csubterms t). 2 * cwidth (map length vs) (map length dl) u + 2 \<le> M\<close>
    \<open>M \<le> N\<close> \<open>M < 2 ^ 57\<close> \<open>room (fst (blast_m vs dl s t))\<close>
  shows \<open>bok N vs dl s t\<close>
  using assms
proof (induction t arbitrary: s)
  case (CoreTermL_Const bs)
  then show ?case by simp
next
  case (CoreTermL_Var i)
  then show ?case by simp
next
  case (CoreTermL_Ref i)
  then show ?case by simp
next
  case (CoreTermL_Not a)
  have w: \<open>2 * cwidth (map length vs) (map length dl) a + 2 \<le> M\<close>
    using CoreTermL_Not.prems(2) by simp
  have la: \<open>length (snd (blast_m vs dl s a)) = cwidth (map length vs) (map length dl) a\<close>
    using CoreTermL_Not.prems(1) by (simp add: blast_m_length)
  have \<open>bok N vs dl s a\<close>
    by (rule CoreTermL_Not.IH) (insert CoreTermL_Not.prems, simp_all)
  then show ?case using w la CoreTermL_Not.prems(3,4) by simp
next
  case (CoreTermL_Bin op a b)
  let ?W = \<open>map length vs\<close> and ?D = \<open>map length dl\<close>
  let ?s1 = \<open>fst (blast_m vs dl s a)\<close>
  let ?s2 = \<open>fst (blast_m vs dl ?s1 b)\<close>
  have fin: \<open>room (fst (blast_bin_m ?s2 op (snd (blast_m vs dl s a)) (snd (blast_m vs dl ?s1 b))))\<close>
    using CoreTermL_Bin.prems(5) by simp
  have m2: \<open>room ?s2\<close>
    using room_mono[OF blast_bin_m_mono fin] .
  have m1: \<open>room ?s1\<close>
    using room_mono[OF blast_m_mono m2] .
  have cwt: \<open>cwt ?W ?D a\<close> \<open>cwt ?W ?D b\<close> \<open>op \<noteq> BinOp_Concat \<longrightarrow> cwidth ?W ?D a = cwidth ?W ?D b\<close>
    using CoreTermL_Bin.prems(1) by simp_all
  have sub: \<open>\<forall>u \<in> set (csubterms a). 2 * cwidth ?W ?D u + 2 \<le> M\<close> \<open>\<forall>u \<in> set (csubterms b). 2 * cwidth ?W ?D u + 2 \<le> M\<close>
    \<open>2 * cwidth ?W ?D (CoreTermL_Bin op a b) + 2 \<le> M\<close>
    using CoreTermL_Bin.prems(2) by simp_all
  have wa: \<open>2 * cwidth ?W ?D a + 2 \<le> M\<close>
    using sub(1) subterms_self[of a] by blast
  have la: \<open>length (snd (blast_m vs dl s a)) = cwidth ?W ?D a\<close>
    using cwt(1) by (rule blast_m_length)
  have lb: \<open>length (snd (blast_m vs dl ?s1 b)) = cwidth ?W ?D b\<close>
    using cwt(2) by (rule blast_m_length)
  have oka: \<open>bok N vs dl s a\<close>
    using cwt(1) sub(1) CoreTermL_Bin.prems(3,4) m1 by (rule CoreTermL_Bin.IH(1))
  have okb: \<open>bok N vs dl ?s1 b\<close>
    using cwt(2) sub(2) CoreTermL_Bin.prems(3,4) m2 by (rule CoreTermL_Bin.IH(2))
  have \<open>bin_ok N ?s2 op (snd (blast_m vs dl s a)) (snd (blast_m vs dl ?s1 b))\<close>
    unfolding bin_ok_def
    using fin la lb cwt(3) wa sub(3) CoreTermL_Bin.prems(3,4)
      divrem_len[of ?s2 \<open>snd (blast_m vs dl s a)\<close> \<open>snd (blast_m vs dl ?s1 b)\<close>]
    by (cases op) (simp_all add: bin_width_def)
  then show ?case using oka okb by simp
next
  case (CoreTermL_Extract hi lo a)
  have w: \<open>2 * cwidth (map length vs) (map length dl) (CoreTermL_Extract hi lo a) + 2 \<le> M\<close>
    using CoreTermL_Extract.prems(2) by simp
  have cwt: \<open>cwt (map length vs) (map length dl) a\<close> \<open>unat lo \<le> unat hi\<close>
    \<open>unat hi < cwidth (map length vs) (map length dl) a\<close>
    using CoreTermL_Extract.prems(1) by simp_all
  have wa: \<open>2 * cwidth (map length vs) (map length dl) a + 2 \<le> M\<close>
    using CoreTermL_Extract.prems(2) subterms_self[of a] by auto
  have \<open>bok N vs dl s a\<close>
    by (rule CoreTermL_Extract.IH) (insert CoreTermL_Extract.prems, simp_all)
  then show ?case using w cwt wa CoreTermL_Extract.prems(3,4) by (simp add: blast_m_length)
next
  case (CoreTermL_Ite c a b)
  let ?W = \<open>map length vs\<close> and ?D = \<open>map length dl\<close>
  let ?s1 = \<open>fst (blast_m vs dl s c)\<close>
  let ?s2 = \<open>fst (blast_m vs dl ?s1 a)\<close>
  let ?s3 = \<open>fst (blast_m vs dl ?s2 b)\<close>
  have fin: \<open>room (fst (ite_vec_m ?s3 (snd (blast_m vs dl s c) ! 0) (snd (blast_m vs dl ?s1 a))
      (snd (blast_m vs dl ?s2 b))))\<close>
    using CoreTermL_Ite.prems(5) by (simp add: split_def Let_def)
  have m3: \<open>room ?s3\<close> using room_mono[OF ite_vec_m_count(1) fin] .
  have m2: \<open>room ?s2\<close> using room_mono[OF blast_m_mono m3] .
  have m1: \<open>room ?s1\<close> using room_mono[OF blast_m_mono m2] .
  have cwt: \<open>cwt ?W ?D c\<close> \<open>cwt ?W ?D a\<close> \<open>cwt ?W ?D b\<close> \<open>cwidth ?W ?D c = 1\<close> \<open>cwidth ?W ?D a = cwidth ?W ?D b\<close>
    using CoreTermL_Ite.prems(1) by simp_all
  have sub: \<open>\<forall>u \<in> set (csubterms c). 2 * cwidth ?W ?D u + 2 \<le> M\<close>
    \<open>\<forall>u \<in> set (csubterms a). 2 * cwidth ?W ?D u + 2 \<le> M\<close> \<open>\<forall>u \<in> set (csubterms b). 2 * cwidth ?W ?D u + 2 \<le> M\<close>
    using CoreTermL_Ite.prems(2) by simp_all
  have wa: \<open>2 * cwidth ?W ?D a + 2 \<le> M\<close>
    using sub(2) subterms_self[of a] by blast
  have lc: \<open>length (snd (blast_m vs dl s c)) = 1\<close>
    using blast_m_length[OF cwt(1)] cwt(4) by simp
  have la: \<open>length (snd (blast_m vs dl ?s1 a)) = cwidth ?W ?D a\<close>
    using cwt(2) by (rule blast_m_length)
  have lb: \<open>length (snd (blast_m vs dl ?s2 b)) = cwidth ?W ?D b\<close>
    using cwt(3) by (rule blast_m_length)
  have okc: \<open>bok N vs dl s c\<close>
    using cwt(1) sub(1) CoreTermL_Ite.prems(3,4) m1 by (rule CoreTermL_Ite.IH(1))
  have oka: \<open>bok N vs dl ?s1 a\<close>
    using cwt(2) sub(2) CoreTermL_Ite.prems(3,4) m2 by (rule CoreTermL_Ite.IH(2))
  have okb: \<open>bok N vs dl ?s2 b\<close>
    using cwt(3) sub(3) CoreTermL_Ite.prems(3,4) m3 by (rule CoreTermL_Ite.IH(3))
  show ?case using okc oka okb lc la lb cwt(5) wa fin CoreTermL_Ite.prems(3,4) by simp
qed

section \<open>Encoding a problem: pure facts\<close>

subsection \<open>Sorts\<close>

lemma def_widths_append: \<open>cdef_widths ws ds (xs @ ys) = cdef_widths ws (cdef_widths ws ds xs) ys\<close>
  by (induction xs arbitrary: ds) simp_all

lemma defs_wt_append:
  \<open>cdefs_wt ws ds (xs @ ys) = (cdefs_wt ws ds xs \<and> cdefs_wt ws (cdef_widths ws ds xs) ys)\<close>
  by (induction xs arbitrary: ds) auto

lemma def_widths_prefix: \<open>\<exists>e. cdef_widths ws ds xs = ds @ e\<close>
proof (induction xs arbitrary: ds)
  case Nil
  show ?case by simp
next
  case (Cons d dd)
  obtain e where \<open>cdef_widths ws (ds @ [cwidth ws ds d]) dd = (ds @ [cwidth ws ds d]) @ e\<close>
    using Cons.IH by blast
  then show ?case by simp
qed

lemma def_widths_take_Suc:
  \<open>j < length ts \<Longrightarrow> cdef_widths ws [] (take (Suc j) ts) =
     cdef_widths ws [] (take j ts) @ [cwidth ws (cdef_widths ws [] (take j ts)) (ts ! j)]\<close>
  by (simp add: take_Suc_conv_app_nth def_widths_append)

lemma defs_wt_nth:
  assumes \<open>cdefs_wt ws [] ts\<close> \<open>j < length ts\<close>
  shows \<open>cwt ws (cdef_widths ws [] (take j ts)) (ts ! j)\<close>
proof -
  have \<open>cdefs_wt ws [] (take j ts @ ts ! j # drop (Suc j) ts)\<close>
    using assms(1) by (subst (asm) id_take_nth_drop[OF assms(2)])
  then show ?thesis by (simp add: defs_wt_append)
qed

lemma wt_subterms: \<open>cwt ws ds t \<Longrightarrow> u \<in> set (csubterms t) \<Longrightarrow> cwt ws ds u\<close>
  by (induction t) auto

lemma wt_width_append: \<open>cwt ws ds t \<Longrightarrow> cwidth ws (ds @ e) t = cwidth ws ds t\<close>
  by (induction t) (auto simp: nth_append split: BinOp_splits)

lemma tbound_size: \<open>Suc (size t) \<le> tbound ws ds t\<close>
  by (simp add: tbound_def)

lemma tbound_width: \<open>u \<in> set (csubterms t) \<Longrightarrow> 2 * cwidth ws ds u + 2 \<le> tbound ws ds t\<close>
proof -
  assume u: \<open>u \<in> set (csubterms t)\<close>
  have \<open>2 * cwidth ws ds u + 2 \<in> set (map (\<lambda>u. 2 * cwidth ws ds u + 2) (csubterms t))\<close>
    using u by force
  then have \<open>2 * cwidth ws ds u + 2 \<le> Max (set (map (\<lambda>u. 2 * cwidth ws ds u + 2) (csubterms t)))\<close>
    by (intro Max_ge) simp_all
  then show ?thesis unfolding tbound_def by simp
qed

subsection \<open>The fuel bound\<close>

definition fb_set :: \<open>CoreProblemL \<Rightarrow> nat set\<close> where
  \<open>fb_set p \<equiv>
     {fst (fst (encode_m p)) + 2, length (snd (fst (encode_m p))) + 2,
      2 * (fst (fst (encode_m p)) + length (snd (fst (encode_m p)))), 2 * length (cvar_widths p) + 2,
      2 * length (CoreProblemL_defs p) + 2, 2 * length (CoreProblemL_asserts p) + 2} \<union>
     set (map (\<lambda>w. w + 2) (cvar_widths p)) \<union>
     set (map (\<lambda>c. length c + 2) (snd (fst (encode_m p)))) \<union>
     set (map (tbound (cvar_widths p) (cdef_widths (cvar_widths p) [] (CoreProblemL_defs p)))
            (CoreProblemL_defs p @ CoreProblemL_asserts p))\<close>

lemma fuel_bound_fb_set: \<open>fuel_bound p = Max (fb_set p)\<close>
  by (simp only: fuel_bound_def fb_set_def Let_def split_def)

lemma fb_ge: \<open>x \<in> fb_set p \<Longrightarrow> x \<le> fuel_bound p\<close>
  unfolding fuel_bound_fb_set by (rule Max_ge) (simp_all add: fb_set_def)

lemma fb_facts:
  \<open>fst (fst (encode_m p)) + 2 \<le> fuel_bound p\<close>
  \<open>2 * sz (fst (encode_m p)) \<le> fuel_bound p\<close>
  \<open>2 * length (CoreProblemL_widths p) + 2 \<le> fuel_bound p\<close>
  \<open>2 * length (CoreProblemL_defs p) + 2 \<le> fuel_bound p\<close>
  \<open>2 * length (CoreProblemL_asserts p) + 2 \<le> fuel_bound p\<close>
  by (rule fb_ge; simp add: fb_set_def cvar_widths_def sz_def)+

lemma fb_width:
  assumes \<open>i < length (CoreProblemL_widths p)\<close>
  shows \<open>unat (CoreProblemL_widths p ! i) + 2 \<le> fuel_bound p\<close>
  using nth_mem[OF assms] by (intro fb_ge) (auto simp: fb_set_def cvar_widths_def)

lemma fb_tbound:
  \<open>t \<in> set (CoreProblemL_defs p) \<or> t \<in> set (CoreProblemL_asserts p) \<Longrightarrow>
   tbound (cvar_widths p) (cdef_widths (cvar_widths p) [] (CoreProblemL_defs p)) t \<le> fuel_bound p\<close>
  by (intro fb_ge) (auto simp: fb_set_def)

subsection \<open>The three loops of \<^verbatim>\<open>encode\<close>\<close>

definition enc_vars :: \<open>CoreProblemL \<Rightarrow> nat \<Rightarrow> st \<times> Lit list list\<close> where
  \<open>enc_vars p n \<equiv> foldl (vars_step (CoreProblemL_widths p)) (init_st, []) [0..<n]\<close>

abbreviation enc_vs :: \<open>CoreProblemL \<Rightarrow> Lit list list\<close> where
  \<open>enc_vs p \<equiv> snd (enc_vars p (length (CoreProblemL_widths p)))\<close>

definition enc_defs :: \<open>CoreProblemL \<Rightarrow> nat \<Rightarrow> st \<times> Lit list list\<close> where
  \<open>enc_defs p n \<equiv>
     foldl (defs_step (enc_vs p) (CoreProblemL_defs p)) (fst (enc_vars p (length (CoreProblemL_widths p))), []) [0..<n]\<close>

abbreviation enc_dl :: \<open>CoreProblemL \<Rightarrow> Lit list list\<close> where
  \<open>enc_dl p \<equiv> snd (enc_defs p (length (CoreProblemL_defs p)))\<close>

definition enc_asserts :: \<open>CoreProblemL \<Rightarrow> nat \<Rightarrow> st\<close> where
  \<open>enc_asserts p n \<equiv>
     foldl (asserts_step (enc_vs p) (enc_dl p) (CoreProblemL_asserts p)) (fst (enc_defs p (length (CoreProblemL_defs p))))
       [0..<n]\<close>

lemma encode_m_eq: \<open>encode_m p = (enc_asserts p (length (CoreProblemL_asserts p)), enc_vs p)\<close>
  by (simp add: encode_m_def enc_asserts_def enc_defs_def enc_vars_def split_def Let_def)

lemma enc_vars_simps [simp]:
  \<open>enc_vars p 0 = (init_st, [])\<close>
  \<open>enc_vars p (Suc n) =
     (fst (fresh_vec_m (fst (enc_vars p n)) (unat (CoreProblemL_widths p ! n))),
      snd (enc_vars p n) @ [snd (fresh_vec_m (fst (enc_vars p n)) (unat (CoreProblemL_widths p ! n)))])\<close>
  by (simp_all add: enc_vars_def vars_step_def split_def Let_def del: fresh_vec_m_simps)

lemma enc_defs_simps [simp]:
  \<open>enc_defs p 0 = (fst (enc_vars p (length (CoreProblemL_widths p))), [])\<close>
  \<open>enc_defs p (Suc n) =
     (fst (blast_m (enc_vs p) (snd (enc_defs p n)) (fst (enc_defs p n)) (CoreProblemL_defs p ! n)),
      snd (enc_defs p n) @ [snd (blast_m (enc_vs p) (snd (enc_defs p n)) (fst (enc_defs p n)) (CoreProblemL_defs p ! n))])\<close>
  by (simp_all add: enc_defs_def defs_step_def split_def Let_def)

lemma vecs_of_len: \<open>vecs_of v = xs \<Longrightarrow> rvec_length v = length xs\<close>
  by (metis vecs_of_simps(1))

lemma allvok_new: \<open>allvok (rvec_new_val l)\<close>
  by (simp add: allvok_def)

lemma size_ct_of [simp]: \<open>size (ct_of t) = size t\<close>
  by (induction t) simp_all

lemma rvec_length_vecs: \<open>rvec_length v = length (vecs_of v)\<close>
  by simp

lemma enc_vars_length [simp]: \<open>length (snd (enc_vars p n)) = n\<close>
  by (induction n) simp_all

lemma enc_defs_length [simp]: \<open>length (snd (enc_defs p n)) = n\<close>
  by (induction n) simp_all

lemma enc_asserts_simps [simp]:
  \<open>enc_asserts p 0 = fst (enc_defs p (length (CoreProblemL_defs p)))\<close>
  \<open>enc_asserts p (Suc n) =
     addc_m (fst (blast_m (enc_vs p) (enc_dl p) (enc_asserts p n) (CoreProblemL_asserts p ! n)))
       [snd (blast_m (enc_vs p) (enc_dl p) (enc_asserts p n) (CoreProblemL_asserts p ! n)) ! 0]\<close>
  by (simp_all add: enc_asserts_def asserts_step_def split_def Let_def)

lemma enc_vars_mono: \<open>m \<le> n \<Longrightarrow> sz (fst (enc_vars p m)) \<le> sz (fst (enc_vars p n))\<close>
  unfolding enc_vars_def
  by (rule foldl_upt_mono[where g=\<open>\<lambda>X. sz (fst X)\<close>]) (simp_all add: vars_step_def split_def Let_def sz_def)

lemma enc_defs_mono: \<open>m \<le> n \<Longrightarrow> sz (fst (enc_defs p m)) \<le> sz (fst (enc_defs p n))\<close>
  unfolding enc_defs_def
  by (rule foldl_upt_mono[where g=\<open>\<lambda>X. sz (fst X)\<close>]) (simp_all add: defs_step_def split_def Let_def blast_m_mono)

lemma enc_asserts_mono: \<open>m \<le> n \<Longrightarrow> sz (enc_asserts p m) \<le> sz (enc_asserts p n)\<close>
  unfolding enc_asserts_def
  by (rule foldl_upt_mono[where g=\<open>\<lambda>X. sz X\<close>])
     (auto simp add: asserts_step_def split_def Let_def intro: le_SucI blast_m_mono)

lemma enc_le:
  shows enc_asserts_le: \<open>n \<le> length (CoreProblemL_asserts p) \<Longrightarrow> sz (enc_asserts p n) \<le> sz (fst (encode_m p))\<close>
    and enc_defs_le: \<open>n \<le> length (CoreProblemL_defs p) \<Longrightarrow> sz (fst (enc_defs p n)) \<le> sz (fst (encode_m p))\<close>
    and enc_vars_le: \<open>n \<le> length (CoreProblemL_widths p) \<Longrightarrow> sz (fst (enc_vars p n)) \<le> sz (fst (encode_m p))\<close>
proof -
  have A: \<open>n \<le> length (CoreProblemL_asserts p) \<Longrightarrow> sz (enc_asserts p n) \<le> sz (fst (encode_m p))\<close> for n
    using enc_asserts_mono[of n \<open>length (CoreProblemL_asserts p)\<close> p] by (simp add: encode_m_eq)
  have D: \<open>n \<le> length (CoreProblemL_defs p) \<Longrightarrow> sz (fst (enc_defs p n)) \<le> sz (fst (encode_m p))\<close> for n
    using enc_defs_mono[of n \<open>length (CoreProblemL_defs p)\<close> p] A[of 0] by simp
  have V: \<open>n \<le> length (CoreProblemL_widths p) \<Longrightarrow> sz (fst (enc_vars p n)) \<le> sz (fst (encode_m p))\<close> for n
    using enc_vars_mono[of n \<open>length (CoreProblemL_widths p)\<close> p] D[of 0] by simp
  show \<open>n \<le> length (CoreProblemL_asserts p) \<Longrightarrow> sz (enc_asserts p n) \<le> sz (fst (encode_m p))\<close> by (rule A)
  show \<open>n \<le> length (CoreProblemL_defs p) \<Longrightarrow> sz (fst (enc_defs p n)) \<le> sz (fst (encode_m p))\<close> by (rule D)
  show \<open>n \<le> length (CoreProblemL_widths p) \<Longrightarrow> sz (fst (enc_vars p n)) \<le> sz (fst (encode_m p))\<close> by (rule V)
qed

lemma enc_vars_len:
  \<open>n \<le> length (CoreProblemL_widths p) \<Longrightarrow> map length (snd (enc_vars p n)) = map unat (take n (CoreProblemL_widths p))\<close>
  by (induction n) (simp_all add: take_Suc_conv_app_nth)

lemma enc_vs_len [simp]: \<open>map length (enc_vs p) = cvar_widths p\<close>
  using enc_vars_len[of \<open>length (CoreProblemL_widths p)\<close> p] by (simp add: cvar_widths_def)

lemma enc_defs_len:
  assumes \<open>cproblem_wt p\<close>
  shows \<open>n \<le> length (CoreProblemL_defs p) \<Longrightarrow>
     map length (snd (enc_defs p n)) = cdef_widths (cvar_widths p) [] (take n (CoreProblemL_defs p))\<close>
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have n: \<open>n < length (CoreProblemL_defs p)\<close> using Suc.prems by simp
  have IH: \<open>map length (snd (enc_defs p n)) = cdef_widths (cvar_widths p) [] (take n (CoreProblemL_defs p))\<close>
    using Suc by simp
  have cwt: \<open>cwt (cvar_widths p) (cdef_widths (cvar_widths p) [] (take n (CoreProblemL_defs p))) (CoreProblemL_defs p ! n)\<close>
    using defs_wt_nth[OF _ n] assms by (simp add: cproblem_wt_def Let_def)
  have \<open>length (snd (blast_m (enc_vs p) (snd (enc_defs p n)) (fst (enc_defs p n)) (CoreProblemL_defs p ! n))) =
        cwidth (cvar_widths p) (cdef_widths (cvar_widths p) [] (take n (CoreProblemL_defs p))) (CoreProblemL_defs p ! n)\<close>
    using blast_m_length[of \<open>enc_vs p\<close> \<open>snd (enc_defs p n)\<close> \<open>CoreProblemL_defs p ! n\<close> \<open>fst (enc_defs p n)\<close>] cwt IH
    by simp
  then show ?case using IH n by (simp add: def_widths_take_Suc)
qed

lemma enc_dl_len:
  \<open>cproblem_wt p \<Longrightarrow> map length (enc_dl p) = cdef_widths (cvar_widths p) [] (CoreProblemL_defs p)\<close>
  using enc_defs_len[of p \<open>length (CoreProblemL_defs p)\<close>] by simp

lemma enc_vars_ok:
  assumes \<open>fuel_bound p \<le> N\<close> \<open>fuel_bound p < 2 ^ 57\<close> \<open>i < length (CoreProblemL_widths p)\<close>
  shows \<open>unat (CoreProblemL_widths p ! i) \<le> N \<and>
    room (fst (fresh_vec_m (fst (enc_vars p i)) (unat (CoreProblemL_widths p ! i))))\<close>
proof -
  have \<open>sz (fst (enc_vars p (Suc i))) \<le> sz (fst (encode_m p))\<close>
    using assms(3) by (intro enc_vars_le) simp
  then show ?thesis using fb_width[OF assms(3)] fb_facts(2)[of p] assms(1,2) by (simp add: room_def)
qed

lemma enc_defs_ok:
  assumes \<open>cproblem_wt p\<close> \<open>fuel_bound p \<le> N\<close> \<open>fuel_bound p < 2 ^ 57\<close> \<open>j < length (CoreProblemL_defs p)\<close>
  shows \<open>Suc (size (CoreProblemL_defs p ! j)) \<le> N \<and>
    bok N (enc_vs p) (snd (enc_defs p j)) (fst (enc_defs p j)) (CoreProblemL_defs p ! j)\<close>
proof -
  let ?W = \<open>cvar_widths p\<close> and ?ts = \<open>CoreProblemL_defs p\<close>
  let ?t = \<open>?ts ! j\<close> and ?Dj = \<open>cdef_widths (cvar_widths p) [] (take j (CoreProblemL_defs p))\<close>
  let ?DS = \<open>cdef_widths (cvar_widths p) [] (CoreProblemL_defs p)\<close>
  have tb: \<open>tbound ?W ?DS ?t \<le> fuel_bound p\<close>
    using assms(4) by (intro fb_tbound) simp
  have cwt: \<open>cwt ?W ?Dj ?t\<close>
    using defs_wt_nth[OF _ assms(4)] assms(1) by (simp add: cproblem_wt_def Let_def)
  have eq: \<open>?DS = cdef_widths ?W ?Dj (drop j ?ts)\<close>
    by (simp only: def_widths_append[symmetric] append_take_drop_id)
  obtain e where e: \<open>?DS = ?Dj @ e\<close>
    using def_widths_prefix[of ?W ?Dj \<open>drop j ?ts\<close>] unfolding eq by blast
  have sub: \<open>\<forall>u \<in> set (csubterms ?t). 2 * cwidth ?W ?Dj u + 2 \<le> fuel_bound p\<close>
  proof
    fix u assume u: \<open>u \<in> set (csubterms ?t)\<close>
    have \<open>cwidth ?W ?DS u = cwidth ?W ?Dj u\<close>
      unfolding e using wt_subterms[OF cwt u] by (rule wt_width_append)
    then show \<open>2 * cwidth ?W ?Dj u + 2 \<le> fuel_bound p\<close>
      using tbound_width[OF u, of ?W ?DS] tb by simp
  qed
  have \<open>sz (fst (enc_defs p (Suc j))) \<le> sz (fst (encode_m p))\<close>
    using assms(4) by (intro enc_defs_le) simp
  then have f: \<open>room (fst (blast_m (enc_vs p) (snd (enc_defs p j)) (fst (enc_defs p j)) ?t))\<close>
    using fb_facts(2)[of p] assms(3) by (simp add: room_def)
  have ld: \<open>map length (snd (enc_defs p j)) = ?Dj\<close>
    using enc_defs_len[OF assms(1)] assms(4) by simp
  have \<open>bok N (enc_vs p) (snd (enc_defs p j)) (fst (enc_defs p j)) ?t\<close>
    by (rule bok_intro[where M=\<open>fuel_bound p\<close>]) (use cwt sub f ld assms(2,3) in simp_all)
  moreover have \<open>Suc (size ?t) \<le> N\<close>
    using tbound_size[of ?t ?W ?DS] tb assms(2) by simp
  ultimately show ?thesis by simp
qed

lemma enc_asserts_ok:
  assumes \<open>cproblem_wt p\<close> \<open>fuel_bound p \<le> N\<close> \<open>fuel_bound p < 2 ^ 57\<close> \<open>k < length (CoreProblemL_asserts p)\<close>
  shows \<open>Suc (size (CoreProblemL_asserts p ! k)) \<le> N \<and>
    bok N (enc_vs p) (enc_dl p) (enc_asserts p k) (CoreProblemL_asserts p ! k) \<and>
    0 < length (snd (blast_m (enc_vs p) (enc_dl p) (enc_asserts p k) (CoreProblemL_asserts p ! k)))\<close>
proof -
  let ?W = \<open>cvar_widths p\<close> and ?t = \<open>CoreProblemL_asserts p ! k\<close>
  let ?DS = \<open>cdef_widths (cvar_widths p) [] (CoreProblemL_defs p)\<close>
  have tb: \<open>tbound ?W ?DS ?t \<le> fuel_bound p\<close>
    using assms(4) by (intro fb_tbound) simp
  have cwt: \<open>cwt ?W ?DS ?t\<close> \<open>cwidth ?W ?DS ?t = 1\<close>
    using assms(1,4) by (simp_all add: cproblem_wt_def Let_def)
  have sub: \<open>\<forall>u \<in> set (csubterms ?t). 2 * cwidth ?W ?DS u + 2 \<le> fuel_bound p\<close>
    using tbound_width[of _ ?t ?W ?DS] tb by (blast intro: le_trans)
  have \<open>sz (enc_asserts p (Suc k)) \<le> sz (fst (encode_m p))\<close>
    using assms(4) by (intro enc_asserts_le) simp
  then have f: \<open>room (fst (blast_m (enc_vs p) (enc_dl p) (enc_asserts p k) ?t))\<close>
    using fb_facts(2)[of p] assms(3) by (simp add: room_def)
  have ld: \<open>map length (enc_dl p) = ?DS\<close>
    using enc_dl_len[OF assms(1)] .
  have \<open>bok N (enc_vs p) (enc_dl p) (enc_asserts p k) ?t\<close>
    by (rule bok_intro[where M=\<open>fuel_bound p\<close>]) (use cwt sub f ld assms(2,3) in simp_all)
  moreover have \<open>Suc (size ?t) \<le> N\<close>
    using tbound_size[of ?t ?W ?DS] tb assms(2) by simp
  moreover have \<open>length (snd (blast_m (enc_vs p) (enc_dl p) (enc_asserts p k) ?t)) = 1\<close>
    using blast_m_length[of \<open>enc_vs p\<close> \<open>enc_dl p\<close> ?t \<open>enc_asserts p k\<close>] cwt ld by simp
  ultimately show ?thesis by simp
qed

lemma init_st_eq: \<open>init_st = (Suc 0, [[lconst True]])\<close>
  by (simp add: init_st_def addc_m_def)

context QFBV_ctx
begin

subsection \<open>\<^verbatim>\<open>blast_bin\<close>\<close>

definition blast_bin_contract ::
  \<open>Cnf \<Rightarrow> BinOp \<Rightarrow> Lit rvec \<Rightarrow> Lit rvec \<Rightarrow> ('s, Cnf \<times> Lit rvec \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>blast_bin_contract c op a b \<equiv>
     make_function_contract
       (can_alloc_reference \<star> \<langle>cnf_ok c \<and> vok b \<and> bin_ok urust_fuel (st_of c) op (rvec_elems a) (rvec_elems b)\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>cnfv_res r (blast_bin_m (st_of c) op (rvec_elems a) (rvec_elems b))\<rangle>)\<close>

lemma blast_bin_spec [crush_specs]:
  shows \<open>\<Gamma>; blast_bin c op a b \<Turnstile>\<^sub>F blast_bin_contract c op a b\<close>
  apply (crush_boot f: blast_bin_def contract: blast_bin_contract_def)
  apply (cases op; simp only: BinOp_case_simps)
             apply (crush_base simp add: bin_ok_def cnfv_res_def cnf_res_def push_not_None)+
  done

subsection \<open>\<^verbatim>\<open>blast\<close>\<close>

text \<open>The \<open>k\<close>-th unfolding of \<^const>\<open>blast\<close>: its precondition requires the recursion depth
  \<open>size t + 1\<close> to be at most \<open>k\<close>, so the innermost function is never called.\<close>
definition blast_contract ::
  \<open>nat \<Rightarrow> Cnf \<Rightarrow> Lit rvec rvec \<Rightarrow> Lit rvec rvec \<Rightarrow> CoreTerm \<Rightarrow> ('s, Cnf \<times> Lit rvec \<times> tnil, 'abort) function_contract\<close>
  where
  [crush_contracts]: \<open>blast_contract k c vv dd t \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
        \<langle>Suc (size t) \<le> k \<and> cnf_ok c \<and> allvok vv \<and> allvok dd \<and>
         bok urust_fuel (vecs_of vv) (vecs_of dd) (st_of c) (ct_of t)\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>cnfv_res r (blast_m (vecs_of vv) (vecs_of dd) (st_of c) (ct_of t))\<rangle>)\<close>

lemma blast_rec_step_spec:
  assumes \<open>\<And>c vv dd t. \<Gamma>; R c vv dd t \<Turnstile>\<^sub>F blast_contract k c vv dd t\<close>
  shows \<open>\<Gamma>; blast_rec_step R c vv dd t \<Turnstile>\<^sub>F blast_contract (Suc k) c vv dd t\<close>
  apply (crush_boot f: blast_rec_step_def contract: blast_contract_def)
  apply (cases t; simp only: CoreTerm.case)
        apply (crush_base specs add: assms simp add: cnfv_res_def allvok_nth)+
  done

lemma blast_rec_spec:
  shows \<open>\<Gamma>; (blast_rec_step ^^ k) g c vv dd t \<Turnstile>\<^sub>F blast_contract k c vv dd t\<close>
proof (induction k arbitrary: c vv dd t)
  case 0
  show ?case
    apply (ucincl_discharge\<open>intro satisfies_function_contractI\<close>)
    apply (subst wp_sstriple_iff)
    apply (simp add: blast_contract_def Let_def apure_precise_False asepconj_bot_zero2 bot_aentails_all)
    done
next
  case (Suc k)
  show ?case
    unfolding funpow.simps(2) comp_def by (rule blast_rec_step_spec) (rule Suc.IH)
qed

lemma blast_spec [crush_specs]:
  shows \<open>\<Gamma>; blast c vv dd t \<Turnstile>\<^sub>F blast_contract urust_fuel c vv dd t\<close>
  unfolding blast_def by (rule blast_rec_spec)

subsection \<open>\<^verbatim>\<open>encode\<close>\<close>

definition encode_contract :: \<open>CoreProblem \<Rightarrow> ('s, Cnf \<times> Lit rvec rvec \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>encode_contract p \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
        \<langle>cproblem_wt (cprob_of p) \<and> fuel_bound (cprob_of p) \<le> urust_fuel \<and> fuel_bound (cprob_of p) < 2 ^ 57\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>cnf_ok (fst r) \<and> st_of (fst r) = fst (encode_m (cprob_of p)) \<and>
           vecs_of (fst (snd r)) = snd (encode_m (cprob_of p)) \<and> snd (snd r) = TNil\<rangle>)\<close>

lemma encode_spec_aux:
  assumes A: \<open>cproblem_wt (cprob_of p)\<close> \<open>fuel_bound (cprob_of p) \<le> urust_fuel\<close> \<open>fuel_bound (cprob_of p) < 2 ^ 57\<close>
  shows \<open>\<Gamma>; encode p \<Turnstile>\<^sub>F encode_contract p\<close>
proof -
  let ?q = \<open>cprob_of p\<close>
  note fb = fb_facts[of ?q]
  have L: \<open>rvec_length (CoreProblem_widths p) < 72057594037927936\<close>
    \<open>rvec_length (CoreProblem_defs p) < 72057594037927936\<close>
    \<open>rvec_length (CoreProblem_asserts p) < 72057594037927936\<close> \<open>rvec_length (CoreProblem_widths p) \<le> urust_fuel\<close>
    \<open>rvec_length (CoreProblem_defs p) \<le> urust_fuel\<close> \<open>rvec_length (CoreProblem_asserts p) \<le> urust_fuel\<close>
    using fb A by (simp_all add: cvar_widths_def)
  have I: \<open>\<And>i. i < rvec_length (CoreProblem_widths p) \<Longrightarrow> i < 18446744073709551615\<close>
    \<open>\<And>i. i < rvec_length (CoreProblem_defs p) \<Longrightarrow> i < 18446744073709551615\<close>
    \<open>\<And>i. i < rvec_length (CoreProblem_asserts p) \<Longrightarrow> i < 18446744073709551615\<close>
    using L by linarith+
  have W: \<open>unat (word64_of_nat (rvec_length (CoreProblem_widths p))) = rvec_length (CoreProblem_widths p)\<close>
    \<open>unat (word64_of_nat (rvec_length (CoreProblem_defs p))) = rvec_length (CoreProblem_defs p)\<close>
    \<open>unat (word64_of_nat (rvec_length (CoreProblem_asserts p))) = rvec_length (CoreProblem_asserts p)\<close>
    using L by (simp_all add: unat_of_nat_eq)
  have I56: \<open>\<And>i. i < rvec_length (CoreProblem_widths p) \<Longrightarrow> i < 72057594037927936\<close>
    \<open>\<And>i. i < rvec_length (CoreProblem_defs p) \<Longrightarrow> i < 72057594037927936\<close>
    \<open>\<And>i. i < rvec_length (CoreProblem_asserts p) \<Longrightarrow> i < 72057594037927936\<close>
    using L by linarith+
  note V = enc_vars_ok[OF A(2,3), simplified]
  note D = enc_defs_ok[OF A]
  have D2: \<open>\<And>j. j < rvec_length (CoreProblem_defs p) \<Longrightarrow> Suc (size (rvec_elems (CoreProblem_defs p) ! j)) \<le> urust_fuel \<and>
      bok urust_fuel (snd (enc_vars ?q (rvec_length (CoreProblem_widths p)))) (snd (enc_defs ?q j)) (fst (enc_defs ?q j))
        (ct_of (rvec_elems (CoreProblem_defs p) ! j))\<close>
    using D by simp
  note As = enc_asserts_ok[OF A]
  note As2 = enc_asserts_ok[OF A, THEN conjunct2, THEN conjunct2, simplified]
  have As3: \<open>\<And>k. k < rvec_length (CoreProblem_asserts p) \<Longrightarrow> Suc (size (rvec_elems (CoreProblem_asserts p) ! k)) \<le> urust_fuel \<and>
      bok urust_fuel (snd (enc_vars ?q (rvec_length (CoreProblem_widths p)))) (snd (enc_defs ?q (rvec_length (CoreProblem_defs p))))
        (enc_asserts ?q k) (ct_of (rvec_elems (CoreProblem_asserts p) ! k)) \<and>
      [] \<noteq> snd (blast_m (snd (enc_vars ?q (rvec_length (CoreProblem_widths p)))) (snd (enc_defs ?q (rvec_length (CoreProblem_defs p))))
        (enc_asserts ?q k) (ct_of (rvec_elems (CoreProblem_asserts p) ! k)))\<close>
    using As by (simp, metis)
  have C: \<open>\<And>k a. k < rvec_length (CoreProblem_asserts p) \<Longrightarrow> st_of a = fst (blast_m (snd (enc_vars ?q (rvec_length (CoreProblem_widths p)))) (snd (enc_defs ?q (rvec_length (CoreProblem_defs p))))
        (enc_asserts ?q k) (ct_of (rvec_elems (CoreProblem_asserts p) ! k))) \<Longrightarrow>
      length (vecs_of (Cnf_clauses a)) < 72057594037927936\<close>
  proof -
    fix k a assume k: \<open>k < rvec_length (CoreProblem_asserts p)\<close> and a: \<open>st_of a = fst (blast_m (snd (enc_vars ?q (rvec_length (CoreProblem_widths p)))) (snd (enc_defs ?q (rvec_length (CoreProblem_defs p))))
        (enc_asserts ?q k) (ct_of (rvec_elems (CoreProblem_asserts p) ! k)))\<close>
    have e: \<open>vecs_of (Cnf_clauses a) = snd (fst (blast_m (snd (enc_vars ?q (rvec_length (CoreProblem_widths p))))
        (snd (enc_defs ?q (rvec_length (CoreProblem_defs p)))) (enc_asserts ?q k) (ct_of (rvec_elems (CoreProblem_asserts p) ! k))))\<close>
      using a by (metis snd_conv st_of_def)
    have \<open>sz (enc_asserts ?q (Suc k)) \<le> sz (fst (encode_m ?q))\<close> using k by (intro enc_asserts_le) simp
    then show \<open>length (vecs_of (Cnf_clauses a)) < 72057594037927936\<close>
      using k fb(2) A(3) by (simp add: sz_def e nth_map del: vecs_of_simps(1))
  qed
  show ?thesis
    apply (crush_boot f: encode_def contract: encode_contract_def)
    apply (crush_base simp add: L init_st_def addc_m_def vecs_of_def push_not_None)
    subgoal for cl0 c0 cnf_ref vars_ref i_ref
      apply (ucincl_discharge\<open>
        rule_tac
          INV=\<open>\<lambda>k. \<Squnion>gc c gv v gi i. cnf_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c \<star> vars_ref \<mapsto>\<langle>\<top>\<rangle> gv\<down>v \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
                 can_alloc_reference \<star>
                 \<langle>unat i \<le> rvec_length (CoreProblem_widths p) \<and> cnf_ok c \<and> st_of c = fst (enc_vars ?q (unat i)) \<and>
                  vecs_of v = snd (enc_vars ?q (unat i)) \<and> vok v \<and> allvok v \<and>
                  rvec_length (CoreProblem_widths p) - unat i \<le> k\<rangle>\<close> and
          INV'=\<open>\<lambda>k. \<Squnion>gc c gv v gi i. cnf_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c \<star> vars_ref \<mapsto>\<langle>\<top>\<rangle> gv\<down>v \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
                 can_alloc_reference \<star>
                 \<langle>unat i < rvec_length (CoreProblem_widths p) \<and> cnf_ok c \<and> st_of c = fst (enc_vars ?q (unat i)) \<and>
                  vecs_of v = snd (enc_vars ?q (unat i)) \<and> vok v \<and> allvok v \<and>
                  rvec_length (CoreProblem_widths p) - unat i \<le> Suc k\<rangle>\<close> and
          \<tau>=\<open>\<lambda>r. can_alloc_reference \<star>
            \<langle>cnf_ok (fst r) \<and> st_of (fst r) = fst (encode_m ?q) \<and> vecs_of (fst (snd r)) = snd (encode_m ?q) \<and>
             snd (snd r) = TNil\<rangle>\<close> and
          \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_bounded_while_framedI\<close>)
      apply (crush_base simp add: cnfv_res_def L I V init_st_eq push_not_None unat_word_Suc_simp antisym_conv
          word_less_nat_alt)
      prefer 8 apply (simp add: allvok_new)
      apply (frule vecs_of_len, simp add: I56)
      apply (frule vecs_of_len, simp add: I56)
      apply (frule vecs_of_len, simp add: I56)
      apply (frule vecs_of_len, simp add: I56)
      apply (subst (asm) unat_of_nat_eq, use L(1) in simp, simp)
      apply (subst (asm) unat_of_nat_eq, use L(1) in simp, simp)
      subgoal for gc c gv v gi i defs_ref j_ref
        apply (ucincl_discharge\<open>
          rule_tac
            INV=\<open>\<lambda>k. \<Squnion>gc c gv v gi i gd d gj j. cnf_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c \<star> vars_ref \<mapsto>\<langle>\<top>\<rangle> gv\<down>v \<star>
                   i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> defs_ref \<mapsto>\<langle>\<top>\<rangle> gd\<down>d \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star>
                   can_alloc_reference \<star>
                   \<langle>unat j \<le> rvec_length (CoreProblem_defs p) \<and> cnf_ok c \<and> st_of c = fst (enc_defs ?q (unat j)) \<and>
                    vecs_of v = enc_vs ?q \<and> allvok v \<and> vecs_of d = snd (enc_defs ?q (unat j)) \<and> vok d \<and> allvok d \<and>
                    rvec_length (CoreProblem_defs p) - unat j \<le> k\<rangle>\<close> and
            INV'=\<open>\<lambda>k. \<Squnion>gc c gv v gi i gd d gj j. cnf_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c \<star> vars_ref \<mapsto>\<langle>\<top>\<rangle> gv\<down>v \<star>
                   i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> defs_ref \<mapsto>\<langle>\<top>\<rangle> gd\<down>d \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star>
                   can_alloc_reference \<star>
                   \<langle>unat j < rvec_length (CoreProblem_defs p) \<and> cnf_ok c \<and> st_of c = fst (enc_defs ?q (unat j)) \<and>
                    vecs_of v = enc_vs ?q \<and> allvok v \<and> vecs_of d = snd (enc_defs ?q (unat j)) \<and> vok d \<and> allvok d \<and>
                    rvec_length (CoreProblem_defs p) - unat j \<le> Suc k\<rangle>\<close> and
            \<tau>=\<open>\<lambda>r. can_alloc_reference \<star>
              \<langle>cnf_ok (fst r) \<and> st_of (fst r) = fst (encode_m ?q) \<and> vecs_of (fst (snd r)) = snd (encode_m ?q) \<and>
               snd (snd r) = TNil\<rangle>\<close> and
            \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
          in wp_bounded_while_framedI\<close>)
        apply (crush_base simp add: cnfv_res_def L I)
        defer 12
        apply (auto simp add: rvec_length_vecs I I56 D2 W unat_word_Suc_simp allvok_new simp del: vecs_of_simps(1))[12]
        subgoal for gca ca gva va gia ia gd d gj j k_ref
          apply (ucincl_discharge\<open>
            rule_tac
              INV=\<open>\<lambda>k. \<Squnion>gc c gv v gi i gd d gj j gk kk. cnf_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c \<star>
                     vars_ref \<mapsto>\<langle>\<top>\<rangle> gv\<down>v \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> defs_ref \<mapsto>\<langle>\<top>\<rangle> gd\<down>d \<star>
                     j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> k_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>kk \<star> can_alloc_reference \<star>
                     \<langle>unat kk \<le> rvec_length (CoreProblem_asserts p) \<and> cnf_ok c \<and> st_of c = enc_asserts ?q (unat kk) \<and>
                      vecs_of v = enc_vs ?q \<and> allvok v \<and> vecs_of d = enc_dl ?q \<and> allvok d \<and>
                      rvec_length (CoreProblem_asserts p) - unat kk \<le> k\<rangle>\<close> and
              INV'=\<open>\<lambda>k. \<Squnion>gc c gv v gi i gd d gj j gk kk. cnf_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c \<star>
                     vars_ref \<mapsto>\<langle>\<top>\<rangle> gv\<down>v \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> defs_ref \<mapsto>\<langle>\<top>\<rangle> gd\<down>d \<star>
                     j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> k_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>kk \<star> can_alloc_reference \<star>
                     \<langle>unat kk < rvec_length (CoreProblem_asserts p) \<and> cnf_ok c \<and> st_of c = enc_asserts ?q (unat kk) \<and>
                      vecs_of v = enc_vs ?q \<and> allvok v \<and> vecs_of d = enc_dl ?q \<and> allvok d \<and>
                      rvec_length (CoreProblem_asserts p) - unat kk \<le> Suc k\<rangle>\<close> and
              \<tau>=\<open>\<lambda>r. can_alloc_reference \<star>
                \<langle>cnf_ok (fst r) \<and> st_of (fst r) = fst (encode_m ?q) \<and> vecs_of (fst (snd r)) = snd (encode_m ?q) \<and>
                 snd (snd r) = TNil\<rangle>\<close> and
              \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
            in wp_bounded_while_framedI\<close>)
          apply (crush_base simp add: I)
          apply (auto simp add: rvec_length_vecs L I I56 As3 C W unat_word_Suc_simp word_less_nat_alt encode_m_eq cnfv_res_def simp del: vecs_of_simps(1))
          done
        done
      done
    done
qed

lemma encode_spec [crush_specs]:
  shows \<open>\<Gamma>; encode p \<Turnstile>\<^sub>F encode_contract p\<close>
proof (cases \<open>cproblem_wt (cprob_of p) \<and> fuel_bound (cprob_of p) \<le> urust_fuel \<and> fuel_bound (cprob_of p) < 2 ^ 57\<close>)
  case True
  then show ?thesis using encode_spec_aux by blast
next
  case False
  then have F: \<open>(cproblem_wt (cprob_of p) \<and> fuel_bound (cprob_of p) \<le> urust_fuel \<and> fuel_bound (cprob_of p) < 2 ^ 57) = False\<close>
    by simp
  show ?thesis
    apply (ucincl_discharge\<open>intro satisfies_function_contractI\<close>)
    apply (subst wp_sstriple_iff)
    apply (simp only: encode_contract_def F)
    apply (simp add: Let_def apure_precise_False asepconj_bot_zero2 bot_aentails_all)
    done
qed

end

end
