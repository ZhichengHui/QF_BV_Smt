theory QFBV_LowerRefine
  imports QFBV_Lower
begin

lemma unat_of_nat_64': \<open>n < 18446744073709551616 \<Longrightarrow> unat (word_of_nat n :: 64 word) = n\<close>
  by (simp add: unat_of_nat_eq)

lemma unat_word_Suc_simp':
  fixes x :: \<open>64 word\<close>
  assumes \<open>unat x < 18446744073709551615\<close>
  shows \<open>unat (x + 1) = Suc (unat x)\<close>
proof -
  have \<open>unat x + unat (1 :: 64 word) < 2 ^ LENGTH(64)\<close> using assms by simp
  then have \<open>unat (x + 1) = unat x + unat (1 :: 64 word)\<close> using unat_add_lem by blast
  then show ?thesis by simp
qed

lemma wnunat [simp]: \<open>word_of_nat (unat w) = w\<close> for w :: \<open>64 word\<close>
  by simp

section \<open>The Rust functions of the rewriting compute their models\<close>

text \<open>The equations of \<^const>\<open>lower_m\<close> in terms of \<open>fst\<close> and \<open>snd\<close> of the recursive results, as
  \<^verbatim>\<open>crush\<close> sees them.\<close>
lemma lower_m_simps':
  \<open>lower_m ws dm L (TermL_Not a) =
     push_m (fst (lower_m ws dm L a)) (CoreTermL_Not (cr (snd (lower_m ws dm L a)))) (snd (fst (lower_m ws dm L a)) ! snd (lower_m ws dm L a))\<close>
  \<open>lower_m ws dm L (TermL_Neg a) =
     push_m (fst (lower_m ws dm L a)) (neg_t (snd (lower_m ws dm L a)) (snd (fst (lower_m ws dm L a)) ! snd (lower_m ws dm L a)))
       (snd (fst (lower_m ws dm L a)) ! snd (lower_m ws dm L a))\<close>
  \<open>lower_m ws dm L (TermL_Bin op a b) =
     lower_bin_m (fst (lower_m ws dm (fst (lower_m ws dm L a)) b)) op (snd (lower_m ws dm L a))
       (snd (lower_m ws dm (fst (lower_m ws dm L a)) b))\<close>
  \<open>lower_m ws dm L (TermL_Extract hi lo a) =
     push_m (fst (lower_m ws dm L a)) (CoreTermL_Extract hi lo (cr (snd (lower_m ws dm L a)))) (unat hi - unat lo + 1)\<close>
  \<open>lower_m ws dm L (TermL_ZeroExtend i a) =
     push_m (fst (lower_m ws dm L a))
       (CoreTermL_Bin BinOp_Concat (CoreTermL_Const (replicate (unat i) False)) (cr (snd (lower_m ws dm L a))))
       (snd (fst (lower_m ws dm L a)) ! snd (lower_m ws dm L a) + unat i)\<close>
  \<open>lower_m ws dm L (TermL_SignExtend i a) =
     push_m (fst (lower_m ws dm L a))
       (CoreTermL_Bin BinOp_Concat
          (CoreTermL_Ite (msb_t (snd (lower_m ws dm L a)) (snd (fst (lower_m ws dm L a)) ! snd (lower_m ws dm L a)))
             (CoreTermL_Const (replicate (unat i) True)) (CoreTermL_Const (replicate (unat i) False)))
          (cr (snd (lower_m ws dm L a))))
       (snd (fst (lower_m ws dm L a)) ! snd (lower_m ws dm L a) + unat i)\<close>
  \<open>lower_m ws dm L (TermL_Ite c a b) =
     push_m (fst (lower_m ws dm (fst (lower_m ws dm (fst (lower_m ws dm L c)) a)) b))
       (CoreTermL_Ite (cr (snd (lower_m ws dm L c))) (cr (snd (lower_m ws dm (fst (lower_m ws dm L c)) a)))
          (cr (snd (lower_m ws dm (fst (lower_m ws dm (fst (lower_m ws dm L c)) a)) b))))
       (snd (fst (lower_m ws dm (fst (lower_m ws dm (fst (lower_m ws dm L c)) a)) b)) !
          snd (lower_m ws dm (fst (lower_m ws dm L c)) a))\<close>
  by (simp_all add: split_def Let_def)

lemma lower_m_Repeat':
  \<open>lower_m ws dm L (TermL_Repeat i a) =
     (let L1 = fst (lower_m ws dm L a); ka = snd (lower_m ws dm L a); w = snd L1 ! ka;
          L2 = fst (push_m L1 (CoreTermL_Const []) 0); k0 = snd (push_m L1 (CoreTermL_Const []) 0);
          r = foldl (repeat_step ka w) (L2, k0, 0) [0..<unat i] in
      (fst r, fst (snd r)))\<close>
  by (simp add: split_def Let_def)

lemma lower_m_RotateLeft':
  \<open>lower_m ws dm L (TermL_RotateLeft i a) =
     (let L1 = fst (lower_m ws dm L a); ka = snd (lower_m ws dm L a); w = snd L1 ! ka; r = unat i mod w in
      if r = 0 then (L1, ka)
      else push_m L1 (CoreTermL_Bin BinOp_Concat (CoreTermL_Extract (word_of_nat (w - 1 - r)) 0 (cr ka))
                        (CoreTermL_Extract (word_of_nat (w - 1)) (word_of_nat (w - r)) (cr ka))) w)\<close>
  by (simp add: split_def Let_def)

lemma lower_m_RotateRight':
  \<open>lower_m ws dm L (TermL_RotateRight i a) =
     (let L1 = fst (lower_m ws dm L a); ka = snd (lower_m ws dm L a); w = snd L1 ! ka; r = unat i mod w in
      if r = 0 then (L1, ka)
      else push_m L1 (CoreTermL_Bin BinOp_Concat (CoreTermL_Extract (word_of_nat (r - 1)) 0 (cr ka))
                        (CoreTermL_Extract (word_of_nat (w - 1)) (word_of_nat r) (cr ka))) w)\<close>
  by (simp add: split_def Let_def)

declare lower_m.simps(4-13) [simp del]
declare lower_m_simps' [simp]

text \<open>A Rust \<^verbatim>\<open>Lower\<close> whose vectors can grow, of equal lengths.\<close>
definition lower_ok :: \<open>Lower \<Rightarrow> bool\<close> where
  \<open>lower_ok l \<equiv> vok (Lower_defs l) \<and> vok (Lower_widths l) \<and> rvec_length (Lower_defs l) = rvec_length (Lower_widths l)\<close>

lemma lst_of_simps [simp]:
  \<open>fst (lst_of l) = map ct_of (rvec_elems (Lower_defs l))\<close>
  \<open>snd (lst_of l) = map unat (rvec_elems (Lower_widths l))\<close>
  \<open>lst_of (make_Lower d w) = (map ct_of (rvec_elems d), map unat (rvec_elems w))\<close>
  \<open>lower_ok (make_Lower d w) = (vok d \<and> vok w \<and> rvec_length d = rvec_length w)\<close>
  by (simp_all add: lst_of_def lower_ok_def)

text \<open>An equation on the state of a \<^verbatim>\<open>Lower\<close> is one on its two fields.\<close>
lemma lst_of_eq [simp]:
  \<open>(lst_of l = L) = (map ct_of (rvec_elems (Lower_defs l)) = fst L \<and> map unat (rvec_elems (Lower_widths l)) = snd L)\<close>
  by (cases L) (auto simp add: lst_of_def)

text \<open>The same equation, oriented to express the state by the fields of the \<^verbatim>\<open>Lower\<close>.\<close>
lemma lst_of_eq':
  \<open>(lst_of l = L) = (fst L = map ct_of (rvec_elems (Lower_defs l)) \<and> snd L = map unat (rvec_elems (Lower_widths l)))\<close>
  by (auto simp add: lst_of_eq)

subsection \<open>The precondition of \<^verbatim>\<open>lower\<close>\<close>

text \<open>What each call of the recursion needs: indices in bounds, the arithmetic on widths without
  overflow, and the loop for \<open>repeat\<close> within the fuel \<open>N\<close>. The facts are stated on the results of
  the model, as \<open>bok\<close> of \<^verbatim>\<open>QFBV_Refine\<close> does for \<^verbatim>\<open>blast\<close>.\<close>
definition kok :: \<open>lst \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>kok L k \<equiv> k < length (snd L) \<and> k < 2 ^ 64 \<and> snd L ! k < 2 ^ 56 \<and> 1 \<le> snd L ! k\<close>

primrec lpre :: \<open>nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> lst \<Rightarrow> TermL \<Rightarrow> bool\<close> where
  \<open>lpre N ws dm L (TermL_Const bs) = (length bs < 2 ^ 56)\<close>
| \<open>lpre N ws dm L (TermL_Var i) = (unat i < length ws)\<close>
| \<open>lpre N ws dm L (TermL_Ref j) = (unat j < length dm)\<close>
| \<open>lpre N ws dm L (TermL_Not a) = (lpre N ws dm L a \<and> kok (fst (lower_m ws dm L a)) (snd (lower_m ws dm L a)))\<close>
| \<open>lpre N ws dm L (TermL_Neg a) = (lpre N ws dm L a \<and> kok (fst (lower_m ws dm L a)) (snd (lower_m ws dm L a)))\<close>
| \<open>lpre N ws dm L (TermL_Bin op a b) =
     (lpre N ws dm L a \<and> lpre N ws dm (fst (lower_m ws dm L a)) b \<and>
      kok (fst (lower_m ws dm (fst (lower_m ws dm L a)) b)) (snd (lower_m ws dm L a)) \<and>
      kok (fst (lower_m ws dm (fst (lower_m ws dm L a)) b)) (snd (lower_m ws dm (fst (lower_m ws dm L a)) b)) \<and>
      length (fst (fst (lower_bin_m (fst (lower_m ws dm (fst (lower_m ws dm L a)) b)) op (snd (lower_m ws dm L a))
        (snd (lower_m ws dm (fst (lower_m ws dm L a)) b))))) < 2 ^ 56 \<and>
      (op = Op_Concat \<longrightarrow>
         snd (fst (lower_m ws dm (fst (lower_m ws dm L a)) b)) ! snd (lower_m ws dm L a) +
         snd (fst (lower_m ws dm (fst (lower_m ws dm L a)) b)) ! snd (lower_m ws dm (fst (lower_m ws dm L a)) b) < 2 ^ 64))\<close>
| \<open>lpre N ws dm L (TermL_Extract hi lo a) =
     (lpre N ws dm L a \<and> kok (fst (lower_m ws dm L a)) (snd (lower_m ws dm L a)) \<and>
      unat lo \<le> unat hi \<and> unat hi - unat lo + 1 < 2 ^ 64)\<close>
| \<open>lpre N ws dm L (TermL_Repeat i a) =
     (lpre N ws dm L a \<and> kok (fst (lower_m ws dm L a)) (snd (lower_m ws dm L a)) \<and>
      unat i \<le> N \<and> snd (fst (lower_m ws dm L a)) ! snd (lower_m ws dm L a) * unat i < 2 ^ 64 \<and>
      length (fst (fst (lower_m ws dm L a))) + 1 + unat i < 2 ^ 56)\<close>
| \<open>lpre N ws dm L (TermL_ZeroExtend i a) =
     (lpre N ws dm L a \<and> kok (fst (lower_m ws dm L a)) (snd (lower_m ws dm L a)) \<and>
      snd (fst (lower_m ws dm L a)) ! snd (lower_m ws dm L a) + unat i < 2 ^ 56)\<close>
| \<open>lpre N ws dm L (TermL_SignExtend i a) =
     (lpre N ws dm L a \<and> kok (fst (lower_m ws dm L a)) (snd (lower_m ws dm L a)) \<and>
      snd (fst (lower_m ws dm L a)) ! snd (lower_m ws dm L a) + unat i < 2 ^ 56)\<close>
| \<open>lpre N ws dm L (TermL_RotateLeft i a) = (lpre N ws dm L a \<and> kok (fst (lower_m ws dm L a)) (snd (lower_m ws dm L a)))\<close>
| \<open>lpre N ws dm L (TermL_RotateRight i a) = (lpre N ws dm L a \<and> kok (fst (lower_m ws dm L a)) (snd (lower_m ws dm L a)))\<close>
| \<open>lpre N ws dm L (TermL_Ite c a b) =
     (lpre N ws dm L c \<and> lpre N ws dm (fst (lower_m ws dm L c)) a \<and>
      lpre N ws dm (fst (lower_m ws dm (fst (lower_m ws dm L c)) a)) b \<and>
      kok (fst (lower_m ws dm (fst (lower_m ws dm (fst (lower_m ws dm L c)) a)) b)) (snd (lower_m ws dm L c)) \<and>
      kok (fst (lower_m ws dm (fst (lower_m ws dm (fst (lower_m ws dm L c)) a)) b)) (snd (lower_m ws dm (fst (lower_m ws dm L c)) a)) \<and>
      kok (fst (lower_m ws dm (fst (lower_m ws dm (fst (lower_m ws dm L c)) a)) b))
        (snd (lower_m ws dm (fst (lower_m ws dm (fst (lower_m ws dm L c)) a)) b)))\<close>

text \<open>The precondition holds for a well-sorted term whose rewriting stays within the bounds.\<close>
lemma kok_of_env: \<open>env_ok ws L k w \<Longrightarrow> kok L k\<close>
  using lok_length[of ws L] by (simp add: env_ok_def kok_def)

text \<open>The loop for \<open>repeat\<close> in closed form: after \<open>j\<close> iterations from the state \<open>(L, k, acc)\<close>, the
  definitions are \<open>j\<close> more, the current definition is the last one, and the width has grown by \<open>j\<close>
  times \<open>w\<close>.\<close>
lemma repeat_step_comp:
  \<open>fst (fst (repeat_step ka w s j)) = fst (fst s) @ [CoreTermL_Bin BinOp_Concat (cr ka) (cr (fst (snd s)))]\<close>
  \<open>snd (fst (repeat_step ka w s j)) = snd (fst s) @ [snd (snd s) + w]\<close>
  \<open>fst (snd (repeat_step ka w s j)) = length (fst (fst s))\<close>
  \<open>snd (snd (repeat_step ka w s j)) = snd (snd s) + w\<close>
  by (simp_all add: repeat_step_def push_m_def split_def)

lemma repeat_step_lst:
  \<open>fst (repeat_step ka w s j) =
     (fst (fst s) @ [CoreTermL_Bin BinOp_Concat (cr ka) (cr (fst (snd s)))], snd (fst s) @ [snd (snd s) + w])\<close>
  by (simp add: repeat_step_def push_m_def split_def)

lemma repeat_F_len:
  \<open>length (fst (fst (foldl (repeat_step ka w) (L, k, acc) [0..<j]))) = length (fst L) + j\<close>
  by (induction j) (simp_all add: repeat_step_comp)

lemma repeat_F_acc:
  \<open>snd (snd (foldl (repeat_step ka w) (L, k, acc) [0..<j])) = acc + w * j\<close>
  by (induction j) (simp_all add: repeat_step_comp)

lemma repeat_F_k:
  \<open>fst (snd (foldl (repeat_step ka w) (L, k, acc) [0..<Suc j])) = length (fst L) + j\<close>
  by (simp add: repeat_step_comp repeat_F_len)

lemma repeat_F_Suc:
  \<open>foldl (repeat_step ka w) s [0..<Suc j] = repeat_step ka w (foldl (repeat_step ka w) s [0..<j]) j\<close>
  by simp

lemma repeat_F_k_lt:
  assumes \<open>k0 < length (fst L0)\<close>
  shows \<open>fst (snd (foldl (repeat_step ka w) (L0, k0, acc) [0..<j])) <
         length (fst (fst (foldl (repeat_step ka w) (L0, k0, acc) [0..<j])))\<close>
proof (cases j)
  case 0
  then show ?thesis using assms by simp
next
  case (Suc j')
  show ?thesis unfolding Suc repeat_F_k repeat_F_len by simp
qed

text \<open>The loop of \<^verbatim>\<open>repeat\<close> in closed form: the fold over @{term \<open>[0..<j]\<close>} of the concatenation step.\<close>
definition rep_fold :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> lst \<Rightarrow> TermL \<Rightarrow> nat \<Rightarrow> lst \<times> nat \<times> nat\<close> where
  \<open>rep_fold ws dm L a j \<equiv>
     foldl (repeat_step (snd (lower_m ws dm L a)) (snd (fst (lower_m ws dm L a)) ! snd (lower_m ws dm L a)))
       (fst (push_m (fst (lower_m ws dm L a)) (CoreTermL_Const []) 0),
        snd (push_m (fst (lower_m ws dm L a)) (CoreTermL_Const []) 0), 0) [0..<j]\<close>

lemma lower_m_Repeat'':
  \<open>lower_m ws dm L (TermL_Repeat i a) = (fst (rep_fold ws dm L a (unat i)), fst (snd (rep_fold ws dm L a (unat i))))\<close>
  by (simp add: lower_m_Repeat' rep_fold_def Let_def)

lemma rep_fold_0: \<open>rep_fold ws dm L a 0 = (fst (push_m (fst (lower_m ws dm L a)) (CoreTermL_Const []) 0), snd (push_m (fst (lower_m ws dm L a)) (CoreTermL_Const []) 0), 0)\<close>
  by (simp add: rep_fold_def)

lemma rep_fold_len: \<open>length (fst (fst (rep_fold ws dm L a j))) = length (fst (fst (lower_m ws dm L a))) + 1 + j\<close>
  by (simp add: rep_fold_def repeat_F_len push_m_def)

lemma rep_fold_acc: \<open>snd (snd (rep_fold ws dm L a j)) = (snd (fst (lower_m ws dm L a)) ! snd (lower_m ws dm L a)) * j\<close>
  by (simp add: rep_fold_def repeat_F_acc)

lemma rep_fold_k_lt: \<open>fst (snd (rep_fold ws dm L a j)) < length (fst (fst (rep_fold ws dm L a j)))\<close>
  unfolding rep_fold_def by (rule repeat_F_k_lt) (simp add: push_m_def)

lemma rep_fold_Suc:
  \<open>rep_fold ws dm L a (Suc j) =
     repeat_step (snd (lower_m ws dm L a)) (snd (fst (lower_m ws dm L a)) ! snd (lower_m ws dm L a)) (rep_fold ws dm L a j) j\<close>
  by (simp add: rep_fold_def)

lemma rep_unat_acc:
  fixes jj :: \<open>64 word\<close> and W :: nat
  assumes \<open>unat jj \<le> unat i\<close> \<open>W * unat i < 18446744073709551616\<close> \<open>W < 18446744073709551616\<close>
  shows \<open>unat (word_of_nat W * jj :: 64 word) = W * unat jj\<close>
proof -
  have b: \<open>W * unat jj < 18446744073709551616\<close>
    by (rule le_less_trans[OF mult_le_mono2[OF assms(1), of W] assms(2)])
  have \<open>unat (word_of_nat W :: 64 word) * unat jj < 2 ^ LENGTH(64)\<close>
    using b assms(3) by (simp add: unat_of_nat_64')
  then have \<open>unat (word_of_nat W * jj :: 64 word) = unat (word_of_nat W :: 64 word) * unat jj\<close>
    using unat_mult_lem by blast
  then show ?thesis using assms(3) by (simp add: unat_of_nat_64')
qed

lemma rep_acc_ov:
  fixes jj :: \<open>64 word\<close>
  assumes \<open>unat jj < unat i\<close> \<open>W * unat i < 18446744073709551616\<close> \<open>W < 18446744073709551616\<close>
  shows \<open>unat (word_of_nat W * jj :: 64 word) + W < 18446744073709551616\<close>
proof -
  have \<open>W * unat jj + W = W * Suc (unat jj)\<close> by simp
  also have \<open>\<dots> \<le> W * unat i\<close> using assms(1) by (intro mult_le_mono2) simp
  also have \<open>\<dots> < 18446744073709551616\<close> using assms(2) by simp
  finally show ?thesis using rep_unat_acc[OF less_imp_le[OF assms(1)] assms(2,3)] by simp
qed

lemma rep_unat_acc_W:
  fixes jj :: \<open>64 word\<close>
  assumes \<open>unat jj < unat i\<close> \<open>W * unat i < 18446744073709551616\<close> \<open>W < 18446744073709551616\<close>
  shows \<open>unat (word_of_nat W * jj + word_of_nat W :: 64 word) = W * unat jj + W\<close>
proof -
  have e: \<open>word_of_nat W * jj + word_of_nat W = (word_of_nat (W * unat jj + W) :: 64 word)\<close>
    by (simp add: of_nat_add of_nat_mult wnunat)
  have b: \<open>W * unat jj + W < 18446744073709551616\<close>
    using rep_acc_ov[OF assms] rep_unat_acc[OF less_imp_le[OF assms(1)] assms(2,3)] by simp
  show ?thesis unfolding e by (rule unat_of_nat_64'[OF b])
qed

lemma rep_fold_k_bound:
  assumes \<open>length (fst (fst (lower_m ws dm L a))) + 1 + j < 18446744073709551616\<close>
  shows \<open>fst (snd (rep_fold ws dm L a j)) < 18446744073709551616\<close>
proof -
  have \<open>fst (snd (rep_fold ws dm L a j)) < length (fst (fst (rep_fold ws dm L a j)))\<close> by (rule rep_fold_k_lt)
  also have \<open>\<dots> = length (fst (fst (lower_m ws dm L a))) + 1 + j\<close> by (rule rep_fold_len)
  also have \<open>\<dots> < 18446744073709551616\<close> using assms by simp
  finally show ?thesis .
qed

lemma rep_cr_idx:
  assumes \<open>length (fst (fst (lower_m ws dm L a))) + 1 + j < 18446744073709551616\<close>
  shows \<open>cr (unat (word_of_nat (fst (snd (rep_fold ws dm L a j))) :: 64 word)) = cr (fst (snd (rep_fold ws dm L a j)))\<close>
  using rep_fold_k_bound[OF assms] by (simp add: unat_of_nat_64')

lemma unat_Suc_of_lt:
  fixes r i :: \<open>64 word\<close>
  assumes \<open>unat r < unat i\<close>
  shows \<open>unat (r + 1) = Suc (unat r)\<close>
proof -
  have \<open>unat i < 18446744073709551616\<close> using unat_lt2p[of i] by simp
  then have \<open>unat r < 18446744073709551615\<close> using assms by linarith
  then show ?thesis by (rule unat_word_Suc_simp')
qed

lemma rep_fold_unat_Suc:
  fixes r i :: \<open>64 word\<close>
  assumes \<open>unat r < unat i\<close>
  shows \<open>rep_fold ws dm L a (unat (r + 1)) =
         repeat_step (snd (lower_m ws dm L a)) (snd (fst (lower_m ws dm L a)) ! snd (lower_m ws dm L a))
           (rep_fold ws dm L a (unat r)) (unat r)\<close>
proof -
  have \<open>unat (r + 1) = Suc (unat r)\<close> by (rule unat_Suc_of_lt[OF assms])
  then show ?thesis by (simp add: rep_fold_Suc)
qed

lemma rep_k_step:
  fixes r i :: \<open>64 word\<close>
  assumes \<open>unat r < unat i\<close>
  shows \<open>(1 + (word_of_nat (length (fst (fst (lower_m ws dm L a)))) + r) :: 64 word) =
         word_of_nat (fst (snd (rep_fold ws dm L a (unat (r + 1)))))\<close>
proof -
  have u: \<open>unat (r + 1) = Suc (unat r)\<close> by (rule unat_Suc_of_lt[OF assms])
  have \<open>fst (snd (rep_fold ws dm L a (Suc (unat r)))) = length (fst (fst (lower_m ws dm L a))) + 1 + unat r\<close>
    by (simp only: rep_fold_Suc repeat_step_comp(3) rep_fold_len)
  then show ?thesis unfolding u
    by (simp add: of_nat_add ac_simps)
qed

lemma lower_bin_m_len: \<open>length (fst L) + 1 \<le> length (fst (fst (lower_bin_m L op ka kb)))\<close>
  by (cases op) (simp_all add: lower_bin_m_def Let_def push_m_def split_def)

text \<open>The precondition holds for a well-sorted term whose rewriting stays within the bounds.\<close>
lemma lpre_intro:
  assumes \<open>wt ws ds t\<close> \<open>lok ws L\<close> \<open>dm_ok ds dm L\<close> \<open>bnd (fst (lower_m ws dm L t))\<close>
    \<open>\<forall>u \<in> set (subterms t). width ws ds u \<le> N\<close>
  shows \<open>lpre N ws dm L t\<close>
  using assms
proof (induction t arbitrary: L)
  case (TermL_Const bs)
  obtain L' k where r: \<open>lower_m ws dm L (TermL_Const bs) = (L', k)\<close> by (cases \<open>lower_m ws dm L (TermL_Const bs)\<close>)
  note S = lower_m_correct[OF TermL_Const.prems(1-3) r TermL_Const.prems(4)[unfolded r, simplified]]
  then show ?case by (simp add: env_ok_def)
next
  case (TermL_Var i)
  then show ?case by simp
next
  case (TermL_Ref j)
  then show ?case by (simp add: dm_ok_def)
next
  case (TermL_Not a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  obtain L' k where r: \<open>lower_m ws dm L (TermL_Not a) = (L', k)\<close> by (cases \<open>lower_m ws dm L (TermL_Not a)\<close>)
  have B': \<open>bnd L'\<close> using TermL_Not.prems(4) r by simp
  have p: \<open>push_m L1 (CoreTermL_Not (cr ka)) (snd L1 ! ka) = (L', k)\<close> using r a by simp
  have B1: \<open>bnd L1\<close> using bnd_pfx[OF pfx_push[OF p] B'] .
  have wta: \<open>wt ws ds a\<close> using TermL_Not.prems(1) by simp
  note S = lower_m_correct[OF wta TermL_Not.prems(2,3) a B1]
  have lp: \<open>lpre N ws dm L a\<close> using TermL_Not.IH[OF wta TermL_Not.prems(2,3)] TermL_Not.prems(5) a B1 by simp
  have kk: \<open>kok L1 ka\<close> using S kok_of_env by blast
  show ?case using lp kk a by simp
next
  case (TermL_Neg a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  obtain L' k where r: \<open>lower_m ws dm L (TermL_Neg a) = (L', k)\<close> by (cases \<open>lower_m ws dm L (TermL_Neg a)\<close>)
  have B': \<open>bnd L'\<close> using TermL_Neg.prems(4) r by simp
  have p: \<open>push_m L1 (neg_t ka (snd L1 ! ka)) (snd L1 ! ka) = (L', k)\<close> using r a by simp
  have B1: \<open>bnd L1\<close> using bnd_pfx[OF pfx_push[OF p] B'] .
  have wta: \<open>wt ws ds a\<close> using TermL_Neg.prems(1) by simp
  note S = lower_m_correct[OF wta TermL_Neg.prems(2,3) a B1]
  have lp: \<open>lpre N ws dm L a\<close> using TermL_Neg.IH[OF wta TermL_Neg.prems(2,3)] TermL_Neg.prems(5) a B1 by simp
  have kk: \<open>kok L1 ka\<close> using S kok_of_env by blast
  show ?case using lp kk a by simp
next
  case (TermL_Bin op a b)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  obtain L2 kb where b: \<open>lower_m ws dm L1 b = (L2, kb)\<close> by (cases \<open>lower_m ws dm L1 b\<close>)
  obtain L' k where r: \<open>lower_bin_m L2 op ka kb = (L', k)\<close> by (cases \<open>lower_bin_m L2 op ka kb\<close>)
  have R: \<open>lower_m ws dm L (TermL_Bin op a b) = (L', k)\<close> using a b r by simp
  have B': \<open>bnd L'\<close> using TermL_Bin.prems(4) R by simp
  have B2: \<open>bnd L2\<close> using bnd_pfx[OF lower_bin_m_pfx[OF r] B'] .
  have B1: \<open>bnd L1\<close> using bnd_pfx[OF lower_m_pfx[OF b] B2] .
  have wt: \<open>wt ws ds a\<close> \<open>wt ws ds b\<close> \<open>op \<noteq> Op_Concat \<longrightarrow> width ws ds b = width ws ds a\<close>
    using TermL_Bin.prems(1) by simp_all
  note Sa = lower_m_correct[OF wt(1) TermL_Bin.prems(2,3) a B1]
  have L1: \<open>lok ws L1\<close> and X1: \<open>lext ws L L1\<close> using Sa lext_lok by blast+
  note D1 = dm_ok_lext[OF TermL_Bin.prems(2,3) X1]
  note Sb = lower_m_correct[OF wt(2) L1 D1 b B2]
  have X2: \<open>lext ws L1 L2\<close> using Sb by blast
  have EA: \<open>env_ok ws L2 ka (width ws ds a)\<close> using Sa env_lext[OF _ X2] by blast
  have EB: \<open>env_ok ws L2 kb (width ws ds b)\<close> using Sb by blast
  have Ia: \<open>lpre N ws dm L a\<close> using TermL_Bin.IH(1)[OF wt(1) TermL_Bin.prems(2,3)] TermL_Bin.prems(5) a B1 by simp
  have Ib: \<open>lpre N ws dm L1 b\<close> using TermL_Bin.IH(2)[OF wt(2) L1 D1] TermL_Bin.prems(5) b B2 by simp
  have len: \<open>length (fst (fst (lower_bin_m L2 op ka kb))) < 2 ^ 56\<close> using r B' by (simp add: bnd_def)
  have cc: \<open>op = Op_Concat \<Longrightarrow> width ws ds a + width ws ds b < 2 ^ 64\<close>
  proof -
    assume \<open>op = Op_Concat\<close>
    then have \<open>width ws ds (TermL_Bin op a b) = width ws ds a + width ws ds b\<close> by simp
    moreover have \<open>env_ok ws L' k (width ws ds (TermL_Bin op a b))\<close>
      using lower_m_correct[OF TermL_Bin.prems(1-3) R B'] by simp
    ultimately show ?thesis by (simp add: env_ok_def)
  qed
  show ?case using Ia Ib kok_of_env[OF EA] kok_of_env[OF EB] len cc EA EB a b by (simp add: env_ok_def)
next
  case (TermL_Extract hi lo a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  obtain L' k where r: \<open>lower_m ws dm L (TermL_Extract hi lo a) = (L', k)\<close> by (cases \<open>lower_m ws dm L (TermL_Extract hi lo a)\<close>)
  have B': \<open>bnd L'\<close> using TermL_Extract.prems(4) r by simp
  have p: \<open>push_m L1 (CoreTermL_Extract hi lo (cr ka)) (unat hi - unat lo + 1) = (L', k)\<close> using r a by simp
  have B1: \<open>bnd L1\<close> using bnd_pfx[OF pfx_push[OF p] B'] .
  have wt: \<open>wt ws ds a\<close> \<open>unat lo \<le> unat hi\<close> using TermL_Extract.prems(1) by simp_all
  note S = lower_m_correct[OF wt(1) TermL_Extract.prems(2,3) a B1]
  have W: \<open>env_ok ws L' k (width ws ds (TermL_Extract hi lo a))\<close>
    using lower_m_correct[OF TermL_Extract.prems(1-3) r B'] by simp
  have lp: \<open>lpre N ws dm L a\<close> using TermL_Extract.IH[OF wt(1) TermL_Extract.prems(2,3)] TermL_Extract.prems(5) a B1 by simp
  have kk: \<open>kok L1 ka\<close> using S kok_of_env by blast
  have b: \<open>unat hi - unat lo + 1 < 2 ^ 64\<close> using W by (simp add: env_ok_def)
  show ?case using lp kk wt(2) b a by simp
next
  case (TermL_Repeat i a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  let ?wa = \<open>snd L1 ! ka\<close>
  obtain L2 k0 where p: \<open>push_m L1 (CoreTermL_Const []) 0 = (L2, k0)\<close> by (cases \<open>push_m L1 (CoreTermL_Const []) 0\<close>)
  obtain L3 k3 acc where f: \<open>foldl (repeat_step ka ?wa) (L2, k0, 0) [0..<unat i] = (L3, k3, acc)\<close>
    by (cases \<open>foldl (repeat_step ka ?wa) (L2, k0, 0) [0..<unat i]\<close>)
  have R: \<open>lower_m ws dm L (TermL_Repeat i a) = (L3, k3)\<close> using a p f by (simp add: lower_m.simps Let_def)
  have B3: \<open>bnd L3\<close> using TermL_Repeat.prems(4) R by simp
  have B2: \<open>bnd L2\<close> using bnd_pfx[OF repeat_fold_pfx[OF f] B3] .
  have B1: \<open>bnd L1\<close> using bnd_pfx[OF pfx_push[OF p] B2] .
  have wt: \<open>wt ws ds a\<close> \<open>1 \<le> unat i\<close> using TermL_Repeat.prems(1) by simp_all
  note S = lower_m_correct[OF wt(1) TermL_Repeat.prems(2,3) a B1]
  have EA: \<open>env_ok ws L1 ka (width ws ds a)\<close> using S by simp
  have wa: \<open>?wa = width ws ds a\<close> and wa1: \<open>1 \<le> width ws ds a\<close> using EA by (simp_all add: env_ok_def)
  have W: \<open>env_ok ws L3 k3 (width ws ds (TermL_Repeat i a))\<close>
    using lower_m_correct[OF TermL_Repeat.prems(1-3) R B3] by simp
  have iN: \<open>unat i \<le> N\<close>
  proof -
    have 1: \<open>unat i * width ws ds a \<le> N\<close> using TermL_Repeat.prems(5) by simp
    have 2: \<open>unat i * 1 \<le> unat i * width ws ds a\<close> using wa1 by (rule mult_le_mono2)
    show ?thesis using order_trans[OF 2 1] by simp
  qed
  have ov: \<open>?wa * unat i < 2 ^ 64\<close> using W wa by (simp add: env_ok_def mult.commute)
  have pL2: \<open>L2 = (fst L1 @ [CoreTermL_Const []], snd L1 @ [0])\<close> using p by (simp add: push_m_def)
  have len3: \<open>length (fst L3) = length (fst L1) + 1 + unat i\<close>
    using repeat_F_len[of ka ?wa L2 k0 0 \<open>unat i\<close>] f by (simp add: pL2)
  have len: \<open>length (fst L1) + 1 + unat i < 2 ^ 56\<close> using B3 len3 by (simp add: bnd_def)
  show ?case using TermL_Repeat.IH[OF wt(1) TermL_Repeat.prems(2,3)] TermL_Repeat.prems(5) a B1 kok_of_env[OF EA] iN ov len by simp
next
  case (TermL_ZeroExtend i a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  obtain L' k where r: \<open>lower_m ws dm L (TermL_ZeroExtend i a) = (L', k)\<close> by (cases \<open>lower_m ws dm L (TermL_ZeroExtend i a)\<close>)
  have B': \<open>bnd L'\<close> using TermL_ZeroExtend.prems(4) r by simp
  have p: \<open>push_m L1 (CoreTermL_Bin BinOp_Concat (CoreTermL_Const (replicate (unat i) False)) (cr ka)) (snd L1 ! ka + unat i) = (L', k)\<close>
    using r a by simp
  have B1: \<open>bnd L1\<close> using bnd_pfx[OF pfx_push[OF p] B'] .
  have wta: \<open>wt ws ds a\<close> using TermL_ZeroExtend.prems(1) by simp
  note S = lower_m_correct[OF wta TermL_ZeroExtend.prems(2,3) a B1]
  have EA: \<open>env_ok ws L1 ka (width ws ds a)\<close> using S by simp
  have W: \<open>env_ok ws L' k (width ws ds (TermL_ZeroExtend i a))\<close>
    using lower_m_correct[OF TermL_ZeroExtend.prems(1-3) r B'] by simp
  show ?case using TermL_ZeroExtend.IH[OF wta TermL_ZeroExtend.prems(2,3)] TermL_ZeroExtend.prems(5) a B1 kok_of_env[OF EA] W EA
    by (simp add: env_ok_def)
next
  case (TermL_SignExtend i a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  obtain L' k where r: \<open>lower_m ws dm L (TermL_SignExtend i a) = (L', k)\<close> by (cases \<open>lower_m ws dm L (TermL_SignExtend i a)\<close>)
  have B': \<open>bnd L'\<close> using TermL_SignExtend.prems(4) r by simp
  have p: \<open>push_m L1 (CoreTermL_Bin BinOp_Concat
             (CoreTermL_Ite (msb_t ka (snd L1 ! ka)) (CoreTermL_Const (replicate (unat i) True)) (CoreTermL_Const (replicate (unat i) False)))
             (cr ka)) (snd L1 ! ka + unat i) = (L', k)\<close>
    using r a by simp
  have B1: \<open>bnd L1\<close> using bnd_pfx[OF pfx_push[OF p] B'] .
  have wta: \<open>wt ws ds a\<close> using TermL_SignExtend.prems(1) by simp
  note S = lower_m_correct[OF wta TermL_SignExtend.prems(2,3) a B1]
  have EA: \<open>env_ok ws L1 ka (width ws ds a)\<close> using S by simp
  have W: \<open>env_ok ws L' k (width ws ds (TermL_SignExtend i a))\<close>
    using lower_m_correct[OF TermL_SignExtend.prems(1-3) r B'] by simp
  show ?case using TermL_SignExtend.IH[OF wta TermL_SignExtend.prems(2,3)] TermL_SignExtend.prems(5) a B1 kok_of_env[OF EA] W EA
    by (simp add: env_ok_def)
next
  case (TermL_RotateLeft i a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  have wta: \<open>wt ws ds a\<close> using TermL_RotateLeft.prems(1) by simp
  let ?w = \<open>snd L1 ! ka\<close> and ?r = \<open>unat i mod snd L1 ! ka\<close>
  have B1: \<open>bnd L1\<close>
  proof (cases \<open>?r = 0\<close>)
    case True
    then show ?thesis using TermL_RotateLeft.prems(4) a by (simp add: lower_m_RotateLeft' Let_def)
  next
    case False
    let ?t = \<open>CoreTermL_Bin BinOp_Concat (CoreTermL_Extract (word_of_nat (?w - 1 - ?r)) 0 (cr ka))
                (CoreTermL_Extract (word_of_nat (?w - 1)) (word_of_nat (?w - ?r)) (cr ka))\<close>
    have \<open>fst (lower_m ws dm L (TermL_RotateLeft i a)) = fst (push_m L1 ?t ?w)\<close>
      using False a by (simp add: lower_m_RotateLeft' Let_def)
    moreover have \<open>pfx L1 (fst (push_m L1 ?t ?w))\<close> by (simp add: pfx_def push_m_def)
    ultimately show ?thesis using TermL_RotateLeft.prems(4) bnd_pfx by metis
  qed
  note S = lower_m_correct[OF wta TermL_RotateLeft.prems(2,3) a B1]
  have lp: \<open>lpre N ws dm L a\<close> using TermL_RotateLeft.IH[OF wta TermL_RotateLeft.prems(2,3)] TermL_RotateLeft.prems(5) a B1 by simp
  have kk: \<open>kok L1 ka\<close> using S kok_of_env by blast
  show ?case using lp kk a by simp
next
  case (TermL_RotateRight i a)
  obtain L1 ka where a: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  have wta: \<open>wt ws ds a\<close> using TermL_RotateRight.prems(1) by simp
  let ?w = \<open>snd L1 ! ka\<close> and ?r = \<open>unat i mod snd L1 ! ka\<close>
  have B1: \<open>bnd L1\<close>
  proof (cases \<open>?r = 0\<close>)
    case True
    then show ?thesis using TermL_RotateRight.prems(4) a by (simp add: lower_m_RotateRight' Let_def)
  next
    case False
    let ?t = \<open>CoreTermL_Bin BinOp_Concat (CoreTermL_Extract (word_of_nat (?r - 1)) 0 (cr ka))
                (CoreTermL_Extract (word_of_nat (?w - 1)) (word_of_nat ?r) (cr ka))\<close>
    have \<open>fst (lower_m ws dm L (TermL_RotateRight i a)) = fst (push_m L1 ?t ?w)\<close>
      using False a by (simp add: lower_m_RotateRight' Let_def)
    moreover have \<open>pfx L1 (fst (push_m L1 ?t ?w))\<close> by (simp add: pfx_def push_m_def)
    ultimately show ?thesis using TermL_RotateRight.prems(4) bnd_pfx by metis
  qed
  note S = lower_m_correct[OF wta TermL_RotateRight.prems(2,3) a B1]
  have lp: \<open>lpre N ws dm L a\<close> using TermL_RotateRight.IH[OF wta TermL_RotateRight.prems(2,3)] TermL_RotateRight.prems(5) a B1 by simp
  have kk: \<open>kok L1 ka\<close> using S kok_of_env by blast
  show ?case using lp kk a by simp
next
  case (TermL_Ite c a b)
  obtain L1 kc where c: \<open>lower_m ws dm L c = (L1, kc)\<close> by (cases \<open>lower_m ws dm L c\<close>)
  obtain L2 ka where a: \<open>lower_m ws dm L1 a = (L2, ka)\<close> by (cases \<open>lower_m ws dm L1 a\<close>)
  obtain L3 kb where b: \<open>lower_m ws dm L2 b = (L3, kb)\<close> by (cases \<open>lower_m ws dm L2 b\<close>)
  obtain L' k where r: \<open>lower_m ws dm L (TermL_Ite c a b) = (L', k)\<close> by (cases \<open>lower_m ws dm L (TermL_Ite c a b)\<close>)
  have B': \<open>bnd L'\<close> using TermL_Ite.prems(4) r by simp
  have p: \<open>push_m L3 (CoreTermL_Ite (cr kc) (cr ka) (cr kb)) (snd L3 ! ka) = (L', k)\<close> using r c a b by simp
  have B3: \<open>bnd L3\<close> using bnd_pfx[OF pfx_push[OF p] B'] .
  have B2: \<open>bnd L2\<close> using bnd_pfx[OF lower_m_pfx[OF b] B3] .
  have B1: \<open>bnd L1\<close> using bnd_pfx[OF lower_m_pfx[OF a] B2] .
  have wt: \<open>wt ws ds c\<close> \<open>wt ws ds a\<close> \<open>wt ws ds b\<close> \<open>width ws ds c = 1\<close> \<open>width ws ds a = width ws ds b\<close>
    using TermL_Ite.prems(1) by simp_all
  note Sc = lower_m_correct[OF wt(1) TermL_Ite.prems(2,3) c B1]
  have L1: \<open>lok ws L1\<close> and X1: \<open>lext ws L L1\<close> using Sc lext_lok by blast+
  note D1 = dm_ok_lext[OF TermL_Ite.prems(2,3) X1]
  note Sa = lower_m_correct[OF wt(2) L1 D1 a B2]
  have L2: \<open>lok ws L2\<close> and X2: \<open>lext ws L1 L2\<close> using Sa lext_lok by blast+
  note D2 = dm_ok_lext[OF L1 D1 X2]
  note Sb = lower_m_correct[OF wt(3) L2 D2 b B3]
  have X3: \<open>lext ws L2 L3\<close> using Sb by blast
  have EC: \<open>env_ok ws L3 kc (width ws ds c)\<close> using Sc env_lext[OF _ X2] env_lext[OF _ X3] by blast
  have EA: \<open>env_ok ws L3 ka (width ws ds a)\<close> using Sa env_lext[OF _ X3] by blast
  have EB: \<open>env_ok ws L3 kb (width ws ds b)\<close> using Sb by blast
  have Ic: \<open>lpre N ws dm L c\<close> using TermL_Ite.IH(1)[OF wt(1) TermL_Ite.prems(2,3)] TermL_Ite.prems(5) c B1 by simp
  have Ia: \<open>lpre N ws dm L1 a\<close> using TermL_Ite.IH(2)[OF wt(2) L1 D1] TermL_Ite.prems(5) a B2 by simp
  have Ib: \<open>lpre N ws dm L2 b\<close> using TermL_Ite.IH(3)[OF wt(3) L2 D2] TermL_Ite.prems(5) b B3 by simp
  show ?case using Ic Ia Ib kok_of_env[OF EC] kok_of_env[OF EA] kok_of_env[OF EB] c a b by simp
qed

context QFBV_ctx
begin

subsection \<open>The builders of core terms\<close>

text \<open>A function on a \<^verbatim>\<open>Lower\<close> computes the model \<open>m\<close> of the state: the result is a
  well-formed \<^verbatim>\<open>Lower\<close> of the state that \<open>m\<close> gives, and the index that \<open>m\<close> gives.\<close>
definition low_res :: \<open>Lower \<times> 64 word \<times> tnil \<Rightarrow> lst \<times> nat \<Rightarrow> bool\<close> where
  \<open>low_res r m \<equiv> lower_ok (fst r) \<and> lst_of (fst r) = fst m \<and> rvec_length (Lower_defs (fst r)) = length (fst (fst m)) \<and>
     rvec_length (Lower_widths (fst r)) = length (fst (fst m)) \<and> snd r = (word_of_nat (snd m), TNil)\<close>

lemma unat_add_nov: \<open>unat a + unat b < 2 ^ 64 \<Longrightarrow> unat (a + b) = unat a + unat b\<close> for a b :: \<open>64 word\<close>
  using unat_add_lem[of a b] by (simp add: word_size)

definition push_def_contract :: \<open>Lower \<Rightarrow> CoreTerm \<Rightarrow> 64 word \<Rightarrow> ('s, Lower \<times> 64 word \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>push_def_contract l t w \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>lower_ok l \<and> rvec_length (Lower_defs l) < 2 ^ 56\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>low_res r (push_m (lst_of l) (ct_of t) (unat w))\<rangle>)\<close>

lemma word_of_nat_unat [simp]: \<open>word_of_nat (unat w) = w\<close>
  by simp

lemma push_def_spec [crush_specs]:
  shows \<open>\<Gamma>; push_def l t w \<Turnstile>\<^sub>F push_def_contract l t w\<close>
  apply (crush_boot f: push_def_def contract: push_def_contract_def)
  apply (crush_base simp add: lower_ok_def push_m_def low_res_def)
  done

definition cref_contract :: \<open>nat \<Rightarrow> ('s, CoreTerm, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>cref_contract k \<equiv> make_function_contract can_alloc_reference (\<lambda>r. can_alloc_reference \<star> \<langle>ct_of r = cr k\<rangle>)\<close>

lemma cref_spec [crush_specs]:
  shows \<open>\<Gamma>; cref k \<Turnstile>\<^sub>F cref_contract (unat k)\<close>
  by (crush_boot f: cref_def contract: cref_contract_def) (crush_base simp add: cr_def)

definition cnot_contract :: \<open>CoreTerm \<Rightarrow> ('s, CoreTerm, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>cnot_contract a \<equiv> make_function_contract can_alloc_reference (\<lambda>r. can_alloc_reference \<star> \<langle>ct_of r = CoreTermL_Not (ct_of a)\<rangle>)\<close>

lemma cnot_spec [crush_specs]:
  shows \<open>\<Gamma>; cnot a \<Turnstile>\<^sub>F cnot_contract a\<close>
  by (crush_boot f: cnot_def contract: cnot_contract_def) crush_base

definition cbin_contract :: \<open>BinOp \<Rightarrow> CoreTerm \<Rightarrow> CoreTerm \<Rightarrow> ('s, CoreTerm, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>cbin_contract op a b \<equiv>
     make_function_contract can_alloc_reference (\<lambda>r. can_alloc_reference \<star> \<langle>ct_of r = CoreTermL_Bin op (ct_of a) (ct_of b)\<rangle>)\<close>

lemma cbin_spec [crush_specs]:
  shows \<open>\<Gamma>; cbin op a b \<Turnstile>\<^sub>F cbin_contract op a b\<close>
  by (crush_boot f: cbin_def contract: cbin_contract_def) crush_base

definition cite_contract :: \<open>CoreTerm \<Rightarrow> CoreTerm \<Rightarrow> CoreTerm \<Rightarrow> ('s, CoreTerm, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>cite_contract c a b \<equiv>
     make_function_contract can_alloc_reference (\<lambda>r. can_alloc_reference \<star> \<langle>ct_of r = CoreTermL_Ite (ct_of c) (ct_of a) (ct_of b)\<rangle>)\<close>

lemma cite_spec [crush_specs]:
  shows \<open>\<Gamma>; cite c a b \<Turnstile>\<^sub>F cite_contract c a b\<close>
  by (crush_boot f: cite_def contract: cite_contract_def) crush_base

definition cextract_contract :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> CoreTerm \<Rightarrow> ('s, CoreTerm, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>cextract_contract hi lo a \<equiv>
     make_function_contract can_alloc_reference (\<lambda>r. can_alloc_reference \<star> \<langle>ct_of r = CoreTermL_Extract hi lo (ct_of a)\<rangle>)\<close>

lemma cextract_spec [crush_specs]:
  shows \<open>\<Gamma>; cextract hi lo a \<Turnstile>\<^sub>F cextract_contract hi lo a\<close>
  by (crush_boot f: cextract_def contract: cextract_contract_def) crush_base

text \<open>The builders that compute \<open>w - 1\<close> need \<open>1 \<le> w\<close>.\<close>
definition cone_contract :: \<open>nat \<Rightarrow> ('s, CoreTerm, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>cone_contract w \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>1 \<le> w \<and> w < 2 ^ 56\<rangle>) (\<lambda>r. can_alloc_reference \<star> \<langle>ct_of r = one_t w\<rangle>)\<close>

lemma unat_minus_1: \<open>1 \<le> unat w \<Longrightarrow> unat (w - 1) = unat w - 1\<close> for w :: \<open>64 word\<close>
  by (simp add: unat_sub word_le_nat_alt)

lemma word_minus_1_of_nat: \<open>1 \<le> unat w \<Longrightarrow> w - 1 = word_of_nat (unat w - 1)\<close> for w :: \<open>64 word\<close>
  by (metis unat_minus_1 word_unat.Rep_inverse)

lemma cone_spec [crush_specs]:
  shows \<open>\<Gamma>; cone w \<Turnstile>\<^sub>F cone_contract (unat w)\<close>
  apply (crush_boot f: cone_def contract: cone_contract_def)
  apply (crush_base simp add: one_t_def unat_minus_1 word_le_nat_alt from_elem_Some rvec_from_elem_val_def)
  done

definition cneg_contract :: \<open>nat \<Rightarrow> nat \<Rightarrow> ('s, CoreTerm, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>cneg_contract k w \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>1 \<le> w \<and> w < 2 ^ 56\<rangle>) (\<lambda>r. can_alloc_reference \<star> \<langle>ct_of r = neg_t k w\<rangle>)\<close>

lemma cneg_spec [crush_specs]:
  shows \<open>\<Gamma>; cneg k w \<Turnstile>\<^sub>F cneg_contract (unat k) (unat w)\<close>
  by (crush_boot f: cneg_def contract: cneg_contract_def) (crush_base simp add: neg_t_def)

definition cmsb_contract :: \<open>nat \<Rightarrow> nat \<Rightarrow> ('s, CoreTerm, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>cmsb_contract k w \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>1 \<le> w\<rangle>) (\<lambda>r. can_alloc_reference \<star> \<langle>ct_of r = msb_t k w\<rangle>)\<close>

lemma cmsb_spec [crush_specs]:
  shows \<open>\<Gamma>; cmsb k w \<Turnstile>\<^sub>F cmsb_contract (unat k) (unat w)\<close>
  by (crush_boot f: cmsb_def contract: cmsb_contract_def) (crush_base simp add: msb_t_def word_le_nat_alt)

definition cabs_contract :: \<open>nat \<Rightarrow> nat \<Rightarrow> ('s, CoreTerm, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>cabs_contract k w \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>1 \<le> w \<and> w < 2 ^ 56\<rangle>) (\<lambda>r. can_alloc_reference \<star> \<langle>ct_of r = abs_t k w\<rangle>)\<close>

lemma cabs_spec [crush_specs]:
  shows \<open>\<Gamma>; cabs k w \<Turnstile>\<^sub>F cabs_contract (unat k) (unat w)\<close>
  by (crush_boot f: cabs_def contract: cabs_contract_def) (crush_base simp add: abs_t_def)

definition cslt_contract :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('s, CoreTerm, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>cslt_contract ka kb w \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>1 \<le> w\<rangle>) (\<lambda>r. can_alloc_reference \<star> \<langle>ct_of r = slt_t ka kb w\<rangle>)\<close>

lemma cslt_spec [crush_specs]:
  shows \<open>\<Gamma>; cslt ka kb w \<Turnstile>\<^sub>F cslt_contract (unat ka) (unat kb) (unat w)\<close>
  by (crush_boot f: cslt_def contract: cslt_contract_def) (crush_base simp add: slt_t_def)

definition csle_contract :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('s, CoreTerm, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>csle_contract ka kb w \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>1 \<le> w\<rangle>) (\<lambda>r. can_alloc_reference \<star> \<langle>ct_of r = sle_t ka kb w\<rangle>)\<close>

lemma csle_spec [crush_specs]:
  shows \<open>\<Gamma>; csle ka kb w \<Turnstile>\<^sub>F csle_contract (unat ka) (unat kb) (unat w)\<close>
  by (crush_boot f: csle_def contract: csle_contract_def) (crush_base simp add: sle_t_def)

subsection \<open>\<^verbatim>\<open>lower_bin\<close>\<close>

lemma unat_plus_of_nat: \<open>a + b < 2 ^ 64 \<Longrightarrow> unat (word_of_nat a + word_of_nat b :: 64 word) = a + b\<close>
  using unat_of_nat_64'[of \<open>a + b\<close>] by simp

lemma unat_1_plus_wn:
  fixes n :: nat
  assumes \<open>n < 18446744073709551615\<close>
  shows \<open>unat (1 + word_of_nat n :: 64 word) = Suc n\<close>
proof -
  have \<open>unat (1 :: 64 word) + unat (word_of_nat n :: 64 word) < 2 ^ LENGTH(64)\<close>
    using assms by (simp add: unat_of_nat_64')
  then have \<open>unat (1 + word_of_nat n :: 64 word) = unat (1 :: 64 word) + unat (word_of_nat n :: 64 word)\<close>
    using unat_add_lem by blast
  then show ?thesis using assms by (simp add: unat_of_nat_64')
qed

lemma unat_wn_plus_word:
  fixes a :: nat and i :: \<open>64 word\<close>
  assumes \<open>a + unat i < 18446744073709551616\<close>
  shows \<open>unat (word_of_nat a + i :: 64 word) = a + unat i\<close>
proof -
  have \<open>unat (word_of_nat a :: 64 word) + unat i < 2 ^ LENGTH(64)\<close> using assms by (simp add: unat_of_nat_64')
  then have \<open>unat (word_of_nat a + i :: 64 word) = unat (word_of_nat a :: 64 word) + unat i\<close>
    using unat_add_lem by blast
  then show ?thesis using assms by (simp add: unat_of_nat_64')
qed

lemma word_of_nat_minus:
  fixes a b :: nat
  assumes \<open>b \<le> a\<close>
  shows \<open>(word_of_nat a - word_of_nat b :: 64 word) = word_of_nat (a - b)\<close>
proof -
  have e: \<open>a - b + b = a\<close> using assms by simp
  have \<open>(word_of_nat a - word_of_nat b :: 64 word) = word_of_nat (a - b + b) - word_of_nat b\<close>
    by (simp only: e)
  also have \<open>\<dots> = word_of_nat (a - b)\<close> by (simp only: of_nat_add add_diff_cancel_right')
  finally show ?thesis .
qed

lemma unat_extract_w:
  fixes hi lo :: \<open>64 word\<close>
  assumes \<open>unat lo \<le> unat hi\<close> \<open>unat hi - unat lo + 1 < 18446744073709551616\<close>
  shows \<open>unat ((hi - lo) + 1 :: 64 word) = unat hi - unat lo + 1\<close>
proof -
  have s: \<open>unat (hi - lo) = unat hi - unat lo\<close> using assms(1) by (simp add: unat_sub word_le_nat_alt)
  have \<open>unat (hi - lo) < 18446744073709551615\<close> using s assms(2) by simp
  then show ?thesis using unat_word_Suc_simp'[of \<open>hi - lo\<close>] s by simp
qed

lemma unat_eq_0': \<open>(unat (x :: 64 word) = 0) = (x = 0)\<close>
  by (simp add: unat_eq_zero)

text \<open>The word arithmetic of the two extracts of a rotation, for @{term \<open>1 \<le> w\<close>} and @{term \<open>r < w\<close>}.\<close>
lemma rotate_extract_words:
  fixes w r :: nat
  assumes \<open>1 \<le> w\<close> \<open>r < w\<close>
  shows \<open>(word_of_nat w - 1 - word_of_nat r :: 64 word) = word_of_nat (w - 1 - r)\<close>
    and \<open>(word_of_nat w - 1 :: 64 word) = word_of_nat (w - 1)\<close>
    and \<open>(word_of_nat w - word_of_nat r :: 64 word) = word_of_nat (w - r)\<close>
proof -
  have o: \<open>(1 :: 64 word) = word_of_nat 1\<close> by simp
  show e1: \<open>(word_of_nat w - 1 :: 64 word) = word_of_nat (w - 1)\<close>
    using assms(1) o word_of_nat_minus[of 1 w] by simp
  show \<open>(word_of_nat w - word_of_nat r :: 64 word) = word_of_nat (w - r)\<close>
    using assms(2) word_of_nat_minus[of r w] by simp
  have \<open>(word_of_nat w - 1 - word_of_nat r :: 64 word) = word_of_nat (w - 1) - word_of_nat r\<close>
    using e1 by simp
  also have \<open>\<dots> = word_of_nat (w - 1 - r)\<close> using assms(2) word_of_nat_minus[of r \<open>w - 1\<close>] by simp
  finally show \<open>(word_of_nat w - 1 - word_of_nat r :: 64 word) = word_of_nat (w - 1 - r)\<close> .
qed

definition lower_bin_contract :: \<open>Lower \<Rightarrow> Op \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, Lower \<times> 64 word \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>lower_bin_contract l op ka kb \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
        \<langle>lower_ok l \<and> kok (lst_of l) (unat ka) \<and> kok (lst_of l) (unat kb) \<and>
         length (fst (fst (lower_bin_m (lst_of l) op (unat ka) (unat kb)))) < 2 ^ 56 \<and>
         (op = Op_Concat \<longrightarrow> snd (lst_of l) ! unat ka + snd (lst_of l) ! unat kb < 2 ^ 64)\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>low_res r (lower_bin_m (lst_of l) op (unat ka) (unat kb))\<rangle>)\<close>

lemma lower_bin_spec [crush_specs]:
  shows \<open>\<Gamma>; lower_bin l op ka kb \<Turnstile>\<^sub>F lower_bin_contract l op ka kb\<close>
  apply (crush_boot f: lower_bin_def contract: lower_bin_contract_def)
  apply (cases op; simp only: Op_case_simps)
  sorry \<comment> \<open>TODO rvec: the cases of lower_bin (as lower_rec_step: low_res_def, widths_nth, lst_of_def)\<close>

subsection \<open>\<^verbatim>\<open>lower\<close>\<close>

text \<open>The \<open>k\<close>-th unfolding of \<^const>\<open>lower\<close>: its precondition requires the recursion depth
  \<open>size t + 1\<close> to be at most \<open>k\<close>, so the innermost function is never called. The widths of the
  variables and the core definitions of the definitions are given as words.\<close>
definition lower_contract ::
  \<open>nat \<Rightarrow> 64 word rvec \<Rightarrow> 64 word rvec \<Rightarrow> Lower \<Rightarrow> Term \<Rightarrow> ('s, Lower \<times> 64 word \<times> tnil, 'abort) function_contract\<close>
  where
  [crush_contracts]: \<open>lower_contract k wsw dmw l t \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
        \<langle>Suc (size t) \<le> k \<and> lower_ok l \<and>
         lpre urust_fuel (map unat (rvec_elems wsw)) (map unat (rvec_elems dmw)) (lst_of l) (term_of t) \<and>
         length (fst (fst (lower_m (map unat (rvec_elems wsw)) (map unat (rvec_elems dmw)) (lst_of l) (term_of t))))
           < 2 ^ 56\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>low_res r (lower_m (map unat (rvec_elems wsw)) (map unat (rvec_elems dmw)) (lst_of l) (term_of t))\<rangle>)\<close>

lemma unat_mod_of_nat: \<open>w < 2 ^ 64 \<Longrightarrow> unat (i mod word_of_nat w :: 64 word) = unat i mod w\<close>
  by (simp add: unat_mod unat_of_nat_64')

lemma rot_mod_word:
  fixes i :: \<open>64 word\<close>
  assumes \<open>w < 18446744073709551616\<close>
  shows \<open>unat (i mod word_of_nat w) = unat i mod w\<close>
    and \<open>(i mod word_of_nat w = 0) = (unat i mod w = 0)\<close>
proof -
  show u: \<open>unat (i mod word_of_nat w) = unat i mod w\<close> using assms by (simp add: unat_mod_of_nat)
  have \<open>(i mod word_of_nat w = 0) = (unat (i mod word_of_nat w) = 0)\<close> by (rule unat_eq_0'[symmetric])
  then show \<open>(i mod word_of_nat w = 0) = (unat i mod w = 0)\<close> using u by simp
qed

lemma rot_word_ineqs:
  fixes i :: \<open>64 word\<close>
  assumes \<open>Suc 0 \<le> w\<close> \<open>w < 18446744073709551616\<close>
  shows \<open>1 \<le> (word_of_nat w :: 64 word)\<close>
    and \<open>i mod word_of_nat w \<le> word_of_nat w\<close>
    and \<open>i mod word_of_nat w \<le> word_of_nat w - 1\<close>
    and \<open>(word_of_nat w :: 64 word) \<noteq> 0\<close>
proof -
  have uw: \<open>unat (word_of_nat w :: 64 word) = w\<close> using assms(2) by (rule unat_of_nat_64')
  have um: \<open>unat (i mod word_of_nat w) = unat i mod w\<close> using assms(2) by (rule rot_mod_word(1))
  have lt: \<open>unat i mod w < w\<close> using assms(1) by simp
  show o: \<open>1 \<le> (word_of_nat w :: 64 word)\<close> using assms(1) uw by (simp add: word_le_nat_alt)
  show \<open>i mod word_of_nat w \<le> word_of_nat w\<close> using lt uw um by (simp add: word_le_nat_alt)
  have \<open>unat (word_of_nat w - 1 :: 64 word) = w - 1\<close> using o uw by (simp add: unat_sub)
  then show \<open>i mod word_of_nat w \<le> word_of_nat w - 1\<close> using lt um by (simp add: word_le_nat_alt)
  show \<open>(word_of_nat w :: 64 word) \<noteq> 0\<close> using uw assms(1) by auto
qed

lemma rot_mod_pos:
  fixes i :: \<open>64 word\<close>
  assumes \<open>w < 18446744073709551616\<close> \<open>0 < unat i mod w\<close>
  shows \<open>1 \<le> i mod word_of_nat w\<close>
proof -
  have \<open>unat (i mod word_of_nat w) = unat i mod w\<close> using assms(1) by (rule rot_mod_word(1))
  then show ?thesis using assms(2) by (simp add: word_le_nat_alt)
qed

lemma rot_mod_eq:
  fixes i :: \<open>64 word\<close>
  assumes \<open>w < 18446744073709551616\<close>
  shows \<open>i mod word_of_nat w = word_of_nat (unat i mod w)\<close>
proof -
  have \<open>word_of_nat (unat (i mod word_of_nat w)) = i mod word_of_nat w\<close> by (rule wnunat)
  then show ?thesis using rot_mod_word(1)[OF assms, of i] by simp
qed

lemma wn_minus1:
  \<open>Suc 0 \<le> m \<Longrightarrow> (word_of_nat m :: 64 word) - 1 = word_of_nat (m - Suc 0)\<close>
  using word_of_nat_minus[of 1 m] by simp

lemma wn_mod_le:
  fixes i :: \<open>64 word\<close>
  assumes \<open>Suc 0 \<le> w\<close> \<open>w < 18446744073709551616\<close>
  shows \<open>(word_of_nat (unat i mod w) :: 64 word) \<le> word_of_nat w\<close>
    and \<open>(word_of_nat (unat i mod w) :: 64 word) \<le> word_of_nat w - 1\<close>
    and \<open>(1 :: 64 word) \<le> word_of_nat w\<close>
proof -
  have lt: \<open>unat i mod w < w\<close> using assms(1) by simp
  have u1: \<open>unat (word_of_nat (unat i mod w) :: 64 word) = unat i mod w\<close>
    by (rule unat_of_nat_64') (use lt assms(2) in linarith)
  have uw: \<open>unat (word_of_nat w :: 64 word) = w\<close> using assms(2) by (rule unat_of_nat_64')
  show \<open>(word_of_nat (unat i mod w) :: 64 word) \<le> word_of_nat w\<close>
    using lt u1 uw by (simp add: word_le_nat_alt)
  show o: \<open>(1 :: 64 word) \<le> word_of_nat w\<close> using assms(1) uw by (simp add: word_le_nat_alt)
  have \<open>unat (word_of_nat w - 1 :: 64 word) = w - 1\<close> using o uw by (simp add: unat_sub)
  then show \<open>(word_of_nat (unat i mod w) :: 64 word) \<le> word_of_nat w - 1\<close>
    using lt u1 by (simp add: word_le_nat_alt)
qed

lemma wn_mod_ne0:
  fixes i :: \<open>64 word\<close>
  assumes \<open>Suc 0 \<le> w\<close> \<open>w < 18446744073709551616\<close>
  shows \<open>((word_of_nat (unat i mod w) :: 64 word) = 0) = (unat i mod w = 0)\<close>
proof -
  have \<open>unat i mod w < w\<close> using assms(1) by simp
  then have \<open>unat i mod w < 18446744073709551616\<close> using assms(2) by linarith
  then have \<open>unat (word_of_nat (unat i mod w) :: 64 word) = unat i mod w\<close> by (rule unat_of_nat_64')
  then show ?thesis by (metis unat_eq_0')
qed

lemma wn_mod_pos:
  fixes i :: \<open>64 word\<close>
  assumes \<open>Suc 0 \<le> w\<close> \<open>w < 18446744073709551616\<close> \<open>\<not> (unat i mod w = 0)\<close>
  shows \<open>(1 :: 64 word) \<le> word_of_nat (unat i mod w)\<close>
proof -
  have \<open>unat i mod w < w\<close> using assms(1) by simp
  then have \<open>unat i mod w < 18446744073709551616\<close> using assms(2) by linarith
  then have \<open>unat (word_of_nat (unat i mod w) :: 64 word) = unat i mod w\<close> by (rule unat_of_nat_64')
  then show ?thesis using assms(3) by (simp add: word_le_nat_alt)
qed

lemma wn_rot_sub:
  fixes i :: \<open>64 word\<close>
  assumes \<open>Suc 0 \<le> w\<close>
  shows \<open>(word_of_nat w :: 64 word) - 1 - word_of_nat (unat i mod w) = word_of_nat (w - Suc (unat i mod w))\<close>
proof -
  have lt: \<open>unat i mod w < w\<close> using assms by simp
  have e: \<open>w = (w - Suc (unat i mod w)) + 1 + unat i mod w\<close> using lt by simp
  have \<open>(word_of_nat ((w - Suc (unat i mod w)) + 1 + unat i mod w) :: 64 word)
        = word_of_nat (w - Suc (unat i mod w)) + 1 + word_of_nat (unat i mod w)\<close>
    by (simp only: of_nat_add of_nat_1)
  then have w: \<open>(word_of_nat w :: 64 word) = word_of_nat (w - Suc (unat i mod w)) + 1 + word_of_nat (unat i mod w)\<close>
    by (simp only: e[symmetric])
  show ?thesis by (simp only: w add.assoc diff_diff_eq add_diff_cancel_right')
qed

lemma lm_mono: \<open>length (fst L) \<le> length (fst (fst (lower_m ws dm L t)))\<close>
  using pfx_length[OF lower_m_pfx[of ws dm L t \<open>fst (lower_m ws dm L t)\<close> \<open>snd (lower_m ws dm L t)\<close>]] by simp

lemma lm_bin_len:
  assumes \<open>length (fst (fst (lower_m ws dm L (TermL_Bin op a b)))) < N\<close>
  shows \<open>length (fst (fst (lower_m ws dm (fst (lower_m ws dm L a)) b))) < N\<close>
    and \<open>length (fst (fst (lower_m ws dm L a))) < N\<close>
proof -
  obtain L1 ka where 1: \<open>lower_m ws dm L a = (L1, ka)\<close> by (cases \<open>lower_m ws dm L a\<close>)
  obtain L2 kb where 2: \<open>lower_m ws dm L1 b = (L2, kb)\<close> by (cases \<open>lower_m ws dm L1 b\<close>)
  obtain L3 k where 3: \<open>lower_bin_m L2 op ka kb = (L3, k)\<close> by (cases \<open>lower_bin_m L2 op ka kb\<close>)
  have \<open>length (fst L3) < N\<close> using assms 1 2 3 by simp
  moreover have \<open>length (fst L2) \<le> length (fst L3)\<close> using pfx_length[OF lower_bin_m_pfx[OF 3]] by simp
  moreover have \<open>length (fst L1) \<le> length (fst L2)\<close> using pfx_length[OF lower_m_pfx[OF 2]] by simp
  ultimately show \<open>length (fst (fst (lower_m ws dm (fst (lower_m ws dm L a)) b))) < N\<close>
    and \<open>length (fst (fst (lower_m ws dm L a))) < N\<close> using 1 2 by simp_all
qed

lemma widths_nth: \<open>map unat (rvec_elems w) = ys \<Longrightarrow> k < length ys \<Longrightarrow> unat (rvec_elems w ! k) = ys ! k\<close>
  by (metis length_map nth_map)

lemma widths_add:
  \<open>map unat (rvec_elems w) = ys \<Longrightarrow> k < length ys \<Longrightarrow> ys ! k + unat i < 2 ^ 64 \<Longrightarrow>
   unat (rvec_elems w ! k + i) = ys ! k + unat i\<close> for w :: \<open>64 word rvec\<close> and i :: \<open>64 word\<close>
  using unat_add_nov[of \<open>rvec_elems w ! k\<close> i] widths_nth[of w ys k] by simp

lemma lower_rec_step_spec:
  assumes IH: \<open>\<And>wsw dmw l t. \<Gamma>; R wsw dmw l t \<Turnstile>\<^sub>F lower_contract k wsw dmw l t\<close>
  shows \<open>\<Gamma>; lower_rec_step R wsw dmw l t \<Turnstile>\<^sub>F lower_contract (Suc k) wsw dmw l t\<close>
proof (cases t)
  case (Term_Const bs)
  show ?thesis unfolding Term_Const
    apply (crush_boot f: lower_rec_step_def contract: lower_contract_def)
    apply (crush_base simp add: unat_of_nat_64' push_m_def lower_ok_def)
    done
next
  case (Term_Var i)
  show ?thesis unfolding Term_Var
    apply (crush_boot f: lower_rec_step_def contract: lower_contract_def)
    apply (crush_base simp add: nth_map push_m_def lower_ok_def)
    done
next
  case (Term_Ref j)
  show ?thesis unfolding Term_Ref
    apply (crush_boot f: lower_rec_step_def contract: lower_contract_def)
    apply (crush_base simp add: nth_map push_m_def lower_ok_def low_res_def)
    done
next
  case (Term_Not a)
  show ?thesis unfolding Term_Not
    apply (crush_boot f: lower_rec_step_def contract: lower_contract_def)
    apply (crush_base specs add: IH simp add: low_res_def lower_ok_def push_m_def from_elem_Some rvec_from_elem_val_def kok_def unat_of_nat_64' nth_map widths_nth)
    apply (all \<open>(metis length_map)?\<close>)
    done
next
  case (Term_Neg a)
  show ?thesis unfolding Term_Neg
    apply (crush_boot f: lower_rec_step_def contract: lower_contract_def)
    apply (crush_base specs add: IH simp add: low_res_def lower_ok_def push_m_def from_elem_Some rvec_from_elem_val_def kok_def unat_of_nat_64' nth_map widths_nth)
    apply (all \<open>(metis length_map)?\<close>)
    done
next
  case (Term_Bin op a b)
  show ?thesis unfolding Term_Bin
    apply (crush_boot f: lower_rec_step_def contract: lower_contract_def)
    apply (crush_base specs add: IH simp add: low_res_def lower_ok_def push_m_def from_elem_Some rvec_from_elem_val_def kok_def unat_of_nat_64' nth_map widths_nth)
    apply (auto simp add: lst_of_def kok_def widths_nth unat_of_nat_64' nth_map lm_bin_len)
    apply (all \<open>(metis length_map lm_mono le_less_trans order.strict_trans2)?\<close>)
    done
next
  case (Term_Extract hi lo a)
  show ?thesis unfolding Term_Extract
    apply (crush_boot f: lower_rec_step_def contract: lower_contract_def)
    apply (crush_base specs add: IH simp add: low_res_def lower_ok_def push_m_def from_elem_Some rvec_from_elem_val_def kok_def unat_of_nat_64' nth_map widths_nth unat_extract_w)
    apply (all \<open>(metis length_map)?\<close>)
    apply (simp_all add: word_le_nat_alt unat_sub)
    done
next
  case (Term_Repeat i a)
  show ?thesis unfolding Term_Repeat
    apply (crush_boot f: lower_rec_step_def contract: lower_contract_def)
    apply (crush_base specs add: IH simp add: low_res_def lower_ok_def push_m_def from_elem_Some rvec_from_elem_val_def kok_def unat_of_nat_64' nth_map lower_m_Repeat'' Let_def)
    subgoal for la lb l_ref k_ref acc_ref j_ref
      apply (ucincl_discharge\<open>rule_tac
        INV=\<open>\<lambda>c. \<Squnion>gl ll gk kk ga aa gj jj. l_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>ll \<star> k_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>kk \<star>
             acc_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>aa \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>jj \<star> can_alloc_reference \<star>
             \<langle>unat jj \<le> unat i \<and> length (fst (fst (lower_m (map unat (rvec_elems wsw)) (map unat (rvec_elems dmw)) (lst_of l) (term_of a)))) + 1 + unat jj < 2 ^ 64 \<and>
              lower_ok ll \<and> lst_of ll = fst (rep_fold (map unat (rvec_elems wsw)) (map unat (rvec_elems dmw)) (lst_of l) (term_of a) (unat jj)) \<and>
              kk = word_of_nat (fst (snd (rep_fold (map unat (rvec_elems wsw)) (map unat (rvec_elems dmw)) (lst_of l) (term_of a) (unat jj)))) \<and>
              aa = word_of_nat (snd (snd (rep_fold (map unat (rvec_elems wsw)) (map unat (rvec_elems dmw)) (lst_of l) (term_of a) (unat jj)))) \<and>
              unat i - unat jj \<le> c\<rangle>\<close> and
        INV'=\<open>\<lambda>c. \<Squnion>gl ll gk kk ga aa gj jj. l_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>ll \<star> k_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>kk \<star>
             acc_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>aa \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>jj \<star> can_alloc_reference \<star>
             \<langle>unat jj < unat i \<and> length (fst (fst (lower_m (map unat (rvec_elems wsw)) (map unat (rvec_elems dmw)) (lst_of l) (term_of a)))) + 1 + unat jj < 2 ^ 64 \<and>
              lower_ok ll \<and> lst_of ll = fst (rep_fold (map unat (rvec_elems wsw)) (map unat (rvec_elems dmw)) (lst_of l) (term_of a) (unat jj)) \<and>
              kk = word_of_nat (fst (snd (rep_fold (map unat (rvec_elems wsw)) (map unat (rvec_elems dmw)) (lst_of l) (term_of a) (unat jj)))) \<and>
              aa = word_of_nat (snd (snd (rep_fold (map unat (rvec_elems wsw)) (map unat (rvec_elems dmw)) (lst_of l) (term_of a) (unat jj)))) \<and>
              unat i - unat jj \<le> Suc c\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_bounded_while_framedI\<close>)
      sorry \<comment> \<open>TODO rvec: the Repeat loop step\<close>
    apply (metis length_map)
    done
next
  case (Term_ZeroExtend i a)
  show ?thesis unfolding Term_ZeroExtend
    apply (crush_boot f: lower_rec_step_def contract: lower_contract_def)
    apply (crush_base specs add: IH simp add: low_res_def lower_ok_def push_m_def from_elem_Some rvec_from_elem_val_def kok_def unat_of_nat_64' nth_map widths_nth unat_wn_plus_word)
    apply (auto simp add: lst_of_def kok_def widths_nth unat_of_nat_64' nth_map)
    prefer 2 apply (metis length_map)
    apply (rule widths_add; (assumption | simp)?)
    done
next
  case (Term_SignExtend i a)
  show ?thesis unfolding Term_SignExtend
    apply (crush_boot f: lower_rec_step_def contract: lower_contract_def)
    apply (crush_base specs add: IH simp add: low_res_def lower_ok_def push_m_def from_elem_Some rvec_from_elem_val_def kok_def unat_of_nat_64' nth_map widths_nth unat_wn_plus_word)
    apply (auto simp add: lst_of_def kok_def widths_nth unat_of_nat_64' nth_map)
    prefer 2 apply (metis length_map)
    apply (rule widths_add; (assumption | simp)?)
    done
next
  case (Term_RotateLeft i a)
  show ?thesis sorry \<comment> \<open>TODO rvec: the word facts on \<open>rvec_elems (Lower_widths _) ! k\<close> (see 1fdec72)\<close>
next
  case (Term_RotateRight i a)
  show ?thesis sorry \<comment> \<open>TODO rvec: as for RotateLeft\<close>
next
  case (Term_Ite c a b)
  show ?thesis sorry \<comment> \<open>TODO rvec: as Term_Bin (auto with lst_of_def; a lemma like lm_bin_len for three operands)\<close>
qed

lemma lower_rec_spec:
  shows \<open>\<Gamma>; (lower_rec_step ^^ k) g wsw dmw l t \<Turnstile>\<^sub>F lower_contract k wsw dmw l t\<close>
proof (induction k arbitrary: wsw dmw l t)
  case 0
  show ?case
    apply (ucincl_discharge\<open>intro satisfies_function_contractI\<close>)
    apply (subst wp_sstriple_iff)
    apply (simp add: lower_contract_def Let_def apure_precise_False asepconj_bot_zero2 bot_aentails_all)
    done
next
  case (Suc k)
  show ?case
    unfolding funpow.simps(2) comp_def by (rule lower_rec_step_spec) (rule Suc.IH)
qed

lemma lower_spec [crush_specs]:
  shows \<open>\<Gamma>; lower wsw dmw l t \<Turnstile>\<^sub>F lower_contract urust_fuel wsw dmw l t\<close>
  unfolding lower_def by (rule lower_rec_spec)

end

end
