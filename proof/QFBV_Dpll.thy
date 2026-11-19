theory QFBV_Dpll
  imports QFBV_DpllWatch
begin

section \<open>DPLL: contracts of propagation over the watches and of the search\<close>

context QFBV_ctx
begin

text \<open>The result of \<^verbatim>\<open>wpropagate\<close> from the watches \<open>p\<close>, the trail \<open>t\<close> and the position \<open>q\<close>.\<close>
definition wprop_wpost ::
  \<open>Lit list list \<Rightarrow> 64 word list \<Rightarrow> Lit list \<Rightarrow> nat \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow>
   Lit list \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> bool\<close> where
  \<open>wprop_wpost cs p t q p1 nx1 h1 t1 q1 b \<equiv> wl_ok cs p1 nx1 h1 \<and> q \<le> q1 \<and>
     (\<forall>k \<le> length t. WP cs p t k \<longrightarrow> WP cs p1 t1 k) \<and>
     (b \<longrightarrow> q1 = length t1 \<and> (WS cs p t (set (take q t)) \<longrightarrow> WS cs p1 t1 (set t1)))\<close>

lemma wx_ex: \<open>q < length t \<Longrightarrow> lidx (lneg (t ! q)) = x \<Longrightarrow> \<exists>w. lidx w = x \<and> lneg w \<in> set t\<close>
  by (metis lneg_lneg nth_mem)

lemma wpw_step:
  assumes \<open>wprop_winv cs p t q p' nx' h' t' q'\<close> \<open>q' < length t'\<close> \<open>visit_post cs xn p' t' p1 nx1 h1 t1 b\<close>
    \<open>lidx (lneg (t' ! q')) = xn\<close> \<open>wprop_post cs t' n a1 t1 b'\<close> \<open>wprop_inv cs t n a' t'\<close>
  shows \<open>(b \<longrightarrow> wprop_winv cs p t q p1 nx1 h1 t1 (Suc q')) \<and> wprop_wpost cs p t q p1 nx1 h1 t1 (Suc q') False\<close>
proof -
  obtain e where e: \<open>t' = t @ e\<close> using assms(6) by (auto simp: wprop_inv_def)
  have T: \<open>\<exists>e. t = take (length t) t'\<close> \<open>length t \<le> length t'\<close> using e by simp_all
  have T1: \<open>\<exists>e. t1 = t' @ e\<close> using assms(5) by (auto simp: wprop_post_def wprop_inv_def)
  note S = wprop_winv_step[OF assms(1,2) T(1) assms(3)[folded assms(4)] T1 T(2)]
  have \<open>q \<le> q'\<close> using assms(1) by (simp add: wprop_winv_def)
  then show ?thesis using S by (simp add: wprop_wpost_def)
qed

lemma wpw_exit':
  \<open>wprop_winv cs p t q p' nx' h' t' (length t') \<Longrightarrow> wprop_wpost cs p t q p' nx' h' t' (length t') True\<close>
  by (simp add: wprop_winv_def wprop_wpost_def)

lemma winv_wl: \<open>wprop_winv cs p t q p' nx' h' t' q' \<Longrightarrow> wl_ok cs p' nx' h'\<close>
  by (simp add: wprop_winv_def)

lemma wpw_exit:
  \<open>wprop_winv cs p t q p' nx' h' t' q' \<Longrightarrow> \<not> q' < length t' \<Longrightarrow> q' \<le> length t' \<Longrightarrow>
   wprop_wpost cs p t q p' nx' h' t' q' True\<close>
  by (simp add: wprop_winv_def wprop_wpost_def)

definition dpll_wpropagate_contract ::
  \<open>Lit list list \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> bool option list \<Rightarrow> Lit list \<Rightarrow> 64 word \<Rightarrow>
   ('s, 64 word list \<times> 64 word list \<times> 64 word list \<times> bool option list \<times> Lit list \<times> 64 word \<times> bool \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>dpll_wpropagate_contract cs p nx h a t q \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
          \<langle>dpll_wpre cs (length a) p nx h \<and> length a + 2 \<le> urust_fuel \<and> tr_ok (length a) a t \<and>
           unat q \<le> length t \<and> wl_ok cs p nx h\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>case r of (p1, nx1, h1, a1, t1, q1, b, _) \<Rightarrow>
             dpll_wpre cs (length a) p1 nx1 h1 \<and> length a1 = length a \<and> wprop_post cs t (length a) a1 t1 b \<and>
             unat q1 \<le> length t1 \<and> wprop_wpost cs p t (unat q) p1 nx1 h1 t1 (unat q1) b\<rangle>)\<close>

lemma dpll_wpropagate_spec [crush_specs]:
  shows \<open>\<Gamma>; wpropagate cs p nx h a t q \<Turnstile>\<^sub>F dpll_wpropagate_contract cs p nx h a t q\<close>
  apply (crush_boot f: wpropagate_def contract: dpll_wpropagate_contract_def)
  apply (crush_base inline: len_def simp add: dpll_wpre_def)
  subgoal for p_ref nx_ref h_ref a_ref t_ref q_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gp p' gn nx' gh h' ga a' gt t' gq q'.
               p_ref \<mapsto>\<langle>\<top>\<rangle> gp\<down>p' \<star> nx_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>nx' \<star> h_ref \<mapsto>\<langle>\<top>\<rangle> gh\<down>h' \<star>
               a_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>a' \<star> t_ref \<mapsto>\<langle>\<top>\<rangle> gt\<down>t' \<star> q_ref \<mapsto>\<langle>\<top>\<rangle> gq\<down>q' \<star>
               can_alloc_reference \<star>
               \<langle>dpll_wpre cs (length a) p' nx' h' \<and> length h' = length h \<and>
                length a' = length a \<and> tr_ok (length a) a' t' \<and> wprop_inv cs t (length a) a' t' \<and>
                (\<forall>j < length t'. 2 * unat (Lit_var (t' ! j)) < 18446744073709551615 \<and>
                   unat (Lit_var (t' ! j)) < length a) \<and>
                length t' \<le> length a \<and> unat q' \<le> length t' \<and>
                (unat q' < length t' \<longrightarrow> length a - unat q' \<le> k) \<and>
                wprop_winv cs p t (unat q) p' nx' h' t' (unat q')\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gp p' gn nx' gh h' ga a' gt t' gq q'.
               p_ref \<mapsto>\<langle>\<top>\<rangle> gp\<down>p' \<star> nx_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>nx' \<star> h_ref \<mapsto>\<langle>\<top>\<rangle> gh\<down>h' \<star>
               a_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>a' \<star> t_ref \<mapsto>\<langle>\<top>\<rangle> gt\<down>t' \<star> q_ref \<mapsto>\<langle>\<top>\<rangle> gq\<down>q' \<star>
               can_alloc_reference \<star>
               \<langle>dpll_wpre cs (length a) p' nx' h' \<and> length h' = length h \<and>
                length a' = length a \<and> tr_ok (length a) a' t' \<and> wprop_inv cs t (length a) a' t' \<and>
                (\<forall>j < length t'. 2 * unat (Lit_var (t' ! j)) < 18446744073709551615 \<and>
                   unat (Lit_var (t' ! j)) < length a) \<and>
                length t' \<le> length a \<and> unat q' < length t' \<and> length a - unat q' \<le> Suc k \<and>
                wprop_winv cs p t (unat q) p' nx' h' t' (unat q')\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star>
          \<langle>case r of (p1, nx1, h1, a1, t1, q1, b, _) \<Rightarrow>
             dpll_wpre cs (length a) p1 nx1 h1 \<and> length a1 = length a \<and> wprop_post cs t (length a) a1 t1 b \<and>
             unat q1 \<le> length t1 \<and> wprop_wpost cs p t (unat q) p1 nx1 h1 t1 (unat q1) b\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base wp split: prod.splits tnil.splits inline: lit_neg_def
        simp add: word_less_nat_alt unat_of_nat_eq dpll_unat_Suc Suc2_lt)
    apply (all \<open>(frule (1) wprop_step)?\<close>)
    apply (all \<open>(frule q_suc2, assumption, assumption)?\<close>)
    apply (all \<open>(rule wx_ex, assumption, (simp add: lidx_def lneg_def; fail))?\<close>)
    apply (all \<open>(frule wpw_step, assumption, assumption, (simp add: lidx_def lneg_def; fail), assumption,
        assumption)?\<close>)
    apply (all \<open>(frule (2) wpw_exit)?\<close>)
    apply (auto simp add: dpll_wpre_def wprop_post_def unat_of_nat_eq
        intro: tb_var tb_dbl tr_ok_length wprop_refl wprop_winv_refl winv_wl wpw_exit')
    done
  done

text \<open>The steps of the search loop of \<^verbatim>\<open>dpll\<close>, now with propagation over the watches.\<close>

lemma dpll_init:
  assumes \<open>dpll_wf N cs\<close> \<open>tpass_m cs (replicate N None) [] = (a0, t0, b)\<close>
  shows \<open>(b \<longrightarrow> dstate cs N a0 t0 [] \<and> length a0 = N \<and> tr_ok N a0 t0) \<and> (\<not> b \<longrightarrow> \<not> (\<exists>\<sigma>. cnf_sem \<sigma> cs))\<close>
proof -
  note P = dpll_tpass[OF assms(1) subset_refl tr_ok_init assms(2)]
  have D: \<open>dstate cs N a0 t0 []\<close> using P by (auto simp: dstate_def)
  have \<open>\<not> b \<longrightarrow> \<not> (\<exists>\<sigma>. cnf_sem \<sigma> cs)\<close> using dstate_unsat[OF D] P by blast
  then show ?thesis using D P by (auto simp: tr_ok_def)
qed

lemma dpll_w_facts:
  assumes \<open>dstate cs N r ra L\<close> \<open>wprop_post cs ra (length r) a1 t1 b\<close>
  shows \<open>length r = N \<and> length a1 = N \<and> tr_ok N a1 t1 \<and> dstate cs N a1 t1 L \<and>
         meas N (length ra) L \<le> meas N (length t1) L \<and> length ra \<le> length t1 \<and>
         (\<not> b \<longrightarrow> (\<forall>\<sigma>. agrees a1 \<sigma> \<longrightarrow> \<not> cnf_sem \<sigma> cs))\<close>
proof -
  have r: \<open>length r = N\<close> using dstate_tr[OF assms(1)] by simp
  have P: \<open>tr_ok N a1 t1\<close> \<open>\<exists>e. t1 = ra @ e\<close> \<open>\<forall>j. length ra \<le> j \<and> j < length t1 \<longrightarrow> tr_imp cs t1 j\<close>
    \<open>\<not> b \<longrightarrow> (\<forall>\<sigma>. agrees a1 \<sigma> \<longrightarrow> \<not> cnf_sem \<sigma> cs)\<close>
    using assms(2) r by (simp_all add: wprop_post_def wprop_inv_def)
  note D = dstate_prop[OF assms(1) P(1-3)]
  show ?thesis using r P D by (auto simp: tr_ok_def)
qed

lemma dpll_s_decide:
  assumes \<open>dstate cs N a1 t1 (map unat lim)\<close> \<open>3 ^ N - meas N (length t1) (map unat lim) < Suc k\<close>
    \<open>unat v < length a1\<close> \<open>a1 ! unat v = None\<close> \<open>N < 2 ^ 64\<close>
  shows \<open>3 ^ N - meas N (Suc (length t1)) (map unat lim @ [unat (word64_of_nat (length t1))]) < k \<and>
         dstate cs N (a1[unat v := Some True]) (t1 @ [make_Lit v False])
           (map unat lim @ [unat (word64_of_nat (length t1))])\<close>
proof -
  have T: \<open>tr_ok N a1 t1\<close> \<open>length a1 = N\<close> \<open>length t1 \<le> N\<close> using dstate_tr[OF assms(1)] by simp_all
  have u: \<open>unat (word64_of_nat (length t1)) = length t1\<close>
    using T assms(5) by (simp add: unat_of_nat_eq)
  have D: \<open>dstate cs N (a1[unat v := Some True]) (t1 @ [make_Lit v False]) (map unat lim @ [length t1]) \<and>
       meas N (length t1) (map unat lim) < meas N (length (t1 @ [make_Lit v False])) (map unat lim @ [length t1])\<close>
    by (rule dstate_decide) (use T assms(1,3,4) in auto)
  have l: \<open>length (t1 @ [make_Lit v False]) \<le> N\<close>
    using D unfolding dstate_def by (blast dest: tr_ok_length)
  have \<open>meas N (length t1) (map unat lim) < 3 ^ N\<close> using T meas_lt by auto
  moreover have \<open>meas N (Suc (length t1)) (map unat lim @ [length t1]) < 3 ^ N\<close> using l meas_lt by auto
  ultimately have \<open>3 ^ N - meas N (Suc (length t1)) (map unat lim @ [length t1]) < k\<close>
    using D assms(2) by auto
  then show ?thesis using D u by simp
qed

lemma dpll_s_backtrack:
  assumes \<open>dstate cs N rd re (map unat rb)\<close> \<open>3 ^ N - meas N (length re) (map unat rb) < Suc k\<close>
    \<open>\<forall>\<sigma>. agrees rd \<sigma> \<longrightarrow> \<not> cnf_sem \<sigma> cs\<close> \<open>rb \<noteq> []\<close>
    \<open>tr_ok (length rd) a (take (unat (last rb)) re)\<close>
  shows \<open>3 ^ N - meas N (Suc (min (length re) (unat (last rb)))) (map unat (butlast rb)) < k \<and>
         dstate cs N
          (a[unat (Lit_var (re ! unat (last rb))) := Some (Lit_neg (re ! unat (last rb)))])
          (take (unat (last rb)) re @
           [make_Lit (Lit_var (re ! unat (last rb))) (\<not> Lit_neg (re ! unat (last rb)))])
          (map unat (butlast rb)) \<and>
         unat (Lit_var (re ! unat (last rb))) < length a \<and> unat (last rb) < length re\<close>
proof -
  have T: \<open>tr_ok N rd re\<close> \<open>length rd = N\<close> \<open>length re \<le> N\<close> using dstate_tr[OF assms(1)] by simp_all
  let ?p = \<open>unat (last rb)\<close> and ?L = \<open>map unat (butlast rb)\<close>
  have rb: \<open>map unat rb = ?L @ [?p]\<close> using assms(4) by (metis append_butlast_last_id map_append list.simps(8,9))
  have Ds: \<open>dstate cs N rd re (?L @ [?p])\<close> using assms(1) rb by simp
  have a2: \<open>tr_ok N a (take ?p re)\<close> using assms(5) T by simp
  note B = dstate_backtrack[OF Ds assms(3) a2]
  have pl: \<open>?p < length re\<close> using Ds by (simp add: dstate_def)
  have mn: \<open>min (length re) ?p = ?p\<close> using pl by simp
  have D2: \<open>dstate cs N (a[unat (Lit_var (re ! ?p)) := Some (Lit_neg (re ! ?p))]) (take ?p re @ [lneg (re ! ?p)]) ?L\<close>
    and M: \<open>meas N (length re) (?L @ [?p]) < meas N (length (take ?p re @ [lneg (re ! ?p)])) ?L\<close>
    using B by blast+
  have l: \<open>length (take ?p re @ [lneg (re ! ?p)]) \<le> N\<close>
    using D2 unfolding dstate_def by (blast dest: tr_ok_length)
  have \<open>meas N (length re) (map unat rb) < 3 ^ N\<close> using T meas_lt by auto
  moreover have \<open>meas N (Suc ?p) ?L < 3 ^ N\<close> using l pl meas_lt by auto
  ultimately have m: \<open>3 ^ N - meas N (Suc ?p) ?L < k\<close> using M pl rb assms(2) by auto
  have v: \<open>unat (Lit_var (re ! ?p)) < length a\<close>
    using T pl a2 nth_mem[OF pl] by (auto simp: tr_ok_def)
  show ?thesis using m D2 v mn pl by (simp add: lneg_def)
qed

lemma dpll_init':
  assumes \<open>\<forall>c \<in> set cs. lits_lt N c \<and> P c\<close> \<open>tpass_m cs (replicate N None) [] = (a0, t0, b)\<close>
  shows \<open>(b \<longrightarrow> dstate cs N a0 t0 [] \<and> length a0 = N \<and> tr_ok N a0 t0) \<and> (\<not> b \<longrightarrow> \<not> (\<exists>\<sigma>. cnf_sem \<sigma> cs))\<close>
  using assms by (intro dpll_init) (auto simp: dpll_wf_def)

lemma dpll_wbt:
  assumes \<open>dstate cs N r ra (map unat rb)\<close> \<open>3 ^ N - meas N (length ra) (map unat rb) < Suc k\<close>
    \<open>wprop_post cs ra N rd re False\<close> \<open>rb \<noteq> []\<close> \<open>tr_ok N a (take (unat (last rb)) re)\<close>
  shows \<open>3 ^ N - meas N (Suc (min (length re) (unat (last rb)))) (map unat (butlast rb)) < k \<and>
         dstate cs N
          (a[unat (Lit_var (re ! unat (last rb))) := Some (Lit_neg (re ! unat (last rb)))])
          (take (unat (last rb)) re @
           [make_Lit (Lit_var (re ! unat (last rb))) (\<not> Lit_neg (re ! unat (last rb)))])
          (map unat (butlast rb)) \<and>
         unat (Lit_var (re ! unat (last rb))) < length a \<and> unat (last rb) < length re\<close>
proof -
  have r: \<open>length r = N\<close> using dstate_tr[OF assms(1)] by simp
  note F = dpll_w_facts[OF assms(1), of rd re False] assms(3) r
  have m: \<open>3 ^ N - meas N (length re) (map unat rb) < Suc k\<close> using F assms(2) by auto
  show ?thesis by (rule dpll_s_backtrack) (use F m assms(4,5) in auto)
qed

lemma dpll_wdec:
  assumes \<open>dstate cs N r ra (map unat lim)\<close> \<open>3 ^ N - meas N (length ra) (map unat lim) < Suc k\<close>
    \<open>wprop_post cs ra N a1 t1 b\<close> \<open>unat v < N\<close> \<open>a1 ! unat v = None\<close> \<open>N < 9223372036854775808\<close>
  shows \<open>3 ^ N - meas N (Suc (length t1)) (map unat lim @ [unat (word64_of_nat (length t1))]) < k \<and>
         dstate cs N (a1[unat v := Some True]) (t1 @ [make_Lit v False])
           (map unat lim @ [unat (word64_of_nat (length t1))]) \<and>
         tr_ok N (a1[unat v := Some True]) (t1 @ [make_Lit v False]) \<and> length a1 = N\<close>
proof -
  have r: \<open>length r = N\<close> using dstate_tr[OF assms(1)] by simp
  note F = dpll_w_facts[OF assms(1), of a1 t1 b] assms(3) r
  have m: \<open>3 ^ N - meas N (length t1) (map unat lim) < Suc k\<close> using F assms(2) by auto
  have D: \<open>3 ^ N - meas N (Suc (length t1)) (map unat lim @ [unat (word64_of_nat (length t1))]) < k \<and>
         dstate cs N (a1[unat v := Some True]) (t1 @ [make_Lit v False])
           (map unat lim @ [unat (word64_of_nat (length t1))])\<close>
    by (rule dpll_s_decide) (use F m assms(4-6) in auto)
  then show ?thesis using F dstate_tr by blast
qed

lemma dpll_wunsat1:
  assumes \<open>dstate cs N r ra []\<close> \<open>wprop_post cs ra N rd re False\<close> \<open>cnf_sem \<sigma> cs\<close>
  shows False
proof -
  have r: \<open>length r = N\<close> using dstate_tr[OF assms(1)] by simp
  note F = dpll_w_facts[OF assms(1), of rd re False] assms(2) r
  have D: \<open>dstate cs N rd re []\<close> and C: \<open>\<forall>\<sigma>. agrees rd \<sigma> \<longrightarrow> \<not> cnf_sem \<sigma> cs\<close>
    using F by blast+
  show False using dstate_unsat[OF D C] assms(3) by blast
qed

lemma wprop_post_len: \<open>wprop_post cs t n a1 t1 b \<Longrightarrow> length t1 \<le> n \<and> length a1 = n \<and> tr_ok n a1 t1\<close>
  using tr_ok_length by (auto simp: wprop_post_def wprop_inv_def tr_ok_def)

lemma dpll_bt_idx:
  assumes \<open>dstate cs N r ra (map unat rb)\<close> \<open>rb \<noteq> []\<close> \<open>wprop_post cs ra N a1 t1 b\<close>
  shows \<open>unat (last rb) < length t1\<close>
proof -
  have \<open>unat (last rb) < length ra\<close> using assms(1,2) by (auto simp: dstate_def)
  moreover have \<open>length ra \<le> length t1\<close> using assms(3) by (auto simp: wprop_post_def wprop_inv_def)
  ultimately show ?thesis by simp
qed

text \<open>The invariant of the watches after propagation, for the three ways the search goes on.\<close>
lemma wst_after:
  assumes \<open>wstate cs p nx h t q L\<close> \<open>wprop_wpost cs p t q p1 nx1 h1 t1 q1 b\<close> \<open>wprop_post cs t n a1 t1 b\<close>
    \<open>q1 \<le> length t1\<close>
  shows \<open>wl_ok cs p1 nx1 h1 \<and> SP cs t1 \<and> (\<forall>k \<in> set L. k \<le> length t \<and> WP cs p1 t1 k \<and> SP cs (take k t1)) \<and>
         (b \<longrightarrow> wstate cs p1 nx1 h1 t1 q1 L \<and> q1 = length t1)\<close>
proof -
  obtain e where e: \<open>t1 = t @ e\<close> using assms(3) by (auto simp: wprop_post_def wprop_inv_def)
  have P: \<open>wl_ok cs p1 nx1 h1\<close> \<open>q \<le> q1\<close> \<open>\<forall>k \<le> length t. WP cs p t k \<longrightarrow> WP cs p1 t1 k\<close>
    \<open>b \<longrightarrow> q1 = length t1 \<and> (WS cs p t (set (take q t)) \<longrightarrow> WS cs p1 t1 (set t1))\<close>
    using assms(2) by (simp_all add: wprop_wpost_def)
  show ?thesis by (rule wstate_prop[OF assms(1) P(1) e P(2) assms(4) P(3) P(4)])
qed

lemma dpll_wsatW:
  assumes \<open>wstate cs p nx h t (unat q) L\<close> \<open>wprop_wpost cs p t (unat q) p1 nx1 h1 t1 (unat q1) True\<close>
    \<open>wprop_post cs t N a1 t1 True\<close> \<open>unat q1 \<le> length t1\<close> \<open>\<forall>v < M. \<exists>y. a1 ! v = Some y\<close>
    \<open>\<forall>c \<in> set cs. lits_lt N c \<and> P c\<close> \<open>M = N \<or> M = length a1\<close>
  shows \<open>length a1 = N \<and> (\<forall>v < length a1. a1 ! v \<noteq> None) \<and> cnf_sem (sigma_of a1) cs\<close>
proof -
  have W: \<open>wstate cs p1 nx1 h1 t1 (unat q1) L\<close> \<open>unat q1 = length t1\<close> using wst_after[OF assms(1-4)] by blast+
  have T: \<open>tr_ok N a1 t1\<close> \<open>length a1 = N\<close> using wprop_post_len[OF assms(3)] by simp_all
  have tot: \<open>\<forall>v < N. a1 ! v \<noteq> None\<close> using assms(5,7) T(2) by auto
  have wf: \<open>dpll_wf N cs\<close> using assms(6) by (simp add: dpll_wf_def)
  show ?thesis using wstate_total[OF W(1)[unfolded W(2)] T(1) wf tot] T(2) tot by simp
qed

lemma dpll_wdecW:
  assumes \<open>wstate cs p nx h t (unat q) L\<close> \<open>wprop_wpost cs p t (unat q) p1 nx1 h1 t1 (unat q1) True\<close>
    \<open>wprop_post cs t N a1 t1 True\<close> \<open>unat q1 \<le> length t1\<close> \<open>N < 9223372036854775808\<close>
  shows \<open>wstate cs p1 nx1 h1 (t1 @ [l]) (unat q1) (L @ [unat (word64_of_nat (length t1))])\<close>
proof -
  have W: \<open>wstate cs p1 nx1 h1 t1 (unat q1) L\<close> \<open>unat q1 = length t1\<close> using wst_after[OF assms(1-4)] by blast+
  have \<open>length t1 \<le> N\<close> using wprop_post_len[OF assms(3)] by simp
  then have \<open>unat (word64_of_nat (length t1)) = length t1\<close> using assms(5) by (simp add: unat_of_nat_eq)
  then show ?thesis using wstate_decide[OF W(1)[unfolded W(2)]] W(2) by simp
qed

lemma dpll_wbtW:
  assumes \<open>wstate cs p nx h t (unat q) (map unat rb)\<close> \<open>wprop_wpost cs p t (unat q) p1 nx1 h1 t1 (unat q1) b\<close>
    \<open>wprop_post cs t N a1 t1 b\<close> \<open>unat q1 \<le> length t1\<close> \<open>rb \<noteq> []\<close> \<open>dstate cs N' r t (map unat rb)\<close>
  shows \<open>wstate cs p1 nx1 h1 (take (unat (last rb)) t1 @ [d]) (unat (last rb)) (map unat (butlast rb))\<close>
proof -
  have W: \<open>wl_ok cs p1 nx1 h1\<close>
    \<open>\<forall>k \<in> set (map unat rb). k \<le> length t \<and> WP cs p1 t1 k \<and> SP cs (take k t1)\<close>
    using wst_after[OF assms(1-4)] by blast+
  have rb: \<open>map unat rb = map unat (butlast rb) @ [unat (last rb)]\<close> using assms(5)
    by (metis append_butlast_last_id map_append list.simps(8,9))
  have lt: \<open>length t \<le> length t1\<close> using assms(3) by (auto simp: wprop_post_def wprop_inv_def)
  have K: \<open>\<forall>k \<in> set (map unat (butlast rb) @ [unat (last rb)]). k \<le> length t1 \<and> WP cs p1 t1 k \<and> SP cs (take k t1)\<close>
    using W(2) lt rb by (metis le_trans)
  have \<open>sorted_wrt (<) (map unat rb)\<close> using assms(6) by (simp add: dstate_def)
  then have \<open>\<forall>k \<in> set (map unat (butlast rb)). k < unat (last rb)\<close>
    using rb by (metis sorted_wrt_append list.set_intros(1))
  then show ?thesis using wstate_backtrack[OF W(1) K] by simp
qed

lemma dpll_wst_init:
  assumes \<open>wl_ok cs p nx h\<close> \<open>\<forall>c \<in> set cs. lits_lt N c \<and> P c\<close> \<open>tpass_m cs (replicate N None) [] = (a0, t0, True)\<close>
  shows \<open>wstate cs p nx h t0 0 []\<close>
proof -
  have \<open>SP cs t0\<close> by (rule tpass_SP[OF _ tr_ok_init assms(3)]) (use assms(2) in \<open>simp add: dpll_wf_def\<close>)
  then show ?thesis using wstate_init[OF assms(1)] by simp
qed

lemma wstate_wl: \<open>wstate cs p nx h t q L \<Longrightarrow> wl_ok cs p nx h\<close>
  by (simp add: wstate_def)

lemma tr_ok_lenA: \<open>tr_ok n a t \<Longrightarrow> length a = n\<close>
  by (simp add: tr_ok_def)

lemma dpll_cs_ok_wcs:
  \<open>dpll_cs_ok cs n \<Longrightarrow> 2 * n < 2 ^ 64 \<Longrightarrow> wcs_ok cs n urust_fuel\<close>
  unfolding dpll_cs_ok_def wcs_ok_def
  by (fastforce simp: lits_lt_def dest: nth_mem)

definition dpll_top_contract :: \<open>Lit list list \<Rightarrow> 64 word \<Rightarrow> ('s, bool option list option, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>dpll_top_contract cs n \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
          \<langle>dpll_cs_ok cs (unat n) \<and> length cs + 2 \<le> urust_fuel \<and> length cs < 2 ^ 64 \<and>
           unat n + 2 \<le> urust_fuel \<and> 3 ^ unat n < urust_fuel \<and>
           2 * length cs \<le> urust_fuel \<and> 2 * length cs < 2 ^ 64 \<and> 2 * unat n < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>case r of
             None \<Rightarrow> \<not> (\<exists>\<sigma>. cnf_sem \<sigma> cs)
           | Some a' \<Rightarrow> length a' = unat n \<and> (\<forall>v < length a'. a' ! v \<noteq> None) \<and> cnf_sem (sigma_of a') cs\<rangle>)\<close>

lemma dpll_top_spec [crush_specs]:
  shows \<open>\<Gamma>; dpll cs n \<Turnstile>\<^sub>F dpll_top_contract cs n\<close>
  apply (crush_boot f: dpll_def contract: dpll_top_contract_def)
  apply (crush_base split: prod.splits tnil.splits simp add: dpll_cs_ok_def)
  subgoal for p0 nx0 h0 p_ref nx_ref h_ref a0 t0 ok0 a_ref t_ref l_ref q_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gp p gn nx gh h ga a gt t gl lim gq q.
               p_ref \<mapsto>\<langle>\<top>\<rangle> gp\<down>p \<star> nx_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>nx \<star> h_ref \<mapsto>\<langle>\<top>\<rangle> gh\<down>h \<star>
               a_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>a \<star> t_ref \<mapsto>\<langle>\<top>\<rangle> gt\<down>t \<star> l_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>lim \<star>
               q_ref \<mapsto>\<langle>\<top>\<rangle> gq\<down>q \<star> can_alloc_reference \<star>
               \<langle>dstate cs (unat n) a t (map unat lim) \<and> 3 ^ unat n - meas (unat n) (length t) (map unat lim) < k \<and>
                dpll_wpre cs (unat n) p nx h \<and> length a = unat n \<and> tr_ok (unat n) a t \<and> unat q \<le> length t \<and>
                wstate cs p nx h t (unat q) (map unat lim)\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gp p gn nx gh h ga a gt t gl lim gq q.
               p_ref \<mapsto>\<langle>\<top>\<rangle> gp\<down>p \<star> nx_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>nx \<star> h_ref \<mapsto>\<langle>\<top>\<rangle> gh\<down>h \<star>
               a_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>a \<star> t_ref \<mapsto>\<langle>\<top>\<rangle> gt\<down>t \<star> l_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>lim \<star>
               q_ref \<mapsto>\<langle>\<top>\<rangle> gq\<down>q \<star> can_alloc_reference \<star>
               \<langle>dstate cs (unat n) a t (map unat lim) \<and> 3 ^ unat n - meas (unat n) (length t) (map unat lim) < Suc k \<and>
                dpll_wpre cs (unat n) p nx h \<and> length a = unat n \<and> tr_ok (unat n) a t \<and> unat q \<le> length t \<and>
                wstate cs p nx h t (unat q) (map unat lim)\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star>
          \<langle>case r of
             None \<Rightarrow> \<not> (\<exists>\<sigma>. cnf_sem \<sigma> cs)
           | Some a' \<Rightarrow> length a' = unat n \<and> (\<forall>v < length a'. a' ! v \<noteq> None) \<and> cnf_sem (sigma_of a') cs\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base wp split: prod.splits tnil.splits option.splits
        inline: lit_neg_def vec_push_def vec_pop_def simp add: dpll_cs_ok_def)
    apply (all \<open>(rule fst_conv)?\<close>)
    apply (all \<open>(frule (4) dpll_wbt)?\<close>)
    apply (all \<open>(frule (5) dpll_wbtW)?\<close>)
    apply (all \<open>(frule (5) dpll_wdec)?\<close>)
    apply (all \<open>(frule (4) dpll_wdecW)?\<close>)
    apply (all \<open>(frule (5) dpll_wsatW, simp)?\<close>)
    apply (all \<open>(frule (2) dpll_bt_idx)?\<close>)
    apply (all \<open>(frule (1) dpll_init')?\<close>)
    apply (all \<open>(frule wprop_post_len)?\<close>)
    apply (auto simp add: dpll_wpre_def intro: dpll_cs_ok_wcs[unfolded dpll_cs_ok_def] dstate_tr[THEN conjunct1]
        less_imp_diff_less tr_ok_lenA dpll_wst_init wstate_wl dest: dpll_wunsat1)
    done
  using dpll_init' by blast


end

end
