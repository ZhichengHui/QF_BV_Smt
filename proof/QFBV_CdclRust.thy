theory QFBV_CdclRust
  imports QFBV_Dpll
begin

section \<open>CDCL: contracts of the analysis and backjump helpers\<close>

text \<open>Contracts of the helpers of the conflict analysis and the backjump of \<^verbatim>\<open>dpll\<close> against
  their models in \<^verbatim>\<open>QFBV_Cdcl\<close>. Trail positions, reasons and decision positions are \<open>usize\<close>
  vectors here and natural numbers in the models: they are related by \<open>map unat\<close>.\<close>

context QFBV_ctx
begin

subsection \<open>\<^verbatim>\<open>level_of\<close>\<close>

lemma lvl_step:
  \<open>j < length xs \<Longrightarrow> f (xs ! j) \<le> p \<Longrightarrow>
   length (takeWhile (\<lambda>x. x \<le> p) (drop j (map f xs))) = Suc (length (takeWhile (\<lambda>x. x \<le> p) (drop (Suc j) (map f xs))))\<close>
  for f :: \<open>'a \<Rightarrow> nat\<close>
  by (simp add: Cons_nth_drop_Suc[symmetric])

lemma lvl_stop:
  \<open>j \<le> length xs \<Longrightarrow> \<not> f (xs ! j) \<le> p \<Longrightarrow> takeWhile (\<lambda>x. x \<le> p) (drop j (map f xs)) = []\<close>
  for f :: \<open>'a \<Rightarrow> nat\<close>
  by (cases \<open>j < length xs\<close>) (simp_all add: Cons_nth_drop_Suc[symmetric])

definition cdcl_level_of_contract :: \<open>64 word rvec \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>cdcl_level_of_contract lim p \<equiv>
     make_function_contract
       (can_alloc_reference \<star> \<langle>rvec_length lim + 2 \<le> urust_fuel \<and> rvec_length lim < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>unat r = level_of_m (map unat (rvec_elems lim)) (unat p)\<rangle>)\<close>

lemma cdcl_level_of_spec [crush_specs]:
  shows \<open>\<Gamma>; level_of lim p \<Turnstile>\<^sub>F cdcl_level_of_contract lim p\<close>
  apply (crush_boot f: level_of_def contract: cdcl_level_of_contract_def)
  apply (crush_base)
  subgoal for j_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gj j. j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star>
               \<langle>unat j \<le> rvec_length lim \<and> (unat j < rvec_length lim \<and> rvec_elems lim ! unat j \<le> p \<longrightarrow> rvec_length lim - unat j \<le> k) \<and>
                level_of_m (map unat (rvec_elems lim)) (unat p) = unat j + length (takeWhile (\<lambda>x. x \<le> unat p) (drop (unat j) (map unat (rvec_elems lim))))\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gj j. j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star>
               \<langle>unat j < rvec_length lim \<and> rvec_length lim - unat j \<le> Suc k \<and> rvec_elems lim ! unat j \<le> p \<and>
                level_of_m (map unat (rvec_elems lim)) (unat p) = unat j + length (takeWhile (\<lambda>x. x \<le> unat p) (drop (unat j) (map unat (rvec_elems lim))))\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: word_less_nat_alt word_le_nat_alt dpll_unat_Suc)
    apply (auto simp add: unat_of_nat_eq level_of_m_def lvl_step lvl_stop word_le_nat_alt)
    done
  done

subsection \<open>\<^verbatim>\<open>set_pos\<close>\<close>

definition cdcl_set_pos_contract :: \<open>64 word rvec \<Rightarrow> Lit rvec \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word rvec, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>cdcl_set_pos_contract tp t k \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
          \<langle>unat k \<le> rvec_length t \<and> (\<forall>j < rvec_length t. lv (rvec_elems t ! j) < rvec_length tp) \<and>
           rvec_length t + 2 \<le> urust_fuel \<and> vok t \<and> vok tp\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>map unat (rvec_elems r) = set_pos_m (map unat (rvec_elems tp)) (rvec_elems t) (unat k) \<and>
           rvec_length r = rvec_length tp \<and> vok r\<rangle>)\<close>

lemma cdcl_set_pos_spec [crush_specs]:
  shows \<open>\<Gamma>; set_pos tp t k \<Turnstile>\<^sub>F cdcl_set_pos_contract tp t k\<close>
  apply (crush_boot f: set_pos_def contract: cdcl_set_pos_contract_def)
  apply (crush_base)
  subgoal for tp_ref k_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>f. \<Squnion>gp tp' gk j. tp_ref \<mapsto>\<langle>\<top>\<rangle> gp\<down>tp' \<star> k_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>j \<star> can_alloc_reference \<star>
               \<langle>unat k \<le> unat j \<and> unat j \<le> rvec_length t \<and> rvec_length t - unat j \<le> f \<and>
                map unat (rvec_elems tp') = foldl (\<lambda>tp i. tp[lv (rvec_elems t ! i) := i]) (map unat (rvec_elems tp)) [unat k..<unat j] \<and>
                rvec_length tp' = rvec_length tp \<and> vok tp'\<rangle>\<close> and
        INV'=\<open>\<lambda>f. \<Squnion>gp tp' gk j. tp_ref \<mapsto>\<langle>\<top>\<rangle> gp\<down>tp' \<star> k_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>j \<star> can_alloc_reference \<star>
               \<langle>unat k \<le> unat j \<and> unat j < rvec_length t \<and> rvec_length t - unat j \<le> Suc f \<and>
                map unat (rvec_elems tp') = foldl (\<lambda>tp i. tp[lv (rvec_elems t ! i) := i]) (map unat (rvec_elems tp)) [unat k..<unat j] \<and>
                rvec_length tp' = rvec_length tp \<and> vok tp'\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: word_less_nat_alt word_le_nat_alt dpll_unat_Suc dw_focus_modify)
    apply (all \<open>(frule vok_length[of t])?\<close>)
    apply (auto simp add: unat_of_nat_eq set_pos_m_def map_update dpll_unat_Suc)
    done
  done

subsection \<open>\<^verbatim>\<open>second_watch\<close>\<close>

lemma sw_pos_Suc:
  \<open>2 \<le> k \<Longrightarrow> sw_pos tp c (Suc k) = (if tp ! lv (c ! sw_pos tp c k) < tp ! lv (c ! k) then k else sw_pos tp c k)\<close>
  by (simp add: sw_pos_def)

lemma sw_pos_2: \<open>sw_pos tp c 2 = 1\<close>
  by (simp add: sw_pos_def)

definition cdcl_second_watch_contract :: \<open>Lit rvec \<Rightarrow> 64 word rvec \<Rightarrow> ('s, Lit rvec, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>cdcl_second_watch_contract c tp \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
          \<langle>2 \<le> rvec_length c \<and> (\<forall>l \<in> set (rvec_elems c). lv l < rvec_length tp) \<and>
           rvec_length c + 2 \<le> urust_fuel \<and> vok c\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>rvec_elems r = sw_m (map unat (rvec_elems tp)) (rvec_elems c) \<and> rvec_length r = rvec_length c \<and> vok r\<rangle>)\<close>

lemma cdcl_second_watch_spec [crush_specs]:
  shows \<open>\<Gamma>; second_watch c tp \<Turnstile>\<^sub>F cdcl_second_watch_contract c tp\<close>
  apply (crush_boot f: second_watch_def contract: cdcl_second_watch_contract_def)
  apply (crush_base)
  subgoal for c_ref b_ref k_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>f. \<Squnion>gc c' gb b gk k. c_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c' \<star> b_ref \<mapsto>\<langle>\<top>\<rangle> gb\<down>b \<star> k_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>k \<star>
               can_alloc_reference \<star>
               \<langle>c' = c \<and> 2 \<le> unat k \<and> unat k \<le> rvec_length c \<and> rvec_length c - unat k \<le> f \<and>
                unat b = sw_pos (map unat (rvec_elems tp)) (rvec_elems c) (unat k) \<and> unat b < unat k\<rangle>\<close> and
        INV'=\<open>\<lambda>f. \<Squnion>gc c' gb b gk k. c_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c' \<star> b_ref \<mapsto>\<langle>\<top>\<rangle> gb\<down>b \<star> k_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>k \<star>
               can_alloc_reference \<star>
               \<langle>c' = c \<and> 2 \<le> unat k \<and> unat k < rvec_length c \<and> rvec_length c - unat k \<le> Suc f \<and>
                unat b = sw_pos (map unat (rvec_elems tp)) (rvec_elems c) (unat k) \<and> unat b < unat k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: word_less_nat_alt word_le_nat_alt dpll_unat_Suc dw_focus_modify)
    apply (all \<open>(frule vok_length[of c])?\<close>)
    apply (auto simp add: unat_of_nat_eq sw_m_def sw_pos_Suc sw_pos_2 dpll_unat_Suc Let_def)
    done
  done

subsection \<open>\<^verbatim>\<open>add_clause_watched\<close>\<close>

lemma m1_word64: \<open>(- 1 :: 64 word) = 0xFFFFFFFFFFFFFFFF\<close>
  by simp

definition cdcl_add_clause_watched_contract ::
  \<open>Lit rvec rvec \<Rightarrow> 64 word rvec \<Rightarrow> 64 word rvec \<Rightarrow> 64 word rvec \<Rightarrow> Lit rvec \<Rightarrow>
   ('s, Lit rvec rvec \<times> 64 word rvec \<times> 64 word rvec \<times> 64 word rvec \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>cdcl_add_clause_watched_contract cs p nx h c \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
          \<langle>vok cs \<and> vok p \<and> vok nx \<and> vok h \<and> vok c \<and> rvec_length cs < 2 ^ 56 \<and> rvec_length p + 2 < 2 ^ 56 \<and>
           rvec_length nx + 2 < 2 ^ 56 \<and> rvec_length h < 2 ^ 57 \<and>
           (2 \<le> rvec_length c \<longrightarrow> lidx (rvec_elems c ! 0) < rvec_length h \<and> lidx (rvec_elems c ! 1) < rvec_length h)\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>case r of (cs1, p1, nx1, h1, _) \<Rightarrow>
             acw_m (vecs_of cs) (rvec_elems p) (rvec_elems nx) (rvec_elems h) (rvec_elems c) =
               (vecs_of cs1, rvec_elems p1, rvec_elems nx1, rvec_elems h1) \<and>
             vok cs1 \<and> vok p1 \<and> vok nx1 \<and> vok h1 \<and> rvec_length h1 = rvec_length h \<and>
             (allvok cs \<longrightarrow> allvok cs1)\<rangle>)\<close>

lemma cdcl_add_clause_watched_spec [crush_specs]:
  shows \<open>\<Gamma>; add_clause_watched cs p nx h c \<Turnstile>\<^sub>F cdcl_add_clause_watched_contract cs p nx h c\<close>
  apply (crush_boot f: add_clause_watched_def contract: cdcl_add_clause_watched_contract_def)
  apply (crush_base simp add: dw_focus_modify)
  apply (all \<open>(frule vok_length[of c])?\<close>)
  apply (all \<open>(frule vok_length[of nx])?\<close>)
  apply (auto simp add: acw_m_def Let_def lidx_def word_le_nat_alt unat_of_nat_eq vecs_of_def nth_append dpll_unat_Suc m1_word64)
  apply (all \<open>(simp add: add.commute; fail)?\<close>)
  done

subsection \<open>\<^verbatim>\<open>analyze_clause\<close>\<close>

text \<open>Every literal that \<^verbatim>\<open>analyze_clause\<close> counts or learns marks a variable that was not marked:
  the count, the number of learned literals and the number of unmarked variables have a constant
  sum, which bounds the count and the learned clause.\<close>
lemma cl_upd_True:
  \<open>i < length xs \<Longrightarrow> \<not> xs ! i \<Longrightarrow> Suc (count_list (xs[i := True]) False) = count_list xs False\<close>
proof (induction xs arbitrary: i)
  case (Cons x xs)
  then show ?case by (cases i) auto
qed simp

lemma cl_upd_sum:
  assumes \<open>\<forall>j < length c. lv (c ! j) < length sn \<and> Q j\<close> \<open>r < length c\<close> \<open>length ra = length sn\<close>
    \<open>\<not> ra ! lv (c ! r)\<close> \<open>x + count_list ra False = y\<close>
  shows \<open>Suc (x + count_list (ra[lv (c ! r) := True]) False) = y\<close>
  using cl_upd_True[of \<open>lv (c ! r)\<close> ra] assms by auto

lemma ac_nil: \<open>ac_m tp st [] s = s\<close>
  by (simp add: ac_m_def)

lemma ac_drop:
  \<open>k < length c \<Longrightarrow> ac_m tp st (drop k c) s = ac_m tp st (drop (Suc k) c) (ac_step tp st s (c ! k))\<close>
  by (simp add: ac_m_def Cons_nth_drop_Suc[symmetric])

definition cdcl_analyze_clause_contract ::
  \<open>Lit rvec \<Rightarrow> 64 word rvec \<Rightarrow> 64 word \<Rightarrow> bool rvec \<Rightarrow> Lit rvec \<Rightarrow> 64 word \<Rightarrow>
   ('s, bool rvec \<times> Lit rvec \<times> 64 word \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>cdcl_analyze_clause_contract c tp st sn ln k \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
          \<langle>(\<forall>j < rvec_length c. lv (rvec_elems c ! j) < rvec_length sn \<and> lv (rvec_elems c ! j) < rvec_length tp) \<and>
           rvec_length c + 2 \<le> urust_fuel \<and> vok c \<and> vok ln \<and>
           rvec_elems ln \<noteq> [] \<and> (\<forall>l \<in> set (rvec_elems ln). lv l < rvec_length sn) \<and>
           unat k + rvec_length ln + count_list (rvec_elems sn) False < 2 ^ 56\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>case r of (sn1, ln1, k1, _) \<Rightarrow>
             ac_m (map unat (rvec_elems tp)) (unat st) (rvec_elems c) (rvec_elems sn, rvec_elems ln, unat k) =
               (rvec_elems sn1, rvec_elems ln1, unat k1) \<and> vok ln1 \<and>
             unat k1 + rvec_length ln1 + count_list (rvec_elems sn1) False = unat k + rvec_length ln + count_list (rvec_elems sn) False \<and>
             rvec_length sn1 = rvec_length sn \<and> rvec_elems ln1 \<noteq> [] \<and> (\<forall>l \<in> set (rvec_elems ln1). lv l < rvec_length sn) \<and>
             rvec_elems ln1 ! 0 = rvec_elems ln ! 0\<rangle>)\<close>

lemma cdcl_analyze_clause_spec [crush_specs]:
  shows \<open>\<Gamma>; analyze_clause c tp st sn ln k \<Turnstile>\<^sub>F cdcl_analyze_clause_contract c tp st sn ln k\<close>
  apply (crush_boot f: analyze_clause_def contract: cdcl_analyze_clause_contract_def)
  apply (crush_base)
  subgoal for s_ref l_ref c_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>f. \<Squnion>gs sn' gl ln' gc k' gi i. s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>sn' \<star> l_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>ln' \<star> c_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>k' \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
               can_alloc_reference \<star>
               \<langle>unat i \<le> rvec_length c \<and> rvec_length c - unat i \<le> f \<and> rvec_length sn' = rvec_length sn \<and> vok ln' \<and>
                ac_m (map unat (rvec_elems tp)) (unat st) (rvec_elems c) (rvec_elems sn, rvec_elems ln, unat k) =
                  ac_m (map unat (rvec_elems tp)) (unat st) (drop (unat i) (rvec_elems c)) (rvec_elems sn', rvec_elems ln', unat k') \<and>
                unat k' + rvec_length ln' + count_list (rvec_elems sn') False = unat k + rvec_length ln + count_list (rvec_elems sn) False \<and>
                rvec_elems ln' \<noteq> [] \<and> (\<forall>l \<in> set (rvec_elems ln'). lv l < rvec_length sn) \<and> rvec_elems ln' ! 0 = rvec_elems ln ! 0\<rangle>\<close> and
        INV'=\<open>\<lambda>f. \<Squnion>gs sn' gl ln' gc k' gi i. s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>sn' \<star> l_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>ln' \<star> c_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>k' \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
               can_alloc_reference \<star>
               \<langle>unat i < rvec_length c \<and> rvec_length c - unat i \<le> Suc f \<and> rvec_length sn' = rvec_length sn \<and> vok ln' \<and>
                ac_m (map unat (rvec_elems tp)) (unat st) (rvec_elems c) (rvec_elems sn, rvec_elems ln, unat k) =
                  ac_m (map unat (rvec_elems tp)) (unat st) (drop (unat i) (rvec_elems c)) (rvec_elems sn', rvec_elems ln', unat k') \<and>
                unat k' + rvec_length ln' + count_list (rvec_elems sn') False = unat k + rvec_length ln + count_list (rvec_elems sn) False \<and>
                rvec_elems ln' \<noteq> [] \<and> (\<forall>l \<in> set (rvec_elems ln'). lv l < rvec_length sn) \<and> rvec_elems ln' ! 0 = rvec_elems ln ! 0\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: word_less_nat_alt word_le_nat_alt dpll_unat_Suc dw_focus_modify)
    apply (all \<open>(frule vok_length[of c])?\<close>)
    apply (auto simp add: unat_of_nat_eq ac_step_def dpll_unat_Suc push_not_None word_le_nat_alt ac_drop cl_upd_True ac_nil nth_append)
    apply (all \<open>(rule cl_upd_sum; assumption)\<close>)
    done
  done

subsection \<open>\<^verbatim>\<open>clear_lits\<close>, \<^verbatim>\<open>clear_trail\<close>\<close>

definition cdcl_clear_lits_contract :: \<open>bool rvec \<Rightarrow> Lit rvec \<Rightarrow> ('s, bool rvec, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>cdcl_clear_lits_contract sn ls \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
          \<langle>(\<forall>l \<in> set (rvec_elems ls). lv l < rvec_length sn) \<and> rvec_length ls + 2 \<le> urust_fuel \<and> vok ls\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>rvec_elems r = foldl (\<lambda>s l. s[lv l := False]) (rvec_elems sn) (rvec_elems ls) \<and> rvec_length r = rvec_length sn\<rangle>)\<close>

lemma cdcl_clear_lits_spec [crush_specs]:
  shows \<open>\<Gamma>; clear_lits sn ls \<Turnstile>\<^sub>F cdcl_clear_lits_contract sn ls\<close>
  apply (crush_boot f: clear_lits_def contract: cdcl_clear_lits_contract_def)
  apply (crush_base)
  subgoal for s_ref k_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>f. \<Squnion>gs sn' gk k. s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>sn' \<star> k_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>k \<star> can_alloc_reference \<star>
               \<langle>unat k \<le> rvec_length ls \<and> rvec_length ls - unat k \<le> f \<and> rvec_length sn' = rvec_length sn \<and>
                rvec_elems sn' = foldl (\<lambda>s l. s[lv l := False]) (rvec_elems sn) (take (unat k) (rvec_elems ls))\<rangle>\<close> and
        INV'=\<open>\<lambda>f. \<Squnion>gs sn' gk k. s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>sn' \<star> k_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>k \<star> can_alloc_reference \<star>
               \<langle>unat k < rvec_length ls \<and> rvec_length ls - unat k \<le> Suc f \<and> rvec_length sn' = rvec_length sn \<and>
                rvec_elems sn' = foldl (\<lambda>s l. s[lv l := False]) (rvec_elems sn) (take (unat k) (rvec_elems ls))\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: word_less_nat_alt word_le_nat_alt dpll_unat_Suc dw_focus_modify)
    apply (all \<open>(frule vok_length[of ls])?\<close>)
    apply (auto simp add: unat_of_nat_eq dpll_unat_Suc take_Suc_conv_app_nth)
    done
  done

definition cdcl_clear_trail_contract :: \<open>bool rvec \<Rightarrow> Lit rvec \<Rightarrow> 64 word \<Rightarrow> ('s, bool rvec, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>cdcl_clear_trail_contract sn t st \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
          \<langle>(\<forall>j < rvec_length t. lv (rvec_elems t ! j) < rvec_length sn) \<and> rvec_length t + 2 \<le> urust_fuel \<and> vok t\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>rvec_elems r = foldl (\<lambda>s j. s[lv (rvec_elems t ! j) := False]) (rvec_elems sn) [unat st..<rvec_length t] \<and>
           rvec_length r = rvec_length sn\<rangle>)\<close>

lemma cdcl_clear_trail_spec [crush_specs]:
  shows \<open>\<Gamma>; clear_trail sn t st \<Turnstile>\<^sub>F cdcl_clear_trail_contract sn t st\<close>
  apply (crush_boot f: clear_trail_def contract: cdcl_clear_trail_contract_def)
  apply (crush_base)
  subgoal for s_ref j_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>f. \<Squnion>gs sn' gj j. s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>sn' \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star>
               \<langle>unat st \<le> unat j \<and> (unat j \<le> rvec_length t \<or> unat j = unat st) \<and>
                (unat j < rvec_length t \<longrightarrow> rvec_length t - unat j \<le> f) \<and> rvec_length sn' = rvec_length sn \<and>
                rvec_elems sn' = foldl (\<lambda>s j. s[lv (rvec_elems t ! j) := False]) (rvec_elems sn) [unat st..<unat j]\<rangle>\<close> and
        INV'=\<open>\<lambda>f. \<Squnion>gs sn' gj j. s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>sn' \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star>
               \<langle>unat st \<le> unat j \<and> unat j < rvec_length t \<and> rvec_length t - unat j \<le> Suc f \<and> rvec_length sn' = rvec_length sn \<and>
                rvec_elems sn' = foldl (\<lambda>s j. s[lv (rvec_elems t ! j) := False]) (rvec_elems sn) [unat st..<unat j]\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: word_less_nat_alt word_le_nat_alt dpll_unat_Suc dw_focus_modify)
    apply (all \<open>(frule vok_length[of t])?\<close>)
    apply (auto simp add: unat_of_nat_eq dpll_unat_Suc)
    done
  done

subsection \<open>\<^verbatim>\<open>analyze_loop\<close>\<close>

text \<open>The loop of \<^const>\<open>analyze_m\<close>, entered with the count \<open>k\<close> (it does not run if \<open>k = 0\<close>).\<close>
definition ana_m ::
  \<open>Lit list list \<Rightarrow> Lit list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool list \<Rightarrow> Lit list \<Rightarrow> nat \<Rightarrow>
   bool list \<times> Lit list \<times> nat \<times> nat \<times> bool\<close> where
  \<open>ana_m cs t rs tp st sn ln k \<equiv>
     if 0 < k then ana_loop cs t rs tp st (sn, ln, k) (length t) else (sn, ln, k, length t, False)\<close>

lemma analyze_m_ana:
  \<open>analyze_m cs t rs tp st sn cf =
     (case ac_m tp st (cs ! cf) (sn, [make_Lit 0 False], 0) of (s1, l1, k1) \<Rightarrow>
       (case ana_m cs t rs tp st s1 l1 k1 of (s2, l2, k2, i2, ok2) \<Rightarrow> (l2, clr_m l2 t st s2, k2 = 1 \<and> \<not> ok2)))\<close>
  by (simp add: analyze_m_def ana_m_def)

text \<open>\<^const>\<open>ana_loop\<close> behind a definition: its equations unfold without end on a symbolic position.\<close>
definition ana_at ::
  \<open>Lit list list \<Rightarrow> Lit list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool list \<times> Lit list \<times> nat \<Rightarrow> nat \<Rightarrow>
   bool list \<times> Lit list \<times> nat \<times> nat \<times> bool\<close> where
  \<open>ana_at \<equiv> ana_loop\<close>

lemma ana_m_at: \<open>ana_m cs t rs tp st sn ln k =
    (if 0 < k then ana_at cs t rs tp st (sn, ln, k) (length t) else (sn, ln, k, length t, False))\<close>
  by (simp add: ana_m_def ana_at_def)

lemma ana_step:
  \<open>st < i \<Longrightarrow> ana_at cs t rs tp st (sn, ln, k) i =
     (if sn ! lv (t ! (i - 1)) then
        (if k \<le> 1 then (sn, ln[0 := lneg (t ! (i - 1))], k, i - 1, False)
         else ana_at cs t rs tp st (ac_m tp st (cs ! (rs ! (i - 1))) (sn, ln, k - 1)) (i - 1))
      else ana_at cs t rs tp st (sn, ln, k) (i - 1))\<close>
  by (simp add: ana_at_def)

lemma ana_stop: \<open>\<not> st < i \<Longrightarrow> ana_at cs t rs tp st (sn, ln, k) i = (sn, ln, k, i, True)\<close>
  by (simp add: ana_at_def)

lemma ac_m_ext:
  \<open>ac_m tp st c (sn, ln, k) = (sn', ln', k') \<Longrightarrow> (\<exists>e. ln' = ln @ e \<and> set e \<subseteq> set c) \<and> length sn' = length sn\<close>
proof (induction c arbitrary: sn ln k)
  case Nil
  then show ?case by (simp add: ac_m_def)
next
  case (Cons l c)
  obtain s1 l1 k1 where s1: \<open>ac_step tp st (sn, ln, k) l = (s1, l1, k1)\<close> by (cases \<open>ac_step tp st (sn, ln, k) l\<close>) auto
  have r: \<open>ac_m tp st c (s1, l1, k1) = (sn', ln', k')\<close> using Cons.prems s1 by (simp add: ac_m_def)
  note IH = Cons.IH[OF r]
  have \<open>(l1 = ln \<or> l1 = ln @ [l]) \<and> length s1 = length sn\<close> using s1 by (auto simp: ac_step_def split: if_splits)
  then show ?case using IH by fastforce
qed

text \<open>The facts about the learned literals that the loop keeps.\<close>
lemma ac_lits:
  assumes \<open>ac_m tp st c (sn, ln, k) = (sn', ln', k')\<close> \<open>\<forall>l \<in> set ln. lv l < N\<close> \<open>\<forall>j < length c. lv (c ! j) < N\<close> \<open>ln \<noteq> []\<close>
  shows \<open>(\<forall>l \<in> set ln'. lv l < N) \<and> ln' \<noteq> [] \<and> length sn' = length sn\<close>
proof -
  obtain e where e: \<open>ln' = ln @ e\<close> \<open>set e \<subseteq> set c\<close> \<open>length sn' = length sn\<close> using ac_m_ext[OF assms(1)] by blast
  have \<open>\<forall>l \<in> set c. lv l < N\<close> using assms(3) by (auto simp: in_set_conv_nth)
  then show ?thesis using e assms(2,4) by auto
qed

lemma unat_dec_lt: \<open>unat a < unat r \<Longrightarrow> unat (r - 1) = unat r - 1\<close> for a r :: \<open>64 word\<close>
  by (metis less_nat_zero_code unat_eq_zero unat_minus_one)

lemma unat_dec_gt1: \<open>\<not> unat r \<le> Suc 0 \<Longrightarrow> unat (r - 1) = unat r - 1\<close> for r :: \<open>64 word\<close>
  by (metis le0 unat_eq_zero unat_minus_one Suc_leI le_SucI)

definition cdcl_analyze_loop_contract ::
  \<open>Lit rvec rvec \<Rightarrow> Lit rvec \<Rightarrow> 64 word rvec \<Rightarrow> 64 word rvec \<Rightarrow> 64 word \<Rightarrow> bool rvec \<Rightarrow> Lit rvec \<Rightarrow> 64 word \<Rightarrow>
   ('s, bool rvec \<times> Lit rvec \<times> 64 word \<times> bool \<times> Lit \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>cdcl_analyze_loop_contract cs t rs tp st sn ln k \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
          \<langle>(\<forall>i < rvec_length cs. \<forall>j < rvec_length (rvec_elems cs ! i).
              lv (rvec_elems (rvec_elems cs ! i) ! j) < rvec_length sn \<and> lv (rvec_elems (rvec_elems cs ! i) ! j) < rvec_length tp) \<and>
           (\<forall>i < rvec_length cs. rvec_length (rvec_elems cs ! i) + 2 \<le> urust_fuel) \<and> allvok cs \<and>
           rvec_length rs = rvec_length t \<and> (\<forall>j < rvec_length t. unat (rvec_elems rs ! j) < rvec_length cs) \<and>
           (\<forall>j < rvec_length t. lv (rvec_elems t ! j) < rvec_length sn) \<and> rvec_length t + 2 \<le> urust_fuel \<and> vok t \<and>
           vok ln \<and> rvec_elems ln \<noteq> [] \<and> (\<forall>l \<in> set (rvec_elems ln). lv l < rvec_length sn) \<and>
           unat k + rvec_length ln + count_list (rvec_elems sn) False < 2 ^ 56\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>case r of (sn2, ln2, k2, ok2, u2, _) \<Rightarrow>
             (case ana_m (vecs_of cs) (rvec_elems t) (map unat (rvec_elems rs)) (map unat (rvec_elems tp)) (unat st)
                     (rvec_elems sn) (rvec_elems ln) (unat k) of
                (s', l', k', i', ok') \<Rightarrow> rvec_elems sn2 = s' \<and> (rvec_elems ln2)[0 := u2] = l' \<and> unat k2 = k' \<and> ok2 = ok') \<and>
             vok ln2 \<and> rvec_length sn2 = rvec_length sn \<and> rvec_elems ln2 \<noteq> [] \<and>
             (\<forall>l \<in> set (rvec_elems ln2). lv l < rvec_length sn) \<and> lv u2 < rvec_length sn \<and>
             unat k2 + rvec_length ln2 + count_list (rvec_elems sn2) False \<le> unat k + rvec_length ln + count_list (rvec_elems sn) False\<rangle>)\<close>

lemma cdcl_analyze_loop_spec [crush_specs]:
  shows \<open>\<Gamma>; analyze_loop cs t rs tp st sn ln k \<Turnstile>\<^sub>F cdcl_analyze_loop_contract cs t rs tp st sn ln k\<close>
  apply (crush_boot f: analyze_loop_def contract: cdcl_analyze_loop_contract_def)
  apply (crush_base)
  subgoal for s_ref l_ref c_ref u_ref i_ref o_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>f. \<Squnion>gs sn' gl ln' gc k' gu u gi i go ok. s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>sn' \<star> l_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>ln' \<star> c_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>k' \<star>
               u_ref \<mapsto>\<langle>\<top>\<rangle> gu\<down>u \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> o_ref \<mapsto>\<langle>\<top>\<rangle> go\<down>ok \<star> can_alloc_reference \<star>
               \<langle>unat i \<le> rvec_length t \<and> (ok \<and> unat st < unat i \<longrightarrow> unat i - unat st \<le> f) \<and>
                rvec_length sn' = rvec_length sn \<and> vok ln' \<and> rvec_elems ln' \<noteq> [] \<and> (\<forall>l \<in> set (rvec_elems ln'). lv l < rvec_length sn) \<and>
                unat k' + rvec_length ln' + count_list (rvec_elems sn') False \<le> unat k + rvec_length ln + count_list (rvec_elems sn) False \<and>
                lv u < rvec_length sn \<and> (ok \<longrightarrow> 0 < unat k) \<and> (ok \<longrightarrow> u = rvec_elems ln' ! 0) \<and> (ok \<longrightarrow> ana_m (vecs_of cs) (rvec_elems t) (map unat (rvec_elems rs)) (map unat (rvec_elems tp)) (unat st) (rvec_elems sn) (rvec_elems ln) (unat k) = ana_at (vecs_of cs) (rvec_elems t) (map unat (rvec_elems rs)) (map unat (rvec_elems tp)) (unat st) (rvec_elems sn', rvec_elems ln', unat k') (unat i)) \<and>
                (\<not> ok \<longrightarrow> ana_m (vecs_of cs) (rvec_elems t) (map unat (rvec_elems rs)) (map unat (rvec_elems tp)) (unat st) (rvec_elems sn) (rvec_elems ln) (unat k) = (rvec_elems sn', (rvec_elems ln')[0 := u], unat k', unat i, False))\<rangle>\<close> and
        INV'=\<open>\<lambda>f. \<Squnion>gs sn' gl ln' gc k' gu u gi i go ok. s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>sn' \<star> l_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>ln' \<star> c_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>k' \<star>
               u_ref \<mapsto>\<langle>\<top>\<rangle> gu\<down>u \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> o_ref \<mapsto>\<langle>\<top>\<rangle> go\<down>ok \<star> can_alloc_reference \<star>
               \<langle>unat i \<le> rvec_length t \<and> ok \<and> unat st < unat i \<and> unat i - unat st \<le> Suc f \<and>
                rvec_length sn' = rvec_length sn \<and> vok ln' \<and> rvec_elems ln' \<noteq> [] \<and> (\<forall>l \<in> set (rvec_elems ln'). lv l < rvec_length sn) \<and>
                unat k' + rvec_length ln' + count_list (rvec_elems sn') False \<le> unat k + rvec_length ln + count_list (rvec_elems sn) False \<and>
                lv u < rvec_length sn \<and> (ok \<longrightarrow> 0 < unat k) \<and> (ok \<longrightarrow> u = rvec_elems ln' ! 0) \<and> (ok \<longrightarrow> ana_m (vecs_of cs) (rvec_elems t) (map unat (rvec_elems rs)) (map unat (rvec_elems tp)) (unat st) (rvec_elems sn) (rvec_elems ln) (unat k) = ana_at (vecs_of cs) (rvec_elems t) (map unat (rvec_elems rs)) (map unat (rvec_elems tp)) (unat st) (rvec_elems sn', rvec_elems ln', unat k') (unat i)) \<and>
                (\<not> ok \<longrightarrow> ana_m (vecs_of cs) (rvec_elems t) (map unat (rvec_elems rs)) (map unat (rvec_elems tp)) (unat st) (rvec_elems sn) (rvec_elems ln) (unat k) = (rvec_elems sn', (rvec_elems ln')[0 := u], unat k', unat i, False))\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: word_less_nat_alt word_le_nat_alt dw_focus_modify inline: lit_neg_def)
    apply (all \<open>(frule vok_length[of t])?\<close>)
    apply (all \<open>(frule unat_dec_lt)?\<close>)
    apply (all \<open>(frule unat_dec_gt1)?\<close>)
    apply (all \<open>(auto simp add: ana_step ana_stop ana_m_at lneg_def vecs_of_def unat_of_nat_eq allvok_nth dest!: set_update_subset_insert[THEN subsetD]; fail)?\<close>)
    done
  done

subsection \<open>\<^verbatim>\<open>analyze\<close>\<close>

lemma unat_one_iff: \<open>(unat x = Suc 0) = (x = 1)\<close> for x :: \<open>64 word\<close>
  by (metis One_nat_def unat_1 word_unat.Rep_inverse)

lemma count_lt55: \<open>length xs < 2 ^ 55 \<Longrightarrow> Suc (count_list xs False) < 2 ^ 56\<close>
  using count_le_length[of xs False] by simp

definition cdcl_set_first_contract :: \<open>Lit rvec \<Rightarrow> Lit \<Rightarrow> ('s, Lit rvec, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>cdcl_set_first_contract c l \<equiv>
     make_function_contract
       (can_alloc_reference \<star> \<langle>rvec_elems c \<noteq> [] \<and> vok c\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>rvec_elems r = (rvec_elems c)[0 := l] \<and> vok r\<rangle>)\<close>

lemma cdcl_set_first_spec [crush_specs]:
  shows \<open>\<Gamma>; set_first c l \<Turnstile>\<^sub>F cdcl_set_first_contract c l\<close>
  apply (crush_boot f: set_first_def contract: cdcl_set_first_contract_def)
  apply (crush_base simp add: dw_focus_modify)
  done

definition cdcl_analyze_contract ::
  \<open>Lit rvec rvec \<Rightarrow> Lit rvec \<Rightarrow> 64 word rvec \<Rightarrow> 64 word rvec \<Rightarrow> 64 word \<Rightarrow> bool rvec \<Rightarrow> 64 word \<Rightarrow>
   ('s, Lit rvec \<times> bool rvec \<times> bool \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>cdcl_analyze_contract cs t rs tp st sn cf \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
          \<langle>(\<forall>i < rvec_length cs. \<forall>j < rvec_length (rvec_elems cs ! i).
              lv (rvec_elems (rvec_elems cs ! i) ! j) < rvec_length sn \<and> lv (rvec_elems (rvec_elems cs ! i) ! j) < rvec_length tp) \<and>
           (\<forall>i < rvec_length cs. rvec_length (rvec_elems cs ! i) + 2 \<le> urust_fuel) \<and> allvok cs \<and> unat cf < rvec_length cs \<and>
           rvec_length rs = rvec_length t \<and> (\<forall>j < rvec_length t. unat (rvec_elems rs ! j) < rvec_length cs) \<and>
           (\<forall>j < rvec_length t. lv (rvec_elems t ! j) < rvec_length sn) \<and> rvec_length t + 2 \<le> urust_fuel \<and> vok t \<and>
           0 < rvec_length sn \<and> rvec_length sn < 2 ^ 55 \<and> rvec_length sn + 3 \<le> urust_fuel\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>case r of (l, sn1, f, _) \<Rightarrow>
             analyze_m (vecs_of cs) (rvec_elems t) (map unat (rvec_elems rs)) (map unat (rvec_elems tp)) (unat st)
               (rvec_elems sn) (unat cf) = (rvec_elems l, rvec_elems sn1, f) \<and>
             vok l \<and> rvec_length sn1 = rvec_length sn \<and> rvec_elems l \<noteq> [] \<and> (\<forall>x \<in> set (rvec_elems l). lv x < rvec_length sn)\<rangle>)\<close>

lemma cdcl_analyze_spec [crush_specs]:
  shows \<open>\<Gamma>; analyze cs t rs tp st sn cf \<Turnstile>\<^sub>F cdcl_analyze_contract cs t rs tp st sn cf\<close>
  apply (crush_boot f: analyze_def contract: cdcl_analyze_contract_def)
  apply (crush_base simp add: dw_focus_modify)
  apply (all \<open>(unfold GUARD_def, rule hd_Cons_tl[symmetric], simp)?\<close>)
  apply (all \<open>insert count_le_length[of \<open>rvec_elems sn\<close> False]\<close>)
  apply (auto simp add: analyze_m_ana clr_m_def unat_one_iff allvok_nth dest!: set_update_subset_insert[THEN subsetD])
  done

end

end
