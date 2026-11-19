theory QFBV_Watch
  imports QFBV_DpllPure
begin

section \<open>Watched literals: the invariant\<close>

text \<open>The watch lists of \<^verbatim>\<open>dpll\<close> (\<^verbatim>\<open>watch_init\<close>, \<^verbatim>\<open>visit\<close>, \<^verbatim>\<open>wpropagate\<close>). Slot \<open>s\<close> is the
  watch \<open>s mod 2\<close> of clause \<open>s div 2\<close>; \<open>p ! s\<close> is the position in its clause of the literal it
  watches, \<open>nx ! s\<close> the next slot in its list, \<open>h ! x\<close> the first slot of the list of the literal of
  index \<open>x\<close>; a link at or above \<open>length nx\<close> ends a list.\<close>

definition lidx :: \<open>Lit \<Rightarrow> nat\<close> where
  \<open>lidx l \<equiv> 2 * unat (Lit_var l) + (if Lit_neg l then 1 else 0)\<close>

text \<open>The other slot of the clause of slot \<open>s\<close>.\<close>
definition oth :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>oth s \<equiv> if even s then Suc s else s - 1\<close>

text \<open>Slot \<open>s\<close> belongs to one of the first \<open>m\<close> clauses, and that clause watches two literals.\<close>
definition wact :: \<open>Lit list list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>wact cs m s \<equiv> s < 2 * m \<and> 2 \<le> length (cs ! (s div 2))\<close>

definition wlit :: \<open>Lit list list \<Rightarrow> 64 word list \<Rightarrow> nat \<Rightarrow> Lit\<close> where
  \<open>wlit cs p s \<equiv> cs ! (s div 2) ! unat (p ! s)\<close>

text \<open>The list that starts at slot \<open>s\<close> of the links \<open>nx\<close> is \<open>xs\<close>.\<close>
fun lseg :: \<open>64 word list \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool\<close> where
  \<open>lseg nx s [] = (length nx \<le> s)\<close>
| \<open>lseg nx s (y # ys) = (s = y \<and> y < length nx \<and> lseg nx (unat (nx ! y)) ys)\<close>

text \<open>The watches of the first \<open>m\<close> clauses: \<open>Ls ! x\<close> is the list of the literal of index \<open>x\<close>; it
  holds exactly the slots that watch that literal. The two watches of a clause are at different
  positions.\<close>
definition wl_lists ::
  \<open>Lit list list \<Rightarrow> nat \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> nat list list \<Rightarrow> bool\<close> where
  \<open>wl_lists cs m p nx h Ls \<equiv>
     m \<le> length cs \<and> length p = 2 * length cs \<and> length nx = 2 * length cs \<and> length Ls = length h \<and>
     (\<forall>s. wact cs m s \<longrightarrow> unat (p ! s) < length (cs ! (s div 2)) \<and> lidx (wlit cs p s) < length h) \<and>
     (\<forall>c < m. 2 \<le> length (cs ! c) \<longrightarrow> p ! (2 * c) \<noteq> p ! Suc (2 * c)) \<and>
     (\<forall>x < length h. lseg nx (unat (h ! x)) (Ls ! x) \<and> distinct (Ls ! x) \<and>
        (\<forall>s. s \<in> set (Ls ! x) \<longleftrightarrow> wact cs m s \<and> lidx (wlit cs p s) = x))\<close>

definition wl_ok :: \<open>Lit list list \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> bool\<close> where
  \<open>wl_ok cs p nx h \<equiv> \<exists>Ls. wl_lists cs (length cs) p nx h Ls\<close>

text \<open>Every watch whose literal is false by \<open>S\<close> has a partner that is true on the trail \<open>t\<close>.\<close>
definition WS :: \<open>Lit list list \<Rightarrow> 64 word list \<Rightarrow> Lit list \<Rightarrow> Lit set \<Rightarrow> bool\<close> where
  \<open>WS cs p t S \<equiv> \<forall>s. wact cs (length cs) s \<longrightarrow> lneg (wlit cs p s) \<in> S \<longrightarrow> wlit cs p (oth s) \<in> set t\<close>

text \<open>The invariant at a prefix of the trail of length \<open>k\<close>, kept for the decision levels.\<close>
definition WP :: \<open>Lit list list \<Rightarrow> 64 word list \<Rightarrow> Lit list \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>WP cs p t k \<equiv> WS cs p (take k t) (set (take k t))\<close>

text \<open>The clauses of fewer than two literals are satisfied by the trail.\<close>
definition SP :: \<open>Lit list list \<Rightarrow> Lit list \<Rightarrow> bool\<close> where
  \<open>SP cs t \<equiv> \<forall>c \<in> set cs. length c < 2 \<longrightarrow> (\<exists>l \<in> set c. l \<in> set t)\<close>

subsection \<open>Lists of slots\<close>

lemma lseg_lt: \<open>lseg nx s xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> y < length nx\<close>
  by (induction xs arbitrary: s) auto

lemma lseg_upd: \<open>lseg nx s xs \<Longrightarrow> i \<notin> set xs \<Longrightarrow> lseg (nx[i := v]) s xs\<close>
  by (induction xs arbitrary: s) auto

lemma lseg_Cons_iff: \<open>lseg nx s xs \<Longrightarrow> s < length nx \<Longrightarrow> xs \<noteq> [] \<and> hd xs = s\<close>
  by (cases xs) auto

lemma lseg_append:
  \<open>lseg nx s (K @ R) \<Longrightarrow> K \<noteq> [] \<Longrightarrow> lseg nx (unat (nx ! last K)) R\<close>
  by (induction K arbitrary: s) (auto split: if_splits)

lemma lseg_unlink:
  assumes \<open>lseg nx s (K @ y # R)\<close> \<open>K \<noteq> []\<close> \<open>distinct (K @ y # R)\<close>
  shows \<open>lseg (nx[last K := nx ! y]) s (K @ R)\<close>
  using assms
proof (induction K arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons k K)
  show ?case
  proof (cases K)
    case Nil
    have \<open>lseg nx (unat (nx ! y)) R\<close> using Cons.prems(1) Nil by simp
    then have \<open>lseg (nx[k := nx ! y]) (unat (nx ! y)) R\<close>
      using lseg_upd Cons.prems(3) Nil by fastforce
    then show ?thesis using Cons.prems(1) Nil by simp
  next
    case (Cons k' K')
    then have \<open>lseg (nx[last (k # K) := nx ! y]) (unat (nx ! k)) (K @ R)\<close>
      using Cons.IH[of \<open>unat (nx ! k)\<close>] \<open>lseg nx s ((k # K) @ y # R)\<close> \<open>distinct ((k # K) @ y # R)\<close>
      by simp
    moreover have \<open>last (k # K) \<noteq> k\<close> using Cons \<open>distinct ((k # K) @ y # R)\<close> by auto
    ultimately show ?thesis using \<open>lseg nx s ((k # K) @ y # R)\<close> by simp
  qed
qed

lemma lseg_length:
  assumes \<open>lseg nx s xs\<close> \<open>distinct xs\<close>
  shows \<open>length xs \<le> length nx\<close>
proof -
  have \<open>set xs \<subseteq> {..<length nx}\<close> using lseg_lt[OF assms(1)] by blast
  then have \<open>card (set xs) \<le> length nx\<close> using card_mono[of \<open>{..<length nx}\<close>] by fastforce
  then show ?thesis using distinct_card[OF assms(2)] by simp
qed

subsection \<open>Literals on the trail\<close>

lemma lidx_inj: \<open>lidx l = lidx l' \<Longrightarrow> l = l'\<close>
proof -
  assume e: \<open>lidx l = lidx l'\<close>
  then have n: \<open>Lit_neg l = Lit_neg l'\<close>
    unfolding lidx_def by (cases \<open>Lit_neg l\<close>; cases \<open>Lit_neg l'\<close>; simp; presburger)
  then have \<open>unat (Lit_var l) = unat (Lit_var l')\<close> using e unfolding lidx_def by simp
  then have \<open>Lit_var l = Lit_var l'\<close> by (simp add: unat_inj)
  then show ?thesis using n by (simp add: Lit.expand)
qed

lemma lneg_lneg: \<open>lneg (lneg l) = l\<close>
  by (simp add: lneg_def Lit.expand)

lemma lneg_neq: \<open>lneg l \<noteq> l\<close>
  unfolding lneg_def by (metis Lit.collapse Lit.inject)

lemma tr_true:
  assumes \<open>tr_ok n a t\<close> \<open>unat (Lit_var l) < n\<close>
  shows \<open>lit_value_m a l = Some True \<longleftrightarrow> l \<in> set t\<close>
proof
  assume v: \<open>lit_value_m a l = Some True\<close>
  then obtain b where b: \<open>a ! unat (Lit_var l) = Some b\<close> \<open>b \<noteq> Lit_neg l\<close>
    by (auto simp: lit_value_m_def split: option.splits)
  have \<open>\<exists>l' \<in> set t. unat (Lit_var l') = unat (Lit_var l)\<close>
    using assms b(1) unfolding tr_ok_def by blast
  then obtain l' where l': \<open>l' \<in> set t\<close> \<open>unat (Lit_var l') = unat (Lit_var l)\<close> by blast
  then have \<open>a ! unat (Lit_var l) = Some (\<not> Lit_neg l')\<close> using assms(1) by (auto simp: tr_ok_def)
  then have \<open>Lit_neg l' = Lit_neg l\<close> using b by auto
  moreover have \<open>Lit_var l' = Lit_var l\<close> using l'(2) by (simp add: unat_inj)
  ultimately show \<open>l \<in> set t\<close> using l'(1) by (metis Lit.expand)
next
  assume \<open>l \<in> set t\<close>
  then have \<open>a ! unat (Lit_var l) = Some (\<not> Lit_neg l)\<close> using assms(1) by (auto simp: tr_ok_def)
  then show \<open>lit_value_m a l = Some True\<close> by (simp add: lit_value_m_def)
qed

lemma lit_value_lneg: \<open>lit_value_m a (lneg l) = map_option Not (lit_value_m a l)\<close>
  by (auto simp: lit_value_m_def lneg_def split: option.splits)

lemma tr_false:
  assumes \<open>tr_ok n a t\<close> \<open>unat (Lit_var l) < n\<close>
  shows \<open>lit_value_m a l = Some False \<longleftrightarrow> lneg l \<in> set t\<close>
proof -
  have \<open>unat (Lit_var (lneg l)) < n\<close> using assms(2) by (simp add: lneg_def)
  then have \<open>lit_value_m a (lneg l) = Some True \<longleftrightarrow> lneg l \<in> set t\<close> using tr_true[OF assms(1)] by blast
  moreover have \<open>lit_value_m a l = Some False \<longleftrightarrow> lit_value_m a (lneg l) = Some True\<close>
    by (cases \<open>lit_value_m a l\<close>) (auto simp: lit_value_lneg)
  ultimately show ?thesis by blast
qed

lemma tr_not_both: \<open>tr_ok n a t \<Longrightarrow> l \<in> set t \<Longrightarrow> lneg l \<notin> set t\<close>
  using tr_true[of n a t l] tr_false[of n a t l] by (auto simp: tr_ok_def)

lemma take_prefix: \<open>k \<le> length t \<Longrightarrow> take k (t @ e) = take k t\<close>
  by simp

subsection \<open>The status of a clause whose literals but one are false\<close>

lemma status_all_false:
  \<open>\<forall>l \<in> set ls. lit_value_m a l = Some False \<Longrightarrow> status_m a ls u op = status_m a [] u op\<close>
  by (induction ls) auto

lemma status_one:
  assumes \<open>j < length ls\<close> \<open>\<forall>m < length ls. m \<noteq> j \<longrightarrow> lit_value_m a (ls ! m) = Some False\<close>
  shows \<open>status_m a ls u op =
     (case lit_value_m a (ls ! j) of
        Some True \<Rightarrow> Status_Satisfied
      | Some False \<Rightarrow> status_m a [] u op
      | None \<Rightarrow> (if u \<noteq> None then status_m a [] u True else status_m a [] (Some (ls ! j)) op))\<close>
  using assms
proof (induction ls arbitrary: j u op)
  case Nil
  then show ?case by simp
next
  case (Cons l ls)
  show ?case
  proof (cases j)
    case 0
    have \<open>\<forall>l' \<in> set ls. lit_value_m a l' = Some False\<close>
    proof
      fix l' assume \<open>l' \<in> set ls\<close>
      then obtain i where \<open>i < length ls\<close> \<open>l' = ls ! i\<close> by (auto simp: in_set_conv_nth)
      then show \<open>lit_value_m a l' = Some False\<close> using Cons.prems(2)[rule_format, of \<open>Suc i\<close>] 0 by simp
    qed
    then show ?thesis using 0 status_all_false[of ls a] by (auto split: option.splits bool.splits)
  next
    case (Suc j')
    have f: \<open>lit_value_m a l = Some False\<close> using Cons.prems(2)[rule_format, of 0] Suc by simp
    have \<open>\<forall>m < length ls. m \<noteq> j' \<longrightarrow> lit_value_m a (ls ! m) = Some False\<close>
      using Cons.prems(2) Suc by auto
    moreover have \<open>j' < length ls\<close> using Cons.prems(1) Suc by simp
    ultimately show ?thesis using Cons.IH[of j' u op] f \<open>j = Suc j'\<close> by (simp split: option.splits bool.splits)
  qed
qed

lemma status_one_clause:
  assumes \<open>j < length c\<close> \<open>\<forall>m < length c. m \<noteq> j \<longrightarrow> lit_value_m a (c ! m) = Some False\<close>
    \<open>lit_value_m a (c ! j) \<noteq> Some True\<close>
  shows \<open>(lit_value_m a (c ! j) = Some False \<and> status_m a c None False = Status_Conflict) \<or>
         (lit_value_m a (c ! j) = None \<and> status_m a c None False = Status_Unit (c ! j))\<close>
  using status_one[OF assms(1,2), of None False] assms(3) by (auto split: option.splits bool.splits)

subsection \<open>The steps of a visit\<close>

text \<open>\<^verbatim>\<open>move_watch\<close>.\<close>
definition mw_m ::
  \<open>64 word list \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow>
   64 word list \<times> 64 word list \<times> 64 word list\<close> where
  \<open>mw_m p nx h s prev x k y \<equiv>
     let ns = nx ! unat s; p1 = p[unat s := k] in
     if unat prev < length nx then (p1, (nx[unat prev := ns])[unat s := h ! unat y], h[unat y := s])
     else let h1 = h[unat x := ns] in (p1, nx[unat s := h1 ! unat y], h1[unat y := s])\<close>

text \<open>The result of \<^verbatim>\<open>visit_slot\<close> on slot \<open>s\<close> of the list of index \<open>x\<close>: the slot stays if the other
  watch of its clause is true; otherwise its watch moves to a literal of the clause that is not false,
  if there is one; otherwise the status of the clause decides.\<close>
definition vslot_post ::
  \<open>Lit list list \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> bool option list \<Rightarrow> Lit list \<Rightarrow>
   64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow>
   64 word list \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> bool option list \<Rightarrow> Lit list \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool\<close> where
  \<open>vslot_post cs p nx h a t x s prev p1 nx1 h1 a1 t1 keep okb \<equiv>
     let c = cs ! (unat s div 2); i = unat (p ! unat s); j = unat (p ! oth (unat s)) in
     if i < length c \<and> j < length c \<and> lit_value_m a (c ! j) \<noteq> Some True then
       (\<exists>k y. unat k < length c \<and> unat k \<noteq> i \<and> unat k \<noteq> j \<and> lit_value_m a (c ! unat k) \<noteq> Some False \<and>
          unat y = lidx (c ! unat k) \<and> (p1, nx1, h1) = mw_m p nx h s prev x k y \<and>
          a1 = a \<and> t1 = t \<and> \<not> keep \<and> okb) \<or>
       ((\<forall>k < length c. k \<noteq> i \<and> k \<noteq> j \<longrightarrow> lit_value_m a (c ! k) = Some False) \<and>
          p1 = p \<and> nx1 = nx \<and> h1 = h \<and> keep \<and>
          (case status_m a c None False of
             Status_Conflict \<Rightarrow> a1 = a \<and> t1 = t \<and> \<not> okb
           | Status_Unit l \<Rightarrow> a1 = a[unat (Lit_var l) := Some (\<not> Lit_neg l)] \<and> t1 = t @ [l] \<and> okb
           | Status_Satisfied \<Rightarrow> a1 = a \<and> t1 = t \<and> okb
           | Status_Open \<Rightarrow> a1 = a \<and> t1 = t \<and> okb))
     else p1 = p \<and> nx1 = nx \<and> h1 = h \<and> a1 = a \<and> t1 = t \<and> keep \<and> okb\<close>

text \<open>The invariant of the loop of \<^verbatim>\<open>visit\<close> over the list of index \<open>x\<close>, whose literal \<open>w\<close> is false,
  from the watches \<open>p0\<close> and the trail \<open>t0\<close>: the list is \<open>K @ R\<close>, where \<open>K\<close> holds the slots visited
  that stay (the last one is \<open>prev\<close>) and \<open>R\<close> those still to visit, from slot \<open>s\<close>; \<open>st\<close> counts the
  steps. A watch false by \<open>S\<close> or by \<open>w\<close> has a true partner unless its slot is still to visit.\<close>
definition vinv ::
  \<open>Lit list list \<Rightarrow> nat \<Rightarrow> Lit \<Rightarrow> 64 word list \<Rightarrow> Lit list \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow>
   Lit list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>vinv cs x w p0 t0 p nx h t s prev st \<equiv> \<exists>Ls K R.
     wl_lists cs (length cs) p nx h Ls \<and> x < length h \<and> Ls ! x = K @ R \<and> lseg nx s R \<and>
     (K = [] \<longrightarrow> length nx \<le> prev) \<and> (K \<noteq> [] \<longrightarrow> prev = last K) \<and> st + length R \<le> length nx \<and>
     (\<forall>S. S \<subseteq> set t0 \<longrightarrow> WS cs p0 t0 S \<longrightarrow>
        (\<forall>s'. wact cs (length cs) s' \<longrightarrow> lneg (wlit cs p s') \<in> insert (lneg w) S \<longrightarrow>
           wlit cs p (oth s') \<in> set t \<or> s' \<in> set R)) \<and>
     (\<forall>k \<le> length t0. WP cs p0 t0 k \<longrightarrow> WP cs p t k)\<close>

text \<open>The facts every step of the visit uses.\<close>
definition vctx :: \<open>Lit list list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> Lit \<Rightarrow> Lit list \<Rightarrow> 64 word list \<Rightarrow> bool\<close> where
  \<open>vctx cs n x w t0 h \<equiv> dpll_wf n cs \<and> length h = 2 * n \<and> lidx w = x \<and> lneg w \<in> set t0\<close>

lemma oth_oth: \<open>oth (oth s) = s\<close>
  by (auto simp: oth_def)

lemma oth_neq: \<open>oth s \<noteq> s\<close>
  by (cases \<open>even s\<close>) (auto simp: oth_def elim: oddE)

lemma oth_div: \<open>oth s div 2 = s div 2\<close>
  by (auto simp: oth_def elim!: evenE oddE)

lemma wact_oth: \<open>wact cs m s \<Longrightarrow> wact cs m (oth s)\<close>
  by (auto simp: wact_def oth_div oth_def elim!: evenE oddE)

lemma wl_pos_neq:
  assumes \<open>wl_lists cs m p nx h Ls\<close> \<open>wact cs m s\<close>
  shows \<open>p ! s \<noteq> p ! oth s\<close>
proof -
  have \<open>s div 2 < m\<close> \<open>2 \<le> length (cs ! (s div 2))\<close> using assms(2) by (auto simp: wact_def)
  then have \<open>p ! (2 * (s div 2)) \<noteq> p ! Suc (2 * (s div 2))\<close> using assms(1) by (auto simp: wl_lists_def)
  then show ?thesis by (cases \<open>even s\<close>) (auto simp: oth_def elim!: evenE oddE)
qed

lemma vinv_entry:
  assumes \<open>wl_ok cs p nx h\<close> \<open>x < length h\<close> \<open>lidx w = x\<close>
  shows \<open>vinv cs x w p t p nx h t (unat (h ! x)) (length nx) 0\<close>
proof -
  obtain Ls where L: \<open>wl_lists cs (length cs) p nx h Ls\<close> using assms(1) by (auto simp: wl_ok_def)
  have X: \<open>lseg nx (unat (h ! x)) (Ls ! x)\<close> \<open>distinct (Ls ! x)\<close>
    \<open>\<forall>s. s \<in> set (Ls ! x) \<longleftrightarrow> wact cs (length cs) s \<and> lidx (wlit cs p s) = x\<close>
    using L assms(2) unfolding wl_lists_def by blast+
  have len: \<open>length (Ls ! x) \<le> length nx\<close> using lseg_length X(1,2) by blast
  have sem: \<open>\<forall>S. S \<subseteq> set t \<longrightarrow> WS cs p t S \<longrightarrow>
     (\<forall>s'. wact cs (length cs) s' \<longrightarrow> lneg (wlit cs p s') \<in> insert (lneg w) S \<longrightarrow>
        wlit cs p (oth s') \<in> set t \<or> s' \<in> set (Ls ! x))\<close>
  proof (intro allI impI)
    fix S s'
    assume ws: \<open>WS cs p t S\<close> and act: \<open>wact cs (length cs) s'\<close>
      and f: \<open>lneg (wlit cs p s') \<in> insert (lneg w) S\<close>
    show \<open>wlit cs p (oth s') \<in> set t \<or> s' \<in> set (Ls ! x)\<close>
    proof (cases \<open>lneg (wlit cs p s') = lneg w\<close>)
      case True
      then have \<open>wlit cs p s' = w\<close> by (metis lneg_lneg)
      then show ?thesis using X(3) assms(3) act by auto
    next
      case False
      then show ?thesis using ws act f unfolding WS_def by auto
    qed
  qed
  show ?thesis unfolding vinv_def
    by (rule exI[of _ Ls], rule exI[of _ \<open>[]\<close>], rule exI[of _ \<open>Ls ! x\<close>]) (use L assms(2) X len sem in auto)
qed

lemma mw_m_facts:
  assumes \<open>(p1, nx1, h1) = mw_m p nx h sw pw xw k yw\<close> \<open>unat sw < length nx\<close>
    \<open>unat xw < length h\<close> \<open>unat yw < length h\<close> \<open>unat yw \<noteq> unat xw\<close>
  shows \<open>p1 = p[unat sw := k] \<and> length h1 = length h \<and> h1 ! unat yw = sw \<and>
         (\<forall>z < length h. z \<noteq> unat yw \<longrightarrow> z \<noteq> unat xw \<longrightarrow> h1 ! z = h ! z) \<and>
         (unat pw < length nx \<longrightarrow> h1 ! unat xw = h ! unat xw \<and>
            nx1 = (nx[unat pw := nx ! unat sw])[unat sw := h ! unat yw]) \<and>
         (\<not> unat pw < length nx \<longrightarrow> h1 ! unat xw = nx ! unat sw \<and> nx1 = nx[unat sw := h ! unat yw])\<close>
  using assms by (auto simp: mw_m_def Let_def nth_list_update split: if_splits)

lemma wlit_upd:
  \<open>s < length p \<Longrightarrow> wlit cs (p[s := k]) s' = (if s' = s then cs ! (s div 2) ! unat k else wlit cs p s')\<close>
  by (simp add: wlit_def)

lemma WP_move:
  assumes \<open>WP cs p t k\<close> \<open>wlit cs p s = w\<close> \<open>w \<notin> set t\<close> \<open>lneg (cs ! (s div 2) ! unat kw) \<notin> set t\<close>
    \<open>s < length p\<close>
  shows \<open>WP cs (p[s := kw]) t k\<close>
  unfolding WP_def WS_def
proof (intro allI impI)
  fix s' assume act: \<open>wact cs (length cs) s'\<close> and f: \<open>lneg (wlit cs (p[s := kw]) s') \<in> set (take k t)\<close>
  have tk: \<open>set (take k t) \<subseteq> set t\<close> by (rule set_take_subset)
  have ne: \<open>s' \<noteq> s\<close> using f assms(4,5) tk wlit_upd[of s p cs kw s] by auto
  then have \<open>lneg (wlit cs p s') \<in> set (take k t)\<close> using f assms(5) by (simp add: wlit_upd)
  then have o: \<open>wlit cs p (oth s') \<in> set (take k t)\<close> using assms(1) act unfolding WP_def WS_def by blast
  have \<open>oth s' \<noteq> s\<close> using o assms(2,3) tk by auto
  then show \<open>wlit cs (p[s := kw]) (oth s') \<in> set (take k t)\<close> using o assms(5) by (simp add: wlit_upd)
qed

lemma wl_mem:
  \<open>wl_lists cs M p nx h Ls \<Longrightarrow> z < length h \<Longrightarrow> v \<in> set (Ls ! z) \<longleftrightarrow> wact cs M v \<and> lidx (wlit cs p v) = z\<close>
  by (simp add: wl_lists_def)

lemma wl_lseg:
  \<open>wl_lists cs M p nx h Ls \<Longrightarrow> z < length h \<Longrightarrow> lseg nx (unat (h ! z)) (Ls ! z) \<and> distinct (Ls ! z)\<close>
  by (simp add: wl_lists_def)

lemma wl_disj:
  assumes \<open>wl_lists cs M p nx h Ls\<close> \<open>z < length h\<close> \<open>z' < length h\<close> \<open>z \<noteq> z'\<close> \<open>v \<in> set (Ls ! z)\<close>
  shows \<open>v \<notin> set (Ls ! z')\<close>
  using wl_mem[OF assms(1,2), of v] wl_mem[OF assms(1,3), of v] assms(4,5) by simp

lemma wl_move:
  assumes L: \<open>wl_lists cs M p nx h Ls\<close>
    and Lx: \<open>Ls ! x = K @ s # R\<close> and pk: \<open>K = [] \<longrightarrow> length nx \<le> unat pw\<close>
    and pl: \<open>K \<noteq> [] \<longrightarrow> unat pw = last K\<close>
    and x: \<open>x < length h\<close> and y: \<open>y < length h\<close> and yx: \<open>y \<noteq> x\<close>
    and k: \<open>unat k < length (cs ! (s div 2))\<close> and kj: \<open>k \<noteq> p ! oth s\<close>
    and ky: \<open>lidx (cs ! (s div 2) ! unat k) = y\<close>
    and mw: \<open>(p1, nx1, h1) = mw_m p nx h sw pw xw k yw\<close>
    and u: \<open>unat sw = s\<close> \<open>unat xw = x\<close> \<open>unat yw = y\<close>
  shows \<open>wl_lists cs M p1 nx1 h1 (Ls[x := K @ R, y := s # Ls ! y]) \<and> lseg nx1 (unat (nx ! s)) R\<close>
proof -
  have LL: \<open>M \<le> length cs\<close> \<open>length p = 2 * length cs\<close> \<open>length nx = 2 * length cs\<close> \<open>length Ls = length h\<close>
    \<open>\<forall>s. wact cs M s \<longrightarrow> unat (p ! s) < length (cs ! (s div 2)) \<and> lidx (wlit cs p s) < length h\<close>
    \<open>\<forall>c < M. 2 \<le> length (cs ! c) \<longrightarrow> p ! (2 * c) \<noteq> p ! Suc (2 * c)\<close>
    \<open>\<forall>z < length h. lseg nx (unat (h ! z)) (Ls ! z) \<and> distinct (Ls ! z) \<and>
        (\<forall>s. s \<in> set (Ls ! z) \<longleftrightarrow> wact cs M s \<and> lidx (wlit cs p s) = z)\<close>
    using L unfolding wl_lists_def by blast+
  have lx: \<open>lseg nx (unat (h ! x)) (K @ s # R)\<close> \<open>distinct (K @ s # R)\<close>
    using wl_lseg[OF L x] unfolding Lx by blast+
  have \<open>s \<in> set (Ls ! x)\<close> using Lx by simp
  then have sx: \<open>wact cs M s\<close> \<open>lidx (wlit cs p s) = x\<close> using wl_mem[OF L x] by blast+
  have sN: \<open>s < length nx\<close> using lseg_lt[OF lx(1)] by simp
  have sp: \<open>s < length p\<close> using sN LL(2,3) by simp
  have sy: \<open>s \<notin> set (Ls ! y)\<close> using wl_disj[OF L x y] yx Lx by auto
  have Kx: \<open>\<forall>v \<in> set K. \<forall>z < length h. z \<noteq> x \<longrightarrow> v \<notin> set (Ls ! z)\<close>
    using wl_disj[OF L x] Lx by auto
  have sz: \<open>\<forall>z < length h. z \<noteq> x \<longrightarrow> s \<notin> set (Ls ! z)\<close> using wl_disj[OF L x] Lx by auto
  note MW = mw_m_facts[OF mw, unfolded u, OF sN x y yx]
  define nxA where \<open>nxA = (if K \<noteq> [] then nx[unat pw := nx ! s] else nx)\<close>
  have nx1: \<open>nx1 = nxA[s := h ! y]\<close>
  proof (cases \<open>K = []\<close>)
    case True
    then show ?thesis using MW pk by (simp add: nxA_def)
  next
    case False
    have \<open>last K \<in> set (Ls ! x)\<close> using False Lx by simp
    then have \<open>unat pw < length nx\<close> using pl False lseg_lt[OF lx(1)] by auto
    then show ?thesis using MW False by (simp add: nxA_def)
  qed
  have hx: \<open>unat (h1 ! x) = (if K = [] then unat (nx ! s) else unat (h ! x))\<close>
  proof (cases \<open>K = []\<close>)
    case True
    then show ?thesis using MW pk by simp
  next
    case False
    have \<open>last K \<in> set (Ls ! x)\<close> using False Lx by simp
    then have \<open>unat pw < length nx\<close> using pl False lseg_lt[OF lx(1)] by auto
    then show ?thesis using MW False by simp
  qed
  text \<open>A list that holds neither the slot nor the one before it keeps its links.\<close>
  have keep: \<open>lseg nx1 v xs\<close> if \<open>lseg nx v xs\<close> \<open>s \<notin> set xs\<close> \<open>K \<noteq> [] \<longrightarrow> unat pw \<notin> set xs\<close> for v xs
  proof -
    have \<open>lseg nxA v xs\<close> using that lseg_upd[of nx v xs \<open>unat pw\<close>] by (auto simp: nxA_def)
    then show ?thesis using nx1 lseg_upd that(2) by simp
  qed
  have pwK: \<open>K \<noteq> [] \<longrightarrow> unat pw \<in> set K\<close> using pl by auto
  have lR: \<open>lseg nx (unat (nx ! s)) R\<close>
  proof (cases \<open>K = []\<close>)
    case True
    then show ?thesis using lx(1) by simp
  next
    case False
    have \<open>lseg nx (unat (nx ! last K)) (s # R)\<close> using lseg_append[OF lx(1) False] .
    then show ?thesis by simp
  qed
  have R1: \<open>lseg nx1 (unat (nx ! s)) R\<close>
    by (rule keep[OF lR]) (use lx(2) pwK in auto)
  have Lx1: \<open>lseg nx1 (unat (h1 ! x)) (K @ R)\<close>
  proof (cases \<open>K = []\<close>)
    case True
    then show ?thesis using R1 hx by simp
  next
    case False
    have \<open>lseg (nx[last K := nx ! s]) (unat (h ! x)) (K @ R)\<close> using lseg_unlink[OF lx(1) False lx(2)] .
    then have \<open>lseg nxA (unat (h ! x)) (K @ R)\<close> using False pl by (simp add: nxA_def)
    then have \<open>lseg nx1 (unat (h ! x)) (K @ R)\<close> using nx1 lseg_upd lx(2) by simp
    then show ?thesis using hx False by simp
  qed
  have Ly1: \<open>lseg nx1 (unat (h1 ! y)) (s # Ls ! y)\<close>
  proof -
    have \<open>lseg nx1 (unat (h ! y)) (Ls ! y)\<close>
      by (rule keep) (use LL(7) y sy Kx pwK yx in auto)
    moreover have \<open>nx1 ! s = h ! y\<close> using nx1 sN by (simp add: nxA_def)
    moreover have \<open>s < length nx1\<close> using nx1 sN by (simp add: nxA_def)
    ultimately show ?thesis using MW u by simp
  qed
  let ?Ls = \<open>Ls[x := K @ R, y := s # Ls ! y]\<close>
  have p1: \<open>p1 = p[s := k]\<close> using MW by simp
  have wl1: \<open>\<And>v. wlit cs p1 v = (if v = s then cs ! (s div 2) ! unat k else wlit cs p v)\<close>
    using p1 wlit_upd[OF sp] by simp
  have mem: \<open>\<forall>z < length h1. lseg nx1 (unat (h1 ! z)) (?Ls ! z) \<and> distinct (?Ls ! z) \<and>
        (\<forall>v. v \<in> set (?Ls ! z) \<longleftrightarrow> wact cs M v \<and> lidx (wlit cs p1 v) = z)\<close>
  proof (intro allI impI)
    fix z assume z: \<open>z < length h1\<close>
    then have zh: \<open>z < length h\<close> using MW by simp
    show \<open>lseg nx1 (unat (h1 ! z)) (?Ls ! z) \<and> distinct (?Ls ! z) \<and>
        (\<forall>v. v \<in> set (?Ls ! z) \<longleftrightarrow> wact cs M v \<and> lidx (wlit cs p1 v) = z)\<close>
    proof (cases \<open>z = y\<close>)
      case True
      have \<open>?Ls ! z = s # Ls ! y\<close> using True y LL(4) by simp
      moreover have \<open>\<forall>v. v \<in> set (s # Ls ! y) \<longleftrightarrow> wact cs M v \<and> lidx (wlit cs p1 v) = y\<close>
        using LL(7) y sx(1) ky wl1 sy by auto
      ultimately show ?thesis using Ly1 True LL(7) y sy by auto
    next
      case zy: False
      show ?thesis
      proof (cases \<open>z = x\<close>)
        case True
        have \<open>?Ls ! z = K @ R\<close> using True x yx LL(4) by simp
        moreover have \<open>\<forall>v. v \<in> set (K @ R) \<longleftrightarrow> wact cs M v \<and> lidx (wlit cs p1 v) = x\<close>
        proof
          fix v
          have \<open>v \<in> set (K @ R) \<longleftrightarrow> v \<in> set (Ls ! x) \<and> v \<noteq> s\<close> using Lx lx(2) by auto
          then show \<open>v \<in> set (K @ R) \<longleftrightarrow> wact cs M v \<and> lidx (wlit cs p1 v) = x\<close>
            using LL(7) x wl1 ky yx by auto
        qed
        ultimately show ?thesis using Lx1 True lx(2) by auto
      next
        case zx: False
        have e: \<open>?Ls ! z = Ls ! z\<close> using zx zy by simp
        have hz: \<open>h1 ! z = h ! z\<close> using MW zh zx zy by simp
        have \<open>lseg nx1 (unat (h1 ! z)) (Ls ! z)\<close>
          using keep[of \<open>unat (h ! z)\<close> \<open>Ls ! z\<close>] LL(7) zh sz zx Kx pwK hz by auto
        moreover have \<open>\<forall>v. v \<in> set (Ls ! z) \<longleftrightarrow> wact cs M v \<and> lidx (wlit cs p1 v) = z\<close>
          using LL(7) zh wl1 ky zy sz zx by auto
        ultimately show ?thesis using e LL(7) zh by auto
      qed
    qed
  qed
  have pos: \<open>\<forall>v. wact cs M v \<longrightarrow> unat (p1 ! v) < length (cs ! (v div 2)) \<and> lidx (wlit cs p1 v) < length h1\<close>
    using LL(5) p1 wl1 k ky y MW sp by (auto simp: nth_list_update)
  have dis: \<open>\<forall>c < M. 2 \<le> length (cs ! c) \<longrightarrow> p1 ! (2 * c) \<noteq> p1 ! Suc (2 * c)\<close>
  proof (intro allI impI)
    fix c assume c: \<open>c < M\<close> \<open>2 \<le> length (cs ! c)\<close>
    have o1: \<open>2 * c < length p\<close> \<open>Suc (2 * c) < length p\<close> using c LL(1,2) by auto
    have old: \<open>p ! (2 * c) \<noteq> p ! Suc (2 * c)\<close> using LL(6) c by blast
    consider \<open>s = 2 * c\<close> | \<open>s = Suc (2 * c)\<close> | \<open>s \<noteq> 2 * c \<and> s \<noteq> Suc (2 * c)\<close> by blast
    then show \<open>p1 ! (2 * c) \<noteq> p1 ! Suc (2 * c)\<close>
    proof cases
      case 1
      then have \<open>oth s = Suc (2 * c)\<close> by (simp add: oth_def)
      then show ?thesis using 1 p1 kj o1 by simp
    next
      case 2
      then have \<open>oth s = 2 * c\<close> by (simp add: oth_def)
      then show ?thesis using 2 p1 kj o1 by simp
    next
      case 3
      then show ?thesis using p1 old by simp
    qed
  qed
  have lens: \<open>length p1 = 2 * length cs\<close> \<open>length nx1 = 2 * length cs\<close> \<open>length ?Ls = length h1\<close>
    using p1 nx1 LL MW by (simp_all add: nxA_def)
  show ?thesis using LL(1) lens pos dis mem R1 unfolding wl_lists_def by blast
qed

lemma vinv_step:
  assumes \<open>vinv cs (unat xw) w p0 t0 p nx h t (unat sw) (unat pw) st\<close> \<open>unat sw < length nx\<close>
    \<open>vslot_post cs p nx h a t xw sw pw p1 nx1 h1 a1 t1 keep True\<close>
    \<open>tr_ok n a t\<close> \<open>\<exists>e. t = t0 @ e\<close> \<open>vctx cs n (unat xw) w t0 h\<close>
  shows \<open>vinv cs (unat xw) w p0 t0 p1 nx1 h1 t1 (unat (nx ! unat sw)) (if keep then unat sw else unat pw) (Suc st)\<close>
proof -
  let ?x = \<open>unat xw\<close> and ?s = \<open>unat sw\<close>
  obtain Ls K R0 where V: \<open>wl_lists cs (length cs) p nx h Ls\<close> \<open>?x < length h\<close> \<open>Ls ! ?x = K @ R0\<close>
    \<open>lseg nx ?s R0\<close> \<open>K = [] \<longrightarrow> length nx \<le> unat pw\<close> \<open>K \<noteq> [] \<longrightarrow> unat pw = last K\<close>
    \<open>st + length R0 \<le> length nx\<close>
    and SEM: \<open>\<forall>S. S \<subseteq> set t0 \<longrightarrow> WS cs p0 t0 S \<longrightarrow>
        (\<forall>s'. wact cs (length cs) s' \<longrightarrow> lneg (wlit cs p s') \<in> insert (lneg w) S \<longrightarrow>
           wlit cs p (oth s') \<in> set t \<or> s' \<in> set R0)\<close>
    and WPP: \<open>\<forall>k \<le> length t0. WP cs p0 t0 k \<longrightarrow> WP cs p t k\<close>
    by (insert assms(1)[unfolded vinv_def], elim exE conjE, rule that, assumption+)
  have \<open>R0 \<noteq> [] \<and> hd R0 = ?s\<close> using lseg_Cons_iff[OF V(4) assms(2)] .
  then obtain R where R0: \<open>R0 = ?s # R\<close> by (cases R0) auto
  have lR: \<open>lseg nx (unat (nx ! ?s)) R\<close> using V(4) R0 by simp
  have Lx: \<open>Ls ! ?x = K @ ?s # R\<close> using V(3) R0 by simp
  have \<open>?s \<in> set (Ls ! ?x)\<close> using Lx by simp
  then have sx: \<open>wact cs (length cs) ?s\<close> \<open>lidx (wlit cs p ?s) = ?x\<close> using wl_mem[OF V(1,2)] by blast+
  have wf: \<open>dpll_wf n cs\<close> and lh: \<open>length h = 2 * n\<close> and lw: \<open>lidx w = ?x\<close> and nw: \<open>lneg w \<in> set t0\<close>
    using assms(6) by (simp_all add: vctx_def)
  obtain e where te: \<open>t = t0 @ e\<close> using assms(5) by blast
  have nwt: \<open>lneg w \<in> set t\<close> using nw te by simp
  have t0t: \<open>set t0 \<subseteq> set t\<close> using te by simp
  have ws: \<open>wlit cs p ?s = w\<close> using sx(2) lw lidx_inj by metis
  have wnt: \<open>w \<notin> set t\<close> using tr_not_both[OF assms(4) nwt] lneg_lneg by metis
  define c where \<open>c = cs ! (?s div 2)\<close>
  define i where \<open>i = unat (p ! ?s)\<close>
  define j where \<open>j = unat (p ! oth ?s)\<close>
  have sc: \<open>?s div 2 < length cs\<close> using sx(1) by (auto simp: wact_def)
  have lc: \<open>\<forall>m < length c. unat (Lit_var (c ! m)) < n\<close>
  proof (intro allI impI)
    fix m assume \<open>m < length c\<close>
    then have \<open>c ! m \<in> set c\<close> by simp
    moreover have \<open>c \<in> set cs\<close> using nth_mem[OF sc] unfolding c_def .
    ultimately show \<open>unat (Lit_var (c ! m)) < n\<close> using wf unfolding dpll_wf_def lits_lt_def by blast
  qed
  have WL: \<open>\<forall>s. wact cs (length cs) s \<longrightarrow> unat (p ! s) < length (cs ! (s div 2))\<close>
    using V(1) unfolding wl_lists_def by blast
  have il: \<open>i < length c\<close> using WL sx(1) unfolding i_def c_def by blast
  have jl: \<open>j < length c\<close> using WL wact_oth[OF sx(1)] oth_div[of ?s] unfolding j_def c_def by metis
  have ij: \<open>i \<noteq> j\<close> using wl_pos_neq[OF V(1) sx(1)] unfolding i_def j_def by (simp add: unat_inj)
  have ci: \<open>c ! i = w\<close> using ws unfolding wlit_def c_def i_def .
  have cj: \<open>c ! j = wlit cs p (oth ?s)\<close> unfolding wlit_def c_def j_def by (simp add: oth_div)
  have wF: \<open>lit_value_m a w = Some False\<close>
    using tr_false[OF assms(4), of w] nwt lc il ci by auto
  have lenp: \<open>?s < length p\<close> using V(1) sx(1) unfolding wl_lists_def wact_def by simp
  have N1: \<open>Suc st + length R \<le> length nx\<close> using V(7) R0 by simp
  note P = assms(3)[unfolded vslot_post_def Let_def, folded c_def i_def j_def]
  have SEMR: \<open>wlit cs p (oth s') \<in> set t \<or> s' \<in> set R\<close>
    if \<open>S \<subseteq> set t0\<close> \<open>WS cs p0 t0 S\<close> \<open>wact cs (length cs) s'\<close> \<open>lneg (wlit cs p s') \<in> insert (lneg w) S\<close>
      \<open>s' \<noteq> ?s\<close> for S s'
    using SEM that R0 by auto
  consider (A) \<open>lit_value_m a (c ! j) = Some True\<close> \<open>p1 = p\<close> \<open>nx1 = nx\<close> \<open>h1 = h\<close> \<open>t1 = t\<close> \<open>keep\<close>
    | (B) k y where \<open>unat k < length c\<close> \<open>unat k \<noteq> i\<close> \<open>unat k \<noteq> j\<close> \<open>lit_value_m a (c ! unat k) \<noteq> Some False\<close>
        \<open>unat y = lidx (c ! unat k)\<close> \<open>(p1, nx1, h1) = mw_m p nx h sw pw xw k y\<close> \<open>t1 = t\<close> \<open>\<not> keep\<close>
    | (C) \<open>\<forall>k < length c. k \<noteq> i \<and> k \<noteq> j \<longrightarrow> lit_value_m a (c ! k) = Some False\<close>
        \<open>lit_value_m a (c ! j) \<noteq> Some True\<close> \<open>p1 = p\<close> \<open>nx1 = nx\<close> \<open>h1 = h\<close> \<open>keep\<close>
        \<open>case status_m a c None False of Status_Conflict \<Rightarrow> False | Status_Unit l \<Rightarrow> t1 = t @ [l]
           | Status_Satisfied \<Rightarrow> t1 = t | Status_Open \<Rightarrow> t1 = t\<close>
    using P il jl by (auto split: if_splits Status.splits)
  then show ?thesis
  proof cases
    case A
    have cjt: \<open>wlit cs p (oth ?s) \<in> set t\<close> using A(1) tr_true[OF assms(4)] lc jl cj by metis
    have sem: \<open>\<forall>S. S \<subseteq> set t0 \<longrightarrow> WS cs p0 t0 S \<longrightarrow>
        (\<forall>s'. wact cs (length cs) s' \<longrightarrow> lneg (wlit cs p s') \<in> insert (lneg w) S \<longrightarrow>
           wlit cs p (oth s') \<in> set t \<or> s' \<in> set R)\<close>
      using SEMR cjt by blast
    show ?thesis unfolding vinv_def
      by (rule exI[of _ Ls], rule exI[of _ \<open>K @ [?s]\<close>], rule exI[of _ R])
         (use A V(1,2) Lx lR N1 sem WPP in auto)
  next
    case (B k y)
    have yx: \<open>unat y \<noteq> ?x\<close>
    proof
      assume \<open>unat y = ?x\<close>
      then have \<open>c ! unat k = w\<close> using B(5) lw lidx_inj by metis
      then show False using B(4) wF by simp
    qed
    have yl: \<open>unat y < length h\<close> using B(1,5) lc lh by (auto simp: lidx_def)
    have kj: \<open>k \<noteq> p ! oth ?s\<close> using B(3) unfolding j_def by auto
    note M = wl_move[OF V(1) Lx V(5,6,2) yl yx B(1)[unfolded c_def] kj B(5)[unfolded c_def, symmetric] B(6) refl refl refl]
    have p1: \<open>p1 = p[?s := k]\<close> using mw_m_facts[OF B(6) assms(2) V(2) yl yx] by simp
    have Lx1: \<open>(Ls[?x := K @ R, unat y := ?s # Ls ! unat y]) ! ?x = K @ R\<close>
      using yx V(1,2) unfolding wl_lists_def by simp
    have kt: \<open>lneg (c ! unat k) \<notin> set t\<close> using B(1,4) tr_false[OF assms(4)] lc by metis
    have wl1: \<open>\<And>v. wlit cs p1 v = (if v = ?s then c ! unat k else wlit cs p v)\<close>
      using p1 wlit_upd[OF lenp] unfolding c_def by simp
    have sem: \<open>\<forall>S. S \<subseteq> set t0 \<longrightarrow> WS cs p0 t0 S \<longrightarrow>
        (\<forall>s'. wact cs (length cs) s' \<longrightarrow> lneg (wlit cs p1 s') \<in> insert (lneg w) S \<longrightarrow>
           wlit cs p1 (oth s') \<in> set t1 \<or> s' \<in> set R)\<close>
    proof (intro allI impI)
      fix S s'
      assume S: \<open>S \<subseteq> set t0\<close> \<open>WS cs p0 t0 S\<close> and act: \<open>wact cs (length cs) s'\<close>
        and f: \<open>lneg (wlit cs p1 s') \<in> insert (lneg w) S\<close>
      have ns: \<open>s' \<noteq> ?s\<close>
      proof
        assume \<open>s' = ?s\<close>
        then have \<open>lneg (c ! unat k) \<in> set t\<close> using f wl1 S(1) nwt t0t by auto
        then show False using kt by simp
      qed
      then have f0: \<open>lneg (wlit cs p s') \<in> insert (lneg w) S\<close> using f wl1 by simp
      show \<open>wlit cs p1 (oth s') \<in> set t1 \<or> s' \<in> set R\<close>
      proof (cases \<open>oth s' = ?s\<close>)
        case True
        have \<open>wlit cs p (oth s') \<notin> set t\<close> using True ws wnt by simp
        then show ?thesis using SEMR[OF S act f0 ns] by simp
      next
        case False
        then show ?thesis using SEMR[OF S act f0 ns] wl1 B(7) by simp
      qed
    qed
    have wpp: \<open>\<forall>k' \<le> length t0. WP cs p0 t0 k' \<longrightarrow> WP cs p1 t1 k'\<close>
      using WPP WP_move[OF _ ws wnt kt[unfolded c_def] lenp] p1 B(7) by simp
    have ln1: \<open>length nx1 = length nx\<close> \<open>length h1 = length h\<close>
      using M V(1) mw_m_facts[OF B(6) assms(2) V(2) yl yx] unfolding wl_lists_def by simp_all
    show ?thesis unfolding vinv_def
      by (rule exI[of _ \<open>Ls[?x := K @ R, unat y := ?s # Ls ! unat y]\<close>], rule exI[of _ K], rule exI[of _ R],
          intro conjI) (use M Lx1 V(2,5,6) N1 sem wpp B(8) ln1 in simp_all)
  next
    case C
    have allF: \<open>\<forall>m < length c. m \<noteq> j \<longrightarrow> lit_value_m a (c ! m) = Some False\<close>
      using C(1) ci wF by auto
    have st: \<open>status_m a c None False = Status_Unit (c ! j)\<close> \<open>t1 = t @ [c ! j]\<close>
      using status_one_clause[OF jl allF C(2)] C(7) by auto
    have cjt: \<open>wlit cs p (oth ?s) \<in> set t1\<close> using st(2) cj by simp
    have sem: \<open>\<forall>S. S \<subseteq> set t0 \<longrightarrow> WS cs p0 t0 S \<longrightarrow>
        (\<forall>s'. wact cs (length cs) s' \<longrightarrow> lneg (wlit cs p s') \<in> insert (lneg w) S \<longrightarrow>
           wlit cs p (oth s') \<in> set t1 \<or> s' \<in> set R)\<close>
    proof (intro allI impI)
      fix S s'
      assume S: \<open>S \<subseteq> set t0\<close> \<open>WS cs p0 t0 S\<close> and act: \<open>wact cs (length cs) s'\<close>
        and f: \<open>lneg (wlit cs p s') \<in> insert (lneg w) S\<close>
      show \<open>wlit cs p (oth s') \<in> set t1 \<or> s' \<in> set R\<close>
      proof (cases \<open>s' = ?s\<close>)
        case True
        then show ?thesis using cjt by simp
      next
        case False
        then show ?thesis using SEMR[OF S act f False] st(2) by auto
      qed
    qed
    have lt0: \<open>length t0 \<le> length t\<close> using te by simp
    have wpp: \<open>\<forall>k' \<le> length t0. WP cs p0 t0 k' \<longrightarrow> WP cs p t1 k'\<close>
      using WPP lt0 st(2) by (simp add: WP_def)
    show ?thesis unfolding vinv_def
      by (rule exI[of _ Ls], rule exI[of _ \<open>K @ [?s]\<close>], rule exI[of _ R])
         (use C(3-6) V(1,2) Lx lR N1 sem wpp in auto)
  qed
qed

lemma vinv_conflict:
  assumes \<open>vinv cs x w p0 t0 p nx h t s prev st\<close>
    \<open>vslot_post cs p nx h a t xw sw pw p1 nx1 h1 a1 t1 keep False\<close>
  shows \<open>wl_ok cs p1 nx1 h1 \<and> (\<forall>k \<le> length t0. WP cs p0 t0 k \<longrightarrow> WP cs p1 t1 k)\<close>
proof -
  have e: \<open>p1 = p \<and> nx1 = nx \<and> h1 = h \<and> t1 = t\<close>
    using assms(2) unfolding vslot_post_def Let_def by (auto split: if_splits Status.splits)
  show ?thesis using assms(1) e unfolding vinv_def wl_ok_def by blast
qed

lemma vinv_exit:
  assumes \<open>vinv cs x w p0 t0 p nx h t s prev st\<close> \<open>length nx \<le> s\<close>
  shows \<open>wl_ok cs p nx h \<and> (\<forall>k \<le> length t0. WP cs p0 t0 k \<longrightarrow> WP cs p t k) \<and>
         (\<forall>S. S \<subseteq> set t0 \<longrightarrow> WS cs p0 t0 S \<longrightarrow> WS cs p t (insert (lneg w) S))\<close>
proof -
  obtain Ls K R where V: \<open>wl_lists cs (length cs) p nx h Ls\<close> \<open>lseg nx s R\<close>
    \<open>\<forall>k \<le> length t0. WP cs p0 t0 k \<longrightarrow> WP cs p t k\<close>
    \<open>\<forall>S. S \<subseteq> set t0 \<longrightarrow> WS cs p0 t0 S \<longrightarrow>
        (\<forall>s'. wact cs (length cs) s' \<longrightarrow> lneg (wlit cs p s') \<in> insert (lneg w) S \<longrightarrow>
           wlit cs p (oth s') \<in> set t \<or> s' \<in> set R)\<close>
    using assms(1) unfolding vinv_def by blast
  have \<open>R = []\<close> using V(2) assms(2) by (cases R) auto
  then show ?thesis using V unfolding wl_ok_def WS_def by auto
qed

lemma vinv_bound:
  assumes \<open>vinv cs x w p0 t0 p nx h t s prev st\<close> \<open>s < length nx\<close>
  shows \<open>st < length nx\<close>
proof -
  obtain R where V: \<open>lseg nx s R\<close> \<open>st + length R \<le> length nx\<close>
    using assms(1) unfolding vinv_def by blast
  have \<open>R \<noteq> []\<close> using V(1) assms(2) by auto
  then show ?thesis using V(2) by (cases R) auto
qed

end
