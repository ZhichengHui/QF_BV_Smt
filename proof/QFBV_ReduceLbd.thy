theory QFBV_ReduceLbd
  imports QFBV_Reduce
begin

section \<open>Learned-clause deletion: the LBD update in the analysis\<close>

text \<open>A functional model of \<^verbatim>\<open>update_lbd\<close> of the prototype commit \<^verbatim>\<open>a01c02d\<close> (branch
  \<^verbatim>\<open>agent/17f61c03-tier\<close>, Glucose's LBD update), statement by statement, on \<open>nat\<close>s and lists, over
  the model \<^const>\<open>clause_lbd_m\<close> of \<^verbatim>\<open>clause_lbd\<close>. As there, a clause is the list of its
  variables, so \<open>db\<close> is a \<open>nat list list\<close>; the pair \<^verbatim>\<open>let (b, m2) = clause_lbd(..)\<close> is
  \<open>fst r\<close>, \<open>snd r\<close>. The facts are the ones the contract of \<^verbatim>\<open>dpll\<close> needs: \<open>lbd\<close> and
  \<open>mark\<close> keep their lengths; only the entries of learned clauses of LBD above 2 among \<open>used\<close>
  change, and a changed entry decreases by more than one to the present LBD of the clause, at most
  its number of literals; every stamp of \<open>mark\<close> stays at most \<open>st\<close>, so every new stamp is fresh;
  and \<open>st\<close> grows by at most \<open>length used\<close>. With the increment \<^verbatim>\<open>stamp += 1\<close> before the
  \<^verbatim>\<open>clause_lbd\<close> of the learned clause in \<^verbatim>\<open>dpll\<close>, a conflict uses at most \<open>1 + length used\<close>
  stamps.\<close>

text \<open>The loop: \<^verbatim>\<open>let c = used[k]; if c >= m0 && c - m0 < lbd.len() && lbd[c - m0] > 2 {\<close>
  \<^verbatim>\<open>st += 1; let (b, m2) = clause_lbd(&db[c], tp, lim, mark, st); mark = m2;\<close>
  \<^verbatim>\<open>if b + 1 < lbd[c - m0] { lbd[c - m0] = b; } } k += 1\<close>, while \<^verbatim>\<open>k < used.len()\<close>; from
  \<^verbatim>\<open>k = 0\<close>.\<close>
function upd_loop :: \<open>nat list list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<times> nat list \<times> nat\<close> where
  \<open>upd_loop db used tp lim lbd mark st m0 k =
    (if k < length used then
       (let c = used ! k in
        if m0 \<le> c \<and> c - m0 < length lbd \<and> 2 < lbd ! (c - m0) then
          (let r = clause_lbd_m (db ! c) tp lim mark (st + 1) in
           upd_loop db used tp lim (if fst r + 1 < lbd ! (c - m0) then lbd[c - m0 := fst r] else lbd)
             (snd r) (st + 1) m0 (k + 1))
        else upd_loop db used tp lim lbd mark st m0 (k + 1))
     else (lbd, mark, st))\<close>
  by pat_completeness auto
termination
  by (relation \<open>measure (\<lambda>(_, used, _, _, _, _, _, _, k). length used - k)\<close>) auto

declare upd_loop.simps [simp del]

definition update_lbd_m :: \<open>nat list list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> nat list \<times> nat list \<times> nat\<close> where
  \<open>update_lbd_m db used tp lim lbd mark st m0 = upd_loop db used tp lim lbd mark st m0 0\<close>

text \<open>The index of \<^verbatim>\<open>db[c]\<close> is in range by the guard alone, once \<open>lbd\<close> has an entry for each
  learned clause and no more (\<open>m0 + length lbd \<le> length db\<close>, which \<^verbatim>\<open>update_lbd\<close> keeps since
  it keeps \<open>length lbd\<close>).\<close>
lemma upd_guard_bound:
  \<open>m0 \<le> c \<Longrightarrow> c - m0 < length lbd \<Longrightarrow> m0 + length lbd \<le> length db \<Longrightarrow> c < length db\<close>
  by linarith

text \<open>\<^verbatim>\<open>clause_lbd\<close> writes only the stamp \<open>st\<close> into \<open>mark\<close>.\<close>
lemma lbd_loop_set:
  \<open>lbd_loop vs tp lim mark st d k = (d', mark') \<Longrightarrow> set mark' \<subseteq> insert st (set mark)\<close>
proof (induction vs tp lim mark st d k rule: lbd_loop.induct)
  case (1 vs tp lim mark st d k)
  show ?case
  proof (cases \<open>k < length vs\<close>)
    case True
    define v where \<open>v = level_at_m lim (tp ! (vs ! k))\<close>
    show ?thesis
    proof (cases \<open>v < length mark \<and> mark ! v \<noteq> st\<close>)
      case new: True
      have e: \<open>lbd_loop vs tp lim mark st d k = lbd_loop vs tp lim (mark[v := st]) st (d + 1) (k + 1)\<close>
        using True new by (subst lbd_loop.simps) (simp add: v_def Let_def)
      show ?thesis
        using "1.IH"(1)[OF True v_def new "1.prems"[unfolded e]] set_update_subset_insert[of mark v st] by auto
    next
      case old: False
      have e: \<open>lbd_loop vs tp lim mark st d k = lbd_loop vs tp lim mark st d (k + 1)\<close>
        using True old[unfolded v_def] by (subst lbd_loop.simps) (auto simp: Let_def)
      show ?thesis using "1.IH"(2)[OF True v_def old "1.prems"[unfolded e]] .
    qed
  next
    case False
    then show ?thesis using "1.prems" by (subst (asm) lbd_loop.simps) auto
  qed
qed

lemma clause_lbd_m_set:
  \<open>clause_lbd_m vs tp lim mark st = (d, mark') \<Longrightarrow> set mark' \<subseteq> insert st (set mark)\<close>
  using lbd_loop_set by (simp add: clause_lbd_m_def)

text \<open>The present LBD of clause \<open>c\<close>, as \<^verbatim>\<open>clause_lbd\<close> computes it with a fresh stamp and a
  \<open>mark\<close> of length \<open>n\<close>.\<close>
definition cur_lbd :: \<open>nat list list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>cur_lbd db tp lim n c = card (lvls tp lim n (db ! c))\<close>

text \<open>The invariant: entry \<open>i\<close> is the original one, or it has been lowered to the present LBD,
  by more than one, from an original value above 2, for a clause among the first \<open>k\<close> of \<open>used\<close>.\<close>
definition upd_ok :: \<open>nat list list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow>
    nat list \<Rightarrow> bool\<close> where
  \<open>upd_ok db tp lim us n m0 lbd0 lbd \<longleftrightarrow> length lbd = length lbd0 \<and>
    (\<forall>i < length lbd0. lbd ! i = lbd0 ! i \<or>
      (lbd ! i = cur_lbd db tp lim n (m0 + i) \<and> cur_lbd db tp lim n (m0 + i) + 1 < lbd0 ! i \<and>
       2 < lbd0 ! i \<and> m0 + i \<in> set us))\<close>

lemma upd_loop_inv:
  assumes \<open>\<forall>x \<in> set mark. x \<le> st\<close> \<open>length mark = n\<close> \<open>k \<le> length used\<close>
    \<open>upd_ok db tp lim (take k used) n m0 lbd0 lbd\<close>
    \<open>upd_loop db used tp lim lbd mark st m0 k = (lbd', mark', st')\<close>
  shows \<open>upd_ok db tp lim used n m0 lbd0 lbd' \<and> length mark' = n \<and> (\<forall>x \<in> set mark'. x \<le> st') \<and>
    st \<le> st' \<and> st' \<le> st + (length used - k)\<close>
  using assms
proof (induction db used tp lim lbd mark st m0 k rule: upd_loop.induct)
  case (1 db used tp lim lbd mark st m0 k)
  show ?case
  proof (cases \<open>k < length used\<close>)
    case True
    obtain c where c: \<open>used ! k = c\<close> by simp
    have tk: \<open>set (take k used) \<subseteq> set (take (k + 1) used)\<close> \<open>c \<in> set (take (k + 1) used)\<close>
      using True c by (auto simp: take_Suc_conv_app_nth set_take_subset_set_take)
    have mono: \<open>upd_ok db tp lim (take (k + 1) used) n m0 lbd0 lbd\<close>
      using "1.prems"(4) tk(1) by (fastforce simp: upd_ok_def)
    show ?thesis
    proof (cases \<open>m0 \<le> c \<and> c - m0 < length lbd \<and> 2 < lbd ! (c - m0)\<close>)
      case g: True
      obtain b m2 where r: \<open>clause_lbd_m (db ! c) tp lim mark (st + 1) = (b, m2)\<close> by (metis prod.exhaust)
      have fr: \<open>st + 1 \<notin> set mark\<close> using "1.prems"(1) by auto
      note cl = clause_lbd_m_props[OF fr r]
      have b: \<open>b = cur_lbd db tp lim n c\<close> using cl(1) "1.prems"(2) by (simp add: cur_lbd_def)
      have m2: \<open>\<forall>x \<in> set m2. x \<le> st + 1\<close> \<open>length m2 = n\<close>
        using cl(2) "1.prems"(1,2) clause_lbd_m_set[OF r] by (auto dest!: subsetD)
      define lbd1 where \<open>lbd1 = (if b + 1 < lbd ! (c - m0) then lbd[c - m0 := b] else lbd)\<close>
      have ok1: \<open>upd_ok db tp lim (take (k + 1) used) n m0 lbd0 lbd1\<close>
      proof (cases \<open>b + 1 < lbd ! (c - m0)\<close>)
        case u: True
        have i: \<open>m0 + (c - m0) = c\<close> using g by simp
        have l: \<open>length lbd = length lbd0\<close> using mono by (simp add: upd_ok_def)
        have \<open>lbd ! (c - m0) = lbd0 ! (c - m0)\<close> using mono g u b i l by (auto simp: upd_ok_def)
        then show ?thesis using mono g u b i l tk(2) by (auto simp: upd_ok_def lbd1_def nth_list_update)
      next
        case False
        then show ?thesis using mono by (simp add: lbd1_def)
      qed
      have e: \<open>upd_loop db used tp lim lbd mark st m0 k = upd_loop db used tp lim lbd1 m2 (st + 1) m0 (k + 1)\<close>
        by (subst upd_loop.simps) (simp only: Let_def c r if_P[OF True] if_P[OF g] fst_conv snd_conv lbd1_def)
      have ih: \<open>upd_ok db tp lim used n m0 lbd0 lbd' \<and> length mark' = n \<and> (\<forall>x \<in> set mark'. x \<le> st') \<and>
          st + 1 \<le> st' \<and> st' \<le> st + 1 + (length used - (k + 1))\<close>
        using "1.IH"(1)[OF True c[symmetric] g r[symmetric], unfolded fst_conv snd_conv, folded lbd1_def]
          m2 ok1 "1.prems"(5)[unfolded e] True by simp
      then show ?thesis using True by auto
    next
      case n: False
      have e: \<open>upd_loop db used tp lim lbd mark st m0 k = upd_loop db used tp lim lbd mark st m0 (k + 1)\<close>
        by (subst upd_loop.simps) (simp only: Let_def c if_P[OF True] if_not_P[OF n])
      have ih: \<open>upd_ok db tp lim used n m0 lbd0 lbd' \<and> length mark' = n \<and> (\<forall>x \<in> set mark'. x \<le> st') \<and>
          st \<le> st' \<and> st' \<le> st + (length used - (k + 1))\<close>
        using "1.IH"(2)[OF True c[symmetric] n "1.prems"(1,2) _ mono "1.prems"(5)[unfolded e]] True by simp
      then show ?thesis by auto
    qed
  next
    case False
    then have \<open>lbd' = lbd\<close> \<open>mark' = mark\<close> \<open>st' = st\<close> \<open>k = length used\<close>
      using "1.prems"(3,5) by (subst (asm) upd_loop.simps; simp)+
    then show ?thesis using "1.prems"(1,2,4) by simp
  qed
qed

lemma card_lvls_pos:
  \<open>x \<in> set vs \<Longrightarrow> level_at_m lim (tp ! x) < n \<Longrightarrow> 0 < card (lvls tp lim n vs)\<close>
  unfolding lvls_def by (subst card_gt_0_iff) auto

text \<open>The facts of \<^verbatim>\<open>update_lbd\<close>, for a \<open>mark\<close> whose stamps are at most \<open>st\<close> (as the stamps
  only grow, every one used so far). A lowered entry is at least 1 when some literal of the clause
  has a level below \<open>length mark\<close> (\<open>card_lvls_pos\<close>).\<close>
lemma update_lbd_m_props:
  assumes \<open>\<forall>x \<in> set mark. x \<le> st\<close> \<open>update_lbd_m db used tp lim lbd mark st m0 = (lbd', mark', st')\<close>
  shows \<open>length lbd' = length lbd\<close> \<open>length mark' = length mark\<close> \<open>\<forall>x \<in> set mark'. x \<le> st'\<close>
    \<open>st \<le> st'\<close> \<open>st' \<le> st + length used\<close>
    \<open>\<forall>i < length lbd. lbd' ! i \<le> lbd ! i\<close>
    \<open>i < length lbd \<Longrightarrow> lbd' ! i \<noteq> lbd ! i \<Longrightarrow> m0 + i \<in> set used \<and> 2 < lbd ! i \<and>
      lbd' ! i + 1 < lbd ! i \<and> lbd' ! i = card (lvls tp lim (length mark) (db ! (m0 + i))) \<and>
      lbd' ! i \<le> length (db ! (m0 + i))\<close>
proof -
  have ok0: \<open>upd_ok db tp lim (take 0 used) (length mark) m0 lbd lbd\<close> by (simp add: upd_ok_def)
  note r = upd_loop_inv[OF assms(1) refl le0 ok0 assms(2)[unfolded update_lbd_m_def]]
  show \<open>length lbd' = length lbd\<close> \<open>length mark' = length mark\<close> \<open>\<forall>x \<in> set mark'. x \<le> st'\<close>
    \<open>st \<le> st'\<close> \<open>st' \<le> st + length used\<close>
    using r by (simp_all add: upd_ok_def)
  show \<open>\<forall>i < length lbd. lbd' ! i \<le> lbd ! i\<close> using r by (fastforce simp: upd_ok_def)
  show \<open>m0 + i \<in> set used \<and> 2 < lbd ! i \<and> lbd' ! i + 1 < lbd ! i \<and>
      lbd' ! i = card (lvls tp lim (length mark) (db ! (m0 + i))) \<and> lbd' ! i \<le> length (db ! (m0 + i))\<close>
    if \<open>i < length lbd\<close> \<open>lbd' ! i \<noteq> lbd ! i\<close>
    using r that lvls_card_le[of tp lim \<open>length mark\<close> \<open>db ! (m0 + i)\<close>] by (auto simp: upd_ok_def cur_lbd_def)
qed

text \<open>The lengths alone, without the freshness of the stamps in \<open>mark\<close>: they hold also when the
  stamp wraps around, which breaks the hypothesis of \<open>update_lbd_m_props\<close>.\<close>
lemma lbd_loop_length:
  \<open>lbd_loop vs tp lim mark st d k = (d', mark') \<Longrightarrow> length mark' = length mark\<close>
proof (induction vs tp lim mark st d k rule: lbd_loop.induct)
  case (1 vs tp lim mark st d k)
  then show ?case by (subst (asm) (2) lbd_loop.simps) (auto simp: Let_def split: if_splits)
qed

lemma upd_loop_length:
  \<open>upd_loop db used tp lim lbd mark st m0 k = (lbd', mark', st') \<Longrightarrow>
    length lbd' = length lbd \<and> length mark' = length mark\<close>
proof (induction db used tp lim lbd mark st m0 k rule: upd_loop.induct)
  case (1 db used tp lim lbd mark st m0 k)
  show ?case
  proof (cases \<open>k < length used\<close>)
    case True
    show ?thesis
    proof (cases \<open>m0 \<le> used ! k \<and> used ! k - m0 < length lbd \<and> 2 < lbd ! (used ! k - m0)\<close>)
      case g: True
      obtain b m2 where r: \<open>clause_lbd_m (db ! (used ! k)) tp lim mark (st + 1) = (b, m2)\<close> by (metis prod.exhaust)
      have lm: \<open>length m2 = length mark\<close> using r lbd_loop_length by (simp add: clause_lbd_m_def)
      have e: \<open>upd_loop db used tp lim lbd mark st m0 k = upd_loop db used tp lim (if b + 1 < lbd ! (used ! k - m0) then lbd[used ! k - m0 := b] else lbd) m2 (st + 1) m0 (k + 1)\<close>
        by (subst upd_loop.simps) (simp only: Let_def r if_P[OF True] if_P[OF g] fst_conv snd_conv)
      show ?thesis using "1.IH"(1)[OF True refl g r[symmetric], unfolded fst_conv snd_conv, OF "1.prems"[unfolded e]] lm
        by (cases \<open>b + 1 < lbd ! (used ! k - m0)\<close>) auto
    next
      case n: False
      have e: \<open>upd_loop db used tp lim lbd mark st m0 k = upd_loop db used tp lim lbd mark st m0 (k + 1)\<close>
        by (subst upd_loop.simps) (simp only: Let_def if_P[OF True] if_not_P[OF n])
      show ?thesis using "1.IH"(2)[OF True refl n "1.prems"[unfolded e]] .
    qed
  next
    case False
    then show ?thesis using "1.prems" by (subst (asm) upd_loop.simps) auto
  qed
qed

lemma update_lbd_m_length:
  \<open>update_lbd_m db used tp lim lbd mark st m0 = (lbd', mark', st') \<Longrightarrow>
    length lbd' = length lbd \<and> length mark' = length mark\<close>
  unfolding update_lbd_m_def by (rule upd_loop_length)

end
