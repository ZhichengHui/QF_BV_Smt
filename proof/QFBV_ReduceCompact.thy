theory QFBV_ReduceCompact
  imports QFBV_Reduce
begin

section \<open>Learned-clause deletion: the compaction\<close>

text \<open>The compaction part of \<^verbatim>\<open>reduce_db\<close> (branch \<^verbatim>\<open>agent/034a756b-reduce\<close>, commit
  \<^verbatim>\<open>7043c52\<close>): the forward loop that builds \<^verbatim>\<open>map\<close> (\<open>mp\<close> here; \<open>map\<close> is a constant of HOL),
  \<^verbatim>\<open>db2\<close>, \<^verbatim>\<open>lbd2\<close> and \<^verbatim>\<open>pos2\<close> from the mask \<^verbatim>\<open>keep\<close>, and the renumbering of the reasons
  \<^verbatim>\<open>rs\<close>. The rebuild of the watch lists in between is not modelled. The facts: the kept clauses
  keep their order (\<open>db2\<close> is \<open>db\<close> filtered by \<open>keep\<close>, so a sub-list of \<open>db\<close> with the same original
  prefix), their LBD and their watched positions, and every renumbered reason points to the same
  clause.\<close>

subsection \<open>Models\<close>

text \<open>The forward loop:
  \<^verbatim>\<open>if keep[c] { map[c] = db2.len(); db2.push(db[c].clone()); pos2.push(pos[2 * c]);\<close>
  \<^verbatim>\<open>pos2.push(pos[2 * c + 1]); if c >= m0 { lbd2.push(lbd[c - m0]); } } c += 1\<close>.\<close>
function compact_loop :: \<open>bool list \<Rightarrow> 'c list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    nat list \<Rightarrow> 'c list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list \<times> 'c list \<times> nat list \<times> nat list\<close> where
  \<open>compact_loop keep db lbd pos m0 m mp db2 lbd2 pos2 c =
    (if c < m then
       (if keep ! c then
          compact_loop keep db lbd pos m0 m (mp[c := length db2]) (db2 @ [db ! c])
            (if m0 \<le> c then lbd2 @ [lbd ! (c - m0)] else lbd2) (pos2 @ [pos ! (2 * c), pos ! (2 * c + 1)]) (c + 1)
        else compact_loop keep db lbd pos m0 m mp db2 lbd2 pos2 (c + 1))
     else (mp, db2, lbd2, pos2))\<close>
  by pat_completeness auto
termination
  by (relation \<open>measure (\<lambda>(_, _, _, _, _, m, _, _, _, _, c). m - c)\<close>) auto

declare compact_loop.simps [simp del]

definition compact_m :: \<open>bool list \<Rightarrow> 'c list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow>
    nat list \<times> 'c list \<times> nat list \<times> nat list\<close> where
  \<open>compact_m keep db lbd pos m0 =
    compact_loop keep db lbd pos m0 (length db) (replicate (length db) 0) [] [] [] 0\<close>

text \<open>The renumbering: \<^verbatim>\<open>if rs[i] < m { rs[i] = map[rs[i]]; } i += 1\<close>.\<close>
function renum_loop :: \<open>nat list \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list\<close> where
  \<open>renum_loop mp m rs i =
    (if i < length rs then renum_loop mp m (if rs ! i < m then rs[i := mp ! (rs ! i)] else rs) (i + 1)
     else rs)\<close>
  by pat_completeness auto
termination
  by (relation \<open>measure (\<lambda>(_, _, rs, i). length rs - i)\<close>) auto

declare renum_loop.simps [simp del]

text \<open>\<^verbatim>\<open>reduce_db\<close> without the watch lists: the new clauses, LBDs, reasons and watched positions,
  and the mask and the map.\<close>
definition reduce_m :: \<open>'c list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow>
    'c list \<times> nat list \<times> nat list \<times> nat list \<times> bool list \<times> nat list\<close> where
  \<open>reduce_m db lbd pos rs m0 =
    (let keep = keep_m (length db) lbd rs m0 in
     case compact_m keep db lbd pos m0 of (mp, db2, lbd2, pos2) \<Rightarrow>
       (db2, lbd2, renum_loop mp (length db) rs 0, pos2, keep, mp))\<close>

subsection \<open>Closed forms\<close>

lemma compact_loop_eq:
  assumes \<open>length mp = m\<close>
    \<open>compact_loop keep db lbd pos m0 m mp db2 lbd2 pos2 c = (mp', db2', lbd2', pos2')\<close>
  shows \<open>db2' = db2 @ map (nth db) (filter (nth keep) [c..<m]) \<and>
    lbd2' = lbd2 @ map (\<lambda>j. lbd ! (j - m0)) (filter (\<lambda>j. m0 \<le> j) (filter (nth keep) [c..<m])) \<and>
    pos2' = pos2 @ concat (map (\<lambda>j. [pos ! (2 * j), pos ! (2 * j + 1)]) (filter (nth keep) [c..<m])) \<and>
    length mp' = m \<and>
    (\<forall>j. c \<le> j \<and> j < m \<and> keep ! j \<longrightarrow> mp' ! j = length db2 + length (filter (nth keep) [c..<j])) \<and>
    (\<forall>j. \<not> (c \<le> j \<and> j < m \<and> keep ! j) \<longrightarrow> mp' ! j = mp ! j)\<close>
  using assms
proof (induction keep db lbd pos m0 m mp db2 lbd2 pos2 c rule: compact_loop.induct)
  case (1 keep db lbd pos m0 m mp db2 lbd2 pos2 c)
  show ?case
  proof (cases \<open>c < m\<close>)
    case True
    have u: \<open>[c..<m] = c # [c + 1..<m]\<close> using True upt_conv_Cons by simp
    have uj: \<open>[c..<j] = c # [c + 1..<j]\<close> if \<open>c < j\<close> for j using that upt_conv_Cons by simp
    show ?thesis
    proof (cases \<open>keep ! c\<close>)
      case k: True
      have e: \<open>compact_loop keep db lbd pos m0 m mp db2 lbd2 pos2 c =
          compact_loop keep db lbd pos m0 m (mp[c := length db2]) (db2 @ [db ! c])
            (if m0 \<le> c then lbd2 @ [lbd ! (c - m0)] else lbd2) (pos2 @ [pos ! (2 * c), pos ! (2 * c + 1)]) (c + 1)\<close>
        by (subst compact_loop.simps) (simp only: if_P[OF True] if_P[OF k] if_True)
      note ih = "1.IH"(1)[OF True k _ "1.prems"(2)[unfolded e]]
      have ih': \<open>db2' = (db2 @ [db ! c]) @ map (nth db) (filter (nth keep) [c + 1..<m]) \<and>
          lbd2' = (if m0 \<le> c then lbd2 @ [lbd ! (c - m0)] else lbd2) @
            map (\<lambda>j. lbd ! (j - m0)) (filter (\<lambda>j. m0 \<le> j) (filter (nth keep) [c + 1..<m])) \<and>
          pos2' = (pos2 @ [pos ! (2 * c), pos ! (2 * c + 1)]) @
            concat (map (\<lambda>j. [pos ! (2 * j), pos ! (2 * j + 1)]) (filter (nth keep) [c + 1..<m])) \<and>
          length mp' = m \<and>
          (\<forall>j. c + 1 \<le> j \<and> j < m \<and> keep ! j \<longrightarrow>
            mp' ! j = length (db2 @ [db ! c]) + length (filter (nth keep) [c + 1..<j])) \<and>
          (\<forall>j. \<not> (c + 1 \<le> j \<and> j < m \<and> keep ! j) \<longrightarrow> mp' ! j = mp[c := length db2] ! j)\<close>
        using ih "1.prems"(1) by simp
      show ?thesis
      proof (intro conjI allI impI)
        fix j assume j: \<open>c \<le> j \<and> j < m \<and> keep ! j\<close>
        show \<open>mp' ! j = length db2 + length (filter (nth keep) [c..<j])\<close>
        proof (cases \<open>j = c\<close>)
          case True
          then show ?thesis using ih' True "1.prems"(1) \<open>c < m\<close> by simp
        next
          case False
          then show ?thesis using ih' j k uj[of j] by simp
        qed
      next
        fix j assume j: \<open>\<not> (c \<le> j \<and> j < m \<and> keep ! j)\<close>
        then have \<open>j \<noteq> c\<close> using k True by auto
        then show \<open>mp' ! j = mp ! j\<close> using ih' j by simp
      qed (use ih' u k in simp_all)
    next
      case n: False
      have e: \<open>compact_loop keep db lbd pos m0 m mp db2 lbd2 pos2 c =
          compact_loop keep db lbd pos m0 m mp db2 lbd2 pos2 (c + 1)\<close>
        by (subst compact_loop.simps) (simp only: if_P[OF True] if_not_P[OF n] if_True)
      note ih = "1.IH"(2)[OF True n "1.prems"(1) "1.prems"(2)[unfolded e]]
      show ?thesis
      proof (intro conjI allI impI)
        fix j assume j: \<open>c \<le> j \<and> j < m \<and> keep ! j\<close>
        then have \<open>c < j\<close> using n by (cases \<open>j = c\<close>) auto
        then show \<open>mp' ! j = length db2 + length (filter (nth keep) [c..<j])\<close>
          using ih j n uj[of j] by simp
      next
        fix j assume j: \<open>\<not> (c \<le> j \<and> j < m \<and> keep ! j)\<close>
        then show \<open>mp' ! j = mp ! j\<close> using ih by simp
      qed (use ih u n in simp_all)
    qed
  next
    case False
    then show ?thesis using "1.prems" by (subst (asm) compact_loop.simps) auto
  qed
qed

lemma renum_loop_nth:
  \<open>length (renum_loop mp m rs i) = length rs \<and>
    (\<forall>j < length rs. renum_loop mp m rs i ! j = (if i \<le> j \<and> rs ! j < m then mp ! (rs ! j) else rs ! j))\<close>
proof (induction mp m rs i rule: renum_loop.induct)
  case (1 mp m rs i)
  show ?case
  proof (cases \<open>i < length rs\<close>)
    case True
    have e: \<open>renum_loop mp m rs i = renum_loop mp m (if rs ! i < m then rs[i := mp ! (rs ! i)] else rs) (i + 1)\<close>
      using True by (subst renum_loop.simps) simp
    show ?thesis using "1.IH"[OF True] True unfolding e
      by (auto simp: nth_list_update) (metis le_antisym not_less_eq_eq)
  next
    case False
    then show ?thesis using renum_loop.simps[of mp m rs i] by simp
  qed
qed

subsection \<open>Facts of the compaction\<close>

lemma nth_filter_upt:
  assumes \<open>a \<le> c\<close> \<open>c < m\<close> \<open>P c\<close>
  shows \<open>length (filter P [a..<c]) < length (filter P [a..<m])\<close>
    \<open>filter P [a..<m] ! length (filter P [a..<c]) = c\<close>
proof -
  have \<open>[a..<m] = [a..<c] @ c # [c + 1..<m]\<close>
    using assms(1,2) upt_add_eq_append[of a c \<open>m - c\<close>] upt_conv_Cons[of c m] by simp
  then have \<open>filter P [a..<m] = filter P [a..<c] @ c # filter P [c + 1..<m]\<close> using assms(3) by simp
  then show \<open>length (filter P [a..<c]) < length (filter P [a..<m])\<close>
    \<open>filter P [a..<m] ! length (filter P [a..<c]) = c\<close> by simp_all
qed

lemma nth_concat_pairs:
  \<open>k < length xs \<Longrightarrow> i < 2 \<Longrightarrow>
    concat (map (\<lambda>j. [f j, g j]) xs) ! (2 * k + i) = [f (xs ! k), g (xs ! k)] ! i\<close>
proof (induction xs arbitrary: k)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases k)
    case 0
    then show ?thesis using Cons.prems by (cases i) auto
  next
    case (Suc k')
    then show ?thesis using Cons by (simp add: nth_append numeral_2_eq_2)
  qed
qed

lemma length_concat_pairs: \<open>length (concat (map (\<lambda>j. [f j, g j]) xs)) = 2 * length xs\<close>
  by (induction xs) auto

text \<open>The facts of the compaction, for a mask \<open>keep\<close> of the length of \<open>db\<close>; those about the
  original prefix also need that it keeps the clauses before \<open>m0 \<le> length db\<close>.\<close>
lemma compact_m_props:
  assumes \<open>compact_m keep db lbd pos m0 = (mp, db2, lbd2, pos2)\<close> \<open>length keep = length db\<close>
  shows \<open>db2 = map (nth db) (filter (nth keep) [0..<length db])\<close> \<open>subseq db2 db\<close>
    \<open>length mp = length db\<close> \<open>length pos2 = 2 * length db2\<close>
    \<open>c < length db \<Longrightarrow> keep ! c \<Longrightarrow> mp ! c < length db2\<close>
    \<open>c < length db \<Longrightarrow> keep ! c \<Longrightarrow> db2 ! (mp ! c) = db ! c\<close>
    \<open>c < length db \<Longrightarrow> keep ! c \<Longrightarrow> i < 2 \<Longrightarrow> pos2 ! (2 * mp ! c + i) = pos ! (2 * c + i)\<close>
    \<open>\<forall>c < m0. keep ! c \<Longrightarrow> m0 \<le> c \<Longrightarrow> c < length db \<Longrightarrow> keep ! c \<Longrightarrow>
      m0 \<le> mp ! c \<and> lbd2 ! (mp ! c - m0) = lbd ! (c - m0)\<close>
    \<open>m0 \<le> length db \<Longrightarrow> \<forall>c < m0. keep ! c \<Longrightarrow> take m0 db2 = take m0 db\<close>
    \<open>m0 \<le> length db \<Longrightarrow> \<forall>c < m0. keep ! c \<Longrightarrow> length lbd2 = length db2 - m0\<close>
proof -
  let ?m = \<open>length db\<close>
  let ?ks = \<open>filter (nth keep) [0..<?m]\<close>
  note r = compact_loop_eq[OF _ assms(1)[unfolded compact_m_def], simplified]
  show db2: \<open>db2 = map (nth db) ?ks\<close> using r by simp
  have \<open>subseq (map (nth db) ?ks) (map (nth db) [0..<?m])\<close> by (intro subseq_map subseq_filter_left)
  then show \<open>subseq db2 db\<close> using db2 by (simp add: map_nth)
  show \<open>length mp = ?m\<close> using r by simp
  show \<open>length pos2 = 2 * length db2\<close> using r db2 by (simp add: length_concat_pairs)
  have mpc: \<open>mp ! c = length (filter (nth keep) [0..<c])\<close> if \<open>c < ?m\<close> \<open>keep ! c\<close> for c
    using r that by simp
  note nf = nth_filter_upt[of 0 c ?m \<open>nth keep\<close>]
  show \<open>c < ?m \<Longrightarrow> keep ! c \<Longrightarrow> mp ! c < length db2\<close> using mpc nf(1) db2 by simp
  show \<open>c < ?m \<Longrightarrow> keep ! c \<Longrightarrow> db2 ! (mp ! c) = db ! c\<close> using mpc nf db2 by simp
  show \<open>c < ?m \<Longrightarrow> keep ! c \<Longrightarrow> i < 2 \<Longrightarrow> pos2 ! (2 * mp ! c + i) = pos ! (2 * c + i)\<close>
    using r mpc nf nth_concat_pairs[of \<open>mp ! c\<close> ?ks i \<open>\<lambda>j. pos ! (2 * j)\<close> \<open>\<lambda>j. pos ! (2 * j + 1)\<close>]
    by (cases i) (auto simp: numeral_2_eq_2 less_Suc_eq)
  have fm: \<open>filter (\<lambda>j. m0 \<le> j) (filter (nth keep) [0..<n]) = filter (nth keep) [m0..<n]\<close> for n
  proof -
    have \<open>filter (\<lambda>j. m0 \<le> j) (filter (nth keep) [0..<n]) = filter (nth keep) (filter (\<lambda>j. m0 \<le> j) [0..<n])\<close>
      by (simp add: conj_commute)
    also have \<open>filter (\<lambda>j. m0 \<le> j) [0..<n] = [m0..<n]\<close>
      by (induction n) auto
    finally show ?thesis .
  qed
  have pre: \<open>filter (nth keep) [0..<n] = [0..<m0] @ filter (nth keep) [m0..<n]\<close>
    if \<open>m0 \<le> n\<close> \<open>\<forall>c < m0. keep ! c\<close> for n
  proof -
    have \<open>[0..<n] = [0..<m0] @ [m0..<n]\<close> using that(1) by (metis le_add_diff_inverse upt_add_eq_append zero_le)
    moreover have \<open>filter (nth keep) [0..<m0] = [0..<m0]\<close> using that(2) by (simp add: filter_id_conv)
    ultimately show ?thesis by simp
  qed
  have lbd2: \<open>lbd2 = map (\<lambda>j. lbd ! (j - m0)) (filter (nth keep) [m0..<?m])\<close> using r fm by simp
  show \<open>m0 \<le> mp ! c \<and> lbd2 ! (mp ! c - m0) = lbd ! (c - m0)\<close>
    if \<open>\<forall>c < m0. keep ! c\<close> \<open>m0 \<le> c\<close> \<open>c < ?m\<close> \<open>keep ! c\<close>
  proof -
    have \<open>mp ! c = m0 + length (filter (nth keep) [m0..<c])\<close> using mpc[OF that(3,4)] pre[OF that(2,1)] by simp
    then show ?thesis using nth_filter_upt[OF that(2,3), of \<open>nth keep\<close>] that(4) lbd2 by simp
  qed
  show \<open>take m0 db2 = take m0 db\<close> if \<open>m0 \<le> ?m\<close> \<open>\<forall>c < m0. keep ! c\<close>
  proof -
    have \<open>take m0 db2 = map (nth db) [0..<m0]\<close> using pre[OF that] db2 by (simp add: take_map)
    also have \<open>\<dots> = take m0 db\<close> using that(1) by (intro nth_equalityI) auto
    finally show ?thesis .
  qed
  show \<open>m0 \<le> ?m \<Longrightarrow> \<forall>c < m0. keep ! c \<Longrightarrow> length lbd2 = length db2 - m0\<close>
    using pre db2 lbd2 by simp
qed

subsection \<open>\<^verbatim>\<open>reduce_db\<close> without the watch lists\<close>

text \<open>The facts for the contract of \<^verbatim>\<open>dpll\<close>, for \<open>m0 \<le> length db\<close> only: the original
  clauses are the unchanged prefix, the kept clauses a sub-list of \<open>db\<close>; every clause before
  \<open>m0\<close>, every reason and every clause of LBD at most 2 is kept, with its clause, its LBD and its
  watched positions at index \<open>mp ! c\<close>; and every reason \<open>rs ! j < length db\<close> is renumbered to
  the index of the same clause (the others, such as \<^verbatim>\<open>usize::MAX\<close>, stay). The number of
  deleted clauses is the subject of \<open>sel_m_props\<close>.\<close>
lemma reduce_m_props:
  assumes \<open>reduce_m db lbd pos rs m0 = (db2, lbd2, rs2, pos2, keep, mp)\<close> \<open>m0 \<le> length db\<close>
  shows \<open>keep = keep_m (length db) lbd rs m0\<close> \<open>length keep = length db\<close>
    \<open>\<forall>c < length db. c < m0 \<or> c \<in> set rs \<or> lbd ! (c - m0) \<le> 2 \<longrightarrow> keep ! c\<close>
    \<open>db2 = map (nth db) (filter (nth keep) [0..<length db])\<close> \<open>subseq db2 db\<close> \<open>length db2 \<le> length db\<close>
    \<open>take m0 db2 = take m0 db\<close> \<open>m0 \<le> length db2\<close>
    \<open>length lbd2 = length db2 - m0\<close> \<open>length pos2 = 2 * length db2\<close>
    \<open>c < length db \<Longrightarrow> keep ! c \<Longrightarrow> mp ! c < length db2 \<and> db2 ! (mp ! c) = db ! c \<and>
      (\<forall>i < 2. pos2 ! (2 * mp ! c + i) = pos ! (2 * c + i))\<close>
    \<open>m0 \<le> c \<Longrightarrow> c < length db \<Longrightarrow> keep ! c \<Longrightarrow> m0 \<le> mp ! c \<and> lbd2 ! (mp ! c - m0) = lbd ! (c - m0)\<close>
    \<open>length rs2 = length rs\<close>
    \<open>j < length rs \<Longrightarrow> rs ! j < length db \<Longrightarrow> rs2 ! j = mp ! (rs ! j) \<and> rs2 ! j < length db2 \<and>
      db2 ! (rs2 ! j) = db ! (rs ! j) \<and> (\<forall>i < 2. pos2 ! (2 * rs2 ! j + i) = pos ! (2 * rs ! j + i))\<close>
    \<open>j < length rs \<Longrightarrow> \<not> rs ! j < length db \<Longrightarrow> rs2 ! j = rs ! j\<close>
proof -
  let ?m = \<open>length db\<close>
  have k: \<open>keep = keep_m ?m lbd rs m0\<close> and c: \<open>compact_m keep db lbd pos m0 = (mp, db2, lbd2, pos2)\<close>
    and rs2: \<open>rs2 = renum_loop mp ?m rs 0\<close>
    using assms(1) by (auto simp: reduce_m_def Let_def split: prod.splits)
  show \<open>keep = keep_m ?m lbd rs m0\<close> by (rule k)
  show lk: \<open>length keep = ?m\<close> using keep_m_props(1) k by simp
  show kept: \<open>\<forall>c < ?m. c < m0 \<or> c \<in> set rs \<or> lbd ! (c - m0) \<le> 2 \<longrightarrow> keep ! c\<close>
    using keep_m_props(2) k by simp
  have k0: \<open>\<forall>c < m0. keep ! c\<close> using kept assms(2) by simp
  note cp = compact_m_props[OF c lk]
  show \<open>db2 = map (nth db) (filter (nth keep) [0..<?m])\<close> \<open>subseq db2 db\<close> using cp by simp_all
  then show \<open>length db2 \<le> ?m\<close> using list_emb_length by blast
  show t: \<open>take m0 db2 = take m0 db\<close> using cp(9)[OF assms(2) k0] .
  then show \<open>m0 \<le> length db2\<close> using assms(2) by (metis length_take min.absorb2 min.bounded_iff nat_le_linear)
  show \<open>length lbd2 = length db2 - m0\<close> \<open>length pos2 = 2 * length db2\<close>
    using cp(4) cp(10)[OF assms(2) k0] by simp_all
  show kc: \<open>mp ! c < length db2 \<and> db2 ! (mp ! c) = db ! c \<and> (\<forall>i < 2. pos2 ! (2 * mp ! c + i) = pos ! (2 * c + i))\<close>
    if \<open>c < ?m\<close> \<open>keep ! c\<close> for c
    using cp(5-7) that by simp
  show \<open>m0 \<le> c \<Longrightarrow> c < ?m \<Longrightarrow> keep ! c \<Longrightarrow> m0 \<le> mp ! c \<and> lbd2 ! (mp ! c - m0) = lbd ! (c - m0)\<close>
    using cp(8)[OF k0] by simp
  note rn = renum_loop_nth[of mp ?m rs 0, folded rs2]
  show \<open>length rs2 = length rs\<close> using rn by simp
  show \<open>rs2 ! j = mp ! (rs ! j) \<and> rs2 ! j < length db2 \<and> db2 ! (rs2 ! j) = db ! (rs ! j) \<and>
      (\<forall>i < 2. pos2 ! (2 * rs2 ! j + i) = pos ! (2 * rs ! j + i))\<close>
    if \<open>j < length rs\<close> \<open>rs ! j < ?m\<close> for j
  proof -
    have \<open>keep ! (rs ! j)\<close> using kept that by simp
    then show ?thesis using kc[OF that(2)] rn that by simp
  qed
  show \<open>j < length rs \<Longrightarrow> \<not> rs ! j < ?m \<Longrightarrow> rs2 ! j = rs ! j\<close> using rn by simp
qed

end
