theory QFBV_Heap
  imports Main
begin

section \<open>The decision heap: the pure model\<close>

text \<open>Functional models of the decision heap of \<^verbatim>\<open>dpll\<close> (\<^verbatim>\<open>heap_up\<close>, \<^verbatim>\<open>heap_down\<close>,
  \<^verbatim>\<open>heap_rebuild\<close>, \<^verbatim>\<open>heap_insert\<close>, \<^verbatim>\<open>heap_pop\<close>, \<^verbatim>\<open>heap_pick\<close>, \<^verbatim>\<open>heap_back\<close>,
  \<^verbatim>\<open>heap_bumped\<close>), statement by statement, on \<open>nat list\<close>s: \<open>heap\<close> lists variables,
  \<open>hp ! v\<close> is the position of \<open>v\<close> in \<open>heap\<close> or \<open>NONE_POS\<close> (\<^verbatim>\<open>usize::MAX\<close>), \<open>act\<close> are
  the activities. A trail is modelled by the list of its variables (\<open>map (\<lambda>l. unat (Lit_var l)) t\<close>).
  The facts are the ones the contracts need: the position invariant \<open>hinv\<close>, the set of elements,
  the bounds of every index; the heap order is not needed for correctness and is not proved.\<close>

definition NONE_POS :: nat where
  \<open>NONE_POS = 2 ^ 64 - 1\<close>

definition before_m :: \<open>nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>before_m act u v \<longleftrightarrow> act ! u > act ! v \<or> (act ! u = act ! v \<and> u < v)\<close>

subsection \<open>Models\<close>

text \<open>The loop of \<^verbatim>\<open>heap_up\<close>: moves the hole at \<open>i\<close> up while \<open>v\<close> comes before its parent.\<close>
function up_loop :: \<open>nat list \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list \<times> nat list \<times> nat\<close> where
  \<open>up_loop act v heap hp i =
    (if 0 < i \<and> before_m act v (heap ! ((i - 1) div 2)) then
       (let u = heap ! ((i - 1) div 2) in
        up_loop act v (heap[i := u]) (hp[u := i]) ((i - 1) div 2))
     else (heap, hp, i))\<close>
  by pat_completeness auto
termination
  by (relation \<open>measure (\<lambda>(_, _, _, _, i). i)\<close>) auto

declare up_loop.simps [simp del]

definition heap_up_m :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list \<times> nat list\<close> where
  \<open>heap_up_m act heap hp i =
    (let v = heap ! i in
     case up_loop act v heap hp i of (heap, hp, i) \<Rightarrow> (heap[i := v], hp[v := i]))\<close>

text \<open>The loop of \<^verbatim>\<open>heap_down\<close>: moves the hole at \<open>i\<close> down while a child comes before \<open>v\<close>.\<close>
function down_loop :: \<open>nat list \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list \<times> nat list \<times> nat\<close> where
  \<open>down_loop act v heap hp i =
    (let l = 2 * i + 1 in
     if length heap \<le> l then (heap, hp, i)
     else
       (let c = (if l + 1 < length heap \<and> before_m act (heap ! (l + 1)) (heap ! l) then l + 1 else l) in
        if \<not> before_m act (heap ! c) v then (heap, hp, i)
        else
          (let u = heap ! c in
           down_loop act v (heap[i := u]) (hp[u := i]) c)))\<close>
  by pat_completeness auto
termination
  by (relation \<open>measure (\<lambda>(_, _, heap, _, i). length heap - i)\<close>) (auto simp: Let_def)

declare down_loop.simps [simp del]

definition heap_down_m :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list \<times> nat list\<close> where
  \<open>heap_down_m act heap hp i =
    (let v = heap ! i in
     case down_loop act v heap hp i of (heap, hp, i) \<Rightarrow> (heap[i := v], hp[v := i]))\<close>

text \<open>The loop of \<^verbatim>\<open>heap_rebuild\<close>, from \<open>i\<close> down: \<open>i -= 1\<close>, then \<^verbatim>\<open>heap_down\<close> at \<open>i\<close>.\<close>
fun rebuild_loop :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list \<times> nat list\<close> where
  \<open>rebuild_loop act heap hp 0 = (heap, hp)\<close>
| \<open>rebuild_loop act heap hp (Suc i) =
    (case heap_down_m act heap hp i of (h2, p2) \<Rightarrow> rebuild_loop act h2 p2 i)\<close>

definition heap_rebuild_m :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<times> nat list\<close> where
  \<open>heap_rebuild_m act heap hp = rebuild_loop act heap hp (length heap div 2)\<close>

definition heap_insert_m :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list \<times> nat list\<close> where
  \<open>heap_insert_m act heap hp v =
    (if hp ! v \<noteq> NONE_POS then (heap, hp)
     else (let i = length heap in heap_up_m act (heap @ [v]) hp i))\<close>

definition heap_pop_m :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<times> nat list \<times> nat option\<close> where
  \<open>heap_pop_m act heap hp =
    (if heap = [] then (heap, hp, None)
     else
       (let last = last heap in
        let heap = butlast heap in
        if heap = [] then (heap, hp[last := NONE_POS], Some last)
        else
          (let top = heap ! 0 in
           let hp = hp[top := NONE_POS] in
           let heap = heap[0 := last] in
           let hp = hp[last := 0] in
           case heap_down_m act heap hp 0 of (h2, p2) \<Rightarrow> (h2, p2, Some top))))\<close>

lemma up_loop_length: \<open>up_loop act v heap hp i = (h, p, j) \<Longrightarrow> length h = length heap\<close>
proof (induction act v heap hp i arbitrary: h p j rule: up_loop.induct)
  case (1 act v heap hp i)
  then show ?case by (cases \<open>0 < i \<and> before_m act v (heap ! ((i - 1) div 2))\<close>)
      (auto simp: up_loop.simps[of act v heap hp i] Let_def)
qed

text \<open>One step of the loop of \<^verbatim>\<open>heap_down\<close>, with the child \<open>c\<close> it compares.\<close>
lemma down_loop_eq:
  assumes \<open>c = (if 2 * i + 1 + 1 < length heap \<and> before_m act (heap ! (2 * i + 1 + 1)) (heap ! (2 * i + 1))
    then 2 * i + 1 + 1 else 2 * i + 1)\<close>
  shows \<open>down_loop act v heap hp i =
    (if length heap \<le> 2 * i + 1 \<or> \<not> before_m act (heap ! c) v then (heap, hp, i)
     else down_loop act v (heap[i := heap ! c]) (hp[heap ! c := i]) c)\<close>
  using assms by (subst down_loop.simps) (simp add: Let_def)

lemma down_loop_length: \<open>down_loop act v heap hp i = (h, p, j) \<Longrightarrow> length h = length heap\<close>
proof (induction act v heap hp i arbitrary: h p j rule: down_loop.induct)
  case (1 act v heap hp i)
  define c where \<open>c = (if 2 * i + 1 + 1 < length heap \<and> before_m act (heap ! (2 * i + 1 + 1)) (heap ! (2 * i + 1))
    then 2 * i + 1 + 1 else 2 * i + 1)\<close>
  show ?case
  proof (cases \<open>length heap \<le> 2 * i + 1 \<or> \<not> before_m act (heap ! c) v\<close>)
    case True
    then show ?thesis using 1(2) down_loop_eq[OF c_def] by simp
  next
    case False
    then have \<open>down_loop act v (heap[i := heap ! c]) (hp[heap ! c := i]) c = (h, p, j)\<close>
      using 1(2) down_loop_eq[OF c_def] by simp
    then show ?thesis using 1(1)[OF refl _ c_def _ refl] False by simp
  qed
qed

lemma heap_down_m_length: \<open>heap_down_m act heap hp i = (h, p) \<Longrightarrow> length h = length heap\<close>
  by (auto simp: heap_down_m_def Let_def split: prod.splits dest: down_loop_length)

lemma heap_pop_m_length:
  assumes \<open>heap_pop_m act heap hp = (h, p, Some x)\<close>
  shows \<open>length h < length heap\<close>
proof -
  have ne: \<open>heap \<noteq> []\<close> using assms by (auto simp: heap_pop_m_def)
  show ?thesis
  proof (cases \<open>butlast heap = []\<close>)
    case True
    then show ?thesis using assms ne by (auto simp: heap_pop_m_def Let_def)
  next
    case False
    obtain h2 p2 where D: \<open>heap_down_m act ((butlast heap)[0 := last heap])
        ((hp[butlast heap ! 0 := NONE_POS])[last heap := 0]) 0 = (h2, p2)\<close>
      by (metis surj_pair)
    then have \<open>h = h2\<close> using assms ne False by (simp add: heap_pop_m_def Let_def)
    then show ?thesis using heap_down_m_length[OF D] ne by simp
  qed
qed

text \<open>The loop of \<^verbatim>\<open>heap_pick\<close>: pops until the heap is empty or the popped variable is
  unassigned.\<close>
function heap_pick_m :: \<open>nat list \<Rightarrow> bool option list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<times> nat list \<times> nat option\<close> where
  \<open>heap_pick_m act a heap hp =
    (case heap_pop_m act heap hp of
       (h2, p2, None) \<Rightarrow> (h2, p2, None)
     | (h2, p2, Some x) \<Rightarrow> (if a ! x = None then (h2, p2, Some x) else heap_pick_m act a h2 p2))\<close>
  by pat_completeness auto
termination
  by (relation \<open>measure (\<lambda>(_, _, heap, _). length heap)\<close>) (auto dest: heap_pop_m_length[OF sym])

declare heap_pick_m.simps [simp del]

text \<open>The loop of \<^verbatim>\<open>heap_back\<close>: inserts the variables of the trail from position \<open>k\<close> on.\<close>
function back_loop :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list \<times> nat list\<close> where
  \<open>back_loop act ts heap hp k =
    (if k < length ts then
       (case heap_insert_m act heap hp (ts ! k) of (h2, p2) \<Rightarrow> back_loop act ts h2 p2 (Suc k))
     else (heap, hp))\<close>
  by pat_completeness auto
termination
  by (relation \<open>measure (\<lambda>(_, ts, _, _, k). length ts - k)\<close>) auto

declare back_loop.simps [simp del]

definition heap_back_m :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list \<times> nat list\<close> where
  \<open>heap_back_m act heap hp ts p = back_loop act ts heap hp p\<close>

text \<open>A loop of \<^verbatim>\<open>heap_bumped\<close> (both have this body): from position \<open>k\<close> of the variables \<open>vs\<close>
  on, moves each variable in the heap up.\<close>
function bump_loop :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list \<times> nat list\<close> where
  \<open>bump_loop act vs heap hp k =
    (if k < length vs then
       (let v = vs ! k in
        let i = hp ! v in
        if i \<noteq> NONE_POS then
          (case heap_up_m act heap hp i of (h2, p2) \<Rightarrow> bump_loop act vs h2 p2 (Suc k))
        else bump_loop act vs heap hp (Suc k))
     else (heap, hp))\<close>
  by pat_completeness auto
termination
  by (relation \<open>measure (\<lambda>(_, vs, _, _, k). length vs - k)\<close>) auto

declare bump_loop.simps [simp del]

text \<open>\<open>cv\<close>: the variables of the learned clause; \<open>ts\<close>: the variables of the trail.\<close>
definition heap_bumped_m :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list \<times> nat list\<close> where
  \<open>heap_bumped_m act heap hp cv ts start =
    (case bump_loop act cv heap hp 0 of (h2, p2) \<Rightarrow> bump_loop act ts h2 p2 start)\<close>

subsection \<open>The position invariant\<close>

definition hinv :: \<open>nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool\<close> where
  \<open>hinv n heap hp \<longleftrightarrow> length hp = n \<and> n \<le> NONE_POS \<and> distinct heap \<and> (\<forall>v \<in> set heap. v < n) \<and>
     (\<forall>i < length heap. hp ! (heap ! i) = i) \<and> (\<forall>v < n. v \<notin> set heap \<longrightarrow> hp ! v = NONE_POS)\<close>

lemma hinv_length: \<open>hinv n heap hp \<Longrightarrow> length heap \<le> n\<close>
proof -
  assume h: \<open>hinv n heap hp\<close>
  then have \<open>set heap \<subseteq> {..<n}\<close> \<open>distinct heap\<close> by (auto simp: hinv_def)
  then show ?thesis by (metis card_lessThan card_mono distinct_card finite_lessThan)
qed

lemma hinv_init: \<open>n \<le> NONE_POS \<Longrightarrow> hinv n [] (replicate n NONE_POS)\<close>
  by (simp add: hinv_def)

text \<open>A variable with a position is in the heap at that position.\<close>
lemma hinv_pos:
  assumes \<open>hinv n heap hp\<close> \<open>v < n\<close>
  shows \<open>hp ! v \<noteq> NONE_POS \<longleftrightarrow> v \<in> set heap\<close>
    and \<open>hp ! v \<noteq> NONE_POS \<Longrightarrow> hp ! v < length heap \<and> heap ! (hp ! v) = v\<close>
proof -
  have \<open>v \<in> set heap \<Longrightarrow> hp ! v < length heap \<and> heap ! (hp ! v) = v\<close>
    using assms(1) by (auto simp: hinv_def in_set_conv_nth)
  moreover have \<open>length heap \<le> NONE_POS\<close> using hinv_length[OF assms(1)] assms(1) by (simp add: hinv_def)
  ultimately show \<open>hp ! v \<noteq> NONE_POS \<longleftrightarrow> v \<in> set heap\<close>
    \<open>hp ! v \<noteq> NONE_POS \<Longrightarrow> hp ! v < length heap \<and> heap ! (hp ! v) = v\<close>
    using assms by (auto simp: hinv_def)
qed

lemma hinv_swap:
  assumes h: \<open>hinv n H P\<close> and ij: \<open>i < length H\<close> \<open>j < length H\<close>
  shows \<open>hinv n (H[i := H ! j, j := H ! i]) (P[H ! i := j, H ! j := i])\<close>
proof (cases \<open>i = j\<close>)
  case True
  have \<open>P[H ! j := j] = P\<close> using h ij by (metis hinv_def list_update_id)
  then show ?thesis using h ij True by (simp add: hinv_def)
next
  case False
  have D: \<open>distinct H\<close> using h by (simp add: hinv_def)
  have ne: \<open>\<And>k. k < length H \<Longrightarrow> k \<noteq> i \<Longrightarrow> H ! k \<noteq> H ! i\<close> \<open>\<And>k. k < length H \<Longrightarrow> k \<noteq> j \<Longrightarrow> H ! k \<noteq> H ! j\<close>
    using D ij nth_eq_iff_index_eq by blast+
  have L: \<open>H ! i < length P\<close> \<open>H ! j < length P\<close> using h ij by (auto simp: hinv_def)
  have pos: \<open>\<forall>k < length H. (P[H ! i := j, H ! j := i]) ! ((H[i := H ! j, j := H ! i]) ! k) = k\<close>
  proof (intro allI impI)
    fix k assume k: \<open>k < length H\<close>
    show \<open>(P[H ! i := j, H ! j := i]) ! ((H[i := H ! j, j := H ! i]) ! k) = k\<close>
      using k ij False ne[OF k] L h by (auto simp: hinv_def nth_list_update)
  qed
  have \<open>set (H[i := H ! j, j := H ! i]) = set H\<close> using ij by simp
  moreover have \<open>distinct (H[i := H ! j, j := H ! i])\<close> using D ij by simp
  moreover have \<open>\<forall>v < n. v \<notin> set H \<longrightarrow> (P[H ! i := j, H ! j := i]) ! v = NONE_POS\<close>
    using h ij by (auto simp: hinv_def nth_list_update)
  ultimately show ?thesis using h pos by (simp add: hinv_def)
qed

text \<open>The loop state of \<^verbatim>\<open>heap_up\<close> and \<^verbatim>\<open>heap_down\<close>: with \<open>v\<close> written at the hole \<open>i\<close>, the
  invariant holds.\<close>
definition hole_inv :: \<open>nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>hole_inv n heap hp v i \<longleftrightarrow> i < length heap \<and> hinv n (heap[i := v]) (hp[v := i])\<close>

lemma hole_inv_hinv: \<open>hinv n heap hp \<Longrightarrow> i < length heap \<Longrightarrow> hole_inv n heap hp (heap ! i) i\<close>
  by (metis hinv_def hole_inv_def list_update_id)

text \<open>The bounds of the indices of a loop step.\<close>
lemma hole_inv_bounds:
  assumes \<open>hole_inv n heap hp v i\<close>
  shows \<open>i < length heap \<and> v < n \<and> length hp = n \<and> length heap \<le> n \<and>
    (\<forall>j < length heap. j \<noteq> i \<longrightarrow> heap ! j < n)\<close>
proof -
  have h: \<open>hinv n (heap[i := v]) (hp[v := i])\<close> \<open>i < length heap\<close>
    using assms by (auto simp: hole_inv_def)
  have \<open>\<forall>j < length heap. j \<noteq> i \<longrightarrow> heap ! j < n\<close>
  proof (intro allI impI)
    fix j assume \<open>j < length heap\<close> \<open>j \<noteq> i\<close>
    then have \<open>heap ! j \<in> set (heap[i := v])\<close> by (metis length_list_update nth_list_update_neq nth_mem)
    then show \<open>heap ! j < n\<close> using h by (simp add: hinv_def)
  qed
  moreover have \<open>v < n\<close> using h set_update_memI[OF h(2), of v] by (simp add: hinv_def)
  moreover have \<open>length heap \<le> n\<close> using hinv_length[OF h(1)] by simp
  ultimately show ?thesis using h by (simp add: hinv_def)
qed

lemma hole_inv_move:
  assumes I: \<open>hole_inv n heap hp v i\<close> and j: \<open>j < length heap\<close> \<open>j \<noteq> i\<close>
  shows \<open>hole_inv n (heap[i := heap ! j]) (hp[heap ! j := i]) v j \<and>
    set ((heap[i := heap ! j])[j := v]) = set (heap[i := v])\<close>
proof -
  let ?H = \<open>heap[i := v]\<close> and ?P = \<open>hp[v := i]\<close> and ?u = \<open>heap ! j\<close>
  have h: \<open>hinv n ?H ?P\<close> and i: \<open>i < length heap\<close> using I by (auto simp: hole_inv_def)
  have Hi: \<open>?H ! i = v\<close> \<open>?H ! j = ?u\<close> using i j by auto
  have uv: \<open>?u \<noteq> v\<close>
    using h i j Hi nth_eq_iff_index_eq[of ?H i j] by (simp add: hinv_def)
  have S: \<open>hinv n (heap[i := ?u, j := v]) (hp[v := j, ?u := i])\<close>
    using hinv_swap[OF h, of i j] i j Hi by simp
  have E2: \<open>hp[v := j, ?u := i] = hp[?u := i, v := j]\<close> using uv by (simp add: list_update_swap)
  have \<open>set (heap[i := ?u, j := v]) = set ?H\<close>
    using set_swap[of i ?H j] i j Hi by (metis length_list_update list_update_overwrite)
  then show ?thesis using S E2 j by (simp add: hole_inv_def)
qed

subsection \<open>The models keep the invariant\<close>

lemma up_loop_inv:
  \<open>hole_inv n heap hp v i \<Longrightarrow> up_loop act v heap hp i = (h, p, j) \<Longrightarrow>
    hole_inv n h p v j \<and> set (h[j := v]) = set (heap[i := v])\<close>
proof (induction act v heap hp i arbitrary: h p j rule: up_loop.induct)
  case (1 act v heap hp i)
  show ?case
  proof (cases \<open>0 < i \<and> before_m act v (heap ! ((i - 1) div 2))\<close>)
    case True
    let ?q = \<open>(i - 1) div 2\<close>
    have q: \<open>?q < length heap\<close> \<open>?q \<noteq> i\<close> using True 1(2) by (auto simp: hole_inv_def)
    note M = hole_inv_move[OF 1(2) q]
    have \<open>up_loop act v (heap[i := heap ! ?q]) (hp[heap ! ?q := i]) ?q = (h, p, j)\<close>
      using 1(3) True by (subst (asm) up_loop.simps) (simp add: Let_def)
    then show ?thesis using 1(1)[OF True refl] M by simp
  next
    case False
    then show ?thesis using 1(2,3) by (subst (asm) up_loop.simps) auto
  qed
qed

lemma heap_up_m_inv:
  assumes \<open>hole_inv n heap hp (heap ! i) i\<close> \<open>heap_up_m act heap hp i = (h, p)\<close>
  shows \<open>hinv n h p \<and> set h = set heap\<close>
proof -
  obtain h1 p1 j where U: \<open>up_loop act (heap ! i) heap hp i = (h1, p1, j)\<close> by (cases \<open>up_loop act (heap ! i) heap hp i\<close>) auto
  then have \<open>h = h1[j := heap ! i]\<close> \<open>p = p1[heap ! i := j]\<close> using assms(2) by (auto simp: heap_up_m_def Let_def)
  then show ?thesis using up_loop_inv[OF assms(1) U] by (simp add: hole_inv_def)
qed

lemma heap_up_m_hinv:
  \<open>hinv n heap hp \<Longrightarrow> i < length heap \<Longrightarrow> heap_up_m act heap hp i = (h, p) \<Longrightarrow> hinv n h p \<and> set h = set heap\<close>
  using heap_up_m_inv hole_inv_hinv by blast

lemma down_loop_inv:
  \<open>hole_inv n heap hp v i \<Longrightarrow> down_loop act v heap hp i = (h, p, j) \<Longrightarrow>
    hole_inv n h p v j \<and> set (h[j := v]) = set (heap[i := v])\<close>
proof (induction act v heap hp i arbitrary: h p j rule: down_loop.induct)
  case (1 act v heap hp i)
  define c where \<open>c = (if 2 * i + 1 + 1 < length heap \<and> before_m act (heap ! (2 * i + 1 + 1)) (heap ! (2 * i + 1))
    then 2 * i + 1 + 1 else 2 * i + 1)\<close>
  show ?case
  proof (cases \<open>length heap \<le> 2 * i + 1 \<or> \<not> before_m act (heap ! c) v\<close>)
    case True
    then show ?thesis using 1(2,3) down_loop_eq[OF c_def] by simp
  next
    case False
    have c: \<open>c < length heap\<close> \<open>c \<noteq> i\<close> using False by (auto simp: c_def)
    note M = hole_inv_move[OF 1(2) c]
    have \<open>down_loop act v (heap[i := heap ! c]) (hp[heap ! c := i]) c = (h, p, j)\<close>
      using 1(3) down_loop_eq[OF c_def] False by simp
    then show ?thesis using 1(1)[OF refl _ c_def _ refl] False M by simp
  qed
qed

lemma heap_down_m_inv:
  assumes \<open>hole_inv n heap hp (heap ! i) i\<close> \<open>heap_down_m act heap hp i = (h, p)\<close>
  shows \<open>hinv n h p \<and> set h = set heap \<and> length h = length heap\<close>
proof -
  obtain h1 p1 j where U: \<open>down_loop act (heap ! i) heap hp i = (h1, p1, j)\<close> by (cases \<open>down_loop act (heap ! i) heap hp i\<close>) auto
  then have \<open>h = h1[j := heap ! i]\<close> \<open>p = p1[heap ! i := j]\<close> using assms(2) by (auto simp: heap_down_m_def Let_def)
  then show ?thesis using down_loop_inv[OF assms(1) U] down_loop_length[OF U] by (simp add: hole_inv_def)
qed

lemma heap_down_m_hinv:
  \<open>hinv n heap hp \<Longrightarrow> i < length heap \<Longrightarrow> heap_down_m act heap hp i = (h, p) \<Longrightarrow> hinv n h p \<and> set h = set heap\<close>
  using heap_down_m_inv hole_inv_hinv by blast

lemma rebuild_loop_inv:
  \<open>hinv n heap hp \<Longrightarrow> i \<le> length heap \<Longrightarrow> rebuild_loop act heap hp i = (h, p) \<Longrightarrow>
    hinv n h p \<and> set h = set heap\<close>
proof (induction i arbitrary: heap hp)
  case 0
  then show ?case by simp
next
  case (Suc i)
  obtain h2 p2 where D: \<open>heap_down_m act heap hp i = (h2, p2)\<close> by (cases \<open>heap_down_m act heap hp i\<close>) auto
  have I: \<open>hinv n h2 p2 \<and> set h2 = set heap \<and> length h2 = length heap\<close>
    using heap_down_m_inv[OF hole_inv_hinv[OF Suc(2)] D] Suc(3) by simp
  then show ?case using Suc D by auto
qed

lemma heap_rebuild_m_inv:
  \<open>hinv n heap hp \<Longrightarrow> heap_rebuild_m act heap hp = (h, p) \<Longrightarrow> hinv n h p \<and> set h = set heap\<close>
  unfolding heap_rebuild_m_def by (erule rebuild_loop_inv) auto

text \<open>The index of the loop of \<^verbatim>\<open>heap_rebuild\<close> is in the heap.\<close>
lemma rebuild_bound: \<open>Suc i \<le> length heap div 2 \<Longrightarrow> i < length heap\<close>
  by simp

lemma heap_insert_m_inv:
  assumes h: \<open>hinv n heap hp\<close> and v: \<open>v < n\<close> and I: \<open>heap_insert_m act heap hp v = (h', p')\<close>
  shows \<open>hinv n h' p' \<and> set h' = insert v (set heap)\<close>
proof (cases \<open>hp ! v \<noteq> NONE_POS\<close>)
  case True
  then show ?thesis using I hinv_pos(1)[OF h v] h by (auto simp: heap_insert_m_def)
next
  case False
  then have nv: \<open>v \<notin> set heap\<close> using hinv_pos(1)[OF h v] by simp
  have \<open>hinv n (heap @ [v]) (hp[v := length heap])\<close>
  proof -
    have \<open>\<forall>i < length (heap @ [v]). (hp[v := length heap]) ! ((heap @ [v]) ! i) = i\<close>
    proof (intro allI impI)
      fix i assume \<open>i < length (heap @ [v])\<close>
      then show \<open>(hp[v := length heap]) ! ((heap @ [v]) ! i) = i\<close>
        using h v nv by (cases \<open>i < length heap\<close>) (auto simp: hinv_def nth_append nth_list_update)
    qed
    then show ?thesis using h v nv by (auto simp: hinv_def nth_list_update)
  qed
  then have H: \<open>hole_inv n (heap @ [v]) hp ((heap @ [v]) ! length heap) (length heap)\<close>
    by (simp add: hole_inv_def)
  have \<open>heap_up_m act (heap @ [v]) hp (length heap) = (h', p')\<close> using I False by (simp add: heap_insert_m_def)
  then show ?thesis using heap_up_m_inv[OF H] by simp
qed

lemma heap_pop_m_inv:
  assumes h: \<open>hinv n heap hp\<close> and P: \<open>heap_pop_m act heap hp = (h', p', r)\<close>
  shows \<open>hinv n h' p' \<and> (r = None \<longleftrightarrow> heap = []) \<and>
    (heap = [] \<longrightarrow> h' = []) \<and>
    (\<forall>x. r = Some x \<longrightarrow> x \<in> set heap \<and> set h' = set heap - {x})\<close>
proof (cases heap)
  case Nil
  then show ?thesis using h P by (simp add: heap_pop_m_def)
next
  case (Cons top rest)
  show ?thesis
  proof (cases rest)
    case Nil
    then have E: \<open>h' = []\<close> \<open>p' = hp[top := NONE_POS]\<close> \<open>r = Some top\<close>
      using P Cons by (auto simp: heap_pop_m_def)
    then show ?thesis using h Cons Nil by (auto simp: hinv_def nth_list_update)
  next
    case (Cons y ys)
    then obtain mid lst where R: \<open>rest = mid @ [lst]\<close> by (metis list.distinct(1) rev_exhaust)
    have hc: \<open>heap = top # mid @ [lst]\<close> using \<open>heap = top # rest\<close> R by simp
    let ?H = \<open>lst # mid\<close> and ?P = \<open>hp[top := NONE_POS, lst := 0]\<close>
    have D: \<open>heap_down_m act ?H ?P 0 = (h', p')\<close> \<open>r = Some top\<close>
      using P hc by (auto simp: heap_pop_m_def Let_def split: prod.splits)
    have dist: \<open>distinct heap\<close> and lt: \<open>\<forall>v \<in> set heap. v < n\<close> and ln: \<open>length hp = n\<close> \<open>n \<le> NONE_POS\<close>
      and ps: \<open>\<forall>i < length heap. hp ! (heap ! i) = i\<close> and nn: \<open>\<forall>v < n. v \<notin> set heap \<longrightarrow> hp ! v = NONE_POS\<close>
      using h by (auto simp: hinv_def)
    have tl: \<open>top \<noteq> lst\<close> \<open>top \<notin> set mid\<close> \<open>lst \<notin> set mid\<close> \<open>distinct mid\<close> using dist hc by auto
    have \<open>hinv n ?H ?P\<close>
    proof -
      have \<open>\<forall>i < length ?H. ?P ! (?H ! i) = i\<close>
      proof (intro allI impI)
        fix i assume i: \<open>i < length ?H\<close>
        show \<open>?P ! (?H ! i) = i\<close>
        proof (cases i)
          case 0
          then show ?thesis using lt ln hc by (simp add: nth_list_update)
        next
          case (Suc k)
          then have k: \<open>k < length mid\<close> using i by simp
          then have m: \<open>mid ! k \<noteq> top\<close> \<open>mid ! k \<noteq> lst\<close> using tl nth_mem by metis+
          have \<open>hp ! (heap ! Suc k) = Suc k\<close> using ps[rule_format, of \<open>Suc k\<close>] k hc by simp
          then show ?thesis using Suc k m hc by (simp add: nth_list_update nth_append)
        qed
      qed
      moreover have \<open>\<forall>v < n. v \<notin> set ?H \<longrightarrow> ?P ! v = NONE_POS\<close>
        using nn hc ln lt by (auto simp: nth_list_update)
      ultimately show ?thesis using tl lt ln hc by (simp add: hinv_def)
    qed
    then have \<open>hinv n h' p' \<and> set h' = set ?H\<close> using heap_down_m_hinv[OF _ _ D(1)] by simp
    then show ?thesis using D(2) hc tl by auto
  qed
qed

subsection \<open>Picking a decision and the covering invariant\<close>

text \<open>Every unassigned variable is in the heap.\<close>
definition hcov :: \<open>nat \<Rightarrow> nat list \<Rightarrow> bool option list \<Rightarrow> bool\<close> where
  \<open>hcov n heap a \<longleftrightarrow> (\<forall>v < n. a ! v = None \<longrightarrow> v \<in> set heap)\<close>

lemma heap_pick_m_inv:
  \<open>hinv n heap hp \<Longrightarrow> heap_pick_m act a heap hp = (h', p', r) \<Longrightarrow>
    hinv n h' p' \<and> set h' \<subseteq> set heap \<and>
    (r = None \<longrightarrow> h' = [] \<and> (\<forall>v \<in> set heap. a ! v \<noteq> None)) \<and>
    (\<forall>x. r = Some x \<longrightarrow> x \<in> set heap \<and> x \<notin> set h' \<and> a ! x = None \<and>
       (\<forall>v \<in> set heap. v \<notin> set h' \<and> v \<noteq> x \<longrightarrow> a ! v \<noteq> None))\<close>
proof (induction act a heap hp arbitrary: h' p' r rule: heap_pick_m.induct)
  case (1 act a heap hp)
  obtain h2 p2 y where Q: \<open>heap_pop_m act heap hp = (h2, p2, y)\<close> by (cases \<open>heap_pop_m act heap hp\<close>) auto
  note I = heap_pop_m_inv[OF 1(2) Q]
  show ?case
  proof (cases y)
    case None
    then show ?thesis using 1(3) Q I by (subst (asm) heap_pick_m.simps) auto
  next
    case (Some x)
    show ?thesis
    proof (cases \<open>a ! x = None\<close>)
      case True
      then show ?thesis using 1(3) Q I Some by (subst (asm) heap_pick_m.simps) auto
    next
      case False
      then have R: \<open>heap_pick_m act a h2 p2 = (h', p', r)\<close>
        using 1(3) Q Some by (subst (asm) heap_pick_m.simps) (simp del: not_None_eq)
      have IH: \<open>hinv n h' p' \<and> set h' \<subseteq> set h2 \<and>
        (r = None \<longrightarrow> h' = [] \<and> (\<forall>v \<in> set h2. a ! v \<noteq> None)) \<and>
        (\<forall>x. r = Some x \<longrightarrow> x \<in> set h2 \<and> x \<notin> set h' \<and> a ! x = None \<and>
          (\<forall>v \<in> set h2. v \<notin> set h' \<and> v \<noteq> x \<longrightarrow> a ! v \<noteq> None))\<close>
        by (rule 1(1)[OF Q[symmetric] refl Some False I[THEN conjunct1] R])
      then show ?thesis using I Some False by (simp del: not_None_eq) blast
    qed
  qed
qed

text \<open>(i) of the decision: \<open>heap_pick_m\<close> returns an unassigned variable, or none and then every
  variable is assigned; the covering holds after the returned variable is assigned.\<close>
theorem heap_pick_m_hcov:
  assumes h: \<open>hinv n heap hp\<close> and c: \<open>hcov n heap a\<close> and la: \<open>length a = n\<close>
    and P: \<open>heap_pick_m act a heap hp = (h', p', r)\<close>
  shows \<open>hinv n h' p' \<and>
    (r = None \<longrightarrow> (\<forall>v < n. a ! v \<noteq> None) \<and> hcov n h' a) \<and>
    (\<forall>x. r = Some x \<longrightarrow> x < n \<and> a ! x = None \<and> (\<forall>b. hcov n h' (a[x := Some b])))\<close>
proof -
  note I = heap_pick_m_inv[OF h P]
  have lt: \<open>\<forall>v \<in> set heap. v < n\<close> using h by (simp add: hinv_def)
  have N: \<open>r = None \<longrightarrow> (\<forall>v < n. a ! v \<noteq> None)\<close> using I c by (auto simp: hcov_def)
  have S: \<open>\<forall>x. r = Some x \<longrightarrow> x < n \<and> a ! x = None \<and> (\<forall>b. hcov n h' (a[x := Some b]))\<close>
  proof (intro allI impI)
    fix x assume r: \<open>r = Some x\<close>
    have x: \<open>x < n\<close> \<open>a ! x = None\<close> using I r lt by auto
    have \<open>\<forall>b. hcov n h' (a[x := Some b])\<close>
      unfolding hcov_def
    proof (intro allI impI)
      fix b v assume v: \<open>v < n\<close> \<open>a[x := Some b] ! v = None\<close>
      then have \<open>v \<noteq> x\<close> \<open>a ! v = None\<close> using la x by (auto simp: nth_list_update split: if_splits)
      then show \<open>v \<in> set h'\<close> using I r c v(1) by (auto simp: hcov_def)
    qed
    then show \<open>x < n \<and> a ! x = None \<and> (\<forall>b. hcov n h' (a[x := Some b]))\<close> using x by simp
  qed
  show ?thesis using I N S by (auto simp: hcov_def)
qed

lemma back_loop_inv:
  \<open>hinv n heap hp \<Longrightarrow> \<forall>v \<in> set ts. v < n \<Longrightarrow> back_loop act ts heap hp k = (h', p') \<Longrightarrow>
    hinv n h' p' \<and> set h' = set heap \<union> set (drop k ts)\<close>
proof (induction act ts heap hp k arbitrary: h' p' rule: back_loop.induct)
  case (1 act ts heap hp k)
  show ?case
  proof (cases \<open>k < length ts\<close>)
    case True
    obtain h2 p2 where Q: \<open>heap_insert_m act heap hp (ts ! k) = (h2, p2)\<close> by (cases \<open>heap_insert_m act heap hp (ts ! k)\<close>) auto
    have I: \<open>hinv n h2 p2 \<and> set h2 = insert (ts ! k) (set heap)\<close>
      using heap_insert_m_inv[OF 1(2) _ Q] 1(3) True by simp
    have \<open>back_loop act ts h2 p2 (Suc k) = (h', p')\<close> using 1(4) True Q by (subst (asm) back_loop.simps) simp
    then have \<open>hinv n h' p' \<and> set h' = set h2 \<union> set (drop (Suc k) ts)\<close>
      using 1(1)[OF True Q[symmetric]] I 1(3) by blast
    moreover have \<open>set (drop k ts) = insert (ts ! k) (set (drop (Suc k) ts))\<close>
      using True by (simp add: Cons_nth_drop_Suc[symmetric])
    ultimately show ?thesis using I by auto
  next
    case False
    then show ?thesis using 1(2,4) by (subst (asm) back_loop.simps) simp
  qed
qed

lemma heap_back_m_inv:
  \<open>hinv n heap hp \<Longrightarrow> \<forall>v \<in> set ts. v < n \<Longrightarrow> heap_back_m act heap hp ts p = (h', p') \<Longrightarrow>
    hinv n h' p' \<and> set h' = set heap \<union> set (drop p ts)\<close>
  unfolding heap_back_m_def by (rule back_loop_inv)

text \<open>(ii) after a cut of the trail to position \<open>p\<close>: \<open>ts\<close> are the variables of the trail
  \<open>t\<close> (\<open>map (\<lambda>l. unat (Lit_var l)) t\<close>); \<open>a\<close> assigns only variables of the trail and \<open>a2\<close> all
  variables of \<open>take p t\<close>. With \<open>tr_ok n a t\<close> and \<open>tr_ok n a2 (take p t)\<close> these are the
  last and the third conjunct of \<open>tr_ok\<close>.\<close>
theorem heap_back_m_hcov:
  assumes h: \<open>hinv n heap hp\<close> and c: \<open>hcov n heap a\<close> and lt: \<open>\<forall>v \<in> set ts. v < n\<close>
    and A: \<open>\<forall>v < n. a ! v \<noteq> None \<longrightarrow> v \<in> set ts\<close>
    and A2: \<open>\<forall>v \<in> set (take p ts). a2 ! v \<noteq> None\<close>
    and B: \<open>heap_back_m act heap hp ts p = (h', p')\<close>
  shows \<open>hinv n h' p' \<and> hcov n h' a2 \<and> set h' = set heap \<union> set (drop p ts)\<close>
proof -
  note I = heap_back_m_inv[OF h lt B]
  have \<open>hcov n h' a2\<close>
    unfolding hcov_def
  proof (intro allI impI)
    fix v assume v: \<open>v < n\<close> \<open>a2 ! v = None\<close>
    then have \<open>v \<notin> set (take p ts)\<close> using A2 by auto
    then have \<open>v \<in> set (drop p ts) \<or> a ! v = None\<close>
      using A v(1) by (metis Un_iff append_take_drop_id set_append)
    then show \<open>v \<in> set h'\<close> using I c v(1) by (auto simp: hcov_def)
  qed
  then show ?thesis using I by simp
qed

subsection \<open>Bumping\<close>

lemma bump_loop_inv:
  \<open>hinv n heap hp \<Longrightarrow> \<forall>v \<in> set vs. v < n \<Longrightarrow> bump_loop act vs heap hp k = (h', p') \<Longrightarrow>
    hinv n h' p' \<and> set h' = set heap\<close>
proof (induction act vs heap hp k arbitrary: h' p' rule: bump_loop.induct)
  case (1 act vs heap hp k)
  show ?case
  proof (cases \<open>k < length vs\<close>)
    case True
    have v: \<open>vs ! k < n\<close> using 1(4) True by simp
    show ?thesis
    proof (cases \<open>hp ! (vs ! k) \<noteq> NONE_POS\<close>)
      case T2: True
      obtain h2 p2 where Q: \<open>heap_up_m act heap hp (hp ! (vs ! k)) = (h2, p2)\<close>
        by (cases \<open>heap_up_m act heap hp (hp ! (vs ! k))\<close>) auto
      have I: \<open>hinv n h2 p2 \<and> set h2 = set heap\<close>
        using heap_up_m_hinv[OF 1(3) _ Q] hinv_pos(2)[OF 1(3) v T2] by simp
      have \<open>bump_loop act vs h2 p2 (Suc k) = (h', p')\<close>
        using 1(5) True T2 Q by (subst (asm) bump_loop.simps) (simp add: Let_def)
      then show ?thesis using 1(1)[OF True refl refl T2 Q[symmetric]] I 1(4) by simp
    next
      case F2: False
      have \<open>bump_loop act vs heap hp (Suc k) = (h', p')\<close>
        using 1(5) True F2 by (subst (asm) bump_loop.simps) (simp add: Let_def)
      then show ?thesis using 1(2)[OF True refl refl F2] 1(3,4) by simp
    qed
  next
    case False
    then show ?thesis using 1(3,5) by (subst (asm) bump_loop.simps) simp
  qed
qed

lemma heap_bumped_m_inv:
  \<open>hinv n heap hp \<Longrightarrow> \<forall>v \<in> set cv. v < n \<Longrightarrow> \<forall>v \<in> set ts. v < n \<Longrightarrow>
    heap_bumped_m act heap hp cv ts start = (h', p') \<Longrightarrow> hinv n h' p' \<and> set h' = set heap\<close>
proof -
  assume h: \<open>hinv n heap hp\<close> and cv: \<open>\<forall>v \<in> set cv. v < n\<close> and ts: \<open>\<forall>v \<in> set ts. v < n\<close>
    and B: \<open>heap_bumped_m act heap hp cv ts start = (h', p')\<close>
  obtain h2 p2 where Q: \<open>bump_loop act cv heap hp 0 = (h2, p2)\<close> by (metis surj_pair)
  note I = bump_loop_inv[OF h cv Q]
  have \<open>bump_loop act ts h2 p2 start = (h', p')\<close> using B Q by (simp add: heap_bumped_m_def)
  then show ?thesis using bump_loop_inv[OF I[THEN conjunct1] ts] I by simp
qed

end
