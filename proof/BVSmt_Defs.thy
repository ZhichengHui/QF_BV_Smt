theory BVSmt_Defs
  imports BVSmt_Core
begin

section \<open>Functional models of the Rust functions\<close>

text \<open>
  Each Rust function of the bit-blaster has a functional model here; \<^verbatim>\<open>BVSmt_Refine\<close> proves
  that the Rust function computes its model. A CNF state is modelled by \<open>st\<close>: the number of
  variables as a natural number (so that it cannot wrap around) and the clauses. Loops that run
  over \<open>i = 0, 1, \<dots>, n - 1\<close> are modelled by \<^const>\<open>foldl\<close> over \<open>[0..<n]\<close>.
\<close>

type_synonym st = \<open>nat \<times> Lit list list\<close>

text \<open>The Rust \<^verbatim>\<open>Cnf\<close> of a state.\<close>
definition cnf_of :: \<open>st \<Rightarrow> Cnf\<close> where
  \<open>cnf_of s \<equiv> make_Cnf (word_of_nat (fst s)) (snd s)\<close>

text \<open>The state of a Rust \<^verbatim>\<open>Cnf\<close>.\<close>
definition st_of :: \<open>Cnf \<Rightarrow> st\<close> where
  \<open>st_of c \<equiv> (unat (Cnf_num_vars c), Cnf_clauses c)\<close>

subsection \<open>Literals and gates\<close>

definition lconst :: \<open>bool \<Rightarrow> Lit\<close> where
  \<open>lconst b \<equiv> make_Lit 0 (\<not> b)\<close>

definition lneg :: \<open>Lit \<Rightarrow> Lit\<close> where
  \<open>lneg l \<equiv> make_Lit (Lit_var l) (\<not> Lit_neg l)\<close>

definition fresh_m :: \<open>st \<Rightarrow> st \<times> Lit\<close> where
  \<open>fresh_m s \<equiv> ((Suc (fst s), snd s), make_Lit (word_of_nat (fst s)) False)\<close>

definition addc_m :: \<open>st \<Rightarrow> Lit list \<Rightarrow> st\<close> where
  \<open>addc_m s c \<equiv> (fst s, snd s @ [c])\<close>

definition and_m :: \<open>st \<Rightarrow> Lit \<Rightarrow> Lit \<Rightarrow> st \<times> Lit\<close> where
  \<open>and_m s a b \<equiv>
     let (s1, x) = fresh_m s in
     (addc_m (addc_m (addc_m s1 [lneg x, a]) [lneg x, b]) [x, lneg a, lneg b], x)\<close>

definition or_m :: \<open>st \<Rightarrow> Lit \<Rightarrow> Lit \<Rightarrow> st \<times> Lit\<close> where
  \<open>or_m s a b \<equiv> let (s1, x) = and_m s (lneg a) (lneg b) in (s1, lneg x)\<close>

definition xor_m :: \<open>st \<Rightarrow> Lit \<Rightarrow> Lit \<Rightarrow> st \<times> Lit\<close> where
  \<open>xor_m s a b \<equiv>
     let (s1, x) = fresh_m s in
     (addc_m (addc_m (addc_m (addc_m s1 [lneg x, a, b]) [lneg x, lneg a, lneg b])
        [x, lneg a, b]) [x, a, lneg b], x)\<close>

definition ite_m :: \<open>st \<Rightarrow> Lit \<Rightarrow> Lit \<Rightarrow> Lit \<Rightarrow> st \<times> Lit\<close> where
  \<open>ite_m s c a b \<equiv>
     let (s1, x) = fresh_m s in
     (addc_m (addc_m (addc_m (addc_m s1 [lneg c, lneg x, a]) [lneg c, x, lneg a])
        [c, lneg x, b]) [c, x, lneg b], x)\<close>

definition bitw_m :: \<open>BinOp \<Rightarrow> st \<Rightarrow> Lit \<Rightarrow> Lit \<Rightarrow> st \<times> Lit\<close> where
  \<open>bitw_m op s a b \<equiv>
     (case op of BinOp_And \<Rightarrow> and_m s a b | BinOp_Or \<Rightarrow> or_m s a b | _ \<Rightarrow> xor_m s a b)\<close>

subsection \<open>Bit-vector circuits\<close>

definition const_m :: \<open>bool list \<Rightarrow> Lit list\<close> where
  \<open>const_m bs \<equiv> map lconst bs\<close>

text \<open>\<^verbatim>\<open>bv_of_nat\<close>: after \<open>i\<close> iterations, \<open>x = v div 2^i\<close>.\<close>
definition of_nat_m :: \<open>nat \<Rightarrow> nat \<Rightarrow> Lit list\<close> where
  \<open>of_nat_m v w \<equiv> map (\<lambda>i. lconst (v div 2 ^ i mod 2 = 1)) [0..<w]\<close>

definition fresh_vec_m :: \<open>st \<Rightarrow> nat \<Rightarrow> st \<times> Lit list\<close> where
  \<open>fresh_vec_m s w \<equiv>
     ((fst s + w, snd s), map (\<lambda>i. make_Lit (word_of_nat (fst s + i)) False) [0..<w])\<close>

definition not_m :: \<open>Lit list \<Rightarrow> Lit list\<close> where
  \<open>not_m a \<equiv> map lneg a\<close>

definition bitwise_m :: \<open>BinOp \<Rightarrow> st \<Rightarrow> Lit list \<Rightarrow> Lit list \<Rightarrow> st \<times> Lit list\<close> where
  \<open>bitwise_m op s a b \<equiv>
     foldl (\<lambda>(s, r) i. let (s1, x) = bitw_m op s (a ! i) (b ! i) in (s1, r @ [x]))
       (s, []) [0..<length a]\<close>

text \<open>One step of the ripple-carry adder on bit \<open>i\<close>.\<close>
definition add_step :: \<open>Lit list \<Rightarrow> Lit list \<Rightarrow> st \<times> Lit list \<times> Lit \<Rightarrow> nat \<Rightarrow> st \<times> Lit list \<times> Lit\<close> where
  \<open>add_step a b \<equiv> \<lambda>(s, r, c) i.
     let (s1, t) = xor_m s (a ! i) (b ! i) in
     let (s2, x) = xor_m s1 t c in
     let (s3, c1) = ite_m s2 t c (a ! i) in
     (s3, r @ [x], c1)\<close>

definition add_m :: \<open>st \<Rightarrow> Lit list \<Rightarrow> Lit list \<Rightarrow> Lit \<Rightarrow> st \<times> Lit list \<times> Lit\<close> where
  \<open>add_m s a b cin \<equiv> foldl (add_step a b) (s, [], cin) [0..<length a]\<close>

definition partial_m :: \<open>st \<Rightarrow> Lit list \<Rightarrow> Lit \<Rightarrow> nat \<Rightarrow> st \<times> Lit list\<close> where
  \<open>partial_m s a bi i \<equiv>
     foldl (\<lambda>(s, r) j. if j < i then (s, r @ [lconst False])
                        else let (s1, x) = and_m s (a ! (j - i)) bi in (s1, r @ [x]))
       (s, []) [0..<length a]\<close>

definition mul_step :: \<open>Lit list \<Rightarrow> Lit list \<Rightarrow> st \<times> Lit list \<Rightarrow> nat \<Rightarrow> st \<times> Lit list\<close> where
  \<open>mul_step a b \<equiv> \<lambda>(s, acc) i.
     let (s1, p) = partial_m s a (b ! i) i in
     let (s2, sm, c) = add_m s1 acc p (lconst False) in
     (s2, sm)\<close>

definition mul_m :: \<open>st \<Rightarrow> Lit list \<Rightarrow> Lit list \<Rightarrow> st \<times> Lit list\<close> where
  \<open>mul_m s a b \<equiv> foldl (mul_step a b) (s, replicate (length a) (lconst False)) [0..<length a]\<close>

definition eq_step :: \<open>Lit list \<Rightarrow> Lit list \<Rightarrow> st \<times> Lit \<Rightarrow> nat \<Rightarrow> st \<times> Lit\<close> where
  \<open>eq_step a b \<equiv> \<lambda>(s, r) i.
     let (s1, x) = xor_m s (a ! i) (b ! i) in
     and_m s1 r (lneg x)\<close>

definition eq_m :: \<open>st \<Rightarrow> Lit list \<Rightarrow> Lit list \<Rightarrow> st \<times> Lit\<close> where
  \<open>eq_m s a b \<equiv> foldl (eq_step a b) (s, lconst True) [0..<length a]\<close>

definition ult_m :: \<open>st \<Rightarrow> Lit list \<Rightarrow> Lit list \<Rightarrow> st \<times> Lit\<close> where
  \<open>ult_m s a b \<equiv> let (s1, r, c) = add_m s a (not_m b) (lconst True) in (s1, lneg c)\<close>

definition ite_vec_m :: \<open>st \<Rightarrow> Lit \<Rightarrow> Lit list \<Rightarrow> Lit list \<Rightarrow> st \<times> Lit list\<close> where
  \<open>ite_vec_m s c a b \<equiv>
     foldl (\<lambda>(s, r) i. let (s1, x) = ite_m s c (a ! i) (b ! i) in (s1, r @ [x]))
       (s, []) [0..<length a]\<close>

definition shift_const_m :: \<open>Lit list \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> Lit list\<close> where
  \<open>shift_const_m a s left \<equiv>
     map (\<lambda>j. if left then (if j < s then lconst False else a ! (j - s))
               else (if s < length a - j then a ! (j + s) else lconst False))
       [0..<length a]\<close>

definition shift_step :: \<open>Lit list \<Rightarrow> Lit list \<Rightarrow> bool \<Rightarrow> st \<times> Lit list \<Rightarrow> nat \<Rightarrow> st \<times> Lit list\<close> where
  \<open>shift_step a b left \<equiv> \<lambda>(s, r) k.
     let (s1, e) = eq_m s b (of_nat_m k (length a)) in
     ite_vec_m s1 e (shift_const_m a k left) r\<close>

definition shift_m :: \<open>st \<Rightarrow> Lit list \<Rightarrow> Lit list \<Rightarrow> bool \<Rightarrow> st \<times> Lit list\<close> where
  \<open>shift_m s a b left \<equiv>
     foldl (shift_step a b left) (s, replicate (length a) (lconst False)) [0..<length a]\<close>

definition zext_m :: \<open>Lit list \<Rightarrow> nat \<Rightarrow> Lit list\<close> where
  \<open>zext_m a w \<equiv> map (\<lambda>i. if i < length a then a ! i else lconst False) [0..<w]\<close>

definition extract_m :: \<open>Lit list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> Lit list\<close> where
  \<open>extract_m a hi lo \<equiv> map ((!) a) [lo..<Suc hi]\<close>

definition concat_m :: \<open>Lit list \<Rightarrow> Lit list \<Rightarrow> Lit list\<close> where
  \<open>concat_m hi lo \<equiv> lo @ hi\<close>

definition divrem_m :: \<open>st \<Rightarrow> Lit list \<Rightarrow> Lit list \<Rightarrow> st \<times> Lit list \<times> Lit list\<close> where
  \<open>divrem_m s a b \<equiv>
     let w = length a in
     let (s, q) = fresh_vec_m s w in
     let (s, r) = fresh_vec_m s w in
     let (s, b_zero) = eq_m s b (replicate w (lconst False)) in
     let (s, q_ones) = eq_m s q (replicate w (lconst True)) in
     let (s, r_a) = eq_m s r a in
     let (s, case_zero) = and_m s q_ones r_a in
     let (s, prod) = mul_m s (zext_m q (w + w)) (zext_m b (w + w)) in
     let (s, sm, c) = add_m s prod (zext_m r (w + w)) (lconst False) in
     let (s, sum_a) = eq_m s sm (zext_m a (w + w)) in
     let (s, r_lt) = ult_m s r b in
     let (s, case_nonzero) = and_m s sum_a r_lt in
     let (s, ok) = ite_m s b_zero case_zero case_nonzero in
     (addc_m s [ok], q, r)\<close>

definition blast_bin_m :: \<open>st \<Rightarrow> BinOp \<Rightarrow> Lit list \<Rightarrow> Lit list \<Rightarrow> st \<times> Lit list\<close> where
  \<open>blast_bin_m s op a b \<equiv>
     (case op of
        BinOp_And \<Rightarrow> bitwise_m op s a b
      | BinOp_Or \<Rightarrow> bitwise_m op s a b
      | BinOp_Xor \<Rightarrow> bitwise_m op s a b
      | BinOp_Add \<Rightarrow> (let (s1, r, c) = add_m s a b (lconst False) in (s1, r))
      | BinOp_Mul \<Rightarrow> mul_m s a b
      | BinOp_Udiv \<Rightarrow> (let (s1, q, r) = divrem_m s a b in (s1, q))
      | BinOp_Urem \<Rightarrow> (let (s1, q, r) = divrem_m s a b in (s1, r))
      | BinOp_Shl \<Rightarrow> shift_m s a b True
      | BinOp_Lshr \<Rightarrow> shift_m s a b False
      | BinOp_Concat \<Rightarrow> (s, concat_m a b)
      | BinOp_Eq \<Rightarrow> (let (s1, x) = eq_m s a b in (s1, [x]))
      | BinOp_Ult \<Rightarrow> (let (s1, x) = ult_m s a b in (s1, [x])))\<close>

text \<open>The cwidth of the result of a binary operator on operands of widths \<open>wa\<close>, \<open>wb\<close>.\<close>
definition bin_width :: \<open>BinOp \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>bin_width op wa wb \<equiv>
     (case op of BinOp_Concat \<Rightarrow> wa + wb | BinOp_Eq \<Rightarrow> 1 | BinOp_Ult \<Rightarrow> 1 | _ \<Rightarrow> wa)\<close>

text \<open>\<^verbatim>\<open>blast\<close>, given the literals of the variables and of the definitions.\<close>
primrec blast_m :: \<open>Lit list list \<Rightarrow> Lit list list \<Rightarrow> st \<Rightarrow> CoreTerm \<Rightarrow> st \<times> Lit list\<close> where
  \<open>blast_m vs dl s (CoreTerm_Const bs) = (s, const_m bs)\<close>
| \<open>blast_m vs dl s (CoreTerm_Var i) = (s, vs ! unat i)\<close>
| \<open>blast_m vs dl s (CoreTerm_Ref i) = (s, dl ! unat i)\<close>
| \<open>blast_m vs dl s (CoreTerm_Not a) = (let (s1, la) = blast_m vs dl s a in (s1, not_m la))\<close>
| \<open>blast_m vs dl s (CoreTerm_Bin op a b) =
     (let (s1, la) = blast_m vs dl s a in
      let (s2, lb) = blast_m vs dl s1 b in
      blast_bin_m s2 op la lb)\<close>
| \<open>blast_m vs dl s (CoreTerm_Extract hi lo a) =
     (let (s1, la) = blast_m vs dl s a in (s1, extract_m la (unat hi) (unat lo)))\<close>
| \<open>blast_m vs dl s (CoreTerm_Ite c a b) =
     (let (s1, lc) = blast_m vs dl s c in
      let (s2, la) = blast_m vs dl s1 a in
      let (s3, lb) = blast_m vs dl s2 b in
      ite_vec_m s3 (lc ! 0) la lb)\<close>

subsection \<open>The encoding of a problem\<close>

text \<open>The three loops of \<^verbatim>\<open>encode\<close>: allocate the variables, blast the definitions, blast the
  assertions and assert their bit.\<close>
definition vars_step :: \<open>64 word list \<Rightarrow> st \<times> Lit list list \<Rightarrow> nat \<Rightarrow> st \<times> Lit list list\<close> where
  \<open>vars_step ws \<equiv> \<lambda>(s, vs) i. let (s1, ls) = fresh_vec_m s (unat (ws ! i)) in (s1, vs @ [ls])\<close>

definition defs_step :: \<open>Lit list list \<Rightarrow> CoreTerm list \<Rightarrow> st \<times> Lit list list \<Rightarrow> nat \<Rightarrow> st \<times> Lit list list\<close> where
  \<open>defs_step vs ts \<equiv> \<lambda>(s, dl) j. let (s1, ls) = blast_m vs dl s (ts ! j) in (s1, dl @ [ls])\<close>

definition asserts_step :: \<open>Lit list list \<Rightarrow> Lit list list \<Rightarrow> CoreTerm list \<Rightarrow> st \<Rightarrow> nat \<Rightarrow> st\<close> where
  \<open>asserts_step vs dl ts \<equiv> \<lambda>s k. let (s1, ls) = blast_m vs dl s (ts ! k) in addc_m s1 [ls ! 0]\<close>

definition init_st :: st where
  \<open>init_st \<equiv> (1, [[lconst True]])\<close>

definition encode_m :: \<open>CoreProblem \<Rightarrow> st \<times> Lit list list\<close> where
  \<open>encode_m p \<equiv>
     let (s1, vs) = foldl (vars_step (CoreProblem_widths p)) (init_st, []) [0..<length (CoreProblem_widths p)] in
     let (s2, dl) = foldl (defs_step vs (CoreProblem_defs p)) (s1, []) [0..<length (CoreProblem_defs p)] in
     let s3 = foldl (asserts_step vs dl (CoreProblem_asserts p)) s2 [0..<length (CoreProblem_asserts p)] in
     (s3, vs)\<close>

subsection \<open>DPLL\<close>

definition lit_value_m :: \<open>bool option list \<Rightarrow> Lit \<Rightarrow> bool option\<close> where
  \<open>lit_value_m a l \<equiv> (case a ! unat (Lit_var l) of Some b \<Rightarrow> Some (b \<noteq> Lit_neg l) | None \<Rightarrow> None)\<close>

text \<open>\<^verbatim>\<open>clause_status\<close> on the literals not yet visited, with the loop's state \<open>u\<close> (the
  unassigned literal seen) and \<open>op\<close> (two unassigned literals seen).\<close>
fun status_m :: \<open>bool option list \<Rightarrow> Lit list \<Rightarrow> Lit option \<Rightarrow> bool \<Rightarrow> Status\<close> where
  \<open>status_m a [] u op =
     (if op then Status_Open else (case u of Some l \<Rightarrow> Status_Unit l | None \<Rightarrow> Status_Conflict))\<close>
| \<open>status_m a (l # ls) u op =
     (case lit_value_m a l of
        Some True \<Rightarrow> Status_Satisfied
      | Some False \<Rightarrow> status_m a ls u op
      | None \<Rightarrow> (if u \<noteq> None then status_m a ls u True else status_m a ls (Some l) op))\<close>

text \<open>\<^verbatim>\<open>propagate_pass\<close> on the clauses not yet visited, with the loop's state \<open>a\<close>, \<open>ch\<close>.\<close>
fun pass_m :: \<open>Lit list list \<Rightarrow> bool option list \<Rightarrow> bool \<Rightarrow> (bool option list \<times> bool) option\<close> where
  \<open>pass_m [] a ch = Some (a, ch)\<close>
| \<open>pass_m (c # cs) a ch =
     (case status_m a c None False of
        Status_Conflict \<Rightarrow> None
      | Status_Unit l \<Rightarrow> pass_m cs (a[unat (Lit_var l) := Some (\<not> Lit_neg l)]) True
      | Status_Satisfied \<Rightarrow> pass_m cs a ch
      | Status_Open \<Rightarrow> pass_m cs a ch)\<close>

definition read_bits_m :: \<open>bool option list \<Rightarrow> Lit list \<Rightarrow> bool list\<close> where
  \<open>read_bits_m a ls \<equiv> map (\<lambda>l. lit_value_m a l = Some True) ls\<close>

definition read_model_m :: \<open>bool option list \<Rightarrow> Lit list list \<Rightarrow> bool list list\<close> where
  \<open>read_model_m a vs \<equiv> map (read_bits_m a) vs\<close>

section \<open>Semantics of CNF formulas\<close>

text \<open>An assignment \<open>\<sigma>\<close> of all variables.\<close>
definition lit_sem :: \<open>(nat \<Rightarrow> bool) \<Rightarrow> Lit \<Rightarrow> bool\<close> where
  \<open>lit_sem \<sigma> l \<equiv> \<sigma> (unat (Lit_var l)) \<noteq> Lit_neg l\<close>

definition cnf_sem :: \<open>(nat \<Rightarrow> bool) \<Rightarrow> Lit list list \<Rightarrow> bool\<close> where
  \<open>cnf_sem \<sigma> cs \<equiv> \<forall>c \<in> set cs. \<exists>l \<in> set c. lit_sem \<sigma> l\<close>

text \<open>The number a list of literals denotes under \<open>\<sigma>\<close>.\<close>
definition val :: \<open>(nat \<Rightarrow> bool) \<Rightarrow> Lit list \<Rightarrow> nat\<close> where
  \<open>val \<sigma> ls \<equiv> bits_nat (map (lit_sem \<sigma>) ls)\<close>

text \<open>Every literal's variable is below \<open>n\<close>.\<close>
definition lits_lt :: \<open>nat \<Rightarrow> Lit list \<Rightarrow> bool\<close> where
  \<open>lits_lt n ls \<equiv> \<forall>l \<in> set ls. unat (Lit_var l) < n\<close>

text \<open>A well-formed state: the clauses mention only allocated variables, and assert that variable
  0 is true.\<close>
definition wf_st :: \<open>st \<Rightarrow> bool\<close> where
  \<open>wf_st s \<equiv> (\<forall>c \<in> set (snd s). lits_lt (fst s) c) \<and> [lconst True] \<in> set (snd s) \<and> 0 < fst s\<close>

text \<open>\<open>s'\<close> extends \<open>s\<close>: more variables, more clauses, and every assignment satisfying \<open>s\<close> can be
  changed on the new variables to satisfy \<open>s'\<close>.\<close>
definition ext :: \<open>st \<Rightarrow> st \<Rightarrow> bool\<close> where
  \<open>ext s s' \<equiv>
     fst s \<le> fst s' \<and> (\<exists>cs. snd s' = snd s @ cs) \<and>
     (\<forall>\<sigma>. cnf_sem \<sigma> (snd s) \<longrightarrow> (\<exists>\<sigma>'. (\<forall>v < fst s. \<sigma>' v = \<sigma> v) \<and> cnf_sem \<sigma>' (snd s')))\<close>

text \<open>A partial assignment \<open>a\<close> and the total assignments \<open>\<sigma>\<close> that agree with it.\<close>
definition agrees :: \<open>bool option list \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>agrees a \<sigma> \<equiv> \<forall>v < length a. \<forall>b. a ! v = Some b \<longrightarrow> \<sigma> v = b\<close>

text \<open>The total assignment of a partial assignment (unassigned variables false).\<close>
definition sigma_of :: \<open>bool option list \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>sigma_of a v \<equiv> (v < length a \<and> a ! v = Some True)\<close>

section \<open>Bounds\<close>

text \<open>A bound on the iterations of every loop that blasting \<open>t\<close> runs (each loop runs over at
  most twice the cwidth of a subterm) and on the depth of the recursion.\<close>
definition tbound :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> CoreTerm \<Rightarrow> nat\<close> where
  \<open>tbound ws ds t \<equiv> max (Suc (size t)) (Max (set (map (\<lambda>u. 2 * cwidth ws ds u + 2) (csubterms t))))\<close>

text \<open>The fuel the solver needs: a bound on the iterations of every loop and on the depth of
  every recursion, for the problem \<open>p\<close>. It depends on \<open>p\<close> only.\<close>
definition fuel_bound :: \<open>CoreProblem \<Rightarrow> nat\<close> where
  \<open>fuel_bound p \<equiv>
     let ws = cvar_widths p in
     let ds = cdef_widths ws [] (CoreProblem_defs p) in
     let (s, vs) = encode_m p in
     Max ({fst s + 2, length (snd s) + 2, length ws + 2, length (CoreProblem_defs p) + 2,
           length (CoreProblem_asserts p) + 2} \<union>
          set (map (\<lambda>w. w + 2) ws) \<union>
          set (map (\<lambda>c. length c + 2) (snd s)) \<union>
          set (map (tbound ws ds) (CoreProblem_defs p @ CoreProblem_asserts p)))\<close>

end
