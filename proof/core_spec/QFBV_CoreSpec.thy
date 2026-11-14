theory QFBV_CoreSpec
  imports "QFBV_Spec.QFBV_Spec"
begin

section \<open>The specification of the core solver\<close>

text \<open>
  OVERVIEW

  The Rust entry point is \<^verbatim>\<open>pub fn solve(p: &Problem) -> Answer\<close> (\<^verbatim>\<open>core/src/lib.rs\<close>), translated
  to \<^verbatim>\<open>QFBV_ctx.solve\<close>. A problem has variables of the widths \<^const>\<open>Problem_widths\<close>,
  definitions \<^const>\<open>Problem_defs\<close> (each may refer to the earlier ones by \<^const>\<open>Term_Ref\<close>), and
  assertions \<^const>\<open>Problem_asserts\<close> (terms of width 1). Booleans are bit-vectors of width 1, true
  being 1. Bit lists are least significant bit first.

  The specification: for a well-sorted problem, the answer \<open>Sat m\<close> gives a model \<open>m\<close>: an
  assignment (bits of every variable, of the declared widths) under which every assertion
  evaluates to 1; the answer \<open>Unsat\<close> means that no model exists.

  The statement \<open>solve_correct\<close> at the end of this theory: for every well-sorted problem
  (\<open>problem_wt\<close>) whose \<open>size_bound\<close> is less than \<open>2^64\<close> (\<open>sizes_ok\<close>), there is a number \<open>N\<close>
  such that the solver, translated with any fuel \<open>\<ge> N\<close>, satisfies the contract (and so does not
  panic). For a problem that is not well-sorted, or whose \<open>size_bound\<close> is not below \<open>2^64\<close>, the
  statement says nothing.

  The input of the solver is a value of type \<^typ>\<open>Problem\<close>, not SMT-LIB text. Its terms
  (\<^typ>\<open>Term\<close>) have a constructor for every function symbol of the theory FixedSizeBitVectors and of
  the logic QF_BV of SMT-LIB 2.6 (\<^verbatim>\<open>spec/smtlib-2.6/\<close> holds the two source files), and for \<open>=\<close>,
  \<open>distinct\<close> and \<open>ite\<close> of the Core theory on bit-vectors. Each constructor takes the operands of the
  binary form in which SMT-LIB defines the function. This core is reached through
  \<^verbatim>\<open>check_sat\<close> (\<^verbatim>\<open>QFBV_Spec\<close>), which takes a general problem
  (\<^typ>\<open>SmtProblem\<close>, built by the unverified SMT-LIB front end \<^verbatim>\<open>frontend/\<close>) and translates
  it into a \<^typ>\<open>Problem\<close>: the forms that SMT-LIB defines as abbreviations of the binary ones
  (\<open>bvand\<close>, \<open>bvor\<close>, \<open>bvadd\<close>, \<open>bvmul\<close>, \<open>bvxor\<close> with more than two operands, and \<open>distinct\<close> and
  \<open>=\<close> with more than two operands), definitions with parameters, and the Bool terms of the Core
  theory (Bool is read as width 1) are handled by that translation, which is verified.
  The function symbols, by source:

  \<^item> FixedSizeBitVectors: \<open>concat\<close>, \<open>extract\<close>, \<open>bvnot\<close>, \<open>bvneg\<close>, \<open>bvand\<close>, \<open>bvor\<close>, \<open>bvadd\<close>, \<open>bvmul\<close>,
    \<open>bvudiv\<close>, \<open>bvurem\<close>, \<open>bvshl\<close>, \<open>bvlshr\<close>, \<open>bvult\<close> (section \<open>:definition\<close> of the theory).
  \<^item> QF_BV (section \<open>:extensions\<close> of the logic): \<open>bvnand\<close>, \<open>bvnor\<close>, \<open>bvxor\<close>, \<open>bvxnor\<close>, \<open>bvcomp\<close>,
    \<open>bvsub\<close>, \<open>bvsdiv\<close>, \<open>bvsrem\<close>, \<open>bvsmod\<close>, \<open>bvashr\<close>, \<open>repeat\<close>, \<open>zero_extend\<close>, \<open>sign_extend\<close>,
    \<open>rotate_left\<close>, \<open>rotate_right\<close>, \<open>bvule\<close>, \<open>bvugt\<close>, \<open>bvuge\<close>, \<open>bvslt\<close>, \<open>bvsle\<close>, \<open>bvsgt\<close>, \<open>bvsge\<close>.

  Semantics. SMT-LIB gives the meaning of a bit-vector of width \<open>w\<close> as a natural number below \<open>2^w\<close>
  (\<open>bv2nat\<close>); this specification uses these numbers as the values of terms (\<open>eval\<close>). The
  functions of FixedSizeBitVectors are defined on numbers in the theory itself; each is
  transcribed below (\<open>bin_sem\<close>, \<open>eval\<close>) with the text of the theory beside it. The
  functions of QF_BV are defined in the logic as abbreviations of other terms; for each one, the
  definition below gives the number the abbreviated term denotes, as a function of the values of
  the operands, with the text of the logic beside it. The signed operations read a value as a
  two's complement integer (\<open>sint\<close>, the \<open>bv2int\<close> of SMT-LIB) and take the result modulo
  \<open>2^w\<close> (\<open>to_bv\<close>, the \<open>nat2bv\<close> of SMT-LIB); division by zero follows the text of SMT-LIB
  (\<open>bvudiv\<close> by 0 is all ones, \<open>bvurem\<close> by 0 is the dividend, and the signed operations inherit
  their behaviour from these).

  Widths: SMT-LIB requires every bit-vector width to be at least 1. \<open>wt\<close> requires it of every
  constant, variable and definition that a term refers to, so every width that occurs in a term is
  at least 1. \<open>problem_wt\<close> does not look at variables that no term refers to: such a variable
  may be declared with width 0, and an assignment then gives it the empty bit list. It does not
  change the value of any term.

  Choices of the transcription:
  \<^item> \<^verbatim>\<open>usize\<close> fields are @{typ \<open>64 word\<close>}; widths and indices are read with \<^const>\<open>unat\<close>.
  \<^item> \<open>xs ! i\<close> is unspecified out of bounds; \<open>wt\<close> keeps every index in bounds.
  \<^item> The problem is passed by shared reference, which the translation passes by value.
  \<^item> \<open>can_alloc_reference\<close>: the solver allocates mutable locals; this is AutoCorrode's requirement.
  \<^item> \<^const>\<open>make_function_contract\<close> makes the abort postcondition false: the contract also states
    that the solver does not panic (no out-of-bounds index, no arithmetic overflow).
  \<^item> The translation bounds every loop and the recursion by the locale parameter
    \<^term>\<open>urust_fuel\<close> and panics when it runs out. \<open>solve_correct\<close> quantifies the fuel:
    it states that some fuel suffices, and that every larger fuel suffices too. It does not
    say how large the fuel must be.

  Trusted, not proved here:
  \<^item> The translation (AutoCorrode) gives the Rust program its meaning. The theorem is about the
    translated function. That it carries over to the compiled Rust program rests on the
    translation: with enough fuel, the translated function does what the Rust function does,
    and fuel only adds a panic when it runs out.
  \<^item> \<open>solve_correct\<close> is stated in the locale \<open>QFBV_heap\<close>, whose assumptions describe a heap with
    one kind of reference per type of mutable local. This theory gives no interpretation of the
    locale. As in other AutoCorrode developments, the assumptions are those of AutoCorrode's
    reference model, and the theorem holds for every heap that satisfies them.
\<close>

subsection \<open>Values\<close>

text \<open>The number a bit list denotes, least significant bit first (\<open>bv2nat\<close>).\<close>
fun bits_nat :: \<open>bool list \<Rightarrow> nat\<close> where
  \<open>bits_nat [] = 0\<close>
| \<open>bits_nat (b # bs) = of_bool b + 2 * bits_nat bs\<close>

text \<open>The two's complement reading of a value \<open>x\<close> of width \<open>w\<close> (\<open>bv2int\<close>): \<open>x\<close> itself if its most
  significant bit is 0, otherwise \<open>x - 2^w\<close>.\<close>
definition sint :: \<open>nat \<Rightarrow> nat \<Rightarrow> int\<close> where
  \<open>sint w x \<equiv> if x < 2 ^ (w - 1) then int x else int x - 2 ^ w\<close>

text \<open>The value of width \<open>w\<close> of an integer (\<open>nat2bv[w]\<close>, extended to negative integers): the
  integer modulo \<open>2^w\<close>, in \<open>[0, 2^w)\<close>.\<close>
definition to_bv :: \<open>nat \<Rightarrow> int \<Rightarrow> nat\<close> where
  \<open>to_bv w z \<equiv> nat (z mod 2 ^ w)\<close>

text \<open>Integer division rounding towards zero, and its remainder (which has the sign of the
  dividend), for a divisor other than 0.\<close>
definition tdiv :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close> where
  \<open>tdiv a b \<equiv> if (a < 0) = (b < 0) then \<bar>a\<bar> div \<bar>b\<bar> else - (\<bar>a\<bar> div \<bar>b\<bar>)\<close>

definition tmod :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close> where
  \<open>tmod a b \<equiv> a - b * tdiv a b\<close>

text \<open>The value of \<open>((_ repeat i) t)\<close> for a value \<open>x\<close> of width \<open>w\<close>. QF_BV: \<open>((_ repeat 1) t)\<close> stands
  for \<open>t\<close>, and \<open>((_ repeat j) t)\<close> abbreviates \<open>(concat t ((_ repeat |j-1|) t))\<close>: \<open>x\<close> above the
  \<open>w * (j - 1)\<close> bits of the rest.\<close>
fun repeat_val :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>repeat_val w 0 x = 0\<close>
| \<open>repeat_val w (Suc j) x = x * 2 ^ (w * j) + repeat_val w j x\<close>

subsection \<open>Sorts\<close>

text \<open>The width of a term, given the widths \<open>ws\<close> of the variables and \<open>ds\<close> of the definitions.
  Sorts of QF_BV: \<open>concat\<close> of widths \<open>i\<close>, \<open>j\<close> has width \<open>i + j\<close>; \<open>((_ extract i j) s)\<close> has width
  \<open>i - j + 1\<close>; \<open>bvcomp\<close> has width 1; the predicates are Boolean (width 1 here); \<open>((_ repeat i) s)\<close>
  has width \<open>i * m\<close>; \<open>zero_extend\<close> and \<open>sign_extend\<close> by \<open>i\<close> have width \<open>m + i\<close>; every other
  function has the width \<open>m\<close> of its operands.\<close>
fun width :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> Term \<Rightarrow> nat\<close> where
  \<open>width ws ds (Term_Const bs) = length bs\<close>
| \<open>width ws ds (Term_Var i) = ws ! unat i\<close>
| \<open>width ws ds (Term_Ref i) = ds ! unat i\<close>
| \<open>width ws ds (Term_Not a) = width ws ds a\<close>
| \<open>width ws ds (Term_Neg a) = width ws ds a\<close>
| \<open>width ws ds (Term_Bin op a b) =
     (case op of
        Op_Concat \<Rightarrow> width ws ds a + width ws ds b
      | Op_Comp \<Rightarrow> 1
      | Op_Eq \<Rightarrow> 1 | Op_Distinct \<Rightarrow> 1
      | Op_Ult \<Rightarrow> 1 | Op_Ule \<Rightarrow> 1 | Op_Ugt \<Rightarrow> 1 | Op_Uge \<Rightarrow> 1
      | Op_Slt \<Rightarrow> 1 | Op_Sle \<Rightarrow> 1 | Op_Sgt \<Rightarrow> 1 | Op_Sge \<Rightarrow> 1
      | _ \<Rightarrow> width ws ds a)\<close>
| \<open>width ws ds (Term_Extract hi lo a) = unat hi - unat lo + 1\<close>
| \<open>width ws ds (Term_Repeat i a) = unat i * width ws ds a\<close>
| \<open>width ws ds (Term_ZeroExtend i a) = width ws ds a + unat i\<close>
| \<open>width ws ds (Term_SignExtend i a) = width ws ds a + unat i\<close>
| \<open>width ws ds (Term_RotateLeft i a) = width ws ds a\<close>
| \<open>width ws ds (Term_RotateRight i a) = width ws ds a\<close>
| \<open>width ws ds (Term_Ite c a b) = width ws ds a\<close>

text \<open>Well-sortedness, following the sort declarations of SMT-LIB: every width is at least 1
  (\<open>m > 0\<close>); indices are in bounds; the operands of a binary function other than \<open>concat\<close> have
  equal widths; \<open>((_ extract i j) s)\<close> needs \<open>m > i \<ge> j \<ge> 0\<close>; \<open>repeat\<close> needs \<open>i \<ge> 1\<close>; the condition
  of \<open>ite\<close> is Boolean (width 1) and its branches have equal widths.\<close>
fun wt :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> Term \<Rightarrow> bool\<close> where
  \<open>wt ws ds (Term_Const bs) = (0 < length bs)\<close>
| \<open>wt ws ds (Term_Var i) = (unat i < length ws \<and> 0 < ws ! unat i)\<close>
| \<open>wt ws ds (Term_Ref i) = (unat i < length ds \<and> 0 < ds ! unat i)\<close>
| \<open>wt ws ds (Term_Not a) = wt ws ds a\<close>
| \<open>wt ws ds (Term_Neg a) = wt ws ds a\<close>
| \<open>wt ws ds (Term_Bin op a b) =
     (wt ws ds a \<and> wt ws ds b \<and> (op \<noteq> Op_Concat \<longrightarrow> width ws ds a = width ws ds b))\<close>
| \<open>wt ws ds (Term_Extract hi lo a) = (wt ws ds a \<and> unat lo \<le> unat hi \<and> unat hi < width ws ds a)\<close>
| \<open>wt ws ds (Term_Repeat i a) = (wt ws ds a \<and> 1 \<le> unat i)\<close>
| \<open>wt ws ds (Term_ZeroExtend i a) = wt ws ds a\<close>
| \<open>wt ws ds (Term_SignExtend i a) = wt ws ds a\<close>
| \<open>wt ws ds (Term_RotateLeft i a) = wt ws ds a\<close>
| \<open>wt ws ds (Term_RotateRight i a) = wt ws ds a\<close>
| \<open>wt ws ds (Term_Ite c a b) =
     (wt ws ds c \<and> wt ws ds a \<and> wt ws ds b \<and> width ws ds c = 1 \<and> width ws ds a = width ws ds b)\<close>

subsection \<open>Evaluation\<close>

text \<open>A binary function on the values \<open>x\<close>, \<open>y\<close> of operands of widths \<open>w\<close>, \<open>v\<close> (\<open>v = w\<close> except for
  \<open>concat\<close>). The text of SMT-LIB 2.6 is quoted for each case; \<open>s\<close>, \<open>t\<close> are the operands,
  \<open>m\<close> their width.

  FixedSizeBitVectors, \<open>:definition\<close>:
  \<^item> \<open>bvand\<close>, \<open>bvor\<close>: \<open>[[(bvand s t)]] := \<lambda>x:[0, m). if [[s]](x) = 0 then 0 else [[t]](x)\<close>,
    \<open>[[(bvor s t)]] := \<lambda>x:[0, m). if [[s]](x) = 1 then 1 else [[t]](x)\<close>: the bitwise operations
    on numbers (\<^const>\<open>Bit_Operations.and\<close>, \<^const>\<open>Bit_Operations.or\<close>).
  \<^item> \<open>bvadd\<close>: \<open>nat2bv[m](bv2nat([[s]]) + bv2nat([[t]]))\<close>; \<open>bvmul\<close>: \<open>nat2bv[m](bv2nat([[s]]) * bv2nat([[t]]))\<close>.
  \<^item> \<open>bvudiv\<close>: \<open>if bv2nat([[t]]) = 0 then \<lambda>x:[0, m). 1 else nat2bv[m](bv2nat([[s]]) div bv2nat([[t]]))\<close>.
  \<^item> \<open>bvurem\<close>: \<open>if bv2nat([[t]]) = 0 then [[s]] else nat2bv[m](bv2nat([[s]]) rem bv2nat([[t]]))\<close>.
  \<^item> \<open>bvshl\<close>: \<open>nat2bv[m](bv2nat([[s]]) * 2^(bv2nat([[t]])))\<close>; \<open>bvlshr\<close>: \<open>nat2bv[m](bv2nat([[s]]) div 2^(bv2nat([[t]])))\<close>.
  \<^item> \<open>concat\<close>: \<open>\<lambda>x:[0, n+m). if (x < m) then [[t]](x) else [[s]](x - m)\<close> where \<open>t\<close> has width \<open>m\<close>:
    \<open>s\<close> above the \<open>m\<close> bits of \<open>t\<close>.
  \<^item> \<open>bvult\<close>: \<open>true iff bv2nat([[s]]) < bv2nat([[t]])\<close>.

  QF_BV, \<open>:extensions\<close>:
  \<^item> \<open>bvnand s t\<close> abbreviates \<open>(bvnot (bvand s t))\<close>; \<open>bvnor\<close>: \<open>(bvnot (bvor s t))\<close>.
  \<^item> \<open>bvxor s t\<close> abbreviates \<open>(bvor (bvand s (bvnot t)) (bvand (bvnot s) t))\<close>: the bitwise exclusive
    or; \<open>bvxnor s t\<close> abbreviates \<open>(bvor (bvand s t) (bvand (bvnot s) (bvnot t)))\<close>: its negation.
  \<^item> \<open>bvcomp s t\<close>: \<open>bvxnor\<close> of the bits, conjoined over all bits: \<open>#b1\<close> iff \<open>s\<close> and \<open>t\<close> are equal.
  \<^item> \<open>bvsub s t\<close> abbreviates \<open>(bvadd s (bvneg t))\<close>: \<open>s - t\<close> modulo \<open>2^m\<close>.
  \<^item> \<open>bvsdiv s t\<close>: \<open>(bvudiv s t)\<close> if both sign bits are 0; \<open>(bvneg (bvudiv (bvneg s) t))\<close> if they are
    1, 0; \<open>(bvneg (bvudiv s (bvneg t)))\<close> if 0, 1; \<open>(bvudiv (bvneg s) (bvneg t))\<close> if 1, 1. For
    \<open>t \<noteq> 0\<close>, this is the quotient of the two's complement values rounded towards zero
    (\<^const>\<open>tdiv\<close>), modulo \<open>2^m\<close>. For \<open>t = 0\<close> (sign bit 0), \<open>bvudiv\<close> by 0 gives all ones: the result
    is all ones (\<open>2^m - 1\<close>) when the sign bit of \<open>s\<close> is 0, and \<open>bvneg\<close> of all ones, 1, when it is 1.
  \<^item> \<open>bvsrem s t\<close>: \<open>(bvurem s t)\<close>; \<open>(bvneg (bvurem (bvneg s) t))\<close>; \<open>(bvurem s (bvneg t))\<close>;
    \<open>(bvneg (bvurem (bvneg s) (bvneg t)))\<close> for the same four cases: the remainder of that
    division, with the sign of \<open>s\<close> (\<^const>\<open>tmod\<close>), modulo \<open>2^m\<close>. For \<open>t = 0\<close>, \<open>bvurem\<close> by 0 gives
    the dividend, so the result is \<open>s\<close>.
  \<^item> \<open>bvsmod s t\<close>: with \<open>u = (bvurem abs_s abs_t)\<close> of the absolute values: \<open>u\<close> if \<open>u = 0\<close> or both sign
    bits are 0; \<open>(bvadd (bvneg u) t)\<close> if they are 1, 0; \<open>(bvadd u t)\<close> if 0, 1; \<open>(bvneg u)\<close> if 1, 1.
    For \<open>t \<noteq> 0\<close>, this is the remainder with the sign of \<open>t\<close>: \<open>mod\<close> of the two's complement values
    (the \<open>mod\<close> of Isabelle/HOL rounds the quotient down), modulo \<open>2^m\<close>. For \<open>t = 0\<close>, \<open>u\<close> is
    \<open>abs_s\<close> and every case gives \<open>s\<close>.
  \<^item> \<open>bvashr s t\<close> abbreviates \<open>(ite (= ((_ extract |m-1| |m-1|) s) #b0) (bvlshr s t) (bvnot (bvlshr (bvnot s) t)))\<close>:
    the two's complement value of \<open>s\<close> divided by \<open>2^t\<close>, rounded down, modulo \<open>2^m\<close>.
  \<^item> \<open>bvule s t\<close> abbreviates \<open>(or (bvult s t) (= s t))\<close>; \<open>bvugt s t\<close>: \<open>(bvult t s)\<close>; \<open>bvuge s t\<close>:
    \<open>(or (bvult t s) (= s t))\<close>.
  \<^item> \<open>bvslt s t\<close> abbreviates \<open>(or (and (= msb_s #b1) (= msb_t #b0)) (and (= msb_s msb_t) (bvult s t)))\<close>:
    the two's complement value of \<open>s\<close> is below that of \<open>t\<close>; \<open>bvsle\<close>: the same with \<open>bvule\<close>;
    \<open>bvsgt s t\<close>: \<open>(bvslt t s)\<close>; \<open>bvsge s t\<close>: \<open>(bvsle t s)\<close>.
  Core theory: \<open>=\<close> is true iff the values are equal, \<open>distinct\<close> iff they differ.\<close>
fun bin_sem :: \<open>Op \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>bin_sem Op_And w x v y = Bit_Operations.and x y\<close>
| \<open>bin_sem Op_Or w x v y = Bit_Operations.or x y\<close>
| \<open>bin_sem Op_Xor w x v y = Bit_Operations.xor x y\<close>
| \<open>bin_sem Op_Nand w x v y = 2 ^ w - 1 - Bit_Operations.and x y\<close>
| \<open>bin_sem Op_Nor w x v y = 2 ^ w - 1 - Bit_Operations.or x y\<close>
| \<open>bin_sem Op_Xnor w x v y = 2 ^ w - 1 - Bit_Operations.xor x y\<close>
| \<open>bin_sem Op_Comp w x v y = of_bool (x = y)\<close>
| \<open>bin_sem Op_Add w x v y = (x + y) mod 2 ^ w\<close>
| \<open>bin_sem Op_Sub w x v y = (x + (2 ^ w - y)) mod 2 ^ w\<close>
| \<open>bin_sem Op_Mul w x v y = (x * y) mod 2 ^ w\<close>
| \<open>bin_sem Op_Udiv w x v y = (if y = 0 then 2 ^ w - 1 else x div y)\<close>
| \<open>bin_sem Op_Urem w x v y = (if y = 0 then x else x mod y)\<close>
| \<open>bin_sem Op_Sdiv w x v y =
     (if y = 0 then (if sint w x < 0 then 1 else 2 ^ w - 1)
      else to_bv w (tdiv (sint w x) (sint w y)))\<close>
| \<open>bin_sem Op_Srem w x v y = (if y = 0 then x else to_bv w (tmod (sint w x) (sint w y)))\<close>
| \<open>bin_sem Op_Smod w x v y = (if y = 0 then x else to_bv w (sint w x mod sint w y))\<close>
| \<open>bin_sem Op_Shl w x v y = (x * 2 ^ y) mod 2 ^ w\<close>
| \<open>bin_sem Op_Lshr w x v y = x div 2 ^ y\<close>
| \<open>bin_sem Op_Ashr w x v y = to_bv w (sint w x div 2 ^ y)\<close>
| \<open>bin_sem Op_Concat w x v y = x * 2 ^ v + y\<close>
| \<open>bin_sem Op_Eq w x v y = of_bool (x = y)\<close>
| \<open>bin_sem Op_Distinct w x v y = of_bool (x \<noteq> y)\<close>
| \<open>bin_sem Op_Ult w x v y = of_bool (x < y)\<close>
| \<open>bin_sem Op_Ule w x v y = of_bool (x \<le> y)\<close>
| \<open>bin_sem Op_Ugt w x v y = of_bool (y < x)\<close>
| \<open>bin_sem Op_Uge w x v y = of_bool (y \<le> x)\<close>
| \<open>bin_sem Op_Slt w x v y = of_bool (sint w x < sint w y)\<close>
| \<open>bin_sem Op_Sle w x v y = of_bool (sint w x \<le> sint w y)\<close>
| \<open>bin_sem Op_Sgt w x v y = of_bool (sint w y < sint w x)\<close>
| \<open>bin_sem Op_Sge w x v y = of_bool (sint w y \<le> sint w x)\<close>

text \<open>The value of a term, given the widths \<open>ws\<close>, \<open>ds\<close> and the values \<open>vs\<close>, \<open>dv\<close> of the variables
  and the definitions. The unary and the indexed functions, with the text of SMT-LIB 2.6 (\<open>s\<close> or
  \<open>t\<close> the operand of width \<open>m\<close>, value \<open>x\<close>):
  \<^item> \<open>bvnot\<close>: \<open>\<lambda>x:[0, m). if [[s]](x) = 0 then 1 else 0\<close>: every bit flipped, \<open>2^m - 1 - x\<close>.
  \<^item> \<open>bvneg\<close>: \<open>nat2bv[m](2^m - bv2nat([[s]]))\<close>.
  \<^item> \<open>((_ extract i j) s)\<close>: \<open>\<lambda>x:[0, i-j+1). [[s]](j + x)\<close>: bits \<open>j\<close> to \<open>i\<close>.
  \<^item> \<open>((_ repeat i) t)\<close>: see \<^const>\<open>repeat_val\<close>.
  \<^item> \<open>((_ zero_extend i) t)\<close> abbreviates \<open>(concat ((_ repeat i) #b0) t)\<close> (and \<open>t\<close> for \<open>i = 0\<close>): the
    value is unchanged.
  \<^item> \<open>((_ sign_extend i) t)\<close> abbreviates \<open>(concat ((_ repeat i) ((_ extract |m-1| |m-1|) t)) t)\<close>: the
    two's complement value of \<open>t\<close>, as a value of width \<open>m + i\<close>.
  \<^item> \<open>((_ rotate_left i) t)\<close> abbreviates \<open>((_ rotate_left |i-1|) (concat ((_ extract |m-2| 0) t) ((_ extract |m-1| |m-1|) t)))\<close>
    (and \<open>t\<close> for \<open>i = 0\<close> or \<open>m = 1\<close>): \<open>i\<close> times, every bit moves up one place and the top bit
    moves to the bottom. With \<open>r = i mod m\<close>, the low \<open>m - r\<close> bits of \<open>t\<close> end up above its high
    \<open>r\<close> bits.
  \<^item> \<open>((_ rotate_right i) t)\<close> abbreviates \<open>((_ rotate_right |i-1|) (concat ((_ extract 0 0) t) ((_ extract |m-1| 1) t)))\<close>:
    \<open>i\<close> times, every bit moves down one place and the bottom bit moves to the top. With
    \<open>r = i mod m\<close>, the low \<open>r\<close> bits of \<open>t\<close> end up above its high \<open>m - r\<close> bits.
  \<^item> \<open>ite c a b\<close> (Core): \<open>a\<close> iff \<open>c\<close> is true (1).\<close>
fun eval :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> Term \<Rightarrow> nat\<close> where
  \<open>eval ws ds vs dv (Term_Const bs) = bits_nat bs\<close>
| \<open>eval ws ds vs dv (Term_Var i) = vs ! unat i\<close>
| \<open>eval ws ds vs dv (Term_Ref i) = dv ! unat i\<close>
| \<open>eval ws ds vs dv (Term_Not a) = 2 ^ width ws ds a - 1 - eval ws ds vs dv a\<close>
| \<open>eval ws ds vs dv (Term_Neg a) = (2 ^ width ws ds a - eval ws ds vs dv a) mod 2 ^ width ws ds a\<close>
| \<open>eval ws ds vs dv (Term_Bin op a b) =
     bin_sem op (width ws ds a) (eval ws ds vs dv a) (width ws ds b) (eval ws ds vs dv b)\<close>
| \<open>eval ws ds vs dv (Term_Extract hi lo a) =
     (eval ws ds vs dv a div 2 ^ unat lo) mod 2 ^ (unat hi - unat lo + 1)\<close>
| \<open>eval ws ds vs dv (Term_Repeat i a) = repeat_val (width ws ds a) (unat i) (eval ws ds vs dv a)\<close>
| \<open>eval ws ds vs dv (Term_ZeroExtend i a) = eval ws ds vs dv a\<close>
| \<open>eval ws ds vs dv (Term_SignExtend i a) =
     to_bv (width ws ds a + unat i) (sint (width ws ds a) (eval ws ds vs dv a))\<close>
| \<open>eval ws ds vs dv (Term_RotateLeft i a) =
     (let w = width ws ds a; r = unat i mod w; x = eval ws ds vs dv a in
      (x mod 2 ^ (w - r)) * 2 ^ r + x div 2 ^ (w - r))\<close>
| \<open>eval ws ds vs dv (Term_RotateRight i a) =
     (let w = width ws ds a; r = unat i mod w; x = eval ws ds vs dv a in
      (x mod 2 ^ r) * 2 ^ (w - r) + x div 2 ^ r)\<close>
| \<open>eval ws ds vs dv (Term_Ite c a b) =
     (if eval ws ds vs dv c = 1 then eval ws ds vs dv a else eval ws ds vs dv b)\<close>

subsection \<open>Problems\<close>

text \<open>The definitions in order: each is well-sorted over the earlier ones.\<close>
fun defs_wt :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> Term list \<Rightarrow> bool\<close> where
  \<open>defs_wt ws ds [] = True\<close>
| \<open>defs_wt ws ds (d # dd) = (wt ws ds d \<and> defs_wt ws (ds @ [width ws ds d]) dd)\<close>

text \<open>The widths of the definitions, appended to \<open>ds\<close>.\<close>
fun def_widths :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> Term list \<Rightarrow> nat list\<close> where
  \<open>def_widths ws ds [] = ds\<close>
| \<open>def_widths ws ds (d # dd) = def_widths ws (ds @ [width ws ds d]) dd\<close>

text \<open>The values of the definitions, appended to \<open>dv\<close> (the values of definitions of widths \<open>ds\<close>), given
  the widths \<open>ws\<close> and values \<open>vs\<close> of the variables.\<close>
fun def_values :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> Term list \<Rightarrow> nat list\<close> where
  \<open>def_values ws ds vs dv [] = dv\<close>
| \<open>def_values ws ds vs dv (d # dd) =
     def_values ws (ds @ [width ws ds d]) vs (dv @ [eval ws ds vs dv d]) dd\<close>

definition var_widths :: \<open>Problem \<Rightarrow> nat list\<close> where
  \<open>var_widths p \<equiv> map unat (Problem_widths p)\<close>

text \<open>A well-sorted problem: well-sorted definitions and assertions of width 1.\<close>
definition problem_wt :: \<open>Problem \<Rightarrow> bool\<close> where
  \<open>problem_wt p \<equiv>
     let ws = var_widths p in
     let ds = def_widths ws [] (Problem_defs p) in
     defs_wt ws [] (Problem_defs p) \<and>
     (\<forall>t \<in> set (Problem_asserts p). wt ws ds t \<and> width ws ds t = 1)\<close>

text \<open>An assignment gives every variable a bit list of its width.\<close>
definition is_assignment :: \<open>Problem \<Rightarrow> bool list list \<Rightarrow> bool\<close> where
  \<open>is_assignment p m \<equiv> map length m = var_widths p\<close>

text \<open>Every assertion evaluates to 1 under the assignment.\<close>
definition satisfies :: \<open>Problem \<Rightarrow> bool list list \<Rightarrow> bool\<close> where
  \<open>satisfies p m \<equiv>
     let ws = var_widths p in
     let vs = map bits_nat m in
     let ds = def_widths ws [] (Problem_defs p) in
     let dv = def_values ws [] vs [] (Problem_defs p) in
     \<forall>t \<in> set (Problem_asserts p). eval ws ds vs dv t = 1\<close>

text \<open>A model is an assignment under which every assertion evaluates to 1.\<close>
definition is_model :: \<open>Problem \<Rightarrow> bool list list \<Rightarrow> bool\<close> where
  \<open>is_model p m \<equiv> is_assignment p m \<and> satisfies p m\<close>

subsection \<open>The size of a problem\<close>

text \<open>The subterms of a term, the term included.\<close>
primrec subterms :: \<open>Term \<Rightarrow> Term list\<close> where
  \<open>subterms (Term_Const bs) = [Term_Const bs]\<close>
| \<open>subterms (Term_Var i) = [Term_Var i]\<close>
| \<open>subterms (Term_Ref i) = [Term_Ref i]\<close>
| \<open>subterms (Term_Not a) = Term_Not a # subterms a\<close>
| \<open>subterms (Term_Neg a) = Term_Neg a # subterms a\<close>
| \<open>subterms (Term_Bin op a b) = Term_Bin op a b # subterms a @ subterms b\<close>
| \<open>subterms (Term_Extract hi lo a) = Term_Extract hi lo a # subterms a\<close>
| \<open>subterms (Term_Repeat i a) = Term_Repeat i a # subterms a\<close>
| \<open>subterms (Term_ZeroExtend i a) = Term_ZeroExtend i a # subterms a\<close>
| \<open>subterms (Term_SignExtend i a) = Term_SignExtend i a # subterms a\<close>
| \<open>subterms (Term_RotateLeft i a) = Term_RotateLeft i a # subterms a\<close>
| \<open>subterms (Term_RotateRight i a) = Term_RotateRight i a # subterms a\<close>
| \<open>subterms (Term_Ite c a b) = Term_Ite c a b # subterms c @ subterms a @ subterms b\<close>

text \<open>The weight of a term: the sum over its subterms (counted with multiplicity) of the cube of
  the width plus one. Widths are those given by \<^const>\<open>width\<close>, so a \<^const>\<open>Term_Ref\<close> weighs by the
  width of the definition it refers to, however large that is. The cube covers \<open>repeat\<close>, whose
  rewriting builds \<open>i\<close> concatenations of growing widths.\<close>
definition term_weight :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> Term \<Rightarrow> nat\<close> where
  \<open>term_weight ws ds t \<equiv> sum_list (map (\<lambda>u. (width ws ds u + 1) ^ 3) (subterms t))\<close>

text \<open>The size of a problem, as a bound on the work of the solver: one plus the sum of the widths of
  the variables, plus the numbers of variables, definitions and assertions, plus the weights of
  all definitions and assertions, times 1000000. It is linear in the number of subterms and
  cubic in their widths. The solver needs a fuel (a bound on the iterations of each loop and
  on the depth of the recursion) and counters (of type \<^verbatim>\<open>usize\<close>) of this size.\<close>
definition size_bound :: \<open>Problem \<Rightarrow> nat\<close> where
  \<open>size_bound p \<equiv>
     let ws = var_widths p in
     let ds = def_widths ws [] (Problem_defs p) in
     1000000 * (1 + sum_list ws + length ws + length (Problem_defs p) + length (Problem_asserts p) +
                sum_list (map (term_weight ws ds) (Problem_defs p @ Problem_asserts p)))\<close>

context QFBV_ctx
begin

subsection \<open>The contract\<close>

definition solve_contract :: \<open>Problem \<Rightarrow> ('s, Answer, 'abort) function_contract\<close> where
  \<open>solve_contract p \<equiv>
     let pre = can_alloc_reference \<star> \<langle>problem_wt p\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>case r of
           Answer_Sat m \<Rightarrow> is_model p m
         | Answer_Unsat \<Rightarrow> (\<forall>m. \<not> is_model p m)\<rangle> in
     make_function_contract pre post\<close>

end

subsection \<open>The overflow condition\<close>

text \<open>\<^const>\<open>size_bound\<close> bounds the fuel; it may be large. The counters of the solver (of type
  \<^verbatim>\<open>usize\<close>) are bounded by the following linear measures instead.\<close>

text \<open>The weight of a term for the counters of the rewriting: one plus the width of each subterm.\<close>
definition lweight :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> Term \<Rightarrow> nat\<close> where
  \<open>lweight ws ds t \<equiv> sum_list (map (\<lambda>u. width ws ds u + 1) (subterms t))\<close>

text \<open>The number of stages of the barrel shifter on width \<open>n\<close>: the least \<open>i\<close> with \<open>n \<le> 2^i\<close>.\<close>
definition nst :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>nst n \<equiv> LEAST i. n \<le> 2 ^ i\<close>

text \<open>A bound on the variables and clauses that blasting the rewriting of a binary operation on
  operands of width \<open>w\<close> adds: quadratic for multiplication, division and remainder, \<open>w\<close> times the
  number of stages for shifts, linear otherwise.\<close>
definition ebin :: \<open>Op \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>ebin op w \<equiv>
     if op \<in> {Op_Mul, Op_Udiv, Op_Urem, Op_Sdiv, Op_Srem, Op_Smod} then 76 * w * w + 300 * w + 20
     else if op \<in> {Op_Shl, Op_Lshr, Op_Ashr} then 10 * w * nst w + 30 * w
     else 30 * w + 20\<close>

definition enode :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> Term \<Rightarrow> nat\<close> where
  \<open>enode ws ds u \<equiv> (case u of
     Term_Bin op a b \<Rightarrow> ebin op (width ws ds a)
   | Term_Neg a \<Rightarrow> 15 * width ws ds a
   | Term_SignExtend i a \<Rightarrow> 5 * unat i
   | Term_Ite c a b \<Rightarrow> 5 * width ws ds a
   | _ \<Rightarrow> 0)\<close>

definition ecount :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> Term \<Rightarrow> nat\<close> where
  \<open>ecount ws ds t \<equiv> sum_list (map (enode ws ds) (subterms t))\<close>

definition ovf_bound :: \<open>Problem \<Rightarrow> nat\<close> where
  \<open>ovf_bound p \<equiv>
     let ws = var_widths p in
     let ds = def_widths ws [] (Problem_defs p) in
     4 * (1 + sum_list ws + length ws + length (Problem_defs p) + length (Problem_asserts p) +
          sum_list (map (\<lambda>t. 4 * lweight ws ds t + ecount ws ds t) (Problem_defs p @ Problem_asserts p)))\<close>

text \<open>The condition on the size of a problem: \<^const>\<open>ovf_bound\<close> is below \<open>2^63\<close>.\<close>
definition sizes_ok :: \<open>Problem \<Rightarrow> bool\<close> where
  \<open>sizes_ok p \<equiv> ovf_bound p < 2 ^ 63\<close>

subsection \<open>The statement over all instances with enough fuel\<close>

text \<open>Like the top-level statement, \<open>solve_correct\<close> is made in the locale \<^locale>\<open>QFBV_heap\<close>.\<close>

context QFBV_heap
begin

abbreviation solve :: \<open>nat \<Rightarrow> Problem \<Rightarrow> ('s, Answer, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>solve fuel \<equiv>
     QFBV_ctx.solve update_raw_fun dereference_raw_fun reference_raw_fun
       prism_1 prism_2 prism_3 prism_4 prism_5 prism_6 prism_7 prism_8 prism_9
       prism_10 prism_11 prism_12 prism_13 fuel\<close>

abbreviation solve_contract :: \<open>Problem \<Rightarrow> ('s, Answer, 'abort) function_contract\<close> where
  \<open>solve_contract \<equiv> QFBV_ctx.solve_contract can_alloc_reference\<close>

definition solve_correct where
  \<open>solve_correct \<Gamma> \<equiv>
     \<forall>p. problem_wt p \<and> sizes_ok p \<longrightarrow> (\<exists>N. \<forall>fuel \<ge> N. \<Gamma>; solve fuel p \<Turnstile>\<^sub>F solve_contract p)\<close>

end

end
