(*<*)
theory Log_Monitor
  imports Prepare Tuple_Code "Log_Parser.Log_Values" "Log_Parser.Log_Code"
begin
(*>*)



section \<open>From the log to the verdicts\<close>

subsection \<open>Strings\<close>

text \<open>The parser's byte strings and the monitor's strings both represent character lists, and
  both are OCaml strings in the generated code.\<close>

definition string8_of_bytes :: "bytes \<Rightarrow> string8" where
  "string8_of_bytes b = Abs_string8 (Rep_bytes b)"

lemma Rep_string8_of_bytes[simp]: "Rep_string8 (string8_of_bytes b) = Rep_bytes b"
  by (simp add: string8_of_bytes_def Abs_string8_inverse)

lemma string8_of_bytes_inject[simp]: "string8_of_bytes a = string8_of_bytes b \<longleftrightarrow> a = b"
  by (metis Rep_bytes_inject Rep_string8_of_bytes)

text \<open>Trusted: both types are printed as OCaml's strings, a character list as the string of the
  characters' codes (@{theory Log_Parser.Log_Code} prints @{typ char} so; the printings of
  @{theory MFOTL_Monitor_Devel.Event_Data} compare strings byte-wise, as the characters' codes
  are compared), so the conversion is the identity.\<close>

declare [[code drop: string8_of_bytes]]

code_printing
  constant string8_of_bytes \<rightharpoonup> (OCaml) "(fun x -> x)"

text \<open>Trusted as well: the equality of strings is that of OCaml's strings. (The code of
  @{text "HOL.equal"} on @{typ string8} is OCaml's polymorphic equality, which is slower.)\<close>

definition str8_eq :: "string8 \<Rightarrow> string8 \<Rightarrow> bool" where
  "str8_eq a b \<longleftrightarrow> a = b"

declare [[code drop: str8_eq]]

code_printing
  constant str8_eq \<rightharpoonup> (OCaml) "String.equal"

text \<open>The hash code of a string (@{theory MFOTL_Monitor_Devel.Event_Data}) is the fold over its
  characters; its code reads the bytes of the OCaml string, through the conversion to byte strings,
  trusted like @{const string8_of_bytes}.\<close>

definition bytes_of_string8 :: "string8 \<Rightarrow> bytes" where
  "bytes_of_string8 s = Abs_bytes (Rep_string8 s)"

lemma Rep_bytes_of_string8[simp]: "Rep_bytes (bytes_of_string8 s) = Rep_string8 s"
  by (simp add: bytes_of_string8_def Abs_bytes_inverse)

declare [[code drop: bytes_of_string8]]

code_printing
  constant bytes_of_string8 \<rightharpoonup> (OCaml) "(fun x -> x)"

lemma hashcode_char_code: "hashcode (c :: char) = Uint32_signed (integer_of_char c)"
proof -
  have "0 \<le> (of_char c :: int) \<and> of_char c < (256 :: int)"
    using nat_of_char_less_256[of c] unfolding of_nat_of_char[where 'a=int, symmetric] by simp
  then have "\<not> (integer_of_char c < - 0x80000000 \<or> integer_of_char c \<ge> 0x80000000)"
    including integer.lifting unfolding integer_of_char_def by transfer simp
  then show ?thesis
    unfolding hashcode_char_def Uint32_signed_def integer_of_char_def
    including integer.lifting by (simp, transfer, simp)
qed

function hash_bytes :: "bytes \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> hashcode \<Rightarrow> hashcode" where
  "hash_bytes s n i h = (if i < n
    then hash_bytes s n (i + 1) (h * hc_mult + Uint32_signed (integer_of_char (bytes_at s i)))
    else h)"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(_, n, i, _). nat_of_integer (n - i))")
   apply simp
  apply simp
  including integer.lifting
  apply transfer
  apply simp
  done

lemma nat_of_integer_Suc: "0 \<le> i \<Longrightarrow> nat_of_integer (i + 1) = Suc (nat_of_integer i)"
  including integer.lifting by transfer (simp add: Suc_nat_eq_nat_zadd1)

lemma nat_of_integer_less: "0 \<le> i \<Longrightarrow> i < integer_of_nat m \<Longrightarrow> nat_of_integer i < m"
  including integer.lifting by transfer simp

lemma nat_of_integer_ge: "\<not> i < integer_of_nat m \<Longrightarrow> m \<le> nat_of_integer i"
  including integer.lifting by transfer simp

lemma hash_bytes_foldl:
  "0 \<le> i \<Longrightarrow> n = bytes_length s \<Longrightarrow>
   hash_bytes s n i h = foldl (\<lambda>h c. h * hc_mult + hashcode c) h (drop (nat_of_integer i) (Rep_bytes s))"
proof (induction s n i h rule: hash_bytes.induct)
  case (1 s n i h)
  show ?case
  proof (cases "i < n")
    case True
    have k: "nat_of_integer i < length (Rep_bytes s)"
      using True 1(2,3) by (simp add: bytes_length_def nat_of_integer_less)
    have "drop (nat_of_integer i) (Rep_bytes s) =
      Rep_bytes s ! nat_of_integer i # drop (nat_of_integer (i + 1)) (Rep_bytes s)"
      using Cons_nth_drop_Suc[OF k] 1(2) by (simp add: nat_of_integer_Suc)
    then show ?thesis
      using True 1 by (subst hash_bytes.simps)
        (simp add: bytes_at_def hashcode_char_code[unfolded hashcode_char_def] del: hash_bytes.simps)
  next
    case False
    then have "length (Rep_bytes s) \<le> nat_of_integer i"
      using 1(3) by (simp add: bytes_length_def nat_of_integer_ge)
    then show ?thesis
      using False by (subst hash_bytes.simps) simp
  qed
qed

lemma hashcode_string8_code[code]:
  "hashcode s = (let b = bytes_of_string8 s in hash_bytes b (bytes_length b) 0 hc_init)"
  unfolding hashcode_string8_def Let_def
  by (subst hash_bytes_foldl) (simp_all add: hashcode_list_def hc_mult_def hc_init_def)

subsection \<open>Signatures\<close>

text \<open>The signature as the front end reads it: the predicates with their argument types.\<close>

type_synonym lsig = "(string8 \<times> ty list) list"

definition lsig_lookup :: "lsig \<Rightarrow> string8 \<times> nat \<Rightarrow> ty list option" where
  "lsig_lookup S pn = map_option snd (find (\<lambda>(p, tys). (p, length tys) = pn) S)"

definition lsig_tsig :: "lsig \<Rightarrow> tyssig" where
  "lsig_tsig S = map_sig TCst (lsig_lookup S)"

text \<open>The code compares the names first.\<close>

fun lsig_find :: "lsig \<Rightarrow> string8 \<Rightarrow> nat \<Rightarrow> ty list option" where
  "lsig_find [] q n = None"
| "lsig_find ((p, tys) # S) q n = (if str8_eq p q \<and> length tys = n then Some tys else lsig_find S q n)"

lemma lsig_lookup_code[code]: "lsig_lookup S (q, n) = lsig_find S q n"
  by (induction S q n rule: lsig_find.induct) (auto simp: lsig_lookup_def str8_eq_def)

text \<open>For large signatures, the code looks predicates up in a mapping from their names to their
  arities and argument types.\<close>

definition ix_list :: "(Formula.name, (nat \<times> ty list) list) mapping \<Rightarrow> Formula.name \<Rightarrow> (nat \<times> ty list) list" where
  "ix_list m p = (case Mapping.lookup m p of None \<Rightarrow> [] | Some l \<Rightarrow> l)"

fun ix_add :: "Formula.name \<times> ty list \<Rightarrow> (Formula.name, (nat \<times> ty list) list) mapping \<Rightarrow>
    (Formula.name, (nat \<times> ty list) list) mapping" where
  "ix_add (p, tys) m = Mapping.update p ((length tys, tys) # ix_list m p) m"

definition lsig_index :: "lsig \<Rightarrow> (Formula.name, (nat \<times> ty list) list) mapping" where
  "lsig_index S = fold ix_add (rev S) Mapping.empty"

definition index_lookup :: "(Formula.name, (nat \<times> ty list) list) mapping \<Rightarrow> Formula.name \<times> nat \<Rightarrow> ty list option" where
  "index_lookup I pn = map_option snd (find (\<lambda>(n, _). n = snd pn) (ix_list I (fst pn)))"

text \<open>The lookup the conversion uses: in the list for small signatures, in the mapping for the
  others.\<close>

definition lsig_lookup_fun :: "lsig \<Rightarrow> Formula.name \<times> nat \<Rightarrow> ty list option" where
  "lsig_lookup_fun S = (if length S < 32 then lsig_lookup S else (let I = lsig_index S in index_lookup I))"

subsection \<open>Converting events\<close>

text \<open>A field of a given type. Integers are read as in @{theory Log_Parser.Log_Values}; floats
  by a parameter @{text pf}, the platform's reader, about which nothing is assumed.\<close>

definition conv_field :: "(bytes \<Rightarrow> double option) \<Rightarrow> ty \<Rightarrow> bytes \<Rightarrow> event_data option" where
  "conv_field pf t f = (case t of
     TInt \<Rightarrow> map_option (EInt \<circ> integer_of_int) (bint_of f)
   | TFloat \<Rightarrow> map_option EFloat (pf f)
   | TString \<Rightarrow> Some (EString (string8_of_bytes f)))"

text \<open>The field conversion uses the fused integer conversion.\<close>

lemma conv_field_code[code]: "conv_field pf t f = (case t of
     TInt \<Rightarrow> map_option EInt (ibint_of f)
   | TFloat \<Rightarrow> map_option EFloat (pf f)
   | TString \<Rightarrow> Some (EString (string8_of_bytes f)))"
  by (simp add: conv_field_def ibint_of_def option.map_comp comp_def split: ty.splits)

text \<open>The errors the conversion reports.\<close>

datatype verror = VE_PARSE perror | VE_TIMESTAMP bytes | VE_ORDER nat nat | VE_PREDICATE bytes nat
  | VE_FIELD bytes nat ty | VE_COMMAND bytes

text \<open>The fields of an event, by their types; on failure, the index of the first field that does
  not convert.\<close>

fun conv_fields :: "(bytes \<Rightarrow> double option) \<Rightarrow> ty list \<Rightarrow> bytes list \<Rightarrow> nat \<Rightarrow> (nat \<times> ty) + event_data list" where
  "conv_fields pf (t # ts) (f # fs) i = (case conv_field pf t f of
     None \<Rightarrow> Inl (i, t)
   | Some x \<Rightarrow> map_sum id (Cons x) (conv_fields pf ts fs (Suc i)))"
| "conv_fields pf _ _ i = Inr []"

definition conv_event :: "(bytes \<Rightarrow> double option) \<Rightarrow> (Formula.name \<times> nat \<Rightarrow> ty list option) \<Rightarrow>
    bytes \<times> bytes list \<Rightarrow> verror + Formula.event" where
  "conv_event pf L e = (case e of (p, fs) \<Rightarrow> let q = string8_of_bytes p in
     (case L (q, length fs) of
       None \<Rightarrow> Inl (VE_PREDICATE p (length fs))
     | Some tys \<Rightarrow> map_sum (\<lambda>(i, t). VE_FIELD p i t) (Pair q) (conv_fields pf tys fs 0)))"

fun conv_events :: "(bytes \<Rightarrow> double option) \<Rightarrow> (Formula.name \<times> nat \<Rightarrow> ty list option) \<Rightarrow>
    (bytes \<times> bytes list) list \<Rightarrow> verror + Formula.event list" where
  "conv_events pf L [] = Inr []"
| "conv_events pf L (e # es) = (case conv_event pf L e of
     Inl err \<Rightarrow> Inl err
   | Inr x \<Rightarrow> map_sum id (Cons x) (conv_events pf L es))"

text \<open>The code converts the events of a time point with an accumulator, so that the depth of the
  recursion does not grow with their number.\<close>

fun conv_events_acc :: "(bytes \<Rightarrow> double option) \<Rightarrow> (Formula.name \<times> nat \<Rightarrow> ty list option) \<Rightarrow>
    Formula.event list \<Rightarrow> (bytes \<times> bytes list) list \<Rightarrow> verror + Formula.event list" where
  "conv_events_acc pf L acc [] = Inr (rev acc)"
| "conv_events_acc pf L acc (e # es) = (case conv_event pf L e of
     Inl err \<Rightarrow> Inl err
   | Inr x \<Rightarrow> conv_events_acc pf L (x # acc) es)"

lemma conv_events_acc: "conv_events_acc pf L acc es = map_sum id ((@) (rev acc)) (conv_events pf L es)"
  by (induction pf L acc es rule: conv_events_acc.induct) (auto simp: map_sum_def split: sum.splits)

lemma conv_events_code[code]: "conv_events pf L es = conv_events_acc pf L [] es"
  by (cases "conv_events pf L es") (simp_all add: conv_events_acc)

text \<open>The first event of a predicate whose name the signature does not declare. Which error is
  reported for an entry follows MonPoly's parser, which checks the names of the predicates, then
  the order of the timestamps, and then the arity and the fields of each event in turn.\<close>

fun pred_error :: "lsig \<Rightarrow> (bytes \<times> bytes list) list \<Rightarrow> verror option" where
  "pred_error S [] = None"
| "pred_error S ((p, fs) # es) = (if list_ex (\<lambda>(q, _). str8_eq q (string8_of_bytes p)) S
     then pred_error S es else Some (VE_PREDICATE p (length fs)))"

text \<open>The error of the first event that does not convert, as MonPoly's parser reports it: it
  converts the fields against the types that the signature declares for the name of the predicate
  one after the other, and reports a wrong number of fields only if the fields they have in
  common convert.\<close>

fun conv_error :: "(bytes \<Rightarrow> double option) \<Rightarrow> (Formula.name \<times> nat \<Rightarrow> ty list option) \<Rightarrow> lsig \<Rightarrow>
    (bytes \<times> bytes list) list \<Rightarrow> verror option" where
  "conv_error pf L S [] = None"
| "conv_error pf L S ((p, fs) # es) = (let q = string8_of_bytes p in
     case L (q, length fs) of
       Some tys \<Rightarrow> (case conv_fields pf tys fs 0 of
         Inl (i, t) \<Rightarrow> Some (VE_FIELD p i t)
       | Inr _ \<Rightarrow> conv_error pf L S es)
     | None \<Rightarrow> (case find (\<lambda>(q', _). str8_eq q' q) S of
         None \<Rightarrow> Some (VE_PREDICATE p (length fs))
       | Some (_, tys) \<Rightarrow> (case conv_fields pf tys fs 0 of
           Inl (i, t) \<Rightarrow> Some (VE_FIELD p i t)
         | Inr _ \<Rightarrow> Some (VE_PREDICATE p (length fs)))))"

subsection \<open>Sorting\<close>

text \<open>The tuples of a table are sorted, without duplicates, before the table is built, so that
  the tree is built in one pass. The merge sort below merges the runs of increasing elements of
  the list, so that a sorted list is one run, and is tail recursive, since a time point may hold
  many events: merging onto an accumulator reverses the order, so a round of merges turns lists
  that increase into lists that decrease, and the next round merges those with the comparator
  turned around. It drops duplicates as it merges, and is proved to sort strictly, so that the
  tree can be built without checking that it is.\<close>

lemma comparator_converse:
  assumes "comparator c"
  shows "comparator (\<lambda>x y. c y x)"
proof
  fix x y z
  show "invert_order (c y x) = c x y"
    by (rule comparator.sym[OF assms])
  show "c y x = order.Eq \<Longrightarrow> x = y"
    using comparator.weak_eq[OF assms, of y x] by simp
  show "c y x = order.Lt \<Longrightarrow> c z y = order.Lt \<Longrightarrow> c z x = order.Lt"
    using comparator.comp_trans[OF assms, of z y x] by simp
qed

fun cmerge :: "'a comparator \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "cmerge c [] ys = ys"
| "cmerge c (x # xs) [] = x # xs"
| "cmerge c (x # xs) (y # ys) = (case c x y of
     order.Lt \<Rightarrow> x # cmerge c xs (y # ys)
   | order.Gt \<Rightarrow> y # cmerge c (x # xs) ys
   | order.Eq \<Rightarrow> x # cmerge c xs ys)"

lemma set_cmerge: "comparator c \<Longrightarrow> set (cmerge c xs ys) = set xs \<union> set ys"
  by (induction c xs ys rule: cmerge.induct) (auto split: order.splits dest: comparator.weak_eq)

lemma sorted_cmerge: "comparator c \<Longrightarrow> sorted_wrt (lt_of_comp c) xs \<Longrightarrow> sorted_wrt (lt_of_comp c) ys \<Longrightarrow>
  sorted_wrt (lt_of_comp c) (cmerge c xs ys)"
proof (induction c xs ys rule: cmerge.induct)
  case (3 c x xs y ys)
  have tr: "lt_of_comp c a b \<Longrightarrow> lt_of_comp c b d \<Longrightarrow> lt_of_comp c a d" for a b d
    using comparator.comp_trans[OF 3(4), of a b d] by (simp add: comparator.Lt_lt_conv[OF 3(4)])
  note conv = comparator.Lt_lt_conv[OF 3(4)] comparator.Gt_lt_conv[OF 3(4)] comparator.eq_Eq_conv[OF 3(4)]
  from 3 show ?case
    by (auto simp: set_cmerge conv split: order.splits intro: tr)
qed simp_all

fun cmerge_rev :: "'a comparator \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "cmerge_rev c acc [] ys = fold Cons ys acc"
| "cmerge_rev c acc (x # xs) [] = fold Cons (x # xs) acc"
| "cmerge_rev c acc (x # xs) (y # ys) = (case c x y of
     order.Lt \<Rightarrow> cmerge_rev c (x # acc) xs (y # ys)
   | order.Gt \<Rightarrow> cmerge_rev c (y # acc) (x # xs) ys
   | order.Eq \<Rightarrow> cmerge_rev c (x # acc) xs ys)"

lemma cmerge_rev: "cmerge_rev c acc xs ys = rev (cmerge c xs ys) @ acc"
  by (induction c acc xs ys rule: cmerge_rev.induct) (auto simp: fold_Cons_rev split: order.splits)

fun cmerge_pairs :: "'a comparator \<Rightarrow> 'a list list \<Rightarrow> 'a list list \<Rightarrow> 'a list list" where
  "cmerge_pairs c acc (a # b # r) = cmerge_pairs c (cmerge_rev c [] a b # acc) r"
| "cmerge_pairs c acc [a] = rev a # acc"
| "cmerge_pairs c acc [] = acc"

lemma length_cmerge_pairs: "length (cmerge_pairs c acc xss) = length acc + (length xss + 1) div 2"
  by (induction c acc xss rule: cmerge_pairs.induct) auto

lemma set_cmerge_pairs: "comparator c \<Longrightarrow> \<Union> (set ` set (cmerge_pairs c acc xss)) = \<Union> (set ` set (acc @ xss))"
  by (induction c acc xss rule: cmerge_pairs.induct) (auto simp: cmerge_rev set_cmerge)

lemma sorted_rev_converse:
  "sorted_wrt (lt_of_comp (\<lambda>x y. c y x)) (rev xs) \<longleftrightarrow> sorted_wrt (lt_of_comp c) xs"
  "sorted_wrt (lt_of_comp c) (rev xs) \<longleftrightarrow> sorted_wrt (lt_of_comp (\<lambda>x y. c y x)) xs"
proof -
  have L: "lt_of_comp (\<lambda>x y. c y x) = (\<lambda>a b. lt_of_comp c b a)"
    by (simp add: fun_eq_iff lt_of_comp_def)
  show "sorted_wrt (lt_of_comp (\<lambda>x y. c y x)) (rev xs) \<longleftrightarrow> sorted_wrt (lt_of_comp c) xs"
    unfolding L sorted_wrt_rev by (rule refl)
  show "sorted_wrt (lt_of_comp c) (rev xs) \<longleftrightarrow> sorted_wrt (lt_of_comp (\<lambda>x y. c y x)) xs"
    unfolding L sorted_wrt_rev by (rule refl)
qed

lemma sorted_cmerge_pairs: "comparator c \<Longrightarrow> \<forall>a \<in> set xss. sorted_wrt (lt_of_comp c) a \<Longrightarrow>
    \<forall>a \<in> set acc. sorted_wrt (lt_of_comp (\<lambda>x y. c y x)) a \<Longrightarrow>
    \<forall>a \<in> set (cmerge_pairs c acc xss). sorted_wrt (lt_of_comp (\<lambda>x y. c y x)) a"
proof (induction c acc xss rule: cmerge_pairs.induct)
  case (1 c acc a b r)
  then show ?case
    using sorted_cmerge[of c a b] by (simp add: cmerge_rev sorted_rev_converse)
qed (simp_all add: sorted_rev_converse)

function cmerge_all :: "'a comparator \<Rightarrow> bool \<Rightarrow> 'a list list \<Rightarrow> 'a list" where
  "cmerge_all c d [] = []"
| "cmerge_all c d [a] = (if d then rev a else a)"
| "cmerge_all c d (a # b # r) = cmerge_all c (\<not> d) (cmerge_pairs (if d then (\<lambda>x y. c y x) else c) [] (a # b # r))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(c, d, xss). length xss)") (auto simp: length_cmerge_pairs)

lemma cmerge_all: "comparator c \<Longrightarrow> \<forall>a \<in> set xss. sorted_wrt (lt_of_comp (if d then (\<lambda>x y. c y x) else c)) a \<Longrightarrow>
  set (cmerge_all c d xss) = \<Union> (set ` set xss) \<and> sorted_wrt (lt_of_comp c) (cmerge_all c d xss)"
proof (induction c d xss rule: cmerge_all.induct)
  case (2 c d a)
  then show ?case
    by (cases d) (simp_all add: sorted_rev_converse)
next
  case (3 c d a b r)
  let ?c = "if d then (\<lambda>x y. c y x) else c"
  have comp: "comparator ?c"
    using 3(2) comparator_converse[OF 3(2)] by (cases d) simp_all
  have conv: "(\<lambda>x y. ?c y x) = (if \<not> d then (\<lambda>x y. c y x) else c)"
    by auto
  have "\<forall>a \<in> set (cmerge_pairs ?c [] (a # b # r)). sorted_wrt (lt_of_comp (if \<not> d then (\<lambda>x y. c y x) else c)) a"
    using sorted_cmerge_pairs[OF comp, of "a # b # r" "[]"] 3(3) unfolding conv by simp
  with 3(1)[OF 3(2)] set_cmerge_pairs[OF comp, of "[]" "a # b # r"] show ?case
    by simp
qed simp

text \<open>The runs of increasing elements of the list.\<close>

fun runs_tc :: "'a comparator \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list list \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "runs_tc c x cur acc [] = rev (x # cur) # acc"
| "runs_tc c x cur acc (y # ys) = (if c x y = order.Lt then runs_tc c y (x # cur) acc ys
     else runs_tc c y [] (rev (x # cur) # acc) ys)"

lemma sorted_runs_tc: "comparator c \<Longrightarrow> sorted_wrt (lt_of_comp c) (rev (x # cur)) \<Longrightarrow>
  \<forall>a \<in> set acc. sorted_wrt (lt_of_comp c) a \<Longrightarrow> \<forall>a \<in> set (runs_tc c x cur acc ys). sorted_wrt (lt_of_comp c) a"
proof (induction c x cur acc ys rule: runs_tc.induct)
  case (2 c x cur acc y ys)
  show ?case
  proof (cases "c x y = order.Lt")
    case True
    have "lt_of_comp c z y" if "z \<in> set (x # cur)" for z
    proof -
      have "z = x \<or> lt_of_comp c z x"
        using that 2(4) by (auto simp: sorted_wrt_append)
      then show ?thesis
        using True comparator.comp_trans[OF 2(3), of z x y] by (auto simp: comparator.Lt_lt_conv[OF 2(3)])
    qed
    then have "sorted_wrt (lt_of_comp c) (rev (y # x # cur))"
      using 2(4) by (simp add: sorted_wrt_append)
    with True 2 show ?thesis
      by simp
  next
    case False
    have A: "\<forall>a \<in> set (rev (x # cur) # acc). sorted_wrt (lt_of_comp c) a"
      using 2(4,5) by simp
    have S: "sorted_wrt (lt_of_comp c) (rev [y])"
      by simp
    have R: "runs_tc c x cur acc (y # ys) = runs_tc c y [] (rev (x # cur) # acc) ys"
      using False by simp
    show ?thesis
      unfolding R by (rule 2(2)[OF False 2(3) S A])
  qed
qed simp

lemma set_runs_tc: "\<Union> (set ` set (runs_tc c x cur acc ys)) = Set.insert x (set cur \<union> \<Union> (set ` set acc) \<union> set ys)"
  by (induction c x cur acc ys rule: runs_tc.induct) auto

definition csort :: "'a comparator \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "csort c xs = (case xs of [] \<Rightarrow> [] | x # ys \<Rightarrow> cmerge_all c False (runs_tc c x [] [] ys))"

lemma csort:
  assumes "comparator c"
  shows "set (csort c xs) = set xs" and "sorted_wrt (lt_of_comp c) (csort c xs)"
proof -
  have "set (csort c xs) = set xs \<and> sorted_wrt (lt_of_comp c) (csort c xs)"
  proof (cases xs)
    case (Cons x ys)
    have "\<forall>a \<in> set (runs_tc c x [] [] ys). sorted_wrt (lt_of_comp c) a"
      by (rule sorted_runs_tc[OF assms]) simp_all
    then have "set (cmerge_all c False (runs_tc c x [] [] ys)) = \<Union> (set ` set (runs_tc c x [] [] ys)) \<and>
      sorted_wrt (lt_of_comp c) (cmerge_all c False (runs_tc c x [] [] ys))"
      using cmerge_all[OF assms, of "runs_tc c x [] [] ys" False] by simp
    then show ?thesis
      unfolding Cons csort_def set_runs_tc by simp
  qed (simp add: csort_def)
  then show "set (csort c xs) = set xs" and "sorted_wrt (lt_of_comp c) (csort c xs)"
    by simp_all
qed

subsection \<open>Databases\<close>

text \<open>The events of a time point, grouped by predicate and arity.\<close>

fun add_ev :: "Formula.event \<Rightarrow> ((Formula.name \<times> nat) \<times> event_data list list) list \<Rightarrow>
    ((Formula.name \<times> nat) \<times> event_data list list) list" where
  "add_ev (p, vs) [] = [((p, length vs), [vs])]"
| "add_ev (p, vs) ((k, xs) # g) = (if k = (p, length vs) then (k, vs # xs) # g else (k, xs) # add_ev (p, vs) g)"

definition group_evs :: "Formula.event list \<Rightarrow> ((Formula.name \<times> nat) \<times> event_data list list) list" where
  "group_evs evs = fold add_ev evs []"

text \<open>The code computes the key of an event once.\<close>

fun add_evk :: "Formula.name \<times> nat \<Rightarrow> event_data list \<Rightarrow> ((Formula.name \<times> nat) \<times> event_data list list) list \<Rightarrow>
    ((Formula.name \<times> nat) \<times> event_data list list) list" where
  "add_evk k vs [] = [(k, [vs])]"
| "add_evk k vs ((k', xs) # g) = (if str8_eq (fst k') (fst k) \<and> snd k' = snd k then (k', vs # xs) # g
     else (k', xs) # add_evk k vs g)"

lemma add_ev_code: "add_ev (p, vs) g = add_evk (p, length vs) vs g"
  by (induction "(p, vs)" g rule: add_ev.induct) (auto simp: str8_eq_def prod_eq_iff)

definition build_db :: "Formula.event list \<Rightarrow> udatabase" where
  "build_db evs = fold (\<lambda>(k, xs) db. uinsert_table_into_db k (utable_of_list xs) db) (group_evs evs) uempty_db"

definition map_t :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "map_t f xs = rev (fold (\<lambda>x acc. f x # acc) xs [])"

lemma map_t[simp]: "map_t f xs = map f xs"
proof -
  have "fold (\<lambda>x acc. f x # acc) xs acc = rev (map f xs) @ acc" for acc
    by (induction xs arbitrary: acc) auto
  then show ?thesis
    by (simp add: map_t_def)
qed

subsection \<open>Building the tables faster\<close>

text \<open>The tree of a table is built by @{const rbtreeify}, whose generated code computes with the
  natural numbers of the generated code, which wrap the integers. The copy below computes with the
  integers directly, and is proved to build the same tree.\<close>

lemma nat_of_integer_half: "\<not> n \<le> 0 \<Longrightarrow> n \<noteq> 1 \<Longrightarrow> nat_of_integer (n div 2) < nat_of_integer n"
  "\<not> n \<le> 1 \<Longrightarrow> nat_of_integer (n div 2) < nat_of_integer n"
  including integer.lifting by (transfer, auto)+

function rbtreeify_fi :: "integer \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a, 'b) rbt \<times> ('a \<times> 'b) list"
  and rbtreeify_gi :: "integer \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a, 'b) rbt \<times> ('a \<times> 'b) list" where
  "rbtreeify_fi n kvs = (if n \<le> 0 then (RBT_Impl.Empty, kvs)
    else if n = 1 then (case kvs of (k, v) # kvs' \<Rightarrow> (RBT_Impl.Branch RBT_Impl.R RBT_Impl.Empty k v RBT_Impl.Empty, kvs'))
    else (case Code_Numeral.divmod_abs n 2 of (n', r) \<Rightarrow>
      if r = 0 then (case rbtreeify_fi n' kvs of (t1, (k, v) # kvs') \<Rightarrow>
        apfst (RBT_Impl.Branch RBT_Impl.B t1 k v) (rbtreeify_gi n' kvs'))
      else (case rbtreeify_fi n' kvs of (t1, (k, v) # kvs') \<Rightarrow>
        apfst (RBT_Impl.Branch RBT_Impl.B t1 k v) (rbtreeify_fi n' kvs'))))"
| "rbtreeify_gi n kvs = (if n \<le> 1 then (RBT_Impl.Empty, kvs)
    else (case Code_Numeral.divmod_abs n 2 of (n', r) \<Rightarrow>
      if r = 0 then (case rbtreeify_gi n' kvs of (t1, (k, v) # kvs') \<Rightarrow>
        apfst (RBT_Impl.Branch RBT_Impl.B t1 k v) (rbtreeify_gi n' kvs'))
      else (case rbtreeify_fi n' kvs of (t1, (k, v) # kvs') \<Rightarrow>
        apfst (RBT_Impl.Branch RBT_Impl.B t1 k v) (rbtreeify_gi n' kvs'))))"
  by pat_completeness auto
termination
  by (relation "measure (case_sum (\<lambda>(n, _). nat_of_integer n) (\<lambda>(n, _). nat_of_integer n))")
    (auto simp: divmod_abs_def nat_of_integer_half)

declare rbtreeify_fi.simps[simp del] rbtreeify_gi.simps[simp del]

lemma integer_of_nat_rbt_simps:
  "integer_of_nat n \<le> 0 \<longleftrightarrow> n = 0" "integer_of_nat n \<le> 1 \<longleftrightarrow> n = 0 \<or> n = 1"
  "integer_of_nat n = 1 \<longleftrightarrow> n = 1"
  "Code_Numeral.divmod_abs (integer_of_nat n) 2 = (integer_of_nat (n div 2), integer_of_nat (n mod 2))"
  "integer_of_nat m = 0 \<longleftrightarrow> m = 0"
  by (simp_all add: integer_eq_iff less_eq_integer.rep_eq divmod_abs_def integer_of_nat.rep_eq
      zdiv_int zmod_int le_Suc_eq)

lemma rbtreeify_fi: "rbtreeify_fi (integer_of_nat n) kvs = rbtreeify_f n kvs"
  and rbtreeify_gi: "rbtreeify_gi (integer_of_nat n) kvs = rbtreeify_g n kvs"
proof -
  have fg: "rbtreeify_fi (integer_of_nat n) kvs = rbtreeify_f n kvs \<and>
      rbtreeify_gi (integer_of_nat n) kvs = rbtreeify_g n kvs" for n and kvs :: "('a \<times> 'b) list"
  proof (induction n arbitrary: kvs rule: less_induct)
    case (less n kvs)
    consider "n = 0" | "n = 1" | "1 < n"
      by linarith
    then show ?case
    proof cases
      case 3
      then have ne: "n \<noteq> 0" "n \<noteq> 1" and lt: "n div 2 < n"
        by simp_all
      show ?thesis
      proof
        show "rbtreeify_fi (integer_of_nat n) kvs = rbtreeify_f n kvs"
          by (subst rbtreeify_fi.simps, subst rbtreeify_f.simps)
            (simp only: integer_of_nat_rbt_simps less.IH[OF lt] ne if_False prod.case)
        show "rbtreeify_gi (integer_of_nat n) kvs = rbtreeify_g n kvs"
          by (subst rbtreeify_gi.simps, subst rbtreeify_g.simps)
            (simp only: integer_of_nat_rbt_simps less.IH[OF lt] ne if_False prod.case simp_thms)
      qed
    qed (simp_all add: rbtreeify_fi.simps rbtreeify_gi.simps rbtreeify_f.simps rbtreeify_g.simps
      integer_of_nat_rbt_simps)
  qed
  show "rbtreeify_fi (integer_of_nat n) kvs = rbtreeify_f n kvs"
    using fg by simp
  show "rbtreeify_gi (integer_of_nat n) kvs = rbtreeify_g n kvs"
    using fg by simp
qed

fun ilen :: "integer \<Rightarrow> 'a list \<Rightarrow> integer" where
  "ilen acc [] = acc"
| "ilen acc (x # xs) = ilen (acc + 1) xs"

lemma ilen: "ilen acc xs = acc + integer_of_nat (length xs)"
  by (induction acc xs rule: ilen.induct) (simp_all add: integer_of_nat_eq_of_nat)

lemma ilen_code[code]: "ilen acc [] = acc" "ilen acc (x # xs) = ilen (idx_succ acc) xs"
  by (simp_all add: idx_succ_def)

definition rbtreeify_i :: "('a \<times> 'b) list \<Rightarrow> ('a, 'b) rbt" where
  "rbtreeify_i kvs = fst (rbtreeify_gi (ilen 1 kvs) kvs)"

lemma rbtreeify_i: "rbtreeify_i kvs = rbtreeify kvs"
proof -
  have "ilen 1 kvs = integer_of_nat (Suc (length kvs))"
    by (simp add: ilen integer_of_nat_eq_of_nat)
  then show ?thesis
    by (simp add: rbtreeify_i_def rbtreeify_def rbtreeify_gi)
qed

text \<open>The tables of a time point are built with this sort and tree construction. The groups
  hold their tuples in the reverse order of the log; the code reverses them before sorting them,
  so that tuples that come sorted in the log are sorted in linear time.\<close>

lemma comparator_edl: "comparator ed_comparator"
  by (rule ID_ccompare'[OF ID_ccompare_etuple])

definition urbt_sort :: "event_data list list \<Rightarrow> event_data list set_rbt" where
  "urbt_sort xs = rbt_of_sorted_list (csort ed_comparator xs)"

lemma urbt_sort_code[code abstract]:
  "RBT_Mapping2.impl_of (urbt_sort xs) = rbtreeify_i (map_t (\<lambda>x. (x, ())) (csort ed_comparator xs))"
proof -
  have "strict_sorted_by ed_comparator (csort ed_comparator xs)"
    using csort(2)[OF comparator_edl] strict_sorted_by_sorted_wrt[OF comparator_edl] by simp
  then show ?thesis
    by (simp add: urbt_sort_def rbt_of_sorted_list.rep_eq ccomp_etuple rbtreeify_i)
qed

lemma build_db_code_sort[code]: "build_db evs =
  fold (\<lambda>(k, xs) db. uinsert_table_into_db k (RBT_set (urbt_sort (rev xs))) db) (group_evs evs) uempty_db"
proof -
  have "utable_of_list xs = RBT_set (urbt_sort (rev xs))" for xs
    by (simp add: utable_of_list_def urbt_sort_def RBT_set_rbt_of_sorted_list ID_ccompare_etuple
        csort(1)[OF comparator_edl])
  then show ?thesis
    by (simp add: build_db_def)
qed

subsection \<open>Converting events faster\<close>

text \<open>The fields are converted by a tail-recursive loop, which computes the index of a field only
  if it does not convert, and the lengths of lists are counted as integers rather than as natural
  numbers.\<close>

fun conv_fields_a :: "(bytes \<Rightarrow> double option) \<Rightarrow> ty list \<Rightarrow> bytes list \<Rightarrow> event_data list \<Rightarrow>
    (nat \<times> ty) + event_data list" where
  "conv_fields_a pf (t # ts) (f # fs) acc = (case conv_field pf t f of
     None \<Rightarrow> Inl (length acc, t)
   | Some x \<Rightarrow> conv_fields_a pf ts fs (x # acc))"
| "conv_fields_a pf _ _ acc = Inr (rev acc)"

lemma conv_fields_a: "conv_fields_a pf tys fs acc = map_sum id ((@) (rev acc)) (conv_fields pf tys fs (length acc))"
  by (induction pf tys fs acc rule: conv_fields_a.induct) (auto simp: sum.map_comp comp_def split: option.splits)

lemma conv_event_fast[code]: "conv_event pf L e = (case e of (p, fs) \<Rightarrow> let q = string8_of_bytes p; m = nat_of_integer (ilen 0 fs) in
     (case L (q, m) of
       None \<Rightarrow> Inl (VE_PREDICATE p m)
     | Some tys \<Rightarrow> map_sum (\<lambda>(i, t). VE_FIELD p i t) (Pair q) (conv_fields_a pf tys fs [])))"
proof -
  have A: "nat_of_integer (ilen 0 fs) = length fs" for fs :: "bytes list"
    by (simp add: ilen)
  have B: "conv_fields_a pf tys fs [] = conv_fields pf tys fs 0" for tys fs
    by (cases "conv_fields pf tys fs 0") (simp_all add: conv_fields_a)
  show ?thesis
    by (auto simp: conv_event_def A B Let_def split: prod.splits option.splits)
qed

lemma lsig_find_fast[code]: "lsig_find [] q n = None"
  "lsig_find ((p, tys) # S) q n = (if str8_eq p q \<and> ilen 0 tys = integer_of_nat n then Some tys else lsig_find S q n)"
  by (simp_all add: ilen integer_of_nat_eq_of_nat)

lemma add_ev_fast[code]: "add_ev (p, vs) g = add_evk (p, nat_of_integer (ilen 0 vs)) vs g"
  by (simp add: add_ev_code ilen)

subsection \<open>The predicates of the formula\<close>

text \<open>The predicates that occur freely in a formula (@{const Rewriting.preds}), as a list.\<close>

fun free_preds :: "'t Formula.formula \<Rightarrow> (Formula.name \<times> nat) list" where
  "free_preds (Formula.Pred e ts) = [(e, length ts)]"
| "free_preds (Formula.Let p \<phi> \<psi>) = free_preds \<phi> @ filter (\<lambda>x. x \<noteq> (p, Formula.nfv \<phi>)) (free_preds \<psi>)"
| "free_preds (Formula.Frz p \<phi> \<psi>) = free_preds \<phi> @ filter (\<lambda>x. x \<noteq> (p, Formula.nfv \<phi>)) (free_preds \<psi>)"
| "free_preds (Formula.LetPast p \<phi> \<psi>) = filter (\<lambda>x. x \<noteq> (p, Formula.nfv \<phi>)) (free_preds \<phi> @ free_preds \<psi>)"
| "free_preds (Formula.Eq t1 t2) = []"
| "free_preds (Formula.Less t1 t2) = []"
| "free_preds (Formula.LessEq t1 t2) = []"
| "free_preds (Formula.Neg \<phi>) = free_preds \<phi>"
| "free_preds (Formula.Or \<phi> \<psi>) = free_preds \<phi> @ free_preds \<psi>"
| "free_preds (Formula.And \<phi> \<psi>) = free_preds \<phi> @ free_preds \<psi>"
| "free_preds (Formula.Ands \<phi>s) = concat (map free_preds \<phi>s)"
| "free_preds (Formula.Exists t \<phi>) = free_preds \<phi>"
| "free_preds (Formula.Agg y \<omega> tys f \<phi>) = free_preds \<phi>"
| "free_preds (Formula.Prev I \<phi>) = free_preds \<phi>"
| "free_preds (Formula.Next I \<phi>) = free_preds \<phi>"
| "free_preds (Formula.Since \<phi> I \<psi>) = free_preds \<phi> @ free_preds \<psi>"
| "free_preds (Formula.Until \<phi> I \<psi>) = free_preds \<phi> @ free_preds \<psi>"
| "free_preds (Formula.Trigger \<phi> I \<psi>) = free_preds \<phi> @ free_preds \<psi>"
| "free_preds (Formula.Release \<phi> I \<psi>) = free_preds \<phi> @ free_preds \<psi>"
| "free_preds (Formula.MatchF I r) = regex_list free_preds r"
| "free_preds (Formula.MatchP I r) = regex_list free_preds r"
| "free_preds (Formula.TP t) = []"
| "free_preds (Formula.TS t) = []"

subsection \<open>The monitor on the log\<close>

text \<open>The configuration: which predicates' events to skip, the signature, the lookup of a
  predicate in it, and the reader of floats.\<close>

datatype vconf = VConf (vc_skip: "Formula.name \<Rightarrow> bool") (vc_lsig: lsig)
  (vc_lookup: "Formula.name \<times> nat \<Rightarrow> ty list option") (vc_pf: "bytes \<Rightarrow> double option")

text \<open>The parser keeps the events of the predicates whose names occur freely in the formula,
  and those of the predicates the signature does not declare, which the conversion reports. The
  events of the other predicates are neither converted nor checked.\<close>

definition vkeep :: "vconf \<Rightarrow> bytes \<Rightarrow> bool" where
  "vkeep cf b = (\<not> vc_skip cf (string8_of_bytes b))"

text \<open>The predicates whose events the parser skips: in a list for few predicates, in a set for
  many.\<close>

definition vskip :: "bool \<Rightarrow> tysym Formula.formula \<Rightarrow> lsig \<Rightarrow> Formula.name list" where
  "vskip filt \<phi> S = (if filt then (let F = set (map fst (free_preds \<phi>)) in filter (\<lambda>q. q \<notin> F) (map fst S))
     else [])"

definition vskip_fun :: "Formula.name list \<Rightarrow> Formula.name \<Rightarrow> bool" where
  "vskip_fun xs = (if length xs < 32 then (\<lambda>q. list_ex (str8_eq q) xs) else (let A = set xs in (\<lambda>q. q \<in> A)))"

text \<open>The state of the monitor proper is that of the executable monitor and the last timestamp; that of
  the whole monitor includes the parser's.\<close>

type_synonym vmstate = "emstate \<times> nat"
type_synonym vstate = "estate \<times> vmstate"

text \<open>The output: the verdicts of a time point, or an error at an offset in the input.\<close>

datatype vout = VO_VERDICTS "(nat \<times> ts \<times> utable) list" | VO_ERROR integer verror

definition vtp :: "integer \<Rightarrow> Formula.event list \<Rightarrow> nat \<Rightarrow> vmstate \<Rightarrow> vout \<times> vmstate" where
  "vtp sp xs t z = (if t < snd z then (VO_ERROR sp (VE_ORDER t (snd z)), z)
     else (case emstep (build_db xs, t) (fst z) of (vs, ust) \<Rightarrow> (VO_VERDICTS vs, (ust, t))))"

text \<open>An item that does not denote a time point is reported, and the monitor's state does not
  change. If the events do not convert, the error reported is the first of, in the order of
  MonPoly's parser: an event of an undeclared predicate, a decreasing timestamp, and the first
  event that does not convert (@{const conv_error}).\<close>

definition vitem :: "vconf \<Rightarrow> out \<Rightarrow> vmstate \<Rightarrow> vout \<times> vmstate" where
  "vitem cf x z = (case x of
     O_ERROR pos e \<Rightarrow> (VO_ERROR pos (VE_PARSE e), z)
   | O_ITEM sp (Command c args) \<Rightarrow> (VO_ERROR sp (VE_COMMAND c), z)
   | O_ITEM sp (Entry ts evs) \<Rightarrow> (case bnat_of ts of
       None \<Rightarrow> (VO_ERROR sp (VE_TIMESTAMP ts), z)
     | Some t \<Rightarrow> (case conv_events (vc_pf cf) (vc_lookup cf) evs of
         Inl e \<Rightarrow> (VO_ERROR sp (case pred_error (vc_lsig cf) evs of
             Some e' \<Rightarrow> e'
           | None \<Rightarrow> if t < snd z then VE_ORDER t (snd z)
             else (case conv_error (vc_pf cf) (vc_lookup cf) (vc_lsig cf) evs of Some e' \<Rightarrow> e' | None \<Rightarrow> e)), z)
       | Inr xs \<Rightarrow> vtp sp xs t z)))"

fun vitems :: "vconf \<Rightarrow> out list \<Rightarrow> vmstate \<Rightarrow> vout list \<times> vmstate" where
  "vitems cf [] z = ([], z)"
| "vitems cf (x # xs) z = (case vitem cf x z of (v, st1) \<Rightarrow>
     (case vitems cf xs st1 of (vs, st2) \<Rightarrow> (v # vs, st2)))"

fun vitems_acc :: "vconf \<Rightarrow> out list \<Rightarrow> vmstate \<Rightarrow> vout list \<Rightarrow> vout list \<times> vmstate" where
  "vitems_acc cf [] z acc = (rev acc, z)"
| "vitems_acc cf (x # xs) z acc = (case vitem cf x z of (v, st1) \<Rightarrow> vitems_acc cf xs st1 (v # acc))"

lemma vitems_acc: "vitems_acc cf xs z acc = (case vitems cf xs z of (vs, z') \<Rightarrow> (rev acc @ vs, z'))"
  by (induction cf xs z acc rule: vitems_acc.induct) (auto split: prod.splits)

lemma vitems_code[code]: "vitems cf xs z = vitems_acc cf xs z []"
  by (simp add: vitems_acc split: prod.splits)

text \<open>A chunk of the input, the end of the input, with an optional last time point with no events,
  and the initial state, if the formula is well-formed, its preparation succeeds, and the executable
  compiler covers it. Unless @{text filt} is set, the parser keeps all events.\<close>

definition vfeed_chunk :: "vconf \<Rightarrow> bytes \<Rightarrow> vstate \<Rightarrow> vout list \<times> vstate" where
  "vfeed_chunk cf s z = (case efeed_chunk (vkeep cf) s (fst z) of
     (xs, est) \<Rightarrow> (case vitems cf xs (snd z) of (vs, mst) \<Rightarrow> (vs, (est, mst))))"

definition vfinish :: "vconf \<Rightarrow> nat option \<Rightarrow> vstate \<Rightarrow> vout list" where
  "vfinish cf fin z = (case vitems cf (efinish (vkeep cf) (fst z)) (snd z) of
     (vs, mst) \<Rightarrow> vs @ (case fin of None \<Rightarrow> [] | Some t \<Rightarrow> [fst (vtp (fst (fst z)) [] t mst)]))"

datatype vinit_error = VI_WF | VI_PREPARE String.literal | VI_FRAGMENT nat

definition vinit :: "ipolicy \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> lsig \<Rightarrow> (bytes \<Rightarrow> double option) \<Rightarrow> tysym Formula.formula \<Rightarrow>
    vinit_error + vconf \<times> vstate" where
  "vinit ix mw rw filt S pf \<phi> = (if \<not> wf_formula \<phi> then Inl VI_WF else
     (case eminit_verimon ix mw rw (lsig_tsig S) \<phi> of
       Inl e \<Rightarrow> Inl (VI_PREPARE e)
     | Inr ust \<Rightarrow> (let n = efail_nodes (eabs (emstate_m ust)) in
         if n = 0 then Inr (VConf (vskip_fun (vskip filt \<phi> S)) S (lsig_lookup_fun S) pf, (einit, ust, 0))
         else Inl (VI_FRAGMENT n))))"

text \<open>For the driver: the least offset in the input that later outputs may report, except that
  of the pending item -- that of the pending lexeme, if any, and otherwise the number of bytes
  read.\<close>

definition vpending :: "vstate \<Rightarrow> integer" where
  "vpending z = (case fst z of (b, l, _) \<Rightarrow> (case l of
     E_SIMPLE xs j t \<Rightarrow> t | E_QUOTED xs j t \<Rightarrow> t | E_ESCAPE xs j t \<Rightarrow> t | _ \<Rightarrow> b))"

end
(*>*)
