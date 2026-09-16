(*<*)
theory Code_Opt
  imports Monitor_Impl
begin
(*>*)

section \<open>Efficient code equations\<close>

subsection \<open>Folding a red-black tree of keys\<close>

text \<open>
  @{const RBT_Set2.fold} is defined by discarding the value of each entry, which the generated
  code does by wrapping the element function in a closure: one closure allocated per fold, and
  two indirect calls per element instead of one.  A fold that takes the element function
  directly does the same work.
\<close>

fun rbt_fold_key :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a, unit) RBT_Impl.rbt \<Rightarrow> 'b \<Rightarrow> 'b" where
  "rbt_fold_key f RBT_Impl.Empty s = s"
| "rbt_fold_key f (RBT_Impl.Branch c l k v r) s = rbt_fold_key f r (f k (rbt_fold_key f l s))"

lemma rbt_fold_key_eq: "rbt_fold_key f t s = RBT_Impl.fold (\<lambda>a _. f a) t s"
  by (induction f t s rule: rbt_fold_key.induct) (auto simp: RBT_Impl.fold_def)

declare [[code drop: RBT_Set2.fold]]

lemma rbt_set2_fold_code[code]:
  "RBT_Set2.fold f t = rbt_fold_key f (RBT_Mapping2.impl_of t)"
  by (rule ext) (simp add: rbt_fold_key_eq RBT_Set2.fold.rep_eq)

declare [[code drop: rbt_fold]]

lemma rbt_fold_code[code]: "rbt_fold f t = rbt_fold_key f (RBT_Mapping2.impl_of t)"
  by (simp add: rbt_fold_def rbt_set2_fold_code)

text \<open>
  Folding over a mapped list builds the mapped list first.  Applying the two functions to the
  element in one step removes it, and -- because the redirections of Section \<open>Monomorphic_Code\<close>
  rewrite an operation applied to an argument, not an operation on its own -- it also lets the
  monomorphic container operations reach folds whose function argument was written point-free.
\<close>

lemma fold_map_unfold[code_unfold]: "fold f (map g xs) = fold (\<lambda>x. f (g x)) xs"
  by (simp add: fold_map comp_def)

text \<open>
  @{const fst} and @{const snd} are generated from their defining equations on a pair pattern,
  which compiles them as functions of two arguments; every application to a pair that is not
  written out at the call site then goes through the adapter that rebuilds the pair.  They
  account for five of the eleven million entries into it on P2.
\<close>

declare [[code drop: fst snd]]

lemma fst_code[code]: "fst p = (case p of (a, b) \<Rightarrow> a)"
  by (simp split: prod.splits)

lemma snd_code[code]: "snd p = (case p of (a, b) \<Rightarrow> b)"
  by (simp split: prod.splits)

text \<open>
  The lookup in a red-black tree is stated point-free, so the generated code applies it to the
  tree, gets a closure back and then applies that to the key: one closure allocated per lookup,
  and on P2 that is 1.3\% of everything the monitor allocates.
\<close>

declare [[code drop: RBT_Mapping2.lookup]]

lemma rbt_mapping2_lookup_code[code]:
  "RBT_Mapping2.lookup t k = rbt_comp_lookup ccomp (RBT_Mapping2.impl_of t) k"
  by (simp add: RBT_Mapping2.lookup_def)

subsection \<open>Direct comparators\<close>

text \<open>
  The comparators derived by the @{text derive} command are expressed via the generic
  @{const comparator_of}, whose generated code performs two dictionary-dispatched comparisons
  (@{text "<"} followed by @{text "="}) per element. The following code equations spell out the
  comparators for the base types occurring in event data and tuples directly.
\<close>

declare [[code drop: "compare :: nat \<Rightarrow> _" "compare :: integer \<Rightarrow> _" "compare :: string8 \<Rightarrow> _" comparator_event_data]]

lemma compare_nat_code[code]: "compare (x :: nat) y = (if x < y then Lt else if x = y then Eq else Gt)"
  by (simp add: compare_nat_def comparator_of_def)

lemma compare_integer_code[code]: "compare (x :: integer) y = (if x < y then Lt else if x = y then Eq else Gt)"
  by (simp add: compare_integer_def comparator_of_def)

lemma compare_string8_code[code]: "compare (x :: string8) y = (if x < y then Lt else if x = y then Eq else Gt)"
  by (simp add: compare_string8_def comparator_of_def)

lemma comparator_event_data_code[code]:
  "comparator_event_data (EInt x) (EInt y) = (if x < y then Lt else if x = y then Eq else Gt)"
  "comparator_event_data (EInt x) (EFloat e) = Lt"
  "comparator_event_data (EInt x) (EString t) = Lt"
  "comparator_event_data (EFloat d) (EInt y) = Gt"
  "comparator_event_data (EFloat d) (EFloat e) = comparator_double d e"
  "comparator_event_data (EFloat d) (EString t) = Lt"
  "comparator_event_data (EString s) (EInt y) = Gt"
  "comparator_event_data (EString s) (EFloat e) = Gt"
  "comparator_event_data (EString s) (EString t) = (if s < t then Lt else if s = t then Eq else Gt)"
  by (simp_all add: comparator_of_def)

subsection \<open>Run-time selection of the multi-way join strategy\<close>

text \<open>
  @{const use_generic_join} is an unspecified constant; both values are covered by the
  correctness proofs. The generated code reads it from a mutable flag in a small auxiliary
  module, so that the front end can choose the strategy at run time.
\<close>

code_printing code_module Config \<rightharpoonup> (OCaml)
\<open>module Config : sig
  val generic_join : bool ref
  val imperative_join : bool ref
  val bulk_min : int ref
end = struct
  let generic_join = ref false
  let imperative_join = ref false
  let bulk_min = ref 64
end\<close>
| constant use_generic_join \<rightharpoonup> (OCaml) "'!Config.generic'_join"

text \<open>
  The smallest table that is worth building in one pass from a sorted list rather than by
  inserting its tuples one at a time (see @{text set_of_list} in theory @{text
  Monomorphic_Code}). Sorting costs \<open>n log n\<close> comparisons on top of the ones the insertions
  would have done, so for a handful of tuples it does not pay. The value is read from a
  mutable flag so that it can be measured without regenerating the kernel.
\<close>

definition bulk_min :: integer where
  "bulk_min = 64"

code_printing
  constant bulk_min \<rightharpoonup> (OCaml) "(Z.of'_int '!Config.bulk'_min)"

subsection \<open>Joins\<close>

text \<open>
  The default code for the general case of @{const bin_join} is a nested loop over both tables
  (quadratic in the table sizes). We replace it, via a proven code equation, by an index-based
  join.
  The code equations are unconditional theorems, so the correctness proofs of the monitor
  are unaffected. (The multi-way join is evaluated pairwise by definition, see
  @{const mmulti_join} in theory @{text Optimized_Join}.)
\<close>

subsection \<open>Nested-loop join as a fold\<close>

text \<open>
  The default code equation @{thm join_True_code} builds a set of singleton sets (which
  requires the expensive comparator on sets) and then takes its union. We replace it by a
  double fold that inserts the joined tuples directly into the result.
\<close>

definition join1_insert :: "'a tuple \<Rightarrow> 'a tuple \<Rightarrow> 'a table \<Rightarrow> 'a table" where
  "join1_insert a b acc = (case join1 (a, b) of None \<Rightarrow> acc | Some z \<Rightarrow> Set.insert z acc)"

lemma comp_fun_idem_join1_insert: "comp_fun_idem (join1_insert a)"
  by unfold_locales (auto simp: fun_eq_iff join1_insert_def Set.insert_commute split: option.splits)

lemma fold_join1_insert:
  assumes "finite B"
  shows "Finite_Set.fold (join1_insert a) acc B = acc \<union> (\<Union>b \<in> B. set_option (join1 (a, b)))"
proof -
  interpret comp_fun_idem "join1_insert a"
    by (rule comp_fun_idem_join1_insert)
  from assms show ?thesis
  proof (induction B arbitrary: acc)
    case (insert x B)
    then show ?case
      unfolding fold_insert[OF insert.hyps(1,2)] insert.IH
      by (auto simp: join1_insert_def split: option.splits)
  qed simp
qed

lift_definition join1_insert_cfi :: "'a tuple \<Rightarrow> ('a tuple, 'a table) comp_fun_idem" is join1_insert
  by (rule comp_fun_idem_join1_insert)

definition join_row :: "'a table \<Rightarrow> 'a tuple \<Rightarrow> 'a table \<Rightarrow> 'a table" where
  "join_row B a acc = set_fold_cfi (join1_insert_cfi a) acc B"

lemma join_row_alt: "join_row B a acc = (if finite B then acc \<union> (\<Union>b \<in> B. set_option (join1 (a, b))) else acc)"
  unfolding join_row_def set_fold_cfi.rep_eq join1_insert_cfi.rep_eq
  by (cases "finite B") (auto simp: fold_join1_insert)

lemma comp_fun_idem_join_row: "comp_fun_idem (join_row B)"
  by unfold_locales (auto simp: fun_eq_iff join_row_alt)

lift_definition join_row_cfi :: "'a table \<Rightarrow> ('a tuple, 'a table) comp_fun_idem" is join_row
  by (rule comp_fun_idem_join_row)

lemma fold_join_row:
  assumes "finite A" "finite B"
  shows "Finite_Set.fold (join_row B) {} A = join A True B"
proof -
  interpret comp_fun_idem "join_row B"
    by (rule comp_fun_idem_join_row)
  from assms(1) show ?thesis
    unfolding join_True_code
  proof (induction A)
    case (insert x F)
    have "Finite_Set.fold (join_row B) {} (Set.insert x F) = join_row B x (Finite_Set.fold (join_row B) {} F)"
      by (rule fold_insert[OF insert.hyps(1,2)])
    also have "\<dots> = join_row B x (\<Union>a\<in>F. \<Union>b\<in>B. set_option (join1 (a, b)))"
      unfolding insert.IH ..
    also have "\<dots> = (\<Union>a\<in>Set.insert x F. \<Union>b\<in>B. set_option (join1 (a, b)))"
      unfolding join_row_alt using assms(2) by auto
    finally show ?case .
  qed simp
qed

declare [[code drop: join]]

lemma join_True_fold_code[code]:
  "join A True B = (if finite A \<and> finite B then set_fold_cfi (join_row_cfi B) {} A
     else Code.abort (STR ''join: infinite table'') (\<lambda>_. join A True B))"
proof (cases "finite A \<and> finite B")
  case True
  have "set_fold_cfi (join_row_cfi B) {} A = Finite_Set.fold (join_row B) {} A"
    unfolding set_fold_cfi.rep_eq join_row_cfi.rep_eq ..
  then show ?thesis
    using True by (simp add: fold_join_row)
next
  case False
  show ?thesis
    unfolding if_not_P[OF False] by simp
qed

lemmas join_False_code'[code] = join_False_code

subsection \<open>Index-based binary join\<close>

text \<open>
  The general case of @{const bin_join} (neither column set contains the other) clusters the
  smaller table by the common columns and probes the resulting index with the tuples of the
  larger table. The code equation is unconditional: it checks that all tuples are defined on
  the join columns (which holds for well-formed tables) and otherwise falls back to the
  nested loop.
\<close>

definition complete_on :: "nat set \<Rightarrow> 'a tuple \<Rightarrow> bool" where
  "complete_on I t \<longleftrightarrow> (\<forall>i \<in> I. i < length t \<and> t ! i \<noteq> None)"

lemma join1_Some_restrict_complete:
  assumes "join1 (x, y) = Some z" "complete_on I x" "complete_on I y"
  shows "restrict I x = restrict I y"
proof -
  have len: "length x = length y"
    and nth: "\<And>i. i < length x \<Longrightarrow> x ! i = None \<or> y ! i = None \<or> (\<exists>a. x ! i = Some a \<and> y ! i = Some a)"
    using join1_Some_iff[of x y] assms(1) by auto
  have eq: "x ! i = y ! i" if "i \<in> I" for i
  proof -
    have "i < length x" "x ! i \<noteq> None" "y ! i \<noteq> None"
      using assms(2,3) that by (auto simp: complete_on_def)
    then show ?thesis
      using nth[of i] by auto
  qed
  show ?thesis
    unfolding restrict_def len
    by (rule map_cong[OF refl]) (simp add: eq)
qed

lemma lookup_cluster: "Mapping.lookup (cluster f Y) x =
  (if Some x \<in> f ` Y then Some {y \<in> Y. f y = Some x} else None)"
  by transfer simp

subsection \<open>Probe join: index the smaller table, probe with the larger one\<close>

definition join1_insert' :: "'a tuple \<Rightarrow> 'a tuple \<Rightarrow> 'a table \<Rightarrow> 'a table" where
  "join1_insert' b a acc = join1_insert a b acc"

lemma comp_fun_idem_join1_insert': "comp_fun_idem (join1_insert' b)"
  by unfold_locales
    (auto simp: fun_eq_iff join1_insert'_def join1_insert_def Set.insert_commute split: option.splits)

lemma fold_join1_insert':
  assumes "finite T"
  shows "Finite_Set.fold (join1_insert' b) acc T = acc \<union> (\<Union>a \<in> T. set_option (join1 (a, b)))"
proof -
  interpret comp_fun_idem "join1_insert' b"
    by (rule comp_fun_idem_join1_insert')
  from assms show ?thesis
  proof (induction T arbitrary: acc)
    case (insert x T)
    then show ?case
      unfolding fold_insert[OF insert.hyps(1,2)] insert.IH
      by (auto simp: join1_insert'_def join1_insert_def split: option.splits)
  qed simp
qed

lift_definition join1_insert_cfi' :: "'a tuple \<Rightarrow> ('a tuple, 'a table) comp_fun_idem" is join1_insert'
  by (rule comp_fun_idem_join1_insert')

definition probe_step :: "nat set \<Rightarrow> ('a tuple, 'a table) mapping \<Rightarrow> 'a tuple \<Rightarrow> 'a table \<Rightarrow> 'a table" where
  "probe_step I m b acc = (case Mapping.lookup m (restrict I b) of None \<Rightarrow> acc
     | Some T \<Rightarrow> set_fold_cfi (join1_insert_cfi' b) acc T)"

lemma probe_step_alt: "probe_step I m b acc = (case Mapping.lookup m (restrict I b) of None \<Rightarrow> acc
     | Some T \<Rightarrow> if finite T then acc \<union> (\<Union>a \<in> T. set_option (join1 (a, b))) else acc)"
  unfolding probe_step_def set_fold_cfi.rep_eq join1_insert_cfi'.rep_eq
  by (auto simp: fold_join1_insert' split: option.splits)

lemma comp_fun_idem_probe_step: "comp_fun_idem (probe_step I m)"
  by unfold_locales (auto simp: fun_eq_iff probe_step_alt split: option.splits)

lift_definition probe_step_cfi :: "nat set \<Rightarrow> ('a tuple, 'a table) mapping \<Rightarrow> ('a tuple, 'a table) comp_fun_idem"
  is probe_step
  by (rule comp_fun_idem_probe_step)

definition probe_join :: "nat set \<Rightarrow> 'a table \<Rightarrow> 'a table \<Rightarrow> 'a table" where
  "probe_join I t t' = set_fold_cfi (probe_step_cfi I (cluster (Some \<circ> restrict I) t)) {} t'"

lemma fold_probe_step:
  assumes "finite t" "finite t'"
  shows "Finite_Set.fold (probe_step I (cluster (Some \<circ> restrict I) t)) {} t' =
    (\<Union>b \<in> t'. \<Union>a \<in> {a \<in> t. restrict I a = restrict I b}. set_option (join1 (a, b)))"
proof -
  interpret comp_fun_idem "probe_step I (cluster (Some \<circ> restrict I) t)"
    by (rule comp_fun_idem_probe_step)
  let ?m = "cluster (Some \<circ> restrict I) t"
  from assms(2) show ?thesis
  proof (induction t')
    case (insert b F)
    have fin: "finite {a \<in> t. restrict I a = restrict I b}"
      using assms(1) by simp
    have "Finite_Set.fold (probe_step I ?m) {} (Set.insert b F) = probe_step I ?m b (Finite_Set.fold (probe_step I ?m) {} F)"
      by (rule fold_insert[OF insert.hyps(1,2)])
    also have "\<dots> = probe_step I ?m b (\<Union>b \<in> F. \<Union>a \<in> {a \<in> t. restrict I a = restrict I b}. set_option (join1 (a, b)))"
      unfolding insert.IH ..
    also have "\<dots> = (\<Union>b \<in> Set.insert b F. \<Union>a \<in> {a \<in> t. restrict I a = restrict I b}. set_option (join1 (a, b)))"
      unfolding probe_step_alt lookup_cluster using fin by (auto split: if_splits simp: image_iff)
    finally show ?case .
  qed simp
qed

lemma probe_join_join:
  assumes "finite t" "finite t'" "\<forall>x \<in> t. complete_on I x" "\<forall>y \<in> t'. complete_on I y"
  shows "probe_join I t t' = join t True t'"
  unfolding probe_join_def set_fold_cfi.rep_eq probe_step_cfi.rep_eq fold_probe_step[OF assms(1,2)]
proof (intro set_eqI iffI)
  fix z
  assume "z \<in> (\<Union>b \<in> t'. \<Union>a \<in> {a \<in> t. restrict I a = restrict I b}. set_option (join1 (a, b)))"
  then show "z \<in> join t True t'"
    unfolding join_True_code by auto
next
  fix z
  assume "z \<in> join t True t'"
  then obtain a b where ab: "a \<in> t" "b \<in> t'" "join1 (a, b) = Some z"
    unfolding join_True_code by auto
  then have "restrict I a = restrict I b"
    using assms(3,4) join1_Some_restrict_complete by blast
  then show "z \<in> (\<Union>b \<in> t'. \<Union>a \<in> {a \<in> t. restrict I a = restrict I b}. set_option (join1 (a, b)))"
    using ab by (intro UN_I[of b] UN_I[of a]) auto
qed

section \<open>Projections without index arithmetic\<close>

text \<open>
  @{const restrict} is defined through @{term "[0..<length v]"} and @{const nth}, i.e. with
  big-integer index arithmetic and quadratic list access per tuple; it is evaluated for every
  tuple of both operands of a probe join and for every tuple entering a tuple index. The code
  equation below walks the tuple once. For the probe join the column set is additionally
  turned into a mask once per join (@{text restrict_with}), which is the same function as
  @{const restrict} (it falls back to it for tuples of an unexpected length), so that the
  projection of a tuple is a single traversal without set membership tests.
\<close>

fun restrict_aux :: "nat \<Rightarrow> nat set \<Rightarrow> 'a option list \<Rightarrow> 'a option list" where
  "restrict_aux i A [] = []"
| "restrict_aux i A (x # xs) = (if i \<in> A then x else None) # restrict_aux (Suc i) A xs"

lemma length_restrict_aux[simp]: "length (restrict_aux i A v) = length v"
  by (induction v arbitrary: i) auto

lemma nth_restrict_aux: "j < length v \<Longrightarrow> restrict_aux i A v ! j = (if i + j \<in> A then v ! j else None)"
  by (induction v arbitrary: i j) (auto simp: nth_Cons split: nat.splits)

declare [[code drop: restrict]]

lemma restrict_code[code]: "restrict A v = restrict_aux 0 A v"
  by (rule nth_equalityI) (auto simp: restrict_def nth_restrict_aux)

fun proj_tuple_chk :: "bool list \<Rightarrow> 'a tuple \<Rightarrow> 'a tuple option" where
  "proj_tuple_chk [] [] = Some []"
| "proj_tuple_chk (b # bs) (x # xs) = map_option ((#) (if b then x else None)) (proj_tuple_chk bs xs)"
| "proj_tuple_chk _ _ = None"

lemma proj_tuple_chk: "proj_tuple_chk bs xs = (if length bs = length xs then Some (proj_tuple bs xs) else None)"
  by (induction bs xs rule: proj_tuple_chk.induct) auto

definition restrict_with :: "nat set \<Rightarrow> nat \<Rightarrow> 'a tuple \<Rightarrow> 'a tuple" where
  "restrict_with I n = (let mask = join_mask n I in
    (\<lambda>v. case proj_tuple_chk mask v of Some r \<Rightarrow> r | None \<Rightarrow> restrict I v))"

lemma restrict_with[simp]: "restrict_with I n = restrict I"
proof -
  have len: "length (join_mask n I) = n"
    by (simp add: join_mask_def)
  show ?thesis
    by (auto simp: restrict_with_def Let_def fun_eq_iff proj_tuple_chk len proj_tuple_join_mask_restrict
        split: option.splits if_splits)
qed

text \<open>
  The probe join requires all join columns to be defined in every tuple of both operands
  (@{const complete_on}); @{const bin_join} checks this for every tuple on every join, with
  @{const length} and @{const nth} on big-integer indices. @{text complete_with} builds the mask
  once per join and checks a tuple in one traversal; it equals @{const complete_on}
  unconditionally (a tuple of an unexpected length or a column set outside the arity falls
  back to the definition).
\<close>

fun complete_chk :: "bool list \<Rightarrow> 'a option list \<Rightarrow> bool option" where
  "complete_chk [] [] = Some True"
| "complete_chk (b # bs) (x # xs) = (case complete_chk bs xs of None \<Rightarrow> None
    | Some r \<Rightarrow> Some ((b \<longrightarrow> x \<noteq> None) \<and> r))"
| "complete_chk _ _ = None"

lemma complete_chk: "complete_chk bs xs =
  (if length bs = length xs then Some (\<forall>i < length bs. bs ! i \<longrightarrow> xs ! i \<noteq> None) else None)"
  by (induction bs xs rule: complete_chk.induct) (auto simp: less_Suc_eq_0_disj nth_Cons split: nat.splits)

lemma complete_on_mask:
  assumes "\<forall>i \<in> I. i < n" "length t = n"
  shows "complete_on I t \<longleftrightarrow> (\<forall>i < n. join_mask n I ! i \<longrightarrow> t ! i \<noteq> None)"
  using assms by (auto simp: complete_on_def join_mask_def)

definition complete_with :: "nat set \<Rightarrow> nat \<Rightarrow> 'a tuple \<Rightarrow> bool" where
  "complete_with I n = (let mask = join_mask n I; ok = (\<forall>i \<in> I. i < n) in
    (\<lambda>t. if ok then (case complete_chk mask t of Some b \<Rightarrow> b | None \<Rightarrow> complete_on I t)
     else complete_on I t))"

lemma complete_with[simp]: "complete_with I n = complete_on I"
proof -
  have len: "length (join_mask m I) = m" for m
    by (simp add: join_mask_def)
  show ?thesis
    by (auto simp: complete_with_def Let_def fun_eq_iff complete_chk len complete_on_mask split: option.splits if_splits)
qed

definition probe_join_n :: "nat \<Rightarrow> nat set \<Rightarrow> 'a table \<Rightarrow> 'a table \<Rightarrow> 'a table" where
  "probe_join_n n I t t' = probe_join I t t'"

declare [[code drop: bin_join]]

lemma bin_join_code[code]:
  "bin_join n A t pos A' t' =
    (if t = {} then {}
    else if t' = {} then (if pos then {} else t)
    else if A' = {} then (if (pos \<longleftrightarrow> replicate n None \<in> t') then t else {})
    else if A' = A then (if pos then t \<inter> t' else t - t')
    else if A' \<subseteq> A then (let m = join_mask n A' in {as \<in> t. proj_tuple_in_join pos m as t'})
    else if A \<subseteq> A' \<and> pos then (let m = join_mask n A in {as \<in> t'. proj_tuple_in_join pos m as t})
    else if pos \<and> finite t \<and> finite t' \<and>
        (let c = complete_with (A \<inter> A') n in (\<forall>x \<in> t. c x) \<and> (\<forall>y \<in> t'. c y))
      then (if card t \<le> card t' then probe_join_n n (A \<inter> A') t t' else probe_join_n n (A \<inter> A') t' t)
    else join t pos t')"
  by (subst bin_join.simps) (auto simp: Let_def probe_join_n_def probe_join_join join_commute)

section \<open>Code equations for the auxiliary structures\<close>

subsection \<open>Until: building the candidate set without sets of sets\<close>

text \<open>
  The code equations of @{const add_new_mmuaux} and @{const add_new_mmauaux} build the set of
  candidate tuples as the union of an image of singleton sets, which the generated code
  evaluates through a set of sets (and its expensive comparator). We build it with a fold.
\<close>

definition tmp_elem :: "('a tuple, nat) mapping \<Rightarrow> bool list \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a tuple \<Rightarrow> (nat \<times> 'a tuple) set" where
  "tmp_elem a1_map maskL pos tp len as = (case Mapping.lookup a1_map (proj_tuple maskL as) of None \<Rightarrow>
      (if \<not>pos then {(tp - len, as)} else {})
      | Some tp' \<Rightarrow> if pos then {(max (tp - len) tp', as)}
      else {(max (tp - len) (tp' + 1), as)})"

lemma tmp_elem_eta: "tmp_elem a1_map maskL pos tp len = (\<lambda>as. case Mapping.lookup a1_map (proj_tuple maskL as) of None \<Rightarrow>
      (if \<not>pos then {(tp - len, as)} else {})
      | Some tp' \<Rightarrow> if pos then {(max (tp - len) tp', as)}
      else {(max (tp - len) (tp' + 1), as)})"
  by (simp add: fun_eq_iff tmp_elem_def)

definition tmp_step :: "('a tuple, nat) mapping \<Rightarrow> bool list \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a tuple \<Rightarrow> (nat \<times> 'a tuple) set \<Rightarrow> (nat \<times> 'a tuple) set" where
  "tmp_step a1_map maskL pos tp len as acc = (case Mapping.lookup a1_map (proj_tuple maskL as) of
      None \<Rightarrow> (if \<not>pos then Set.insert (tp - len, as) acc else acc)
    | Some tp' \<Rightarrow> (if pos then Set.insert (max (tp - len) tp', as) acc else Set.insert (max (tp - len) (tp' + 1), as) acc))"

lemma comp_fun_idem_tmp_step: "comp_fun_idem (tmp_step a1_map maskL pos tp len)"
  by unfold_locales (auto simp: fun_eq_iff tmp_step_def Set.insert_commute split: option.splits)

lemma fold_tmp_step:
  assumes "finite X"
  shows "Finite_Set.fold (tmp_step a1_map maskL pos tp len) acc X = acc \<union> \<Union>(tmp_elem a1_map maskL pos tp len ` X)"
proof -
  interpret comp_fun_idem "tmp_step a1_map maskL pos tp len"
    by (rule comp_fun_idem_tmp_step)
  from assms show ?thesis
  proof (induction X arbitrary: acc)
    case (insert x X)
    then show ?case
      unfolding fold_insert[OF insert.hyps(1,2)] insert.IH
      by (auto simp: tmp_step_def tmp_elem_def split: option.splits)
  qed simp
qed

lift_definition tmp_step_cfi :: "('a tuple, nat) mapping \<Rightarrow> bool list \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('a tuple, (nat \<times> 'a tuple) set) comp_fun_idem"
  is tmp_step
  by (rule comp_fun_idem_tmp_step)

definition tmp_set :: "('a tuple, nat) mapping \<Rightarrow> bool list \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> 'a tuple) set \<Rightarrow> 'a table \<Rightarrow> (nat \<times> 'a tuple) set" where
  "tmp_set a1_map maskL pos tp len B rel2 = \<Union>(tmp_elem a1_map maskL pos tp len ` rel2) \<union> B"

lemma tmp_set_code[code]:
  "tmp_set a1_map maskL pos tp len B rel2 = (if finite rel2 then set_fold_cfi (tmp_step_cfi a1_map maskL pos tp len) B rel2
     else Code.abort (STR ''tmp_set: infinite table'') (\<lambda>_. tmp_set a1_map maskL pos tp len B rel2))"
  unfolding set_fold_cfi.rep_eq tmp_step_cfi.rep_eq by (simp add: fold_tmp_step tmp_set_def Un_commute)

declare [[code drop: add_new_mmuaux add_new_mmauaux]]

lemma add_new_mmuaux_fold_code:
  "add_new_mmuaux args rel1 rel2 nt aux =
    (let (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_map, tstp_map, done) =
    shift_mmuaux args nt aux;
    I = args_ivl args; pos = args_pos args;
    new_tstp = (if memL I 0 then Inr tp else Inl nt);
    tstp_map = Mapping.update tp nt tstp_map;
    tmp = tmp_set a1_map maskL pos tp len (if memL I 0 then {tp} \<times> rel2 else {}) rel2;
    tmp = Set.filter (\<lambda>(tp, as). case Mapping.lookup tstp_map tp of Some ts \<Rightarrow> memL I (nt - ts)) tmp;
    table = snd ` tmp;
    tables = append_queue (table, if memL I 0 then Inr tp else Inl nt) tables;
    a2_map = Mapping.update (tp + 1) Mapping.empty
      (upd_nested_max_tstp a2_map new_tstp tmp);
    a1_map = (if pos then Mapping.filter (\<lambda>as _. as \<in> rel1)
      (upd_set a1_map (\<lambda>_. tp) (rel1 - Mapping.keys a1_map)) else upd_set a1_map (\<lambda>_. tp) rel1);
    tss = append_queue nt tss in
    (tp + 1, tss, tables, len + 1, maskL, maskR, result \<union> snd ` (Set.filter (\<lambda>(t, x). t = tp - len) tmp), a1_map, a2_map, tstp_map, done))" 
  by (subst add_new_mmuaux_code) (simp only: tmp_set_def tmp_elem_eta)

text \<open>
  For the plain Until structure the three consumers of @{text tmp} (the table appended to the
  queue, the nested update of @{text a2_map} and the contribution to the result) are computed
  in one fold over the new table instead: @{text until_step} processes one pair, and
  @{text until_elem_step} the one or two pairs that a tuple of the operand contributes; both
  are @{const comp_fun_idem}, so that the fold over the operand equals the folds over the
  pair set (@{text fold_until_elem_step}, @{text fold_until_step}). The aggregation variant
  below still materialises the pair set, which it also needs for its own bookkeeping.
\<close>

lemma cfi_upd_nested_step: "comp_fun_idem (upd_nested_step d (max_tstp d))"
  by (unfold_locales; rule ext)
    (auto simp add: comp_def upd_nested_step_def Mapping.lookup_update'
      update_update max_tstp_d_d max_tstp_idem' split: option.splits)

type_synonym 'a until_acc = "'a table \<times> (nat, ('a tuple, ts + tp) mapping) mapping \<times> 'a table"

definition until_step :: "(nat \<Rightarrow> bool) \<Rightarrow> ts + tp \<Rightarrow> nat \<Rightarrow> nat \<times> 'a tuple \<Rightarrow> 'a until_acc \<Rightarrow> 'a until_acc" where
  "until_step P d t0 p acc = (case acc of (tbl, a2, res) \<Rightarrow> if P (fst p) then
     (Set.insert (snd p) tbl, upd_nested_step d (max_tstp d) p a2,
      if fst p = t0 then Set.insert (snd p) res else res)
   else acc)"

lemma comp_fun_idem_until_step: "comp_fun_idem (until_step P d t0 :: nat \<times> 'a tuple \<Rightarrow> 'a until_acc \<Rightarrow> 'a until_acc)"
proof -
  interpret u: comp_fun_idem "upd_nested_step d (max_tstp d)" by (rule cfi_upd_nested_step)
  have comm: "upd_nested_step d (max_tstp d) y (upd_nested_step d (max_tstp d) x a) =
    upd_nested_step d (max_tstp d) x (upd_nested_step d (max_tstp d) y a)"
    for x y :: "nat \<times> 'a tuple" and a :: "(nat, ('a tuple, ts + tp) mapping) mapping"
    using u.fun_left_comm by metis
  have idem: "upd_nested_step d (max_tstp d) x (upd_nested_step d (max_tstp d) x a) =
    upd_nested_step d (max_tstp d) x a"
    for x :: "nat \<times> 'a tuple" and a :: "(nat, ('a tuple, ts + tp) mapping) mapping"
    using u.fun_left_idem by metis
  show ?thesis
    by unfold_locales (auto simp: fun_eq_iff until_step_def comm idem Set.insert_commute split: prod.splits)
qed

lemma Set_filter_insert: "Set.filter Q (Set.insert x X) = (if Q x then Set.insert x (Set.filter Q X) else Set.filter Q X)"
  by auto

lemma fold_until_step:
  assumes "finite X"
  shows "Finite_Set.fold (until_step P d t0) (tbl, a2, res) X =
    (tbl \<union> snd ` Set.filter (\<lambda>p. P (fst p)) X, upd_nested_max_tstp a2 d (Set.filter (\<lambda>p. P (fst p)) X),
     res \<union> snd ` Set.filter (\<lambda>p. P (fst p) \<and> fst p = t0) X)"
proof -
  interpret comp_fun_idem "until_step P d t0" by (rule comp_fun_idem_until_step)
  note upd_nested_insert' = upd_nested_insert[of d "max_tstp d", OF max_tstp_d_d[symmetric] max_tstp_idem']
  from assms show ?thesis
  proof (induction X)
    case (insert x X)
    show ?case
      unfolding fold_insert[OF insert.hyps(1,2)] insert.IH Set_filter_insert
      by (cases "P (fst x)"; cases "fst x = t0")
        (simp_all add: until_step_def upd_nested_max_tstp_def upd_nested_insert')
  qed (simp add: upd_nested_max_tstp_def)
qed

definition until_pairs :: "('a tuple, nat) mapping \<Rightarrow> bool list \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> 'a tuple \<Rightarrow> (nat \<times> 'a tuple) set" where
  "until_pairs a1_map maskL pos tp len inz as = tmp_elem a1_map maskL pos tp len as \<union> (if inz then {(tp, as)} else {})"

lemma finite_tmp_elem: "finite (tmp_elem a1_map maskL pos tp len as)"
  by (auto simp: tmp_elem_def split: option.splits)

lemma finite_until_pairs: "finite (until_pairs a1_map maskL pos tp len inz as)"
  by (auto simp: until_pairs_def finite_tmp_elem)

definition until_elem_step :: "('a tuple, nat) mapping \<Rightarrow> bool list \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow>
  (nat \<Rightarrow> bool) \<Rightarrow> ts + tp \<Rightarrow> 'a tuple \<Rightarrow> 'a until_acc \<Rightarrow> 'a until_acc" where
  "until_elem_step a1_map maskL pos tp len inz P d as acc =
    (let acc' = (case Mapping.lookup a1_map (proj_tuple maskL as) of
        None \<Rightarrow> (if \<not>pos then until_step P d (tp - len) (tp - len, as) acc else acc)
      | Some tp' \<Rightarrow> until_step P d (tp - len) (if pos then (max (tp - len) tp', as) else (max (tp - len) (tp' + 1), as)) acc)
     in if inz then until_step P d (tp - len) (tp, as) acc' else acc')"

lemma until_elem_step_fold:
  "until_elem_step a1_map maskL pos tp len inz P d as acc =
    Finite_Set.fold (until_step P d (tp - len)) acc (until_pairs a1_map maskL pos tp len inz as)"
proof -
  interpret comp_fun_idem "until_step P d (tp - len)" by (rule comp_fun_idem_until_step)
  show ?thesis
    by (auto simp: until_elem_step_def until_pairs_def tmp_elem_def Let_def split: option.splits)
qed

lemma fold_fold_union:
  assumes "comp_fun_idem f" "finite A" "finite B"
  shows "Finite_Set.fold f (Finite_Set.fold f z A) B = Finite_Set.fold f z (A \<union> B)"
proof -
  interpret comp_fun_idem f by fact
  from assms(3) show ?thesis
    using assms(2) by (induction B) auto
qed

lemma comp_fun_idem_until_elem_step: "comp_fun_idem (until_elem_step a1_map maskL pos tp len inz P d)"
proof -
  note cfi = comp_fun_idem_until_step[of P d "tp - len"]
  show ?thesis
    by unfold_locales
      (auto simp: fun_eq_iff until_elem_step_fold fold_fold_union[OF cfi finite_until_pairs finite_until_pairs] Un_commute)
qed

lift_definition until_elem_step_cfi :: "('a tuple, nat) mapping \<Rightarrow> bool list \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow>
  (nat \<Rightarrow> bool) \<Rightarrow> ts + tp \<Rightarrow> ('a tuple, 'a until_acc) comp_fun_idem"
  is until_elem_step
  by (rule comp_fun_idem_until_elem_step)

definition until_tmp :: "('a tuple, nat) mapping \<Rightarrow> bool list \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> 'a table \<Rightarrow> (nat \<times> 'a tuple) set" where
  "until_tmp a1_map maskL pos tp len inz rel2 = \<Union>(tmp_elem a1_map maskL pos tp len ` rel2) \<union> (if inz then {tp} \<times> rel2 else {})"

lemma until_tmp_insert: "until_tmp a1_map maskL pos tp len inz (Set.insert as rel2) =
  until_tmp a1_map maskL pos tp len inz rel2 \<union> until_pairs a1_map maskL pos tp len inz as"
  by (auto simp: until_tmp_def until_pairs_def)

lemma finite_until_tmp: "finite rel2 \<Longrightarrow> finite (until_tmp a1_map maskL pos tp len inz rel2)"
  by (auto simp: until_tmp_def finite_tmp_elem)

lemma fold_until_elem_step:
  assumes "finite rel2"
  shows "Finite_Set.fold (until_elem_step a1_map maskL pos tp len inz P d) acc rel2 =
    Finite_Set.fold (until_step P d (tp - len)) acc (until_tmp a1_map maskL pos tp len inz rel2)"
proof -
  interpret e: comp_fun_idem "until_elem_step a1_map maskL pos tp len inz P d" by (rule comp_fun_idem_until_elem_step)
  note cfi = comp_fun_idem_until_step[of P d "tp - len"]
  from assms show ?thesis
  proof (induction rel2)
    case (insert as rel2)
    have "Finite_Set.fold (until_elem_step a1_map maskL pos tp len inz P d) acc (Set.insert as rel2) =
      until_elem_step a1_map maskL pos tp len inz P d as (Finite_Set.fold (until_elem_step a1_map maskL pos tp len inz P d) acc rel2)"
      by (rule e.fold_insert[OF insert.hyps(1,2)])
    also have "\<dots> = Finite_Set.fold (until_step P d (tp - len))
      (Finite_Set.fold (until_step P d (tp - len)) acc (until_tmp a1_map maskL pos tp len inz rel2))
      (until_pairs a1_map maskL pos tp len inz as)"
      unfolding insert.IH by (rule until_elem_step_fold)
    also have "\<dots> = Finite_Set.fold (until_step P d (tp - len)) acc (until_tmp a1_map maskL pos tp len inz (Set.insert as rel2))"
      unfolding until_tmp_insert by (rule fold_fold_union[OF cfi finite_until_tmp[OF insert.hyps(1)] finite_until_pairs])
    finally show ?case .
  qed (simp add: until_tmp_def)
qed

lemma until_fused:
  assumes "finite rel2"
  shows "set_fold_cfi (until_elem_step_cfi a1_map maskL pos tp len inz P d) ({}, a2, res) rel2 =
    (let tmp = Set.filter (\<lambda>(t, as). P t) (\<Union>(tmp_elem a1_map maskL pos tp len ` rel2) \<union> (if inz then {tp} \<times> rel2 else {})) in
     (snd ` tmp, upd_nested_max_tstp a2 d tmp, res \<union> snd ` Set.filter (\<lambda>(t, x). t = tp - len) tmp))"
  unfolding set_fold_cfi.rep_eq until_elem_step_cfi.rep_eq fold_until_elem_step[OF assms]
  unfolding fold_until_step[OF finite_until_tmp[OF assms]]
  unfolding until_tmp_def Let_def
  by (auto simp: split_beta image_iff intro!: prod_eqI)

declare [[code drop: add_new_mmuaux]]

lemma add_new_mmuaux_fused_code[code]:
  "add_new_mmuaux args rel1 rel2 nt aux =
    (let (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_map, tstp_map, done) =
    shift_mmuaux args nt aux;
    I = args_ivl args; pos = args_pos args;
    new_tstp = (if memL I 0 then Inr tp else Inl nt);
    tstp_map = Mapping.update tp nt tstp_map;
    P = (\<lambda>t. case Mapping.lookup tstp_map t of Some ts \<Rightarrow> memL I (nt - ts));
    (tbl, a2_map', result') = (if finite rel2
      then set_fold_cfi (until_elem_step_cfi a1_map maskL pos tp len (memL I 0) P new_tstp) ({}, a2_map, result) rel2
      else Code.abort (STR ''add_new_mmuaux: infinite table'') (\<lambda>_.
        let tmp = Set.filter (\<lambda>(t, as). P t) (\<Union>(tmp_elem a1_map maskL pos tp len ` rel2) \<union> (if memL I 0 then {tp} \<times> rel2 else {})) in
        (snd ` tmp, upd_nested_max_tstp a2_map new_tstp tmp, result \<union> snd ` Set.filter (\<lambda>(t, x). t = tp - len) tmp)));
    tables = append_queue (tbl, if memL I 0 then Inr tp else Inl nt) tables;
    a2_map = Mapping.update (tp + 1) Mapping.empty a2_map';
    a1_map = (if pos then Mapping.filter (\<lambda>as _. as \<in> rel1)
      (upd_set a1_map (\<lambda>_. tp) (rel1 - Mapping.keys a1_map)) else upd_set a1_map (\<lambda>_. tp) rel1);
    tss = append_queue nt tss in
    (tp + 1, tss, tables, len + 1, maskL, maskR, result', a1_map, a2_map, tstp_map, done))"
proof -
  have *: "(if finite R
      then set_fold_cfi (until_elem_step_cfi a1_map maskL pos tp len inz P d) ({}, a2, res) R
      else Code.abort msg (\<lambda>_.
        let tmp = Set.filter (\<lambda>(t, as). P t) (\<Union>(tmp_elem a1_map maskL pos tp len ` R) \<union> (if inz then {tp} \<times> R else {})) in
        (snd ` tmp, upd_nested_max_tstp a2 d tmp, res \<union> snd ` Set.filter (\<lambda>(t, x). t = tp - len) tmp))) =
    (let tmp = Set.filter (\<lambda>(t, as). P t) (\<Union>(tmp_elem a1_map maskL pos tp len ` R) \<union> (if inz then {tp} \<times> R else {})) in
     (snd ` tmp, upd_nested_max_tstp a2 d tmp, res \<union> snd ` Set.filter (\<lambda>(t, x). t = tp - len) tmp))"
    for a1_map :: "(event_data tuple, nat) mapping" and maskL pos tp len inz P d a2 res msg R
    by (auto simp: until_fused)
  show ?thesis
    unfolding *
    unfolding add_new_mmuaux_def Let_def tmp_elem_eta upd_nested_max_tstp_def
    by (simp split: prod.splits)
qed

lemma add_new_mmauaux_fold_code[code]:
  "add_new_mmauaux args rel1 rel2 nt (mmuaux, aggaux) =
    (case args_agg args of 
     None \<Rightarrow> let (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_map, tstp_map, done) = add_new_mmuaux args rel1 rel2 nt mmuaux in
  ((tp, tss, tables, len, maskL, maskR, result, a1_map, a2_map, tstp_map, done), aggaux) |
     Some aggargs \<Rightarrow>
    (let ((tp, tss, tables, len, maskL, maskR, result, a1_map, a2_map, tstp_map, done), aggaux) = shift_mmauaux args nt (mmuaux, aggaux);
    I = args_ivl args; pos = args_pos args;
    new_tstp = (if memL I 0 then Inr tp else Inl nt);
    tstp_map = Mapping.update tp nt tstp_map;
    m = case Mapping.lookup a2_map (tp - len) of Some m \<Rightarrow> m;
    tmp = tmp_set a1_map maskL pos tp len (if memL I 0 then {tp} \<times> rel2 else {}) rel2;
    tmp = Set.filter (\<lambda>(tp, as). case Mapping.lookup tstp_map tp of Some ts \<Rightarrow> memL I (nt - ts)) tmp;
    table = snd ` tmp;
    tables = append_queue (table, if memL I 0 then Inr tp else Inl nt) tables;
    a2_map' = Mapping.update (tp + 1) Mapping.empty
      (upd_nested_max_tstp a2_map new_tstp tmp);
    a1_map = (if pos then Mapping.filter (\<lambda>as _. as \<in> rel1)
      (upd_set a1_map (\<lambda>_. tp) (rel1 - Mapping.keys a1_map)) else upd_set a1_map (\<lambda>_. tp) rel1);
    to_add = to_add_set (tp - len) m tmp;
    aggaux = insert_maggaux' aggargs to_add aggaux;
    tss = append_queue nt tss in
    ((tp + 1, tss, tables, len + 1, maskL, maskR, result \<union> snd ` (Set.filter (\<lambda>(t, x). t = tp - len) tmp), a1_map, a2_map', tstp_map, done), aggaux)))"
  by (subst add_new_mmauaux_code) (simp only: tmp_set_def tmp_elem_eta)

subsection \<open>Unions of families of tables as folds\<close>

text \<open>
  @{term "\<Union>(snd ` set xs)"} and @{term "\<Union>(set xs)"} are compiled by Containers through a
  set of sets; the following code equations fold the union over the list instead. They affect
  @{const set_of_idx} (used by the indexed tables of the Since structure), @{const gc_mmsaux}
  and the @{text eval_step} functions of the Until structures.
\<close>

lemma Union_image_snd_fold: "\<Union>(snd ` set xs) = fold (\<lambda>p acc. snd p \<union> acc) xs {}"
proof -
  have "\<Union>(snd ` set xs) \<union> A = fold (\<lambda>p acc. snd p \<union> acc) xs A" for A
  proof (induction xs arbitrary: A)
    case (Cons p xs)
    show ?case
      using Cons.IH[of "snd p \<union> A"] by auto
  qed simp
  from this[of "{}"] show ?thesis by simp
qed

lemma Union_set_fold: "\<Union>(set xs) = fold (\<union>) xs {}"
proof -
  have "\<Union>(set xs) \<union> A = fold (\<union>) xs A" for A
  proof (induction xs arbitrary: A)
    case (Cons x xs)
    show ?case
      using Cons.IH[of "x \<union> A"] by auto
  qed simp
  from this[of "{}"] show ?thesis by simp
qed

declare [[code drop: set_of_idx]]

lemma set_of_idx_fold_code[code]:
  fixes t :: "('a :: ccompare, 'b set) mapping_rbt"
  shows "set_of_idx (RBT_Mapping t) =
    (case ID CCOMPARE('a) of None \<Rightarrow> Code.abort (STR ''set_of_idx RBT_Mapping: ccompare = None'') (\<lambda>_. set_of_idx (RBT_Mapping t))
    | Some _ \<Rightarrow> fold (\<lambda>p acc. snd p \<union> acc) (RBT_Mapping2.entries t) {})"
  by (subst set_of_idx_code) (simp only: Union_image_snd_fold)

declare [[code drop: gc_mmsaux eval_step_mmuaux eval_step_mmauaux]]

lemma gc_mmsaux_fold_code[code]:
  "gc_mmsaux args (nt, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) =
    (let all_tuples = fold (\<lambda>p acc. snd p \<union> acc) (linearize data_prev @ linearize data_in) {};
    tuple_since' = Mapping.filter (\<lambda>as _. as \<in> all_tuples) tuple_since in
    (nt, nt, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in,
     wf_table_upd args tuple_since' (\<lambda>_. wf_table_of_set_args args (Mapping.keys tuple_since')), tuple_since'))"
  by (subst gc_mmsaux.simps) (simp only: set_append[symmetric] Union_image_snd_fold)

lemma eval_step_mmuaux_fold_code[code]:
  "eval_step_mmuaux args (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_map, tstp_map, done) =
    (case safe_hd tss of (Some ts, tss') \<Rightarrow>
      (case Mapping.lookup a2_map (tp - len) of Some m \<Rightarrow>
        let I = args_ivl args;
        T = eval_args_agg args result;
        tss' = tl_queue tss';
        (ts', tss'') = case safe_hd tss' of 
              (Some ts', tss'') \<Rightarrow> (ts', tss'') |
              (None, tss'') \<Rightarrow> (0, tss'');
        (tables, taken) = takedropWhile_queue (\<lambda>(table, tstp). \<not> ts_tp_lt I ts' (tp - len + 1) tstp) tables;
        to_del_approx = fold (\<union>) (map fst taken) {};
        to_del = Set.filter (\<lambda>x. case Mapping.lookup m x of Some tstp \<Rightarrow> (\<not>ts_tp_lt I ts' (tp - len + 1) tstp) |
                                                            None \<Rightarrow> False) to_del_approx;
        m'' = mapping_delete_set m to_del;
        result' = if len = 1 then {} else (result - to_del) \<union> (case Mapping.lookup a2_map (tp - len + 1) of Some m' \<Rightarrow> Mapping.keys m');
        a2_map = if len = 1 then Mapping.update tp Mapping.empty a2_map
                 else Mapping.update (tp - len + 1)
          (case Mapping.lookup a2_map (tp - len + 1) of Some m' \<Rightarrow>
          Mapping.combine (\<lambda>tstp tstp'. max_tstp tstp tstp') m'' m') a2_map;
        a2_map = Mapping.delete (tp - len) a2_map;
        tstp_map = Mapping.delete (tp - len) tstp_map in
        (tp, tss'', tables, len - 1, maskL, maskR, result', a1_map, a2_map, tstp_map, T # done)))"
  by (subst eval_step_mmuaux.simps) (simp only: Union_set_fold)

lemma eval_step_mmauaux_fold_code[code]:
  "eval_step_mmauaux args ((tp, tss, tables, len, maskL, maskR, result, a1_map, a2_map, tstp_map, done), aggaux) = 
  (case safe_hd tss of 
  (Some ts, tss') \<Rightarrow>
    (case args_agg args of 
    None \<Rightarrow> (eval_step_mmuaux args (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_map, tstp_map, done), aggaux) |
    Some aggargs \<Rightarrow>
      (case Mapping.lookup a2_map (tp - len) of 
      Some m \<Rightarrow> 
        let I = args_ivl args;
        tss' = tl_queue tss';
        (ts', tss'') = case safe_hd tss' of 
              (Some ts', tss'') \<Rightarrow> (ts', tss'') |
              (None, tss'') \<Rightarrow> (0, tss'');
        (tables, taken) = takedropWhile_queue (\<lambda>(table, tstp). \<not> ts_tp_lt I ts' (tp - len + 1) tstp) tables;
        to_del_approx = fold (\<union>) (map fst taken) {};
        to_del = Set.filter (\<lambda>x. case Mapping.lookup m x of Some tstp \<Rightarrow> (\<not>ts_tp_lt I ts' (tp - len + 1) tstp) |
                                                            None \<Rightarrow> False) to_del_approx;
        m'' = mapping_delete_set m to_del;
        result' = if len = 1 then {} else (result - to_del) \<union> (case Mapping.lookup a2_map (tp - len + 1) of Some m' \<Rightarrow> Mapping.keys m');
        to_ins = case Mapping.lookup a2_map (tp - len + 1) of Some m' \<Rightarrow> m';
        a2_map = if len = 1 then Mapping.update tp Mapping.empty a2_map
                 else Mapping.update (tp - len + 1)
          (Mapping.combine (\<lambda>tstp tstp'. max_tstp tstp tstp') m'' to_ins) a2_map;
        a2_map = Mapping.delete (tp - len) a2_map;
        tstp_map = Mapping.delete (tp - len) tstp_map;
        agg_result = result_maggaux' aggargs aggaux;
        T = case agg_result of Some k \<Rightarrow> k |
                               None \<Rightarrow> eval_args_agg args (Mapping.keys m);
        to_ins = Mapping.filter (\<lambda>k v. Mapping.lookup m'' k = None) to_ins;
        aggaux = (if len = 1 then init_maggaux' aggargs else insert_maggaux' aggargs (Mapping.keys to_ins) (delete_maggaux' aggargs to_del aggaux)) in
        ((tp, tss'', tables, len - 1, maskL, maskR, result', a1_map, a2_map, tstp_map, T # done), aggaux))))"
  by (subst eval_step_mmauaux.simps) (simp only: Union_set_fold)

text \<open>
  The deque-based Until structure of @{theory MFODL_Monitor_Devel.Optimized_Until_Deque} gets the
  same treatment for its @{const eval_step_dq}. Its @{const add_new_dq} is a fold already.
\<close>

declare [[code drop: eval_step_dq]]

lemma eval_step_dq_fold_code[code]:
  "eval_step_dq args (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_dq, tstp_dq, done) =
    (case safe_hd tss of (Some ts, tss') \<Rightarrow>
      (let m = dq_nth a2_dq 0;
        I = args_ivl args;
        T = eval_args_agg args result;
        tss' = tl_queue tss';
        (ts', tss'') = case safe_hd tss' of
              (Some ts', tss'') \<Rightarrow> (ts', tss'') |
              (None, tss'') \<Rightarrow> (0, tss'');
        (tables, taken) = takedropWhile_queue (\<lambda>(table, tstp). \<not> ts_tp_lt I ts' (tp - len + 1) tstp) tables;
        to_del_approx = fold (\<union>) (map fst taken) {};
        to_del = Set.filter (\<lambda>x. case Mapping.lookup m x of Some tstp \<Rightarrow> (\<not>ts_tp_lt I ts' (tp - len + 1) tstp) |
                                                            None \<Rightarrow> False) to_del_approx;
        m'' = mapping_delete_set m to_del;
        a2_dq' = dq_tl a2_dq;
        m' = dq_nth a2_dq' 0;
        result' = if len = 1 then {} else (result - to_del) \<union> Mapping.keys m';
        a2_dq = dq_upd a2_dq' 0 (if len = 1 then Mapping.empty
          else Mapping.combine (\<lambda>tstp tstp'. max_tstp tstp tstp') m'' m');
        tstp_dq = dq_tl tstp_dq in
        (tp, tss'', tables, len - 1, maskL, maskR, result', a1_map, a2_dq, tstp_dq, T # done)))"
  by (subst eval_step_dq.simps) (simp only: Union_set_fold)


section \<open>Since without join columns\<close>

text \<open>
  The Since structure keeps two @{typ "'a wf_table"}s indexed by the join columns
  @{term "args_L args"}. They are consulted by @{const join_mmsaux} only when there are join
  columns that do not cover all columns; without them (@{term "args_L args = {}"}, e.g. for
  @{text ONCE}) or when all columns are join columns (@{term "args_L args = args_R args"}) the
  operations of @{text Optimized_Since} maintain them as @{term "wf_table_of_keys n R m"}, the
  set of keys of the corresponding mapping. Both @{const wf_table_of_set} and @{const wf_table_of_keys} are made
  representations of @{typ "'a wf_table"} for the code generator: constructing them costs
  nothing, the (never taken) reads filter lazily, and the binary operations convert them to the
  plain set representation first. Constructing an index for the empty or the full join column
  set is also replaced by the plain representation.
\<close>

lemma wf_table_of_idx_of_set: "wf_table_of_idx (wf_idx_of_set n A I X) = wf_table_of_set n A X"
  by (rule wf_table_eqI) (simp_all add: wf_idx_sig_of_set wf_idx_set_of_set wf_table_sig_of_set wf_table_set_of_set)

declare [[code drop: wf_table_of_set_args]]

lemma wf_table_of_set_args_code[code]:
  "wf_table_of_set_args args X = (if args_L args = {} \<or> args_L args = args_R args
     then wf_table_of_set (args_n args) (args_R args) X
     else wf_table_of_idx (wf_idx_of_set (args_n args) (args_R args) (args_L args) X))"
  by (simp add: wf_table_of_set_args_def wf_table_of_idx_of_set)

declare [[code drop: init_mmsaux]]

lemma init_mmsaux_code[code]:
  "init_mmsaux args = (0, 0, join_mask (args_n args) (args_L args),
    join_mask (args_n args) (args_R args), empty_queue, empty_queue,
    {}, wf_table_of_set_args args {}, Mapping.empty, wf_table_of_set_args args {}, Mapping.empty)"
  by (simp add: wf_table_of_set_args_def)

declare [[code drop: wf_table_of_set wf_table_of_keys]]

code_datatype wf_table_of_wf_set wf_table_of_idx wf_table_of_set wf_table_of_keys

text \<open>Re-declaring the representations drops the existing code equations that match on them.\<close>

declare wf_table_sig_code[code] wf_table_set_code[code] wf_table_union_code[code]
  wf_table_join_code[code] wf_table_antijoin_code[code] wf_table_permute_code[code] wf_table_idx_code[code]

lemma wf_table_conv:
  "wf_table_of_set n A X = wf_table_of_wf_set (wf_set_of_set n A X)"
  "wf_table_of_keys n A m = wf_table_of_wf_set (wf_set_of_set n A (Mapping.keys m))"
  by (simp_all add: wf_table_of_set_code wf_table_of_keys_def)

lemma wf_table_sig_code'[code]:
  "wf_table_sig (wf_table_of_set n A X) = (n, A)"
  "wf_table_sig (wf_table_of_keys n A m) = (n, A)"
  by (simp_all add: wf_table_sig_of_set)

lemma wf_table_set_code'[code]:
  "wf_table_set (wf_table_of_set n A X) = Set.filter (wf_tuple n A) X"
  "wf_table_set (wf_table_of_keys n A m) = Set.filter (wf_tuple n A) (Mapping.keys m)"
  by (simp_all add: wf_table_set_of_set wf_table_of_keys_def)

lemma wf_table_union_code'[code]:
  "wf_table_union (wf_table_of_set n A X) t = wf_table_union (wf_table_of_wf_set (wf_set_of_set n A X)) t"
  "wf_table_union (wf_table_of_keys n A m) t = wf_table_union (wf_table_of_wf_set (wf_set_of_set n A (Mapping.keys m))) t"
  "wf_table_union t (wf_table_of_set n A X) = wf_table_union t (wf_table_of_wf_set (wf_set_of_set n A X))"
  "wf_table_union t (wf_table_of_keys n A m) = wf_table_union t (wf_table_of_wf_set (wf_set_of_set n A (Mapping.keys m)))"
  by (simp_all only: wf_table_conv)

lemma wf_table_join_code'[code]:
  "wf_table_join (wf_table_of_set n A X) t = wf_table_join (wf_table_of_wf_set (wf_set_of_set n A X)) t"
  "wf_table_join (wf_table_of_keys n A m) t = wf_table_join (wf_table_of_wf_set (wf_set_of_set n A (Mapping.keys m))) t"
  "wf_table_join t (wf_table_of_set n A X) = wf_table_join t (wf_table_of_wf_set (wf_set_of_set n A X))"
  "wf_table_join t (wf_table_of_keys n A m) = wf_table_join t (wf_table_of_wf_set (wf_set_of_set n A (Mapping.keys m)))"
  by (simp_all only: wf_table_conv)

lemma wf_table_antijoin_code'[code]:
  "wf_table_antijoin (wf_table_of_set n A X) t = wf_table_antijoin (wf_table_of_wf_set (wf_set_of_set n A X)) t"
  "wf_table_antijoin (wf_table_of_keys n A m) t = wf_table_antijoin (wf_table_of_wf_set (wf_set_of_set n A (Mapping.keys m))) t"
  "wf_table_antijoin t (wf_table_of_set n A X) = wf_table_antijoin t (wf_table_of_wf_set (wf_set_of_set n A X))"
  "wf_table_antijoin t (wf_table_of_keys n A m) = wf_table_antijoin t (wf_table_of_wf_set (wf_set_of_set n A (Mapping.keys m)))"
  by (simp_all only: wf_table_conv)

lemma wf_table_idx_code'[code]:
  "wf_table_idx I (wf_table_of_set n A X) = wf_table_idx I (wf_table_of_wf_set (wf_set_of_set n A X))"
  "wf_table_idx I (wf_table_of_keys n A m) = wf_table_idx I (wf_table_of_wf_set (wf_set_of_set n A (Mapping.keys m)))"
  by (simp_all only: wf_table_conv)

lemma wf_table_permute_code'[code]:
  "wf_table_permute ns (wf_table_of_set n A X) = wf_table_permute ns (wf_table_of_wf_set (wf_set_of_set n A X))"
  "wf_table_permute ns (wf_table_of_keys n A m) = wf_table_permute ns (wf_table_of_wf_set (wf_set_of_set n A (Mapping.keys m)))"
  by (simp_all only: wf_table_conv)


section \<open>Aggregations by clustering\<close>

text \<open>
  The default code for @{const eval_agg} filters the whole table once per group and each group
  once per distinct value of the aggregated term (quadratic). The following code equation
  clusters the table by the group key and each group by the term value with @{const cluster}
  (one red-black-tree insertion per tuple).
\<close>

derive (no) cenum event_data

lemma keys_cluster: "Mapping.keys (cluster (Some \<circ> g) X) = g ` X"
  by (auto simp: Mapping.keys_dom_lookup lookup_cluster image_iff split: if_splits)

lemma lookup_cluster_Some: "k \<in> g ` X \<Longrightarrow> Mapping.lookup (cluster (Some \<circ> g) X) k = Some (Set.filter (\<lambda>x. g x = k) X)"
  by (auto simp: lookup_cluster image_iff)

definition agg_values :: "Formula.trm \<Rightarrow> event_data table \<Rightarrow> (event_data \<times> enat) set" where
  "agg_values f G = (let vals = cluster (Some \<circ> meval_trm f) G in
     (\<lambda>v. case Mapping.lookup vals v of Some S \<Rightarrow> (v, ecard S)) ` Mapping.keys vals)"

lemma agg_values: "agg_values f G = (\<lambda>v. (v, ecard (Set.filter (\<lambda>x. meval_trm f x = v) G))) ` meval_trm f ` G"
  unfolding agg_values_def Let_def keys_cluster
  by (intro image_cong refl) (simp add: lookup_cluster_Some)

declare [[code drop: eval_agg]]

lemma eval_agg_code[code]:
  "eval_agg n g0 y \<omega> tys f rel = (if g0 \<and> rel = empty_table then singleton_table n y (eval_agg_op \<omega> {})
    else (let groups = cluster (Some \<circ> drop (length tys)) rel in
      (\<lambda>k. case Mapping.lookup groups k of Some G \<Rightarrow> list_update k y (Some (eval_agg_op \<omega> (agg_values f G))))
        ` Mapping.keys groups))"
  unfolding eval_agg_def Let_def keys_cluster
  by (intro if_cong refl image_cong) (simp add: lookup_cluster_Some agg_values)


subsection \<open>Unions of option-valued images without sets of sets\<close>

text \<open>
  @{term "\<Union>v \<in> X. set_option (f v)"} (used by the @{text Match} mode of predicate evaluation)
  is compiled by Containers through a set of sets, whose comparator compares whole tables.
  The rewrite below turns it into an image followed by @{const Option.these}.
\<close>

lemma Union_set_option_these[code_unfold]: "(\<Union>v \<in> X. set_option (f v)) = Option.these (f ` X)"
proof (intro set_eqI iffI)
  fix x
  assume "x \<in> (\<Union>v \<in> X. set_option (f v))"
  then obtain v where "v \<in> X" "f v = Some x" by auto
  then show "x \<in> Option.these (f ` X)" by (auto simp: in_these_eq intro: rev_image_eqI)
next
  fix x
  assume "x \<in> Option.these (f ` X)"
  then show "x \<in> (\<Union>v \<in> X. set_option (f v))" by (auto simp: in_these_eq)
qed


subsection \<open>Moving tables into the window in one pass\<close>

text \<open>
  @{const add_new_ts_mmsaux'} moves the tables whose time stamp has entered the window from
  @{text data_prev} to @{text data_in}, updates @{text tuple_in} with the tuples that are valid
  at their time point, and collects those tuples to add them to the result table. The equation
  of @{const upd_set_keys} names the set of valid tuples of a table twice, so the generated
  code computes it twice, builds it as a table, and then traverses it again for the mapping and
  once more for the result. Folding over the table once and updating the mapping and the result
  in the step avoids the intermediate table and the extra traversals. When the operator has no
  join columns or all columns are join columns, the collected tuples are only used for the
  result table (@{const wf_table_upd} then ignores the index), so the fold can start from the
  result table itself and the union at the end disappears as well.
\<close>

definition move_insert :: "('a tuple, ts) mapping \<Rightarrow> ts \<Rightarrow> 'a tuple \<Rightarrow>
  (('a tuple, ts) mapping \<times> 'a table) \<Rightarrow> (('a tuple, ts) mapping \<times> 'a table)" where
  "move_insert tuple_since t as = (\<lambda>(m, Y). if valid_tuple tuple_since (t, as)
     then (Mapping.update as t m, Set.insert as Y) else (m, Y))"

lemma Mapping_update_same_commute:
  "Mapping.update a t (Mapping.update b t m) = Mapping.update b t (Mapping.update a t m)"
  by (rule mapping_eqI) (auto simp: Mapping.lookup_update')

lemma Mapping_update_idem: "Mapping.update a t (Mapping.update a t m) = Mapping.update a t m"
  by (rule mapping_eqI) (auto simp: Mapping.lookup_update')

lemma comp_fun_idem_move_insert: "comp_fun_idem (move_insert tuple_since t)"
  by unfold_locales
    (auto simp: fun_eq_iff move_insert_def Set.insert_commute Mapping_update_same_commute Mapping_update_idem
      split: prod.splits)

lemma upd_set_const_insert:
  "Mapping.update x t (upd_set m (\<lambda>_. t) S) = upd_set m (\<lambda>_. t) (Set.insert x S)"
  by (rule mapping_eqI) (auto simp: Mapping_lookup_upd_set Mapping.lookup_update')

lemma fold_move_insert:
  assumes "finite X"
  shows "Finite_Set.fold (move_insert tuple_since t) (m, Y) X =
    (upd_set m (\<lambda>_. t) {as \<in> X. valid_tuple tuple_since (t, as)},
     Y \<union> {as \<in> X. valid_tuple tuple_since (t, as)})"
proof -
  interpret comp_fun_idem "move_insert tuple_since t"
    by (rule comp_fun_idem_move_insert)
  from assms show ?thesis
  proof (induction X arbitrary: m Y rule: finite_induct)
    case empty
    show ?case by auto
  next
    case (insert x F)
    have step: "Finite_Set.fold (move_insert tuple_since t) (m, Y) (Set.insert x F) =
      move_insert tuple_since t x (upd_set m (\<lambda>_. t) {as \<in> F. valid_tuple tuple_since (t, as)},
        Y \<union> {as \<in> F. valid_tuple tuple_since (t, as)})"
      unfolding fold_insert[OF insert.hyps(1,2)] insert.IH ..
    show ?case
    proof (cases "valid_tuple tuple_since (t, x)")
      case True
      then have S: "{as \<in> Set.insert x F. valid_tuple tuple_since (t, as)} =
        Set.insert x {as \<in> F. valid_tuple tuple_since (t, as)}" by auto
      show ?thesis unfolding step S
        by (simp only: move_insert_def prod.case if_P[OF True] upd_set_const_insert Un_insert_right)
    next
      case False
      then have S: "{as \<in> Set.insert x F. valid_tuple tuple_since (t, as)} =
        {as \<in> F. valid_tuple tuple_since (t, as)}" by auto
      show ?thesis unfolding step S
        by (simp only: move_insert_def prod.case if_not_P[OF False])
    qed
  qed
qed

lift_definition move_insert_cfi :: "('a tuple, ts) mapping \<Rightarrow> ts \<Rightarrow>
  ('a tuple, ('a tuple, ts) mapping \<times> 'a table) comp_fun_idem" is move_insert
  by (rule comp_fun_idem_move_insert)

definition move_tbl :: "('a tuple, ts) mapping \<Rightarrow> ts \<times> 'a table \<Rightarrow>
  (('a tuple, ts) mapping \<times> 'a table) \<Rightarrow> (('a tuple, ts) mapping \<times> 'a table)" where
  "move_tbl tuple_since = (\<lambda>(t, X) acc. if finite X
     then set_fold_cfi (move_insert_cfi tuple_since t) acc X
     else upd_set_keys (\<lambda>X t. {as \<in> X. valid_tuple tuple_since (t, as)}) (t, X) acc)"

lemma move_tbl_eq:
  "move_tbl tuple_since = upd_set_keys (\<lambda>X t. {as \<in> X. valid_tuple tuple_since (t, as)})"
proof (intro ext, goal_cases)
  case (1 tX acc)
  obtain t X where tX: "tX = (t, X)" by (cases tX)
  obtain m Y where acc: "acc = (m, Y)" by (cases acc)
  show ?case
    unfolding tX acc move_tbl_def prod.case
    by (cases "finite X")
      (simp_all add: set_fold_cfi.rep_eq move_insert_cfi.rep_eq fold_move_insert upd_set_keys.simps)
qed

lemma fold_upd_set_keys_un:
  "fold (upd_set_keys Z) xs (m, Y1 \<union> Y2) =
    (fst (fold (upd_set_keys Z) xs (m, Y1)), snd (fold (upd_set_keys Z) xs (m, Y1)) \<union> Y2)"
proof (induction xs arbitrary: m Y1 Y2)
  case (Cons x xs)
  obtain t X where x: "x = (t, X)" by (cases x)
  have "(Y1 \<union> Y2) \<union> Z X t = (Y1 \<union> Z X t) \<union> Y2" by auto
  then show ?case
    unfolding x by (simp add: upd_set_keys.simps Cons.IH)
qed simp

declare [[code drop: add_new_ts_mmsaux']]

lemma add_new_ts_mmsaux'_code[code]:
  "add_new_ts_mmsaux' args nt (t, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in,
     tuple_in, wf_table_since, tuple_since) =
    (let I = args_ivl args;
     (data_prev', move) = takedropWhile_queue (\<lambda>(t, X). memL I (nt - t)) data_prev;
     data_in' = fold (\<lambda>(t, X) data_in. append_queue (t, X) data_in) move data_in in
     if args_L args = {} \<or> args_L args = args_R args
     then (let (tuple_in', table_in') = fold (move_tbl tuple_since) move (tuple_in, table_in)
           in (nt, gc, maskL, maskR, data_prev', data_in', table_in',
               wf_table_of_keys (args_n args) (args_R args) tuple_in', tuple_in',
               wf_table_since, tuple_since))
     else (let (tuple_in', add) = fold (move_tbl tuple_since) move (tuple_in, {})
           in (nt, gc, maskL, maskR, data_prev', data_in', table_in \<union> add,
               wf_table_union wf_table_in (wf_table_of_set_args args add), tuple_in',
               wf_table_since, tuple_since)))"
proof -
  let ?Z = "\<lambda>X t. {as \<in> X. valid_tuple tuple_since (t, as)}"
  have key: "fold (upd_set_keys ?Z) mv (tuple_in, table_in) =
    (fst (fold (upd_set_keys ?Z) mv (tuple_in, {})),
     table_in \<union> snd (fold (upd_set_keys ?Z) mv (tuple_in, {})))" for mv
    using fold_upd_set_keys_un[of ?Z mv tuple_in "{}" table_in] by (simp add: Un_commute)
  show ?thesis
    unfolding add_new_ts_mmsaux'.simps move_tbl_eq wf_table_upd_def Let_def
    by (simp add: key split_beta)
qed

subsection \<open>Adding a table to the window without updating the mapping twice\<close>

text \<open>
  When the interval starts at 0, @{const add_new_table_mmsaux} puts the new table straight into
  the window. Its equation names @{term "upd_set tuple_in (\<lambda>_. t) X"} twice, once for the
  mapping component and once for the index, so the generated code inserts every tuple of the
  table into the mapping twice. Naming the updated mapping once removes the second pass.
\<close>

declare [[code drop: add_new_table_mmsaux]]

lemma add_new_table_mmsaux_code[code]:
  "add_new_table_mmsaux args X (t, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in,
     tuple_in, wf_table_since, tuple_since) =
    (let X' = minus_keys X tuple_since;
         tuple_since' = upd_set tuple_since (\<lambda>_. t) X';
         wf_table_since' = wf_table_upd args tuple_since'
           (\<lambda>_. wf_table_union wf_table_since (wf_table_of_set_args args X')) in
     if memL (args_ivl args) 0
     then (let tuple_in' = upd_set tuple_in (\<lambda>_. t) X in
           (t, gc, maskL, maskR, data_prev, append_queue (t, X) data_in, table_in \<union> X,
            wf_table_upd args tuple_in'
              (\<lambda>_. wf_table_union wf_table_in (wf_table_of_set_args args X)),
            tuple_in', wf_table_since', tuple_since'))
     else (t, gc, maskL, maskR, append_queue (t, X) data_prev, data_in, table_in, wf_table_in,
           tuple_in, wf_table_since', tuple_since'))"
  by (simp add: Let_def)

(*<*)
end
(*>*)
