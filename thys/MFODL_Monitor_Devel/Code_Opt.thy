(*<*)
theory Code_Opt
  imports Monitor_Impl
begin
(*>*)

section \<open>Efficient code equations\<close>

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
end = struct
  let generic_join = ref false
end\<close>
| constant use_generic_join \<rightharpoonup> (OCaml) "!Config.generic'_join"

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

declare [[code drop: bin_join]]

lemma bin_join_code[code]:
  "bin_join n A t pos A' t' =
    (if t = {} then {}
    else if t' = {} then (if pos then {} else t)
    else if A' = {} then (if (pos \<longleftrightarrow> replicate n None \<in> t') then t else {})
    else if A' = A then (if pos then t \<inter> t' else t - t')
    else if A' \<subseteq> A then {as \<in> t. proj_tuple_in_join pos (join_mask n A') as t'}
    else if A \<subseteq> A' \<and> pos then {as \<in> t'. proj_tuple_in_join pos (join_mask n A) as t}
    else if pos \<and> finite t \<and> finite t' \<and>
        (\<forall>x \<in> t. complete_on (A \<inter> A') x) \<and> (\<forall>y \<in> t'. complete_on (A \<inter> A') y)
      then (if card t \<le> card t' then probe_join (A \<inter> A') t t' else probe_join (A \<inter> A') t' t)
    else join t pos t')"
  by (subst bin_join.simps) (auto simp: probe_join_join join_commute)

(*<*)
end
(*>*)
