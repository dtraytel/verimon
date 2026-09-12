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

subsection \<open>Joins\<close>

text \<open>
  The default code for the general case of @{const bin_join} is a nested loop over both tables
  (quadratic in the table sizes). We replace it, via a proven code equation, by an index-based
  join: both tables are clustered by their common columns and only matching buckets are joined.
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
  by (cases "finite B") (auto simp: fold_join1_insert fold_infinite)

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

lemma lookup_mapping_join: "Mapping.lookup (mapping_join f m m') x =
  (case Mapping.lookup m x of None \<Rightarrow> None
   | Some y \<Rightarrow> (case Mapping.lookup m' x of None \<Rightarrow> None | Some y' \<Rightarrow> Some (f y y')))"
  by (transfer fixing: f x) simp

lemma set_of_idx_iff: "z \<in> set_of_idx m \<longleftrightarrow> (\<exists>k Y. Mapping.lookup m k = Some Y \<and> z \<in> Y)"
  by transfer (auto simp: ran_def)

definition idx_join_gen :: "nat set \<Rightarrow> 'a table \<Rightarrow> 'a table \<Rightarrow> 'a table" where
  "idx_join_gen I t t' = set_of_idx (mapping_join (\<lambda>T T'. join T True T')
     (cluster (Some \<circ> restrict I) t) (cluster (Some \<circ> restrict I) t'))"

lemma idx_join_gen_join:
  assumes "\<forall>x \<in> t. complete_on I x" "\<forall>y \<in> t'. complete_on I y"
  shows "idx_join_gen I t t' = join t True t'"
proof (rule set_eqI)
  fix z
  have "z \<in> idx_join_gen I t t' \<longleftrightarrow> (\<exists>k. Some k \<in> (Some \<circ> restrict I) ` t \<and> Some k \<in> (Some \<circ> restrict I) ` t' \<and>
    z \<in> join {y \<in> t. restrict I y = k} True {y \<in> t'. restrict I y = k})"
    unfolding idx_join_gen_def set_of_idx_iff lookup_mapping_join lookup_cluster
    by (auto split: if_splits option.splits)
  also have "\<dots> \<longleftrightarrow> z \<in> join t True t'"
  proof
    assume "\<exists>k. Some k \<in> (Some \<circ> restrict I) ` t \<and> Some k \<in> (Some \<circ> restrict I) ` t' \<and>
      z \<in> join {y \<in> t. restrict I y = k} True {y \<in> t'. restrict I y = k}"
    then show "z \<in> join t True t'"
      unfolding join_True_code by auto
  next
    assume "z \<in> join t True t'"
    then obtain a b where ab: "a \<in> t" "b \<in> t'" "join1 (a, b) = Some z"
      unfolding join_True_code by auto
    then have eq: "restrict I a = restrict I b"
      using assms join1_Some_restrict_complete by blast
    show "\<exists>k. Some k \<in> (Some \<circ> restrict I) ` t \<and> Some k \<in> (Some \<circ> restrict I) ` t' \<and>
      z \<in> join {y \<in> t. restrict I y = k} True {y \<in> t'. restrict I y = k}"
    proof (intro exI[of _ "restrict I a"] conjI)
      show "Some (restrict I a) \<in> (Some \<circ> restrict I) ` t"
        using ab(1) by force
      show "Some (restrict I a) \<in> (Some \<circ> restrict I) ` t'"
        using ab(2) eq by force
      show "z \<in> join {y \<in> t. restrict I y = restrict I a} True {y \<in> t'. restrict I y = restrict I a}"
        unfolding join_True_code
        apply (rule UN_I[of a])
        subgoal using ab(1) by simp
        apply (rule UN_I[of b])
        subgoal using ab(2) eq by simp
        subgoal using ab(3) by simp
        done
    qed
  qed
  finally show "z \<in> idx_join_gen I t t' \<longleftrightarrow> z \<in> join t True t'" .
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
    else if pos \<and> (\<forall>x \<in> t. complete_on (A \<inter> A') x) \<and> (\<forall>y \<in> t'. complete_on (A \<inter> A') y)
      then idx_join_gen (A \<inter> A') t t'
    else join t pos t')"
  by (subst bin_join.simps) (auto simp: idx_join_gen_join)

(*<*)
end
(*>*)
