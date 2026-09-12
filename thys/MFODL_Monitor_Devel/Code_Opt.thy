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
  val imperative_join : bool ref
end = struct
  let generic_join = ref false
  let imperative_join = ref false
end\<close>
| constant use_generic_join \<rightharpoonup> (OCaml) "'!Config.generic'_join"

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

lemma add_new_mmuaux_fold_code[code]: 
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
     wf_table_of_set_args args (Mapping.keys tuple_since'), tuple_since'))"
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

(*<*)
end
(*>*)
