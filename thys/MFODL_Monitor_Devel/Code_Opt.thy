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
  Similarly, the worst-case optimal multi-way join used for @{const mmulti_join} has high
  constant factors; whenever the inputs are proper tables we evaluate the multi-way join as a
  sequence of binary (anti)joins instead. Both code equations are unconditional theorems, so
  the correctness proofs of the monitor are unaffected.
\<close>

subsection \<open>Nested-loop join as a fold\<close>

text \<open>
  The default code equation @{thm join_True_code} builds a set of singleton sets (which
  requires the expensive comparator on sets) and then takes its union. We replace it by a
  double fold that inserts the joined tuples directly into the result.
\<close>

definition join1_insert :: "'a tuple \<Rightarrow> 'a tuple \<Rightarrow> 'a table \<Rightarrow> 'a table" where
  "join1_insert a b acc = (case join1 (a, b) of None \<Rightarrow> acc | Some z \<Rightarrow> insert z acc)"

lemma comp_fun_idem_join1_insert: "comp_fun_idem (join1_insert a)"
  by unfold_locales (auto simp: fun_eq_iff join1_insert_def insert_commute split: option.splits)

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
  unfolding join_row_def
  by (transfer fixing: B a acc) (auto simp: fold_join1_insert fold_infinite)

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
    by (induction A) (auto simp: join_row_alt assms(2))
qed

declare [[code drop: join]]

lemma join_True_fold_code[code]:
  "join A True B = (if finite A \<and> finite B then set_fold_cfi (join_row_cfi B) {} A
     else Code.abort (STR ''join: infinite table'') (\<lambda>_. join A True B))"
proof (cases "finite A \<and> finite B")
  case True
  have "set_fold_cfi (join_row_cfi B) {} A = Finite_Set.fold (join_row B) {} A"
    by (transfer fixing: A B) simp
  then show ?thesis
    using True by (simp add: fold_join_row)
qed simp

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

subsection \<open>Multi-way join as a sequence of binary joins\<close>

fun mmulti_join_pos :: "nat \<Rightarrow> nat set \<Rightarrow> 'a table \<Rightarrow> (nat set \<times> 'a table) list \<Rightarrow> nat set \<times> 'a table" where
  "mmulti_join_pos n A t [] = (A, t)"
| "mmulti_join_pos n A t ((A', t') # L) = mmulti_join_pos n (A \<union> A') (bin_join n A t True A' t') L"

fun mmulti_join_neg :: "nat \<Rightarrow> nat set \<Rightarrow> 'a table \<Rightarrow> (nat set \<times> 'a table) list \<Rightarrow> 'a table" where
  "mmulti_join_neg n A t [] = t"
| "mmulti_join_neg n A t ((A', t') # L) = mmulti_join_neg n A (bin_join n A t False A' t') L"

definition mmulti_join_pw :: "nat \<Rightarrow> nat set list \<Rightarrow> nat set list \<Rightarrow> 'a table list \<Rightarrow> 'a table" where
  "mmulti_join_pw n A_pos A_neg L = (case zip A_pos L of [] \<Rightarrow> {}
    | (A, t) # Lpos \<Rightarrow> (case mmulti_join_pos n A t Lpos of (A', t') \<Rightarrow>
        mmulti_join_neg n A' t' (zip A_neg (drop (length A_pos) L))))"

lemma join_restrict_tables:
  assumes "table n A X" "table n B Y" "\<not> b \<Longrightarrow> B \<subseteq> A"
  shows "v \<in> join X b Y \<longleftrightarrow> wf_tuple n (A \<union> B) v \<and> restrict A v \<in> X \<and>
    (if b then restrict B v \<in> Y else restrict B v \<notin> Y)"
  apply (rule join_restrict)
  using assms by (auto simp: table_def)

lemma mmulti_join_pos_fst: "fst (mmulti_join_pos n A t L) = A \<union> \<Union>(fst ` set L)"
proof (induction L arbitrary: A t)
  case (Cons At L)
  then show ?case
    by (cases At) (auto simp: Un_assoc)
qed simp

lemma mmulti_join_pos_correct:
  assumes "table n A t" "\<forall>(A', X) \<in> set L. table n A' X"
  shows "table n (A \<union> \<Union>(fst ` set L)) (snd (mmulti_join_pos n A t L)) \<and>
    (\<forall>z. z \<in> snd (mmulti_join_pos n A t L) \<longleftrightarrow> wf_tuple n (A \<union> \<Union>(fst ` set L)) z \<and>
       restrict A z \<in> t \<and> (\<forall>(A', X) \<in> set L. restrict A' z \<in> X))"
  using assms
proof (induction L arbitrary: A t)
  case Nil
  then show ?case
    by (auto simp: table_def restrict_idle)
next
  case (Cons At L)
  obtain A' t' where At: "At = (A', t')"
    by (cases At)
  have tab': "table n A' t'"
    using Cons.prems(2) by (auto simp: At)
  have join: "bin_join n A t True A' t' = join t True t'"
    by (rule bin_join_table[OF Cons.prems(1) tab'])
  have tab_join: "table n (A \<union> A') (join t True t')"
    by (rule join_table[OF Cons.prems(1) tab']) auto
  have IH: "table n (A \<union> A' \<union> \<Union>(fst ` set L)) (snd (mmulti_join_pos n (A \<union> A') (join t True t') L)) \<and>
    (\<forall>z. z \<in> snd (mmulti_join_pos n (A \<union> A') (join t True t') L) \<longleftrightarrow>
      wf_tuple n (A \<union> A' \<union> \<Union>(fst ` set L)) z \<and>
      restrict (A \<union> A') z \<in> join t True t' \<and> (\<forall>(A', X) \<in> set L. restrict A' z \<in> X))"
    by (rule Cons.IH[OF tab_join]) (use Cons.prems(2) in \<open>auto simp: At\<close>)
  have *: "restrict (A \<union> A') z \<in> join t True t' \<longleftrightarrow> restrict A z \<in> t \<and> restrict A' z \<in> t'"
    if "wf_tuple n (A \<union> A' \<union> \<Union>(fst ` set L)) z" for z
  proof -
    have wf: "wf_tuple n (A \<union> A') (restrict (A \<union> A') z)"
      by (rule wf_tuple_restrict_simple[OF that]) auto
    show ?thesis
      using join_restrict_tables[OF Cons.prems(1) tab', of True "restrict (A \<union> A') z"] wf
      by (auto simp: restrict_restrict Int_absorb2[OF sup_ge1] Int_absorb2[OF sup_ge2])
  qed
  have eq: "mmulti_join_pos n A t (At # L) = mmulti_join_pos n (A \<union> A') (join t True t') L"
    by (simp only: At mmulti_join_pos.simps join)
  have cols: "A \<union> \<Union>(fst ` set (At # L)) = A \<union> A' \<union> \<Union>(fst ` set L)"
    by (simp add: At Un_assoc)
  show ?case
    unfolding eq cols
  proof (intro conjI allI)
    show "table n (A \<union> A' \<union> \<Union>(fst ` set L)) (snd (mmulti_join_pos n (A \<union> A') (join t True t') L))"
      using IH by blast
    fix z
    show "z \<in> snd (mmulti_join_pos n (A \<union> A') (join t True t') L) \<longleftrightarrow>
      wf_tuple n (A \<union> A' \<union> \<Union>(fst ` set L)) z \<and> restrict A z \<in> t \<and> (\<forall>(A', X) \<in> set (At # L). restrict A' z \<in> X)"
      using conjunct2[OF IH, rule_format, of z] *[of z] by (auto simp: At)
  qed
qed

lemma mmulti_join_neg_correct:
  assumes "table n A t" "\<forall>(A', X) \<in> set L. table n A' X \<and> A' \<subseteq> A"
  shows "z \<in> mmulti_join_neg n A t L \<longleftrightarrow> z \<in> t \<and> (\<forall>(A', X) \<in> set L. restrict A' z \<notin> X)"
  using assms
proof (induction L arbitrary: t)
  case Nil
  then show ?case
    by simp
next
  case (Cons At L)
  obtain A' t' where At: "At = (A', t')"
    by (cases At)
  have tab': "table n A' t'" and sub: "A' \<subseteq> A"
    using Cons.prems(2) by (auto simp: At)
  have join: "bin_join n A t False A' t' = join t False t'"
    by (rule bin_join_table[OF Cons.prems(1) tab'])
  have tab_join: "table n A (join t False t')"
    by (rule join_table[OF Cons.prems(1) tab']) (use sub in auto)
  have *: "z \<in> join t False t' \<longleftrightarrow> z \<in> t \<and> restrict A' z \<notin> t'" for z
    using join_restrict_tables[OF Cons.prems(1) tab', of False z] sub Cons.prems(1)
    by (auto simp: Un_absorb2 restrict_idle table_def)
  have IH: "z \<in> mmulti_join_neg n A (join t False t') L \<longleftrightarrow>
    z \<in> join t False t' \<and> (\<forall>(A', X) \<in> set L. restrict A' z \<notin> X)"
    by (rule Cons.IH[OF tab_join]) (use Cons.prems(2) in \<open>auto simp: At\<close>)
  have eq: "mmulti_join_neg n A t (At # L) = mmulti_join_neg n A (join t False t') L"
    by (simp only: At mmulti_join_neg.simps join)
  show ?case
    unfolding eq IH * by (auto simp: At)
qed

lemma mmulti_join_pw_correct:
  assumes "A_pos \<noteq> []" "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A) (A_pos @ A_neg) L"
    "\<forall>A \<in> set A_neg. A \<subseteq> \<Union>(set A_pos)"
  shows "z \<in> mmulti_join_pw n A_pos A_neg L \<longleftrightarrow> wf_tuple n (\<Union>A\<in>set A_pos. A) z \<and>
    list_all2 (\<lambda>A X. restrict A z \<in> X) A_pos (take (length A_pos) L) \<and>
    list_all2 (\<lambda>A X. restrict A z \<notin> X) A_neg (drop (length A_pos) L)"
proof -
  define L_pos where "L_pos = take (length A_pos) L"
  define L_neg where "L_neg = drop (length A_pos) L"
  have len: "length L = length A_pos + length A_neg"
    using list_all2_lengthD[OF assms(2)] by simp
  have len_pos: "length L_pos = length A_pos" and len_neg: "length L_neg = length A_neg"
    by (auto simp: L_pos_def L_neg_def len)
  have L: "L = L_pos @ L_neg"
    by (simp add: L_pos_def L_neg_def)
  have "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A) A_pos L_pos"
    "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A) A_neg L_neg"
    using assms(2) unfolding L list_all2_append[OF len_pos[symmetric]] by auto
  then have tabs: "\<forall>(A, X) \<in> set (zip A_pos L_pos). table n A X" "\<forall>(A, X) \<in> set (zip A_neg L_neg). table n A X"
    unfolding list_all2_iff by auto
  obtain A1 A_pos' where A_pos: "A_pos = A1 # A_pos'"
    using assms(1) by (cases A_pos) auto
  obtain t1 L_pos' where L_pos: "L_pos = t1 # L_pos'"
    using len_pos by (cases L_pos) (auto simp: A_pos)
  have len_pos': "length L_pos' = length A_pos'"
    using len_pos by (simp add: A_pos L_pos)
  have zip_pos: "zip A_pos L = (A1, t1) # zip A_pos' L_pos'"
    by (simp add: L A_pos L_pos zip_append2 len_pos')
  have tab1: "table n A1 t1" and tabs_pos': "\<forall>(A, X) \<in> set (zip A_pos' L_pos'). table n A X"
    using tabs(1) by (auto simp: A_pos L_pos)
  have cols: "A1 \<union> \<Union>(fst ` set (zip A_pos' L_pos')) = \<Union>(set A_pos)"
    unfolding set_map[symmetric] map_fst_zip[OF len_pos'[symmetric]] by (simp add: A_pos)
  obtain A' t' where pos: "mmulti_join_pos n A1 t1 (zip A_pos' L_pos') = (A', t')"
    by fastforce
  have A': "A' = \<Union>(set A_pos)"
    using mmulti_join_pos_fst[of n A1 t1 "zip A_pos' L_pos'"] unfolding pos cols by simp
  have pos_corr: "table n (\<Union>(set A_pos)) t' \<and> (\<forall>z. z \<in> t' \<longleftrightarrow> wf_tuple n (\<Union>(set A_pos)) z \<and>
    restrict A1 z \<in> t1 \<and> (\<forall>(A, X) \<in> set (zip A_pos' L_pos'). restrict A z \<in> X))"
    using mmulti_join_pos_correct[OF tab1 tabs_pos'] unfolding pos cols by simp
  have negs: "\<forall>(A, X) \<in> set (zip A_neg L_neg). table n A X \<and> A \<subseteq> \<Union>(set A_pos)"
    using tabs(2) assms(3) by (auto dest: set_zip_leftD)
  have "mmulti_join_pw n A_pos A_neg L = mmulti_join_neg n A' t' (zip A_neg L_neg)"
    by (simp add: mmulti_join_pw_def zip_pos pos L_neg_def)
  then have "z \<in> mmulti_join_pw n A_pos A_neg L \<longleftrightarrow> z \<in> t' \<and> (\<forall>(A, X) \<in> set (zip A_neg L_neg). restrict A z \<notin> X)"
    using mmulti_join_neg_correct[OF conjunct1[OF pos_corr] negs, of z] unfolding A' by simp
  also have "\<dots> \<longleftrightarrow> wf_tuple n (\<Union>(set A_pos)) z \<and> list_all2 (\<lambda>A X. restrict A z \<in> X) A_pos L_pos \<and>
    list_all2 (\<lambda>A X. restrict A z \<notin> X) A_neg L_neg"
    using pos_corr unfolding list_all2_iff by (auto simp: A_pos L_pos len_pos' len_neg)
  finally show ?thesis
    by (simp add: L_pos_def L_neg_def)
qed

declare [[code drop: mmulti_join]]

lemma mmulti_join_code[code]:
  "mmulti_join n A_pos A_neg L =
    (if A_pos \<noteq> [] \<and> list_all2 (\<lambda>A X. table n A X \<and> wf_set n A) (A_pos @ A_neg) L \<and>
        (\<forall>A \<in> set A_neg. A \<subseteq> fold (\<union>) A_pos {})
     then mmulti_join_pw n A_pos A_neg L
     else (if length A_pos + length A_neg \<noteq> length L then {} else
    let L_pos = take (length A_pos) L; L_neg = drop (length A_pos) L in
    (case dominate_True A_pos L_pos of None \<Rightarrow>
      (case dominate_False A_pos L_pos A_neg L_neg of None \<Rightarrow> mmulti_join' A_pos A_neg L
      | Some (((A_zs, A_x, A_xs), A_ws, A_y, A_ys), ((zs, x, xs), ws, y, ys)) \<Rightarrow>
        mmulti_join n (A_zs @ A_x # A_xs) (A_ws @ A_ys)
        ((zs @ bin_join n A_x x False A_y y # xs) @ (ws @ ys)))
    | Some ((A_zs, A_x, A_xs, A_y, A_ys), (zs, x, xs, y, ys)) \<Rightarrow>
      mmulti_join n (A_zs @ (A_x \<union> A_y) # A_xs @ A_ys) A_neg
      ((zs @ bin_join n A_x x True A_y y # xs @ ys) @ L_neg))))"
proof (cases "A_pos \<noteq> [] \<and> list_all2 (\<lambda>A X. table n A X \<and> wf_set n A) (A_pos @ A_neg) L \<and>
        (\<forall>A \<in> set A_neg. A \<subseteq> fold (\<union>) A_pos {})")
  case True
  then have assms: "A_pos \<noteq> []" "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A) (A_pos @ A_neg) L"
    "\<forall>A \<in> set A_neg. A \<subseteq> \<Union>(set A_pos)"
    by (auto simp: Sup_set_fold)
  show ?thesis
    unfolding if_P[OF True]
    by (rule set_eqI) (simp only: mmulti_join_correct[OF assms(1,2)] mmulti_join_pw_correct[OF assms])
next
  case False
  show ?thesis
    unfolding if_not_P[OF False]
    apply (subst mmulti_join.simps)
    apply (rule refl)
    done
qed

(*<*)
end
(*>*)
