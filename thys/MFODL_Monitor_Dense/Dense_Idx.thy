(*<*)
theory Dense_Idx
  imports Kernel_Code
begin
(*>*)

section \<open>The Since index maintained by its keys\<close>

text \<open>
  The kernel's Since structure keeps its two tables indexed by the left operand's columns
  (@{typ "'a wf_idx"}), and maintains the indices by whole-index operations: the tuples that
  enter the window are indexed on their own (@{const idx_create}) and the two indices merged
  (@{const idx_union}); the tuples that leave are indexed and the indices antijoined.  The tuples
  that move are typically few.  This theory gives the two operations key-driven executable
  forms, as the dense evaluator had them (\<^verbatim>\<open>Dense_Idx_Code\<close>): a fold over the tuples that
  enter or leave, each visiting only its own bucket.  They are stated as equalities with the
  kernel's operations and installed as code equations and @{attribute code_unfold} rules, so the
  kernel is untouched and the generated code changes its cost, not its result.
\<close>

subsection \<open>Insertion into an index\<close>

definition idx_bucket :: "('a tuple, 'a table) mapping \<Rightarrow> 'a tuple \<Rightarrow> 'a table" where
  "idx_bucket T k = (case Mapping.lookup T k of None \<Rightarrow> {} | Some Y \<Rightarrow> Y)"

definition idx_add1 :: "nat list \<Rightarrow> nat list \<Rightarrow> 'a tuple \<Rightarrow> ('a tuple, 'a table) mapping \<Rightarrow>
    ('a tuple, 'a table) mapping" where
  "idx_add1 cs I x T = (let k = restrict I cs x in Mapping.update k (Set.insert x (idx_bucket T k)) T)"

lemma lookup_idx_add1: "Mapping.lookup (idx_add1 cs I x T) k =
  (if k = restrict I cs x then Some (Set.insert x (idx_bucket T k)) else Mapping.lookup T k)"
  by (simp add: idx_add1_def Let_def Mapping.lookup_update')

lemma idx_bucket_add1: "idx_bucket (idx_add1 cs I x T) k =
  (if k = restrict I cs x then Set.insert x (idx_bucket T k) else idx_bucket T k)"
  by (simp add: idx_bucket_def lookup_idx_add1)

lemma comp_fun_idem_idx_add1: "comp_fun_idem (idx_add1 cs I)"
  by unfold_locales
    (auto simp: fun_eq_iff lookup_idx_add1 idx_bucket_add1 intro!: mapping_eqI)

lift_definition idx_add1_cfi :: "nat list \<Rightarrow> nat list \<Rightarrow>
    ('a tuple, ('a tuple, 'a table) mapping) comp_fun_idem" is idx_add1
  by (rule comp_fun_idem_idx_add1)

lemma lookup_fold_idx_add1:
  assumes "finite X"
  shows "Mapping.lookup (Finite_Set.fold (idx_add1 cs I) T X) k =
    (if k \<in> restrict I cs ` X then Some (idx_bucket T k \<union> {y \<in> X. restrict I cs y = k})
     else Mapping.lookup T k)"
  using assms
proof (induction X arbitrary: k)
  case (insert x X)
  interpret comp_fun_idem "idx_add1 cs I" by (rule comp_fun_idem_idx_add1)
  show ?case
    using insert.IH[of k] insert.IH[of "restrict I cs x"] insert.hyps
    by (auto simp: fold_insert lookup_idx_add1 idx_bucket_def image_iff
        split: option.splits if_splits)
qed simp

definition idx_ins :: "nat list \<Rightarrow> nat list \<Rightarrow> ('a tuple, 'a table) mapping \<Rightarrow> 'a table \<Rightarrow>
    ('a tuple, 'a table) mapping" where
  "idx_ins cs I T X = idx_union T (idx_create cs I X)"

lemma lookup_idx_ins: "Mapping.lookup (idx_ins cs I T X) k =
  (if k \<in> restrict I cs ` X then Some (idx_bucket T k \<union> {y \<in> X. restrict I cs y = k})
   else Mapping.lookup T k)"
  by (auto simp: idx_ins_def idx_union_def idx_create_def Mapping.lookup_combine lookup_cluster
      combine_options_def idx_bucket_def image_iff split: option.splits)

lemma idx_ins_fold: "finite X \<Longrightarrow> idx_ins cs I T X = Finite_Set.fold (idx_add1 cs I) T X"
  by (intro mapping_eqI) (simp add: lookup_idx_ins lookup_fold_idx_add1)

lemma idx_ins_code:
  "idx_ins cs I T X = (if finite X then set_fold_cfi (idx_add1_cfi cs I) T X
     else Code.abort (STR ''idx_ins: infinite'') (\<lambda>_. idx_ins cs I T X))"
  by (simp add: set_fold_cfi.rep_eq idx_add1_cfi.rep_eq idx_ins_fold)

lemma idx_ins_RBT_code[code]:
  fixes rbt :: "'a :: ccompare tuple set_rbt"
  shows "idx_ins cs I T (RBT_set rbt) = (case ID CCOMPARE('a tuple) of
      None \<Rightarrow> Code.abort (STR ''idx_ins: ccompare = None'') (\<lambda>_. idx_ins cs I T (RBT_set rbt))
    | Some _ \<Rightarrow> RBT_Set2.fold (idx_add1 cs I) rbt T)"
proof (cases "ID CCOMPARE('a tuple)")
  case None
  then show ?thesis by simp
next
  case (Some c)
  then have "finite (RBT_set rbt)" by (subst RBT_set_conv_keys) auto
  with Some show ?thesis
    by (subst idx_ins_code)
      (simp add: set_fold_cfi_RBT[OF idx_add1_cfi.rep_eq, where s = "STR ''x''"])
qed

lemmas idx_ins_fallback_code[code] =
  idx_ins_code[of _ _ _ "DList_set _"] idx_ins_code[of _ _ _ "Set_Monad _"]
  idx_ins_code[of _ _ _ "Collect_set _"] idx_ins_code[of _ _ _ "Complement _"]

lift_definition wf_idx_ins :: "'a wf_idx \<Rightarrow> 'a table \<Rightarrow> 'a wf_idx" is
  "\<lambda>(cs, I, T) X. (cs, I, idx_ins cs I T (Set.filter (wf_tuple cs) X))"
  by (auto simp: idx_ins_def intro!: idx_union(2) idx_create(2) table_filter)

lemma filter_mem_self: "filter (\<lambda>c. c \<in> set xs) xs = xs"
  by (rule filter_True) simp

lemma wf_idx_union_of_set:
  assumes "wf_idx_sig i = cs" "wf_idx_cols i = filter (\<lambda>c. c \<in> set cs) L"
  shows "wf_idx_union i (wf_idx_of_set cs L X) = wf_idx_ins i X"
  using assms
  apply transfer
  subgoal for i cs L X
    by (cases i) (simp add: Let_def idx_reindex_def idx_ins_def, auto intro!: filter_cong)
  done

subsection \<open>Deletion from an index\<close>

definition idx_del1 :: "nat list \<Rightarrow> nat list \<Rightarrow> 'a tuple \<Rightarrow> ('a tuple, 'a table) mapping \<Rightarrow>
    ('a tuple, 'a table) mapping" where
  "idx_del1 cs I x T = (let k = restrict I cs x; B = idx_bucket T k - {x} in
     if B = {} then Mapping.delete k T else Mapping.update k B T)"

lemma lookup_idx_del1: "Mapping.lookup (idx_del1 cs I x T) k =
  (if k = restrict I cs x then (if idx_bucket T k - {x} = {} then None else Some (idx_bucket T k - {x}))
   else Mapping.lookup T k)"
  by (simp add: idx_del1_def Let_def Mapping.lookup_update')

lemma idx_bucket_del1: "idx_bucket (idx_del1 cs I x T) k =
  (if k = restrict I cs x then idx_bucket T k - {x} else idx_bucket T k)"
  by (simp add: idx_bucket_def lookup_idx_del1)

lemma comp_fun_idem_idx_del1: "comp_fun_idem (idx_del1 cs I)"
  by unfold_locales
    (auto simp: fun_eq_iff lookup_idx_del1 idx_bucket_del1 intro!: mapping_eqI)

lift_definition idx_del1_cfi :: "nat list \<Rightarrow> nat list \<Rightarrow>
    ('a tuple, ('a tuple, 'a table) mapping) comp_fun_idem" is idx_del1
  by (rule comp_fun_idem_idx_del1)

lemma lookup_fold_idx_del1:
  assumes "finite D"
  shows "Mapping.lookup (Finite_Set.fold (idx_del1 cs I) T D) k =
    (if k \<in> restrict I cs ` D then
       (if idx_bucket T k - {y \<in> D. restrict I cs y = k} = {} then None
        else Some (idx_bucket T k - {y \<in> D. restrict I cs y = k}))
     else Mapping.lookup T k)"
  using assms
proof (induction D arbitrary: k)
  case (insert x D)
  interpret comp_fun_idem "idx_del1 cs I" by (rule comp_fun_idem_idx_del1)
  have b: "idx_bucket (Finite_Set.fold (idx_del1 cs I) T D) k' =
    (if k' \<in> restrict I cs ` D then idx_bucket T k' - {y \<in> D. restrict I cs y = k'}
     else idx_bucket T k')" for k'
    by (simp add: idx_bucket_def insert.IH)
  show ?case
  proof (cases "k = restrict I cs x")
    case True
    have s: "{y \<in> Set.insert x D. restrict I cs y = k} = Set.insert x {y \<in> D. restrict I cs y = k}"
      using True by auto
    have e: "idx_bucket (Finite_Set.fold (idx_del1 cs I) T D) k - {x}
        = idx_bucket T k - Set.insert x {y \<in> D. restrict I cs y = k}"
      using True by (auto simp: b image_iff)
    show ?thesis
      unfolding fold_insert[OF insert.hyps] lookup_idx_del1 s e using True by simp
  next
    case False
    have s: "{y \<in> Set.insert x D. restrict I cs y = k} = {y \<in> D. restrict I cs y = k}"
      using False by auto
    show ?thesis
      unfolding fold_insert[OF insert.hyps] lookup_idx_del1 s using False by (simp add: insert.IH)
  qed
qed simp

text \<open>The executable deletion, and its equality with the kernel's antijoin of the index with the
  index of the deleted tuples, on the index's own columns.\<close>

definition idx_dels :: "nat list \<Rightarrow> nat list \<Rightarrow> ('a tuple, 'a table) mapping \<Rightarrow> 'a table \<Rightarrow>
    ('a tuple, 'a table) mapping" where
  "idx_dels cs I T D = (if finite D then Finite_Set.fold (idx_del1 cs I) T D else T)"

lemma idx_dels_code:
  "idx_dels cs I T D = (if finite D then set_fold_cfi (idx_del1_cfi cs I) T D else T)"
  by (simp add: idx_dels_def set_fold_cfi.rep_eq idx_del1_cfi.rep_eq)

lemma idx_dels_RBT_code[code]:
  fixes rbt :: "'a :: ccompare tuple set_rbt"
  shows "idx_dels cs I T (RBT_set rbt) = (case ID CCOMPARE('a tuple) of
      None \<Rightarrow> Code.abort (STR ''idx_dels: ccompare = None'') (\<lambda>_. idx_dels cs I T (RBT_set rbt))
    | Some _ \<Rightarrow> RBT_Set2.fold (idx_del1 cs I) rbt T)"
proof (cases "ID CCOMPARE('a tuple)")
  case None
  then show ?thesis by simp
next
  case (Some c)
  then have "finite (RBT_set rbt)" by (subst RBT_set_conv_keys) auto
  with Some show ?thesis
    by (subst idx_dels_code)
      (simp add: set_fold_cfi_RBT[OF idx_del1_cfi.rep_eq, where s = "STR ''x''"])
qed

lemmas idx_dels_fallback_code[code] =
  idx_dels_code[of _ _ _ "DList_set _"] idx_dels_code[of _ _ _ "Set_Monad _"]
  idx_dels_code[of _ _ _ "Collect_set _"] idx_dels_code[of _ _ _ "Complement _"]

lemma idx_antijoin_create:
  assumes d: "distinct cs" and wf: "idx_wf cs I T" and D: "table cs D" and f: "finite D"
  shows "idx_antijoin cs T cs (idx_create cs I D) = idx_dels cs I T D"
proof (rule mapping_eqI)
  fix k
  let ?K = "restrict I cs"
  let ?Dk = "{y \<in> D. ?K y = k}"
  have jn: "bin_join cs Y False cs ?Dk = Y - ?Dk" if "Mapping.lookup T k = Some Y" for Y
  proof -
    have tY: "table cs Y" using idx_wfD(1)[OF wf that] .
    have tD: "table cs ?Dk" using D by (auto simp: table_def)
    have "bin_join cs Y False cs ?Dk = join cs Y False cs ?Dk"
      by (rule bin_join_table[OF d d tY tD])
    also have "\<dots> = Y - ?Dk"
      using tY tD d by (intro join_same_cols(2)) (auto simp: table_def wf_tuple_def)
    finally show ?thesis .
  qed
  have lhs: "Mapping.lookup (idx_antijoin cs T cs T') k =
      combine_options (\<union>)
        (case Mapping.lookup T k of None \<Rightarrow> None
         | Some y \<Rightarrow> (case Mapping.lookup T' k of None \<Rightarrow> Some y | Some _ \<Rightarrow> None))
        (case Mapping.lookup T k of None \<Rightarrow> None
         | Some y \<Rightarrow> (case Mapping.lookup T' k of None \<Rightarrow> None
           | Some y' \<Rightarrow> (let Z = bin_join cs y False cs y' in if Z \<noteq> {} then Some Z else None)))"
    for T' :: "('a tuple, 'a table) mapping"
    by (simp add: idx_antijoin_def Mapping.lookup_combine Mapping.lookup_filter lookup_mapping_join
        lookup_mapping_antijoin Let_def del: bin_join.simps split: option.splits)
  show "Mapping.lookup (idx_antijoin cs T cs (idx_create cs I D)) k =
      Mapping.lookup (idx_dels cs I T D) k"
  proof (cases "k \<in> ?K ` D")
    case True
    then have c: "Mapping.lookup (idx_create cs I D) k = Some ?Dk"
      by (auto simp: idx_create_def lookup_cluster image_iff)
    show ?thesis
    proof (cases "Mapping.lookup T k")
      case None
      then show ?thesis
        unfolding idx_dels_def if_P[OF f] lookup_fold_idx_del1[OF f] lhs c
        using True by (simp add: idx_bucket_def)
    next
      case (Some Y)
      then show ?thesis
        unfolding idx_dels_def if_P[OF f] lookup_fold_idx_del1[OF f] lhs c
        using True jn[OF Some] by (simp add: idx_bucket_def Let_def)
    qed
  next
    case False
    then have c: "Mapping.lookup (idx_create cs I D) k = None"
      by (auto simp: idx_create_def lookup_cluster image_iff)
    show ?thesis
      unfolding idx_dels_def if_P[OF f] lookup_fold_idx_del1[OF f] lhs c
      using False by (simp split: option.splits)
  qed
qed

lift_definition wf_idx_rem :: "'a wf_idx \<Rightarrow> 'a table \<Rightarrow> 'a wf_idx" is
  "\<lambda>(cs, I, T) D. (cs, I, idx_antijoin cs T cs (idx_create cs I (Set.filter (wf_tuple cs) D)))"
  by (auto intro!: idx_antijoin(2) idx_create(2) table_filter)

text \<open>The index's invariant gives the deletion its executable form.\<close>

declare [[code drop: wf_idx_rem]]

lemma wf_idx_rem_code[code]: "Rep_wf_idx (wf_idx_rem i D) = (case Rep_wf_idx i of (cs, I, T) \<Rightarrow>
    (let D' = Set.filter (wf_tuple cs) D in
     if finite D' then (cs, I, idx_dels cs I T D')
     else (cs, I, idx_antijoin cs T cs (idx_create cs I D'))))"
proof -
  obtain cs I T where r: "Rep_wf_idx i = (cs, I, T)" "distinct cs" "set I \<subseteq> set cs" "idx_wf cs I T"
    by (rule wf_idx_rep)
  have t: "table cs (Set.filter (wf_tuple cs) D)" by (auto simp: table_def)
  show ?thesis
    using idx_antijoin_create[OF r(2) r(4) t]
    by (simp add: wf_idx_rem.rep_eq r Let_def)
qed

lemma wf_idx_antijoin_of_set:
  assumes "wf_idx_sig i = cs" "wf_idx_cols i = filter (\<lambda>c. c \<in> set cs) L" "wf_idx_cols i \<noteq> cs"
  shows "wf_idx_antijoin i (wf_idx_of_set cs L D) = wf_idx_rem i D"
  using assms
  apply transfer
  subgoal for i cs L D
    by (cases i) (simp add: Let_def idx_reindex_def, auto intro!: filter_cong)
  done

subsection \<open>The indexed tables\<close>

text \<open>A copy of the union, so that the fallback of the equation below is not redirected to it.\<close>

definition wf_table_union0 :: "'a wf_table \<Rightarrow> 'a wf_table \<Rightarrow> 'a wf_table" where
  "wf_table_union0 = wf_table_union"

lemma wf_table_union0_code[code]: "wf_table_union0 t u = wf_table_union t u"
  by (simp add: wf_table_union0_def)

definition wf_table_add :: "args \<Rightarrow> 'a wf_table \<Rightarrow> 'a table \<Rightarrow> 'a wf_table" where
  "wf_table_add args t X = wf_table_union t (wf_table_of_set_args args X)"

lemma wf_table_add_unfold[code_unfold]:
  "wf_table_union t (wf_table_of_set_args args X) = wf_table_add args t X"
  by (simp add: wf_table_add_def)

lemma wf_table_add_code[code]:
  "wf_table_add args (wf_table_of_idx i) X = (if wf_idx_sig i = args_R args \<and>
       wf_idx_cols i = filter (\<lambda>c. c \<in> set (args_R args)) (args_L args)
     then wf_table_of_idx (wf_idx_ins i X)
     else wf_table_union0 (wf_table_of_idx i) (wf_table_of_set_args args X))"
  "wf_table_add args (wf_table_of_wf_set s) X = wf_table_union0 (wf_table_of_wf_set s) (wf_table_of_set_args args X)"
  "wf_table_add args (wf_table_of_set cs Y) X = wf_table_union0 (wf_table_of_set cs Y) (wf_table_of_set_args args X)"
  "wf_table_add args (wf_table_of_keys cs m) X = wf_table_union0 (wf_table_of_keys cs m) (wf_table_of_set_args args X)"
  by (simp_all add: wf_table_add_def wf_table_union0_def wf_table_of_set_args_def
      wf_table_union_code(1) wf_idx_union_of_set)

definition wf_table_antijoin0 :: "'a wf_table \<Rightarrow> 'a wf_table \<Rightarrow> 'a wf_table" where
  "wf_table_antijoin0 = wf_table_antijoin"

lemma wf_table_antijoin0_code[code]: "wf_table_antijoin0 t u = wf_table_antijoin t u"
  by (simp add: wf_table_antijoin0_def)

definition wf_table_del :: "args \<Rightarrow> 'a wf_table \<Rightarrow> 'a table \<Rightarrow> 'a wf_table" where
  "wf_table_del args t D = wf_table_antijoin t (wf_table_of_set_args args D)"

lemma wf_table_del_unfold[code_unfold]:
  "wf_table_antijoin t (wf_table_of_set_args args D) = wf_table_del args t D"
  by (simp add: wf_table_del_def)

lemma wf_table_del_code[code]:
  "wf_table_del args (wf_table_of_idx i) D = (if wf_idx_sig i = args_R args \<and>
       wf_idx_cols i = filter (\<lambda>c. c \<in> set (args_R args)) (args_L args) \<and> wf_idx_cols i \<noteq> args_R args
     then wf_table_of_idx (wf_idx_rem i D)
     else wf_table_antijoin0 (wf_table_of_idx i) (wf_table_of_set_args args D))"
  "wf_table_del args (wf_table_of_wf_set s) D = wf_table_antijoin0 (wf_table_of_wf_set s) (wf_table_of_set_args args D)"
  "wf_table_del args (wf_table_of_set cs Y) D = wf_table_antijoin0 (wf_table_of_set cs Y) (wf_table_of_set_args args D)"
  "wf_table_del args (wf_table_of_keys cs m) D = wf_table_antijoin0 (wf_table_of_keys cs m) (wf_table_of_set_args args D)"
  by (simp_all add: wf_table_del_def wf_table_antijoin0_def wf_table_of_set_args_def
      wf_table_antijoin_code(1)) (auto simp: wf_idx_antijoin_of_set)

(*<*)
end
(*>*)
