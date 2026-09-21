(*<*)
theory Dense_Idx_Code
  imports Dense_Unbox "MFODL_Monitor_Devel.Monomorphic_Code"
begin
(*>*)

section \<open>The Since index maintained by its keys\<close>

text \<open>
  The dense Since keeps its stored tables clustered by the join columns (@{const didx}), and
  @{theory MFODL_Monitor_Imp.Dense_Aux} maintains that index by whole-index operations: the tuples
  that enter the window are clustered and merged in (@{const didx_union}), the tuples that leave
  it are clustered and subtracted (@{const didx_minus}), and the probe by the left operand's table
  restricts the index by a filter over all its keys.  Each of these walks the whole index at every
  time point, while the tuples that actually move are typically few.

  This theory gives the three operations key-driven executable forms: a fold over the tuples that
  enter or leave, each visiting only its own bucket, and a restriction that visits only the keys
  of the probing table.  They are stated as equalities with the abstract operations and installed
  as code equations and @{attribute code_unfold} rules, so the verified algorithm is untouched and
  the generated code changes its cost, not its result.
\<close>

subsection \<open>Insertion\<close>

definition didx_add1 :: "bool list \<Rightarrow> 'b list \<Rightarrow> ('b list, 'b list set) mapping \<Rightarrow>
    ('b list, 'b list set) mapping" where
  "didx_add1 msk x i = (let k = dproj msk x in Mapping.update k (Set.insert x (dbucket i k)) i)"

lemma lookup_didx_add1: "Mapping.lookup (didx_add1 msk x i) k =
  (if k = dproj msk x then Some (Set.insert x (dbucket i k)) else Mapping.lookup i k)"
  by (simp add: didx_add1_def Let_def Mapping.lookup_update')

lemma dbucket_didx_add1: "dbucket (didx_add1 msk x i) k =
  (if k = dproj msk x then Set.insert x (dbucket i k) else dbucket i k)"
  by (simp add: dbucket_def lookup_didx_add1)

lemma comp_fun_idem_didx_add1: "comp_fun_idem (didx_add1 msk)"
  by unfold_locales
    (auto simp: fun_eq_iff lookup_didx_add1 dbucket_didx_add1 intro!: mapping_eqI)

lift_definition didx_add1_cfi :: "bool list \<Rightarrow>
    ('b list, ('b list, 'b list set) mapping) comp_fun_idem" is didx_add1
  by (rule comp_fun_idem_didx_add1)

definition didx_add :: "bool list \<Rightarrow> 'b list set \<Rightarrow> ('b list, 'b list set) mapping \<Rightarrow>
    ('b list, 'b list set) mapping" where
  "didx_add msk X i = didx_union i (didx msk X)"

lemma lookup_didx_add: "Mapping.lookup (didx_add msk X i) k =
  (if k \<in> dproj msk ` X then Some (dbucket i k \<union> {y \<in> X. dproj msk y = k})
   else Mapping.lookup i k)"
  by (auto simp: didx_add_def didx_union_def Mapping.lookup_combine lookup_didx combine_options_def
      dbucket_def split: option.splits)

lemma lookup_fold_didx_add1:
  assumes "finite X"
  shows "Mapping.lookup (Finite_Set.fold (didx_add1 msk) i X) k =
    (if k \<in> dproj msk ` X then Some (dbucket i k \<union> {y \<in> X. dproj msk y = k})
     else Mapping.lookup i k)"
  using assms
proof (induction X arbitrary: k)
  case empty
  then show ?case by simp
next
  case (insert x X)
  interpret comp_fun_idem "didx_add1 msk" by (rule comp_fun_idem_didx_add1)
  show ?case
    using insert.IH[of k] insert.IH[of "dproj msk x"] insert.hyps
    by (auto simp: fold_insert lookup_didx_add1 dbucket_def image_iff
        split: option.splits if_splits)
qed

lemma didx_add_fold: "finite X \<Longrightarrow> didx_add msk X i = Finite_Set.fold (didx_add1 msk) i X"
  by (intro mapping_eqI) (simp add: lookup_didx_add lookup_fold_didx_add1)

lemma didx_add_code:
  "didx_add msk X i = (if finite X then set_fold_cfi (didx_add1_cfi msk) i X
     else Code.abort (STR ''didx_add: infinite'') (\<lambda>_. didx_add msk X i))"
  by (simp add: set_fold_cfi.rep_eq didx_add1_cfi.rep_eq didx_add_fold)

lemma didx_add_RBT_code[code]:
  fixes rbt :: "'b :: ccompare list set_rbt"
  shows "didx_add msk (RBT_set rbt) i = (case ID CCOMPARE('b list) of
      None \<Rightarrow> Code.abort (STR ''didx_add: ccompare = None'') (\<lambda>_. didx_add msk (RBT_set rbt) i)
    | Some _ \<Rightarrow> RBT_Set2.fold (didx_add1 msk) rbt i)"
proof (cases "ID CCOMPARE('b list)")
  case None
  then show ?thesis by simp
next
  case (Some c)
  then have "finite (RBT_set rbt)" by (subst RBT_set_conv_keys) auto
  with Some show ?thesis
    by (subst didx_add_code)
      (simp add: set_fold_cfi_RBT[OF didx_add1_cfi.rep_eq, where s = "STR ''x''"])
qed

lemmas didx_add_fallback_code[code] =
  didx_add_code[of _ "DList_set _"] didx_add_code[of _ "Set_Monad _"]
  didx_add_code[of _ "Collect_set _"] didx_add_code[of _ "Complement _"]

lemma didx_union_didx_unfold[code_unfold]: "didx_union i (didx msk X) = didx_add msk X i"
  by (simp add: didx_add_def)

subsection \<open>Subtraction\<close>

definition didx_del1 :: "bool list \<Rightarrow> 'b list \<Rightarrow> ('b list, 'b list set) mapping \<Rightarrow>
    ('b list, 'b list set) mapping" where
  "didx_del1 msk x i = (let k = dproj msk x; B = dbucket i k - {x} in
     if B = {} then Mapping.delete k i else Mapping.update k B i)"

lemma lookup_didx_del1: "Mapping.lookup (didx_del1 msk x i) k =
  (if k = dproj msk x then (if dbucket i k - {x} = {} then None else Some (dbucket i k - {x}))
   else Mapping.lookup i k)"
  by (simp add: didx_del1_def Let_def Mapping.lookup_update')

lemma dbucket_didx_del1: "dbucket (didx_del1 msk x i) k =
  (if k = dproj msk x then dbucket i k - {x} else dbucket i k)"
  by (simp add: dbucket_def lookup_didx_del1)

lemma comp_fun_idem_didx_del1: "comp_fun_idem (didx_del1 msk)"
  by unfold_locales
    (auto simp: fun_eq_iff lookup_didx_del1 dbucket_didx_del1 intro!: mapping_eqI)

lift_definition didx_del1_cfi :: "bool list \<Rightarrow>
    ('b list, ('b list, 'b list set) mapping) comp_fun_idem" is didx_del1
  by (rule comp_fun_idem_didx_del1)

definition didx_del :: "bool list \<Rightarrow> 'b list set \<Rightarrow> ('b list, 'b list set) mapping \<Rightarrow>
    ('b list, 'b list set) mapping" where
  "didx_del msk D i = didx_minus i (didx msk D)"

lemma lookup_didx_del: "Mapping.lookup (didx_del msk D i) k =
  (if k \<in> dproj msk ` D then
     (if dbucket i k - {y \<in> D. dproj msk y = k} = {} then None
      else Some (dbucket i k - {y \<in> D. dproj msk y = k}))
   else Mapping.lookup i k)"
  by (auto simp: didx_del_def didx_minus_def Mapping.lookup_filter Mapping.lookup_map_values
      lookup_didx dbucket_def split: option.splits)

lemma lookup_fold_didx_del1:
  assumes "finite D"
  shows "Mapping.lookup (Finite_Set.fold (didx_del1 msk) i D) k =
    (if k \<in> dproj msk ` D then
       (if dbucket i k - {y \<in> D. dproj msk y = k} = {} then None
        else Some (dbucket i k - {y \<in> D. dproj msk y = k}))
     else Mapping.lookup i k)"
  using assms
proof (induction D arbitrary: k)
  case empty
  then show ?case by simp
next
  case (insert x D)
  interpret comp_fun_idem "didx_del1 msk" by (rule comp_fun_idem_didx_del1)
  have b: "dbucket (Finite_Set.fold (didx_del1 msk) i D) k' =
    (if k' \<in> dproj msk ` D then dbucket i k' - {y \<in> D. dproj msk y = k'} else dbucket i k')" for k'
    by (simp add: dbucket_def insert.IH)
  show ?case
  proof (cases "k = dproj msk x")
    case True
    have s: "{y \<in> Set.insert x D. dproj msk y = k} = Set.insert x {y \<in> D. dproj msk y = k}"
      using True by auto
    have e: "dbucket (Finite_Set.fold (didx_del1 msk) i D) k - {x}
        = dbucket i k - Set.insert x {y \<in> D. dproj msk y = k}"
      using True by (auto simp: b image_iff)
    show ?thesis
      unfolding fold_insert[OF insert.hyps] lookup_didx_del1 s e using True by simp
  next
    case False
    have s: "{y \<in> Set.insert x D. dproj msk y = k} = {y \<in> D. dproj msk y = k}"
      using False by auto
    show ?thesis
      unfolding fold_insert[OF insert.hyps] lookup_didx_del1 s using False by (simp add: insert.IH)
  qed
qed

lemma didx_del_fold: "finite D \<Longrightarrow> didx_del msk D i = Finite_Set.fold (didx_del1 msk) i D"
  by (intro mapping_eqI) (simp add: lookup_didx_del lookup_fold_didx_del1)

lemma didx_del_code:
  "didx_del msk D i = (if finite D then set_fold_cfi (didx_del1_cfi msk) i D
     else Code.abort (STR ''didx_del: infinite'') (\<lambda>_. didx_del msk D i))"
  by (simp add: set_fold_cfi.rep_eq didx_del1_cfi.rep_eq didx_del_fold)

lemma didx_del_RBT_code[code]:
  fixes rbt :: "'b :: ccompare list set_rbt"
  shows "didx_del msk (RBT_set rbt) i = (case ID CCOMPARE('b list) of
      None \<Rightarrow> Code.abort (STR ''didx_del: ccompare = None'') (\<lambda>_. didx_del msk (RBT_set rbt) i)
    | Some _ \<Rightarrow> RBT_Set2.fold (didx_del1 msk) rbt i)"
proof (cases "ID CCOMPARE('b list)")
  case None
  then show ?thesis by simp
next
  case (Some c)
  then have "finite (RBT_set rbt)" by (subst RBT_set_conv_keys) auto
  with Some show ?thesis
    by (subst didx_del_code)
      (simp add: set_fold_cfi_RBT[OF didx_del1_cfi.rep_eq, where s = "STR ''x''"])
qed

lemmas didx_del_fallback_code[code] =
  didx_del_code[of _ "DList_set _"] didx_del_code[of _ "Set_Monad _"]
  didx_del_code[of _ "Collect_set _"] didx_del_code[of _ "Complement _"]

lemma didx_minus_didx_unfold[code_unfold]: "didx_minus i (didx msk D) = didx_del msk D i"
  by (simp add: didx_del_def)

subsection \<open>Restricting a mapping by a key set\<close>

definition mfilter_keys :: "bool \<Rightarrow> 'k set \<Rightarrow> ('k, 'v) mapping \<Rightarrow> ('k, 'v) mapping" where
  "mfilter_keys pos Y m = Mapping.filter (\<lambda>k _. (k \<in> Y) = pos) m"

lemma lookup_mfilter_keys: "Mapping.lookup (mfilter_keys pos Y m) k =
  (if (k \<in> Y) = pos then Mapping.lookup m k else None)"
  by (auto simp: mfilter_keys_def Mapping.lookup_filter split: option.splits)

lemma mfilter_keys_False: "mfilter_keys False Y m = mapping_delete_set m Y"
  by (intro mapping_eqI) (simp add: lookup_mfilter_keys delete_set_lookup)

definition mrestrict1 :: "('k, 'v) mapping \<Rightarrow> 'k \<Rightarrow> ('k, 'v) mapping \<Rightarrow> ('k, 'v) mapping" where
  "mrestrict1 m k acc = (case Mapping.lookup m k of None \<Rightarrow> acc | Some v \<Rightarrow> Mapping.update k v acc)"

lemma lookup_mrestrict1: "Mapping.lookup (mrestrict1 m k acc) k' =
  (if k' = k \<and> Mapping.lookup m k \<noteq> None then Mapping.lookup m k else Mapping.lookup acc k')"
  by (auto simp: mrestrict1_def Mapping.lookup_update' split: option.splits)

lemma comp_fun_idem_mrestrict1: "comp_fun_idem (mrestrict1 m)"
  by unfold_locales (auto simp: fun_eq_iff lookup_mrestrict1 intro!: mapping_eqI)

lift_definition mrestrict1_cfi :: "('k, 'v) mapping \<Rightarrow> ('k, ('k, 'v) mapping) comp_fun_idem"
  is mrestrict1
  by (rule comp_fun_idem_mrestrict1)

lemma lookup_fold_mrestrict1:
  assumes "finite Y"
  shows "Mapping.lookup (Finite_Set.fold (mrestrict1 m) Mapping.empty Y) k =
    (if k \<in> Y then Mapping.lookup m k else None)"
  using assms
proof (induction Y)
  case empty
  then show ?case by simp
next
  case (insert x Y)
  interpret comp_fun_idem "mrestrict1 m" by (rule comp_fun_idem_mrestrict1)
  show ?case
    unfolding fold_insert[OF insert.hyps] lookup_mrestrict1 insert.IH by auto
qed

lemma mfilter_keys_True_fold:
  "finite Y \<Longrightarrow> mfilter_keys True Y m = Finite_Set.fold (mrestrict1 m) Mapping.empty Y"
  by (intro mapping_eqI) (simp add: lookup_mfilter_keys lookup_fold_mrestrict1)

lemma mfilter_keys_code:
  "mfilter_keys pos Y m = (if pos then
     (if finite Y then set_fold_cfi (mrestrict1_cfi m) Mapping.empty Y
      else Code.abort (STR ''mfilter_keys: infinite'') (\<lambda>_. mfilter_keys pos Y m))
   else mapping_delete_set m Y)"
  by (simp add: set_fold_cfi.rep_eq mrestrict1_cfi.rep_eq mfilter_keys_True_fold mfilter_keys_False)

lemma mfilter_keys_RBT_code[code]:
  fixes rbt :: "'k :: ccompare set_rbt"
  shows "mfilter_keys pos (RBT_set rbt) m = (case ID CCOMPARE('k) of
      None \<Rightarrow> Code.abort (STR ''mfilter_keys: ccompare = None'')
        (\<lambda>_. mfilter_keys pos (RBT_set rbt) m)
    | Some _ \<Rightarrow> (if pos then RBT_Set2.fold (mrestrict1 m) rbt Mapping.empty
        else mapping_delete_set m (RBT_set rbt)))"
proof (cases "ID CCOMPARE('k)")
  case None
  then show ?thesis by simp
next
  case (Some c)
  then have "finite (RBT_set rbt)" by (subst RBT_set_conv_keys) auto
  with Some show ?thesis
    by (subst mfilter_keys_code)
      (simp add: set_fold_cfi_RBT[OF mrestrict1_cfi.rep_eq, where s = "STR ''x''"])
qed

lemmas mfilter_keys_fallback_code[code] =
  mfilter_keys_code[of _ "DList_set _"] mfilter_keys_code[of _ "Set_Monad _"]
  mfilter_keys_code[of _ "Collect_set _"] mfilter_keys_code[of _ "Complement _"]

subsection \<open>The deletion of a key set, on a tree\<close>

text \<open>@{const mapping_delete_set} folds the deletion over the set through the
  @{type comp_fun_idem} wrapper; on a tree the fold names the deletion directly, applied, so
  that the specialisation of the deletion at the monitor's types reaches it.\<close>

declare [[code drop: mapping_delete_set]]

lemma mapping_delete_set_RBT_code[code]:
  fixes rbt :: "'k :: ccompare set_rbt"
  shows "mapping_delete_set m (RBT_set rbt) = (case ID CCOMPARE('k) of
      None \<Rightarrow> Code.abort (STR ''mapping_delete_set: ccompare = None'')
        (\<lambda>_. mapping_delete_set m (RBT_set rbt))
    | Some _ \<Rightarrow> RBT_Set2.fold (\<lambda>k. Mapping.delete k) rbt m)"
proof (cases "ID CCOMPARE('k)")
  case None
  then show ?thesis by simp
next
  case (Some c)
  then have "finite (RBT_set rbt)" by (subst RBT_set_conv_keys) auto
  with Some show ?thesis
    by (subst mapping_delete_set_code)
      (simp add: set_fold_cfi_RBT[OF mapping_delete_set_cfi.rep_eq, where s = "STR ''x''"])
qed

lemmas mapping_delete_set_fallback_code[code] =
  mapping_delete_set_code[of _ "DList_set _"] mapping_delete_set_code[of _ "Set_Monad _"]
  mapping_delete_set_code[of _ "Collect_set _"] mapping_delete_set_code[of _ "Complement _"]

text \<open>The same for @{const upd_set}, whose step applies the update to the key and the value
  and so stays applied.\<close>

declare [[code drop: upd_set]]

lemma upd_set_RBT_code[code]:
  fixes rbt :: "'k :: ccompare set_rbt"
  shows "upd_set m f (RBT_set rbt) = (case ID CCOMPARE('k) of
      None \<Rightarrow> Code.abort (STR ''upd_set: ccompare = None'') (\<lambda>_. upd_set m f (RBT_set rbt))
    | Some _ \<Rightarrow> RBT_Set2.fold (\<lambda>a. Mapping.update a (f a)) rbt m)"
proof (cases "ID CCOMPARE('k)")
  case None
  then show ?thesis by simp
next
  case (Some c)
  then have "finite (RBT_set rbt)" by (subst RBT_set_conv_keys) auto
  with Some show ?thesis
    by (subst upd_set_code) (simp add: set_fold_cfi_RBT[OF upd_cfi.rep_eq, where s = "STR ''x''"])
qed

lemmas upd_set_fallback_code[code] =
  upd_set_code[of _ _ "DList_set _"] upd_set_code[of _ _ "Set_Monad _"]
  upd_set_code[of _ _ "Collect_set _"] upd_set_code[of _ _ "Complement _"]

subsection \<open>The expiry's fold, applied\<close>

text \<open>@{const gshift_end} folds @{const filter_set} over the expired time points with the step
  unapplied, which no rule on an applied occurrence reaches; the fold gets a name whose code
  equation applies the step.\<close>

definition fold_filter_set :: "(ts \<times> 'b list set) list \<Rightarrow> ('b list, ts) mapping \<times> 'b list set \<Rightarrow>
    ('b list, ts) mapping \<times> 'b list set" where
  "fold_filter_set = fold filter_set"

lemma fold_filter_set_code[code]:
  "fold_filter_set [] acc = acc"
  "fold_filter_set (x # xs) acc = fold_filter_set xs (filter_set x acc)"
  by (simp_all add: fold_filter_set_def)

declare [[code drop: gshift_end]]

lemma gshift_end_code[code]:
  "gshift_end args nt (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) =
    (let I = args_ivl args;
     data_prev' = dropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) data_prev;
     (data_in, discard) = takedropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) data_in;
     (tuple_in, del) = fold_filter_set discard (tuple_in, {}) in
     (t, gc, msk, data_prev', data_in, table_in - del,
      gidx_upd args (\<lambda>_. didx_minus idx_in (didx msk del)), tuple_in, idx_since, tuple_since))"
  unfolding fold_filter_set_def by simp

subsection \<open>The probes, restated\<close>

text \<open>
  The two operations that restrict the index by the probing table apply @{const Mapping.filter}
  to a \<open>\<lambda>\<close>-abstraction.  The boxing of the filter at the monitor's types rewrites the
  bare constant, before any rule on the applied form could match, so the restriction cannot be
  installed by a rewrite rule on the pattern: the two operations get their code equations
  restated with @{const mfilter_keys}, which is what they mean.
\<close>

declare [[code drop: dsemi_idx gjoin_msaux]]

lemma dsemi_idx_code[code]: "dsemi_idx msk pos idx X = set_of_idx (mfilter_keys pos X idx)"
  by (simp add: dsemi_idx_def mfilter_keys_def)

lemma gjoin_msaux_code[code]:
  "gjoin_msaux args Y (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) =
    (let pos = args_pos args in
     (if \<forall>i \<in> set msk. \<not> i then
        (let take_all = (([] \<in> Y) = pos) in
         (t, gc, msk, data_prev, data_in,
          if take_all then table_in else {},
          if take_all then idx_in else Mapping.empty,
          if take_all then tuple_in else Mapping.empty,
          if take_all then idx_since else Mapping.empty,
          if take_all then tuple_since else Mapping.empty))
      else if \<forall>i \<in> set msk. i then
        (let in_del = (if pos then table_in - Y else table_in \<inter> Y);
         tuple_in' = mapping_delete_set tuple_in in_del;
         tuple_since' = mfilter_keys pos Y tuple_since in
         (t, gc, msk, data_prev, data_in, table_in - in_del, Mapping.empty, tuple_in',
          Mapping.empty, tuple_since'))
      else
        (let in_del = dsemi_idx msk (\<not> pos) idx_in Y;
         since_del = dsemi_idx msk (\<not> pos) idx_since Y in
         (t, gc, msk, data_prev, data_in, table_in - in_del,
          mfilter_keys pos Y idx_in, mapping_delete_set tuple_in in_del,
          mfilter_keys pos Y idx_since,
          mapping_delete_set tuple_since since_del))))"
  unfolding mfilter_keys_def by simp

(*<*)
end
(*>*)
