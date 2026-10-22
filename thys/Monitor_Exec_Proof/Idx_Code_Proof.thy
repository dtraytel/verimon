(*<*)
theory Idx_Code_Proof
  imports "Monitor_Exec.Idx_Code" Until_Gen_Proof "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



lemma lookup_eidx_add1: "Mapping.lookup (eidx_add1 msk x i) k =
  (if k = eproj msk x then Some (Set.insert x (ebucket i k)) else Mapping.lookup i k)"
  by (simp add: eidx_add1_def Let_def Mapping.lookup_update')

lemma ebucket_eidx_add1: "ebucket (eidx_add1 msk x i) k =
  (if k = eproj msk x then Set.insert x (ebucket i k) else ebucket i k)"
  by (simp add: ebucket_def lookup_eidx_add1)

lemma comp_fun_idem_eidx_add1: "comp_fun_idem (eidx_add1 msk)"
  by unfold_locales
    (auto simp: fun_eq_iff lookup_eidx_add1 ebucket_eidx_add1 intro!: mapping_eqI)

lemma lookup_eidx_add: "Mapping.lookup (eidx_add msk X i) k =
  (if k \<in> eproj msk ` X then Some (ebucket i k \<union> {y \<in> X. eproj msk y = k})
   else Mapping.lookup i k)"
  by (auto simp: eidx_add_def eidx_union_def Mapping.lookup_combine lookup_eidx combine_options_def
      ebucket_def split: option.splits)

lemma lookup_fold_eidx_add1:
  assumes "finite X"
  shows "Mapping.lookup (Finite_Set.fold (eidx_add1 msk) i X) k =
    (if k \<in> eproj msk ` X then Some (ebucket i k \<union> {y \<in> X. eproj msk y = k})
     else Mapping.lookup i k)"
  using assms
proof (induction X arbitrary: k)
  case empty
  then show ?case by simp
next
  case (insert x X)
  interpret comp_fun_idem "eidx_add1 msk" by (rule comp_fun_idem_eidx_add1)
  show ?case
    using insert.IH[of k] insert.IH[of "eproj msk x"] insert.hyps
    by (auto simp: fold_insert lookup_eidx_add1 ebucket_def image_iff
        split: option.splits if_splits)
qed

lemma eidx_add_fold: "finite X \<Longrightarrow> eidx_add msk X i = Finite_Set.fold (eidx_add1 msk) i X"
  by (intro mapping_eqI) (simp add: lookup_eidx_add lookup_fold_eidx_add1)

lemma lookup_eidx_del1: "Mapping.lookup (eidx_del1 msk x i) k =
  (if k = eproj msk x then (if ebucket i k - {x} = {} then None else Some (ebucket i k - {x}))
   else Mapping.lookup i k)"
  by (simp add: eidx_del1_def Let_def Mapping.lookup_update')

lemma ebucket_eidx_del1: "ebucket (eidx_del1 msk x i) k =
  (if k = eproj msk x then ebucket i k - {x} else ebucket i k)"
  by (simp add: ebucket_def lookup_eidx_del1)

lemma comp_fun_idem_eidx_del1: "comp_fun_idem (eidx_del1 msk)"
  by unfold_locales
    (auto simp: fun_eq_iff lookup_eidx_del1 ebucket_eidx_del1 intro!: mapping_eqI)

lemma lookup_eidx_del: "Mapping.lookup (eidx_del msk D i) k =
  (if k \<in> eproj msk ` D then
     (if ebucket i k - {y \<in> D. eproj msk y = k} = {} then None
      else Some (ebucket i k - {y \<in> D. eproj msk y = k}))
   else Mapping.lookup i k)"
  by (auto simp: eidx_del_def eidx_minus_def Mapping.lookup_filter Mapping.lookup_map_values
      lookup_eidx ebucket_def split: option.splits)

lemma lookup_fold_eidx_del1:
  assumes "finite D"
  shows "Mapping.lookup (Finite_Set.fold (eidx_del1 msk) i D) k =
    (if k \<in> eproj msk ` D then
       (if ebucket i k - {y \<in> D. eproj msk y = k} = {} then None
        else Some (ebucket i k - {y \<in> D. eproj msk y = k}))
     else Mapping.lookup i k)"
  using assms
proof (induction D arbitrary: k)
  case empty
  then show ?case by simp
next
  case (insert x D)
  interpret comp_fun_idem "eidx_del1 msk" by (rule comp_fun_idem_eidx_del1)
  have b: "ebucket (Finite_Set.fold (eidx_del1 msk) i D) k' =
    (if k' \<in> eproj msk ` D then ebucket i k' - {y \<in> D. eproj msk y = k'} else ebucket i k')" for k'
    by (simp add: ebucket_def insert.IH)
  show ?case
  proof (cases "k = eproj msk x")
    case True
    have s: "{y \<in> Set.insert x D. eproj msk y = k} = Set.insert x {y \<in> D. eproj msk y = k}"
      using True by auto
    have e: "ebucket (Finite_Set.fold (eidx_del1 msk) i D) k - {x}
        = ebucket i k - Set.insert x {y \<in> D. eproj msk y = k}"
      using True by (auto simp: b image_iff)
    show ?thesis
      unfolding fold_insert[OF insert.hyps] lookup_eidx_del1 s e using True by simp
  next
    case False
    have s: "{y \<in> Set.insert x D. eproj msk y = k} = {y \<in> D. eproj msk y = k}"
      using False by auto
    show ?thesis
      unfolding fold_insert[OF insert.hyps] lookup_eidx_del1 s using False by (simp add: insert.IH)
  qed
qed

lemma eidx_del_fold: "finite D \<Longrightarrow> eidx_del msk D i = Finite_Set.fold (eidx_del1 msk) i D"
  by (intro mapping_eqI) (simp add: lookup_eidx_del lookup_fold_eidx_del1)

lemma eidx_del_code:
  "eidx_del msk D i = (if finite D then set_fold_cfi (eidx_del1_cfi msk) i D
     else Code.abort (STR ''eidx_del: infinite'') (\<lambda>_. eidx_del msk D i))"
  by (simp add: set_fold_cfi.rep_eq eidx_del1_cfi.rep_eq eidx_del_fold)

lemma lookup_mfilter_keys: "Mapping.lookup (mfilter_keys pos Y m) k =
  (if (k \<in> Y) = pos then Mapping.lookup m k else None)"
  by (auto simp: mfilter_keys_def Mapping.lookup_filter split: option.splits)

lemma mfilter_keys_False: "mfilter_keys False Y m = mapping_delete_set m Y"
  by (intro mapping_eqI) (simp add: lookup_mfilter_keys delete_set_lookup)

lemma lookup_mrestrict1: "Mapping.lookup (mrestrict1 m k acc) k' =
  (if k' = k \<and> Mapping.lookup m k \<noteq> None then Mapping.lookup m k else Mapping.lookup acc k')"
  by (auto simp: mrestrict1_def Mapping.lookup_update' split: option.splits)

lemma comp_fun_idem_mrestrict1: "comp_fun_idem (mrestrict1 m)"
  by unfold_locales (auto simp: fun_eq_iff lookup_mrestrict1 intro!: mapping_eqI)

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

lemma mapping_delete_set_Un:
  "mapping_delete_set m (A \<union> B) = mapping_delete_set (mapping_delete_set m A) B"
  by (intro mapping_eqI) (simp add: delete_set_lookup)

lemma fold_del_buckets:
  "fold (\<lambda>p (T, tm). (T - snd p, mapping_delete_set tm (snd p))) xs (T, tm)
   = (T - \<Union>(snd ` set xs), mapping_delete_set tm (\<Union>(snd ` set xs)))"
  by (induct xs arbitrary: T tm)
    (auto simp: mapping_delete_set_Un[symmetric] mapping_delete_set_empty Diff_Un
      Un_commute[of "snd _"] Diff_Diff_Int intro: arg_cong2[where f = "(-)"])

lemma fold_del_buckets1:
  "fold (\<lambda>p tm. mapping_delete_set tm (snd p)) xs tm = mapping_delete_set tm (\<Union>(snd ` set xs))"
  by (induct xs arbitrary: tm) (auto simp: mapping_delete_set_Un[symmetric] mapping_delete_set_empty)

lemma lookup_fold_delete_fst:
  "Mapping.lookup (fold (\<lambda>p. Mapping.delete (fst p)) D M) k =
    (if k \<in> fst ` set D then None else Mapping.lookup M k)"
  by (induct D arbitrary: M) (auto simp: lookup_delete)

lemma mfilter_keys_True_RBT:
  fixes t :: "('k :: ccompare, 'v) mapping_rbt"
  assumes "ID CCOMPARE('k) \<noteq> None"
  shows "mfilter_keys True Y (RBT_Mapping t) =
    fold (\<lambda>p. Mapping.delete (fst p)) (List.filter (\<lambda>p. fst p \<notin> Y) (RBT_Mapping2.entries t))
      (RBT_Mapping t)"
proof (intro mapping_eqI)
  fix k
  have "k \<in> fst ` set (RBT_Mapping2.entries t) \<longleftrightarrow> RBT_Mapping2.lookup t k \<noteq> None"
    using dom_map_of_conv_image_fst[of "RBT_Mapping2.entries t"] assms by (auto simp: dom_def)
  then show "Mapping.lookup (mfilter_keys True Y (RBT_Mapping t)) k =
    Mapping.lookup (fold (\<lambda>p. Mapping.delete (fst p)) (List.filter (\<lambda>p. fst p \<notin> Y) (RBT_Mapping2.entries t))
      (RBT_Mapping t)) k"
    by (auto simp: lookup_mfilter_keys lookup_fold_delete_fst lookup_Mapping_code(1)
        simp del: RBT_Mapping_def)
qed

lemma entries_filter_RBT:
  "RBT_Mapping2.entries (RBT_Mapping2.filter P t) = List.filter P (RBT_Mapping2.entries t)"
  by transfer simp

lemma set_of_idx_mfilter_keys_False_RBT:
  fixes t :: "('k :: ccompare, 'b set) mapping_rbt"
  assumes "ID CCOMPARE('k) \<noteq> None"
  shows "set_of_idx (mfilter_keys False Y (RBT_Mapping t)) =
    \<Union>(snd ` set (List.filter (\<lambda>p. fst p \<notin> Y) (RBT_Mapping2.entries t)))"
proof -
  have "mfilter_keys False Y (RBT_Mapping t) = RBT_Mapping (RBT_Mapping2.filter (\<lambda>p. fst p \<notin> Y) t)"
    using assms by (intro mapping_eqI) (simp add: lookup_mfilter_keys Mapping.lookup.abs_eq split: option.splits)
  then show ?thesis
    using set_of_idx_code[of "RBT_Mapping2.filter (\<lambda>p. fst p \<notin> Y) t"] assms
    by (simp add: entries_filter_RBT del: RBT_Mapping_def split: option.splits)
qed

text \<open>The entries whose keys fail are collected by a fold over the index that conses only
  them, not by filtering the list of all its entries, which the join would build at every time
  point however few keys drop out.  The fold collects them in reverse order, so they are
  processed by a right fold.\<close>

lemma fold_cons_fails:
  "List.fold (\<lambda>(k, v) acc. if k \<in> Y then acc else (k, v) # acc) xs a =
    rev (List.filter (\<lambda>p. fst p \<notin> Y) xs) @ a"
  by (induct xs arbitrary: a) auto

lemma entries_fails_fold:
  "List.filter (\<lambda>p. fst p \<notin> Y) (RBT_Mapping2.entries t) =
    rev (RBT_Mapping2.fold (\<lambda>k v acc. if k \<in> Y then acc else (k, v) # acc) t [])"
  by transfer (simp add: RBT_Impl.fold_def fold_cons_fails)

end
(*>*)
