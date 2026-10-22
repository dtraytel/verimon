(*<*)
theory Idx_Code
  imports Until_Gen "Monitor_Impl.Monomorphic_Code"
begin
(*>*)



section \<open>The Since index maintained by its keys\<close>

text \<open>
  The executable Since keeps its stored tables clustered by the join columns (@{const eidx}), and
  @{theory MFODL_Monitor_Exec.Frame_Aux} maintains that index by whole-index operations: the tuples
  that enter the window are clustered and merged in (@{const eidx_union}), the tuples that leave
  it are clustered and subtracted (@{const eidx_minus}), and the probe by the left operand's table
  restricts the index by a filter over all its keys.  Each of these walks the whole index at every
  time point, while the tuples that actually move are typically few.

  This theory gives the three operations key-driven executable forms: a fold over the tuples that
  enter or leave, each visiting only its own bucket, and a restriction that visits only the keys
  of the probing table.  They are stated as equalities with the abstract operations and installed
  as code equations and @{attribute code_unfold} rules, so the verified algorithm is untouched and
  the generated code changes its cost, not its result.
\<close>

subsection \<open>Insertion\<close>

definition eidx_add1 :: "bool list \<Rightarrow> 'b list \<Rightarrow> ('b list, 'b list set) mapping \<Rightarrow>
    ('b list, 'b list set) mapping" where
  "eidx_add1 msk x i = (let k = eproj msk x in Mapping.update k (Set.insert x (ebucket i k)) i)"

lift_definition eidx_add1_cfi :: "bool list \<Rightarrow>
    ('b list, ('b list, 'b list set) mapping) comp_fun_idem" is eidx_add1
  by (rule comp_fun_idem_eidx_add1)

definition eidx_add :: "bool list \<Rightarrow> 'b list set \<Rightarrow> ('b list, 'b list set) mapping \<Rightarrow>
    ('b list, 'b list set) mapping" where
  "eidx_add msk X i = eidx_union i (eidx msk X)"

lemma eidx_add_code:
  "eidx_add msk X i = (if finite X then set_fold_cfi (eidx_add1_cfi msk) i X
     else Code.abort (STR ''eidx_add: infinite'') (\<lambda>_. eidx_add msk X i))"
  by (simp add: set_fold_cfi.rep_eq eidx_add1_cfi.rep_eq eidx_add_fold)

lemma eidx_add_RBT_code[code]:
  fixes rbt :: "'b :: ccompare list set_rbt"
  shows "eidx_add msk (RBT_set rbt) i = (case ID CCOMPARE('b list) of
      None \<Rightarrow> Code.abort (STR ''eidx_add: ccompare = None'') (\<lambda>_. eidx_add msk (RBT_set rbt) i)
    | Some _ \<Rightarrow> RBT_Set2.fold (eidx_add1 msk) rbt i)"
proof (cases "ID CCOMPARE('b list)")
  case None
  then show ?thesis by simp
next
  case (Some c)
  then have "finite (RBT_set rbt)" by (subst RBT_set_conv_keys) auto
  with Some show ?thesis
    by (subst eidx_add_code)
      (simp add: set_fold_cfi_RBT[OF eidx_add1_cfi.rep_eq, where s = "STR ''x''"])
qed

lemmas eidx_add_fallback_code[code] =
  eidx_add_code[of _ "DList_set _"] eidx_add_code[of _ "Set_Monad _"]
  eidx_add_code[of _ "Collect_set _"] eidx_add_code[of _ "Complement _"]

lemma eidx_union_didx_unfold[code_unfold]: "eidx_union i (eidx msk X) = eidx_add msk X i"
  by (simp add: eidx_add_def)

subsection \<open>Subtraction\<close>

definition eidx_del1 :: "bool list \<Rightarrow> 'b list \<Rightarrow> ('b list, 'b list set) mapping \<Rightarrow>
    ('b list, 'b list set) mapping" where
  "eidx_del1 msk x i = (let k = eproj msk x; B = ebucket i k - {x} in
     if B = {} then Mapping.delete k i else Mapping.update k B i)"

lift_definition eidx_del1_cfi :: "bool list \<Rightarrow>
    ('b list, ('b list, 'b list set) mapping) comp_fun_idem" is eidx_del1
  by (rule comp_fun_idem_eidx_del1)

definition eidx_del :: "bool list \<Rightarrow> 'b list set \<Rightarrow> ('b list, 'b list set) mapping \<Rightarrow>
    ('b list, 'b list set) mapping" where
  "eidx_del msk D i = eidx_minus i (eidx msk D)"

lemma eidx_del_RBT_code[code]:
  fixes rbt :: "'b :: ccompare list set_rbt"
  shows "eidx_del msk (RBT_set rbt) i = (case ID CCOMPARE('b list) of
      None \<Rightarrow> Code.abort (STR ''eidx_del: ccompare = None'') (\<lambda>_. eidx_del msk (RBT_set rbt) i)
    | Some _ \<Rightarrow> RBT_Set2.fold (eidx_del1 msk) rbt i)"
proof (cases "ID CCOMPARE('b list)")
  case None
  then show ?thesis by simp
next
  case (Some c)
  then have "finite (RBT_set rbt)" by (subst RBT_set_conv_keys) auto
  with Some show ?thesis
    by (subst eidx_del_code)
      (simp add: set_fold_cfi_RBT[OF eidx_del1_cfi.rep_eq, where s = "STR ''x''"])
qed

lemmas eidx_del_fallback_code[code] =
  eidx_del_code[of _ "DList_set _"] eidx_del_code[of _ "Set_Monad _"]
  eidx_del_code[of _ "Collect_set _"] eidx_del_code[of _ "Complement _"]

lemma eidx_minus_didx_unfold[code_unfold]: "eidx_minus i (eidx msk D) = eidx_del msk D i"
  by (simp add: eidx_del_def)

subsection \<open>Restricting a mapping by a key set\<close>

definition mfilter_keys :: "bool \<Rightarrow> 'k set \<Rightarrow> ('k, 'v) mapping \<Rightarrow> ('k, 'v) mapping" where
  "mfilter_keys pos Y m = Mapping.filter (\<lambda>k _. (k \<in> Y) = pos) m"

definition mrestrict1 :: "('k, 'v) mapping \<Rightarrow> 'k \<Rightarrow> ('k, 'v) mapping \<Rightarrow> ('k, 'v) mapping" where
  "mrestrict1 m k acc = (case Mapping.lookup m k of None \<Rightarrow> acc | Some v \<Rightarrow> Mapping.update k v acc)"

lift_definition mrestrict1_cfi :: "('k, 'v) mapping \<Rightarrow> ('k, ('k, 'v) mapping) comp_fun_idem"
  is mrestrict1
  by (rule comp_fun_idem_mrestrict1)

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

text \<open>@{const eshift_end} folds @{const filter_set} over the expired time points with the step
  unapplied, which no rule on an applied occurrence reaches; the fold gets a name whose code
  equation applies the step.\<close>

definition fold_filter_set :: "(ts \<times> 'b list set) list \<Rightarrow> ('b list, ts) mapping \<times> 'b list set \<Rightarrow>
    ('b list, ts) mapping \<times> 'b list set" where
  "fold_filter_set = fold filter_set"

lemma fold_filter_set_code[code]:
  "fold_filter_set [] acc = acc"
  "fold_filter_set (x # xs) acc = fold_filter_set xs (filter_set x acc)"
  by (simp_all add: fold_filter_set_def)

declare [[code drop: eshift_end]]

lemma eshift_end_code[code]:
  "eshift_end args nt (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) =
    (let I = args_ivl args;
     data_prev' = dropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) data_prev;
     (data_in, discard) = takedropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) data_in;
     (tuple_in, del) = fold_filter_set discard (tuple_in, {}) in
     (t, gc, msk, data_prev', data_in, table_in - del,
      eidx_upd args (\<lambda>_. eidx_minus idx_in (eidx msk del)), tuple_in, idx_since, tuple_since))"
  unfolding fold_filter_set_def by simp
subsection \<open>The probes, restated\<close>

text \<open>
  The two operations that restrict the index by the probing table apply @{const Mapping.filter}
  to a \<open>\<lambda>\<close>-abstraction.  The boxing of the filter at the monitor's types rewrites the
  bare constant, before any rule on the applied form could match, so the restriction cannot be
  installed by a rewrite rule on the pattern: the two operations get their code equations
  restated with @{const mfilter_keys}, which is what they mean.
\<close>

declare [[code drop: esemi_idx ejoin_msaux]]

lemma esemi_idx_code[code]: "esemi_idx msk pos idx X = set_of_idx (mfilter_keys pos X idx)"
  by (simp add: esemi_idx_def mfilter_keys_def)

subsection \<open>Deleting an index's buckets\<close>

text \<open>
  The join removes, from the window's table and from the per-tuple time stamps, the tuples of the
  index entries whose keys fail the probe.  Gathering those tuples into one set first builds a
  table that is only ever subtracted; removing each entry's tuples in turn does without it.
\<close>

definition del_buckets :: "('k, 'b set) mapping \<Rightarrow> 'b set \<times> ('b, 'v) mapping \<Rightarrow>
    'b set \<times> ('b, 'v) mapping" where
  "del_buckets M = (\<lambda>(T, tm). (T - set_of_idx M, mapping_delete_set tm (set_of_idx M)))"

definition del_buckets1 :: "('k, 'b set) mapping \<Rightarrow> ('b, 'v) mapping \<Rightarrow> ('b, 'v) mapping" where
  "del_buckets1 M tm = mapping_delete_set tm (set_of_idx M)"

lemma del_buckets_code[code]:
  fixes t :: "('k :: ccompare, 'b set) mapping_rbt"
  shows "del_buckets (RBT_Mapping t) = (case ID CCOMPARE('k) of
      None \<Rightarrow> Code.abort (STR ''del_buckets RBT_Mapping: ccompare = None'')
        (\<lambda>_. del_buckets (RBT_Mapping t))
    | Some _ \<Rightarrow> fold (\<lambda>p (T, tm). (T - snd p, mapping_delete_set tm (snd p)))
        (RBT_Mapping2.entries t))"
proof (cases "ID CCOMPARE('k)")
  case (Some c)
  have S: "set_of_idx (RBT_Mapping t) = \<Union>(snd ` set (RBT_Mapping2.entries t))"
    using set_of_idx_code[of t] Some by simp
  show ?thesis unfolding Some option.case del_buckets_def S
    by (simp add: fold_del_buckets fun_eq_iff)
qed simp

lemma del_buckets1_code[code]:
  fixes t :: "('k :: ccompare, 'b set) mapping_rbt"
  shows "del_buckets1 (RBT_Mapping t) tm = (case ID CCOMPARE('k) of
      None \<Rightarrow> Code.abort (STR ''del_buckets1 RBT_Mapping: ccompare = None'')
        (\<lambda>_. del_buckets1 (RBT_Mapping t) tm)
    | Some _ \<Rightarrow> fold (\<lambda>p tm. mapping_delete_set tm (snd p)) (RBT_Mapping2.entries t) tm)"
proof (cases "ID CCOMPARE('k)")
  case (Some c)
  have S: "set_of_idx (RBT_Mapping t) = \<Union>(snd ` set (RBT_Mapping2.entries t))"
    using set_of_idx_code[of t] Some by simp
  show ?thesis unfolding Some option.case del_buckets1_def S by (simp add: fold_del_buckets1)
qed simp

subsection \<open>The probe by a positive left operand, driven by the index\<close>

text \<open>
  With a positive left operand the join keeps the index entries whose keys are in the left
  table and deletes the tuples of the others.  @{thm [source] mfilter_keys_RBT_code} computes the
  kept part by visiting the left table's tuples, and the dropped part by deleting all of them from
  a copy of the index: work in the size of the left table, twice for each of the two indices,
  however few keys drop out.  Under a freeze whose frozen formula lags, the left operand is a
  large frozen table and the index is small.  MonPoly's join walks the index and removes only the
  buckets whose key fails the probe; the two operations below do the same: one pass over the
  index's entries collects the entries whose keys fail, whose keys are then deleted from the index
  and whose buckets from the window's table and time stamps.  Rebuilding the kept part instead
  (@{const RBT_Mapping2.filter}, linear in the index) costs more when few keys drop out.
\<close>

definition gjoin_idx :: "bool \<Rightarrow> 'k set \<Rightarrow> ('k, 'b set) mapping \<Rightarrow> 'b set \<times> ('b, 'v) mapping \<Rightarrow>
    ('k, 'b set) mapping \<times> 'b set \<times> ('b, 'v) mapping" where
  "gjoin_idx pos Y M acc = (mfilter_keys pos Y M, del_buckets (mfilter_keys (\<not> pos) Y M) acc)"

definition gjoin_idx1 :: "bool \<Rightarrow> 'k set \<Rightarrow> ('k, 'b set) mapping \<Rightarrow> ('b, 'v) mapping \<Rightarrow>
    ('k, 'b set) mapping \<times> ('b, 'v) mapping" where
  "gjoin_idx1 pos Y M tm = (mfilter_keys pos Y M, del_buckets1 (mfilter_keys (\<not> pos) Y M) tm)"

lemma gjoin_idx_code[code]:
  fixes t :: "('k :: ccompare, 'b set) mapping_rbt"
  shows "gjoin_idx pos Y (RBT_Mapping t) acc = (case ID CCOMPARE('k) of
      None \<Rightarrow> Code.abort (STR ''gjoin_idx RBT_Mapping: ccompare = None'')
        (\<lambda>_. gjoin_idx pos Y (RBT_Mapping t) acc)
    | Some _ \<Rightarrow> (if pos then
        (let D = RBT_Mapping2.fold (\<lambda>k v acc. if k \<in> Y then acc else (k, v) # acc) t [] in
         (foldr (\<lambda>p. Mapping.delete (fst p)) D (RBT_Mapping t),
          foldr (\<lambda>p (T, tm). (T - snd p, mapping_delete_set tm (snd p))) D acc))
      else (mfilter_keys pos Y (RBT_Mapping t), del_buckets (mfilter_keys (\<not> pos) Y (RBT_Mapping t)) acc)))"
proof (cases "ID CCOMPARE('k)")
  case (Some c)
  then have n: "ID CCOMPARE('k) \<noteq> None" by simp
  obtain T tm where acc: "acc = (T, tm)" by (cases acc)
  show ?thesis
    using Some by (simp add: acc gjoin_idx_def mfilter_keys_True_RBT[OF n]
        set_of_idx_mfilter_keys_False_RBT[OF n] del_buckets_def fold_del_buckets
        Let_def entries_fails_fold foldr_conv_fold del: RBT_Mapping_def)
qed simp

lemma gjoin_idx1_code[code]:
  fixes t :: "('k :: ccompare, 'b set) mapping_rbt"
  shows "gjoin_idx1 pos Y (RBT_Mapping t) tm = (case ID CCOMPARE('k) of
      None \<Rightarrow> Code.abort (STR ''gjoin_idx1 RBT_Mapping: ccompare = None'')
        (\<lambda>_. gjoin_idx1 pos Y (RBT_Mapping t) tm)
    | Some _ \<Rightarrow> (if pos then
        (let D = RBT_Mapping2.fold (\<lambda>k v acc. if k \<in> Y then acc else (k, v) # acc) t [] in
         (foldr (\<lambda>p. Mapping.delete (fst p)) D (RBT_Mapping t),
          foldr (\<lambda>p tm. mapping_delete_set tm (snd p)) D tm))
      else (mfilter_keys pos Y (RBT_Mapping t), del_buckets1 (mfilter_keys (\<not> pos) Y (RBT_Mapping t)) tm)))"
proof (cases "ID CCOMPARE('k)")
  case (Some c)
  then have n: "ID CCOMPARE('k) \<noteq> None" by simp
  show ?thesis
    using Some by (simp add: gjoin_idx1_def mfilter_keys_True_RBT[OF n]
        set_of_idx_mfilter_keys_False_RBT[OF n] del_buckets1_def fold_del_buckets1
        Let_def entries_fails_fold foldr_conv_fold del: RBT_Mapping_def)
qed simp

lemma ejoin_msaux_code[code]:
  "ejoin_msaux args Y (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
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
        (let (idx_in', table_in', tuple_in') = gjoin_idx pos Y idx_in (table_in, tuple_in);
             (idx_since', tuple_since') = gjoin_idx1 pos Y idx_since tuple_since in
         (t, gc, msk, data_prev, data_in, table_in', idx_in', tuple_in', idx_since',
          tuple_since'))))"
proof -
  have D: "\<And>M. del_buckets M (table_in, tuple_in)
      = (table_in - set_of_idx M, mapping_delete_set tuple_in (set_of_idx M))"
    by (simp add: del_buckets_def)
  show ?thesis
    by (simp only: ejoin_msaux.simps Let_def D gjoin_idx_def gjoin_idx1_def del_buckets1_def
        mfilter_keys_def esemi_idx_def prod.case)
qed

subsection \<open>The Until structure's map of the left operand\<close>

text \<open>For a positive left operand the Until structure keeps, for every tuple of the latest left
  table, the time point since which it has held; the update restricts the map to that table.  The
  restriction is @{const mfilter_keys}, which looks the table's tuples up rather than filtering
  the whole map through a generic predicate.\<close>

declare [[code drop: gadd_new_dq]]

lemma gadd_new_dq_code[code]:
  "gadd_new_dq args msk rel1 rel2 nt aux =
    (let (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, dn) =
       gshift_dq args nt aux;
     I = args_ivl args; pos = args_pos args; inz = memL I 0;
     new_tstp = (if inz then Inr tp else Inl nt);
     tstp_dq = dq_push nt tstp_dq;
     P = (\<lambda>t. memL I (nt - dq_nth_s tstp_dq (t - (tp - len)) 0));
     (tbl, a2_dq') = fold (guntil_elem_step_dq a1_map msk pos tp len inz P new_tstp)
       (csl rel2) ({}, a2_dq);
     tables = append_queue (tbl, new_tstp) tables;
     a2_dq = dq_push Mapping.empty a2_dq';
     a1_map = (if pos then mfilter_keys True rel1
       (upd_set a1_map (\<lambda>_. tp) (rel1 - Mapping.keys a1_map)) else upd_set a1_map (\<lambda>_. tp) rel1);
     tss = append_queue nt tss in
     (tp + 1, tss, tables, len + 1, result, a1_map, a2_dq, tstp_dq, dn))"
  unfolding gadd_new_dq_def mfilter_keys_def eq_True ..

(*<*)
end
(*>*)
