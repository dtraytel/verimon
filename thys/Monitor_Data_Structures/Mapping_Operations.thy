theory Mapping_Operations
  imports "Containers.Mapping_Impl" Mapping_Facts
begin

section \<open>Operations on mappings\<close>

subsection \<open>Values, joins and antijoins\<close>

lift_definition set_of_idx :: "('a, 'b set) mapping \<Rightarrow> 'b set" is
  "\<lambda>m. \<Union>(ran m)" .

lemma set_of_idx_code[code]:
  fixes t :: "('a :: ccompare, 'b set) mapping_rbt"
  shows "set_of_idx (RBT_Mapping t) =
    (case ID CCOMPARE('a) of None \<Rightarrow> Code.abort (STR ''set_of_idx RBT_Mapping: ccompare = None'') (\<lambda>_. set_of_idx (RBT_Mapping t))
    | Some _ \<Rightarrow> \<Union>(snd ` set (RBT_Mapping2.entries t)))"
  unfolding RBT_Mapping_def
  by transfer (auto simp: ran_def rbt_comp_lookup[OF ID_ccompare'] ord.is_rbt_def linorder.rbt_lookup_in_tree[OF comparator.linorder[OF ID_ccompare']] split: option.splits)+

lemma mem_set_of_idx: "z \<in> set_of_idx T \<longleftrightarrow> (\<exists>x Y. Mapping.lookup T x = Some Y \<and> z \<in> Y)"
  by transfer (auto simp: ran_def)

lemma mapping_combine[code]:
  fixes t :: "('a :: ccompare, 'b) mapping_rbt"
  shows "Mapping.combine f (RBT_Mapping t) (RBT_Mapping u) =
    (case ID CCOMPARE('a) of None \<Rightarrow> Code.abort (STR ''combine RBT_Mapping: ccompare = None'') (\<lambda>_. Mapping.combine f (RBT_Mapping t) (RBT_Mapping u))
    | Some _ \<Rightarrow> RBT_Mapping (RBT_Mapping2.join (\<lambda>_. f) t u))"
  by (auto simp add: Mapping.combine.abs_eq Mapping_inject lookup_join split: option.split)

lift_definition mapping_join :: "('b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) mapping \<Rightarrow> ('a, 'b) mapping \<Rightarrow> ('a, 'b) mapping" is
  "\<lambda>f m m' x. case m x of None \<Rightarrow> None | Some y \<Rightarrow> (case m' x of None \<Rightarrow> None | Some y' \<Rightarrow> Some (f y y'))" .

lemma mapping_join_code[code]:
  fixes t :: "('a :: ccompare, 'b) mapping_rbt"
  shows "mapping_join f (RBT_Mapping t) (RBT_Mapping u) =
    (case ID CCOMPARE('a) of None \<Rightarrow> Code.abort (STR ''mapping_join RBT_Mapping: ccompare = None'') (\<lambda>_. mapping_join f (RBT_Mapping t) (RBT_Mapping u))
    | Some _ \<Rightarrow> RBT_Mapping (RBT_Mapping2.meet (\<lambda>_. f) t u))"
  by (auto simp add: mapping_join.abs_eq Mapping_inject lookup_meet split: option.split)

lemma lookup_mapping_join: "Mapping.lookup (mapping_join f m m') x =
  (case Mapping.lookup m x of None \<Rightarrow> None
   | Some y \<Rightarrow> (case Mapping.lookup m' x of None \<Rightarrow> None | Some y' \<Rightarrow> Some (f y y')))"
  by (simp add: Mapping.lookup_def mapping_join.rep_eq split: option.splits)

context fixes dummy :: "'a :: ccompare" begin

lift_definition diff ::
  "('a, 'b) mapping_rbt \<Rightarrow> ('a, 'b) mapping_rbt \<Rightarrow> ('a, 'b) mapping_rbt" is "rbt_comp_minus ccomp"
  by (auto 4 3 intro: linorder.rbt_minus_is_rbt ID_ccompare ord.is_rbt_rbt_sorted simp: rbt_comp_minus[OF ID_ccompare'])

end

context assumes ID_ccompare_neq_None: "ID CCOMPARE('a :: ccompare) \<noteq> None"
begin

lemma lookup_diff:
  "RBT_Mapping2.lookup (diff (t1 :: ('a, 'b) mapping_rbt) t2) =
  (\<lambda>k. case RBT_Mapping2.lookup t1 k of None \<Rightarrow> None | Some v1 \<Rightarrow> (case RBT_Mapping2.lookup t2 k of None \<Rightarrow> Some v1 | Some v2 \<Rightarrow> None))"
  by transfer (auto simp add: fun_eq_iff linorder.rbt_lookup_rbt_minus[OF mapping_linorder] ID_ccompare_neq_None restrict_map_def split: option.splits)

end

lift_definition mapping_antijoin :: "('a, 'b) mapping \<Rightarrow> ('a, 'b) mapping \<Rightarrow> ('a, 'b) mapping" is
  "\<lambda>m m' x. case m x of None \<Rightarrow> None | Some y \<Rightarrow> (case m' x of None \<Rightarrow> Some y | Some y' \<Rightarrow> None)" .

lemma mapping_antijoin_code[code]:
  fixes t :: "('a :: ccompare, 'b) mapping_rbt"
  shows "mapping_antijoin (RBT_Mapping t) (RBT_Mapping u) =
    (case ID CCOMPARE('a) of None \<Rightarrow> Code.abort (STR ''mapping_antijoin RBT_Mapping: ccompare = None'') (\<lambda>_. mapping_antijoin (RBT_Mapping t) (RBT_Mapping u))
    | Some _ \<Rightarrow> RBT_Mapping (diff t u))"
  by (auto simp add: mapping_antijoin.abs_eq Mapping_inject lookup_diff split: option.split)

lemma lookup_mapping_antijoin: "Mapping.lookup (mapping_antijoin m m') x =
  (case Mapping.lookup m x of None \<Rightarrow> None
   | Some y \<Rightarrow> (case Mapping.lookup m' x of None \<Rightarrow> Some y | Some y' \<Rightarrow> None))"
  by (simp add: Mapping.lookup_def mapping_antijoin.rep_eq split: option.splits)

subsection \<open>Updates and deletions\<close>

lift_definition upd_set :: "('a, 'b) mapping \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> ('a, 'b) mapping" is
  "\<lambda>m f X a. if a \<in> X then Some (f a) else m a" .

lemma Mapping_lookup_upd_set: "Mapping.lookup (upd_set m f X) a =
  (if a \<in> X then Some (f a) else Mapping.lookup m a)"
  by (simp add: Mapping.lookup.rep_eq upd_set.rep_eq)

lemma upd_set_empty[simp]: "upd_set m f {} = m"
  by transfer auto

lemma upd_set_insert[simp]: "upd_set m f (Set.insert x A) = Mapping.update x (f x) (upd_set m f A)"
  by (rule mapping_eqI) (auto simp: Mapping_lookup_upd_set Mapping.lookup_update')

lemma upd_set_fold:
  assumes "finite A"
  shows "upd_set m f A = Finite_Set.fold (\<lambda>a. Mapping.update a (f a)) m A"
proof -
  interpret comp_fun_idem "\<lambda>a. Mapping.update a (f a)"
    by unfold_locales (transfer; auto simp: fun_eq_iff)+
  from assms show ?thesis
    by (induct A arbitrary: m rule: finite.induct) auto
qed

lift_definition upd_cfi :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, ('a, 'b) mapping) comp_fun_idem"
  is "\<lambda>f a m. Mapping.update a (f a) m"
  by unfold_locales (transfer; auto simp: fun_eq_iff)+

lemma upd_set_code[code]:
  "upd_set m f A = (if finite A then set_fold_cfi (upd_cfi f) m A else Code.abort (STR ''upd_set: infinite'') (\<lambda>_. upd_set m f A))"
  by (transfer fixing: m) (auto simp: upd_set_fold)

lemma Mapping_upd_set_keys: "Mapping.keys (upd_set m f X) = Mapping.keys m \<union> X"
  by (auto simp add: Mapping_lookup_upd_set dest!: Mapping.in_keysD intro: Mapping_keys_intro)

lemma Mapping_lookup_fold_upd_set_idle: "{(t, X) \<in> set xs. as \<in> Z X t} = {} \<Longrightarrow>
  Mapping.lookup (fold (\<lambda>(t, X) m. upd_set m (\<lambda>_. t) (Z X t)) xs m) as = Mapping.lookup m as"
proof (induction xs arbitrary: m)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  obtain x1 x2 where "x = (x1, x2)" by (cases x)
  have "Mapping.lookup (fold (\<lambda>(t, X) m. upd_set m (\<lambda>_. t) (Z X t)) xs (upd_set m (\<lambda>_. x1) (Z x2 x1))) as =
    Mapping.lookup (upd_set m (\<lambda>_. x1) (Z x2 x1)) as"
    using Cons by auto
  also have "Mapping.lookup (upd_set m (\<lambda>_. x1) (Z x2 x1)) as = Mapping.lookup m as"
    using Cons.prems by (auto simp: \<open>x = (x1, x2)\<close> Mapping_lookup_upd_set)
  finally show ?case by (simp add: \<open>x = (x1, x2)\<close>)
qed

lemma Mapping_keys_fold_upd_set: "k \<in> Mapping.keys (fold (\<lambda>(t, X) m. upd_set m (\<lambda>_. t) (Z t X))
  xs m) \<Longrightarrow> k \<in> Mapping.keys m \<or> (\<exists>(t, X) \<in> set xs. k \<in> Z t X)"
  by (induction xs arbitrary: m) (fastforce simp add: Mapping_upd_set_keys)+

definition mapping_delete_set :: "('a, 'b) mapping \<Rightarrow> 'a set \<Rightarrow> ('a, 'b) mapping" where
  "mapping_delete_set m X = Mapping.filter (\<lambda>k _. k \<notin> X) m"

lemma delete_set_lookup: "Mapping.lookup (mapping_delete_set m X) a = (if a \<in> X then
  None else Mapping.lookup m a)"
  by (auto simp: mapping_delete_set_def Mapping.lookup_filter split: option.splits)

lemma delete_set_keys[simp]: "Mapping.keys (mapping_delete_set m X) = Mapping.keys m - X"
  by (auto simp add: delete_set_lookup intro!: Mapping_keys_intro
      dest!: Mapping.in_keysD split: if_splits)

lemma mapping_delete_set_empty: "mapping_delete_set m {} = m"
  unfolding mapping_delete_set_def
  by (auto simp: Mapping_lookup_filter_Some intro!: mapping_eqI)

lemma mapping_delete_set_insert: "mapping_delete_set m (Set.insert a X) = Mapping.delete a (mapping_delete_set m X)"
proof(rule mapping_eqI)
  fix x
  show "Mapping.lookup (mapping_delete_set m (Set.insert a X)) x =
        Mapping.lookup (Mapping.delete a (mapping_delete_set m X)) x"
    unfolding Mapping_lookup_delete mapping_delete_set_def
    by (auto simp add: Mapping_lookup_filter_None)
       (metis (mono_tags, lifting) Mapping_lookup_filter_None Mapping_lookup_filter_Some)
qed

lemma mapping_delete_fold:
  assumes "finite A"
  shows "mapping_delete_set m A = Finite_Set.fold Mapping.delete m A"
proof -
  interpret comp_fun_idem "Mapping.delete" by(unfold_locales; transfer; simp add: fun_eq_iff)
  from assms show ?thesis
  proof (induction A arbitrary: m)
    case empty
    then show ?case using mapping_delete_set_empty by auto
  next
    case (insert a A)
    then show ?case using mapping_delete_set_insert[of m a A] fold_insert[OF insert(1-2), of m] by(simp)
  qed
qed

lift_definition mapping_delete_set_cfi :: "('a, ('a, 'b) mapping) comp_fun_idem" is
  Mapping.delete by(unfold_locales; transfer; simp add:fun_eq_iff)

lemma mapping_delete_set_code[code]:
  "mapping_delete_set m A = (if finite A then set_fold_cfi mapping_delete_set_cfi m A else Code.abort (STR ''mapping_delete_set: infinite'') (\<lambda>_. mapping_delete_set m A))"
  using mapping_delete_fold[of A m] by (simp add: mapping_delete_set_cfi.rep_eq set_fold_cfi.rep_eq)

definition remove_Union where
  "remove_Union A X B = A - (\<Union>x \<in> X. B x)"

lemma remove_Union_finite:
  assumes "finite X"
  shows "remove_Union A X B = Finite_Set.fold (\<lambda>x A. A - B x) A X"
proof -
  interpret comp_fun_idem "\<lambda>x A. A - B x"
    by unfold_locales auto
  from assms show ?thesis
    by (induct X arbitrary: A rule: finite_induct) (auto simp: remove_Union_def)
qed

lift_definition remove_Union_cfi :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('a, 'b set) comp_fun_idem" is "\<lambda>B x A. A - B x"
  by unfold_locales auto

lemma remove_Union_code[code]: "remove_Union A X B =
  (if finite X then set_fold_cfi (remove_Union_cfi B) A X else A - (\<Union>x \<in> X. B x))"
  by (transfer fixing: A X B) (use remove_Union_finite[of X A B] in \<open>auto simp add: remove_Union_def\<close>)

lift_definition update_mapping_with :: "('a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) mapping \<Rightarrow> ('a, 'b) mapping" is
  "\<lambda>f k v m. case m k of None \<Rightarrow> m(k \<mapsto> v) | Some v' \<Rightarrow> m(k \<mapsto> f k v' v)" .

lift_definition mapping_rbt_insertwk :: "('a::ccompare \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b 
  \<Rightarrow> ('a, 'b) mapping_rbt \<Rightarrow> ('a, 'b) mapping_rbt" is
  "rbt_comp_insert_with_key ccomp"
  by (auto 0 3 intro: linorder.rbt_insertwk_is_rbt ID_ccompare simp: rbt_comp_insert_with_key[OF ID_ccompare'])

declare [[code drop: update_mapping_with]]

lemma update_mapping_with_code[code]:
  fixes t :: "('a :: ccompare, 'b) mapping_rbt" shows
  "update_mapping_with f k v (RBT_Mapping t) =
  (case ID CCOMPARE('a) of None \<Rightarrow> Code.abort (STR ''update_mapping_with RBT_Mapping: ccompare = None'') (\<lambda>_. update_mapping_with f k v (RBT_Mapping t))
  | Some _ \<Rightarrow> RBT_Mapping (mapping_rbt_insertwk f k v t))"
  by (clarsimp split: option.split, transfer fixing: f k v)
    (auto simp add: rbt_comp_lookup[OF ID_ccompare'] rbt_comp_insert_with_key[OF ID_ccompare']
      linorder.rbt_lookup_rbt_insertwk[OF ID_ccompare] ord.is_rbt_rbt_sorted
      split: option.split)

lemma lookup_update_mapping_with:
  "Mapping.lookup (update_mapping_with f k v m) k' =
    (if k' = k then (case Mapping.lookup m k of None \<Rightarrow> Some v | Some v' \<Rightarrow> Some (f k v' v)) else Mapping.lookup m k')"
  by transfer (auto split: option.splits)

subsection \<open>Filtering by stored value\<close>

abbreviation "filter_cond X' ts t' \<equiv> (\<lambda>as _. \<not> (as \<in> X' \<and> Mapping.lookup ts as = Some t'))"

abbreviation "filter_cond' X' ts t' \<equiv> (\<lambda>as. \<not> (as \<in> X' \<and> Mapping.lookup ts as = Some t'))"

fun filter_set where "filter_set (t, X) (m, Y) =
  (let m' = Mapping.filter (filter_cond X m t) m in (m', Y \<union> (Mapping.keys m - Mapping.keys m')))"

declare filter_set.simps[simp del]

definition "filter_mapping m X t = Mapping.filter (filter_cond X m t) m"

lemma filter_mapping_empty[simp]: "filter_mapping m {} t = m"
  unfolding filter_mapping_def
  by transfer (auto simp: fun_eq_iff split: option.splits)

lemma filter_mapping_insert[simp]: "filter_mapping m (Set.insert x A) t = (let m' = filter_mapping m A t in
  case Mapping.lookup m' x of Some u \<Rightarrow> if t = u then Mapping.delete x m' else m' | _ \<Rightarrow> m')"
  unfolding filter_mapping_def
  by transfer (auto simp: fun_eq_iff Let_def split: option.splits)

lemma filter_mapping_fold:
  assumes "finite A"
  shows "filter_mapping m A t = Finite_Set.fold (\<lambda>a m.
    case Mapping.lookup m a of Some u \<Rightarrow> if t = u then Mapping.delete a m else m | _ \<Rightarrow> m) m A"
proof -
  interpret comp_fun_idem "\<lambda>a m.
    case Mapping.lookup m a of Some u \<Rightarrow> if t = u then Mapping.delete a m else m | _ \<Rightarrow> m"
    by unfold_locales
      (transfer; auto simp: fun_eq_iff split: option.splits)+
  from assms show ?thesis
    by (induct A arbitrary: m rule: finite.induct) (auto simp: Let_def)
qed

lift_definition filter_mapping_cfi :: "'b \<Rightarrow> ('a, ('a, 'b) mapping) comp_fun_idem"
  is "\<lambda>t a m.
    case Mapping.lookup m a of Some u \<Rightarrow> if t = u then Mapping.delete a m else m | _ \<Rightarrow> m"
  by unfold_locales
    (transfer; auto simp: fun_eq_iff split: option.splits)+

lemma filter_mapping_code[code]:
  "filter_mapping m A t = (if finite A then set_fold_cfi (filter_mapping_cfi t) m A else Code.abort (STR ''filter_mapping: infinite'') (\<lambda>_. filter_mapping m A t))"
  by (transfer fixing: m) (auto simp: filter_mapping_fold)

definition "filter_set' Z m X t = {as \<in> Z. filter_cond' X m t as}"

lemma filter_set'_empty[simp]: "filter_set' Z m {} t = Z"
  unfolding filter_set'_def
  by transfer (auto simp: fun_eq_iff split: option.splits)

lemma filter_set'_insert[simp]: "filter_set' Z m (Set.insert x A) t = (let Z' = filter_set' Z m A t in
  case Mapping.lookup m x of Some u \<Rightarrow> if t = u then Z' - {x} else Z' | _ \<Rightarrow> Z')"
  unfolding filter_set'_def
  by transfer (auto simp: Let_def split: option.splits)

lemma filter_set'_fold:
  assumes "finite A"
  shows "filter_set' Z m A t = Finite_Set.fold (\<lambda>a Z'.
    case Mapping.lookup m a of Some u \<Rightarrow> if t = u then Z' - {a} else Z' | _ \<Rightarrow> Z') Z A"
proof -
  interpret comp_fun_idem "\<lambda>a Z'.
    case Mapping.lookup m a of Some u \<Rightarrow> if t = u then Z' - {a} else Z' | _ \<Rightarrow> Z'"
    by unfold_locales
      (transfer; auto simp: fun_eq_iff split: option.splits)+
  from assms show ?thesis
    by (induct A arbitrary: Z rule: finite.induct) (auto simp: Let_def)
qed

lift_definition filter_set_cfi :: "('a, 'b) mapping \<Rightarrow> 'b \<Rightarrow> ('a, 'a set) comp_fun_idem"
  is "\<lambda>m t a Z'.
    case Mapping.lookup m a of Some u \<Rightarrow> if t = u then Z' - {a} else Z' | _ \<Rightarrow> Z'"
  by (unfold_locales, transfer) (fastforce simp: comp_def split: option.splits)+

lemma filter_set'_code[code]:
  "filter_set' Z m A t = (if finite A then set_fold_cfi (filter_set_cfi m t) Z A else Code.abort (STR ''filter_set: infinite'') (\<lambda>_. filter_set' Z m A t))"
  by transfer (auto simp: filter_set'_fold)

lemma filter_set_empty[simp]: "filter_set (t, {}) (m, Y) = (m, Y)"
  unfolding filter_set.simps
  by transfer (auto simp: Let_def fun_eq_iff split: option.splits)

lemma filter_set_insert[simp]: "filter_set (t, Set.insert x A) (m, Y) = (let (m', Y') = filter_set (t, A) (m, Y) in
  case Mapping.lookup m' x of Some u \<Rightarrow> if t = u then (Mapping.delete x m', Y' \<union> {x}) else (m', Y') | _ \<Rightarrow> (m', Y'))"
  unfolding filter_set.simps
  by transfer (auto simp: fun_eq_iff Let_def split: option.splits)

lemma filter_set_fold:
  assumes "finite A"
  shows "filter_set (t, A) (m, Y) = Finite_Set.fold (\<lambda>a (m, Y).
    case Mapping.lookup m a of Some u \<Rightarrow> if t = u then (Mapping.delete a m, Y \<union> {a}) else (m, Y) | _ \<Rightarrow> (m, Y)) (m, Y) A"
proof -
  interpret comp_fun_idem "\<lambda>a (m, Y).
    case Mapping.lookup m a of Some u \<Rightarrow> if t = u then (Mapping.delete a m, Y \<union> {a}) else (m, Y) | _ \<Rightarrow> (m, Y)"
    by unfold_locales
      (transfer; auto simp: fun_eq_iff split: option.splits)+
  from assms show ?thesis
    by (induct A arbitrary: m rule: finite.induct) (auto simp: Let_def)
qed

lift_definition filter_cfi :: "'b \<Rightarrow> ('a, ('a, 'b) mapping \<times> 'a set) comp_fun_idem"
  is "\<lambda>t a (m, Y).
    case Mapping.lookup m a of Some u \<Rightarrow> if t = u then (Mapping.delete a m, Y \<union> {a}) else (m, Y) | _ \<Rightarrow> (m, Y)"
  by unfold_locales (transfer; auto simp: fun_eq_iff split: option.splits)+

lemma filter_set_code[code]:
  "filter_set (t, A) (m, Y) = (if finite A then set_fold_cfi (filter_cfi t) (m, Y) A else Code.abort (STR ''upd_set: infinite'') (\<lambda>_. filter_set (t, A) (m, Y)))"
  by (transfer fixing: m) (auto simp: filter_set_fold)

subsection \<open>Nested updates\<close>

lift_definition upd_set' :: "('a, 'b) mapping \<Rightarrow> 'b \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> ('a, 'b) mapping" is
  "\<lambda>m d f X a. (if a \<in> X then (case Mapping.lookup m a of Some b \<Rightarrow> Some (f b) | None \<Rightarrow> Some d)
    else Mapping.lookup m a)" .

lemma upd_set'_lookup: "Mapping.lookup (upd_set' m d f X) a = (if a \<in> X then
  (case Mapping.lookup m a of Some b \<Rightarrow> Some (f b) | None \<Rightarrow> Some d) else Mapping.lookup m a)"
  by (simp add: Mapping.lookup.rep_eq upd_set'.rep_eq)

lemma upd_set'_keys: "Mapping.keys (upd_set' m d f X) = Mapping.keys m \<union> X"
  by (auto simp add: upd_set'_lookup intro!: Mapping_keys_intro
      dest!: Mapping.in_keysD split: option.splits)

lemma upd_set'_insert_dq: "d = f d \<Longrightarrow> (\<And>x. f (f x) = f x) \<Longrightarrow> upd_set' m d f (Set.insert x A) =
  (let m' = (upd_set' m d f A) in case Mapping.lookup m' x of None \<Rightarrow> Mapping.update x d m'
  | Some v \<Rightarrow> Mapping.update x (f v) m')"
  by (rule mapping_eqI) (auto simp: upd_set'_lookup Mapping.lookup_update' split: option.splits)

lemma upd_set'_aux1: "upd_set' Mapping.empty d f {b. b = k \<or> (a, b) \<in> A} =
  Mapping.update k d (upd_set' Mapping.empty d f {b. (a, b) \<in> A})"
  by (rule mapping_eqI) (auto simp add: Let_def upd_set'_lookup Mapping.lookup_update'
      split: option.splits)

lemma upd_set'_aux2: "Mapping.lookup m k = None \<Longrightarrow> upd_set' m d f {b. b = k \<or> (a, b) \<in> A} =
  Mapping.update k d (upd_set' m d f {b. (a, b) \<in> A})"
  by (rule mapping_eqI) (auto simp add: upd_set'_lookup Mapping.lookup_update' split: option.splits)

lemma upd_set'_aux3: "Mapping.lookup m k = Some v \<Longrightarrow> upd_set' m d f {b. b = k \<or> (a, b) \<in> A} =
  Mapping.update k (f v) (upd_set' m d f {b. (a, b) \<in> A})"
  by (rule mapping_eqI) (auto simp add: upd_set'_lookup Mapping.lookup_update' split: option.splits)

lemma upd_set'_aux4: "k \<notin> fst ` A \<Longrightarrow> upd_set' Mapping.empty d f {b. (k, b) \<in> A} = Mapping.empty"
  by (rule mapping_eqI) (auto simp add: upd_set'_lookup Mapping.lookup_update' Domain.DomainI fst_eq_Domain
      split: option.splits)

lemma upd_set'_empty[simp]: "upd_set' m d f {} = m"
  by (rule mapping_eqI) (auto simp add: upd_set'_lookup)

lift_definition upd_nested :: "('a, ('b, 'c) mapping) mapping \<Rightarrow>
  'c \<Rightarrow> ('c \<Rightarrow> 'c) \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> ('a, ('b, 'c) mapping) mapping" is
  "\<lambda>m d f X a. case Mapping.lookup m a of Some m' \<Rightarrow> Some (upd_set' m' d f {b. (a, b) \<in> X})
  | None \<Rightarrow> if a \<in> fst ` X then Some (upd_set' Mapping.empty d f {b. (a, b) \<in> X}) else None" .

lemma upd_nested_lookup: "Mapping.lookup (upd_nested m d f X) a =
  (case Mapping.lookup m a of Some m' \<Rightarrow> Some (upd_set' m' d f {b. (a, b) \<in> X})
  | None \<Rightarrow> if a \<in> fst ` X then Some (upd_set' Mapping.empty d f {b. (a, b) \<in> X}) else None)"
  by (simp add: Mapping.lookup.abs_eq upd_nested.abs_eq)

lemma upd_nested_keys: "Mapping.keys (upd_nested m d f X) = Mapping.keys m \<union> fst ` X"
  by (auto simp add: upd_nested_lookup Domain.DomainI fst_eq_Domain intro!: Mapping_keys_intro
      dest!: Mapping.in_keysD split: option.splits)

definition upd_nested_step :: "'c \<Rightarrow> ('c \<Rightarrow> 'c) \<Rightarrow> 'a \<times> 'b \<Rightarrow> ('a, ('b, 'c) mapping) mapping \<Rightarrow>
  ('a, ('b, 'c) mapping) mapping" where
  "upd_nested_step d f x m = (case x of (k, k') \<Rightarrow>
    (case Mapping.lookup m k of Some m' \<Rightarrow>
      (case Mapping.lookup m' k' of Some v \<Rightarrow> Mapping.update k (Mapping.update k' (f v) m') m
      | None \<Rightarrow> Mapping.update k (Mapping.update k' d m') m)
    | None \<Rightarrow> Mapping.update k (Mapping.update k' d Mapping.empty) m))"

lemma upd_nested_empty[simp]: "upd_nested m d f {} = m"
  by (rule mapping_eqI)
    (clarsimp simp: upd_nested_def Mapping.lookup.abs_eq split: option.splits)

lemma upd_nested_insert:
  "d = f d \<Longrightarrow> (\<And>x. f (f x) = f x) \<Longrightarrow> upd_nested m d f (Set.insert x A) =
  upd_nested_step d f x (upd_nested m d f A)"
  unfolding upd_nested_step_def
  using upd_set'_aux1[of d f _ _ A] upd_set'_aux2[of _ _ d f _ A] upd_set'_aux3[of _ _ _ d f _ A]
    upd_set'_aux4[of _ A d f]
  by (auto simp add: Let_def upd_nested_lookup upd_set'_lookup Mapping.lookup_update'
      split: option.splits prod.splits if_splits intro!: mapping_eqI)

definition to_add_set where
  "to_add_set a m tmp = {b. (a, b) \<in> tmp \<and> Mapping.lookup m b = None}"

definition to_add_set_fun :: "'b \<Rightarrow> ('a, 'c) mapping \<Rightarrow> 'b \<times> 'a \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "to_add_set_fun a m elem s = (if a = fst elem \<and> Mapping.lookup m (snd elem) = None then Set.insert (snd elem) s else s)"

lemma to_add_set_empty: "to_add_set a m {} = {}"
  unfolding to_add_set_def by auto

lemma to_add_set_fold:
  assumes "finite tmp"
  shows "to_add_set a m tmp = Finite_Set.fold (to_add_set_fun a m) {} tmp"
proof -
  interpret comp_fun_idem "to_add_set_fun a m"
    by(unfold_locales) (auto simp:to_add_set_fun_def comp_def split:if_splits)
  from assms show ?thesis
  proof (induction tmp)
    case empty
    then show ?case using to_add_set_empty[of a m] by simp
  next
    case (insert a A)
    show ?case unfolding fold_insert[OF insert(1-2)] insert(3)[symmetric] unfolding to_add_set_def to_add_set_fun_def
      by transfer auto
   qed 
 qed

lift_definition to_add_set_cfi :: "'b \<Rightarrow> ('a, 'c) mapping \<Rightarrow> (('b \<times> 'a), 'a set) comp_fun_idem" is 
  "\<lambda>a m. to_add_set_fun a m" by(unfold_locales) (auto simp:to_add_set_fun_def comp_def split:if_splits)

lemma to_add_set_code[code]: "to_add_set a m tmp = (if finite tmp then set_fold_cfi (to_add_set_cfi a m) {} tmp else Code.abort (STR ''to_add_set: infinite set'') (\<lambda>_. to_add_set a m tmp))"
  using to_add_set_fold[of tmp a m] by transfer auto

end
