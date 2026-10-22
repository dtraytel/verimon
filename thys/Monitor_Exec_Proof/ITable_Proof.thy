(*<*)
theory ITable_Proof
  imports "Monitor_Exec.ITable" Idx_Code_Proof "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



lemma iidxs_eidx: "Mapping.lookup (iidxs A) msk = Some m \<Longrightarrow> m = eidx msk (iset A)"
  using Rep_itab[of A] by (auto simp: iinv_def iset_def iidxs_def)

lemma Rep_itab_inverse': "iinv TI \<Longrightarrow> Rep_itab (Abs_itab TI) = TI"
  by (simp add: Abs_itab_inverse)

lemma lookup_fold_iensure1:
  "Mapping.lookup (fold (iensure1 T) msks I) msk =
     (if msk \<in> set msks \<and> Mapping.lookup I msk = None then Some (eidx msk T)
      else Mapping.lookup I msk)"
  by (induct msks arbitrary: I)
    (auto simp: iensure1_def Mapping.lookup_update' split: option.splits)

lemma iensure_has:
  "msk \<in> set msks \<Longrightarrow> Mapping.lookup (iidxs (iensure msks A)) msk \<noteq> None"
  by (simp add: iidxs_def Rep_itab_iensure lookup_fold_iensure1)

lemma iidxs_iupd_None: "Mapping.lookup (iidxs (iupd X D A)) msk = None \<longleftrightarrow>
    Mapping.lookup (iidxs A) msk = None"
  by (simp add: iidxs_def Rep_itab_iupd Mapping.lookup_map_values)


text \<open>Inserting and removing one tuple visits one bucket of each index.\<close>

lemma eidx_insert: "eidx msk (Set.insert x T) = eidx_add1 msk x (eidx msk T)"
  by (rule mapping_eqI) (auto simp: lookup_eidx lookup_eidx_add1 ebucket_def image_iff)

lemma eidx_remove: "eidx msk (T - {x}) = eidx_del1 msk x (eidx msk T)"
proof (rule mapping_eqI)
  fix k
  have b: "ebucket (eidx msk T) k = {y \<in> T. eproj msk y = k}"
    by (auto simp: ebucket_def lookup_eidx)
  show "Mapping.lookup (eidx msk (T - {x})) k = Mapping.lookup (eidx_del1 msk x (eidx msk T)) k"
  proof (cases "k = eproj msk x")
    case True
    have "{y \<in> T. eproj msk y = k} - {x} = {y \<in> T - {x}. eproj msk y = k}"
      and "(k \<in> eproj msk ` (T - {x})) = ({y \<in> T - {x}. eproj msk y = k} \<noteq> {})"
      by auto
    then show ?thesis using True by (simp add: lookup_eidx lookup_eidx_del1 b[unfolded True])
  next
    case False
    have "(k \<in> eproj msk ` (T - {x})) = (k \<in> eproj msk ` T)"
      and "{y \<in> T - {x}. eproj msk y = k} = {y \<in> T. eproj msk y = k}"
      using False by auto
    then show ?thesis using False by (simp add: lookup_eidx lookup_eidx_del1)
  qed
qed

text \<open>A table without indices, which is most tables, is updated without visiting its (empty)
  map of indices.\<close>

lemma map_values_no_keys: "Mapping.keys m = {} \<Longrightarrow> Mapping.map_values f m = m"
  by (rule mapping_eqI) (auto simp: Mapping.lookup_map_values Mapping.keys_dom_lookup split: option.splits)

lemma Rep_itab_iadd: "Rep_itab (iadd X A) =
    (iset A \<union> X, Mapping.map_values (\<lambda>msk m. eidx_union m (eidx msk X)) (iidxs A))"
  unfolding iadd_def
  by (rule Rep_itab_inverse')
    (auto simp: iinv_def Mapping.lookup_map_values eidx_union_eq dest: iidxs_eidx)

lemma Rep_itab_isub: "Rep_itab (isub D A) =
    (iset A - D, Mapping.map_values (\<lambda>msk m. eidx_minus m (eidx msk D)) (iidxs A))"
  unfolding isub_def
  by (rule Rep_itab_inverse')
    (auto simp: iinv_def Mapping.lookup_map_values eidx_minus_eq dest: iidxs_eidx)

text \<open>An indexed table is determined by its set and the masks of its indices.\<close>

lemma itab_eqI:
  assumes "iset A = iset B" "Mapping.keys (iidxs A) = Mapping.keys (iidxs B)"
  shows "A = B"
proof -
  have "iidxs A = iidxs B"
  proof (rule mapping_eqI)
    fix msk
    show "Mapping.lookup (iidxs A) msk = Mapping.lookup (iidxs B) msk"
    proof (cases "msk \<in> Mapping.keys (iidxs A)")
      case True
      then have "Mapping.lookup (iidxs A) msk \<noteq> None" "Mapping.lookup (iidxs B) msk \<noteq> None"
        using assms(2) by (auto simp: Mapping.keys_dom_lookup)
      then obtain m m' where a: "Mapping.lookup (iidxs A) msk = Some m"
        and b: "Mapping.lookup (iidxs B) msk = Some m'" by blast
      show ?thesis using a b iidxs_eidx[OF a] iidxs_eidx[OF b] assms(1) by simp
    next
      case False
      then show ?thesis using assms(2) by (auto simp: Mapping.keys_dom_lookup)
    qed
  qed
  then show ?thesis using assms(1)
    by (metis Rep_itab_inject iidxs_def iset_def prod.expand)
qed

lemma isub_isub: "isub D2 (isub D1 A) = isub (D1 \<union> D2) A"
  by (rule itab_eqI) auto

lemma fold_union_image: "fold (\<lambda>x acc. acc \<union> f x) l acc = acc \<union> (\<Union>x \<in> set l. f x)"
  by (induct l arbitrary: acc) auto

lemma ebucket_eidx: "ebucket (eidx msk T) k = {y \<in> T. eproj msk y = k}"
  by (auto simp: ebucket_def lookup_eidx)

lemma iprobe_eq:
  "set (csl A) = A \<Longrightarrow>
   iprobe p lk (eidx rk B) A = {emerge p a b | a b. a \<in> A \<and> b \<in> B \<and> eproj lk a = eproj rk b}"
  by (auto simp: iprobe_def fold_union_image ebucket_eidx) metis

lemma iprobe_l_eq:
  "set (csl B) = B \<Longrightarrow>
   iprobe_l p rk (eidx lk A) B = {emerge p a b | a b. a \<in> A \<and> b \<in> B \<and> eproj lk a = eproj rk b}"
  by (simp add: iprobe_l_def fold_union_image ebucket_eidx) blast

text \<open>The test of finiteness costs nothing on the tree-based sets of the Containers framework,
  which are finite by construction.\<close>

theorem ijoin0_eq:
  fixes A B :: "event_data itab"
  shows "ijoin0 pl A pos B = gbin_join0 pl (iset A) pos (iset B)"
proof (cases pl)
  case (EJSub msk)
  then show ?thesis
    by (cases pos; cases "Mapping.lookup (iidxs A) msk")
      (auto simp: esemi_idx_dsemi dest!: iidxs_eidx)
next
  case (EJSup msk)
  then show ?thesis
    by (cases pos; cases "Mapping.lookup (iidxs B) msk")
      (auto simp: esemi_idx_dsemi esemi_def dest!: iidxs_eidx)
next
  case (EJGen p lk rk)
  show ?thesis
  proof (cases "pos \<and> finite (iset A) \<and> finite (iset B)")
    case True
    then have cA: "set (csl (iset A)) = iset A" and cB: "set (csl (iset B)) = iset B"
      by (simp_all add: set_csl_ed)
    show ?thesis
      using EJGen True
      apply (cases "Mapping.lookup (iidxs B) rk"; cases "Mapping.lookup (iidxs A) lk")
         apply (auto simp: iprobe_eq[OF cA] iprobe_l_eq[OF cB] ggen_join_eq[OF cA cB] dest!: iidxs_eidx)
      apply blast+
      done
  next
    case False
    then show ?thesis
      using EJGen by (simp only: ijoin0.simps if_not_P[OF False] if_False)
  qed
qed simp_all

theorem ijoin_eq:
  fixes A B :: "event_data itab"
  shows "ijoin pl A pos B = gbin_join pl (iset A) pos (iset B)"
  using ijoin0_eq by (simp add: ijoin_def gbin_join_def)
(*<*)
end
(*>*)
