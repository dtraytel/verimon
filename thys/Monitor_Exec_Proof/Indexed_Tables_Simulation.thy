(*<*)
theory Indexed_Tables_Simulation
  imports "Monitor_Exec.Indexed_Tables" Exec_Until_Simulation "Monitor_Impl_Proof.Monitor_Instance_Valid"
begin
(*>*)



lemma iensure_has:
  "msk \<in> set msks \<Longrightarrow> Mapping.lookup (iidxs (iensure msks A)) msk \<noteq> None"
  by (simp add: iidxs_def Rep_itab_iensure lookup_fold_iensure1)

lemma iidxs_iupd_None: "Mapping.lookup (iidxs (iupd X D A)) msk = None \<longleftrightarrow>
    Mapping.lookup (iidxs A) msk = None"
  by (simp add: iidxs_def Rep_itab_iupd Mapping.lookup_map_values)


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
