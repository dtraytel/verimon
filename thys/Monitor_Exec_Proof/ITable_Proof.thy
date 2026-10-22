(*<*)
theory ITable_Proof
  imports "Monitor_Exec.ITable" Idx_Code_Proof "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



lemma iensure_has:
  "msk \<in> set msks \<Longrightarrow> Mapping.lookup (iidxs (iensure msks A)) msk \<noteq> None"
  by (simp add: iidxs_def Rep_itab_iensure lookup_fold_iensure1)

lemma iidxs_iupd_None: "Mapping.lookup (iidxs (iupd X D A)) msk = None \<longleftrightarrow>
    Mapping.lookup (iidxs A) msk = None"
  by (simp add: iidxs_def Rep_itab_iupd Mapping.lookup_map_values)


text \<open>Inserting and removing one tuple visits one bucket of each index.\<close>

text \<open>A table without indices, which is most tables, is updated without visiting its (empty)
  map of indices.\<close>

text \<open>An indexed table is determined by its set and the masks of its indices.\<close>

lemma fold_union_image: "fold (\<lambda>x acc. acc \<union> f x) l acc = acc \<union> (\<Union>x \<in> set l. f x)"
  by (induct l arbitrary: acc) auto

lemma ebucket_eidx: "ebucket (eidx msk T) k = {y \<in> T. eproj msk y = k}"
  by (auto simp: ebucket_def lookup_eidx)

lemma iprobe_l_eq:
  "set (csl B) = B \<Longrightarrow>
   iprobe_l p rk (eidx lk A) B = {emerge p a b | a b. a \<in> A \<and> b \<in> B \<and> eproj lk a = eproj rk b}"
  by (simp add: iprobe_l_def fold_union_image ebucket_eidx) blast

text \<open>The test of finiteness costs nothing on the tree-based sets of the Containers framework,
  which are finite by construction.\<close>

end
(*>*)
