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


text \<open>The test of finiteness costs nothing on the tree-based sets of the Containers framework,
  which are finite by construction.\<close>

end
(*>*)
