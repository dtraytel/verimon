(*<*)
theory Agg_Gen_Proof
  imports "Monitor_Exec.Agg_Gen" Window_Proof Frame_Aux_Proof "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



subsection \<open>Folds that drop the structure\<close>

text \<open>The kernel's steps carry a flag and keep folding once it is down; the steps here stop at
  the first failure.  The two agree, and a fold of steps that commute with a map @{text R} is
  the map of the fold.  The keys a fold leaves are the ones it started with and the groups of
  the tuples it inserted.\<close>

lemma gins_None[simp]: "gins k ev xs None = None"
  by (induct xs) (simp_all add: gins_def gstep_ins_def)

lemma gdel_None[simp]: "gdel k ev xs None = None"
  by (induct xs) (simp_all add: gdel_def gstep_del_def)

lemma fold_gstep_None[simp]:
  "fold (gstep_ins k ev) xs None = None" "fold (gstep_del k ev) xs None = None"
  using gins_None gdel_None by (simp_all add: gins_def gdel_def)

(*<*)
end
(*>*)
