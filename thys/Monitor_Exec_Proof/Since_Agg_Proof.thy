(*<*)
theory Since_Agg_Proof
  imports "Monitor_Exec.Since_Agg" Window_Proof Frame_Aux_Proof Agg_Gen_Proof "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



text \<open>The parameters the compiler builds from a fused node's aggregation are well formed at the
  width of the node's operand.\<close>

text \<open>The kernel reads a window's tuple at the frame: its group key is the tuple's suffix after
  the bound columns, and the shifted term evaluates to the term on the tuple.\<close>

text \<open>The executable aggregation is the kernel's aggregation at the ascending frame, with the result
  column moved into place.\<close>

subsubsection \<open>The scans, and what the window's validity says about its tables\<close>

subsubsection \<open>Validity\<close>

lemma lookup_None_keys: "(Mapping.lookup c t = None) = (t \<notin> Mapping.keys c)"
  by (simp add: Mapping.keys_dom_lookup domIff)

lemma cnt_add1_ucc: "cnt_add1 t (ucc c) = ucc (ucnt_add1 t c)"
proof (cases "Mapping.lookup c t")
  case None
  then show ?thesis by (simp add: cnt_add1_def ucnt_add1_def ucc.simps)
next
  case (Some k)
  have "t \<in> Mapping.keys c" using Some lookup_None_keys[of c t] by simp
  with Some show ?thesis by (simp add: cnt_add1_def ucnt_add1_def ucc.simps insert_absorb)
qed

lemma cnt_del1_ucc: "cnt_del1 t (ucc c) = ucc (ucnt_del1 t c)"
proof (cases "Mapping.lookup c t")
  case None
  then show ?thesis by (simp add: cnt_del1_def ucnt_del1_def ucc.simps)
next
  case (Some k)
  have "t \<in> Mapping.keys c" using Some lookup_None_keys[of c t] by simp
  with Some show ?thesis
    by (simp add: cnt_del1_def ucnt_del1_def ucc.simps insert_absorb)
qed

lemma fold_cnt_add1_ucc: "fold cnt_add1 xs (ucc c) = ucc (fold ucnt_add1 xs c)"
  by (induct xs arbitrary: c) (simp_all add: cnt_add1_ucc)

lemma fold_cnt_del1_ucc: "fold cnt_del1 xs (ucc c) = ucc (fold ucnt_del1 xs c)"
  by (induct xs arbitrary: c) (simp_all add: cnt_del1_ucc)

lemma cnt_add_ucc[simp]: "cnt_add T (ucc c) = ucc (ucnt_add T c)"
  by (simp add: cnt_add_def ucnt_add_def fold_cnt_add1_ucc)

lemma cnt_del_ucc[simp]: "cnt_del T (ucc c) = ucc (ucnt_del T c)"
  by (simp add: cnt_del_def ucnt_del_def fold_cnt_del1_ucc)

lemma ag_ins_ucc[simp]: "ag_ins p w T (ucc c) ax = uag_ins p w T c ax"
  by (cases p) (simp add: ag_ins_def uag_ins_def ucc.simps lookup_None_keys)

end
(*>*)
