(*<*)
theory Window_Dispatch_Proof
  imports "Monitor_Exec.Window_Dispatch" Agg_Cache_Proof Match_Window_Proof "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



lemma esx_init_rdsx: "esx_init args msk = rdsx (udsx_init args msk)"
  by (simp add: esx_init_def udsx_init_def)

lemma esx_init_agg_rdsx[simp]: "rdsx (udsx_init_agg args p q) = esx_init_agg args p"
  by (simp add: esx_init_agg_def udsx_init_agg_def sa_init_rsc[symmetric])

text \<open>The structure above reports the node's whole result; this one reports it read through the
  guard straight away.\<close>

lemma eux_init_rdux: "eux_init args = rdux (udux_init args)"
  by (simp add: eux_init_def udux_init_def)

lemma eux_init_agg_rdux: "eux_init_agg args p = rdux (udux_init_agg args p)"
  by (simp add: eux_init_agg_def udux_init_agg_def rua_init)

text \<open>The traversal commutes with the representations: the traversal of
  @{const esx_eval_since} on the images reports the same results, read through the node's guard.
  The accumulator is carried the same way, so the statement relates the two lists it is started
  with.\<close>

subsection \<open>The Until buffer's traversal, and the two buffers of the fused And-Trigger\<close>

end
(*>*)
