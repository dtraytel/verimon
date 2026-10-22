(*<*)
theory Release_Window_Proof
  imports "Monitor_Exec.Release_Window" Frame_Aux_Proof "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



subsection \<open>The summaries\<close>

lemma esemi_Int: "esemi msk b (A \<inter> r) l = A \<inter> esemi msk b r l"
  by (auto simp: esemi_def)

lemma esemi_sub: "esemi msk b r l \<subseteq> r"
  by (auto simp: esemi_def)

text \<open>An entry the list updates is the composition of its summary with the new point's.\<close>

end
(*>*)
