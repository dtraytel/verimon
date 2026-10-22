(*<*)
theory Map_Upd_Code_Proof
  imports "Monitor_Exec.Map_Upd_Code" Agg_Code_Proof "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



context
  fixes c :: "'a comparator"
begin

end

context
  fixes c :: "'a comparator"
begin

end

text \<open>The window's steps of @{theory MFODL_Monitor_Exec.Agg_Cache} pass the aggregate's
  step to @{const cstep} as an argument, where the redirection to its copy at the short tuples
  below does not reach it; these name the two instances with the step applied.\<close>

text \<open>The steps of @{theory MFODL_Monitor_Exec.Agg_Gen} are generic in the element
  type, and their generated code built the comparator of the key lists at every lookup; these are
  their copies at @{typ event_data}, whose mapping operations the specialised ones take over.\<close>

end
(*>*)
