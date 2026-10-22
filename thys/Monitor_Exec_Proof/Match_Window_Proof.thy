(*<*)
theory Match_Window_Proof
  imports "Monitor_Exec.Match_Window" Frame_Aux_Proof Until_Gen_Proof "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



text \<open>The window's lookup and tabulation are the kernel's.\<close>

subsection \<open>The lax epsilon\<close>

context eregex_frame
begin

end

subsection \<open>The past-match window\<close>

context ematchP_frame
begin

end

subsection \<open>The future-match window\<close>

context ematchF_frame
begin

end

(*<*)
end
(*>*)
