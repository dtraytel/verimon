(*<*)
theory Idx_Code_Proof
  imports "Monitor_Exec.Idx_Code" Until_Gen_Proof "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



text \<open>The entries whose keys fail are collected by a fold over the index that conses only
  them, not by filtering the list of all its entries, which the join would build at every time
  point however few keys drop out.  The fold collects them in reverse order, so they are
  processed by a right fold.\<close>

end
(*>*)
