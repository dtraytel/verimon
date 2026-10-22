(*<*)
theory Agg_Code_Proof
  imports "Monitor_Exec.Agg_Code" Mono_Sweep_Proof "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



text \<open>
  The aggregation over a window keeps one order-statistic tree per group for MIN, MAX and MED
  (@{typ list_aux}, over @{typ "'a treelist"}, over @{typ "'a wf_wbt"}).  Its operations are
  refined here at the level of code equations, with the refinements proved against the
  equations they replace.  They are placed after
  @{theory MFODL_Monitor_Exec.Mono_Sweep} so that the theory lies on the import chain
  of the export rather than beside it: a side branch would bring back, at the merge, the code
  preprocessor rules that the theories in between delete.
\<close>

text \<open>@{theory MFODL_Monitor_Exec.Mono_Sweep} specialises the treelist operations at
  @{typ integer} and @{typ string8}, but their bodies still called the generic tree operations
  with a dictionary, and the generic @{const cmp} goes through the dictionary's @{text less} and
  @{text equal} at every node.  These are the tree operations' copies at the two types, and the
  @{typ nat} comparison of @{const select}.\<close>

end
(*>*)
