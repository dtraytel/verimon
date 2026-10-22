(*<*)
theory Tuple_Code_Proof
  imports "Monitor_Exec.Tuple_Code" Compile_Proof Idx_Code_Proof "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



text \<open>The match of a predicate's table against the atom's terms is an image followed by
  @{const Option.these}, which the generated code ran through the generic set operations with
  their dictionaries; on a tree it is one fold that inserts the matches.\<close>

end
(*>*)
