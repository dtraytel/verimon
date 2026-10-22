(*<*)
theory Tuple_Code_Proof
  imports "Monitor_Exec.Tuple_Code" Compile_Proof Idx_Code_Proof "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



text \<open>The match of a predicate's table against the atom's terms is an image followed by
  @{const Option.these}, which the generated code ran through the generic set operations with
  their dictionaries; on a tree it is one fold that inserts the matches.\<close>

lemma these_image_fold:
  "fold (\<lambda>x acc. case u x of None \<Rightarrow> acc | Some f \<Rightarrow> Set.insert (h f) acc) xs A
   = A \<union> Option.these ((\<lambda>x. map_option h (u x)) ` set xs)"
  by (induct xs arbitrary: A) (auto split: option.splits)

end
(*>*)
