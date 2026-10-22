(*<*)
theory Tuple_Fields_Proof
  imports "Monitor_Exec.Tuple_Fields" "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



lemma umatch_match: "umatch tms xs = match tms xs"
  by (induct tms xs rule: umatch.induct) auto

lemma these_map_option_image: "Option.these (map_option g ` S) = g ` Option.these S"
  by (force simp: Option.these_def image_iff)

end
(*>*)
