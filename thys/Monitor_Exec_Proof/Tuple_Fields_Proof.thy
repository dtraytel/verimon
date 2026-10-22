(*<*)
theory Tuple_Fields_Proof
  imports "Monitor_Exec.Tuple_Fields" "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



lemma csl_finite: "finite X \<Longrightarrow> csl X = csorted_list_of_set X"
  by (simp add: csl_def)

lemma csl_infinite: "\<not> finite X \<Longrightarrow> csl X = []"
  by (simp add: csl_def)

lemma set_csl_ed: "finite (X :: event_data list set) \<Longrightarrow> set (csl X) = X"
  using ID_ccompare_ed by (simp add: csl_finite) (subst csorted_list_of_set_split, auto)

lemma umatch_match: "umatch tms xs = match tms xs"
  by (induct tms xs rule: umatch.induct) auto

lemma these_map_option_image: "Option.these (map_option g ` S) = g ` Option.these S"
  by (force simp: Option.these_def image_iff)

lemma uagg_values:
  "uagg_values f G = (\<lambda>v. (v, ecard (Set.filter (\<lambda>x. umeval_trm f x = v) G))) ` umeval_trm f ` G"
  unfolding uagg_values_def Let_def keys_cluster
  by (intro image_cong[OF refl]) (simp add: lookup_cluster_Some)

(*<*)
end
(*>*)
