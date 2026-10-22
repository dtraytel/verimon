(*<*)
theory Mapping_Facts
  imports "HOL-Library.Mapping"
begin
(*>*)

section \<open>Facts about mappings\<close>

lemma Mapping_keys_intro: "Mapping.lookup f x \<noteq> None \<Longrightarrow> x \<in> Mapping.keys f"
  by (simp add: domIff keys_dom_lookup)

lemma Mapping_lookup_delete: "Mapping.lookup (Mapping.delete k m) k' =
  (if k = k' then None else Mapping.lookup m k')"
  by transfer auto

lemma Mapping_lookup_filter_None: "(\<And>v. \<not>P k v) \<Longrightarrow>
  Mapping.lookup (Mapping.filter P m) k = None"
  by (auto simp add: Mapping.lookup_filter split: option.splits)

lemma Mapping_lookup_filter_Some: "(\<And>v. P k v) \<Longrightarrow>
  Mapping.lookup (Mapping.filter P m) k = Mapping.lookup m k"
  by (auto simp add: Mapping.lookup_filter split: option.splits)

lemma Mapping_lookup_filter_keys: "k \<in> Mapping.keys (Mapping.filter f m) \<Longrightarrow>
  Mapping.lookup (Mapping.filter f m) k = Mapping.lookup m k"
  by (metis default_def insert_subset keys_default keys_filter lookup_default lookup_default_filter)

lemma Mapping_filter_keys: "(\<forall>k \<in> Mapping.keys m. P (Mapping.lookup m k)) \<Longrightarrow>
  (\<forall>k \<in> Mapping.keys (Mapping.filter f m). P (Mapping.lookup (Mapping.filter f m) k))"
  using Mapping_lookup_filter_keys Mapping.keys_filter by fastforce

lemma Mapping_lookup_filter_Some_P: "Mapping.lookup (Mapping.filter P m) k = Some v \<Longrightarrow> P k v"
  by (auto simp add: Mapping.lookup_filter split: option.splits if_splits)

lemma Mapping_lookup_filter_not_None: "Mapping.lookup (Mapping.filter P m) k \<noteq> None \<Longrightarrow>
  Mapping.lookup (Mapping.filter P m) k = Mapping.lookup m k"
  by (auto simp add: Mapping.lookup_filter split: option.splits)

lemma Mapping_keys_filterI: "Mapping.lookup m k = Some v \<Longrightarrow> f k v \<Longrightarrow>
  k \<in> Mapping.keys (Mapping.filter f m)"
  by transfer (auto split: option.splits if_splits)

lemma Mapping_keys_filterD: "k \<in> Mapping.keys (Mapping.filter f m) \<Longrightarrow>
  \<exists>v. Mapping.lookup m k = Some v \<and> f k v"
  by transfer (auto split: option.splits if_splits)

lemma Mapping_keys_filter: "Mapping.keys (Mapping.filter (\<lambda>x _. P x) m) = Set.filter P (Mapping.keys m)"
  by transfer (auto split: option.splits if_splits)

lemma mapping_filter_keys_diff: "Mapping.keys (Mapping.filter p m) = Mapping.keys m - (Mapping.keys m - Mapping.keys (Mapping.filter p m))"
  by (simp add: double_diff keys_filter)

lemma finite_keys_filter: "finite (Mapping.keys m) \<Longrightarrow> finite (Mapping.keys (Mapping.filter p m))" by (meson infinite_super keys_filter)

lemma Mapping_filter_cong:
  assumes cong: "(\<And>k v. k \<in> Mapping.keys m \<Longrightarrow> f k v = f' k v)"
  shows "Mapping.filter f m = Mapping.filter f' m"
proof -
  have "\<And>k. Mapping.lookup (Mapping.filter f m) k = Mapping.lookup (Mapping.filter f' m) k"
    using cong
    by (fastforce simp add: Mapping.lookup_filter intro: Mapping_keys_intro split: option.splits)
  then show ?thesis
    by (simp add: mapping_eqI)
qed

lemma Mapping_empty_filter: "Mapping.filter f Mapping.empty = Mapping.empty"
  by (metis Mapping.lookup_empty Mapping_lookup_filter_not_None mapping_eqI)

lemma fold_Mapping_filter_empty: "fold (\<lambda>el tuple_in. Mapping.filter (f el tuple_in) tuple_in) xs Mapping.empty = Mapping.empty"
proof (induction xs arbitrary: )
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then have "(fold (\<lambda>el tuple_in. Mapping.filter (f el tuple_in) tuple_in) xs Mapping.empty) = Mapping.empty"
    by auto
  then have "(fold (\<lambda>el tuple_in. Mapping.filter (f el tuple_in) tuple_in) xs (Mapping.filter (f x Mapping.empty) Mapping.empty)) = Mapping.empty"
    using Mapping_empty_filter[of "f x Mapping.empty"]
    by auto
  then have "(fold (\<lambda>el tuple_in. Mapping.filter (f el tuple_in) tuple_in) xs \<circ> (\<lambda>el tuple_in. Mapping.filter (f el tuple_in) tuple_in) x) Mapping.empty = Mapping.empty"
    by auto
  then show ?case by simp
qed

lemma Mapping_lookup_combineE: "Mapping.lookup (Mapping.combine f m m') k = Some v \<Longrightarrow>
  (Mapping.lookup m k = Some v \<Longrightarrow> P) \<Longrightarrow>
  (Mapping.lookup m' k = Some v \<Longrightarrow> P) \<Longrightarrow>
  (\<And>v' v''. Mapping.lookup m k = Some v' \<Longrightarrow> Mapping.lookup m' k = Some v'' \<Longrightarrow>
  f v' v'' = v \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding Mapping.lookup_combine
  by (auto simp add: combine_options_def split: option.splits)

lemma lookup_tabulate_upt: "Mapping.lookup (Mapping.tabulate [a..<b] f) t = (if a \<le> t \<and> t < b then Some (f t) else None)"
  by (subst Mapping.lookup_tabulate) auto

(*<*)
end
(*>*)
