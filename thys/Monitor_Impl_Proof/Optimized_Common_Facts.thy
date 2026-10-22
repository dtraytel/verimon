(*<*)
theory Optimized_Common_Facts
  imports "Monitor_Impl.Optimized_Common"
begin
(*>*)


lemma fold_append_queue_map: "linearize (fold (\<lambda>(t, l, r) q. append_queue (t, r) q) xs q) = linearize q @ (map (\<lambda>(t, l, r). (t, r)) xs)"
  by (induction xs arbitrary: q) (auto simp add: append_queue_rep)

lemma filter_set_sub: "filter_set (t, X) (m, Y) = (m', Y') \<Longrightarrow> Y' \<subseteq> Y \<union> X"
  by (auto simp: filter_set.simps Let_def Mapping_lookup_filter_Some domIff keys_dom_lookup)

lemma fold_filter_set_None: "Mapping.lookup ts as = None \<Longrightarrow>
  fold filter_set ds (ts, Y) = (ts', Y') \<Longrightarrow>
  Mapping.lookup ts' as = None \<and> (as \<in> Y' \<longleftrightarrow> as \<in> Y)"
proof (induction ds arbitrary: ts Y)
  case (Cons a ds)
  show ?case
  proof (cases a)
    case (Pair t' X')
    obtain ts'' Y'' where step: "filter_set a (ts, Y) = (ts'', Y'')"
      by fastforce
    show ?thesis
    proof (cases "Mapping.lookup ts'' as")
      case None
      have "as \<in> Y'' \<longleftrightarrow> as \<in> Y"
        using Cons(2) step
        by (auto simp: Pair filter_set.simps Let_def keys_is_none_rep)
      then show ?thesis
        using Cons(1)[OF None] Cons(2,3)
        by (auto simp: step)
    next
      case (Some t'')
      have False
        using Cons(2) Some step Mapping_lookup_filter_not_None
        by (force simp: Pair filter_set.simps Let_def)
      then show ?thesis ..
    qed
  qed
qed simp

lemma upd_set_keys_sub: "upd_set_keys Z (t, X) (m, Y) = (m', Y') \<Longrightarrow> Y' \<subseteq> Y \<union> Z X t"
  by (auto simp: upd_set_keys.simps Mapping_lookup_filter_Some domIff keys_dom_lookup)

lemma finite_fst_ts_tuple_rel: "finite (fst ` {tas \<in> ts_tuple_rel_f f (set xs). P tas})"
proof -
  have "fst ` {tas \<in> ts_tuple_rel_f f (set xs). P tas} \<subseteq> fst ` ts_tuple_rel_f f (set xs)"
    by auto
  moreover have "\<dots> \<subseteq> set (map fst xs)"
    by (force simp add: ts_tuple_rel_f_def)
  finally show ?thesis
    using finite_subset by blast
qed

lemma ts_tuple_rel_intro: "as \<in> f X \<Longrightarrow> (t, X) \<in> ys \<Longrightarrow> (t, as) \<in> ts_tuple_rel_f f ys"
  by (auto simp add: ts_tuple_rel_f_def)

lemma ts_tuple_rel_Un: "ts_tuple_rel_f f (ys \<union> zs) = ts_tuple_rel_f f ys \<union> ts_tuple_rel_f f zs"
  by (auto simp add: ts_tuple_rel_f_def)

lemma ts_tuple_rel_mono: "ys \<subseteq> zs \<Longrightarrow> ts_tuple_rel_f f ys \<subseteq> ts_tuple_rel_f f zs"
  by (auto simp add: ts_tuple_rel_f_def)

lemma ts_tuple_rel_filter: "ts_tuple_rel_f f (set (filter (\<lambda>(t, X). P t) xs)) =
  {(t, X) \<in> ts_tuple_rel_f f (set xs). P t}"
  by (auto simp add: ts_tuple_rel_f_def)

lemma ts_tuple_rel_set_filter: "x \<in> ts_tuple_rel_f f (set (filter P xs)) \<Longrightarrow>
  x \<in> ts_tuple_rel_f f (set xs)"
  by (auto simp add: ts_tuple_rel_f_def)

(* TODO: combine with shift_end *)
lemma ts_tuple_rel_empty: "ts_tuple_rel_f (\<lambda>_. {}) A = {}"
  unfolding ts_tuple_rel_f_def
  by auto

lemma safe_max_empty: "safe_max X = None \<longleftrightarrow> X = {}"
  by (simp add: safe_max_def)

lemma safe_max_empty_dest: "safe_max X = None \<Longrightarrow> X = {}"
  by (simp add: safe_max_def split: if_splits)

lemma safe_max_Some_dest_in: "finite X \<Longrightarrow> safe_max X = Some x \<Longrightarrow> x \<in> X"
  using Max_in by (auto simp add: safe_max_def split: if_splits)

lemma safe_max_Some_dest_le: "finite X \<Longrightarrow> safe_max X = Some x \<Longrightarrow> y \<in> X \<Longrightarrow> y \<le> x"
  using Max_ge by (auto simp add: safe_max_def split: if_splits)

(*<*)
end
(*>*)
