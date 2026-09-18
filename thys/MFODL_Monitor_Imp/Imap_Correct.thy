(*<*)
theory Imap_Correct
  imports Table_Imp "MFODL_Monitor_Devel.Imperative_Join"
begin
(*>*)

section \<open>The hash table of @{theory MFODL_Monitor_Imp.Table_Imp}, in separation logic\<close>

text \<open>
  @{theory MFODL_Monitor_Imp.Table_Imp} builds a hash table directly on an array, for the
  reasons that theory gives, and states no correctness property of it.  This theory supplies
  one: an assertion relating a table on the heap to the partial function it stands for, and a
  Hoare triple for each operation the join below uses.

  Two constants the table is built from stay folded throughout.  @{const ihash} is the hash of
  a tuple and @{const ibkt} turns a hash and a capacity into a bucket index; both are replaced
  at code generation by the OCaml the comments there give, so a proof that unfolded them would
  be a proof about a table with one bucket and would say nothing about the program that runs.
  All that is used of them is that @{const ihash} is a function -- which it is, being one -- and
  that a bucket index is in range, which is the one lemma below that looks at @{const ibkt}.
\<close>

subsection \<open>Tuple equality and bucket scans\<close>

lemma oeq_eq[simp]: "oeq x y \<longleftrightarrow> x = y"
  by (cases x; cases y) auto

lemma teq_eq[simp]: "teq x y \<longleftrightarrow> x = y"
  by (induct x y rule: teq.induct) (auto simp: List.null_def)

lemma hm_look_list_eq:
  assumes "\<forall>e \<in> set b. fst e = ihash (fst (snd e))"
  shows "hm_look_list (ihash x) x b = map_of (map snd b) x"
  using assms by (induct b) auto

lemma hm_del_list_eq:
  assumes "\<forall>e \<in> set b. fst e = ihash (fst (snd e))"
    and "distinct (map (\<lambda>e. fst (snd e)) b)"
  shows "map (\<lambda>e. fst (snd e)) (hm_del_list (ihash x) x b)
      = removeAll x (map (\<lambda>e. fst (snd e)) b)"
  using assms by (induct b) auto

lemma hm_del_list_set: "set (hm_del_list h x b) \<subseteq> set b"
  by (induct b) auto

subsection \<open>Bucket indices are in range\<close>

lemma im_cap_aux_ge: "8 \<le> c \<Longrightarrow> 8 \<le> im_cap_aux k c n"
  by (induct k arbitrary: c) auto

lemma im_cap_ge: "8 \<le> im_cap n"
  by (simp add: im_cap_def im_cap_aux_ge)

lemma im_cap_pos: "0 < im_cap n"
  using im_cap_ge[of n] by simp

lemma ibkt_in_range: "0 < n \<Longrightarrow> 0 \<le> ibkt h n \<and> ibkt h n < n"
  by (simp add: ibkt_def)
