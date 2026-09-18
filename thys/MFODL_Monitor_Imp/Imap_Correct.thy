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
  by (induct x y rule: teq.induct) (auto simp: List.null_iff)

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

subsection \<open>The abstraction\<close>

text \<open>
  A table stands for the partial function its entries give.  The invariant says that the array
  has the capacity the record carries, that every entry sits in the bucket its stored hash
  selects and stores the hash of its own key, and that no key occurs twice.  The entry count the
  record carries is unconstrained: it only decides when the table grows, and correctness does not
  depend on that.
\<close>

definition ientry_ok :: "integer \<Rightarrow> nat \<Rightarrow> ('v ientry) \<Rightarrow> bool" where
  "ientry_ok n i e \<longleftrightarrow> fst e = ihash (fst (snd e)) \<and> ibkt (fst e) n = integer_of_nat i"

definition imap_inv :: "integer \<Rightarrow> ('v ientry) list list \<Rightarrow> bool" where
  "imap_inv n bs \<longleftrightarrow> 0 < n \<and> integer_of_nat (length bs) = n \<and>
     (\<forall>i < length bs. \<forall>e \<in> set (bs ! i). ientry_ok n i e) \<and>
     distinct (map (\<lambda>e. fst (snd e)) (concat bs))"

definition imap_map :: "('v ientry) list list \<Rightarrow> event_data tuple \<Rightarrow> 'v option" where
  "imap_map bs = map_of (map snd (concat bs))"

definition is_imap :: "(event_data tuple \<Rightarrow> 'v option) \<Rightarrow> ('v::heap) imap \<Rightarrow> assn" where
  "is_imap m q = (\<exists>\<^sub>Abs. snd (snd q) \<mapsto>\<^sub>a bs * \<up>(imap_inv (fst q) bs \<and> m = imap_map bs))"

lemma in_concat_nth:
  assumes "e \<in> set (concat bs)"
  shows "\<exists>j < length bs. e \<in> set (bs ! j)"
proof -
  from assms obtain l where l: "l \<in> set bs" and el: "e \<in> set l" by auto
  from l obtain j where "j < length bs" and "bs ! j = l" by (auto simp: in_set_conv_nth)
  then show ?thesis using el by auto
qed

lemma map_of_perm:
  assumes d': "distinct (map fst l')" and s: "set l' = set l"
  shows "map_of l' = map_of l"
proof
  fix k
  show "map_of l' k = map_of l k"
  proof (cases "map_of l k")
    case None
    then have "k \<notin> fst ` set l" by (simp add: map_of_eq_None_iff)
    then have "k \<notin> fst ` set l'" using s by simp
    then have "map_of l' k = None" by (simp add: map_of_eq_None_iff)
    then show ?thesis using None by simp
  next
    case (Some v)
    then have "(k, v) \<in> set l" by (rule map_of_SomeD)
    then have "(k, v) \<in> set l'" using s by simp
    then show ?thesis using Some d' by (simp add: map_of_is_SomeI)
  qed
qed

lemma imap_map_bucket:
  assumes inv: "imap_inv n bs" and i: "i < length bs"
    and ib: "ibkt (ihash x) n = integer_of_nat i"
  shows "imap_map bs x = map_of (map snd (bs ! i)) x"
proof -
  have d: "distinct (map fst (map snd (concat bs)))"
    using inv by (simp add: imap_inv_def o_def)
  have si: "set (bs ! i) \<subseteq> set (concat bs)" using nth_mem[OF i] by auto
  have sub: "set (map snd (bs ! i)) \<subseteq> set (map snd (concat bs))" using si by auto
  show ?thesis
  proof (cases "map_of (map snd (bs ! i)) x")
    case None
    have "x \<notin> fst ` set (map snd (concat bs))"
    proof
      assume "x \<in> fst ` set (map snd (concat bs))"
      then obtain p where p: "p \<in> set (map snd (concat bs))" and kp: "fst p = x" by auto
      from p obtain e where e: "e \<in> set (concat bs)" and pe: "p = snd e" by auto
      have k: "fst (snd e) = x" using kp pe by simp
      obtain j where j: "j < length bs" and ej: "e \<in> set (bs ! j)"
        using in_concat_nth[OF e] by blast
      have io: "ientry_ok n j e" using inv j ej by (simp add: imap_inv_def)
      have "ibkt (ihash (fst (snd e))) n = integer_of_nat j"
        using io unfolding ientry_ok_def by auto
      then have "integer_of_nat j = integer_of_nat i" using k ib by simp
      then have "j = i" by (simp add: integer_of_nat_eq_of_nat)
      then have "e \<in> set (bs ! i)" using ej by simp
      then have "x \<in> fst ` set (map snd (bs ! i))" using k by force
      then show False using None by (simp add: map_of_eq_None_iff)
    qed
    then have "map_of (map snd (concat bs)) x = None" by (simp add: map_of_eq_None_iff)
    then show ?thesis using None by (simp add: imap_map_def)
  next
    case (Some v)
    then have "(x, v) \<in> set (map snd (bs ! i))" by (rule map_of_SomeD)
    then have "(x, v) \<in> set (map snd (concat bs))" using sub by blast
    then show ?thesis using Some d by (simp add: imap_map_def map_of_is_SomeI)
  qed
qed

subsection \<open>Creating a table\<close>

lemma integer_of_nat_nat_of_integer: "0 \<le> k \<Longrightarrow> integer_of_nat (nat_of_integer k) = k"
  by (simp add: integer_eq_iff nat_of_integer.rep_eq less_eq_integer.rep_eq
      integer_of_nat_eq_of_nat)

lemma nat_of_integer_less:
  assumes "0 \<le> k" and "k < integer_of_nat l"
  shows "nat_of_integer k < l"
  using assms by (simp add: less_integer.rep_eq less_eq_integer.rep_eq
      nat_of_integer.rep_eq integer_of_nat_eq_of_nat nat_less_iff)

lemma imap_map_replicate[simp]: "imap_map (replicate k []) = Map.empty"
  by (simp add: imap_map_def)

lemma im_new_rule: "<emp> im_new n <is_imap Map.empty>"
proof -
  have p: "0 < im_cap n" by (rule im_cap_pos)
  have l: "integer_of_nat (nat_of_integer (im_cap n)) = im_cap n"
    by (rule integer_of_nat_nat_of_integer) (use p in simp)
  show ?thesis
    unfolding im_new_def Array.new'_def
    by (sep_auto simp: is_imap_def imap_inv_def l p)
qed

subsection \<open>Looking a key up\<close>

lemma im_lookup_h_rule:
  "<is_imap m q> im_lookup_h q (ihash x) x <\<lambda>r. is_imap m q * \<up>(r = m x)>"
proof (cases q)
  case (fields n c a)
  show ?thesis
    unfolding fields is_imap_def im_lookup_h_def Array.nth'_def
  proof (sep_auto, goal_cases)
    case (1 bs)
    then have inv: "imap_inv n bs" by simp
    then have p: "0 < n" and le: "integer_of_nat (length bs) = n"
      by (simp_all add: imap_inv_def)
    show ?case
      by (rule nat_of_integer_less) (use ibkt_in_range[OF p] le in auto)
  next
    case (2 bs)
    then have inv: "imap_inv n bs" and mm: "m = imap_map bs" by simp_all
    have le: "integer_of_nat (length bs) = n" using inv by (simp add: imap_inv_def)
    have p: "0 < n" using inv by (simp add: imap_inv_def)
    have lt: "nat_of_integer (ibkt (ihash x) n) < length bs"
      by (rule nat_of_integer_less) (use ibkt_in_range[OF p] le in auto)
    have ib: "ibkt (ihash x) n = integer_of_nat (nat_of_integer (ibkt (ihash x) n))"
      using ibkt_in_range[OF p] by (simp add: integer_of_nat_nat_of_integer)
    have hb: "\<forall>e \<in> set (bs ! nat_of_integer (ibkt (ihash x) n)). fst e = ihash (fst (snd e))"
      using inv lt by (auto simp: imap_inv_def ientry_ok_def)
    have eq: "hm_look_list (ihash x) x (bs ! nat_of_integer (ibkt (ihash x) n)) = m x"
      unfolding hm_look_list_eq[OF hb] mm by (rule imap_map_bucket[OF inv lt ib, symmetric])
    show ?case by (sep_auto simp: eq inv mm)
  qed
qed

(*<*)
end
(*>*)
