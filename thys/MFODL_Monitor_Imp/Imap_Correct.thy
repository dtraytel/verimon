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

lemma integer_of_nat_nat_of_integer: "0 \<le> k \<Longrightarrow> integer_of_nat (nat_of_integer k) = k"
  by (simp add: integer_eq_iff nat_of_integer.rep_eq less_eq_integer.rep_eq
      integer_of_nat_eq_of_nat)

lemma nat_of_integer_less:
  assumes "0 \<le> k" and "k < integer_of_nat l"
  shows "nat_of_integer k < l"
  using assms by (simp add: less_integer.rep_eq less_eq_integer.rep_eq
      nat_of_integer.rep_eq integer_of_nat_eq_of_nat nat_less_iff)

text \<open>The bucket a key belongs to, as an index into the list of buckets.\<close>

definition ibucket :: "integer \<Rightarrow> event_data tuple \<Rightarrow> nat" where
  "ibucket n x = nat_of_integer (ibkt (ihash x) n)"

lemma ibucket_conv: "0 < n \<Longrightarrow> (ibkt (ihash x) n = integer_of_nat i) \<longleftrightarrow> ibucket n x = i"
  using ibkt_in_range[of n "ihash x"]
  by (auto simp: ibucket_def integer_of_nat_nat_of_integer)

lemma ibucket_lt: "0 < n \<Longrightarrow> integer_of_nat l = n \<Longrightarrow> ibucket n x < l"
  unfolding ibucket_def
  by (rule nat_of_integer_less) (use ibkt_in_range[of n "ihash x"] in auto)

subsection \<open>The abstraction\<close>

text \<open>
  A table stands for the partial function its entries give.  The invariant says that the array
  has the capacity the record carries, that every entry sits in the bucket its stored hash
  selects and stores the hash of its own key, and that no key occurs twice.  The entry count the
  record carries is unconstrained: it only decides when the table grows, and correctness does not
  depend on that.
\<close>

definition ientry_ok :: "integer \<Rightarrow> nat \<Rightarrow> ('v ientry) \<Rightarrow> bool" where
  "ientry_ok n i e \<longleftrightarrow> fst e = ihash (fst (snd e)) \<and> ibucket n (fst (snd e)) = i"

definition imap_inv :: "integer \<Rightarrow> ('v ientry) list list \<Rightarrow> bool" where
  "imap_inv n bs \<longleftrightarrow> 0 < n \<and> integer_of_nat (length bs) = n \<and>
     (\<forall>i < length bs. \<forall>e \<in> set (bs ! i). ientry_ok n i e) \<and>
     distinct (map (\<lambda>e. fst (snd e)) (concat bs))"

text \<open>
  The map a list of buckets stands for is read off the bucket the key belongs to, which is how
  @{const im_lookup_h} reads it.  Stating it this way makes an update of one bucket a local
  change of the map; @{text imap_map_global} below identifies it with the map of all entries,
  which is what the growth step needs.
\<close>

definition imap_map :: "integer \<Rightarrow> ('v ientry) list list \<Rightarrow> event_data tuple \<Rightarrow> 'v option" where
  "imap_map n bs x = hm_look_list (ihash x) x (bs ! ibucket n x)"

definition is_imap :: "(event_data tuple \<Rightarrow> 'v option) \<Rightarrow> ('v::heap) imap \<Rightarrow> assn" where
  "is_imap m q =
     (\<exists>\<^sub>Abs. snd (snd q) \<mapsto>\<^sub>a bs * \<up>(imap_inv (fst q) bs \<and> m = imap_map (fst q) bs))"

lemma imap_inv_pos: "imap_inv n bs \<Longrightarrow> 0 < n"
  by (simp add: imap_inv_def)

lemma imap_inv_len: "imap_inv n bs \<Longrightarrow> integer_of_nat (length bs) = n"
  by (simp add: imap_inv_def)

lemma imap_inv_bucket_lt: "imap_inv n bs \<Longrightarrow> ibucket n x < length bs"
  by (rule ibucket_lt[OF imap_inv_pos imap_inv_len])

lemma imap_inv_hash: "imap_inv n bs \<Longrightarrow> i < length bs \<Longrightarrow> \<forall>e \<in> set (bs ! i). fst e = ihash (fst (snd e))"
  by (auto simp: imap_inv_def ientry_ok_def)

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

text \<open>
  Scanning the key's own bucket sees every entry with that key, because the invariant puts an
  entry nowhere else.  So the local reading of the map agrees with the global one.
\<close>

lemma imap_map_global:
  assumes inv: "imap_inv n bs"
  shows "imap_map n bs = map_of (map snd (concat bs))"
proof
  fix x
  have i: "ibucket n x < length bs" by (rule imap_inv_bucket_lt[OF inv])
  have d: "distinct (map fst (map snd (concat bs)))"
    using inv by (simp add: imap_inv_def o_def)
  have si: "set (bs ! ibucket n x) \<subseteq> set (concat bs)" using nth_mem[OF i] by auto
  have sub: "set (map snd (bs ! ibucket n x)) \<subseteq> set (map snd (concat bs))" using si by auto
  have lk: "imap_map n bs x = map_of (map snd (bs ! ibucket n x)) x"
    unfolding imap_map_def by (rule hm_look_list_eq[OF imap_inv_hash[OF inv i]])
  show "imap_map n bs x = map_of (map snd (concat bs)) x"
  proof (cases "map_of (map snd (bs ! ibucket n x)) x")
    case None
    have "x \<notin> fst ` set (map snd (concat bs))"
    proof
      assume "x \<in> fst ` set (map snd (concat bs))"
      then obtain p where p: "p \<in> set (map snd (concat bs))" and kp: "fst p = x" by auto
      from p obtain e where e: "e \<in> set (concat bs)" and pe: "p = snd e" by auto
      have k: "fst (snd e) = x" using kp pe by simp
      obtain j where j: "j < length bs" and ej: "e \<in> set (bs ! j)"
        using in_concat_nth[OF e] by blast
      have "ientry_ok n j e" using inv j ej by (simp add: imap_inv_def)
      then have "j = ibucket n x" using k unfolding ientry_ok_def by auto
      then have "e \<in> set (bs ! ibucket n x)" using ej by simp
      then have "x \<in> fst ` set (map snd (bs ! ibucket n x))" using k by force
      then show False using None by (simp add: map_of_eq_None_iff)
    qed
    then have "map_of (map snd (concat bs)) x = None" by (simp add: map_of_eq_None_iff)
    then show ?thesis using None lk by simp
  next
    case (Some v)
    then have "(x, v) \<in> set (map snd (bs ! ibucket n x))" by (rule map_of_SomeD)
    then have "(x, v) \<in> set (map snd (concat bs))" using sub by blast
    then show ?thesis using Some d lk by (simp add: map_of_is_SomeI)
  qed
qed

subsection \<open>Changing one bucket\<close>

text \<open>
  A key can only ever sit in the bucket its hash selects, so two keys in different buckets are
  different and the global distinctness is exactly distinctness inside each bucket.  Both the
  invariant and the map are therefore local: replacing one bucket by a well-formed one leaves
  the rest of the table alone.
\<close>

lemma concat_nth_split:
  "i < length bs \<Longrightarrow> concat bs = concat (take i bs) @ bs ! i @ concat (drop (Suc i) bs)"
  by (subst id_take_nth_drop[of i bs]) simp_all

lemma distinct_concat_bucketed:
  "(\<And>j. j < length bs \<Longrightarrow> distinct (map k (bs ! j))) \<Longrightarrow>
   (\<And>j e. j < length bs \<Longrightarrow> e \<in> set (bs ! j) \<Longrightarrow> g (k e) = s + j) \<Longrightarrow>
   distinct (map k (concat bs))"
proof (induct bs arbitrary: s)
  case Nil
  show ?case by simp
next
  case (Cons b bs)
  have db: "distinct (map k b)" using Cons(2)[of 0] by simp
  have gb: "\<And>e. e \<in> set b \<Longrightarrow> g (k e) = s" using Cons(3)[of 0] by simp
  have ih: "distinct (map k (concat bs))"
  proof (rule Cons(1))
    fix j assume "j < length bs"
    then show "distinct (map k (bs ! j))" using Cons(2)[of "Suc j"] by simp
  next
    fix j e assume "j < length bs" and "e \<in> set (bs ! j)"
    then show "g (k e) = Suc s + j" using Cons(3)[of "Suc j" e] by simp
  qed
  have "set (map k b) \<inter> set (map k (concat bs)) = {}"
  proof safe
    fix y assume y: "y \<in> set (map k b)" and y': "y \<in> set (map k (concat bs))"
    from y obtain e where e: "e \<in> set b" and ke: "k e = y" by auto
    from y' obtain e' where e': "e' \<in> set (concat bs)" and ke': "k e' = y" by auto
    obtain j where j: "j < length bs" and ej: "e' \<in> set (bs ! j)"
      using in_concat_nth[OF e'] by blast
    have "g y = s" using gb[OF e] ke by simp
    moreover have "g y = Suc s + j" using Cons(3)[of "Suc j" e'] j ej ke' by simp
    ultimately show "y \<in> {}" by simp
  qed
  then show ?case using db ih by auto
qed

lemma imap_inv_alt:
  assumes pos: "0 < n" and len: "integer_of_nat (length bs) = n"
    and ok: "\<And>i e. i < length bs \<Longrightarrow> e \<in> set (bs ! i) \<Longrightarrow> ientry_ok n i e"
    and d: "\<And>i. i < length bs \<Longrightarrow> distinct (map (\<lambda>e. fst (snd e)) (bs ! i))"
  shows "imap_inv n bs"
proof -
  have "distinct (map (\<lambda>e. fst (snd e)) (concat bs))"
  proof (rule distinct_concat_bucketed[where g = "ibucket n" and s = 0])
    fix j assume "j < length bs"
    then show "distinct (map (\<lambda>e. fst (snd e)) (bs ! j))" by (rule d)
  next
    fix j e assume "j < length bs" and "e \<in> set (bs ! j)"
    from ok[OF this] show "ibucket n (fst (snd e)) = 0 + j" by (simp add: ientry_ok_def)
  qed
  then show ?thesis using pos len ok by (auto simp: imap_inv_def)
qed

lemma imap_inv_bucket_distinct:
  assumes inv: "imap_inv n bs" and i: "i < length bs"
  shows "distinct (map (\<lambda>e. fst (snd e)) (bs ! i))"
proof -
  have "distinct (map (\<lambda>e. fst (snd e)) (concat bs))" using inv by (simp add: imap_inv_def)
  then show ?thesis by (subst (asm) concat_nth_split[OF i]) simp
qed

lemma imap_inv_list_update:
  assumes inv: "imap_inv n bs" and i: "i < length bs"
    and ok: "\<And>e. e \<in> set b' \<Longrightarrow> ientry_ok n i e"
    and d: "distinct (map (\<lambda>e. fst (snd e)) b')"
  shows "imap_inv n (list_update bs i b')"
proof (rule imap_inv_alt)
  show "0 < n" by (rule imap_inv_pos[OF inv])
next
  show "integer_of_nat (length (list_update bs i b')) = n" using imap_inv_len[OF inv] by simp
next
  fix j e assume j: "j < length (list_update bs i b')" and e: "e \<in> set (list_update bs i b' ! j)"
  show "ientry_ok n j e"
  proof (cases "j = i")
    case True
    then show ?thesis using e ok i by simp
  next
    case False
    then show ?thesis using e inv j by (auto simp: imap_inv_def)
  qed
next
  fix j assume j: "j < length (list_update bs i b')"
  show "distinct (map (\<lambda>e. fst (snd e)) (list_update bs i b' ! j))"
  proof (cases "j = i")
    case True
    then show ?thesis using d i by simp
  next
    case False
    then show ?thesis using imap_inv_bucket_distinct[OF inv] j by simp
  qed
qed

lemma imap_map_list_update:
  assumes inv: "imap_inv n bs" and i: "i < length bs"
  shows "imap_map n (list_update bs i b') x =
    (if i = ibucket n x then hm_look_list (ihash x) x b' else imap_map n bs x)"
  using imap_inv_bucket_lt[OF inv] i by (simp add: imap_map_def)

subsection \<open>Creating a table\<close>

lemma imap_map_replicate:
  assumes "0 < n" and "integer_of_nat k = n"
  shows "imap_map n (replicate k []) = Map.empty"
proof
  fix x
  have "ibucket n x < k" by (rule ibucket_lt[OF assms])
  then show "imap_map n (replicate k []) x = Map.empty x" by (simp add: imap_map_def)
qed

lemma im_new_rule: "<emp> im_new n <is_imap Map.empty>"
proof -
  have p: "0 < im_cap n" by (rule im_cap_pos)
  have l: "integer_of_nat (nat_of_integer (im_cap n)) = im_cap n"
    by (rule integer_of_nat_nat_of_integer) (use p in simp)
  show ?thesis
    unfolding im_new_def Array.new'_def
    by (sep_auto simp: is_imap_def imap_inv_def l p imap_map_replicate[OF p l])
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
    then have "imap_inv n bs" by simp
    from imap_inv_bucket_lt[OF this] show ?case by (simp add: ibucket_def)
  next
    case (2 bs)
    then show ?case by (sep_auto simp: imap_map_def ibucket_def)
  qed
qed

lemma im_lookup_rule: "<is_imap m q> im_lookup q x <\<lambda>r. is_imap m q * \<up>(r = m x)>"
  unfolding im_lookup_def by (rule im_lookup_h_rule)

subsection \<open>Reading all entries back\<close>

lemma nat_of_integer_integer_of_nat[simp]: "nat_of_integer (integer_of_nat j) = j"
  by (simp add: nat_of_integer.rep_eq integer_of_nat_eq_of_nat)

lemma integer_of_nat_less_iff[simp]: "integer_of_nat i < integer_of_nat j \<longleftrightarrow> i < j"
  by (simp add: less_integer.rep_eq integer_of_nat_eq_of_nat)

lemma integer_of_nat_le_iff[simp]: "integer_of_nat i \<le> integer_of_nat j \<longleftrightarrow> i \<le> j"
  by (simp add: less_eq_integer.rep_eq integer_of_nat_eq_of_nat)

lemma integer_of_nat_Suc: "integer_of_nat (Suc j) = integer_of_nat j + 1"
  by (simp add: integer_of_nat_eq_of_nat)

lemma integer_of_nat_0[simp]: "integer_of_nat 0 = 0"
  by (simp add: integer_of_nat_eq_of_nat)

text \<open>
  The fold walks the buckets from an index to the end, so its rule is an induction on how many
  buckets are left.  With the append as the folded step the result is the entries of those
  buckets, the buckets in reverse order; only the multiset of entries matters downstream.
\<close>

lemma im_fold_idx_append_rule:
  assumes n: "integer_of_nat (length bs) = n"
  shows "j \<le> length bs \<Longrightarrow>
    <a \<mapsto>\<^sub>a bs>
      im_fold_idx (\<lambda>b acc. b @ acc) a (integer_of_nat j) n acc
    <\<lambda>r. a \<mapsto>\<^sub>a bs * \<up>(r = concat (rev (drop j bs)) @ acc)>"
proof (induct "length bs - j" arbitrary: j acc)
  case 0
  then have "j = length bs" by simp
  then show ?case by (subst im_fold_idx.simps) (sep_auto simp: n)
next
  case (Suc x)
  then have lt: "j < length bs" by simp
  have ne: "\<not> n \<le> integer_of_nat j" using lt unfolding n[symmetric] by simp
  have ih: "<a \<mapsto>\<^sub>a bs>
      im_fold_idx (\<lambda>b acc. b @ acc) a (integer_of_nat (Suc j)) n (bs ! j @ acc)
    <\<lambda>r. a \<mapsto>\<^sub>a bs * \<up>(r = concat (rev (drop (Suc j) bs)) @ bs ! j @ acc)>"
    by (rule Suc(1)) (use lt Suc(2) in simp_all)
  have dr: "concat (rev (drop j bs)) @ acc = concat (rev (drop (Suc j) bs)) @ bs ! j @ acc"
    using lt by (subst Cons_nth_drop_Suc[symmetric]) simp_all
  show ?case
    by (subst im_fold_idx.simps)
       (sep_auto simp: ne Array.nth'_def lt integer_of_nat_Suc[symmetric] dr heap: ih)
qed

lemma im_entries_rule:
  assumes n: "integer_of_nat (length bs) = n"
  shows "<a \<mapsto>\<^sub>a bs> im_entries (n, c, a) <\<lambda>r. a \<mapsto>\<^sub>a bs * \<up>(r = concat (rev bs))>"
proof -
  have "<a \<mapsto>\<^sub>a bs> im_fold_idx (\<lambda>b acc. b @ acc) a (integer_of_nat 0) n []
        <\<lambda>r. a \<mapsto>\<^sub>a bs * \<up>(r = concat (rev (drop 0 bs)) @ [])>"
    by (rule im_fold_idx_append_rule[OF n]) simp
  then show ?thesis unfolding im_entries_def by simp
qed

subsection \<open>Redistributing the entries into a bigger table\<close>

lemma concat_list_update:
  "i < length bs \<Longrightarrow>
   concat (list_update bs i b') = concat (take i bs) @ b' @ concat (drop (Suc i) bs)"
  by (subst upd_conv_take_nth_drop) simp_all

lemma distinct_map_mset_cong: "mset xs = mset ys \<Longrightarrow> distinct (map k ys) \<Longrightarrow> distinct (map k xs)"
  by (metis mset_eq_imp_distinct_iff mset_map)

lemma im_new_rule':
  "<emp> im_new n <\<lambda>q. \<exists>\<^sub>Abs. snd (snd q) \<mapsto>\<^sub>a bs * \<up>(imap_inv (fst q) bs \<and> concat bs = [])>"
proof -
  have p: "0 < im_cap n" by (rule im_cap_pos)
  have l: "integer_of_nat (nat_of_integer (im_cap n)) = im_cap n"
    by (rule integer_of_nat_nat_of_integer) (use p in simp)
  show ?thesis
    unfolding im_new_def Array.new'_def
    by (sep_auto simp: imap_inv_def l p)
qed

text \<open>
  Filling a fresh table from a list of entries keeps the invariant and collects exactly those
  entries: each one goes into the bucket its stored hash selects, which is the bucket of its own
  key because the hash stored next to a key is that key's.
\<close>

lemma im_fill_rule:
  "imap_inv n bs \<Longrightarrow> (\<forall>e \<in> set kvs. fst e = ihash (fst (snd e))) \<Longrightarrow>
   distinct (map (\<lambda>e. fst (snd e)) (concat bs @ kvs)) \<Longrightarrow>
   <a \<mapsto>\<^sub>a bs>
     im_fill (n, c, a) kvs
   <\<lambda>q'. \<exists>\<^sub>Abs'. a \<mapsto>\<^sub>a bs' * \<up>(fst q' = n \<and> snd (snd q') = a \<and> imap_inv n bs' \<and>
      mset (concat bs') = mset (concat bs @ kvs))>"
proof (induct kvs arbitrary: bs c)
  case Nil
  then show ?case by (subst im_fill.simps) sep_auto
next
  case (Cons e r)
  note inv = Cons(2)
  have pos: "0 < n" by (rule imap_inv_pos[OF inv])
  have hsh: "fst e = ihash (fst (snd e))" using Cons(3) by simp
  define i where "i = ibucket n (fst (snd e))"
  have ib: "ibkt (fst e) n = integer_of_nat i"
    unfolding i_def hsh by (simp add: ibucket_conv[OF pos])
  have lt: "i < length bs" unfolding i_def by (rule imap_inv_bucket_lt[OF inv])
  have ke: "fst (snd e) \<notin> set (map (\<lambda>e. fst (snd e)) (concat bs))" using Cons(4) by auto
  have sub: "set (bs ! i) \<subseteq> set (concat bs)" using nth_mem[OF lt] by auto
  have d1: "distinct (map (\<lambda>e. fst (snd e)) (e # bs ! i))"
    using imap_inv_bucket_distinct[OF inv lt] ke sub by auto
  have ok1: "\<And>e'. e' \<in> set (e # bs ! i) \<Longrightarrow> ientry_ok n i e'"
    using inv lt hsh by (auto simp: imap_inv_def ientry_ok_def i_def)
  have inv1: "imap_inv n (list_update bs i (e # bs ! i))"
    by (rule imap_inv_list_update[OF inv lt ok1 d1])
  have ms: "mset (concat (list_update bs i (e # bs ! i))) = add_mset e (mset (concat bs))"
    using lt by (simp add: concat_list_update concat_nth_split[of i bs])
  have mm: "mset (concat (list_update bs i (e # bs ! i)) @ r) = mset (concat bs @ e # r)"
    using ms by simp
  have d2: "distinct (map (\<lambda>e. fst (snd e)) (concat (list_update bs i (e # bs ! i)) @ r))"
    by (rule distinct_map_mset_cong[OF mm Cons(4)])
  have ih: "<a \<mapsto>\<^sub>a list_update bs i (e # bs ! i)>
      im_fill (n, c + 1, a) r
    <\<lambda>q'. \<exists>\<^sub>Abs'. a \<mapsto>\<^sub>a bs' * \<up>(fst q' = n \<and> snd (snd q') = a \<and> imap_inv n bs' \<and>
       mset (concat bs') = mset (concat (list_update bs i (e # bs ! i)) @ r))>"
    by (rule Cons(1)[OF inv1 _ d2]) (use Cons(3) in simp)
  show ?case
    by (subst im_fill.simps)
       (sep_auto simp: ib Array.nth'_def Array.upd'_def lt ms heap: ih)
qed

subsection \<open>Growing a table\<close>

text \<open>
  Growing redistributes the entries of the old array into a fresh one twice its size.  The
  entries are the same, only their order and their buckets change, and the map of a table is
  the map of its entries, so the map is unchanged.  The old array is left behind, which is what
  the @{text \<open>\<^sub>t\<close>} of the triple allows.
\<close>

lemma imap_map_mset_cong:
  assumes inv: "imap_inv n bs" and inv': "imap_inv n' bs'"
    and ms: "mset (concat bs') = mset (concat bs)"
  shows "imap_map n' bs' = imap_map n bs"
proof -
  have "distinct (map fst (map snd (concat bs')))" using inv' by (simp add: imap_inv_def o_def)
  moreover have "set (map snd (concat bs')) = set (map snd (concat bs))"
    using ms by (metis mset_map set_mset_mset)
  ultimately have "map_of (map snd (concat bs')) = map_of (map snd (concat bs))"
    by (rule map_of_perm)
  then show ?thesis using imap_map_global[OF inv] imap_map_global[OF inv'] by simp
qed

lemma mset_concat_rev[simp]: "mset (concat (rev xs)) = mset (concat xs)"
  by (induct xs) simp_all

lemma set_concat_rev[simp]: "set (concat (rev xs)) = set (concat xs)"
  by (induct xs) auto

lemma im_grow_rule:
  assumes inv: "imap_inv n bs"
  shows "<a \<mapsto>\<^sub>a bs> im_grow (n, c, a) <\<lambda>q'. is_imap (imap_map n bs) q'>\<^sub>t"
proof -
  let ?k = "\<lambda>e. fst (snd e)"
  have hsh0: "\<forall>e \<in> set (concat bs). fst e = ihash (?k e)"
  proof
    fix e assume "e \<in> set (concat bs)"
    from in_concat_nth[OF this] obtain j where "j < length bs" and "e \<in> set (bs ! j)" by blast
    then show "fst e = ihash (?k e)" using inv by (auto simp: imap_inv_def ientry_ok_def)
  qed
  have hsh: "\<forall>e \<in> set (concat (rev bs)). fst e = ihash (?k e)" using hsh0 by simp
  have dst: "distinct (map ?k (concat (rev bs)))"
    by (rule distinct_map_mset_cong[OF mset_concat_rev]) (use inv in \<open>simp add: imap_inv_def\<close>)
  define n' where "n' = im_cap (2 * n)"
  define bs0 where "bs0 = replicate (nat_of_integer n') ([] :: 'a ientry list)"
  have p': "0 < n'" unfolding n'_def by (rule im_cap_pos)
  have l': "integer_of_nat (length bs0) = n'"
    unfolding bs0_def by (simp add: integer_of_nat_nat_of_integer[OF less_imp_le[OF p']])
  have inv0: "imap_inv n' bs0" using p' l' by (simp add: imap_inv_def bs0_def)
  have c0: "concat bs0 = []" by (simp add: bs0_def)
  have d0: "distinct (map ?k (concat bs0 @ concat (rev bs)))"
    using dst unfolding c0 by simp
  have fill: "\<And>a'. <a' \<mapsto>\<^sub>a bs0> im_fill (n', 0, a') (concat (rev bs))
    <\<lambda>q'. \<exists>\<^sub>Abs'. a' \<mapsto>\<^sub>a bs' * \<up>(fst q' = n' \<and> snd (snd q') = a' \<and> imap_inv n' bs' \<and>
       mset (concat bs') = mset (concat bs0 @ concat (rev bs)))>"
    by (rule im_fill_rule[OF inv0 hsh d0])
  have eq: "\<And>bs'. imap_inv n' bs' \<Longrightarrow>
      mset (concat bs') = mset (concat bs0 @ concat (rev bs)) \<Longrightarrow>
      imap_map n' bs' = imap_map n bs"
    by (rule imap_map_mset_cong[OF inv]) (simp_all add: c0)
  show ?thesis
    unfolding im_grow_def im_new_def Array.new'_def
    by (sep_auto simp: is_imap_def n'_def[symmetric] bs0_def[symmetric] eq
        heap: im_entries_rule[OF imap_inv_len[OF inv]] fill)
qed

subsection \<open>Adding or replacing a key\<close>

lemma hm_look_list_del:
  "\<forall>e \<in> set b. fst e = ihash (fst (snd e)) \<Longrightarrow> y \<noteq> x \<Longrightarrow>
   hm_look_list (ihash y) y (hm_del_list (ihash x) x b) = hm_look_list (ihash y) y b"
  by (induct b) auto

lemma hm_look_list_None_key:
  "hm_look_list (ihash x) x b = None \<Longrightarrow> \<forall>e \<in> set b. fst e = ihash (fst (snd e)) \<Longrightarrow>
   x \<notin> set (map (\<lambda>e. fst (snd e)) b)"
  by (induct b) (auto split: if_splits)

lemma imap_map_insert:
  assumes inv: "imap_inv n bs"
    and rest: "\<And>y. y \<noteq> x \<Longrightarrow> hm_look_list (ihash y) y rest
                 = hm_look_list (ihash y) y (bs ! ibucket n x)"
  shows "imap_map n (list_update bs (ibucket n x) ((ihash x, x, v) # rest))
       = (imap_map n bs)(x \<mapsto> v)"
proof
  fix y
  have lt: "ibucket n x < length bs" by (rule imap_inv_bucket_lt[OF inv])
  note upd = imap_map_list_update[OF inv lt, of "(ihash x, x, v) # rest" y]
  consider (eq) "y = x" | (same) "y \<noteq> x" "ibucket n x = ibucket n y"
    | (other) "y \<noteq> x" "ibucket n x \<noteq> ibucket n y" by blast
  then show "imap_map n (list_update bs (ibucket n x) ((ihash x, x, v) # rest)) y
      = ((imap_map n bs)(x \<mapsto> v)) y"
  proof cases
    case eq
    then show ?thesis using upd by simp
  next
    case same
    then show ?thesis using upd rest[OF same(1)] by (simp add: imap_map_def)
  next
    case other
    then show ?thesis using upd by simp
  qed
qed

text \<open>
  Both branches of an update put the new entry at the head of the key's bucket; they differ
  only in what they keep behind it -- the bucket as it was, when the key is new, and the bucket
  without its entry for that key, when the key is already there.  What the rest has to satisfy
  is the same in both cases.
\<close>

lemma im_update_bucket_inv:
  assumes inv: "imap_inv n bs"
    and sub: "set rest \<subseteq> set (bs ! ibucket n x)"
    and dk: "distinct (map (\<lambda>e. fst (snd e)) rest)"
    and nk: "x \<notin> set (map (\<lambda>e. fst (snd e)) rest)"
  shows "imap_inv n (list_update bs (ibucket n x) ((ihash x, x, v) # rest))"
proof (rule imap_inv_list_update[OF inv imap_inv_bucket_lt[OF inv]])
  fix e assume "e \<in> set ((ihash x, x, v) # rest)"
  then show "ientry_ok n (ibucket n x) e"
    using sub inv imap_inv_bucket_lt[OF inv] by (auto simp: ientry_ok_def imap_inv_def)
next
  show "distinct (map (\<lambda>e. fst (snd e)) ((ihash x, x, v) # rest))" using dk nk by simp
qed

lemma im_update_None:
  assumes inv: "imap_inv n bs" and lk: "hm_look_list (ihash x) x (bs ! ibucket n x) = None"
  shows "imap_inv n (list_update bs (ibucket n x) ((ihash x, x, v) # bs ! ibucket n x))"
    and "imap_map n (list_update bs (ibucket n x) ((ihash x, x, v) # bs ! ibucket n x))
       = (imap_map n bs)(x \<mapsto> v)"
proof -
  have lt: "ibucket n x < length bs" by (rule imap_inv_bucket_lt[OF inv])
  have hb: "\<forall>e \<in> set (bs ! ibucket n x). fst e = ihash (fst (snd e))"
    by (rule imap_inv_hash[OF inv lt])
  show "imap_inv n (list_update bs (ibucket n x) ((ihash x, x, v) # bs ! ibucket n x))"
    by (rule im_update_bucket_inv[OF inv subset_refl imap_inv_bucket_distinct[OF inv lt]
        hm_look_list_None_key[OF lk hb]])
  show "imap_map n (list_update bs (ibucket n x) ((ihash x, x, v) # bs ! ibucket n x))
      = (imap_map n bs)(x \<mapsto> v)"
    by (rule imap_map_insert[OF inv]) simp
qed

lemma im_update_Some:
  assumes inv: "imap_inv n bs" and lk: "hm_look_list (ihash x) x (bs ! ibucket n x) = Some u"
  shows "imap_inv n (list_update bs (ibucket n x)
            ((ihash x, x, v) # hm_del_list (ihash x) x (bs ! ibucket n x)))"
    and "imap_map n (list_update bs (ibucket n x)
            ((ihash x, x, v) # hm_del_list (ihash x) x (bs ! ibucket n x)))
       = (imap_map n bs)(x \<mapsto> v)"
proof -
  have lt: "ibucket n x < length bs" by (rule imap_inv_bucket_lt[OF inv])
  have hb: "\<forall>e \<in> set (bs ! ibucket n x). fst e = ihash (fst (snd e))"
    by (rule imap_inv_hash[OF inv lt])
  have db: "distinct (map (\<lambda>e. fst (snd e)) (bs ! ibucket n x))"
    by (rule imap_inv_bucket_distinct[OF inv lt])
  have km: "map (\<lambda>e. fst (snd e)) (hm_del_list (ihash x) x (bs ! ibucket n x))
      = removeAll x (map (\<lambda>e. fst (snd e)) (bs ! ibucket n x))"
    by (rule hm_del_list_eq[OF hb db])
  show "imap_inv n (list_update bs (ibucket n x)
            ((ihash x, x, v) # hm_del_list (ihash x) x (bs ! ibucket n x)))"
    by (rule im_update_bucket_inv[OF inv hm_del_list_set])
       (simp_all add: km db distinct_removeAll)
  show "imap_map n (list_update bs (ibucket n x)
            ((ihash x, x, v) # hm_del_list (ihash x) x (bs ! ibucket n x)))
      = (imap_map n bs)(x \<mapsto> v)"
    by (rule imap_map_insert[OF inv]) (rule hm_look_list_del[OF hb])
qed

lemma im_update_h_rule:
  "<is_imap m q> im_update_h q (ihash x) x v <\<lambda>q'. is_imap (m(x \<mapsto> v)) q'>\<^sub>t"
proof (cases q)
  case (fields n c a)
  have pre: "is_imap m (n, c, a) = (\<exists>\<^sub>Abs. a \<mapsto>\<^sub>a bs * \<up>(imap_inv n bs \<and> m = imap_map n bs))"
    by (simp add: is_imap_def)
  show ?thesis
    unfolding fields pre im_update_h_def Array.nth'_def Array.upd'_def
    by (sep_auto simp: ibucket_def[symmetric] imap_inv_bucket_lt is_imap_def
        im_update_None im_update_Some split: option.splits heap: im_grow_rule)
qed

lemma im_update_rule: "<is_imap m q> im_update q x v <\<lambda>q'. is_imap (m(x \<mapsto> v)) q'>\<^sub>t"
  unfolding im_update_def by (rule im_update_h_rule)

(*<*)
end
(*>*)
