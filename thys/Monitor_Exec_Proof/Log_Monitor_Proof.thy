(*<*)
theory Log_Monitor_Proof
  imports "Monitor_Exec.Log_Monitor" Prepare_Proof Tuple_Code_Proof "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



lemma hashcode_char_code: "hashcode (c :: char) = Uint32_signed (integer_of_char c)"
proof -
  have "0 \<le> (of_char c :: int) \<and> of_char c < (256 :: int)"
    using nat_of_char_less_256[of c] unfolding of_nat_of_char[where 'a=int, symmetric] by simp
  then have "\<not> (integer_of_char c < - 0x80000000 \<or> integer_of_char c \<ge> 0x80000000)"
    including integer.lifting unfolding integer_of_char_def by transfer simp
  then show ?thesis
    unfolding hashcode_char_def Uint32_signed_def integer_of_char_def
    including integer.lifting by (simp, transfer, simp)
qed

lemma nat_of_integer_Suc: "0 \<le> i \<Longrightarrow> nat_of_integer (i + 1) = Suc (nat_of_integer i)"
  including integer.lifting by transfer (simp add: Suc_nat_eq_nat_zadd1)

lemma nat_of_integer_less: "0 \<le> i \<Longrightarrow> i < integer_of_nat m \<Longrightarrow> nat_of_integer i < m"
  including integer.lifting by transfer simp

lemma nat_of_integer_ge: "\<not> i < integer_of_nat m \<Longrightarrow> m \<le> nat_of_integer i"
  including integer.lifting by transfer simp

lemma hash_bytes_foldl:
  "0 \<le> i \<Longrightarrow> n = bytes_length s \<Longrightarrow>
   hash_bytes s n i h = foldl (\<lambda>h c. h * hc_mult + hashcode c) h (drop (nat_of_integer i) (Rep_bytes s))"
proof (induction s n i h rule: hash_bytes.induct)
  case (1 s n i h)
  show ?case
  proof (cases "i < n")
    case True
    have k: "nat_of_integer i < length (Rep_bytes s)"
      using True 1(2,3) by (simp add: bytes_length_def nat_of_integer_less)
    have "drop (nat_of_integer i) (Rep_bytes s) =
      Rep_bytes s ! nat_of_integer i # drop (nat_of_integer (i + 1)) (Rep_bytes s)"
      using Cons_nth_drop_Suc[OF k] 1(2) by (simp add: nat_of_integer_Suc)
    then show ?thesis
      using True 1 by (subst hash_bytes.simps)
        (simp add: bytes_at_def hashcode_char_code[unfolded hashcode_char_def] del: hash_bytes.simps)
  next
    case False
    then have "length (Rep_bytes s) \<le> nat_of_integer i"
      using 1(3) by (simp add: bytes_length_def nat_of_integer_ge)
    then show ?thesis
      using False by (subst hash_bytes.simps) simp
  qed
qed

lemma lsig_lookup_length: "lsig_lookup S (p, n) = Some tys \<Longrightarrow> length tys = n"
  by (induction S) (auto simp: lsig_lookup_def split: if_splits)

lemma ix_list_fold: "ix_list (fold ix_add xs m) p = [(length tys, tys). (q, tys) \<leftarrow> rev xs, q = p] @ ix_list m p"
proof (induction xs arbitrary: m)
  case (Cons x xs)
  obtain q tys where x: "x = (q, tys)"
    by (cases x)
  show ?case
    using Cons[of "ix_add x m"] by (auto simp: x ix_list_def split: if_splits)
qed simp

lemma ix_list_lsig_index: "ix_list (lsig_index S) p = [(length tys, tys). (q, tys) \<leftarrow> S, q = p]"
proof -
  have "ix_list Mapping.empty p = []"
    by (simp add: ix_list_def)
  then show ?thesis
    by (simp add: lsig_index_def ix_list_fold)
qed

lemma index_lookup_lsig_index: "index_lookup (lsig_index S) = lsig_lookup S"
proof (rule ext)
  fix pn :: "Formula.name \<times> nat"
  obtain p n where pn: "pn = (p, n)"
    by (cases pn)
  show "index_lookup (lsig_index S) pn = lsig_lookup S pn"
    unfolding pn index_lookup_def ix_list_lsig_index lsig_lookup_def
    by (induction S) (auto split: if_splits)
qed

lemma Rep_prefix_of_list: "sorted (map snd xs) \<Longrightarrow> Rep_prefix (prefix_of_list xs) = xs"
  by (simp add: prefix_of_list.rep_eq)

lemma conv_field_string: "conv_field pf t f = field_of_string (sf pf) t (Rep_bytes f)"
  by (cases t) (simp_all add: conv_field_def field_of_string_def bint_of_correct string8_of_bytes_def
    Rep_bytes_inverse)

lemma conv_fields_string: "length tys = length fs \<Longrightarrow>
  opt_of_sum (conv_fields pf tys fs i) = those (map2 (field_of_string (sf pf)) tys (map Rep_bytes fs))"
proof (induction pf tys fs i rule: conv_fields.induct)
  case (1 pf t ts f fs i)
  then show ?case
    by (auto simp: conv_field_string split: option.splits)
qed auto

lemma conv_event_string: "opt_of_sum (conv_event pf (lsig_lookup S) e) = event_of_string (sf pf) S (abs_event e)"
proof -
  obtain p fs where e: "e = (p, fs)"
    by (cases e)
  show ?thesis
  proof (cases "lsig_lookup S (string8_of_bytes p, length fs)")
    case (Some tys)
    with conv_fields_string[OF lsig_lookup_length[OF Some], of pf 0] show ?thesis
      by (simp add: e conv_event_def event_of_string_def string8_of_bytes_def)
  qed (simp add: e conv_event_def event_of_string_def string8_of_bytes_def)
qed

lemma conv_events_string:
  "opt_of_sum (conv_events pf (lsig_lookup S) evs) = those (map (\<lambda>e. event_of_string (sf pf) S (abs_event e)) evs)"
proof (induction evs)
  case (Cons e evs)
  show ?case
  proof (cases "conv_event pf (lsig_lookup S) e")
    case (Inl err)
    with conv_event_string[of pf S e] show ?thesis
      by simp
  next
    case (Inr x)
    with conv_event_string[of pf S e, symmetric] Cons.IH[symmetric] show ?thesis
      by (simp add: opt_of_sum_def split: sum.splits)
  qed
qed simp

lemma conv_events_acc: "conv_events_acc pf L acc es = map_sum id ((@) (rev acc)) (conv_events pf L es)"
  by (induction pf L acc es rule: conv_events_acc.induct) (auto simp: map_sum_def split: sum.splits)

subsection \<open>Sorting\<close>

text \<open>The tuples of a table are sorted, without duplicates, before the table is built, so that
  the tree is built in one pass. The merge sort below merges the runs of increasing elements of
  the list, so that a sorted list is one run, and is tail recursive, since a time point may hold
  many events: merging onto an accumulator reverses the order, so a round of merges turns lists
  that increase into lists that decrease, and the next round merges those with the comparator
  turned around. It drops duplicates as it merges, and is proved to sort strictly, so that the
  tree can be built without checking that it is.\<close>

lemma comparator_converse:
  assumes "comparator c"
  shows "comparator (\<lambda>x y. c y x)"
proof
  fix x y z
  show "invert_order (c y x) = c x y"
    by (rule comparator.sym[OF assms])
  show "c y x = order.Eq \<Longrightarrow> x = y"
    using comparator.weak_eq[OF assms, of y x] by simp
  show "c y x = order.Lt \<Longrightarrow> c z y = order.Lt \<Longrightarrow> c z x = order.Lt"
    using comparator.comp_trans[OF assms, of z y x] by simp
qed

lemma set_cmerge: "comparator c \<Longrightarrow> set (cmerge c xs ys) = set xs \<union> set ys"
  by (induction c xs ys rule: cmerge.induct) (auto split: order.splits dest: comparator.weak_eq)

lemma sorted_cmerge: "comparator c \<Longrightarrow> sorted_wrt (lt_of_comp c) xs \<Longrightarrow> sorted_wrt (lt_of_comp c) ys \<Longrightarrow>
  sorted_wrt (lt_of_comp c) (cmerge c xs ys)"
proof (induction c xs ys rule: cmerge.induct)
  case (3 c x xs y ys)
  have tr: "lt_of_comp c a b \<Longrightarrow> lt_of_comp c b d \<Longrightarrow> lt_of_comp c a d" for a b d
    using comparator.comp_trans[OF 3(4), of a b d] by (simp add: comparator.Lt_lt_conv[OF 3(4)])
  note conv = comparator.Lt_lt_conv[OF 3(4)] comparator.Gt_lt_conv[OF 3(4)] comparator.eq_Eq_conv[OF 3(4)]
  from 3 show ?case
    by (auto simp: set_cmerge conv split: order.splits intro: tr)
qed simp_all

lemma cmerge_rev: "cmerge_rev c acc xs ys = rev (cmerge c xs ys) @ acc"
  by (induction c acc xs ys rule: cmerge_rev.induct) (auto simp: fold_Cons_rev split: order.splits)

lemma length_cmerge_pairs: "length (cmerge_pairs c acc xss) = length acc + (length xss + 1) div 2"
  by (induction c acc xss rule: cmerge_pairs.induct) auto

lemma set_cmerge_pairs: "comparator c \<Longrightarrow> \<Union> (set ` set (cmerge_pairs c acc xss)) = \<Union> (set ` set (acc @ xss))"
  by (induction c acc xss rule: cmerge_pairs.induct) (auto simp: cmerge_rev set_cmerge)

lemma sorted_rev_converse:
  "sorted_wrt (lt_of_comp (\<lambda>x y. c y x)) (rev xs) \<longleftrightarrow> sorted_wrt (lt_of_comp c) xs"
  "sorted_wrt (lt_of_comp c) (rev xs) \<longleftrightarrow> sorted_wrt (lt_of_comp (\<lambda>x y. c y x)) xs"
proof -
  have L: "lt_of_comp (\<lambda>x y. c y x) = (\<lambda>a b. lt_of_comp c b a)"
    by (simp add: fun_eq_iff lt_of_comp_def)
  show "sorted_wrt (lt_of_comp (\<lambda>x y. c y x)) (rev xs) \<longleftrightarrow> sorted_wrt (lt_of_comp c) xs"
    unfolding L sorted_wrt_rev by (rule refl)
  show "sorted_wrt (lt_of_comp c) (rev xs) \<longleftrightarrow> sorted_wrt (lt_of_comp (\<lambda>x y. c y x)) xs"
    unfolding L sorted_wrt_rev by (rule refl)
qed

lemma sorted_cmerge_pairs: "comparator c \<Longrightarrow> \<forall>a \<in> set xss. sorted_wrt (lt_of_comp c) a \<Longrightarrow>
    \<forall>a \<in> set acc. sorted_wrt (lt_of_comp (\<lambda>x y. c y x)) a \<Longrightarrow>
    \<forall>a \<in> set (cmerge_pairs c acc xss). sorted_wrt (lt_of_comp (\<lambda>x y. c y x)) a"
proof (induction c acc xss rule: cmerge_pairs.induct)
  case (1 c acc a b r)
  then show ?case
    using sorted_cmerge[of c a b] by (simp add: cmerge_rev sorted_rev_converse)
qed (simp_all add: sorted_rev_converse)

lemma cmerge_all: "comparator c \<Longrightarrow> \<forall>a \<in> set xss. sorted_wrt (lt_of_comp (if d then (\<lambda>x y. c y x) else c)) a \<Longrightarrow>
  set (cmerge_all c d xss) = \<Union> (set ` set xss) \<and> sorted_wrt (lt_of_comp c) (cmerge_all c d xss)"
proof (induction c d xss rule: cmerge_all.induct)
  case (2 c d a)
  then show ?case
    by (cases d) (simp_all add: sorted_rev_converse)
next
  case (3 c d a b r)
  let ?c = "if d then (\<lambda>x y. c y x) else c"
  have comp: "comparator ?c"
    using 3(2) comparator_converse[OF 3(2)] by (cases d) simp_all
  have conv: "(\<lambda>x y. ?c y x) = (if \<not> d then (\<lambda>x y. c y x) else c)"
    by auto
  have "\<forall>a \<in> set (cmerge_pairs ?c [] (a # b # r)). sorted_wrt (lt_of_comp (if \<not> d then (\<lambda>x y. c y x) else c)) a"
    using sorted_cmerge_pairs[OF comp, of "a # b # r" "[]"] 3(3) unfolding conv by simp
  with 3(1)[OF 3(2)] set_cmerge_pairs[OF comp, of "[]" "a # b # r"] show ?case
    by simp
qed simp

lemma sorted_runs_tc: "comparator c \<Longrightarrow> sorted_wrt (lt_of_comp c) (rev (x # cur)) \<Longrightarrow>
  \<forall>a \<in> set acc. sorted_wrt (lt_of_comp c) a \<Longrightarrow> \<forall>a \<in> set (runs_tc c x cur acc ys). sorted_wrt (lt_of_comp c) a"
proof (induction c x cur acc ys rule: runs_tc.induct)
  case (2 c x cur acc y ys)
  show ?case
  proof (cases "c x y = order.Lt")
    case True
    have "lt_of_comp c z y" if "z \<in> set (x # cur)" for z
    proof -
      have "z = x \<or> lt_of_comp c z x"
        using that 2(4) by (auto simp: sorted_wrt_append)
      then show ?thesis
        using True comparator.comp_trans[OF 2(3), of z x y] by (auto simp: comparator.Lt_lt_conv[OF 2(3)])
    qed
    then have "sorted_wrt (lt_of_comp c) (rev (y # x # cur))"
      using 2(4) by (simp add: sorted_wrt_append)
    with True 2 show ?thesis
      by simp
  next
    case False
    have A: "\<forall>a \<in> set (rev (x # cur) # acc). sorted_wrt (lt_of_comp c) a"
      using 2(4,5) by simp
    have S: "sorted_wrt (lt_of_comp c) (rev [y])"
      by simp
    have R: "runs_tc c x cur acc (y # ys) = runs_tc c y [] (rev (x # cur) # acc) ys"
      using False by simp
    show ?thesis
      unfolding R by (rule 2(2)[OF False 2(3) S A])
  qed
qed simp

lemma set_runs_tc: "\<Union> (set ` set (runs_tc c x cur acc ys)) = Set.insert x (set cur \<union> \<Union> (set ` set acc) \<union> set ys)"
  by (induction c x cur acc ys rule: runs_tc.induct) auto

lemma csort:
  assumes "comparator c"
  shows "set (csort c xs) = set xs" and "sorted_wrt (lt_of_comp c) (csort c xs)"
proof -
  have "set (csort c xs) = set xs \<and> sorted_wrt (lt_of_comp c) (csort c xs)"
  proof (cases xs)
    case (Cons x ys)
    have "\<forall>a \<in> set (runs_tc c x [] [] ys). sorted_wrt (lt_of_comp c) a"
      by (rule sorted_runs_tc[OF assms]) simp_all
    then have "set (cmerge_all c False (runs_tc c x [] [] ys)) = \<Union> (set ` set (runs_tc c x [] [] ys)) \<and>
      sorted_wrt (lt_of_comp c) (cmerge_all c False (runs_tc c x [] [] ys))"
      using cmerge_all[OF assms, of "runs_tc c x [] [] ys" False] by simp
    then show ?thesis
      unfolding Cons csort_def set_runs_tc by simp
  qed (simp add: csort_def)
  then show "set (csort c xs) = set xs" and "sorted_wrt (lt_of_comp c) (csort c xs)"
    by simp_all
qed

lemma add_ev_code: "add_ev (p, vs) g = add_evk (p, length vs) vs g"
  by (induction "(p, vs)" g rule: add_ev.induct) (auto simp: str8_eq_def prod_eq_iff)

text \<open>The groups have distinct keys, and each holds the tuples of its key.\<close>

lemma map_of_add_ev:
  "map_of (add_ev (p, vs) g) k =
   (if k = (p, length vs) then Some (vs # (case map_of g k of None \<Rightarrow> [] | Some xs \<Rightarrow> xs)) else map_of g k)"
  by (induction "(p, vs)" g rule: add_ev.induct) auto

lemma keys_add_ev: "fst ` set (add_ev (p, vs) g) = Set.insert (p, length vs) (fst ` set g)"
  by (induction "(p, vs)" g rule: add_ev.induct) auto

lemma distinct_add_ev: "distinct (map fst g) \<Longrightarrow> distinct (map fst (add_ev (p, vs) g))"
  by (induction "(p, vs)" g rule: add_ev.induct) (auto simp: keys_add_ev)

lemma map_of_fold_add_ev:
  "map_of (fold add_ev evs g) k = (case filter (\<lambda>e. (fst e, length (snd e)) = k) evs of
     [] \<Rightarrow> map_of g k
   | fs \<Rightarrow> Some (rev (map snd fs) @ (case map_of g k of None \<Rightarrow> [] | Some xs \<Rightarrow> xs)))"
proof (induction evs arbitrary: g)
  case (Cons e evs)
  obtain p vs where e: "e = (p, vs)"
    by (cases e)
  show ?case
    using Cons[of "add_ev (p, vs) g"]
    by (auto simp: e map_of_add_ev split: list.splits option.splits)
qed simp

lemma map_of_group_evs:
  "map_of (group_evs evs) k = (case filter (\<lambda>e. (fst e, length (snd e)) = k) evs of
     [] \<Rightarrow> None | fs \<Rightarrow> Some (rev (map snd fs)))"
  by (simp add: group_evs_def map_of_fold_add_ev split: list.splits)

lemma distinct_group_evs: "distinct (map fst (group_evs evs))"
proof -
  have "distinct (map fst (fold add_ev evs g))" if "distinct (map fst g)" for g
    using that
  proof (induction evs arbitrary: g)
    case (Cons e evs)
    then show ?case
      by (cases e) (simp add: distinct_add_ev)
  qed simp
  then show ?thesis
    by (simp add: group_evs_def)
qed

lemma lookup_fold_uinsert:
  assumes "distinct (map fst g)"
  shows "Mapping.lookup (fold (\<lambda>(k, xs) db. uinsert_table_into_db k (f xs) db) g db) k =
    (case map_of g k of Some xs \<Rightarrow> Some (case Mapping.lookup db k of None \<Rightarrow> [f xs] | Some T \<Rightarrow> map ((\<union>) (f xs)) T)
     | None \<Rightarrow> Mapping.lookup db k)"
  using assms
proof (induction g arbitrary: db)
  case (Cons a g)
  obtain k' xs' where a: "a = (k', xs')"
    by (cases a)
  from Cons.prems a have "k' \<notin> fst ` set g"
    by auto
  then have "map_of g k' = None"
    by (simp add: map_of_eq_None_iff)
  with Cons a show ?case
    by (auto simp: uinsert_table_into_db_def lookup_update_mapping_with split: option.splits)
qed simp

theorem build_db_mk_db: "build_db evs = mk_db (set evs)"
proof (rule mapping_eqI)
  fix k :: "Formula.name \<times> nat"
  obtain p n where k: "k = (p, n)"
    by (cases k)
  have lk: "Mapping.lookup (build_db evs) k = map_option (\<lambda>xs. [set xs]) (map_of (group_evs evs) k)"
    using lookup_fold_uinsert[of "group_evs evs" "\<lambda>xs. utable_of_list xs" uempty_db k] distinct_group_evs
    by (auto simp: build_db_def uempty_db_def utable_of_list_def ID_ccompare_etuple
      split: option.splits)
  have mk: "Mapping.lookup (mk_db (set evs)) (p, n) = (if \<exists>ts. (p, ts) \<in> set evs \<and> n = length ts
    then Some [{ts. (p, ts) \<in> set evs \<and> n = length ts}] else None)"
    by (simp add: Mapping.lookup.rep_eq mk_db.rep_eq)
  have f: "set (map snd (filter (\<lambda>e. (fst e, length (snd e)) = k) evs)) = {ts. (p, ts) \<in> set evs \<and> n = length ts}"
    by (force simp: k)
  have e: "filter (\<lambda>e. (fst e, length (snd e)) = k) evs = [] \<longleftrightarrow> \<not> (\<exists>ts. (p, ts) \<in> set evs \<and> n = length ts)"
    by (force simp: k filter_empty_conv)
  show "Mapping.lookup (build_db evs) k = Mapping.lookup (mk_db (set evs)) k"
  proof (cases "filter (\<lambda>e. (fst e, length (snd e)) = k) evs = []")
    case True
    then show ?thesis
      using lk mk e by (simp add: map_of_group_evs k)
  next
    case False
    then have "map_of (group_evs evs) k = Some (rev (map snd (filter (\<lambda>e. (fst e, length (snd e)) = k) evs)))"
      by (simp add: map_of_group_evs split: list.splits)
    then show ?thesis
      using lk mk e f False by (simp add: k)
  qed
qed

subsection \<open>Building the tables faster\<close>

text \<open>The tree of a table is built by @{const rbtreeify}, whose generated code computes with the
  natural numbers of the generated code, which wrap the integers. The copy below computes with the
  integers directly, and is proved to build the same tree.\<close>

lemma nat_of_integer_half: "\<not> n \<le> 0 \<Longrightarrow> n \<noteq> 1 \<Longrightarrow> nat_of_integer (n div 2) < nat_of_integer n"
  "\<not> n \<le> 1 \<Longrightarrow> nat_of_integer (n div 2) < nat_of_integer n"
  including integer.lifting by (transfer, auto)+

lemma integer_of_nat_rbt_simps:
  "integer_of_nat n \<le> 0 \<longleftrightarrow> n = 0" "integer_of_nat n \<le> 1 \<longleftrightarrow> n = 0 \<or> n = 1"
  "integer_of_nat n = 1 \<longleftrightarrow> n = 1"
  "Code_Numeral.divmod_abs (integer_of_nat n) 2 = (integer_of_nat (n div 2), integer_of_nat (n mod 2))"
  "integer_of_nat m = 0 \<longleftrightarrow> m = 0"
  by (simp_all add: integer_eq_iff less_eq_integer.rep_eq divmod_abs_def integer_of_nat.rep_eq
      zdiv_int zmod_int le_Suc_eq)

lemma rbtreeify_fi: "rbtreeify_fi (integer_of_nat n) kvs = rbtreeify_f n kvs"
  and rbtreeify_gi: "rbtreeify_gi (integer_of_nat n) kvs = rbtreeify_g n kvs"
proof -
  have fg: "rbtreeify_fi (integer_of_nat n) kvs = rbtreeify_f n kvs \<and>
      rbtreeify_gi (integer_of_nat n) kvs = rbtreeify_g n kvs" for n and kvs :: "('a \<times> 'b) list"
  proof (induction n arbitrary: kvs rule: less_induct)
    case (less n kvs)
    consider "n = 0" | "n = 1" | "1 < n"
      by linarith
    then show ?case
    proof cases
      case 3
      then have ne: "n \<noteq> 0" "n \<noteq> 1" and lt: "n div 2 < n"
        by simp_all
      show ?thesis
      proof
        show "rbtreeify_fi (integer_of_nat n) kvs = rbtreeify_f n kvs"
          by (subst rbtreeify_fi.simps, subst rbtreeify_f.simps)
            (simp only: integer_of_nat_rbt_simps less.IH[OF lt] ne if_False prod.case)
        show "rbtreeify_gi (integer_of_nat n) kvs = rbtreeify_g n kvs"
          by (subst rbtreeify_gi.simps, subst rbtreeify_g.simps)
            (simp only: integer_of_nat_rbt_simps less.IH[OF lt] ne if_False prod.case simp_thms)
      qed
    qed (simp_all add: rbtreeify_fi.simps rbtreeify_gi.simps rbtreeify_f.simps rbtreeify_g.simps
      integer_of_nat_rbt_simps)
  qed
  show "rbtreeify_fi (integer_of_nat n) kvs = rbtreeify_f n kvs"
    using fg by simp
  show "rbtreeify_gi (integer_of_nat n) kvs = rbtreeify_g n kvs"
    using fg by simp
qed

lemma ilen: "ilen acc xs = acc + integer_of_nat (length xs)"
  by (induction acc xs rule: ilen.induct) (simp_all add: integer_of_nat_eq_of_nat)

lemma rbtreeify_i: "rbtreeify_i kvs = rbtreeify kvs"
proof -
  have "ilen 1 kvs = integer_of_nat (Suc (length kvs))"
    by (simp add: ilen integer_of_nat_eq_of_nat)
  then show ?thesis
    by (simp add: rbtreeify_i_def rbtreeify_def rbtreeify_gi)
qed

text \<open>The tables of a time point are built with this sort and tree construction. The groups
  hold their tuples in the reverse order of the log; the code reverses them before sorting them,
  so that tuples that come sorted in the log are sorted in linear time.\<close>

lemma comparator_edl: "comparator ed_comparator"
  by (rule ID_ccompare'[OF ID_ccompare_etuple])

lemma conv_fields_a: "conv_fields_a pf tys fs acc = map_sum id ((@) (rev acc)) (conv_fields pf tys fs (length acc))"
  by (induction pf tys fs acc rule: conv_fields_a.induct) (auto simp: sum.map_comp comp_def split: option.splits)

lemma vskip_fun: "vskip_fun xs q \<longleftrightarrow> q \<in> set xs"
  by (auto simp: vskip_fun_def str8_eq_def list_ex_iff)

lemma vitems_acc: "vitems_acc cf xs z acc = (case vitems cf xs z of (vs, z') \<Rightarrow> (rev acc @ vs, z'))"
  by (induction cf xs z acc rule: vitems_acc.induct) (auto split: prod.splits)

lemma usteps_append: "usteps (tps1 @ tps2) ust = (case usteps tps1 ust of (vs1, ust1) \<Rightarrow>
  (case usteps tps2 ust1 of (vs2, ust2) \<Rightarrow> (vs1 @ vs2, ust2)))"
  by (induction tps1 ust rule: usteps.induct) (auto split: prod.splits)

lemma usteps_dmsteps0:
  "fst (usteps tps ust) = emsteps0_stateless (map (apfst set) tps) (ust)"
proof (induction tps arbitrary: ust)
  case (Cons tp tps)
  obtain xs t where tp: "tp = (xs, t)"
    by (cases tp)
  obtain vs1 ust1 where u: "emstep (build_db xs, t) ust = (vs1, ust1)"
    by fastforce
  have "emstep (mk_db (set xs), t) ust = (vs1, ust1)"
    using u by (simp add: build_db_mk_db)
  then show ?case
    using Cons.IH[of ust1] u by (cases "usteps tps ust1") (simp add: tp)
qed simp

lemma conv_item_string:
  assumes "vc_lookup cf = lsig_lookup (vc_lsig cf)"
  shows "map_option (apfst set) (conv_item cf x) = tp_of_item (sf (vc_pf cf)) (vc_lsig cf) (map_item Rep_bytes x)"
proof (cases x)
  case (Entry ts evs)
  have "those (map (event_of_string (sf (vc_pf cf)) (vc_lsig cf)) (map abs_event evs)) =
    opt_of_sum (conv_events (vc_pf cf) (vc_lookup cf) evs)"
    by (simp add: assms conv_events_string comp_def)
  then show ?thesis
    by (auto simp: Entry conv_item_def tp_of_item_def conv_entry_def bnat_of_correct opt_of_sum_def
      split: option.splits sum.splits)
qed (simp add: conv_item_def tp_of_item_def)

lemma vitem_None: "conv_item cf e = None \<Longrightarrow> \<exists>err. vitem cf (O_ITEM sp e) z = (VO_ERROR sp err, z)"
  by (auto simp: vitem_def conv_item_def conv_entry_def opt_of_sum_def split: item.splits sum.splits option.splits)

lemma vitem_Some:
  assumes "conv_item cf e = Some (xs, t)"
  shows "vitem cf (O_ITEM sp e) z = vtp sp xs t z"
proof -
  obtain ts evs where e: "e = Entry ts evs"
    using assms by (cases e) (auto simp: conv_item_def)
  obtain t' where t: "bnat_of ts = Some t'"
    using assms by (cases "bnat_of ts") (auto simp: e conv_item_def conv_entry_def)
  obtain ys where c: "conv_events (vc_pf cf) (vc_lookup cf) evs = Inr ys"
    using assms by (cases "conv_events (vc_pf cf) (vc_lookup cf) evs") (auto simp: e t conv_item_def conv_entry_def)
  have "ys = xs" "t' = t"
    using assms by (simp_all add: e t c conv_item_def conv_entry_def)
  then show ?thesis
    by (simp add: vitem_def e t c)
qed

lemma vitems_has_err: "has_err xs \<Longrightarrow> has_verror (fst (vitems cf xs z))"
proof (induction cf xs z rule: vitems.induct)
  case (2 cf x xs z)
  obtain v z1 where v: "vitem cf x z = (v, z1)"
    by (metis prod.exhaust)
  show ?case
  proof (cases x)
    case (O_ITEM sp e)
    with "2.prems" have "has_err xs"
      by simp
    with "2.IH"[OF v[symmetric]] v show ?thesis
      by (auto split: prod.splits vout.splits)
  qed (use v in \<open>auto simp: vitem_def split: prod.splits\<close>)
qed simp

text \<open>Without errors, the items are converted and their timestamps do not decrease, and the
  verdicts are those of the monitor on the time points.\<close>

lemma vitems_ok:
  assumes "oks xs = Some es" "vitems cf xs (ust, lt) = (vs, z')" "\<not> has_verror vs"
  shows "\<exists>tps. those (map (conv_item cf) es) = Some tps \<and> sorted (lt # map snd tps) \<and>
    vverdicts vs = fst (usteps tps ust) \<and> z' = (snd (usteps tps ust), last (lt # map snd tps))"
  using assms
proof (induction xs arbitrary: es ust lt vs z')
  case (Cons x xs)
  from Cons.prems(1) obtain sp e es' where x: "x = O_ITEM sp e" and es: "es = e # es'"
    and oks: "oks xs = Some es'"
    by (cases x) auto
  obtain v z1 where v: "vitem cf x (ust, lt) = (v, z1)"
    by (metis prod.exhaust)
  obtain vs' where vs': "vitems cf xs z1 = (vs', z')" and vs: "vs = v # vs'"
    using Cons.prems(2) v by (auto split: prod.splits)
  have ok: "\<not> has_verror (v # vs')"
    using Cons.prems(3) vs by simp
  obtain ys t where c: "conv_item cf e = Some (ys, t)"
    using vitem_None[of cf e sp "(ust, lt)"] v ok x by (cases "conv_item cf e") auto
  obtain vs1 ust1 where u: "emstep (build_db ys, t) ust = (vs1, ust1)"
    by fastforce
  have t: "\<not> t < lt" and v1: "v = VO_VERDICTS vs1" and z1: "z1 = (ust1, t)"
    using v ok vitem_Some[OF c, of sp "(ust, lt)"] u x by (auto simp: vtp_def split: if_splits)
  have "\<not> has_verror vs'"
    using ok by (auto split: vout.splits)
  then obtain tps where "those (map (conv_item cf) es') = Some tps" "sorted (t # map snd tps)"
    "vverdicts vs' = fst (usteps tps ust1)" "z' = (snd (usteps tps ust1), last (t # map snd tps))"
    using Cons.IH[OF oks vs'[unfolded z1]] by blast
  then show ?case
    using c t u es vs v1
    by (intro exI[of _ "(ys, t) # tps"]) (auto split: prod.splits)
qed simp

lemma vitems_noerr:
  assumes "oks xs = Some es" "those (map (conv_item cf) es) = Some tps" "sorted (lt # map snd tps)"
  shows "\<not> has_verror (fst (vitems cf xs (ust, lt)))"
  using assms
proof (induction xs arbitrary: es tps ust lt)
  case (Cons x xs)
  from Cons.prems(1) obtain sp e es' where x: "x = O_ITEM sp e" and es: "es = e # es'"
    and oks: "oks xs = Some es'"
    by (cases x) auto
  from Cons.prems(2) es obtain ys t tps' where c: "conv_item cf e = Some (ys, t)"
    and tps: "those (map (conv_item cf) es') = Some tps'" "tps = (ys, t) # tps'"
    by (auto split: option.splits)
  obtain vs1 ust1 where u: "emstep (build_db ys, t) ust = (vs1, ust1)"
    by fastforce
  from Cons.prems(3) tps have "lt \<le> t" "sorted (t # map snd tps')"
    by auto
  with Cons.IH[OF oks tps(1), of t ust1] vitem_Some[OF c, of sp "(ust, lt)"] u x show ?case
    by (auto simp: vtp_def split: prod.splits)
qed simp

subsubsection \<open>The prefix a log denotes is well typed and finite\<close>

lemma those_map_option: "those (map (map_option g) xs) = map_option (map g) (those xs)"
  by (induction xs) (simp_all add: option.map_comp comp_def split: option.splits)

lemma those_Some_in: "those (map f xs) = Some ys \<Longrightarrow> y \<in> set ys \<Longrightarrow> \<exists>x\<in>set xs. f x = Some y"
  by (induction xs arbitrary: ys) (auto split: option.splits)

lemma field_of_string_ty: "field_of_string pf t f = Some x \<Longrightarrow> ty_of x = t"
  by (cases t) (auto simp: field_of_string_def)

lemma those_map2_field_of_string:
  "those (map2 (field_of_string pf) tys fs) = Some xs \<Longrightarrow> length tys = length fs \<Longrightarrow> wty_tuple tys xs"
proof (induction tys arbitrary: fs xs)
  case (Cons t tys)
  then obtain f fs' where "fs = f # fs'"
    by (cases fs) auto
  with Cons show ?case
    by (auto simp: wty_tuple_def field_of_string_ty split: option.splits)
qed (simp add: wty_tuple_def)

lemma event_of_string_wty:
  assumes "event_of_string pf S e = Some x"
  shows "wty_event (lsig_lookup S) (fst x) (snd x)"
proof -
  obtain p fs where e: "e = (p, fs)"
    by (cases e)
  with assms obtain tys xs where tys: "lsig_lookup S (Abs_string8 p, length fs) = Some tys"
    and xs: "those (map2 (field_of_string pf) tys fs) = Some xs" and x: "x = (Abs_string8 p, xs)"
    by (auto simp: event_of_string_def split: option.splits)
  have w: "wty_tuple tys xs"
    using those_map2_field_of_string[OF xs lsig_lookup_length[OF tys]] .
  then have "length xs = length fs"
    using lsig_lookup_length[OF tys] by (simp add: wty_tuple_def list_all2_lengthD)
  with tys w x show ?thesis
    by (simp add: wty_event_def)
qed

lemma tp_of_item_wty: "tp_of_item pf S it = Some tp \<Longrightarrow> wty_db (lsig_lookup S) (fst tp) \<and> finite (fst tp)"
  by (fastforce simp: tp_of_item_def wty_db_def dest: those_Some_in event_of_string_wty
    split: item.splits option.splits)

lemma prefix_of_items_Some:
  assumes "prefix_of_items pf S fin items = Some \<pi>"
  obtains tps where "those (map (tp_of_item pf S) items) = Some tps"
    and "sorted (map snd (tps @ (case fin of None \<Rightarrow> [] | Some t \<Rightarrow> [({}, t)])))"
    and "Rep_prefix \<pi> = tps @ (case fin of None \<Rightarrow> [] | Some t \<Rightarrow> [({}, t)])"
  using assms by (auto simp: prefix_of_items_def Let_def Rep_prefix_of_list split: option.splits if_splits)

lemma prefix_of_items_wty:
  assumes "prefix_of_items pf S fin items = Some \<pi>"
  shows "wty_prefix (lsig_lookup S) \<pi>" and "pfinite \<pi>"
proof -
  obtain tps where tps: "those (map (tp_of_item pf S) items) = Some tps"
    and R: "Rep_prefix \<pi> = tps @ (case fin of None \<Rightarrow> [] | Some t \<Rightarrow> [({}, t)])"
    using prefix_of_items_Some[OF assms] by blast
  have H: "wty_db (lsig_lookup S) (fst tp) \<and> finite (fst tp)" if "tp \<in> set (Rep_prefix \<pi>)" for tp
  proof -
    from that R consider "tp \<in> set tps" | "fst tp = {}"
      by (auto split: option.splits)
    then show ?thesis
    proof cases
      case 1
      then obtain it where "tp_of_item pf S it = Some tp"
        using those_Some_in[OF tps] by blast
      then show ?thesis
        by (rule tp_of_item_wty)
    qed (simp add: wty_db_def)
  qed
  then show "wty_prefix (lsig_lookup S) \<pi>" and "pfinite \<pi>"
    by (simp_all add: wty_prefix.rep_eq pfinite.rep_eq)
qed

subsubsection \<open>The time points of the items\<close>

lemma sorted_snoc_last: "sorted ((a :: nat) # ys) \<Longrightarrow> sorted ((a # ys) @ [t]) \<longleftrightarrow> last (a # ys) \<le> t"
proof (induction ys arbitrary: a)
  case (Cons y ys)
  then show ?case
    by auto
qed simp

lemma those_conv_item:
  assumes "vc_lookup cf = lsig_lookup (vc_lsig cf)"
  shows "those (map (tp_of_item (sf (vc_pf cf)) (vc_lsig cf)) (abs_items es)) =
    map_option (map (apfst set)) (those (map (conv_item cf) es))"
  by (simp add: comp_def conv_item_string[OF assms, symmetric] those_map_option[symmetric])

subsection \<open>The verdicts depend only on the events of the predicates that occur freely\<close>

text \<open>An event that a formula matches is one of a predicate that occurs freely in it.\<close>

lemma matches_preds: "Safety.matches v \<phi> e \<Longrightarrow> (fst e, length (snd e)) \<in> Rewriting.preds \<phi>"
proof (induction \<phi> arbitrary: v e)
  case (LetPast p \<phi> \<psi>)
  from LetPast.prems have ne: "(fst e, length (snd e)) \<noteq> (p, Formula.nfv \<phi>)"
    by auto
  from LetPast.prems obtain e' where r: "(\<lambda>e' e. Safety.matches (snd e') \<phi> e \<and> fst e' = p \<and>
      length (snd e') = Formula.nfv \<phi>)\<^sup>*\<^sup>* e' e" and m: "Safety.matches v \<psi> e'"
    by auto
  from r show ?case
  proof (cases rule: rtranclp.cases)
    case rtrancl_refl
    with LetPast.IH(2)[OF m] ne show ?thesis
      by simp
  next
    case (rtrancl_into_rtrancl b)
    with LetPast.IH(1)[of "snd b" e] ne show ?thesis
      by simp
  qed
qed (fastforce simp: fv_regex_alt)+

lemma pmap_\<Gamma>_pmap_\<Gamma>: "pmap_\<Gamma> f (pmap_\<Gamma> g \<pi>) = pmap_\<Gamma> (f \<circ> g) \<pi>"
  by transfer (auto split: prod.splits)

lemma wty_prefix_pmap_\<Gamma>_Int: "wty_prefix S \<pi> \<Longrightarrow> wty_prefix S (pmap_\<Gamma> (\<lambda>D. D \<inter> E) \<pi>)"
  by (fastforce simp: wty_prefix.rep_eq pmap_\<Gamma>.rep_eq wty_db_def)

text \<open>Restricting a well-typed prefix to a superset of the relevant events does not change the
  verdicts.\<close>

lemma (in future_bounded_mfodl) Mt_restrict:
  assumes wty: "wty_prefix SIG \<pi>" and E: "\<And>v e. Safety.matches v \<phi> e \<Longrightarrow> e \<in> E"
  shows "Mt (pmap_\<Gamma> (\<lambda>D. D \<inter> E) \<pi>) = Mt \<pi>"
proof -
  let ?\<pi>E = "pmap_\<Gamma> (\<lambda>D. D \<inter> E) \<pi>"
  have p: "\<pi> \<in> formula_slicer.prefixes" and pE: "?\<pi>E \<in> formula_slicer.prefixes"
    using wty wty_prefix_pmap_\<Gamma>_Int[OF wty] by (auto simp: prefixes_alt)
  have "(\<lambda>D. D \<inter> E \<inter> relevant_events \<phi> UNIV) = (\<lambda>D. D \<inter> relevant_events \<phi> UNIV)"
    using E by auto
  then have eq: "pmap_\<Gamma> (\<lambda>D. D \<inter> relevant_events \<phi> UNIV) ?\<pi>E =
    pmap_\<Gamma> (\<lambda>D. D \<inter> relevant_events \<phi> UNIV) \<pi>"
    by (simp only: pmap_\<Gamma>_pmap_\<Gamma> comp_def)
  have "(i, v) \<in> M ?\<pi>E \<longleftrightarrow> (i, v) \<in> M \<pi>" for i v
  proof (cases "wf_tuple (Formula.fv_list \<phi>) v")
    case True
    let ?y = "map (tup_get (Formula.fv_list \<phi>) v) [0..<Suc (Max (Set.insert 0 (Formula.fv \<phi>)))]"
    have "mem_restr UNIV (Formula.fv_list \<phi>) v"
      by (rule mem_restrI[where y = ?y]) (auto simp: True less_Suc_eq_le simp del: upt_Suc intro: Max_ge)
    then show ?thesis
      using sliceable_M[OF p, of UNIV v i] sliceable_M[OF pE, of UNIV v i] eq by simp
  qed (simp add: M_def)
  then have "M ?\<pi>E = M \<pi>"
    by auto
  then show ?thesis
    by (simp add: Mt_def)
qed

lemma vinit_Inr:
  assumes "vinit ix mw rw filt S pf \<phi> = Inr (cf, z)"
  obtains ust where "cf = VConf (vskip_fun (vskip filt \<phi> S)) S (lsig_lookup_fun S) pf" "z = (einit, ust, 0)"
    "wf_formula \<phi>" "eminit_verimon ix mw rw (lsig_tsig S) \<phi> = Inr ust" "efail_nodes (eabs (emstate_m ust)) = 0"
  using assms by (auto simp: vinit_def Let_def split: if_splits sum.splits)

lemma sk_vkeep: "sk (vkeep (VConf (vskip_fun (vskip filt \<phi> S)) S' L pf)) = keep_spec filt \<phi> S"
  by (auto simp: fun_eq_iff sk_def vkeep_def vskip_fun vskip_def Let_def keep_spec_def string8_of_bytes_def
      Abs_bytes_inverse)
text \<open>Filtering the items restricts the prefix they denote to the events kept.\<close>

lemma those_map_cong: "those (map f xs) = Some ys \<Longrightarrow> (\<And>x y. f x = Some y \<Longrightarrow> g x = Some (h y)) \<Longrightarrow>
  those (map g xs) = Some (map h ys)"
  by (induction xs arbitrary: ys) (auto split: option.splits)

lemma those_filter: "those (map f xs) = Some ys \<Longrightarrow> (\<And>x y. f x = Some y \<Longrightarrow> P x \<longleftrightarrow> Q y) \<Longrightarrow>
  those (map f (filter P xs)) = Some (filter Q ys)"
  by (induction xs arbitrary: ys) (auto split: option.splits)

lemma event_of_string_fst: "event_of_string pf S e = Some x \<Longrightarrow> fst x = Abs_string8 (fst e)"
  by (auto simp: event_of_string_def split: option.splits prod.splits)

lemma tp_of_item_filter:
  assumes "tp_of_item pf S it = Some tp"
  shows "tp_of_item pf S (filter_item K it) = Some (apfst (\<lambda>D. D \<inter> {e. K (Rep_string8 (fst e))}) tp)"
proof (cases it)
  case (Entry ts evs)
  with assms obtain t xs where t: "nat_of_string ts = Some t" and xs: "those (map (event_of_string pf S) evs) = Some xs"
    and tp: "tp = (set xs, t)"
    by (auto simp: tp_of_item_def split: option.splits)
  have "those (map (event_of_string pf S) (filter (K \<circ> fst) evs)) = Some (filter (\<lambda>e. K (Rep_string8 (fst e))) xs)"
    by (rule those_filter[OF xs]) (auto dest: event_of_string_fst simp: Abs_string8_inverse)
  then show ?thesis
    by (auto simp: Entry tp_of_item_def t tp)
qed (use assms in \<open>simp add: tp_of_item_def\<close>)

lemma prefix_of_list_map: "sorted (map snd xs) \<Longrightarrow> prefix_of_list (map (apfst f) xs) = pmap_\<Gamma> f (prefix_of_list xs)"
  by transfer (auto simp: comp_def apfst_def map_prod_def split_beta)

lemma prefix_of_items_filter:
  assumes "prefix_of_items pf S fin items = Some \<pi>"
  shows "prefix_of_items pf S fin (map (filter_item K) items) = Some (pmap_\<Gamma> (\<lambda>D. D \<inter> {e. K (Rep_string8 (fst e))}) \<pi>)"
proof -
  let ?g = "\<lambda>D. D \<inter> {e. K (Rep_string8 (fst e))}"
  let ?fin = "case fin of None \<Rightarrow> [] | Some t \<Rightarrow> [({}, t)]"
  obtain tps where tps: "those (map (tp_of_item pf S) items) = Some tps"
    and srt: "sorted (map snd (tps @ ?fin))" and \<pi>: "\<pi> = prefix_of_list (tps @ ?fin)"
    using assms by (auto simp: prefix_of_items_def Let_def split: option.splits if_splits)
  have "those (map (tp_of_item pf S) (map (filter_item K) items)) = Some (map (apfst ?g) tps)"
    using those_map_cong[OF tps, of "tp_of_item pf S \<circ> filter_item K" "apfst ?g"] tp_of_item_filter
    by (simp add: comp_def)
  moreover have "map (apfst ?g) tps @ ?fin = map (apfst ?g) (tps @ ?fin)"
    by (simp split: option.splits)
  ultimately show ?thesis
    using srt prefix_of_list_map[OF srt, of ?g]
    by (simp add: prefix_of_items_def \<pi> comp_def del: map_append split: option.splits)
qed

lemma map_sig_lsig: "map_sig (convert_tysym o check_subst) (lsig_tsig S) = lsig_lookup S"
proof -
  have "convert_tysym (check_subst (TCst x)) = x" for x
    using wf_f_check_subst unfolding wf_f_def by (metis comp_apply tysym.inject(3))
  then show ?thesis
    by (auto simp: fun_eq_iff map_sig_def lsig_tsig_def option.map_comp comp_def option.map_ident)
qed

context
  fixes mw :: bool
begin

interpretation monitor_\<phi>: future_bounded_mfodl "Formula.formula.map_formula (convert_tysym \<circ> check_subst) \<phi>"
  "map_sig (convert_tysym o check_subst) (lsig_tsig S)" "convert_tysym o check_subst o TAny"
  using future_bounded_\<phi> by (auto simp: future_bounded_mfodl_def future_bounded_mfodl_axioms_def wty_mfodl_def)

text \<open>The verdicts depend only on the events of the predicates that occur freely in the
  formula.\<close>

theorem Mt_preds:
  assumes "wty_prefix (lsig_lookup S) \<pi>" "wty_prefix (lsig_lookup S) \<pi>'"
    and "pmap_\<Gamma> (\<lambda>D. D \<inter> {e. (fst e, length (snd e)) \<in> Rewriting.preds \<phi>}) \<pi> =
      pmap_\<Gamma> (\<lambda>D. D \<inter> {e. (fst e, length (snd e)) \<in> Rewriting.preds \<phi>}) \<pi>'"
  shows "monitor_\<phi>.Mt \<pi> = monitor_\<phi>.Mt \<pi>'"
proof -
  have E: "Safety.matches v (Formula.formula.map_formula (convert_tysym \<circ> check_subst) \<phi>) e \<Longrightarrow>
    e \<in> {e. (fst e, length (snd e)) \<in> Rewriting.preds \<phi>}" for v e
    using matches_preds[of v "Formula.formula.map_formula (convert_tysym \<circ> check_subst) \<phi>" e] by simp
  from assms show ?thesis
    using monitor_\<phi>.Mt_restrict[OF _ E, of \<pi>] monitor_\<phi>.Mt_restrict[OF _ E, of \<pi>']
    by (simp add: map_sig_lsig)
qed

end

end

text \<open>The monitor starts only if the assumptions of the locale hold.\<close>

lemma vinit_verimon_log:
  assumes "vinit ix mw rw filt S pf \<phi> = Inr (cf, z)"
  shows "verimon_log rw S \<phi>"
proof -
  obtain ust where "wf_formula \<phi>" "eminit_verimon ix mw rw (lsig_tsig S) \<phi> = Inr ust"
    using vinit_Inr[OF assms] by metis
  then show ?thesis
    by (cases "prepare_verimon rw (lsig_tsig S) \<phi>")
      (auto simp: verimon_log_def verimon_prepare_def eminit_verimon_def)
qed

(*<*)
end
(*>*)
