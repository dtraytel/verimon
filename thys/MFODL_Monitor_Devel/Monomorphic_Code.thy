(*<*)
theory Monomorphic_Code
  imports Code_Opt
begin
(*>*)

section \<open>Two adaptations of the generated code\<close>

text \<open>
  @{const literal_string8} is the identity on the common string representation; the adaptation
  in @{text Event_Data} prints it as @{text id}, and the generated code prints a direct
  identity instead.  And a union of the sets of two lists is built as the set of their
  concatenation, in one pass (the Since structures' result over their two queues).  Both used
  to come in with the libraries of the imperative join, which is no longer part of the session.
\<close>

code_printing
  constant "literal_string8 :: string8 \<Rightarrow> String.literal" \<rightharpoonup> (OCaml) "(fun x -> x)"

lemma set_union_code[code_unfold]: "set xs \<union> set ys = set (xs @ ys)"
  by simp

section \<open>Monomorphisation of the hot code as a refinement\<close>

text \<open>
  The generated code passes type class dictionaries (@{class ceq}, @{class ccompare}, \dots) at
  run time. For the tuple type @{typ "event_data tuple"} these dictionaries are composite
  (@{text "ccompare_list (ccompare_option ccompare_event_data)"}) and are rebuilt at every
  call of a polymorphic function that constructs them from its own dictionary parameters, in
  particular in the per-tuple inner loops of the joins and of the auxiliary structures.

  This theory removes that overhead by a refinement at the level of code equations, without
  changing any definition or correctness proof of the monitor:
  \<^item> for each polymorphic function @{text f} of the implementation that is hot at type
    @{typ event_data}, a monomorphic copy @{text "ed_f = f"} is introduced whose code equations
    are the code equations of @{text f} instantiated to @{typ event_data} (derived by the
    kernel from the definition @{text "ed_f = f"}), and all applied occurrences of @{text f} at
    that type are redirected to @{text ed_f} by a @{text code_unfold} rule;
  \<^item> for each generic container operation @{text c} used at a closed type involving tuples of
    event data, a nullary constant @{text "c_v = Box c"} is introduced. The generated code for a
    nullary constant of a non-function type is a value, so the dictionaries of @{text c} at that
    type are built once, when the program starts; @{text "c x = unbox c_v x"} redirects the calls.
  Both constructions are automated in \<^file>\<open>monomorphize.ML\<close>.
\<close>

subsection \<open>A direct comparator on tuples of event data\<close>

fun ed_comparator :: "event_data tuple comparator" where
  "ed_comparator [] [] = Eq"
| "ed_comparator [] (y # ys) = Lt"
| "ed_comparator (x # xs) [] = Gt"
| "ed_comparator (a # xs) (b # ys) =
    (case comparator_event_data a b of Eq \<Rightarrow> ed_comparator xs ys | r \<Rightarrow> r)"

lemma ed_comparator_eq: "ed_comparator xs ys = comparator_list comparator_event_data xs ys"
  by (induction xs ys rule: ed_comparator.induct) (auto split: order.splits)

lemma ccompare_etuple: "CCOMPARE(event_data tuple) = Some ed_comparator"
  by (simp add: ccompare_list_def ccompare_event_data_def ID_def ed_comparator_eq[abs_def])

lemma ID_ccompare_etuple: "ID CCOMPARE(event_data tuple) = Some ed_comparator"
  by (simp add: ccompare_etuple ID_def)

lemma ccomp_etuple: "(ccomp :: event_data tuple comparator) = ed_comparator"
  by (simp add: ID_ccompare_etuple)

lemma ceq_etuple: "CEQ(event_data tuple) = Some (equality_list (=))"
  by (simp add: ceq_list_def ceq_event_data_def ID_def)

lemma ID_ceq_etuple: "ID CEQ(event_data tuple) = Some (equality_list (=))"
  by (simp add: ceq_etuple ID_def)

lemmas etuple_dict_simps = ccompare_etuple ID_ccompare_etuple ccomp_etuple ceq_etuple ID_ceq_etuple
  option.case option.sel ID_def id_apply

subsection \<open>Folds over red-black trees without the @{type comp_fun_idem} wrapper\<close>

lemma set_fold_cfi_RBT:
  fixes rbt :: "'a :: ccompare set_rbt"
  assumes "comp_fun_idem_apply g = f"
  shows "set_fold_cfi g b (RBT_set rbt) = (case ID CCOMPARE('a) of
      None \<Rightarrow> Code.abort s (\<lambda>_. set_fold_cfi g b (RBT_set rbt))
    | Some _ \<Rightarrow> RBT_Set2.fold f rbt b)"
proof (cases "ID CCOMPARE('a)")
  case None
  then show ?thesis by simp
next
  case (Some c)
  then show ?thesis by (subst set_fold_cfi_code(1)) (simp add: assms)
qed

datatype 'a boxed = Box (unbox: 'a)

ML_file \<open>monomorphize.ML\<close>

subsection \<open>Empty tables and mappings as values\<close>

lemma RBT_Mapping_empty: "RBT_Mapping RBT_Mapping2.empty = Mapping.empty"
  by (simp add: Mapping.empty_def)

definition ed_bot :: "event_data table" where "ed_bot = {}"

lemma ed_bot_code[code]: "ed_bot = RBT_set RBT_Set2.empty"
  by (simp add: ed_bot_def)

lemma ed_bot_unfold[code_unfold]:
  "(bot :: event_data table) = ed_bot"
  "set_empty (of_phantom SET_IMPL(event_data tuple)) = ed_bot"
  "(empty_table :: event_data table) = ed_bot"
  by (simp_all add: ed_bot_def empty_table_def)

definition ed_mempty_nat :: "(event_data tuple, nat) mapping" where "ed_mempty_nat = Mapping.empty"
lemma ed_mempty_nat_code[code]: "ed_mempty_nat = RBT_Mapping RBT_Mapping2.empty"
  by (simp only: ed_mempty_nat_def RBT_Mapping_empty)
lemma ed_mempty_nat_unfold[code_unfold]:
  "(Mapping.empty :: (event_data tuple, nat) mapping) = ed_mempty_nat"
  "(mapping_empty (of_phantom MAPPING_IMPL(event_data tuple)) :: (event_data tuple, nat) mapping) = ed_mempty_nat"
  by (simp_all add: ed_mempty_nat_def)

definition ed_mempty_tstp :: "(event_data tuple, nat + nat) mapping" where "ed_mempty_tstp = Mapping.empty"
lemma ed_mempty_tstp_code[code]: "ed_mempty_tstp = RBT_Mapping RBT_Mapping2.empty"
  by (simp only: ed_mempty_tstp_def RBT_Mapping_empty)
lemma ed_mempty_tstp_unfold[code_unfold]:
  "(Mapping.empty :: (event_data tuple, nat + nat) mapping) = ed_mempty_tstp"
  "(mapping_empty (of_phantom MAPPING_IMPL(event_data tuple)) :: (event_data tuple, nat + nat) mapping) = ed_mempty_tstp"
  by (simp_all add: ed_mempty_tstp_def)

definition ed_mempty_table :: "(event_data tuple, event_data table) mapping" where "ed_mempty_table = Mapping.empty"
lemma ed_mempty_table_code[code]: "ed_mempty_table = RBT_Mapping RBT_Mapping2.empty"
  by (simp only: ed_mempty_table_def RBT_Mapping_empty)
lemma ed_mempty_table_unfold[code_unfold]:
  "(Mapping.empty :: (event_data tuple, event_data table) mapping) = ed_mempty_table"
  "(mapping_empty (of_phantom MAPPING_IMPL(event_data tuple)) :: (event_data tuple, event_data table) mapping) = ed_mempty_table"
  by (simp_all add: ed_mempty_table_def)

definition ed_mempty_sum :: "(event_data tuple, nat \<times> integer) mapping" where "ed_mempty_sum = Mapping.empty"
lemma ed_mempty_sum_code[code]: "ed_mempty_sum = RBT_Mapping RBT_Mapping2.empty"
  by (simp only: ed_mempty_sum_def RBT_Mapping_empty)
lemma ed_mempty_sum_unfold[code_unfold]:
  "(Mapping.empty :: (event_data tuple, nat \<times> integer) mapping) = ed_mempty_sum"
  "(mapping_empty (of_phantom MAPPING_IMPL(event_data tuple)) :: (event_data tuple, nat \<times> integer) mapping) = ed_mempty_sum"
  by (simp_all add: ed_mempty_sum_def)

definition ed_mempty_rank :: "(event_data tuple, list_aux) mapping" where "ed_mempty_rank = Mapping.empty"
lemma ed_mempty_rank_code[code]: "ed_mempty_rank = RBT_Mapping RBT_Mapping2.empty"
  by (simp only: ed_mempty_rank_def RBT_Mapping_empty)
lemma ed_mempty_rank_unfold[code_unfold]:
  "(Mapping.empty :: (event_data tuple, list_aux) mapping) = ed_mempty_rank"
  "(mapping_empty (of_phantom MAPPING_IMPL(event_data tuple)) :: (event_data tuple, list_aux) mapping) = ed_mempty_rank"
  by (simp_all add: ed_mempty_rank_def)

ML \<open>
val etuple = "event_data tuple"
val ed_value_types =
  [("nat", "nat"), ("tstp", "nat + nat"), ("table", "event_data table"),
   ("sum", "nat \<times> integer"), ("rank", "list_aux")]
val ed_mapping_ops =
  [("Mapping.keys", "keys"), ("Mapping.is_empty", "mis_empty")]
val ed_box_specs =
  [
   ("finite", "ed_finite_v", [etuple]),
   ("set_eq", "ed_set_eq_v", [etuple]),
   ("Set.is_empty", "ed_is_empty_v", [etuple]),
   ("RBT_Set2.fold", "ed_rbt_fold_table_v", [etuple, "event_data table"]),
   ("cluster", "ed_cluster_ed_v", [etuple, "event_data"]),
   ("Mapping.keys", "ed_keys_ed_table_v", ["event_data", "event_data table"]),
   ("Mapping.lookup", "ed_lookup_ed_table_v", ["event_data", "event_data table"])]
  @ maps (fn (c, nm) => map (fn (tn, ty) => (c, "ed_" ^ nm ^ "_" ^ tn ^ "_v", [etuple, ty])) ed_value_types)
      ed_mapping_ops
\<close>

setup \<open>Monomorphize.box_cmd ed_box_specs\<close>

text \<open>
  Membership and lookup are monomorphised rather than boxed.  A box builds the dictionary once
  but still passes it, so the comparator that reaches the red-black tree is the composite
  @{text "comparator_list (comparator_option comparator_event_data)"}, three calls through the
  generic application path for every element of every tuple compared.  Monomorphising the chain
  down to the tree primitive lets @{thm [source] ccomp_etuple} rewrite it to
  @{const ed_comparator}.  Lookups are where this pays: on the Until benchmark the composite
  comparator is entered 5.48 million times against @{const ed_comparator}'s 559 thousand, and
  the tree descents of 602 thousand lookups account for nearly all of it.

  The write side goes the same way -- update, delete and combine, each down to its tree
  primitive -- and the projection out of a tree is boxed at every value type, because it ignores
  the dictionary its caller builds for it and that build was one per lookup.

  These come before the compatibility rules below, which mention the redirected constants.
\<close>

setup \<open>Monomorphize.monomorphize_cmd
  ([("Set.member", "ed_member", [etuple]),
    ("RBT_Mapping2.lookup", "ed_rbt_lookup_unit", [etuple, "unit"]),
    ("RBT_Mapping2.delete", "ed_rbt_delete_unit", [etuple, "unit"])]
   @ maps (fn (tn, ty) =>
       [("Mapping.lookup", "ed_lookup_" ^ tn, [etuple, ty]),
        ("Mapping.update", "ed_update_" ^ tn, [etuple, ty]),
        ("Mapping.delete", "ed_delete_" ^ tn, [etuple, ty]),
        ("Mapping.combine", "ed_combine_" ^ tn, [ty, etuple]),
        ("RBT_Mapping2.lookup", "ed_rbt_lookup_" ^ tn, [etuple, ty]),
        ("RBT_Mapping2.insert", "ed_rbt_insert_" ^ tn, [etuple, ty]),
        ("RBT_Mapping2.delete", "ed_rbt_delete_" ^ tn, [etuple, ty]),
        ("RBT_Mapping2.join", "ed_rbt_join_" ^ tn, [etuple, ty])]) ed_value_types)
  ["etuple_dict_simps"]\<close>

subsection \<open>Compatibility with the other preprocessor rules\<close>

text \<open>
  The code preprocessor rewrites bottom-up. The redirections above therefore fire inside the
  left-hand sides of other @{text code_unfold} rules before those get a chance to apply (e.g.
  @{term "{a \<in> A. P a}"} is normally folded into @{term "Set.filter P A"}, and membership in
  @{term "Mapping.keys m"} is normally turned into a lookup). We restate the affected rules in
  terms of the redirected constants.
\<close>

lemma ed_member_compat[code_unfold]:
  "Collect (\<lambda>a. ed_member a A \<and> P a) = Set.filter P A"
  "Collect (\<lambda>a. ed_member a A) = A"
  "ed_member a (Collect Q) = Q a"
  "ed_member x (set xs) = List.member xs x"
  unfolding ed_member_unfold[symmetric]
  by auto

lemma ed_bot_compat[code_unfold]:
  "(A = ed_bot) = Set.is_empty A"
  "(ed_bot = A) = Set.is_empty A"
  "set_eq A ed_bot = Set.is_empty A"
  "set_eq ed_bot A = Set.is_empty A"
  by (auto simp: ed_bot_def)

lemma ed_keys_compat[code_unfold]:
  "ed_member k (unbox ed_keys_nat_v m1) = (\<not> Option.is_none (ed_lookup_nat m1 k))"
  "ed_member k (unbox ed_keys_tstp_v m2) = (\<not> Option.is_none (ed_lookup_tstp m2 k))"
  "ed_member k (unbox ed_keys_table_v m3) = (\<not> Option.is_none (ed_lookup_table m3 k))"
  "ed_member k (unbox ed_keys_sum_v m4) = (\<not> Option.is_none (ed_lookup_sum m4 k))"
  "ed_member k (unbox ed_keys_rank_v m5) = (\<not> Option.is_none (ed_lookup_rank m5 k))"
  unfolding ed_member_unfold[symmetric] ed_keys_nat_v_unfold[symmetric] ed_lookup_nat_unfold[symmetric] ed_keys_tstp_v_unfold[symmetric] ed_lookup_tstp_unfold[symmetric] ed_keys_table_v_unfold[symmetric] ed_lookup_table_unfold[symmetric] ed_keys_sum_v_unfold[symmetric] ed_lookup_sum_unfold[symmetric] ed_keys_rank_v_unfold[symmetric] ed_lookup_rank_unfold[symmetric]
  by (simp_all add: Mapping.keys_is_none_rep)

section \<open>Bulk construction of tables\<close>

text \<open>
  The front end builds the database of a time point by inserting tuples one at a time
  (@{const insert_into_db}). @{text rbt_of_sorted_list} builds a table from a list in one step: if
  the list is strictly sorted with respect to the comparator (checked in linear time; the
  front end sorts with an unverified comparator), the red-black tree is built in linear time
  by @{const rbtreeify}, otherwise by the usual repeated insertion. Either way the result is
  @{term "set xs"}.
\<close>

fun strict_sorted_by :: "'a comparator \<Rightarrow> 'a list \<Rightarrow> bool" where
  "strict_sorted_by c (x # y # zs) \<longleftrightarrow> c x y = Lt \<and> strict_sorted_by c (y # zs)"
| "strict_sorted_by c _ \<longleftrightarrow> True"

lemma lt_of_comp_Lt: "lt_of_comp c x y \<longleftrightarrow> c x y = Lt"
  by (simp add: lt_of_comp_def split: order.splits)

lemma strict_sorted_by_sorted_wrt:
  assumes "comparator c"
  shows "strict_sorted_by c xs \<longleftrightarrow> sorted_wrt (lt_of_comp c) xs"
proof -
  have transp: "transp (lt_of_comp c)"
    using comparator.comp_trans[OF assms]
    by (auto intro!: transpI simp: lt_of_comp_def split: order.splits)
  show ?thesis
  proof (induction xs rule: induct_list012)
    case (3 x y zs)
    then show ?case
      by (subst sorted_wrt2[OF transp]) (simp add: lt_of_comp_Lt[abs_def])
  qed auto
qed

lift_definition rbt_of_sorted_list :: "'a :: ccompare list \<Rightarrow> 'a set_rbt" is
  "\<lambda>xs. if strict_sorted_by ccomp xs then rbtreeify (map (\<lambda>x. (x, ())) xs)
    else rbt_comp_bulkload ccomp (map (\<lambda>x. (x, ())) xs)"
proof goal_cases
  case (1 xs)
  show ?case
  proof (cases "ID CCOMPARE('a)")
    case None
    then show ?thesis by simp
  next
    case (Some c)
    note lin = ID_ccompare[OF Some] and comp = ID_ccompare'[OF Some]
    show ?thesis
      using Some
      by (auto simp: rbt_comp_bulkload[OF comp] strict_sorted_by_sorted_wrt[OF comp]
          linorder.strict_sorted_iff[OF lin] comp_def
          intro!: linorder.is_rbt_rbtreeify[OF lin] linorder.rbt_bulkload_is_rbt[OF lin])
  qed
qed

lemma RBT_set_rbt_of_sorted_list:
  assumes "ID CCOMPARE('a :: ccompare) \<noteq> None"
  shows "RBT_set (rbt_of_sorted_list (xs :: 'a list)) = set xs"
proof -
  from assms obtain c where Some: "ID CCOMPARE('a) = Some c" by auto
  note lin = ID_ccompare[OF Some] and comp = ID_ccompare'[OF Some]
  show ?thesis
    using Some
    by (auto simp: RBT_set_def RBT_Set2.member.rep_eq rbt_of_sorted_list.rep_eq rbt_comp_lookup[OF comp]
        rbt_comp_bulkload[OF comp] strict_sorted_by_sorted_wrt[OF comp] linorder.strict_sorted_iff[OF lin] comp_def
        linorder.rbt_lookup_rbtreeify[OF lin] linorder.rbt_lookup_rbt_bulkload[OF lin] dom_map_of_conv_image_fst
        image_image)
qed

section \<open>Tables built in one pass\<close>

text \<open>
  An operator that builds its result table by inserting its tuples one at a time into a
  persistent red-black tree copies the root-to-leaf path it descends for every tuple, so a
  table of \<open>n\<close> tuples costs about \<open>n log n\<close> nodes of six words where one pass costs \<open>n\<close>.
  @{const rbt_of_sorted_list} above builds the tree in one pass, but it wants a list that is
  strictly sorted with respect to the comparator, and the tuples an operator produces are not.
  They are therefore collected in a list and sorted here, by a bottom-up merge sort that drops
  duplicates as it merges -- which is exactly the form @{const rbt_of_sorted_list} checks for,
  so nothing is sorted twice and nothing falls back to the bulkload.

  Only the set of the sorted list matters for correctness: @{const rbt_of_sorted_list} checks
  the sortedness itself and falls back if it does not hold, so the equation relating it to
  @{const set} holds unconditionally and the merge sort needs no sortedness proof -- only that
  it preserves the set of its argument.

  The probe join was meant to be the first user, and is not: measured on the earlier
  option-tuple representation, the one-pass construction lost to the
  repeated insertion it was meant to replace, by 34% of @{text complex} on a log whose join
  produces many duplicates and by 5% on one whose joins are small.

  The reason is that inserting into a set deduplicates as it goes, so a join that produces
  \<open>n\<close> tuples of which \<open>k\<close> are distinct costs \<open>n log k\<close> comparisons and keeps a tree of \<open>k\<close>
  nodes. Collecting the tuples in a list defers the deduplication to the sort, which then does
  \<open>n log n\<close> comparisons on the undeduplicated count; when \<open>n\<close> is much larger than \<open>k\<close> -- which
  is what a join over a small domain produces -- that is far worse, and no threshold on the
  length of the list can tell the two cases apart, because \<open>k\<close> is not known until the work is
  done. The construction is right for tuples one already has in a list and wrong for tuples one
  is generating; see Section 15.6 of \<^file>\<open>../../EFFICIENCY.md\<close>.
\<close>

section \<open>A comparator merge sort\<close>

fun merge_c :: "('a :: ccompare) list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "merge_c [] ys = ys"
| "merge_c (x # xs) [] = x # xs"
| "merge_c (x # xs) (y # ys) = (case ccomp x y of
     Lt \<Rightarrow> x # merge_c xs (y # ys)
   | Gt \<Rightarrow> y # merge_c (x # xs) ys
   | Eq \<Rightarrow> x # merge_c xs ys)"

fun merge_pairs_c :: "('a :: ccompare) list list \<Rightarrow> 'a list list" where
  "merge_pairs_c (a # b # r) = merge_c a b # merge_pairs_c r"
| "merge_pairs_c r = r"

fun merge_all_c :: "nat \<Rightarrow> ('a :: ccompare) list list \<Rightarrow> 'a list" where
  "merge_all_c 0 xss = concat xss"
| "merge_all_c (Suc k) xss = (case xss of [] \<Rightarrow> [] | [a] \<Rightarrow> a
     | _ \<Rightarrow> merge_all_c k (merge_pairs_c xss))"

definition sort_c :: "('a :: ccompare) list \<Rightarrow> 'a list" where
  "sort_c xs = merge_all_c (length xs) (map (\<lambda>x. [x]) xs)"

lemma set_merge_c:
  assumes "ID CCOMPARE('a :: ccompare) \<noteq> None"
  shows "set (merge_c (xs :: 'a list) ys) = set xs \<union> set ys"
proof -
  from assms obtain c where Some: "ID CCOMPARE('a) = Some c" by auto
  have ccomp_eq: "(ccomp :: 'a comparator) = c" using Some by simp
  have eq: "\<And>x y. ccomp x y = Eq \<Longrightarrow> (x :: 'a) = y"
    using comparator.eq[OF ID_ccompare'[OF Some]] by (simp add: ccomp_eq)
  show ?thesis
    by (induction xs ys rule: merge_c.induct) (auto split: order.splits dest: eq)
qed

lemma set_concat_merge_pairs_c:
  assumes "ID CCOMPARE('a :: ccompare) \<noteq> None"
  shows "\<Union> (set ` set (merge_pairs_c (xss :: 'a list list))) = \<Union> (set ` set xss)"
proof (induction xss rule: merge_pairs_c.induct)
  case (1 a b r)
  then show ?case by (simp add: set_merge_c[OF assms] Un_assoc)
qed simp_all

lemma set_merge_all_c:
  assumes "ID CCOMPARE('a :: ccompare) \<noteq> None"
  shows "set (merge_all_c n (xss :: 'a list list)) = \<Union> (set ` set xss)"
proof (induction n arbitrary: xss)
  case (Suc k)
  show ?case
  proof (cases xss)
    case Nil
    then show ?thesis by simp
  next
    case (Cons a r)
    show ?thesis
    proof (cases r)
      case Nil
      then show ?thesis using Cons by simp
    next
      case (Cons b r')
      then show ?thesis using \<open>xss = a # r\<close>
        by (simp add: Suc.IH set_concat_merge_pairs_c[OF assms] set_merge_c[OF assms] Un_assoc)
    qed
  qed
qed simp

lemma set_sort_c:
  assumes "ID CCOMPARE('a :: ccompare) \<noteq> None"
  shows "set (sort_c (xs :: 'a list)) = set xs"
  by (simp add: sort_c_def set_merge_all_c[OF assms])

definition set_of_list :: "('a :: ccompare) list \<Rightarrow> 'a set" where
  "set_of_list xs = (if integer_of_nat (length xs) < bulk_min then set xs
     else RBT_set (rbt_of_sorted_list (sort_c xs)))"

lemma set_of_list_eq:
  assumes "ID CCOMPARE('a :: ccompare) \<noteq> None"
  shows "set_of_list (xs :: 'a list) = set xs"
  by (simp add: set_of_list_def RBT_set_rbt_of_sorted_list[OF assms] set_sort_c[OF assms])

text \<open>
  A second round of boxes, for operations whose definitions come after the first one: the bulk
  construction of a table, the projection out of a red-black tree that @{const rbt_fold} needs,
  and the two operations on the database, whose key type is a pair rather than a tuple and whose
  dictionary was therefore rebuilt at every predicate lookup and every inserted table.
\<close>

text \<open>
  Insertion into a table is monomorphised rather than boxed.  A box builds the dictionary once
  but still passes it, so the comparator reached at the bottom is the composite
  @{text "comparator_list (comparator_option comparator_event_data)"}: three calls through the
  generic application path for every element of every tuple compared.  Monomorphising the whole
  chain down to the red-black tree primitive lets @{thm [source] ccomp_etuple} rewrite the
  comparator to @{const ed_comparator}, a single recursive function over the tuple.

  @{const max} and @{const min} are not class parameters but plain overloaded definitions, so
  the generated code has one copy that takes an @{class ord} dictionary and calls the ordering
  through it.  @{const nat_of_integer} and subtraction on @{typ nat} both go through
  @{term "max 0"}, which on P2 is six million dictionary-dispatched comparisons -- a third of
  all entries into the two-argument application path.  Monomorphic copies at the three types
  that occur here call the ordering directly.

  Membership is the same story one level up.  @{const Set.member} is monomorphised, but its
  red-black-tree case calls @{const RBT_Set2.member}, which is not, so the dictionary is built
  and the composite comparator reached after all: on the Until benchmark that is 3.8 million
  entries into the chain and on the aggregation benchmark 5.6\% of the run.  The same holds for
  the nested update of the Until deque, whose key type is a tuple and whose value type is a
  time-stamp or a time-point.
\<close>

setup \<open>Monomorphize.box_cmd
  (map (fn (tn, ty) => ("RBT_Mapping2.impl_of", "ed_impl_of_" ^ tn ^ "_v", [etuple, ty])) ed_value_types
   @ [("RBT_Mapping2.impl_of", "ed_impl_of_v", [etuple, "unit"]),
   ("Mapping.lookup", "db_lookup_v", ["string8 \<times> nat", "event_data table list"]),
   ("update_mapping_with", "db_update_with_v", ["string8 \<times> nat", "event_data table list"])])\<close>

setup \<open>Monomorphize.monomorphize_cmd
  [("Set.insert", "ed_insert", [etuple]),
   ("RBT_Mapping2.insert", "ed_rbt_insert", [etuple, "unit"]),
   ("RBT_Set2.member", "ed_rbt_member", [etuple]),
   ("max", "ed_max_integer", ["integer"]),
   ("max", "ed_max_nat", ["nat"]),
   ("min", "ed_min_nat", ["nat"]),
   ("singleton_table", "ed_singleton_table", ["event_data"]),
   ("unit_table", "ed_unit_table", ["event_data"]),
   ("valid_tuple", "ed_valid_tuple", ["event_data"]),
   ("init_mmsaux", "ed_init_mmsaux", ["event_data"]),
   ("init_mmtaux", "ed_init_mmtaux", ["event_data"])]
  ["etuple_dict_simps"]\<close>

lemma lookup_update_mapping_with:
  "Mapping.lookup (update_mapping_with f k v m) k' =
    (if k' = k then (case Mapping.lookup m k of None \<Rightarrow> Some v | Some v' \<Rightarrow> Some (f k v' v)) else Mapping.lookup m k')"
  by transfer (auto split: option.splits)

(*<*)
end
(*>*)
