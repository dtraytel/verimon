(*<*)
theory Dense_Code_Opt
  imports Dense_Imp
begin
(*>*)

section \<open>The input tables of the monitor over the short tuples\<close>

text \<open>
  The front end builds the tables of a time point itself, sorted, and hands them to
  @{const table_of_list}, which checks the sortedness in linear time and builds the tree in one
  pass.  The monitor over the short tuples reads the same tables with nothing around the fields,
  so it needs the same three entry points at its own tuple type; the bodies are those of
  @{theory MFODL_Monitor_Devel.Monomorphic_Code} and
  @{theory MFODL_Monitor_Devel.Monitor_Impl} with the option gone.
\<close>

definition utable_of_list :: "event_data list list \<Rightarrow> utable" where
  "utable_of_list xs = set xs"

lemma utable_of_list_code[code]: "utable_of_list xs = RBT_set (rbt_of_sorted_list xs)"
  by (simp add: utable_of_list_def RBT_set_rbt_of_sorted_list ID_ccompare_ed)

definition uempty_db :: udatabase where "uempty_db = Mapping.empty"

text \<open>And the fold the front end prints a verdict with, at the short tuples.\<close>

definition urbt_fold :: "_ \<Rightarrow> event_data list set_rbt \<Rightarrow> _ \<Rightarrow> _" where
  "urbt_fold = RBT_Set2.fold"

definition uinsert_table_into_db :: "string8 \<times> nat \<Rightarrow> utable \<Rightarrow> udatabase \<Rightarrow> udatabase" where
  "uinsert_table_into_db p X db = update_mapping_with (\<lambda>_ tbl _. map ((\<union>) X) tbl) p [X] db"

section \<open>The dictionaries and the comparator of the dense inner loops\<close>

text \<open>
  @{theory MFODL_Monitor_Devel.Monomorphic_Code} removed the per-call construction of the
  composite type class dictionaries for @{typ "event_data tuple"} from the kernel's inner loops.
  It was written before the dense representation existed, and its list of mapping value types --
  @{typ nat}, the timestamp sum, @{typ "event_data table"}, the aggregation sum and rank -- does
  not contain the one the dense join index uses, which is @{typ "event_data tuple list"}: a key
  of shared columns mapped to the tuples that agree on it.  So the dense probe and the dense
  index build their dictionaries per call.  The generated code says so plainly:

  @{verbatim \<open>let rec dprobe_step_l p rk m y acc =
    (match lookupa ((ccompare_list (ccompare_option ccompare_event_data)),
                    (equal_list (equal_option equal_event_data)))
             m (dproj rk y)
     with None -> acc | Some l -> fold (fun x -> ed_insert (dmerge p x y)) l acc)\<close>}

  Four dictionary records, a @{text Some} and two closures, allocated for every probed tuple --
  @{const dprobe_step_l} enters that path 2.06 million times on the @{text complex} benchmark,
  @{const dindex_step} another 0.2 million.  And the comparator that reaches the tree is the
  composite @{text "comparator_list (comparator_option comparator_event_data)"}, three frames and
  two indirect calls per element, where @{const ed_comparator} is one frame and a direct call.
  @{const Set.insert} in the same function is already redirected to @{text ed_insert}; only the
  mapping side was missing.
\<close>

setup \<open>Monomorphize.monomorphize_cmd
  (let val etuple = "event_data tuple"; val tl = "event_data tuple list" in
    [("Mapping.lookup", "ed_lookup_tuples", [etuple, tl]),
     ("Mapping.update", "ed_update_tuples", [etuple, tl]),
     ("Mapping.delete", "ed_delete_tuples", [etuple, tl]),
     ("RBT_Mapping2.lookup", "ed_rbt_lookup_tuples", [etuple, tl]),
     ("RBT_Mapping2.insert", "ed_rbt_insert_tuples", [etuple, tl]),
     ("RBT_Mapping2.delete", "ed_rbt_delete_tuples", [etuple, tl])] end)
  ["etuple_dict_simps"]\<close>

text \<open>
  The projection out of a mapping's tree ignores the comparator its caller builds for it, so it
  is boxed at every value type in @{theory MFODL_Monitor_Devel.Monomorphic_Code} -- and has to be
  at this one too, or the monomorphised lookup above simply moves the per-call dictionary build
  one frame down into @{text impl_of}.  It did: before this box, @{text ed_rbt_lookup_tuples}
  called @{text ccompare_lista} 2.16 million times and @{text ed_rbt_insert_tuples} another
  0.1 million.
\<close>

setup \<open>Monomorphize.box_cmd
  [("RBT_Mapping2.impl_of", "ed_impl_of_tuples_v", ["event_data tuple", "event_data tuple list"])]\<close>

section \<open>The tree primitives with the comparator called directly\<close>

text \<open>
  Monomorphisation gets @{const ed_comparator} as far as the red-black tree, but no further: the
  primitives of @{theory Deriving.RBT_Comparator_Impl} take the comparator as an argument, so
  inside @{const rbt_comp_lookup} it is an unknown function and OCaml compiles @{text "c k x"} as
  a generic two-argument application.  On the @{text complex} benchmark that is 15.5 million
  @{text caml_apply2} calls from the lookup, 6.5 million from the insertion and 1.7 million from
  the deletion, out of 57.4 million in total, at about eight instructions each.  It also stops
  the comparator from being inlined.

  Specialising each primitive on @{const ed_comparator} -- a copy whose own recursion calls it by
  name -- turns those into direct calls.  Nothing is proved about the trees: each copy is defined
  as the partial application and its code equations are the originals' with the argument
  substituted, so the copy is the original by definition and the @{text code_unfold} rules only
  choose which of two equal functions the generated code names.
\<close>

definition ed_rbtc_lookup :: "(event_data tuple, 'v) rbt \<Rightarrow> event_data tuple \<Rightarrow> 'v option" where
  "ed_rbtc_lookup = rbt_comp_lookup ed_comparator"

lemma ed_rbtc_lookup_simps[code]:
  "ed_rbtc_lookup RBT_Impl.Empty k = None"
  "ed_rbtc_lookup (RBT_Impl.Branch cc l x y r) k =
     (case ed_comparator k x of Lt \<Rightarrow> ed_rbtc_lookup l k | Gt \<Rightarrow> ed_rbtc_lookup r k
        | Eq \<Rightarrow> Some y)"
  unfolding ed_rbtc_lookup_def by simp_all

lemma ed_rbtc_lookup_unfold[code_unfold]: "rbt_comp_lookup ed_comparator = ed_rbtc_lookup"
  by (simp add: ed_rbtc_lookup_def)

definition ed_rbtc_ins :: "(event_data tuple \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow> event_data tuple \<Rightarrow> 'v \<Rightarrow>
    (event_data tuple, 'v) rbt \<Rightarrow> (event_data tuple, 'v) rbt" where
  "ed_rbtc_ins = rbt_comp_ins ed_comparator"

lemma ed_rbtc_ins_simps[code]:
  "ed_rbtc_ins f k v RBT_Impl.Empty =
     RBT_Impl.Branch RBT_Impl.R RBT_Impl.Empty k v RBT_Impl.Empty"
  "ed_rbtc_ins f k v (RBT_Impl.Branch RBT_Impl.B l x y r) =
     (case ed_comparator k x of Lt \<Rightarrow> balance (ed_rbtc_ins f k v l) x y r
        | Gt \<Rightarrow> balance l x y (ed_rbtc_ins f k v r)
        | Eq \<Rightarrow> RBT_Impl.Branch RBT_Impl.B l x (f k y v) r)"
  "ed_rbtc_ins f k v (RBT_Impl.Branch RBT_Impl.R l x y r) =
     (case ed_comparator k x of Lt \<Rightarrow> RBT_Impl.Branch RBT_Impl.R (ed_rbtc_ins f k v l) x y r
        | Gt \<Rightarrow> RBT_Impl.Branch RBT_Impl.R l x y (ed_rbtc_ins f k v r)
        | Eq \<Rightarrow> RBT_Impl.Branch RBT_Impl.R l x (f k y v) r)"
  unfolding ed_rbtc_ins_def by simp_all

lemma ed_rbtc_ins_unfold[code_unfold]: "rbt_comp_ins ed_comparator = ed_rbtc_ins"
  by (simp add: ed_rbtc_ins_def)

definition ed_rbtc_insert_with_key :: "(event_data tuple \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow> event_data tuple \<Rightarrow>
    'v \<Rightarrow> (event_data tuple, 'v) rbt \<Rightarrow> (event_data tuple, 'v) rbt" where
  "ed_rbtc_insert_with_key = rbt_comp_insert_with_key ed_comparator"

lemma ed_rbtc_insert_with_key_code[code]:
  "ed_rbtc_insert_with_key f k v t = paint RBT_Impl.B (ed_rbtc_ins f k v t)"
  by (simp add: ed_rbtc_insert_with_key_def ed_rbtc_ins_def rbt_comp_insert_with_key_def)

lemma ed_rbtc_insert_with_key_unfold[code_unfold]:
  "rbt_comp_insert_with_key ed_comparator = ed_rbtc_insert_with_key"
  by (simp add: ed_rbtc_insert_with_key_def)

definition ed_rbtc_insert :: "event_data tuple \<Rightarrow> 'v \<Rightarrow> (event_data tuple, 'v) rbt \<Rightarrow>
    (event_data tuple, 'v) rbt" where
  "ed_rbtc_insert = rbt_comp_insert ed_comparator"

lemma ed_rbtc_insert_code[code]:
  "ed_rbtc_insert k v t = ed_rbtc_insert_with_key (\<lambda>_ _ nv. nv) k v t"
  by (simp add: ed_rbtc_insert_def ed_rbtc_insert_with_key_def rbt_comp_insert_def)

lemma ed_rbtc_insert_unfold[code_unfold]: "rbt_comp_insert ed_comparator = ed_rbtc_insert"
  by (simp add: ed_rbtc_insert_def)

text \<open>
  The deletion is three mutually recursive functions, and its two catch-all equations are split
  into the cases the code generator gets anyway.
\<close>

definition ed_rbtc_del :: "event_data tuple \<Rightarrow> (event_data tuple, 'v) rbt \<Rightarrow>
    (event_data tuple, 'v) rbt" where
  "ed_rbtc_del = rbt_comp_del ed_comparator"

definition ed_rbtc_del_from_left :: "event_data tuple \<Rightarrow> (event_data tuple, 'v) rbt \<Rightarrow>
    event_data tuple \<Rightarrow> 'v \<Rightarrow> (event_data tuple, 'v) rbt \<Rightarrow> (event_data tuple, 'v) rbt" where
  "ed_rbtc_del_from_left = rbt_comp_del_from_left ed_comparator"

definition ed_rbtc_del_from_right :: "event_data tuple \<Rightarrow> (event_data tuple, 'v) rbt \<Rightarrow>
    event_data tuple \<Rightarrow> 'v \<Rightarrow> (event_data tuple, 'v) rbt \<Rightarrow> (event_data tuple, 'v) rbt" where
  "ed_rbtc_del_from_right = rbt_comp_del_from_right ed_comparator"

lemma ed_rbtc_del_simps[code]:
  "ed_rbtc_del x RBT_Impl.Empty = RBT_Impl.Empty"
  "ed_rbtc_del x (RBT_Impl.Branch cc a y s b) =
     (case ed_comparator x y of Lt \<Rightarrow> ed_rbtc_del_from_left x a y s b
        | Gt \<Rightarrow> ed_rbtc_del_from_right x a y s b | Eq \<Rightarrow> RBT_Impl.combine a b)"
  unfolding ed_rbtc_del_def ed_rbtc_del_from_left_def ed_rbtc_del_from_right_def by simp_all

lemma ed_rbtc_del_from_left_simps[code]:
  "ed_rbtc_del_from_left x (RBT_Impl.Branch RBT_Impl.B lt z v rt) y s b =
     balance_left (ed_rbtc_del x (RBT_Impl.Branch RBT_Impl.B lt z v rt)) y s b"
  "ed_rbtc_del_from_left x RBT_Impl.Empty y s b =
     RBT_Impl.Branch RBT_Impl.R (ed_rbtc_del x RBT_Impl.Empty) y s b"
  "ed_rbtc_del_from_left x (RBT_Impl.Branch RBT_Impl.R va vb vc vd) y s b =
     RBT_Impl.Branch RBT_Impl.R
       (ed_rbtc_del x (RBT_Impl.Branch RBT_Impl.R va vb vc vd)) y s b"
  unfolding ed_rbtc_del_def ed_rbtc_del_from_left_def by simp_all

lemma ed_rbtc_del_from_right_simps[code]:
  "ed_rbtc_del_from_right x a y s (RBT_Impl.Branch RBT_Impl.B lt z v rt) =
     balance_right a y s (ed_rbtc_del x (RBT_Impl.Branch RBT_Impl.B lt z v rt))"
  "ed_rbtc_del_from_right x a y s RBT_Impl.Empty =
     RBT_Impl.Branch RBT_Impl.R a y s (ed_rbtc_del x RBT_Impl.Empty)"
  "ed_rbtc_del_from_right x a y s (RBT_Impl.Branch RBT_Impl.R va vb vc vd) =
     RBT_Impl.Branch RBT_Impl.R a y s
       (ed_rbtc_del x (RBT_Impl.Branch RBT_Impl.R va vb vc vd))"
  unfolding ed_rbtc_del_def ed_rbtc_del_from_right_def by simp_all

lemma ed_rbtc_del_unfold[code_unfold]:
  "rbt_comp_del ed_comparator = ed_rbtc_del"
  "rbt_comp_del_from_left ed_comparator = ed_rbtc_del_from_left"
  "rbt_comp_del_from_right ed_comparator = ed_rbtc_del_from_right"
  by (simp_all add: ed_rbtc_del_def ed_rbtc_del_from_left_def ed_rbtc_del_from_right_def)

definition ed_rbtc_delete :: "event_data tuple \<Rightarrow> (event_data tuple, 'v) rbt \<Rightarrow>
    (event_data tuple, 'v) rbt" where
  "ed_rbtc_delete = rbt_comp_delete ed_comparator"

lemma ed_rbtc_delete_code[code]: "ed_rbtc_delete k t = paint RBT_Impl.B (ed_rbtc_del k t)"
  by (simp add: ed_rbtc_delete_def ed_rbtc_del_def rbt_comp_delete_def)

lemma ed_rbtc_delete_unfold[code_unfold]: "rbt_comp_delete ed_comparator = ed_rbtc_delete"
  by (simp add: ed_rbtc_delete_def)

section \<open>The set operations, monomorphised rather than boxed\<close>

text \<open>
  @{theory MFODL_Monitor_Devel.Monomorphic_Code} boxes the set operations -- @{term "(\<union>)"},
  @{term "(\<inter>)"}, @{term "(-)"}, @{const Set.filter}, @{const image} -- and monomorphises only
  membership and lookup.  A box builds the dictionary once, when the program starts, which
  removes the construction cost; but it still *passes* the dictionary, so the comparator that
  reaches the red-black tree inside is the composite
  @{text "comparator_list (comparator_option comparator_event_data)"}, three frames and two
  indirect calls per element.  That is what is left of the generic chain: 3.0 million
  @{const comparator_list} steps and 3.2 million @{const comparator_option} steps, 120 M
  instructions, on the @{text complex} benchmark after the two sections above.

  Monomorphising them instead fixes the type, which lets @{thm [source] ccomp_etuple} rewrite the
  comparator to @{const ed_comparator} and the rules of the previous section then pick up the
  specialised tree primitives.  The boxes' redirect rules have to leave the code preprocessor
  first, or the two would compete for the same term.
\<close>

setup \<open>Code_Preproc.map_pre (fn ctxt => ctxt delsimps
  @{thms ed_union_v_unfold ed_inter_v_unfold ed_minus_v_unfold ed_filter_v_unfold
    ed_image_v_unfold})\<close>

setup \<open>Monomorphize.monomorphize_cmd
  (let val etuple = "event_data tuple" in
    [("sup :: _ set \<Rightarrow> _", "ed_union", [etuple]),
     ("inf :: _ set \<Rightarrow> _", "ed_inter", [etuple]),
     ("minus :: _ set \<Rightarrow> _", "ed_minus", [etuple]),
     ("Set.filter", "ed_filter", [etuple]),
     ("image", "ed_image", [etuple, etuple])] end)
  ["etuple_dict_simps"]\<close>

text \<open>
  Monomorphising the class operations is only half of it: their tree-to-tree branches, which are
  the hot ones, call the primitives of @{theory Containers.RBT_Mapping2} and
  @{theory Containers.RBT_Set2}, and those take the comparator as an argument, so what the
  monomorphisation achieves on its own is to move the dictionary build from the box's once-at-start
  into the branch.  The primitives have to go with them.
\<close>

setup \<open>Monomorphize.monomorphize_cmd
  (let val etuple = "event_data tuple" in
    [("RBT_Mapping2.join", "ed_rbt_join_unit", [etuple, "unit"]),
     ("RBT_Mapping2.meet", "ed_rbt_meet_unit", [etuple, "unit"]),
     ("RBT_Set2.minus", "ed_rbt_set_minus", [etuple]),
     ("RBT_Set2.inter_list", "ed_rbt_inter_list", [etuple])] end)
  ["etuple_dict_simps"]\<close>

section \<open>The same, for the short tuples\<close>

text \<open>
  Everything above is about @{typ "event_data tuple"}, which is what the monitor over the wide
  tuples uses and what @{theory MFODL_Monitor_Devel.Monomorphic_Code} was written for.  The
  monitor over the short tuples keys its sets and mappings on @{typ "event_data list"}, which
  that theory does not mention at all, so without this section every set operation and every
  mapping operation of the dense evaluator builds its dictionaries per call and reaches the tree
  through @{text "comparator_list comparator_event_data"} rather than through a comparator that
  knows the type.  The section is the one above with the option gone.
\<close>

subsection \<open>A direct comparator on the short tuples\<close>

fun edl_comparator :: "event_data list comparator" where
  "edl_comparator [] [] = Eq"
| "edl_comparator [] (y # ys) = Lt"
| "edl_comparator (x # xs) [] = Gt"
| "edl_comparator (x # xs) (y # ys) =
    (case comparator_event_data x y of Eq \<Rightarrow> edl_comparator xs ys | r \<Rightarrow> r)"

lemma edl_comparator_eq: "edl_comparator xs ys = comparator_list comparator_event_data xs ys"
  by (induction xs ys rule: edl_comparator.induct) (auto split: order.splits)

lemma ccompare_edl: "CCOMPARE(event_data list) = Some edl_comparator"
  by (simp add: ccompare_list_def ccompare_event_data_def ID_def edl_comparator_eq[abs_def])

lemma ID_ccompare_edl: "ID CCOMPARE(event_data list) = Some edl_comparator"
  by (simp add: ccompare_edl ID_def)

lemma ccomp_edl: "(ccomp :: event_data list comparator) = edl_comparator"
  by (simp add: ID_ccompare_edl)

lemma ceq_edl: "CEQ(event_data list) = Some (equality_list (=))"
  by (simp add: ceq_list_def ceq_event_data_def ID_def)

lemma ID_ceq_edl: "ID CEQ(event_data list) = Some (equality_list (=))"
  by (simp add: ceq_edl ID_def)

lemmas edl_dict_simps = ccompare_edl ID_ccompare_edl ccomp_edl ceq_edl ID_ceq_edl
  option.case option.sel ID_def id_apply

subsection \<open>The empty table as a value\<close>

definition edl_bot :: utable where "edl_bot = {}"

lemma edl_bot_code[code]: "edl_bot = RBT_set RBT_Set2.empty"
  by (simp add: edl_bot_def)

lemma edl_bot_unfold[code_unfold]:
  "(bot :: utable) = edl_bot"
  "set_empty (of_phantom SET_IMPL(event_data list)) = edl_bot"
  by (simp_all add: edl_bot_def)

lemma edl_bot_compat[code_unfold]:
  "(A = edl_bot) = Set.is_empty A"
  "(edl_bot = A) = Set.is_empty A"
  "set_eq A edl_bot = Set.is_empty A"
  "set_eq edl_bot A = Set.is_empty A"
  by (auto simp: edl_bot_def)

subsection \<open>The set and mapping operations at the short tuples\<close>

ML \<open>
val edl = "event_data list"
val edl_value_types =
  [("nat", "nat"), ("tstp", "nat + nat"), ("table", "event_data list set"),
   ("tuples", "event_data list list")]
\<close>

setup \<open>Monomorphize.monomorphize_cmd
  ([("Set.member", "edl_member", [edl]),
    ("Set.insert", "edl_insert", [edl]),
    ("Set.remove", "edl_remove", [edl]),
    ("sup :: _ set \<Rightarrow> _", "edl_union", [edl]),
    ("inf :: _ set \<Rightarrow> _", "edl_inter", [edl]),
    ("minus :: _ set \<Rightarrow> _", "edl_minus", [edl]),
    ("Set.filter", "edl_filter", [edl]),
    ("image", "edl_image", [edl, edl]),
    ("RBT_Set2.minus", "edl_rbt_set_minus", [edl]),
    ("RBT_Set2.inter_list", "edl_rbt_inter_list", [edl]),
    ("RBT_Mapping2.join", "edl_rbt_join_unit", [edl, "unit"]),
    ("RBT_Mapping2.meet", "edl_rbt_meet_unit", [edl, "unit"]),
    ("RBT_Mapping2.insert", "edl_rbt_insert_unit", [edl, "unit"]),
    ("RBT_Mapping2.lookup", "edl_rbt_lookup_unit", [edl, "unit"]),
    ("RBT_Mapping2.delete", "edl_rbt_delete_unit", [edl, "unit"]),
    ("RBT_Set2.member", "edl_rbt_member", [edl]),
    ("upd_nested_step_dq", "edl_upd_nested_step_dq", ["nat + nat", edl])]
   @ maps (fn (tn, ty) =>
       [("Mapping.lookup", "edl_lookup_" ^ tn, [edl, ty]),
        ("Mapping.update", "edl_update_" ^ tn, [edl, ty]),
        ("Mapping.delete", "edl_delete_" ^ tn, [edl, ty]),
        ("RBT_Mapping2.lookup", "edl_rbt_lookup_" ^ tn, [edl, ty]),
        ("RBT_Mapping2.insert", "edl_rbt_insert_" ^ tn, [edl, ty]),
        ("RBT_Mapping2.delete", "edl_rbt_delete_" ^ tn, [edl, ty]),
        ("RBT_Mapping2.join", "edl_rbt_join_" ^ tn, [edl, ty])]) edl_value_types)
  ["edl_dict_simps"]\<close>

text \<open>As above, the projection out of a mapping's tree has to be boxed at every value type, or
  the monomorphised lookup moves the per-call dictionary build one frame down into it.\<close>

setup \<open>Monomorphize.box_cmd
  (("RBT_Mapping2.impl_of", "edl_impl_of_unit_v", [edl, "unit"]) ::
   map (fn (tn, ty) => ("RBT_Mapping2.impl_of", "edl_impl_of_" ^ tn ^ "_v", [edl, ty]))
     edl_value_types)\<close>

subsection \<open>The heap index of the dense join\<close>

text \<open>
  The operations of @{theory MFODL_Monitor_Imp.Table_Imp} take the @{class heap} dictionary of
  the key type and of the value type, and the code generator builds both at every call.  The
  index of the join over the wide tuples is boxed for that reason in
  @{theory MFODL_Monitor_Imp.Join_Imp2}; the one over the short tuples is entered once per
  indexed and once per probed tuple, so it needs the same.
\<close>

setup \<open>Monomorphize.box_cmd
  (let val edl = "event_data list"; val edll = "event_data list list" in
    [("im_lookup_h", "djidx_lookup_h_v", [edl, edll]),
     ("im_update_h", "djidx_update_h_v", [edl, edll]),
     ("im_new", "djidx_new_v", [edl, edll])] end)\<close>

subsection \<open>The tree primitives with the short tuples' comparator called directly\<close>

definition edl_rbtc_lookup :: "(event_data list, 'v) rbt \<Rightarrow> event_data list \<Rightarrow> 'v option" where
  "edl_rbtc_lookup = rbt_comp_lookup edl_comparator"

lemma edl_rbtc_lookup_simps[code]:
  "edl_rbtc_lookup RBT_Impl.Empty k = None"
  "edl_rbtc_lookup (RBT_Impl.Branch cc l x y r) k =
     (case edl_comparator k x of Lt \<Rightarrow> edl_rbtc_lookup l k | Gt \<Rightarrow> edl_rbtc_lookup r k
        | Eq \<Rightarrow> Some y)"
  unfolding edl_rbtc_lookup_def by simp_all

lemma edl_rbtc_lookup_unfold[code_unfold]: "rbt_comp_lookup edl_comparator = edl_rbtc_lookup"
  by (simp add: edl_rbtc_lookup_def)

definition edl_rbtc_ins :: "(event_data list \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow> event_data list \<Rightarrow> 'v \<Rightarrow>
    (event_data list, 'v) rbt \<Rightarrow> (event_data list, 'v) rbt" where
  "edl_rbtc_ins = rbt_comp_ins edl_comparator"

lemma edl_rbtc_ins_simps[code]:
  "edl_rbtc_ins f k v RBT_Impl.Empty =
     RBT_Impl.Branch RBT_Impl.R RBT_Impl.Empty k v RBT_Impl.Empty"
  "edl_rbtc_ins f k v (RBT_Impl.Branch RBT_Impl.B l x y r) =
     (case edl_comparator k x of Lt \<Rightarrow> balance (edl_rbtc_ins f k v l) x y r
        | Gt \<Rightarrow> balance l x y (edl_rbtc_ins f k v r)
        | Eq \<Rightarrow> RBT_Impl.Branch RBT_Impl.B l x (f k y v) r)"
  "edl_rbtc_ins f k v (RBT_Impl.Branch RBT_Impl.R l x y r) =
     (case edl_comparator k x of Lt \<Rightarrow> RBT_Impl.Branch RBT_Impl.R (edl_rbtc_ins f k v l) x y r
        | Gt \<Rightarrow> RBT_Impl.Branch RBT_Impl.R l x y (edl_rbtc_ins f k v r)
        | Eq \<Rightarrow> RBT_Impl.Branch RBT_Impl.R l x (f k y v) r)"
  unfolding edl_rbtc_ins_def by simp_all

lemma edl_rbtc_ins_unfold[code_unfold]: "rbt_comp_ins edl_comparator = edl_rbtc_ins"
  by (simp add: edl_rbtc_ins_def)

definition edl_rbtc_insert_with_key :: "(event_data list \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow> event_data list \<Rightarrow>
    'v \<Rightarrow> (event_data list, 'v) rbt \<Rightarrow> (event_data list, 'v) rbt" where
  "edl_rbtc_insert_with_key = rbt_comp_insert_with_key edl_comparator"

lemma edl_rbtc_insert_with_key_code[code]:
  "edl_rbtc_insert_with_key f k v t = paint RBT_Impl.B (edl_rbtc_ins f k v t)"
  by (simp add: edl_rbtc_insert_with_key_def edl_rbtc_ins_def rbt_comp_insert_with_key_def)

lemma edl_rbtc_insert_with_key_unfold[code_unfold]:
  "rbt_comp_insert_with_key edl_comparator = edl_rbtc_insert_with_key"
  by (simp add: edl_rbtc_insert_with_key_def)

definition edl_rbtc_insert :: "event_data list \<Rightarrow> 'v \<Rightarrow> (event_data list, 'v) rbt \<Rightarrow>
    (event_data list, 'v) rbt" where
  "edl_rbtc_insert = rbt_comp_insert edl_comparator"

lemma edl_rbtc_insert_code[code]:
  "edl_rbtc_insert k v t = edl_rbtc_insert_with_key (\<lambda>_ _ nv. nv) k v t"
  by (simp add: edl_rbtc_insert_def edl_rbtc_insert_with_key_def rbt_comp_insert_def)

lemma edl_rbtc_insert_unfold[code_unfold]: "rbt_comp_insert edl_comparator = edl_rbtc_insert"
  by (simp add: edl_rbtc_insert_def)

definition edl_rbtc_del :: "event_data list \<Rightarrow> (event_data list, 'v) rbt \<Rightarrow>
    (event_data list, 'v) rbt" where
  "edl_rbtc_del = rbt_comp_del edl_comparator"

definition edl_rbtc_del_from_left :: "event_data list \<Rightarrow> (event_data list, 'v) rbt \<Rightarrow>
    event_data list \<Rightarrow> 'v \<Rightarrow> (event_data list, 'v) rbt \<Rightarrow> (event_data list, 'v) rbt" where
  "edl_rbtc_del_from_left = rbt_comp_del_from_left edl_comparator"

definition edl_rbtc_del_from_right :: "event_data list \<Rightarrow> (event_data list, 'v) rbt \<Rightarrow>
    event_data list \<Rightarrow> 'v \<Rightarrow> (event_data list, 'v) rbt \<Rightarrow> (event_data list, 'v) rbt" where
  "edl_rbtc_del_from_right = rbt_comp_del_from_right edl_comparator"

lemma edl_rbtc_del_simps[code]:
  "edl_rbtc_del x RBT_Impl.Empty = RBT_Impl.Empty"
  "edl_rbtc_del x (RBT_Impl.Branch cc a y s b) =
     (case edl_comparator x y of Lt \<Rightarrow> edl_rbtc_del_from_left x a y s b
        | Gt \<Rightarrow> edl_rbtc_del_from_right x a y s b | Eq \<Rightarrow> RBT_Impl.combine a b)"
  unfolding edl_rbtc_del_def edl_rbtc_del_from_left_def edl_rbtc_del_from_right_def by simp_all

lemma edl_rbtc_del_from_left_simps[code]:
  "edl_rbtc_del_from_left x (RBT_Impl.Branch RBT_Impl.B lt z v rt) y s b =
     balance_left (edl_rbtc_del x (RBT_Impl.Branch RBT_Impl.B lt z v rt)) y s b"
  "edl_rbtc_del_from_left x RBT_Impl.Empty y s b =
     RBT_Impl.Branch RBT_Impl.R (edl_rbtc_del x RBT_Impl.Empty) y s b"
  "edl_rbtc_del_from_left x (RBT_Impl.Branch RBT_Impl.R va vb vc vd) y s b =
     RBT_Impl.Branch RBT_Impl.R
       (edl_rbtc_del x (RBT_Impl.Branch RBT_Impl.R va vb vc vd)) y s b"
  unfolding edl_rbtc_del_def edl_rbtc_del_from_left_def by simp_all

lemma edl_rbtc_del_from_right_simps[code]:
  "edl_rbtc_del_from_right x a y s (RBT_Impl.Branch RBT_Impl.B lt z v rt) =
     balance_right a y s (edl_rbtc_del x (RBT_Impl.Branch RBT_Impl.B lt z v rt))"
  "edl_rbtc_del_from_right x a y s RBT_Impl.Empty =
     RBT_Impl.Branch RBT_Impl.R a y s (edl_rbtc_del x RBT_Impl.Empty)"
  "edl_rbtc_del_from_right x a y s (RBT_Impl.Branch RBT_Impl.R va vb vc vd) =
     RBT_Impl.Branch RBT_Impl.R a y s
       (edl_rbtc_del x (RBT_Impl.Branch RBT_Impl.R va vb vc vd))"
  unfolding edl_rbtc_del_def edl_rbtc_del_from_right_def by simp_all

lemma edl_rbtc_del_unfold[code_unfold]:
  "rbt_comp_del edl_comparator = edl_rbtc_del"
  "rbt_comp_del_from_left edl_comparator = edl_rbtc_del_from_left"
  "rbt_comp_del_from_right edl_comparator = edl_rbtc_del_from_right"
  by (simp_all add: edl_rbtc_del_def edl_rbtc_del_from_left_def edl_rbtc_del_from_right_def)

definition edl_rbtc_delete :: "event_data list \<Rightarrow> (event_data list, 'v) rbt \<Rightarrow>
    (event_data list, 'v) rbt" where
  "edl_rbtc_delete = rbt_comp_delete edl_comparator"

lemma edl_rbtc_delete_code[code]: "edl_rbtc_delete k t = paint RBT_Impl.B (edl_rbtc_del k t)"
  by (simp add: edl_rbtc_delete_def edl_rbtc_del_def rbt_comp_delete_def)

lemma edl_rbtc_delete_unfold[code_unfold]: "rbt_comp_delete edl_comparator = edl_rbtc_delete"
  by (simp add: edl_rbtc_delete_def)

subsection \<open>The dense operations, at the element type the evaluator uses\<close>

text \<open>
  20.31's generic layer is polymorphic in the element type, so the code generator gives every
  operation of it a dictionary argument and rebuilds the composite comparator from that argument
  at every call -- which is exactly what the two sections above remove for the wide tuples, and
  what the dense evaluator used to have for free when its operations were stated at
  @{typ "event_data tuple"} outright.  Without this section the generated probe reads

  @{verbatim \<open>let rec gprobe_step_l (_A1, _A2, _A3) p rk m y acc =
    (match lookupa ((ccompare_list _A2), (equal_list _A3)) m (dproj rk y)
     with None -> acc
     | Some l -> fold (fun x -> insert ((ceq_list _A1), (ccompare_list _A2)) (dmerge p x y)) l acc)\<close>}

  and the generality is paid for once per probed tuple.  Specialising each operation at
  @{typ event_data} lets @{thm [source] edl_dict_simps} fix the dictionaries and the rules above
  pick up @{const edl_comparator} and the specialised tree primitives.

  The heap-resident Since is generic in its tuple type rather than its element type, and is used
  at both, so it is specialised twice.
\<close>

ML \<open>
val dense_elem_consts =
  ["gbin_join", "gbin_join0", "ggen_join", "gindex", "gindex_step",
   "gprobe_step", "gprobe_step_l", "gands_pos", "gands_neg", "gmulti_join",
   "dsemi", "dsemi_idx",
   "ginit_msaux", "gvalid_tuple", "gidx_upd", "gshift_end",
   "gadd_new_ts_msaux'", "gadd_new_ts_msaux", "ggc_msaux",
   "gadd_new_table_msaux", "gresult_msaux", "gjoin_msaux", "ggc_join_msaux",
   "ginit_dq", "geval_step_dq", "gshift_dq", "geval_dq",
   "guntil_step_dq", "guntil_elem_step_dq", "gadd_new_dq",
   "gevt_add", "gevt_del", "gsevt_move", "gsevt_expire", "ginit_sevt",
   "gadd_new_ts_sevt", "gjoin_sevt", "gadd_new_table_sevt", "gresult_sevt",
   "gevt_extend", "ginit_evt", "glength_evt", "gevt_step", "gevt_shift",
   "gadd_new_evt", "geval_evt",
   "gsemi_join", "ginit_mmtaux", "gupdate_mmtaux'", "gupdate_mmtaux", "gresult_mmtaux",
   "glookup", "gmrtabulate", "geps_lax", "greps_strict", "gleps_strict",
   "grdelta", "gldelta", "gupdate_matchP", "gupdate_matchF_base", "gupdate_matchF_step",
   "gupdate_matchF", "geval_matchF"]

val heap_since_consts =
  ["gjc", "filter_loop2", "expire_loop2", "upd_loop2", "move_loop2",
   "del_loop2", "ins_loop2", "since_loop2", "init2", "shift_end2",
   "add_new_ts2'", "add_new_ts2", "gc2", "join2", "gc_join2",
   "add_new_table2", "result2"]

fun mono_name pre c = pre ^ String.translate (fn #"'" => "a" | ch => String.str ch) c
\<close>

setup \<open>Monomorphize.monomorphize_cmd
  (map (fn c => (c, mono_name "de_" c, ["event_data"])) dense_elem_consts
   @ map (fn c => (c, mono_name "hsd_" c, ["event_data list"])) heap_since_consts
   @ map (fn c => (c, mono_name "hsw_" c, ["event_data tuple"])) heap_since_consts)
  ["edl_dict_simps", "etuple_dict_simps"]\<close>

subsection \<open>The set and mapping operations whose dictionaries are built once\<close>

text \<open>
  Monomorphising the dense operations fixes the type but does not by itself remove every
  dictionary: the operations they call that are not themselves specialised -- the emptiness and
  cardinality tests, the sorted list of a table, the folds, the mapping projections -- still take
  one, and a monomorphic caller builds it on the spot rather than receiving it.
  @{theory MFODL_Monitor_Devel.Monomorphic_Code} boxes exactly those for the wide tuples, so that
  the dictionary is built once when the module is initialised; the same list at the short ones.
\<close>

definition edl_mempty_nat :: "(event_data list, nat) mapping" where
  "edl_mempty_nat = Mapping.empty"
lemma edl_mempty_nat_code[code]: "edl_mempty_nat = RBT_Mapping RBT_Mapping2.empty"
  by (simp only: edl_mempty_nat_def RBT_Mapping_empty)
lemma edl_mempty_nat_unfold[code_unfold]:
  "(Mapping.empty :: (event_data list, nat) mapping) = edl_mempty_nat"
  "(mapping_empty (of_phantom MAPPING_IMPL(event_data list)) :: (event_data list, nat) mapping)
     = edl_mempty_nat"
  by (simp_all add: edl_mempty_nat_def)

definition edl_mempty_tstp :: "(event_data list, nat + nat) mapping" where
  "edl_mempty_tstp = Mapping.empty"
lemma edl_mempty_tstp_code[code]: "edl_mempty_tstp = RBT_Mapping RBT_Mapping2.empty"
  by (simp only: edl_mempty_tstp_def RBT_Mapping_empty)
lemma edl_mempty_tstp_unfold[code_unfold]:
  "(Mapping.empty :: (event_data list, nat + nat) mapping) = edl_mempty_tstp"
  "(mapping_empty (of_phantom MAPPING_IMPL(event_data list))
      :: (event_data list, nat + nat) mapping) = edl_mempty_tstp"
  by (simp_all add: edl_mempty_tstp_def)

definition edl_mempty_table :: "(event_data list, utable) mapping" where
  "edl_mempty_table = Mapping.empty"
lemma edl_mempty_table_code[code]: "edl_mempty_table = RBT_Mapping RBT_Mapping2.empty"
  by (simp only: edl_mempty_table_def RBT_Mapping_empty)
lemma edl_mempty_table_unfold[code_unfold]:
  "(Mapping.empty :: (event_data list, utable) mapping) = edl_mempty_table"
  "(mapping_empty (of_phantom MAPPING_IMPL(event_data list))
      :: (event_data list, utable) mapping) = edl_mempty_table"
  by (simp_all add: edl_mempty_table_def)

definition edl_mempty_tuples :: "(event_data list, event_data list list) mapping" where
  "edl_mempty_tuples = Mapping.empty"
lemma edl_mempty_tuples_code[code]: "edl_mempty_tuples = RBT_Mapping RBT_Mapping2.empty"
  by (simp only: edl_mempty_tuples_def RBT_Mapping_empty)
lemma edl_mempty_tuples_unfold[code_unfold]:
  "(Mapping.empty :: (event_data list, event_data list list) mapping) = edl_mempty_tuples"
  "(mapping_empty (of_phantom MAPPING_IMPL(event_data list))
      :: (event_data list, event_data list list) mapping) = edl_mempty_tuples"
  by (simp_all add: edl_mempty_tuples_def)

setup \<open>Monomorphize.box_cmd
  (let val edl = "event_data list"; val tbl = "event_data list set" in
    [("Set.remove", "edl_remove_v", [edl]),
     ("Ball", "edl_Ball_v", [edl]),
     ("Bex", "edl_Bex_v", [edl]),
     ("finite", "edl_finite_v", [edl]),
     ("card", "edl_card_v", [edl]),
     ("set_eq", "edl_set_eq_v", [edl]),
     ("Set.is_empty", "edl_is_empty_v", [edl]),
     ("less_eq :: _ set \<Rightarrow> _", "edl_subset_v", [edl]),
     ("csorted_list_of_set", "edl_csorted_list_of_set_v", [edl]),
     ("rbt_of_sorted_list", "edl_rbt_of_sorted_list_v", [edl]),
     ("RBT_Set2.fold", "edl_rbt_fold_table_v", [edl, tbl]),
     ("set_fold_cfi", "edl_fold_cfi_table_v", [edl, tbl]),
     ("cluster", "edl_cluster_v", [edl, edl]),
     ("set_of_idx", "edl_set_of_idx_v", [edl, edl]),
     ("mapping_join", "edl_mapping_join_v", [edl, tbl]),
     ("mapping_antijoin", "edl_mapping_antijoin_v", [edl, tbl]),
     ("upd_set", "edl_upd_set_nat_v", [edl, "nat"]),
     ("minus_keys", "edl_minus_keys_v", [edl, "nat"])]
    @ maps (fn (c, nm) => map (fn (tn, ty) => (c, "edl_" ^ nm ^ "_" ^ tn ^ "_v", [edl, ty]))
              edl_value_types)
        [("Mapping.filter", "mfilter"), ("Mapping.keys", "keys"),
         ("Mapping.is_empty", "mis_empty"), ("Mapping.combine", "combine")]
   end)\<close>

(*<*)
end
(*>*)
