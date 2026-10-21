(*<*)
theory Tuple_Code
  imports Compile Idx_Code "Monitor_Impl.Monomorphic_Code"
begin
(*>*)

section \<open>The input tables of the monitor over the short tuples\<close>

text \<open>
  The front end builds the tables of a time point itself, sorted, and hands them to
  @{text utable_of_list}, which checks the sortedness in linear time and builds the tree in one
  pass.  The kernel's tuples are the short tuples, so the three entry points are those of
  @{theory Monitor_Impl.Monomorphic_Code} and @{theory Monitor_Impl.Monitor_Impl},
  named for the executable monitor.
\<close>

type_synonym udatabase = database

definition utable_of_list :: "event_data list list \<Rightarrow> utable" where
  "utable_of_list xs = set xs"

lemma utable_of_list_code[code]: "utable_of_list xs = RBT_set (rbt_of_sorted_list xs)"
  by (simp add: utable_of_list_def RBT_set_rbt_of_sorted_list ID_ccompare_etuple)

definition uempty_db :: udatabase where "uempty_db = Mapping.empty"

text \<open>And the fold the front end prints a verdict with, at the short tuples.\<close>

definition urbt_fold :: "_ \<Rightarrow> event_data list set_rbt \<Rightarrow> _ \<Rightarrow> _" where
  "urbt_fold = RBT_Set2.fold"

definition uinsert_table_into_db :: "string8 \<times> nat \<Rightarrow> utable \<Rightarrow> udatabase \<Rightarrow> udatabase" where
  "uinsert_table_into_db p X db = update_mapping_with (\<lambda>_ tbl _. map ((\<union>) X) tbl) p [X] db"

section \<open>The dictionaries and the comparator of the executable inner loops\<close>

text \<open>
  @{theory Monitor_Impl.Monomorphic_Code} removed the per-call construction of the
  composite type class dictionaries for @{typ "event_data tuple"} from the kernel's inner loops.
  Its list of mapping value types -- @{typ nat}, the timestamp sum, @{typ "event_data table"},
  the aggregation sum and rank -- does not contain the one the executable join index uses, which is
  @{typ "event_data tuple list"}: a key of shared columns mapped to the tuples that agree on it.
  So the executable probe and the executable index would build their dictionaries per call, and the
  comparator that reaches the tree would be the composite one on lists rather than
  @{const ed_comparator}.
\<close>

setup \<open>Monomorphize.monomorphize_cmd
  (let val etuple = "event_data tuple"; val tl = "event_data tuple list" in
    [("Mapping.lookup", "ed_lookup_tuples", [etuple, tl]),
     ("Mapping.update", "ed_update_tuples", [etuple, tl]),
     ("RBT_Mapping2.lookup", "ed_rbt_lookup_tuples", [etuple, tl]),
     ("RBT_Mapping2.insert", "ed_rbt_insert_tuples", [etuple, tl])] end)
  ["etuple_dict_simps"]\<close>

text \<open>
  The projection out of a mapping's tree ignores the comparator its caller builds for it, so it
  is boxed at every value type in @{theory Monitor_Impl.Monomorphic_Code} -- and has to be
  at this one too, or the monomorphised lookup above simply moves the per-call dictionary build
  one frame down into @{text impl_of}.
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
  "ed_rbtc_insert_with_key f k v t = RBT_Impl.paint RBT_Impl.B (ed_rbtc_ins f k v t)"
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

lemma ed_rbtc_delete_code[code]: "ed_rbtc_delete k t = RBT_Impl.paint RBT_Impl.B (ed_rbtc_del k t)"
  by (simp add: ed_rbtc_delete_def ed_rbtc_del_def rbt_comp_delete_def)

lemma ed_rbtc_delete_unfold[code_unfold]: "rbt_comp_delete ed_comparator = ed_rbtc_delete"
  by (simp add: ed_rbtc_delete_def)

section \<open>The set operations, monomorphised rather than boxed\<close>

text \<open>
  The set operations -- @{term "(\<union>)"}, @{term "(\<inter>)"}, @{term "(-)"},
  @{const Set.filter}, @{const image} -- are monomorphised like membership and lookup in
  @{theory Monitor_Impl.Monomorphic_Code}, not boxed.  A box builds the dictionary once, when the program starts, which
  removes the construction cost; but it still *passes* the dictionary, so the comparator that
  reaches the red-black tree inside is the composite one on lists, reached through a closure for
  every element.

  Monomorphising them instead fixes the type, which lets @{thm [source] ccomp_etuple} rewrite the
  comparator to @{const ed_comparator} and the rules of the previous section then pick up the
  specialised tree primitives.
\<close>

setup \<open>Monomorphize.monomorphize_cmd
  (let val etuple = "event_data tuple" in
    [("sup :: _ set \<Rightarrow> _", "ed_union", [etuple]),
     ("inf :: _ set \<Rightarrow> _", "ed_inter", [etuple]),
     ("Groups.minus_class.minus :: _ set \<Rightarrow> _", "ed_minus", [etuple]),
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

section \<open>The remaining set and mapping operations of the executable evaluator\<close>

text \<open>
  The kernel's tuples are the executable evaluator's short tuples, @{typ "event_data list"}, so the
  comparator, the dictionaries, the empty table and most of the specialised set and mapping
  operations are those of @{theory Monitor_Impl.Monomorphic_Code} and of the sections
  above.  What the evaluator needs beyond them: the removal of an element, monomorphised rather
  than boxed, and the mapping operations at the value types the kernel does not use -- the join
  index's tuple lists, and the count sets with a count or a sum of the grouped aggregations.
\<close>

ML \<open>
val edl = "event_data list"
val edl_value_types =
  [("gcnt", "nat \<times> (event_data list, nat) mapping"),
   ("gsum", "(nat \<times> integer) \<times> (event_data list, nat) mapping")]
\<close>

setup \<open>Monomorphize.monomorphize_cmd
  ([("Set.remove", "edl_remove", [edl])]
   @ maps (fn (tn, ty) =>
       [("Mapping.lookup", "edl_lookup_" ^ tn, [edl, ty]),
        ("Mapping.update", "edl_update_" ^ tn, [edl, ty]),
        ("Mapping.delete", "edl_delete_" ^ tn, [edl, ty]),
        ("RBT_Mapping2.lookup", "edl_rbt_lookup_" ^ tn, [edl, ty]),
        ("RBT_Mapping2.insert", "edl_rbt_insert_" ^ tn, [edl, ty]),
        ("RBT_Mapping2.delete", "edl_rbt_delete_" ^ tn, [edl, ty]),
        ("RBT_Mapping2.join", "edl_rbt_join_" ^ tn, [edl, ty])]) edl_value_types)
  ["etuple_dict_simps"]\<close>

text \<open>An image passes @{const Set.insert} to the tree's fold unapplied, where the redirection
  to the specialised insertion does not reach it; the equation on a tree names it.\<close>

lemma ed_image_rbt[code]:
  "ed_image h (RBT_set rbt) = RBT_Set2.fold (\<lambda>x. ed_insert (h x)) rbt {}"
  unfolding ed_image_def ed_insert_def
  by (simp add: Set_image_code(1) ID_ccompare_etuple ccomp_etuple ID_ceq_etuple comp_def)

text \<open>The match of a predicate's table against the atom's terms is an image followed by
  @{const Option.these}, which the generated code ran through the generic set operations with
  their dictionaries; on a tree it is one fold that inserts the matches.\<close>

lemma these_image_fold:
  "fold (\<lambda>x acc. case u x of None \<Rightarrow> acc | Some f \<Rightarrow> Set.insert (h f) acc) xs A
   = A \<union> Option.these ((\<lambda>x. map_option h (u x)) ` set xs)"
  by (induct xs arbitrary: A) (auto split: option.splits)

lemma umatch_table_rbt[code]:
  "umatch_table tms cs (RBT_set rbt) = RBT_Set2.fold (\<lambda>x acc. case umatch tms x of None \<Rightarrow> acc
     | Some f \<Rightarrow> ed_insert (map (\<lambda>c. the (f c)) cs) acc) rbt {}"
proof -
  have i: "ID CCOMPARE(event_data list) \<noteq> None" by (simp add: ID_ccompare_etuple)
  show ?thesis
    unfolding umatch_table_def RBT_set_conv_keys[OF i] RBT_Set2.fold_conv_fold_keys' ed_insert_def
      these_image_fold RBT_Set2.keys.rep_eq by simp
qed

lemma umatch_table_other[code]:
  "umatch_table tms cs (DList_set d) = Option.these ((\<lambda>x. map_option (\<lambda>f. map (\<lambda>c. the (f c)) cs)
     (umatch tms x)) ` DList_set d)"
  "umatch_table tms cs (Set_Monad xs) = Option.these ((\<lambda>x. map_option (\<lambda>f. map (\<lambda>c. the (f c)) cs)
     (umatch tms x)) ` Set_Monad xs)"
  "umatch_table tms cs (Collect_set P) = Option.these ((\<lambda>x. map_option (\<lambda>f. map (\<lambda>c. the (f c)) cs)
     (umatch tms x)) ` Collect_set P)"
  "umatch_table tms cs (Complement Q) = Option.these ((\<lambda>x. map_option (\<lambda>f. map (\<lambda>c. the (f c)) cs)
     (umatch tms x)) ` Complement Q)"
  by (simp_all add: umatch_table_def)

text \<open>As above, the projection out of a mapping's tree has to be boxed at every value type, or
  the monomorphised lookup moves the per-call dictionary build one frame down into it.\<close>

setup \<open>Monomorphize.box_cmd
  (map (fn (tn, ty) => ("RBT_Mapping2.impl_of", "edl_impl_of_" ^ tn ^ "_v", [edl, ty]))
     edl_value_types)\<close>

section \<open>The executable operations, at the element type the evaluator uses\<close>

text \<open>
  The executable evaluator's generic layer is polymorphic in the element type, so the code generator
  gives every operation of it a dictionary argument and rebuilds the composite comparator from
  that argument at every call.  Without this section the generated probe reads

  @{verbatim \<open>let rec gprobe_step_l (_A1, _A2, _A3) p rk m y acc =
    (match lookupa ((ccompare_list _A2), (equal_list _A3)) m (eproj rk y)
     with None -> acc
     | Some l -> fold (fun x -> insert ((ceq_list _A1), (ccompare_list _A2)) (emerge p x y)) l acc)\<close>}

  and the generality is paid for once per probed tuple.  Specialising each operation at
  @{typ event_data} lets @{thm [source] etuple_dict_simps} fix the dictionaries and the rules above
  pick up @{const ed_comparator} and the specialised tree primitives.
\<close>

ML \<open>
val exec_elem_consts =
  ["gbin_join", "gbin_join0", "ggen_join", "gindex", "gindex_step",
   "gprobe_step", "gprobe_step_l", "gands_pos", "gands_neg", "gmulti_join",
   "esemi", "esemi_idx",
   "ginit_dq", "geval_step_dq", "gshift_dq", "geval_dq",
   "guntil_step_dq", "guntil_elem_step_dq", "gadd_new_dq",
   "tcomp", "tw_init", "tw_push", "tw_update", "tw_result", "tw_empty", "ecomp", "esum_of", "eunion",
   "eraux_shift", "eraux_update", "eraux_eval",
   "gnth", "glookup", "gmrtabulate", "geps_lax", "greps_strict", "gleps_strict",
   "grdelta", "gldelta", "gupdate_matchP", "gupdate_matchF_base", "gupdate_matchF_step",
   "gupdate_matchF", "geval_matchF",
   "eidx_add1", "eidx_add", "eidx_del1", "eidx_del", "ebucket", "fold_filter_set",
   "einit_msaux", "ejoin_msaux", "eadd_new_ts_msaux'", "eadd_new_ts_msaux",
   "eadd_new_table_msaux", "eadd_new_table_lz", "egc_msaux", "egc_join_msaux", "egc_join_lz",
   "eshift_end", "eidx_upd", "eidx",
   "itab", "iset", "iidxs", "iindex", "iensure1", "iensure", "iupd", "iins", "idel", "iadd", "isub", "iunion",
   "iprobe", "iprobe_l", "ijoin0", "ijoin"]
fun mono_name pre c = pre ^ String.translate (fn #"'" => "a" | ch => String.str ch) c

(* The indexed window structures are defined at event_data already; specialising them still
   fixes the dictionaries of the operations they call, and must happen in the same call as the
   rest, before the operations they call are redirected to their own specialisations. *)
val iwindow_consts =
  ["icnt_add1", "icnt_del1", "icnt_add", "icnt_del",
   "isw_move", "isw_expire", "isw_add_new_ts", "isw_join", "isw_add_new_table", "isw_result",
   "isw_ensure",
   "ieshift_end", "ieadd_new_ts_msaux'", "ieadd_new_ts_msaux", "iegc_msaux",
   "ieadd_new_table_msaux", "ieadd_new_table_lz", "iejoin_msaux", "iegc_join_msaux",
   "iegc_join_lz", "ieresult_msaux", "iems_ensure",
   "iuw_extend", "iuw_step", "iuw_shift", "iuw_add_new", "iuw_eval", "iuw_ensure"]
\<close>

setup \<open>Monomorphize.monomorphize_cmd
  (map (fn c => (c, mono_name "de_" c, ["event_data"])) exec_elem_consts
   @ [("gupd_nested_step_dq", "de_gupd_nested_step_dq", ["nat + nat", "event_data list"]),
      ("mapping_delete_set", "de_mapping_delete_set_tstp", ["event_data list", "nat + nat"]),
      ("mrestrict1", "de_mrestrict1_nat", ["event_data list", "nat"]),
      ("mrestrict1", "de_mrestrict1_table", ["event_data list", "event_data list set"]),
      ("mfilter_keys", "de_mfilter_keys_nat", ["event_data list", "nat"]),
      ("mfilter_keys", "de_mfilter_keys_table", ["event_data list", "event_data list set"]),
      ("upd_set", "de_upd_set_nat", ["event_data list", "nat"]),
      ("upd_set_keys", "de_upd_set_keys", ["event_data list set", "nat", "event_data list"]),
      ("minus_keys", "de_minus_keys", ["event_data list", "nat"]),
      ("filter_set", "de_filter_set", ["nat", "event_data list"]),
      ("filter_cfi", "de_filter_cfi", ["nat", "event_data list"]),
      ("del_buckets", "de_del_buckets_nat", ["event_data list", "event_data list", "nat"]),
      ("del_buckets1", "de_del_buckets1_nat", ["event_data list", "event_data list", "nat"]),
      ("gjoin_idx", "de_gjoin_idx_nat", ["event_data list", "event_data list", "nat"]),
      ("gjoin_idx1", "de_gjoin_idx1_nat", ["event_data list", "event_data list", "nat"]),
      ("mapping_delete_set", "de_mapping_delete_set_table",
        ["event_data list", "event_data list set"])]
   @ [("igjoin_idx", "de_igjoin_idx_nat", ["event_data list", "event_data", "nat"])]
   @ map (fn c => (c, mono_name "de_" c, [])) iwindow_consts)
  ["etuple_dict_simps"]\<close>

text \<open>The deletion of a key set passes the deletion to the tree's fold unapplied; at the two
  value types of the Since structure it gets the specialised deletion by hand.\<close>

lemma de_mapping_delete_set_table_rbt[code]:
  "de_mapping_delete_set_table m (RBT_set rbt) = RBT_Set2.fold ed_delete_table rbt m"
  by (simp add: de_mapping_delete_set_table_def ed_delete_table_def mapping_delete_set_RBT_code
      ID_ccompare_etuple ccomp_etuple)

section \<open>The set and mapping operations whose dictionaries are built once\<close>

text \<open>
  Monomorphising the executable operations fixes the type but does not by itself remove every
  dictionary: the operations they call that are not themselves specialised -- the emptiness tests,
  the folds, the mapping projections -- still take one, and a monomorphic caller builds it on the
  spot rather than receiving it.  @{theory Monitor_Impl.Monomorphic_Code} boxes those at
  the kernel's value types; the same at the executable evaluator's own.
\<close>

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
  (maps (fn (c, nm) => map (fn (tn, ty) => (c, "edl_" ^ nm ^ "_" ^ tn ^ "_v", [edl, ty]))
     (("tuples", "event_data list list") :: edl_value_types))
   [("Mapping.filter", "mfilter"), ("Mapping.keys", "keys"),
    ("Mapping.is_empty", "mis_empty"), ("Mapping.combine", "combine")])\<close>

(*<*)
end
(*>*)
