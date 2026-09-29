(*<*)
theory Dense_Tree_Code
  imports Dense_Idx
begin
(*>*)

text \<open>
  The tree code of the dense monitor's export.  It comes from the code-generator theories of
  the dense evaluator that ran before the kernel was dense (\<^verbatim>\<open>Dense_Code_Opt\<close>,
  \<^verbatim>\<open>Dense_Map_Upd\<close>, \<^verbatim>\<open>Dense_RBT_Code\<close> and \<^verbatim>\<open>Dense_Mono_Hot\<close>), where the
  copies at the evaluator's short tuples and those at the kernel's tuples were separate; the
  kernel's tuples are the short tuples now, so one copy remains.  Nothing here is about the
  monitor: each specialised function is defined as the library's at @{const ed_comparator}, or
  each code equation is proved from the library's definitions.
\<close>

section \<open>The tree primitives with the comparator called directly\<close>

text \<open>
  Monomorphisation gets @{const ed_comparator} as far as the red-black tree, but no further: the
  primitives of @{theory Deriving.RBT_Comparator_Impl} take the comparator as an argument, so
  inside @{const rbt_comp_lookup} it is an unknown function and OCaml compiles @{text "c k x"} as
  a generic two-argument application.  It also stops the comparator from being inlined.

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

lemma ed_rbtc_del_from_left_simps:
  "ed_rbtc_del_from_left x (RBT_Impl.Branch RBT_Impl.B lt z v rt) y s b =
     balance_left (ed_rbtc_del x (RBT_Impl.Branch RBT_Impl.B lt z v rt)) y s b"
  "ed_rbtc_del_from_left x RBT_Impl.Empty y s b =
     RBT_Impl.Branch RBT_Impl.R (ed_rbtc_del x RBT_Impl.Empty) y s b"
  "ed_rbtc_del_from_left x (RBT_Impl.Branch RBT_Impl.R va vb vc vd) y s b =
     RBT_Impl.Branch RBT_Impl.R
       (ed_rbtc_del x (RBT_Impl.Branch RBT_Impl.R va vb vc vd)) y s b"
  unfolding ed_rbtc_del_def ed_rbtc_del_from_left_def by simp_all

lemma ed_rbtc_del_from_right_simps:
  "ed_rbtc_del_from_right x a y s (RBT_Impl.Branch RBT_Impl.B lt z v rt) =
     balance_right a y s (ed_rbtc_del x (RBT_Impl.Branch RBT_Impl.B lt z v rt))"
  "ed_rbtc_del_from_right x a y s RBT_Impl.Empty =
     RBT_Impl.Branch RBT_Impl.R a y s (ed_rbtc_del x RBT_Impl.Empty)"
  "ed_rbtc_del_from_right x a y s (RBT_Impl.Branch RBT_Impl.R va vb vc vd) =
     RBT_Impl.Branch RBT_Impl.R a y s
       (ed_rbtc_del x (RBT_Impl.Branch RBT_Impl.R va vb vc vd))"
  unfolding ed_rbtc_del_def ed_rbtc_del_from_right_def by simp_all

text \<open>The two descending steps inspect one level at a time: a black node passed on unchanged is
  not rebuilt from its fields.\<close>

lemma ed_rbtc_del_from_left_code[code]:
  "ed_rbtc_del_from_left x a y s b = (case a of
     RBT_Impl.Empty \<Rightarrow> Branch RBT_Impl.R RBT_Impl.Empty y s b
   | Branch ca lt z v rt \<Rightarrow> (case ca of
       RBT_Impl.B \<Rightarrow> balance_left (ed_rbtc_del x a) y s b
     | RBT_Impl.R \<Rightarrow> Branch RBT_Impl.R (ed_rbtc_del x a) y s b))"
  by (cases a) (simp_all add: ed_rbtc_del_from_left_simps ed_rbtc_del_simps split: color.split)

lemma ed_rbtc_del_from_right_code[code]:
  "ed_rbtc_del_from_right x a y s b = (case b of
     RBT_Impl.Empty \<Rightarrow> Branch RBT_Impl.R a y s RBT_Impl.Empty
   | Branch cb lt z v rt \<Rightarrow> (case cb of
       RBT_Impl.B \<Rightarrow> balance_right a y s (ed_rbtc_del x b)
     | RBT_Impl.R \<Rightarrow> Branch RBT_Impl.R a y s (ed_rbtc_del x b)))"
  by (cases b) (simp_all add: ed_rbtc_del_from_right_simps ed_rbtc_del_simps split: color.split)

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

section \<open>The tree union, difference and intersection at the comparator\<close>

text \<open>The union and the difference of two trees fall back, on a small operand, to inserting
  or deleting its keys one by one, and they split the other tree at a key; the intersection
  looks the small operand's keys up in the other tree.  All took the comparator as an argument
  and called it through a closure at every node.  These are their copies at
  @{const ed_comparator}, with the specialised insertion, deletion, lookup and split.\<close>

definition ed_rbtc_split :: "(event_data tuple, 'v) rbt \<Rightarrow> event_data tuple \<Rightarrow>
    (event_data tuple, 'v) rbt \<times> 'v option \<times> (event_data tuple, 'v) rbt" where
  "ed_rbtc_split = rbt_split_comp ed_comparator"

lemma ed_rbtc_split_simps[code]:
  "ed_rbtc_split RBT_Impl.Empty k = (RBT_Impl.Empty, None, RBT_Impl.Empty)"
  "ed_rbtc_split (RBT_Impl.Branch cc l a b r) x = (case ed_comparator x a of
    Lt \<Rightarrow> (case ed_rbtc_split l x of (l1, \<beta>, l2) \<Rightarrow> (l1, \<beta>, RBT_Impl.rbt_join l2 a b r))
  | Gt \<Rightarrow> (case ed_rbtc_split r x of (r1, \<beta>, r2) \<Rightarrow> (RBT_Impl.rbt_join l a b r1, \<beta>, r2))
  | Eq \<Rightarrow> (l, Some b, r))"
  unfolding ed_rbtc_split_def by simp_all

lemma ed_rbtc_split_unfold[code_unfold]: "rbt_split_comp ed_comparator = ed_rbtc_split"
  by (simp add: ed_rbtc_split_def)

definition ed_rbtc_union_swap_rec :: "(event_data tuple \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow> bool \<Rightarrow>
    (event_data tuple, 'v) rbt \<Rightarrow> (event_data tuple, 'v) rbt \<Rightarrow> (event_data tuple, 'v) rbt" where
  "ed_rbtc_union_swap_rec = rbt_comp_union_swap_rec ed_comparator"

lemma ed_rbtc_union_swap_rec_code[code]: "ed_rbtc_union_swap_rec f \<gamma> t1 t2 = (let (\<gamma>, t2, t1) =
    if RBT_Impl.flip_rbt t2 t1 then (\<not>\<gamma>, t1, t2) else (\<gamma>, t2, t1);
    f' = (if \<gamma> then (\<lambda>k v v'. f k v' v) else f) in
    if RBT_Impl.small_rbt t2 then RBT_Impl.fold (ed_rbtc_insert_with_key f') t2 t1
    else case t1 of rbt.Empty \<Rightarrow> t2
      | Branch x l1 a b r1 \<Rightarrow>
        case ed_rbtc_split t2 a of (l2, \<beta>, r2) \<Rightarrow>
          RBT_Impl.rbt_join (ed_rbtc_union_swap_rec f \<gamma> l1 l2) a
            (case \<beta> of None \<Rightarrow> b | Some x \<Rightarrow> f' a b x) (ed_rbtc_union_swap_rec f \<gamma> r1 r2))"
  unfolding ed_rbtc_union_swap_rec_def ed_rbtc_insert_with_key_def ed_rbtc_split_def
  by (rule rbt_comp_union_swap_rec.simps)

definition ed_rbtc_union_with_key :: "(event_data tuple \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow>
    (event_data tuple, 'v) rbt \<Rightarrow> (event_data tuple, 'v) rbt \<Rightarrow> (event_data tuple, 'v) rbt" where
  "ed_rbtc_union_with_key = rbt_comp_union_with_key ed_comparator"

lemma ed_rbtc_union_with_key_code[code]:
  "ed_rbtc_union_with_key f t1 t2 = RBT_Impl.paint RBT_Impl.B (ed_rbtc_union_swap_rec f False t1 t2)"
  by (simp add: ed_rbtc_union_with_key_def ed_rbtc_union_swap_rec_def rbt_comp_union_with_key_def)

lemma ed_rbtc_union_with_key_unfold[code_unfold]:
  "rbt_comp_union_with_key ed_comparator = ed_rbtc_union_with_key"
  by (simp add: ed_rbtc_union_with_key_def)

definition ed_comp_minus :: "(event_data tuple, 'v) rbt \<Rightarrow> (event_data tuple, 'v) rbt \<Rightarrow>
    (event_data tuple, 'v) rbt" where
  "ed_comp_minus = comp_minus ed_comparator"

lemma ed_comp_minus_code[code]: "ed_comp_minus t1 t2 =
    (if RBT_Impl.small_rbt t2 then RBT_Impl.fold (\<lambda>k _ t. ed_rbtc_delete k t) t2 t1
     else if RBT_Impl.small_rbt t1 then rbtreeify (filter_comp_minus ed_comparator t1 t2)
     else case t2 of RBT_Impl.Empty \<Rightarrow> t1
       | RBT_Impl.Branch _ l2 a b r2 \<Rightarrow>
         case ed_rbtc_split t1 a of (l1, _, r1) \<Rightarrow>
           RBT_Impl.rbt_join2 (ed_comp_minus l1 l2) (ed_comp_minus r1 r2))"
  unfolding ed_comp_minus_def ed_rbtc_delete_def ed_rbtc_split_def
  by (rule comp_minus.simps)

definition ed_rbtc_minus :: "(event_data tuple, 'v) rbt \<Rightarrow> (event_data tuple, 'v) rbt \<Rightarrow>
    (event_data tuple, 'v) rbt" where
  "ed_rbtc_minus = rbt_comp_minus ed_comparator"

lemma ed_rbtc_minus_code[code]: "ed_rbtc_minus t1 t2 = RBT_Impl.paint RBT_Impl.B (ed_comp_minus t1 t2)"
  by (simp add: ed_rbtc_minus_def ed_comp_minus_def rbt_comp_minus_def)

lemma ed_rbtc_minus_unfold[code_unfold]: "rbt_comp_minus ed_comparator = ed_rbtc_minus"
  by (simp add: ed_rbtc_minus_def)

definition ed_map_filter_comp_inter :: "(event_data tuple \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow>
    (event_data tuple, 'v) rbt \<Rightarrow> (event_data tuple, 'v) rbt \<Rightarrow> (event_data tuple \<times> 'v) list" where
  "ed_map_filter_comp_inter = map_filter_comp_inter ed_comparator"

lemma ed_map_filter_comp_inter_code[code]: "ed_map_filter_comp_inter f t1 t2 =
    List.map_filter (\<lambda>(k, v). case ed_rbtc_lookup t1 k of None \<Rightarrow> None
      | Some v' \<Rightarrow> Some (k, f k v' v)) (RBT_Impl.entries t2)"
  by (simp add: ed_map_filter_comp_inter_def map_filter_comp_inter_def ed_rbtc_lookup_def)

lemma ed_map_filter_comp_inter_unfold[code_unfold]:
  "map_filter_comp_inter ed_comparator = ed_map_filter_comp_inter"
  by (simp add: ed_map_filter_comp_inter_def)

definition ed_rbtc_inter_swap_rec :: "(event_data tuple \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow> bool \<Rightarrow>
    (event_data tuple, 'v) rbt \<Rightarrow> (event_data tuple, 'v) rbt \<Rightarrow> (event_data tuple, 'v) rbt" where
  "ed_rbtc_inter_swap_rec = rbt_comp_inter_swap_rec ed_comparator"

lemma ed_rbtc_inter_swap_rec_code[code]: "ed_rbtc_inter_swap_rec f \<gamma> t1 t2 = (let (\<gamma>, t2, t1) =
    if RBT_Impl.flip_rbt t2 t1 then (\<not>\<gamma>, t1, t2) else (\<gamma>, t2, t1);
    f' = if \<gamma> then (\<lambda>k v v'. f k v' v) else f in
    if RBT_Impl.small_rbt t2 then rbtreeify (ed_map_filter_comp_inter f' t1 t2)
    else case t1 of rbt.Empty \<Rightarrow> rbt.Empty
    | Branch x l1 a b r1 \<Rightarrow>
      (case ed_rbtc_split t2 a of (l2, \<beta>, r2) \<Rightarrow>
        let l' = ed_rbtc_inter_swap_rec f \<gamma> l1 l2; r' = ed_rbtc_inter_swap_rec f \<gamma> r1 r2 in
        (case \<beta> of None \<Rightarrow> RBT_Impl.rbt_join2 l' r' | Some b' \<Rightarrow> RBT_Impl.rbt_join l' a (f' a b b') r')))"
  unfolding ed_rbtc_inter_swap_rec_def ed_map_filter_comp_inter_def ed_rbtc_split_def
  by (rule rbt_comp_inter_swap_rec.simps)

definition ed_rbtc_inter_with_key :: "(event_data tuple \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow>
    (event_data tuple, 'v) rbt \<Rightarrow> (event_data tuple, 'v) rbt \<Rightarrow> (event_data tuple, 'v) rbt" where
  "ed_rbtc_inter_with_key = rbt_comp_inter_with_key ed_comparator"

lemma ed_rbtc_inter_with_key_code[code]:
  "ed_rbtc_inter_with_key f t1 t2 = RBT_Impl.paint RBT_Impl.B (ed_rbtc_inter_swap_rec f False t1 t2)"
  by (simp add: ed_rbtc_inter_with_key_def ed_rbtc_inter_swap_rec_def rbt_comp_inter_with_key_def)

lemma ed_rbtc_inter_with_key_unfold[code_unfold]:
  "rbt_comp_inter_with_key ed_comparator = ed_rbtc_inter_with_key"
  by (simp add: ed_rbtc_inter_with_key_def)

section \<open>The set operations, monomorphised rather than boxed\<close>

text \<open>
  @{theory MFODL_Monitor_Devel.Monomorphic_Code} boxes the set operations -- @{term "(\<union>)"},
  @{term "(\<inter>)"}, @{term "(-)"}, @{const Set.filter}, @{const image} -- and monomorphises only
  membership and lookup.  A box builds the dictionary once, when the program starts, which
  removes the construction cost; but it still passes the dictionary, so the comparator that
  reaches the red-black tree inside is the generic one on lists, reached through a closure for
  every element.  Monomorphising them instead fixes the type, which lets
  @{thm [source] ccomp_etuple} rewrite the comparator to @{const ed_comparator}, and the rules
  of the previous sections then pick up the specialised tree primitives.  The boxes' redirect
  rules have to leave the code preprocessor first, or the two would compete for the same term.
\<close>

setup \<open>Code_Preproc.map_pre (fn ctxt => ctxt delsimps
  @{thms ed_union_v_unfold ed_inter_v_unfold ed_minus_v_unfold ed_filter_v_unfold
    ed_image_v_unfold})\<close>

setup \<open>Monomorphize.monomorphize_cmd
  [("sup :: _ set \<Rightarrow> _", "ed_union", [etuple]),
   ("inf :: _ set \<Rightarrow> _", "ed_inter", [etuple]),
   ("Groups.minus_class.minus :: _ set \<Rightarrow> _", "ed_minus", [etuple]),
   ("Set.filter", "ed_filter", [etuple]),
   ("image", "ed_image", [etuple, etuple])]
  ["etuple_dict_simps"]\<close>

text \<open>
  Monomorphising the class operations is only half of it: their tree-to-tree branches, which are
  the hot ones, call the primitives of @{theory Containers.RBT_Mapping2} and
  @{theory Containers.RBT_Set2}, and those take the comparator as an argument, so what the
  monomorphisation achieves on its own is to move the dictionary build from the box's
  once-at-start into the branch.  The primitives have to go with them.
\<close>

setup \<open>Monomorphize.monomorphize_cmd
  [("RBT_Mapping2.join", "ed_rbt_join_unit", [etuple, "unit"]),
   ("RBT_Mapping2.meet", "ed_rbt_meet_unit", [etuple, "unit"]),
   ("RBT_Set2.minus", "ed_rbt_set_minus", [etuple]),
   ("RBT_Set2.inter_list", "ed_rbt_inter_list", [etuple])]
  ["etuple_dict_simps"]\<close>

section \<open>The red-black trees' rebalancing, in code\<close>

text \<open>
  @{const RBT_Impl.balance} restores the colour invariant on the way back up from an insertion,
  at every level of every insertion into every tree the monitor keeps.  Its equations are
  sequential, and its last one, @{text "balance a s t b = Branch B a s t b"}, is what applies at
  almost every level.  The code generator completes the patterns of such a definition into
  disjoint nested ones, which replaces the variables @{text a} and @{text b} of that last equation
  by the constructors they were split into -- so the generated code rebuilds both subtrees from
  their fields, three blocks where one is needed.

  The code equation below therefore inspects the arguments one level at a time, a node and then
  its colour, and never splits a variable that its right-hand side uses; the two sides that are
  checked for a red child, the left one only when it is red itself, are two small functions.
  In @{text bal_right} the right child's left child matters only when the right child's right
  child is not red; the fallback it gives is a function of its own, so that the red case does
  not build it first.
\<close>

definition bal_right_b :: "('a, 'b) rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) rbt \<Rightarrow>
    ('a, 'b) rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt" where
  "bal_right_b l k v r b s t c = (case b of
     RBT_Impl.Empty \<Rightarrow> Branch RBT_Impl.B l k v r
   | Branch cb b1 s1 t1 c1 \<Rightarrow> (case cb of
       RBT_Impl.B \<Rightarrow> Branch RBT_Impl.B l k v r
     | RBT_Impl.R \<Rightarrow> Branch RBT_Impl.R (Branch RBT_Impl.B l k v b1) s1 t1
                        (Branch RBT_Impl.B c1 s t c)))"

definition bal_right :: "('a, 'b) rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt" where
  "bal_right l k v r = (case r of
     RBT_Impl.Empty \<Rightarrow> Branch RBT_Impl.B l k v r
   | Branch cr b s t c \<Rightarrow> (case cr of
       RBT_Impl.B \<Rightarrow> Branch RBT_Impl.B l k v r
     | RBT_Impl.R \<Rightarrow>
       (case c of
          RBT_Impl.Empty \<Rightarrow> bal_right_b l k v r b s t c
        | Branch cc c1 y z d \<Rightarrow> (case cc of
            RBT_Impl.B \<Rightarrow> bal_right_b l k v r b s t c
          | RBT_Impl.R \<Rightarrow> Branch RBT_Impl.R (Branch RBT_Impl.B l k v b) s t
                             (Branch RBT_Impl.B c1 y z d)))))"

definition bal_left :: "('a, 'b) rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) rbt \<Rightarrow>
    ('a, 'b) rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt" where
  "bal_left a w x b l k v r = (case a of
     RBT_Impl.Empty \<Rightarrow> (case b of
         RBT_Impl.Empty \<Rightarrow> bal_right l k v r
       | Branch cb b1 s t c \<Rightarrow> (case cb of
           RBT_Impl.B \<Rightarrow> bal_right l k v r
         | RBT_Impl.R \<Rightarrow> Branch RBT_Impl.R (Branch RBT_Impl.B a w x b1) s t (Branch RBT_Impl.B c k v r)))
   | Branch ca a1 w1 x1 b1 \<Rightarrow> (case ca of
       RBT_Impl.R \<Rightarrow> Branch RBT_Impl.R (Branch RBT_Impl.B a1 w1 x1 b1) w x (Branch RBT_Impl.B b k v r)
     | RBT_Impl.B \<Rightarrow> (case b of
         RBT_Impl.Empty \<Rightarrow> bal_right l k v r
       | Branch cb b2 s t c \<Rightarrow> (case cb of
           RBT_Impl.B \<Rightarrow> bal_right l k v r
         | RBT_Impl.R \<Rightarrow> Branch RBT_Impl.R (Branch RBT_Impl.B a w x b2) s t
                            (Branch RBT_Impl.B c k v r)))))"

lemma balance_code[code]:
  "balance l k v r = (case l of
     RBT_Impl.Empty \<Rightarrow> bal_right l k v r
   | Branch cl a w x b \<Rightarrow> (case cl of
       RBT_Impl.B \<Rightarrow> bal_right l k v r
     | RBT_Impl.R \<Rightarrow> (case r of
         RBT_Impl.Empty \<Rightarrow> bal_left a w x b l k v r
       | Branch cr c y z d \<Rightarrow> (case cr of
           RBT_Impl.B \<Rightarrow> bal_left a w x b l k v r
         | RBT_Impl.R \<Rightarrow> Branch RBT_Impl.R (Branch RBT_Impl.B a w x b) k v
                            (Branch RBT_Impl.B c y z d)))))"
  by (cases "(l, k, v, r)" rule: balance.cases)
    (simp_all add: bal_left_def bal_right_def bal_right_b_def split: color.split)

text \<open>
  The deletion has the same problem.  Its rebalancing steps @{const balance_left} and
  @{const balance_right} and its @{const RBT_Impl.combine} of a deleted node's children are
  sequential equations, whose completed patterns rebuild the subtrees they only look at: a black
  node passed on unchanged, at every level of every deletion.  The equations below inspect one
  level at a time, as above.
\<close>

definition bal_left_del :: "('a, 'b) rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt" where
  "bal_left_del l k x r = (case r of
     RBT_Impl.Empty \<Rightarrow> RBT_Impl.Empty
   | Branch cr a s y b \<Rightarrow> (case cr of
       RBT_Impl.B \<Rightarrow> balance l k x (Branch RBT_Impl.R a s y b)
     | RBT_Impl.R \<Rightarrow> (case a of
         RBT_Impl.Empty \<Rightarrow> RBT_Impl.Empty
       | Branch ca a1 s1 y1 b1 \<Rightarrow> (case ca of
           RBT_Impl.B \<Rightarrow> Branch RBT_Impl.R (Branch RBT_Impl.B l k x a1) s1 y1
                          (balance b1 s y (RBT_Impl.paint RBT_Impl.R b))
         | RBT_Impl.R \<Rightarrow> RBT_Impl.Empty))))"

lemma balance_left_code[code]:
  "balance_left l k x r = (case l of
     RBT_Impl.Empty \<Rightarrow> bal_left_del l k x r
   | Branch cl a k' x' b \<Rightarrow> (case cl of
       RBT_Impl.R \<Rightarrow> Branch RBT_Impl.R (Branch RBT_Impl.B a k' x' b) k x r
     | RBT_Impl.B \<Rightarrow> bal_left_del l k x r))"
  by (cases "(l, k, x, r)" rule: balance_left.cases) (simp_all add: bal_left_del_def)

definition bal_right_del :: "('a, 'b) rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt" where
  "bal_right_del l k x r = (case l of
     RBT_Impl.Empty \<Rightarrow> RBT_Impl.Empty
   | Branch cl a1 k1 x1 b1 \<Rightarrow> (case cl of
       RBT_Impl.B \<Rightarrow> balance (Branch RBT_Impl.R a1 k1 x1 b1) k x r
     | RBT_Impl.R \<Rightarrow> (case b1 of
         RBT_Impl.Empty \<Rightarrow> RBT_Impl.Empty
       | Branch cb b2 s2 y2 c2 \<Rightarrow> (case cb of
           RBT_Impl.B \<Rightarrow> Branch RBT_Impl.R (balance (RBT_Impl.paint RBT_Impl.R a1) k1 x1 b2) s2 y2
                          (Branch RBT_Impl.B c2 k x r)
         | RBT_Impl.R \<Rightarrow> RBT_Impl.Empty))))"

lemma balance_right_code[code]:
  "balance_right l k x r = (case r of
     RBT_Impl.Empty \<Rightarrow> bal_right_del l k x r
   | Branch cr b s y c \<Rightarrow> (case cr of
       RBT_Impl.R \<Rightarrow> Branch RBT_Impl.R l k x (Branch RBT_Impl.B b s y c)
     | RBT_Impl.B \<Rightarrow> bal_right_del l k x r))"
  by (cases "(l, k, x, r)" rule: balance_right.cases) (simp_all add: bal_right_del_def)

lemma combine_code[code]:
  "RBT_Impl.combine l r = (case l of
     RBT_Impl.Empty \<Rightarrow> r
   | Branch cl a k x b \<Rightarrow> (case r of
       RBT_Impl.Empty \<Rightarrow> l
     | Branch cr c s y d \<Rightarrow> (case cl of
         RBT_Impl.R \<Rightarrow> (case cr of
             RBT_Impl.R \<Rightarrow> (let bc = RBT_Impl.combine b c in case bc of
                 RBT_Impl.Empty \<Rightarrow> Branch RBT_Impl.R a k x (Branch RBT_Impl.R bc s y d)
               | Branch cbc b2 t z c2 \<Rightarrow> (case cbc of
                   RBT_Impl.R \<Rightarrow> Branch RBT_Impl.R (Branch RBT_Impl.R a k x b2) t z
                                  (Branch RBT_Impl.R c2 s y d)
                 | RBT_Impl.B \<Rightarrow> Branch RBT_Impl.R a k x (Branch RBT_Impl.R bc s y d)))
           | RBT_Impl.B \<Rightarrow> Branch RBT_Impl.R a k x (RBT_Impl.combine b r))
       | RBT_Impl.B \<Rightarrow> (case cr of
             RBT_Impl.R \<Rightarrow> Branch RBT_Impl.R (RBT_Impl.combine l c) s y d
           | RBT_Impl.B \<Rightarrow> (let bc = RBT_Impl.combine b c in case bc of
                 RBT_Impl.Empty \<Rightarrow> balance_left a k x (Branch RBT_Impl.B bc s y d)
               | Branch cbc b2 t z c2 \<Rightarrow> (case cbc of
                   RBT_Impl.R \<Rightarrow> Branch RBT_Impl.R (Branch RBT_Impl.B a k x b2) t z
                                  (Branch RBT_Impl.B c2 s y d)
                 | RBT_Impl.B \<Rightarrow> balance_left a k x (Branch RBT_Impl.B bc s y d)))))))"
  by (cases "(l, r)" rule: RBT_Impl.combine.cases) (simp_all add: Let_def split: rbt.split color.split)

text \<open>An insertion and a deletion end by painting the root black, which rebuilt the root although
  it almost always is black already.\<close>

lemma paint_code[code]:
  "RBT_Impl.paint c t = (case t of
     RBT_Impl.Empty \<Rightarrow> RBT_Impl.Empty
   | Branch c' l k v r \<Rightarrow> (case c of
       RBT_Impl.B \<Rightarrow> (case c' of RBT_Impl.B \<Rightarrow> t | RBT_Impl.R \<Rightarrow> Branch RBT_Impl.B l k v r)
     | RBT_Impl.R \<Rightarrow> (case c' of RBT_Impl.R \<Rightarrow> t | RBT_Impl.B \<Rightarrow> Branch RBT_Impl.R l k v r)))"
  by (cases t) (simp_all split: color.split)

section \<open>The join-based set operations, without counting black heights\<close>

text \<open>
  The union, the intersection and the difference of two red-black trees split one tree at the
  other's root and join the results back together.  Every join, and every recursive step of the
  operations themselves, compares the black heights of two trees, and the library computes each
  height as a @{typ nat} by walking the tree's left spine -- a boxed number per level, and per
  call.  @{theory MFODL_Monitor_Devel.RBT_set_opt} already decides these comparisons for its own
  trees by descending the two spines in lockstep, or by counting a bound down; both allocate
  nothing.  Those are stated for the trees of unit values; the library's operations are at
  every value type, so the two comparisons are restated here at that generality and the
  library's code equations are replaced by ones that use them.
\<close>

function bh_le_g :: "('a, 'b) rbt \<Rightarrow> ('c, 'd) rbt \<Rightarrow> bool" where
  "bh_le_g RBT_Impl.Empty t2 = True"
| "bh_le_g (Branch RBT_Impl.R l1 a1 b1 r1) t2 = bh_le_g l1 t2"
| "bh_le_g (Branch RBT_Impl.B l1 a1 b1 r1) RBT_Impl.Empty = False"
| "bh_le_g (Branch RBT_Impl.B l1 a1 b1 r1) (Branch RBT_Impl.R l2 a2 b2 r2) =
     bh_le_g (Branch RBT_Impl.B l1 a1 b1 r1) l2"
| "bh_le_g (Branch RBT_Impl.B l1 a1 b1 r1) (Branch RBT_Impl.B l2 a2 b2 r2) = bh_le_g l1 l2"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(t1, t2). size t1 + size t2)") auto

lemma bh_le_g_correct: "bh_le_g t1 t2 \<longleftrightarrow> bheight t1 \<le> bheight t2"
  by (induction t1 t2 rule: bh_le_g.induct) auto

fun bh_lt_g :: "integer \<Rightarrow> ('a, 'b) rbt \<Rightarrow> bool" where
  "bh_lt_g k RBT_Impl.Empty = (0 < k)"
| "bh_lt_g k (Branch RBT_Impl.R l a b r) = bh_lt_g k l"
| "bh_lt_g k (Branch RBT_Impl.B l a b r) = (if k \<le> 0 then False else bh_lt_g (k - 1) l)"

lemma bh_lt_g_correct: "bh_lt_g k t \<longleftrightarrow> integer_of_nat (bheight t) < k"
proof (induction k t rule: bh_lt_g.induct)
  case (3 k l a b r)
  show ?case
  proof (cases "k \<le> 0")
    case True
    have "k \<le> 0" by (rule True)
    also have "(0::integer) \<le> 1 + of_nat (bheight l)"
      by simp
    finally have "k \<le> 1 + of_nat (bheight l)" .
    then show ?thesis using True by (simp add: integer_of_nat_eq_of_nat not_less)
  next
    case False
    then show ?thesis using 3
      by (simp add: integer_of_nat_eq_of_nat less_diff_eq add.commute)
  qed
qed (auto simp: integer_of_nat_eq_of_nat)

text \<open>The library's two tests, and the three joins, through the comparisons.  The union and the
  intersection come with code equations that compute both heights up front, and are given their
  defining equations back, which are stated with the two tests.\<close>

declare [[code drop: RBT_Impl.small_rbt RBT_Impl.flip_rbt RBT_Impl.rbt_joinL RBT_Impl.rbt_joinR
  RBT_Impl.rbt_join RBT_Comparator_Impl.rbt_comp_union_swap_rec
  RBT_Comparator_Impl.rbt_comp_inter_swap_rec]]

lemma small_rbt_bh_code[code]: "RBT_Impl.small_rbt t = bh_lt_g 4 t"
  by (simp add: RBT_Impl.small_rbt_def bh_lt_g_correct integer_of_nat_eq_of_nat)

lemma flip_rbt_bh_code[code]: "RBT_Impl.flip_rbt t1 t2 = (\<not> bh_le_g t1 t2)"
  by (simp add: RBT_Impl.flip_rbt_def bh_le_g_correct not_le)

lemma rbt_joinL_bh_code[code]: "RBT_Impl.rbt_joinL l a b r = (if bh_le_g r l
    then Branch RBT_Impl.R l a b r
    else case r of
      Branch RBT_Impl.B l' a' b' r' \<Rightarrow> rbt_baliL (RBT_Impl.rbt_joinL l a b l') a' b' r'
    | Branch RBT_Impl.R l' a' b' r' \<Rightarrow> Branch RBT_Impl.R (RBT_Impl.rbt_joinL l a b l') a' b' r')"
  by (subst RBT_Impl.rbt_joinL.simps) (simp add: bh_le_g_correct)

lemma rbt_joinR_bh_code[code]: "RBT_Impl.rbt_joinR l a b r = (if bh_le_g l r
    then Branch RBT_Impl.R l a b r
    else case l of
      Branch RBT_Impl.B l' a' b' r' \<Rightarrow> rbt_baliR l' a' b' (RBT_Impl.rbt_joinR r' a b r)
    | Branch RBT_Impl.R l' a' b' r' \<Rightarrow> Branch RBT_Impl.R l' a' b' (RBT_Impl.rbt_joinR r' a b r))"
  by (subst RBT_Impl.rbt_joinR.simps) (simp add: bh_le_g_correct)

lemma rbt_join_bh_code[code]: "RBT_Impl.rbt_join l a b r = (if \<not> bh_le_g l r
    then RBT_Impl.paint RBT_Impl.B (RBT_Impl.rbt_joinR l a b r)
    else if \<not> bh_le_g r l
    then RBT_Impl.paint RBT_Impl.B (RBT_Impl.rbt_joinL l a b r)
    else Branch RBT_Impl.B l a b r)"
  by (simp add: RBT_Impl.rbt_join_def bh_le_g_correct Let_def)

declare RBT_Comparator_Impl.rbt_comp_union_swap_rec.simps[code]
  RBT_Comparator_Impl.rbt_comp_inter_swap_rec.simps[code]

section \<open>The kernel's own set operations at the comparator\<close>

text \<open>The kernel's union, intersection and difference of two tables are those of
  @{theory MFODL_Monitor_Devel.RBT_set_opt}, over trees of unit values, and they too take the
  comparator as an argument.  These are their copies at @{const ed_comparator}; the tables'
  operations that call them get copies, so that the comparator they pass is resolved.\<close>

definition ed_split_comp :: "event_data tuple urbt \<Rightarrow> event_data tuple \<Rightarrow>
    event_data tuple urbt \<times> bool \<times> event_data tuple urbt" where
  "ed_split_comp = split_comp ed_comparator"

definition ed_union_comp :: "event_data tuple urbt \<Rightarrow> event_data tuple urbt \<Rightarrow> event_data tuple urbt" where
  "ed_union_comp = union_comp ed_comparator"

definition ed_inter_comp :: "event_data tuple urbt \<Rightarrow> event_data tuple urbt \<Rightarrow> event_data tuple urbt" where
  "ed_inter_comp = inter_comp ed_comparator"

definition ed_minus_comp :: "event_data tuple urbt \<Rightarrow> event_data tuple urbt \<Rightarrow> event_data tuple urbt" where
  "ed_minus_comp = minus_comp ed_comparator"

lemmas ed_split_comp_code[code] = split_comp.simps[of ed_comparator, folded ed_split_comp_def]

lemma ed_union_comp_code[code]: "ed_union_comp t1 t2 = (let (t1, t2) =
    if RBT_set_opt.flip_rbt t1 t2 then (t2, t1) else (t1, t2) in
    if RBT_set_opt.small_rbt t1 then RBT_Impl.fold (rbt_comp_insert ed_comparator) t1 t2
    else (case t2 of RBT_Impl.Empty \<Rightarrow> t1
      | RBT_Impl.Branch _ l2 a () r2 \<Rightarrow>
        case ed_split_comp t1 a of (l1, _, r1) \<Rightarrow>
          RBT_set_opt.rbt_join (ed_union_comp l1 l2) a (ed_union_comp r1 r2)))"
  unfolding ed_union_comp_def ed_split_comp_def by (rule union_comp.simps)

lemma ed_inter_comp_code[code]: "ed_inter_comp t1 t2 = (let (t1, t2) =
    if RBT_set_opt.flip_rbt t1 t2 then (t2, t1) else (t1, t2) in
    if RBT_set_opt.small_rbt t1 then
      rbtreeify (filter (\<lambda>(k, _). rbt_comp_lookup ed_comparator t2 k = Some ()) (RBT_Impl.entries t1))
    else case t2 of RBT_Impl.Empty \<Rightarrow> RBT_Impl.Empty
    | RBT_Impl.Branch _ l2 a () r2 \<Rightarrow>
      case ed_split_comp t1 a of (l1, ain, r1) \<Rightarrow>
        let l' = ed_inter_comp l1 l2; r' = ed_inter_comp r1 r2
        in if ain then RBT_set_opt.rbt_join l' a r' else RBT_set_opt.rbt_join2 l' r')"
  unfolding ed_inter_comp_def ed_split_comp_def by (rule inter_comp.simps)

lemma ed_minus_comp_code[code]: "ed_minus_comp t1 t2 = (if RBT_set_opt.small_rbt t2
    then RBT_Impl.fold (\<lambda>k _ t. rbt_comp_delete ed_comparator k t) t2 t1
    else if RBT_set_opt.small_rbt t1 then
      rbtreeify (filter (\<lambda>(k, _). rbt_comp_lookup ed_comparator t2 k = None) (RBT_Impl.entries t1))
    else case t2 of RBT_Impl.Empty \<Rightarrow> t1
      | RBT_Impl.Branch _ l2 a () r2 \<Rightarrow>
        case ed_split_comp t1 a of (l1, _, r1) \<Rightarrow>
          RBT_set_opt.rbt_join2 (ed_minus_comp l1 l2) (ed_minus_comp r1 r2))"
  unfolding ed_minus_comp_def ed_split_comp_def by (rule minus_comp.simps)

lemma ed_set_comp_unfold[code_unfold]:
  "split_comp ed_comparator = ed_split_comp"
  "union_comp ed_comparator = ed_union_comp"
  "inter_comp ed_comparator = ed_inter_comp"
  "minus_comp ed_comparator = ed_minus_comp"
  by (simp_all add: ed_split_comp_def ed_union_comp_def ed_inter_comp_def ed_minus_comp_def)

setup \<open>Monomorphize.monomorphize_cmd
  [("rbt_union_rbt_join2", "ed_rbt_union_join2", [etuple]),
   ("rbt_inter_rbt_join2", "ed_rbt_inter_join2", [etuple]),
   ("rbt_minus_rbt_join2", "ed_rbt_minus_join2", [etuple])]
  ["etuple_dict_simps"]\<close>

(*<*)
end
(*>*)
