(*<*)
theory Dense_Code_Opt
  imports Dense_Imp
begin
(*>*)

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

definition ed_rbt_lookup :: "(event_data tuple, 'v) rbt \<Rightarrow> event_data tuple \<Rightarrow> 'v option" where
  "ed_rbt_lookup = rbt_comp_lookup ed_comparator"

lemma ed_rbt_lookup_simps[code]:
  "ed_rbt_lookup RBT_Impl.Empty k = None"
  "ed_rbt_lookup (RBT_Impl.Branch cc l x y r) k =
     (case ed_comparator k x of Lt \<Rightarrow> ed_rbt_lookup l k | Gt \<Rightarrow> ed_rbt_lookup r k
        | Eq \<Rightarrow> Some y)"
  unfolding ed_rbt_lookup_def by simp_all

lemma ed_rbt_lookup_unfold[code_unfold]: "rbt_comp_lookup ed_comparator = ed_rbt_lookup"
  by (simp add: ed_rbt_lookup_def)

definition ed_rbt_ins :: "(event_data tuple \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow> event_data tuple \<Rightarrow> 'v \<Rightarrow>
    (event_data tuple, 'v) rbt \<Rightarrow> (event_data tuple, 'v) rbt" where
  "ed_rbt_ins = rbt_comp_ins ed_comparator"

lemma ed_rbt_ins_simps[code]:
  "ed_rbt_ins f k v RBT_Impl.Empty =
     RBT_Impl.Branch RBT_Impl.R RBT_Impl.Empty k v RBT_Impl.Empty"
  "ed_rbt_ins f k v (RBT_Impl.Branch RBT_Impl.B l x y r) =
     (case ed_comparator k x of Lt \<Rightarrow> balance (ed_rbt_ins f k v l) x y r
        | Gt \<Rightarrow> balance l x y (ed_rbt_ins f k v r)
        | Eq \<Rightarrow> RBT_Impl.Branch RBT_Impl.B l x (f k y v) r)"
  "ed_rbt_ins f k v (RBT_Impl.Branch RBT_Impl.R l x y r) =
     (case ed_comparator k x of Lt \<Rightarrow> RBT_Impl.Branch RBT_Impl.R (ed_rbt_ins f k v l) x y r
        | Gt \<Rightarrow> RBT_Impl.Branch RBT_Impl.R l x y (ed_rbt_ins f k v r)
        | Eq \<Rightarrow> RBT_Impl.Branch RBT_Impl.R l x (f k y v) r)"
  unfolding ed_rbt_ins_def by simp_all

lemma ed_rbt_ins_unfold[code_unfold]: "rbt_comp_ins ed_comparator = ed_rbt_ins"
  by (simp add: ed_rbt_ins_def)

definition ed_rbt_insert_with_key :: "(event_data tuple \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow> event_data tuple \<Rightarrow>
    'v \<Rightarrow> (event_data tuple, 'v) rbt \<Rightarrow> (event_data tuple, 'v) rbt" where
  "ed_rbt_insert_with_key = rbt_comp_insert_with_key ed_comparator"

lemma ed_rbt_insert_with_key_code[code]:
  "ed_rbt_insert_with_key f k v t = paint RBT_Impl.B (ed_rbt_ins f k v t)"
  by (simp add: ed_rbt_insert_with_key_def ed_rbt_ins_def rbt_comp_insert_with_key_def)

lemma ed_rbt_insert_with_key_unfold[code_unfold]:
  "rbt_comp_insert_with_key ed_comparator = ed_rbt_insert_with_key"
  by (simp add: ed_rbt_insert_with_key_def)

definition ed_rbt_insert :: "event_data tuple \<Rightarrow> 'v \<Rightarrow> (event_data tuple, 'v) rbt \<Rightarrow>
    (event_data tuple, 'v) rbt" where
  "ed_rbt_insert = rbt_comp_insert ed_comparator"

lemma ed_rbt_insert_code[code]:
  "ed_rbt_insert k v t = ed_rbt_insert_with_key (\<lambda>_ _ nv. nv) k v t"
  by (simp add: ed_rbt_insert_def ed_rbt_insert_with_key_def rbt_comp_insert_def)

lemma ed_rbt_insert_unfold[code_unfold]: "rbt_comp_insert ed_comparator = ed_rbt_insert"
  by (simp add: ed_rbt_insert_def)

text \<open>
  The deletion is three mutually recursive functions, and its two catch-all equations are split
  into the cases the code generator gets anyway.
\<close>

definition ed_rbt_del :: "event_data tuple \<Rightarrow> (event_data tuple, 'v) rbt \<Rightarrow>
    (event_data tuple, 'v) rbt" where
  "ed_rbt_del = rbt_comp_del ed_comparator"

definition ed_rbt_del_from_left :: "event_data tuple \<Rightarrow> (event_data tuple, 'v) rbt \<Rightarrow>
    event_data tuple \<Rightarrow> 'v \<Rightarrow> (event_data tuple, 'v) rbt \<Rightarrow> (event_data tuple, 'v) rbt" where
  "ed_rbt_del_from_left = rbt_comp_del_from_left ed_comparator"

definition ed_rbt_del_from_right :: "event_data tuple \<Rightarrow> (event_data tuple, 'v) rbt \<Rightarrow>
    event_data tuple \<Rightarrow> 'v \<Rightarrow> (event_data tuple, 'v) rbt \<Rightarrow> (event_data tuple, 'v) rbt" where
  "ed_rbt_del_from_right = rbt_comp_del_from_right ed_comparator"

lemma ed_rbt_del_simps[code]:
  "ed_rbt_del x RBT_Impl.Empty = RBT_Impl.Empty"
  "ed_rbt_del x (RBT_Impl.Branch cc a y s b) =
     (case ed_comparator x y of Lt \<Rightarrow> ed_rbt_del_from_left x a y s b
        | Gt \<Rightarrow> ed_rbt_del_from_right x a y s b | Eq \<Rightarrow> RBT_Impl.combine a b)"
  unfolding ed_rbt_del_def ed_rbt_del_from_left_def ed_rbt_del_from_right_def by simp_all

lemma ed_rbt_del_from_left_simps[code]:
  "ed_rbt_del_from_left x (RBT_Impl.Branch RBT_Impl.B lt z v rt) y s b =
     balance_left (ed_rbt_del x (RBT_Impl.Branch RBT_Impl.B lt z v rt)) y s b"
  "ed_rbt_del_from_left x RBT_Impl.Empty y s b =
     RBT_Impl.Branch RBT_Impl.R (ed_rbt_del x RBT_Impl.Empty) y s b"
  "ed_rbt_del_from_left x (RBT_Impl.Branch RBT_Impl.R va vb vc vd) y s b =
     RBT_Impl.Branch RBT_Impl.R
       (ed_rbt_del x (RBT_Impl.Branch RBT_Impl.R va vb vc vd)) y s b"
  unfolding ed_rbt_del_def ed_rbt_del_from_left_def by simp_all

lemma ed_rbt_del_from_right_simps[code]:
  "ed_rbt_del_from_right x a y s (RBT_Impl.Branch RBT_Impl.B lt z v rt) =
     balance_right a y s (ed_rbt_del x (RBT_Impl.Branch RBT_Impl.B lt z v rt))"
  "ed_rbt_del_from_right x a y s RBT_Impl.Empty =
     RBT_Impl.Branch RBT_Impl.R a y s (ed_rbt_del x RBT_Impl.Empty)"
  "ed_rbt_del_from_right x a y s (RBT_Impl.Branch RBT_Impl.R va vb vc vd) =
     RBT_Impl.Branch RBT_Impl.R a y s
       (ed_rbt_del x (RBT_Impl.Branch RBT_Impl.R va vb vc vd))"
  unfolding ed_rbt_del_def ed_rbt_del_from_right_def by simp_all

lemma ed_rbt_del_unfold[code_unfold]:
  "rbt_comp_del ed_comparator = ed_rbt_del"
  "rbt_comp_del_from_left ed_comparator = ed_rbt_del_from_left"
  "rbt_comp_del_from_right ed_comparator = ed_rbt_del_from_right"
  by (simp_all add: ed_rbt_del_def ed_rbt_del_from_left_def ed_rbt_del_from_right_def)

definition ed_rbt_delete :: "event_data tuple \<Rightarrow> (event_data tuple, 'v) rbt \<Rightarrow>
    (event_data tuple, 'v) rbt" where
  "ed_rbt_delete = rbt_comp_delete ed_comparator"

lemma ed_rbt_delete_code[code]: "ed_rbt_delete k t = paint RBT_Impl.B (ed_rbt_del k t)"
  by (simp add: ed_rbt_delete_def ed_rbt_del_def rbt_comp_delete_def)

lemma ed_rbt_delete_unfold[code_unfold]: "rbt_comp_delete ed_comparator = ed_rbt_delete"
  by (simp add: ed_rbt_delete_def)

(*<*)
end
(*>*)
