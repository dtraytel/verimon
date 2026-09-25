(*<*)
theory Dense_Map_Upd
  imports Dense_Agg_Code
begin
(*>*)

section \<open>A mapping's lookup and update, in one descent\<close>

text \<open>
  The count set of a window and the aggregate's mapping from groups are updated tuple by tuple,
  and every update of an existing key is a lookup followed by an insertion: two descents of the
  same red-black tree, each comparing the key with the same nodes.  @{text mupd} is the pair of
  the two, and on a tree it is one descent (@{text rbt_comp_ins_lk}) that returns the old value
  and inserts the new one, which is computed from it.  For a new key the tree it builds is the one
  the insertion builds; for a present key it only replaces the value, as the tree's
  @{text map_entry} does, and skips the insertion's rebalancing on the way up.
\<close>

subsection \<open>On the trees\<close>

context
  fixes c :: "'a comparator"
begin

fun rbt_comp_ins_lk :: "('b option \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> ('a, 'b) rbt \<Rightarrow> 'b option \<times> ('a, 'b) rbt"
  where
  "rbt_comp_ins_lk F k RBT_Impl.Empty =
     (None, Branch RBT_Impl.R RBT_Impl.Empty k (F None) RBT_Impl.Empty)"
| "rbt_comp_ins_lk F k (Branch RBT_Impl.B l x y r) = (case c k x of
     Lt \<Rightarrow> (case rbt_comp_ins_lk F k l of (ov, l') \<Rightarrow>
       (ov, if Option.is_none ov then balance l' x y r else Branch RBT_Impl.B l' x y r))
   | Gt \<Rightarrow> (case rbt_comp_ins_lk F k r of (ov, r') \<Rightarrow>
       (ov, if Option.is_none ov then balance l x y r' else Branch RBT_Impl.B l x y r'))
   | Eq \<Rightarrow> (Some y, Branch RBT_Impl.B l x (F (Some y)) r))"
| "rbt_comp_ins_lk F k (Branch RBT_Impl.R l x y r) = (case c k x of
     Lt \<Rightarrow> (case rbt_comp_ins_lk F k l of (ov, l') \<Rightarrow> (ov, Branch RBT_Impl.R l' x y r))
   | Gt \<Rightarrow> (case rbt_comp_ins_lk F k r of (ov, r') \<Rightarrow> (ov, Branch RBT_Impl.R l x y r'))
   | Eq \<Rightarrow> (Some y, Branch RBT_Impl.R l x (F (Some y)) r))"

lemma fst_rbt_comp_ins_lk: "fst (rbt_comp_ins_lk F k t) = rbt_comp_lookup c t k"
  by (induct F k t rule: rbt_comp_ins_lk.induct) (auto split: order.splits prod.splits option.splits)

text \<open>A key not in the tree is inserted as by the insertion.  A key in it only has its value
  replaced, which is the tree's @{text map_entry}: the tree keeps its shape and its colours, and
  the rebalancing on the way up, which the insertion does in any case, is skipped.\<close>

lemma rbt_comp_ins_lk:
  "rbt_comp_ins_lk F k t = (rbt_comp_lookup c t k, case rbt_comp_lookup c t k of
     None \<Rightarrow> rbt_comp_ins c (\<lambda>_ _ nv. nv) k (F None) t
   | Some v \<Rightarrow> rbt_comp_map_entry c k (\<lambda>_. F (Some v)) t)"
proof (induct F k t rule: rbt_comp_ins_lk.induct)
  case (2 F k l x y r)
  then show ?case
    using fst_rbt_comp_ins_lk[of F k l] fst_rbt_comp_ins_lk[of F k r]
    by (auto split: order.splits prod.splits option.splits)
qed (auto split: order.splits prod.splits option.splits)

text \<open>The same descent, returning the new value as well, for a caller that reads it.\<close>

fun rbt_comp_ins_lk2 :: "('b option \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> ('a, 'b) rbt \<Rightarrow> 'b option \<times> 'b \<times> ('a, 'b) rbt"
  where
  "rbt_comp_ins_lk2 F k RBT_Impl.Empty =
     (let nv = F None in (None, nv, Branch RBT_Impl.R RBT_Impl.Empty k nv RBT_Impl.Empty))"
| "rbt_comp_ins_lk2 F k (Branch RBT_Impl.B l x y r) = (case c k x of
     Lt \<Rightarrow> (case rbt_comp_ins_lk2 F k l of (ov, nv, l') \<Rightarrow>
       (ov, nv, if Option.is_none ov then balance l' x y r else Branch RBT_Impl.B l' x y r))
   | Gt \<Rightarrow> (case rbt_comp_ins_lk2 F k r of (ov, nv, r') \<Rightarrow>
       (ov, nv, if Option.is_none ov then balance l x y r' else Branch RBT_Impl.B l x y r'))
   | Eq \<Rightarrow> (let nv = F (Some y) in (Some y, nv, Branch RBT_Impl.B l x nv r)))"
| "rbt_comp_ins_lk2 F k (Branch RBT_Impl.R l x y r) = (case c k x of
     Lt \<Rightarrow> (case rbt_comp_ins_lk2 F k l of (ov, nv, l') \<Rightarrow> (ov, nv, Branch RBT_Impl.R l' x y r))
   | Gt \<Rightarrow> (case rbt_comp_ins_lk2 F k r of (ov, nv, r') \<Rightarrow> (ov, nv, Branch RBT_Impl.R l x y r'))
   | Eq \<Rightarrow> (let nv = F (Some y) in (Some y, nv, Branch RBT_Impl.R l x nv r)))"

lemma rbt_comp_ins_lk2: "rbt_comp_ins_lk2 F k t =
    (case rbt_comp_ins_lk F k t of (ov, t') \<Rightarrow> (ov, F ov, t'))"
proof (induct F k t rule: rbt_comp_ins_lk2.induct)
  case (2 F k l x y r)
  then show ?case
    using fst_rbt_comp_ins_lk[of F k l] fst_rbt_comp_ins_lk[of F k r]
    by (auto simp: Let_def split: order.splits prod.splits option.splits)
qed (auto simp: Let_def split: order.splits prod.splits option.splits)

end

subsection \<open>On the lifted trees\<close>

lemma paint_rbt_comp_ins: "paint RBT_Impl.B (rbt_comp_ins c (\<lambda>_ _ nv. nv) k v t) = rbt_comp_insert c k v t"
  by (simp add: rbt_comp_insert_def rbt_comp_insert_with_key_def)

lemma is_rbt_rbt_comp_map_entry:
  "ID CCOMPARE('a :: ccompare) = Some c \<Longrightarrow> ord.is_rbt (lt_of_comp c) (t :: ('a, 'b) rbt) \<Longrightarrow>
    ord.is_rbt (lt_of_comp c) (rbt_comp_map_entry c k f t)"
  by (simp add: rbt_comp_map_entry[OF ID_ccompare'] ord.rbt_map_entry_is_rbt)

declare [[typedef_overloaded]]

lift_definition (code_dt) upd_lk :: "'a :: ccompare \<Rightarrow> ('b option \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) mapping_rbt \<Rightarrow>
    'b option \<times> ('a, 'b) mapping_rbt" is
  "\<lambda>k F t. case rbt_comp_ins_lk ccomp F k t of
     (None, t') \<Rightarrow> (None, paint RBT_Impl.B t') | (Some v, t') \<Rightarrow> (Some v, t')"
  unfolding rbt_comp_ins_lk prod.case
  by (auto 4 3 intro: linorder.rbt_insert_is_rbt ID_ccompare is_rbt_rbt_comp_map_entry
      simp: paint_rbt_comp_ins rbt_comp_insert[OF ID_ccompare'] split: option.splits)

lift_definition (code_dt) upd_lk2 :: "'a :: ccompare \<Rightarrow> ('b option \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) mapping_rbt \<Rightarrow>
    'b option \<times> 'b \<times> ('a, 'b) mapping_rbt" is
  "\<lambda>k F t. case rbt_comp_ins_lk2 ccomp F k t of
     (None, nv, t') \<Rightarrow> (None, nv, paint RBT_Impl.B t') | (Some v, nv, t') \<Rightarrow> (Some v, nv, t')"
  unfolding rbt_comp_ins_lk2 rbt_comp_ins_lk prod.case
  by (auto 4 3 intro: linorder.rbt_insert_is_rbt ID_ccompare is_rbt_rbt_comp_map_entry
      simp: paint_rbt_comp_ins rbt_comp_insert[OF ID_ccompare'] split: option.splits)

declare [[typedef_overloaded = false]]

lemma upd_lk2_eq: "upd_lk2 k F t = (case upd_lk k F t of (ov, t') \<Rightarrow> (ov, F ov, t'))"
  by transfer (simp add: rbt_comp_ins_lk2 split: prod.splits option.splits)

lemma upd_lk_eq: "upd_lk k F t = (RBT_Mapping2.lookup t k, case RBT_Mapping2.lookup t k of
    None \<Rightarrow> RBT_Mapping2.insert k (F None) t
  | Some v \<Rightarrow> RBT_Mapping2.map_entry k (\<lambda>_. F (Some v)) t)"
  by transfer (simp add: rbt_comp_ins_lk paint_rbt_comp_ins split: option.splits)

subsection \<open>On the mappings\<close>

definition mupd :: "'a \<Rightarrow> ('b option \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) mapping \<Rightarrow> 'b option \<times> ('a, 'b) mapping"
  where "mupd k F m = (Mapping.lookup m k, Mapping.update k (F (Mapping.lookup m k)) m)"

lemma mupd_code[code]:
  fixes t :: "('a :: ccompare, 'b) mapping_rbt"
  shows "mupd k F (RBT_Mapping t) = (case ID CCOMPARE('a) of
      None \<Rightarrow> Code.abort (STR ''mupd RBT_Mapping: ccompare = None'') (\<lambda>_. mupd k F (RBT_Mapping t))
    | Some _ \<Rightarrow> (case upd_lk k F t of (ov, t') \<Rightarrow> (ov, RBT_Mapping t')))"
    "mupd k F (Assoc_List_Mapping al) =
      (Mapping.lookup (Assoc_List_Mapping al) k,
       Mapping.update k (F (Mapping.lookup (Assoc_List_Mapping al) k)) (Assoc_List_Mapping al))"
    "mupd k F (Mapping f) = (Mapping.lookup (Mapping f) k, Mapping.update k (F (Mapping.lookup (Mapping f) k)) (Mapping f))"
  by (auto simp: mupd_def upd_lk_eq lookup_Mapping_code update_Mapping Mapping.lookup.abs_eq
      fun_eq_iff split: option.splits)

text \<open>The update that returns the new value too, computed once.\<close>

definition mupd2 :: "'a \<Rightarrow> ('b option \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) mapping \<Rightarrow> 'b option \<times> 'b \<times> ('a, 'b) mapping"
  where "mupd2 k F m = (case mupd k F m of (ov, m') \<Rightarrow> (ov, F ov, m'))"

lemma mupd2_code[code]:
  fixes t :: "('a :: ccompare, 'b) mapping_rbt"
  shows "mupd2 k F (RBT_Mapping t) = (case ID CCOMPARE('a) of
      None \<Rightarrow> Code.abort (STR ''mupd2 RBT_Mapping: ccompare = None'') (\<lambda>_. mupd2 k F (RBT_Mapping t))
    | Some _ \<Rightarrow> (case upd_lk2 k F t of (ov, nv, t') \<Rightarrow> (ov, nv, RBT_Mapping t')))"
    "mupd2 k F (Assoc_List_Mapping al) = (case mupd k F (Assoc_List_Mapping al) of (ov, m') \<Rightarrow> (ov, F ov, m'))"
    "mupd2 k F (Mapping f) = (case mupd k F (Mapping f) of (ov, m') \<Rightarrow> (ov, F ov, m'))"
proof -
  show "mupd2 k F (RBT_Mapping t) = (case ID CCOMPARE('a) of
      None \<Rightarrow> Code.abort (STR ''mupd2 RBT_Mapping: ccompare = None'') (\<lambda>_. mupd2 k F (RBT_Mapping t))
    | Some _ \<Rightarrow> (case upd_lk2 k F t of (ov, nv, t') \<Rightarrow> (ov, nv, RBT_Mapping t')))"
  proof (cases "ID CCOMPARE('a)")
    case (Some c)
    then show ?thesis
      unfolding mupd2_def by (subst mupd_code(1)) (auto simp: upd_lk2_eq split: prod.splits)
  qed simp
qed (simp_all add: mupd2_def)

subsection \<open>The updates of the count sets and of the aggregates\<close>

text \<open>Each of these reads a key's value and writes one computed from it; through @{const mupd}
  they do both in the one descent.  The code equations are proved against the definitions.\<close>

definition cnt_inc :: "nat option \<Rightarrow> nat" where
  "cnt_inc ov = (case ov of None \<Rightarrow> 1 | Some k \<Rightarrow> k + 1)"

lemma ucnt_add1_mupd[code]: "ucnt_add1 t c = snd (mupd t cnt_inc c)"
  by (simp add: ucnt_add1_def mupd_def cnt_inc_def split: option.splits)

lemma de_gcnt_add1_mupd[code]:
  "de_gcnt_add1 t cc = (case cc of (c, s) \<Rightarrow> (case mupd t cnt_inc c of
     (None, c') \<Rightarrow> (c', Set.insert t s) | (Some _, c') \<Rightarrow> (c', s)))"
  by (simp add: de_gcnt_add1_def gcnt_add1_def mupd_def cnt_inc_def split: option.splits prod.splits)

lemma cnt_ins_fold_mupd[code]:
  "cnt_ins_fold F xs c b = fold (\<lambda>t (c, acc). case mupd t cnt_inc c of
     (None, c') \<Rightarrow> (c', F t acc) | (Some _, c') \<Rightarrow> (c', acc)) xs (c, b)"
  unfolding cnt_ins_fold_def
  by (rule arg_cong[where f = "\<lambda>g. fold g xs (c, b)"])
    (auto simp: fun_eq_iff mupd_def cnt_inc_def split: option.splits)

lemma gi_cnt_mupd[code]:
  "gi_cnt k t (v, m) = (if v then (v, snd (mupd (drop k t) cnt_inc m)) else (v, m))"
  by (simp add: mupd_def cnt_inc_def split: option.splits)

lemma gi_sum_mupd[code]:
  "gi_sum k ev t (v, m) = (if v then (case ev t of
       EInt i \<Rightarrow> (True, snd (mupd (drop k t)
         (\<lambda>ov. case ov of None \<Rightarrow> (1, i) | Some (cnt, s) \<Rightarrow> (cnt + 1, s + i)) m))
     | _ \<Rightarrow> (False, Mapping.empty))
     else (v, m))"
  by (simp add: mupd_def Let_def split: option.splits event_data.splits)

lemma gi_rank_mupd[code]:
  "gi_rank k ev ty t (v, m) = (if v then (case (ev t, ty) of
       (EInt c, IntT) \<Rightarrow> (case mupd (drop k t) (\<lambda>ov. case ov of
            Some (LInt s) \<Rightarrow> LInt (insert_treelist c s)
          | _ \<Rightarrow> LInt (insert_treelist c empty_treelist)) m of
          (Some (LString _), _) \<Rightarrow> (False, Mapping.empty) | (_, m') \<Rightarrow> (True, m'))
     | (EString c, StringT) \<Rightarrow> (case mupd (drop k t) (\<lambda>ov. case ov of
            Some (LString s) \<Rightarrow> LString (insert_treelist c s)
          | _ \<Rightarrow> LString (insert_treelist c empty_treelist)) m of
          (Some (LInt _), _) \<Rightarrow> (False, Mapping.empty) | (_, m') \<Rightarrow> (True, m'))
     | _ \<Rightarrow> (False, Mapping.empty))
     else (v, m))"
  by (auto simp: mupd_def Let_def split: option.splits event_data.splits type.splits list_aux.splits)

text \<open>A deletion from a rank aggregate writes the shrunk multiset in the same descent, and
  descends again only to delete a group whose multiset became empty.\<close>

lemma gd_rank_mupd2[code]:
  "gd_rank k ev ty t (v, m) = (if v then (case (ev t, ty) of
       (EInt c, IntT) \<Rightarrow> (case mupd2 (drop k t) (\<lambda>ov. case ov of
            Some (LInt s) \<Rightarrow> LInt (remove_treelist c s) | _ \<Rightarrow> LInt empty_treelist) m of
          (Some (LInt _), nv, m') \<Rightarrow>
            (True, if nv = LInt empty_treelist then Mapping.delete (drop k t) m else m')
        | (Some (LString _), _, _) \<Rightarrow> (False, Mapping.empty) | (None, _, _) \<Rightarrow> (True, m))
     | (EString c, StringT) \<Rightarrow> (case mupd2 (drop k t) (\<lambda>ov. case ov of
            Some (LString s) \<Rightarrow> LString (remove_treelist c s) | _ \<Rightarrow> LString empty_treelist) m of
          (Some (LString _), nv, m') \<Rightarrow>
            (True, if nv = LString empty_treelist then Mapping.delete (drop k t) m else m')
        | (Some (LInt _), _, _) \<Rightarrow> (False, Mapping.empty) | (None, _, _) \<Rightarrow> (True, m))
     | _ \<Rightarrow> (False, Mapping.empty))
     else (v, m))"
  by (auto simp: mupd2_def mupd_def Let_def split: option.splits event_data.splits type.splits list_aux.splits)

subsection \<open>The tree union and difference at the short tuples' comparator\<close>

text \<open>The union and the difference of two trees fall back, on a small operand, to inserting
  or deleting its keys one by one, and they split the other tree at a key; both took the
  comparator as an argument and called it through a closure at every node.  These are their
  copies at the short tuples' comparator, with the specialised insertion, deletion and split.\<close>

definition edl_rbtc_split :: "(event_data list, 'v) rbt \<Rightarrow> event_data list \<Rightarrow>
    (event_data list, 'v) rbt \<times> 'v option \<times> (event_data list, 'v) rbt" where
  "edl_rbtc_split = rbt_split_comp edl_comparator"

lemma edl_rbtc_split_simps[code]:
  "edl_rbtc_split RBT_Impl.Empty k = (RBT_Impl.Empty, None, RBT_Impl.Empty)"
  "edl_rbtc_split (RBT_Impl.Branch cc l a b r) x = (case edl_comparator x a of
    Lt \<Rightarrow> (case edl_rbtc_split l x of (l1, \<beta>, l2) \<Rightarrow> (l1, \<beta>, rbt_join l2 a b r))
  | Gt \<Rightarrow> (case edl_rbtc_split r x of (r1, \<beta>, r2) \<Rightarrow> (rbt_join l a b r1, \<beta>, r2))
  | Eq \<Rightarrow> (l, Some b, r))"
  unfolding edl_rbtc_split_def by simp_all

lemma edl_rbtc_split_unfold[code_unfold]: "rbt_split_comp edl_comparator = edl_rbtc_split"
  by (simp add: edl_rbtc_split_def)

definition edl_rbtc_union_swap_rec :: "(event_data list \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow> bool \<Rightarrow>
    (event_data list, 'v) rbt \<Rightarrow> (event_data list, 'v) rbt \<Rightarrow> (event_data list, 'v) rbt" where
  "edl_rbtc_union_swap_rec = rbt_comp_union_swap_rec edl_comparator"

lemma edl_rbtc_union_swap_rec_code[code]: "edl_rbtc_union_swap_rec f \<gamma> t1 t2 = (let (\<gamma>, t2, t1) =
    if flip_rbt t2 t1 then (\<not>\<gamma>, t1, t2) else (\<gamma>, t2, t1);
    f' = (if \<gamma> then (\<lambda>k v v'. f k v' v) else f) in
    if small_rbt t2 then RBT_Impl.fold (edl_rbtc_insert_with_key f') t2 t1
    else case t1 of rbt.Empty \<Rightarrow> t2
      | Branch x l1 a b r1 \<Rightarrow>
        case edl_rbtc_split t2 a of (l2, \<beta>, r2) \<Rightarrow>
          rbt_join (edl_rbtc_union_swap_rec f \<gamma> l1 l2) a (case \<beta> of None \<Rightarrow> b | Some x \<Rightarrow> f' a b x)
            (edl_rbtc_union_swap_rec f \<gamma> r1 r2))"
  unfolding edl_rbtc_union_swap_rec_def edl_rbtc_insert_with_key_def edl_rbtc_split_def
  by (rule rbt_comp_union_swap_rec.simps)

definition edl_rbtc_union_with_key :: "(event_data list \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow>
    (event_data list, 'v) rbt \<Rightarrow> (event_data list, 'v) rbt \<Rightarrow> (event_data list, 'v) rbt" where
  "edl_rbtc_union_with_key = rbt_comp_union_with_key edl_comparator"

lemma edl_rbtc_union_with_key_code[code]:
  "edl_rbtc_union_with_key f t1 t2 = paint RBT_Impl.B (edl_rbtc_union_swap_rec f False t1 t2)"
  by (simp add: edl_rbtc_union_with_key_def edl_rbtc_union_swap_rec_def rbt_comp_union_with_key_def)

lemma edl_rbtc_union_with_key_unfold[code_unfold]:
  "rbt_comp_union_with_key edl_comparator = edl_rbtc_union_with_key"
  by (simp add: edl_rbtc_union_with_key_def)

definition edl_comp_minus :: "(event_data list, 'v) rbt \<Rightarrow> (event_data list, 'v) rbt \<Rightarrow>
    (event_data list, 'v) rbt" where
  "edl_comp_minus = comp_minus edl_comparator"

lemma edl_comp_minus_code[code]: "edl_comp_minus t1 t2 =
    (if small_rbt t2 then RBT_Impl.fold (\<lambda>k _ t. edl_rbtc_delete k t) t2 t1
     else if small_rbt t1 then rbtreeify (filter_comp_minus edl_comparator t1 t2)
     else case t2 of RBT_Impl.Empty \<Rightarrow> t1
       | RBT_Impl.Branch _ l2 a b r2 \<Rightarrow>
         case edl_rbtc_split t1 a of (l1, _, r1) \<Rightarrow>
           rbt_join2 (edl_comp_minus l1 l2) (edl_comp_minus r1 r2))"
  unfolding edl_comp_minus_def edl_rbtc_delete_def edl_rbtc_split_def
  by (rule comp_minus.simps)

definition edl_rbtc_minus :: "(event_data list, 'v) rbt \<Rightarrow> (event_data list, 'v) rbt \<Rightarrow>
    (event_data list, 'v) rbt" where
  "edl_rbtc_minus = rbt_comp_minus edl_comparator"

lemma edl_rbtc_minus_code[code]: "edl_rbtc_minus t1 t2 = paint RBT_Impl.B (edl_comp_minus t1 t2)"
  by (simp add: edl_rbtc_minus_def edl_comp_minus_def rbt_comp_minus_def)

lemma edl_rbtc_minus_unfold[code_unfold]: "rbt_comp_minus edl_comparator = edl_rbtc_minus"
  by (simp add: edl_rbtc_minus_def)

subsection \<open>The Since index's insertion\<close>

text \<open>A tuple entering the Since structure is added to the bucket of its key in the index:
  the bucket's lookup and the index's update are one descent through @{const mupd}.\<close>

lemma de_didx_add1_mupd[code]:
  "de_didx_add1 msk x i = (let k = dproj msk x in
     snd (mupd k (\<lambda>ov. Set.insert x (case ov of None \<Rightarrow> {} | Some z \<Rightarrow> z)) i))"
  by (simp add: de_didx_add1_def didx_add1_def dbucket_def mupd_def Let_def split: option.splits)

subsection \<open>The Until structure's time stamp maps\<close>

text \<open>The Until deque keeps, per time point, a mapping from the tuples to time stamps.  A
  tuple entering it updates its entry with a function of the old one -- a lookup and an update,
  one descent through @{const mupd}.  And the deletion of a set of keys from such a mapping, at the
  step, went through the generic deletion with the comparator built at every call; the Since
  structure's two value types got the specialised deletion by hand, and this is the third.\<close>

lemma de_gupd_nested_step_dq_mupd[code]:
  "de_gupd_nested_step_dq base d f x dq = (case x of (k, k') \<Rightarrow>
    if base \<le> k \<and> k - base < dq_len dq then
      (let i = k - base; m' = dq_nth_l dq i Mapping.empty in
       dq_upd dq i (snd (mupd k' (\<lambda>ov. case ov of Some v \<Rightarrow> f v | None \<Rightarrow> d) m')))
    else dq)"
  by (simp add: de_gupd_nested_step_dq_def gupd_nested_step_dq_def mupd_def Let_def
      split: option.splits prod.splits)

lemma de_mapping_delete_set_tstp_rbt[code]:
  "de_mapping_delete_set_tstp m (RBT_set rbt) = RBT_Set2.fold edl_delete_tstp rbt m"
  by (simp add: de_mapping_delete_set_tstp_def edl_delete_tstp_def mapping_delete_set_RBT_code
      ccompare_edl ID_ccompare_edl ccomp_edl ceq_edl ID_ceq_edl ID_def)

text \<open>For a positive left operand, the map from the tuples of the latest left table to the time
  point since which they hold is refreshed at every step: the tuples new to it get the current
  time point, and the others are dropped.  That is a filter, a set difference and an insertion per
  new tuple; on a tree it is the table's own tree with the values filled in by a lookup.\<close>

definition mrefresh :: "'v \<Rightarrow> 'k set \<Rightarrow> ('k, 'v) mapping \<Rightarrow> ('k, 'v) mapping" where
  "mrefresh v Y m = mfilter_keys True Y (upd_set m (\<lambda>_. v) (Y - Mapping.keys m))"

lemma lookup_mrefresh: "Mapping.lookup (mrefresh v Y m) k =
  (if k \<in> Y then Some (case Mapping.lookup m k of None \<Rightarrow> v | Some w \<Rightarrow> w) else None)"
  by (auto simp: mrefresh_def lookup_mfilter_keys Mapping_lookup_upd_set keys_is_none_rep
      split: option.splits)

lemma mrefresh_RBT_code[code]:
  fixes rbt :: "'k :: ccompare set_rbt"
  shows "mrefresh v (RBT_set rbt) m = (case ID CCOMPARE('k) of
      None \<Rightarrow> Code.abort (STR ''mrefresh: ccompare = None'') (\<lambda>_. mrefresh v (RBT_set rbt) m)
    | Some _ \<Rightarrow>
      RBT_Mapping (RBT_Mapping2.map (\<lambda>k _. case Mapping.lookup m k of None \<Rightarrow> v | Some w \<Rightarrow> w) rbt))"
proof (cases "ID CCOMPARE('k)")
  case (Some c)
  have u: "z \<noteq> Some () \<longleftrightarrow> z = None" for z :: "unit option"
    by (cases z) auto
  from Some show ?thesis
    by (intro mapping_eqI)
      (auto simp: lookup_mrefresh RBT_set_def RBT_Set2.member_lookup Mapping.lookup.abs_eq u
        split: option.splits)
qed simp

lemmas mrefresh_fallback_code[code] =
  mrefresh_def[of _ "DList_set _"] mrefresh_def[of _ "Set_Monad _"]
  mrefresh_def[of _ "Collect_set _"] mrefresh_def[of _ "Complement _"]

setup \<open>Monomorphize.monomorphize_cmd
  [("mrefresh", "de_mrefresh_nat", ["nat", "event_data list"])] ["edl_dict_simps"]\<close>

text \<open>A tuple of the right operand enters the deque's map at a time point only if the time
  stamp of that point lies in the interval's left end.  For an interval starting at 0, the common
  case, that is always so, and the test -- a walk of the time stamp deque to the point -- is
  dropped.\<close>

lemma de_gadd_new_dq_inz:
  "de_gadd_new_dq args msk rel1 rel2 nt aux =
    (let (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_dq, tstp_dq, dn) =
       de_gshift_dq args nt aux;
     I = args_ivl args; pos = args_pos args; inz = memL I 0;
     new_tstp = (if inz then Inr tp else Inl nt);
     tstp_dq = dq_push nt tstp_dq;
     P = (if inz then (\<lambda>_. True) else (\<lambda>t. memL I (nt - dq_nth_s tstp_dq (t - (tp - len)) 0)));
     (tbl, a2_dq') = fold (de_guntil_elem_step_dq a1_map msk pos tp len inz P new_tstp)
       (csl rel2) ({}, a2_dq);
     tables = append_queue (tbl, new_tstp) tables;
     a2_dq = dq_push Mapping.empty a2_dq';
     a1_map = (if pos then mrefresh tp rel1 a1_map else upd_set a1_map (\<lambda>_. tp) rel1);
     tss = append_queue nt tss in
     (tp + 1, tss, tables, len + 1, maskL, maskR, result, a1_map, a2_dq, tstp_dq, dn))"
proof -
  have "(\<lambda>t. memL (args_ivl args) (nt - dq_nth_s d (t - k) 0)) = (\<lambda>_. True)"
    if "memL (args_ivl args) 0" for d k
    using that by auto
  then show ?thesis
    unfolding de_gadd_new_dq_def gadd_new_dq_code de_gshift_dq_def de_guntil_elem_step_dq_def
      mrefresh_def[symmetric]
    by (simp add: Let_def split: prod.splits)
qed

text \<open>With the test dropped, every tuple of the right operand enters the new table, which is then
  the operand's table itself; the fold keeps only the deque.\<close>

definition guntil_a2_step :: "('b list, nat) mapping \<Rightarrow> bool list \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    ts + tp \<Rightarrow> 'b list \<Rightarrow> ('b list, ts + tp) mapping dq \<Rightarrow> ('b list, ts + tp) mapping dq" where
  "guntil_a2_step a1_map msk pos tp len d as a2 =
    (let a2' = gupd_nested_step_dq (tp - len) d (max_tstp d) (tp, as) a2 in
     case Mapping.lookup a1_map (dproj msk as) of
        None \<Rightarrow> (if \<not>pos then gupd_nested_step_dq (tp - len) d (max_tstp d) (tp - len, as) a2' else a2')
      | Some tp' \<Rightarrow> gupd_nested_step_dq (tp - len) d (max_tstp d) (if pos then (max (tp - len) tp', as)
          else (max (tp - len) (tp' + 1), as)) a2')"

lemma guntil_elem_step_dq_True:
  "guntil_elem_step_dq a1_map msk pos tp len True (\<lambda>_. True) d as (tbl, a2) =
    (Set.insert as tbl, guntil_a2_step a1_map msk pos tp len d as a2)"
  by (simp add: guntil_elem_step_dq_def guntil_step_dq_def guntil_a2_step_def Let_def
      split: option.splits)

lemma fold_guntil_elem_step_dq_True:
  "fold (guntil_elem_step_dq a1_map msk pos tp len True (\<lambda>_. True) d) xs (tbl, a2) =
    (tbl \<union> set xs, fold (guntil_a2_step a1_map msk pos tp len d) xs a2)"
  by (induction xs arbitrary: tbl a2) (simp_all add: guntil_elem_step_dq_True)

setup \<open>Monomorphize.monomorphize_cmd
  [("guntil_a2_step", "de_guntil_a2_step", ["event_data"])] ["edl_dict_simps"]\<close>

lemma de_gadd_new_dq_code[code]:
  "de_gadd_new_dq args msk rel1 rel2 nt aux =
    (let (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_dq, tstp_dq, dn) =
       de_gshift_dq args nt aux;
     I = args_ivl args; pos = args_pos args; inz = memL I 0;
     new_tstp = (if inz then Inr tp else Inl nt);
     tstp_dq = dq_push nt tstp_dq;
     (tbl, a2_dq') = (if inz
       then (if finite rel2 then rel2 else {},
             fold (de_guntil_a2_step a1_map msk pos tp len new_tstp) (csl rel2) a2_dq)
       else fold (de_guntil_elem_step_dq a1_map msk pos tp len inz
         (\<lambda>t. memL I (nt - dq_nth_s tstp_dq (t - (tp - len)) 0)) new_tstp) (csl rel2) ({}, a2_dq));
     tables = append_queue (tbl, new_tstp) tables;
     a2_dq = dq_push Mapping.empty a2_dq';
     a1_map = (if pos then mrefresh tp rel1 a1_map else upd_set a1_map (\<lambda>_. tp) rel1);
     tss = append_queue nt tss in
     (tp + 1, tss, tables, len + 1, maskL, maskR, result, a1_map, a2_dq, tstp_dq, dn))"
proof -
  have "set (csl rel2) = (if finite rel2 then rel2 else {})"
    by (simp add: set_csl_ed csl_infinite)
  then show ?thesis
    unfolding de_gadd_new_dq_inz de_guntil_a2_step_def de_guntil_elem_step_dq_def
    by (simp add: fold_guntil_elem_step_dq_True Let_def split: prod.splits)
qed

text \<open>At a step, the tuples of the tables leaving the window are deleted from the front map if
  their time stamp there has left it too.  The deletion went through the set of those tuples,
  built by a filter; a fold over the tables' tuples deletes them as it finds them.  The fold looks
  each tuple up in the map it has built so far, which is the original map at the tuples not yet
  seen, since they are distinct.\<close>

definition mdel_if :: "('v \<Rightarrow> bool) \<Rightarrow> 'k \<Rightarrow> ('k, 'v) mapping \<Rightarrow> ('k, 'v) mapping" where
  "mdel_if Q x m = (case Mapping.lookup m x of Some v \<Rightarrow> if Q v then Mapping.delete x m else m
     | None \<Rightarrow> m)"

lemma lookup_delete_if:
  "Mapping.lookup (Mapping.delete a m) k = (if a = k then None else Mapping.lookup m k)"
  by simp

lemma lookup_fold_mdel_if:
  "distinct xs \<Longrightarrow> Mapping.lookup (fold (mdel_if Q) xs m) k =
    (if k \<in> set xs \<and> (case Mapping.lookup m k of Some v \<Rightarrow> Q v | None \<Rightarrow> False) then None
     else Mapping.lookup m k)"
  by (induction xs arbitrary: m) (auto simp: mdel_if_def lookup_delete_if split: option.splits)

lemma fold_mdel_if:
  "distinct xs \<Longrightarrow> fold (mdel_if Q) xs m = mapping_delete_set m
    (Set.filter (\<lambda>x. case Mapping.lookup m x of Some v \<Rightarrow> Q v | None \<Rightarrow> False) (set xs))"
  by (rule mapping_eqI) (auto simp: lookup_fold_mdel_if delete_set_lookup split: option.splits)

setup \<open>Monomorphize.monomorphize_cmd
  [("mdel_if", "de_mdel_if_tstp", ["nat + nat", "event_data list"])] ["edl_dict_simps"]\<close>

lemma de_geval_step_dq_code[code]:
  "de_geval_step_dq args (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_dq, tstp_dq, dn) =
    (case safe_hd tss of (Some ts, tss') \<Rightarrow>
      (let m = dq_hd_s a2_dq Mapping.empty;
        I = args_ivl args;
        T = Mapping.keys m;
        tss' = tl_queue tss';
        (ts', tss'') = case safe_hd tss' of
              (Some ts', tss'') \<Rightarrow> (ts', tss'') |
              (None, tss'') \<Rightarrow> (0, tss'');
        (tables, taken) = takedropWhile_queue
           (\<lambda>(table, tstp). \<not> ts_tp_lt I ts' (tp - len + 1) tstp) tables;
        to_del_approx = \<Union>(set (map fst taken));
        m'' = (if finite to_del_approx
          then fold (mdel_if (\<lambda>tstp. \<not> ts_tp_lt I ts' (tp - len + 1) tstp)) (csl to_del_approx) m
          else mapping_delete_set m (Set.filter (\<lambda>x. case Mapping.lookup m x of
              Some tstp \<Rightarrow> (\<not> ts_tp_lt I ts' (tp - len + 1) tstp) | None \<Rightarrow> False) to_del_approx));
        a2_dq' = dq_tl a2_dq;
        m' = dq_hd_s a2_dq' Mapping.empty;
        a2_dq = dq_upd a2_dq' 0 (if len = 1 then Mapping.empty
          else Mapping.combine (\<lambda>tstp tstp'. max_tstp tstp tstp') m'' m');
        tstp_dq = dq_tl tstp_dq in
        (tp, tss'', tables, len - 1, maskL, maskR, result, a1_map, a2_dq, tstp_dq, T # dn)))"
proof -
  have eq: "(if finite X then fold (mdel_if Q) (csl X) m
      else mapping_delete_set m (Set.filter (\<lambda>x. case Mapping.lookup m x of
        Some tstp \<Rightarrow> Q tstp | None \<Rightarrow> False) X)) =
    mapping_delete_set m (Set.filter (\<lambda>x. case Mapping.lookup m x of
        Some tstp \<Rightarrow> Q tstp | None \<Rightarrow> False) X)"
    for Q and X :: "event_data list set" and m :: "(event_data list, nat + nat) mapping"
    using fold_mdel_if[OF distinct_csl_edl, of Q X m] set_csl_ed[of X] by simp
  show ?thesis
    unfolding de_geval_step_dq_def geval_step_dq.simps Let_def eq ..
qed

subsection \<open>A deletion that returns the deleted value\<close>

text \<open>The window's count set drops a tuple leaving it by a lookup, to learn its count, and then a
  deletion (or, for a count above one, an update): two descents.  @{text rbt_comp_del_lk} is the
  deletion returning the value it removed, in the deletion's one descent; the count above one,
  the rare case, then takes an update of the original tree.\<close>

context
  fixes c :: "'a comparator"
begin

fun rbt_comp_del_lk_from_left :: "'a \<Rightarrow> ('a, 'b) rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) rbt \<Rightarrow>
    'b option \<times> ('a, 'b) rbt" and
  rbt_comp_del_lk_from_right :: "'a \<Rightarrow> ('a, 'b) rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) rbt \<Rightarrow>
    'b option \<times> ('a, 'b) rbt" and
  rbt_comp_del_lk :: "'a \<Rightarrow> ('a, 'b) rbt \<Rightarrow> 'b option \<times> ('a, 'b) rbt"
where
  "rbt_comp_del_lk x RBT_Impl.Empty = (None, RBT_Impl.Empty)"
| "rbt_comp_del_lk x (Branch _ a y s b) = (case c x y of
     Lt \<Rightarrow> rbt_comp_del_lk_from_left x a y s b
   | Gt \<Rightarrow> rbt_comp_del_lk_from_right x a y s b
   | Eq \<Rightarrow> (Some s, RBT_Impl.combine a b))"
| "rbt_comp_del_lk_from_left x (Branch RBT_Impl.B lt z v rt) y s b =
     (case rbt_comp_del_lk x (Branch RBT_Impl.B lt z v rt) of (ov, l') \<Rightarrow> (ov, balance_left l' y s b))"
| "rbt_comp_del_lk_from_left x a y s b =
     (case rbt_comp_del_lk x a of (ov, a') \<Rightarrow> (ov, Branch RBT_Impl.R a' y s b))"
| "rbt_comp_del_lk_from_right x a y s (Branch RBT_Impl.B lt z v rt) =
     (case rbt_comp_del_lk x (Branch RBT_Impl.B lt z v rt) of (ov, r') \<Rightarrow> (ov, balance_right a y s r'))"
| "rbt_comp_del_lk_from_right x a y s b =
     (case rbt_comp_del_lk x b of (ov, b') \<Rightarrow> (ov, Branch RBT_Impl.R a y s b'))"

lemma rbt_comp_del_lk:
  fixes a b t :: "('a, 'b) rbt"
  shows "rbt_comp_del_lk_from_left x a y s b = (rbt_comp_lookup c a x, rbt_comp_del_from_left c x a y s b)"
  "rbt_comp_del_lk_from_right x a y s b = (rbt_comp_lookup c b x, rbt_comp_del_from_right c x a y s b)"
  "rbt_comp_del_lk x t = (rbt_comp_lookup c t x, rbt_comp_del c x t)"
  by (induct x a y s b and x a y s b and x t
      rule: rbt_comp_del_lk_from_left_rbt_comp_del_lk_from_right_rbt_comp_del_lk.induct)
    (auto split: order.splits prod.splits)

end

declare [[typedef_overloaded]]

lift_definition (code_dt) del_lk :: "'a :: ccompare \<Rightarrow> ('a, 'b) mapping_rbt \<Rightarrow>
    'b option \<times> ('a, 'b) mapping_rbt" is
  "\<lambda>k t. case rbt_comp_del_lk ccomp k t of (ov, t') \<Rightarrow> (ov, paint RBT_Impl.B t')"
  unfolding rbt_comp_del_lk prod.case rbt_comp_delete_def[symmetric]
  by (auto 4 3 intro: linorder.rbt_delete_is_rbt ID_ccompare simp: rbt_comp_delete[OF ID_ccompare'])

declare [[typedef_overloaded = false]]

lemma del_lk_eq: "del_lk k t = (RBT_Mapping2.lookup t k, RBT_Mapping2.delete k t)"
  by transfer (simp add: rbt_comp_del_lk rbt_comp_delete_def)

definition mdel_lk :: "'a \<Rightarrow> ('a, 'b) mapping \<Rightarrow> 'b option \<times> ('a, 'b) mapping"
  where "mdel_lk k m = (Mapping.lookup m k, Mapping.delete k m)"

lemma mdel_lk_code[code]:
  fixes t :: "('a :: ccompare, 'b) mapping_rbt"
  shows "mdel_lk k (RBT_Mapping t) = (case ID CCOMPARE('a) of
      None \<Rightarrow> Code.abort (STR ''mdel_lk RBT_Mapping: ccompare = None'') (\<lambda>_. mdel_lk k (RBT_Mapping t))
    | Some _ \<Rightarrow> (case del_lk k t of (ov, t') \<Rightarrow> (ov, RBT_Mapping t')))"
    "mdel_lk k (Assoc_List_Mapping al) =
      (Mapping.lookup (Assoc_List_Mapping al) k, Mapping.delete k (Assoc_List_Mapping al))"
    "mdel_lk k (Mapping f) = (Mapping.lookup (Mapping f) k, Mapping.delete k (Mapping f))"
  by (simp_all add: mdel_lk_def del_lk_eq lookup_Mapping_code delete_Mapping Mapping.lookup.abs_eq
      split: option.splits)

text \<open>The count sets' deletions through it.\<close>

lemma ucnt_del1_mdel_lk[code]: "ucnt_del1 t c = (case mdel_lk t c of
     (None, _) \<Rightarrow> c
   | (Some k, c') \<Rightarrow> (if k \<le> 1 then c' else Mapping.update t (k - 1) c))"
  by (simp add: ucnt_del1_def mdel_lk_def split: option.splits)

lemma de_gcnt_del1_mdel_lk[code]: "de_gcnt_del1 t cc = (case cc of (c, s) \<Rightarrow> (case mdel_lk t c of
     (None, _) \<Rightarrow> (c, s)
   | (Some k, c') \<Rightarrow> (if k \<le> 1 then (c', Set.remove t s) else (Mapping.update t (k - 1) c, s))))"
  by (simp add: de_gcnt_del1_def gcnt_del1_def mdel_lk_def split: option.splits prod.splits)

lemma cnt_del_fold_mdel_lk[code]:
  "cnt_del_fold F xs c b = fold (\<lambda>t (c, acc). case mdel_lk t c of
       (None, _) \<Rightarrow> (c, acc)
     | (Some k, c') \<Rightarrow> (if k \<le> 1 then (c', if k = 1 then F t acc else acc)
                        else (Mapping.update t (k - 1) c, acc))) xs (c, b)"
  unfolding cnt_del_fold_def
  by (rule arg_cong[where f = "\<lambda>g. fold g xs (c, b)"])
    (auto simp: fun_eq_iff mdel_lk_def split: option.splits)

text \<open>The aggregate's deletions: the group's entry, read and written in one descent by
  @{const mupd}, since a group usually outlives the tuple; the last tuple of a group then takes
  a deletion of the original mapping.\<close>

lemma gd_cnt_mupd[code]:
  "gd_cnt k t (v, m) = (if v then (v, case mupd (drop k t)
       (\<lambda>ov. case ov of Some i \<Rightarrow> i - 1 | None \<Rightarrow> 0) m of
       (Some i, m') \<Rightarrow> (if i = 1 then Mapping.delete (drop k t) m else m')
     | (None, _) \<Rightarrow> m)
     else (v, m))"
  by (simp add: mupd_def split: option.splits)

lemma gd_sum_mupd[code]:
  "gd_sum k ev t (v, m) = (if v then (case ev t of
       EInt i \<Rightarrow> (case mupd (drop k t)
         (\<lambda>ov. case ov of Some (cnt, s) \<Rightarrow> (cnt - 1, s - i) | None \<Rightarrow> (0, 0)) m of
           (Some (cnt, s), m') \<Rightarrow> (True, if cnt = 1 then Mapping.delete (drop k t) m else m')
         | (None, _) \<Rightarrow> (False, Mapping.empty))
     | _ \<Rightarrow> (False, Mapping.empty))
     else (v, m))"
  by (simp add: mupd_def Let_def split: option.splits event_data.splits prod.splits)

text \<open>The count set by group: a tuple's step descends the outer map once, reading and writing the
  group's entry, and the group's own map once; the group is deleted, in a second descent, only
  when its last tuple leaves.\<close>

lemma nis_empty_code[code]:
  fixes t :: "(event_data list, 'a \<times> ucnt) mapping_rbt"
  shows "nis_empty (RBT_Mapping t) = (case ID CCOMPARE(event_data list) of
      None \<Rightarrow> Code.abort (STR ''nis_empty RBT_Mapping: ccompare = None'') (\<lambda>_. nis_empty (RBT_Mapping t))
    | Some _ \<Rightarrow> RBT_Mapping2.is_empty t)"
    "nis_empty (Assoc_List_Mapping al) = (case DAList.impl_of al of [] \<Rightarrow> True | _ \<Rightarrow> False)"
proof -
  show "nis_empty (RBT_Mapping t) = (case ID CCOMPARE(event_data list) of
      None \<Rightarrow> Code.abort (STR ''nis_empty RBT_Mapping: ccompare = None'') (\<lambda>_. nis_empty (RBT_Mapping t))
    | Some _ \<Rightarrow> RBT_Mapping2.is_empty t)"
  proof (cases "ID CCOMPARE(event_data list)")
    case None
    then show ?thesis unfolding nis_empty_def by (simp only: option.case Code.abort_def)
  next
    case (Some c)
    then show ?thesis unfolding nis_empty_def using is_empty_Mapping(1)[of t] by (simp only: option.case)
  qed
  have "al = DAList.empty \<longleftrightarrow> DAList.impl_of al = []"
    by (metis DAList.empty.rep_eq DAList.impl_of_inject)
  then show "nis_empty (Assoc_List_Mapping al) = (case DAList.impl_of al of [] \<Rightarrow> True | _ \<Rightarrow> False)"
    unfolding nis_empty_def is_empty_Mapping(2) by (simp split: list.splits)
qed

lemma nins_mupd[code]: "nins k si su t M = snd (mupd (drop k t) (\<lambda>ov. case ov of
     None \<Rightarrow> (si t, Mapping.update t 1 Mapping.empty)
   | Some (a, I) \<Rightarrow> (case mupd t cnt_inc I of
       (None, I') \<Rightarrow> (su t a, I') | (Some _, I') \<Rightarrow> (a, I'))) M)"
  by (simp add: nins_def mupd_def cnt_inc_def Let_def split: option.splits prod.splits)

lemma ndel_mupd2[code]: "ndel k sd t M = (case mupd2 (drop k t) (\<lambda>ov. case ov of
     None \<Rightarrow> (undefined, Mapping.empty)
   | Some (a, I) \<Rightarrow> (case mdel_lk t I of
       (None, _) \<Rightarrow> (a, I)
     | (Some m, I') \<Rightarrow> (if m \<le> 1 then (sd t a, I') else (a, Mapping.update t (m - 1) I)))) M of
     (None, _, _) \<Rightarrow> M
   | (Some (a, I), (a', I'), M') \<Rightarrow>
       if Mapping.is_empty I' \<and> \<not> Mapping.is_empty I then Mapping.delete (drop k t) M else M')"
proof -
  have upd_same: "Mapping.update g v M = M" if "Mapping.lookup M g = Some v" for g v
    using that by (intro mapping_eqI) (auto simp: lookup_update')
  have ne: "\<not> Mapping.is_empty (Mapping.update t n I)" for n and I :: "(event_data list, nat) mapping"
    by (simp add: Mapping.is_empty_def)
  have e: "Mapping.lookup I t = None" if "Mapping.is_empty I" for I :: "(event_data list, nat) mapping"
    using that by (auto simp: Mapping.is_empty_def in_keys_lookup)
  show ?thesis
    by (auto simp: ndel_def mupd2_def mupd_def mdel_lk_def Let_def ne upd_same e
        split: option.splits prod.splits)
qed


subsection \<open>At the short tuples\<close>

definition edl_rbtc_ins_lk :: "('v option \<Rightarrow> 'v) \<Rightarrow> event_data list \<Rightarrow>
    (event_data list, 'v) rbt \<Rightarrow> 'v option \<times> (event_data list, 'v) rbt" where
  "edl_rbtc_ins_lk = rbt_comp_ins_lk edl_comparator"

lemmas edl_rbtc_ins_lk_simps[code] = rbt_comp_ins_lk.simps[of edl_comparator, folded edl_rbtc_ins_lk_def]

lemma edl_rbtc_ins_lk_unfold[code_unfold]: "rbt_comp_ins_lk edl_comparator = edl_rbtc_ins_lk"
  by (simp add: edl_rbtc_ins_lk_def)

definition edl_rbtc_ins_lk2 :: "('v option \<Rightarrow> 'v) \<Rightarrow> event_data list \<Rightarrow>
    (event_data list, 'v) rbt \<Rightarrow> 'v option \<times> 'v \<times> (event_data list, 'v) rbt" where
  "edl_rbtc_ins_lk2 = rbt_comp_ins_lk2 edl_comparator"

lemmas edl_rbtc_ins_lk2_simps[code] = rbt_comp_ins_lk2.simps[of edl_comparator, folded edl_rbtc_ins_lk2_def]

lemma edl_rbtc_ins_lk2_unfold[code_unfold]: "rbt_comp_ins_lk2 edl_comparator = edl_rbtc_ins_lk2"
  by (simp add: edl_rbtc_ins_lk2_def)

definition edl_rbtc_del_lk :: "event_data list \<Rightarrow> (event_data list, 'v) rbt \<Rightarrow>
    'v option \<times> (event_data list, 'v) rbt" where
  "edl_rbtc_del_lk = rbt_comp_del_lk edl_comparator"

definition edl_rbtc_del_lk_fl :: "event_data list \<Rightarrow> (event_data list, 'v) rbt \<Rightarrow> event_data list \<Rightarrow>
    'v \<Rightarrow> (event_data list, 'v) rbt \<Rightarrow> 'v option \<times> (event_data list, 'v) rbt" where
  "edl_rbtc_del_lk_fl = rbt_comp_del_lk_from_left edl_comparator"

definition edl_rbtc_del_lk_fr :: "event_data list \<Rightarrow> (event_data list, 'v) rbt \<Rightarrow> event_data list \<Rightarrow>
    'v \<Rightarrow> (event_data list, 'v) rbt \<Rightarrow> 'v option \<times> (event_data list, 'v) rbt" where
  "edl_rbtc_del_lk_fr = rbt_comp_del_lk_from_right edl_comparator"

lemmas edl_rbtc_del_lk_simps[code] =
  rbt_comp_del_lk.simps[of edl_comparator, folded edl_rbtc_del_lk_def edl_rbtc_del_lk_fl_def
    edl_rbtc_del_lk_fr_def]
  rbt_comp_del_lk_from_left.simps[of edl_comparator, folded edl_rbtc_del_lk_def edl_rbtc_del_lk_fl_def
    edl_rbtc_del_lk_fr_def]
  rbt_comp_del_lk_from_right.simps[of edl_comparator, folded edl_rbtc_del_lk_def edl_rbtc_del_lk_fl_def
    edl_rbtc_del_lk_fr_def]

lemma edl_rbtc_del_lk_unfold[code_unfold]: "rbt_comp_del_lk edl_comparator = edl_rbtc_del_lk"
  by (simp add: edl_rbtc_del_lk_def)

setup \<open>Monomorphize.monomorphize_cmd
  (maps (fn (tn, ty) =>
     [("Dense_Map_Upd.upd_lk_aux", "edl_upd_lk_aux_" ^ tn, [edl, ty]),
      ("upd_lk", "edl_upd_lk_" ^ tn, [edl, ty]), ("mupd", "edl_mupd_" ^ tn, [edl, ty]),
      ("Dense_Map_Upd.del_lk_aux", "edl_del_lk_aux_" ^ tn, [edl, ty]),
      ("del_lk", "edl_del_lk_" ^ tn, [edl, ty]), ("mdel_lk", "edl_mdel_lk_" ^ tn, [edl, ty])])
     edl_value_types)
  ["edl_dict_simps"]\<close>

setup \<open>Monomorphize.monomorphize_cmd
  (maps (fn (tn, ty) =>
     [("Dense_Map_Upd.upd_lk2_aux", "edl_upd_lk2_aux_" ^ tn, [edl, ty]),
      ("upd_lk2", "edl_upd_lk2_" ^ tn, [edl, ty]), ("mupd2", "edl_mupd2_" ^ tn, [edl, ty])])
     [("laux", "list_aux"), ("gcnt", "nat \<times> (event_data list, nat) mapping"),
      ("gsum", "(nat \<times> integer) \<times> (event_data list, nat) mapping")])
  ["edl_dict_simps"]\<close>

subsection \<open>The result's upkeep, with the steps applied\<close>

text \<open>The window's steps of @{theory MFODL_Monitor_Dense.Dense_Agg_Cache} pass the aggregate's
  step to @{const cstep} as an argument, where the redirection to its copy at the short tuples
  below does not reach it; these name the two instances with the step applied.\<close>

definition cstep_ins :: "uconstr option \<Rightarrow> daggp \<Rightarrow> event_data list \<Rightarrow>
    ugagg option \<times> event_data list set \<Rightarrow> ugagg option \<times> event_data list set" where
  "cstep_ins = cstep gstep_ins"

definition cstep_del :: "uconstr option \<Rightarrow> daggp \<Rightarrow> event_data list \<Rightarrow>
    ugagg option \<times> event_data list set \<Rightarrow> ugagg option \<times> event_data list set" where
  "cstep_del = cstep gstep_del"

text \<open>The table is updated with the group's value before and after the step.  Read off the
  mapping, these are two more descents per tuple; a rank aggregate's step returns both, the old
  multiset read and the new one written by its one descent.\<close>

definition rkval :: "ty Formula.agg_op \<Rightarrow> list_aux \<Rightarrow> event_data option" where
  "rkval \<omega> l = (case fst \<omega> of
       Formula.Agg_Min \<Rightarrow> Some (get_edata_list l 0)
     | Formula.Agg_Max \<Rightarrow> Some (get_edata_list l (get_length l - 1))
     | Formula.Agg_Med \<Rightarrow> Some (let u = get_length l; u' = u div 2;
         aggval = (if even u
           then (double_of_event_data_agg (get_edata_list l (u' - 1))
                 + double_of_event_data_agg (get_edata_list l u')) / double_of_int 2
           else double_of_event_data_agg (get_edata_list l u'))
         in EFloat aggval)
     | _ \<Rightarrow> None)"

lemma gval_GRank: "gval \<omega> (GRank m ty) g = (case Mapping.lookup m g of None \<Rightarrow> None | Some l \<Rightarrow> rkval \<omega> l)"
  by (cases "fst \<omega>") (simp_all add: rkval_def split: option.splits)

definition gstepv_ins :: "ty Formula.agg_op \<Rightarrow> nat \<Rightarrow> (event_data list \<Rightarrow> event_data) \<Rightarrow> event_data list \<Rightarrow>
    ugagg \<Rightarrow> (ugagg \<times> event_data option \<times> event_data option) option" where
  "gstepv_ins \<omega> k ev t a = map_option (\<lambda>a'. (a', gval \<omega> a (drop k t), gval \<omega> a' (drop k t)))
     (gstep_ins k ev t (Some a))"

definition gstepv_del :: "ty Formula.agg_op \<Rightarrow> nat \<Rightarrow> (event_data list \<Rightarrow> event_data) \<Rightarrow> event_data list \<Rightarrow>
    ugagg \<Rightarrow> (ugagg \<times> event_data option \<times> event_data option) option" where
  "gstepv_del \<omega> k ev t a = map_option (\<lambda>a'. (a', gval \<omega> a (drop k t), gval \<omega> a' (drop k t)))
     (gstep_del k ev t (Some a))"

lemma gstepv_ins_code[code]: "gstepv_ins \<omega> k ev t a = (case a of
    GRank m ty \<Rightarrow> (case (ev t, ty) of
       (EInt c, IntT) \<Rightarrow> (case mupd2 (drop k t) (\<lambda>ov. case ov of
            Some (LInt s) \<Rightarrow> LInt (insert_treelist c s)
          | _ \<Rightarrow> LInt (insert_treelist c empty_treelist)) m of
          (Some (LString _), _, _) \<Rightarrow> None
        | (ov, nv, m') \<Rightarrow> Some (GRank m' ty, case ov of None \<Rightarrow> None | Some l \<Rightarrow> rkval \<omega> l, rkval \<omega> nv))
     | (EString c, StringT) \<Rightarrow> (case mupd2 (drop k t) (\<lambda>ov. case ov of
            Some (LString s) \<Rightarrow> LString (insert_treelist c s)
          | _ \<Rightarrow> LString (insert_treelist c empty_treelist)) m of
          (Some (LInt _), _, _) \<Rightarrow> None
        | (ov, nv, m') \<Rightarrow> Some (GRank m' ty, case ov of None \<Rightarrow> None | Some l \<Rightarrow> rkval \<omega> l, rkval \<omega> nv))
     | _ \<Rightarrow> None)
  | _ \<Rightarrow> map_option (\<lambda>a'. (a', gval \<omega> a (drop k t), gval \<omega> a' (drop k t))) (gstep_ins k ev t (Some a)))"
  by (auto simp: gstepv_ins_def gstep_ins_def gval_GRank mupd2_def mupd_def Let_def
      simp del: gval.simps split: gagg.splits option.splits event_data.splits type.splits list_aux.splits)

lemma gstepv_del_code[code]: "gstepv_del \<omega> k ev t a = (case a of
    GRank m ty \<Rightarrow> (case (ev t, ty) of
       (EInt c, IntT) \<Rightarrow> (case mupd2 (drop k t) (\<lambda>ov. case ov of
            Some (LInt s) \<Rightarrow> LInt (remove_treelist c s) | _ \<Rightarrow> LInt empty_treelist) m of
          (Some (LInt s), nv, m') \<Rightarrow> (if nv = LInt empty_treelist
            then Some (GRank (Mapping.delete (drop k t) m) ty, rkval \<omega> (LInt s), None)
            else Some (GRank m' ty, rkval \<omega> (LInt s), rkval \<omega> nv))
        | (Some (LString _), _, _) \<Rightarrow> None | (None, _, _) \<Rightarrow> Some (a, None, None))
     | (EString c, StringT) \<Rightarrow> (case mupd2 (drop k t) (\<lambda>ov. case ov of
            Some (LString s) \<Rightarrow> LString (remove_treelist c s) | _ \<Rightarrow> LString empty_treelist) m of
          (Some (LString s), nv, m') \<Rightarrow> (if nv = LString empty_treelist
            then Some (GRank (Mapping.delete (drop k t) m) ty, rkval \<omega> (LString s), None)
            else Some (GRank m' ty, rkval \<omega> (LString s), rkval \<omega> nv))
        | (Some (LInt _), _, _) \<Rightarrow> None | (None, _, _) \<Rightarrow> Some (a, None, None))
     | _ \<Rightarrow> None)
  | _ \<Rightarrow> map_option (\<lambda>a'. (a', gval \<omega> a (drop k t), gval \<omega> a' (drop k t))) (gstep_del k ev t (Some a)))"
  by (auto simp: gstepv_del_def gstep_del_def gval_GRank mupd2_def mupd_def Let_def
      simp del: gval.simps split: gagg.splits option.splits event_data.splits type.splits list_aux.splits)

lemma cstep_ins_code[code]: "cstep_ins q p t axC = (case axC of (ax, C) \<Rightarrow> (case p of (g0, \<omega>, f, k, pos) \<Rightarrow>
     (case ax of None \<Rightarrow> (None, C)
      | Some a \<Rightarrow> (case gstepv_ins \<omega> k (umeval_trm f) t a of None \<Rightarrow> (None, C)
         | Some (a', ov, nv) \<Rightarrow> (Some a', cupd (uqok q) pos (drop k t) ov nv C)))))"
  by (simp add: cstep_ins_def cstep_def gstepv_ins_def split: option.splits prod.splits)

lemma cstep_del_code[code]: "cstep_del q p t axC = (case axC of (ax, C) \<Rightarrow> (case p of (g0, \<omega>, f, k, pos) \<Rightarrow>
     (case ax of None \<Rightarrow> (None, C)
      | Some a \<Rightarrow> (case gstepv_del \<omega> k (umeval_trm f) t a of None \<Rightarrow> (None, C)
         | Some (a', ov, nv) \<Rightarrow> (Some a', cupd (uqok q) pos (drop k t) ov nv C)))))"
  by (simp add: cstep_del_def cstep_def gstepv_del_def split: option.splits prod.splits)
text \<open>The result table of a structure built afresh is the aggregate's result, as the read
  computes it without the table.\<close>

declare gcache_ugres[code]

lemma cstep_ins_unfold[code_unfold]: "cstep gstep_ins = cstep_ins"
  by (simp add: cstep_ins_def)

lemma cstep_del_unfold[code_unfold]: "cstep gstep_del = cstep_del"
  by (simp add: cstep_del_def)

subsection \<open>The aggregate's result, with the guard read off the value\<close>

text \<open>The result of an aggregate writes each group's value into the group's tuple and keeps
  what passes the node's guard.  @{thm [source] ugmr_code} lists the mapping's entries first,
  builds every group's tuple by a @{const take}, an append and a @{const drop}, and evaluates the
  guard on the tuple.  Here the walk is the tree's own fold, the tuple is built in one pass
  (@{text ins_at}) and only for the groups that pass, and a guard's term that is the result
  column or a constant is read off the value without the tuple.\<close>

fun ins_at :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "ins_at 0 v g = v # g"
| "ins_at (Suc n) v [] = [v]"
| "ins_at (Suc n) v (x # xs) = x # ins_at n v xs"

lemma ins_at_eq: "ins_at p v g = take p g @ v # drop p g"
  by (induct p v g rule: ins_at.induct) simp_all

lemma ins_at_code[code]: "ins_at n v g = (if n = 0 then v # g
    else case g of [] \<Rightarrow> [v] | x # xs \<Rightarrow> x # ins_at (n - 1) v xs)"
  by (cases n; cases g) simp_all

definition tval :: "nat \<Rightarrow> event_data list \<Rightarrow> event_data \<Rightarrow> Formula.trm \<Rightarrow> event_data" where
  "tval p g v t = umeval_trm t (take p g @ v # drop p g)"

lemma tval_code[code]: "tval p g v t = (case t of
    Formula.Var i \<Rightarrow> (if i = p \<and> p \<le> length g then v else umeval_trm t (ins_at p v g))
  | Formula.Const c \<Rightarrow> c
  | _ \<Rightarrow> umeval_trm t (ins_at p v g))"
  by (cases t) (auto simp: tval_def ins_at_eq nth_append)

definition qval :: "uconstr option \<Rightarrow> nat \<Rightarrow> event_data list \<Rightarrow> event_data \<Rightarrow> bool" where
  "qval q p g v = uqok q (take p g @ v # drop p g)"

lemma qval_code[code]: "qval q p g v = (case q of None \<Rightarrow> True
    | Some (t1, b, mc, t2) \<Rightarrow> (eval_constraint0 mc (tval p g v t1) (tval p g v t2) = b))"
  by (simp add: qval_def uqok_def ueval_constraint_def tval_def split: option.splits prod.splits)

definition ugmr_q :: "uconstr option \<Rightarrow> nat \<Rightarrow> ('b \<Rightarrow> event_data) \<Rightarrow>
    (event_data list, 'b) mapping \<Rightarrow> event_data list set" where
  "ugmr_q q p f m = ugmr (uqok q) p f m"

lemma ugmr_q_code[code]:
  fixes t :: "(event_data list, 'b) mapping_rbt"
  shows "ugmr_q q p f (RBT_Mapping t) =
    (case ID CCOMPARE(event_data list) of
       None \<Rightarrow> Code.abort (STR ''ugmr_q RBT_Mapping: ccompare = None'')
                (\<lambda>_. ugmr_q q p f (RBT_Mapping t))
     | Some _ \<Rightarrow> RBT_Impl.fold (\<lambda>g a A. let v = f a
                    in if qval q p g v then Set.insert (ins_at p v g) A else A)
                  (mapping_rbt.impl_of t) {})"
proof (cases "ID CCOMPARE(event_data list)")
  case (Some c)
  have "ugmr_q q p f (RBT_Mapping t) = fold (\<lambda>e A. let v = take p (fst e) @ f (snd e) # drop p (fst e)
      in if uqok q v then Set.insert v A else A) (RBT_Mapping2.entries t) {}"
    using ugmr_code[of "uqok q" p f t] Some by (simp add: ugmr_q_def)
  also have "\<dots> = RBT_Impl.fold (\<lambda>g a A. let v = f a
      in if qval q p g v then Set.insert (ins_at p v g) A else A) (mapping_rbt.impl_of t) {}"
    unfolding ins_at_eq qval_def
    by (simp add: RBT_Impl.fold_def RBT_Mapping2.entries.rep_eq split_def Let_def)
  finally show ?thesis using Some by simp
qed simp

definition ugres_q :: "uconstr option \<Rightarrow> bool \<Rightarrow> ty Formula.agg_op \<Rightarrow> nat \<Rightarrow> ugagg \<Rightarrow>
    event_data list set" where
  "ugres_q q = ugres (uqok q)"

lemma ugmr_q_unfold[code_unfold]: "ugmr (uqok q) = ugmr_q q"
  by (simp add: ugmr_q_def fun_eq_iff)

lemmas ugres_q_code[code] = ugres_code[of "uqok q" for q, folded ugres_q_def]

lemma ugres_q_unfold[code_unfold]: "ugres (uqok q) = ugres_q q"
  by (simp add: ugres_q_def)

subsection \<open>The steps at the short tuples\<close>

text \<open>The steps of @{theory MFODL_Monitor_Dense.Dense_Agg_Gen} are generic in the element
  type, and their generated code built the comparator of the key lists at every lookup; these are
  their copies at @{typ event_data}, whose mapping operations the specialised ones take over.\<close>

setup \<open>Monomorphize.monomorphize_cmd
  [("gi_cnt", "edl_gi_cnt", ["event_data"]),
   ("gd_cnt", "edl_gd_cnt", ["event_data"]),
   ("gi_sum", "edl_gi_sum", ["event_data"]),
   ("gd_sum", "edl_gd_sum", ["event_data"]),
   ("gi_rank", "edl_gi_rank", ["event_data"]),
   ("gd_rank", "edl_gd_rank", ["event_data"]),
   ("gstep_ins", "edl_gstep_ins", ["event_data"]),
   ("gstep_del", "edl_gstep_del", ["event_data"]),
   ("gval", "edl_gval", ["event_data"]),
   ("gempty", "edl_gempty", ["event_data"])]
  ["edl_dict_simps"]\<close>

text \<open>The count set by group at its two value types, with the mapping operations above
  specialised; and a tuple's count read through its group, where the specialised lookup took
  the projection's place.\<close>

lemma edl_lookup_nflat[code_unfold]: "edl_lookup_nat (nflat k M) t = nlk k M t"
  by (simp add: edl_lookup_nat_def lookup_nflat_nlk)

setup \<open>Monomorphize.monomorphize_cmd
  (maps (fn (tn, ty) =>
     [("nins", "edl_nins_" ^ tn, [ty]), ("ndel", "edl_ndel_" ^ tn, [ty]),
      ("nlk", "edl_nlk_" ^ tn, [ty]), ("nis_empty", "edl_nis_empty_" ^ tn, [ty]),
      ("nflat_x", "edl_nflat_x_" ^ tn, [ty])])
     [("gcnt", "nat"), ("gsum", "nat \<times> integer")])
  ["edl_dict_simps"]\<close>

subsection \<open>MIN and MAX outside a window, in one pass\<close>

text \<open>The minimum and the maximum of a group need neither the multiset of its values nor an
  order-statistic tree: one pass over the table, keeping per group the extreme seen so far, has
  them.  @{text mm_step} folds one tuple into that mapping with one descent (@{const mupd}).\<close>

definition mm_step :: "('b list \<Rightarrow> 'c) \<Rightarrow> ('c \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> nat \<Rightarrow> 'b list \<Rightarrow>
    ('b list, 'c) mapping \<Rightarrow> ('b list, 'c) mapping" where
  "mm_step ev op k t m =
     snd (mupd (drop k t) (\<lambda>ov. case ov of None \<Rightarrow> ev t | Some u \<Rightarrow> op u (ev t)) m)"

definition mm_acc :: "('b list \<Rightarrow> 'c) \<Rightarrow> ('c \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> 'c option \<Rightarrow> 'b list \<Rightarrow> 'c option" where
  "mm_acc ev op ov t = Some (case ov of None \<Rightarrow> ev t | Some u \<Rightarrow> op u (ev t))"

lemma lookup_fold_mm_step:
  "Mapping.lookup (fold (mm_step ev op k) xs m) g
   = foldl (mm_acc ev op) (Mapping.lookup m g) (filter (\<lambda>t. drop k t = g) xs)"
  by (induct xs arbitrary: m) (simp_all add: mm_step_def mupd_def mm_acc_def lookup_update')

lemma foldl_mm_acc_Some: "foldl (mm_acc ev op) (Some u) ts = Some (foldl op u (map ev ts))"
  by (induct ts arbitrary: u) (simp_all add: mm_acc_def)

lemma keys_fold_mm_step: "Mapping.keys (fold (mm_step ev op k) xs m) = Mapping.keys m \<union> drop k ` set xs"
  by (induct xs arbitrary: m) (auto simp: mm_step_def mupd_def)

lemma foldl_max_Max: "foldl max u xs = Max (Set.insert u (set xs))" for u :: "'a :: linorder"
proof -
  have "foldl max u xs = fold max xs u"
    by (induct xs arbitrary: u) (simp_all add: max.commute)
  then show ?thesis
    by (simp add: Max.set_eq_fold[symmetric])
qed

lemma foldl_min_Min: "foldl min u xs = Min (Set.insert u (set xs))" for u :: "'a :: linorder"
proof -
  have "foldl min u xs = fold min xs u"
    by (induct xs arbitrary: u) (simp_all add: min.commute)
  then show ?thesis
    by (simp add: Min.set_eq_fold[symmetric])
qed

text \<open>The multiset of a finite, non-empty group's values lists each of its values at least once
  and nothing else, so its minimum and maximum are those of the values.\<close>

lemma set_csorted_list_of_set_mset:
  "finite (M :: (event_data \<times> enat) set) \<Longrightarrow> set (csorted_list_of_set M) = M"
proof -
  obtain c where c_def: "ID ccompare = Some (c :: (event_data \<times> enat) comparator)"
    by (simp add: ID_def ccompare_prod_def ccompare_event_data_def ccompare_enat_def
        split: if_splits option.splits)
  note c_class = comparator.linorder[OF ID_ccompare'[OF c_def]]
  assume "finite M"
  then show ?thesis
    using linorder.set_sorted_list_of_set[OF c_class] by (simp add: csorted_list_of_set_def c_def)
qed

lemma flatten_uagg_values:
  assumes "finite G" "G \<noteq> {}"
  shows "set (flatten_multiset (uagg_values f G)) = umeval_trm f ` G"
    and "finite_multiset (uagg_values f G)"
proof -
  let ?M = "uagg_values f G"
  let ?c = "\<lambda>v. card {x \<in> G. umeval_trm f x = v}"
  have M: "?M = (\<lambda>v. (v, enat (?c v))) ` umeval_trm f ` G"
    using assms(1) by (simp add: uagg_values ecard_def)
  have fM: "finite ?M"
    using assms(1) by (simp add: M)
  have pos: "0 < ?c (umeval_trm f x')" if "x' \<in> G" for x'
    using assms(1) that by (auto simp: card_gt_0_iff)
  have "set (flatten_multiset ?M) = {x. \<exists>c. (x, c) \<in> ?M \<and> the_enat c \<noteq> 0}"
    unfolding flatten_multiset_def set_concat set_map set_csorted_list_of_set_mset[OF fM]
    by (auto split: prod.splits)
  then show "set (flatten_multiset ?M) = umeval_trm f ` G"
    using pos by (auto simp: M image_iff)
  show "finite_multiset ?M"
    using fM by (auto simp: finite_multiset_def M)
qed

text \<open>The order on @{typ event_data} is total only within each kind of value, and not even there
  on floats; on integers, the fold over the flattened multiset is the extreme of the integers.\<close>

lemma foldl_max_ival: "\<forall>x \<in> set (u # xs). is_eint x \<Longrightarrow>
    foldl max u xs = EInt (foldl max (ival u) (map ival xs))"
  by (induct xs arbitrary: u) (auto simp: is_eint_def ival_def max_def split: event_data.splits)

lemma foldl_min_ival: "\<forall>x \<in> set (u # xs). is_eint x \<Longrightarrow>
    foldl min u xs = EInt (foldl min (ival u) (map ival xs))"
  by (induct xs arbitrary: u) (auto simp: is_eint_def ival_def min_def split: event_data.splits)

lemma eval_agg_op_uagg_values_Max_Min:
  assumes "finite G" "G \<noteq> {}" "\<forall>x \<in> G. is_eint (umeval_trm f x)"
  shows "eval_agg_op (Formula.Agg_Max, ty) (uagg_values f G) = EInt (Max (ival ` umeval_trm f ` G))"
    and "eval_agg_op (Formula.Agg_Min, ty) (uagg_values f G) = EInt (Min (ival ` umeval_trm f ` G))"
proof -
  note fl = flatten_uagg_values[OF assms(1,2), of f]
  obtain x xs where x: "flatten_multiset (uagg_values f G) = x # xs"
    using fl(1) assms(2) by (cases "flatten_multiset (uagg_values f G)") auto
  have s: "set (x # xs) = umeval_trm f ` G"
    using fl(1) x by simp
  then have i: "\<forall>y \<in> set (x # xs). is_eint y"
    using assms(3) by auto
  have "ival ` umeval_trm f ` G = Set.insert (ival x) (set (map ival xs))"
    using s by (metis image_insert list.set(2) set_map)
  then show "eval_agg_op (Formula.Agg_Max, ty) (uagg_values f G) = EInt (Max (ival ` umeval_trm f ` G))"
    and "eval_agg_op (Formula.Agg_Min, ty) (uagg_values f G) = EInt (Min (ival ` umeval_trm f ` G))"
    using fl x by (simp_all add: foldl_max_ival[OF i] foldl_min_ival[OF i] foldl_max_Max
        foldl_min_Min)
qed

text \<open>The fold computes, per group, the extreme of the integers of the group's tuples; the
  result table is read off the mapping as the window's is (@{const ugmr}).\<close>

definition uagg_mm :: "(integer \<Rightarrow> integer \<Rightarrow> integer) \<Rightarrow> Formula.trm \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    event_data list list \<Rightarrow> event_data list set" where
  "uagg_mm op f k pos xs = ugmr (\<lambda>_. True) pos EInt
     (fold (mm_step (\<lambda>t. ival (umeval_trm f t)) op k) xs Mapping.empty)"

lemma uagg_mm_gen:
  fixes F :: "integer set \<Rightarrow> integer"
  assumes fX: "finite X" and ne: "X \<noteq> {}" and i: "\<forall>x \<in> X. is_eint (umeval_trm f x)"
    and ev: "\<And>G. finite G \<Longrightarrow> G \<noteq> {} \<Longrightarrow> \<forall>x \<in> G. is_eint (umeval_trm f x) \<Longrightarrow>
      eval_agg_op \<omega> (uagg_values f G) = EInt (F (ival ` umeval_trm f ` G))"
    and op: "\<And>u xs. foldl op u xs = F (Set.insert u (set xs))"
  shows "uagg g0 \<omega> f k pos X = uagg_mm op f k pos (csl X)"
proof -
  let ?ev = "\<lambda>t. ival (umeval_trm f t)"
  let ?m = "fold (mm_step ?ev op k) (csl X) Mapping.empty"
  have s: "set (csl X) = X"
    by (rule set_csl_ed[OF fX])
  have keys: "Mapping.keys ?m = drop k ` X"
    by (simp add: keys_fold_mm_step s)
  have lk: "Mapping.lookup ?m g = Some (F (ival ` umeval_trm f ` Set.filter (\<lambda>x. drop k x = g) X))"
    if g: "g \<in> drop k ` X" for g
  proof -
    obtain t ts where tts: "filter (\<lambda>t. drop k t = g) (csl X) = t # ts"
      using g s by (cases "filter (\<lambda>t. drop k t = g) (csl X)") (auto simp: filter_empty_conv)
    have "set (t # ts) = Set.filter (\<lambda>x. drop k x = g) X"
      using tts[symmetric] s by auto
    then have "Set.insert (?ev t) (set (map ?ev ts)) = ival ` umeval_trm f ` Set.filter (\<lambda>x. drop k x = g) X"
      by (metis image_image image_insert list.set(2) set_map)
    then show ?thesis
      by (simp add: lookup_fold_mm_step tts mm_acc_def foldl_mm_acc_Some op)
  qed
  have evG: "eval_agg_op \<omega> (uagg_values f {a \<in> X. drop k a = drop k x})
      = EInt (F (ival ` umeval_trm f ` {a \<in> X. drop k a = drop k x}))" if "x \<in> X" for x
    using ev[of "{a \<in> X. drop k a = drop k x}"] fX i that by auto
  show ?thesis
    unfolding uagg_def uagg_mm_def ugmr_def gmr_def Let_def keys_cluster
    using ne by (auto simp: keys lk lookup_cluster_Some evG intro!: image_cong)
qed

lemma uagg_mm_Max_Min:
  assumes "finite X" "X \<noteq> {}" "\<forall>x \<in> X. is_eint (umeval_trm f x)"
  shows "uagg g0 (Formula.Agg_Max, ty) f k pos X = uagg_mm max f k pos (csl X)"
    and "uagg g0 (Formula.Agg_Min, ty) f k pos X = uagg_mm min f k pos (csl X)"
  by (rule uagg_mm_gen[OF assms eval_agg_op_uagg_values_Max_Min(1) foldl_max_Max]; assumption)
    (rule uagg_mm_gen[OF assms eval_agg_op_uagg_values_Max_Min(2) foldl_min_Min]; assumption)
text \<open>The code checks that the table is finite and not empty and that every value is an
  integer; otherwise it computes the aggregation as @{const uagg} is defined.  The other
  aggregations go through the window's structure (@{thm [source] uagg_g_code}).\<close>

definition uagg_mm_or :: "(integer \<Rightarrow> integer \<Rightarrow> integer) \<Rightarrow> bool \<Rightarrow> ty Formula.agg_op \<Rightarrow>
    Formula.trm \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> event_data list set \<Rightarrow> event_data list set" where
  "uagg_mm_or op g0 \<omega> f k pos X = (let xs = csl X in
     if xs \<noteq> [] \<and> list_all (\<lambda>t. is_eint (umeval_trm f t)) xs then uagg_mm op f k pos xs
     else uagg_gen g0 \<omega> f k pos X)"

lemma uagg_code[code]:
  "uagg g0 \<omega> f k pos X = (case fst \<omega> of
       Formula.Agg_Max \<Rightarrow> uagg_mm_or max g0 \<omega> f k pos X
     | Formula.Agg_Min \<Rightarrow> uagg_mm_or min g0 \<omega> f k pos X
     | _ \<Rightarrow> uagg_g g0 \<omega> f k pos X)"
proof -
  have pre: "finite X \<and> X \<noteq> {} \<and> (\<forall>x \<in> X. is_eint (umeval_trm f x))"
    if "csl X \<noteq> [] \<and> list_all (\<lambda>t. is_eint (umeval_trm f t)) (csl X)"
  proof -
    have fX: "finite X"
      using that csl_infinite by blast
    then show ?thesis
      using that set_csl_ed[OF fX] by (auto simp: list_all_iff)
  qed
  obtain a ty where \<omega>: "\<omega> = (a, ty)"
    by (cases \<omega>)
  let ?c = "csl X \<noteq> [] \<and> list_all (\<lambda>t. is_eint (umeval_trm f t)) (csl X)"
  show ?thesis
  proof (cases a)
    case Agg_Max
    show ?thesis
    proof (cases ?c)
      case True
      with pre[OF True] show ?thesis
        by (simp add: \<omega> Agg_Max uagg_mm_or_def uagg_mm_Max_Min(1))
    next
      case False
      then show ?thesis
        unfolding \<omega> Agg_Max uagg_mm_or_def Let_def
        by (simp only: fst_conv agg_type.case if_False uagg_gen_def)
    qed
  next
    case Agg_Min
    show ?thesis
    proof (cases ?c)
      case True
      with pre[OF True] show ?thesis
        by (simp add: \<omega> Agg_Min uagg_mm_or_def uagg_mm_Max_Min(2))
    next
      case False
      then show ?thesis
        unfolding \<omega> Agg_Min uagg_mm_or_def Let_def
        by (simp only: fst_conv agg_type.case if_False uagg_gen_def)
    qed
  qed (simp_all add: \<omega> uagg_g_def)
qed

(*<*)
end
(*>*)
