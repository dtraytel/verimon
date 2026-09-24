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
     Lt \<Rightarrow> (case rbt_comp_ins_lk F k l of
       (None, l') \<Rightarrow> (None, balance l' x y r) | (ov, l') \<Rightarrow> (ov, Branch RBT_Impl.B l' x y r))
   | Gt \<Rightarrow> (case rbt_comp_ins_lk F k r of
       (None, r') \<Rightarrow> (None, balance l x y r') | (ov, r') \<Rightarrow> (ov, Branch RBT_Impl.B l x y r'))
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

declare [[typedef_overloaded = false]]

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

subsection \<open>At the short tuples\<close>

definition edl_rbtc_ins_lk :: "('v option \<Rightarrow> 'v) \<Rightarrow> event_data list \<Rightarrow>
    (event_data list, 'v) rbt \<Rightarrow> 'v option \<times> (event_data list, 'v) rbt" where
  "edl_rbtc_ins_lk = rbt_comp_ins_lk edl_comparator"

lemmas edl_rbtc_ins_lk_simps[code] = rbt_comp_ins_lk.simps[of edl_comparator, folded edl_rbtc_ins_lk_def]

lemma edl_rbtc_ins_lk_unfold[code_unfold]: "rbt_comp_ins_lk edl_comparator = edl_rbtc_ins_lk"
  by (simp add: edl_rbtc_ins_lk_def)

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

(*<*)
end
(*>*)
