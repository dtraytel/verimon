(*<*)
theory Dense_Map_Upd
  imports Dense_Agg_Upkeep
begin
(*>*)

section \<open>A mapping's lookup and update, in one descent\<close>

text \<open>
  The count set of a window and the aggregate's mapping from groups are updated tuple by tuple,
  and every update of an existing key is a lookup followed by an insertion: two descents of the
  same red-black tree, each comparing the key with the same nodes.  @{text mupd} is the pair of
  the two, and on a tree it is one descent (@{text rbt_comp_ins_lk}) that returns the old value
  and inserts the new one, which is computed from it.  The tree it builds is the one the
  insertion builds, so the operation is proved against the two it replaces with no invariant.
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
     Lt \<Rightarrow> (case rbt_comp_ins_lk F k l of (ov, l') \<Rightarrow> (ov, balance l' x y r))
   | Gt \<Rightarrow> (case rbt_comp_ins_lk F k r of (ov, r') \<Rightarrow> (ov, balance l x y r'))
   | Eq \<Rightarrow> (Some y, Branch RBT_Impl.B l x (F (Some y)) r))"
| "rbt_comp_ins_lk F k (Branch RBT_Impl.R l x y r) = (case c k x of
     Lt \<Rightarrow> (case rbt_comp_ins_lk F k l of (ov, l') \<Rightarrow> (ov, Branch RBT_Impl.R l' x y r))
   | Gt \<Rightarrow> (case rbt_comp_ins_lk F k r of (ov, r') \<Rightarrow> (ov, Branch RBT_Impl.R l x y r'))
   | Eq \<Rightarrow> (Some y, Branch RBT_Impl.R l x (F (Some y)) r))"

lemma rbt_comp_ins_lk:
  "rbt_comp_ins_lk F k t =
    (rbt_comp_lookup c t k, rbt_comp_ins c (\<lambda>_ _ nv. nv) k (F (rbt_comp_lookup c t k)) t)"
  by (induct F k t rule: rbt_comp_ins_lk.induct) (auto split: order.splits prod.splits)

end

subsection \<open>On the lifted trees\<close>

lemma paint_rbt_comp_ins: "paint RBT_Impl.B (rbt_comp_ins c (\<lambda>_ _ nv. nv) k v t) = rbt_comp_insert c k v t"
  by (simp add: rbt_comp_insert_def rbt_comp_insert_with_key_def)

declare [[typedef_overloaded]]

lift_definition (code_dt) upd_lk :: "'a :: ccompare \<Rightarrow> ('b option \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) mapping_rbt \<Rightarrow>
    'b option \<times> ('a, 'b) mapping_rbt" is
  "\<lambda>k F t. case rbt_comp_ins_lk ccomp F k t of (ov, t') \<Rightarrow> (ov, paint RBT_Impl.B t')"
  unfolding rbt_comp_ins_lk prod.case paint_rbt_comp_ins
  by (auto 4 3 intro: linorder.rbt_insert_is_rbt ID_ccompare simp: rbt_comp_insert[OF ID_ccompare'])

declare [[typedef_overloaded = false]]

lemma upd_lk_eq: "upd_lk k F t =
    (RBT_Mapping2.lookup t k, RBT_Mapping2.insert k (F (RBT_Mapping2.lookup t k)) t)"
  by transfer (simp add: rbt_comp_ins_lk paint_rbt_comp_ins)

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
  by (simp_all add: mupd_def upd_lk_eq lookup_Mapping_code update_Mapping Mapping.lookup.abs_eq
      split: option.splits)

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

subsection \<open>At the short tuples\<close>

definition edl_rbtc_ins_lk :: "('v option \<Rightarrow> 'v) \<Rightarrow> event_data list \<Rightarrow>
    (event_data list, 'v) rbt \<Rightarrow> 'v option \<times> (event_data list, 'v) rbt" where
  "edl_rbtc_ins_lk = rbt_comp_ins_lk edl_comparator"

lemma edl_rbtc_ins_lk_simps[code]:
  "edl_rbtc_ins_lk F k RBT_Impl.Empty =
     (None, Branch RBT_Impl.R RBT_Impl.Empty k (F None) RBT_Impl.Empty)"
  "edl_rbtc_ins_lk F k (Branch RBT_Impl.B l x y r) = (case edl_comparator k x of
     Lt \<Rightarrow> (case edl_rbtc_ins_lk F k l of (ov, l') \<Rightarrow> (ov, balance l' x y r))
   | Gt \<Rightarrow> (case edl_rbtc_ins_lk F k r of (ov, r') \<Rightarrow> (ov, balance l x y r'))
   | Eq \<Rightarrow> (Some y, Branch RBT_Impl.B l x (F (Some y)) r))"
  "edl_rbtc_ins_lk F k (Branch RBT_Impl.R l x y r) = (case edl_comparator k x of
     Lt \<Rightarrow> (case edl_rbtc_ins_lk F k l of (ov, l') \<Rightarrow> (ov, Branch RBT_Impl.R l' x y r))
   | Gt \<Rightarrow> (case edl_rbtc_ins_lk F k r of (ov, r') \<Rightarrow> (ov, Branch RBT_Impl.R l x y r'))
   | Eq \<Rightarrow> (Some y, Branch RBT_Impl.R l x (F (Some y)) r))"
  unfolding edl_rbtc_ins_lk_def by simp_all

lemma edl_rbtc_ins_lk_unfold[code_unfold]: "rbt_comp_ins_lk edl_comparator = edl_rbtc_ins_lk"
  by (simp add: edl_rbtc_ins_lk_def)

setup \<open>Monomorphize.monomorphize_cmd
  (maps (fn (tn, ty) =>
     [("Dense_Map_Upd.upd_lk_aux", "edl_upd_lk_aux_" ^ tn, [edl, ty]),
      ("upd_lk", "edl_upd_lk_" ^ tn, [edl, ty]), ("mupd", "edl_mupd_" ^ tn, [edl, ty])])
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
   ("gstep_del", "edl_gstep_del", ["event_data"])]
  ["edl_dict_simps"]\<close>

(*<*)
end
(*>*)
