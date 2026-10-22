(*<*)
theory Agg_Gen
  imports Window Frame_Aux
begin
(*>*)



section \<open>The aggregation structure, over a bare element type\<close>

text \<open>
  The kernel keeps a fused aggregation's aggregate in @{typ aggaux}: a mapping from the group to
  a count, to a count and a sum, or to the sorted multiset of the values, for tuples of the
  kernel's wide frame (@{theory Monitor_Impl.Optimized_Agg}).  The executable window fed it the
  window's tuples widened by a slot for the result column, and the unboxed window widened its
  short tuples to the same frame, only for the kernel to cut the group back off them and compare
  it as a list of options.

  The structure below is the kernel's, restated over tuples @{typ "'b list"} of a bare element
  type and a group that is the tuple's suffix after the @{text k} bound columns -- @{typ
  "event_data option"} at the ascending frame, @{typ event_data} over the short tuples.  The value a
  tuple contributes is a parameter @{text ev}, and the result writes the aggregate into the group
  at position @{text p} through a parameter @{text ij}.  The steps are the kernel's, with the
  group and the value read through these; the folds are over lists, the sorted list of the table
  in use, where the kernel folds over the set.
\<close>

datatype 'b gagg = GCnt "('b list, nat) mapping" | GSum "('b list, nat \<times> integer) mapping"
  | GRank "('b list, list_aux) mapping" type

fun gi_cnt :: "nat \<Rightarrow> 'b list \<Rightarrow> bool \<times> ('b list, nat) mapping \<Rightarrow> bool \<times> ('b list, nat) mapping" where
  "gi_cnt k t (v, m) =
     (if v then (v, (let g = drop k t in case Mapping.lookup m g of
        Some i \<Rightarrow> Mapping.update g (i + 1) m | None \<Rightarrow> Mapping.update g 1 m))
      else (v, m))"

fun gd_cnt :: "nat \<Rightarrow> 'b list \<Rightarrow> bool \<times> ('b list, nat) mapping \<Rightarrow> bool \<times> ('b list, nat) mapping" where
  "gd_cnt k t (v, m) =
     (if v then (v, (let g = drop k t in case Mapping.lookup m g of
        Some i \<Rightarrow> (if i = 1 then Mapping.delete g m else Mapping.update g (i - 1) m)
      | None \<Rightarrow> m))
      else (v, m))"

fun gi_sum :: "nat \<Rightarrow> ('b list \<Rightarrow> event_data) \<Rightarrow> 'b list \<Rightarrow> bool \<times> ('b list, nat \<times> integer) mapping \<Rightarrow>
    bool \<times> ('b list, nat \<times> integer) mapping" where
  "gi_sum k ev t (v, m) =
     (if v then (let g = drop k t; e = ev t in
        case (Mapping.lookup m g, e) of
          (Some (cnt, s), EInt i) \<Rightarrow> (True, Mapping.update g (cnt + 1, s + i) m)
        | (None, EInt i) \<Rightarrow> (True, Mapping.update g (1, i) m)
        | _ \<Rightarrow> (False, Mapping.empty))
      else (v, m))"

fun gd_sum :: "nat \<Rightarrow> ('b list \<Rightarrow> event_data) \<Rightarrow> 'b list \<Rightarrow> bool \<times> ('b list, nat \<times> integer) mapping \<Rightarrow>
    bool \<times> ('b list, nat \<times> integer) mapping" where
  "gd_sum k ev t (v, m) =
     (if v then (let g = drop k t; e = ev t in
        case (Mapping.lookup m g, e) of
          (Some (cnt, s), EInt i) \<Rightarrow> (True, (if cnt = 1 then Mapping.delete g m
             else Mapping.update g (cnt - 1, s - i) m))
        | _ \<Rightarrow> (False, Mapping.empty))
      else (v, m))"

fun gi_rank :: "nat \<Rightarrow> ('b list \<Rightarrow> event_data) \<Rightarrow> type \<Rightarrow> 'b list \<Rightarrow> bool \<times> ('b list, list_aux) mapping \<Rightarrow>
    bool \<times> ('b list, list_aux) mapping" where
  "gi_rank k ev ty t (v, m) =
     (if v then (let g = drop k t; e = ev t;
        (v', l') = (case (Mapping.lookup m g, e, ty) of
            (Some (LInt s), EInt c, IntT) \<Rightarrow> (True, LInt (insert_treelist c s))
          | (Some (LString s), EString c, StringT) \<Rightarrow> (True, LString (insert_treelist c s))
          | (None, EInt c, IntT) \<Rightarrow> (True, LInt (insert_treelist c empty_treelist))
          | (None, EString c, StringT) \<Rightarrow> (True, LString (insert_treelist c empty_treelist))
          | _ \<Rightarrow> (False, LInt empty_treelist))
        in (v', (if v' then Mapping.update g l' m else Mapping.empty)))
      else (v, m))"

fun gd_rank :: "nat \<Rightarrow> ('b list \<Rightarrow> event_data) \<Rightarrow> type \<Rightarrow> 'b list \<Rightarrow> bool \<times> ('b list, list_aux) mapping \<Rightarrow>
    bool \<times> ('b list, list_aux) mapping" where
  "gd_rank k ev ty t (v, m) =
     (if v then (let g = drop k t; e = ev t;
        (v', m') = (case (Mapping.lookup m g, e, ty) of
            (Some (LString s), EString c, StringT) \<Rightarrow> (True, let l' = remove_treelist c s in
               if l' = empty_treelist then Mapping.delete g m else Mapping.update g (LString l') m)
          | (Some (LInt s), EInt c, IntT) \<Rightarrow> (True, let l' = remove_treelist c s in
               if l' = empty_treelist then Mapping.delete g m else Mapping.update g (LInt l') m)
          | (None, EString c, StringT) \<Rightarrow> (True, m)
          | (None, EInt c, IntT) \<Rightarrow> (True, m)
          | _ \<Rightarrow> (False, Mapping.empty))
        in (v', m'))
      else (v, m))"

text \<open>The structure is optional as in the kernel: an operation that cannot maintain it drops it,
  and the aggregate is then recomputed from the window.\<close>

definition ginit :: "ty Formula.agg_op \<Rightarrow> 'b gagg option" where
  "ginit \<omega> = (case (fst \<omega>, snd \<omega>) of
      (Formula.Agg_Cnt, _) \<Rightarrow> Some (GCnt Mapping.empty)
    | (Formula.Agg_Sum, TInt) \<Rightarrow> Some (GSum Mapping.empty)
    | (Formula.Agg_Min, TInt) \<Rightarrow> Some (GRank Mapping.empty IntT)
    | (Formula.Agg_Max, TInt) \<Rightarrow> Some (GRank Mapping.empty IntT)
    | (Formula.Agg_Avg, TInt) \<Rightarrow> Some (GSum Mapping.empty)
    | (Formula.Agg_Avg, TFloat) \<Rightarrow> Some (GSum Mapping.empty)
    | (Formula.Agg_Med, TFloat) \<Rightarrow> Some (GRank Mapping.empty IntT)
    | (Formula.Agg_Min, TString) \<Rightarrow> Some (GRank Mapping.empty StringT)
    | (Formula.Agg_Max, TString) \<Rightarrow> Some (GRank Mapping.empty StringT)
    | _ \<Rightarrow> None)"

definition gstep_ins :: "nat \<Rightarrow> ('b list \<Rightarrow> event_data) \<Rightarrow> 'b list \<Rightarrow> 'b gagg option \<Rightarrow> 'b gagg option"
  where
  "gstep_ins k ev t ax = (case ax of None \<Rightarrow> None
     | Some (GCnt m) \<Rightarrow> (case gi_cnt k t (True, m) of (v, m') \<Rightarrow> if v then Some (GCnt m') else None)
     | Some (GSum m) \<Rightarrow> (case gi_sum k ev t (True, m) of (v, m') \<Rightarrow> if v then Some (GSum m') else None)
     | Some (GRank m ty) \<Rightarrow> (case gi_rank k ev ty t (True, m) of (v, m') \<Rightarrow>
         if v then Some (GRank m' ty) else None))"

definition gstep_del :: "nat \<Rightarrow> ('b list \<Rightarrow> event_data) \<Rightarrow> 'b list \<Rightarrow> 'b gagg option \<Rightarrow> 'b gagg option"
  where
  "gstep_del k ev t ax = (case ax of None \<Rightarrow> None
     | Some (GCnt m) \<Rightarrow> (case gd_cnt k t (True, m) of (v, m') \<Rightarrow> if v then Some (GCnt m') else None)
     | Some (GSum m) \<Rightarrow> (case gd_sum k ev t (True, m) of (v, m') \<Rightarrow> if v then Some (GSum m') else None)
     | Some (GRank m ty) \<Rightarrow> (case gd_rank k ev ty t (True, m) of (v, m') \<Rightarrow>
         if v then Some (GRank m' ty) else None))"

definition gins :: "nat \<Rightarrow> ('b list \<Rightarrow> event_data) \<Rightarrow> 'b list list \<Rightarrow> 'b gagg option \<Rightarrow> 'b gagg option"
  where "gins k ev xs ax = fold (gstep_ins k ev) xs ax"

definition gdel :: "nat \<Rightarrow> ('b list \<Rightarrow> event_data) \<Rightarrow> 'b list list \<Rightarrow> 'b gagg option \<Rightarrow> 'b gagg option"
  where "gdel k ev xs ax = fold (gstep_del k ev) xs ax"

text \<open>The result writes the aggregate into the group at position @{text p}; with no group
  variables and nothing in the window it is the aggregate of the empty set alone.\<close>

definition gmr :: "nat \<Rightarrow> (event_data \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> event_data) \<Rightarrow> ('b list, 'a) mapping \<Rightarrow> 'b list set"
  where
  "gmr p ij f m = (\<lambda>g. case Mapping.lookup m g of
      Some i \<Rightarrow> take p g @ ij (f i) # drop p g | None \<Rightarrow> g) ` Mapping.keys m"

fun gres :: "bool \<Rightarrow> ty Formula.agg_op \<Rightarrow> nat \<Rightarrow> (event_data \<Rightarrow> 'b) \<Rightarrow> 'b gagg \<Rightarrow> 'b list set" where
  "gres g0 \<omega> p ij (GCnt m) = (if g0 \<and> Mapping.keys m = {} then {[ij (eval_agg_op \<omega> {})]}
     else gmr p ij (\<lambda>k. EInt (integer_of_int k)) m)"
| "gres g0 \<omega> p ij (GSum m) = (if g0 \<and> Mapping.keys m = {} then {[ij (eval_agg_op \<omega> {})]}
     else (case fst \<omega> of
       Formula.Agg_Sum \<Rightarrow> gmr p ij (\<lambda>k. EInt (snd k)) m
     | Formula.Agg_Avg \<Rightarrow> gmr p ij
         (\<lambda>k. EFloat (double_of_event_data (EInt (snd k)) / double_of_int (fst k))) m
     | _ \<Rightarrow> {}))"
| "gres g0 \<omega> p ij (GRank m ty) = (if g0 \<and> Mapping.keys m = {} then {[ij (eval_agg_op \<omega> {})]}
     else (case fst \<omega> of
       Formula.Agg_Min \<Rightarrow> gmr p ij (\<lambda>k. get_edata_list k 0) m
     | Formula.Agg_Max \<Rightarrow> gmr p ij (\<lambda>k. get_edata_list k (get_length k - 1)) m
     | Formula.Agg_Med \<Rightarrow> gmr p ij (\<lambda>k. let u = get_length k; u' = u div 2;
         aggval = (if even u
           then (double_of_event_data_agg (get_edata_list k (u' - 1))
                 + double_of_event_data_agg (get_edata_list k u')) / double_of_int 2
           else double_of_event_data_agg (get_edata_list k u'))
         in EFloat aggval) m
     | _ \<Rightarrow> {}))"

subsection \<open>Folds that drop the structure\<close>

fun gkeys :: "'b gagg \<Rightarrow> 'b list set" where
  "gkeys (GCnt m) = Mapping.keys m"
| "gkeys (GSum m) = Mapping.keys m"
| "gkeys (GRank m ty) = Mapping.keys m"

end
(*>*)
