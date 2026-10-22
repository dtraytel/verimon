theory Optimized_Agg
  imports "Monitor_Algorithm.Monitor"
  "Monitor_Data_Structures.Order_Statistic_Tree"
  "Monitor_Data_Structures.Tree_List"
begin


type_synonym 'a agg_map = "(event_data tuple, 'a) mapping"

datatype list_aux = LInt "integer treelist" | LString "string8 treelist"

datatype type = IntT | StringT

datatype aggaux = CntAux "nat agg_map" | 
                  SumAux "(nat \<times> integer) agg_map" | 
                  RankAux "list_aux agg_map \<times> type"

text \<open>The aggregated tuples are over the columns @{term cs}; a group is keyed by the columns
  that the aggregation does not bind (@{const agg_key}).\<close>

definition group where [simp]:
  "group k b cs X = Set.filter (\<lambda>x. agg_key b cs x = k) X"

definition group_multiset where [simp]:
  "group_multiset k b cs f X = (let group = group k b cs X in
                      (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm cs f x = y) group))) ` meval_trm cs f ` group)"

definition mset_conv where
  "mset_conv f s = Finite_Set.fold (\<lambda> (t, m) b. (case f t of 
                                                       Some k \<Rightarrow> (replicate_mset (the_enat m) k) + b |
                                                       _ \<Rightarrow> b)) {#} s"
definition unpack_int :: "event_data \<Rightarrow> integer option" where
  "unpack_int e = (case e of EInt i \<Rightarrow> Some i |
                            _ \<Rightarrow> None)"

definition unpack_string :: "event_data \<Rightarrow> string8 option" where
  "unpack_string e = (case e of EString s \<Rightarrow> Some s |
                            _ \<Rightarrow> None)"

definition int_mset_conv :: "(event_data \<times> enat) set  \<Rightarrow> integer multiset" where
  "int_mset_conv = mset_conv unpack_int"

definition str_mset_conv :: "(event_data \<times> enat) set  \<Rightarrow> string8 multiset" where
  "str_mset_conv = mset_conv unpack_string"

definition valid_aggmap :: "('a option \<Rightarrow> (event_data \<times> enat) set \<Rightarrow>  bool) \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> Formula.trm \<Rightarrow> (event_data tuple, 'a) mapping \<Rightarrow> event_data table \<Rightarrow> bool" where [simp]:
  "valid_aggmap P b cs f m X \<longleftrightarrow> (\<forall>k. k \<in> (agg_key b cs) ` X \<longleftrightarrow> k \<in> Mapping.keys m) \<and>
                    (\<forall>k. k \<in> Mapping.keys m \<longrightarrow> (let M = group_multiset k b cs f X
                    in P (Mapping.lookup m k) M))"

definition type_restr_mset :: "('a \<Rightarrow> event_data) \<Rightarrow> (event_data \<times> enat) set \<Rightarrow> bool" where
  "type_restr_mset f s = (\<forall>t m. (t, m) \<in> s \<longrightarrow> t \<in> range f)"

definition get_length :: "list_aux \<Rightarrow> nat" where
  "get_length l = (case l of LInt k \<Rightarrow> length_treelist k |
                             LString k \<Rightarrow> length_treelist k)"

definition valid_list_aux' :: "'a::linorder treelist \<Rightarrow> 'a multiset \<Rightarrow> bool" where
  "valid_list_aux' l m = (mset_treelist l = m)"

definition valid_list_aux :: "list_aux \<Rightarrow> (event_data \<times> enat) set \<Rightarrow> type \<Rightarrow> bool" where
  "valid_list_aux l s type = (case l of LInt k \<Rightarrow> valid_list_aux' k (int_mset_conv s) \<and> type_restr_mset EInt s \<and> (case type of IntT \<Rightarrow> True | _ \<Rightarrow> False)| 
                                  LString k \<Rightarrow> valid_list_aux' k (str_mset_conv s) \<and> type_restr_mset EString s \<and> (case type of StringT \<Rightarrow> True | _ \<Rightarrow> False))"

fun valid_maggaux :: "aggargs \<Rightarrow> aggaux \<Rightarrow> event_data table \<Rightarrow> bool" where
  "valid_maggaux \<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr> aux X = 
  (finite X \<and>
  (let aggtype = fst \<omega>;
       y0 = snd \<omega> in case aux of 
      CntAux m \<Rightarrow>
        (aggtype = Formula.Agg_Cnt) \<and> 
        (valid_aggmap (\<lambda>k s. 
                      k = Some(size (mset_conv Some s))) 
                      (length tys) cs f m X)
    | SumAux m \<Rightarrow> (aggtype = Formula.Agg_Sum \<or> aggtype = Formula.Agg_Avg) \<and>
                  (type_restr \<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr> X) \<and>
                  (valid_aggmap 
                  (\<lambda>k s. k = Some(size (int_mset_conv s), fold_mset (+) 0 (int_mset_conv s))) 
                  (length tys) cs f m X)
    | RankAux (m, type) \<Rightarrow> (aggtype = Formula.Agg_Min \<or> aggtype = Formula.Agg_Max \<or> aggtype = Formula.Agg_Med) \<and>
                   (case type of IntT \<Rightarrow> (meval_trm cs f ` X) \<subseteq> range EInt | 
                                 StringT \<Rightarrow> (meval_trm cs f ` X) \<subseteq> range EString) \<and>
                   valid_aggmap 
                   (\<lambda>k s. (case k of Some(l) \<Rightarrow> valid_list_aux l s type |
                                     None \<Rightarrow> False)) 
                   (length tys) cs f m X))"

text \<open>
  The second component of @{term "aggargs_\<omega> args"} is the aggregation's \<^emph>\<open>result\<close> type, not
  the type of the values it aggregates.  For @{const Formula.Agg_Min}, @{const Formula.Agg_Max}
  and @{const Formula.Agg_Sum} the two coincide, but @{const Formula.Agg_Avg} and
  @{const Formula.Agg_Med} always return a float, so they arrive here as @{const TFloat} whatever
  their values are, and admitting them on @{const TInt} admits nothing at all.  The value type is
  therefore not available at initialisation.  Both are admitted on the float result type instead,
  and the insertion rejects a non-integer value at the first tuple it meets, which drops the
  structure and falls back to the generic evaluation of the aggregation.  That fallback is what
  keeps this sound: addition of floats is not associative, so an incremental sum must never see
  one -- which is why the accumulator is an @{typ integer} and the insertion accepts
  @{const EInt} alone.
\<close>

fun init_maggaux :: "aggargs \<Rightarrow> (bool \<times> aggaux)" where
  "init_maggaux args = (let aggtype = fst (aggargs_\<omega> args);
       y0 = snd (aggargs_\<omega> args) in case (aggtype, y0) of
      (Formula.Agg_Cnt, _) \<Rightarrow> (True, CntAux Mapping.empty)
    | (Formula.Agg_Sum, TInt) \<Rightarrow> (True, SumAux Mapping.empty)
    | (Formula.Agg_Min, TInt) \<Rightarrow> (True, RankAux (Mapping.empty, IntT))
    | (Formula.Agg_Max, TInt) \<Rightarrow> (True, RankAux (Mapping.empty, IntT))
    | (Formula.Agg_Avg, TInt) \<Rightarrow> (True, SumAux Mapping.empty)
    | (Formula.Agg_Avg, TFloat) \<Rightarrow> (True, SumAux Mapping.empty)
    | (Formula.Agg_Med, TFloat) \<Rightarrow> (True, RankAux (Mapping.empty, IntT))
    | (Formula.Agg_Min, TString) \<Rightarrow> (True, RankAux (Mapping.empty, StringT))
    | (Formula.Agg_Max, TString) \<Rightarrow> (True, RankAux (Mapping.empty, StringT))
    | _ \<Rightarrow> (False, CntAux Mapping.empty))"

fun insert_cnt :: "aggargs \<Rightarrow>  event_data tuple \<Rightarrow> (bool \<times> nat agg_map) \<Rightarrow> (bool \<times> nat agg_map)" where
  "insert_cnt args t (v, m) = 
                (if v then (v, (let group = agg_key (length (aggargs_tys args)) (aggargs_cols args) t 
                          in case (Mapping.lookup m group) of
                            Some i \<Rightarrow> Mapping.update group (i + 1) m |
                            None \<Rightarrow> Mapping.update group 1 m))
                 else (v, m))"

fun insert_sum :: "aggargs \<Rightarrow> event_data tuple \<Rightarrow> (bool \<times> ((nat \<times> integer) agg_map)) \<Rightarrow> (bool \<times> ((nat \<times> integer) agg_map))" where
  "insert_sum args t (v, m) = 
              (if v then (let group = agg_key (length (aggargs_tys args)) (aggargs_cols args) t;
                              term = meval_trm (aggargs_cols args) (aggargs_f args) t
                          in case (Mapping.lookup m group, term) of
                            (Some (cnt, agg_sum), EInt i) \<Rightarrow> (True, Mapping.update group (cnt + 1, agg_sum + i) m) |
                            (None, EInt i) \<Rightarrow> (True, Mapping.update group (1, i) m) |
                            _ \<Rightarrow> (False, Mapping.empty)) 
               else (v, m))"

fun insert_rank :: "aggargs \<Rightarrow> type \<Rightarrow> event_data tuple \<Rightarrow> bool \<times> list_aux agg_map \<Rightarrow> bool \<times> list_aux agg_map" where
  "insert_rank args type t (v, m) = 
              (if v then (let group = agg_key (length (aggargs_tys args)) (aggargs_cols args) t;
                              term = meval_trm (aggargs_cols args) (aggargs_f args) t;
                              (new_v, new_list) = (case ((Mapping.lookup m group), term, type) of 
                                              (Some (LInt t'), EInt term', IntT) => (True, LInt (insert_treelist term' t')) |
                                              (Some (LString t'), EString term', StringT) \<Rightarrow> (True, LString (insert_treelist term' t')) |
                                              (None, EInt term', IntT) \<Rightarrow> (True, LInt (insert_treelist term' empty_treelist)) |
                                              (None, EString term', StringT) \<Rightarrow> (True, LString (insert_treelist term' empty_treelist)) |
                                              _ \<Rightarrow> (False, LInt empty_treelist))
                          in (new_v, (if new_v then Mapping.update group new_list m else Mapping.empty)))
               else (v, m))"

fun delete_cnt :: "aggargs \<Rightarrow> event_data tuple \<Rightarrow> (bool \<times> nat agg_map) \<Rightarrow> (bool \<times> nat agg_map)" where
  "delete_cnt args t (v, m) = 
                (if v then (v, (let group = agg_key (length (aggargs_tys args)) (aggargs_cols args) t
                       in case (Mapping.lookup m group) of
                         Some i \<Rightarrow> (if i = 1 then Mapping.delete group m 
                                    else Mapping.update group (i - 1) m)
                       | None \<Rightarrow> m))
                else (v, m))"

fun delete_sum :: "aggargs \<Rightarrow> event_data tuple \<Rightarrow> (bool \<times> ((nat \<times> integer) agg_map)) \<Rightarrow> (bool \<times> ((nat \<times> integer) agg_map))" where
  "delete_sum args t (v, m) = 
              (if v then (let group = agg_key (length (aggargs_tys args)) (aggargs_cols args) t;
                              term = meval_trm (aggargs_cols args) (aggargs_f args) t
                          in case (Mapping.lookup m group, term) of
                            (Some (cnt, agg_sum), EInt i) \<Rightarrow> (True, (if cnt = 1 then Mapping.delete group m
                                                    else Mapping.update group (cnt - 1, agg_sum - i) m)) |
                           _ \<Rightarrow> (False, Mapping.empty))
              else (v, m))"

fun delete_rank :: "aggargs \<Rightarrow> type \<Rightarrow> event_data tuple \<Rightarrow> bool \<times> list_aux agg_map \<Rightarrow> bool \<times> list_aux agg_map" where
  "delete_rank args type t (v, m) = 
              (if v then (let group = agg_key (length (aggargs_tys args)) (aggargs_cols args) t;
                              term = meval_trm (aggargs_cols args) (aggargs_f args) t;
                              (new_v, new_map) = (case (Mapping.lookup m group, term, type) of
                            (Some (LString t'), EString term', StringT) \<Rightarrow> (True, let l' = remove_treelist term' t' in if l' = empty_treelist then Mapping.delete group m else Mapping.update group (LString l') m) |
                            (Some (LInt t'), EInt term', IntT) \<Rightarrow> (True, let l' = remove_treelist term' t' in if l' = empty_treelist then Mapping.delete group m else Mapping.update group (LInt l') m) |
                            (None, EString term', StringT) \<Rightarrow> (True, m) |
                            (None, EInt term', IntT) \<Rightarrow> (True, m) |
                            _ \<Rightarrow> (False, Mapping.empty))
                          in (new_v, new_map)) 
              else (v, m))"

fun insert_maggaux :: "aggargs \<Rightarrow> event_data table \<Rightarrow> aggaux \<Rightarrow> bool \<times> aggaux" where
  "insert_maggaux args data aux = (case aux of
    CntAux m \<Rightarrow> let (v', m') = Finite_Set.fold (insert_cnt args) (True, m) data in (v', CntAux m')
  | SumAux m \<Rightarrow> let (v', m') = Finite_Set.fold (insert_sum args) (True, m) data in (v', SumAux m')
  | RankAux (m, t) \<Rightarrow> let (v', m') = Finite_Set.fold (insert_rank args t) (True, m) data in (v', RankAux (m', t)))"

fun delete_maggaux :: "aggargs \<Rightarrow> event_data table \<Rightarrow> aggaux \<Rightarrow> bool \<times> aggaux" where
  "delete_maggaux args data aux = (case aux of
    CntAux m \<Rightarrow> let (v', m') = Finite_Set.fold (delete_cnt args) (True, m) data in (v', CntAux m')
  | SumAux m \<Rightarrow> let (v', m') = Finite_Set.fold (delete_sum args) (True, m) data in (v', SumAux m')
  | RankAux (m, t) \<Rightarrow> let (v', m') = Finite_Set.fold (delete_rank args t) (True, m) data in (v', RankAux (m', t)))"

fun get_edata_list :: "list_aux \<Rightarrow> nat \<Rightarrow> event_data" where
  "get_edata_list (LString l) n = EString (get_treelist l n)" |
  "get_edata_list (LInt l) n = EInt (get_treelist l n)"

text \<open>Each group yields its aggregate followed by its key (cf. @{const eval_agg}).\<close>

definition get_map_result where
  "get_map_result m f = (\<lambda>k. (case Mapping.lookup m k of
                             Some i \<Rightarrow> f i # k
                           | None \<Rightarrow> k))` Mapping.keys m"

fun result_maggaux :: "aggargs \<Rightarrow> aggaux \<Rightarrow> event_data table" where
  "result_maggaux \<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr> aux = (case aux of
    CntAux m \<Rightarrow> 
    (if g0 \<and> Mapping.keys m = {} 
     then singleton_table (eval_agg_op \<omega> {})
     else get_map_result m (\<lambda>k. EInt (integer_of_int k))) |
    SumAux m \<Rightarrow> 
    (if g0 \<and> Mapping.keys m = {}
     then singleton_table (eval_agg_op \<omega> {})
     else (case fst \<omega> of 
     Formula.Agg_Sum \<Rightarrow> get_map_result m (\<lambda>k. EInt (snd k)) |
     Formula.Agg_Avg \<Rightarrow> get_map_result m (\<lambda>k. EFloat ((double_of_event_data (EInt (snd k)) / (double_of_int (fst k))))))) |
    RankAux (m, t) \<Rightarrow> 
    (if g0 \<and> Mapping.keys m = {}
     then singleton_table (eval_agg_op \<omega> {})
     else (case fst \<omega> of 
     Formula.Agg_Min \<Rightarrow> get_map_result m (\<lambda>k. get_edata_list k 0) |
     Formula.Agg_Max \<Rightarrow> get_map_result m (\<lambda>k. get_edata_list k (get_length k - 1)) |
     Formula.Agg_Med \<Rightarrow> get_map_result m (\<lambda>k. let u = get_length k;
                                  u' = u div 2;
                                  aggval = (if even u then (double_of_event_data_agg (get_edata_list k (u' - 1)) + double_of_event_data_agg (get_edata_list k u')) / double_of_int 2
                                            else double_of_event_data_agg (get_edata_list k u')) in
                                            EFloat aggval))))"

lemma insert_sum_comm': "(insert_sum args x \<circ> insert_sum args y) (v, m)  = (insert_sum args y \<circ> insert_sum args x) (v, m)"
  by (auto simp:lookup_update' mapping_eqI update_update split:option.splits event_data.splits)

lemma insert_sum_comm: "(insert_sum args x \<circ> insert_sum args y) aux  = (insert_sum args y \<circ> insert_sum args x) aux"
  using insert_sum_comm' by (cases aux) fastforce

lemma lookup_delete: "Mapping.lookup (Mapping.delete k m) k' = (if k = k' then None else Mapping.lookup m k')"
  by transfer auto

lemma delete_sum_comm': "(delete_sum args x \<circ> delete_sum args y) (v, m)  = (delete_sum args y \<circ> delete_sum args x) (v, m)"
  by(auto simp:lookup_update' delete_update lookup_delete update_update mapping_eqI cong:option.case_cong split:event_data.splits option.splits)

lemma delete_sum_comm: "(delete_sum args x \<circ> delete_sum args y) aux  = (delete_sum args y \<circ> delete_sum args x) aux"
  using delete_sum_comm' by (cases aux) fastforce

lemma insert_cnt_comm: "(insert_cnt args x \<circ> insert_cnt args y) (v, m)  = (insert_cnt args y \<circ> insert_cnt args x) (v, m)"
  by(auto; transfer; auto split:option.splits)

lemma delete_cnt_comm:  "(delete_cnt args x \<circ> delete_cnt args y) (v, aux)  = (delete_cnt args y \<circ> delete_cnt args x) (v, aux)"
   by(auto; transfer; auto split:option.splits)

lemma insert_rank_comm': "(insert_rank args type x  \<circ> insert_rank args type y) (v, m)  = (insert_rank args type y \<circ> insert_rank args type x) (v, m)"
proof (cases v)
  case True
  define gx gy where "gx = agg_key (length (aggargs_tys args)) (aggargs_cols args) x" and "gy = agg_key (length (aggargs_tys args)) (aggargs_cols args) y"
  show ?thesis
  proof (cases "gx = gy")
    case True
    \<comment> \<open>Both insertions act on the same list, where they commute.\<close>
    with \<open>v\<close> show ?thesis
      by (cases type; cases "meval_trm (aggargs_cols args) (aggargs_f args) x"; cases "meval_trm (aggargs_cols args) (aggargs_f args) y")
        (simp_all add: gx_def gy_def lookup_update' update_update insert_treelist_comm split: option.splits list_aux.splits)
  next
    case False
    \<comment> \<open>The insertions act on different keys of the mapping, where updates commute.\<close>
    with \<open>v\<close> show ?thesis
      by (cases type; cases "meval_trm (aggargs_cols args) (aggargs_f args) x"; cases "meval_trm (aggargs_cols args) (aggargs_f args) y")
        (simp_all add: gx_def gy_def lookup_update' update_update split: option.splits list_aux.splits)
  qed
qed simp

lemma delete_rank_comm': 
  shows "(delete_rank args type x \<circ> delete_rank args type y) (v, m) = (delete_rank args type y \<circ> delete_rank args type x) (v, m)"
proof (cases v)
  case True
  define gx gy where "gx = agg_key (length (aggargs_tys args)) (aggargs_cols args) x" and "gy = agg_key (length (aggargs_tys args)) (aggargs_cols args) y"
  show ?thesis
  proof (cases "gx = gy")
    case True
    \<comment> \<open>Both deletions act on the same list: removals commute, and a list that
      became empty stays empty under further removals.\<close>
    have remove_empty: "remove_treelist a empty_treelist = empty_treelist" for a :: "'a::linorder"
      by (rule remove_treelist_empty)
    have remove_remove_empty: "remove_treelist a (remove_treelist b l) = empty_treelist"
      if "remove_treelist a l = empty_treelist" for a b :: "'a::linorder" and l
      using that by (metis remove_comm remove_empty)
    from True \<open>v\<close> show ?thesis
      by (cases type; cases "meval_trm (aggargs_cols args) (aggargs_f args) x"; cases "meval_trm (aggargs_cols args) (aggargs_f args) y")
        (auto simp: gx_def gy_def lookup_update' lookup_delete delete_update update_update
          remove_comm remove_empty remove_remove_empty split: option.splits list_aux.splits)
  next
    case False
    \<comment> \<open>The deletions act on different keys of the mapping.\<close>
    with \<open>v\<close> show ?thesis
      by (cases type; cases "meval_trm (aggargs_cols args) (aggargs_f args) x"; cases "meval_trm (aggargs_cols args) (aggargs_f args) y")
        (auto simp: gx_def gy_def lookup_update' lookup_delete mapping_eqI delete_update update_update
          split: option.splits list_aux.splits)
  qed
qed simp
 
                     
lemma delete_rank_comm: 
  shows "(delete_rank args type x \<circ> delete_rank args type y) aux  = (delete_rank args type y \<circ> delete_rank args type x) aux"
  using delete_rank_comm' by (cases aux) fastforce

lemma insert_rank_comm: "(insert_rank args type x \<circ> insert_rank args type y) aux  = (insert_rank args type y \<circ> insert_rank args type x) aux"
  using insert_rank_comm' by (cases aux) fastforce

fun plus' :: "event_data \<Rightarrow> event_data \<Rightarrow> event_data" where
  "plus' (EInt x) (EInt y) = EInt (x + y)"
| "plus' (_::event_data)  _ = EFloat nan"

end
