theory Optimized_Agg_Temporal
  imports 
    Optimized_Agg
    Optimized_Since
    Optimized_Until
begin

section \<open>Aggregation in Since and Until\<close>

subsection \<open>Since with aggregation\<close>

type_synonym mmasaux = "event_data mmsaux \<times> aggaux option"

fun init_maggaux' where
  "init_maggaux' args = (let (v', aux') = init_maggaux args in
                        if v' then Some aux' else None)"

fun insert_maggaux' :: "aggargs \<Rightarrow> event_data table \<Rightarrow> aggaux option \<Rightarrow> aggaux option" where
  "insert_maggaux' args X None = None" |
  "insert_maggaux' args X (Some aux) = (let (v', aux') = insert_maggaux args X aux in
                                       if v' \<and> finite X then Some aux' else None)"

fun delete_maggaux' :: "aggargs \<Rightarrow> event_data table \<Rightarrow> aggaux option \<Rightarrow> aggaux option" where
  "delete_maggaux' args X None = None" |
  "delete_maggaux' args X (Some aux) = (let (v', aux') = delete_maggaux args X aux in
                                       if v' then Some aux' else None)"

fun result_maggaux' :: "aggargs \<Rightarrow> aggaux option \<Rightarrow> event_data table option" where
  "result_maggaux' args None = None" |
  "result_maggaux' args (Some aux) = Some (result_maggaux args aux)"

fun valid_maggaux' :: "aggargs \<Rightarrow> aggaux option \<Rightarrow> event_data table \<Rightarrow> bool" where
  "valid_maggaux' args None X = True" |
  "valid_maggaux' args (Some aux) X = valid_maggaux args aux X"

fun valid_mmasaux :: "args \<Rightarrow> ts \<Rightarrow> mmasaux \<Rightarrow> event_data Monitor.msaux \<Rightarrow> bool" where
  "valid_mmasaux args cur ((nt, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since), aggaux) ys =
   (valid_mmsaux args cur (nt, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) ys \<and>
    (case args_agg args of
      Some aggargs \<Rightarrow> valid_maggaux' aggargs aggaux table_in |
      None \<Rightarrow> True))"

fun init_mmasaux :: "args \<Rightarrow> mmasaux" where
  "init_mmasaux args =  (case args_agg args of
      Some aggargs \<Rightarrow> (init_mmsaux args, init_maggaux' aggargs) |
      None \<Rightarrow> (init_mmsaux args, None))"

fun add_new_table_mmasaux :: "args \<Rightarrow> event_data table \<Rightarrow> mmasaux \<Rightarrow> mmasaux" where
  "add_new_table_mmasaux args X ((nt, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since), aggaux) = 
    (let msaux' = add_new_table_mmsaux args X (nt, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) in
    (case args_agg args of 
      None \<Rightarrow> (msaux', aggaux) |
      Some aggargs \<Rightarrow> (msaux', if (memL (args_ivl args) 0) 
                                      then insert_maggaux' aggargs (X - Mapping.keys tuple_in) aggaux
                                      else aggaux)))" 

fun join_mmasaux :: "args \<Rightarrow> event_data table \<Rightarrow> mmasaux \<Rightarrow> mmasaux" where
  "join_mmasaux args X ((t, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since), aggaux) =
    (case args_agg args of 
      None \<Rightarrow> (join_mmsaux args X (t, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since), aggaux) |
      Some aggargs \<Rightarrow> (let pos = args_pos args in
        (if args_L args = [] then
          (let take_all = (pos \<longleftrightarrow> [] \<in> X);
          table_in' = (if take_all then table_in else {});
          wf_table_in' = (if take_all then wf_table_in else wf_table_of_set_args args {});
          tuple_in' = (if take_all then tuple_in else Mapping.empty);
          aggaux' = (if take_all then aggaux else init_maggaux' aggargs);
          wf_table_since' = (if take_all then wf_table_since else wf_table_of_set_args args {});
          tuple_since' = (if take_all then tuple_since else Mapping.empty) in
          ((t, gc, data_prev, data_in, table_in', wf_table_in', tuple_in', wf_table_since', tuple_since'), aggaux'))
       else if args_L args = args_R args then
          (let in_del = (if pos then table_in - X else table_in \<inter> X);
          tuple_in' = mapping_delete_set tuple_in in_del;
          table_in' = table_in - in_del;
          wf_table_in' = wf_table_upd args tuple_in' (\<lambda>_. wf_table_of_set_args args table_in');
          tuple_since' = Mapping.filter (\<lambda>as _. join_cond pos X as) tuple_since;
          wf_table_since' = wf_table_upd args tuple_since' (\<lambda>_. wf_table_of_set_args args (Mapping.keys tuple_since')) in
          ((t, gc, data_prev, data_in, table_in', wf_table_in', tuple_in', wf_table_since', tuple_since'), delete_maggaux' aggargs in_del aggaux))
       else (let wf_X = wf_table_of_idx (wf_idx_of_set (args_L args) (args_L args) X);
          wf_in_del = (if pos then wf_table_antijoin else wf_table_join) wf_table_in wf_X;
          in_del = wf_table_set wf_in_del;
          tuple_in' = mapping_delete_set tuple_in in_del;
          table_in' = table_in - in_del;
          wf_table_in' = wf_table_antijoin wf_table_in wf_in_del;
          wf_since_del = (if pos then wf_table_antijoin else wf_table_join) wf_table_since wf_X;
          since_del = wf_table_set wf_since_del;
          tuple_since' = mapping_delete_set tuple_since since_del;
          wf_table_since' = wf_table_antijoin wf_table_since wf_since_del in
          ((t, gc, data_prev, data_in, table_in', wf_table_in', tuple_in', wf_table_since', tuple_since'), delete_maggaux' aggargs in_del aggaux)))))"

fun gc_join_mmasaux :: "args \<Rightarrow> event_data table \<Rightarrow> mmasaux \<Rightarrow> mmasaux" where
  "gc_join_mmasaux args X ((t, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since), aux) =
    (if \<not> memR (args_ivl args) (t - gc) then join_mmasaux args X ((gc_mmsaux args (t, gc,
      data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since), aux))
    else join_mmasaux args X ((t, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since), aux))"

fun shift_end_mmasaux :: "args \<Rightarrow> ts \<Rightarrow> mmasaux \<Rightarrow> mmasaux" where
  "shift_end_mmasaux args nt ((t, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since), aggaux) =
    (case args_agg args of 
      None \<Rightarrow> (shift_end args nt (t, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since), aggaux) |
      Some aggargs \<Rightarrow>
        (let I = args_ivl args;
         data_prev' = dropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) data_prev;
         (data_in, discard) = takedropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) data_in;
         (tuple_in, del) = fold filter_set discard (tuple_in, {}) in
         ((t, gc, data_prev', data_in,
          table_in - del, wf_table_upd args tuple_in (\<lambda>_. wf_table_antijoin wf_table_in (wf_table_of_set_args args del)), tuple_in,
          wf_table_since, tuple_since), delete_maggaux' aggargs del aggaux)))"

fun add_new_ts_mmasaux' :: "args \<Rightarrow> ts \<Rightarrow> mmasaux \<Rightarrow> mmasaux" where
  "add_new_ts_mmasaux' args nt ((t, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since), aggaux) =
    (case args_agg args of 
      None \<Rightarrow> (add_new_ts_mmsaux' args nt (t, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since), aggaux) |
      Some aggargs \<Rightarrow>
        (let I = args_ivl args;
         (data_prev, move) = takedropWhile_queue (\<lambda>(t, X). memL I (nt - t)) data_prev;
          data_in = fold (\<lambda>(t, X) data_in. append_queue (t, X) data_in) move data_in;
         (tuple_in', add) = fold (upd_set_keys (\<lambda>X t. {as \<in> X. valid_tuple tuple_since (t, as)})) move (tuple_in, {}) in
         ((nt, gc, data_prev, data_in, table_in \<union> add, wf_table_upd args tuple_in' (\<lambda>_. wf_table_union wf_table_in (wf_table_of_set_args args add)), tuple_in', wf_table_since, tuple_since),
         insert_maggaux' aggargs (add - Mapping.keys tuple_in) aggaux)))"

definition add_new_ts_mmasaux :: "args \<Rightarrow> ts \<Rightarrow> mmasaux \<Rightarrow> mmasaux" where
  "add_new_ts_mmasaux args nt aux = add_new_ts_mmasaux' args nt (shift_end_mmasaux args nt aux)"

fun result_mmasaux :: "args \<Rightarrow> mmasaux \<Rightarrow> event_data table" where
  "result_mmasaux args ((nt, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since), aggaux) =
    (case (args_agg args, aggaux) of 
      (Some aggargs, Some aux) \<Rightarrow> result_maggaux aggargs aux |
      (Some aggargs, None) \<Rightarrow> eval_aggargs aggargs table_in |
      (None, _) \<Rightarrow> table_in)"

subsection \<open>Until with aggregation\<close>

type_synonym mmauaux = "event_data mmuaux \<times> aggaux option"

fun valid_mmauaux' :: "args \<Rightarrow> ts \<Rightarrow> ts \<Rightarrow> mmauaux \<Rightarrow> event_data muaux \<Rightarrow> bool" where
  "valid_mmauaux' args cur dt ((tp, tss, tables, len, result, a1_map, a2_map, tstp_map, done), aggaux) auxlist 
 = (valid_mmuaux' args cur dt (tp, tss, tables, len, result, a1_map, a2_map, tstp_map, done) auxlist \<and>
  (case args_agg args of
      Some aggargs \<Rightarrow> (valid_maggaux' aggargs aggaux (Mapping.keys (the (Mapping.lookup a2_map (tp - len))))) |
      None \<Rightarrow> True))"

definition valid_mmauaux :: "args \<Rightarrow> ts \<Rightarrow> mmauaux \<Rightarrow> event_data muaux \<Rightarrow> bool" where
  "valid_mmauaux args cur = valid_mmauaux' args cur cur"

fun init_mmauaux :: "args \<Rightarrow> mmauaux" where
  "init_mmauaux args = (init_mmuaux args, (case args_agg args of
    Some aggargs \<Rightarrow> init_maggaux' aggargs |
    None \<Rightarrow> None))"

fun lin_ts_mmauaux :: "mmauaux \<Rightarrow> ts list" where
  "lin_ts_mmauaux ((tp, tss, len, tables, result, a1_map, a2_map, tstp_map, done), auxs) =
    linearize tss"

fun eval_step_mmauaux :: "args \<Rightarrow> mmauaux \<Rightarrow> mmauaux" where
  "eval_step_mmauaux args ((tp, tss, tables, len, result, a1_map, a2_map, tstp_map, done), aggaux) = 
  (case safe_hd tss of 
  (Some ts, tss') \<Rightarrow>
    (case args_agg args of 
    None \<Rightarrow> (eval_step_mmuaux args (tp, tss, tables, len, result, a1_map, a2_map, tstp_map, done), aggaux) |
    Some aggargs \<Rightarrow>
      (case Mapping.lookup a2_map (tp - len) of 
      Some m \<Rightarrow> 
        let I = args_ivl args;
        tss' = tl_queue tss';
        (ts', tss'') = case safe_hd tss' of 
              (Some ts', tss'') \<Rightarrow> (ts', tss'') |
              (None, tss'') \<Rightarrow> (0, tss'');
        (tables, taken) = takedropWhile_queue (\<lambda>(table, tstp). \<not> ts_tp_lt I ts' (tp - len + 1) tstp) tables;
        to_del_approx = \<Union>(set (map fst taken));
        to_del = Set.filter (\<lambda>x. case Mapping.lookup m x of Some tstp \<Rightarrow> (\<not>ts_tp_lt I ts' (tp - len + 1) tstp) |
                                                            None \<Rightarrow> False) to_del_approx;
        m'' = mapping_delete_set m to_del;
        result' = if len = 1 then {} else (result - to_del) \<union> (case Mapping.lookup a2_map (tp - len + 1) of Some m' \<Rightarrow> Mapping.keys m');
        to_ins = case Mapping.lookup a2_map (tp - len + 1) of Some m' \<Rightarrow> m';
        a2_map = if len = 1 then Mapping.update tp Mapping.empty a2_map
                 else Mapping.update (tp - len + 1)
          (Mapping.combine (\<lambda>tstp tstp'. max_tstp tstp tstp') m'' to_ins) a2_map;
        a2_map = Mapping.delete (tp - len) a2_map;
        tstp_map = Mapping.delete (tp - len) tstp_map;
        agg_result = result_maggaux' aggargs aggaux;
        T = case agg_result of Some k \<Rightarrow> k |
                               None \<Rightarrow> eval_args_agg args (Mapping.keys m);
        to_ins = Mapping.filter (\<lambda>k v. Mapping.lookup m'' k = None) to_ins;
        aggaux = (if len = 1 then init_maggaux' aggargs else insert_maggaux' aggargs (Mapping.keys to_ins) (delete_maggaux' aggargs to_del aggaux)) in
        ((tp, tss'', tables, len - 1, result', a1_map, a2_map, tstp_map, T # done), aggaux))))"

fun shift_mmauaux :: "args \<Rightarrow> ts \<Rightarrow> mmauaux \<Rightarrow> mmauaux" where
  "shift_mmauaux args nt ((tp, tss, tables, len, result, a1_map, a2_map, tstp_map, done), auxs) =
    (let (tss_queue, tss') = takeWhile_queue (\<lambda>t. \<not> memR (args_ivl args) (nt - t)) tss in
    foldl (\<lambda>aux _. eval_step_mmauaux args aux) ((tp, tss', tables, len, result,
      a1_map, a2_map, tstp_map, done), auxs) (linearize tss_queue))"

fun add_new_mmauaux :: "args \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow> mmauaux \<Rightarrow> mmauaux" where
  "add_new_mmauaux args rel1 rel2 nt (mmuaux, aggaux) =
    (case args_agg args of 
     None \<Rightarrow> let (tp, tss, tables, len, result,  a1_map, a2_map, tstp_map, done) = add_new_mmuaux args rel1 rel2 nt mmuaux in
  ((tp, tss, tables, len, result, a1_map, a2_map, tstp_map, done), aggaux) |
     Some aggargs \<Rightarrow>
    (let ((tp, tss, tables, len, result, a1_map, a2_map, tstp_map, done), aggaux) = shift_mmauaux args nt (mmuaux, aggaux);
    I = args_ivl args; pos = args_pos args;
    new_tstp = (if memL I 0 then Inr tp else Inl nt);
    tstp_map = Mapping.update tp nt tstp_map;
    m = case Mapping.lookup a2_map (tp - len) of Some m \<Rightarrow> m;
    tmp = \<Union>((\<lambda>as. case Mapping.lookup a1_map (restrict (args_L args) (args_R args) as) of None \<Rightarrow>
      (if \<not>pos then {(tp - len, as)} else {})
      | Some tp' \<Rightarrow> if pos then {(max (tp - len) tp', as)}
      else {(max (tp - len) (tp' + 1), as)}) ` rel2) \<union> (if memL I 0 then {tp} \<times> rel2 else {});
    tmp = Set.filter (\<lambda>(tp, as). case Mapping.lookup tstp_map tp of Some ts \<Rightarrow> memL I (nt - ts)) tmp;
    table = snd ` tmp;
    tables = append_queue (table, if memL I 0 then Inr tp else Inl nt) tables;
    a2_map' = Mapping.update (tp + 1) Mapping.empty
      (upd_nested a2_map new_tstp (max_tstp new_tstp) tmp);
    a1_map = (if pos then Mapping.filter (\<lambda>as _. as \<in> rel1)
      (upd_set a1_map (\<lambda>_. tp) (rel1 - Mapping.keys a1_map)) else upd_set a1_map (\<lambda>_. tp) rel1);
    to_add = {b. (tp - len, b) \<in> tmp \<and> Mapping.lookup m b = None};
    tss = append_queue nt tss in
    ((tp + 1, tss, tables, len + 1, result \<union> snd ` (Set.filter (\<lambda>(t, x). t = tp - len) tmp), a1_map, a2_map', tstp_map, done), insert_maggaux' aggargs to_add aggaux)))"

fun length_mmauaux :: "args \<Rightarrow> mmauaux \<Rightarrow> nat" where
  "length_mmauaux args ((tp, tss, tables, len, result, a1_map, a2_map, tstp_map, done), auxs) =
    length done + len"

fun eval_mmauaux' :: "args \<Rightarrow> ts \<Rightarrow> mmauaux \<Rightarrow> (event_data table list \<times> mmauaux)" where
  "eval_mmauaux' args nt aux =
    (let ((tp, tss, tables, len, result, a1_map, a2_map, tstp_map, done), auxs) =
    shift_mmauaux args nt aux in
    (rev done, ((tp, tss, tables, len, result, a1_map, a2_map, tstp_map, []), auxs)))"

end
