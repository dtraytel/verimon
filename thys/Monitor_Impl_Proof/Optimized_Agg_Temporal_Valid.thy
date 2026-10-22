(*<*)
theory Optimized_Agg_Temporal_Valid
  imports "Monitor_Impl.Optimized_Agg_Temporal" Optimized_Since_Valid Optimized_Until_Valid "Monitor_Impl.Optimized_Agg_Valid"
begin
(*>*)

section \<open>Correctness of aggregating Since and Until\<close>

subsection \<open>Since with aggregation\<close>

lemma valid_init_mmasaux: 
  assumes "set L \<subseteq> set R" "distinct L" "distinct R"
  shows "valid_mmasaux (init_args I n L R b agg) 0
  (init_mmasaux (init_args I n L R b agg)) []"
proof(cases agg)
  case None
  then show ?thesis using valid_init_mmsaux[OF assms, of I n b agg] by(simp only:init_args_def init_mmasaux.simps) simp
next
  case (Some aggargs)
  show ?thesis using Some valid_init_mmsaux[OF assms, of I n b agg] 
     valid_init_maggaux[of aggargs] by(cases "type_restr aggargs {}") (auto simp: init_args_def) 
qed

lemma valid_add_new_table_mmasaux_unfolded:
  assumes "valid_mmasaux args cur ((nt, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since), aggaux) auxlist"
  and "table (args_R args) rel2"
  shows "valid_mmasaux args cur (add_new_table_mmasaux args rel2 ((nt, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since), aggaux))
    (case auxlist of [] => [(cur, rel2)] | 
    ((t, y) # ts) \<Rightarrow> if t = cur then (t, y \<union> rel2) # ts else (cur, rel2) # auxlist)"
proof -
  let ?msaux = "(nt, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since)"
  let ?msaux' = "add_new_table_mmsaux args rel2 ?msaux"
  obtain nt' gc' data_prev' data_in' table_in' wf_table_in' tuple_in' wf_table_since' tuple_since'
    where split: "?msaux' = (nt', gc', data_prev', data_in', table_in', wf_table_in', tuple_in', wf_table_since', tuple_since')" by fastforce 
  have valid_msaux: "valid_mmsaux args cur ?msaux auxlist" using assms(1) by(auto split:option.splits) 
  note valid_msaux' = valid_add_new_table_mmsaux[OF valid_msaux assms(2)] 
  show ?thesis
  proof(cases "memL (args_ivl args) 0")
    case True
    then have tuple_in_eq: "Mapping.keys tuple_in' = Mapping.keys tuple_in \<union> (rel2 - Mapping.keys tuple_in)" 
      using split Mapping_upd_set_keys[of tuple_in] by auto
    have table_in'_def: "table_in' = Mapping.keys tuple_in \<union> rel2" 
      using True split valid_msaux by simp
    show ?thesis
    proof(cases "args_agg args")
      case None
      then show ?thesis using True valid_msaux' assms(1) by(auto simp del:valid_mmsaux.simps split:option.splits)
    next
      case (Some aggargs)
      then have some_aggargs: "args_agg args = Some aggargs" by auto
      then obtain msaux' aggaux' where new_def: "(msaux', aggaux') = add_new_table_mmasaux args rel2 (?msaux, aggaux)"
        by(auto split:prod.splits)
      show ?thesis
      proof(cases aggaux')
        case None
        then show ?thesis using Some new_def valid_msaux' by(auto simp del:valid_mmsaux.simps)
      next
        case (Some a)
        then obtain aux where [simp]: "aggaux = Some aux" using new_def some_aggargs by(cases aggaux) (auto split:if_splits) 
        then have valid_maggaux: "valid_maggaux aggargs aux (Mapping.keys tuple_in)" 
          using assms(1) some_aggargs
          by auto
        show ?thesis
        proof(cases "memL (args_ivl args) 0")
          case True
          then have finite: "finite (rel2 - Mapping.keys tuple_in)" 
            using new_def some_aggargs Some by(simp del:insert_maggaux.simps split:prod.splits if_splits)
          then show ?thesis using True Some some_aggargs new_def valid_msaux' valid_insert_maggaux[OF valid_maggaux finite] split tuple_in_eq
            by(simp add: table_in'_def del:valid_mmsaux.simps split:prod.splits if_splits)
        next
          case False
          then show ?thesis using assms(1) valid_maggaux some_aggargs valid_msaux' by simp
        qed
      qed
    qed
  next
    case False
    then have "Mapping.keys tuple_in' = Mapping.keys tuple_in" using split by auto
    then show ?thesis using False valid_msaux' assms(1) by(auto simp del:valid_mmsaux.simps split:option.splits)
  qed
qed

lemma valid_add_new_table_mmasaux:
  assumes valid_before: "valid_mmasaux args cur (mmsaux, aux) auxlist"
  and table_X: "table (args_R args) X"
  shows "valid_mmasaux args cur (add_new_table_mmasaux args X (mmsaux, aux))
    (case auxlist of
      [] => [(cur, X)]
    | ((t, y) # ts) \<Rightarrow> if t = cur then (t, y \<union> X) # ts else (cur, X) # auxlist)"
  using valid_add_new_table_mmasaux_unfolded assms
  by (cases mmsaux) fast

subsubsection \<open>Join and garbage collection\<close>

lemma valid_join_mmasaux_unfolded:
  assumes "valid_mmasaux args cur ((nt, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since), aggaux) auxlist"
  and "table (args_L args) rel1"
  shows "valid_mmasaux args cur (join_mmasaux args rel1 ((nt, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since), aggaux))
    (map (\<lambda>(t, rel). (t, join (args_R args) rel (args_pos args) (args_L args) rel1)) auxlist)"
proof -
  let ?msaux = "(nt, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since)"
  let ?msaux' = "join_mmsaux args rel1 ?msaux"
  let ?p1 = "join_filter_cond (args_pos args) rel1"
  let ?p2 = "\<lambda>k _. join_cond (args_pos args) rel1 (restrict (args_L args) (args_R args) k)"
  have valid_msaux: "valid_mmsaux args cur ?msaux auxlist" using assms(1) by(auto split:option.splits) 
  note valid_msaux' = valid_join_mmsaux[OF valid_msaux assms(2)]
  have keys_in: "Mapping.keys tuple_in = table_in"
    using valid_msaux
    by auto
  show ?thesis
  proof(cases "args_agg args")
    case None
    then show ?thesis using valid_msaux' by(auto simp del:valid_mmsaux.simps split:if_splits) 
  next
    case (Some aggargs)
    then have some_aggargs: "args_agg args = Some aggargs" by auto
    show ?thesis 
    proof(cases "args_L args = []")
      case True
      let ?temp = "let take_all = (args_pos args \<longleftrightarrow> [] \<in> rel1); 
      table_in' = (if take_all then table_in else {});
      wf_table_in' = (if take_all then wf_table_in else wf_table_of_set_args args {});
      tuple_in' = (if take_all then tuple_in else Mapping.empty);
      aggaux' = (if take_all then aggaux else init_maggaux' aggargs);
      wf_table_since' = (if take_all then wf_table_since else wf_table_of_set_args args {});
      tuple_since = (if take_all then tuple_since else Mapping.empty) in
      ((nt, gc, data_prev, data_in, table_in', wf_table_in', tuple_in', wf_table_since', tuple_since), aggaux')"
      have *: "join_mmasaux args rel1 ((nt, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since), aggaux) = ?temp" 
        using Some True by auto
      have "valid_mmasaux args cur ?temp (map (\<lambda>(t, rel). (t, join (args_R args) rel (args_pos args) (args_L args) rel1)) auxlist)"
        using valid_msaux' True valid_init_maggaux assms(1) some_aggargs
        by(simp del:valid_mmsaux.simps init_maggaux.simps split:if_splits option.splits prod.splits) (metis case_prodD)
      then show ?thesis using * by presburger
    next
      case False
      show ?thesis
      proof (cases "args_L args = args_R args")
        case eq: True
        let ?temp = "let in_del = (if args_pos args then table_in - rel1 else table_in \<inter> rel1);
          tuple_in' = mapping_delete_set tuple_in in_del;
          table_in' = table_in - in_del;
          wf_table_in' = wf_table_upd args tuple_in' (\<lambda>_. wf_table_of_set_args args table_in');
          tuple_since' = Mapping.filter (\<lambda>as _. join_cond (args_pos args) rel1 as) tuple_since;
          wf_table_since' = wf_table_upd args tuple_since' (\<lambda>_. wf_table_of_set_args args (Mapping.keys tuple_since')) in
          ((nt, gc, data_prev, data_in, table_in', wf_table_in', tuple_in', wf_table_since', tuple_since'), delete_maggaux' aggargs in_del aggaux)"
        have *: "join_mmasaux args rel1 ((nt, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since), aggaux) = ?temp"
          using False eq some_aggargs by auto
        have "valid_mmasaux args cur ?temp (map (\<lambda>(t, rel). (t, join (args_R args) rel (args_pos args) (args_L args) rel1)) auxlist)"
        proof(cases aggaux)
          case None
          then show ?thesis using some_aggargs valid_msaux' False eq by(simp del:valid_mmsaux.simps)
        next
          case (Some a)
          then have valid_maggaux: "valid_maggaux aggargs a (Mapping.keys tuple_in)" using some_aggargs assms(1) by auto
          have in_del_sub: "(if args_pos args then table_in - rel1 else table_in \<inter> rel1) \<subseteq> Mapping.keys tuple_in"
            by (auto simp: keys_in)
          show ?thesis using valid_delete_maggaux[OF valid_maggaux in_del_sub] some_aggargs Some valid_msaux' False eq
            by (auto simp del:delete_maggaux.simps valid_mmsaux.simps simp: keys_in split:option.splits prod.splits if_splits)
        qed
        then show ?thesis using * by presburger
      next
        case neq: False
      let ?temp = "let wf_X = wf_table_of_idx (wf_idx_of_set (args_L args) (args_L args) rel1);
        wf_in_del = (if args_pos args then wf_table_antijoin else wf_table_join) wf_table_in wf_X;
        in_del = wf_table_set wf_in_del;
        tuple_in' = mapping_delete_set tuple_in in_del;
        table_in' = table_in - in_del;
        wf_table_in' = wf_table_antijoin wf_table_in wf_in_del;
        wf_since_del = (if args_pos args then wf_table_antijoin else wf_table_join) wf_table_since wf_X;
        since_del = wf_table_set wf_since_del;
        tuple_since' = mapping_delete_set tuple_since since_del;
        wf_table_since' = wf_table_antijoin wf_table_since wf_since_del in
        ((nt, gc, data_prev, data_in, table_in', wf_table_in', tuple_in', wf_table_since', tuple_since'), delete_maggaux' aggargs in_del aggaux)"
      have *: "join_mmasaux args rel1 ((nt, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since), aggaux) = ?temp" 
        using False neq some_aggargs by auto
      have "valid_mmasaux args cur ?temp (map (\<lambda>(t, rel). (t, join (args_R args) rel (args_pos args) (args_L args) rel1)) auxlist)" 
      proof(cases aggaux)
        case None
        then show ?thesis using some_aggargs valid_msaux' False neq by(simp del:valid_mmsaux.simps) 
      next
        case (Some a)
        then have valid_maggaux: "valid_maggaux aggargs a (Mapping.keys tuple_in)" using some_aggargs assms(1) by auto
        have L_R: "set (args_L args) \<subseteq> set (args_R args)"
          and distL: "distinct (args_L args)" and distR: "distinct (args_R args)"
          and sig_in: "wf_table_sig wf_table_in = args_R args"
          and table_in: "wf_table_set wf_table_in = table_in"
          and tab_in: "table (args_R args) table_in"
          using valid_msaux keys_in
          by auto
        have aux: "wf_idx_sig (wf_idx_of_set (args_L args) (args_L args) rel1) = args_L args"
          by (simp add: wf_idx_sig_of_set distL)
        have aux_set: "wf_idx_set (wf_idx_of_set (args_L args) (args_L args) rel1) = rel1"
          using assms(2) by (auto simp: wf_idx_set_of_set distL dest: tableD)
        note sub = join_sub[OF distR distL tab_in assms(2) L_R]
        have cols: "cols_union (args_R args) (args_L args) = args_R args"
          using L_R by (rule cols_union_subset)
        show ?thesis using
            valid_delete_maggaux[OF valid_maggaux,
              where ?Y="wf_table_set ((if args_pos args then wf_table_antijoin else wf_table_join) wf_table_in (wf_table_of_idx (wf_idx_of_set (args_L args) (args_L args) rel1)))"]
              some_aggargs Some valid_msaux' False neq mapping_filter_keys_diff[of _ tuple_in, symmetric]
          by (auto simp del:delete_maggaux.simps valid_mmsaux.simps simp: keys_in table_in
              wf_table_set_antijoin wf_table_set_join sig_in aux aux_set L_R sub split:option.splits prod.splits if_splits)
      qed
      then show ?thesis using * by presburger
      qed
    qed
  qed
qed

lemma valid_join_mmasaux: "valid_mmasaux args cur (mmsaux, aux) auxlist \<Longrightarrow>
  table (args_L args) X \<Longrightarrow> valid_mmasaux args cur
  (join_mmasaux args X (mmsaux, aux)) (map (\<lambda>(t, rel). (t, join (args_R args) rel (args_pos args) (args_L args) X)) auxlist)"
  using valid_join_mmasaux_unfolded by (cases mmsaux) fast

lemma gc_join_mmasaux_alt: "gc_join_mmasaux args rel1 (mmsaux, aux) = join_mmasaux args rel1 ((gc_mmsaux args mmsaux), aux) \<or>
  gc_join_mmasaux args rel1 (mmsaux, aux) = join_mmasaux args rel1 (mmsaux, aux)"
  by(cases mmsaux) (auto simp only: gc_join_mmasaux.simps split: if_splits)

lemma valid_gc_mmasaux_unfolded:
  assumes valid_before: "valid_mmasaux args cur ((nt, gc, data_prev, data_in, table_in, wf_table_in,
    tuple_in, wf_table_since, tuple_since), aux) ys"
  shows "valid_mmasaux args cur (gc_mmsaux args (nt, gc, data_prev, data_in, table_in, wf_table_in,
    tuple_in, wf_table_since, tuple_since), aux) ys"
proof -
  have valid_msaux: "valid_mmsaux args cur (nt, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) ys" using valid_before
    by(simp del:valid_mmsaux.simps split:option.splits)
  note valid_msaux' = valid_gc_mmsaux_unfolded[OF valid_msaux]
  show ?thesis using valid_gc_mmsaux_unfolded[OF valid_msaux] valid_before
    by(simp split:option.splits prod.splits) 
qed

lemma valid_gc_mmasaux: "valid_mmasaux args cur (mmsaux, aux) ys \<Longrightarrow> valid_mmasaux args cur ((gc_mmsaux args mmsaux), aux) ys"
  using valid_gc_mmasaux_unfolded by (cases mmsaux) fast

lemma valid_gc_join_mmasaux:
  assumes "valid_mmasaux args cur (mmsaux, aux) auxlist" "table (args_L args) rel1"
  shows "valid_mmasaux args cur (gc_join_mmasaux args rel1 (mmsaux, aux))
    (map (\<lambda>(t, rel). (t, join (args_R args) rel (args_pos args) (args_L args) rel1)) auxlist)"
  using gc_join_mmasaux_alt[of args rel1 mmsaux aux]
  valid_gc_mmasaux[OF assms(1)] valid_join_mmasaux using assms by presburger

subsubsection \<open>New timestamps and result\<close>

lemma valid_shift_end_mmasaux_unfolded:
  assumes valid_before: "valid_mmasaux args cur
    ((ot, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since), aggaux) auxlist"
  and nt_mono: "nt \<ge> cur"
  shows "valid_mmasaux args cur (shift_end_mmasaux args nt
    ((ot, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since), aggaux))
    (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) auxlist)"
proof -
  let ?msaux = "(ot, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since)"
  obtain data_in' discard where takedrop_def: "(data_in', discard) = takedropWhile_queue (\<lambda>(t, X). \<not> memR (args_ivl args) (nt - t)) data_in"
    by (metis old.prod.exhaust)
  obtain msaux' aggaux' where updated_def: "shift_end_mmasaux args nt ((ot, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since), aggaux) = (msaux', aggaux')"
    by fastforce
  then obtain ot' gc' data_prev' data_in' table_in' wf_table_in' tuple_in' wf_table_since' tuple_since' where split:
    "msaux' = (ot', gc', data_prev', data_in', table_in', wf_table_in', tuple_in', wf_table_since', tuple_since')"
    by (cases msaux') auto
  have tbl: "table_in = Mapping.keys tuple_in" using valid_before by auto
  have valid_msaux: "valid_mmsaux args cur ?msaux auxlist" using assms(1) by(auto split:option.splits) 
  show ?thesis
  proof(cases "args_agg args")
    case None
    then show ?thesis using valid_shift_end_mmsaux[OF valid_msaux assms(2)] takedrop_def
      by(auto simp del:valid_mmsaux.simps split:prod.splits) 
  next
    case (Some aggargs)
    have valid_maggaux: "valid_maggaux' aggargs aggaux (Mapping.keys tuple_in)" using valid_before Some by auto
    define empty where "empty = ({} :: event_data table)"
    obtain to_del where *: "(tuple_in', to_del) = fold filter_set discard (tuple_in, empty)" 
      "aggaux' = delete_maggaux' aggargs to_del aggaux" 
      "table_in' = table_in - to_del"
      using split updated_def Some takedrop_def empty_def 
      by(auto simp del: takedropWhile_queue.simps dropWhile_queue.simps split:prod.splits option.splits)
    then have "msaux' = shift_end args nt (ot, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since)"
      using  valid_before Some split updated_def takedrop_def
      by(auto simp del: valid_mmsaux.simps dropWhile_queue.simps takedropWhile_queue.simps split:prod.splits)
    then have valid_msaux': "valid_mmsaux args cur msaux' (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) auxlist)"
      using valid_shift_end_mmsaux[OF valid_msaux assms(2)] by simp
    have subs: "to_del \<subseteq> Mapping.keys tuple_in" using *(1) empty_def
    proof(induction discard arbitrary: empty tuple_in)
      case Nil
      then show ?case using Nil by auto
    next
      case (Cons a discard)
      then obtain X t where aux: "a = (t, X)" by fastforce
      then show ?case using Cons.IH[OF Cons(2)[unfolded aux fold.simps comp_def filter_set.simps Let_def]]
      by auto (metis (no_types, opaque_lifting) Cons.prems(1) Cons.prems(2) Mapping_keys_intro empty_iff fold_filter_set_None)
  qed
    have "valid_maggaux' aggargs aggaux' table_in'"
    proof(cases aggaux)
      case None
      then show ?thesis using *(2) by auto
    next
      case (Some a)
      then have **: "valid_maggaux aggargs a (Mapping.keys tuple_in)" using valid_maggaux by auto
      show ?thesis unfolding *(2-3) tbl using valid_delete_maggaux[OF ** subs] Some
        by (auto simp del:delete_maggaux.simps split:if_splits)
    qed
    then show ?thesis using Some valid_msaux' takedrop_def updated_def split
      by(auto simp del:shift_end_mmasaux.simps valid_maggaux.simps takedropWhile_queue.simps dropWhile_queue.simps valid_mmsaux.simps split:option.splits prod.splits)
  qed
qed

lemma valid_shift_end_mmasaux: "valid_mmasaux args cur (mmsaux, aux) auxlist \<Longrightarrow> nt \<ge> cur \<Longrightarrow>
  valid_mmasaux args cur (shift_end_mmasaux args nt (mmsaux, aux))
  (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) auxlist)"
  using valid_shift_end_mmasaux_unfolded by (cases mmsaux) fast

lemma valid_add_new_ts_mmasaux'_unfolded:
  assumes valid_before: "valid_mmasaux args cur ((ot, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since), aggaux) auxlist"
  and nt_mono: "nt \<ge> cur"
  shows "valid_mmasaux args nt (add_new_ts_mmasaux' args nt
    ((ot, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since), aggaux)) auxlist"
proof -
  let ?msaux = "(ot, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since)"
  obtain data_prev' move where takedrop_def: "(data_prev', move) = takedropWhile_queue (\<lambda>(t, X). memL (args_ivl args) (nt - t)) data_prev"
    by (metis old.prod.exhaust)
  obtain msaux' aggaux' where updated_def: "add_new_ts_mmasaux' args nt ((ot, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since), aggaux) = (msaux', aggaux')"
    by fastforce
  then obtain ot' gc' data_prev' data_in' table_in' wf_table_in' tuple_in' wf_table_since' tuple_since' where split:
    "msaux' = (ot', gc', data_prev', data_in', table_in', wf_table_in', tuple_in', wf_table_since', tuple_since')"
    by (cases msaux') auto
  have valid_msaux: "valid_mmsaux args cur ?msaux auxlist" using assms(1) by(auto split:option.splits) 
  have tbl: "Mapping.keys tuple_in = table_in" using valid_before by auto
  show ?thesis
  proof(cases "args_agg args")
    case None
    show ?thesis using None valid_add_new_ts_mmsaux'[OF valid_msaux assms(2)] takedrop_def
      by(auto simp del:valid_mmsaux.simps split:prod.splits) 
  next
    case (Some aggargs)
    let ?lambda = "(upd_set_keys (\<lambda>X t. {as \<in> X. valid_tuple tuple_since (t, as)}))"
    define empty where empty_def: "empty = ({} :: event_data table)"
    obtain add where *: "(tuple_in', add) = fold ?lambda move (tuple_in, empty)" "table_in' = table_in \<union> add"
      using split updated_def Some takedrop_def by(auto simp: empty_def split:prod.splits)
    then have agg': "aggaux' = insert_maggaux' aggargs (add - table_in) aggaux"
      using split updated_def Some takedrop_def tbl by(auto simp: empty_def split:prod.splits)
    have "msaux' = add_new_ts_mmsaux' args nt (ot, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since)"
      using valid_before Some split updated_def takedrop_def
      by(auto simp del: valid_mmsaux.simps dropWhile_queue.simps takedropWhile_queue.simps split:prod.splits)
    then have valid_msaux': "valid_mmsaux args nt msaux' auxlist"
      using valid_add_new_ts_mmsaux'[OF valid_msaux assms(2)] by simp
    have valid_maggaux: "valid_maggaux' aggargs aggaux (Mapping.keys tuple_in)" using valid_before Some by auto
    then have valid_maggaux': "valid_maggaux' aggargs aggaux' table_in'" 
    proof(cases aggaux)
      case None
      then show ?thesis unfolding agg' by auto
    next
      case (Some a)
      then have **: "valid_maggaux aggargs a (Mapping.keys tuple_in)" using valid_maggaux by auto
      then show ?thesis unfolding agg' using valid_insert_maggaux[OF **, of "add - table_in"] tbl  Some *(2)
        by(auto simp del:insert_maggaux.simps split:prod.splits if_splits option.splits)
    qed
    show ?thesis using valid_maggaux' valid_msaux' updated_def Some split by(auto simp del:shift_end_mmasaux.simps)
  qed
qed

lemma valid_add_new_ts_mmasaux': "valid_mmasaux args cur (mmsaux, aux) auxlist \<Longrightarrow> nt \<ge> cur \<Longrightarrow>
  valid_mmasaux args nt (add_new_ts_mmasaux' args nt (mmsaux, aux)) auxlist"
  using valid_add_new_ts_mmasaux'_unfolded by (cases mmsaux) fast

lemma valid_add_new_ts_mmasaux:
  assumes "valid_mmasaux args cur (mmsaux, aux) auxlist" "nt \<ge> cur"
  shows "valid_mmasaux args nt (add_new_ts_mmasaux args nt (mmsaux, aux))
    (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) auxlist)"
proof -
  obtain mmsaux' aux' where shift: "shift_end_mmasaux args nt (mmsaux, aux) = (mmsaux', aux')"
    by (cases "shift_end_mmasaux args nt (mmsaux, aux)")
  have "valid_mmasaux args cur (mmsaux', aux') (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) auxlist)"
    using valid_shift_end_mmasaux[OF assms] unfolding shift .
  then show ?thesis
    unfolding add_new_ts_mmasaux_def shift by (rule valid_add_new_ts_mmasaux'[OF _ assms(2)])
qed

lemma valid_result_mmasaux_unfolded:
  assumes "valid_mmasaux args cur ((nt, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since), aggaux) auxlist"
  shows "result_mmasaux args ((nt, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since), aggaux) = eval_args_agg args (foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist, memL (args_ivl args) (cur - t)] {})"
proof -
  let ?msaux = "(nt, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since)"
  have valid_msaux: "valid_mmsaux args cur ?msaux auxlist" using assms by(auto split:option.splits) 
  have tuple_in_rel: "foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist, memL (args_ivl args) (cur - t)] {} = table_in"
    using valid_result_mmsaux[OF valid_msaux] by auto
  show ?thesis
  proof(cases "args_agg args")
    case None
    then show ?thesis using tuple_in_rel assms by(simp add: eval_args_agg_def split:option.splits) 
  next
    case (Some a)
    then show ?thesis using tuple_in_rel assms valid_result_maggaux 
      by(auto simp del: valid_mmsaux.simps simp add: eval_args_agg_def split:option.splits)
  qed
qed

lemma valid_result_mmasaux: "valid_mmasaux args cur (mmsaux, aux) auxlist \<Longrightarrow>
  result_mmasaux args (mmsaux, aux) = eval_args_agg args (foldr (\<union>) (concat (map (\<lambda>(t, rel). if memL (args_ivl args) (cur - t) then [rel] else []) auxlist)) {})"
  using valid_result_mmasaux_unfolded by (cases mmsaux) fast

interpretation default_mmasaux: msaux valid_mmasaux init_mmasaux add_new_ts_mmasaux gc_join_mmasaux
  add_new_table_mmasaux result_mmasaux
  using valid_init_mmasaux valid_add_new_ts_mmasaux valid_gc_join_mmasaux valid_add_new_table_mmasaux
    valid_result_mmasaux
  by unfold_locales (auto simp del: valid_mmasaux.simps split:prod.splits)

subsection \<open>Until with aggregation\<close>

lemma valid_length_mmauaux:
  assumes "valid_mmauaux args cur (mmaux, auxs) auxlist"
  shows "length_mmauaux args (mmaux, auxs) = length auxlist"
  using assms by (cases mmaux) (auto simp add: valid_mmauaux_def dest: list_all2_lengthD)

lemma valid_init_mmauaux:
  assumes "set L \<subseteq> set R" "distinct L" "distinct R"
  shows "valid_mmauaux (init_args I n L R b agg) 0 (init_mmauaux (init_args I n L R b agg)) []"
proof -
  let ?map = "Mapping.update 0 Mapping.empty Mapping.empty"
  note valid_mmuaux = valid_init_mmuaux[OF assms, of I n b agg] 
  show ?thesis 
  proof (cases "agg")
    case None
    then show ?thesis using valid_mmuaux
      by(simp only:init_args_def init_mmauaux.simps; simp add: init_mmuaux_def valid_mmauaux_def valid_mmuaux_def)
  next
    case (Some a)
    then show ?thesis using valid_mmuaux Some valid_init_maggaux[of a]
      by(simp only:init_args_def init_mmauaux.simps) (auto simp add: Mapping.lookup_update[of 0 Mapping.empty Mapping.empty] simp del: valid_mmuaux'.simps simp add: init_mmuaux_def valid_mmauaux_def valid_mmuaux_def)
  qed
qed

subsubsection \<open>Evaluation steps\<close>

lemma valid_eval_step_mmauaux_unfolded:
  assumes "valid_mmauaux' args cur dt ((tp, tss, tables, len, result,  a1_map, a2_map, tstp_map, done), aggaux) auxlist"
    "lin_ts_mmauaux ((tp, tss, tables, len, result, a1_map, a2_map, tstp_map, done), aggaux) = ts # tss''" "\<not> memR (args_ivl args) (dt - ts)"
  shows "valid_mmauaux' args cur dt (eval_step_mmauaux args ((tp, tss, tables, len, result, a1_map, a2_map, tstp_map, done), aggaux)) auxlist \<and>
    lin_ts_mmauaux (eval_step_mmauaux args ((tp, tss, tables, len, result, a1_map, a2_map, tstp_map, done), aggaux)) = tss'' \<and>
    (case eval_step_mmauaux args ((tp, tss, tables, len, result, a1_map, a2_map, tstp_map, done), aggaux) of
    (mmaux', auxs') \<Rightarrow> mmaux' = eval_step_mmuaux args (tp, tss, tables, len, result, a1_map, a2_map, tstp_map, done))"
proof -
  let ?muaux = "(tp, tss, tables, len, result, a1_map, a2_map, tstp_map, done)"
  obtain tss' where safe_hd_eq: "safe_hd tss = (Some ts, tss')" using assms(2) safe_hd_rep case_optionE by (cases "safe_hd tss") fastforce
  have a2_map_keys: "Mapping.keys a2_map = {tp - len..tp}"
    using assms(1) by auto
  have tp_minus_keys: "tp - len \<in> Mapping.keys a2_map"
    using a2_map_keys by auto
  have len_tp: "len \<le> tp"
    using assms(1) by auto
  have lin_tss_not_Nil: "linearize tss \<noteq> []"
    using safe_hd_rep[OF safe_hd_eq] by auto
  have len_pos: "len > 0"
    using lin_tss_not_Nil assms(1) by auto
  have tp_minus_keys': "tp - len + 1 \<in> Mapping.keys a2_map"
    using a2_map_keys len_pos len_tp by auto
  obtain m where m_def: "Mapping.lookup a2_map (tp - len) = Some m"
    using tp_minus_keys by (auto dest: Mapping.in_keysD)
  have res_eq: "result = Mapping.keys m" using assms(1) m_def by auto
  obtain m' where m'_def: "Mapping.lookup a2_map (tp - len + 1) = Some m'"
    using tp_minus_keys' by (auto dest: Mapping.in_keysD)
  obtain muaux' auxs' where updated_def: "(muaux', auxs') = eval_step_mmauaux args (?muaux, aggaux)" 
    by (metis surj_pair)
  then obtain tp' tss''' tables' len' result' a1_map' a2_map' tstp_map' done' where split:
    "muaux' = (tp', tss''', tables', len', result', a1_map', a2_map', tstp_map', done')" 
    using lin_ts_mmuaux.cases by (smt (verit, ccfv_SIG) length_mmuaux.elims)
  define I where "I = args_ivl args"
  obtain ts' tss'''' where ts'_tss''''_def: "(case safe_hd (tl_queue tss') of (Some ts', tss'') \<Rightarrow> (ts', tss'') | (None, tss'') \<Rightarrow> (0, tss'')) = (ts', tss'''')"
    by fastforce
  then have ts'_def: "ts' = (case safe_hd (tl_queue tss') of (Some ts', tss'') \<Rightarrow> ts' | (None, tss'') \<Rightarrow> 0)" by (auto split: prod.splits option.splits)
  have lin_tss''': "linearize tss'''' = linearize (tl_queue tss')"
    using ts'_tss''''_def safe_hd_rep[of "tl_queue tss'"]
    by (auto split: prod.splits option.splits)
  define taken where "taken = snd (takedropWhile_queue (\<lambda>(table, tstp). \<not> ts_tp_lt I ts' (tp - len + 1) tstp) tables)"
  define tables' where "tables' = fst (takedropWhile_queue (\<lambda>(table, tstp). \<not> ts_tp_lt I ts' (tp - len + 1) tstp) tables)"
  have takedrop_split: "takedropWhile_queue (\<lambda>(table, tstp). \<not> ts_tp_lt I ts' (tp - len + 1) tstp) tables = (tables', taken)" unfolding tables'_def taken_def by auto
  define to_del_approx where "to_del_approx = \<Union>{x. x \<in> set (map fst taken)}"
  define to_del where "to_del = Set.filter (\<lambda>x. case Mapping.lookup m x of Some tstp \<Rightarrow> (\<not>ts_tp_lt I ts' (tp - len + 1) tstp) |
                                                            None \<Rightarrow> False) to_del_approx"
  define to_ins where "to_ins = (case Mapping.lookup a2_map (tp - len + 1) of Some m' \<Rightarrow> m')"
  define m'' where "m'' = mapping_delete_set m to_del"
  define result' where "result' \<equiv> if len = 1 then {} else (result - to_del) \<union> (case Mapping.lookup a2_map (tp - len + 1) of Some m' \<Rightarrow> Mapping.keys m')"
  have muaux'_def: "muaux' = eval_step_mmuaux args ?muaux" 
  proof(cases "args_agg args")
    case None
    then show ?thesis using updated_def safe_hd_eq by auto
  next
    case (Some a)
    then have "valid_maggaux' a aggaux (Mapping.keys m)" using m_def assms(1) by auto
    moreover define T where "T = (case (result_maggaux' a aggaux) of Some k \<Rightarrow> k |
                               None \<Rightarrow> eval_args_agg args (Mapping.keys m))"
    ultimately have T_eq: "T = eval_args_agg args result" unfolding eval_args_agg_def
      using res_eq valid_result_maggaux[of a _ "Mapping.keys m"] Some by(cases aggaux; auto split:option.splits)
    have "muaux' = fst (eval_step_mmauaux args (?muaux, aggaux))"
      using updated_def by (metis fst_conv)
    also have "... = eval_step_mmuaux args ?muaux"
      using T_eq[unfolded T_def] m_def safe_hd_eq m'_def Some
      by (simp add: split_beta del: takedropWhile_queue.simps)
    finally show ?thesis .
  qed
  have valid_muaux: "valid_mmuaux' args cur dt ?muaux auxlist" 
    using assms(1) by auto
  have lin_ts_muaux: "lin_ts_mmuaux (tp, tss, tables, len, result, a1_map, a2_map, tstp_map, done) = ts # tss''" using assms(2) by(auto split:option.splits)
  have valid_old: "lin_ts_mmauaux (eval_step_mmauaux args ((tp, tss, tables, len, result, a1_map, a2_map, tstp_map, done), aggaux)) = tss''"
                  "valid_mmuaux' args cur dt muaux' auxlist"
    using updated_def[symmetric] split valid_eval_step_mmuaux'[OF valid_muaux lin_ts_muaux assms(3)] muaux'_def[symmetric]
    by simp+
  show ?thesis
  proof(cases "args_agg args")
  case None
  then show ?thesis 
    using updated_def[symmetric] valid_old split
    using valid_old by (simp add: muaux'_def)
  next
    case aargs: (Some aggargs)
    let ?m' = "mapping_delete_set m to_del"
    have valid_agg: "valid_maggaux' aggargs aggaux (Mapping.keys m)"
      using assms(1) m_def aargs by(auto simp del: valid_mmuaux'.simps)
    define T where "T = (case (result_maggaux' aggargs aggaux) of Some k \<Rightarrow> k |
                               None \<Rightarrow> eval_args_agg args (Mapping.keys m))"
    then have T_eq: "T = eval_args_agg args (Mapping.keys m)" 
      unfolding eval_args_agg_def
      using valid_agg valid_result_maggaux[of aggargs _ "Mapping.keys m"] aargs 
      by(cases aggaux; auto split:option.splits)
    have done'_def: "done' = T#done" using updated_def split m_def safe_hd_eq aargs m'_def T_def
      by (auto simp del:takedropWhile_queue.simps split:prod.splits)
    have subs: "to_del \<subseteq> Mapping.keys m" 
      unfolding to_del_def 
      by(transfer) 
        (auto split:option.splits)
    then have valid_del: "valid_maggaux' aggargs (delete_maggaux' aggargs to_del aggaux) (Mapping.keys ?m')"
    proof(cases aggaux)
      case None
      then show ?thesis by auto
    next
      case (Some a)
      then have *: "valid_maggaux aggargs a (Mapping.keys m)" using valid_agg by auto
      then show ?thesis  
        using valid_delete_maggaux[OF * subs] Some 
        unfolding delete_set_keys 
        by(auto simp del:delete_maggaux.simps split:prod.splits if_splits)
    qed
    have aux: "Suc (tp - Suc 0) = tp" using len_pos len_tp by fastforce
    have a2_map'_eq: "a2_map' = Mapping.delete (tp - len) (if len = 1 then Mapping.update tp Mapping.empty a2_map
        else Mapping.update (tp - len + 1) (Mapping.combine max_tstp ?m' to_ins) a2_map)"
      using safe_hd_eq m_def m'_def ts'_tss''''_def takedrop_split[unfolded I_def] muaux'_def[unfolded split]
      unfolding to_ins_def to_del_def to_del_approx_def I_def
      by (simp del: takedropWhile_queue.simps)
    have a2_map_split: "Mapping.lookup  a2_map' (tp - len + 1) = (if len = 1 then Some Mapping.empty else Some (Mapping.combine max_tstp ?m' to_ins))"
      using aux by (simp add: a2_map'_eq lookup_update')
    let ?to_ins = "Mapping.filter (\<lambda>k v. Mapping.lookup m'' k = None) to_ins"
    let ?aggaux' = "if len = 1 then init_maggaux' aggargs else insert_maggaux' aggargs (Mapping.keys ?to_ins) (delete_maggaux' aggargs to_del aggaux)"
    have *: "valid_maggaux' aggargs ?aggaux' (Mapping.keys (the (Mapping.lookup a2_map' (tp - len + 1))))"
    proof(cases "len = 1")
      case True
      then show ?thesis unfolding a2_map_split using valid_init_maggaux[of aggargs] by(auto simp del: init_maggaux.simps)
    next
      case False
      then show ?thesis 
      proof(cases "delete_maggaux' aggargs to_del aggaux")
        case None
        then show ?thesis using False by auto
      next
        case (Some a)
        then have *: "valid_maggaux aggargs a (Mapping.keys m'')" 
          unfolding m''_def using valid_del by auto
        have **: "Mapping.keys m'' \<inter> Mapping.keys ?to_ins = {}" 
          by(transfer) (auto split:option.splits)
        have aux: "Mapping.keys m'' \<union> Mapping.keys ?to_ins = Mapping.keys m'' \<union> Mapping.keys to_ins" by transfer auto
        show ?thesis using Some False valid_insert_maggaux[OF * _ **, unfolded aux] finite_keys_filter[of to_ins]
          unfolding m''_def a2_map_split by(auto simp del: insert_maggaux.simps split:prod.splits)
      qed
    qed
    have "tp' = tp" "len' = len - 1"
      using muaux'_def[unfolded split] safe_hd_eq m_def by (simp_all add: split_beta)
    then have new_len: "tp' - len' = Suc (tp - len)"
      using len_pos len_tp by simp
    have "auxs' = snd (eval_step_mmauaux args (?muaux, aggaux))"
      using updated_def by (metis snd_conv)
    then have aux_eq: "auxs' = ?aggaux'"
      using safe_hd_eq aargs m_def ts'_tss''''_def takedrop_split[unfolded I_def]
      unfolding m''_def to_ins_def to_del_def to_del_approx_def I_def
      by (simp del: takedropWhile_queue.simps)
    have "(case eval_step_mmauaux args (?muaux, aggaux) of (mmaux', auxs') \<Rightarrow>
       mmaux' = eval_step_mmuaux args ?muaux)" unfolding updated_def[symmetric] using muaux'_def by auto
    moreover have "lin_ts_mmauaux (eval_step_mmauaux args (?muaux, aggaux)) = tss''" 
      using valid_old unfolding updated_def[symmetric] split by auto
    moreover have "valid_mmauaux' args cur dt (eval_step_mmauaux args (?muaux, aggaux)) auxlist"
      using valid_old new_len *[unfolded aux_eq[symmetric]] 
      unfolding updated_def[symmetric] split valid_mmauaux'.simps aargs
      by(simp del:valid_mmuaux'.simps)
    ultimately show ?thesis by auto
  qed
qed

lemma valid_eval_step_mmauaux':
  assumes "valid_mmauaux' args cur dt (mmaux, auxs) auxlist"
    "lin_ts_mmauaux (mmaux, auxs) = ts # tss''" "\<not> memR (args_ivl args) (dt - ts)"
  shows "valid_mmauaux' args cur dt (eval_step_mmauaux args (mmaux, auxs)) auxlist \<and>
    lin_ts_mmauaux (eval_step_mmauaux args (mmaux, auxs)) = tss'' \<and> 
    (case eval_step_mmauaux args (mmaux, auxs) of (mmaux', auxs') \<Rightarrow>
    mmaux' = eval_step_mmuaux args mmaux)"
proof -
  obtain tp tss tables len result a1_map a2_map tstp_map donea 
    where "mmaux = (tp, tss, tables, len, result, a1_map, a2_map, tstp_map, donea)"
    by (cases mmaux) auto
  then show ?thesis 
    using valid_eval_step_mmauaux_unfolded
    assms by presburger
qed

lemma valid_foldl_eval_step_mmauaux':
  assumes valid_before: "valid_mmauaux' args cur dt aux auxlist"
    "lin_ts_mmauaux aux = tss @ tss'"
    "\<And>ts. ts \<in> set (take (length tss) (lin_ts_mmauaux aux)) \<Longrightarrow> \<not> memR (args_ivl args) (dt - ts)"
  shows "valid_mmauaux' args cur dt (foldl (\<lambda>aux _. eval_step_mmauaux args aux) aux tss) auxlist \<and>
    lin_ts_mmauaux (foldl (\<lambda>aux _. eval_step_mmauaux args aux) aux tss) = tss' \<and> (case (foldl (\<lambda>aux _. eval_step_mmauaux args aux) aux tss) of (mmaux', auxs') \<Rightarrow>
     case aux of (mmaux, auxs) \<Rightarrow> mmaux' = foldl (\<lambda>aux _. eval_step_mmuaux args aux) mmaux tss)"
  using assms
proof (induction tss arbitrary: aux)
  case (Cons ts tss)
  have app_ass: "lin_ts_mmauaux aux = ts # (tss @ tss')"
    using Cons(3) by auto
  obtain mmaux auxs where split: "aux = (mmaux, auxs)" by fastforce
  have "\<not> memR (args_ivl args) (dt - ts)"
    using Cons by auto
  then have valid_step: "valid_mmauaux' args cur dt (eval_step_mmauaux args aux) auxlist"
    "lin_ts_mmauaux (eval_step_mmauaux args aux) = tss @ tss'" 
    "case eval_step_mmauaux args aux of (mmaux', auxs') \<Rightarrow>
     mmaux' = eval_step_mmuaux args mmaux"
    using valid_eval_step_mmauaux' Cons(2) app_ass split by auto 
  have *: "\<And>ts. ts \<in> set (take (length tss) (lin_ts_mmauaux (eval_step_mmauaux args aux))) \<Longrightarrow>
         \<not> memR (args_ivl args) (dt - ts)" using app_ass Cons(4) apply(auto) using valid_step(2) by force
  have "(case foldl (\<lambda>aux _. eval_step_mmauaux args aux) (eval_step_mmauaux args aux) tss of (mmaux', auxs') \<Rightarrow>
         case eval_step_mmauaux args aux of (mmaux, auxs) \<Rightarrow> 
         mmaux' = foldl (\<lambda>aux _. eval_step_mmuaux args aux) mmaux tss)"
    using Cons(1)[OF valid_step(1-2) *] by auto
  then have "(case foldl (\<lambda>aux _. eval_step_mmauaux args aux) aux (ts # tss) of (mmaux', auxs') \<Rightarrow>
       case aux of (mmaux, auxs) \<Rightarrow> mmaux' = foldl (\<lambda>aux _. eval_step_mmuaux args aux) mmaux (ts # tss))" 
    using valid_step(3) split by(simp only:foldl.simps split:prod.splits) simp
  then show ?case
    using Cons(1)[OF valid_step(1-2)] valid_step Cons(4) app_ass by auto
qed auto

lemma valid_mmauaux'_mono:
  assumes "valid_mmauaux' args cur dt aux auxlist" "dt \<le> dt'"
  shows "valid_mmauaux' args cur dt' aux auxlist"
  using assms less_le_trans by (cases aux) (fastforce simp: memR_antimono)

subsubsection \<open>New time-points and evaluation\<close>

lemma valid_shift_mmauaux':
  assumes "valid_mmauaux' args cur cur (mmaux, auxs) auxlist" "nt \<ge> cur"
  shows "valid_mmauaux' args cur nt (shift_mmauaux args nt (mmaux, auxs)) auxlist \<and>
    (\<forall>ts \<in> set (lin_ts_mmauaux (shift_mmauaux args nt (mmaux, auxs))). memR (args_ivl args) (nt - ts)) \<and>
     (case shift_mmauaux args nt (mmaux, auxs) of (mmaux', auxs') \<Rightarrow> 
     mmaux' = shift_mmuaux args nt mmaux)"
proof -
  define I where "I = args_ivl args"
  define pos where "pos = args_pos args"
  let ?aux = "(mmaux, auxs)"
  have valid_folded: "valid_mmauaux' args cur nt ?aux auxlist"
    using assms(1,2) valid_mmauaux'_mono by blast
  obtain tp len tss tables result a1_map a2_map tstp_map "done" where aux_def:
    "mmaux = (tp, tss, tables, len, result, a1_map, a2_map, tstp_map, done)"
    by (cases mmaux) auto
  note valid_before = valid_folded[unfolded aux_def]
  define tss_list where "tss_list =
    linearize (fst (takeWhile_queue (\<lambda>t. \<not> memR I (nt - t)) tss))"
  define tss' where "tss' = snd (takeWhile_queue (\<lambda>t. \<not> memR I (nt - t)) tss)"
  obtain tss_queue where takeWhile_def: "takeWhile_queue (\<lambda>t. \<not> memR I (nt - t)) tss = (tss_queue, tss')" 
    unfolding tss'_def using prod.exhaust_sel by blast
  then have list_queue_aux: "tss_list = linearize tss_queue" 
    unfolding tss_list_def by auto
  let ?mmaux = "(tp, tss', tables, len, result, a1_map, a2_map, tstp_map, done)"
  have tss_list_takeWhile: "tss_list = takeWhile (\<lambda>t. \<not> memR I (nt - t)) (linearize tss)"
    using tss_list_def unfolding takeWhile_queue_rep_fst .
  then obtain tss_list' where tss_list'_def: "linearize tss = tss_list @ tss_list'"
    "tss_list' = dropWhile (\<lambda>t. \<not> memR I (nt - t)) (linearize tss)"
    by auto
  obtain tp' len' tss' tables' result' a1_map' a2_map' tstp_map' "done'" where
    foldl_aux_def: "(tp', tss', tables', len', result', a1_map', a2_map', tstp_map', done') =
    foldl (\<lambda>aux _. eval_step_mmuaux args aux) ?mmaux tss_list"
    by (cases "foldl (\<lambda>aux _. eval_step_mmuaux args aux) ?mmaux tss_list") auto
  have lin_tss_aux: "lin_ts_mmauaux (?mmaux, auxs) = linearize tss"
    unfolding aux_def tss'_def lin_ts_mmauaux.simps takeWhile_queue_rep_snd by auto
  then have valid_aux: "valid_mmauaux' args cur nt (?mmaux, auxs) auxlist" using valid_before by(auto)
  have "take (length tss_list) (lin_ts_mmauaux (?mmaux, auxs)) = tss_list"
    unfolding lin_tss_aux using tss_list'_def(1) by auto
  then have valid_foldl: "valid_mmauaux' args cur nt
    (foldl (\<lambda>aux _. eval_step_mmauaux args aux) (?mmaux, auxs) tss_list) auxlist"
    "lin_ts_mmauaux (foldl (\<lambda>aux _. eval_step_mmauaux args aux) (?mmaux, auxs) tss_list) = tss_list'"
    "case (foldl (\<lambda>aux _. eval_step_mmauaux args aux) (?mmaux, auxs) tss_list) of (mmaux', auxs') \<Rightarrow>
     mmaux' = foldl (\<lambda>aux _. eval_step_mmuaux args aux) ?mmaux tss_list"
    using valid_foldl_eval_step_mmauaux'[OF valid_aux, unfolded lin_tss_aux,
      OF tss_list'_def(1)] tss_list_takeWhile set_takeWhileD
    unfolding lin_tss_aux I_def by fastforce+
  have shift_mmuaux_eq: "shift_mmauaux args nt (mmaux, auxs) 
    = foldl (\<lambda>aux _. eval_step_mmauaux args aux) (?mmaux, auxs) tss_list"
    using tss_list_def unfolding aux_def I_def tss'_def by (auto split:prod.splits)
  have aux: "(case shift_mmauaux args nt (mmaux, auxs) of (mmaux', auxs') \<Rightarrow> 
     mmaux' = shift_mmuaux args nt mmaux)" using valid_foldl(3)
    unfolding aux_def apply(simp only:shift_mmauaux.simps shift_mmuaux.simps) 
    unfolding takeWhile_def[unfolded I_def] tss'_def
    by(simp only:Let_def split:prod.splits) 
      (auto simp add:list_queue_aux simp del:takeWhile_queue.simps)
  have "\<And>ts. ts \<in> set tss_list' \<Longrightarrow> memR (args_ivl args) (nt - ts)"
    using sorted_dropWhile_filter tss_list'_def(2) valid_before 
    unfolding I_def by auto
  then show ?thesis
    using valid_foldl(1)[unfolded shift_mmuaux_eq[symmetric]] aux
    unfolding valid_foldl(2)[unfolded shift_mmuaux_eq[symmetric]] by auto
qed

lemma valid_add_new_mmauaux_unfolded:
  assumes valid_before: "valid_mmauaux args cur ((tp, tss, tables, len, result, a1_map, a2_map, tstp_map, done), auxs) auxlist"
    and tabs: "table (args_L args) rel1" "table (args_R args) rel2"
    and nt_mono: "nt \<ge> cur"
  shows "valid_mmauaux args nt (add_new_mmauaux args rel1 rel2 nt ((tp, tss, tables, len, result, a1_map, a2_map, tstp_map, done), auxs))
    (update_until args rel1 rel2 nt auxlist)"
proof - 
  let ?muaux = "(tp, tss, tables, len, result, a1_map, a2_map, tstp_map, done)"
  have *: "valid_mmauaux' args cur cur (?muaux, auxs) auxlist" using valid_before unfolding valid_mmauaux_def by auto
  obtain tp' tss' tables' len' result' a1_map' a2_map' tstp_map' done' aggaux' where updated_def: 
    "add_new_mmauaux args rel1 rel2 nt (?muaux, auxs) = ((tp', tss', tables', len', result', a1_map', a2_map', tstp_map', done'), aggaux')"
    by (cases "add_new_mmauaux args rel1 rel2 nt (?muaux, auxs)" rule: lin_ts_mmauaux.cases)
  obtain tp_i tss_i tables_i len_i result_i a1_map_i a2_map_i tstp_map_i done_i aggaux_i where inter_def: 
    "shift_mmauaux args nt (?muaux, auxs) = ((tp_i, tss_i, tables_i, len_i, result_i, a1_map_i, a2_map_i, tstp_map_i, done_i), aggaux_i)"
    by (cases "shift_mmauaux args nt (?muaux, auxs)" rule: lin_ts_mmauaux.cases)
  let ?muaux_i = "(tp_i, tss_i, tables_i, len_i, result_i, a1_map_i, a2_map_i, tstp_map_i, done_i)"
  let ?muaux' = "(tp', tss', tables', len', result', a1_map', a2_map', tstp_map', done')"
  have valid_shift: "valid_mmauaux' args cur nt (?muaux_i, aggaux_i) auxlist"
    "?muaux_i = shift_mmuaux args nt ?muaux"
    using valid_shift_mmauaux'[OF * nt_mono] inter_def 
    by(auto simp del:valid_mmauaux'.simps shift_mmauaux.simps shift_mmuaux.simps) 
  define new_tstp where "new_tstp = (if memL (args_ivl args) 0 then Inr tp_i else Inl nt)"
  define tstp_map'' where "tstp_map'' = Mapping.update tp_i nt tstp_map_i"
  define tmp where "tmp = \<Union>((\<lambda>as. case Mapping.lookup a1_map_i (restrict (args_L args) (args_R args) as) of None \<Rightarrow>
      (if \<not>(args_pos args) then {(tp_i - len_i, as)} else {})
      | Some tp' \<Rightarrow> if (args_pos args) then {(max (tp_i - len_i) tp', as)}
      else {(max (tp_i - len_i) (tp' + 1), as)}) ` rel2) \<union> (if memL (args_ivl args) 0 then {tp_i} \<times> rel2 else {})"
  define tmp' where "tmp' = Set.filter (\<lambda>(tp, as). case Mapping.lookup tstp_map' tp of Some ts \<Rightarrow> memL (args_ivl args) (nt - ts)) tmp"
  have "tp_i - len_i \<in> Mapping.keys a2_map_i" using valid_shift(1) by(auto)
  then obtain m where m_def: "Mapping.lookup a2_map_i (tp_i - len_i) = Some m" by transfer auto
  have muaux'_def: "add_new_mmuaux args rel1 rel2 nt ?muaux = ?muaux'"
    using updated_def inter_def[folded valid_shift(2)[symmetric]]
    by (cases "shift_mmuaux args nt (tp, tss, tables, len, result, a1_map, a2_map, tstp_map, done)")
       (auto simp only: add_new_mmauaux.simps add_new_mmuaux_def Let_def split: option.splits)
  have valid_old: "valid_mmuaux args cur ?muaux auxlist" using assms(1) unfolding valid_mmauaux_def valid_mmuaux_def by auto
  have valid_muaux: "valid_mmuaux args nt ?muaux' (update_until args rel1 rel2 nt auxlist)" 
    using valid_add_new_mmuaux[OF valid_old tabs nt_mono] muaux'_def by simp
  show ?thesis
  proof(cases "args_agg args")
    case None
    then show ?thesis using valid_muaux 
      unfolding updated_def valid_mmauaux_def split valid_mmauaux'.simps valid_mmuaux_def 
      by auto
  next
    case aargs: (Some aggargs)
    have upd_defs: "a2_map' = Mapping.update (tp_i + 1) Mapping.empty (upd_nested a2_map_i new_tstp (max_tstp new_tstp) tmp')"
     "done' = done_i" "tp' = tp_i + 1" "len' = len_i + 1"
      using aargs updated_def unfolding tmp'_def tstp_map''_def tmp_def new_tstp_def add_new_mmauaux.simps unfolding inter_def  by(auto)
    have "(tp_i + 1 = tp_i - len_i) = False" by auto
    then obtain m' where m'_def: "Mapping.lookup a2_map' (tp' - len') = Some m'" "m' = (upd_set' m new_tstp (max_tstp new_tstp) {b. (tp_i - len_i, b) \<in> tmp'})"
      using m_def upd_defs(3-4) unfolding upd_defs(1) lookup_update' upd_nested_lookup by auto
    define to_add where "to_add = {b. (tp_i - len_i, b) \<in> tmp' \<and> Mapping.lookup m b = None}"
    have upd_agg: "aggaux' = insert_maggaux' aggargs to_add aggaux_i"
      using m_def aargs updated_def 
      unfolding to_add_def tmp'_def tstp_map''_def tmp_def new_tstp_def add_new_mmauaux.simps inter_def 
      by auto
    have *: "Mapping.keys m \<inter> {b. (tp_i - len_i, b) \<in> tmp' \<and> Mapping.lookup m b = None} = {}" by(auto; transfer; auto)
    have "valid_maggaux' aggargs aggaux' (Mapping.keys m')"
    proof(cases aggaux_i)
      case None
      then show ?thesis unfolding upd_agg by auto
    next
      case (Some a)
      then have **: "valid_maggaux aggargs a (Mapping.keys m)" using aargs valid_shift(1) m_def by auto
      show ?thesis 
      proof(cases "finite to_add")
        case True
        have "Mapping.keys m \<union> {b. (tp_i - len_i, b) \<in> tmp' \<and> Mapping.lookup m b = None} = Mapping.keys m \<union> {b. (tp_i - len_i, b) \<in> tmp'}"
          by(auto; transfer; auto)
        then show ?thesis using valid_insert_maggaux[OF ** _ *] using Some unfolding upd_agg m'_def upd_set'_keys to_add_def by(auto simp del:insert_maggaux.simps split:prod.splits)
      next
        case False
        then show ?thesis using Some unfolding upd_agg by auto
      qed
    qed
    then show ?thesis using valid_muaux m'_def(1) unfolding updated_def valid_mmauaux_def split valid_mmauaux'.simps upd_defs valid_mmuaux_def aargs
      by(simp del:valid_mmuaux'.simps) 
  qed
qed

lemma valid_add_new_mmauaux:
  assumes valid_before: "valid_mmauaux args cur (mmaux, auxs) auxlist"
    and tabs: "table (args_L args) rel1" "table (args_R args) rel2"
    and nt_mono: "nt \<ge> cur"
  shows "valid_mmauaux args nt (add_new_mmauaux args rel1 rel2 nt (mmaux, auxs))
    (update_until args rel1 rel2 nt auxlist)"
  using valid_add_new_mmauaux_unfolded[OF _ tabs nt_mono] valid_before by (cases mmaux) fast

lemma done_empty_valid_mmauaux'_intro:
  assumes "valid_mmauaux' args cur dt
    ((tp, tss, tables, len, result, a1_map, a2_map, tstp_map, done), auxs) auxlist"
  shows "valid_mmauaux' args cur dt'
    ((tp, tss, tables, len, result, a1_map, a2_map, tstp_map, []), auxs)
    (drop (length done) auxlist)"
  using assms sorted_wrt_drop by (auto simp add: drop_map[symmetric] split:option.splits)

lemma valid_eval_mmauaux:
  assumes "valid_mmauaux args cur (mmaux, auxs) auxlist" "nt \<ge> cur"
    "eval_mmauaux' args nt (mmaux, auxs) = (res, aux')" "eval_until (args_ivl args) nt auxlist = (res', auxlist')"
  shows "valid_mmauaux args cur aux' auxlist' \<and> res = map (eval_args_agg args) res'"
proof -
  define I where "I = args_ivl args"
  define pos where "pos = args_pos args"
  have valid_folded: "valid_mmauaux' args cur nt (mmaux, auxs) auxlist"
    using assms(1,2) valid_mmauaux'_mono unfolding valid_mmauaux_def by blast
  obtain tp len tss tables result a1_map a2_map tstp_map "done" auxs' where shift_aux_def:
    "shift_mmauaux args nt (mmaux, auxs) = ((tp, tss, tables, len, result, a1_map, a2_map, tstp_map, done), auxs')"
    by (cases "shift_mmauaux args nt (mmaux, auxs)") auto
  have valid_shift_aux: "valid_mmauaux' args cur nt ((tp, tss, tables, len, result,
    a1_map, a2_map, tstp_map, done), auxs') auxlist"
    "\<And>ts. ts \<in> set (linearize tss) \<Longrightarrow> memR (args_ivl args) (nt - ts)"
    using valid_shift_mmauaux'[OF assms(1)[unfolded valid_mmauaux_def]  assms(2)]
    unfolding shift_aux_def by (auto simp del: valid_mmauaux'.simps)
  have len_done_auxlist: "length done \<le> length auxlist"
    using valid_shift_aux by auto
  have list_all: "\<And>x. x \<in> set (take (length done) auxlist) \<Longrightarrow> check_before I nt x"
    using valid_shift_aux unfolding I_def by auto
  have set_drop_auxlist: "\<And>x. x \<in> set (drop (length done) auxlist) \<Longrightarrow> \<not>check_before I nt x"
    using valid_shift_aux[unfolded valid_mmauaux'.simps valid_mmuaux'.simps]
      list_all2_check_before[OF _ valid_shift_aux(2)] unfolding I_def by fast
  have take_auxlist_takeWhile: "take (length done) auxlist = takeWhile (check_before I nt) auxlist"
    using len_done_auxlist list_all set_drop_auxlist
    by (rule take_takeWhile) assumption+
  have rev_done: "rev done = map (eval_args_agg args) (map proj_thd (take (length done) auxlist))"
    using valid_shift_aux by auto
  then have res'_def: "map (eval_args_agg args) res' = rev done"
    using eval_until_res[OF assms(4)] unfolding take_auxlist_takeWhile I_def by auto
  then have auxlist'_def: "auxlist' = drop (length done) auxlist"
    using eval_until_auxlist'[OF assms(4)] by (metis length_map length_rev)
  have eval_mmuaux_eq: "eval_mmauaux' args nt (mmaux, auxs)  = (rev done, ((tp, tss, tables, len, result,
    a1_map, a2_map, tstp_map, []), auxs'))"
    using shift_aux_def by auto
  show ?thesis
    using assms(3) done_empty_valid_mmauaux'_intro[OF valid_shift_aux(1)]
    unfolding shift_aux_def eval_mmuaux_eq pos_def auxlist'_def res'_def valid_mmauaux_def 
    by (auto simp del:valid_mmuaux'.simps split:option.splits)
qed

interpretation default_mmauaux: muaux valid_mmauaux init_mmauaux add_new_mmauaux length_mmauaux eval_mmauaux'
proof (unfold_locales, goal_cases)
  case (1 L R n aggargs I pos)
  from 1(1-3) show ?case by (rule valid_init_mmauaux)
next
  case (2 args cur aux auxlist rel1 rel2 nt)
  then show ?case by (cases aux) (simp only: valid_add_new_mmauaux)
next
  case (3 args cur aux auxlist)
  then show ?case by (cases aux) (simp only: valid_length_mmauaux)
next
  case (4 args cur aux auxlist nt res aux' res' auxlist')
  then show ?case by (cases aux) (simp only: valid_eval_mmauaux)
qed

end
