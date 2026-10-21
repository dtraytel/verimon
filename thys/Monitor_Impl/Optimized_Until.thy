(*<*)
theory Optimized_Until
  imports Optimized_Common
begin
(*>*)

subsection \<open>Optimized data structure for Until\<close>

type_synonym tp = nat

type_synonym 'a mmuaux = "tp \<times> ts queue \<times> ('a table \<times> (ts + tp)) queue \<times> nat \<times>
  'a table \<times> ('a tuple, tp) mapping \<times> (tp, ('a tuple, ts + tp) mapping) mapping \<times> (tp, ts) mapping \<times> 'a table list"

definition tstp_lt :: "ts + tp \<Rightarrow> ts \<Rightarrow> tp \<Rightarrow> bool" where
  "tstp_lt tstp ts tp = case_sum (\<lambda>ts'. ts' \<le> ts) (\<lambda>tp'. tp' < tp) tstp"

definition ts_tp_lt :: " \<I> \<Rightarrow> ts \<Rightarrow> tp \<Rightarrow> ts + tp \<Rightarrow> bool" where
  "ts_tp_lt I ts tp tstp = case_sum (\<lambda>ts'. memL I (ts' - ts)) (\<lambda>tp'. tp \<le> tp') tstp"

definition tstp_unpack:: "ts + tp \<Rightarrow> nat" where
  "tstp_unpack tstp = case_sum id id tstp"

fun max_tstp :: "ts + tp \<Rightarrow> ts + tp \<Rightarrow> ts + tp" where
  "max_tstp (Inl ts) (Inl ts') = Inl (max ts ts')"
| "max_tstp (Inr tp) (Inr tp') = Inr (max tp tp')"
| "max_tstp (Inl ts) _ = Inl ts"
| "max_tstp _ (Inl ts) = Inl ts"

definition filter_a1_map :: "bool \<Rightarrow> tp \<Rightarrow> ('a tuple, tp) mapping \<Rightarrow> 'a table" where
  "filter_a1_map pos tp a1_map =
    {xs \<in> Mapping.keys a1_map. case Mapping.lookup a1_map xs of Some tp' \<Rightarrow>
    (pos \<longrightarrow> tp' \<le> tp) \<and> (\<not>pos \<longrightarrow> tp \<le> tp')}"

definition filter_a2_map :: "\<I> \<Rightarrow> ts \<Rightarrow> tp \<Rightarrow> (tp, ('a tuple, ts + tp) mapping) mapping \<Rightarrow>
  'a table" where
  "filter_a2_map I ts tp a2_map = {xs. \<exists>tp' \<le> tp. (case Mapping.lookup a2_map tp' of Some m \<Rightarrow>
    (case Mapping.lookup m xs of Some tstp \<Rightarrow> ts_tp_lt I ts tp tstp | _ \<Rightarrow> False)
    | _ \<Rightarrow> False)}"

definition ivl_restr_a2_map :: "\<I> \<Rightarrow> ts \<Rightarrow> tp \<Rightarrow> (tp, ('a tuple, ts + tp) mapping) mapping \<Rightarrow> bool" where
  "ivl_restr_a2_map I ts tp a2_map = (case Mapping.lookup a2_map tp of Some m \<Rightarrow>
    (\<forall>xs. (case Mapping.lookup m xs of Some tstp \<Rightarrow> ts_tp_lt I ts tp tstp |
                                                             _ \<Rightarrow> True))
    | _ \<Rightarrow> False)"

definition valid_tstp_map :: "ts \<Rightarrow> tp \<Rightarrow> (tp, ts) mapping \<Rightarrow> bool" where
  "valid_tstp_map ts tp tstp_map = (case Mapping.lookup tstp_map tp of
                                   Some ts' \<Rightarrow> ts = ts' |
                                   None \<Rightarrow> False)"

fun triple_eq_pair :: "('a \<times> 'b \<times> 'c) \<Rightarrow> ('a \<times> 'd) \<Rightarrow> ('d \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'd \<Rightarrow> 'c) \<Rightarrow> bool" where
  "triple_eq_pair (t, a1, a2) (ts', tp') f g \<longleftrightarrow> t = ts' \<and> a1 = f tp' \<and> a2 = g ts' tp'"


fun valid_mmuaux' :: "args \<Rightarrow> ts \<Rightarrow> ts \<Rightarrow> event_data mmuaux \<Rightarrow> event_data muaux \<Rightarrow> bool" where
  "valid_mmuaux' args cur dt (tp, tss, tables, len, result, a1_map, a2_map, tstp_map, done) auxlist \<longleftrightarrow>
    set (args_L args) \<subseteq> set (args_R args) \<and>
    distinct (args_L args) \<and>
    distinct (args_R args) \<and>
    len \<le> tp \<and>
    length (linearize tss) = len \<and> sorted (linearize tss) \<and>
    (\<forall>t \<in> set (linearize tss). t \<le> cur \<and> memR (args_ivl args) (cur - t)) \<and>
    table (args_L args) (Mapping.keys a1_map) \<and>
    Mapping.keys tstp_map = (if len > 0 then {tp - len..tp - 1} else {}) \<and>
    Mapping.keys a2_map = {tp - len..tp} \<and>
    sorted (map (tstp_unpack \<circ> snd) (linearize tables)) \<and>
    (\<forall>tstp \<in> set (map snd (linearize tables)). case tstp of Inl ts \<Rightarrow> ts \<le> cur |
                                                            Inr tp' \<Rightarrow> tp' \<le> tp ) \<and>
    list_all (\<lambda>k. isl k \<longleftrightarrow> \<not> memL (args_ivl args) 0) (map snd (linearize tables)) \<and>
    (case Mapping.lookup a2_map (tp - len) of Some m \<Rightarrow> result = Mapping.keys m | _ \<Rightarrow> False) \<and>
    Mapping.lookup a2_map tp = Some Mapping.empty \<and>
    (\<forall>xs \<in> Mapping.keys a1_map. case Mapping.lookup a1_map xs of Some tp' \<Rightarrow> tp' < tp) \<and>
    (\<forall>tp' \<in> Mapping.keys a2_map. case Mapping.lookup a2_map tp' of Some m \<Rightarrow>
      (\<forall>xs \<in> Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow>
        \<exists>(table, tstp') \<in> set (linearize tables). tstp = tstp' \<and> xs \<in> table)) \<and>
    (\<forall>tp' \<in> Mapping.keys a2_map. case Mapping.lookup a2_map tp' of Some m \<Rightarrow>
      table (args_R args) (Mapping.keys m) \<and>
      (\<forall>xs \<in> Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow>
      tstp_lt tstp cur tp \<and> (isl tstp \<longleftrightarrow> \<not> memL (args_ivl args) 0))) \<and>
    length done + len = length auxlist \<and>
    rev done = map (eval_args_agg args) (map proj_thd (take (length done) auxlist)) \<and>
    (\<forall>x \<in> set (take (length done) auxlist). check_before (args_ivl args) dt x) \<and>
    sorted (map fst auxlist) \<and>
    (list_all2 (\<lambda>x y. triple_eq_pair x y (\<lambda>tp'. filter_a1_map (args_pos args) tp' a1_map)
      (\<lambda>ts' tp'. filter_a2_map (args_ivl args) ts' tp' a2_map)) (drop (length done) auxlist)
      (zip (linearize tss) [tp - len..<tp])) \<and>
    list_all (\<lambda>(ts', tp'). ivl_restr_a2_map (args_ivl args) ts' tp' a2_map \<and> valid_tstp_map ts' tp' tstp_map) (zip (linearize tss) [tp - len..<tp])"

definition valid_mmuaux :: "args \<Rightarrow> ts \<Rightarrow> event_data mmuaux \<Rightarrow> event_data muaux \<Rightarrow>
  bool" where
  "valid_mmuaux args cur = valid_mmuaux' args cur cur"

fun eval_step_mmuaux :: "args \<Rightarrow> event_data mmuaux \<Rightarrow> event_data mmuaux" where
  "eval_step_mmuaux args (tp, tss, tables, len, result, a1_map, a2_map, tstp_map, done) =
    (case safe_hd tss of (Some ts, tss') \<Rightarrow>
      (case Mapping.lookup a2_map (tp - len) of Some m \<Rightarrow>
        let I = args_ivl args;
        T = eval_args_agg args result;
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
        a2_map = if len = 1 then Mapping.update tp Mapping.empty a2_map
                 else Mapping.update (tp - len + 1)
          (case Mapping.lookup a2_map (tp - len + 1) of Some m' \<Rightarrow>
          Mapping.combine (\<lambda>tstp tstp'. max_tstp tstp tstp') m'' m') a2_map;
        a2_map = Mapping.delete (tp - len) a2_map;
        tstp_map = Mapping.delete (tp - len) tstp_map in
        (tp, tss'', tables, len - 1, result', a1_map, a2_map, tstp_map, T # done)))"

fun lin_ts_mmuaux :: "event_data mmuaux \<Rightarrow> ts list" where
  "lin_ts_mmuaux (tp, tss, len, result, a1_map, a2_map, done, done_length) =
    linearize tss"

fun shift_mmuaux :: "args \<Rightarrow> ts \<Rightarrow> event_data mmuaux \<Rightarrow> event_data mmuaux" where
  "shift_mmuaux args nt (tp, tss, len, result, a1_map, a2_map, done, done_length) =
    (let (tss_queue, tss') = takeWhile_queue (\<lambda>t. \<not> memR (args_ivl args) (nt - t)) tss in
    foldl (\<lambda>aux _. eval_step_mmuaux args aux) (tp, tss', len,
      result, a1_map, a2_map, done, done_length) (linearize tss_queue))"

lift_definition upd_set' :: "('a, 'b) mapping \<Rightarrow> 'b \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> ('a, 'b) mapping" is
  "\<lambda>m d f X a. (if a \<in> X then (case Mapping.lookup m a of Some b \<Rightarrow> Some (f b) | None \<Rightarrow> Some d)
    else Mapping.lookup m a)" .

lift_definition upd_nested :: "('a, ('b, 'c) mapping) mapping \<Rightarrow>
  'c \<Rightarrow> ('c \<Rightarrow> 'c) \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> ('a, ('b, 'c) mapping) mapping" is
  "\<lambda>m d f X a. case Mapping.lookup m a of Some m' \<Rightarrow> Some (upd_set' m' d f {b. (a, b) \<in> X})
  | None \<Rightarrow> if a \<in> fst ` X then Some (upd_set' Mapping.empty d f {b. (a, b) \<in> X}) else None" .

definition add_new_mmuaux :: "args \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow> event_data mmuaux \<Rightarrow> event_data mmuaux" where
  "add_new_mmuaux args rel1 rel2 nt aux =
    (let (tp, tss, tables, len, result, a1_map, a2_map, tstp_map, done) =
    shift_mmuaux args nt aux;
    I = args_ivl args; pos = args_pos args;
    new_tstp = (if memL I 0 then Inr tp else Inl nt);
    tstp_map = Mapping.update tp nt tstp_map;
    tmp = \<Union>((\<lambda>as. case Mapping.lookup a1_map (restrict (args_L args) (args_R args) as) of None \<Rightarrow>
      (if \<not>pos then {(tp - len, as)} else {})
      | Some tp' \<Rightarrow> if pos then {(max (tp - len) tp', as)}
      else {(max (tp - len) (tp' + 1), as)}) ` rel2) \<union> (if memL I 0 then {tp} \<times> rel2 else {});
    tmp = Set.filter (\<lambda>(tp, as). case Mapping.lookup tstp_map tp of Some ts \<Rightarrow> memL I (nt - ts)) tmp;
    table = snd ` tmp;
    tables = append_queue (table, if memL I 0 then Inr tp else Inl nt) tables;
    a2_map = Mapping.update (tp + 1) Mapping.empty
      (upd_nested a2_map new_tstp (max_tstp new_tstp) tmp);
    a1_map = (if pos then Mapping.filter (\<lambda>as _. as \<in> rel1)
      (upd_set a1_map (\<lambda>_. tp) (rel1 - Mapping.keys a1_map)) else upd_set a1_map (\<lambda>_. tp) rel1);
    tss = append_queue nt tss in
    (tp + 1, tss, tables, len + 1, result \<union> snd ` (Set.filter (\<lambda>(t, x). t = tp - len) tmp), a1_map, a2_map, tstp_map, done))"

fun eval_mmuaux' :: "args \<Rightarrow> ts \<Rightarrow> event_data mmuaux \<Rightarrow> event_data table list \<times> event_data mmuaux" where
  "eval_mmuaux' args nt aux =
    (let (tp, tss, tables, len, result, a1_map, a2_map, tstp_map, done) =
    shift_mmuaux args nt aux in
    (rev done, (tp, tss, tables, len, result, a1_map, a2_map, tstp_map, [])))"

definition init_mmuaux :: "args \<Rightarrow> event_data mmuaux" where
  "init_mmuaux args = (0, empty_queue, empty_queue, 0,
  {}, Mapping.empty, Mapping.update 0 Mapping.empty Mapping.empty, Mapping.empty, [])"

fun length_mmuaux :: "args \<Rightarrow> event_data mmuaux \<Rightarrow> nat" where
  "length_mmuaux args (tp, tss, tables, len, result, a1_map, a2_map, tstp_map, done) =
    length done + len"

end
(*>*)
