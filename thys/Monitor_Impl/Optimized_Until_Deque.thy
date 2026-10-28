(*<*)
theory Optimized_Until_Deque
  imports Optimized_Agg_Temporal "Monitor_Data_Structures.Deque"
begin
(*>*)

section \<open>Until structure with deques\<close>

text \<open>The time-point-indexed mappings of @{theory Monitor_Impl.Optimized_Until} change only at
  the ends of their contiguous key ranges; deques replace them, related by a simulation.\<close>

subsection \<open>Simulation relation\<close>

type_synonym 'a mmuaux_dq = "tp \<times> ts queue \<times> ('a table \<times> (ts + tp)) queue \<times> nat \<times>
  'a table \<times> ('a tuple, tp) mapping \<times> ('a tuple, ts + tp) mapping dq \<times> ts dq \<times> 'a table list"

definition rel_a2 :: "tp \<Rightarrow> nat \<Rightarrow> ('a tuple, ts + tp) mapping dq \<Rightarrow> (tp, ('a tuple, ts + tp) mapping) mapping \<Rightarrow> bool" where
  "rel_a2 tp len d m \<longleftrightarrow> dq_inv d \<and> dq_len d = len + 1 \<and> Mapping.keys m = {tp - len..tp} \<and>
    (\<forall>k \<le> len. Mapping.lookup m (tp - len + k) = Some (dq_nth d k))"

definition rel_tstp :: "tp \<Rightarrow> nat \<Rightarrow> ts dq \<Rightarrow> (tp, ts) mapping \<Rightarrow> bool" where
  "rel_tstp tp len d m \<longleftrightarrow> dq_inv d \<and> dq_len d = len \<and> Mapping.keys m = {tp - len..<tp} \<and>
    (\<forall>k < len. Mapping.lookup m (tp - len + k) = Some (dq_nth d k))"

fun rel_uaux :: "event_data mmuaux_dq \<Rightarrow> event_data mmuaux \<Rightarrow> bool" where
  "rel_uaux (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, done)
     (tp', tss', tables', len', result', a1_map', a2_map, tstp_map, done') \<longleftrightarrow>
   tp' = tp \<and> tss' = tss \<and> tables' = tables \<and> len' = len \<and>
   result' = result \<and> a1_map' = a1_map \<and> done' = done \<and> len \<le> tp \<and>
   rel_a2 tp len a2_dq a2_map \<and> rel_tstp tp len tstp_dq tstp_map"

subsection \<open>Operations\<close>

fun eval_step_dq :: "args \<Rightarrow> event_data mmuaux_dq \<Rightarrow> event_data mmuaux_dq" where
  "eval_step_dq args (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, done) =
    (case safe_hd tss of (Some ts, tss') \<Rightarrow>
      (let m = dq_nth a2_dq 0;
        I = args_ivl args;
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
        a2_dq' = dq_tl a2_dq;
        m' = dq_nth a2_dq' 0;
        result' = if len = 1 then {} else (result - to_del) \<union> Mapping.keys m';
        a2_dq = dq_upd a2_dq' 0 (if len = 1 then Mapping.empty
          else Mapping.combine (\<lambda>tstp tstp'. max_tstp tstp tstp') m'' m');
        tstp_dq = dq_tl tstp_dq in
        (tp, tss'', tables, len - 1, result', a1_map, a2_dq, tstp_dq, T # done)))"

fun shift_dq :: "args \<Rightarrow> ts \<Rightarrow> event_data mmuaux_dq \<Rightarrow> event_data mmuaux_dq" where
  "shift_dq args nt (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, done) =
    (let (tss_queue, tss') = takeWhile_queue (\<lambda>t. \<not> memR (args_ivl args) (nt - t)) tss in
    foldl (\<lambda>aux _. eval_step_dq args aux) (tp, tss', tables, len,
      result, a1_map, a2_dq, tstp_dq, done) (linearize tss_queue))"

fun eval_dq :: "args \<Rightarrow> ts \<Rightarrow> event_data mmuaux_dq \<Rightarrow> event_data table list \<times> event_data mmuaux_dq" where
  "eval_dq args nt aux =
    (let (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, done) = shift_dq args nt aux in
    (rev done, (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, [])))"

definition init_dq :: "args \<Rightarrow> event_data mmuaux_dq" where
  "init_dq args = (0, empty_queue, empty_queue, 0,
  {}, Mapping.empty, dq_push Mapping.empty dq_empty, dq_empty, [])"

fun length_dq :: "args \<Rightarrow> event_data mmuaux_dq \<Rightarrow> nat" where
  "length_dq args (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, done) = length done + len"

subsection \<open>Nested update and conversions\<close>

definition upd_nested_step_dq :: "nat \<Rightarrow> 'c \<Rightarrow> ('c \<Rightarrow> 'c) \<Rightarrow> nat \<times> 'b \<Rightarrow> ('b, 'c) mapping dq \<Rightarrow> ('b, 'c) mapping dq" where
  "upd_nested_step_dq base d f x dq = (case x of (k, k') \<Rightarrow>
    if base \<le> k \<and> k - base < dq_len dq then
      (let i = k - base; m' = dq_nth dq i in
       dq_upd dq i (case Mapping.lookup m' k' of Some v \<Rightarrow> Mapping.update k' (f v) m' | None \<Rightarrow> Mapping.update k' d m'))
    else dq)"

definition upd_nested_dq :: "nat \<Rightarrow> 'c \<Rightarrow> ('c \<Rightarrow> 'c) \<Rightarrow> (nat \<times> 'b) list \<Rightarrow> ('b, 'c) mapping dq \<Rightarrow> ('b, 'c) mapping dq" where
  "upd_nested_dq base d f xs dq = foldr (upd_nested_step_dq base d f) xs dq"

definition a2_of_dq :: "tp \<Rightarrow> nat \<Rightarrow> 'a dq \<Rightarrow> (tp, 'a) mapping" where
  "a2_of_dq tp len dq = Mapping.tabulate [tp - len..<tp + 1] (\<lambda>t. dq_nth dq (t - (tp - len)))"

definition tstp_of_dq :: "tp \<Rightarrow> nat \<Rightarrow> 'a dq \<Rightarrow> (tp, 'a) mapping" where
  "tstp_of_dq tp len dq = Mapping.tabulate [tp - len..<tp] (\<lambda>t. dq_nth dq (t - (tp - len)))"

fun uaux_of_dq :: "event_data mmuaux_dq \<Rightarrow> event_data mmuaux" where
  "uaux_of_dq (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, done) =
    (tp, tss, tables, len, result, a1_map, a2_of_dq tp len a2_dq, tstp_of_dq tp len tstp_dq, done)"

definition dq_of_a2 :: "tp \<Rightarrow> nat \<Rightarrow> (tp, 'a) mapping \<Rightarrow> 'a dq" where
  "dq_of_a2 tp len m = dq_of_list (map (\<lambda>k. the (Mapping.lookup m (tp - len + k))) [0..<len + 1])"

definition dq_of_tstp :: "tp \<Rightarrow> nat \<Rightarrow> (tp, 'a) mapping \<Rightarrow> 'a dq" where
  "dq_of_tstp tp len m = dq_of_list (map (\<lambda>k. the (Mapping.lookup m (tp - len + k))) [0..<len])"

fun dq_of_uaux :: "event_data mmuaux \<Rightarrow> event_data mmuaux_dq" where
  "dq_of_uaux (tp, tss, tables, len, result, a1_map, a2_map, tstp_map, done) =
    (tp, tss, tables, len, result, a1_map, dq_of_a2 tp len a2_map, dq_of_tstp tp len tstp_map, done)"

subsection \<open>Adding a new time point\<close>

text \<open>One fold over the sorted operand table inserts each candidate pair passing the interval
  check into the new table, its deque entry and, at the oldest time point, the result.\<close>

type_synonym 'a until_acc_dq = "'a table \<times> ('a tuple, ts + tp) mapping dq \<times> 'a table"

definition until_step_dq :: "(nat \<Rightarrow> bool) \<Rightarrow> ts + tp \<Rightarrow> nat \<Rightarrow> nat \<times> 'a tuple \<Rightarrow> 'a until_acc_dq \<Rightarrow> 'a until_acc_dq" where
  "until_step_dq P d t0 p acc = (case acc of (tbl, a2, res) \<Rightarrow> if P (fst p) then
     (Set.insert (snd p) tbl, upd_nested_step_dq t0 d (max_tstp d) p a2,
      if fst p = t0 then Set.insert (snd p) res else res)
   else acc)"

definition until_cand :: "('a tuple, nat) mapping \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a tuple \<Rightarrow> (nat \<times> 'a tuple) set" where
  "until_cand a1_map L R pos tp len as = (case Mapping.lookup a1_map (restrict L R as) of None \<Rightarrow>
      (if \<not>pos then {(tp - len, as)} else {})
      | Some tp' \<Rightarrow> if pos then {(max (tp - len) tp', as)}
      else {(max (tp - len) (tp' + 1), as)})"

definition until_pairs_list :: "('a tuple, nat) mapping \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> 'a tuple \<Rightarrow> (nat \<times> 'a tuple) list" where
  "until_pairs_list a1_map L R pos tp len inz as =
    (case Mapping.lookup a1_map (restrict L R as) of
        None \<Rightarrow> (if \<not>pos then [(tp - len, as)] else [])
      | Some tp' \<Rightarrow> [if pos then (max (tp - len) tp', as) else (max (tp - len) (tp' + 1), as)]) @
    (if inz then [(tp, as)] else [])"

definition until_elem_step_dq :: "('a tuple, nat) mapping \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow>
  (nat \<Rightarrow> bool) \<Rightarrow> ts + tp \<Rightarrow> 'a tuple \<Rightarrow> 'a until_acc_dq \<Rightarrow> 'a until_acc_dq" where
  "until_elem_step_dq a1_map L R pos tp len inz P d as acc =
    (let acc' = (if inz then until_step_dq P d (tp - len) (tp, as) acc else acc) in
     case Mapping.lookup a1_map (restrict L R as) of
        None \<Rightarrow> (if \<not>pos then until_step_dq P d (tp - len) (tp - len, as) acc' else acc')
      | Some tp' \<Rightarrow> until_step_dq P d (tp - len) (if pos then (max (tp - len) tp', as) else (max (tp - len) (tp' + 1), as)) acc')"

definition add_new_dq :: "args \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow> event_data mmuaux_dq \<Rightarrow> event_data mmuaux_dq" where
  "add_new_dq args rel1 rel2 nt aux = (if finite rel2 then
    (let (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, done) = shift_dq args nt aux;
    I = args_ivl args; pos = args_pos args; inz = memL I 0;
    new_tstp = (if inz then Inr tp else Inl nt);
    tstp_dq = dq_push nt tstp_dq;
    P = (\<lambda>t. memL I (nt - dq_nth tstp_dq (t - (tp - len))));
    (tbl, a2_dq', result') = fold (until_elem_step_dq a1_map (args_L args) (args_R args) pos tp len inz P new_tstp)
      (csorted_list_of_set rel2) ({}, a2_dq, result);
    tables = append_queue (tbl, new_tstp) tables;
    a2_dq = dq_push Mapping.empty a2_dq';
    a1_map = (if pos then Mapping.filter (\<lambda>as _. as \<in> rel1)
      (upd_set a1_map (\<lambda>_. tp) (rel1 - Mapping.keys a1_map)) else upd_set a1_map (\<lambda>_. tp) rel1);
    tss = append_queue nt tss in
    (tp + 1, tss, tables, len + 1, result', a1_map, a2_dq, tstp_dq, done))
  else dq_of_uaux (add_new_mmuaux args rel1 rel2 nt (uaux_of_dq aux)))"

subsection \<open>Combined Until structure\<close>

datatype muaux_dq = MU_agg mmauaux | MU_dq "event_data mmuaux_dq"

definition init_muaux_dq :: "args \<Rightarrow> muaux_dq" where
  "init_muaux_dq args = (if args_agg args = None then MU_dq (init_dq args) else MU_agg (init_mmauaux args))"

fun add_new_muaux_dq :: "args \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow> muaux_dq \<Rightarrow> muaux_dq" where
  "add_new_muaux_dq args rel1 rel2 nt (MU_dq d) = MU_dq (add_new_dq args rel1 rel2 nt d)"
| "add_new_muaux_dq args rel1 rel2 nt (MU_agg a) = MU_agg (add_new_mmauaux args rel1 rel2 nt a)"

fun length_muaux_dq :: "args \<Rightarrow> muaux_dq \<Rightarrow> nat" where
  "length_muaux_dq args (MU_dq d) = length_dq args d"
| "length_muaux_dq args (MU_agg a) = length_mmauaux args a"

fun eval_muaux_dq :: "args \<Rightarrow> ts \<Rightarrow> muaux_dq \<Rightarrow> event_data table list \<times> muaux_dq" where
  "eval_muaux_dq args nt (MU_dq d) = (let (res, d') = eval_dq args nt d in (res, MU_dq d'))"
| "eval_muaux_dq args nt (MU_agg a) = (let (res, a') = eval_mmauaux' args nt a in (res, MU_agg a'))"

fun valid_muaux_dq :: "args \<Rightarrow> ts \<Rightarrow> muaux_dq \<Rightarrow> event_data muaux \<Rightarrow> bool" where
  "valid_muaux_dq args cur (MU_dq d) auxlist \<longleftrightarrow> (\<exists>a. rel_uaux d a \<and> valid_mmuaux args cur a auxlist)"
| "valid_muaux_dq args cur (MU_agg a) auxlist \<longleftrightarrow> valid_mmauaux args cur a auxlist"

lemma ID_ccompare_etuple_dq: "ID CCOMPARE(event_data tuple) \<noteq> None"
  by (simp add: ccompare_list_def ccompare_option_def ccompare_event_data_def ID_def split: option.splits)

(*<*)
end
(*>*)
