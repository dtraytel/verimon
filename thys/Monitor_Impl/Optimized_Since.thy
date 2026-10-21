(*<*)
theory Optimized_Since
  imports Optimized_Common
begin
(*>*)

section \<open>Optimized data structure for Since\<close>

type_synonym 'a mmsaux = "ts \<times> ts \<times>
  (ts \<times> 'a table) queue \<times> (ts \<times> 'a table) queue \<times>
  'a table \<times> 'a wf_table \<times> (('a tuple, ts) mapping) \<times> 'a wf_table \<times> (('a tuple, ts) mapping)"

fun time_mmsaux :: "'a mmsaux \<Rightarrow> ts" where
  "time_mmsaux aux = (case aux of (nt, _) \<Rightarrow> nt)"

fun valid_mmsaux :: "args \<Rightarrow> ts \<Rightarrow> 'a mmsaux \<Rightarrow> 'a Monitor.msaux \<Rightarrow> bool" where
  "valid_mmsaux args cur (nt, gc, data_prev, data_in, table_in, wf_table_in, 
  tuple_in, wf_table_since, tuple_since) ys 
  \<longleftrightarrow>
    set (args_L args) \<subseteq> set (args_R args) \<and>
    distinct (args_L args) \<and>
    distinct (args_R args) \<and>    (\<forall>(t, X) \<in> set ys. table (args_R args) X) \<and>
    table (args_R args) (Mapping.keys tuple_in) \<and>
    table (args_R args) (Mapping.keys tuple_since) \<and>
    (\<forall>as \<in> \<Union>(snd ` (set (linearize data_prev))). wf_tuple (args_R args) as) \<and>
    (\<forall>as \<in> \<Union>(snd ` (set (linearize data_in))). wf_tuple (args_R args) as) \<and>
    cur = nt \<and>
    ts_tuple_rel (set ys) =
    {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union> set (linearize data_in)).
    valid_tuple tuple_since tas} \<and>
    sorted (map fst (linearize data_prev)) \<and>
    (\<forall>t \<in> fst ` set (linearize data_prev). t \<le> nt \<and> \<not> memL (args_ivl args) (nt - t)) \<and>
    sorted (map fst (linearize data_in)) \<and>
    (\<forall>t \<in> fst ` set (linearize data_in). t \<le> nt \<and> memL (args_ivl args) (nt - t)) \<and>
    table_in = Mapping.keys tuple_in \<and>
    wf_table_sig wf_table_in = args_R args \<and>
    wf_table_set wf_table_in = Mapping.keys tuple_in \<and>
    wf_table_sig wf_table_since = args_R args \<and>
    wf_table_set wf_table_since = Mapping.keys tuple_since \<and>
    (\<forall>as. Mapping.lookup tuple_in as = safe_max (fst `
    {tas \<in> ts_tuple_rel (set (linearize data_in)). valid_tuple tuple_since tas \<and> as = snd tas})) \<and>
    (\<forall>as \<in> Mapping.keys tuple_since. case Mapping.lookup tuple_since as of Some t \<Rightarrow> t \<le> nt)"

definition wf_table_of_set_args :: "args \<Rightarrow> 'a table \<Rightarrow> 'a wf_table" where
  "wf_table_of_set_args args X = wf_table_of_idx (wf_idx_of_set (args_R args) (args_L args) X)"

text \<open>
  The two indexed tables are consulted by @{text join_mmsaux} only when there are join columns
  that do not cover all columns. Without join columns (@{term "args_L args = []"}, e.g. for
  @{text ONCE}) and when all columns are join columns (@{term "args_L args = args_R args"}, where
  the join is a plain intersection or difference) they are maintained as the (lazily represented)
  set of keys of the corresponding mapping, which costs nothing per operation in the generated
  code.
\<close>

definition wf_table_of_keys :: "nat list \<Rightarrow> ('a tuple, ts) mapping \<Rightarrow> 'a wf_table" where
  "wf_table_of_keys cs m = wf_table_of_set cs (Mapping.keys m)"

definition wf_table_upd :: "args \<Rightarrow> ('a tuple, ts) mapping \<Rightarrow> (unit \<Rightarrow> 'a wf_table) \<Rightarrow> 'a wf_table" where
  "wf_table_upd args m w = (if args_L args = [] \<or> args_L args = args_R args
    then wf_table_of_keys (args_R args) m else w ())"

fun init_mmsaux :: "args \<Rightarrow> 'a mmsaux" where
  "init_mmsaux args = (0, 0, empty_queue, empty_queue,
  {}, wf_table_of_idx (wf_idx_of_set (args_R args) (args_L args) {}), Mapping.empty,
  wf_table_of_set_args args {}, Mapping.empty)"

fun shift_end :: "args \<Rightarrow> ts \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux"
  where "shift_end args nt (t, gc, data_prev, data_in, table_in, wf_table_in, 
  tuple_in, wf_table_since, tuple_since) =
    (let I = args_ivl args;
    data_prev' = dropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) data_prev;
    (data_in, discard) = takedropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) data_in;
    (tuple_in, del) = fold filter_set discard (tuple_in, {}) in
    (t, gc, data_prev', data_in,
     table_in - del, wf_table_upd args tuple_in (\<lambda>_. wf_table_antijoin wf_table_in (wf_table_of_set_args args del)), tuple_in,
     wf_table_since, tuple_since))"

fun add_new_ts_mmsaux' :: "args \<Rightarrow> ts \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "add_new_ts_mmsaux' args nt (t, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) =
    (let I = args_ivl args;
    (data_prev, move) = takedropWhile_queue (\<lambda>(t, X). memL I (nt - t)) data_prev;
    data_in = fold (\<lambda>(t, X) data_in. append_queue (t, X) data_in) move data_in;
    (tuple_in, add) = fold (upd_set_keys (\<lambda>X t. {as \<in> X. valid_tuple tuple_since (t, as)})) move (tuple_in, {}) in
    (nt, gc, data_prev, data_in, table_in \<union> add, wf_table_upd args tuple_in (\<lambda>_. wf_table_union wf_table_in (wf_table_of_set_args args add)), tuple_in, wf_table_since, tuple_since))"

definition add_new_ts_mmsaux :: "args \<Rightarrow> ts \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "add_new_ts_mmsaux args nt aux = add_new_ts_mmsaux' args nt (shift_end args nt aux)"

fun join_mmsaux :: "args \<Rightarrow> 'a table \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "join_mmsaux args X (t, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) =
    (let pos = args_pos args in
    (if args_L args = [] then
      (let take_all = (pos \<longleftrightarrow> [] \<in> X);
      table_in' = (if take_all then table_in else {});
      wf_table_in' = (if take_all then wf_table_in else wf_table_of_set_args args {});
      tuple_in' = (if take_all then tuple_in else Mapping.empty);
      wf_table_since' = (if take_all then wf_table_since else wf_table_of_set_args args {});
      tuple_since' = (if take_all then tuple_since else Mapping.empty) in
      (t, gc, data_prev, data_in, table_in', wf_table_in', tuple_in', wf_table_since', tuple_since'))
     else if args_L args = args_R args then
      (let in_del = (if pos then table_in - X else table_in \<inter> X);
      tuple_in' = mapping_delete_set tuple_in in_del;
      table_in' = table_in - in_del;
      wf_table_in' = wf_table_upd args tuple_in' (\<lambda>_. wf_table_of_set_args args table_in');
      tuple_since' = Mapping.filter (\<lambda>as _. join_cond pos X as) tuple_since;
      wf_table_since' = wf_table_upd args tuple_since' (\<lambda>_. wf_table_of_set_args args (Mapping.keys tuple_since')) in
      (t, gc, data_prev, data_in, table_in', wf_table_in', tuple_in', wf_table_since', tuple_since'))
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
      (t, gc, data_prev, data_in, table_in', wf_table_in', tuple_in', wf_table_since', tuple_since'))))"

fun join_mmsaux_abs :: "args \<Rightarrow> 'a table \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "join_mmsaux_abs args X (t, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) =
    (let pos = args_pos args in
    (let tuple_in = Mapping.filter (\<lambda>as _. join_cond pos X (restrict (args_L args) (args_R args) as)) tuple_in;
    tuple_since = Mapping.filter (\<lambda>as _. join_cond pos X (restrict (args_L args) (args_R args) as)) tuple_since in
    (t, gc, data_prev, data_in,
     Mapping.keys tuple_in, wf_table_of_set_args args (Mapping.keys tuple_in), tuple_in,
     wf_table_of_set_args args (Mapping.keys tuple_since), tuple_since)))"

fun gc_mmsaux :: "args \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "gc_mmsaux args (nt, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) =
    (let all_tuples = \<Union>(snd ` (set (linearize data_prev) \<union> set (linearize data_in)));
    tuple_since' = Mapping.filter (\<lambda>as _. as \<in> all_tuples) tuple_since in
    (nt, nt, data_prev, data_in, table_in, wf_table_in, tuple_in,
     wf_table_upd args tuple_since' (\<lambda>_. wf_table_of_set_args args (Mapping.keys tuple_since')), tuple_since'))"

fun gc_join_mmsaux :: "args \<Rightarrow> 'a table \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "gc_join_mmsaux args X (t, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) =
    (if \<not> memR (args_ivl args) (t - gc) then join_mmsaux args X (gc_mmsaux args (t, gc,
      data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since))
    else join_mmsaux args X (t, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since))"

definition "minus_keys X m = X - Mapping.keys m"

lemma minus_keys_code[code]: "minus_keys X m = {x \<in> X. case Mapping.lookup m x of None \<Rightarrow> True | _ \<Rightarrow> False}"
  by (auto simp: minus_keys_def Mapping.keys_dom_lookup split: option.splits)

fun add_new_table_mmsaux :: "args \<Rightarrow> 'a table \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "add_new_table_mmsaux args X (t, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) =
    (let X' = (minus_keys X tuple_since);
         tuple_since' = upd_set tuple_since (\<lambda>_. t) X';
         wf_table_since' = wf_table_upd args tuple_since' (\<lambda>_. wf_table_union wf_table_since (wf_table_of_set_args args X')) in
    (if memL (args_ivl args) 0 then
      (t, gc, data_prev, append_queue (t, X) data_in, table_in \<union> X, wf_table_upd args (upd_set tuple_in (\<lambda>_. t) X) (\<lambda>_. wf_table_union wf_table_in (wf_table_of_set_args args X)), upd_set tuple_in (\<lambda>_. t) X, wf_table_since', tuple_since')
    else (t, gc, append_queue (t, X) data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since', tuple_since')))"

fun result_mmsaux :: "args \<Rightarrow> 'a mmsaux \<Rightarrow> 'a table" where
  "result_mmsaux args (nt, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) = table_in"

definition "result_mmsaux' args aux = eval_args_agg args (result_mmsaux args aux)"

end
(*>*)
