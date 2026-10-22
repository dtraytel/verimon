(*<*)
theory Optimized_Trigger
  imports Optimized_Common
begin
(*>*)

subsection \<open>Optimized data structure for Trigger\<close>

(* simply stores all tables for \<phi> and \<psi> in [0, b] *)
type_synonym 'a mtaux = "(ts \<times> 'a table \<times> 'a table) list"

definition time :: "(ts \<times> 'a table \<times> 'a table) \<Rightarrow> ts" where
  "time = fst"

definition relL :: "(ts \<times> 'a table \<times> 'a table) \<Rightarrow> 'a table" where
  "relL = (fst o snd)"

definition relR :: "(ts \<times> 'a table \<times> 'a table) \<Rightarrow> 'a table" where
  "relR = (snd o snd)"

type_synonym 'a mmtaux = "
  ts \<times>                                 \<comment> \<open>the newest timestamp\<close>
  nat \<times> nat \<times> nat \<times>                   \<comment> \<open>index of the first queue entry in data_prev, data_in and the last index of data_in\<close>
  (ts \<times> 'a table \<times> 'a table) queue \<times>  \<comment> \<open>data_prev: all databases containing the tuples satisfying the lhs or the rhs where the timestamp doesn't yet satisfy memL\<close>
  (ts \<times> 'a table) queue \<times>              \<comment> \<open>data_in: all databases containing the tuples satisfying the rhs where the ts is in the interval\<close>
  (('a tuple, ts) mapping) \<times>           \<comment> \<open>tuple_in for once\<close>
  'a table \<times>                            \<comment> \<open>Mapping.keys tuple_in_once, just here for performance improvements\<close>
  (('a tuple, nat) mapping) \<times>          \<comment> \<open>tuple_since for historically. stores the index since when the rhs of the formula holds\<close>
  ('a table) \<times>
  ('a table)                            \<comment> \<open>the set of tuples currently satisfying \<psi> S_[0, \<infinity>] (\<psi> \<and> \<phi>)\<close>
"

fun mmtaux_data_prev :: "'a mmtaux \<Rightarrow> (ts \<times> 'a table \<times> 'a table) queue" where
  "mmtaux_data_prev (_, _, _, _, data_prev, _) = data_prev"

fun mmtaux_data_in :: "'a mmtaux \<Rightarrow> (ts \<times> 'a table) queue" where
  "mmtaux_data_in (_, _, _, _, _, data_in, _) = data_in"

definition ts_tuple_rel_binary :: "(ts \<times> 'a table \<times> 'a table) set \<Rightarrow> (ts \<times> 'a tuple \<times> 'a tuple) set" where
  "ts_tuple_rel_binary ys = {(t, as, bs). \<exists>X Y. as \<in> X \<and> bs \<in> Y \<and> (t, X, Y) \<in> ys}"

abbreviation "ts_tuple_rel_binary_lhs \<equiv> ts_tuple_rel_f fst"
abbreviation "ts_tuple_rel_binary_rhs \<equiv> ts_tuple_rel_f snd"

definition auxlist_data_prev :: "args \<Rightarrow> ts \<Rightarrow> (ts \<times> 'a table \<times> 'a table) list \<Rightarrow> (ts \<times> 'a table \<times> 'a table) list" where
  "auxlist_data_prev args mt auxlist = filter (\<lambda>(t, _). \<not>memL (args_ivl args) (mt - t)) auxlist"

definition auxlist_data_in :: "args \<Rightarrow> ts \<Rightarrow> (ts \<times> 'a table \<times> 'a table) list \<Rightarrow> (ts \<times> 'a table \<times> 'a table) list" where
  "auxlist_data_in args mt auxlist = filter (\<lambda>(t, _). mem (args_ivl args) (mt - t)) auxlist"

definition tuple_since_tp where
  "tuple_since_tp args as lin_data_in idx_oldest idx_mid idx = (
    (lin_data_in \<noteq> []) \<and>
    idx < idx_mid \<and>
    (\<forall>(t, r) \<in> set (drop (idx-idx_oldest) lin_data_in). 
      as \<in> r
    ) \<and>
    (idx > idx_oldest \<longrightarrow> as \<notin> (snd (lin_data_in!(idx-idx_oldest-1))))
  )"

definition proj_tuple_in_join :: "bool \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> 'a tuple \<Rightarrow> 'a table \<Rightarrow> bool" where
  "proj_tuple_in_join pos L R as t = join_cond pos t (restrict L R as)"

definition tuple_since_lhs where
  "tuple_since_lhs tuple lin_data_in args auxlist_in = ((lin_data_in \<noteq> []) \<and> ( \<comment> \<open>with an empty data_in, all tuples satisfy trigger\<close>
    \<exists>n \<in> {0..<length lin_data_in}. \<comment> \<open>dropping less then length guarantees length suffix > 0\<close>
      let suffix = drop n auxlist_in in (
        (\<forall>(t, l, r) \<in> set suffix.
          tuple \<in> r
        ) \<and>
        (
          join_cond (args_pos args) (relL (hd suffix)) (restrict (args_L args) (args_R args) tuple)
        )
    )
  ))"

definition valid_nmtaux :: "args \<Rightarrow> ts \<Rightarrow> 'a mmtaux \<Rightarrow> 'a mtaux \<Rightarrow> bool" where
  "valid_nmtaux args cur = (\<lambda>(mt, idx_next, idx_mid, idx_oldest, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) auxlist.
    (if mem (args_ivl args) 0 then set (args_L args) \<subseteq> set (args_R args) else (args_L args) = (args_R args)) \<and>
    (\<not>mem (args_ivl args) 0 \<longrightarrow> args_pos args) \<and>
    distinct (args_L args) \<and>
    distinct (args_R args) \<and>
    (\<forall>(t, relL, relR) \<in> set auxlist. table (args_L args) relL \<and> table (args_R args) relR) \<and>
    table (args_L args) (Mapping.keys tuple_in_once) \<and>
    table (args_R args) (Mapping.keys tuple_since_hist) \<and>
    (\<forall>as \<in> \<Union>((relL) ` (set (linearize data_prev))). wf_tuple (args_L args) as) \<and>
    (\<forall>as \<in> \<Union>((relR) ` (set (linearize data_prev))). wf_tuple (args_R args) as) \<and>
    (\<forall>as \<in> \<Union>((snd) ` (set (linearize data_in))). wf_tuple (args_R args) as) \<and>
    cur = mt \<and>
    \<comment> \<open>all valid rhs/\<psi> tuples in data_in should have a valid entry in tuple_since_hist, as it is shifted\<close>
    ts_tuple_rel_binary_rhs (set (auxlist_data_in args mt auxlist)) =
    ts_tuple_rel (set (linearize data_in)) \<and>
    \<comment> \<open>the entries stored should be the same, hence they're sorted as well\<close>
    sorted (map fst auxlist) \<and>
    auxlist_data_prev args mt auxlist = (linearize data_prev) \<and>
    auxlist_data_prev args mt auxlist = drop (length (linearize data_in)) auxlist \<and>
    length (linearize data_prev) + idx_mid = idx_next  \<and>  \<comment> \<open>length (linearize data_prev) = idx_next - idx_mid\<close>
    map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = (linearize data_in) \<and>
    auxlist_data_in args mt auxlist = take (length (linearize data_in)) auxlist \<and>
    length (linearize data_in) + idx_oldest = idx_mid \<and> \<comment> \<open>length (linearize data_in) = idx_mid - idx_oldest\<close>
    \<comment> \<open>also all tuples in auxlist (and hence data_prev/data_in) satisfy memR \<close>
    (\<forall>db \<in> set auxlist. time db \<le> mt \<and> memR (args_ivl args) (mt - time db)) \<and>
     \<comment> \<open>check whether tuple_in once contains the newest occurence of the tuple satisfying the lhs\<close>
    newest_tuple_in_mapping fst data_prev tuple_in_once (\<lambda>x. True) \<and>
    (\<forall>as \<in> Mapping.keys tuple_in_once. case Mapping.lookup tuple_in_once as of Some t \<Rightarrow> \<exists>l r. (t, l, r) \<in> set (linearize data_prev) \<and> join_cond (args_pos args) l as) \<and>
    (\<forall>as. (case Mapping.lookup tuple_since_hist as of
      Some idx \<Rightarrow> tuple_since_tp args as (linearize data_in) idx_oldest idx_mid idx
      | None   \<Rightarrow> \<forall>idx. \<not>tuple_since_tp args as (linearize data_in) idx_oldest idx_mid idx)
    ) \<and>
    \<comment> \<open>conditions for sat / trigger conditions\<close>
    (\<forall>tuple. tuple \<in> hist_sat \<longleftrightarrow>
      (\<not>Queue.is_empty data_in) \<and> ( \<comment> \<open>with an empty data_in, all tuples satisfy trigger\<close>
        \<forall>(t, l, r) \<in> set (auxlist_data_in args mt auxlist). tuple \<in> r
    )) \<and>
    (\<forall>tuple. tuple \<in> since_sat \<longrightarrow>
      ((tuple \<in> hist_sat) \<or> tuple_since_lhs tuple (linearize data_in) args (auxlist_data_in args mt auxlist))
    ) \<and>
    (\<forall>tuple. tuple_since_lhs tuple (linearize data_in) args (auxlist_data_in args mt auxlist) \<longrightarrow>
      tuple \<in> since_sat
    ) \<and>
    tuple_in_once_keys = Mapping.keys tuple_in_once)
  "

definition init_mmtaux :: "args \<Rightarrow> 'a mmtaux" where
  "init_mmtaux args = (0, 0, 0, 0, empty_queue, empty_queue, Mapping.empty, {}, Mapping.empty, {}, {})"

fun result_nmtaux :: "args \<Rightarrow> event_data mmtaux \<Rightarrow> (nat list \<times> event_data table)" where
  "result_nmtaux args (mt, idx_next, idx_mid, idx_oldest, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) = 
  (
    \<comment> \<open>with an empty data_in, all tuples satisfy trigger\<close>
    if (Queue.is_empty data_in) then
      ([], unit_table)
    else
      (args_R args, tuple_in_once_keys \<union> hist_sat \<union> since_sat)
  )
"

fun proj_tuple_in_join_optim :: "bool \<Rightarrow> 'a table \<Rightarrow> nat list \<Rightarrow> 'a table \<Rightarrow> nat list \<Rightarrow> 'a table" where
  "proj_tuple_in_join_optim pos r R l L = (
    if L = R then (
      if pos then r \<inter> l else r - l 
    )
    else if L = [] then (
      \<comment> \<open>if there are no free variables then we either take all or nothing\<close>
      if pos \<longleftrightarrow> [] \<in> l then r else {}
    )
    else
      {as \<in> r. proj_tuple_in_join pos L R as l}
    )"

fun shift_end' where "shift_end' I nt to_table (data_prev, data_in, tuple_in, tuple_in_keys) =
    (let
      data_prev = dropWhile_queue (\<lambda>(t, _). \<not> memR I (nt - t)) data_prev;
      (data_in, in_discard) = takedropWhile_queue (\<lambda>(t, _). \<not> memR I (nt - t)) data_in;
      (tuple_in, tuple_in_keys') = fold (\<lambda>(t, X) (tuple_in, tuple_in_keys). (
        (
          Mapping.filter (filter_cond (to_table X) tuple_in t) tuple_in,
          {as \<in> tuple_in_keys. (filter_cond' (to_table X) tuple_in t) as}
        )
      )) in_discard (tuple_in, tuple_in_keys) in
      (data_prev, data_in, in_discard, tuple_in, tuple_in_keys')
    )"

definition update_nmtaux' :: "args \<Rightarrow> ts \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (ts \<times> 'a table \<times> 'a table) queue \<Rightarrow> (ts \<times> 'a table) queue \<Rightarrow> (('a tuple, ts) mapping) \<Rightarrow> 'a table \<Rightarrow> (('a tuple, nat) mapping) \<Rightarrow> 'a table \<Rightarrow> 'a table \<Rightarrow> (nat \<times> nat \<times> (ts \<times> 'a table \<times> 'a table) queue \<times> (ts \<times> 'a table) queue \<times> (('a tuple, ts) mapping) \<times> 'a table \<times> (('a tuple, nat) mapping) \<times> 'a table \<times> 'a table)" where
  "update_nmtaux' args nt idx_mid idx_oldest data_prev data_in tuple_in_once tuple_in_once_keys tuple_since_hist hist_sat since_sat = (
    \<comment> \<open>in a first step, we update tuple_in_once by removing all tuples where currently a ts
       is stored, that points to a db that with the new ts (nt) no longer is part of
       [0, a-1] / data_prev\<close>
    let (_, data_prev', move, tuple_in_once', tuple_in_once_keys') = shift_end'
      (flip_int_less_lower (args_ivl args)) \<comment> \<open>[0, a-1]\<close>
      nt  \<comment> \<open>the new timestamp\<close>
      fst \<comment> \<open>here we look at the lhs tuples / \<phi>\<close>
      (empty_queue::(ts \<times> 'a list set \<times> 'a list set) queue, data_prev, tuple_in_once, tuple_in_once_keys); \<comment> \<open>add type\<close>
    \<comment> \<open>pass empty_queue as the first argument as it would filter out all: [0, a-1] \<inter> [a, b] = {}.
       idx_mid can be moved forward by the number of all tuples dropped from data_prev (move)\<close>
    move_len = length move;
    idx_mid' = idx_mid + move_len;
    \<comment> \<open>in a next step, we drop all entries from data_in that are no longer relevant \<close>
    (data_in', drop) = takedropWhile_queue (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) data_in;
     \<comment> \<open>instead of first appending and then filtering, we filter move separately. this saves us the append
       operation for all entries in move\<close>
    move' = filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) move;
    \<comment> \<open>idx_ildest has to be moved forward by the number of dbs dropped from data_in and the ones
        dropped from data_prev because they don't satisfy memR anymore (move')\<close>
    drop_prev_len = move_len - length move';
    idx_oldest' = idx_oldest + length drop + drop_prev_len;
    
    \<comment> \<open>next, the right hand side of entries in move have to be appended to data_in. these all already
       satisfy memR as we just filtered them for it\<close>
    data_in'' = fold (\<lambda>(t, l, r) data_in. append_queue (t, r) data_in) move' data_in';
    
    \<comment> \<open>we now have to update hist_since using the tables in move. in particular, for all dbs inside move,
       we have to do some sort of join with the keys of hist_since\<close>
    (tuple_since_hist', hist_sat', idx_move, since_sat') = fold (\<lambda>(t, l, r) (tuple_since_hist, hist_sat, idx_move, since_sat).
      let tuple_since_hist = Mapping.filter (\<lambda>as _. as \<in> r) tuple_since_hist;
          hist_sat         = hist_sat \<inter> r;
          since_sat        = since_sat \<inter> r

      in \<comment> \<open>filter entries that are not present in the current db\<close>
      (
        upd_set tuple_since_hist (\<lambda>_. idx_move) (r - Mapping.keys tuple_since_hist), \<comment> \<open>then add entries for the ones that are present in the current db\<close>
        hist_sat,
        idx_move+1, \<comment> \<open>increase index by one every db\<close>
        since_sat \<union> proj_tuple_in_join_optim (args_pos args) r (args_R args) l (args_L args)
      ) 
    ) move (tuple_since_hist, hist_sat, idx_mid, since_sat); \<comment> \<open>use original idx_mid, not idx_mid' where the length of move already is included\<close>
    tuple_since_hist'' = (if (idx_mid' = idx_oldest') then Mapping.empty else tuple_since_hist'); \<comment> \<open>if data_in'' is empty, empty the mapping\<close>
    since_sat'' = (if (idx_mid' = idx_oldest') then {} else since_sat');
    \<comment> \<open>in contrast to mmsaux, we don't have to look at what tuples were dropped from data_in as
       we do not have any 'in mappings', just 'since mappings'. What has to be done though,
       is to check whether there are now new tuples that satisfy historically.
       In order to do this, we look at the latest db, iterate over all tuples and check,
       whether hist_since points to an index that is older than the current oldest ts, i.e.
       whether the rhs is satisfied in the whole interval\<close>
    hist_sat'' = (case fst (safe_hd data_in'')
      of None \<Rightarrow>
        {} \<comment> \<open>if data_in is empty, no tuples should be in the set.
              (mmtaux only returns results if data_in isn't empty)\<close>
      | Some db \<Rightarrow>
        \<comment> \<open>select all tuples where tuple_since_hist points to the smallest ts\<close>
        hist_sat' \<union> {tuple \<in> (snd db).
          case (Mapping.lookup tuple_since_hist'' tuple) of
            Some idx \<Rightarrow> idx \<le> idx_oldest'
          | None \<Rightarrow> False
        }
    )
    in
    (idx_mid', idx_oldest', data_prev', data_in'', tuple_in_once', tuple_in_once_keys', tuple_since_hist'', hist_sat'', since_sat'')
  )"

definition update_nmtaux :: "args \<Rightarrow> ts \<Rightarrow> 'a table \<Rightarrow> 'a table \<Rightarrow> 'a mmtaux \<Rightarrow> 'a mmtaux" where
  "update_nmtaux args nt l r = (\<lambda>(cur, idx_next, idx_mid, idx_oldest, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat). (
  let (idx_mid', idx_oldest', data_prev', data_in', tuple_in_once', tuple_in_once_keys', tuple_since_hist', hist_sat', since_sat') =
    update_nmtaux' args nt idx_mid idx_oldest data_prev data_in tuple_in_once tuple_in_once_keys tuple_since_hist hist_sat since_sat
  in (
    if mem (args_ivl args) 0 then (
      let tuple_since_hist'' = Mapping.filter (\<lambda>as _. as \<in> r) tuple_since_hist' in
        (
          nt,
          idx_next+1,
          idx_mid'+1,
          idx_oldest',
          data_prev',
          (append_queue (nt, r) data_in'),
          tuple_in_once',
          tuple_in_once_keys',
          upd_set tuple_since_hist'' (\<lambda>_. idx_mid') (r - Mapping.keys tuple_since_hist''),
          (if Queue.is_empty data_in' then r else hist_sat' \<inter> r),
          (since_sat' \<inter> r) \<union> {as \<in> r. proj_tuple_in_join (args_pos args) (args_L args) (args_R args) as l}
        )
      )
    else
      (
        nt,
        idx_next+1,
        idx_mid',
        idx_oldest',
        append_queue (nt, l, r) data_prev',
        data_in',
        upd_set tuple_in_once' (\<lambda>_. nt) l,
        tuple_in_once_keys' \<union> l,
        tuple_since_hist',
        hist_sat',
        since_sat'
      )
  )))"

subsection \<open>Left-hand tables over the right-hand columns\<close>

text \<open>If the interval does not contain 0, the monitor only guarantees that the two column
  lists are permutations of each other, while the structure above requires them to be equal.
  In that case, the structure stores the left-hand tables reordered to the right-hand columns.\<close>

definition trigger_args :: "args \<Rightarrow> args" where
  "trigger_args args = (if mem (args_ivl args) 0 then args else args\<lparr>args_L := args_R args\<rparr>)"

definition trigger_lhs :: "args \<Rightarrow> 'a table \<Rightarrow> 'a table" where
  "trigger_lhs args l = (if mem (args_ivl args) 0 \<or> args_L args = args_R args then l
    else restrict (args_R args) (args_L args) ` l)"

definition valid_mmtaux :: "args \<Rightarrow> ts \<Rightarrow> event_data mmtaux \<Rightarrow> event_data mtaux \<Rightarrow> bool" where
  "valid_mmtaux args cur aux auxlist \<longleftrightarrow>
    (if mem (args_ivl args) 0 then set (args_L args) \<subseteq> set (args_R args) else set (args_L args) = set (args_R args)) \<and>
    distinct (args_L args) \<and> distinct (args_R args) \<and>
    (\<forall>(t, l, r) \<in> set auxlist. table (args_L args) l) \<and>
    valid_nmtaux (trigger_args args) cur aux (map (\<lambda>(t, l, r). (t, trigger_lhs args l, r)) auxlist)"

definition update_mmtaux :: "args \<Rightarrow> ts \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> event_data mmtaux \<Rightarrow> event_data mmtaux" where
  "update_mmtaux args nt l r aux = update_nmtaux (trigger_args args) nt (trigger_lhs args l) r aux"

definition result_mmtaux :: "args \<Rightarrow> event_data mmtaux \<Rightarrow> nat list \<times> event_data table" where
  "result_mmtaux args aux = result_nmtaux (trigger_args args) aux"

end
(*>*)
