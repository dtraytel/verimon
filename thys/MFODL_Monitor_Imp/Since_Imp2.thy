(*<*)
theory Since_Imp2
  imports Table_Imp Optimized_Since_Imp
begin
(*>*)

section \<open>The Since structure over heap-resident maps\<close>

text \<open>
  The same structure as @{theory MFODL_Monitor_Imp.Optimized_Since_Imp}, but over the maps of
  @{theory MFODL_Monitor_Imp.Table_Imp} instead of the generic hash map of the separation-logic
  library, and without proofs. The two tuple-keyed mappings live on the heap and are updated in
  place; the window queues and the result table stay pure, because the evaluation function
  stores the operand tables in the window and hands the result to the front end.

  Definitions only. Nothing here is related to the pure structure; the monitor built on it is
  checked against the verified kernel by differential testing.
\<close>

subsection \<open>Loops over the tables of a step\<close>

partial_function (heap) filter_loop2 ::
  "ts \<Rightarrow> event_data tuple list \<Rightarrow> ts imap \<Rightarrow> event_data table \<Rightarrow> (ts imap \<times> event_data table) Heap" where
  [code]:
  "filter_loop2 t xs h Y = (case xs of [] \<Rightarrow> return (h, Y)
    | x # r \<Rightarrow> (let hx = ihash x in
        do { v \<leftarrow> im_lookup_h h hx x;
             if v = Some t then do { h \<leftarrow> im_delete_h h hx x; filter_loop2 t r h (Set.insert x Y) }
             else filter_loop2 t r h Y }))"

partial_function (heap) expire_loop2 ::
  "(ts \<times> event_data table) list \<Rightarrow> ts imap \<Rightarrow> event_data table \<Rightarrow> (ts imap \<times> event_data table) Heap" where
  [code]:
  "expire_loop2 xs h Y = (case xs of [] \<Rightarrow> return (h, Y)
    | tX # r \<Rightarrow> do { p \<leftarrow> filter_loop2 (fst tX) (csorted_list_of_set (snd tX)) h Y;
                      expire_loop2 r (fst p) (snd p) })"

partial_function (heap) upd_loop2 ::
  "ts \<Rightarrow> event_data tuple list \<Rightarrow> ts imap \<Rightarrow> ts imap \<Rightarrow> event_data table \<Rightarrow> (ts imap \<times> event_data table) Heap" where
  [code]:
  "upd_loop2 t xs hs h Y = (case xs of [] \<Rightarrow> return (h, Y)
    | x # r \<Rightarrow> (let hx = ihash x in
        do { v \<leftarrow> im_lookup_h hs hx x;
             (case v of None \<Rightarrow> upd_loop2 t r hs h Y
              | Some t' \<Rightarrow> if t' \<le> t
                  then do { h \<leftarrow> im_update_h h hx x t; upd_loop2 t r hs h (Set.insert x Y) }
                  else upd_loop2 t r hs h Y) }))"

partial_function (heap) move_loop2 ::
  "(ts \<times> event_data table) list \<Rightarrow> ts imap \<Rightarrow> ts imap \<Rightarrow> event_data table \<Rightarrow> (ts imap \<times> event_data table) Heap" where
  [code]:
  "move_loop2 xs hs h Y = (case xs of [] \<Rightarrow> return (h, Y)
    | tX # r \<Rightarrow> do { p \<leftarrow> upd_loop2 (fst tX) (csorted_list_of_set (snd tX)) hs h Y;
                      move_loop2 r hs (fst p) (snd p) })"

partial_function (heap) del_loop2 ::
  "(event_data tuple \<Rightarrow> bool) \<Rightarrow> event_data tuple list \<Rightarrow> ts imap \<Rightarrow> ts imap Heap" where
  [code]:
  "del_loop2 p ks h = (case ks of [] \<Rightarrow> return h
    | k # r \<Rightarrow> if p k then del_loop2 p r h else do { h \<leftarrow> im_delete h k; del_loop2 p r h })"

partial_function (heap) ins_loop2 :: "ts \<Rightarrow> event_data tuple list \<Rightarrow> ts imap \<Rightarrow> ts imap Heap" where
  [code]:
  "ins_loop2 t xs h = (case xs of [] \<Rightarrow> return h
    | x # r \<Rightarrow> do { h \<leftarrow> im_update h x t; ins_loop2 t r h })"

partial_function (heap) since_loop2 :: "ts \<Rightarrow> event_data tuple list \<Rightarrow> ts imap \<Rightarrow> ts imap Heap" where
  [code]:
  "since_loop2 t xs h = (case xs of [] \<Rightarrow> return h
    | x # r \<Rightarrow> (let hx = ihash x in
        do { v \<leftarrow> im_lookup_h h hx x;
             h \<leftarrow> (if v = None then im_update_h h hx x t else return h);
             since_loop2 t r h }))"

subsection \<open>Operations\<close>

type_synonym msaux2 = "event_data mmsaux_core \<times> ts imap \<times> ts imap"

definition init2 :: "args \<Rightarrow> msaux2 Heap" where
  "init2 args = do { hin \<leftarrow> im_new 16; hsince \<leftarrow> im_new 16;
     return ((0, 0, join_mask (args_n args) (args_L args), join_mask (args_n args) (args_R args),
       empty_queue, empty_queue, {}), hin, hsince) }"

definition shift_end2 :: "args \<Rightarrow> ts \<Rightarrow> msaux2 \<Rightarrow> msaux2 Heap" where
  "shift_end2 args nt q = (case q of ((t, gc, mL, mR, dp, di, tin), hin, hsince) \<Rightarrow>
    (let I = args_ivl args;
         dp' = dropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) dp;
         p = takedropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) di
     in do { r \<leftarrow> expire_loop2 (snd p) hin {};
             return ((t, gc, mL, mR, dp', fst p, tin - snd r), fst r, hsince) }))"

definition add_new_ts2' :: "args \<Rightarrow> ts \<Rightarrow> msaux2 \<Rightarrow> msaux2 Heap" where
  "add_new_ts2' args nt q = (case q of ((t, gc, mL, mR, dp, di, tin), hin, hsince) \<Rightarrow>
    (let I = args_ivl args;
         p = takedropWhile_queue (\<lambda>(t, X). memL I (nt - t)) dp;
         di' = fold append_queue (snd p) di
     in do { r \<leftarrow> move_loop2 (snd p) hsince hin {};
             return ((nt, gc, mL, mR, fst p, di', tin \<union> snd r), fst r, hsince) }))"

definition add_new_ts2 :: "args \<Rightarrow> ts \<Rightarrow> msaux2 \<Rightarrow> msaux2 Heap" where
  "add_new_ts2 args nt q = do { q \<leftarrow> shift_end2 args nt q; add_new_ts2' args nt q }"

definition gc2 :: "msaux2 \<Rightarrow> msaux2 Heap" where
  "gc2 q = (case q of ((t, gc, mL, mR, dp, di, tin), hin, hsince) \<Rightarrow>
     (let all = fold (\<lambda>p acc. snd p \<union> acc) (linearize dp @ linearize di) {} in
      do { hsince \<leftarrow> im_filter (\<lambda>k. k \<in> all) hsince;
           return ((t, t, mL, mR, dp, di, tin), hin, hsince) }))"

definition join2 :: "args \<Rightarrow> event_data table \<Rightarrow> msaux2 \<Rightarrow> msaux2 Heap" where
  "join2 args X q = (case q of ((t, gc, mL, mR, dp, di, tin), hin, hsince) \<Rightarrow>
    (let pos = args_pos args in
     if (\<forall>i \<in> set mL. \<not> i) then
       (if (pos \<longleftrightarrow> replicate (length mL) None \<in> X) then return q
        else do { hin \<leftarrow> im_new 16; hsince \<leftarrow> im_new 16;
                  return ((t, gc, mL, mR, dp, di, {}), hin, hsince) })
     else (let in_del = (if pos then tin - X else tin \<inter> X) in
       do { hin \<leftarrow> del_loop2 (\<lambda>k. k \<notin> in_del) (csorted_list_of_set in_del) hin;
            hsince \<leftarrow> im_filter (jc pos X) hsince;
            return ((t, gc, mL, mR, dp, di, tin - in_del), hin, hsince) })))"

definition gc_join2 :: "args \<Rightarrow> event_data table \<Rightarrow> msaux2 \<Rightarrow> msaux2 Heap" where
  "gc_join2 args X q = (case q of ((t, gc, mL, mR, dp, di, tin), hin, hsince) \<Rightarrow>
    if \<not> memR (args_ivl args) (t - gc) then do { q \<leftarrow> gc2 q; join2 args X q } else join2 args X q)"

definition add_new_table2 :: "args \<Rightarrow> event_data table \<Rightarrow> msaux2 \<Rightarrow> msaux2 Heap" where
  "add_new_table2 args X q = (case q of ((t, gc, mL, mR, dp, di, tin), hin, hsince) \<Rightarrow>
    (let xs = csorted_list_of_set X in
     do { hsince \<leftarrow> since_loop2 t xs hsince;
          if memL (args_ivl args) 0 then do {
            hin \<leftarrow> ins_loop2 t xs hin;
            return ((t, gc, mL, mR, dp, append_queue (t, X) di, tin \<union> X), hin, hsince) }
          else return ((t, gc, mL, mR, append_queue (t, X) dp, di, tin), hin, hsince) }))"

definition result2 :: "msaux2 \<Rightarrow> event_data table Heap" where
  "result2 q = return (snd (snd (snd (snd (snd (snd (fst q)))))))"

subsection \<open>Since with a closed left operand\<close>

text \<open>
  The counterpart for Since of the Until structure for a closed left operand, which is defined
  further down in this session.  @{text "ONCE I \<phi>"} becomes @{text "TT SINCE I \<phi>"}, and a closed left operand again makes
  ``the left operand held throughout'' a property of time points alone: the answer at @{text i}
  is the union of the right operand's tables over the time points @{text j} whose timestamp lies
  in the interval measured back from @{text i}, cut off at the last time point at which the left
  operand failed.  All three bounds move forward as @{text i} does, so the window is again one
  whose ends only advance, and the union is kept as a count per tuple.

  Unlike the Until structure, this one does not need the interval to start at zero: for Since a
  non-zero left bound delays a table's entry into the window rather than excluding a prefix of
  it, so the table waits in a second queue until its timestamp is old enough.

  Definitions only, no proofs.
\<close>

type_synonym sevtaux = "ts \<times> (ts \<times> event_data table) queue \<times> (ts \<times> event_data table) queue \<times>
  (event_data tuple, nat) mapping \<times> event_data table"

text \<open>Tables whose timestamp has become old enough enter the window, unless they are already too
old to be in it at all.\<close>

function sevt_move :: "args \<Rightarrow> ts \<Rightarrow> (ts \<times> event_data table) queue \<Rightarrow> (ts \<times> event_data table) queue \<Rightarrow>
    (event_data tuple, nat) mapping \<Rightarrow> event_data table \<Rightarrow>
    (ts \<times> event_data table) queue \<times> (ts \<times> event_data table) queue \<times>
    (event_data tuple, nat) mapping \<times> event_data table" where
  "sevt_move args nt pend win cnt cur =
     (case safe_hd pend of
        (None, pend') \<Rightarrow> (pend', win, cnt, cur)
      | (Some e, pend') \<Rightarrow>
        (if memL (args_ivl args) (nt - fst e)
         then (if memR (args_ivl args) (nt - fst e)
               then (case evt_add (snd e) (cnt, cur) of (cnt', cur') \<Rightarrow>
                       sevt_move args nt (tl_queue pend') (append_queue e win) cnt' cur')
               else sevt_move args nt (tl_queue pend') win cnt cur)
         else (pend', win, cnt, cur)))"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(args, nt, pend, win, cnt, cur). length (linearize pend))")
     (fastforce split: prod.splits)+

declare sevt_move.simps[simp del]

text \<open>Tables whose timestamp has fallen out of the interval leave the window.\<close>

function sevt_expire :: "args \<Rightarrow> ts \<Rightarrow> (ts \<times> event_data table) queue \<Rightarrow>
    (event_data tuple, nat) mapping \<Rightarrow> event_data table \<Rightarrow>
    (ts \<times> event_data table) queue \<times> (event_data tuple, nat) mapping \<times> event_data table" where
  "sevt_expire args nt win cnt cur =
     (case safe_hd win of
        (None, win') \<Rightarrow> (win', cnt, cur)
      | (Some e, win') \<Rightarrow>
        (if memR (args_ivl args) (nt - fst e) then (win', cnt, cur)
         else (case evt_del (snd e) (cnt, cur) of (cnt', cur') \<Rightarrow>
                 sevt_expire args nt (tl_queue win') cnt' cur')))"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(args, nt, win, cnt, cur). length (linearize win))")
     (fastforce split: prod.splits)+

declare sevt_expire.simps[simp del]

subsection \<open>Operations\<close>

definition init_sevt :: "args \<Rightarrow> sevtaux" where
  "init_sevt args = (0, empty_queue, empty_queue, Mapping.empty, {})"

definition add_new_ts_sevt :: "args \<Rightarrow> ts \<Rightarrow> sevtaux \<Rightarrow> sevtaux" where
  "add_new_ts_sevt args nt aux = (case aux of (t, pend, win, cnt, cur) \<Rightarrow>
     (case sevt_move args nt pend win cnt cur of (pend', win', cnt', cur') \<Rightarrow>
      (case sevt_expire args nt win' cnt' cur' of (win'', cnt'', cur'') \<Rightarrow>
        (nt, pend', win'', cnt'', cur''))))"

text \<open>A closed left operand that fails cuts off everything before the current time point.\<close>

definition join_sevt :: "args \<Rightarrow> event_data table \<Rightarrow> sevtaux \<Rightarrow> sevtaux" where
  "join_sevt args X aux = (case aux of (t, pend, win, cnt, cur) \<Rightarrow>
     (if (if args_pos args then \<not> Set.is_empty X else Set.is_empty X) then aux
      else (t, empty_queue, empty_queue, Mapping.empty, {})))"

definition add_new_table_sevt :: "args \<Rightarrow> event_data table \<Rightarrow> sevtaux \<Rightarrow> sevtaux" where
  "add_new_table_sevt args X aux = (case aux of (t, pend, win, cnt, cur) \<Rightarrow>
     (if memL (args_ivl args) 0
      then (case evt_add X (cnt, cur) of (cnt', cur') \<Rightarrow>
              (t, pend, append_queue (t, X) win, cnt', cur'))
      else (t, append_queue (t, X) pend, win, cnt, cur)))"

definition result_sevt :: "args \<Rightarrow> sevtaux \<Rightarrow> event_data table" where
  "result_sevt args aux = (case aux of (t, pend, win, cnt, cur) \<Rightarrow> cur)"

definition sevt_applies :: "args \<Rightarrow> bool" where
  "sevt_applies args \<longleftrightarrow> args_agg args = None \<and> args_L args = {}"

subsection \<open>Heap structure or pure structure\<close>

text \<open>
  As in @{theory MFODL_Monitor_Imp.Optimized_Since_Imp}: the heap structure is used for Since
  operators without aggregation whose join columns are all of them or none, and the pure
  aggregation-aware structure otherwise.
\<close>

datatype msaux_j = MSJ_imp msaux2 | MSJ_pure mmasaux | MSJ_evt sevtaux

definition init_j :: "args \<Rightarrow> msaux_j Heap" where
  "init_j args = (if sevt_applies args then return (MSJ_evt (init_sevt args))
     else if args_agg args = None \<and> special_args args
     then do { q \<leftarrow> init2 args; return (MSJ_imp q) } else return (MSJ_pure (init_mmasaux args)))"

fun add_new_ts_j :: "args \<Rightarrow> ts \<Rightarrow> msaux_j \<Rightarrow> msaux_j Heap" where
  "add_new_ts_j args nt (MSJ_imp q) = do { q \<leftarrow> add_new_ts2 args nt q; return (MSJ_imp q) }"
| "add_new_ts_j args nt (MSJ_pure s) = return (MSJ_pure (add_new_ts_mmasaux args nt s))"
| "add_new_ts_j args nt (MSJ_evt a) = return (MSJ_evt (add_new_ts_sevt args nt a))"

fun join_j :: "args \<Rightarrow> event_data table \<Rightarrow> msaux_j \<Rightarrow> msaux_j Heap" where
  "join_j args X (MSJ_imp q) = do { q \<leftarrow> gc_join2 args X q; return (MSJ_imp q) }"
| "join_j args X (MSJ_pure s) = return (MSJ_pure (gc_join_mmasaux args X s))"
| "join_j args X (MSJ_evt a) = return (MSJ_evt (join_sevt args X a))"

fun add_new_table_j :: "args \<Rightarrow> event_data table \<Rightarrow> msaux_j \<Rightarrow> msaux_j Heap" where
  "add_new_table_j args X (MSJ_imp q) = do { q \<leftarrow> add_new_table2 args X q; return (MSJ_imp q) }"
| "add_new_table_j args X (MSJ_pure s) = return (MSJ_pure (add_new_table_mmasaux args X s))"
| "add_new_table_j args X (MSJ_evt a) = return (MSJ_evt (add_new_table_sevt args X a))"

fun result_j :: "args \<Rightarrow> msaux_j \<Rightarrow> event_data table Heap" where
  "result_j args (MSJ_imp q) = result2 q"
| "result_j args (MSJ_pure s) = return (result_mmasaux args s)"
| "result_j args (MSJ_evt a) = return (result_sevt args a)"

(*<*)
end
(*>*)
