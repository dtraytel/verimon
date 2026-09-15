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
    | x # r \<Rightarrow> do { v \<leftarrow> im_lookup h x;
        if v = Some t then do { h \<leftarrow> im_delete h x; filter_loop2 t r h (Set.insert x Y) }
        else filter_loop2 t r h Y })"

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
    | x # r \<Rightarrow> do { v \<leftarrow> im_lookup hs x;
        (case v of None \<Rightarrow> upd_loop2 t r hs h Y
         | Some t' \<Rightarrow> if t' \<le> t then do { h \<leftarrow> im_update h x t; upd_loop2 t r hs h (Set.insert x Y) }
                      else upd_loop2 t r hs h Y) })"

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
    | x # r \<Rightarrow> do { v \<leftarrow> im_lookup h x;
                     h \<leftarrow> (if v = None then im_update h x t else return h);
                     since_loop2 t r h })"

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

subsection \<open>Heap structure or pure structure\<close>

text \<open>
  As in @{theory MFODL_Monitor_Imp.Optimized_Since_Imp}: the heap structure is used for Since
  operators without aggregation whose join columns are all of them or none, and the pure
  aggregation-aware structure otherwise.
\<close>

datatype msaux_j = MSJ_imp msaux2 | MSJ_pure mmasaux

definition init_j :: "args \<Rightarrow> msaux_j Heap" where
  "init_j args = (if args_agg args = None \<and> special_args args
     then do { q \<leftarrow> init2 args; return (MSJ_imp q) } else return (MSJ_pure (init_mmasaux args)))"

fun add_new_ts_j :: "args \<Rightarrow> ts \<Rightarrow> msaux_j \<Rightarrow> msaux_j Heap" where
  "add_new_ts_j args nt (MSJ_imp q) = do { q \<leftarrow> add_new_ts2 args nt q; return (MSJ_imp q) }"
| "add_new_ts_j args nt (MSJ_pure s) = return (MSJ_pure (add_new_ts_mmasaux args nt s))"

fun join_j :: "args \<Rightarrow> event_data table \<Rightarrow> msaux_j \<Rightarrow> msaux_j Heap" where
  "join_j args X (MSJ_imp q) = do { q \<leftarrow> gc_join2 args X q; return (MSJ_imp q) }"
| "join_j args X (MSJ_pure s) = return (MSJ_pure (gc_join_mmasaux args X s))"

fun add_new_table_j :: "args \<Rightarrow> event_data table \<Rightarrow> msaux_j \<Rightarrow> msaux_j Heap" where
  "add_new_table_j args X (MSJ_imp q) = do { q \<leftarrow> add_new_table2 args X q; return (MSJ_imp q) }"
| "add_new_table_j args X (MSJ_pure s) = return (MSJ_pure (add_new_table_mmasaux args X s))"

fun result_j :: "args \<Rightarrow> msaux_j \<Rightarrow> event_data table Heap" where
  "result_j args (MSJ_imp q) = result2 q"
| "result_j args (MSJ_pure s) = return (result_mmasaux args s)"

(*<*)
end
(*>*)
