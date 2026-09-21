(*<*)
theory Since_Imp2
  imports Table_Imp Optimized_Since_Imp "MFODL_Monitor_Dense.Since_Evt"
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

text \<open>
  The structure is written over a tuple type that is a parameter, so that the monitor over the
  short tuples further down in this session can use the same one.  Everything the structure does
  with a tuple is to hash it, compare it with another and put it in a table, so the hash and the
  equality are the only two operations it has to be given.
\<close>

partial_function (heap) filter_loop2 ::
  "('t \<Rightarrow> integer) \<Rightarrow> ('t \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> ts \<Rightarrow> 't list \<Rightarrow> ('t::{heap,ccompare}, ts) imap \<Rightarrow> 't set \<Rightarrow>
    (('t, ts) imap \<times> 't set) Heap" where
  [code]:
  "filter_loop2 hsh eq t xs h Y = (case xs of [] \<Rightarrow> return (h, Y)
    | x # r \<Rightarrow> (let hx = hsh x in
        do { v \<leftarrow> im_lookup_h eq h hx x;
             if v = Some t
             then do { h \<leftarrow> im_delete_h eq h hx x;
                       filter_loop2 hsh eq t r h (Set.insert x Y) }
             else filter_loop2 hsh eq t r h Y }))"

partial_function (heap) expire_loop2 ::
  "('t \<Rightarrow> integer) \<Rightarrow> ('t \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> (ts \<times> 't set) list \<Rightarrow> ('t::{heap,ccompare}, ts) imap \<Rightarrow>
    't set \<Rightarrow> (('t, ts) imap \<times> 't set) Heap" where
  [code]:
  "expire_loop2 hsh eq xs h Y = (case xs of [] \<Rightarrow> return (h, Y)
    | tX # r \<Rightarrow> do { p \<leftarrow> filter_loop2 hsh eq (fst tX) (csorted_list_of_set (snd tX)) h Y;
                      expire_loop2 hsh eq r (fst p) (snd p) })"

partial_function (heap) upd_loop2 ::
  "('t \<Rightarrow> integer) \<Rightarrow> ('t \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> ts \<Rightarrow> 't list \<Rightarrow> ('t::{heap,ccompare}, ts) imap \<Rightarrow>
    ('t, ts) imap \<Rightarrow> 't set \<Rightarrow> (('t, ts) imap \<times> 't set) Heap" where
  [code]:
  "upd_loop2 hsh eq t xs hs h Y = (case xs of [] \<Rightarrow> return (h, Y)
    | x # r \<Rightarrow> (let hx = hsh x in
        do { v \<leftarrow> im_lookup_h eq hs hx x;
             (case v of None \<Rightarrow> upd_loop2 hsh eq t r hs h Y
              | Some t' \<Rightarrow> if t' \<le> t
                  then do { h \<leftarrow> im_update_h eq h hx x t;
                            upd_loop2 hsh eq t r hs h (Set.insert x Y) }
                  else upd_loop2 hsh eq t r hs h Y) }))"

partial_function (heap) move_loop2 ::
  "('t \<Rightarrow> integer) \<Rightarrow> ('t \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> (ts \<times> 't set) list \<Rightarrow> ('t::{heap,ccompare}, ts) imap \<Rightarrow>
    ('t, ts) imap \<Rightarrow> 't set \<Rightarrow> (('t, ts) imap \<times> 't set) Heap" where
  [code]:
  "move_loop2 hsh eq xs hs h Y = (case xs of [] \<Rightarrow> return (h, Y)
    | tX # r \<Rightarrow> do { p \<leftarrow> upd_loop2 hsh eq (fst tX) (csorted_list_of_set (snd tX)) hs h Y;
                      move_loop2 hsh eq r hs (fst p) (snd p) })"

partial_function (heap) del_loop2 ::
  "('t \<Rightarrow> integer) \<Rightarrow> ('t \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> ('t \<Rightarrow> bool) \<Rightarrow> 't list \<Rightarrow> ('t::heap, ts) imap \<Rightarrow>
    ('t, ts) imap Heap" where
  [code]:
  "del_loop2 hsh eq p ks h = (case ks of [] \<Rightarrow> return h
    | k # r \<Rightarrow> if p k then del_loop2 hsh eq p r h
              else do { h \<leftarrow> im_delete hsh eq h k; del_loop2 hsh eq p r h })"

partial_function (heap) ins_loop2 ::
  "('t \<Rightarrow> integer) \<Rightarrow> ('t \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> ts \<Rightarrow> 't list \<Rightarrow> ('t::heap, ts) imap \<Rightarrow>
    ('t, ts) imap Heap" where
  [code]:
  "ins_loop2 hsh eq t xs h = (case xs of [] \<Rightarrow> return h
    | x # r \<Rightarrow> do { h \<leftarrow> im_update hsh eq h x t; ins_loop2 hsh eq t r h })"

partial_function (heap) since_loop2 ::
  "('t \<Rightarrow> integer) \<Rightarrow> ('t \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> ts \<Rightarrow> 't list \<Rightarrow> ('t::heap, ts) imap \<Rightarrow>
    ('t, ts) imap Heap" where
  [code]:
  "since_loop2 hsh eq t xs h = (case xs of [] \<Rightarrow> return h
    | x # r \<Rightarrow> (let hx = hsh x in
        do { v \<leftarrow> im_lookup_h eq h hx x;
             h \<leftarrow> (if v = None then im_update_h eq h hx x t else return h);
             since_loop2 hsh eq t r h }))"

subsection \<open>Operations\<close>

type_synonym 't msaux2_core = "ts \<times> ts \<times> bool list \<times> bool list \<times>
  (ts \<times> 't set) queue \<times> (ts \<times> 't set) queue \<times> 't set"

type_synonym 't msaux2 = "'t msaux2_core \<times> ('t, ts) imap \<times> ('t, ts) imap"

text \<open>A copy of @{const jc} over a tuple type that is a parameter.\<close>

definition gjc :: "bool \<Rightarrow> 't set \<Rightarrow> 't \<Rightarrow> bool" where
  "gjc pos X k = (if pos then k \<in> X else k \<notin> X)"

definition init2 :: "args \<Rightarrow> ('t::heap) msaux2 Heap" where
  "init2 args = do { hin \<leftarrow> im_new 16; hsince \<leftarrow> im_new 16;
     return ((0, 0, join_mask (args_n args) (args_L args), join_mask (args_n args) (args_R args),
       empty_queue, empty_queue, {}), hin, hsince) }"

definition shift_end2 :: "('t \<Rightarrow> integer) \<Rightarrow> ('t \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> args \<Rightarrow> ts \<Rightarrow>
    ('t::{heap,ccompare}) msaux2 \<Rightarrow> 't msaux2 Heap" where
  "shift_end2 hsh eq args nt q = (case q of ((t, gc, mL, mR, dp, di, tin), hin, hsince) \<Rightarrow>
    (let I = args_ivl args;
         dp' = dropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) dp;
         p = takedropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) di
     in do { r \<leftarrow> expire_loop2 hsh eq (snd p) hin {};
             return ((t, gc, mL, mR, dp', fst p, tin - snd r), fst r, hsince) }))"

definition add_new_ts2' :: "('t \<Rightarrow> integer) \<Rightarrow> ('t \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> args \<Rightarrow> ts \<Rightarrow>
    ('t::{heap,ccompare}) msaux2 \<Rightarrow> 't msaux2 Heap" where
  "add_new_ts2' hsh eq args nt q = (case q of ((t, gc, mL, mR, dp, di, tin), hin, hsince) \<Rightarrow>
    (let I = args_ivl args;
         p = takedropWhile_queue (\<lambda>(t, X). memL I (nt - t)) dp;
         di' = fold append_queue (snd p) di
     in do { r \<leftarrow> move_loop2 hsh eq (snd p) hsince hin {};
             return ((nt, gc, mL, mR, fst p, di', tin \<union> snd r), fst r, hsince) }))"

definition add_new_ts2 :: "('t \<Rightarrow> integer) \<Rightarrow> ('t \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> args \<Rightarrow> ts \<Rightarrow>
    ('t::{heap,ccompare}) msaux2 \<Rightarrow> 't msaux2 Heap" where
  "add_new_ts2 hsh eq args nt q =
     do { q \<leftarrow> shift_end2 hsh eq args nt q; add_new_ts2' hsh eq args nt q }"

definition gc2 :: "('t::{heap,ccompare}) msaux2 \<Rightarrow> 't msaux2 Heap" where
  "gc2 q = (case q of ((t, gc, mL, mR, dp, di, tin), hin, hsince) \<Rightarrow>
     (let all = fold (\<lambda>p acc. snd p \<union> acc) (linearize dp @ linearize di) {} in
      do { hsince \<leftarrow> im_filter (\<lambda>k. k \<in> all) hsince;
           return ((t, t, mL, mR, dp, di, tin), hin, hsince) }))"

text \<open>The first branch is the one in which the operator has no join columns, so that the left
  operand's only tuple is the empty one; which tuple that is depends on the representation, so
  the caller passes it.\<close>

definition join2 :: "('t \<Rightarrow> integer) \<Rightarrow> ('t \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> 't \<Rightarrow> args \<Rightarrow> 't set \<Rightarrow>
    ('t::{heap,ccompare}) msaux2 \<Rightarrow> 't msaux2 Heap" where
  "join2 hsh eq nul args X q = (case q of ((t, gc, mL, mR, dp, di, tin), hin, hsince) \<Rightarrow>
    (let pos = args_pos args in
     if (\<forall>i \<in> set mL. \<not> i) then
       (if (pos \<longleftrightarrow> nul \<in> X) then return q
        else do { hin \<leftarrow> im_new 16; hsince \<leftarrow> im_new 16;
                  return ((t, gc, mL, mR, dp, di, {}), hin, hsince) })
     else (let in_del = (if pos then tin - X else tin \<inter> X) in
       do { hin \<leftarrow> del_loop2 hsh eq (\<lambda>k. k \<notin> in_del) (csorted_list_of_set in_del) hin;
            hsince \<leftarrow> im_filter (gjc pos X) hsince;
            return ((t, gc, mL, mR, dp, di, tin - in_del), hin, hsince) })))"

definition gc_join2 :: "('t \<Rightarrow> integer) \<Rightarrow> ('t \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> 't \<Rightarrow> args \<Rightarrow> 't set \<Rightarrow>
    ('t::{heap,ccompare}) msaux2 \<Rightarrow> 't msaux2 Heap" where
  "gc_join2 hsh eq nul args X q = (case q of ((t, gc, mL, mR, dp, di, tin), hin, hsince) \<Rightarrow>
    if \<not> memR (args_ivl args) (t - gc) then do { q \<leftarrow> gc2 q; join2 hsh eq nul args X q }
    else join2 hsh eq nul args X q)"

definition add_new_table2 :: "('t \<Rightarrow> integer) \<Rightarrow> ('t \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> args \<Rightarrow> 't set \<Rightarrow>
    ('t::{heap,ccompare}) msaux2 \<Rightarrow> 't msaux2 Heap" where
  "add_new_table2 hsh eq args X q = (case q of ((t, gc, mL, mR, dp, di, tin), hin, hsince) \<Rightarrow>
    (let xs = csorted_list_of_set X in
     do { hsince \<leftarrow> since_loop2 hsh eq t xs hsince;
          if memL (args_ivl args) 0 then do {
            hin \<leftarrow> ins_loop2 hsh eq t xs hin;
            return ((t, gc, mL, mR, dp, append_queue (t, X) di, tin \<union> X), hin, hsince) }
          else return ((t, gc, mL, mR, append_queue (t, X) dp, di, tin), hin, hsince) }))"

definition result2 :: "('t::heap) msaux2 \<Rightarrow> 't set Heap" where
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

  This structure -- @{typ sevtaux} and its operations -- touches no array or reference, so it now
  lives in @{theory MFODL_Monitor_Dense.Since_Evt}, which this theory imports.

  Definitions only, no proofs.
\<close>

subsection \<open>Heap structure or pure structure\<close>

text \<open>
  As in @{theory MFODL_Monitor_Imp.Optimized_Since_Imp}: the heap structure is used for Since
  operators without aggregation whose join columns are all of them or none, and the pure
  aggregation-aware structure otherwise.
\<close>

datatype msaux_j = MSJ_imp "event_data tuple msaux2" | MSJ_pure mmasaux | MSJ_evt sevtaux

definition init_j :: "args \<Rightarrow> msaux_j Heap" where
  "init_j args = (if sevt_applies args then return (MSJ_evt (init_sevt args))
     else if args_agg args = None \<and> special_args args
     then do { q \<leftarrow> init2 args; return (MSJ_imp q) } else return (MSJ_pure (init_mmasaux args)))"

fun add_new_ts_j :: "args \<Rightarrow> ts \<Rightarrow> msaux_j \<Rightarrow> msaux_j Heap" where
  "add_new_ts_j args nt (MSJ_imp q) =
     do { q \<leftarrow> add_new_ts2 ihash teq args nt q; return (MSJ_imp q) }"
| "add_new_ts_j args nt (MSJ_pure s) = return (MSJ_pure (add_new_ts_mmasaux args nt s))"
| "add_new_ts_j args nt (MSJ_evt a) = return (MSJ_evt (add_new_ts_sevt args nt a))"

fun join_j :: "args \<Rightarrow> event_data table \<Rightarrow> msaux_j \<Rightarrow> msaux_j Heap" where
  "join_j args X (MSJ_imp q) =
     do { q \<leftarrow> gc_join2 ihash teq (replicate (args_n args) None) args X q; return (MSJ_imp q) }"
| "join_j args X (MSJ_pure s) = return (MSJ_pure (gc_join_mmasaux args X s))"
| "join_j args X (MSJ_evt a) = return (MSJ_evt (join_sevt args X a))"

fun add_new_table_j :: "args \<Rightarrow> event_data table \<Rightarrow> msaux_j \<Rightarrow> msaux_j Heap" where
  "add_new_table_j args X (MSJ_imp q) =
     do { q \<leftarrow> add_new_table2 ihash teq args X q; return (MSJ_imp q) }"
| "add_new_table_j args X (MSJ_pure s) = return (MSJ_pure (add_new_table_mmasaux args X s))"
| "add_new_table_j args X (MSJ_evt a) = return (MSJ_evt (add_new_table_sevt args X a))"

fun result_j :: "args \<Rightarrow> msaux_j \<Rightarrow> event_data table Heap" where
  "result_j args (MSJ_imp q) = result2 q"
| "result_j args (MSJ_pure s) = return (result_mmasaux args s)"
| "result_j args (MSJ_evt a) = return (result_sevt args a)"

(*<*)
end
(*>*)
