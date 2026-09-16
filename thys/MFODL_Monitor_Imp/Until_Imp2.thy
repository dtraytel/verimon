(*<*)
theory Until_Imp2
  imports Table_Imp "MFODL_Monitor_Devel.Optimized_Until_Deque"
begin
(*>*)

section \<open>The Until structure over heap-resident maps\<close>

text \<open>
  The deque structure of @{theory MFODL_Monitor_Devel.Optimized_Until_Deque} with its
  tuple-keyed mappings on the heap. The deque of time points, the queues of tables and the
  result table stay pure; the mapping from a tuple to the last time point at which the left
  operand held, and the mapping of every time point in the window, are updated in place.

  Definitions only, no proofs.
\<close>

type_synonym imap_tstp = "(ts + tp) imap"

type_synonym muaux2 = "tp \<times> ts queue \<times> (event_data table \<times> (ts + tp)) queue \<times> nat \<times> bool list \<times>
  bool list \<times> event_data table \<times> tp imap \<times> imap_tstp dq \<times> ts dq \<times> event_data table list"

subsection \<open>Passes over a map's buckets\<close>

text \<open>The keys of a map as a table, the merge of one map into another, and the deletion of a
  list of keys, each in one pass and without reading the map back as a list.\<close>

partial_function (heap) im_keys_idx ::
  "(('v::heap) ientry list) array \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> event_data table \<Rightarrow> event_data table Heap" where
  [code]:
  "im_keys_idx a i n acc = (if n \<le> i then return acc
     else do { b \<leftarrow> Array.nth' a i;
               im_keys_idx a (i + 1) n (fold (\<lambda>e acc. Set.insert (fst (snd e)) acc) b acc) })"

definition im_keys_tbl :: "('v::heap) imap \<Rightarrow> event_data table Heap" where
  "im_keys_tbl q = (case q of (n, c, a) \<Rightarrow> im_keys_idx a 0 n {})"

text \<open>The entries carry their hashes, so merging one map into another rehashes nothing: the
  hash travels with the key from the source bucket into the lookup and the update.\<close>

partial_function (heap) im_merge_list :: "('v \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow> ('v ientry) list \<Rightarrow>
    ('v::heap) imap \<Rightarrow> ('v imap) Heap" where
  [code]:
  "im_merge_list f es q = (case es of [] \<Rightarrow> return q
     | e # r \<Rightarrow> (case e of (h, x, w) \<Rightarrow>
         do { v \<leftarrow> im_lookup_h q h x;
              q \<leftarrow> im_update_h q h x (case v of None \<Rightarrow> w | Some u \<Rightarrow> f w u);
              im_merge_list f r q }))"

partial_function (heap) im_merge_idx :: "('v \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow> (('v::heap) ientry list) array \<Rightarrow>
    integer \<Rightarrow> integer \<Rightarrow> ('v imap) \<Rightarrow> ('v imap) Heap" where
  [code]:
  "im_merge_idx f a i n q = (if n \<le> i then return q
     else do { b \<leftarrow> Array.nth' a i; q \<leftarrow> im_merge_list f b q; im_merge_idx f a (i + 1) n q })"

definition im_merge :: "('v \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow> ('v::heap) imap \<Rightarrow> 'v imap \<Rightarrow> ('v imap) Heap" where
  "im_merge f q1 q2 = (case q1 of (n, c, a) \<Rightarrow> im_merge_idx f a 0 n q2)"

partial_function (heap) im_del_list :: "event_data tuple list \<Rightarrow> ('v::heap) imap \<Rightarrow> ('v imap) Heap" where
  [code]:
  "im_del_list xs q = (case xs of [] \<Rightarrow> return q
     | x # r \<Rightarrow> do { q \<leftarrow> im_delete q x; im_del_list r q })"

partial_function (heap) im_keep_list :: "((ts + tp) \<Rightarrow> bool) \<Rightarrow> event_data tuple list \<Rightarrow> imap_tstp \<Rightarrow>
    event_data table \<Rightarrow> event_data table Heap" where
  [code]:
  "im_keep_list P xs q acc = (case xs of [] \<Rightarrow> return acc
     | x # r \<Rightarrow> do { v \<leftarrow> im_lookup q x;
                      im_keep_list P r q (case v of None \<Rightarrow> acc
                        | Some tstp \<Rightarrow> if P tstp then acc else Set.insert x acc) })"

partial_function (heap) ins_tp_list :: "tp \<Rightarrow> event_data tuple list \<Rightarrow> tp imap \<Rightarrow> (tp imap) Heap" where
  [code]:
  "ins_tp_list tp xs q = (case xs of [] \<Rightarrow> return q
     | x # r \<Rightarrow> do { q \<leftarrow> im_update q x tp; ins_tp_list tp r q })"

text \<open>With a positive left operand a tuple that is already in the map keeps the time point it
  has; only tuples that are not in it yet are added.\<close>

partial_function (heap) ins_new_tp_list :: "tp \<Rightarrow> event_data tuple list \<Rightarrow> tp imap \<Rightarrow> (tp imap) Heap" where
  [code]:
  "ins_new_tp_list tp xs q = (case xs of [] \<Rightarrow> return q
     | x # r \<Rightarrow> (let h = ihash x in
         do { v \<leftarrow> im_lookup_h q h x;
              q \<leftarrow> (if v = None then im_update_h q h x tp else return q);
              ins_new_tp_list tp r q }))"

subsection \<open>Adding the tuples of a time point\<close>

type_synonym until_acc2 = "event_data table \<times> imap_tstp dq \<times> event_data table"

definition upd_nested_step2 :: "nat \<Rightarrow> (ts + tp) \<Rightarrow> ((ts + tp) \<Rightarrow> (ts + tp)) \<Rightarrow> nat \<times> event_data tuple \<Rightarrow>
    imap_tstp dq \<Rightarrow> (imap_tstp dq) Heap" where
  "upd_nested_step2 base d f x dq = (case x of (k, k') \<Rightarrow>
     if base \<le> k \<and> k - base < dq_len dq then
       (let i = k - base; m = dq_nth dq i; h = ihash k' in
        do { v \<leftarrow> im_lookup_h m h k';
             m \<leftarrow> im_update_h m h k' (case v of Some u \<Rightarrow> f u | None \<Rightarrow> d);
             return (dq_upd dq i m) })
     else return dq)"

definition until_step2 :: "(nat \<Rightarrow> bool) \<Rightarrow> (ts + tp) \<Rightarrow> nat \<Rightarrow> nat \<times> event_data tuple \<Rightarrow>
    until_acc2 \<Rightarrow> until_acc2 Heap" where
  "until_step2 P d t0 p acc = (case acc of (tbl, a2, res) \<Rightarrow>
     if P (fst p) then do {
       a2 \<leftarrow> upd_nested_step2 t0 d (max_tstp d) p a2;
       return (Set.insert (snd p) tbl, a2, if fst p = t0 then Set.insert (snd p) res else res) }
     else return acc)"

definition until_elem_step2 :: "tp imap \<Rightarrow> bool list \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow>
    (ts + tp) \<Rightarrow> event_data tuple \<Rightarrow> until_acc2 \<Rightarrow> until_acc2 Heap" where
  "until_elem_step2 a1 maskL pos tp len inz P d as acc = do {
     acc \<leftarrow> (if inz then until_step2 P d (tp - len) (tp, as) acc else return acc);
     v \<leftarrow> im_lookup a1 (proj_tuple maskL as);
     (case v of
        None \<Rightarrow> (if \<not> pos then until_step2 P d (tp - len) (tp - len, as) acc else return acc)
      | Some tp' \<Rightarrow> until_step2 P d (tp - len)
          (if pos then (max (tp - len) tp', as) else (max (tp - len) (tp' + 1), as)) acc) }"

partial_function (heap) until_fold2 :: "tp imap \<Rightarrow> bool list \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow>
    (nat \<Rightarrow> bool) \<Rightarrow> (ts + tp) \<Rightarrow> event_data tuple list \<Rightarrow> until_acc2 \<Rightarrow> until_acc2 Heap" where
  [code]:
  "until_fold2 a1 maskL pos tp len inz P d xs acc = (case xs of [] \<Rightarrow> return acc
     | as # r \<Rightarrow> do { acc \<leftarrow> until_elem_step2 a1 maskL pos tp len inz P d as acc;
                       until_fold2 a1 maskL pos tp len inz P d r acc })"

subsection \<open>Operations\<close>

definition init_dq2 :: "args \<Rightarrow> muaux2 Heap" where
  "init_dq2 args = do { a1 \<leftarrow> im_new 16; m \<leftarrow> im_new 16;
     return (0, empty_queue, empty_queue, 0, join_mask (args_n args) (args_L args),
       join_mask (args_n args) (args_R args), {}, a1, dq_push m dq_empty, dq_empty, []) }"

definition length_dq2 :: "args \<Rightarrow> muaux2 \<Rightarrow> nat" where
  "length_dq2 args aux = (case aux of (tp, tss, tables, len, maskL, maskR, result, a1, a2, tstp_dq, done) \<Rightarrow>
     length done + len)"

definition eval_step_dq2 :: "args \<Rightarrow> muaux2 \<Rightarrow> muaux2 Heap" where
  "eval_step_dq2 args aux = (case aux of (tp, tss, tables, len, maskL, maskR, result, a1, a2, tstp_dq, done) \<Rightarrow>
    (case safe_hd tss of (_, tssa) \<Rightarrow>
     (let m = dq_nth a2 0;
       I = args_ivl args;
       T = eval_args_agg args result;
       tssb = tl_queue tssa;
       (ts', tss'') = (case safe_hd tssb of (Some ts', tss'') \<Rightarrow> (ts', tss'') | (None, tss'') \<Rightarrow> (0, tss''));
       (tables', taken) = takedropWhile_queue (\<lambda>(table, tstp). \<not> ts_tp_lt I ts' (tp - len + 1) tstp) tables;
       to_del_approx = fold (\<lambda>p acc. fst p \<union> acc) taken {}
      in do {
       to_del \<leftarrow> im_keep_list (ts_tp_lt I ts' (tp - len + 1)) (csorted_list_of_set to_del_approx) m {};
       m \<leftarrow> im_del_list (csorted_list_of_set to_del) m;
       (if len = 1
        then do { e \<leftarrow> im_new 16;
                  return (tp, tss'', tables', len - 1, maskL, maskR, {}, a1,
                          dq_tl (dq_upd a2 1 e), dq_tl tstp_dq, T # done) }
        else (let m' = dq_nth a2 1 in
              do { ks \<leftarrow> im_keys_tbl m';
                   m' \<leftarrow> im_merge max_tstp m m';
                   return (tp, tss'', tables', len - 1, maskL, maskR, (result - to_del) \<union> ks, a1,
                           dq_tl (dq_upd a2 1 m'), dq_tl tstp_dq, T # done) })) })))"

partial_function (heap) shift_loop2 :: "args \<Rightarrow> nat \<Rightarrow> muaux2 \<Rightarrow> muaux2 Heap" where
  [code]:
  "shift_loop2 args k aux = (if k = 0 then return aux
     else do { aux \<leftarrow> eval_step_dq2 args aux; shift_loop2 args (k - 1) aux })"

definition shift_dq2 :: "args \<Rightarrow> ts \<Rightarrow> muaux2 \<Rightarrow> muaux2 Heap" where
  "shift_dq2 args nt aux = (case aux of (tp, tss, tables, len, maskL, maskR, result, a1, a2, tstp_dq, done) \<Rightarrow>
     (case takeWhile_queue (\<lambda>t. \<not> memR (args_ivl args) (nt - t)) tss of (tss_queue, tssa) \<Rightarrow>
      shift_loop2 args (length (linearize tss_queue))
        (tp, tssa, tables, len, maskL, maskR, result, a1, a2, tstp_dq, done)))"

definition add_new_dq2 :: "args \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow> muaux2 \<Rightarrow> muaux2 Heap" where
  "add_new_dq2 args rel1 rel2 nt aux = do {
     s \<leftarrow> shift_dq2 args nt aux;
     (case s of (tp, tss, tables, len, maskL, maskR, result, a1, a2, tstp_dq, done) \<Rightarrow>
      (let I = args_ivl args; pos = args_pos args; inz = memL I 0;
        new_tstp = (if inz then Inr tp else Inl nt);
        tstp_dq = dq_push nt tstp_dq;
        P = (\<lambda>t. memL I (nt - dq_nth tstp_dq (t - (tp - len))))
       in do {
        r \<leftarrow> until_fold2 a1 maskL pos tp len inz P new_tstp (csorted_list_of_set rel2) ({}, a2, result);
        (case r of (tbl, a2', result') \<Rightarrow>
         do { e \<leftarrow> im_new 16;
              a1 \<leftarrow> (if pos
                     then do { a1 \<leftarrow> ins_new_tp_list tp (csorted_list_of_set rel1) a1;
                               im_filter (\<lambda>as. as \<in> rel1) a1 }
                     else ins_tp_list tp (csorted_list_of_set rel1) a1);
              return (tp + 1, append_queue nt tss, append_queue (tbl, new_tstp) tables, len + 1,
                      maskL, maskR, result', a1, dq_push e a2', tstp_dq, done) }) })) }"

definition eval_dq2 :: "args \<Rightarrow> ts \<Rightarrow> muaux2 \<Rightarrow> (event_data table list \<times> muaux2) Heap" where
  "eval_dq2 args nt aux = do {
     s \<leftarrow> shift_dq2 args nt aux;
     (case s of (tp, tss, tables, len, maskL, maskR, result, a1, a2, tstp_dq, done) \<Rightarrow>
       return (rev done, (tp, tss, tables, len, maskL, maskR, result, a1, a2, tstp_dq, []))) }"


section \<open>Until with a closed left operand\<close>

text \<open>
  @{text "EVENTUALLY I \<phi>"} is rewritten by the front end into @{text "Until TT I \<phi>"}, and
  @{text "ALWAYS"}, @{text "ONCE"} and @{text "HISTORICALLY"} likewise produce an Until or a
  Since whose left operand is closed.  The general structure then carries a mapping from tuples
  to the last time point at which the left operand held, one such mapping per time point in the
  window.  When the left operand is closed it holds either for every valuation or for none, so
  ``the left operand held throughout @{text "[i, j)"}'' is a property of time points alone, and
  the answer at @{text i} is simply the union of the right operand's tables over a contiguous
  run of time points.

  Both ends of that run move to the right as @{text i} advances: the far end because a later
  @{text i} has a later timestamp and so admits later @{text j}, and the blocking end because
  the first time point at which the left operand fails can only move forward.  A sliding window
  whose ends both advance needs no per-time-point mapping.  This structure keeps the union of
  the window as a count for every tuple, so that adding or removing a table costs one update
  per tuple of that table, and keeps the answer itself as a set that changes only when a count
  reaches or leaves zero.  On a log where most time points contribute nothing -- which is what
  a bounded-future interval over a coarse timestamp sequence looks like -- most steps then
  touch nothing at all.

  Definitions only, no proofs; the structure is selected only where the conditions above hold
  and the general one is used otherwise.
\<close>

type_synonym evt_entry = "ts \<times> event_data table \<times> bool"

type_synonym evtaux = "ts queue \<times> evt_entry queue \<times> evt_entry queue \<times> nat \<times> bool \<times>
  (event_data tuple, nat) mapping \<times> event_data table \<times> event_data table list"

subsection \<open>The union of the window, as a count per tuple\<close>

definition evt_add :: "event_data table \<Rightarrow> (event_data tuple, nat) mapping \<times> event_data table \<Rightarrow>
    (event_data tuple, nat) mapping \<times> event_data table" where
  "evt_add T cc = fold (\<lambda>t (c, s). case Mapping.lookup c t of
       None \<Rightarrow> (Mapping.update t 1 c, Set.insert t s)
     | Some k \<Rightarrow> (Mapping.update t (k + 1) c, s)) (csorted_list_of_set T) cc"

definition evt_del :: "event_data table \<Rightarrow> (event_data tuple, nat) mapping \<times> event_data table \<Rightarrow>
    (event_data tuple, nat) mapping \<times> event_data table" where
  "evt_del T cc = fold (\<lambda>t (c, s). case Mapping.lookup c t of
       None \<Rightarrow> (c, s)
     | Some k \<Rightarrow> (if k \<le> 1 then (Mapping.delete t c, Set.remove t s)
                  else (Mapping.update t (k - 1) c, s))) (csorted_list_of_set T) cc"

subsection \<open>Extending the window\<close>

text \<open>The window is extended one time point at a time, and stops at the first one whose
timestamp is out of range or at the one after which the left operand fails.  Both bounds only
move to the right as the structure advances, so over a run each time point enters the window
once, and a step that extends it by nothing touches nothing.\<close>

function evt_extend :: "args \<Rightarrow> ts \<Rightarrow> evt_entry queue \<Rightarrow> evt_entry queue \<Rightarrow> bool \<Rightarrow>
    (event_data tuple, nat) mapping \<Rightarrow> event_data table \<Rightarrow>
    evt_entry queue \<times> evt_entry queue \<times> bool \<times> (event_data tuple, nat) mapping \<times> event_data table" where
  "evt_extend args ts0 win rest bend cnt cur =
     (if \<not> bend then (win, rest, bend, cnt, cur)
      else (case safe_hd rest of
              (None, rest') \<Rightarrow> (win, rest', bend, cnt, cur)
            | (Some e, rest') \<Rightarrow>
                (if memR (args_ivl args) (fst e - ts0)
                 then (case evt_add (fst (snd e)) (cnt, cur) of (cnt', cur') \<Rightarrow>
                         evt_extend args ts0 (append_queue e win) (tl_queue rest')
                           (snd (snd e)) cnt' cur')
                 else (win, rest', bend, cnt, cur))))"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(args, ts0, win, rest, bend, cnt, cur). length (linearize rest))")
     (fastforce split: prod.splits)+

declare evt_extend.simps[simp del]

subsection \<open>Operations\<close>

definition init_evt :: "args \<Rightarrow> evtaux" where
  "init_evt args = (empty_queue, empty_queue, empty_queue, 0, True, Mapping.empty, {}, [])"

definition length_evt :: "args \<Rightarrow> evtaux \<Rightarrow> nat" where
  "length_evt args aux = (case aux of (nts, win, rest, len, bend, cnt, cur, done) \<Rightarrow>
     length done + len)"

text \<open>One time point leaves the structure: the window is extended as far as its timestamp
  allows, the union of the window is the verdict, and the time point itself is dropped.\<close>

definition evt_step :: "args \<Rightarrow> ts \<Rightarrow> evtaux \<Rightarrow> evtaux" where
  "evt_step args ts0 aux = (case aux of (nts, win, rest, len, bend, cnt, cur, done) \<Rightarrow>
     (case evt_extend args ts0 win rest bend cnt cur of (win, rest, bend, cnt, cur) \<Rightarrow>
        (case safe_hd win of
           (None, win') \<Rightarrow>
             (case safe_hd rest of
                (None, rest') \<Rightarrow>
                  (tl_queue nts, win', rest', len - 1, bend, cnt, cur, {} # done)
              | (Some _, rest') \<Rightarrow>
                  (tl_queue nts, win', tl_queue rest', len - 1, bend, cnt, cur, {} # done))
         | (Some e, win') \<Rightarrow>
           (let win'' = tl_queue win';
                (cnt', cur') = evt_del (fst (snd e)) (cnt, cur);
                bend' = (if Queue.is_empty win'' then True else bend)
            in (tl_queue nts, win'', rest, len - 1, bend', cnt', cur', cur # done)))))"

text \<open>A time point leaves the structure as soon as no later one can contribute to it.  Walking
the pending timestamps directly avoids building a queue and a list only to take their length.\<close>

function evt_shift :: "args \<Rightarrow> ts \<Rightarrow> evtaux \<Rightarrow> evtaux" where
  "evt_shift args nt aux = (case aux of (nts, win, rest, len, bend, cnt, cur, done) \<Rightarrow>
     (case safe_hd nts of
        (None, nts') \<Rightarrow> (nts', win, rest, len, bend, cnt, cur, done)
      | (Some ts0, nts') \<Rightarrow>
        (if memR (args_ivl args) (nt - ts0) \<or> len = 0
         then (nts', win, rest, len, bend, cnt, cur, done)
         else evt_shift args nt (evt_step args ts0 (nts', win, rest, len, bend, cnt, cur, done)))))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(args, nt, (nts, win, rest, len, bend, cnt, cur, done)). len)")
     (auto simp: evt_step_def Let_def split: prod.splits option.splits)

declare evt_shift.simps[simp del]

definition add_new_evt :: "args \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow> evtaux \<Rightarrow> evtaux" where
  "add_new_evt args rel1 rel2 nt aux =
     (case evt_shift args nt aux of (nts, win, rest, len, bend, cnt, cur, done) \<Rightarrow>
       (let b = (if args_pos args then \<not> Set.is_empty rel1 else Set.is_empty rel1)
        in (append_queue nt nts, win, append_queue (nt, rel2, b) rest,
            len + 1, bend, cnt, cur, done)))"

definition eval_evt :: "args \<Rightarrow> ts \<Rightarrow> evtaux \<Rightarrow> event_data table list \<times> evtaux" where
  "eval_evt args nt aux =
     (case evt_shift args nt aux of (nts, win, rest, len, bend, cnt, cur, done) \<Rightarrow>
       (rev done, (nts, win, rest, len, bend, cnt, cur, [])))"

text \<open>The structure applies when the left operand is closed, the interval starts at zero so that
  every time point of the window contributes, and there is no aggregation.\<close>

definition evt_applies :: "args \<Rightarrow> bool" where
  "evt_applies args \<longleftrightarrow> args_agg args = None \<and> args_L args = {} \<and> memL (args_ivl args) 0"

subsection \<open>Heap structure or pure structure\<close>

definition use_heap_until :: bool where
  "use_heap_until = False"

text \<open>
  The heap structure for Until operators without aggregation, the pure deque structure of
  @{theory MFODL_Monitor_Devel.Optimized_Until_Deque} otherwise.
\<close>

datatype muaux_j = MUJ_imp muaux2 | MUJ_pure muaux_dq | MUJ_evt evtaux

text \<open>
  The heap structure is defined but not selected, and the condition below is the switch that
  turns it on again. Measured on P2 it is sixty times slower than the pure deque, and the
  reason is structural rather than a matter of constant factors. Every step of
  @{const eval_step_dq2} merges the mapping of the expiring time point into the mapping of the
  next one, so an entry is merged forward once per time point it survives. A persistent tree
  merges two mappings by sharing the parts that do not change, which costs
  @{text "O(m log (n/m))"} and leaves the untouched entries alone; a hash table has to read and
  re-insert every entry of one side, which costs @{text "O(m)"} with a hash and an equality
  test each. Over a window of @{text len} time points the first is near linear in the whole run
  and the second is quadratic. On the P2 prefix of 16000 time points the pure structure retires
  465 million instructions and this one 28 billion, of which 26% is hashing and a further 13%
  is the rehashing that the repeated insertion triggers.

  The lesson generalises beyond this structure: an imperative map wins where entries are
  written once and read often, and loses where the algorithm repeatedly merges maps that a
  persistent structure could share.
\<close>

definition init_u_j :: "args \<Rightarrow> muaux_j Heap" where
  "init_u_j args = (if args_agg args = None \<and> use_heap_until
     then do { d \<leftarrow> init_dq2 args; return (MUJ_imp d) }
     else if evt_applies args then return (MUJ_evt (init_evt args))
     else return (MUJ_pure (init_muaux_dq args)))"

fun add_new_u_j :: "args \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow> muaux_j \<Rightarrow> muaux_j Heap" where
  "add_new_u_j args rel1 rel2 nt (MUJ_imp d) = do { d \<leftarrow> add_new_dq2 args rel1 rel2 nt d; return (MUJ_imp d) }"
| "add_new_u_j args rel1 rel2 nt (MUJ_pure a) = return (MUJ_pure (add_new_muaux_dq args rel1 rel2 nt a))"
| "add_new_u_j args rel1 rel2 nt (MUJ_evt a) = return (MUJ_evt (add_new_evt args rel1 rel2 nt a))"

fun eval_u_j :: "args \<Rightarrow> ts \<Rightarrow> muaux_j \<Rightarrow> (event_data table list \<times> muaux_j) Heap" where
  "eval_u_j args nt (MUJ_imp d) = do { r \<leftarrow> eval_dq2 args nt d; return (fst r, MUJ_imp (snd r)) }"
| "eval_u_j args nt (MUJ_pure a) = return (let r = eval_muaux_dq args nt a in (fst r, MUJ_pure (snd r)))"
| "eval_u_j args nt (MUJ_evt a) = return (let r = eval_evt args nt a in (fst r, MUJ_evt (snd r)))"

(*<*)
end
(*>*)
