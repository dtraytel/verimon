(*<*)
theory Join_Imp2
  imports Table_Imp "MFODL_Monitor_Devel.Optimized_Join"
begin
(*>*)

section \<open>The binary join over a heap-resident index\<close>

text \<open>
  The cases of @{const bin_join} that test every tuple of one table for membership in the other,
  with the probed side indexed by a hash set built once per call. This is the access pattern in
  which an imperative structure should win: the index is written once and read as often as the
  probing side is long. Definitions only, no proofs.
\<close>

definition use_heap_join :: bool where
  "use_heap_join = True"

partial_function (heap) probe_filter :: "(event_data tuple \<Rightarrow> event_data tuple) \<Rightarrow> bool \<Rightarrow> itbl \<Rightarrow>
    event_data tuple list \<Rightarrow> event_data table \<Rightarrow> event_data table Heap" where
  [code]:
  "probe_filter pr pos q xs acc = (case xs of [] \<Rightarrow> return acc
     | x # r \<Rightarrow> do { b \<leftarrow> ht_mem q (pr x);
                      probe_filter pr pos q r (if b = pos then Set.insert x acc else acc) })"

subsection \<open>The indexed probe join\<close>

text \<open>
  The general case, where neither side's columns contain the other's: the smaller side is
  indexed on the columns the two share, and every tuple of the other side probes it. This is
  Measured outcome: neither this nor the cases above changes anything on the benchmarks,
  because a conjunction is compiled to a multi-way conjunction whose joins go through
  @{const mmulti_join}, not through @{const bin_join}. The pure kernel already indexes that
  join (Section 7f of EFFICIENCY.md), and the tables it joins hold about fifty tuples, where
  the micro-benchmark in evaluation/table_bench puts a hash set behind a red-black tree. The
  switch above therefore stays on only because it costs nothing: with it the two conjunctive
  benchmarks retire 2,279,460,795 and 12,648,433,147 instructions, without it 2,279,349,289
  and 12,648,740,584.
\<close>

type_synonym jidx = "(event_data tuple list) imap"

partial_function (heap) idx_ins_list :: "bool list \<Rightarrow> event_data tuple list \<Rightarrow> jidx \<Rightarrow> jidx Heap" where
  [code]:
  "idx_ins_list msk xs q = (case xs of [] \<Rightarrow> return q
     | x # r \<Rightarrow> do { v \<leftarrow> im_lookup q (proj_tuple msk x);
                       q \<leftarrow> im_update q (proj_tuple msk x)
                              (case v of None \<Rightarrow> [x] | Some l \<Rightarrow> x # l);
                       idx_ins_list msk r q })"

partial_function (heap) probe_all :: "bool list \<Rightarrow> jidx \<Rightarrow>
    event_data tuple list \<Rightarrow> event_data table \<Rightarrow> event_data table Heap" where
  [code]:
  "probe_all msk q xs acc = (case xs of [] \<Rightarrow> return acc
     | x # r \<Rightarrow> do { v \<leftarrow> im_lookup q (proj_tuple msk x);
                      probe_all msk q r (case v of None \<Rightarrow> acc
                        | Some l \<Rightarrow> fold (\<lambda>y acc. case join1 (x, y) of None \<Rightarrow> acc
                                            | Some z \<Rightarrow> Set.insert z acc) l acc) })"

definition probe_join_j :: "nat \<Rightarrow> nat set \<Rightarrow> event_data table \<Rightarrow> nat set \<Rightarrow> event_data table \<Rightarrow>
    event_data table Heap" where
  "probe_join_j n A t B t' = (let msk = join_mask n (A \<inter> B) in
     do { q \<leftarrow> im_new (2 * integer_of_nat (card t'));
          q \<leftarrow> idx_ins_list msk (csorted_list_of_set t') q;
          probe_all msk q (csorted_list_of_set t) {} })"

definition bin_join_j :: "nat \<Rightarrow> nat set \<Rightarrow> event_data table \<Rightarrow> bool \<Rightarrow> nat set \<Rightarrow> event_data table \<Rightarrow>
    event_data table Heap" where
  "bin_join_j n A t pos A' t' =
    (if \<not> use_heap_join then return (bin_join n A t pos A' t')
     else if t = {} then return {}
     else if t' = {} then return (if pos then {} else t)
     else if A' = {} then return (if (pos \<longleftrightarrow> replicate n None \<in> t') then t else {})
     else if A' = A then do { q \<leftarrow> ht_of_list (csorted_list_of_set t');
                              probe_filter (\<lambda>as. as) pos q (csorted_list_of_set t) {} }
     else if A' \<subseteq> A then do { q \<leftarrow> ht_of_list (csorted_list_of_set t');
                                probe_filter (proj_tuple (join_mask n A')) pos q (csorted_list_of_set t) {} }
     else if A \<subseteq> A' \<and> pos then do { q \<leftarrow> ht_of_list (csorted_list_of_set t);
                                        probe_filter (proj_tuple (join_mask n A)) pos q (csorted_list_of_set t') {} }
     else if pos then probe_join_j n A t A' t'
     else return (join t pos t'))"

partial_function (heap) mebuf2_take_j :: "(event_data table \<Rightarrow> event_data table \<Rightarrow> event_data table Heap) \<Rightarrow>
    event_data mebuf2 \<Rightarrow> (event_data table list \<times> event_data mebuf2) Heap" where
  [code]:
  "mebuf2_take_j f buf = (case buf of (xs, ys) \<Rightarrow>
    (case mbuf_t_cases xs of (None, xs') \<Rightarrow> return ([], (xs', ys)) | (Some x, xs') \<Rightarrow>
    (case mbuf_t_cases ys of (None, ys') \<Rightarrow> return ([], (x ## xs', ys')) | (Some y, ys') \<Rightarrow>
    do { z \<leftarrow> f x y; r \<leftarrow> mebuf2_take_j f (xs', ys'); return (z # fst r, snd r) })))"

(*<*)
end
(*>*)
