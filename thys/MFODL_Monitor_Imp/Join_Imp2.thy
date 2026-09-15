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

text \<open>
  Building an index pays only once the probing side is long enough to amortise it. Hashing a
  tuple walks its whole representation, whereas a lookup in a small comparison-based tree is a
  handful of comparisons that stop at the first differing column, so below a few hundred tuples
  the tree wins. The threshold is read from a mutable flag so that it can be measured without
  regenerating the kernel; the front end exposes it as @{text "-heap_join_min"}.
\<close>

code_printing code_module ConfigImp \<rightharpoonup> (OCaml)
\<open>module ConfigImp : sig
  val heap_join_min : int ref
end = struct
  let heap_join_min = ref 256
end\<close>

definition heap_join_min :: integer where
  "heap_join_min = 256"

code_printing
  constant heap_join_min \<rightharpoonup> (OCaml) "(Z.of'_int '!ConfigImp.heap'_join'_min)"

text \<open>
  The size of the indexed table decides, and not the number of probes: hashing a tuple walks
  its whole representation, whereas a descent through a small comparison-based tree is a few
  comparisons that stop at the first column in which the tuples differ, so for a short index
  the tree is cheaper however often it is read. Measured on the wide logs of Section 14, an
  index of a hundred tuples probed five hundred times still loses, while one of two thousand
  tuples wins; the threshold is a flag so that it can be moved without regenerating the kernel.
\<close>

definition heap_join_ok :: "event_data tuple list \<Rightarrow> bool" where
  "heap_join_ok idx = (heap_join_min \<le> integer_of_nat (length idx))"

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
     | x # r \<Rightarrow> (let k = proj_tuple msk x; h = ihash k in
         do { v \<leftarrow> im_lookup_h q h k;
              q \<leftarrow> im_update_h q h k (case v of None \<Rightarrow> [x] | Some l \<Rightarrow> x # l);
              idx_ins_list msk r q }))"

partial_function (heap) probe_all :: "bool list \<Rightarrow> jidx \<Rightarrow>
    event_data tuple list \<Rightarrow> event_data table \<Rightarrow> event_data table Heap" where
  [code]:
  "probe_all msk q xs acc = (case xs of [] \<Rightarrow> return acc
     | x # r \<Rightarrow> do { v \<leftarrow> im_lookup q (proj_tuple msk x);
                      probe_all msk q r (case v of None \<Rightarrow> acc
                        | Some l \<Rightarrow> fold (\<lambda>y acc. case join1 (x, y) of None \<Rightarrow> acc
                                            | Some z \<Rightarrow> Set.insert z acc) l acc) })"

definition probe_join_j :: "nat \<Rightarrow> nat set \<Rightarrow> event_data tuple list \<Rightarrow> nat set \<Rightarrow>
    event_data tuple list \<Rightarrow> event_data table Heap" where
  "probe_join_j n A xs B ys = (let msk = join_mask n (A \<inter> B) in
     do { q \<leftarrow> im_new (2 * integer_of_nat (length ys));
          q \<leftarrow> idx_ins_list msk ys q;
          probe_all msk q xs {} })"

text \<open>
  In each case the table that becomes the index is read as a list first; if it turns out to be
  short, the pure join runs instead and the list is discarded. The list is the same one the
  imperative branch would have built, so nothing is done twice on the branch that pays.
\<close>

definition bin_join_j :: "nat \<Rightarrow> nat set \<Rightarrow> event_data table \<Rightarrow> bool \<Rightarrow> nat set \<Rightarrow> event_data table \<Rightarrow>
    event_data table Heap" where
  "bin_join_j n A t pos A' t' =
    (if \<not> use_heap_join then return (bin_join n A t pos A' t')
     else if t = {} then return {}
     else if t' = {} then return (if pos then {} else t)
     else if A' = {} then return (if (pos \<longleftrightarrow> replicate n None \<in> t') then t else {})
     else if A' = A then (let ys = csorted_list_of_set t' in
       if \<not> heap_join_ok ys then return (bin_join n A t pos A' t')
       else do { q \<leftarrow> ht_of_list ys;
                 probe_filter (\<lambda>as. as) pos q (csorted_list_of_set t) {} })
     else if A' \<subseteq> A then (let ys = csorted_list_of_set t' in
       if \<not> heap_join_ok ys then return (bin_join n A t pos A' t')
       else do { q \<leftarrow> ht_of_list ys;
                 probe_filter (proj_tuple (join_mask n A')) pos q (csorted_list_of_set t) {} })
     else if A \<subseteq> A' \<and> pos then (let xs = csorted_list_of_set t in
       if \<not> heap_join_ok xs then return (bin_join n A t pos A' t')
       else do { q \<leftarrow> ht_of_list xs;
                 probe_filter (proj_tuple (join_mask n A)) pos q (csorted_list_of_set t') {} })
     else if pos then (let ys = csorted_list_of_set t' in
       if \<not> heap_join_ok ys then return (bin_join n A t pos A' t')
       else probe_join_j n A (csorted_list_of_set t) A' ys)
     else return (join t pos t'))"

subsection \<open>Multi-way joins\<close>

text \<open>
  A conjunction of more than two conjuncts, and in fact every conjunction whose operands are
  not both ``simple'' in the sense of @{const is_simple_eq}, is compiled to @{term MAnds} and
  evaluated by @{const mmulti_join}, not by @{const bin_join}. The binary join above is
  therefore never reached from a realistic formula, and the multi-way join has to be lifted as
  well for the heap index to do any work at all. The left-deep sequence of binary joins and the
  following anti-joins are cloned one to one; only @{const bin_join} is replaced by
  @{const bin_join_j}.
\<close>

fun mmulti_join_pos_j :: "nat \<Rightarrow> nat set \<Rightarrow> event_data table \<Rightarrow>
    (nat set \<times> event_data table) list \<Rightarrow> (nat set \<times> event_data table) Heap" where
  "mmulti_join_pos_j n A t [] = return (A, t)"
| "mmulti_join_pos_j n A t ((A', t') # L) =
     do { t \<leftarrow> bin_join_j n A t True A' t'; mmulti_join_pos_j n (A \<union> A') t L }"

fun mmulti_join_neg_j :: "nat \<Rightarrow> nat set \<Rightarrow> event_data table \<Rightarrow>
    (nat set \<times> event_data table) list \<Rightarrow> event_data table Heap" where
  "mmulti_join_neg_j n A t [] = return t"
| "mmulti_join_neg_j n A t ((A', t') # L) =
     do { t \<leftarrow> bin_join_j n A t False A' t'; mmulti_join_neg_j n A t L }"

definition mmulti_join_j :: "nat \<Rightarrow> nat set list \<Rightarrow> nat set list \<Rightarrow> event_data table list \<Rightarrow>
    event_data table Heap" where
  "mmulti_join_j n A_pos A_neg L =
     (if use_generic_join \<or> \<not> use_heap_join then return (mmulti_join n A_pos A_neg L)
      else case zip A_pos L of [] \<Rightarrow> return {}
        | At # Lpos \<Rightarrow> (case At of (A, t) \<Rightarrow>
            do { p \<leftarrow> mmulti_join_pos_j n A t Lpos;
                 mmulti_join_neg_j n (fst p) (snd p) (zip A_neg (drop (length A_pos) L)) }))"

partial_function (heap) mebufn_take_j :: "(event_data table list \<Rightarrow> event_data table Heap) \<Rightarrow>
    event_data table mbuf_t \<Rightarrow> event_data mebufn \<Rightarrow> (event_data table mbuf_t \<times> event_data mebufn) Heap" where
  [code]:
  "mebufn_take_j f z buf = (if buf = [] \<or> (\<exists>x \<in> set buf. mbuf_t_is_empty x) then return (z, buf)
     else do { x \<leftarrow> f (map (the \<circ> fst \<circ> mbuf_t_cases) buf);
               mebufn_take_j f (z @@ [x]) (map (snd \<circ> mbuf_t_cases) buf) })"

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
