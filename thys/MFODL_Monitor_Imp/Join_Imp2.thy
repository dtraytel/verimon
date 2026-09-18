(*<*)
theory Join_Imp2
  imports Table_Imp "MFODL_Monitor_Devel.Optimized_Join"
begin
(*>*)

section \<open>The binary join over a heap-resident index\<close>

text \<open>
  The one case of @{const bin_join} in which a hash index beats the comparison-based tree, with
  the probed side indexed once per call, and the multi-way join that reaches it. Definitions
  only, no proofs.
\<close>

definition use_heap_join :: bool where
  "use_heap_join = True"

text \<open>
  The heap index is used in one case only: the one in which neither operand's columns contain
  the other's. The cases the pure code has a good algorithm for are left to it, and the measured
  cost of taking them away from it is steep. When the column sets are equal the join is a set
  intersection or difference, which on two red-black trees over the same order is a linear merge
  that exploits their shared structure rather than a lookup per tuple. When one column set
  contains the other, the indexed side is forced by the shape of the join and cannot be chosen,
  so the index is often the larger table built to be probed a few times; that is what the
  anti-joins of @{text P2} and @{text P3} are. Routing those two families through an index made
  @{text P2} eleven times slower and @{text P3} fifty times, and even requiring the index to be
  no longer than the probing side still left @{text P2} 60% slower.

  The remaining case is the one the pure code has no good algorithm for: it either builds a
  pure index (@{text probe_join_n}) or, if the operands are not complete on the common columns,
  degenerates to a nested loop. Its guard is reproduced here so that the index is built on the
  same tuples the pure code would index.

  Here either table may be indexed, and the smaller one is, as in the pure code: indexing costs
  a hash per tuple of the indexed side and probing one per tuple of the other, so indexing the
  larger side buys a big index that is read a few times. Getting this the wrong way round cost
  more than the index saved wherever the two operands differ much in size; on the standard
  @{text complex} benchmark it is the difference between a 27% loss and a 16% gain. A threshold
  on the size of the indexed side is a flag as well, but its default is zero: once the case and
  the side are chosen, an index of any size was at least as good as the pure code on every
  benchmark measured.
\<close>

definition heap_join_ok :: "event_data tuple list \<Rightarrow> bool" where
  "heap_join_ok idx = (heap_join_min \<le> integer_of_nat (length idx))"

text \<open>
  The index maps a tuple's projection onto the common columns to the tuples of the indexed
  table that have it, so that each tuple of the probing side is combined only with the ones it
  can join with.
\<close>

type_synonym jidx = "(event_data tuple, event_data tuple list) imap"

text \<open>
  The operations on a heap map take the value type's @{class heap} dictionary, and the code
  generator builds it at every call: on the join of @{text "A(x,y) AND (ONCE[0,20] B(y,z))"} the
  nested type representations of a list and of an option are 28.5 and 14.4 million words, and
  with the monadic closures around them the dictionary is 42\% of everything the join allocates.  The index's value type is closed, so the dictionary can be built once.
\<close>

setup \<open>Monomorphize.box_cmd
  [("im_lookup_proj", "jidx_lookup_v", ["event_data tuple list"]),
   ("im_lookup_h", "jidx_lookup_h_v", ["event_data tuple", "event_data tuple list"]),
   ("im_update_h", "jidx_update_h_v", ["event_data tuple", "event_data tuple list"])]\<close>

partial_function (heap) idx_ins_list :: "bool list \<Rightarrow> event_data tuple list \<Rightarrow> jidx \<Rightarrow> jidx Heap" where
  [code]:
  "idx_ins_list msk xs q = (case xs of [] \<Rightarrow> return q
     | x # r \<Rightarrow> (let k = proj_tuple msk x; h = ihash k in
         do { v \<leftarrow> im_lookup_h teq q h k;
              q \<leftarrow> im_update_h teq q h k (case v of None \<Rightarrow> [x] | Some l \<Rightarrow> x # l);
              idx_ins_list msk r q }))"

text \<open>
  The joined tuples are inserted into the result table as they are produced. Collecting them in
  a list and building the table in one pass was measured and is slower: the insertion
  deduplicates as it goes, and a join over a small domain produces many more tuples than it has
  distinct results (see @{text Monomorphic_Code} and Section 15.6 of
  \<^file>\<open>../../EFFICIENCY.md\<close>).
\<close>

partial_function (heap) probe_all :: "bool list \<Rightarrow> jidx \<Rightarrow>
    event_data tuple list \<Rightarrow> event_data table \<Rightarrow> event_data table Heap" where
  [code]:
  "probe_all msk q xs acc = (case xs of [] \<Rightarrow> return acc
     | x # r \<Rightarrow> do { v \<leftarrow> im_lookup_proj q msk x;
                      probe_all msk q r (case v of None \<Rightarrow> acc
                        | Some l \<Rightarrow> fold (\<lambda>y acc. case join1 (x, y) of None \<Rightarrow> acc
                                            | Some z \<Rightarrow> Set.insert z acc) l acc) })"

definition probe_join_j :: "nat \<Rightarrow> nat set \<Rightarrow> event_data tuple list \<Rightarrow> nat set \<Rightarrow>
    event_data tuple list \<Rightarrow> event_data table Heap" where
  "probe_join_j n A xs B ys = (let msk = join_mask n (A \<inter> B) in
     do { q \<leftarrow> im_new (2 * integer_of_nat (length ys));
          q \<leftarrow> idx_ins_list msk ys q;
          probe_all msk q xs {} })"

definition bin_join_j :: "nat \<Rightarrow> nat set \<Rightarrow> event_data table \<Rightarrow> bool \<Rightarrow> nat set \<Rightarrow> event_data table \<Rightarrow>
    event_data table Heap" where
  "bin_join_j n A t pos A' t' =
    (if \<not> use_heap_join \<or> \<not> pos \<or> t = {} \<or> t' = {} \<or> A' = {} \<or> A' \<subseteq> A \<or> A \<subseteq> A'
       \<or> \<not> finite t \<or> \<not> finite t'
       \<or> \<not> (let c = complete_with (A \<inter> A') n in (\<forall>x \<in> t. c x) \<and> (\<forall>y \<in> t'. c y))
     then return (bin_join n A t pos A' t')
     else (let xs = csorted_list_of_set t; ys = csorted_list_of_set t';
               idx = (if length xs \<le> length ys then xs else ys);
               prb = (if length xs \<le> length ys then ys else xs) in
       if \<not> heap_join_ok idx then return (bin_join n A t pos A' t')
       else probe_join_j n A prb A' idx))"

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
