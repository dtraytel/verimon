(*<*)
theory Table_Imp
  imports "MFODL_Monitor_Devel.Imperative_Join"
begin
(*>*)

section \<open>Heap-resident tables\<close>

text \<open>
  Tables and the tuple-keyed mappings of the auxiliary structures as hash tables on the heap.
  Tables are built once and then read only, because the evaluation function stores the result
  of a subformula in the window of the operator above it and also hands it to the front end as
  a verdict; only the mappings inside the structures are updated in place.

  This theory contains definitions only. Nothing here is related to the pure implementation
  layer yet, and no operation is proved to agree with its pure counterpart; the imperative
  monitor built on top of it is checked against the verified kernel by differential testing
  until its performance is settled.

  Two adaptations are trusted for now: the hash of a tuple is OCaml's structural hash, and
  tuple equality is OCaml's structural equality.
\<close>

subsection \<open>Machine-level primitives\<close>

text \<open>
  The bucket index is computed in one step on the OCaml side: going through @{typ nat} would
  allocate an arbitrary-precision integer for the hash and another for the remainder on every
  lookup, and reading the array's length back from the heap would allocate a third. The
  capacity is therefore carried as a pure value and the index is a single primitive.
\<close>

definition teq :: "event_data tuple \<Rightarrow> event_data tuple \<Rightarrow> bool" where
  "teq x y = (x = y)"

definition ibucket :: "event_data tuple \<Rightarrow> integer \<Rightarrow> integer" where
  "ibucket t n = 0"

code_printing
  constant teq \<rightharpoonup> (OCaml) "(fun x y -> x = y)"
| constant ibucket \<rightharpoonup> (OCaml) "(fun t n -> Z.of'_int ((Hashtbl.hash t) mod (Z.to'_int n)))"

type_synonym 'v imap = "integer \<times> integer \<times> ((event_data tuple \<times> 'v) list) array"

fun hm_look_list :: "event_data tuple \<Rightarrow> (event_data tuple \<times> 'v) list \<Rightarrow> 'v option" where
  "hm_look_list x [] = None"
| "hm_look_list x (y # ys) = (if teq x (fst y) then Some (snd y) else hm_look_list x ys)"

fun hm_del_list :: "event_data tuple \<Rightarrow> (event_data tuple \<times> 'v) list \<Rightarrow> (event_data tuple \<times> 'v) list" where
  "hm_del_list x [] = []"
| "hm_del_list x (y # ys) = (if teq x (fst y) then ys else y # hm_del_list x ys)"

definition im_new :: "integer \<Rightarrow> ('v::heap) imap Heap" where
  "im_new n = (let m = (if n < 8 then 8 else n) in
     do { a \<leftarrow> Array.new' m []; return (m, 0, a) })"

definition im_size :: "('v::heap) imap \<Rightarrow> integer" where
  "im_size q = fst (snd q)"

definition im_lookup :: "('v::heap) imap \<Rightarrow> event_data tuple \<Rightarrow> 'v option Heap" where
  "im_lookup q x = (case q of (n, c, a) \<Rightarrow>
     do { b \<leftarrow> Array.nth' a (ibucket x n); return (hm_look_list x b) })"

partial_function (heap) im_fold_idx ::
  "((event_data tuple \<times> 'v) list \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ((event_data tuple \<times> 'v::heap) list) array \<Rightarrow>
    integer \<Rightarrow> integer \<Rightarrow> 'b \<Rightarrow> 'b Heap" where
  [code]:
  "im_fold_idx f a i n acc = (if n \<le> i then return acc
     else do { b \<leftarrow> Array.nth' a i; im_fold_idx f a (i + 1) n (f b acc) })"

definition im_to_list :: "('v::heap) imap \<Rightarrow> (event_data tuple \<times> 'v) list Heap" where
  "im_to_list q = (case q of (n, c, a) \<Rightarrow> im_fold_idx (\<lambda>b acc. b @ acc) a 0 n [])"

partial_function (heap) im_fill :: "('v::heap) imap \<Rightarrow> (event_data tuple \<times> 'v) list \<Rightarrow> ('v imap) Heap" where
  [code]:
  "im_fill q kvs = (case kvs of [] \<Rightarrow> return q
     | xv # r \<Rightarrow> (case q of (n, c, a) \<Rightarrow> (let i = ibucket (fst xv) n in
        do { b \<leftarrow> Array.nth' a i; _ \<leftarrow> Array.upd' a i (xv # b); im_fill (n, c + 1, a) r })))"

definition im_grow :: "('v::heap) imap \<Rightarrow> ('v imap) Heap" where
  "im_grow q = (case q of (n, c, a) \<Rightarrow>
     do { kvs \<leftarrow> im_to_list q; q' \<leftarrow> im_new (2 * n); im_fill q' kvs })"

definition im_update :: "('v::heap) imap \<Rightarrow> event_data tuple \<Rightarrow> 'v \<Rightarrow> ('v imap) Heap" where
  "im_update q x v = (case q of (n, c, a) \<Rightarrow> (let i = ibucket x n in
     do { b \<leftarrow> Array.nth' a i;
          (case hm_look_list x b of
             Some _ \<Rightarrow> do { _ \<leftarrow> Array.upd' a i ((x, v) # hm_del_list x b); return q }
           | None \<Rightarrow> do { _ \<leftarrow> Array.upd' a i ((x, v) # b);
                          if c + 1 < n then return (n, c + 1, a) else im_grow (n, c + 1, a) }) }))"

definition im_delete :: "('v::heap) imap \<Rightarrow> event_data tuple \<Rightarrow> ('v imap) Heap" where
  "im_delete q x = (case q of (n, c, a) \<Rightarrow> (let i = ibucket x n in
     do { b \<leftarrow> Array.nth' a i;
          (case hm_look_list x b of None \<Rightarrow> return q
           | Some _ \<Rightarrow> do { _ \<leftarrow> Array.upd' a i (hm_del_list x b); return (n, c - 1, a) }) }))"

definition im_count :: "(event_data tuple \<times> 'v) list \<Rightarrow> integer" where
  "im_count b = integer_of_nat (length b)"

partial_function (heap) im_filter_idx ::
  "(event_data tuple \<Rightarrow> bool) \<Rightarrow> ((event_data tuple \<times> 'v::heap) list) array \<Rightarrow>
    integer \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> integer Heap" where
  [code]:
  "im_filter_idx p a i n c = (if n \<le> i then return c
     else do { b \<leftarrow> Array.nth' a i;
               (let b' = filter (\<lambda>kv. p (fst kv)) b in
                do { _ \<leftarrow> (if im_count b' = im_count b then return () else Array.upd' a i b');
                     im_filter_idx p a (i + 1) n (c - (im_count b - im_count b')) }) })"

text \<open>
  Keeping the keys that satisfy a predicate, in one pass over the buckets. Reading the whole
  map back as a list first, which is what a generic interface forces, allocates a cons cell per
  entry on every call; the Since structure does this once per time point when the operator has
  join columns.
\<close>

definition im_filter :: "(event_data tuple \<Rightarrow> bool) \<Rightarrow> ('v::heap) imap \<Rightarrow> ('v imap) Heap" where
  "im_filter p q = (case q of (n, c, a) \<Rightarrow> do { c \<leftarrow> im_filter_idx p a 0 n c; return (n, c, a) })"

subsection \<open>A hash set of tuples on the heap\<close>

type_synonym itbl = "unit imap"

definition ht_new :: "integer \<Rightarrow> itbl Heap" where
  "ht_new n = im_new n"

definition ht_ins :: "itbl \<Rightarrow> event_data tuple \<Rightarrow> itbl Heap" where
  "ht_ins q x = im_update q x ()"

definition ht_mem :: "itbl \<Rightarrow> event_data tuple \<Rightarrow> bool Heap" where
  "ht_mem q x = do { v \<leftarrow> im_lookup q x; return (v \<noteq> None) }"

partial_function (heap) ht_ins_list :: "itbl \<Rightarrow> event_data tuple list \<Rightarrow> itbl Heap" where
  [code]:
  "ht_ins_list q xs = (case xs of [] \<Rightarrow> return q
    | y # ys \<Rightarrow> do { q \<leftarrow> ht_ins q y; ht_ins_list q ys })"

definition ht_of_list :: "event_data tuple list \<Rightarrow> itbl Heap" where
  "ht_of_list xs = do { q \<leftarrow> ht_new (2 * integer_of_nat (length xs)); ht_ins_list q xs }"

definition ht_to_list :: "itbl \<Rightarrow> event_data tuple list Heap" where
  "ht_to_list q = do { kvs \<leftarrow> im_to_list q; return (map fst kvs) }"

(*<*)
end
(*>*)
