(*<*)
theory Table_Imp
  imports "MFODL_Monitor_Devel.Monomorphic_Code"
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
  Hashing a tuple is the single most expensive step of every map operation: it walks the
  tuple's representation, whereas everything else around it is a handful of machine
  instructions. The hash is therefore computed as rarely as possible.

  Three measures keep the number of calls down. The hash of a key is stored next to the key
  in its bucket, so growing the table redistributes the entries without looking at a single
  key again, and a bucket scan rejects a colliding entry by comparing two machine integers
  instead of two tuples. The capacity is a power of two, so the bucket index is a bitwise
  and rather than a division. And every operation comes in a variant that takes the hash as
  an argument, so a lookup followed by an update or a deletion of the same key -- the shape
  of nearly every loop in the structures below -- hashes once instead of twice.
\<close>

text \<open>Hashes live in the array next to the keys, so the target type must be storable.\<close>

instance integer :: heap ..

text \<open>
  A threshold worth measuring rather than fixing, so it is read from a mutable flag; the front
  end exposes it as @{text "-heap_join_min"}.
\<close>

code_printing code_module ConfigImp \<rightharpoonup> (OCaml)
\<open>module ConfigImp : sig
  val heap_join_min : int ref
end = struct
  let heap_join_min = ref 0
end\<close>

definition heap_join_min :: integer where
  "heap_join_min = 0"

code_printing
  constant heap_join_min \<rightharpoonup> (OCaml) "(Z.of'_int '!ConfigImp.heap'_join'_min)"

text \<open>
  Equality of two tuples.  Stated as @{text "x = y"} it becomes OCaml's polymorphic comparison,
  which on the join below costs 158M instructions; the type is known here too.
\<close>

fun oeq :: "event_data option \<Rightarrow> event_data option \<Rightarrow> bool" where
  "oeq None None = True"
| "oeq (Some a) (Some b) = (a = b)"
| "oeq None (Some b) = False"
| "oeq (Some a) None = False"

fun teq :: "event_data tuple \<Rightarrow> event_data tuple \<Rightarrow> bool" where
  "teq [] ys = List.null ys"
| "teq (x # xs) [] = False"
| "teq (x # xs) (y # ys) = (oeq x y \<and> teq xs ys)"

text \<open>
  A probe looks up the projection of a tuple, which the obvious code builds and throws away once
  per probed tuple.  Hashing and comparing against the mask directly leaves the projection
  unbuilt; both agree with @{const proj_tuple} clause by clause.
\<close>

fun teq_proj :: "bool list \<Rightarrow> event_data tuple \<Rightarrow> event_data tuple \<Rightarrow> bool" where
  "teq_proj [] xs k = List.null k"
| "teq_proj (b # bs) [] k = List.null k"
| "teq_proj (b # bs) (x # xs) [] = False"
| "teq_proj (b # bs) (x # xs) (y # ys) =
     ((if b then oeq x y else oeq None y) \<and> teq_proj bs xs ys)"

definition ihash_proj :: "bool list \<Rightarrow> event_data tuple \<Rightarrow> integer" where
  "ihash_proj m t = 0"

text \<open>
  The hash of a tuple.  The obvious implementation, OCaml's polymorphic @{text Hashtbl.hash},
  walks an unknown structure with a work queue and a node budget, and on the join of a formula
  like @{text "A(x,y) AND (ONCE[0,20] B(y,z))"} it costs 378 instructions per call over 2.4
  million calls.  The structure is not unknown here: a list of optional event data.  Walking it
  directly, with @{text Z.hash} for the integers, is the same hash function's job done with the
  type in hand.  Only determinism is required of it, since a bucket entry is confirmed by
  @{const teq}.
\<close>

definition ihash :: "event_data tuple \<Rightarrow> integer" where
  "ihash t = 0"

definition ibkt :: "integer \<Rightarrow> integer \<Rightarrow> integer" where
  "ibkt h n = 0"

code_printing
  constant ihash \<rightharpoonup> (OCaml) "(fun t -> let rec go h l = (match l with [] -> h | None :: r -> go (h * 31) r | Some (EInt z) :: r -> go (h * 31 + Z.hash z) r | Some (EFloat f) :: r -> go (h * 31 + Hashtbl.hash f) r | Some (EString s) :: r -> go (h * 31 + Hashtbl.hash s) r) in Z.of'_int ((go 17 t) land 1073741823))"
| constant ihash_proj \<rightharpoonup> (OCaml) "(fun m t -> let rec go h ms l = (match ms, l with [], uu -> h | uv, [] -> h | false :: mr, uw :: r -> go (h * 31) mr r | true :: mr, None :: r -> go (h * 31) mr r | true :: mr, Some (EInt z) :: r -> go (h * 31 + Z.hash z) mr r | true :: mr, Some (EFloat f) :: r -> go (h * 31 + Hashtbl.hash f) mr r | true :: mr, Some (EString s) :: r -> go (h * 31 + Hashtbl.hash s) mr r) in Z.of'_int ((go 17 m t) land 1073741823))"
| constant ibkt \<rightharpoonup> (OCaml) "(fun h n -> Z.logand h (Z.pred n))"

text \<open>
  An entry is a hash, a key and a value. The capacity is carried as a pure value rather than
  read back from the heap, because reading the array's length allocates an arbitrary-precision
  integer on every access.
\<close>

type_synonym 'v ientry = "integer \<times> event_data tuple \<times> 'v"

type_synonym 'v imap = "integer \<times> integer \<times> (('v ientry) list) array"

fun hm_look_list :: "integer \<Rightarrow> event_data tuple \<Rightarrow> ('v ientry) list \<Rightarrow> 'v option" where
  "hm_look_list h x [] = None"
| "hm_look_list h x (y # ys) =
     (if h = fst y \<and> teq x (fst (snd y)) then Some (snd (snd y)) else hm_look_list h x ys)"

fun hm_del_list :: "integer \<Rightarrow> event_data tuple \<Rightarrow> ('v ientry) list \<Rightarrow> ('v ientry) list" where
  "hm_del_list h x [] = []"
| "hm_del_list h x (y # ys) =
     (if h = fst y \<and> teq x (fst (snd y)) then ys else y # hm_del_list h x ys)"

text \<open>
  Capacities are powers of two of at least eight, so that the bucket index is the hash masked
  with the capacity minus one. The fuel bounds the doubling by the width of a machine word.
\<close>

fun im_cap_aux :: "nat \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> integer" where
  "im_cap_aux 0 c n = c"
| "im_cap_aux (Suc k) c n = (if n \<le> c then c else im_cap_aux k (2 * c) n)"

definition im_cap :: "integer \<Rightarrow> integer" where
  "im_cap n = im_cap_aux 64 8 n"

definition im_new :: "integer \<Rightarrow> ('v::heap) imap Heap" where
  "im_new n = (let m = im_cap n in do { a \<leftarrow> Array.new' m []; return (m, 0, a) })"

definition im_size :: "('v::heap) imap \<Rightarrow> integer" where
  "im_size q = fst (snd q)"

subsection \<open>Operations\<close>

text \<open>
  The hash-taking variants are the primitive ones; the others hash and delegate.
\<close>

definition im_lookup_h :: "('v::heap) imap \<Rightarrow> integer \<Rightarrow> event_data tuple \<Rightarrow> 'v option Heap" where
  "im_lookup_h q h x = (case q of (n, c, a) \<Rightarrow>
     do { b \<leftarrow> Array.nth' a (ibkt h n); return (hm_look_list h x b) })"

definition im_lookup :: "('v::heap) imap \<Rightarrow> event_data tuple \<Rightarrow> 'v option Heap" where
  "im_lookup q x = im_lookup_h q (ihash x) x"

fun hm_look_list_proj :: "integer \<Rightarrow> bool list \<Rightarrow> event_data tuple \<Rightarrow> ('v ientry) list \<Rightarrow> 'v option" where
  "hm_look_list_proj h m x [] = None"
| "hm_look_list_proj h m x (y # ys) =
     (if h = fst y \<and> teq_proj m x (fst (snd y)) then Some (snd (snd y))
      else hm_look_list_proj h m x ys)"

definition im_lookup_proj :: "('v::heap) imap \<Rightarrow> bool list \<Rightarrow> event_data tuple \<Rightarrow> 'v option Heap" where
  "im_lookup_proj q m x = (case q of (n, c, a) \<Rightarrow>
     (let h = ihash_proj m x in
      do { b \<leftarrow> Array.nth' a (ibkt h n); return (hm_look_list_proj h m x b) }))"

partial_function (heap) im_fold_idx ::
  "(('v ientry) list \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> (('v::heap) ientry list) array \<Rightarrow>
    integer \<Rightarrow> integer \<Rightarrow> 'b \<Rightarrow> 'b Heap" where
  [code]:
  "im_fold_idx f a i n acc = (if n \<le> i then return acc
     else do { b \<leftarrow> Array.nth' a i; im_fold_idx f a (i + 1) n (f b acc) })"

definition im_entries :: "('v::heap) imap \<Rightarrow> ('v ientry) list Heap" where
  "im_entries q = (case q of (n, c, a) \<Rightarrow> im_fold_idx (\<lambda>b acc. b @ acc) a 0 n [])"

definition im_to_list :: "('v::heap) imap \<Rightarrow> (event_data tuple \<times> 'v) list Heap" where
  "im_to_list q = do { kvs \<leftarrow> im_entries q; return (map snd kvs) }"

text \<open>
  Redistributing the entries of a grown table uses the stored hashes, so no key is hashed
  again. This is the step that dominated the profile of the structures before: a table that
  ends up with \<open>n\<close> entries hashes each of them once more for every doubling it survives.
\<close>

partial_function (heap) im_fill :: "('v::heap) imap \<Rightarrow> ('v ientry) list \<Rightarrow> ('v imap) Heap" where
  [code]:
  "im_fill q kvs = (case kvs of [] \<Rightarrow> return q
     | e # r \<Rightarrow> (case q of (n, c, a) \<Rightarrow> (let i = ibkt (fst e) n in
        do { b \<leftarrow> Array.nth' a i; _ \<leftarrow> Array.upd' a i (e # b); im_fill (n, c + 1, a) r })))"

definition im_grow :: "('v::heap) imap \<Rightarrow> ('v imap) Heap" where
  "im_grow q = (case q of (n, c, a) \<Rightarrow>
     do { kvs \<leftarrow> im_entries q; q' \<leftarrow> im_new (2 * n); im_fill q' kvs })"

definition im_update_h :: "('v::heap) imap \<Rightarrow> integer \<Rightarrow> event_data tuple \<Rightarrow> 'v \<Rightarrow> ('v imap) Heap" where
  "im_update_h q h x v = (case q of (n, c, a) \<Rightarrow> (let i = ibkt h n in
     do { b \<leftarrow> Array.nth' a i;
          (case hm_look_list h x b of
             Some _ \<Rightarrow> do { _ \<leftarrow> Array.upd' a i ((h, x, v) # hm_del_list h x b); return q }
           | None \<Rightarrow> do { _ \<leftarrow> Array.upd' a i ((h, x, v) # b);
                          if c + 1 < n then return (n, c + 1, a) else im_grow (n, c + 1, a) }) }))"

definition im_update :: "('v::heap) imap \<Rightarrow> event_data tuple \<Rightarrow> 'v \<Rightarrow> ('v imap) Heap" where
  "im_update q x v = im_update_h q (ihash x) x v"

definition im_delete_h :: "('v::heap) imap \<Rightarrow> integer \<Rightarrow> event_data tuple \<Rightarrow> ('v imap) Heap" where
  "im_delete_h q h x = (case q of (n, c, a) \<Rightarrow> (let i = ibkt h n in
     do { b \<leftarrow> Array.nth' a i;
          (case hm_look_list h x b of None \<Rightarrow> return q
           | Some _ \<Rightarrow> do { _ \<leftarrow> Array.upd' a i (hm_del_list h x b); return (n, c - 1, a) }) }))"

definition im_delete :: "('v::heap) imap \<Rightarrow> event_data tuple \<Rightarrow> ('v imap) Heap" where
  "im_delete q x = im_delete_h q (ihash x) x"

definition im_count :: "('v ientry) list \<Rightarrow> integer" where
  "im_count b = integer_of_nat (length b)"

partial_function (heap) im_filter_idx ::
  "(event_data tuple \<Rightarrow> bool) \<Rightarrow> (('v::heap) ientry list) array \<Rightarrow>
    integer \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> integer Heap" where
  [code]:
  "im_filter_idx p a i n c = (if n \<le> i then return c
     else do { b \<leftarrow> Array.nth' a i;
               (let b' = filter (\<lambda>e. p (fst (snd e))) b in
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

section \<open>The union of a window of tables, as a count per tuple\<close>

text \<open>Adding a table to the union costs one update per tuple of that table, removing one costs
the same, and the union itself changes only where a count reaches or leaves zero.  Both the
Since and the Until structure for a closed left operand are built on this.\<close>

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


(*<*)
end
(*>*)
