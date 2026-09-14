(* Micro-benchmark: the tuple-keyed mappings of the auxiliary structures.
   Containers Mapping (persistent RBT) against the heap-resident imap of Table_Imp and a
   hand-written OCaml Hashtbl, on the update/lookup/delete pattern the structures produce. *)
open Verified_open.Monitor

let now () = Unix.gettimeofday ()
let nat i = nat_of_integer (Z.of_int i)
let tup k i = List.init k (fun j -> Some (EInt (Z.of_int ((i * 31 + j * 7) mod 100000))))
let mk k n = Array.init n (fun i -> tup k i)

let ccmp = ccompare_list (ccompare_option ccompare_event_data)
let ceq_t = ceq_list (ceq_option ceq_event_data)
let eqd = equal_list (equal_option equal_event_data)
let m_empty () = RBT_Mapping (emptyc ccmp)
let m_upd m k v = updateb (ccmp, eqd) k v m
let m_look m k = lookupa (ccmp, eqd) m k
let m_del m k = delete (ccmp, eqd) k m

module H = Hashtbl.Make (struct
  type t = event_data option list
  let equal = (=)
  let hash = Hashtbl.hash
end)

let time name f = let t0 = now () in let r = f () in
  Printf.printf "  %-20s %7.3f s\n%!" name (now () -. t0); r

let bench k n reps =
  Printf.printf "columns=%d  keys=%d  repetitions=%d\n%!" k n reps;
  let ks = mk k n in
  time "mapping update" (fun () ->
    for _ = 1 to reps do
      let m = ref (m_empty ()) in
      Array.iteri (fun i x -> m := m_upd !m x (nat i)) ks done);
  time "imap update" (fun () ->
    for _ = 1 to reps do
      let m = im_new heap_nat (Z.of_int (2 * n)) () in
      Array.iteri (fun i x -> im_update heap_nat m x (nat i) ()) ks done);
  time "ocaml update" (fun () ->
    for _ = 1 to reps do
      let m = H.create (2 * n) in
      Array.iteri (fun i x -> H.replace m x i) ks done);
  let m1 = let m = ref (m_empty ()) in Array.iteri (fun i x -> m := m_upd !m x (nat i)) ks; !m in
  let m2 = let m = im_new heap_nat (Z.of_int (2 * n)) () in Array.iteri (fun i x -> im_update heap_nat m x (nat i) ()) ks; m in
  let m3 = let m = H.create (2 * n) in Array.iteri (fun i x -> H.replace m x i) ks; m in
  let c = ref 0 in
  time "mapping lookup" (fun () -> for _ = 1 to reps do Array.iter (fun x -> if m_look m1 x <> None then incr c) ks done);
  time "imap lookup" (fun () -> for _ = 1 to reps do Array.iter (fun x -> if im_lookup heap_nat m2 x () <> None then incr c) ks done);
  time "ocaml lookup" (fun () -> for _ = 1 to reps do Array.iter (fun x -> if H.mem m3 x then incr c) ks done);
  time "mapping delete" (fun () -> for _ = 1 to reps do
    let m = ref m1 in Array.iter (fun x -> m := m_del !m x) ks done);
  time "imap delete" (fun () -> for _ = 1 to reps do
    Array.iter (fun x -> im_delete heap_nat m2 x ()) ks;
    Array.iteri (fun i x -> im_update heap_nat m2 x (nat i) ()) ks done);
  Printf.printf "  (checksum %d)\n\n%!" !c

let () = bench 1 50 2000; bench 2 1000 100; bench 4 5000 20
