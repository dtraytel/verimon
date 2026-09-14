(* Micro-benchmark: heap-resident tables (Table_Imp) against the Containers red-black-tree
   tables of the verified kernel, on the access pattern the monitor produces.
   Build: python3 ../since_bench/unseal.py ../../src/verified.ml; cp dune.template dune *)
open Verified_open.Monitor

let now () = Unix.gettimeofday ()
let nat i = nat_of_integer (Z.of_int i)

(* tuples: k columns of small integers, as the monitor builds them *)
let tup k i = List.init k (fun j -> Some (EInt (Z.of_int ((i * 31 + j * 7) mod 100000))))

let mk_tuples k n = List.init n (fun i -> tup k i)

(* --- red-black-tree table operations of the kernel --- *)
let ccmp = ccompare_list (ccompare_option ccompare_event_data)
let ceq_t = ceq_list (ceq_option ceq_event_data)
let cmpf = match ccompare ccmp with Some c -> c | None -> failwith "no comparator"
let ord_int = function Eqa -> 0 | Lt -> -1 | Gt -> 1
let rbt_of xs = table_of_list (List.sort_uniq (fun a b -> ord_int (cmpf a b)) xs)
let rbt_mem x s = member (ceq_t, ccmp) x s
let rbt_union a b = sup_seta (ceq_t, ccmp) a b

(* --- hand-written OCaml hash set, the ceiling for the generated code --- *)
module H = Hashtbl.Make (struct
  type t = event_data option list
  let equal = (=)
  let hash = Hashtbl.hash
end)
let oc_of xs = let h = H.create (2 * List.length xs) in List.iter (fun x -> H.replace h x ()) xs; h
let oc_mem h x = H.mem h x
let oc_union a b = let h = H.create (H.length a + H.length b) in
  H.iter (fun k () -> H.replace h k ()) a; H.iter (fun k () -> H.replace h k ()) b; h

(* --- heap table operations --- *)
let ht_of xs = ht_of_list xs ()
let ht_has q x = ht_mem q x ()


let time name f =
  let t0 = now () in
  let r = f () in
  Printf.printf "  %-22s %7.3f s\n%!" name (now () -. t0); r

let bench k n reps =
  Printf.printf "columns=%d  tuples=%d  repetitions=%d\n%!" k n reps;
  let xs = mk_tuples k n in
  let ys = mk_tuples k n |> List.map (fun t -> match t with Some (EInt v) :: r -> Some (EInt (Z.add v (Z.of_int 1))) :: r | t -> t) in
  let _ = time "rbt build (sort+build)" (fun () -> for _ = 1 to reps do ignore (rbt_of xs) done) in
  let r1 = time "rbt build" (fun () -> let s = ref (rbt_of xs) in for _ = 2 to reps do s := rbt_of xs done; !s) in
  let h1 = time "heap build" (fun () -> let s = ref (ht_of xs) in for _ = 2 to reps do s := ht_of xs done; !s) in
  let o1 = time "ocaml build" (fun () -> let s = ref (oc_of xs) in for _ = 2 to reps do s := oc_of xs done; !s) in
  let probes = mk_tuples k (n * 2) in
  let cnt = ref 0 in
  time "rbt member" (fun () -> for _ = 1 to reps do List.iter (fun x -> if rbt_mem x r1 then incr cnt) probes done);
  let c1 = !cnt in cnt := 0;
  time "heap member" (fun () -> for _ = 1 to reps do List.iter (fun x -> if ht_has h1 x then incr cnt) probes done);
  let c2 = !cnt in cnt := 0;
  time "ocaml member" (fun () -> for _ = 1 to reps do List.iter (fun x -> if oc_mem o1 x then incr cnt) probes done);
  Printf.printf "  (hits %d / %d / %d)\n%!" c1 c2 !cnt;
  let r2 = rbt_of ys in
  time "rbt union" (fun () -> for _ = 1 to reps do ignore (rbt_union r1 r2) done);
  let o2 = oc_of ys in
  time "ocaml union" (fun () -> for _ = 1 to reps do ignore (oc_union o1 o2) done);
  print_newline ()

let () =
  bench 1 50 2000;
  bench 2 50 2000;
  bench 2 1000 100;
  bench 4 1000 100
