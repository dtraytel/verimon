open Verified_open.Monitor
let time name f =
  Gc.compact ();
  let t0 = Unix.gettimeofday () in
  let r = f () in
  let t1 = Unix.gettimeofday () in
  Printf.printf "%-52s %8.3f s\n%!" name (t1 -. t0); r

let n = 300_000
let dom = 20_000
let () = Random.init 7
let raw = Array.init n (fun _ -> (Random.int dom, Random.int dom))
let vtuples = Array.map (fun (a,b) -> [Some (EInt (Z.of_int a)); Some (EInt (Z.of_int b))]) raw
let ztuples = Array.map (fun (a,b) -> [Z.of_int a; Z.of_int b]) raw
let ituples = Array.map (fun (a,b) -> [a; b]) raw

(* (a) Verified RBT set, dictionaries constructed at every call (as generated code does inside polymorphic functions) *)
let dict () = (ceq_list (ceq_option ceq_event_data), ccompare_list (ccompare_option ccompare_event_data))
let bench_verified_dict_per_call () =
  let s = Array.fold_left (fun s t -> insert (dict ()) t s) (set_empty (dict ()) Set_RBT) vtuples in
  let c = Array.fold_left (fun c t -> if member (dict ()) t s then c+1 else c) 0 vtuples in c
(* (a') dictionaries built once *)
let bench_verified_dict_once () =
  let d = dict () in
  let s = Array.fold_left (fun s t -> insert d t s) (set_empty d Set_RBT) vtuples in
  let c = Array.fold_left (fun c t -> if member d t s then c+1 else c) 0 vtuples in c

(* (b) OCaml Set.Make on the same representation, direct comparator *)
let cmp_ed x y = match x, y with
  | EInt a, EInt b -> Z.compare a b
  | EInt _, _ -> -1 | _, EInt _ -> 1
  | EFloat a, EFloat b -> compare a b
  | EFloat _, _ -> -1 | _, EFloat _ -> 1
  | EString a, EString b -> String.compare a b
let rec cmp_tuple x y = match x, y with
  | [], [] -> 0 | [], _ -> -1 | _, [] -> 1
  | None :: xs, None :: ys -> cmp_tuple xs ys
  | None :: _, Some _ :: _ -> -1 | Some _ :: _, None :: _ -> 1
  | Some a :: xs, Some b :: ys -> let c = cmp_ed a b in if c <> 0 then c else cmp_tuple xs ys
module VS = Set.Make (struct type t = event_data option list let compare = cmp_tuple end)
let bench_set_direct () =
  let s = Array.fold_left (fun s t -> VS.add t s) VS.empty vtuples in
  Array.fold_left (fun c t -> if VS.mem t s then c+1 else c) 0 vtuples

(* (c) MonPoly-like: Set.Make over Z.t list with polymorphic compare *)
module ZS = Set.Make (struct type t = Z.t list let compare = compare end)
let bench_set_poly_z () =
  let s = Array.fold_left (fun s t -> ZS.add t s) ZS.empty ztuples in
  Array.fold_left (fun c t -> if ZS.mem t s then c+1 else c) 0 ztuples

(* (c') native int tuples with polymorphic compare *)
module IS = Set.Make (struct type t = Stdlib.Int.t list let compare = compare end)
let bench_set_poly_int () =
  let s = Array.fold_left (fun s t -> IS.add t s) IS.empty ituples in
  Array.fold_left (fun c t -> if IS.mem t s then c+1 else c) 0 ituples

(* (d) Hashtbl on verified representation *)
let bench_hashtbl () =
  let h = Hashtbl.create 1024 in
  Array.iter (fun t -> Hashtbl.replace h t ()) vtuples;
  Array.fold_left (fun c t -> if Hashtbl.mem h t then c+1 else c) 0 vtuples

(* set intersection: verified vs Set.Make *)
let () =
  let r1 = time "(a) Verified RBT_set insert+member, dict per call" bench_verified_dict_per_call in
  let r2 = time "(a') Verified RBT_set insert+member, dict once" bench_verified_dict_once in
  let r3 = time "(b) Set.Make, same repr, direct comparator" bench_set_direct in
  let r4 = time "(c) Set.Make, Z.t list, polymorphic compare (MonPoly)" bench_set_poly_z in
  let r5 = time "(c') Set.Make, int list, polymorphic compare" bench_set_poly_int in
  let r6 = time "(d) Hashtbl, verified repr" bench_hashtbl in
  assert (r1 = r2 && r2 = r3 && r3 = r4 && r4 = r5 && r5 = r6);
  let d = dict () in
  let half = Array.sub vtuples 0 (n/2) and half2 = Array.sub vtuples (n/4) (n/2) in
  let s1 = Array.fold_left (fun s t -> insert d t s) (set_empty d Set_RBT) half in
  let s2 = Array.fold_left (fun s t -> insert d t s) (set_empty d Set_RBT) half2 in
  let v1 = Array.fold_left (fun s t -> VS.add t s) VS.empty half in
  let v2 = Array.fold_left (fun s t -> VS.add t s) VS.empty half2 in
  let c1 = time "Verified inf_set (intersection) x20" (fun () -> let r = ref 0 in for _ = 1 to 20 do r := (match inf_seta d s1 s2 with RBT_set t -> rbt_fold (fun _ c -> c+1) t 0 | _ -> -1) done; !r) in
  let c2 = time "Set.Make inter x20" (fun () -> let r = ref 0 in for _ = 1 to 20 do r := VS.cardinal (VS.inter v1 v2) done; !r) in
  Printf.printf "intersection sizes %d %d\n" c1 c2
