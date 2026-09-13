(* Micro-benchmark: per-operation cost of the verified Since structure (ONCE case, one tuple
   per time point) and of a hash-table based imperative sliding window doing the same work. *)
module M = Verified_open.Monitor

let nat i = M.nat_of_integer (Z.of_int i)
let nat_set l = List.fold_left (fun s i -> M.insert (M.ceq_nat, M.ccompare_nat) (nat i) s)
    (M.set_empty (M.ceq_nat, M.ccompare_nat) (M.of_phantom M.set_impl_nata)) l
let tuple k = [Some (M.EInt (Z.of_int k))]
let sparse = ref 1
let table k = if k mod !sparse = 0 then M.table_of_list [tuple k] else M.ed_bot
let unit_table = M.table_of_list [[None]]

let time f = let t0 = Unix.gettimeofday () in let r = f () in (r, Unix.gettimeofday () -. t0)

let ntp = 200000
let per_ts = 1700
let domain = 5000

let verified () =
  let args = M.init_args (M.interval (nat 2) (M.Enat (nat 21))) (nat 1) (nat_set []) (nat_set [0]) true None in
  let aux = ref (M.init_mmasaux args) in
  let t_shift = ref 0. and t_ts = ref 0. and t_join = ref 0. and t_res = ref 0. and t_add = ref 0. in
  let nres = ref 0 in
  for tp = 0 to ntp - 1 do
    let ts = nat (tp / per_ts) in
    let (a0, d0) = time (fun () -> M.shift_end_mmasaux args ts !aux) in
    let (a1, d1) = time (fun () -> M.add_new_ts_mmasauxa args ts a0) in
    t_shift := !t_shift +. d0;
    let (a2, d2) = time (fun () -> M.gc_join_mmasaux args unit_table a1) in
    let (r, d3) = time (fun () -> M.result_mmasaux args a2) in
    let (a3, d4) = time (fun () -> M.add_new_table_mmasaux args (table (tp mod domain)) a2) in
    aux := a3;
    t_ts := !t_ts +. d1; t_join := !t_join +. d2; t_res := !t_res +. d3; t_add := !t_add +. d4;
    (match r with M.RBT_set _ -> incr nres | _ -> ())
  done;
  Printf.printf "verified Since (us/tp): shift_end %.2f add_new_ts' %.2f  gc_join %.2f  result %.2f  add_new_table %.2f  total %.2f  (%d results)\n"
    (!t_shift *. 1e6 /. float ntp) (!t_ts *. 1e6 /. float ntp) (!t_join *. 1e6 /. float ntp) (!t_res *. 1e6 /. float ntp)
    (!t_add *. 1e6 /. float ntp) ((!t_shift +. !t_ts +. !t_join +. !t_res +. !t_add) *. 1e6 /. float ntp) !nres

(* Imperative sliding window: tuples are ints here (the tuple comparator cost is not the point). *)
let imperative () =
  let memL_lo = 2 and memR_hi = 21 in
  let q_prev = Queue.create () and q_in = Queue.create () in
  let tuple_in : (int, int) Hashtbl.t = Hashtbl.create 1024 in
  let tuple_since : (int, int) Hashtbl.t = Hashtbl.create 1024 in
  let t0 = Unix.gettimeofday () in
  let cnt = ref 0 in
  for tp = 0 to ntp - 1 do
    let nt = tp / per_ts in
    (* shift_end: expire from data_in *)
    let continue = ref true in
    while !continue && not (Queue.is_empty q_in) do
      let (t, xs) = Queue.peek q_in in
      if nt - t >= memR_hi then begin
        ignore (Queue.pop q_in);
        List.iter (fun x -> match Hashtbl.find_opt tuple_in x with
            | Some t' when t' = t -> Hashtbl.remove tuple_in x | _ -> ()) xs
      end else continue := false
    done;
    (* add_new_ts: move from data_prev to data_in *)
    continue := true;
    while !continue && not (Queue.is_empty q_prev) do
      let (t, xs) = Queue.peek q_prev in
      if nt - t >= memL_lo then begin
        ignore (Queue.pop q_prev); Queue.push (t, xs) q_in;
        List.iter (fun x -> match Hashtbl.find_opt tuple_since x with
            | Some t' when t' <= t -> if not (Hashtbl.mem tuple_in x) then Hashtbl.replace tuple_in x t
            | _ -> ()) xs
      end else continue := false
    done;
    (* join with the unit table: take_all, nothing to do; result: tuple_in *)
    cnt := !cnt + Hashtbl.length tuple_in;
    (* add_new_table *)
    let x = tp mod domain in
    if not (Hashtbl.mem tuple_since x) then Hashtbl.replace tuple_since x nt;
    Queue.push (nt, [x]) q_prev
  done;
  let d = Unix.gettimeofday () -. t0 in
  Printf.printf "imperative window (us/tp): total %.2f  (checksum %d)\n" (d *. 1e6 /. float ntp) !cnt

let () = verified (); imperative (); sparse := 8; Printf.printf "-- one non-empty table every 8 time points:\n"; verified ()

(* Piecewise timing of add_new_ts_mmsaux' on the real state sequence. *)
let pieces () =
  let args = M.init_args (M.interval (nat 2) (M.Enat (nat 21))) (nat 1) (nat_set []) (nat_set [0]) true None in
  let aux = ref (M.init_mmasaux args) in
  let ta = ref 0. and tb = ref 0. and tc = ref 0. and td = ref 0. and te = ref 0. in
  for tp = 0 to ntp - 1 do
    let ts = nat (tp / per_ts) in
    let a0 = M.shift_end_mmasaux args ts !aux in
    let ((t, (gc, (maskL, (maskR, (data_prev, (data_in, (table_in, (wf_table_in, (tuple_in, (wf_table_since, tuple_since)))))))))), agg) = a0 in
    let i = M.args_ivl args in
    let ((data_preva, move), da) = time (fun () -> M.takedropWhile_queue (fun (t', _) -> M.memL i (M.minus_nata ts t')) data_prev) in
    let (data_ina, db) = time (fun () -> M.fold (fun (t', x) -> M.append_queue (t', x)) move data_in) in
    let ((tuple_ina, add), dc) = time (fun () -> M.fold (M.unbox M.ed_upd_set_keys_v (fun x t' -> M.unbox M.ed_filter_v (fun asa -> M.ed_valid_tuple tuple_since (t', asa)) x)) move (tuple_in, M.ed_bot)) in
    let (tin, dd) = time (fun () -> M.unbox M.ed_union_v table_in add) in
    let (wf, de) = time (fun () -> M.wf_table_upd args tuple_ina (fun _ -> M.wf_table_union (M.ceq_event_data, M.ccompare_event_data) wf_table_in (M.wf_table_of_set_args (M.ceq_event_data, M.ccompare_event_data) args add))) in
    ta := !ta +. da; tb := !tb +. db; tc := !tc +. dc; td := !td +. dd; te := !te +. de;
    let a1 = ((ts, (gc, (maskL, (maskR, (data_preva, (data_ina, (tin, (wf, (tuple_ina, (wf_table_since, tuple_since)))))))))), agg) in
    let a2 = M.gc_join_mmasaux args unit_table a1 in
    aux := M.add_new_table_mmasaux args (table (tp mod domain)) a2
  done;
  Printf.printf "add_new_ts' pieces (us/tp): takedropWhile %.2f  append %.2f  upd_set_keys %.2f  union %.2f  wf_table_upd %.2f\n"
    (!ta *. 1e6 /. float ntp) (!tb *. 1e6 /. float ntp) (!tc *. 1e6 /. float ntp) (!td *. 1e6 /. float ntp) (!te *. 1e6 /. float ntp)

let () = pieces ()

(* Comparator cost: lookups in a 5000-key tree with the generic comparator chain vs a direct one. *)
let rec ed_comparator xs ys = match xs, ys with
  | [], [] -> M.Eqa | [], _ :: _ -> M.Lt | _ :: _, [] -> M.Gt
  | None :: xs, None :: ys -> ed_comparator xs ys
  | None :: _, Some _ :: _ -> M.Lt | Some _ :: _, None :: _ -> M.Gt
  | Some a :: xs, Some b :: ys -> (match M.comparator_event_data a b with M.Eqa -> ed_comparator xs ys | r -> r)

let comparators () =
  let keys = List.init 5000 (fun k -> [Some (M.EInt (Z.of_int (k * 7919 mod 5000))); Some (M.EInt (Z.of_int k))]) in
  let rbt = match M.table_of_list (List.sort compare keys) with M.RBT_set r -> M.impl_ofa (M.ccompare_list (M.ccompare_option M.ccompare_event_data)) r | _ -> assert false in
  let generic = M.comparator_list (M.comparator_option M.comparator_event_data) in
  let n = 1000000 in
  let probe c = let cnt = ref 0 in for i = 0 to n - 1 do
      match M.rbt_comp_lookup c rbt [Some (M.EInt (Z.of_int (i mod 5000 * 7919 mod 5000))); Some (M.EInt (Z.of_int (i mod 5000)))] with Some () -> incr cnt | None -> () done; !cnt in
  let (c1, d1) = time (fun () -> probe generic) in
  let (c2, d2) = time (fun () -> probe ed_comparator) in
  Printf.printf "lookup in 5000-key tree (ns/lookup): generic comparator %.0f  direct comparator %.0f  (%d %d)\n" (d1 *. 1e9 /. float n) (d2 *. 1e9 /. float n) c1 c2

let () = comparators ()

(* Until structure (EVENTUALLY-like: left operand is the unit table), per-step cost. *)
let until_verified () =
  let args = M.init_args (M.interval (nat 0) (M.Enat (nat 6))) (nat 1) (nat_set []) (nat_set [0]) true None in
  let aux = ref (M.init_mmauaux args) in
  let t_add = ref 0. and t_eval = ref 0. in
  let nres = ref 0 in
  for tp = 0 to ntp - 1 do
    let ts = nat (tp / per_ts) in
    let (a1, d1) = time (fun () -> M.add_new_mmauaux args unit_table (table (tp mod domain)) ts !aux) in
    let ((zs, a2), d2) = time (fun () -> M.eval_mmauaux args ts a1) in
    aux := a2; t_add := !t_add +. d1; t_eval := !t_eval +. d2; nres := !nres + List.length zs
  done;
  Printf.printf "verified Until (us/tp): add_new %.2f  eval %.2f  total %.2f  (%d results)\n"
    (!t_add *. 1e6 /. float ntp) (!t_eval *. 1e6 /. float ntp) ((!t_add +. !t_eval) *. 1e6 /. float ntp) !nres

let until_imperative () =
  (* EVENTUALLY[0,6) with one table per time point: a queue of (ts, tuples); a time point is
     evaluated once the current ts exceeds its ts + 6; its result is the union of the tables
     with ts in [t, t+6). Kept simple: per-tp result = set of tuples in window (hash set). *)
  let q = Queue.create () in
  let window : (int, int) Hashtbl.t = Hashtbl.create 64 in
  let t0 = Unix.gettimeofday () in
  let cnt = ref 0 in
  for tp = 0 to ntp - 1 do
    let nt = tp / per_ts in
    let x = if tp mod !sparse = 0 then Some (tp mod domain) else None in
    (match x with Some x -> Hashtbl.replace window x (Hashtbl.find_opt window x |> Option.value ~default:0 |> (+) 1) | None -> ());
    Queue.push (nt, x) q;
    let continue = ref true in
    while !continue && not (Queue.is_empty q) do
      let (t, y) = Queue.peek q in
      if nt >= t + 6 then begin ignore (Queue.pop q); incr cnt;
        (match y with Some y -> (match Hashtbl.find_opt window y with Some 1 -> Hashtbl.remove window y | Some k -> Hashtbl.replace window y (k-1) | None -> ()) | None -> ()) end
      else continue := false
    done
  done;
  let d = Unix.gettimeofday () -. t0 in
  Printf.printf "imperative Until window (us/tp): total %.2f (%d evaluated)\n" (d *. 1e6 /. float ntp) !cnt

let () = sparse := 1; Printf.printf "-- Until, one tuple per time point:\n"; until_verified (); until_imperative ();
  sparse := 8; Printf.printf "-- Until, one non-empty table every 8 time points:\n"; until_verified (); until_imperative ()

(* Piecewise timing of add_new_mmuaux (plain Until structure). *)
let until_pieces () =
  let args = M.init_args (M.interval (nat 0) (M.Enat (nat 6))) (nat 1) (nat_set []) (nat_set [0]) true None in
  let aux = ref (M.init_mmuaux args) in
  let ts_ = Array.make 8 0. in
  let dl = (M.ceq_list (M.ceq_option M.ceq_event_data), M.ccompare_list (M.ccompare_option M.ccompare_event_data)) in
  let d3 = (M.ceq_event_data, M.ccompare_event_data, M.equal_event_data) in
  for tp0 = 0 to ntp - 1 do
    let nt = nat (tp0 / per_ts) in
    let rel1 = unit_table and rel2 = table (tp0 mod domain) in
    let (st, d0) = time (fun () -> M.shift_mmuaux args nt !aux) in
    let (tp, (tss, (tables, (len, (maskL, (maskR, (result, (a1_map, (a2_map, (tstp_map, donea)))))))))) = st in
    let i = M.args_ivl args in let pos = M.args_pos args in
    let new_tstp = if M.memL i M.zero_nata then M.Inr tp else M.Inl nt in
    let (tstp_mapa, d1) = time (fun () -> M.updateb (M.ccompare_nat, M.equal_nat) tp nt tstp_map) in
    let p t = (match M.lookupa (M.ccompare_nat, M.equal_nat) tstp_mapa t with Some ts -> M.memL i (M.minus_nata nt ts) | None -> false) in
    let ((tbl, (a2_mapa, resulta)), d2) = time (fun () ->
        M.set_fold_cfi dl (M.until_elem_step_cfi d3 a1_map maskL pos tp len (M.memL i M.zero_nata) p new_tstp) (M.ed_bot, (a2_map, result)) rel2) in
    let (tablesa, d3') = time (fun () -> M.append_queue (tbl, (if M.memL i M.zero_nata then M.Inr tp else M.Inl nt)) tables) in
    let (a2_mapb, d4) = time (fun () -> M.updateb (M.ccompare_nat, M.equal_nat) (M.plus_nata tp M.one_nata) M.ed_mempty_tstp a2_mapa) in
    let (a1_mapa, d5) = time (fun () -> M.unbox M.ed_mfilter_nat_v (fun asa _ -> M.unbox M.ed_member_v asa rel1)
        (M.unbox M.ed_upd_set_nat_v a1_map (fun _ -> tp) (M.unbox M.ed_filter_v (fun k -> M.is_none (M.unbox M.ed_lookup_nat_v a1_map k)) rel1))) in
    let (tssa, d6) = time (fun () -> M.append_queue nt tss) in
    List.iteri (fun k d -> ts_.(k) <- ts_.(k) +. d) [d0; d1; d2; d3'; d4; d5; d6];
    aux := (M.plus_nata tp M.one_nata, (tssa, (tablesa, (M.plus_nata len M.one_nata, (maskL, (maskR, (resulta, (a1_mapa, (a2_mapb, (tstp_mapa, donea))))))))))
  done;
  let f k = ts_.(k) *. 1e6 /. float ntp in
  Printf.printf "add_new_mmuaux pieces (us/tp): shift(+eval_steps) %.2f  tstp_map %.2f  fold rel2 %.2f  tables %.2f  a2_map new tp %.2f  a1_map %.2f  tss %.2f\n"
    (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6)

let () = sparse := 1; until_pieces (); sparse := 8; until_pieces ()
