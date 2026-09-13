module M = Verified_open.Monitor
let nat i = M.nat_of_integer (Z.of_int i)
let int_of_nat n = Z.to_int (M.integer_of_nat n)
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
let args () = M.init_args (M.interval (nat 0) (M.Enat (nat 6))) (nat 1) (nat_set []) (nat_set [0]) true None

let dq_pieces () =
  let args = args () in
  let aux = ref (M.init_dq args) in
  let t = Array.make 6 0. in
  let idx_hist = Hashtbl.create 16 in
  let front_empty = ref 0 in
  for tp0 = 0 to ntp - 1 do
    let nt = nat (tp0 / per_ts) in
    let rel1 = unit_table and rel2 = table (tp0 mod domain) in
    let (st, d0) = time (fun () -> M.shift_dq args nt !aux) in
    let (tp, (tss, (tables, (len, (maskL, (maskR, (result, (a1_map, (a2_dq, (tstp_dq, donea)))))))))) = st in
    let (M.Dq (f, b, nf, nb)) = a2_dq in
    if f = [] then incr front_empty;
    let i = M.args_ivl args in let pos = M.args_pos args in
    let inz = M.memL i M.zero_nata in
    let new_tstp = if inz then M.Inr tp else M.Inl nt in
    let (tstp_dqa, d1) = time (fun () -> M.dq_push nt tstp_dq) in
    let p t = M.memL i (M.minus_nata nt (M.dq_nth tstp_dqa (M.minus_nata t (M.minus_nata tp len)))) in
    (* record accessed index for the a1_map pair *)
    (match M.unbox M.ed_lookup_nat_v a1_map [None] with
     | Some tpa -> let k = int_of_nat (M.max M.ord_nat (M.minus_nata tp len) tpa) - int_of_nat (M.minus_nata tp len) in
       let key = if k < 3 then string_of_int k else if k >= int_of_nat len - 2 then "len-" ^ string_of_int (int_of_nat len - k) else "mid" in
       Hashtbl.replace idx_hist key (1 + (try Hashtbl.find idx_hist key with Not_found -> 0))
     | None -> ());
    let (lst, d2) = time (fun () -> M.unbox M.ed_csorted_list_of_set_v rel2) in
    let ((tbl, (a2_dqa, resulta)), d3) = time (fun () ->
      M.fold (M.until_elem_step_dq (M.ceq_event_data, M.ccompare_event_data, M.equal_event_data) a1_map maskL pos tp len inz p new_tstp) lst (M.ed_bot, (a2_dq, result))) in
    let (a2_dqb, d4) = time (fun () -> M.dq_push M.ed_mempty_tstp a2_dqa) in
    let (a1_mapa, d5) = time (fun () -> if pos then M.unbox M.ed_mfilter_nat_v (fun asa _ -> M.unbox M.ed_member_v asa rel1)
        (M.unbox M.ed_upd_set_nat_v a1_map (fun _ -> tp) (M.unbox M.ed_filter_v (fun k -> M.is_none (M.unbox M.ed_lookup_nat_v a1_map k)) rel1))
      else M.unbox M.ed_upd_set_nat_v a1_map (fun _ -> tp) rel1) in
    let tablesa = M.append_queue (tbl, new_tstp) tables in
    let tssa = M.append_queue nt tss in
    List.iteri (fun k d -> t.(k) <- t.(k) +. d) [d0; d1; d2; d3; d4; d5];
    aux := (M.plus_nata tp M.one_nata, (tssa, (tablesa, (M.plus_nata len M.one_nata, (maskL, (maskR, (resulta, (a1_mapa, (a2_dqb, (tstp_dqa, donea))))))))))
  done;
  let g k = t.(k) *. 1e6 /. float ntp in
  Printf.printf "add_new_dq pieces (us/tp): shift %.2f  tstp push %.2f  to-list %.2f  fold %.2f  a2 push %.2f  a1_map %.2f\n" (g 0) (g 1) (g 2) (g 3) (g 4) (g 5);
  Printf.printf "  front empty at add_new: %d of %d steps; a1 pair index: " !front_empty ntp;
  Hashtbl.iter (fun k v -> Printf.printf "%s:%d " k v) idx_hist; print_newline ()

let () = List.iter (fun sp -> sparse := sp; Printf.printf "-- one non-empty table every %d time points:\n" sp; dq_pieces ()) [1; 8]
