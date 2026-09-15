(* Statistical allocation profiling, enabled by the environment variable MONPOLY_MEMPROF
   (the sampling rate, e.g. 1e-4). Every sampled allocation is attributed to the top frames
   of its call stack; at exit the totals are printed to stderr, sorted by sampled words.
   Only a diagnostic: it changes no behaviour and costs nothing unless the variable is set.
   See EFFICIENCY.md, Section 15. *)

let depth = try int_of_string (Sys.getenv "MONPOLY_MEMPROF_DEPTH") with _ -> 4

let table : (string, int * int) Hashtbl.t = Hashtbl.create 1024

let key bt =
  let slots = Printexc.backtrace_slots bt in
  match slots with
  | None -> "<no backtrace>"
  | Some sl ->
    let n = min depth (Array.length sl) in
    let buf = Buffer.create 128 in
    for i = 0 to n - 1 do
      (match Printexc.Slot.location sl.(i) with
       | Some l -> Buffer.add_string buf (Printf.sprintf "%s:%d" l.Printexc.filename l.Printexc.line_number)
       | None -> Buffer.add_string buf "?");
      if i < n - 1 then Buffer.add_string buf " < "
    done;
    Buffer.contents buf

let record (a : Gc.Memprof.allocation) =
  let k = key a.Gc.Memprof.callstack in
  let (w, c) = try Hashtbl.find table k with Not_found -> (0, 0) in
  Hashtbl.replace table k (w + a.Gc.Memprof.n_samples * a.Gc.Memprof.size,
                           c + a.Gc.Memprof.n_samples);
  None

let report () =
  let rows = Hashtbl.fold (fun k (w, c) acc -> (k, w, c) :: acc) table [] in
  let rows = List.sort (fun (_, a, _) (_, b, _) -> compare b a) rows in
  let total = List.fold_left (fun acc (_, w, _) -> acc + w) 0 rows in
  Printf.eprintf "# sampled words: %d\n" total;
  List.iteri (fun i (k, w, c) ->
    if i < 40 then
      Printf.eprintf "%10d %5.1f%% %8d  %s\n" w (100.0 *. float_of_int w /. float_of_int total) c k)
    rows

let start () =
  match Sys.getenv_opt "MONPOLY_MEMPROF" with
  | None -> ()
  | Some r ->
    let rate = try float_of_string r with _ -> 1e-4 in
    Printexc.record_backtrace true;
    ignore (Gc.Memprof.start ~sampling_rate:rate ~callstack_size:32
      { Gc.Memprof.alloc_minor = record; alloc_major = record;
        promote = (fun _ -> None); dealloc_minor = (fun _ -> ()); dealloc_major = (fun _ -> ()) });
    at_exit (fun () -> Gc.Memprof.stop (); report ())
