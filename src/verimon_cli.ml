(* The program verimon-cli: the verified monitor with MonPoly's command line.

   Everything up to the loop over the log is generated code (thys/VeriMon_CLI, theory CLI):
   [cli_main] parses the arguments as MonPoly's front end does, asks for the formula file and
   the signature file ([NeedFile]), parses the formula with the verified parser, reads the
   signature, converts both into the monitor's, prepares the formula and starts the monitor
   ([Run]), or says what to print and with which code to exit ([Done]).  Theorem cli_run states
   that a run is the verified monitor on the converted formula and signature, so that
   verimon_log.vrun_log and vrun_filtered apply to the verdicts it outputs.

   This driver reads the files, prints the texts it is given, and runs the loop over the log in
   chunks ([vfeed_chunk], [vfinish]); the verdicts are printed as [verdict_fold] says (proved equal to [verdict_out]), and the
   errors in the log as [log_error] words them, at the positions this driver computes, as
   Algorithm_verified does for monpoly -verified. *)

open Libmonpoly

module V = Verimon_code.Verimon

let int_of_nat n = Z.to_int (V.integer_of_nat n)
let int_of_int i = Z.to_int (V.integer_of_int i)

(* The generated code's strings of characters, as OCaml strings. *)
let string_of_chars cs = String.of_seq (List.to_seq cs)

(* The pieces of a text are collected in a buffer and written at once: a write per piece costs
   more than the pieces' contents. *)
let text_buf = Buffer.create 4096

let print_text oc t =
  Buffer.clear text_buf;
  List.iter (Buffer.add_string text_buf) t;
  Buffer.output_buffer oc text_buf;
  flush oc

let print_banner () =
  let banner =
    match Build_info.V1.version () with
    | None -> "VeriMon, the verified MonPoly monitor (development build)"
    | Some v -> "VeriMon, the verified MonPoly monitor, version " ^ Build_info.V1.Version.to_string v
  in
  print_endline banner

(* As OCaml's runtime reports an uncaught exception, as MonPoly ends on a file it cannot open. *)
let read_file name =
  try
    let ic = open_in_bin name in
    Fun.protect ~finally:(fun () -> close_in_noerr ic)
      (fun () -> really_input_string ic (in_channel_length ic))
  with Sys_error msg ->
    Printf.eprintf "Fatal error: exception Sys_error(\"%s\")\n%!" (String.escaped msg);
    exit 2

exception Stop

(* The chunk size of the log, as for monpoly -verified (Algorithm_verified.chunk_size). *)
let chunk_size = 512

let run cfg cf st fin n lsig =
  let verbose = V.c_verbose cfg and stop_first = V.c_stop_first cfg in
  let ignore_errors = V.c_ignore_errors cfg in
  let logfile = string_of_chars (V.c_log cfg) in
  let ff f = Printf.sprintf "%g" f in
  let ln = Verified_log_parser.init_lines logfile in
  let item_off = ref (-1) and item_pos = ref Lexing.dummy_pos in
  let position off =
    if off = !item_off then !item_pos else Verified_log_parser.position ln off in
  let cur_tp = ref 0 in
  let error off msg =
    prerr_endline "ERROR while parsing log:";
    prerr_endline (Log_parser.string_of_position (position off) ^ ": " ^ msg);
    if not ignore_errors then exit 1 in
  let handle = function
    | V.VO_VERDICTS vs ->
        if verbose then print_text stdout (V.tp_out (V.nat_of_integer (Z.of_int !cur_tp)));
        List.iter (fun (q, (tsq, table)) ->
            Buffer.clear text_buf;
            let ((), nonempty) =
              V.verdict_fold cfg ff n q tsq table (fun i () -> Verimon_runtime.add_dec_of_z text_buf i)
                (fun s () -> Buffer.add_string text_buf s) () in
            Buffer.output_buffer stdout text_buf;
            flush stdout;
            if stop_first && nonempty then raise Stop) vs;
        incr cur_tp
    | V.VO_ERROR (off, e) ->
        let off = Verified_log_parser.int_of_z off in
        (match V.log_error (V.c_unix cfg) lsig e with
         | V.LE_LOC msg -> error off (string_of_chars msg)
         | V.LE_ORDER msg -> prerr_endline (string_of_chars msg); exit 1
         | V.LE_CMD msg -> prerr_endline (string_of_chars msg); if not ignore_errors then exit 1) in
  let last_pending = ref (-1) in
  let forget st =
    let (_, (_, (_, sp))) = fst st in
    let sp = Verified_log_parser.int_of_z sp in
    if sp <> !item_off then begin
      item_off := sp;
      item_pos := Verified_log_parser.position ln sp
    end;
    let pending = Verified_log_parser.int_of_z (V.vpending st) in
    if pending <> !last_pending then begin
      last_pending := pending;
      Verified_log_parser.forget ln pending
    end in
  (* The outputs up to the first error, as in Algorithm_verified.run_verified: those of the
     longest prefix of the chunk whose outputs have no error, then the outputs of the whole
     chunk from the first error on. *)
  let erred = ref false in
  let is_error = function V.VO_ERROR _ -> true | V.VO_VERDICTS _ -> false in
  let rec from_error = function
    | [] -> []
    | o :: os -> if is_error o then o :: os else from_error os in
  let rec before_error = function
    | [] -> 0
    | o :: os -> if is_error o then 0 else 1 + before_error os in
  let first_error s st outs =
    match from_error outs with
    | (V.VO_ERROR (off, _) :: _) as err ->
        let n = before_error outs in
        if n = 0 then outs else begin
          let len = String.length s in
          let (base, _) = fst st in
          let p = Verified_log_parser.int_of_z off - Verified_log_parser.int_of_z base + 1 in
          let p = max 1 (min len p) in
          let (o1, st1) = V.vfeed_chunk cf (String.sub s 0 p) st in
          let ok1 = not (List.exists is_error o1) in
          if ok1 && List.length o1 = n then o1 @ err
          else begin
            let lo = ref (if ok1 then p else 0) and hi = ref (if ok1 then len else p) in
            let st_lo = ref (if ok1 then st1 else st) and acc = ref (if ok1 then List.rev o1 else []) in
            while !hi - !lo > 1 do
              let mid = (!lo + !hi) / 2 in
              let (o, st_mid) = V.vfeed_chunk cf (String.sub s !lo (mid - !lo)) !st_lo in
              if List.exists is_error o then hi := mid
              else begin
                acc := List.rev_append o !acc;
                st_lo := st_mid;
                lo := mid
              end
            done;
            List.rev !acc @ err
          end
        end
    | _ -> outs in
  let loop read =
    let rec go st =
      match read () with
      | Some s ->
          Verified_log_parser.push_chunk ln s;
          let (outs, st') = V.vfeed_chunk cf s st in
          let outs = if !erred || not (List.exists is_error outs) then outs
            else (erred := true; first_error s st outs) in
          List.iter handle outs;
          forget st';
          go st'
      | None ->
          let outs = V.vfinish cf fin st in
          let outs = if !erred || not (List.exists is_error outs) then outs
            else begin
              let outs0 = V.vfinish cf None st in
              if List.exists is_error outs0 then from_error outs else outs0 @ from_error outs
            end in
          List.iter handle outs in
    try go st with Stop -> () in
  if logfile = "" then loop (Verified_log_parser.channel_reader ~size:chunk_size stdin)
  else begin
    let ic = try open_in_bin logfile with Sys_error msg ->
      Printf.eprintf "Fatal error: exception Sys_error(\"%s\")\n%!" (String.escaped msg); exit 2 in
    Fun.protect ~finally:(fun () -> close_in_noerr ic)
      (fun () -> loop (Verified_log_parser.channel_reader ~size:chunk_size ic))
  end

let () =
  let args = Array.to_list Sys.argv in
  let prog = match args with p :: _ -> p | [] -> "verimon-cli" in
  let rest = match args with _ :: r -> r | [] -> [] in
  let pf s = float_of_string_opt s in
  let rec step = function
    | V.Done (o, e, c) ->
        print_text stdout o; print_text stderr e; exit (int_of_nat c)
    | V.Version -> print_banner (); exit 0
    | V.NeedFile (name, k) -> step (k (read_file name))
    | V.Run (msg, cfg, cf, st, fin, n, lsig) ->
        print_text stderr msg;
        (* As for monpoly -verified: a larger GC space overhead and nursery (EFFICIENCY.md,
           Sections 9 and 18, and Misc.verified_minor_heap), unless the options say otherwise. *)
        let so = int_of_int (V.c_gc_space_overhead cfg) and mh = int_of_int (V.c_gc_minor_heap cfg) in
        Gc.set { (Gc.get ()) with
          Gc.space_overhead = (if so > 0 then so else 500);
          Gc.minor_heap_size = (if mh > 0 then mh else Misc.verified_minor_heap) };
        run cfg cf st fin n lsig;
        if V.c_mem cfg then prerr_endline (Misc.mem_max ());
        exit 0 in
  step (V.cli_main prog rest pf)
