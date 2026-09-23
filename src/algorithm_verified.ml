let no_mw = ref false
let generic_join = ref false
let imperative_join = ref false

module Monitor = struct
  type t = {
    fv_pos: int list;
    mutable cur_tp: int;
    mutable cur_ts: MFOTL.timestamp;
    mutable cur_db: Verified_adapter.db;
    cur_batch: Verified_adapter.batches;
    mutable cur_state: Verified_adapter.state;
  }

  let begin_tp ctxt ts =
    if ts >= ctxt.cur_ts then
      ctxt.cur_ts <- ts
    else
      begin
        Printf.eprintf "ERROR: Out of order timestamp %s (previous: %s)\n"
          (MFOTL.string_of_ts ts) (MFOTL.string_of_ts ctxt.cur_ts);
        exit 1
      end

  (* Events of predicates the formula does not mention are dropped before they are
     converted, as MonPoly's front end does (Filter_rel, disabled by -nofilterrel).  Only
     whole predicates are filtered, not tuples: satisfaction depends on the events of the
     formula's own predicates alone (sat_relevant_events' in Sat.thy), and the time points
     themselves are kept, since end_tp still runs for every one. *)
  let tuple ctxt ((name, _) as s) sl =
    if not !Filter_rel.enabled || Filter_rel.rel_OK name then
      Verified_adapter.add_to_batch ctxt.cur_batch s sl

  let end_tp ctxt =
    let db = Verified_adapter.flush_batch ctxt.cur_batch ctxt.cur_db in
    ctxt.cur_db <- Verified_adapter.empty_db ();
    let (vs, new_state) = Verified_adapter.step ctxt.cur_ts db ctxt.cur_state in
    ctxt.cur_state <- new_state;
    if !Misc.verbose then
      Printf.printf "At time point %d:\n%!" ctxt.cur_tp;
    List.iter (fun (q, tsq, table) ->
      let nonempty = Verified_adapter.show_results ctxt.fv_pos ctxt.cur_tp q tsq table in
      if !Misc.stop_at_first_viol && nonempty then
        raise Log_parser.Stop_parser
      ) vs;
    ctxt.cur_tp <- ctxt.cur_tp + 1

  let command ctxt _name _params =
    prerr_endline "ERROR: Commands are not supported by the verified kernel";
    if not !Misc.ignore_parse_errors then exit 1

  let end_log ctxt =
    if !Misc.new_last_ts then
      begin
        begin_tp ctxt MFOTL.ts_max;
        end_tp ctxt
      end

  let parse_error ctxt pos msg =
    prerr_endline "ERROR while parsing log:";
    prerr_endline (Log_parser.string_of_position pos ^ ": " ^ msg);
    if not !Misc.ignore_parse_errors then exit 1

  let stats _ = Log_parser.Stats.init ()
  
end

(* With -old_log_parser: MonPoly's hand-written parser, and the consumer above, which converts
   the tuples and builds the databases in OCaml. *)
module P = Log_parser.Make (Monitor)

let monitor_gen parse dbschema logfile fv f =
  (* compute permutation for output tuples *)
  let fv_pos = List.map snd (Table.get_matches (MFOTL.free_vars f) fv) in
  assert (List.length fv_pos = List.length fv);

  let cf = Verified_adapter.convert_formula dbschema f in
  let cur_state =
    Verified_adapter.init ~mw:(not !no_mw) ~rw:(not !Rewriting.no_rw) dbschema cf in
  let ctxt = Monitor.{
    fv_pos;
    cur_tp = 0;
    cur_ts = MFOTL.ts_invalid;
    cur_db = Verified_adapter.empty_db ();
    cur_batch = Verified_adapter.empty_batch ();
    cur_state;
  } in
  ignore (parse dbschema logfile ctxt)

(* The verified path (thys/MFODL_Monitor_Dense/Log_Monitor.thy): [vinit] prepares the formula
   and starts the monitor, [vfeed_chunk] reads a chunk of the log and [vfinish] the end of the
   log.  All three are generated code: the verified log parser, which skips the events of the
   predicates the formula does not mention (unless -nofilterrel) before they are even stored,
   the conversion of the timestamps and fields and the construction of the monitor's databases,
   and the verified dense monitor.  Theorems verimon_log.vrun_log and vrun_filtered state that
   the verdicts it outputs for the bytes of a log are those the specification of the formula
   prescribes for the trace the log denotes, and that it reports an error for a log that
   denotes none; this driver only reads the input, prints the verdicts and words the errors.
   Floats are read by OCaml's float_of_string, a parameter of the theorems. *)

module VM = Verified.Monitor

let string_of_nat n = MFOTL.string_of_ts (VM.integer_of_nat n)

let string_of_vty = function
  | VM.TInt -> "int"
  | VM.TFloat -> "float"
  | VM.TString -> "string"

let init_verified dbschema f =
  let cf = Verified_adapter.convert_formula dbschema f in
  let lsig = Verified_adapter.lsig_of_schema dbschema in
  let pf s = float_of_string_opt s in
  let stats n =
    if Sys.getenv_opt "MONPOLY_DENSE_STATS" <> None then
      Printf.eprintf "[verified] nodes outside the verified dense fragment: %d\n%!" n in
  match VM.vinit (not !no_mw) (not !Rewriting.no_rw) !Filter_rel.enabled lsig pf cf with
  | VM.Inr x -> stats 0; x
  | VM.Inl VM.VI_WF ->
      failwith "Error during the verified preparation of the formula: the formula is not well-formed"
  | VM.Inl (VM.VI_PREPARE e) -> failwith ("Error during the verified preparation of the formula: " ^ e)
  | VM.Inl (VM.VI_FRAGMENT n) ->
      stats (Verified_adapter.int_of_nat n);
      failwith "the formula is outside the verified dense fragment"

let run_verified dbschema fname read fv f =
  (* compute permutation for output tuples *)
  let fv_pos = List.map snd (Table.get_matches (MFOTL.free_vars f) fv) in
  assert (List.length fv_pos = List.length fv);
  let (conf, st) = init_verified dbschema f in
  let arities = Hashtbl.create 64 in
  List.iter (fun (p, tl) -> if not (Hashtbl.mem arities p) then Hashtbl.add arities p (List.length tl))
    dbschema;
  let ln = Verified_log_parser.init_lines fname in
  let cur_tp = ref 0 in
  let error off msg =
    prerr_endline "ERROR while parsing log:";
    prerr_endline (Log_parser.string_of_position (Verified_log_parser.position ln off) ^ ": " ^ msg);
    if not !Misc.ignore_parse_errors then exit 1 in
  let handle = function
    | VM.VO_VERDICTS vs ->
        if !Misc.verbose then
          Printf.printf "At time point %d:\n%!" !cur_tp;
        List.iter (fun (q, (tsq, table)) ->
          let nonempty = Verified_adapter.show_results fv_pos !cur_tp (Verified_adapter.int_of_nat q)
            (VM.integer_of_nat tsq) (Verified_adapter.verdict_of_table table) in
          if !Misc.stop_at_first_viol && nonempty then
            raise Log_parser.Stop_parser
          ) vs;
        incr cur_tp
    | VM.VO_ERROR (off, e) ->
        let off = Verified_log_parser.int_of_z off in
        (match e with
         | VM.VE_PARSE e -> error off (Verified_log_parser.message e)
         | VM.VE_TIMESTAMP ts -> error off ("Cannot convert " ^ ts ^ " into a timestamp")
         | VM.VE_ORDER (t, prev) ->
             Printf.eprintf "ERROR: Out of order timestamp %s (previous: %s)\n"
               (string_of_nat t) (string_of_nat prev);
             exit 1
         | VM.VE_PREDICATE (p, n) ->
             (match Hashtbl.find_opt arities p with
              | Some a ->
                  error off (Printf.sprintf "Wrong tuple length for predicate %s (expected: %d, actual: %d)"
                    p a (Verified_adapter.int_of_nat n))
              | None -> error off ("Predicate " ^ p ^ " was not defined in the signature."))
         | VM.VE_FIELD (p, i, t) ->
             error off (Printf.sprintf "Expected type %s for predicate %s, field number %d"
               (string_of_vty t) p (Verified_adapter.int_of_nat i + 1))
         | VM.VE_COMMAND _ ->
             prerr_endline "ERROR: Commands are not supported by the verified kernel";
             if not !Misc.ignore_parse_errors then exit 1) in
  (* the chunks before the item the parser is in are not needed for positions any more *)
  let forget (_, (_, (_, sp))) = Verified_log_parser.forget ln (Verified_log_parser.int_of_z sp) in
  let rec loop st =
    match read () with
    | Some s ->
        Verified_log_parser.push_chunk ln s;
        let (outs, st) = VM.vfeed_chunk conf s st in
        List.iter handle outs;
        forget (fst st);
        loop st
    | None ->
        let fin = if !Misc.new_last_ts then Some (VM.nat_of_integer MFOTL.ts_max) else None in
        List.iter handle (VM.vfinish conf fin st) in
  try loop st with Log_parser.Stop_parser -> ()

let monitor_string dbschema log fv f =
  if !Verified_log_parser.old then
    monitor_gen (fun dbschema log ctxt -> P.parse dbschema (Lexing.from_string log) ctxt) dbschema log fv f
  else
    run_verified dbschema "" (Verified_log_parser.string_reader log) fv f

let monitor dbschema logfile fv f =
  if !Verified_log_parser.old then
    monitor_gen (fun dbschema logfile ctxt -> P.parse_file dbschema logfile ctxt) dbschema logfile fv f
  else if logfile = "" then
    run_verified dbschema logfile (Verified_log_parser.channel_reader stdin) fv f
  else begin
    let ic = open_in_bin logfile in
    Fun.protect ~finally:(fun () -> close_in_noerr ic)
      (fun () -> run_verified dbschema logfile (Verified_log_parser.channel_reader ic) fv f)
  end
