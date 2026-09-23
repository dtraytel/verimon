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
   predicates the signature declares but whose names do not occur freely in the formula (unless
   -nofilterrel) before they are even stored, the conversion of the timestamps and fields and
   the construction of the monitor's databases, and the verified dense monitor.  Theorems
   verimon_log.vrun_log and vrun_filtered state that the verdicts output for the bytes of a log
   are those the specification of the formula prescribes for the prefix the log denotes, and
   that an error is reported exactly when the log restricted to the predicates it keeps denotes
   no prefix; vfeed_chunks_online states the same for the chunks read so far.  Theory
   Log_Monitor_Online states it for this interface, call by call: the initial state satisfies
   the invariant wf_vstate for the bytes read and the prefix they denote (wf_vstate_vinit), and
   a call of vfeed_chunk (vfeed_chunk_online) or vfinish (vfinish_online) from such a state
   either reports an error, exactly when the bytes no longer denote a prefix, or reports none,
   outputs exactly the verdicts that the specification prescribes for the longer prefix and not
   for the shorter one, and (for vfeed_chunk) leaves a state that satisfies the invariant.  The theorems cover the output up to the first error (for the chunk with the first
   error, the driver outputs the verdicts of its longest prefix without an error, see
   first_error), but not what is output after it (with -ignore_parse_errors), nor which error
   is reported.

   Outside the theorems: the formula is MonPoly's, as its front end has read, checked and
   possibly rewritten it, converted by Verified_adapter.convert_formula; the signature is
   MonPoly's; floats are read by float_of_string_opt, a parameter of the theorems; the last
   time point at MaxTS is added unless -nonewlastts or the formula is past-only; and this driver
   reads the input, prints the verdicts, words and locates the errors, and decides whether to
   go on after an error. *)

module VM = Verified.Monitor

let string_of_nat n = MFOTL.string_of_ts (VM.integer_of_nat n)

let string_of_vty = function
  | VM.TInt -> "int"
  | VM.TFloat -> "float"
  | VM.TString -> "string"

let init_verified dbschema f =
  let cf = Verified_adapter.convert_formula dbschema f in
  let lsig = Verified_adapter.lsig_of_schema dbschema cf in
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
  (* Positions: the chunks are kept from the pending lexeme on ([vpending]); the position of
     the pending item, which errors about an entry are reported at, is computed when the item
     begins. *)
  let ln = Verified_log_parser.init_lines fname in
  let item_off = ref (-1) and item_pos = ref Lexing.dummy_pos in
  let position off =
    if off = !item_off then !item_pos else Verified_log_parser.position ln off in
  let cur_tp = ref 0 in
  let error off msg =
    prerr_endline "ERROR while parsing log:";
    prerr_endline (Log_parser.string_of_position (position off) ^ ": " ^ msg);
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
  let last_pending = ref (-1) in
  let forget st =
    let (_, (_, (_, sp))) = fst st in
    let sp = Verified_log_parser.int_of_z sp in
    if sp <> !item_off then begin
      item_off := sp;
      item_pos := Verified_log_parser.position ln sp
    end;
    (* dropping walks the chunks kept, so it is done only when the offset changes *)
    let pending = Verified_log_parser.int_of_z (VM.vpending st) in
    if pending <> !last_pending then begin
      last_pending := pending;
      Verified_log_parser.forget ln pending
    end in
  (* The outputs up to the first error: those of the longest prefix of the chunk whose outputs
     have no error (the outputs only grow with the input), followed by the outputs of the whole
     chunk from the first error on.  The prefix is found by bisection, feeding each probe from
     the state after the longest prefix found so far, so that the chunk is read about twice;
     vfeed_chunk_online covers each probe, from a state that satisfies the invariant.  If no
     verdict precedes the error, there is nothing to find.  After the first error, the outputs
     are handled as they come. *)
  let erred = ref false in
  let is_error = function VM.VO_ERROR _ -> true | VM.VO_VERDICTS _ -> false in
  let rec from_error = function
    | [] -> []
    | o :: os -> if is_error o then o :: os else from_error os in
  let first_error s st outs =
    match outs with
    | o :: _ when is_error o -> outs
    | _ ->
        let lo = ref 0 and hi = ref (String.length s) and st_lo = ref st and acc = ref [] in
        while !hi - !lo > 1 do
          let mid = (!lo + !hi) / 2 in
          let (o, st_mid) = VM.vfeed_chunk conf (String.sub s !lo (mid - !lo)) !st_lo in
          if List.exists is_error o then hi := mid
          else begin
            acc := List.rev_append o !acc;
            st_lo := st_mid;
            lo := mid
          end
        done;
        List.rev !acc @ from_error outs in
  let rec loop st =
    match read () with
    | Some s ->
        Verified_log_parser.push_chunk ln s;
        let (outs, st') = VM.vfeed_chunk conf s st in
        let outs = if !erred || not (List.exists is_error outs) then outs
          else (erred := true; first_error s st outs) in
        List.iter handle outs;
        forget st';
        loop st'
    | None ->
        let fin = if !Misc.new_last_ts then Some (VM.nat_of_integer MFOTL.ts_max) else None in
        let outs = VM.vfinish conf fin st in
        let outs = if !erred || not (List.exists is_error outs) then outs
          else begin
            (* without the last time point, vrun_filtered covers the outputs if they have no
               error *)
            let outs0 = VM.vfinish conf None st in
            if List.exists is_error outs0 then from_error outs else outs0 @ from_error outs
          end in
        List.iter handle outs in
  try loop st with Log_parser.Stop_parser -> ()

(* The verdicts of a chunk are output together, so they survive the monitor's steps on the
   chunk's other time points; small chunks keep them from being promoted to the major heap. *)
let chunk_size = ref 512

let monitor_string dbschema log fv f =
  if !Verified_log_parser.old then
    monitor_gen (fun dbschema log ctxt -> P.parse dbschema (Lexing.from_string log) ctxt) dbschema log fv f
  else
    run_verified dbschema "" (Verified_log_parser.string_reader ~size:!chunk_size log) fv f

let monitor dbschema logfile fv f =
  if !Verified_log_parser.old then
    monitor_gen (fun dbschema logfile ctxt -> P.parse_file dbschema logfile ctxt) dbschema logfile fv f
  else if logfile = "" then
    run_verified dbschema logfile (Verified_log_parser.channel_reader ~size:!chunk_size stdin) fv f
  else begin
    let ic = open_in_bin logfile in
    Fun.protect ~finally:(fun () -> close_in_noerr ic)
      (fun () -> run_verified dbschema logfile (Verified_log_parser.channel_reader ~size:!chunk_size ic) fv f)
  end
