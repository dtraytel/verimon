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

module P = Log_parser.Make (Monitor)
module V = Verified_log_parser.Make (Monitor)

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

let monitor_string = monitor_gen (fun dbschema log ctxt ->
  if !Verified_log_parser.old then P.parse dbschema (Lexing.from_string log) ctxt
  else V.parse_string dbschema log ctxt)
let monitor = monitor_gen (fun dbschema logfile ctxt ->
  if !Verified_log_parser.old then P.parse_file dbschema logfile ctxt
  else V.parse_file dbschema logfile ctxt)
