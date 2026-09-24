(* Throughput of the two log parsers alone: MonPoly's hand-written one (Log_parser) and the
   verified one (Verified_log_parser, generated from session Log_Parser), each driving a consumer
   that only counts the events (with -convert, it also converts the fields as MonPoly's consumer
   does, with Tuple.make_tuple2).  The monitor is not run.

   Usage: log_parser_bench -sig FILE [-convert] [-runs N] LOG *)

open Libmonpoly

let convert = ref false

module Count = struct
  type t = { mutable tps : int; mutable evs : int; st : Log_parser.Stats.t }
  let begin_tp c _ = c.tps <- c.tps + 1
  let tuple c (_, tl) sl =
    c.evs <- c.evs + 1;
    if !convert then ignore (Sys.opaque_identity (Tuple.make_tuple2 sl tl))
  let end_tp _ = ()
  let command _ _ _ = ()
  let end_log _ = ()
  let parse_error _ _ msg = prerr_endline ("parse error: " ^ msg)
  let stats c = c.st
end

module Old = Log_parser.Make (Count)
module New = Verified_log_parser.Make (Count)

let () =
  let sig_file = ref "" and runs = ref 3 and log = ref "" in
  Arg.parse
    [ ("-sig", Arg.Set_string sig_file, "signature");
      ("-convert", Arg.Set convert, "convert the fields");
      ("-runs", Arg.Set_int runs, "runs per parser") ]
    (fun f -> log := f) "log_parser_bench -sig FILE [-convert] [-runs N] LOG";
  let schema = Log_parser.parse_signature_file !sig_file in
  let size = float_of_int (Unix.stat !log).Unix.st_size /. 1e6 in
  let bench name parse =
    let times = List.init !runs (fun _ ->
      Gc.compact ();
      let c = { Count.tps = 0; evs = 0; st = Log_parser.Stats.init () } in
      let t0 = Unix.gettimeofday () in
      ignore (parse schema !log c);
      let t = Unix.gettimeofday () -. t0 in
      (t, c)) in
    let t, c = List.hd (List.sort compare times) in
    Printf.printf "%-9s %7.3f s  %6.1f MB/s  %6.2f M events/s  (%d time points, %d events)\n%!"
      name t (size /. t) (float_of_int c.Count.evs /. t /. 1e6) c.Count.tps c.Count.evs in
  bench "old" Old.parse_file;
  bench "verified" New.parse_file
