(* The verified log parser (session Log_Parser), with the interface of Log_parser.Make.  Both
   monitors read their logs with it unless [old] is set (option -old_log_parser), which selects
   MonPoly's hand-written parser, for differential testing. *)

val old: bool ref

(* The size of the chunks the log is read in (4096). *)
val chunk_size: int ref

module Make (C: Log_parser.Consumer): sig
  val parse_string: Db.schema -> string -> C.t -> bool
  val parse_channel: Db.schema -> string -> in_channel -> C.t -> bool
  val parse_file: Db.schema -> string -> C.t -> bool
end
