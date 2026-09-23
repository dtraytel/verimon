(* The verified log parser (session Log_Parser), with the interface of Log_parser.Make.  Both
   monitors read their logs with it unless [old] is set (option -old_log_parser), which selects
   MonPoly's hand-written parser, for differential testing. *)

val old: bool ref

(* The size of the chunks the log is read in (4096). *)
val chunk_size: int ref

(* Readers of the input in chunks of [size] bytes ([chunk_size] by default). *)
val channel_reader: ?size:int -> in_channel -> unit -> string option
val string_reader: ?size:int -> string -> unit -> string option

(* The keep function of the parser that keeps all events, as MonPoly's consumer needs them. *)
val keep_all: string -> bool

(* Lines and columns of the byte offsets the parser reports: [push_chunk] records a chunk read,
   [position] locates an offset, and [forget] drops the chunks before an offset, which no later
   report precedes. *)
type lines
val init_lines: string -> lines
val push_chunk: lines -> string -> unit
val forget: lines -> int -> unit
val position: lines -> int -> Lexing.position
val int_of_z: Z.t -> int

(* An error of the parser, as MonPoly's parser words it. *)
val message: Verified.Monitor.perror -> string

module Make (C: Log_parser.Consumer): sig
  val parse_string: Db.schema -> string -> C.t -> bool
  val parse_channel: Db.schema -> string -> in_channel -> C.t -> bool
  val parse_file: Db.schema -> string -> C.t -> bool
end
