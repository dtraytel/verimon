open MFOTL
open Predicate
open Relation
open Helper

(** [is_monitorable rw] decides monitorability as the verified monitor does: after VeriMon's
    preparation of the formula, which normalizes and rewrites it if [rw] is set. *)
val is_monitorable: bool -> Db.schema -> formula -> bool * (formula * string) option
val convert_formula: Db.schema -> formula -> Verified.Monitor.tysym Verified.Monitor.formula

type db
val empty_db: unit -> db

(* tuples of a time point, collected per predicate and inserted in bulk *)
type batches
val empty_batch: unit -> batches

(* Raised by [add_to_batch] for an event whose fields do not convert, with MonPoly's message. *)
exception Conversion_error of string
val add_to_batch: batches -> Table.schema -> string list -> unit
val flush_batch: batches -> db -> db

type tyssig 
val convert_into_tysym: tcst -> Verified.Monitor.tysym
(** The signature as the verified monitor on the log reads it (Log_Monitor.thy) for a formula:
    the predicates with the types of their arguments. *)
val lsig_of_schema: Db.schema -> Verified.Monitor.tysym Verified.Monitor.formula ->
  (string * Verified.Monitor.ty list) list
val int_of_nat: Verified.Monitor.nat -> int
val convert_schema_into_sig: Db.schema -> tyssig

type state
(** [init ~mw ~rw schema f] prepares [f] as VeriMon does (type checking, and with [rw]
    normalization and rewriting, and with [mw] the conversion into multi-way joins) and builds
    the verified dense monitor's state from it. *)
val init: mw:bool -> rw:bool -> Db.schema -> Verified.Monitor.tysym Verified.Monitor.formula -> state
type verdict
val verdict_of_table: Verified.Monitor.event_data list Verified.Monitor.set -> verdict
val step: MFOTL.timestamp -> db -> state -> (int * MFOTL.timestamp * verdict) list * state
(** [show_results posl i q tsq table] prints the verdict [table] for time point [q] like
    [Helper.show_results] and returns whether it is non-empty. *)
val show_results: int list -> int -> int -> MFOTL.timestamp -> verdict -> bool
