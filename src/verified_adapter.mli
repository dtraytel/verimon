open MFOTL
open Predicate
open Relation
open Helper

val is_monitorable: Db.schema -> formula -> bool * (formula * string) option
val convert_formula: Db.schema -> formula -> Verified.Monitor.tysym Verified.Monitor.formula

type db
val empty_db: unit -> db

(* tuples of a time point, collected per predicate and inserted in bulk *)
type batches
val empty_batch: unit -> batches
val add_to_batch: batches -> Table.schema -> string list -> unit
val flush_batch: batches -> db -> db

type tyssig 
val convert_into_tysym: tcst -> Verified.Monitor.tysym
val convert_schema_into_sig: Db.schema -> tyssig
val type_check_formula: Db.schema -> Verified.Monitor.tysym Verified.Monitor.formula -> (string, Verified.Monitor.ty Verified.Monitor.formula) Verified.Monitor.sum

type state
val init: Verified.Monitor.ty Verified.Monitor.formula -> state
type verdict
val step: MFOTL.timestamp -> db -> state -> (int * MFOTL.timestamp * verdict) list * state
(** [show_results posl i q tsq table] prints the verdict [table] for time point [q] like
    [Helper.show_results] and returns whether it is non-empty. *)
val show_results: int list -> int -> int -> MFOTL.timestamp -> verdict -> bool
