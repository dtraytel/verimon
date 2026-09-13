open MFOTL
open Predicate
open Relation
open Helper

val is_monitorable: Db.schema -> formula -> bool * (formula * string) option
val convert_formula: Db.schema -> formula -> Verified.Monitor.tysym Verified.Monitor.formula

type db
val empty_db: db
val insert_into_db: Table.schema -> string list -> db -> db

(* tuples of a time point, collected per predicate and inserted in bulk *)
type batch
val empty_batch: unit -> batch
val add_to_batch: batch -> Table.schema -> string list -> unit
val flush_batch: batch -> db -> db

type tyssig 
val convert_into_tysym: tcst -> Verified.Monitor.tysym
val convert_schema_into_sig: Db.schema -> tyssig
val type_check_formula: Db.schema -> Verified.Monitor.tysym Verified.Monitor.formula -> (string, Verified.Monitor.ty Verified.Monitor.formula) Verified.Monitor.sum

type state
val init: Verified.Monitor.ty Verified.Monitor.formula -> state
val step: MFOTL.timestamp -> db -> state -> (int * MFOTL.timestamp * Tuple.tuple list) list * state
