open Relation
open Predicate
open MFOTL
open Tuple

module Sk = Dllist
module Sj = Dllist

type info  = (int * timestamp * relation) Queue.t
type linfo = {mutable llast: Neval.cell}
type ainfo = {mutable arel: relation option}
type pinfo = {mutable plast: Neval.cell}
type ninfo = {mutable init: bool}

type agg_info = {op: agg_op; default: cst}

type sinfo = {mutable srel2: relation option;
              saux: Optimized_mtl.msaux}
type uinfo = {mutable ulast: Neval.cell;
              mutable urel2: relation option;
              uaux: Optimized_mtl.muaux}

type comp_one = relation -> relation
type comp_two = relation -> relation -> relation

type mregex =
  | MSkip of int
  | MTestPos of int
  | MTestNeg of int
  | MPlus of (mregex * mregex)
  | MTimes of (mregex *  mregex)
  | MStar of mregex

type 'a mregex_map

val mrfind: mregex -> 'a mregex_map  -> 'a
val mradd: mregex-> 'a -> 'a mregex_map  -> 'a mregex_map
val mrupdate: mregex -> ('a option -> 'a option) -> 'a mregex_map  -> 'a mregex_map
val mrempty: 'a mregex_map

type rargs = {intv: interval;
  mr: mregex;
  mrs: mregex list;
  attr_fs: var list list}

type mpinfo = {args: rargs;
  mutable mrdeltaaux: (timestamp * relation mregex_map) list;
  mutable buf: relation list list;
  mutable crt: Neval.cell;
  mutable last: Neval.cell;
  mutable out: relation list}

type mfinfo = {args: rargs;
  mutable mldeltaaux: (timestamp * relation list * relation) list;
  mutable buf: relation list list;
  mutable crt: Neval.cell;
  mutable last: Neval.cell;
  mutable out: relation list}

(* pdinfo: per-predicate info with optional constant relation for FRZ.
   When [pconst = Some r] the predicate yields [r] at every timepoint
   (the native "mres Const" analog) instead of consuming the queue. *)
type pdinfo = {
  pqueue: info;
  mutable pconst: relation option;
}

and frz_inst = {
  mutable inst_last: Neval.cell;
  inst_tp: int;
  inst_psi: extformula;
  mutable inst_done: bool;
}

and frz_static = {
  fst_psia: extformula;
  fst_q_pdinfos: pdinfo list;
  mutable fst_pending: (int * relation) option;
}

and frz_per_inst = {
  fpi_neval0: Neval.cell;
  mutable fpi_active: frz_inst Queue.t;
  mutable fpi_mk_inst: unit -> extformula;
  mutable fpi_db_hist: (int * MFOTL.timestamp * (string * relation) list) Queue.t;
  fpi_depth: MFOTL.tsdiff option;
  mutable fpi_win_edge: Neval.cell;
}

and frz_mode =
  | FrzStatic of frz_static
  | FrzPerInst of frz_per_inst

and frz_info = {
  mutable frz_phi_last: Neval.cell;
  frz_mode: frz_mode;
}

and extformula =
  | ERel of relation * int
  | EPred of predicate * comp_one * pdinfo * int
  | ELet of predicate * comp_one * extformula * extformula * linfo * int
  | ENeg of extformula * int
  | EAnd of comp_two * extformula * extformula * ainfo * int
  | EOr of comp_two * extformula * extformula * ainfo * int
  | EExists of comp_one * extformula * int
  | EAggreg of agg_info * Aggreg.aggregator * extformula * int
  | EAggOnce of agg_info * Aggreg.once_aggregator * extformula * int
  | EPrev of interval * extformula * pinfo * int
  | ENext of interval * extformula * ninfo * int
  | ESince of extformula * extformula * sinfo * int
  | EUntil of extformula * extformula * uinfo * int
  | EMatchP of extformula list * mpinfo * int
  | EMatchF of extformula list * mfinfo * int
  | EFrz of predicate * comp_one * extformula * frz_info * int

val contains_eventually: extformula -> bool

val prerr_auxel:  int * Relation.relation -> unit
val prerr_sauxel: MFOTL.timestamp * Relation.relation -> unit

val prerr_predinf: string -> pdinfo -> unit
val prerr_uinf: string -> uinfo -> unit

val prerr_extf: string -> extformula -> unit

val extf_structure: extformula -> string
