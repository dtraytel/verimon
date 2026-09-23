open MFOTL
open Verified.Monitor
open Predicate
open Relation
open Helper

exception UnsupportedFragment of string

let unsupported msg = raise (UnsupportedFragment msg)

let int_of_nat n = Z.to_int (integer_of_nat n)
let nat_of_int i = nat_of_integer (Z.of_int i)
let enat_of_integer i = Enat (nat_of_integer i)

let convert_cst = function
  | Int x -> EInt x
  | Str x -> EString x
  | Float x -> EFloat x
  | Regexp _ -> unsupported "Regular expression constant are not supported"

let convert_var fvl bvl a = nat_of_int (try (Misc.get_pos a bvl)
    with Not_found -> (List.length bvl) + (try Misc.get_pos a fvl
        with Not_found -> List.length fvl))

let convert_term fvl bvl =
  let rec convert = function
    | Cst c -> Const (convert_cst c)
    | Var a -> Var (convert_var fvl bvl a)
    | F2i t -> F2i (convert t)
    | I2f t -> I2f (convert t)
    | Plus (t1, t2) -> Plus (convert t1, convert t2)
    | Minus (t1, t2) -> Minus (convert t1, convert t2)
    | UMinus t -> UMinus (convert t)
    | Mult (t1, t2) -> Mult (convert t1, convert t2)
    | Div (t1, t2) -> Div (convert t1, convert t2)
    | Mod (t1, t2) -> Mod (convert t1, convert t2)
    | t -> unsupported ("Unsupported term " ^ string_of_term t)
  in
  convert

let convert_interval (l,r) =
    let lm = match l with
    | OBnd a -> Z.(a + one)
    | CBnd a -> a
    | Inf -> unsupported ("Unsupported interval " ^ (string_of_interval (l,r)))
    in
    let um = match r with
    | OBnd a -> Some Z.(a - one)
    | CBnd a ->  Some a
    | Inf -> None in
    match um with
    | None -> interval (nat_of_integer lm) Infinity_enat
    | Some um ->
        if lm <= um
        then interval (nat_of_integer lm) (enat_of_integer um)
        else unsupported ("Unsupported interval " ^ (string_of_interval (l,r)))

let convert_agg_op = function
  | Cnt -> Agg_Cnt
  | Min -> Agg_Min
  | Max -> Agg_Max
  | Sum -> Agg_Sum
  | Avg -> Agg_Avg
  | Med -> Agg_Med

(* These must be synchronized with Db.base_schema *)
let special_predicates = ["tp"; "ts"; "tpts"]

let convert_special_predicate fvl bvl = function
  | ("tp", _, [t]) -> TP (convert_term fvl bvl t)
  | ("ts", _, [t]) -> TS (convert_term fvl bvl t)
  | ("tpts", _, [t1; t2]) -> And (TP (convert_term fvl bvl t1), TS (convert_term fvl bvl t2))
  | _ -> failwith "[convert_special_predicate] internal error"

let convert_formula dbschema f =
  let free_vars = MFOTL.free_vars f in
  let truth = Equal (Cst (Int Z.zero), Cst (Int Z.zero)) in
  (* First |free_vars| type variables are reserved for the free variables. *)
  let tvar_ctr = ref (List.length free_vars - 1) in
  let create_tvar () =
    incr tvar_ctr;
    Verified.Monitor.TAny (nat_of_int !tvar_ctr)
  in

  let rec convert_formula_vars fvl bvl lets = function
  | Equal (t1,t2) -> Eq (convert_term fvl bvl t1, convert_term fvl bvl t2)
  | Less (t1,t2) -> Less (convert_term fvl bvl t1, convert_term fvl bvl t2)
  | LessEq (t1,t2) -> LessEq (convert_term fvl bvl t1, convert_term fvl bvl t2)
  | Pred p ->
      let (n, a, tl) = p in
      if List.mem n special_predicates && not (List.mem (n, a) lets)
      then convert_special_predicate fvl bvl p
      else Pred (n, List.map (convert_term fvl bvl) tl)
  | Let (p,f1,f2) ->
      let (n,a,ts) = Predicate.get_info p in
      let fvl1 = List.flatten (List.map Predicate.tvars ts) in
      let lets2 = (n, a) :: lets in
      Let (n, convert_formula_vars fvl1 [] lets f1, convert_formula_vars fvl bvl lets2 f2)
  | LetPast (p,f1,f2) ->
      let (n,a,ts) = Predicate.get_info p in
      let fvl1 = List.flatten (List.map Predicate.tvars ts) in
      let lets' = (n, a) :: lets in
      LetPast (n, convert_formula_vars fvl1 [] lets' f1, convert_formula_vars fvl bvl lets' f2)
  | Frz (p,f1,f2) ->
      let (n,a,ts) = Predicate.get_info p in
      let fvl1 = List.flatten (List.map Predicate.tvars ts) in
      (* p is in scope for f2 (ψ) but not for f1 (φ) *)
      let lets2 = (n, a) :: lets in
      Frz (n, convert_formula_vars fvl1 [] lets f1,
               convert_formula_vars fvl bvl lets2 f2)
  | Neg f -> Neg (convert_formula_vars fvl bvl lets f)
  | And (f1,f2) -> And (convert_formula_vars fvl bvl lets f1, convert_formula_vars fvl bvl lets f2)
  | Or (f1,f2) -> Or (convert_formula_vars fvl bvl lets f1, convert_formula_vars fvl bvl lets f2)
  | Implies (f1,f2) -> convert_formula_vars fvl bvl lets (Or ((Neg f1), f2))
  | Equiv (f1,f2) -> convert_formula_vars fvl bvl lets (And (Implies (f1,f2),Implies(f2,f2)))
  | Exists (v,f) ->
      let rec wrap f = function
      | 0 -> f
      | n -> wrap (Exists (create_tvar (), f)) (n-1)
      in
      wrap (convert_formula_vars fvl (v@bvl) lets f) (List.length v)
  | ForAll (v,f) -> convert_formula_vars fvl bvl lets (Neg (Exists (v,(Neg f))))
  | Aggreg (_,y,op,x,glist,f) ->
      let attr = MFOTL.free_vars f in
      let bound = Misc.diff attr glist in
      let bvl_f = bound @ bvl in
      Agg (convert_var fvl bvl y,
        (convert_agg_op op, create_tvar ()),
        List.init (List.length bound) (fun _ -> create_tvar ()),
        convert_term fvl bvl_f (Var x),
        convert_formula_vars fvl bvl_f lets f)
  | Prev (intv,f) -> Prev ((convert_interval intv), (convert_formula_vars fvl bvl lets f))
  | Next (intv,f) -> Next ((convert_interval intv), (convert_formula_vars fvl bvl lets f))
  | Since (intv,f1,f2) -> Since (convert_formula_vars fvl bvl lets f1,convert_interval intv,convert_formula_vars fvl bvl lets f2)
  | Trigger (intv,f1,f2) -> Trigger (convert_formula_vars fvl bvl lets f1,convert_interval intv,convert_formula_vars fvl bvl lets f2)
  | Until (intv,f1,f2) -> Until (convert_formula_vars fvl bvl lets f1,convert_interval intv,convert_formula_vars fvl bvl lets f2)
  | Release (intv,f1,f2) -> Release (convert_formula_vars fvl bvl lets f1,convert_interval intv,convert_formula_vars fvl bvl lets f2)
  | Eventually (intv,f) -> convert_formula_vars fvl bvl lets (Until (intv,truth,f))
  | Once (intv,f) -> convert_formula_vars fvl bvl lets (Since (intv,truth,f))
  | Always (intv,f) -> convert_formula_vars fvl bvl lets (Neg (Eventually (intv,(Neg f))))
  | PastAlways (intv,f) -> convert_formula_vars fvl bvl lets (Neg (Once (intv,(Neg f))))
  | Frex (intv, r) -> MatchF (convert_interval intv, convert_re_vars fvl bvl lets r)
  | Prex (intv, r) -> MatchP (convert_interval intv, convert_re_vars fvl bvl lets r)
  | f -> unsupported (string_of_formula "Unsupported formula " f)
and convert_re_vars fvl bvl lets = function
  | Skip n -> Skip (nat_of_int n)
  | Test f -> Test (convert_formula_vars fvl bvl lets f)
  | Concat (r1,r2) -> Times (convert_re_vars fvl bvl lets r1, convert_re_vars fvl bvl lets r2)
  | Plus (r1,r2) -> Plusa (convert_re_vars fvl bvl lets r1, convert_re_vars fvl bvl lets r2)
  | Star r -> Star (convert_re_vars fvl bvl lets r)
  in convert_formula_vars free_vars [] [] f

let uconvert_tuple (pname, tl) sl =
  let pos = ref 0 in
  let type_error tname =
    let msg = Printf.sprintf ("[convert_tuple] Expected type %s for\
      \ predicate %s, field number %d") tname pname !pos in
    failwith msg
  in
  try List.map2
    (fun (_, t) s ->
      incr pos;
      (match t with
      | TInt ->
        (try EInt (Z.of_string s)
         with Invalid_argument _ -> type_error "int")
      | TStr -> EString s
      | TFloat ->
        (try EFloat (float_of_string s)
         with Failure _ -> type_error "float")
      | TRegexp -> unsupported "Regular expressions constants are not supported"
      )
    )
    tl sl
  with Invalid_argument _ ->
    let msg = Printf.sprintf "[convert_tuple] Wrong tuple length for\
      \ predicate %s (expected: %d, actual: %d)"
      pname (List.length tl) (List.length sl) in
    failwith msg

type udb = ((string * nat), ((event_data list) set list)) mapping

(* The database of one time point, in the representation the monitor in use reads. *)
type db = Short of udb

type tyssig = string * nat -> (tysym list) option

let empty_db () = Short uempty_db

(* Bulk construction of the tables of a time point.

   The tuples of each predicate are collected, sorted with [compare_utuple] (which mirrors the
   verified comparator on [event_data list]) and handed to the verified [utable_of_list],
   which checks the sortedness in linear time and then builds the red-black tree in linear
   time; if the check fails (the comparators disagree), it falls back to repeated insertion,
   so the result is [set xs] either way. Duplicates are removed only when they are equal as
   values (bitwise for floats), so no tuple is lost. *)

let compare_double x y =
  let iszero z = Stdlib.classify_float z = Stdlib.FP_zero in
  if iszero x && iszero y then Stdlib.compare (Stdlib.copysign 1.0 x) (Stdlib.copysign 1.0 y)
  else Stdlib.compare x y

let compare_event_data a b = match a, b with
  | EInt x, EInt y -> Z.compare x y
  | EInt _, _ -> -1
  | _, EInt _ -> 1
  | EFloat x, EFloat y -> compare_double x y
  | EFloat _, _ -> -1
  | _, EFloat _ -> 1
  | EString x, EString y -> String.compare x y

let equal_event_data a b = match a, b with
  | EInt x, EInt y -> Z.equal x y
  | EFloat x, EFloat y -> Int64.equal (Int64.bits_of_float x) (Int64.bits_of_float y)
  | EString x, EString y -> String.equal x y
  | _ -> false

let rec compare_utuple a b = match a, b with
  | [], [] -> 0
  | [], _ -> -1
  | _, [] -> 1
  | x :: xs, y :: ys ->
    let c = compare_event_data x y in
    if c <> 0 then c else compare_utuple xs ys

let equal_utuple a b =
  List.length a = List.length b && List.for_all2 equal_event_data a b

let rec dedup_sorted eq = function
  | x :: (y :: _ as rest) -> if eq x y then dedup_sorted eq rest else x :: dedup_sorted eq rest
  | l -> l

(* The batch is keyed by the predicate name and its arity.  The generic [Hashtbl] would
   hash and compare that key structurally, which means hashing the name and the
   arbitrary-precision arity and then running the polymorphic comparison down the bucket
   chain -- on the Until benchmark that was 5.5% of the run in [do_compare_val] alone and a
   further 1.6% in [caml_hash].  Hashing the name and comparing the two components directly
   costs a fraction of that, and the arity stays a machine integer until the flush. *)
module Pred_key = struct
  type t = string * Stdlib.Int.t
  let equal ((p1 : string), (a1 : Stdlib.Int.t)) (p2, a2) = a1 = a2 && String.equal p1 p2
  let hash ((p : string), _) = Hashtbl.hash p
end
module Pred_tbl = Hashtbl.Make(Pred_key)

(* Events of one time point arrive grouped by predicate, so the table is consulted once per
   predicate rather than once per event: [b_last] holds the list the previous event went
   into.  The type list is the signature's own, so physical equality identifies the
   predicate -- except for nullary predicates, whose list is the immediate [[]], hence the
   name check as well.  [b_live] invalidates the cache at the flush, which drops the
   lists. *)
type 'a batch = {
  b_conv: (string * (string * tcst) list) -> string list -> 'a;
  b_tbl: 'a list ref Pred_tbl.t;
  mutable b_live: bool;
  mutable b_tl: (string * tcst) list;
  mutable b_name: string;
  mutable b_last: 'a list ref;
}

type batches = UB of event_data list batch

let empty_batch () : batches =
  let mk conv = { b_conv = conv; b_tbl = Pred_tbl.create 16; b_live = false; b_tl = [];
                  b_name = ""; b_last = ref [] } in
  UB (mk uconvert_tuple)

let add_gen : 'a. 'a batch -> string * (string * tcst) list -> string list -> unit =
  fun b ((pname, tl) as schema) sl ->
  let t = b.b_conv schema sl in
  if b.b_live && b.b_tl == tl && String.equal b.b_name pname then
    b.b_last := t :: !(b.b_last)
  else begin
    let r =
      match Pred_tbl.find_opt b.b_tbl (pname, List.length tl) with
      | Some r -> r
      | None ->
        let r = ref [] in Pred_tbl.add b.b_tbl (pname, List.length tl) r; r in
    r := t :: !r;
    b.b_live <- true; b.b_tl <- tl; b.b_name <- pname; b.b_last <- r
  end

let add_to_batch b schema sl = match b with
  | UB b -> add_gen b schema sl

let flush_gen cmp eq tbl_of ins b db =
  let db = Pred_tbl.fold (fun (pname, a) r db ->
    let sorted = dedup_sorted eq (List.stable_sort cmp !r) in
    ins (pname, nat_of_int a) (tbl_of sorted) db) b.b_tbl db in
  (* keep the bucket array; [reset] would reallocate it at every time point *)
  Pred_tbl.clear b.b_tbl;
  b.b_live <- false;
  db

let flush_batch b db = match b, db with
  | UB b, Short db ->
    Short (flush_gen compare_utuple equal_utuple utable_of_list uinsert_table_into_db b db)

(* The signature as the verified monitor on the log reads it (Log_Monitor.thy): the predicates
   with the types of their arguments.  The verified monitor does not support regular
   expressions: a formula that mentions a predicate with such an argument is refused, as
   [convert_schema_into_sig] refuses it when the type checker looks the predicate up; the
   arguments of the other such predicates are read as strings (the parser drops their events
   unless -nofilterrel). *)
let rec vpred_names acc (f : tysym Verified.Monitor.formula) = match f with
  | Verified.Monitor.Pred (p, _) -> p :: acc
  | Verified.Monitor.Let (_, a, b) | Verified.Monitor.Frz (_, a, b)
  | Verified.Monitor.LetPast (_, a, b) | Verified.Monitor.Or (a, b) | Verified.Monitor.And (a, b)
  | Verified.Monitor.Since (a, _, b) | Verified.Monitor.Until (a, _, b)
  | Verified.Monitor.Trigger (a, _, b) | Verified.Monitor.Release (a, _, b) ->
      vpred_names (vpred_names acc a) b
  | Verified.Monitor.Neg a | Verified.Monitor.Exists (_, a) | Verified.Monitor.Agg (_, _, _, _, a)
  | Verified.Monitor.Prev (_, a) | Verified.Monitor.Next (_, a) -> vpred_names acc a
  | Verified.Monitor.Ands l -> List.fold_left vpred_names acc l
  | Verified.Monitor.MatchF (_, r) | Verified.Monitor.MatchP (_, r) -> vregex_names acc r
  | Verified.Monitor.Eq _ | Verified.Monitor.Less _ | Verified.Monitor.LessEq _
  | Verified.Monitor.TP _ | Verified.Monitor.TS _ -> acc
and vregex_names acc = function
  | Verified.Monitor.Skip _ -> acc
  | Verified.Monitor.Test a -> vpred_names acc a
  | Verified.Monitor.Plusa (r, s) | Verified.Monitor.Times (r, s) -> vregex_names (vregex_names acc r) s
  | Verified.Monitor.Star r -> vregex_names acc r

let lsig_of_schema dbschema cf =
  let names = vpred_names [] cf in
  List.map (fun (pname, tl) -> (pname, List.map (fun (_, t) -> match t with
      TInt -> Verified.Monitor.TInt
    | TFloat -> Verified.Monitor.TFloat
    | TStr -> Verified.Monitor.TString
    | TRegexp ->
        if List.mem pname names then unsupported "Regular expressions constants are not supported"
        else Verified.Monitor.TString) tl)) dbschema

let convert_into_tysym ty = 
  match ty with
    TInt -> Verified.Monitor.TCst (Verified.Monitor.TInt)
  | TFloat -> Verified.Monitor.TCst (Verified.Monitor.TFloat)
  | TStr -> Verified.Monitor.TCst (Verified.Monitor.TString)
  | TRegexp -> unsupported "Regular expressions constants are not supported"

let rec convert_schema_into_sig sch = 
  match sch with
    (pname, tl) :: rest -> (fun k -> if k = (pname, nat_of_int (List.length tl))
                                      then Some (List.map convert_into_tysym (List.map snd tl))
                                      else (convert_schema_into_sig rest) k)
  | [] -> (fun k -> None)

(* The monitor is the verified dense evaluator (thys/MFODL_Monitor_Dense): the algorithm of
   Dense_Eval.thy, which drops the empty columns, run on the short tuples as
   Dense_Unbox_Exec.thy states it.  [udminit_verimon] prepares the formula as VeriMon does
   (Dense_VeriMon.thy): it type checks it and, if it is not monitorable and [rw] is set,
   normalizes and rewrites it; then, if [mw] is set, it converts it into multi-way joins; then
   [udminit_push] moves existential quantifiers into the past and future diamonds they commute
   with (Dense_Push.thy) and compiles the result into the dense one.  [udmstep] performs one
   step; all of these are pure functions.  The theorem udminit_verimon_mverdicts of
   Dense_VeriMon.thy states that the verdicts are those of the input formula, through the
   simulation theorem of Dense_Eval.thy and the refinement theorems of Dense_Exec.thy and
   Dense_Unbox_Exec.thy, provided the compiler placed every node: [uvdfail_nodes] counts the
   ones it could not, and a formula with any is refused rather than run outside the theorem.
   The front end therefore neither type checks nor rewrites the formula itself for this monitor
   (see [Rewriting.check_formula]). *)
type state = unit udmstate_ext

let init ~mw ~rw dbschema cf =
  let st = match udminit_verimon mw rw (convert_schema_into_sig dbschema) cf with
    | Inl e -> failwith ("Error during the verified preparation of the formula: " ^ e)
    | Inr st -> st in
  let nf = int_of_nat (uvdfail_nodes (udmstate_m st)) in
  if Sys.getenv_opt "MONPOLY_DENSE_STATS" <> None then
    Printf.eprintf "[verified] nodes outside the verified dense fragment: %d\n%!" nf;
  if nf <> 0 then
    failwith "the formula is outside the verified dense fragment";
  st

let uset_fold f s x = match s with
  | RBT_set r -> urbt_fold f r x
  | _ -> failwith "[uset_fold] unexpected set representation"

(* Verdicts are kept in the kernel's representation; [show_results] below prints them without
   converting to [Tuple.tuple] first.  The monitor over the short tuples produces them without
   the option around the fields. *)
type verdict = UV of event_data list set

let verdict_of_table t = UV t

let annotate wrap vs =
  List.map (fun (tp, (ts, v)) -> (int_of_nat tp, integer_of_nat ts, wrap v)) vs

let step t (Short db) st =
  let (vs, st') = udmstep (db, nat_of_integer t) st in
  (annotate (fun v -> UV v) vs, st')

(* Direct output of verdicts.

   The tuples of a verdict table are folded out of the red-black tree in the order of the
   verified comparator, projected to the requested positions, and written into a buffer with
   the same formatting as [Predicate.string_of_cst]/[Tuple.string_of_tuple]. This avoids
   allocating [Tuple.tuple]s and intermediate strings for every result tuple (formerly around
   a third of the running time for formulas with large output). The output order is that of
   MonPoly ([Tuple.compare], ranking Int < Str < Float), which coincides with the tree order on
   well-typed tables; the list is re-sorted only if the check fails (e.g. after a non-monotone
   projection). *)

let mp_rank = function EInt _ -> 0 | EString _ -> 1 | EFloat _ -> 2

let compare_event_data_mp a b = match a, b with
  | EInt x, EInt y -> Z.compare x y
  | EString x, EString y -> String.compare x y
  | EFloat x, EFloat y -> Stdlib.compare (x: float) y
  | _, _ -> Stdlib.compare (mp_rank a) (mp_rank b)

let rec compare_tuple_mp t1 t2 = match t1, t2 with
  | [], [] -> 0
  | [], _ :: _ -> -1
  | _ :: _, [] -> 1
  | x :: xs, y :: ys ->
    let c = compare_event_data_mp x y in
    if c <> 0 then c else compare_tuple_mp xs ys

(* Decimal representation of a machine integer written directly into the buffer
   ([string_of_int] goes through [Printf]-style formatting and allocates). The scratch bytes
   are allocated once rather than per integer: printing a verdict of a few thousand tuples
   calls this once per column, and the per-call [Bytes.create] was the largest allocation
   site of the [once] benchmark (see EFFICIENCY.md, Section 15). Writing them is finished
   before anything else can run, so one buffer for the whole run is enough. *)
let int_digits = Bytes.create 20

let add_int b n =
  if n = 0 then Buffer.add_char b '0'
  else if n = min_int then Buffer.add_string b (string_of_int n)
  else begin
    let n = if n < 0 then (Buffer.add_char b '-'; -n) else n in
    let digits = int_digits in
    let rec go n k = if n = 0 then k else begin
        Bytes.unsafe_set digits k (Char.unsafe_chr (48 + n mod 10)); go (n / 10) (k - 1) end in
    let k = go n 19 in
    Buffer.add_subbytes b digits (k + 1) (19 - k)
  end

let add_event_data b = function
  | EInt i ->
    if Z.fits_int i then add_int b (Z.to_int i) else Buffer.add_string b (Z.to_string i)
  | EFloat f -> Buffer.add_string b (Printf.sprintf "%g" f)
  | EString s ->
    let n = String.length s in
    if n = 0 then Buffer.add_string b "\"\""
    else if s.[0] = '\"' && s.[n-1] = '\"' then Buffer.add_string b s
    else begin Buffer.add_char b '\"'; Buffer.add_string b s; Buffer.add_char b '\"' end

let add_tuple b t =
  Buffer.add_char b '(';
  List.iteri (fun k x -> if k > 0 then Buffer.add_char b ','; add_event_data b x) t;
  Buffer.add_char b ')'

let add_tuples_ext b lm rm del t = match t with
  | [] -> Buffer.add_string b lm; Buffer.add_string b rm
  | _ ->
    Buffer.add_string b lm;
    List.iteri (fun k x -> if k > 0 then Buffer.add_string b del; add_tuple b x) t;
    Buffer.add_string b rm

let rec is_enum_list n = function
  | [] -> true
  | x :: l -> x = n && is_enum_list (n + 1) l

let show_results_slow_gen posl q tsq rows =
  let tuples = if is_enum_list 0 posl then rows
    else List.map (fun t -> Misc.get_positions posl t) rows in
  let rec strictly_sorted = function
    | x :: (y :: _ as rest) -> compare_tuple_mp x y < 0 && strictly_sorted rest
    | _ -> true
  in
  let tuples = if strictly_sorted tuples then tuples
    else List.sort_uniq compare_tuple_mp tuples in
  let tuples =
    if !Misc.stop_at_first_viol then
      (match tuples with t :: _ :: _ -> [t] | _ -> tuples)
    else tuples
  in
  let b = Buffer.create 1024 in
  if !Misc.verbose then
    if posl = [] then
      Printf.printf "@%s (time point %d): %b\n%!" (MFOTL.string_of_ts tsq) q (tuples <> [])
    else begin
      Buffer.add_string b (Printf.sprintf "@%s (time point %d): " (MFOTL.string_of_ts tsq) q);
      add_tuples_ext b "(" ")" "," tuples;
      Buffer.add_char b '\n';
      print_string (Buffer.contents b);
      flush stdout
    end
  else begin
    if Misc.debugging Dbg_perf then
      Perf.show_results q tsq;
    if tuples <> [] then (* formula satisfied *)
      if posl = [] then (* no free variables *)
        Printf.printf "@%s (time point %d): true\n%!" (MFOTL.string_of_ts tsq) q
      else begin (* free variables *)
        Buffer.add_string b (Printf.sprintf "@%s (time point %d): " (MFOTL.string_of_ts tsq) q);
        add_tuples_ext b "" "" " " tuples;
        Buffer.add_char b '\n';
        print_string (Buffer.contents b);
        flush stdout
      end
  end;
  tuples <> []

let show_results_slow posl q tsq v =
  let rows = match v with
    | UV table -> List.rev (uset_fold (fun t acc -> t :: acc) table []) in
  show_results_slow_gen posl q tsq rows

exception Slow_path

(* Fast path for the common case (no projection, not verbose, all violations wanted): the
   tuples are streamed from the tree in its order straight into the buffer, without building
   tuple lists; the order is checked against the previous tuple on the way. If the tree order
   is not MonPoly's (mixed-type columns) or a column is undefined, the general path is taken. *)
let out_buf = Buffer.create 4096

(* The columns of one tuple, as a top-level function rather than a closure passed to
   [List.iteri]: the closure was allocated once per tuple of every verdict. *)
let rec add_utuple b first = function
  | [] -> ()
  | v :: r -> if not first then Buffer.add_char b ','; add_event_data b v; add_utuple b false r

let show_results_gen fold add_row cmp_prev slow q tsq table =
  begin
    (* Most time points have no verdict, so nothing is built until the first tuple arrives:
       the header costs a [Printf.sprintf], which interprets its format at run time and was
       1.7% of P2 on its own, and the buffer is reused across time points rather than
       allocated per call. The header is still written before the tuples, because it is
       printed directly and the tuples follow from the buffer. *)
    let b = out_buf in
    Buffer.clear b;
    let prev = ref None in
    let ok =
      try
        fold (fun t () ->
            (match !prev with
             | Some p -> if cmp_prev p t >= 0 then raise Slow_path; Buffer.add_char b ' '
             | None -> ());
            Buffer.add_char b '(';
            add_row b true t;
            Buffer.add_char b ')';
            prev := Some t) table ();
        true
      with Slow_path -> false
    in
    if not ok then slow ()
    else begin
      if Misc.debugging Dbg_perf then Perf.show_results q tsq;
      if !prev <> None then begin
        print_string "@";
        print_string (MFOTL.string_of_ts tsq);
        print_string " (time point ";
        print_string (string_of_int q);
        print_string "): ";
        Buffer.add_char b '\n';
        print_string (Buffer.contents b);
        flush stdout
      end;
      !prev <> None
    end
  end

let show_results posl _i q tsq (v: verdict) =
  if !Misc.verbose || !Misc.stop_at_first_viol || posl = [] || not (is_enum_list 0 posl) then
    show_results_slow posl q tsq v
  else match v with
    | UV table ->
      show_results_gen uset_fold add_utuple compare_tuple_mp
        (fun () -> show_results_slow posl q tsq v) q tsq table

(* Monitorability as the verified monitor decides it: the formula is accepted if VeriMon's
   preparation (type checking and, with [rw], normalization and rewriting) yields a monitorable
   formula. *)
let is_monitorable rw dbschema f =
  match prepare_verimon rw (convert_schema_into_sig dbschema) (convert_formula dbschema f) with
  | Inr _ -> (true, None)
  | Inl e when e = "not monitorable" -> (false, Some (f, "MFODL formula is not monitorable"))
  | Inl e -> (false, Some (f, "MFODL formula is not monitorable (" ^ e ^ ")"))
