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

let convert_tuple (pname, tl) sl =
  let pos = ref 0 in
  let type_error tname =
    let msg = Printf.sprintf ("[convert_tuple] Expected type %s for\
      \ predicate %s, field number %d") tname pname !pos in
    failwith msg
  in
  try List.map2
    (fun (_, t) s ->
      incr pos;
      Some (match t with
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

type db = ((string * nat), (((event_data option) list) set list)) mapping
type tyssig = string * nat -> (tysym list) option

let empty_db = empty_db

let insert_into_db ((pname, tl) as schema) sl db =
  let a = nat_of_int (List.length tl) in
  insert_into_db (pname, a) (convert_tuple schema sl) db

(* Bulk construction of the tables of a time point.

   The tuples of each predicate are collected, sorted with [compare_tuple] (which mirrors the
   verified comparator on [event_data option list]) and handed to the verified [table_of_list],
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

let rec compare_tuple a b = match a, b with
  | [], [] -> 0
  | [], _ -> -1
  | _, [] -> 1
  | None :: xs, None :: ys -> compare_tuple xs ys
  | None :: _, Some _ :: _ -> -1
  | Some _ :: _, None :: _ -> 1
  | Some x :: xs, Some y :: ys ->
    let c = compare_event_data x y in
    if c <> 0 then c else compare_tuple xs ys

let equal_event_data a b = match a, b with
  | EInt x, EInt y -> Z.equal x y
  | EFloat x, EFloat y -> Int64.equal (Int64.bits_of_float x) (Int64.bits_of_float y)
  | EString x, EString y -> String.equal x y
  | _ -> false

let equal_tuple a b =
  List.length a = List.length b &&
  List.for_all2 (fun x y -> match x, y with
    | None, None -> true
    | Some x, Some y -> equal_event_data x y
    | _ -> false) a b

let rec dedup_sorted = function
  | x :: (y :: _ as rest) -> if equal_tuple x y then dedup_sorted rest else x :: dedup_sorted rest
  | l -> l

type batch = (string * nat, (event_data option) list list ref) Hashtbl.t

let empty_batch () : batch = Hashtbl.create 16

let add_to_batch (b: batch) ((pname, tl) as schema) sl =
  let key = (pname, nat_of_int (List.length tl)) in
  let t = convert_tuple schema sl in
  match Hashtbl.find_opt b key with
  | Some r -> r := t :: !r
  | None -> Hashtbl.add b key (ref [t])

let flush_batch (b: batch) db =
  let db = Hashtbl.fold (fun key r db ->
    let sorted = dedup_sorted (List.stable_sort compare_tuple !r) in
    insert_table_into_db key (table_of_list sorted) db) b db in
  Hashtbl.clear b; (* keep the bucket array; [reset] would reallocate it at every time point *)
  db

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

let type_check_formula dbschema f =
  type_check (convert_schema_into_sig dbschema) f

(* Two verified kernels are available. The default keeps the Since structures as pure values
   ([minit_safe]/[mstep]); with [-heap_since] the structures of Since operators without join
   columns live on the heap as hash tables ([minit_safe_imp]/[mstep_imp], see
   thys/MFODL_Monitor_Imp). Both are exported from the same formalization and, by the
   refinement theorem, produce the same verdicts. *)

type pure_state =
  (((nat *
      (nat *
        (bool list *
          (bool list *
            ((nat * ((event_data option) list) set) queue *
              ((nat * ((event_data option) list) set) queue *
                (((event_data option) list) set *
                  (event_data wf_table *
                    ((((event_data option) list), nat) mapping *
                      (event_data wf_table *
                        (((event_data option) list), nat)
                          mapping)))))))))) *
     aggaux option),
    muaux_dq,
      (nat *
          (nat *
            (nat *
              (nat *
                (bool list *
                  (bool list *
                    ((nat *
                       (((event_data option) list) set *
                         ((event_data option) list) set))
                       queue *
                      ((nat * ((event_data option) list) set) queue *
                        ((((event_data option) list), nat) mapping *
                          (((event_data option) list) set *
                            ((((event_data option) list), nat) mapping *
                              (((event_data option) list) set *
                                ((event_data option) list) set)))))))))))),
    unit)
    mstate_ext

type heap_state =
  (nat *
    (nat *
      ((msaux_h, muaux_dq,
         (nat *
           (nat *
             (nat *
               (nat *
                 (bool list *
                   (bool list *
                     ((nat *
                        (((event_data option) list) set *
                          ((event_data option) list) set))
                        queue *
                       ((nat * ((event_data option) list) set) queue *
                         ((((event_data option) list), nat) mapping *
                           (((event_data option) list) set *
                             ((((event_data option) list), nat) mapping *
                               (((event_data option) list) set *
                                 ((event_data option) list) set)))))))))))))
         meformula *
        (nat * nat queue))))

type state =
  | Pure of pure_state
  | Heap of heap_state

let init cf = if !Misc.heap_since then Heap (minit_safe_imp cf ()) else Pure (minit_safe cf)


let set_fold f s x = match s with
  | RBT_set r -> rbt_fold f r x
  | _ -> failwith "[set_fold] unexpected set representation"

(* Verdicts are kept in the kernel's representation; [show_results] below prints them without
   converting to [Tuple.tuple] first. *)
type verdict = (event_data option) list set

let annotate vs = List.map (fun (tp, (ts, v)) -> (int_of_nat tp, integer_of_nat ts, v)) vs

let step t db = function
  | Pure st -> let (vs, st') = mstep (db, nat_of_integer t) st in (annotate vs, Pure st')
  | Heap st -> let (vs, st') = mstep_imp (db, nat_of_integer t) st () in (annotate vs, Heap st')

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
   ([string_of_int] goes through [Printf]-style formatting and allocates). *)
let add_int b n =
  if n = 0 then Buffer.add_char b '0'
  else if n = min_int then Buffer.add_string b (string_of_int n)
  else begin
    let n = if n < 0 then (Buffer.add_char b '-'; -n) else n in
    let digits = Bytes.create 20 in
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

let show_results_slow posl q tsq (table: verdict) =
  let defined t = List.filter_map (fun x -> x) t in
  let proj = if is_enum_list 0 posl then defined
    else fun t -> Misc.get_positions posl (defined t) in
  let tuples = List.rev (set_fold (fun t acc -> proj t :: acc) table []) in
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

exception Slow_path

(* MonPoly's tuple order on the kernel's tuples; an undefined column leaves the fast path. *)
let rec compare_otuple_mp t1 t2 = match t1, t2 with
  | [], [] -> 0
  | [], _ :: _ -> -1
  | _ :: _, [] -> 1
  | Some x :: xs, Some y :: ys ->
    let c = compare_event_data_mp x y in
    if c <> 0 then c else compare_otuple_mp xs ys
  | _ -> raise Slow_path

(* Fast path for the common case (no projection, not verbose, all violations wanted): the
   tuples are streamed from the tree in its order straight into the buffer, without building
   tuple lists; the order is checked against the previous tuple on the way. If the tree order
   is not MonPoly's (mixed-type columns) or a column is undefined, the general path is taken. *)
let show_results posl _i q tsq (table: verdict) =
  if !Misc.verbose || !Misc.stop_at_first_viol || posl = [] || not (is_enum_list 0 posl) then
    show_results_slow posl q tsq table
  else begin
    let b = Buffer.create 1024 in
    Buffer.add_string b (Printf.sprintf "@%s (time point %d): " (MFOTL.string_of_ts tsq) q);
    let prev = ref None in
    let ok =
      try
        set_fold (fun t () ->
            (match !prev with
             | Some p -> if compare_otuple_mp p t >= 0 then raise Slow_path; Buffer.add_char b ' '
             | None -> ());
            Buffer.add_char b '(';
            List.iteri (fun k x -> match x with
                | Some v -> if k > 0 then Buffer.add_char b ','; add_event_data b v
                | None -> raise Slow_path) t;
            Buffer.add_char b ')';
            prev := Some t) table ();
        true
      with Slow_path -> false
    in
    if not ok then show_results_slow posl q tsq table
    else begin
      if Misc.debugging Dbg_perf then Perf.show_results q tsq;
      if !prev <> None then begin
        Buffer.add_char b '\n';
        print_string (Buffer.contents b);
        flush stdout
      end;
      !prev <> None
    end
  end

let is_monitorable dbschema f =
  let s = mmonitorable_exec (convert_formula dbschema f) in
  (s, (if s then None else Some (f, "MFODL formula is not monitorable")))
