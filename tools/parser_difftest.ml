(* Differential testing of the verified formula parser (thys/MFODL_Parser,
   exported to src/verified_parser.ml) against MonPoly's ocamlyacc parser
   (src/formula_parser.mly).

   Usage: parser_difftest [-n N] [-seed S] [-depth D] [-v] [FILE...]
   Each FILE is parsed as one formula. Without files, N random formulas are
   generated. For every input both parsers run; the outcomes are classified as
     same     both accept with equal syntax trees, or both reject
     differ   both accept with different syntax trees
     mp-only  only MonPoly accepts
     vp-only  only the verified parser accepts
   Anonymous variables (_1, _2, ...) are compared up to renaming, since
   MonPoly's counter is never reset between parses. *)

open MFOTL

let parse_monpoly s =
  try Some (Formula_parser.formula Formula_lexer.token (Lexing.from_string s))
  with _ -> None

let parse_verified s =
  try Verified_parser_adapter.parse_string s with _ -> None

(* Anonymous variables are named _1, _2, ... from a counter that MonPoly never
   resets, so its numbering of the n-th parse starts where the previous one
   ended. Shift the numbers so that the smallest is 1; the numbering order
   within a formula must then agree exactly. *)
let anon_index v =
  let n = String.length v in
  if n > 1 && v.[0] = '_'
     && String.for_all (fun c -> c >= '0' && c <= '9') (String.sub v 1 (n - 1))
  then Some (int_of_string (String.sub v 1 (n - 1))) else None

let map_formula_vars ren f0 =
  let rec t = function
    | Predicate.Var v -> Predicate.Var (ren v)
    | Predicate.Cst (Predicate.Regexp (p, _)) -> Predicate.Cst (Predicate.Str ("r:" ^ p))
    | Predicate.Cst c -> Predicate.Cst c
    | Predicate.F2i a -> Predicate.F2i (t a) | Predicate.I2f a -> Predicate.I2f (t a)
    | Predicate.I2s a -> Predicate.I2s (t a) | Predicate.S2i a -> Predicate.S2i (t a)
    | Predicate.F2s a -> Predicate.F2s (t a) | Predicate.S2f a -> Predicate.S2f (t a)
    | Predicate.DayOfMonth a -> Predicate.DayOfMonth (t a) | Predicate.Month a -> Predicate.Month (t a)
    | Predicate.Year a -> Predicate.Year (t a) | Predicate.FormatDate a -> Predicate.FormatDate (t a)
    | Predicate.R2s a -> Predicate.R2s (t a) | Predicate.S2r a -> Predicate.S2r (t a)
    | Predicate.Plus (a, b) -> let a = t a in Predicate.Plus (a, t b)
    | Predicate.Minus (a, b) -> let a = t a in Predicate.Minus (a, t b)
    | Predicate.UMinus a -> Predicate.UMinus (t a)
    | Predicate.Mult (a, b) -> let a = t a in Predicate.Mult (a, t b)
    | Predicate.Div (a, b) -> let a = t a in Predicate.Div (a, t b)
    | Predicate.Mod (a, b) -> let a = t a in Predicate.Mod (a, t b)
  in
  let p (n, a, args) = (n, a, List.map t args) in
  let vl = List.map ren in
  let rec f = function
    | Equal (a, b) -> let a = t a in Equal (a, t b)
    | Less (a, b) -> let a = t a in Less (a, t b)
    | LessEq (a, b) -> let a = t a in LessEq (a, t b)
    | Substring (a, b) -> let a = t a in Substring (a, t b)
    | Matches (a, b, l) -> let a = t a in let b = t b in Matches (a, b, List.map (Option.map t) l)
    | Pred q -> Pred (p q)
    | Let (q, a, b) -> let q = p q in let a = f a in Let (q, a, f b)
    | LetPast (q, a, b) -> let q = p q in let a = f a in LetPast (q, a, f b)
    | Frz (q, a, b) -> let q = p q in let a = f a in Frz (q, a, f b)
    | Neg a -> Neg (f a)
    | And (a, b) -> let a = f a in And (a, f b)
    | Or (a, b) -> let a = f a in Or (a, f b)
    | Implies (a, b) -> let a = f a in Implies (a, f b)
    | Equiv (a, b) -> let a = f a in Equiv (a, f b)
    | Exists (l, a) -> (match a with
        | Pred _ -> let a = f a in Exists (vl l, a)   (* add_ex: the predicate comes first *)
        | _ -> let l = vl l in Exists (l, f a))
    | ForAll (l, a) -> let l = vl l in ForAll (l, f a)
    | Aggreg (ty, y, op, x, g, a) -> Aggreg (ty, y, op, x, g, f a)
    | Prev (i, a) -> Prev (i, f a) | Next (i, a) -> Next (i, f a)
    | Eventually (i, a) -> Eventually (i, f a) | Once (i, a) -> Once (i, f a)
    | Always (i, a) -> Always (i, f a) | PastAlways (i, a) -> PastAlways (i, f a)
    | Since (i, a, b) -> let a = f a in Since (i, a, f b)
    | Trigger (i, a, b) -> let a = f a in Trigger (i, a, f b)
    | Until (i, a, b) -> let a = f a in Until (i, a, f b)
    | Release (i, a, b) -> let a = f a in Release (i, a, f b)
    | Frex (i, r) -> Frex (i, re r)
    | Prex (i, r) -> Prex (i, re r)
  and re = function
    | Skip n -> Skip n
    | Test a -> Test (f a)
    | Concat (a, b) -> let a = re a in Concat (a, re b)
    | Plus (a, b) -> let a = re a in Plus (a, re b)
    | Star a -> Star (re a)
  in
  f f0

let canonical f =
  let m = ref max_int in
  ignore (map_formula_vars (fun v -> (match anon_index v with Some k -> m := min !m k | None -> ()); v) f);
  let shift = if !m = max_int then 0 else !m - 1 in
  map_formula_vars (fun v -> match anon_index v with
      | Some k -> "_" ^ string_of_int (k - shift) | None -> v) f

(* ---------------------------------------------------------------------- *)
(* Random formulas, written the way people write them: with few parentheses,
   optional intervals, synonyms of keywords, and some unusual corners of the
   concrete syntax (trailing commas, anonymous arguments, comments). *)

let pick l = List.nth l (Random.int (List.length l))
let chance p = Random.float 1.0 < p

let var () = pick ["x"; "y"; "z"; "u"; "v1"; "w_2"]
let pred_name () = pick ["P"; "Q"; "R"; "A"; "p0"]

let units () =
  if chance 0.5 then string_of_int (Random.int 20)
  else string_of_int (Random.int 10) ^ pick ["s"; "m"; "h"; "d"]

let interval () =
  let l = if chance 0.5 then "[" else "(" in
  let r = if chance 0.2 then "*" ^ pick [")"; "]"] else units () ^ pick [")"; "]"] in
  l ^ units () ^ "," ^ r

let opt_interval () = if chance 0.6 then " " ^ interval () ^ " " else " "

let rec term d =
  if d <= 0 || chance 0.4 then
    pick [ var (); var (); string_of_int (Random.int 100 - 30); "3.5"; "\"abc\"";
           "\"a b\""; "r\"a.*\"" ]
  else
    match Random.int 9 with
    | 0 -> term (d - 1) ^ " + " ^ term (d - 1)
    | 1 -> term (d - 1) ^ " - " ^ term (d - 1)
    | 2 -> term (d - 1) ^ " * " ^ term (d - 1)
    | 3 -> term (d - 1) ^ " / " ^ term (d - 1)
    | 4 -> term (d - 1) ^ " MOD " ^ term (d - 1)
    | 5 -> "- " ^ term (d - 1)
    | 6 -> "(" ^ term (d - 1) ^ ")"
    | 7 -> pick ["f2i"; "i2f"; "DAY_OF_MONTH"; "MONTH"; "YEAR"; "FORMAT_DATE";
                 "r2s"; "s2r"; "i2s"; "s2i"; "f2s"; "s2f"] ^ "(" ^ term (d - 1) ^ ")"
    | _ -> term (d - 1)

let pred d =
  let arg () = if chance 0.15 then "_" else term (d - 1) in
  let n = Random.int 4 in
  let args = List.init n (fun _ -> arg ()) in
  pred_name () ^ "(" ^ String.concat (pick [","; ", "]) args
  ^ (if n > 0 && chance 0.05 then "," else "") ^ ")"

let atom d =
  match Random.int 12 with
  | 0 -> pick ["TRUE"; "FALSE"]
  | 1 | 2 | 3 | 4 -> pred d
  | 5 -> term d ^ pick [" = "; " < "; " <= "; " > "; " >= "] ^ term d
  | 6 -> term d ^ " SUBSTRING " ^ term d
  | 7 ->
    term d ^ " MATCHES " ^ term d
    ^ (if chance 0.5 then
         " (" ^ String.concat ", " (List.init (Random.int 3)
                                      (fun _ -> if chance 0.3 then "_" else term (d - 1))) ^ ")"
       else "")
  | _ -> pred d

let uop () = pick ["PREV"; "PREVIOUS"; "NEXT"; "EVENTUALLY"; "SOMETIMES"; "ONCE";
                   "ALWAYS"; "PAST_ALWAYS"; "HISTORICALLY"]
let bop () = pick ["AND"; "AND"; "OR"; "OR"; "IMPLIES"; "EQUIV";
                   "SINCE"; "UNTIL"; "TRIGGER"; "RELEASE"]

let rec formula d =
  let f =
    if d <= 0 then atom 1
    else match Random.int 20 with
      | 0 | 1 | 2 -> atom 2
      | 3 -> "NOT " ^ formula (d - 1)
      | 4 | 5 | 6 | 7 | 8 ->
        let o = bop () in
        let i = match o with
          | "SINCE" | "UNTIL" | "TRIGGER" | "RELEASE" -> opt_interval ()
          | _ -> " " in
        formula (d - 1) ^ " " ^ o ^ i ^ formula (d - 1)
      | 9 | 10 -> uop () ^ opt_interval () ^ formula (d - 1)
      | 11 ->
        pick ["EXISTS "; "FORALL "] ^ String.concat ", " (List.init (1 + Random.int 2) (fun _ -> var ()))
        ^ ". " ^ formula (d - 1)
      | 12 ->
        pick ["LET "; "LETPAST "; "FRZ "] ^ pred_name () ^ "(" ^ String.concat "," (List.init (Random.int 3) (fun _ -> var ()))
        ^ ") = " ^ formula (d - 1) ^ " IN " ^ formula (d - 1)
      | 13 ->
        var () ^ " <- " ^ pick ["CNT"; "MIN"; "MAX"; "SUM"; "AVG"; "MED"] ^ " " ^ var ()
        ^ (if chance 0.5 then "; " ^ String.concat ", " (List.init (1 + Random.int 2) (fun _ -> var ())) else "")
        ^ " " ^ formula (d - 1)
      | 14 | 15 ->
        pick ["MATCHF"; "MATCHP"; "|>"; "<|"; "FORWARD"; "BACKWARD"; "\xe2\x96\xb7"; "\xe2\x97\x81"]
        ^ opt_interval () ^ regex (d - 1)
      | _ -> "(" ^ formula (d - 1) ^ ")"
  in
  if chance 0.1 then "(" ^ f ^ ")" else f

and regex d =
  let ratom d =
    match Random.int 8 with
    | 0 -> "."
    | 1 | 2 -> formula (d - 1) ^ "?"
    | 3 | 4 -> atom 1
    | 5 -> "(" ^ regex (d - 1) ^ ")"
    | 6 -> "(" ^ formula (d - 1) ^ ")"
    | _ -> "(" ^ regex (d - 1) ^ ")*"
  in
  if d <= 0 then pick ["."; pred 1 ^ "?"; pred 1]
  else match Random.int 4 with
    | 0 -> ratom d ^ " " ^ regex (d - 1)
    | 1 -> ratom d ^ " + " ^ regex (d - 1)
    | 2 -> ratom d ^ "*"
    | _ -> ratom d

(* ---------------------------------------------------------------------- *)

let verbose = ref false
let count = ref 1000
let seed = ref 42
let depth = ref 4
let files = ref []

let read_file fn =
  let ic = open_in_bin fn in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic; s

let () =
  Arg.parse
    [ ("-n", Arg.Set_int count, "number of random formulas (default 1000)");
      ("-seed", Arg.Set_int seed, "random seed (default 42)");
      ("-depth", Arg.Set_int depth, "maximal nesting depth (default 4)");
      ("-v", Arg.Set verbose, "print every input") ]
    (fun f -> files := f :: !files)
    "parser_difftest [-n N] [-seed S] [-depth D] [-v] [FILE...]";
  Random.init !seed;
  let inputs =
    if !files <> [] then List.rev_map (fun fn -> (fn, read_file fn)) !files
    else List.init !count (fun i -> (string_of_int i, formula (1 + Random.int !depth)))
  in
  let same = ref 0 and differ = ref 0 and mp_only = ref 0 and vp_only = ref 0
  and both_ok = ref 0 in
  List.iter (fun (name, s) ->
      let mp = parse_monpoly s and vp = parse_verified s in
      let report kind =
        Printf.printf "%s [%s]: %s\n" kind name (String.trim s);
        (match mp with Some f -> Printf.printf "  monpoly:  %s\n" (MFOTL.string_of_formula "" f) | None -> ());
        (match vp with Some f -> Printf.printf "  verified: %s\n" (MFOTL.string_of_formula "" f) | None -> ())
      in
      match mp, vp with
      | None, None -> incr same; if !verbose then report "reject"
      | Some f, Some g when canonical f = canonical g ->
        incr same; incr both_ok; if !verbose then report "accept"
      | Some _, Some _ -> incr differ; report "DIFFER"
      | Some _, None -> incr mp_only; report "MP-ONLY"
      | None, Some _ -> incr vp_only; report "VP-ONLY")
    inputs;
  Printf.printf "inputs: %d  same: %d (both accept: %d)  differ: %d  mp-only: %d  vp-only: %d\n"
    (List.length inputs) !same !both_ok !differ !mp_only !vp_only;
  if !differ > 0 then exit 1
