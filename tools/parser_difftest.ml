(* Differential testing of the verified formula parser (thys/MFODL_Parser,
   exported to src/verified_parser.ml) against MonPoly's ocamlyacc parser
   (src/formula_parser.mly).

   Usage: parser_difftest [-n N] [-seed S] [-depth D] [-v] [-lex] [-time] [FILE...]
   Each FILE is parsed as one formula. Without files, N random formulas are
   generated. For every input both parsers run; the outcomes are classified as
     same     both accept with equal syntax trees, or both reject
     differ   both accept with different syntax trees
     mp-only  only MonPoly accepts
     vp-only  only the verified parser accepts
   Anonymous variables (_1, _2, ...) are compared up to a shift of their
   numbers, since MonPoly's counter is never reset between parses.

   With -lex, random strings are lexed instead and the token streams of the
   verified lexer model (thys/MFODL_Parser/Parser/MFODL_Lexer.thy) and of
   src/formula_lexer.mll are compared.

   With -time, the inputs are not compared but timed: one line per input with
   its length in characters and tokens, the CPU time of MonPoly's parser, and
   that of the verified parser, in total and split into the lexer, the LR
   parser and the rest (post-processing and conversion to MonPoly's trees). *)

open Libmonpoly
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

(* Token class names of the verified lexer, spelled as in src/formula_parser.mly. *)
let vtok_name = function
  | Verified_parser.Verified_parser.FALSE -> "FALSE"
  | Verified_parser.Verified_parser.TRUE -> "TRUE"
  | Verified_parser.Verified_parser.LPA -> "LPA"
  | Verified_parser.Verified_parser.RPA -> "RPA"
  | Verified_parser.Verified_parser.LSB -> "LSB"
  | Verified_parser.Verified_parser.RSB -> "RSB"
  | Verified_parser.Verified_parser.COM -> "COM"
  | Verified_parser.Verified_parser.SC -> "SC"
  | Verified_parser.Verified_parser.DOT -> "DOT"
  | Verified_parser.Verified_parser.QM -> "QM"
  | Verified_parser.Verified_parser.LD -> "LD"
  | Verified_parser.Verified_parser.LESSEQ -> "LESSEQ"
  | Verified_parser.Verified_parser.EQ -> "EQ"
  | Verified_parser.Verified_parser.LESS -> "LESS"
  | Verified_parser.Verified_parser.GTR -> "GTR"
  | Verified_parser.Verified_parser.GTREQ -> "GTREQ"
  | Verified_parser.Verified_parser.STAR -> "STAR"
  | Verified_parser.Verified_parser.LARROW -> "LARROW"
  | Verified_parser.Verified_parser.SUBSTRING -> "SUBSTRING"
  | Verified_parser.Verified_parser.MATCHES -> "MATCHES"
  | Verified_parser.Verified_parser.PLUS -> "PLUS"
  | Verified_parser.Verified_parser.MINUS -> "MINUS"
  | Verified_parser.Verified_parser.SLASH -> "SLASH"
  | Verified_parser.Verified_parser.MOD -> "MOD"
  | Verified_parser.Verified_parser.F2I -> "F2I"
  | Verified_parser.Verified_parser.I2F -> "I2F"
  | Verified_parser.Verified_parser.DAY_OF_MONTH -> "DAY_OF_MONTH"
  | Verified_parser.Verified_parser.MONTH -> "MONTH"
  | Verified_parser.Verified_parser.YEAR -> "YEAR"
  | Verified_parser.Verified_parser.FORMAT_DATE -> "FORMAT_DATE"
  | Verified_parser.Verified_parser.R2S -> "R2S"
  | Verified_parser.Verified_parser.S2R -> "S2R"
  | Verified_parser.Verified_parser.I2S -> "I2S"
  | Verified_parser.Verified_parser.S2I -> "S2I"
  | Verified_parser.Verified_parser.F2S -> "F2S"
  | Verified_parser.Verified_parser.S2F -> "S2F"
  | Verified_parser.Verified_parser.NAME -> "STR"
  | Verified_parser.Verified_parser.STR_CST -> "STR_CST"
  | Verified_parser.Verified_parser.REGEXP_CST -> "REGEXP_CST"
  | Verified_parser.Verified_parser.INTEGER -> "INT"
  | Verified_parser.Verified_parser.RAT -> "RAT"
  | Verified_parser.Verified_parser.TU -> "TU"
  | Verified_parser.Verified_parser.LET -> "LET"
  | Verified_parser.Verified_parser.LETPAST -> "LETPAST"
  | Verified_parser.Verified_parser.FRZ -> "FRZ"
  | Verified_parser.Verified_parser.IN -> "IN"
  | Verified_parser.Verified_parser.NOT -> "NOT"
  | Verified_parser.Verified_parser.AND -> "AND"
  | Verified_parser.Verified_parser.OR -> "OR"
  | Verified_parser.Verified_parser.IMPL -> "IMPL"
  | Verified_parser.Verified_parser.EQUIV -> "EQUIV"
  | Verified_parser.Verified_parser.EXISTS -> "EX"
  | Verified_parser.Verified_parser.FORALL -> "FA"
  | Verified_parser.Verified_parser.PREV -> "PREV"
  | Verified_parser.Verified_parser.NEXT -> "NEXT"
  | Verified_parser.Verified_parser.EVENTUALLY -> "EVENTUALLY"
  | Verified_parser.Verified_parser.ONCE -> "ONCE"
  | Verified_parser.Verified_parser.ALWAYS -> "ALWAYS"
  | Verified_parser.Verified_parser.PAST_ALWAYS -> "PAST_ALWAYS"
  | Verified_parser.Verified_parser.SINCE -> "SINCE"
  | Verified_parser.Verified_parser.TRIGGER -> "TRIGGER"
  | Verified_parser.Verified_parser.UNTIL -> "UNTIL"
  | Verified_parser.Verified_parser.RELEASE -> "RELEASE"
  | Verified_parser.Verified_parser.BAR -> "BAR"
  | Verified_parser.Verified_parser.FREX -> "FREX"
  | Verified_parser.Verified_parser.PREX -> "PREX"
  | Verified_parser.Verified_parser.CNT -> "CNT"
  | Verified_parser.Verified_parser.MIN_KW -> "MIN"
  | Verified_parser.Verified_parser.MAX_KW -> "MAX"
  | Verified_parser.Verified_parser.SUM_KW -> "SUM"
  | Verified_parser.Verified_parser.AVG -> "AVG"
  | Verified_parser.Verified_parser.MED -> "MED"

(* MonPoly's token stream: names and payloads. *)
let mp_token_name = function
  | Formula_parser.FALSE -> "FALSE" | Formula_parser.TRUE -> "TRUE" | Formula_parser.LPA -> "LPA"
  | Formula_parser.RPA -> "RPA" | Formula_parser.LSB -> "LSB" | Formula_parser.RSB -> "RSB"
  | Formula_parser.COM -> "COM" | Formula_parser.SC -> "SC" | Formula_parser.DOT -> "DOT"
  | Formula_parser.QM -> "QM" | Formula_parser.LD -> "LD" | Formula_parser.LESSEQ -> "LESSEQ"
  | Formula_parser.EQ -> "EQ" | Formula_parser.LESS -> "LESS" | Formula_parser.GTR -> "GTR"
  | Formula_parser.GTREQ -> "GTREQ" | Formula_parser.STAR -> "STAR" | Formula_parser.LARROW -> "LARROW"
  | Formula_parser.SUBSTRING -> "SUBSTRING" | Formula_parser.MATCHES -> "MATCHES"
  | Formula_parser.PLUS -> "PLUS" | Formula_parser.MINUS -> "MINUS" | Formula_parser.SLASH -> "SLASH"
  | Formula_parser.MOD -> "MOD" | Formula_parser.F2I -> "F2I" | Formula_parser.I2F -> "I2F"
  | Formula_parser.DAY_OF_MONTH -> "DAY_OF_MONTH" | Formula_parser.MONTH -> "MONTH"
  | Formula_parser.YEAR -> "YEAR" | Formula_parser.FORMAT_DATE -> "FORMAT_DATE"
  | Formula_parser.R2S -> "R2S" | Formula_parser.S2R -> "S2R" | Formula_parser.I2S -> "I2S"
  | Formula_parser.S2I -> "S2I" | Formula_parser.F2S -> "F2S" | Formula_parser.S2F -> "S2F"
  | Formula_parser.STR _ -> "STR" | Formula_parser.STR_CST _ -> "STR_CST"
  | Formula_parser.REGEXP_CST _ -> "REGEXP_CST" | Formula_parser.INT _ -> "INT"
  | Formula_parser.RAT _ -> "RAT" | Formula_parser.TU _ -> "TU"
  | Formula_parser.LET -> "LET" | Formula_parser.LETPAST -> "LETPAST" | Formula_parser.FRZ -> "FRZ"
  | Formula_parser.IN -> "IN" | Formula_parser.NOT -> "NOT" | Formula_parser.AND -> "AND"
  | Formula_parser.OR -> "OR" | Formula_parser.IMPL -> "IMPL" | Formula_parser.EQUIV -> "EQUIV"
  | Formula_parser.EX -> "EX" | Formula_parser.FA -> "FA" | Formula_parser.PREV -> "PREV"
  | Formula_parser.NEXT -> "NEXT" | Formula_parser.EVENTUALLY -> "EVENTUALLY"
  | Formula_parser.ONCE -> "ONCE" | Formula_parser.ALWAYS -> "ALWAYS"
  | Formula_parser.PAST_ALWAYS -> "PAST_ALWAYS" | Formula_parser.SINCE -> "SINCE"
  | Formula_parser.TRIGGER -> "TRIGGER" | Formula_parser.UNTIL -> "UNTIL"
  | Formula_parser.RELEASE -> "RELEASE" | Formula_parser.BAR -> "BAR" | Formula_parser.FREX -> "FREX"
  | Formula_parser.PREX -> "PREX" | Formula_parser.CNT -> "CNT" | Formula_parser.MIN -> "MIN"
  | Formula_parser.MAX -> "MAX" | Formula_parser.SUM -> "SUM" | Formula_parser.AVG -> "AVG"
  | Formula_parser.MED -> "MED" | Formula_parser.END -> "END" | Formula_parser.EOF -> "EOF"

exception Bad_unit

(* MonPoly's tokens up to EOF; a time unit other than d, h, m, s fails in
   every context, so it counts as a lexing failure here. *)
let lex_monpoly s =
  let lb = Lexing.from_string s in
  let rec go acc =
    match Formula_lexer.token lb with
    | Formula_parser.EOF -> List.rev acc
    | Formula_parser.TU (_, c) when not (String.contains "dhms" c) -> raise Bad_unit
    | t -> go (t :: acc)
  in
  try Some (go []) with _ -> None

(* A verified token (class, lexeme) against a MonPoly token. *)
let same_token (vt, lx) t =
  vtok_name vt = mp_token_name t
  && (match t with
      | Formula_parser.STR s | Formula_parser.STR_CST s | Formula_parser.REGEXP_CST s -> s = lx
      | Formula_parser.INT z -> Z.equal z (Z.of_string lx)
      | Formula_parser.RAT r -> r = float_of_string lx
      | Formula_parser.TU (n, c) ->
        let k = String.length lx in
        k >= 2 && lx.[k - 1] = c && string_of_int n = String.sub lx 0 (k - 1)
      | _ -> true)

let lex_verified s = Verified_parser_adapter.lex_string s

let fragments =
  [| "P"; "x"; "_"; "_x"; "-"; "-5"; "5"; "12"; "1.5"; "-2."; "3s"; "5x"; "7sec"; "\"a\\\"b\""; "\"ab\"";
     "r\"a.*\""; "r\"a\"x"; "("; ")"; "(*"; "*)"; "#"; "\n"; " "; " "; " "; "\t"; "|>"; "<|"; "|"; "<-";
     "<="; "<"; ">="; ">"; "="; "AND"; "ANDX"; "PREVIOUS"; "PREV"; "MATCHES"; "MATCHF"; "MATCHP";
     "\xe2\x96\xb7"; "\xe2\x97\x81"; "FORWARD"; ","; ";"; "?"; "."; "*"; "+"; "/"; "MOD"; "f2i"; "x-1";
     "a:b"; "'"; "\""; "@"; "["; "]"; "EXISTS"; "SUM"; "SUMS"; "CNT"; "TRUE"; "IN"; "INT" |]

let random_lexeme_string () =
  String.concat "" (List.init (1 + Random.int 12) (fun _ -> fragments.(Random.int (Array.length fragments))))

let lex_test n =
  let same = ref 0 and diff = ref 0 in
  for i = 1 to n do
    let s = random_lexeme_string () in
    let ok = match lex_monpoly s, lex_verified s with
      | None, None -> true
      | Some a, Some b -> List.length a = List.length b && List.for_all2 (fun v m -> same_token v m) b a
      | _ -> false
    in
    if ok then incr same
    else begin
      incr diff;
      Printf.printf "LEX-DIFFER [%d]: %S\n" i s
    end
  done;
  Printf.printf "lexed: %d  same: %d  differ: %d\n" n !same !diff;
  if !diff > 0 then exit 1

(* ---------------------------------------------------------------------- *)

let verbose = ref false
let count = ref 1000
let seed = ref 42
let depth = ref 4
let files = ref []
let lex_mode = ref false
let time_mode = ref false

let read_file fn =
  let ic = open_in_bin fn in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic; s

(* CPU seconds per call of f, repeated for at least min_s seconds *)
let cpu_time ?(min_s = 0.2) f =
  let t0 = Sys.time () in
  let rec go n =
    ignore (Sys.opaque_identity (f ()));
    let t = Sys.time () -. t0 in
    if t < min_s then go (n + 1) else t /. float_of_int n
  in
  go 1

let time_inputs inputs =
  let module V = Verified_parser.Verified_parser in
  Printf.printf "%-22s %5s %4s %10s %10s %10s %10s %10s\n"
    "name" "chars" "toks" "monpoly_ms" "verif_ms" "lex_ms" "lr_ms" "rest_ms";
  let tot_mp = ref 0.0 and tot_vp = ref 0.0 in
  List.iter (fun (name, s) ->
      let cs = Verified_parser_adapter.chars_of_string s in
      let toks = match V.lex cs with Some w -> List.length w | None -> 0 in
      let mp = cpu_time (fun () -> parse_monpoly s) in
      let vp = cpu_time (fun () -> parse_verified s) in
      let lx = cpu_time (fun () -> V.lex cs) in
      let lr =
        match V.lex cs with
        | Some w -> cpu_time (fun () -> V.mfodl_parse w)
        | None -> 0.0
      in
      tot_mp := !tot_mp +. mp; tot_vp := !tot_vp +. vp;
      Printf.printf "%-22s %5d %4d %10.3f %10.1f %10.2f %10.1f %10.2f\n%!"
        (Filename.remove_extension (Filename.basename name)) (String.length (String.trim s)) toks
        (1000. *. mp) (1000. *. vp) (1000. *. lx) (1000. *. lr)
        (1000. *. (vp -. lx -. lr)))
    inputs;
  Printf.printf "total: monpoly %.3f s, verified %.1f s (%d inputs)\n"
    !tot_mp !tot_vp (List.length inputs)

let () =
  Arg.parse
    [ ("-n", Arg.Set_int count, "number of random formulas (default 1000)");
      ("-seed", Arg.Set_int seed, "random seed (default 42)");
      ("-depth", Arg.Set_int depth, "maximal nesting depth (default 4)");
      ("-v", Arg.Set verbose, "print every input");
      ("-lex", Arg.Set lex_mode, "compare the lexers on N random strings");
      ("-time", Arg.Set time_mode, "time the parsers instead of comparing them") ]
    (fun f -> files := f :: !files)
    "parser_difftest [-n N] [-seed S] [-depth D] [-v] [-lex] [-time] [FILE...]";
  Random.init !seed;
  if !lex_mode then (lex_test !count; exit 0);
  let inputs =
    if !files <> [] then List.rev_map (fun fn -> (fn, read_file fn)) !files
    else List.init !count (fun i -> (string_of_int i, formula (1 + Random.int !depth)))
  in
  if !time_mode then (time_inputs inputs; exit 0);
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
