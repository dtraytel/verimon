(* Glue between the verified formula parser (src/verified_parser.ml, exported from
   thys/MFODL_Parser) and MonPoly's syntax tree (MFOTL.formula). *)

module V = Verified_parser.Verified_parser

(* Strings are lists of bytes, each a Chara of its eight bits, least significant first. *)
let chars_of_string s =
  List.init (String.length s) (fun i ->
      let c = Char.code s.[i] in
      let b k = c land (1 lsl k) <> 0 in
      V.Chara (b 0, b 1, b 2, b 3, b 4, b 5, b 6, b 7))

let char_of (V.Chara (b0, b1, b2, b3, b4, b5, b6, b7)) =
  let bit b k = if b then 1 lsl k else 0 in
  Char.chr (bit b0 0 + bit b1 1 + bit b2 2 + bit b3 3 + bit b4 4 + bit b5 5 + bit b6 6 + bit b7 7)

let str cs = String.of_seq (Seq.map char_of (List.to_seq cs))
let int i = V.integer_of_int i

let bound = function
  | V.OBnd n -> MFOTL.OBnd (int n)
  | V.CBnd n -> MFOTL.CBnd (int n)
  | V.BInf -> MFOTL.Inf

let interval (a, b) = (bound a, bound b)

(* Regular expression constants are compiled here, as by MonPoly's parser
   (Formula_parser.compile_regexp); an invalid one raises an exception. *)
let cst = function
  | V.CInt n -> Predicate.Int (int n)
  | V.CStr s -> Predicate.Str (str s)
  | V.CFloat s -> Predicate.Float (float_of_string (str s))
  | V.CRegexp s -> let p = str s in Predicate.Regexp (p, Str.regexp p)

let rec term = function
  | V.TVar v -> Predicate.Var (str v)
  | V.TCst c -> Predicate.Cst (cst c)
  | V.TF2i t -> Predicate.F2i (term t)
  | V.TI2f t -> Predicate.I2f (term t)
  | V.TI2s t -> Predicate.I2s (term t)
  | V.TS2i t -> Predicate.S2i (term t)
  | V.TF2s t -> Predicate.F2s (term t)
  | V.TS2f t -> Predicate.S2f (term t)
  | V.TDayOfMonth t -> Predicate.DayOfMonth (term t)
  | V.TMonth t -> Predicate.Month (term t)
  | V.TYear t -> Predicate.Year (term t)
  | V.TFormatDate t -> Predicate.FormatDate (term t)
  | V.TR2s t -> Predicate.R2s (term t)
  | V.TS2r t -> Predicate.S2r (term t)
  | V.TPlus (a, b) -> Predicate.Plus (term a, term b)
  | V.TMinus (a, b) -> Predicate.Minus (term a, term b)
  | V.TUMinus a -> Predicate.UMinus (term a)
  | V.TMult (a, b) -> Predicate.Mult (term a, term b)
  | V.TDiv (a, b) -> Predicate.Div (term a, term b)
  | V.TMod (a, b) -> Predicate.Mod (term a, term b)

let predicate (name, args) = Predicate.make_predicate (str name, List.map term args)

let vars = List.map str

let agg_op = function
  | V.ACnt -> MFOTL.Cnt | V.AMin -> MFOTL.Min | V.AMax -> MFOTL.Max
  | V.ASum -> MFOTL.Sum | V.AAvg -> MFOTL.Avg | V.AMed -> MFOTL.Med

let rec formula = function
  | V.FEqual (a, b) -> MFOTL.Equal (term a, term b)
  | V.FLess (a, b) -> MFOTL.Less (term a, term b)
  | V.FLessEq (a, b) -> MFOTL.LessEq (term a, term b)
  | V.FSubstring (a, b) -> MFOTL.Substring (term a, term b)
  | V.FMatches (a, b, l) -> MFOTL.Matches (term a, term b, List.map (Option.map term) l)
  | V.FPred p -> MFOTL.Pred (predicate p)
  | V.FLet (p, a, b) -> MFOTL.Let (predicate p, formula a, formula b)
  | V.FLetPast (p, a, b) -> MFOTL.LetPast (predicate p, formula a, formula b)
  | V.FFrz (p, a, b) -> MFOTL.Frz (predicate p, formula a, formula b)
  | V.FNeg a -> MFOTL.Neg (formula a)
  | V.FAnd (a, b) -> MFOTL.And (formula a, formula b)
  | V.FOr (a, b) -> MFOTL.Or (formula a, formula b)
  | V.FImplies (a, b) -> MFOTL.Implies (formula a, formula b)
  | V.FEquiv (a, b) -> MFOTL.Equiv (formula a, formula b)
  | V.FExists (vl, a) -> MFOTL.Exists (vars vl, formula a)
  | V.FForAll (vl, a) -> MFOTL.ForAll (vars vl, formula a)
  | V.FAggreg (y, op, x, g, a) ->
    MFOTL.Aggreg (Predicate.TSymb (Predicate.TAny, 0), str y, agg_op op, str x, vars g, formula a)
  | V.FPrev (i, a) -> MFOTL.Prev (interval i, formula a)
  | V.FNext (i, a) -> MFOTL.Next (interval i, formula a)
  | V.FEventually (i, a) -> MFOTL.Eventually (interval i, formula a)
  | V.FOnce (i, a) -> MFOTL.Once (interval i, formula a)
  | V.FAlways (i, a) -> MFOTL.Always (interval i, formula a)
  | V.FPastAlways (i, a) -> MFOTL.PastAlways (interval i, formula a)
  | V.FSince (i, a, b) -> MFOTL.Since (interval i, formula a, formula b)
  | V.FTrigger (i, a, b) -> MFOTL.Trigger (interval i, formula a, formula b)
  | V.FUntil (i, a, b) -> MFOTL.Until (interval i, formula a, formula b)
  | V.FRelease (i, a, b) -> MFOTL.Release (interval i, formula a, formula b)
  | V.FFrex (i, r) -> MFOTL.Frex (interval i, regex r)
  | V.FPrex (i, r) -> MFOTL.Prex (interval i, regex r)

and regex = function
  | V.RSkip n -> MFOTL.Skip (Z.to_int (V.integer_of_nat n))
  | V.RTest a -> MFOTL.Test (formula a)
  | V.RConcat (a, b) -> MFOTL.Concat (regex a, regex b)
  | V.RPlus (a, b) -> MFOTL.Plus (regex a, regex b)
  | V.RStar a -> MFOTL.Star (regex a)

let lex_string s =
  Option.map (List.map (fun (t, l) -> (t, str l))) (V.lex_chars (chars_of_string s))

let parse_string s =
  match V.parse_formula (chars_of_string s) with
  | None -> None
  | Some f -> (try Some (formula f) with Failure _ -> None)
