(* Differential testing of the verified log parser (Verified_log_parser, generated from session
   Log_Parser) against MonPoly's hand-written one (Log_parser).

   Both parsers drive a consumer that records its calls.  The traces are compared up to the first
   parse error: after an error the two parsers recover differently (the verified one resumes at
   the '@', ';' or '>' that caused the error, MonPoly's skips it), and MonPoly's passes on the
   events of a time point before it has read all of it, so that an erroneous time point leaves a
   begin_tp without end_tp; such time points are removed before comparing.

   Usage: log_parser_diff [-sig FILE] LOG...     compares the parsers on the logs
          log_parser_diff -fuzz N [-seed S]       compares them on N random logs
   The verified parser is run with chunks of 4096, 1, 2, 3, and 7 bytes (4096, 7, and 1000 for
   logs of more than 64 KB), which must all give the same trace. *)

open Libmonpoly

type event =
  | Tp of string * (string * string list) list
  | Cmd of string * Helper.commandParameter option
  | Err of int * string
  | End

let string_of_params = function
  | None -> "-"
  | Some (Helper.Arguments l) -> "[" ^ String.concat "; " l ^ "]"
  | Some (Helper.SplitParameters _) -> "split parameters"
  | Some (Helper.SplitSave (h, sh, se)) ->
      let ints a = "(" ^ String.concat "," (List.map string_of_int (Array.to_list a)) ^ ")" in
      let arr f a = "{" ^ String.concat "," (List.map f (Array.to_list a)) ^ "}" in
      "{" ^ arr (fun (i, t) -> "(" ^ string_of_int i ^ ",(" ^ String.concat "," t ^ "))") h ^ ","
      ^ arr ints sh ^ "," ^ arr ints se ^ "}"

let string_of_event = function
  | Tp (ts, evs) ->
      "@" ^ ts ^ " " ^ String.concat " " (List.map (fun (p, fs) ->
        p ^ "(" ^ String.concat "," (List.map String.escaped fs) ^ ")") evs)
  | Cmd (c, p) -> "> " ^ c ^ " " ^ string_of_params p ^ " <"
  | Err (off, msg) -> Printf.sprintf "error at %d: %s" off msg
  | End -> "end"

exception Protocol of string

(* The recording consumer.  A time point is recorded when it ends; a tuple with the name and the
   arity of the schema it is given; an error with its offset, and separately with its line and
   column. *)
module Rec = struct
  type t = {
    mutable events: event list;
    mutable cur: (string * (string * string list) list) option;
    mutable positions: (int * int * int) list;
    stats: Log_parser.Stats.t;
  }
  let create () = { events = []; cur = None; positions = []; stats = Log_parser.Stats.init () }
  let begin_tp c ts = c.cur <- Some (MFOTL.string_of_ts ts, [])
  let tuple c (p, tl) fs = match c.cur with
    | Some (ts, evs) -> c.cur <- Some (ts, (p ^ "/" ^ string_of_int (List.length tl), fs) :: evs)
    | None -> raise (Protocol "tuple outside of a time point")
  let end_tp c = match c.cur with
    | Some (ts, evs) -> c.events <- Tp (ts, List.rev evs) :: c.events; c.cur <- None
    | None -> raise (Protocol "end_tp outside of a time point")
  let command c name params = c.events <- Cmd (name, params) :: c.events
  let end_log c = c.events <- End :: c.events
  let parse_error c pos msg =
    c.cur <- None;
    c.events <- Err (pos.Lexing.pos_cnum, msg) :: c.events;
    c.positions <- Lexing.(pos.pos_cnum, pos.pos_lnum, pos.pos_cnum - pos.pos_bol + 1) :: c.positions
  let stats c = c.stats
end

module Old = Log_parser.Make (Rec)
module New = Verified_log_parser.Make (Rec)

(* MonPoly's parser skips the token after the '<' that ends a command with at most one argument
   or with slicing parameters (with two arguments, it does not read the '<').  So that the
   parsers can be compared beyond commands, MonPoly's parser reads the log with a dummy token
   inserted after each such '<', and its offsets are mapped back.  The insertions are found with
   MonPoly's lexer. *)
let dummy = " _ "

let insertions log =
  let lb = Lexing.from_string log in
  let ins = ref [] in
  let tok () = try Log_lexer.token lb with _ -> Log_lexer.EOF in
  let rec top () = match tok () with
    | Log_lexer.EOF -> ()
    | Log_lexer.CMD -> cmd ()
    | _ -> top ()
  and cmd () = match tok () with
    | Log_lexer.STR _ -> args 0 false
    | Log_lexer.CMD -> cmd ()
    | Log_lexer.EOF -> ()
    | _ -> top ()
  and args n split = match tok () with
    | Log_lexer.EOC ->
        if n <= 1 || split then ins := lb.Lexing.lex_curr_p.Lexing.pos_cnum :: !ins;
        top ()
    | Log_lexer.STR _ when not split -> args (n + 1) split
    | Log_lexer.LCB when n = 0 -> args 0 true
    | Log_lexer.CMD -> cmd ()
    | Log_lexer.AT | Log_lexer.SEP | Log_lexer.EOF | Log_lexer.ERR -> top ()
    | _ when split -> args n split
    | _ -> top () in
  top ();
  List.rev !ins

let with_dummies log ins =
  let b = Buffer.create (String.length log + String.length dummy * List.length ins) in
  let last = List.fold_left (fun p q ->
    Buffer.add_string b (String.sub log p (q - p)); Buffer.add_string b dummy; q) 0 ins in
  Buffer.add_string b (String.sub log last (String.length log - last));
  Buffer.contents b

(* An offset in the log with dummies, in the log. *)
let map_back ins x =
  let d = String.length dummy in
  let rec go k shift = function
    | q :: r when q + k * d + d <= x -> go (k + 1) (shift + d) r
    | _ -> x - shift in
  go 0 0 ins

(* MonPoly's parser lets the exceptions of the conversion of timestamps escape; they are recorded
   as errors at the timestamp. *)
let run_old schema log =
  let ins = insertions log in
  let c = Rec.create () in
  let lb = Lexing.from_string (with_dummies log ins) in
  (try ignore (Old.parse schema lb c)
   with Invalid_argument m | Failure m ->
     c.events <- Err (lb.Lexing.lex_start_p.Lexing.pos_cnum, "exception: " ^ m) :: c.events);
  List.rev_map (function Err (x, m) -> Err (map_back ins x, m) | e -> e) c.events

(* The line and column of an offset, counting "\n", "\r" and "\r\n" as one line break each. *)
let line_col log off =
  let line = ref 1 and bol = ref 0 in
  for i = 0 to min off (String.length log) - 1 do
    match log.[i] with
    | '\n' -> if not (i > 0 && log.[i - 1] = '\r') then incr line; bol := i + 1
    | '\r' -> incr line; bol := i + 1
    | _ -> ()
  done;
  (!line, off - !bol + 1)

exception Wrong_position of int * (int * int) * (int * int)

(* The trace of the verified parser; the positions of its errors must be those of their offsets. *)
let run_new schema log =
  let c = Rec.create () in
  ignore (New.parse_string schema log c);
  List.iter (fun (off, l, col) ->
    let lc = line_col log off in
    if lc <> (l, col) then raise (Wrong_position (off, (l, col), lc))) c.positions;
  List.rev c.events

(* The traces up to and including the first error. *)
let rec upto_error = function
  | [] -> []
  | (Err _ as e) :: _ -> [e]
  | e :: r -> e :: upto_error r

let starts_with p s = String.length s >= String.length p && String.sub s 0 (String.length p) = p
let ends_with p s =
  String.length s >= String.length p && String.sub s (String.length s - String.length p) (String.length p) = p

(* Errors that the grammar leaves to the consumer are reported by MonPoly's parser at the token
   and by the verified one at the end of the entry (and possibly after a syntax error later in
   the same entry); an unrecognized character is reported with the character; a quoted string
   that the input ends in is an unrecognized '"' for MonPoly's lexer, after the string "r" for
   an r-quoted string (on which MonPoly's parser may fail first). *)
let semantic msg = starts_with "Cannot convert " msg || starts_with "Predicate " msg

let unrecognized msg =
  let u = "<unrecognized>" in
  let rec find i =
    if i + String.length u > String.length msg then None
    else if String.sub msg i (String.length u) = u then Some (String.sub msg 0 (i + String.length u))
    else find (i + 1) in
  find 0

(* Whether offset [off] lies within a command, after its '>' and before its '<', by the tokens
   of MonPoly's lexer (which are the verified lexer's, see Log_Grammar.thy).  MonPoly's parser
   reads the parameters of a command while it reads the command; the verified parser reads a
   command's tokens and passes them to the reader of the parameters
   (Verified_log_parser.command_params), which reports its errors at the command's '>'.  So in a
   command, the two may report an error at different offsets and with different messages. *)
let in_command log off =
  let lb = Lexing.from_string log in
  let rec go inside =
    match Log_lexer.token lb with
    | exception _ -> inside
    | t when lb.Lexing.lex_start_p.Lexing.pos_cnum >= off || t = Log_lexer.EOF -> inside
    | Log_lexer.CMD -> go true
    | Log_lexer.EOC -> go false
    | _ -> go inside in
  go false

(* Whether one of the last two commands that begin at or before offset [off] (an error in a
   command, or at the '>' of the next one) has two arguments that are not followed by its '<',
   which MonPoly's parser does not require. *)
let two_args_open log off =
  let lb = Lexing.from_string log in
  let rec cmds acc = match (try Log_lexer.token lb with _ -> Log_lexer.EOF) with
    | Log_lexer.EOF -> acc
    | Log_lexer.CMD when lb.Lexing.lex_start_p.Lexing.pos_cnum <= off ->
        cmds (lb.Lexing.lex_start_p.Lexing.pos_cnum :: acc)
    | _ -> cmds acc in
  let open_at p =
    let lb = Lexing.from_string (String.sub log p (String.length log - p)) in
    let tok () = try Log_lexer.token lb with _ -> Log_lexer.EOF in
    let gt = tok () in
    let name = tok () in
    let a = tok () in
    let b = tok () in
    let t = tok () in
    match gt, name, a, b with
    | Log_lexer.CMD, Log_lexer.STR _, Log_lexer.STR _, Log_lexer.STR _ -> t <> Log_lexer.EOC
    | _ -> false in
  match cmds [] with
  | p :: q :: _ -> open_at p || open_at q
  | [p] -> open_at p
  | [] -> false

type verdict = Same | Tolerated of string | Differ

(* MonPoly's parser keeps at most two arguments of a command, in reverse order, and does not
   require the '<' after them.  (The token it skips after other commands is neutralized by
   run_old.) *)
let compare_traces log o n =
  let at_cmd off = 0 <= off && off < String.length log && log.[off] = '>' in
  let o = upto_error o and n = upto_error n in
  let rec go tol o n =
    let tolerate k = match tol with Some _ -> tol | None -> Some k in
    match o, n with
    | [], [] -> (match tol with Some k -> Tolerated k | None -> Same)
    | [Err (oo, om)], [Err (no, nm)]
      when starts_with "exception: " om && (starts_with "Cannot convert " nm && no <= oo || no > oo) ->
        Tolerated "MonPoly's parser raised an exception"
    | [Err (oo, om)], [Err (no, nm)] when oo = no && om = nm -> go tol [] []
    | [Err (oo, om)], [Err (no, nm)] when oo = no && unrecognized om <> None && unrecognized om = unrecognized nm ->
        go tol [] []
    (* the verified parser reports an error in an entry at its '@', after any syntax error in it *)
    | [Err (oo, om)], [Err (no, nm)] when semantic om && (om = nm && no <= oo || no > oo) ->
        Tolerated "semantic error"
    | [Err (oo, om)], [Err (no, nm)] when nm = "Unterminated quoted string"
        && (unrecognized om <> None && (oo = no || oo = no + 1)
            || oo = no && no + 1 < String.length log && log.[no] = 'r' && log.[no + 1] = '"') ->
        Tolerated "unterminated string"
    | [Err (oo, _)], [Err (no, _)] when in_command log oo && (in_command log no || at_cmd no || no > oo) ->
        Tolerated "error in a command"
    | Cmd (_, Some (Helper.Arguments [_; _])) :: _, Err (no, _) :: _
      when (in_command log no || at_cmd no) && two_args_open log no ->
        Tolerated "two arguments of a command without '<'"
    | Cmd (c, Some (Helper.Arguments [b; a])) :: o, Cmd (c', Some (Helper.Arguments (a' :: b' :: r))) :: n
      when c = c' && a = a' && b = b' ->
        if r = [] then go (tolerate "two arguments of a command") o n
        else Tolerated "more than two arguments of a command"
    | x :: o, y :: n when x = y -> go tol o n
    | _ -> Differ in
  go None o n

let report name log o n =
  Printf.printf "=== %s: the parsers differ\n" name;
  if String.length log < 2000 then Printf.printf "--- log:\n%s\n" log;
  let show l = List.iter (fun e -> print_endline ("  " ^ string_of_event e)) (upto_error l) in
  print_endline "--- MonPoly's parser:"; show o;
  print_endline "--- verified parser:"; show n

(* The schema of a log: all predicates that the verified parser finds in it, as strings. *)
let schema_of log =
  let module V = Verified.Monitor in
  let preds = Hashtbl.create 16 in
  let add = List.iter (function
    | V.O_ITEM (_, V.Entry (_, evs)) -> List.iter (fun (p, _) -> Hashtbl.replace preds p ()) evs
    | _ -> ()) in
  let (o, st) = V.efeed_chunk log V.einit in
  add o; add (V.efinish st);
  Hashtbl.fold (fun p () s -> (p, []) :: s) preds []

let tally = Hashtbl.create 8
let count k = Hashtbl.replace tally k (1 + try Hashtbl.find tally k with Not_found -> 0)

(* The predicates that a trace reports as not in the signature. *)
let undefined trace =
  let pre = "Predicate " and post = " was not defined in the signature." in
  List.filter_map (function
    | Err (_, m) when starts_with pre m && ends_with post m ->
        Some (String.sub m (String.length pre) (String.length m - String.length pre - String.length post))
    | _ -> None) trace

let rec check ?schema name log =
  try check_traces ?schema name log
  with Wrong_position (off, (l, c), (l', c')) ->
    count "position";
    Printf.printf "=== %s: the verified parser locates offset %d at %d:%d instead of %d:%d (with chunks of %d bytes)\n"
      name off l c l' c' !Verified_log_parser.chunk_size;
    Verified_log_parser.chunk_size := 4096;
    false

and check_traces ?schema name log =
  (* Without a signature, the predicates of the log, found by both parsers: those that the
     verified parser outputs, and those that either parser reports as undefined.  Fields may be
     of any arity: the parsers do not check arities, the monitor does. *)
  let given = schema <> None in
  let rec runs schema k =
    let o = run_old schema log and n = run_new schema log in
    let missing = List.sort_uniq compare (undefined o @ undefined n) in
    if given || missing = [] || k = 0 then (schema, o)
    else runs (List.map (fun p -> (p, [])) missing @ schema) (k - 1) in
  let (schema, o) = runs (match schema with Some s -> s | None -> schema_of log) 10 in
  let n = run_new schema log in
  let digest t = Digest.string (Marshal.to_string t []) in
  (* positions are checked by run_new, for all chunk sizes *)
  let d = digest n in
  let ok = ref true in
  List.iter (fun size ->
    Verified_log_parser.chunk_size := size;
    if digest (run_new schema log) <> d then begin
      ok := false; count "chunking";
      Printf.printf "=== %s: chunks of %d bytes give another trace than chunks of 4096\n" name size end)
    (if String.length log <= 65536 then [1; 2; 3; 7] else [7; 1000]);
  Verified_log_parser.chunk_size := 4096;
  (match compare_traces log o n with
   | Same -> count "same"
   | Tolerated k -> count k
   | Differ -> ok := false; count "differ"; report name log o n);
  !ok

(* Random logs: well-formed ones, mutated by inserting, deleting, and replacing characters. *)

let pick a = a.(Random.int (Array.length a))

let simple_chars = "abcrxyzABCPQR0123456789_[]/:-.!"
let simple () = String.init (1 + Random.int 4) (fun _ -> simple_chars.[Random.int (String.length simple_chars)])

(* Quoted strings, with escapes of any byte; now and then long ones, which span chunks. *)
let quoted () =
  let b = Buffer.create 8 in
  let n = if Random.int 50 = 0 then 5000 else Random.int 5 in
  for _ = 1 to n do
    match Random.int 9 with
    | 0 -> Buffer.add_string b "\\\""
    | 1 -> Buffer.add_string b "\\\\"
    | 2 -> Buffer.add_char b '\\'; Buffer.add_char b (Char.chr (Random.int 256))
    | 3 -> Buffer.add_char b (pick [| ' '; '\n'; '\r'; '('; ','; '@'; '#'; '>'; 'r'; '\255'; '\000' |])
    | _ -> Buffer.add_char b simple_chars.[Random.int (String.length simple_chars)]
  done;
  (if Random.bool () then "\"" else "r\"") ^ Buffer.contents b ^ "\""

let field () = if Random.int 4 = 0 then quoted () else simple ()

let white () = match Random.int 14 with
  | 0 -> "\n" | 1 -> "\r\n" | 2 -> "\r" | 3 -> "\t" | 4 -> "  "
  | 5 -> " # a comment, (with) \"tokens\" @ \n"
  | 6 -> "# a comment\r" | 7 -> "#\r\n"
  | 8 -> "" | _ -> " "

let ws () = if Random.int 3 = 0 then white () else " "

let timestamp () = match Random.int 10 with
  | 0 -> string_of_int (Random.int 1_000_000_000) ^ string_of_int (Random.int 1_000_000)
  | 1 -> "00" ^ string_of_int (Random.int 100)
  | _ -> string_of_int (Random.int 100)

let gen_entry b =
  let add = Buffer.add_string b in
  add "@"; add (ws ()); add (timestamp ());
  for _ = 1 to Random.int 4 do
    add (white ()); add (ws ());
    add (pick [| "p"; "q"; "r"; "\"p\""; "long_name_1"; "\"\""; "r\"q\"" |]);
    (match Random.int 3 with
     | 0 -> ()
     | _ ->
        for _ = 1 to 1 + Random.int 2 do
          add (ws ()); add "(";
          let k = Random.int 4 in
          for i = 1 to k do
            add (ws ()); add (field ()); add (ws ()); if i < k then add ","
          done;
          add ")"
        done)
  done;
  if Random.int 4 = 0 then (add (ws ()); add ";")

(* Commands with up to three arguments, or slicing parameters. *)
let gen_command b =
  let add = Buffer.add_string b in
  add ">"; add (ws ()); add (pick [| "print"; "get_pos"; "save_state"; "\"cmd\"" |]);
  (match Random.int 3 with
   | 0 -> for _ = 1 to Random.int 4 do add (white ()); add " "; add (field ()) done
   | 1 -> add " {{(1,(a,b))},{(1,2),(3,4)},{(5,6)}}"
   | _ -> ());
  add (ws ()); add "<"

(* Logs of entries and commands; now and then long ones, of many chunks of 7 bytes. *)
let gen_log () =
  let b = Buffer.create 256 in
  for _ = 1 to (if Random.int 100 = 0 then 300 else Random.int 6) do
    Buffer.add_string b (white ());
    if Random.int 5 = 0 then gen_command b else gen_entry b;
    Buffer.add_string b (white ())
  done;
  if Random.int 6 = 0 then Buffer.add_string b "# a final comment";
  Buffer.contents b

let noise = "@();,<>{}\"\\#r \n\r\tx1$%&\000\255"

let mutate s =
  let s = ref s in
  for _ = 1 to Random.int 3 do
    let n = String.length !s in
    let i = if n = 0 then 0 else Random.int (n + 1) in
    let c = String.make 1 noise.[Random.int (String.length noise)] in
    s := (match Random.int 4 with
      | 0 -> String.sub !s 0 i ^ c ^ String.sub !s i (n - i)
      | 1 when i < n -> String.sub !s 0 i ^ String.sub !s (i + 1) (n - i - 1)
      | 2 when i < n -> String.sub !s 0 i ^ c ^ String.sub !s (i + 1) (n - i - 1)
      | _ -> String.sub !s 0 i)
  done;
  !s

let fuzz n =
  let ok = ref true in
  for i = 1 to n do
    let log = gen_log () in
    let log = if Random.int 3 = 0 then log else mutate log in
    if not (check (Printf.sprintf "random log %d" i) log) then ok := false
  done;
  !ok

let () =
  let sig_file = ref None and fuzz_n = ref 0 and seed = ref 0 and quiet = ref false and logs = ref [] in
  Arg.parse [
    "-sig", Arg.String (fun s -> sig_file := Some s), "FILE\tthe signature (default: all predicates of the log)";
    "-fuzz", Arg.Set_int fuzz_n, "N\tcompare the parsers on N random logs";
    "-seed", Arg.Set_int seed, "S\tthe seed of the random logs";
    "-q", Arg.Set quiet, "\tno summary if the parsers agree";
  ] (fun f -> logs := f :: !logs) "log_parser_diff [-sig FILE] LOG... | -fuzz N [-seed S] [-q]";
  Random.init !seed;
  let ok = ref true in
  List.iter (fun f ->
    let log = In_channel.with_open_bin f In_channel.input_all in
    let schema = Option.map Log_parser.parse_signature_file !sig_file in
    if not (check ?schema f log) then ok := false) (List.rev !logs);
  if !fuzz_n > 0 && not (fuzz !fuzz_n) then ok := false;
  let keys = List.sort compare (Hashtbl.fold (fun k _ l -> k :: l) tally []) in
  if not (!quiet && !ok) then
    Printf.printf "%s\n" (String.concat ", "
      (List.map (fun k -> Printf.sprintf "%s: %d" k (Hashtbl.find tally k)) keys));
  exit (if !ok then 0 else 1)
