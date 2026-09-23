(* The log parser generated from theory Log_Code of session Log_Parser (thys/Log_Parser), driven
   over a channel or a string.

   The generated code reads the log in chunks: efeed_chunk takes the next chunk and the state
   and returns what the chunk completes, efinish returns what the end of the input completes.
   Theorem eparse_correct (Log_Exec.thy) states that, however the input is divided into chunks,
   the outputs contain no error exactly if the input is a log of the grammar of Log_Grammar.thy,
   and that they then list its entries in order; by efeed_chunks_online and efeed_chunks_prompt,
   the entries output so far are those of every log that extends the input read so far, and a
   time point is passed on as soon as the '@' or '>' of the next item has been read.  After an
   error the parser skips to the next '@', ';' or '>' (but a quoted string that is not closed
   contains the rest of the input); what it outputs after an error, and the offsets, are not
   covered by the theorems.  An error is reported once the offending token has ended, which for
   a simple string is at the next byte that is not part of it.

   This module passes the entries to a consumer with the interface of Log_parser.Make and does
   what the grammar leaves to the consumer: it converts timestamps, looks predicates up in the
   signature, keeps MonPoly's statistics, parses the parameters of commands, and turns the
   offsets of errors into lines and columns. *)

module V = Verified.Monitor

let old = ref false

(* Small chunks: the outputs of a chunk live until the chunk has been read, and on large chunks
   they survive minor collections.  (A reference, so that tests can vary it.) *)
let chunk_size = ref 4096

(* Lines and columns.  The generated parser reports byte offsets: of the first token of an item
   (its '@' or '>') and of an error.  These offsets never decrease, so only the chunks from the
   last reported offset on are kept, with the line and the beginning of the line at their start.
   "\n", "\r" and "\r\n" are each one line break, as for MonPoly's lexer (which does not count
   line breaks in quoted strings; these are counted here). *)

type chunk = {
  c_off: int;           (* the offset of the chunk *)
  c_line: int;          (* the line at its start *)
  c_bol: int;           (* the offset of the beginning of that line *)
  c_cr: bool;           (* whether the preceding byte is '\r' *)
  c_text: string;
}

type lines = {
  fname: string;
  mutable chunks: chunk list;   (* the chunks kept, the last one first *)
}

(* The line, the beginning of the line, and whether the last byte is '\r', after the first [upto]
   bytes of a chunk. *)
let scan c upto =
  let s = c.c_text in
  let line = ref c.c_line and bol = ref c.c_bol and cr = ref c.c_cr in
  for i = 0 to upto - 1 do
    match String.unsafe_get s i with
    | '\n' -> if not !cr then incr line; bol := c.c_off + i + 1; cr := false
    | '\r' -> incr line; bol := c.c_off + i + 1; cr := true
    | _ -> cr := false
  done;
  (!line, !bol, !cr)

let init_lines fname = { fname; chunks = [] }

let push_chunk ln s =
  let c = match ln.chunks with
    | [] -> { c_off = 0; c_line = 1; c_bol = 0; c_cr = false; c_text = s }
    | c :: _ ->
        let (line, bol, cr) = scan c (String.length c.c_text) in
        { c_off = c.c_off + String.length c.c_text; c_line = line; c_bol = bol; c_cr = cr; c_text = s } in
  ln.chunks <- c :: ln.chunks

(* Forgets the chunks that end before [off], except the last one. *)
let forget ln off =
  match ln.chunks with
  | [] | [_] -> ()
  | chunks ->
      let rec keep acc = function
        | c :: (_ :: _ as r) when c.c_off > off -> keep (c :: acc) r
        | c :: _ -> List.rev_append acc [c]
        | [] -> List.rev acc in
      ln.chunks <- keep [] chunks

let position ln off =
  let pos (line, bol, _) =
    Lexing.{ pos_fname = ln.fname; pos_lnum = line; pos_bol = bol; pos_cnum = off } in
  let rec find = function
    | c :: r when c.c_off > off && r <> [] -> find r
    | c :: _ -> pos (scan c (max 0 (min (off - c.c_off) (String.length c.c_text))))
    | [] -> pos (1, 0, false) in
  find ln.chunks

(* Messages, as MonPoly's parser words them. *)

let string_of_token = function
  | V.T_AT -> "'@'"
  | V.T_LPAREN -> "'('"
  | V.T_RPAREN -> "')'"
  | V.T_LANGLE -> "'<'"
  | V.T_RANGLE -> "'>'"
  | V.T_LBRACE -> "'{'"
  | V.T_RBRACE -> "'}'"
  | V.T_COMMA -> "','"
  | V.T_SEMICOLON -> "';'"
  | V.T_STR s -> "\"" ^ String.escaped s ^ "\""

let string_of_expect = function
  | V.X_ENTRY -> "'@' or '>'"
  | V.X_TIMESTAMP -> "a time-stamp"
  | V.X_PREDICATE -> "a predicate, '@', ';', or '>'"
  | V.X_FIELD_OR_RPAREN -> "a tuple field or ')'"
  | V.X_COMMA_OR_RPAREN -> "',' or ')'"
  | V.X_FIELD -> "a tuple field"
  | V.X_CMD_NAME -> "a command name"
  | V.X_CMD_ARG -> "a command argument or '<'"

let message = function
  | V.E_TOKEN (x, Some t) -> "Expected " ^ string_of_expect x ^ " but saw " ^ string_of_token t
  | V.E_TOKEN (x, None) -> "Expected " ^ string_of_expect x ^ " but saw <EOF>"
  | V.E_CHAR (x, c) -> "Expected " ^ string_of_expect x ^ " but saw <unrecognized> (" ^ Char.escaped c ^ ")"
  | V.E_UNTERMINATED -> "Unterminated quoted string"

(* The parameters of commands, as Log_parser.parse_command_params reads them. *)

exception Param_error of string

let command_params args =
  let toks = ref args in
  let peek () = match !toks with t :: _ -> Some t | [] -> None in
  let saw () = match peek () with Some t -> string_of_token t | None -> "'<'" in
  let next () = match !toks with _ :: r -> toks := r | [] -> () in
  let expect t = if peek () = Some t then next ()
    else raise (Param_error ("Expected " ^ string_of_token t ^ " but saw " ^ saw ())) in
  let str () = match peek () with
    | Some (V.T_STR s) -> next (); s
    | _ -> raise (Param_error ("Expected a string but saw " ^ saw ())) in
  let int () = let s = str () in
    try int_of_string s
    with Failure _ -> raise (Param_error ("Expected an integer but saw \"" ^ String.escaped s ^ "\"")) in
  let tuple () =
    expect V.T_LPAREN;
    match peek () with
    | Some V.T_RPAREN -> next (); []
    | Some (V.T_STR s) ->
        next ();
        let rec more l = match peek () with
          | Some V.T_COMMA -> next (); let s = str () in more (s :: l)
          | Some V.T_RPAREN -> next (); List.rev l
          | _ -> raise (Param_error ("Expected ',' or ')' but saw " ^ saw ())) in
        more [s]
    | _ -> raise (Param_error ("Expected a string or ')' but saw " ^ saw ())) in
  let int_tuple () =
    try List.map int_of_string (tuple ())
    with Failure _ -> raise (Param_error "Expected a tuple of integers") in
  let list item =
    expect V.T_LBRACE;
    let x0 = item () in
    let rec more l = match peek () with
      | Some V.T_COMMA -> next (); let x = item () in more (x :: l)
      | _ -> List.rev l in
    let l = more [x0] in
    expect V.T_RBRACE;
    Array.of_list l in
  let heavy () = expect V.T_LPAREN; let i = int () in expect V.T_COMMA;
    let t = tuple () in expect V.T_RPAREN; (i, t) in
  match args with
  | [] -> None
  | V.T_LBRACE :: _ ->
      expect V.T_LBRACE;
      let heavies = list heavy in
      expect V.T_COMMA;
      let shares = list (fun () -> Array.of_list (int_tuple ())) in
      expect V.T_COMMA;
      let seeds = list (fun () -> Array.of_list (int_tuple ())) in
      expect V.T_RBRACE;
      if !toks <> [] then raise (Param_error ("Expected '<' but saw " ^ saw ()));
      Some (Helper.SplitSave (heavies, shares, seeds))
  | V.T_STR _ :: _ ->
      Some (Helper.Arguments (List.map (function
        | V.T_STR s -> s
        | t -> raise (Param_error ("Expected a string or '<' but saw " ^ string_of_token t))) args))
  | t :: _ -> raise (Param_error ("Expected a string, '{' or '<' but saw " ^ string_of_token t))

let int_of_z z = if Z.fits_int z then Z.to_int z else max_int

module Make (C : Log_parser.Consumer) = struct

  let run dbschema fname read ctxt =
    let schemas = Hashtbl.create 64 in
    List.iter (fun (p, tl) -> if not (Hashtbl.mem schemas p) then Hashtbl.add schemas p (p, tl))
      dbschema;
    (* the schema of a predicate (Not_found if it is not in the signature), remembering the last
       one, since consecutive events are often of the same predicate *)
    let last = ref None in
    let find p =
      match !last with
      | Some (q, schema) when String.equal p q -> schema
      | _ ->
          let schema = Hashtbl.find schemas p in
          last := Some (p, schema);
          schema in
    let ln = init_lines fname in
    let error off msg = C.parse_error ctxt (position ln off) msg in
    let handle o =
      match o with
      | V.O_ITEM (sp, V.Entry (ts, evs)) ->
          (* an entry with an error is dropped as a whole, as the parser drops an entry with a
             syntax error; the error is located at the entry's '@' *)
          let sp = int_of_z sp in
          forget ln sp;
          (match (try Some (MFOTL.ts_of_string ts) with Failure _ | Invalid_argument _ -> None) with
           | None -> error sp ("Cannot convert " ^ ts ^ " into a timestamp")
           | Some t ->
              match List.find_opt (fun (p, _) -> match find p with _ -> false | exception Not_found -> true) evs with
              | Some (p, _) -> error sp ("Predicate " ^ p ^ " was not defined in the signature.")
              | None ->
                  (* MonPoly's parser counts the predicates of a time point, this counts its
                     tuples *)
                  let stats = C.stats ctxt in
                  stats.Log_parser.Stats.tp_done <- stats.Log_parser.Stats.tp_done + 1;
                  stats.Log_parser.Stats.ev_done <- stats.Log_parser.Stats.ev_done + List.length evs;
                  C.begin_tp ctxt t;
                  List.iter (fun (p, fields) -> C.tuple ctxt (find p) fields) evs;
                  C.end_tp ctxt)
      | V.O_ITEM (sp, V.Command (name, args)) ->
          let sp = int_of_z sp in
          forget ln sp;
          (match command_params args with
           | params -> C.command ctxt name params
           | exception Param_error msg -> error sp msg)
      | V.O_ERROR (off, e) ->
          let off = int_of_z off in
          forget ln off;
          error off (message e) in
    let rec loop st =
      match read () with
      | Some s ->
          push_chunk ln s;
          let (outs, st) = V.efeed_chunk s st in
          List.iter handle outs;
          loop st
      | None -> List.iter handle (V.efinish st) in
    try
      loop V.einit;
      C.end_log ctxt;
      true
    with Log_parser.Stop_parser -> false

  let parse_channel dbschema fname ic ctxt =
    let size = !chunk_size in
    let buf = Bytes.create size in
    run dbschema fname (fun () ->
      let n = input ic buf 0 size in
      if n = 0 then None else Some (Bytes.sub_string buf 0 n)) ctxt

  let parse_string dbschema s ctxt =
    let size = !chunk_size and pos = ref 0 in
    run dbschema "" (fun () ->
      if !pos >= String.length s then None
      else begin
        let n = min size (String.length s - !pos) in
        let c = String.sub s !pos n in
        pos := !pos + n; Some c
      end) ctxt

  let parse_file dbschema fname ctxt =
    if fname = "" then parse_channel dbschema fname stdin ctxt
    else begin
      let ic = open_in_bin fname in
      Fun.protect ~finally:(fun () -> close_in_noerr ic) (fun () -> parse_channel dbschema fname ic ctxt)
    end
end
