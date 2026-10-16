(* What the driver of verimon (verimon.ml) does around the generated code: reading the log in
   chunks, locating the errors in it by line and column, and the run-time settings. *)

(* Lines and columns.  The generated log parser reports byte offsets: of the first token of an
   item (its '@' or '>') and of an error.  These offsets never decrease, so only the chunks from
   the last reported offset on are kept, with the line and the beginning of the line at their
   start.  "\n", "\r" and "\r\n" are each one line break, also in quoted strings. *)

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

(* "file:line:column", the column counted from 1. *)
let string_of_position p = Lexing.(
  Printf.sprintf "%s:%d:%d" p.pos_fname p.pos_lnum (p.pos_cnum - p.pos_bol + 1))

let int_of_z z = if Z.fits_int z then Z.to_int z else max_int

(* A reader of the input in chunks of [size] bytes. *)
let channel_reader ~size ic =
  let buf = Bytes.create size in
  fun () ->
    let n = input ic buf 0 size in
    if n = 0 then None else Some (Bytes.sub_string buf 0 n)

(* The minor heap size in words the monitor runs with unless -gc_minor_heap says otherwise.
   Most of what the monitor allocates dies before the next time point, but with OCaml's default
   256k-word nursery some of it is promoted first and collected by the major GC.  Under OCaml 4,
   768k words is where instruction counts (fewer promotions with a larger nursery) and wall clock
   (a nursery that does not fit the cache costs more than the collections it saves; 4M words is a
   third slower) meet.  OCaml 5's runtime does not have that cost: on the performance suite, 4M
   words is the fastest of 768k, 2M, 4M and 8M words (6% faster than 768k on the runs over 1.5 s,
   the same on the short ones), and 8M words is slower again. *)
let default_minor_heap = if Sys.ocaml_release.major >= 5 then 4194304 else 786432

(* The peak virtual memory of the process in kB (VmPeak in /proc/self/status), for -mem; the
   empty string where there is no such file. *)
let mem_max () =
  let prefix = "VmPeak:" in
  match open_in "/proc/self/status" with
  | exception Sys_error _ -> ""
  | ic ->
      let rec find () =
        match input_line ic with
        | exception End_of_file -> ""
        | l when String.length l > String.length prefix
                 && String.sub l 0 (String.length prefix) = prefix ->
            let digits = String.to_seq l |> Seq.filter (fun c -> c >= '0' && c <= '9') in
            String.of_seq digits
        | _ -> find () in
      Fun.protect ~finally:(fun () -> close_in_noerr ic) find
