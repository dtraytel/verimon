(* The web version of VeriMon: the generated code of thys/VeriMon_CLI (Verimon_code), compiled to
   JavaScript with js_of_ocaml and driven from a page with a signature, a formula and a log.

   The inputs are checked as the command line does: the signature with the formula TRUE, then the
   formula, then the log, each with [cli_main] and, for the log, [vfeed_chunk] and [vfinish] as in
   src/verimon.ml.  The verdicts are printed as the command line prints them ([verdict_fold]). *)

open Js_of_ocaml
open Js_of_ocaml_lwt

let ( >>= ) = Lwt.bind

module Html = Dom_html
module V = Verimon_code.Verimon

(* The examples in groups: name, file name in examples/ and whether the formula is negated. *)
let example_groups =
  [ "Operators",
    [ "until", ("ex", false)
    ; "since", ("since", false)
    ; "aggregations", ("agg", false)
    ; "recursive let", ("letpast", false)
    ]
  ; "Policies",
    [ "publish/approve", ("rv11", true)
    ; "publish/approve/manager", ("rv11b", true)
    ; "three attempts", ("attempts", false)
    ; "failed logins (regular expression)", ("logins", false)
    ; "unprotected access (let)", ("locks", false)
    ]
  ; "Case studies",
    [ "Nokia: propagation of deletions", ("nokia", false)
    ; "GDPR: consent to use data", ("gdpr", false)
    ]
  ]

let examples = List.concat_map snd example_groups
let default_example = "publish/approve"

let negate = ref false

let string_of_chars cs = String.of_seq (List.to_seq cs)
let text t = String.concat "" t
let int_of_nat n = Z.to_int (V.integer_of_nat n)

(* Line and column of a byte offset in the log, as "line:column". *)
let position log off =
  let line = ref 1 and bol = ref 0 in
  for i = 0 to min off (String.length log) - 1 do
    if log.[i] = '\n' then (incr line; bol := i + 1)
  done;
  Printf.sprintf "%d:%d" !line (off - !bol + 1)

let is_error = function V.VO_ERROR _ -> true | V.VO_VERDICTS _ -> false

let rec from_error = function
  | [] -> []
  | o :: os -> if is_error o then o :: os else from_error os

(* Monitors the log: the verdicts, and the first error with its message. *)
let monitor cfg cf st fin n lsig log =
  let buf = Buffer.create 1024 in
  let err = ref None in
  let ff f = Printf.sprintf "%g" f in
  let handle = function
    | V.VO_VERDICTS vs when !err = None ->
        List.iter (fun (q, (tsq, table)) ->
            let ((), _) =
              V.verdict_fold cfg ff n q tsq table
                (fun i () -> Verimon_runtime.add_dec_of_z buf i)
                (fun s () -> Buffer.add_string buf s) () in
            ()) vs
    | V.VO_VERDICTS _ -> ()
    | V.VO_ERROR (off, e) ->
        if !err = None then
          err := Some (match V.log_error (V.c_unix cfg) lsig e with
            | V.LE_LOC msg -> position log (Z.to_int off) ^ ": " ^ string_of_chars msg
            | V.LE_ORDER msg | V.LE_CMD msg -> string_of_chars msg) in
  (* As in src/verimon.ml: the outputs up to the first error are those of the longest prefix of the
     log whose outputs have no error. *)
  let (outs, st') = V.vfeed_chunk cf log st in
  let outs =
    if not (List.exists is_error outs) then outs @ (
      let outs = V.vfinish cf fin st' in
      if not (List.exists is_error outs) then outs
      else
        let outs0 = V.vfinish cf None st' in
        if List.exists is_error outs0 then from_error outs else outs0 @ from_error outs)
    else begin
      let lo = ref 0 and hi = ref (String.length log) and st_lo = ref st and acc = ref [] in
      while !hi - !lo > 1 do
        let mid = (!lo + !hi) / 2 in
        let (o, st_mid) = V.vfeed_chunk cf (String.sub log !lo (mid - !lo)) !st_lo in
        if List.exists is_error o then hi := mid
        else (acc := List.rev_append o !acc; st_lo := st_mid; lo := mid)
      done;
      List.rev !acc @ from_error outs
    end in
  List.iter handle outs;
  (Buffer.contents buf, !err)

(* Runs the command line on the signature and the formula. *)
let cli ?(check = false) sigt formt =
  let args = [ "-sig"; "signature"; "-formula"; "formula" ]
    @ (if !negate then [ "-negate" ] else []) @ (if check then [ "-check" ] else []) in
  let rec step = function
    | V.Done (o, e, c) -> `Done (text o ^ text e, int_of_nat c)
    | V.Version -> `Done ("", 0)
    | V.NeedFile (name, k) -> step (k (if name = "signature" then sigt else formt))
    | V.Run (_, cfg, cf, st, fin, n, lsig) -> `Run (monitor cfg cf st fin n lsig) in
  try step (V.cli_main "verimon" args float_of_string_opt)
  with e -> `Done (Printexc.to_string e, 2)

let http_get url =
  XmlHttpRequest.get url >>= fun { XmlHttpRequest.code; content; _ } ->
  if code = 0 || code = 200 then Lwt.return content else fst (Lwt.wait ())

let getfile f =
  try Lwt.return (Sys_js.read_file ~name:f) with Not_found -> http_get f

let onload _ =
  let d = Html.document in
  let body = Js.Opt.get (d##getElementById (Js.string "verimon_demo")) (fun () -> assert false) in

  let title = Html.createH1 d in
  title##.innerHTML :=
    Js.string "VeriMon 2.0 <font size=3>Monitoring Metric First-Order Dynamic Properties</font>";

  let ex = Html.createDiv d in
  let ed_name = "*edited*" in
  let ex_names = List.map fst examples in
  let append_opt e s = Dom.appendChild e (d##createTextNode (Js.string s)) in
  append_opt ex "Select example ";
  let select = Html.createSelect d in
  let option parent text =
    let option = Html.createOption d in
    append_opt option text;
    Dom.appendChild parent option in
  option select ed_name;
  List.iter (fun (label, exs) ->
      let group = Html.createOptgroup d in
      group##.label := Js.string label;
      List.iter (fun (text, _) -> option group text) exs;
      Dom.appendChild select group) example_groups;
  Dom.appendChild ex select;
  append_opt ex " or edit";

  let tab = Html.createTable d in
  let row cells = let tr = Html.createTr d in List.iter (Dom.appendChild tr) cells; Dom.appendChild tab tr in
  let cell () = let td = Html.createTd d in td##.vAlign := Js.string "top"; td in
  let tdl1 = cell () and tdr1 = cell () and tdl2 = cell () and tdr2 = cell () in
  let tdl3 = cell () and tdl4 = cell () and tdl5 = cell () and tdl6 = cell () in
  tdr2##.rowSpan := 5;

  let negatebox = Html.createInput ~_type:(Js.string "checkbox") d in
  negatebox##.checked := Js.bool !negate;
  let negatelab = Html.createLabel d in
  negatelab##.style##.cssFloat := Js.string "right";
  Dom.appendChild negatelab negatebox;
  Dom.appendChild negatelab (d##createTextNode (Js.string "negate"));

  let heading s = let b = Html.createB d in b##.innerHTML := Js.string s; b in
  let frame id rows =
    let f = Html.createTextarea d in
    f##.style##.border := Js.string "2px green solid";
    f##.rows := rows;
    f##.id := Js.string id;
    f in
  let sigtext = heading "Signature " in
  let sigin = Html.createInput ~_type:(Js.string "file") d in
  let sigframe = frame "sig" 10 in
  let formulatext = heading "MFODL formula " in
  let formulain = Html.createInput ~_type:(Js.string "file") d in
  let formulaframe = frame "formula" 15 in
  let logtext = heading "Log " in
  let login = Html.createInput ~_type:(Js.string "file") d in
  let logframe = frame "log" 35 in
  let restext = heading "Verdicts " in
  let resframe = frame "res" 3 in
  resframe##.style##.border := Js.string "2px red solid";
  resframe##.style##.backgroundColor := Js.string "lightgrey";
  resframe##.disabled := Js._true;

  Dom.appendChild body title;
  Dom.appendChild body ex;
  Dom.appendChild ex negatelab;
  Dom.appendChild body (Html.createHr d);
  List.iter (fun (td, es) -> List.iter (Dom.appendChild td) es)
    [ (tdl1, [ (sigtext :> Dom.node Js.t); (sigin :> Dom.node Js.t) ]);
      (tdr1, [ (logtext :> Dom.node Js.t); (login :> Dom.node Js.t) ]);
      (tdl2, [ (sigframe :> Dom.node Js.t) ]); (tdr2, [ (logframe :> Dom.node Js.t) ]);
      (tdl3, [ (formulatext :> Dom.node Js.t); (formulain :> Dom.node Js.t) ]);
      (tdl4, [ (formulaframe :> Dom.node Js.t) ]);
      (tdl5, [ (restext :> Dom.node Js.t) ]); (tdl6, [ (resframe :> Dom.node Js.t) ]) ];
  row [ tdl1; tdr1 ]; row [ tdl2; tdr2 ]; row [ tdl3 ]; row [ tdl4 ]; row [ tdl5 ]; row [ tdl6 ];
  Dom.appendChild body tab;

  let color_frame border deact xframe =
    xframe##.style##.border := Js.string border;
    xframe##.style##.backgroundColor := Js.string (if deact then "lightgrey" else "white");
    xframe##.style##.backgroundImage := Js.string "none";
    xframe##.disabled := Js.bool deact in
  let deactivate = color_frame "2px grey solid" true in
  let error msg xframe = color_frame "2px red solid" false xframe; xframe##.title := Js.string msg in
  let warn = color_frame "2px yellow solid" false in
  let ok xframe = color_frame "2px green solid" false xframe; xframe##.title := Js.string "" in
  let visibility_res vis =
    resframe##.style##.display := Js.string vis;
    restext##.style##.display := Js.string vis in
  let hide_res () = visibility_res "none" in
  let show_res () = visibility_res "inline" in

  let value f = Js.to_string f##.value in

  let check_log run =
    let (verdicts, err) = run (value logframe ^ "\n") in
    resframe##.value := Js.string verdicts;
    match err with
    | Some msg -> error msg logframe; if verdicts = "" then hide_res () else show_res ()
    | None ->
        ok logframe;
        if verdicts = "" then begin
          hide_res ();
          logframe##.style##.backgroundImage := Js.string "url(\"check.png\")"
        end else (warn logframe; show_res ()) in

  let check_formula () =
    match cli (value sigframe) (value formulaframe) with
    | `Run run -> ok formulaframe; check_log run
    | `Done (msg, c) ->
        deactivate logframe;
        hide_res ();
        if c <> 0 then error msg formulaframe
        else begin
          let reason = match cli ~check:true (value sigframe) (value formulaframe) with
            | `Done (m, _) -> m | `Run _ -> msg in
          warn formulaframe;
          formulaframe##.title := Js.string reason;
          formulaframe##.style##.backgroundImage := Js.string "url(\"tel.png\")"
        end in

  let check_sig () =
    match cli (value sigframe) "TRUE" with
    | `Done (msg, c) when c <> 0 ->
        error msg sigframe;
        deactivate formulaframe;
        deactivate logframe;
        hide_res ()
    | _ -> ok sigframe; check_formula () in

  let register (xin : Html.inputElement Js.t) (xframe : Html.textAreaElement Js.t) xcheck =
    xframe##.oninput := Html.handler (fun _ ->
        xcheck ();
        select##.value := Js.string ed_name;
        xin##.value := Js.string "";
        Js._true);
    xin##.onchange := Html.handler (fun _ ->
        Js.Opt.iter xin##.files (fun fs ->
            Js.Opt.iter (fs##item 0) (fun file ->
                ignore (File.readAsText file >>= fun text ->
                        xframe##.value := text;
                        xcheck ();
                        select##.value := Js.string ed_name;
                        Lwt.return_unit)));
        Js._true) in
  register sigin sigframe check_sig;
  register formulain formulaframe check_sig;
  register login logframe check_sig;

  negatebox##.onclick := Html.handler (fun _ ->
      negate := Js.to_bool negatebox##.checked;
      check_sig ();
      Js._true);

  let load_ex name =
    let (file, neg) = List.assoc name examples in
    let load ext frame = getfile ("examples/" ^ file ^ ext) >>= fun s ->
      frame##.value := Js.string s; Lwt.return_unit in
    ignore (Lwt.join [ load ".sig" sigframe; load ".mfotl" formulaframe; load ".log" logframe ]
            >>= fun () ->
            negate := neg;
            negatebox##.checked := Js.bool neg;
            check_sig ();
            Lwt.return_unit) in
  select##.onchange := Html.handler (fun _ ->
      let i = select##.selectedIndex - 1 in
      if i >= 0 && i < List.length ex_names then load_ex (List.nth ex_names i);
      Js._false);
  select##.value := Js.string default_example;
  load_ex default_example;
  Js._false

let () = Html.window##.onload := Html.handler onload
