(* Writes the module Examples_data: the files given as arguments, as a list of their names and
   contents, so that the examples are compiled into verimon.js. *)

let () =
  print_string "let files = [\n";
  Array.iteri (fun i f ->
      if i > 0 then
        Printf.printf "  (%S, %S);\n" (Filename.basename f)
          (In_channel.with_open_bin f In_channel.input_all)) Sys.argv;
  print_string "]\n"
