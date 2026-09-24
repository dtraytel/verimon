(** The verified formula parser (thys/MFODL_Parser) on MonPoly's syntax trees. *)

val parse_string : string -> MFOTL.formula option
(** [parse_string s] lexes, parses and post-processes [s] like
    [Formula_parser.formula Formula_lexer.token], returning [None] where
    MonPoly's parser fails (and on the documented differences, see
    thys/MFODL_Parser/README.md). *)

val lex_string : string -> (Verified_parser.Verified_parser.mtok * string) list option
(** The token classes and lexemes of the verified lexer model, for testing. *)

val chars_of_string : string -> Verified_parser.Verified_parser.char list
(** The input of the exported parser: the bytes of a string, for testing. *)
