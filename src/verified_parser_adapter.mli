(** The verified formula parser (thys/MFODL_Parser) on MonPoly's syntax trees. *)

val parse_string : string -> MFOTL.formula option
(** [parse_string s] lexes, parses and post-processes [s] like
    [Formula_parser.formula Formula_lexer.token], returning [None] where
    MonPoly's parser fails (and on the documented differences, see
    thys/MFODL_Parser/README.md). *)
