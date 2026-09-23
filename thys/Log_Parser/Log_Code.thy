(*<*)
theory Log_Code
  imports Log_Exec "HOL-Library.Code_Abstract_Char" "HOL-Library.Code_Target_Nat"
begin
(*>*)

section \<open>Code generation\<close>

text \<open>
  The parser of @{theory Log_Parser.Log_Exec} is compiled to OCaml with characters as OCaml's
  characters and byte strings as OCaml's strings. The code printings below are the trusted part.
  Each maps an operation to OCaml code with the same meaning on the represented values: for
  characters, the bijection between @{typ char} and OCaml's 256 characters, which preserves the
  order; for byte strings, OCaml's strings of bytes; for @{typ integer}, Zarith's integers, which
  represent every integer that fits into a machine integer as that machine integer (the same
  assumption as @{text cmp_integer} in the monitor's code setup). The code equations further below
  are proved: they make the loops scan the bytes of a lexeme without returning to the automaton.
\<close>

subsection \<open>Characters\<close>

code_printing
  type_constructor char \<rightharpoonup> (OCaml) "char"
| constant Chr \<rightharpoonup> (OCaml) "(Char.unsafe'_chr (Z.to'_int (Z.logand _ (Z.of'_int 255))))"
| constant integer_of_char \<rightharpoonup> (OCaml) "(Z.of'_int (Char.code _))"
| constant "HOL.equal :: char \<Rightarrow> char \<Rightarrow> bool" \<rightharpoonup> (OCaml) "((_ : char) = _)"
| constant "(\<le>) :: char \<Rightarrow> char \<Rightarrow> bool" \<rightharpoonup> (OCaml) "((_ : char) <= _)"
| constant "(<) :: char \<Rightarrow> char \<Rightarrow> bool" \<rightharpoonup> (OCaml) "((_ : char) < _)"

text \<open>The 256 character constants of @{theory "HOL-Library.Code_Abstract_Char"}, by which the code
  generator replaces character literals, as OCaml character literals.\<close>

setup \<open>
  fold (fn n => Code_Target.set_printings (Code_Symbol.Constant
    ("Code_Abstract_Char.Char_" ^ String_Syntax.hex n,
     [("OCaml", SOME (Code_Printer.plain_const_syntax
        ("'\\" ^ StringCvt.padLeft #"0" 3 (Int.toString n) ^ "'")))])))
    (0 upto 255)
\<close>

subsection \<open>Byte strings and indices\<close>

text \<open>The printings agree with the definitions on all arguments. @{const bytes_sub} is total like
  its definition, taking @{text "nat (j - i)"} bytes after the first @{text "nat i"} ones.
  @{const bytes_at} reads the first byte at a negative index, like its definition; at an index
  beyond the string, where its definition leaves the result unspecified, it raises an exception.
  The parser applies both within the string only.\<close>

definition idx_less :: "integer \<Rightarrow> integer \<Rightarrow> bool" where
  "idx_less i j \<longleftrightarrow> i < j"

definition idx_succ :: "integer \<Rightarrow> integer" where
  "idx_succ i = i + 1"

definition idx_add :: "integer \<Rightarrow> integer \<Rightarrow> integer" where
  "idx_add i j = i + j"

declare [[code drop: bytes_length bytes_at bytes_sub bytes_concat bytes_empty bytes_null idx_less idx_succ idx_add]]

code_printing
  type_constructor bytes \<rightharpoonup> (OCaml) "string"
| constant bytes_length \<rightharpoonup> (OCaml) "(Z.of'_int (String.length _))"
| constant bytes_null \<rightharpoonup> (OCaml) "(String.length _ = 0)"
| constant bytes_at \<rightharpoonup> (OCaml)
    "(fun s i -> String.get s (if Obj.is'_int (Obj.repr i) then (let k = (Obj.magic i : Stdlib.Int.t) in if k < 0 then 0 else k)
      else if Z.sign i < 0 then 0 else Z.to'_int i))"
| constant bytes_sub \<rightharpoonup> (OCaml)
    "(fun s i j -> let n = String.length s in
      if Obj.is'_int (Obj.repr i) && Obj.is'_int (Obj.repr j) && 0 <= (Obj.magic i : Stdlib.Int.t)
        && (Obj.magic i : Stdlib.Int.t) <= (Obj.magic j : Stdlib.Int.t) && (Obj.magic j : Stdlib.Int.t) <= n
      then String.sub s (Obj.magic i : Stdlib.Int.t) ((Obj.magic j : Stdlib.Int.t) - (Obj.magic i : Stdlib.Int.t))
      else (let a = if Z.sign i <= 0 then 0 else if Z.lt i (Z.of'_int n) then Z.to'_int i else n in
        let l = Z.sub j i in
        if Z.sign l <= 0 || a >= n then \"\"
        else String.sub s a (if Z.lt l (Z.of'_int (n - a)) then Z.to'_int l else n - a)))"
| constant bytes_concat \<rightharpoonup> (OCaml) "(String.concat \"\" _)"
| constant bytes_empty \<rightharpoonup> (OCaml) "\"\""
| constant idx_less \<rightharpoonup> (OCaml)
    "(fun i j -> if Obj.is'_int (Obj.repr i) && Obj.is'_int (Obj.repr j) then (Obj.magic i : Stdlib.Int.t) < (Obj.magic j : Stdlib.Int.t) else Z.lt i j)"
| constant idx_succ \<rightharpoonup> (OCaml)
    "(fun i -> if Obj.is'_int (Obj.repr i) && (Obj.magic i : Stdlib.Int.t) < max'_int then Z.of'_int ((Obj.magic i : Stdlib.Int.t) + 1) else Z.succ i)"
| constant idx_add \<rightharpoonup> (OCaml)
    "(fun i j -> if Obj.is'_int (Obj.repr i) && Obj.is'_int (Obj.repr j) && (let a = (Obj.magic i : Stdlib.Int.t) and b = (Obj.magic j : Stdlib.Int.t) in let c = a + b in (c lxor a) land (c lxor b) >= 0) then Z.of'_int ((Obj.magic i : Stdlib.Int.t) + (Obj.magic j : Stdlib.Int.t)) else Z.add i j)"

subsection \<open>Scanning lexemes\<close>

text \<open>The runs of bytes that leave the lexer's state unchanged: white space, the rest of a simple
  string, the content of a quoted string up to a quote or backslash, and a comment.\<close>

definition skips :: "elstate \<Rightarrow> char \<Rightarrow> bool" where
  "skips l c = (case l of
     E_INIT \<Rightarrow> isWhiteSpace c
   | E_SIMPLE _ _ _ \<Rightarrow> isSimpleChar c
   | E_QUOTED _ _ _ \<Rightarrow> c \<noteq> CHR 0x22 \<and> c \<noteq> CHR 0x5C
   | E_ESCAPE _ _ _ \<Rightarrow> False
   | E_COMMENT \<Rightarrow> \<not> isLineCommentEnd c)"

lemma skips_R_SAME: "skips l c \<Longrightarrow> elex_step s b i c l = R_SAME"
  by (cases l) (auto simp: skips_def elex_step_def)

function eskip :: "elstate \<Rightarrow> bytes \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> integer" where
  "eskip l s n i = (if i < n \<and> skips l (bytes_at s i) then eskip l s n (i + 1) else i)"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(l, s, n, i). nat_of_integer (n - i))") (auto simp: integer_simps)

declare eskip.simps[simp del]

lemma eloop_eskip: "eloop s n b i l p sp acc = eloop s n b (eskip l s n i) l p sp acc"
proof (induction l s n i rule: eskip.induct)
  case (1 l s n i)
  show ?case
  proof (cases "i < n \<and> skips l (bytes_at s i)")
    case True
    then have "eloop s n b i l p sp acc = eloop s n b (i + 1) l p sp acc"
      by (subst eloop.simps) (simp add: skips_R_SAME)
    also have "\<dots> = eloop s n b (eskip l s n (i + 1)) l p sp acc"
      using 1 True by simp
    also have "eskip l s n (i + 1) = eskip l s n i"
      using True by (simp add: eskip.simps[of l s n i])
    finally show ?thesis .
  next
    case False
    then have "eskip l s n i = i"
      by (subst eskip.simps) auto
    then show ?thesis
      by simp
  qed
qed

text \<open>The scan for each kind of lexeme, with the class of its bytes unfolded, so that the
  compiled loop makes no calls.\<close>

function skip_white :: "bytes \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> integer" where
  "skip_white s n i = (if idx_less i n \<and>
     (let c = bytes_at s i in c = CHR '' '' \<or> c = CHR 0x09 \<or> c = CHR 0x0A \<or> c = CHR 0x0D)
     then skip_white s n (idx_succ i) else i)"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(s, n, i). nat_of_integer (n - i))") (auto simp: integer_simps idx_less_def idx_succ_def)

function skip_simple :: "bytes \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> integer" where
  "skip_simple s n i = (if idx_less i n \<and>
     (let c = bytes_at s i in
       CHR ''0'' \<le> c \<and> c \<le> CHR ''9'' \<or> CHR ''a'' \<le> c \<and> c \<le> CHR ''z'' \<or> CHR ''A'' \<le> c \<and> c \<le> CHR ''Z'' \<or>
       c = CHR ''_'' \<or> c = CHR ''['' \<or> c = CHR '']'' \<or> c = CHR ''/'' \<or> c = CHR '':'' \<or> c = CHR ''-'' \<or>
       c = CHR ''.'' \<or> c = CHR ''!'')
     then skip_simple s n (idx_succ i) else i)"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(s, n, i). nat_of_integer (n - i))") (auto simp: integer_simps idx_less_def idx_succ_def)

function skip_quoted :: "bytes \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> integer" where
  "skip_quoted s n i = (if idx_less i n \<and> (let c = bytes_at s i in c \<noteq> CHR 0x22 \<and> c \<noteq> CHR 0x5C)
     then skip_quoted s n (idx_succ i) else i)"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(s, n, i). nat_of_integer (n - i))") (auto simp: integer_simps idx_less_def idx_succ_def)

function skip_comment :: "bytes \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> integer" where
  "skip_comment s n i = (if idx_less i n \<and> (let c = bytes_at s i in c \<noteq> CHR 0x0A \<and> c \<noteq> CHR 0x0D)
     then skip_comment s n (idx_succ i) else i)"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(s, n, i). nat_of_integer (n - i))") (auto simp: integer_simps idx_less_def idx_succ_def)

declare skip_white.simps[simp del] skip_simple.simps[simp del] skip_quoted.simps[simp del]
  skip_comment.simps[simp del]

lemma eskip_code[code]: "eskip l s n i = (case l of
     E_INIT \<Rightarrow> skip_white s n i
   | E_SIMPLE _ _ _ \<Rightarrow> skip_simple s n i
   | E_QUOTED _ _ _ \<Rightarrow> skip_quoted s n i
   | E_ESCAPE _ _ _ \<Rightarrow> i
   | E_COMMENT \<Rightarrow> skip_comment s n i)"
proof -
  have "eskip E_INIT s n i = skip_white s n i"
    by (induction s n i rule: skip_white.induct)
      (subst eskip.simps, subst skip_white.simps, auto simp: skips_def isWhiteSpace_def idx_less_def idx_succ_def Let_def)
  moreover have "eskip (E_SIMPLE pre st tp) s n i = skip_simple s n i" for pre st tp
    by (induction s n i rule: skip_simple.induct)
      (subst eskip.simps, subst skip_simple.simps, auto simp: skips_def isSimpleChar_def idx_less_def idx_succ_def Let_def)
  moreover have "eskip (E_QUOTED pre st tp) s n i = skip_quoted s n i" for pre st tp
    by (induction s n i rule: skip_quoted.induct)
      (subst eskip.simps, subst skip_quoted.simps, auto simp: skips_def  idx_less_def idx_succ_def Let_def)
  moreover have "eskip (E_ESCAPE pre st tp) s n i = i" for pre st tp
    by (subst eskip.simps) (simp add: skips_def)
  moreover have "eskip E_COMMENT s n i = skip_comment s n i"
    by (induction s n i rule: skip_comment.induct)
      (subst eskip.simps, subst skip_comment.simps, auto simp: skips_def isLineCommentEnd_def idx_less_def idx_succ_def Let_def)
  ultimately show ?thesis
    by (cases l) simp_all
qed

text \<open>The loop scans before each step of the automaton.\<close>

lemma eloop_code[code]:
  "eloop s n b i l p sp acc = (let i = eskip l s n i in if idx_less i n then (case elex_step s b i (bytes_at s i) l of
       R_SAME \<Rightarrow> eloop s n b (idx_succ i) l p sp acc
     | R_NEXT l' \<Rightarrow> eloop s n b (idx_succ i) l' p sp acc
     | R_TOK t tp l' \<Rightarrow> (case efeed t tp p sp acc of (acc', p') \<Rightarrow> eloop s n b (idx_succ i) l' p' (start tp p' sp) acc')
     | R_TOK2 t tp t' tp' l' \<Rightarrow> (case efeed t tp p sp acc of (acc', p') \<Rightarrow>
         case efeed t' tp' p' (start tp p' sp) acc' of (acc'', p'') \<Rightarrow>
           eloop s n b (idx_succ i) l' p'' (start tp' p'' (start tp p' sp)) acc'')
     | R_TOK_ERR t tp \<Rightarrow> (case efeed t tp p sp acc of (acc', p') \<Rightarrow>
         eloop s n b (idx_succ i) E_INIT None sp (echar_err (idx_add b i) (bytes_at s i) p' acc'))
     | R_ERR \<Rightarrow> eloop s n b (idx_succ i) E_INIT None sp (echar_err (idx_add b i) (bytes_at s i) p acc))
   else (acc, l, p, sp))"
  unfolding idx_less_def idx_succ_def idx_add_def Let_def
  by (subst eloop_eskip, subst eloop.simps) simp

subsection \<open>Other code equations\<close>

text \<open>The steps of the lexer with the character classes unfolded and the most frequent cases
  first.\<close>

lemma elex_init_code[code]: "elex_init pos i c =
    (if CHR ''0'' \<le> c \<and> c \<le> CHR ''9'' \<or> CHR ''A'' \<le> c \<and> c \<le> CHR ''Z'' \<or> CHR ''a'' \<le> c \<and> c \<le> CHR ''z'' \<or>
      c = CHR ''_'' \<or> c = CHR ''['' \<or> c = CHR '']'' \<or> c = CHR ''/'' \<or> c = CHR '':'' \<or> c = CHR ''-'' \<or>
      c = CHR ''.'' \<or> c = CHR ''!'' then R_NEXT (E_SIMPLE [] i pos)
     else if c = CHR '' '' \<or> c = CHR 0x09 \<or> c = CHR 0x0A \<or> c = CHR 0x0D then R_NEXT E_INIT
     else if c = CHR ''@'' then R_TOK T_AT pos E_INIT
     else if c = CHR ''('' then R_TOK T_LPAREN pos E_INIT
     else if c = CHR '')'' then R_TOK T_RPAREN pos E_INIT
     else if c = CHR ''<'' then R_TOK T_LANGLE pos E_INIT
     else if c = CHR ''>'' then R_TOK T_RANGLE pos E_INIT
     else if c = CHR ''{'' then R_TOK T_LBRACE pos E_INIT
     else if c = CHR ''}'' then R_TOK T_RBRACE pos E_INIT
     else if c = CHR '','' then R_TOK T_COMMA pos E_INIT
     else if c = CHR '';'' then R_TOK T_SEMICOLON pos E_INIT
     else if c = CHR ''#'' then R_NEXT E_COMMENT
     else if c = CHR 0x22 then R_NEXT (E_QUOTED [] (idx_succ i) pos)
     else R_ERR)"
  unfolding isSimpleChar_def[symmetric] isWhiteSpace_def[symmetric] idx_succ_def
  by (cases "isSimpleChar c") (simp_all add: elex_init_def simple_not_special)

lemma elex_step_code[code]: "elex_step s b i c l = (case l of
     E_INIT \<Rightarrow> (if c = CHR '' '' \<or> c = CHR 0x09 \<or> c = CHR 0x0A \<or> c = CHR 0x0D then R_SAME
       else elex_init (idx_add b i) i c)
   | E_SIMPLE pre st tp \<Rightarrow>
       (if CHR ''0'' \<le> c \<and> c \<le> CHR ''9'' \<or> CHR ''A'' \<le> c \<and> c \<le> CHR ''Z'' \<or> CHR ''a'' \<le> c \<and> c \<le> CHR ''z'' \<or>
          c = CHR ''_'' \<or> c = CHR ''['' \<or> c = CHR '']'' \<or> c = CHR ''/'' \<or> c = CHR '':'' \<or> c = CHR ''-'' \<or>
          c = CHR ''.'' \<or> c = CHR ''!'' then R_SAME
        else if c = CHR 0x22 \<and> is_r pre s st i then R_NEXT (E_QUOTED [] (idx_succ i) tp)
        else close_tok (T_STR (mk_str pre s st i)) tp (elex_init (idx_add b i) i c))
   | E_QUOTED pre st tp \<Rightarrow>
       (if c = CHR 0x22 then R_TOK (T_STR (mk_str pre s st i)) tp E_INIT
        else if c = CHR 0x5C then R_NEXT (E_ESCAPE pre st tp)
        else R_SAME)
   | E_ESCAPE pre st tp \<Rightarrow> R_NEXT (E_QUOTED pre st tp)
   | E_COMMENT \<Rightarrow> (if c = CHR 0x0A \<or> c = CHR 0x0D then R_NEXT E_INIT else R_SAME))"
  unfolding isSimpleChar_def[symmetric] isWhiteSpace_def[symmetric] idx_succ_def idx_add_def
  unfolding isLineCommentEnd_def[symmetric]
  by (simp add: elex_step_def)

lemma fold_O_ITEM: "fold (\<lambda>e acc. O_ITEM sp e # acc) es acc = rev (map (O_ITEM sp) es) @ acc"
  by (induction es arbitrary: acc) auto

lemma efeed_code[code]: "efeed t pos p sp acc = (case p of
     None \<Rightarrow> (acc, resync t)
   | Some ps \<Rightarrow> (case pstep t ps of
       None \<Rightarrow> (O_ERROR pos (E_TOKEN (expect_of ps) (Some t)) # acc, resync t)
     | Some (es, ps') \<Rightarrow> (fold (\<lambda>e acc. O_ITEM sp e # acc) es acc, Some ps')))"
  by (auto simp: efeed_def fold_O_ITEM split: option.splits)

lemma efinish_p_code[code]: "efinish_p b p sp acc = (case p of
     None \<Rightarrow> acc
   | Some ps \<Rightarrow> (case parse_finish ps of
       None \<Rightarrow> O_ERROR b (E_TOKEN (expect_of ps) None) # acc
     | Some es \<Rightarrow> fold (\<lambda>e acc. O_ITEM sp e # acc) es acc))"
  by (auto simp: efinish_p_def fold_O_ITEM split: option.splits)

(*<*)
end
(*>*)
