theory MFODL_Lexer
  imports MFODL_Grammar
begin

section \<open>Lexer\<close>

text \<open>
  An executable model of MonPoly's formula lexer
  (\<^file>\<open>../../src/formula_lexer.mll\<close>). Like ocamllex, it takes the longest
  match at every position and resolves ties by rule order. Characters are
  bytes, so the Unicode spellings \<open>\<triangleright>\<close> and \<open>\<triangleleft>\<close> of \<open>|>\<close> and \<open><|\<close> are matched by their
  UTF-8 encodings. Unlike MonPoly, a time unit other than \<open>d\<close>, \<open>h\<close>, \<open>m\<close>, \<open>s\<close>
  is rejected here already; MonPoly lexes it as \<open>TU\<close> and fails in every
  context the token can appear in.

  The lexer is not verified; it only splits the input into the tokens that
  the verified parser consumes.
\<close>

definition is_digit :: \<open>char \<Rightarrow> bool\<close> where
  \<open>is_digit c = (CHR ''0'' \<le> c \<and> c \<le> CHR ''9'')\<close>

definition is_letter :: \<open>char \<Rightarrow> bool\<close> where
  \<open>is_letter c = (CHR ''a'' \<le> c \<and> c \<le> CHR ''z'' \<or> CHR ''A'' \<le> c \<and> c \<le> CHR ''Z'')\<close>

definition is_str_start :: \<open>char \<Rightarrow> bool\<close> where
  \<open>is_str_start c = (is_letter c \<or> is_digit c \<or> c = CHR ''_'')\<close>

definition is_str_char :: \<open>char \<Rightarrow> bool\<close> where
  \<open>is_str_char c = (is_str_start c \<or> c \<in> set ''-/:'' \<or> c = CHR 0x27 \<or> c = CHR 0x22)\<close>

definition is_space :: \<open>char \<Rightarrow> bool\<close> where
  \<open>is_space c = (c \<in> set [CHR '' '', CHR 0x09, CHR 0x0A, CHR 0x0D])\<close>

subsection \<open>Matchers\<close>

text \<open>Each matcher returns the length of the longest match at the beginning of
  the input, if any.\<close>

definition m_fixed :: \<open>string \<Rightarrow> string \<Rightarrow> nat option\<close> where
  \<open>m_fixed k s = (if k \<noteq> [] \<and> take (length k) s = k then Some (length k) else None)\<close>

definition count_digits :: \<open>string \<Rightarrow> nat\<close> where
  \<open>count_digits s = length (takeWhile is_digit s)\<close>

definition sign_len :: \<open>string \<Rightarrow> nat\<close> where
  \<open>sign_len s = (case s of CHR ''-'' # _ \<Rightarrow> 1 | _ \<Rightarrow> 0)\<close>

text \<open>\<open>digit+ letter\<close>\<close>

definition m_unit :: \<open>string \<Rightarrow> nat option\<close> where
  \<open>m_unit s = (let n = count_digits s in
     if 0 < n \<and> n < length s \<and> is_letter (s ! n) then Some (Suc n) else None)\<close>

text \<open>\<open>'-'? digit+\<close>\<close>

definition m_int :: \<open>string \<Rightarrow> nat option\<close> where
  \<open>m_int s = (let k = sign_len s; n = count_digits (drop k s) in
     if 0 < n then Some (k + n) else None)\<close>

text \<open>\<open>'-'? digit+ '.' digit*\<close>\<close>

definition m_rat :: \<open>string \<Rightarrow> nat option\<close> where
  \<open>m_rat s = (let k = sign_len s; n = count_digits (drop k s) in
     if 0 < n \<and> k + n < length s \<and> s ! (k + n) = CHR ''.''
     then Some (k + n + 1 + count_digits (drop (k + n + 1) s)) else None)\<close>

text \<open>The body of a quoted string after the opening quote:
  \<open>([^ '"' '\\'] | '\\' _)* '"'\<close>.\<close>

fun q_body :: \<open>string \<Rightarrow> nat option\<close> where
  \<open>q_body [] = None\<close>
| \<open>q_body (c # s) =
     (if c = CHR 0x22 then Some 1
      else if c = CHR 0x5C then (case s of [] \<Rightarrow> None | _ # s' \<Rightarrow> map_option (\<lambda>n. n + 2) (q_body s'))
      else map_option Suc (q_body s))\<close>

definition m_quoted :: \<open>string \<Rightarrow> nat option\<close> where
  \<open>m_quoted s = (case s of c # s' \<Rightarrow> if c = CHR 0x22 then map_option Suc (q_body s') else None
     | [] \<Rightarrow> None)\<close>

definition m_regexp :: \<open>string \<Rightarrow> nat option\<close> where
  \<open>m_regexp s = (case s of c # s' \<Rightarrow> if c = CHR ''r'' then map_option Suc (m_quoted s') else None
     | [] \<Rightarrow> None)\<close>

text \<open>\<open>(letter | digit | '_') (letter | digit | '_' | '-' | '/' | ':' | '\'' | '"')*\<close>\<close>

definition m_string :: \<open>string \<Rightarrow> nat option\<close> where
  \<open>m_string s = (case s of c # s' \<Rightarrow>
     if is_str_start c then Some (Suc (length (takeWhile is_str_char s'))) else None
     | [] \<Rightarrow> None)\<close>

definition m_space :: \<open>string \<Rightarrow> nat option\<close> where
  \<open>m_space s = (case s of c # _ \<Rightarrow> if is_space c then Some 1 else None | [] \<Rightarrow> None)\<close>

subsection \<open>Rules\<close>

datatype action = Emit mtok | Skip | Comment | LineComment | EmitTU

text \<open>The rules in the order of \<^file>\<open>../../src/formula_lexer.mll\<close>.\<close>

definition keywords :: \<open>(string \<times> mtok) list\<close> where
  \<open>keywords =
    [(''+'', PLUS), (''-'', MINUS), (''.'', DOT), (''*'', STAR), (''/'', SLASH),
     (''('', LPA), ('')'', RPA), (''['', LSB), ('']'', RSB),
     (''|>'', FREX), ([CHR 0xE2, CHR 0x96, CHR 0xB7], FREX), (''FORWARD'', FREX), (''MATCHF'', FREX),
     (''<|'', PREX), ([CHR 0xE2, CHR 0x97, CHR 0x81], PREX), (''BACKWARD'', PREX), (''MATCHP'', PREX),
     (''|'', BAR), ('','', COM), ('';'', SC), (''?'', QM), (''_'', LD), (''<-'', LARROW),
     (''<='', LESSEQ), (''SUBSTRING'', SUBSTRING), (''MATCHES'', MATCHES),
     (''r2s'', R2S), (''s2r'', S2R), (''<'', LESS), (''>='', GTREQ), (''>'', GTR), (''='', EQ),
     (''MOD'', MOD), (''f2i'', F2I), (''i2f'', I2F), (''i2s'', I2S), (''s2i'', S2I),
     (''f2s'', F2S), (''s2f'', S2F), (''DAY_OF_MONTH'', DAY_OF_MONTH), (''MONTH'', MONTH),
     (''YEAR'', YEAR), (''FORMAT_DATE'', FORMAT_DATE), (''FALSE'', FALSE), (''TRUE'', TRUE),
     (''LET'', LET), (''LETPAST'', LETPAST), (''FRZ'', FRZ), (''IN'', IN), (''NOT'', NOT),
     (''AND'', AND), (''OR'', OR), (''IMPLIES'', IMPL), (''EQUIV'', EQUIV), (''EXISTS'', EXISTS),
     (''FORALL'', FORALL), (''PREV'', PREV), (''PREVIOUS'', PREV), (''NEXT'', NEXT),
     (''EVENTUALLY'', EVENTUALLY), (''SOMETIMES'', EVENTUALLY), (''ONCE'', ONCE),
     (''ALWAYS'', ALWAYS), (''PAST_ALWAYS'', PAST_ALWAYS), (''HISTORICALLY'', PAST_ALWAYS),
     (''SINCE'', SINCE), (''TRIGGER'', TRIGGER), (''UNTIL'', UNTIL), (''RELEASE'', RELEASE),
     (''CNT'', CNT), (''MIN'', MIN_KW), (''MAX'', MAX_KW), (''SUM'', SUM_KW), (''AVG'', AVG), (''MED'', MED)]\<close>

definition rules :: \<open>((string \<Rightarrow> nat option) \<times> action) list\<close> where
  \<open>rules =
    [(m_space, Skip)] @
    map (\<lambda>(k, t). (m_fixed k, Emit t)) keywords @
    [(m_unit, EmitTU), (m_int, Emit INTEGER), (m_rat, Emit RAT), (m_quoted, Emit STR_CST),
     (m_regexp, Emit REGEXP_CST), (m_string, Emit NAME),
     (m_fixed ''(*'', Comment), (m_fixed ''#'', LineComment)]\<close>

text \<open>The longest match, the first rule among equally long ones.\<close>

fun best_match :: \<open>(nat \<times> action) option \<Rightarrow> ((string \<Rightarrow> nat option) \<times> action) list \<Rightarrow> string \<Rightarrow>
    (nat \<times> action) option\<close> where
  \<open>best_match b [] s = b\<close>
| \<open>best_match b ((m, a) # rs) s = best_match
     (case m s of None \<Rightarrow> b
      | Some n \<Rightarrow> (case b of None \<Rightarrow> Some (n, a) | Some (n', _) \<Rightarrow> if n' < n then Some (n, a) else b))
     rs s\<close>

text \<open>Position of the end of the first \<open>*)\<close>.\<close>

fun comment_end :: \<open>string \<Rightarrow> nat option\<close> where
  \<open>comment_end (c # d # s) =
     (if c = CHR ''*'' \<and> d = CHR '')'' then Some 2 else map_option Suc (comment_end (d # s)))\<close>
| \<open>comment_end _ = None\<close>

definition line_end :: \<open>string \<Rightarrow> nat\<close> where
  \<open>line_end s = (let n = length (takeWhile (\<lambda>c. c \<noteq> CHR 0x0A \<and> c \<noteq> CHR 0x0D) s) in
     if n < length s then Suc n else n)\<close>

definition mk_token :: \<open>mtok \<Rightarrow> nat \<Rightarrow> string \<Rightarrow> mtoken\<close> where
  \<open>mk_token t off lx = \<lparr>tok = t, span = \<lparr>s_line = 0, s_col = off, s_off = off,
     s_len = length lx, s_txt = lx\<rparr>\<rparr>\<close>

definition valid_unit :: \<open>string \<Rightarrow> bool\<close> where
  \<open>valid_unit lx = (last lx \<in> set ''dhms'')\<close>

text \<open>Every step consumes at least one character, so the input length bounds
  the recursion (\<open>fuel\<close>).\<close>

fun lex_aux :: \<open>nat \<Rightarrow> nat \<Rightarrow> string \<Rightarrow> mtoken list option\<close> where
  \<open>lex_aux _ _ [] = Some []\<close>
| \<open>lex_aux 0 _ _ = None\<close>
| \<open>lex_aux (Suc fuel) off s =
    (case best_match None rules s of
      None \<Rightarrow> None
    | Some (n, a) \<Rightarrow>
        let lx = take n s; rest = drop n s in
        (case a of
          Emit t \<Rightarrow> map_option ((#) (mk_token t off lx)) (lex_aux fuel (off + n) rest)
        | EmitTU \<Rightarrow> if valid_unit lx
            then map_option ((#) (mk_token TU off lx)) (lex_aux fuel (off + n) rest) else None
        | Skip \<Rightarrow> lex_aux fuel (off + n) rest
        | Comment \<Rightarrow> (case comment_end rest of
            None \<Rightarrow> None
          | Some k \<Rightarrow> lex_aux fuel (off + n + k) (drop k rest))
        | LineComment \<Rightarrow> let k = line_end rest in lex_aux fuel (off + n + k) (drop k rest)))\<close>

definition lex :: \<open>string \<Rightarrow> mtoken list option\<close> where
  \<open>lex s = lex_aux (length s) 0 s\<close>

end
