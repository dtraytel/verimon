theory MFODL_Lexer
  imports MFODL_Grammar.MFODL_Grammar TIGER_Lexer.Lexer_Command
begin

section \<open>Lexer of MFODL formulas\<close>

text \<open>MonPoly's formula lexer as a specification of the \<^theory_text>\<open>lexer\<close> command of TIGER: longest
  match, ties by rule order, bytes as characters. The rules are those of
  \<^verbatim>\<open>src/formula_lexer.mll\<close> of MonPoly, in its order. Unlike MonPoly, it rejects time units
  other than \<open>d\<close>, \<open>h\<close>, \<open>m\<close> and \<open>s\<close>. Comments \<open>(* \<dots> *)\<close> do not nest.\<close>

text \<open>A guard reads the lexeme as codepoints.\<close>

definition valid_unit :: \<open>nat list \<Rightarrow> bool\<close> where
  \<open>valid_unit u = (last u \<in> of_char ` set ''dhms'')\<close>

lexer (char) mfodl_lexer :: \<open>mtok\<close>
  modes Main Comment
  exclusive Comment
  where digit = \<open>[0-9]\<close> | letter = \<open>[a-zA-Z]\<close>
  | str_start = \<open>letter | digit | [_]\<close>
  | str_char = \<open>str_start | [\-/:'"]\<close>
  | quoted = \<open>"\"" ([^"\\] | "\\" _)* "\""\<close>
  rules
    \<open>[ ] | "\t" | "\n" | "\r"\<close> \<Rightarrow> skip
  | "+" \<Rightarrow> PLUS | "-" \<Rightarrow> MINUS | "." \<Rightarrow> DOT | "*" \<Rightarrow> STAR | "/" \<Rightarrow> SLASH
  | "(" \<Rightarrow> LPA | ")" \<Rightarrow> RPA | "[" \<Rightarrow> LSB | "]" \<Rightarrow> RSB
  | "|>" \<Rightarrow> FREX | \<open>"\u{E2}\u{96}\u{B7}"\<close> \<Rightarrow> FREX | "FORWARD" \<Rightarrow> FREX | "MATCHF" \<Rightarrow> FREX
  | \<open>"<|"\<close> \<Rightarrow> PREX | \<open>"\u{E2}\u{97}\u{81}"\<close> \<Rightarrow> PREX | "BACKWARD" \<Rightarrow> PREX | "MATCHP" \<Rightarrow> PREX
  | "|" \<Rightarrow> BAR | "," \<Rightarrow> COM | ";" \<Rightarrow> SC | "?" \<Rightarrow> QM | "_" \<Rightarrow> LD | \<open>"<-"\<close> \<Rightarrow> LARROW
  | \<open>"<="\<close> \<Rightarrow> LESSEQ | "SUBSTRING" \<Rightarrow> SUBSTRING | "MATCHES" \<Rightarrow> MATCHES
  | "r2s" \<Rightarrow> R2S | "s2r" \<Rightarrow> S2R | \<open>"<"\<close> \<Rightarrow> LESS | ">=" \<Rightarrow> GTREQ | ">" \<Rightarrow> GTR | "=" \<Rightarrow> EQ
  | "MOD" \<Rightarrow> MOD | "f2i" \<Rightarrow> F2I | "i2f" \<Rightarrow> I2F | "i2s" \<Rightarrow> I2S | "s2i" \<Rightarrow> S2I
  | "f2s" \<Rightarrow> F2S | "s2f" \<Rightarrow> S2F | "DAY_OF_MONTH" \<Rightarrow> DAY_OF_MONTH | "MONTH" \<Rightarrow> MONTH
  | "YEAR" \<Rightarrow> YEAR | "FORMAT_DATE" \<Rightarrow> FORMAT_DATE | "FALSE" \<Rightarrow> FALSE | "TRUE" \<Rightarrow> TRUE
  | "LET" \<Rightarrow> LET | "LETPAST" \<Rightarrow> LETPAST | "FRZ" \<Rightarrow> FRZ | "IN" \<Rightarrow> IN | "NOT" \<Rightarrow> NOT
  | "AND" \<Rightarrow> AND | "OR" \<Rightarrow> OR | "IMPLIES" \<Rightarrow> IMPL | "EQUIV" \<Rightarrow> EQUIV | "EXISTS" \<Rightarrow> EXISTS
  | "FORALL" \<Rightarrow> FORALL | "PREV" \<Rightarrow> PREV | "PREVIOUS" \<Rightarrow> PREV | "NEXT" \<Rightarrow> NEXT
  | "EVENTUALLY" \<Rightarrow> EVENTUALLY | "SOMETIMES" \<Rightarrow> EVENTUALLY | "ONCE" \<Rightarrow> ONCE
  | "ALWAYS" \<Rightarrow> ALWAYS | "PAST_ALWAYS" \<Rightarrow> PAST_ALWAYS | "HISTORICALLY" \<Rightarrow> PAST_ALWAYS
  | "SINCE" \<Rightarrow> SINCE | "TRIGGER" \<Rightarrow> TRIGGER | "UNTIL" \<Rightarrow> UNTIL | "RELEASE" \<Rightarrow> RELEASE
  | "CNT" \<Rightarrow> CNT | "MIN" \<Rightarrow> MIN_KW | "MAX" \<Rightarrow> MAX_KW | "SUM" \<Rightarrow> SUM_KW | "AVG" \<Rightarrow> AVG | "MED" \<Rightarrow> MED
  | \<open>digit+ letter\<close> \<Rightarrow> TU when valid_unit
  | \<open>"-"? digit+\<close> \<Rightarrow> INTEGER
  | \<open>"-"? digit+ "." digit*\<close> \<Rightarrow> RAT
  | \<open>quoted\<close> \<Rightarrow> STR_CST
  | \<open>"r" quoted\<close> \<Rightarrow> REGEXP_CST
  | \<open>str_start str_char*\<close> \<Rightarrow> NAME
  | "(*" \<Rightarrow> skip, begin Comment
  | \<open>"#" [^\n\r]* ("\n" | "\r")?\<close> \<Rightarrow> skip
  | <Comment> (
      "*)" \<Rightarrow> skip, begin Main
    | \<open>[^*]+ | "*"\<close> \<Rightarrow> skip
  )

text \<open>The lexer succeeds if it consumes the input and stops outside a comment. The parser reads
  the tokens without their trailing trivia.\<close>

text \<open>The final modes without a set, which VeriMon's code under \<open>Containers\<close> cannot compile
  for a mode type without \<open>ceq\<close> and \<open>ccompare\<close> instances:\<close>

lemma mfodl_lexer_final_code [code]: \<open>mfodl_lexer.final m = (m = Main)\<close>
  by (simp add: mfodl_lexer.final_def)

definition lex :: \<open>string \<Rightarrow> mtoken list option\<close> where
  \<open>lex s = (case mfodl_lexer_lex s of (l, r, st) \<Rightarrow>
     if r = [] \<and> mfodl_lexer.final (hd st) then Some (map token.truncate (toks l)) else None)\<close>

lemma lex_Some_iff_ok: \<open>(\<exists>w. lex s = Some w) \<longleftrightarrow> mfodl_lexer_lex.ok s\<close>
  unfolding lex_def mfodl_lexer_lex.ok_def by (auto split: prod.splits)

text \<open>\<^const>\<open>lex\<close> computes the lexing judgment of the specification, read on bytes, from the
  start mode at the first position, with nothing left over and outside a comment:\<close>

theorem lex_correct:
  \<open>lex s = Some w \<longleftrightarrow>
    (\<exists>l st. char_cls.lexes (char_spec mfodl_lexer.spec) (\<lambda>c. mfodl_lexer.is_newline (of_char c))
       [mfodl_lexer.start] \<lparr>line = 0, col = 0, off = 0\<rparr> s l [] st \<and>
     mfodl_lexer.final (hd st) \<and> w = map token.truncate (toks l))\<close>
proof -
  obtain l r st where L: \<open>mfodl_lexer_lex s = (l, r, st)\<close>
    by (cases \<open>mfodl_lexer_lex s\<close>)
  have \<open>char_cls.lexes (char_spec mfodl_lexer.spec) (\<lambda>c. mfodl_lexer.is_newline (of_char c))
      [mfodl_lexer.start] \<lparr>line = 0, col = 0, off = 0\<rparr> s l' r' st' \<longleftrightarrow> (l', r', st') = (l, r, st)\<close>
    for l' r' st'
    using mfodl_lexer_lex.correct[of s l' r' st'] L by auto
  then show ?thesis
    unfolding lex_def L by auto
qed

end
