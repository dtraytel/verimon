(*<*)
theory Log_Lexer
  imports Log_Grammar
begin
(*>*)

section \<open>The lexer\<close>

text \<open>
  The lexer is an automaton that reads one character at a time and emits the tokens that the
  character completes. Its states record the lexeme being read: nothing (@{text L_INIT}), a
  simple string, the content of a quoted string (after an optional backslash), or a comment.
  This is the automaton of Rappl's lexer, extended by escapes, @{text "r\"\<dots>\""} strings,
  braces, and a final step @{text lex_finish} for the end of the input. Unlike the automaton
  of MonPoly's lexer, it never backtracks: an unterminated quoted string is only detected at the
  end of the input, and contains the rest of the input. (MonPoly's lexer reads a quote that no
  quote follows as a character that begins no token, and continues after it.)
\<close>

datatype lstate = L_INIT | L_SIMPLE string | L_QUOTED string | L_ESCAPE string | L_COMMENT

definition lex_init :: "char \<Rightarrow> (string token list \<times> lstate) option" where
  "lex_init c =
    (if isWhiteSpace c then Some ([], L_INIT)
     else if c = CHR ''@'' then Some ([T_AT], L_INIT)
     else if c = CHR ''('' then Some ([T_LPAREN], L_INIT)
     else if c = CHR '')'' then Some ([T_RPAREN], L_INIT)
     else if c = CHR ''<'' then Some ([T_LANGLE], L_INIT)
     else if c = CHR ''>'' then Some ([T_RANGLE], L_INIT)
     else if c = CHR ''{'' then Some ([T_LBRACE], L_INIT)
     else if c = CHR ''}'' then Some ([T_RBRACE], L_INIT)
     else if c = CHR '','' then Some ([T_COMMA], L_INIT)
     else if c = CHR '';'' then Some ([T_SEMICOLON], L_INIT)
     else if c = CHR ''#'' then Some ([], L_COMMENT)
     else if c = CHR 0x22 then Some ([], L_QUOTED [])
     else if isSimpleChar c then Some ([], L_SIMPLE [c])
     else None)"

fun lex_step :: "char \<Rightarrow> lstate \<Rightarrow> (string token list \<times> lstate) option" where
  "lex_step c L_INIT = lex_init c"
| "lex_step c (L_SIMPLE s) =
    (if isSimpleChar c then Some ([], L_SIMPLE (s @ [c]))
     else if c = CHR 0x22 \<and> s = ''r'' then Some ([], L_QUOTED [])
     else map_option (apfst (Cons (T_STR s))) (lex_init c))"
| "lex_step c (L_QUOTED s) =
    (if c = CHR 0x22 then Some ([T_STR s], L_INIT)
     else if c = CHR 0x5C then Some ([], L_ESCAPE (s @ [c]))
     else Some ([], L_QUOTED (s @ [c])))"
| "lex_step c (L_ESCAPE s) = Some ([], L_QUOTED (s @ [c]))"
| "lex_step c L_COMMENT = (if isLineCommentEnd c then Some ([], L_INIT) else Some ([], L_COMMENT))"

fun lex_run :: "string \<Rightarrow> lstate \<Rightarrow> (string token list \<times> lstate) option" where
  "lex_run [] l = Some ([], l)"
| "lex_run (c # s) l = (case lex_step c l of
     None \<Rightarrow> None
   | Some (ts, l') \<Rightarrow> map_option (apfst ((@) ts)) (lex_run s l'))"

fun lex_finish :: "lstate \<Rightarrow> string token list option" where
  "lex_finish L_INIT = Some []"
| "lex_finish (L_SIMPLE s) = Some [T_STR s]"
| "lex_finish (L_QUOTED s) = None"
| "lex_finish (L_ESCAPE s) = None"
| "lex_finish L_COMMENT = Some []"

definition lex :: "string \<Rightarrow> string token list option" where
  "lex s = (case lex_run s L_INIT of None \<Rightarrow> None | Some (ts, l) \<Rightarrow> map_option ((@) ts) (lex_finish l))"

subsection \<open>Basic properties\<close>

lemma lex_run_append:
  "lex_run (s @ s') l = (case lex_run s l of
     None \<Rightarrow> None
   | Some (ts, l') \<Rightarrow> map_option (apfst ((@) ts)) (lex_run s' l'))"
  by (induction s arbitrary: l) (auto split: option.splits)

lemma lex_run_Cons_Some:
  "lex_step c l = Some (ts, l') \<Longrightarrow> lex_run (c # s) l = map_option (apfst ((@) ts)) (lex_run s l')"
  by simp

subsection \<open>Properties of the lexical grammar\<close>

lemma isWhiteString_append: "isWhiteString w \<Longrightarrow> isWhiteString w' \<Longrightarrow> isWhiteString (w @ w')"
  by (induction w rule: isWhiteString.induct) (auto intro: isWhiteString.intros)

lemma isWhiteString_comment:
  "list_all (Not \<circ> isLineCommentEnd) s \<Longrightarrow> isLineCommentEnd c \<Longrightarrow> isWhiteString (CHR ''#'' # s @ [c])"
  using isWS_Comment[OF _ _ isWS_Nil] by simp

lemma isQuoted_snoc: "isQuoted q \<Longrightarrow> c \<noteq> CHR 0x22 \<Longrightarrow> c \<noteq> CHR 0x5C \<Longrightarrow> isQuoted (q @ [c])"
  by (induction rule: isQuoted.induct) (auto intro: isQuoted.intros)

lemma isQuoted_snoc_escape: "isQuoted q \<Longrightarrow> isQuoted (q @ [CHR 0x5C, c])"
  by (induction rule: isQuoted.induct) (auto intro: isQuoted.intros)

lemma GToken_nonempty: "GToken s t \<Longrightarrow> s \<noteq> []"
  by (cases rule: GToken.cases) auto

lemma Glex_Nil_iff[simp]: "Glex [] ts \<longleftrightarrow> ts = []"
  by (auto elim: Glex.cases dest: GToken_nonempty intro: Glex_WS isWS_Nil)

lemma Glex_white_prepend:
  assumes "isWhiteString w" "Glex s ts"
  shows "Glex (w @ s) ts"
  using assms(2)
proof cases
  case Glex_WS
  then show ?thesis
    using assms(1) by (auto intro: Glex.Glex_WS isWhiteString_append)
next
  case (Glex_Token w' s1 t s2 ts')
  then show ?thesis
    using Glex.Glex_Token[OF isWhiteString_append[OF assms(1)], of w' s1 t s2 ts'] by simp
qed

lemma Glex_single: "GToken s1 t \<Longrightarrow> \<not> isSimpleString s1 \<Longrightarrow> Glex s2 ts \<Longrightarrow> Glex (s1 @ s2) (t # ts)"
  using Glex_Token[of "[]" s1 t s2 ts] by (auto simp add: isWS_Nil munch_def)

subsection \<open>Soundness\<close>

text \<open>@{text "Glex_then s ts P"}: the input @{text s} read so far lexes to @{text ts} and may be
  continued by every lexable input whose first character satisfies @{text P}. This is how the
  invariant of the lexer below states that the tokens emitted so far are right while the next
  lexeme is still incomplete; @{text P} captures the maximal munch condition at the boundary.\<close>

definition Glex_then :: "string \<Rightarrow> string token list \<Rightarrow> (char \<Rightarrow> bool) \<Rightarrow> bool" where
  "Glex_then s ts P \<longleftrightarrow> (\<forall>s' ts'. Glex s' ts' \<longrightarrow> (s' \<noteq> [] \<longrightarrow> P (hd s')) \<longrightarrow> Glex (s @ s') (ts @ ts'))"

lemma Glex_thenD: "Glex_then s ts P \<Longrightarrow> Glex s' ts' \<Longrightarrow> (s' \<noteq> [] \<Longrightarrow> P (hd s')) \<Longrightarrow> Glex (s @ s') (ts @ ts')"
  unfolding Glex_then_def by blast

lemma Glex_then_Glex: "Glex_then s ts P \<Longrightarrow> Glex s ts"
  using Glex_thenD[of s ts P "[]" "[]"] by simp

lemma Glex_then_mono: "Glex_then s ts P \<Longrightarrow> (\<And>c. Q c \<Longrightarrow> P c) \<Longrightarrow> Glex_then s ts Q"
  unfolding Glex_then_def by blast

lemma Glex_then_Nil: "Glex_then [] [] P"
  unfolding Glex_then_def by simp

lemma Glex_then_extend:
  assumes "Glex_then s ts P" "w \<noteq> []" "P (hd w)" "\<And>s' ts'. Glex s' ts' \<Longrightarrow> Glex (w @ s') (tw @ ts')"
  shows "Glex_then (s @ w) (ts @ tw) Q"
  unfolding Glex_then_def
proof (intro allI impI)
  fix s' ts'
  assume "Glex s' ts'"
  then have "Glex (w @ s') (tw @ ts')"
    by (rule assms(4))
  with assms(1-3) show "Glex ((s @ w) @ s') ((ts @ tw) @ ts')"
    by (auto dest: Glex_thenD)
qed

lemma Glex_then_simple:
  assumes "Glex_then s ts (\<lambda>c. c = hd x)" "isSimpleString x"
    and "\<And>c. P c \<Longrightarrow> \<not> isSimpleChar c \<and> (x = ''r'' \<longrightarrow> c \<noteq> CHR 0x22)"
  shows "Glex_then (s @ x) (ts @ [T_STR x]) P"
  unfolding Glex_then_def
proof (intro allI impI)
  fix s' ts'
  assume "Glex s' ts'" "s' \<noteq> [] \<longrightarrow> P (hd s')"
  with assms(2,3) have "Glex (x @ s') (T_STR x # ts')"
    using Glex_Token[of "[]" x "T_STR x" s' ts'] by (auto simp: isWS_Nil munch_def intro: GToken_simple)
  with assms(1,2) show "Glex ((s @ x) @ s') ((ts @ [T_STR x]) @ ts')"
    by (auto dest: Glex_thenD)
qed

definition quote_prefix :: "string \<Rightarrow> bool" where
  "quote_prefix pre \<longleftrightarrow> pre = [CHR 0x22] \<or> pre = [CHR ''r'', CHR 0x22]"

lemma GToken_quote_prefix: "quote_prefix pre \<Longrightarrow> isQuoted q \<Longrightarrow> GToken (pre @ q @ [CHR 0x22]) (T_STR q)"
  by (auto simp: quote_prefix_def intro: GToken_quoted GToken_rquoted)

text \<open>The invariant: the input read so far consists of a prefix that lexes to the tokens emitted
  so far, followed by the incomplete lexeme recorded in the state.\<close>

fun lex_inv :: "string \<Rightarrow> string token list \<Rightarrow> lstate \<Rightarrow> bool" where
  "lex_inv s ts L_INIT \<longleftrightarrow> Glex_then s ts (\<lambda>_. True)"
| "lex_inv s ts (L_SIMPLE x) \<longleftrightarrow>
    (\<exists>s0. s = s0 @ x \<and> isSimpleString x \<and> Glex_then s0 ts (\<lambda>c. c = hd x))"
| "lex_inv s ts (L_QUOTED q) \<longleftrightarrow>
    (\<exists>s0 pre. s = s0 @ pre @ q \<and> quote_prefix pre \<and> isQuoted q \<and> Glex_then s0 ts (\<lambda>c. c = hd pre))"
| "lex_inv s ts (L_ESCAPE q) \<longleftrightarrow> (\<exists>s0 pre q0. s = s0 @ pre @ q \<and> q = q0 @ [CHR 0x5C] \<and>
    quote_prefix pre \<and> isQuoted q0 \<and> Glex_then s0 ts (\<lambda>c. c = hd pre))"
| "lex_inv s ts L_COMMENT \<longleftrightarrow> (\<exists>s0 d. s = s0 @ CHR ''#'' # d \<and> list_all (Not \<circ> isLineCommentEnd) d \<and>
    Glex_then s0 ts (\<lambda>c. c = CHR ''#''))"

lemma Glex_then_white:
  "Glex_then s ts P \<Longrightarrow> P c \<Longrightarrow> isWhiteSpace c \<Longrightarrow> Glex_then (s @ [c]) ts Q"
  using Glex_then_extend[of s ts P "[c]" "[]" Q] Glex_white_prepend[of "[c]"] isWS_Space[OF _ isWS_Nil]
  by auto

lemma Glex_then_punct:
  "Glex_then s ts P \<Longrightarrow> P c \<Longrightarrow> GToken [c] t \<Longrightarrow> \<not> isSimpleChar c \<Longrightarrow> Glex_then (s @ [c]) (ts @ [t]) Q"
  using Glex_then_extend[of s ts P "[c]" "[t]" Q] Glex_single[of "[c]" t] by auto

lemma special_not_simple[simp]:
  "\<not> isSimpleChar CHR ''@''" "\<not> isSimpleChar CHR ''(''" "\<not> isSimpleChar CHR '')''"
  "\<not> isSimpleChar CHR ''<''" "\<not> isSimpleChar CHR ''>''" "\<not> isSimpleChar CHR ''{''"
  "\<not> isSimpleChar CHR ''}''" "\<not> isSimpleChar CHR '',''" "\<not> isSimpleChar CHR '';''"
  "\<not> isSimpleChar CHR ''#''" "\<not> isSimpleChar CHR 0x22"
  by (simp_all add: isSimpleChar_def)

lemma white_not_simple: "isWhiteSpace c \<Longrightarrow> \<not> isSimpleChar c"
  by (auto simp: isWhiteSpace_def isSimpleChar_def)

lemma line_end_not_simple: "isLineCommentEnd c \<Longrightarrow> \<not> isSimpleChar c"
  by (auto simp: isLineCommentEnd_def isSimpleChar_def)

lemma lex_init_cases:
  assumes "lex_init c = Some (ts, l)"
  obtains (white) "isWhiteSpace c" "ts = []" "l = L_INIT"
  | (punct) t where "GToken [c] t" "\<not> isSimpleChar c" "ts = [t]" "l = L_INIT"
  | (comment) "c = CHR ''#''" "ts = []" "l = L_COMMENT"
  | (quote) "c = CHR 0x22" "ts = []" "l = L_QUOTED []"
  | (simple) "isSimpleChar c" "ts = []" "l = L_SIMPLE [c]"
  using assms unfolding lex_init_def
  by (auto split: if_splits intro: GToken.intros)

lemma lex_inv_simpleI:
  "s = u @ x \<Longrightarrow> isSimpleString x \<Longrightarrow> Glex_then u ts (\<lambda>c. c = hd x) \<Longrightarrow> lex_inv s ts (L_SIMPLE x)"
  by auto

lemma lex_inv_quotedI: "s = u @ pre @ q \<Longrightarrow> quote_prefix pre \<Longrightarrow> isQuoted q \<Longrightarrow>
  Glex_then u ts (\<lambda>c. c = hd pre) \<Longrightarrow> lex_inv s ts (L_QUOTED q)"
  by auto

lemma lex_inv_escapeI: "s = u @ pre @ q @ [CHR 0x5C] \<Longrightarrow> quote_prefix pre \<Longrightarrow> isQuoted q \<Longrightarrow>
  Glex_then u ts (\<lambda>c. c = hd pre) \<Longrightarrow> lex_inv s ts (L_ESCAPE (q @ [CHR 0x5C]))"
  by auto

lemma lex_inv_commentI: "s = u @ CHR ''#'' # d \<Longrightarrow> list_all (Not \<circ> isLineCommentEnd) d \<Longrightarrow>
  Glex_then u ts (\<lambda>c. c = CHR ''#'') \<Longrightarrow> lex_inv s ts L_COMMENT"
  by auto

lemma lex_init_inv:
  assumes G: "Glex_then s ts P" and c: "P c" and step: "lex_init c = Some (ts', l')"
  shows "lex_inv (s @ [c]) (ts @ ts') l'"
  using step
proof (cases rule: lex_init_cases)
  case white
  then show ?thesis using Glex_then_white[OF G c] by simp
next
  case (punct t)
  then show ?thesis using Glex_then_punct[OF G c] by simp
next
  case comment
  from G c comment(1) have G': "Glex_then s ts (\<lambda>d. d = CHR ''#'')"
    by (auto elim: Glex_then_mono)
  show ?thesis
    unfolding comment by (rule lex_inv_commentI[where u=s and d="[]"]) (auto intro: G')
next
  case quote
  from G c quote(1) have G': "Glex_then s ts (\<lambda>d. d = CHR 0x22)"
    by (auto elim: Glex_then_mono)
  show ?thesis
    unfolding quote by (rule lex_inv_quotedI[where u=s and pre="[CHR 0x22]"])
      (auto simp: quote_prefix_def intro: isQuoted_Nil G')
next
  case simple
  from G c have G': "Glex_then s ts (\<lambda>d. d = c)"
    by (auto elim: Glex_then_mono)
  show ?thesis
    unfolding simple by (rule lex_inv_simpleI[where u=s]) (auto simp: simple intro: G')
qed

lemma lex_step_inv:
  assumes inv: "lex_inv s ts l" and step: "lex_step c l = Some (ts', l')"
  shows "lex_inv (s @ [c]) (ts @ ts') l'"
proof (cases l)
  case L_INIT
  with inv step show ?thesis
    by (auto intro: lex_init_inv)
next
  case (L_SIMPLE x)
  with inv obtain u where s: "s = u @ x" and x: "isSimpleString x" and G: "Glex_then u ts (\<lambda>d. d = hd x)"
    by auto
  consider (more) "isSimpleChar c" | (rquote) "\<not> isSimpleChar c" "c = CHR 0x22" "x = ''r''"
    | (close) "\<not> isSimpleChar c" "\<not> (c = CHR 0x22 \<and> x = ''r'')"
    by blast
  then show ?thesis
  proof cases
    case more
    with step L_SIMPLE have "ts' = []" "l' = L_SIMPLE (x @ [c])"
      by auto
    with more x G s show ?thesis
      by (auto intro!: lex_inv_simpleI[where u=u])
  next
    case rquote
    with step L_SIMPLE have ts': "ts' = []" "l' = L_QUOTED []"
      by auto
    show ?thesis
      unfolding ts' by (rule lex_inv_quotedI[where u=u and pre="[CHR ''r'', CHR 0x22]"])
        (use rquote G s in \<open>auto simp: quote_prefix_def intro: isQuoted_Nil\<close>)
  next
    case close
    with step L_SIMPLE obtain ts'' where init: "lex_init c = Some (ts'', l')" and ts': "ts' = T_STR x # ts''"
      by (auto split: if_splits)
    have "Glex_then (u @ x) (ts @ [T_STR x]) (\<lambda>d. d = c)"
      using G x close by (intro Glex_then_simple) auto
    from lex_init_inv[OF this _ init] s ts' show ?thesis
      by simp
  qed
next
  case (L_QUOTED q)
  with inv obtain u pre where s: "s = u @ pre @ q" and pre: "quote_prefix pre" and q: "isQuoted q"
    and G: "Glex_then u ts (\<lambda>d. d = hd pre)"
    by auto
  consider (close) "c = CHR 0x22" | (esc) "c = CHR 0x5C" | (char) "c \<noteq> CHR 0x22" "c \<noteq> CHR 0x5C"
    by blast
  then show ?thesis
  proof cases
    case close
    with step L_QUOTED have ts': "ts' = [T_STR q]" "l' = L_INIT"
      by auto
    have "Glex_then (u @ (pre @ q @ [CHR 0x22])) (ts @ [T_STR q]) (\<lambda>_. True)"
    proof (rule Glex_then_extend[OF G])
      show "pre @ q @ [CHR 0x22] \<noteq> []" "hd (pre @ q @ [CHR 0x22]) = hd pre"
        using pre by (auto simp: quote_prefix_def)
      fix s' ts'
      assume "Glex s' ts'"
      then show "Glex ((pre @ q @ [CHR 0x22]) @ s') ([T_STR q] @ ts')"
        using Glex_single[OF GToken_quote_prefix[OF pre q]] by simp
    qed
    with s close ts' show ?thesis
      by simp
  next
    case esc
    with step L_QUOTED have "ts' = []" "l' = L_ESCAPE (q @ [CHR 0x5C])"
      by auto
    with esc s pre q G show ?thesis
      by (auto intro!: lex_inv_escapeI[where u=u])
  next
    case char
    with step L_QUOTED have "ts' = []" "l' = L_QUOTED (q @ [c])"
      by auto
    with char s pre q G show ?thesis
      by (auto intro!: lex_inv_quotedI[where u=u] isQuoted_snoc)
  qed
next
  case (L_ESCAPE q)
  with inv obtain u pre q0 where s: "s = u @ pre @ q" and q: "q = q0 @ [CHR 0x5C]" and pre: "quote_prefix pre"
    and q0: "isQuoted q0" and G: "Glex_then u ts (\<lambda>d. d = hd pre)"
    by auto
  from step L_ESCAPE q have "ts' = []" "l' = L_QUOTED (q0 @ [CHR 0x5C, c])"
    by auto
  with s q pre q0 G show ?thesis
    by (auto intro!: lex_inv_quotedI[where u=u] isQuoted_snoc_escape)
next
  case L_COMMENT
  with inv obtain u d where s: "s = u @ CHR ''#'' # d" and d: "list_all (Not \<circ> isLineCommentEnd) d"
    and G: "Glex_then u ts (\<lambda>c. c = CHR ''#'')"
    by auto
  show ?thesis
  proof (cases "isLineCommentEnd c")
    case True
    with step L_COMMENT have ts': "ts' = []" "l' = L_INIT"
      by auto
    have "Glex_then (u @ (CHR ''#'' # d @ [c])) (ts @ []) (\<lambda>_. True)"
    proof (rule Glex_then_extend[OF G])
      fix s' ts'
      assume "Glex s' ts'"
      then show "Glex ((CHR ''#'' # d @ [c]) @ s') ([] @ ts')"
        using Glex_white_prepend[OF isWhiteString_comment[OF d True]] by simp
    qed simp_all
    with s ts' show ?thesis
      by simp
  next
    case False
    with step L_COMMENT have ts': "ts' = []" "l' = L_COMMENT"
      by auto
    show ?thesis
      unfolding ts' by (rule lex_inv_commentI[where u=u and d="d @ [c]"]) (use False s d G in auto)
  qed
qed

lemma lex_run_inv: "lex_inv s ts l \<Longrightarrow> lex_run s' l = Some (ts', l') \<Longrightarrow> lex_inv (s @ s') (ts @ ts') l'"
proof (induction s' arbitrary: s ts l ts')
  case Nil
  then show ?case by simp
next
  case (Cons c s')
  from Cons.prems(2) obtain ts1 l1 ts2 where
    step: "lex_step c l = Some (ts1, l1)" and run: "lex_run s' l1 = Some (ts2, l')" and ts': "ts' = ts1 @ ts2"
    by (auto split: option.splits)
  from Cons.IH[OF lex_step_inv[OF Cons.prems(1) step] run] ts' show ?case
    by simp
qed

lemma lex_sound:
  assumes "lex s = Some ts"
  shows "lexes s ts"
proof -
  from assms obtain ts1 l ts2 where run: "lex_run s L_INIT = Some (ts1, l)"
    and fin: "lex_finish l = Some ts2" and ts: "ts = ts1 @ ts2"
    by (auto simp: lex_def split: option.splits)
  from lex_run_inv[of "[]" "[]" L_INIT, OF _ run] have inv: "lex_inv s ts1 l"
    by (simp add: Glex_then_Nil)
  show ?thesis
  proof (cases l)
    case L_INIT
    with inv fin ts show ?thesis
      by (auto simp: lexes_def dest: Glex_then_Glex)
  next
    case (L_SIMPLE x)
    with inv obtain s0 where s: "s = s0 @ x" and x: "isSimpleString x"
      and G: "Glex_then s0 ts1 (\<lambda>c. c = hd x)"
      by auto
    from x have "Glex (x @ []) [T_STR x]"
      using Glex_Token[of "[]" x "T_STR x" "[]" "[]"] by (auto simp: isWS_Nil munch_def intro: GToken_simple)
    with G x have "Glex (s0 @ x) (ts1 @ [T_STR x])"
      using Glex_thenD[of s0 ts1 _ x "[T_STR x]"] by auto
    with L_SIMPLE fin ts s show ?thesis
      by (simp add: lexes_def)
  next
    case L_COMMENT
    with inv fin ts show ?thesis
      by (auto simp: lexes_def dest: Glex_then_Glex)
  qed (use fin in auto)
qed

subsection \<open>Completeness\<close>

lemma simple_not_special:
  assumes "isSimpleChar c"
  shows "\<not> isWhiteSpace c" "c \<noteq> CHR ''@''" "c \<noteq> CHR ''(''" "c \<noteq> CHR '')''" "c \<noteq> CHR ''<''"
    "c \<noteq> CHR ''>''" "c \<noteq> CHR ''{''" "c \<noteq> CHR ''}''" "c \<noteq> CHR '',''" "c \<noteq> CHR '';''" "c \<noteq> CHR ''#''"
    "c \<noteq> CHR 0x22"
  using assms white_not_simple by fastforce+

lemma lex_init_simple: "isSimpleChar c \<Longrightarrow> lex_init c = Some ([], L_SIMPLE [c])"
  by (simp add: lex_init_def simple_not_special)

lemma lex_run_comment: "list_all (Not \<circ> isLineCommentEnd) d \<Longrightarrow> lex_run d L_COMMENT = Some ([], L_COMMENT)"
  by (induction d) auto

lemma lex_run_white: "isWhiteString w \<Longrightarrow> lex_run w L_INIT = Some ([], L_INIT)"
proof (induction rule: isWhiteString.induct)
  case (isWS_Space c s)
  then show ?case
    by (simp add: lex_init_def)
next
  case (isWS_Comment d c s')
  then show ?case
    by (simp add: lex_init_def isWhiteSpace_def lex_run_append lex_run_comment)
qed simp

lemma lex_run_simple: "list_all isSimpleChar y \<Longrightarrow> lex_run y (L_SIMPLE x) = Some ([], L_SIMPLE (x @ y))"
  by (induction y arbitrary: x) auto

lemma lex_run_quoted:
  "isQuoted q \<Longrightarrow>
   lex_run (q @ CHR 0x22 # r) (L_QUOTED p) = map_option (apfst ((@) [T_STR (p @ q)])) (lex_run r L_INIT)"
  by (induction q arbitrary: p rule: isQuoted.induct) auto

lemma lex_run_close_simple:
  "\<not> isSimpleChar c \<Longrightarrow> \<not> (c = CHR 0x22 \<and> x = ''r'') \<Longrightarrow>
   lex_run (c # r) (L_SIMPLE x) = map_option (apfst ((@) [T_STR x])) (lex_run (c # r) L_INIT)"
  by (auto split: option.splits)

lemma GToken_simpleD: "GToken s t \<Longrightarrow> isSimpleString s \<Longrightarrow> t = T_STR s"
  by (cases rule: GToken.cases) auto

lemma GToken_lex_run:
  "GToken s1 t \<Longrightarrow> \<not> isSimpleString s1 \<Longrightarrow>
   lex_run (s1 @ s2) L_INIT = map_option (apfst ((@) [t])) (lex_run s2 L_INIT)"
  by (cases rule: GToken.cases) (auto simp: lex_init_def isWhiteSpace_def isSimpleChar_def lex_run_quoted)

text \<open>How a lexable input leaves the lexer: in the initial state, or with a simple string as its
  last token not yet emitted.\<close>

definition lex_ends :: "string token list \<Rightarrow> string token list \<Rightarrow> lstate \<Rightarrow> bool" where
  "lex_ends ts ts1 l \<longleftrightarrow> l = L_INIT \<and> ts = ts1 \<or> (\<exists>x. l = L_SIMPLE x \<and> ts = ts1 @ [T_STR x])"

lemma Glex_lex_run: "Glex s ts \<Longrightarrow> \<exists>ts1 l. lex_run s L_INIT = Some (ts1, l) \<and> lex_ends ts ts1 l"
proof (induction rule: Glex.induct)
  case (Glex_WS w)
  then show ?case
    using lex_run_white by (auto simp: lex_ends_def)
next
  case (Glex_Token w s1 t s2 ts)
  from Glex_Token.IH obtain ts1 l where run2: "lex_run s2 L_INIT = Some (ts1, l)" and ends: "lex_ends ts ts1 l"
    by blast
  have "\<exists>ts1' l'. lex_run (s1 @ s2) L_INIT = Some (ts1', l') \<and> lex_ends (t # ts) ts1' l'"
  proof (cases "isSimpleString s1")
    case True
    with Glex_Token.hyps(2) have t: "t = T_STR s1"
      by (rule GToken_simpleD)
    from True obtain c y where s1: "s1 = c # y" and c: "isSimpleChar c" and y: "list_all isSimpleChar y"
      by (cases s1) auto
    have run1: "lex_run s1 L_INIT = Some ([], L_SIMPLE s1)"
      using c y by (simp add: s1 lex_init_simple lex_run_simple)
    show ?thesis
    proof (cases s2)
      case Nil
      with Glex_Token.hyps(4) have "ts = []"
        by simp
      with Nil run1 t show ?thesis
        by (auto simp: lex_ends_def)
    next
      case (Cons c' r)
      with Glex_Token.hyps(3) True have "\<not> isSimpleChar c'" "\<not> (c' = CHR 0x22 \<and> s1 = ''r'')"
        by (auto simp: munch_def)
      from lex_run_close_simple[OF this, of r] run1 run2 ends Cons t show ?thesis
        by (auto simp: lex_run_append lex_ends_def)
    qed
  next
    case False
    with GToken_lex_run[OF Glex_Token.hyps(2)] run2 ends show ?thesis
      by (auto simp: lex_ends_def)
  qed
  then show ?case
    using lex_run_white[OF Glex_Token.hyps(1)] by (auto simp: lex_run_append)
qed

lemma lex_complete:
  assumes "lexes s ts"
  shows "lex s = Some ts"
  using assms unfolding lexes_def
proof (elim disjE exE conjE)
  assume "Glex s ts"
  then show ?thesis
    by (auto simp: lex_def lex_ends_def dest!: Glex_lex_run)
next
  fix s1 d
  assume s: "s = s1 @ CHR ''#'' # d" and d: "list_all (Not \<circ> isLineCommentEnd) d" and G: "Glex s1 ts"
  from Glex_lex_run[OF G] obtain ts1 l where run: "lex_run s1 L_INIT = Some (ts1, l)" and ends: "lex_ends ts ts1 l"
    by blast
  from ends obtain ts2 where "lex_run (CHR ''#'' # d) l = Some (ts2, L_COMMENT)" "ts = ts1 @ ts2"
    by (auto simp: lex_ends_def lex_init_def isWhiteSpace_def lex_run_comment[OF d])
  with run s show ?thesis
    by (simp add: lex_def lex_run_append)
qed

theorem lex_correct: "lex s = Some ts \<longleftrightarrow> lexes s ts"
  using lex_sound lex_complete by blast

corollary lexes_unique: "lexes s ts \<Longrightarrow> lexes s ts' \<Longrightarrow> ts = ts'"
  by (simp flip: lex_correct)

(*<*)
end
(*>*)

