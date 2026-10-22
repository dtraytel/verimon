(*<*)
theory Signature_Reader
  imports Log_OCaml "MFODL_Syntax.String_Escape"
begin
(*>*)

section \<open>Reader of the signature file\<close>

text \<open>A recursive descent over the tokens of the verified log lexer that follows MonPoly's
  @{text Log_parser.parse_signature} and reports the same errors, in the same order.\<close>

subsection \<open>Strings and failures\<close>

text \<open>The characters of a byte string by the operations on byte strings, so that the code uses
  OCaml's.\<close>

definition string_of_bytes :: "bytes \<Rightarrow> string" where
  "string_of_bytes b = map (\<lambda>i. bytes_at b (integer_of_nat i)) [0..<nat_of_integer (bytes_length b)]"

lemma string_of_bytes[simp]: "string_of_bytes b = Rep_bytes b"
  by (simp add: string_of_bytes_def bytes_at_def bytes_length_def map_nth)

text \<open>An uncaught @{text Failure} as OCaml's runtime reports it, by which MonPoly ends on an error
  in the signature.\<close>

definition fatal_failure :: "string \<Rightarrow> string" where
  "fatal_failure msg = ''Fatal error: exception Failure('' @ CHR 0x22 # escaped msg @ CHR 0x22 # '')''"

subsection \<open>Grammar of signatures\<close>

inductive G_sig :: "'s token list \<Rightarrow> ('s \<times> 's list) list \<Rightarrow> bool" where
  G_sig_Nil: "G_sig [] []"
| G_sig_Cons: "G_tuple tu fs \<Longrightarrow> G_sig ts ds \<Longrightarrow> G_sig (T_STR p # tu @ ts) ((p, fs) # ds)"

definition sig_lang :: "string \<Rightarrow> (string \<times> string list) list \<Rightarrow> bool" where
  "sig_lang s ds \<longleftrightarrow> (\<exists>ts. lexes s ts \<and> G_sig ts ds)"

subsection \<open>Schemas\<close>

datatype sty = SInt | SStr | SFloat | SRegexp

type_synonym schema = "(string \<times> (string \<times> sty) list) list"

definition base_schema :: schema where
  "base_schema = [(''tp'', [(''i'', SInt)]), (''ts'', [(''t'', SInt)]), (''tpts'', [(''i'', SInt), (''t'', SInt)])]"

text \<open>An error of the reader, reported as MonPoly reports its @{text Local_error}s, and the two
  failures that MonPoly raises directly.\<close>

datatype sig_error = SE_PARSE string | SE_TWICE string | SE_INTERNAL

definition sig_error_msg :: "sig_error \<Rightarrow> string" where
  "sig_error_msg e = fatal_failure (case e of
     SE_PARSE m \<Rightarrow> ''Error while parsing signature: '' @ m
   | SE_TWICE p \<Rightarrow> ''[Db.add_predicate] Predicate '' @ p @ '' was defined more than once in the signature.''
   | SE_INTERNAL \<Rightarrow> ''[Log_parser.convert_types] internal error'')"

text \<open>As MonPoly's @{text Misc.nsplit}: the empty string has no parts.\<close>

function colon_parts :: "string \<Rightarrow> string list" where
  "colon_parts s = (let a = takeWhile (\<lambda>c. c \<noteq> CHR '':'') s; r = dropWhile (\<lambda>c. c \<noteq> CHR '':'') s in
     if r = [] then [a] else a # colon_parts (tl r))"
  by pat_completeness auto
termination
proof (relation "measure length", goal_cases)
  case (2 s a r)
  then have "CHR '':'' \<in> set s"
    by auto
  then have "0 < length s"
    by (rule length_pos_if_in_set)
  then show ?case
    using 2 length_dropWhile_le[of "\<lambda>c. c \<noteq> CHR '':''" s]
    by (simp only: in_measure length_tl)
qed simp

declare colon_parts.simps[simp del]

definition nsplit_colon :: "string \<Rightarrow> string list" where
  "nsplit_colon s = (if s = [] then [] else colon_parts s)"

definition get_type :: "string \<Rightarrow> sig_error + sty" where
  "get_type t = (if t = ''int'' then Inr SInt else if t = ''string'' then Inr SStr
     else if t = ''float'' then Inr SFloat else if t = ''regexp'' then Inr SRegexp
     else Inl (SE_PARSE (''Unknown type '' @ t)))"

definition field_decl :: "string \<Rightarrow> sig_error + string \<times> sty" where
  "field_decl f = (case nsplit_colon f of
     [] \<Rightarrow> Inl SE_INTERNAL
   | [t] \<Rightarrow> map_sum id (Pair []) (get_type t)
   | v # t # _ \<Rightarrow> map_sum id (Pair v) (get_type t))"

fun field_decls :: "string list \<Rightarrow> sig_error + (string \<times> sty) list" where
  "field_decls [] = Inr []"
| "field_decls (f # fs) = (case field_decl f of Inl e \<Rightarrow> Inl e
     | Inr d \<Rightarrow> map_sum id (Cons d) (field_decls fs))"

definition add_decl :: "string \<times> string list \<Rightarrow> schema \<Rightarrow> sig_error + schema" where
  "add_decl d S = (case field_decls (snd d) of Inl e \<Rightarrow> Inl e
     | Inr l \<Rightarrow> if fst d \<in> fst ` set S then Inl (SE_TWICE (fst d)) else Inr ((fst d, l) # S))"

fun decls_schema :: "(string \<times> string list) list \<Rightarrow> schema \<Rightarrow> sig_error + schema" where
  "decls_schema [] S = Inr S"
| "decls_schema (d # ds) S = (case add_decl d S of Inl e \<Rightarrow> Inl e | Inr S' \<Rightarrow> decls_schema ds S')"

subsection \<open>Tokens up to a lexical error\<close>

text \<open>The verified lexer stops at a character that begins no token, where MonPoly's lexer emits
  @{text ERR} and goes on. @{text SErr} then ends the tokens, so MonPoly's error is reported unless
  an earlier one is.\<close>

datatype stok = STok "string token" | SErr

fun pend_toks :: "lstate \<Rightarrow> string token list" where
  "pend_toks (L_SIMPLE s) = [T_STR s]"
| "pend_toks _ = []"

fun lex_upto :: "string \<Rightarrow> lstate \<Rightarrow> string token list" where
  "lex_upto [] l = []"
| "lex_upto (c # s) l = (case lex_step c l of
     None \<Rightarrow> pend_toks l
   | Some (ts, l') \<Rightarrow> ts @ lex_upto s l')"

definition sig_tokens :: "string \<Rightarrow> stok list" where
  "sig_tokens s = (case lex_run s L_INIT of
     None \<Rightarrow> map STok (lex_upto s L_INIT) @ [SErr]
   | Some (ts, l) \<Rightarrow> (case lex_finish l of
       None \<Rightarrow> map STok ts @ [SErr]
     | Some ts' \<Rightarrow> map STok (ts @ ts')))"

lemma SErr_map_STok[simp]: "SErr \<notin> set (map STok ts)"
  by auto

lemma append_SErr_neq[simp]: "xs @ [SErr] \<noteq> map STok ts"
proof
  assume "xs @ [SErr] = map STok ts"
  then have "SErr \<in> set (map STok ts)"
    by (metis in_set_conv_decomp)
  then show False
    by auto
qed

lemma inj_STok: "inj STok"
  by (auto intro: injI)

lemma sig_tokens_lex: "sig_tokens s = map STok ts \<longleftrightarrow> lex s = Some ts"
proof (cases "lex_run s L_INIT")
  case (Some p)
  obtain ts0 l where p: "p = (ts0, l)"
    by (cases p)
  show ?thesis
  proof (cases "lex_finish l")
    case (Some ts')
    have "map STok (ts0 @ ts') = map STok ts \<longleftrightarrow> ts0 @ ts' = ts"
      by (rule inj_map_eq_map[OF inj_STok])
    then show ?thesis
      using \<open>lex_run s L_INIT = Some p\<close> Some by (simp add: sig_tokens_def lex_def p)
  qed (use \<open>lex_run s L_INIT = Some p\<close> in \<open>simp add: sig_tokens_def lex_def p\<close>)
qed (simp add: sig_tokens_def lex_def)

lemma sig_tokens_SErr:
  assumes "SErr \<notin> set (sig_tokens s)"
  shows "\<exists>ts. sig_tokens s = map STok ts"
proof (cases "lex_run s L_INIT")
  case (Some p)
  obtain ts0 l where p: "p = (ts0, l)"
    by (cases p)
  show ?thesis
  proof (cases "lex_finish l")
    case None
    then show ?thesis
      using assms Some by (simp add: sig_tokens_def p)
  next
    case (Some ts')
    then show ?thesis
      using \<open>lex_run s L_INIT = Some p\<close> by (simp add: sig_tokens_def p, metis map_append)
  qed
qed (use assms in \<open>simp add: sig_tokens_def\<close>)
subsection \<open>Recursive descent\<close>

definition squote :: "string \<Rightarrow> string" where
  "squote s = CHR 0x27 # s @ [CHR 0x27]"

fun tok_str :: "stok list \<Rightarrow> string" where
  "tok_str [] = ''<EOF>''"
| "tok_str (SErr # _) = ''<unrecognized>''"
| "tok_str (STok t # _) = (case t of
     T_AT \<Rightarrow> squote ''@'' | T_LPAREN \<Rightarrow> squote ''('' | T_RPAREN \<Rightarrow> squote '')''
   | T_LANGLE \<Rightarrow> squote ''<'' | T_RANGLE \<Rightarrow> squote ''>'' | T_LBRACE \<Rightarrow> squote ''{''
   | T_RBRACE \<Rightarrow> squote ''}'' | T_COMMA \<Rightarrow> squote '','' | T_SEMICOLON \<Rightarrow> squote '';''
   | T_STR s \<Rightarrow> CHR 0x22 # escaped s @ [CHR 0x22])"

definition expected :: "string \<Rightarrow> stok list \<Rightarrow> sig_error" where
  "expected what ts = SE_PARSE (''Expected '' @ what @ '' but saw '' @ tok_str ts)"

fun sig_more :: "stok list \<Rightarrow> string list \<Rightarrow> sig_error + string list \<times> stok list" where
  "sig_more [] acc = Inl (expected (squote '','' @ '' or '' @ squote '')'') [])"
| "sig_more (t # ts) acc = (case t of
     STok T_COMMA \<Rightarrow> (case ts of
       STok (T_STR s) # ts' \<Rightarrow> sig_more ts' (s # acc)
     | _ \<Rightarrow> Inl (expected ''a string'' ts))
   | STok T_RPAREN \<Rightarrow> Inr (rev acc, ts)
   | _ \<Rightarrow> Inl (expected (squote '','' @ '' or '' @ squote '')'') (t # ts)))"

definition sig_tuple :: "stok list \<Rightarrow> sig_error + string list \<times> stok list" where
  "sig_tuple ts = (case ts of
     STok T_LPAREN # ts1 \<Rightarrow> (case ts1 of
       STok T_RPAREN # ts2 \<Rightarrow> Inr ([], ts2)
     | STok (T_STR s) # ts2 \<Rightarrow> sig_more ts2 [s]
     | _ \<Rightarrow> Inl (expected (''a string or '' @ squote '')'') ts1))
   | _ \<Rightarrow> Inl (expected (squote ''('') ts))"

lemma sig_more_length: "sig_more ts acc = Inr (fs, ts') \<Longrightarrow> length ts' < length ts"
proof (induction ts acc rule: sig_more.induct)
  case (2 t ts acc)
  then show ?case
    by (fastforce split: stok.splits token.splits list.splits)
qed simp

lemma sig_tuple_length: "sig_tuple ts = Inr (fs, ts') \<Longrightarrow> length ts' < length ts"
  by (auto simp: sig_tuple_def split: stok.splits token.splits list.splits dest!: sig_more_length)

text \<open>Each declaration is added to the schema before the next is read.\<close>

function (sequential) sig_decls :: "stok list \<Rightarrow> schema \<Rightarrow> sig_error + schema" where
  "sig_decls [] S = Inr S"
| "sig_decls (STok (T_STR p) # ts) S = (case sig_tuple ts of
     Inl e \<Rightarrow> Inl e
   | Inr (fs, ts') \<Rightarrow> (case add_decl (p, fs) S of Inl e \<Rightarrow> Inl e | Inr S' \<Rightarrow> sig_decls ts' S'))"
| "sig_decls ts S = Inl (expected ''a string'' ts)"
  by pat_completeness auto
termination
  by (relation "measure (length \<circ> fst)") (auto dest: sig_tuple_length)

definition read_sig :: "string \<Rightarrow> sig_error + schema" where
  "read_sig s = sig_decls (sig_tokens s) base_schema"

subsection \<open>Correctness on token words\<close>

inductive G_more :: "'s token list \<Rightarrow> 's list \<Rightarrow> bool" where
  G_more_end: "G_more [T_RPAREN] []"
| G_more_next: "G_more ts vs \<Longrightarrow> G_more (T_COMMA # T_STR f # ts) (f # vs)"

lemma G_more_last: "G_more ts vs \<Longrightarrow> ts \<noteq> [] \<and> last ts = T_RPAREN"
  by (induction rule: G_more.induct) auto

lemma G_fields_more: "G_fields fs vs \<longleftrightarrow> (\<exists>f ts us. fs @ [T_RPAREN] = T_STR f # ts \<and> vs = f # us \<and> G_more ts us)"
proof
  assume "G_fields fs vs"
  then show "\<exists>f ts us. fs @ [T_RPAREN] = T_STR f # ts \<and> vs = f # us \<and> G_more ts us"
    by (induction rule: G_fields.induct) (auto intro: G_more.intros)
next
  assume "\<exists>f ts us. fs @ [T_RPAREN] = T_STR f # ts \<and> vs = f # us \<and> G_more ts us"
  then obtain f ts us where e: "fs @ [T_RPAREN] = T_STR f # ts" "vs = f # us" "G_more ts us"
    by blast
  from e(3) have "\<And>f fs. fs @ [T_RPAREN] = T_STR f # ts \<Longrightarrow> G_fields fs (f # us)"
  proof (induction rule: G_more.induct)
    case G_more_end
    then show ?case by (cases fs) (auto intro: G_fields.intros)
  next
    case (G_more_next ts vs f')
    have l: "ts \<noteq> [] \<and> last ts = T_RPAREN"
      using G_more_next(1) by (rule G_more_last)
    have b: "butlast (T_STR f' # ts) @ [T_RPAREN] = T_STR f' # ts"
      using l by (metis append_butlast_last_id last_ConsR list.distinct(1))
    have "fs = butlast (T_STR f # T_COMMA # T_STR f' # ts)"
      using G_more_next(3) by (metis butlast_snoc)
    then have "fs = T_STR f # T_COMMA # butlast (T_STR f' # ts)"
      by simp
    then show ?case
      using G_more_next(2)[OF b] by (auto intro: G_fields.intros)
  qed  then show "G_fields fs vs"
    using e by blast
qed

lemma sig_more_G_more:
  "G_more tu vs \<Longrightarrow> sig_more (map STok (tu @ ts')) acc = Inr (rev acc @ vs, map STok ts')"
  by (induction tu vs arbitrary: acc rule: G_more.induct) simp_all

lemma sig_more_InrD:
  "sig_more (map STok ts) acc = Inr (fs, rest) \<Longrightarrow>
    \<exists>tu ts' vs. ts = tu @ ts' \<and> G_more tu vs \<and> fs = rev acc @ vs \<and> rest = map STok ts'"
proof (induction ts arbitrary: acc rule: length_induct)
  case (1 ts)
  show ?case
  proof (cases ts)
    case (Cons t ts1)
    show ?thesis
    proof (cases t)
      case T_COMMA
      show ?thesis
      proof (cases ts1)
        case (Cons t2 ts2)
        show ?thesis
        proof (cases t2)
          case (T_STR s)
          have m: "sig_more (map STok ts2) (s # acc) = Inr (fs, rest)"
            using "1.prems" \<open>ts = t # ts1\<close> T_COMMA Cons T_STR by simp
          have "length ts2 < length ts"
            using \<open>ts = t # ts1\<close> Cons by simp
          then obtain tu ts' vs where "ts2 = tu @ ts'" "G_more tu vs" "fs = rev (s # acc) @ vs"
              "rest = map STok ts'"
            using "1.IH" m by blast
          then show ?thesis
            using \<open>ts = t # ts1\<close> T_COMMA Cons T_STR
            by (intro exI[of _ "T_COMMA # T_STR s # tu"] exI[of _ ts'] exI[of _ "s # vs"])
              (auto intro: G_more_next)
        qed (use "1.prems" \<open>ts = t # ts1\<close> T_COMMA Cons in simp)+
      qed (use "1.prems" \<open>ts = t # ts1\<close> T_COMMA in simp)
    next
      case T_RPAREN
      then show ?thesis
        using "1.prems" Cons
        by (intro exI[of _ "[T_RPAREN]"] exI[of _ ts1] exI[of _ "[]"]) (auto intro: G_more_end)
    qed (use "1.prems" Cons in simp)+
  qed (use "1.prems" in simp)
qed

lemma sig_more_Inr:
  "sig_more (map STok ts) acc = Inr (fs, rest) \<longleftrightarrow>
    (\<exists>tu ts' vs. ts = tu @ ts' \<and> G_more tu vs \<and> fs = rev acc @ vs \<and> rest = map STok ts')"
  using sig_more_InrD sig_more_G_more by blast

lemma sig_tuple_G_tuple:
  assumes "G_tuple tu fs"
  shows "sig_tuple (map STok (tu @ ts')) = Inr (fs, map STok ts')"
  using assms
proof cases
  case G_tuple_empty
  then show ?thesis
    by (simp add: sig_tuple_def)
next
  case (G_tuple_fields fs0)
  from G_tuple_fields(2) have "\<exists>f tm us. fs0 @ [T_RPAREN] = T_STR f # tm \<and> fs = f # us \<and> G_more tm us"
    by (simp only: G_fields_more)
  then obtain f tm us where e: "fs0 @ [T_RPAREN] = T_STR f # tm" "fs = f # us" "G_more tm us"
    by blast
  have "tu @ ts' = T_LPAREN # T_STR f # tm @ ts'"
    using G_tuple_fields(1) e(1) by simp
  then show ?thesis
    using sig_more_G_more[OF e(3), of ts' "[f]"] e(2) by (simp add: sig_tuple_def)
qed

lemma sig_tuple_InrD:
  assumes "sig_tuple (map STok ts) = Inr (fs, rest)"
  shows "\<exists>tu ts'. ts = tu @ ts' \<and> G_tuple tu fs \<and> rest = map STok ts'"
proof -
  obtain ts1 where ts: "ts = T_LPAREN # ts1"
    using assms by (auto simp: sig_tuple_def split: list.splits stok.splits token.splits)
  show ?thesis
  proof (cases ts1)
    case (Cons t ts2)
    show ?thesis
    proof (cases t)
      case T_RPAREN
      then show ?thesis
        using assms ts Cons G_tuple_empty
        by (intro exI[of _ "[T_LPAREN, T_RPAREN]"] exI[of _ ts2]) (auto simp: sig_tuple_def)
    next
      case (T_STR s)
      then have "sig_more (map STok ts2) [s] = Inr (fs, rest)"
        using assms ts Cons by (simp add: sig_tuple_def)
      from sig_more_InrD[OF this] obtain tu ts' vs where
        m: "ts2 = tu @ ts'" "G_more tu vs" "fs = rev [s] @ vs" "rest = map STok ts'"
        by blast
      then have m: "ts2 = tu @ ts'" "G_more tu vs" "fs = s # vs" "rest = map STok ts'"
        by simp_all
      have l: "tu \<noteq> [] \<and> last tu = T_RPAREN"
        using m(2) by (rule G_more_last)
      have "G_fields (T_STR s # butlast tu) fs"
        unfolding G_fields_more using l m(2,3)
        by (metis append_Cons append_butlast_last_id)
      then have "G_tuple (T_LPAREN # (T_STR s # butlast tu) @ [T_RPAREN]) fs"
        by (rule G_tuple_fields)
      moreover have "T_LPAREN # (T_STR s # butlast tu) @ [T_RPAREN] = T_LPAREN # T_STR s # tu"
        using l by (metis append_Cons append_butlast_last_id)
      ultimately show ?thesis
        using ts Cons T_STR m(1,4) by (intro exI[of _ "T_LPAREN # T_STR s # tu"] exI[of _ ts']) simp
    qed (use assms ts Cons in \<open>simp add: sig_tuple_def\<close>)+
  qed (use assms ts in \<open>simp add: sig_tuple_def\<close>)
qed

lemma sig_tuple_Inr:
  "sig_tuple (map STok ts) = Inr (fs, rest) \<longleftrightarrow>
    (\<exists>tu ts'. ts = tu @ ts' \<and> G_tuple tu fs \<and> rest = map STok ts')"
  using sig_tuple_InrD sig_tuple_G_tuple by blast

lemma sig_decls_G_sig:
  "G_sig ts ds \<Longrightarrow> decls_schema ds S = Inr S' \<Longrightarrow> sig_decls (map STok ts) S = Inr S'"
proof (induction ts ds arbitrary: S rule: G_sig.induct)
  case (G_sig_Cons tu fs ts ds p)
  then obtain S1 where "add_decl (p, fs) S = Inr S1" "decls_schema ds S1 = Inr S'"
    by (auto split: sum.splits)
  then show ?case
    using G_sig_Cons(3) sig_tuple_G_tuple[OF G_sig_Cons(1), of ts] by simp
qed simp

lemma sig_decls_InrD:
  "sig_decls (map STok ts) S = Inr S' \<Longrightarrow> \<exists>ds. G_sig ts ds \<and> decls_schema ds S = Inr S'"
proof (induction ts arbitrary: S rule: length_induct)
  case (1 ts)
  show ?case
  proof (cases ts)
    case Nil
    then show ?thesis
      using "1.prems" by (auto intro: G_sig_Nil)
  next
    case (Cons t ts1)
    then obtain p where t: "t = T_STR p"
      using "1.prems" by (cases t) auto
    obtain fs rest where tu: "sig_tuple (map STok ts1) = Inr (fs, rest)"
      using "1.prems" Cons t by (auto split: sum.splits)
    then obtain tu ts2 where ts1: "ts1 = tu @ ts2" "G_tuple tu fs" "rest = map STok ts2"
      using sig_tuple_InrD by blast
    obtain S1 where S1: "add_decl (p, fs) S = Inr S1" "sig_decls (map STok ts2) S1 = Inr S'"
      using "1.prems" Cons t tu ts1(3) by (auto split: sum.splits)
    have "length ts2 < length ts"
      using Cons ts1(1) by simp
    then obtain ds where "G_sig ts2 ds" "decls_schema ds S1 = Inr S'"
      using "1.IH" S1(2) by blast
    then show ?thesis
      using Cons t ts1 S1(1) by (intro exI[of _ "(p, fs) # ds"]) (auto intro: G_sig_Cons)
  qed
qed

lemma sig_decls_correct:
  "sig_decls (map STok ts) S = Inr S' \<longleftrightarrow> (\<exists>ds. G_sig ts ds \<and> decls_schema ds S = Inr S')"
  using sig_decls_InrD sig_decls_G_sig by blast

subsection \<open>Correctness of the reader\<close>

lemma sig_more_suffix: "sig_more ts acc = Inr (fs, ts') \<Longrightarrow> \<exists>pre. ts = pre @ ts' \<and> SErr \<notin> set pre"
proof (induction ts arbitrary: acc rule: length_induct)
  case (1 ts)
  then obtain t ts1 where ts: "ts = t # ts1"
    by (cases ts) auto
  show ?case
  proof (cases t)
    case (STok x)
    show ?thesis
    proof (cases x)
      case T_RPAREN
      then show ?thesis
        using "1.prems" ts STok by (intro exI[of _ "[t]"]) auto
    next
      case T_COMMA
      then obtain s ts2 where ts1: "ts1 = STok (T_STR s) # ts2" and m: "sig_more ts2 (s # acc) = Inr (fs, ts')"
        using "1.prems" ts STok by (auto split: list.splits stok.splits token.splits)
      have "length ts2 < length ts"
        using ts ts1 by simp
      then obtain pre where "ts2 = pre @ ts'" "SErr \<notin> set pre"
        using "1.IH" m by blast
      then show ?thesis
        using ts STok T_COMMA ts1 by (intro exI[of _ "t # STok (T_STR s) # pre"]) auto
    qed (use "1.prems" ts STok in simp)+
  qed (use "1.prems" ts in simp)
qed

lemma sig_tuple_suffix: "sig_tuple ts = Inr (fs, ts') \<Longrightarrow> \<exists>pre. ts = pre @ ts' \<and> SErr \<notin> set pre"
proof -
  assume a: "sig_tuple ts = Inr (fs, ts')"
  then obtain ts1 where ts: "ts = STok T_LPAREN # ts1"
    by (auto simp: sig_tuple_def split: list.splits stok.splits token.splits)
  then obtain t ts2 where ts1: "ts1 = t # ts2"
    using a by (cases ts1) (auto simp: sig_tuple_def)
  show ?thesis
  proof (cases "t = STok T_RPAREN")
    case True
    then show ?thesis
      using a ts ts1 by (intro exI[of _ "[STok T_LPAREN, t]"]) (auto simp: sig_tuple_def)
  next
    case False
    then obtain s where t: "t = STok (T_STR s)" and m: "sig_more ts2 [s] = Inr (fs, ts')"
      using a ts ts1 by (auto simp: sig_tuple_def split: stok.splits token.splits)
    then obtain pre where "ts2 = pre @ ts'" "SErr \<notin> set pre"
      using sig_more_suffix by blast
    then show ?thesis
      using ts ts1 t by (intro exI[of _ "STok T_LPAREN # t # pre"]) auto
  qed
qed

lemma sig_decls_SErr: "SErr \<in> set toks \<Longrightarrow> sig_decls toks S \<noteq> Inr S'"
proof (induction toks arbitrary: S rule: length_induct)
  case (1 toks)
  then obtain t ts where toks: "toks = t # ts"
    by (cases toks) auto
  show ?case
  proof (cases "\<exists>p. t = STok (T_STR p)")
    case True
    then obtain p where t: "t = STok (T_STR p)"
      by blast
    show ?thesis
    proof (cases "sig_tuple ts")
      case (Inr r)
      obtain fs ts' where r: "r = (fs, ts')"
        by (cases r)
      obtain pre where pre: "ts = pre @ ts'" "SErr \<notin> set pre"
        using sig_tuple_suffix Inr r by blast
      have "SErr \<in> set ts'"
        using "1.prems" toks t pre by auto
      moreover have "length ts' < length toks"
        using toks pre by simp
      ultimately have "sig_decls ts' S1 \<noteq> Inr S'" for S1
        using "1.IH" by blast
      then show ?thesis
        using toks t Inr r by (simp split: sum.splits)
    qed (simp add: toks t)
  next
    case False
    then show ?thesis
      using toks by (cases t; cases "case t of STok x \<Rightarrow> x") (auto split: token.splits)
  qed
qed

theorem read_sig_correct:
  "read_sig s = Inr S \<longleftrightarrow> (\<exists>ds. sig_lang s ds \<and> decls_schema ds base_schema = Inr S)"
proof
  assume r: "read_sig s = Inr S"
  then have "SErr \<notin> set (sig_tokens s)"
    using sig_decls_SErr unfolding read_sig_def by blast
  then obtain ts where ts: "sig_tokens s = map STok ts"
    using sig_tokens_SErr by blast
  then have "lexes s ts"
    using sig_tokens_lex lex_correct by blast
  then show "\<exists>ds. sig_lang s ds \<and> decls_schema ds base_schema = Inr S"
    using r sig_decls_correct[of ts base_schema S] unfolding read_sig_def ts sig_lang_def by blast
next
  assume "\<exists>ds. sig_lang s ds \<and> decls_schema ds base_schema = Inr S"
  then obtain ds ts where "lexes s ts" "G_sig ts ds" "decls_schema ds base_schema = Inr S"
    unfolding sig_lang_def by blast
  moreover from \<open>lexes s ts\<close> have "sig_tokens s = map STok ts"
    using sig_tokens_lex lex_correct by blast
  ultimately show "read_sig s = Inr S"
    using sig_decls_correct[of ts base_schema S] unfolding read_sig_def by auto
qed

(*<*)
end
(*>*)
