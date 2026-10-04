(*<*)
theory CLI_Output
  imports CLI_Options
begin
(*>*)

section \<open>The output\<close>

text \<open>
  The verdicts are printed as MonPoly prints them (\<^verbatim>\<open>Verified_adapter.show_results\<close>): for
  each time point with a nonempty verdict, a line with the timestamp, the time point and the
  tuples in MonPoly's order; with @{text "-verbose"}, a line for every time point. The text is a
  list of @{typ string8} pieces, which the driver writes one after the other.

  Three functions on the monitor's values are implemented by OCaml in the code (theory
  @{text CLI_Code}): @{text str8_of_integer} by Zarith's @{text Z.to_string},
  @{text str8_quoted} by a test of the first and last byte, and the printer of floating point
  numbers, which is a parameter (MonPoly's @{text "%g"}).
\<close>

subsection \<open>Values\<close>

fun dec_digits :: "nat \<Rightarrow> string" where
  "dec_digits n = (if n < 10 then [char_of (48 + n)] else dec_digits (n div 10) @ [char_of (48 + n mod 10)])"

declare dec_digits.simps[simp del]

definition str8_of_integer :: "integer \<Rightarrow> string8" where
  "str8_of_integer i = str8_of_string (if i < 0 then CHR ''-'' # dec_digits (nat_of_integer (- i))
     else dec_digits (nat_of_integer i))"

definition str8_quoted :: "string8 \<Rightarrow> bool" where
  "str8_quoted s \<longleftrightarrow> (let cs = Rep_string8 s in cs \<noteq> [] \<and> hd cs = CHR 0x22 \<and> last cs = CHR 0x22)"

abbreviation S8 :: "String.literal \<Rightarrow> string8" where
  "S8 \<equiv> string8_literal"

text \<open>A string is printed in double quotes, unless it is empty (two double quotes) or already
  begins and ends with one (@{text Verified_adapter.add_event_data}).\<close>

definition ed_out :: "(double \<Rightarrow> string8) \<Rightarrow> event_data \<Rightarrow> string8 list" where
  "ed_out ff d = (case d of
     EInt i \<Rightarrow> [str8_of_integer i]
   | EFloat f \<Rightarrow> [ff f]
   | EString s \<Rightarrow> if s = empty_string then [S8 STR ''\"\"'']
       else if str8_quoted s then [s] else [S8 STR ''\"'', s, S8 STR ''\"''])"

fun sep_out :: "string8 \<Rightarrow> string8 list list \<Rightarrow> string8 list" where
  "sep_out d [] = []"
| "sep_out d [x] = x"
| "sep_out d (x # y # zs) = x @ d # sep_out d (y # zs)"

definition tuple_out :: "(double \<Rightarrow> string8) \<Rightarrow> event_data list \<Rightarrow> string8 list" where
  "tuple_out ff t = S8 STR ''('' # sep_out (S8 STR '','') (map (ed_out ff) t) @ [S8 STR '')'']"

subsection \<open>Timestamps\<close>

text \<open>MonPoly adds the last timestamp @{text "2\<^sup>6\<^sup>4"} (@{text MFOTL.ts_max}), and prints it as
  @{text MaxTS}.\<close>

definition ts_max :: nat where
  "ts_max = 2 ^ 64"

text \<open>With @{text "-unix"}, MonPoly prints the fields of OCaml's @{text "Unix.gmtime"} as they
  are: the years since 1900, the month from 0, the day of the month, and the time. The date is
  computed from the days since 1970 (by Hinnant's algorithm for the proleptic Gregorian
  calendar).\<close>

definition civil_of_days :: "int \<Rightarrow> int \<times> int \<times> int" where
  "civil_of_days z0 = (let z = z0 + 719468; era = z div 146097; doe = z - era * 146097;
     yoe = (doe - doe div 1460 + doe div 36524 - doe div 146096) div 365;
     doy = doe - (365 * yoe + yoe div 4 - yoe div 100);
     mp = (5 * doy + 2) div 153; d = doy - (153 * mp + 2) div 5 + 1;
     m = (if mp < 10 then mp + 3 else mp - 9); y = yoe + era * 400 + (if m \<le> 2 then 1 else 0)
   in (y, m, d))"

definition str8_of_int :: "int \<Rightarrow> string8" where
  "str8_of_int i = str8_of_integer (integer_of_int i)"

definition unix_out :: "nat \<Rightarrow> string8 list" where
  "unix_out t = (let s = int t; (y, m, d) = civil_of_days (s div 86400); r = s mod 86400 in
     [str8_of_int (y - 1900), S8 STR ''-'', str8_of_int (m - 1), S8 STR ''-'', str8_of_int d,
      S8 STR '' '', str8_of_int (r div 3600), S8 STR '':'', str8_of_int (r div 60 mod 60),
      S8 STR '':'', str8_of_int (r mod 60)])"

definition ts_out :: "bool \<Rightarrow> nat \<Rightarrow> string8 list" where
  "ts_out unix t = (if unix then unix_out t else if t = ts_max then [S8 STR ''MaxTS'']
     else [str8_of_integer (integer_of_nat t)])"

subsection \<open>Verdicts\<close>

text \<open>MonPoly's order of tuples (@{text Tuple.compare}): lexicographic, with integers before
  strings before floating point numbers; values of the same type in the order of the monitor's
  comparator, which is MonPoly's order on integers and strings.\<close>

definition ed_cmp :: "event_data comparator" where
  "ed_cmp = the (ID ccompare)"

fun mp_ed_cmp :: "event_data comparator" where
  "mp_ed_cmp (EString _) (EFloat _) = Lt"
| "mp_ed_cmp (EFloat _) (EString _) = Gt"
| "mp_ed_cmp a b = ed_cmp a b"

fun mp_cmp :: "event_data list comparator" where
  "mp_cmp [] [] = order.Eq"
| "mp_cmp [] (_ # _) = Lt"
| "mp_cmp (_ # _) [] = Gt"
| "mp_cmp (x # xs) (y # ys) = (case mp_ed_cmp x y of order.Eq \<Rightarrow> mp_cmp xs ys | c \<Rightarrow> c)"

fun adj_sorted :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
  "adj_sorted r (x # y # zs) = (r x y \<and> adj_sorted r (y # zs))"
| "adj_sorted r _ = True"

text \<open>The tuples of a verdict, in MonPoly's order: the monitor's tables are ordered by its
  comparator, which agrees with MonPoly's order on tables whose columns each have one type; only
  otherwise are they sorted.\<close>

definition rows_of :: "utable \<Rightarrow> event_data list list" where
  "rows_of X = (let l = csorted_list_of_set X in
     if adj_sorted (\<lambda>a b. mp_cmp a b = Lt) l then l else csort mp_cmp l)"

text \<open>The lines for the verdict of time point @{text q} with timestamp @{text t}, with
  @{text n} free variables, and whether it is nonempty (@{text "-stop_at_first_viol"} stops
  then, after the first tuple).\<close>

definition verdict_out :: "config \<Rightarrow> (double \<Rightarrow> string8) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> utable \<Rightarrow>
    string8 list \<times> bool" where
  "verdict_out cfg ff n q t X = (let
     rows = (if c_stop_first cfg then take 1 (rows_of X) else rows_of X);
     head = S8 STR ''@'' # ts_out (c_unix cfg) t @ [S8 STR '' (time point '', str8_of_integer (integer_of_nat q), S8 STR ''): ''];
     nl8 = S8 STR ''\<newline>''
   in (if c_verbose cfg then
       (if n = 0 then head @ [if rows = [] then S8 STR ''false'' else S8 STR ''true'', nl8]
        else head @ S8 STR ''('' # sep_out (S8 STR '','') (map (tuple_out ff) rows) @ [S8 STR '')'', nl8])
     else if rows = [] then []
     else if n = 0 then head @ [S8 STR ''true'', nl8]
     else head @ sep_out (S8 STR '' '') (map (tuple_out ff) rows) @ [nl8], rows \<noteq> []))"

text \<open>The same text as a fold, for the driver: each piece is passed to @{text f} as it is
  produced, and each integer of a tuple to @{text fi}, rather than built into a list, which the
  driver would then copy (@{thm [source] verdict_fold_eq}: with @{text fi} the printing of the
  integer, the fold over the pieces of @{const verdict_out}).\<close>

fun sep_fold :: "('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> string8 \<Rightarrow> (string8 \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'b list \<Rightarrow> 'a \<Rightarrow> 'a" where
  "sep_fold g d f [] acc = acc"
| "sep_fold g d f [x] acc = g x acc"
| "sep_fold g d f (x # y # zs) acc = sep_fold g d f (y # zs) (f d (g x acc))"

lemma sep_fold_out: "sep_fold (\<lambda>x. fold f (h x)) d f xs acc = fold f (sep_out d (map h xs)) acc"
  by (induction "\<lambda>x. fold f (h x)" d f xs acc rule: sep_fold.induct) simp_all

definition ed_fold :: "(double \<Rightarrow> string8) \<Rightarrow> (integer \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> (string8 \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow>
    event_data \<Rightarrow> 'a \<Rightarrow> 'a" where
  "ed_fold ff fi f d acc = (case d of
     EInt i \<Rightarrow> fi i acc
   | EFloat x \<Rightarrow> f (ff x) acc
   | EString s \<Rightarrow> if s = empty_string then f (S8 STR ''\"\"'') acc
       else if str8_quoted s then f s acc else f (S8 STR ''\"'') (f s (f (S8 STR ''\"'') acc)))"

lemma ed_fold_out: "ed_fold ff (\<lambda>i. f (str8_of_integer i)) f d acc = fold f (ed_out ff d) acc"
  by (simp add: ed_fold_def ed_out_def split: event_data.splits)

definition tuple_fold :: "(double \<Rightarrow> string8) \<Rightarrow> (integer \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> (string8 \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow>
    event_data list \<Rightarrow> 'a \<Rightarrow> 'a" where
  "tuple_fold ff fi f t acc =
     f (S8 STR '')'') (sep_fold (ed_fold ff fi f) (S8 STR '','') f t (f (S8 STR ''('') acc))"

lemma tuple_fold_out: "tuple_fold ff (\<lambda>i. f (str8_of_integer i)) f t acc = fold f (tuple_out ff t) acc"
proof -
  have "ed_fold ff (\<lambda>i. f (str8_of_integer i)) f = (\<lambda>d. fold f (ed_out ff d))"
    by (simp add: fun_eq_iff ed_fold_out)
  then show ?thesis
    by (simp add: tuple_fold_def tuple_out_def sep_fold_out)
qed

definition verdict_fold :: "config \<Rightarrow> (double \<Rightarrow> string8) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> utable \<Rightarrow>
    (integer \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> (string8 \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a \<times> bool" where
  "verdict_fold conf ff n q t X fi f acc = (let
     rows = (if c_stop_first conf then take 1 (rows_of X) else rows_of X);
     head = S8 STR ''@'' # ts_out (c_unix conf) t @ [S8 STR '' (time point '', str8_of_integer (integer_of_nat q), S8 STR ''): ''];
     nl8 = S8 STR ''\<newline>''
   in (if c_verbose conf then
       (if n = 0 then fold f (head @ [if rows = [] then S8 STR ''false'' else S8 STR ''true'', nl8]) acc
        else f nl8 (f (S8 STR '')'') (sep_fold (tuple_fold ff fi f) (S8 STR '','') f rows
          (f (S8 STR ''('') (fold f head acc)))))
     else if rows = [] then acc
     else if n = 0 then fold f (head @ [S8 STR ''true'', nl8]) acc
     else f nl8 (sep_fold (tuple_fold ff fi f) (S8 STR '' '') f rows (fold f head acc)), rows \<noteq> []))"

lemma verdict_fold_eq:
  "verdict_fold conf ff n q t X (\<lambda>i. f (str8_of_integer i)) f acc =
     apfst (\<lambda>text. fold f text acc) (verdict_out conf ff n q t X)"
proof -
  have "tuple_fold ff (\<lambda>i. f (str8_of_integer i)) f = (\<lambda>t. fold f (tuple_out ff t))"
    by (simp add: fun_eq_iff tuple_fold_out)
  then show ?thesis
    by (simp add: verdict_fold_def verdict_out_def Let_def sep_fold_out)
qed

text \<open>With @{text "-verbose"}, each time point begins with this line.\<close>

definition tp_out :: "nat \<Rightarrow> string8 list" where
  "tp_out q = [S8 STR ''At time point '', str8_of_integer (integer_of_nat q), S8 STR '':\<newline>'']"


subsection \<open>Errors in the log\<close>

text \<open>An error the monitor reports in the log, as MonPoly words it: located at the item it
  concerns (the driver adds the position), an out-of-order timestamp, which ends the program, and
  a command, which the verified monitor does not support.\<close>

datatype lerr = LE_LOC string | LE_ORDER string | LE_CMD string

text \<open>OCaml's @{text Char.escaped}, which unlike @{const escaped} also escapes the single
  quote.\<close>

definition char_escaped :: "char \<Rightarrow> string" where
  "char_escaped c = (if c = CHR 0x27 then [CHR 0x5C, CHR 0x27] else escaped_char c)"

fun string_of_ltok :: "bytes token \<Rightarrow> string" where
  "string_of_ltok T_AT = squote ''@''"
| "string_of_ltok T_LPAREN = squote ''(''"
| "string_of_ltok T_RPAREN = squote '')''"
| "string_of_ltok T_LANGLE = squote ''<''"
| "string_of_ltok T_RANGLE = squote ''>''"
| "string_of_ltok T_LBRACE = squote ''{''"
| "string_of_ltok T_RBRACE = squote ''}''"
| "string_of_ltok T_COMMA = squote '',''"
| "string_of_ltok T_SEMICOLON = squote '';''"
| "string_of_ltok (T_STR s) = CHR 0x22 # escaped (string_of_bytes s) @ [CHR 0x22]"

fun string_of_expect :: "expect \<Rightarrow> string" where
  "string_of_expect X_ENTRY = squote ''@'' @ '' or '' @ squote ''>''"
| "string_of_expect X_TIMESTAMP = ''a time-stamp''"
| "string_of_expect X_PREDICATE = ''a predicate, '' @ squote ''@'' @ '', '' @ squote '';'' @ '', or '' @ squote ''>''"
| "string_of_expect X_FIELD_OR_RPAREN = ''a tuple field or '' @ squote '')''"
| "string_of_expect X_COMMA_OR_RPAREN = squote '','' @ '' or '' @ squote '')''"
| "string_of_expect X_FIELD = ''a tuple field''"
| "string_of_expect X_CMD_NAME = ''a command name''"
| "string_of_expect X_CMD_ARG = ''a command argument or '' @ squote ''<''"

fun perror_msg :: "perror \<Rightarrow> string" where
  "perror_msg (E_TOKEN x (Some t)) = ''Expected '' @ string_of_expect x @ '' but saw '' @ string_of_ltok t"
| "perror_msg (E_TOKEN x None) = ''Expected '' @ string_of_expect x @ '' but saw <EOF>''"
| "perror_msg (E_CHAR x c) = ''Expected '' @ string_of_expect x @ '' but saw <unrecognized> ('' @ char_escaped c @ '')''"
| "perror_msg E_UNTERMINATED = ''Unterminated quoted string''"

definition dec_nat :: "nat \<Rightarrow> string" where
  "dec_nat n = dec_digits n"

definition lsig_arity :: "lsig \<Rightarrow> bytes \<Rightarrow> nat option" where
  "lsig_arity L p = map_option length (map_of L (string8_of_bytes p))"

text \<open>A timestamp in a message (@{text MFOTL.string_of_ts}), with @{text "-unix"} as a date as
  in @{const unix_out}.\<close>

definition unix_str :: "nat \<Rightarrow> string" where
  "unix_str t = (let s = int t; (y, m, d) = civil_of_days (s div 86400); r = s mod 86400 in
     dec_nat (nat (y - 1900)) @ ''-'' @ dec_nat (nat (m - 1)) @ ''-'' @ dec_nat (nat d) @ '' '' @
     dec_nat (nat (r div 3600)) @ '':'' @ dec_nat (nat (r div 60 mod 60)) @ '':'' @ dec_nat (nat (r mod 60)))"

definition ts_str :: "bool \<Rightarrow> nat \<Rightarrow> string" where
  "ts_str unix t = (if unix then unix_str t else dec_nat t)"

fun log_error :: "bool \<Rightarrow> lsig \<Rightarrow> verror \<Rightarrow> lerr" where
  "log_error unix L (VE_PARSE e) = LE_LOC (perror_msg e)"
| "log_error unix L (VE_TIMESTAMP ts) = LE_LOC (''Cannot convert '' @ string_of_bytes ts @ '' into a timestamp'')"
| "log_error unix L (VE_ORDER t p) =
     LE_ORDER (''ERROR: Out of order timestamp '' @ ts_str unix t @ '' (previous: '' @ ts_str unix p @ '')'')"
| "log_error unix L (VE_PREDICATE p n) = LE_LOC (case lsig_arity L p of
     Some a \<Rightarrow> ''Wrong tuple length for predicate '' @ string_of_bytes p @ '' (expected: '' @ dec_nat a @ '', actual: '' @ dec_nat n @ '')''
   | None \<Rightarrow> ''Predicate '' @ string_of_bytes p @ '' was not defined in the signature.'')"
| "log_error unix L (VE_FIELD p i t) = LE_LOC (''Expected type '' @ (case t of TInt \<Rightarrow> ''int'' | TFloat \<Rightarrow> ''float'' | TString \<Rightarrow> ''string'') @
     '' for predicate '' @ string_of_bytes p @ '', field number '' @ dec_nat (Suc i))"
| "log_error unix L (VE_COMMAND c) = LE_CMD ''ERROR: Commands are not supported by the verified kernel''"

(*<*)
end
(*>*)
