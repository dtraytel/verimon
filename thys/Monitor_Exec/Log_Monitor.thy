(*<*)
theory Log_Monitor
  imports Prepare Tuple_Code "Log_Parser.Log_Values" "Log_Parser.Log_Code"
begin
(*>*)



section \<open>From the log to the verdicts\<close>

text \<open>
  This theory composes the verified log parser of session Log_Parser with the verified executable
  monitor, into the monitor that @{text "-verified"} runs on a log: @{text vinit} prepares the
  formula and starts the monitor, @{text vfeed_chunk} reads a chunk of the log, and
  @{text vfinish} the end of the log. The parser skips the events of the predicates that the
  signature declares but whose names do not occur freely in the formula
  (@{theory Log_Parser.Log_Filter}); the time points it outputs are converted by the signature
  into the monitor's databases and fed to @{const emstep}.

  The main theorem, @{text verimon_log.vrun_log} (theory @{text Log_Monitor_Online}), states that for the bytes of a log that
  denotes a prefix -- its items are those the parser reads (@{const parse_log}, which accepts
  exactly the logs of the grammar, @{thm [source] parse_log_correct}), they are entries, their
  timestamps are natural numbers that do not decrease, and their events are those of the
  signature with fields of the declared types (@{text log_prefix}) -- the monitor reports no
  error, and its verdicts are those that the specification of the formula prescribes for the
  prefix (@{text Mt}, as in @{thm [source] verimon_prepare.eminit_verimon_mverdicts}).
  @{text verimon_log.vrun_filtered} states the same for the logs whose events of the other
  declared predicates are arbitrary, and that the monitor reports an error on every other log;
  @{text verimon_log.Mt_preds} states that the verdicts do not depend on these events.
  @{text verimon_log.vfeed_chunks_online}, @{text verimon_log.vfeed_chunks_log} and
  @{text verimon_log.vfeed_chunks_prompt} state the same for a log that is still being read, from
  the initial state; theory @{text Log_Monitor_Online} states it for the online interface, chunk
  by chunk: an invariant relates the state to the bytes read and the prefix they denote, and a
  chunk after which they still denote a prefix preserves it and outputs exactly the verdicts that
  the specification prescribes for the longer prefix and not for the shorter one.
  The theorems say nothing about which error is reported, what is output after the first error,
  nor about the verdicts output together with it, for the same chunk; for that chunk, the driver
  outputs the verdicts of its longest prefix whose outputs have no error, which the theorems
  cover.

  The theorems take the reader of floats as a parameter, about which nothing is assumed: the
  front end passes OCaml's @{text float_of_string_opt}. That the generated code computes these
  functions rests on the code printings: those of @{theory Log_Parser.Log_Code}, of the
  monitor's session (strings, floats, integers and containers), and the two below.
\<close>

subsection \<open>Strings\<close>

text \<open>The parser's byte strings and the monitor's strings both represent character lists, and
  both are OCaml strings in the generated code.\<close>

definition string8_of_bytes :: "bytes \<Rightarrow> string8" where
  "string8_of_bytes b = Abs_string8 (Rep_bytes b)"

lemma Rep_string8_of_bytes[simp]: "Rep_string8 (string8_of_bytes b) = Rep_bytes b"
  by (simp add: string8_of_bytes_def Abs_string8_inverse)

lemma string8_of_bytes_inject[simp]: "string8_of_bytes a = string8_of_bytes b \<longleftrightarrow> a = b"
  by (metis Rep_bytes_inject Rep_string8_of_bytes)

text \<open>Trusted: both types are printed as OCaml's strings, a character list as the string of the
  characters' codes (@{theory Log_Parser.Log_Code} prints @{typ char} so; the printings of
  @{theory MFOTL_Monitor_Devel.Event_Data} compare strings byte-wise, as the characters' codes
  are compared), so the conversion is the identity.\<close>

declare [[code drop: string8_of_bytes]]

code_printing
  constant string8_of_bytes \<rightharpoonup> (OCaml) "(fun x -> x)"

text \<open>Trusted as well: the equality of strings is that of OCaml's strings. (The code of
  @{text "HOL.equal"} on @{typ string8} is OCaml's polymorphic equality, which is slower.)\<close>

definition str8_eq :: "string8 \<Rightarrow> string8 \<Rightarrow> bool" where
  "str8_eq a b \<longleftrightarrow> a = b"

declare [[code drop: str8_eq]]

code_printing
  constant str8_eq \<rightharpoonup> (OCaml) "String.equal"

text \<open>The hash code of a string (@{theory MFOTL_Monitor_Devel.Event_Data}) is the fold over its
  characters; its code reads the bytes of the OCaml string, through the conversion to byte strings,
  trusted like @{const string8_of_bytes}.\<close>

definition bytes_of_string8 :: "string8 \<Rightarrow> bytes" where
  "bytes_of_string8 s = Abs_bytes (Rep_string8 s)"

lemma Rep_bytes_of_string8[simp]: "Rep_bytes (bytes_of_string8 s) = Rep_string8 s"
  by (simp add: bytes_of_string8_def Abs_bytes_inverse)

declare [[code drop: bytes_of_string8]]

code_printing
  constant bytes_of_string8 \<rightharpoonup> (OCaml) "(fun x -> x)"

function hash_bytes :: "bytes \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> hashcode \<Rightarrow> hashcode" where
  "hash_bytes s n i h = (if i < n
    then hash_bytes s n (i + 1) (h * hc_mult + Uint32_signed (integer_of_char (bytes_at s i)))
    else h)"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(_, n, i, _). nat_of_integer (n - i))")
   apply simp
  apply simp
  including integer.lifting
  apply transfer
  apply simp
  done

lemma hashcode_string8_code[code]:
  "hashcode s = (let b = bytes_of_string8 s in hash_bytes b (bytes_length b) 0 hc_init)"
  unfolding hashcode_string8_def Let_def
  by (subst hash_bytes_foldl) (simp_all add: hashcode_list_def hc_mult_def hc_init_def)

subsection \<open>Signatures\<close>

text \<open>The signature as the front end reads it: the predicates with their argument types.\<close>

type_synonym lsig = "(string8 \<times> ty list) list"

definition lsig_lookup :: "lsig \<Rightarrow> string8 \<times> nat \<Rightarrow> ty list option" where
  "lsig_lookup S pn = map_option snd (find (\<lambda>(p, tys). (p, length tys) = pn) S)"

definition lsig_tsig :: "lsig \<Rightarrow> tyssig" where
  "lsig_tsig S = map_sig TCst (lsig_lookup S)"

text \<open>The code compares the names first.\<close>

fun lsig_find :: "lsig \<Rightarrow> string8 \<Rightarrow> nat \<Rightarrow> ty list option" where
  "lsig_find [] q n = None"
| "lsig_find ((p, tys) # S) q n = (if str8_eq p q \<and> length tys = n then Some tys else lsig_find S q n)"

lemma lsig_lookup_code[code]: "lsig_lookup S (q, n) = lsig_find S q n"
  by (induction S q n rule: lsig_find.induct) (auto simp: lsig_lookup_def str8_eq_def)

text \<open>For large signatures, the code looks predicates up in a mapping from their names to their
  arities and argument types.\<close>

definition ix_list :: "(Formula.name, (nat \<times> ty list) list) mapping \<Rightarrow> Formula.name \<Rightarrow> (nat \<times> ty list) list" where
  "ix_list m p = (case Mapping.lookup m p of None \<Rightarrow> [] | Some l \<Rightarrow> l)"

fun ix_add :: "Formula.name \<times> ty list \<Rightarrow> (Formula.name, (nat \<times> ty list) list) mapping \<Rightarrow>
    (Formula.name, (nat \<times> ty list) list) mapping" where
  "ix_add (p, tys) m = Mapping.update p ((length tys, tys) # ix_list m p) m"

definition lsig_index :: "lsig \<Rightarrow> (Formula.name, (nat \<times> ty list) list) mapping" where
  "lsig_index S = fold ix_add (rev S) Mapping.empty"

definition index_lookup :: "(Formula.name, (nat \<times> ty list) list) mapping \<Rightarrow> Formula.name \<times> nat \<Rightarrow> ty list option" where
  "index_lookup I pn = map_option snd (find (\<lambda>(n, _). n = snd pn) (ix_list I (fst pn)))"

text \<open>The lookup the conversion uses: in the list for small signatures, in the mapping for the
  others.\<close>

definition lsig_lookup_fun :: "lsig \<Rightarrow> Formula.name \<times> nat \<Rightarrow> ty list option" where
  "lsig_lookup_fun S = (if length S < 32 then lsig_lookup S else (let I = lsig_index S in index_lookup I))"

lemma lsig_lookup_fun[simp]: "lsig_lookup_fun S = lsig_lookup S"
  by (simp add: lsig_lookup_fun_def index_lookup_lsig_index)

subsection \<open>Converting events\<close>

text \<open>A field of a given type. Integers are read as in @{theory Log_Parser.Log_Values}; floats
  by a parameter @{text pf}, the platform's reader, about which nothing is assumed.\<close>

definition conv_field :: "(bytes \<Rightarrow> double option) \<Rightarrow> ty \<Rightarrow> bytes \<Rightarrow> event_data option" where
  "conv_field pf t f = (case t of
     TInt \<Rightarrow> map_option (EInt \<circ> integer_of_int) (bint_of f)
   | TFloat \<Rightarrow> map_option EFloat (pf f)
   | TString \<Rightarrow> Some (EString (string8_of_bytes f)))"

text \<open>The field conversion uses the fused integer conversion.\<close>

lemma conv_field_code[code]: "conv_field pf t f = (case t of
     TInt \<Rightarrow> map_option EInt (ibint_of f)
   | TFloat \<Rightarrow> map_option EFloat (pf f)
   | TString \<Rightarrow> Some (EString (string8_of_bytes f)))"
  by (simp add: conv_field_def ibint_of_def option.map_comp comp_def split: ty.splits)

text \<open>The errors the conversion reports.\<close>

datatype verror = VE_PARSE perror | VE_TIMESTAMP bytes | VE_ORDER nat nat | VE_PREDICATE bytes nat
  | VE_FIELD bytes nat ty | VE_COMMAND bytes

text \<open>The fields of an event, by their types; on failure, the index of the first field that does
  not convert.\<close>

fun conv_fields :: "(bytes \<Rightarrow> double option) \<Rightarrow> ty list \<Rightarrow> bytes list \<Rightarrow> nat \<Rightarrow> (nat \<times> ty) + event_data list" where
  "conv_fields pf (t # ts) (f # fs) i = (case conv_field pf t f of
     None \<Rightarrow> Inl (i, t)
   | Some x \<Rightarrow> map_sum id (Cons x) (conv_fields pf ts fs (Suc i)))"
| "conv_fields pf _ _ i = Inr []"

definition conv_event :: "(bytes \<Rightarrow> double option) \<Rightarrow> (Formula.name \<times> nat \<Rightarrow> ty list option) \<Rightarrow>
    bytes \<times> bytes list \<Rightarrow> verror + Formula.event" where
  "conv_event pf L e = (case e of (p, fs) \<Rightarrow> let q = string8_of_bytes p in
     (case L (q, length fs) of
       None \<Rightarrow> Inl (VE_PREDICATE p (length fs))
     | Some tys \<Rightarrow> map_sum (\<lambda>(i, t). VE_FIELD p i t) (Pair q) (conv_fields pf tys fs 0)))"

fun conv_events :: "(bytes \<Rightarrow> double option) \<Rightarrow> (Formula.name \<times> nat \<Rightarrow> ty list option) \<Rightarrow>
    (bytes \<times> bytes list) list \<Rightarrow> verror + Formula.event list" where
  "conv_events pf L [] = Inr []"
| "conv_events pf L (e # es) = (case conv_event pf L e of
     Inl err \<Rightarrow> Inl err
   | Inr x \<Rightarrow> map_sum id (Cons x) (conv_events pf L es))"

subsection \<open>What an entry denotes\<close>

text \<open>The specification of the conversion, on the strings of the grammar
  (@{theory Log_Parser.Log_Grammar}): a field is read by its type, an event is one of the
  signature, with as many fields as its predicate has arguments, and an entry is a time point
  whose timestamp is a natural number (@{const nat_of_string}). A command denotes no time point.\<close>

definition field_of_string :: "(string \<Rightarrow> double option) \<Rightarrow> ty \<Rightarrow> string \<Rightarrow> event_data option" where
  "field_of_string pf t f = (case t of
     TInt \<Rightarrow> map_option (EInt \<circ> integer_of_int) (int_of_string f)
   | TFloat \<Rightarrow> map_option EFloat (pf f)
   | TString \<Rightarrow> Some (EString (Abs_string8 f)))"

definition event_of_string :: "(string \<Rightarrow> double option) \<Rightarrow> lsig \<Rightarrow> string \<times> string list \<Rightarrow> Formula.event option" where
  "event_of_string pf S e = (case e of (p, fs) \<Rightarrow>
     (case lsig_lookup S (Abs_string8 p, length fs) of
       None \<Rightarrow> None
     | Some tys \<Rightarrow> map_option (Pair (Abs_string8 p)) (those (map2 (field_of_string pf) tys fs))))"

definition tp_of_item :: "(string \<Rightarrow> double option) \<Rightarrow> lsig \<Rightarrow> string item \<Rightarrow> (Formula.database \<times> nat) option" where
  "tp_of_item pf S it = (case it of
     Entry ts evs \<Rightarrow> (case (nat_of_string ts, those (map (event_of_string pf S) evs)) of
       (Some t, Some xs) \<Rightarrow> Some (set xs, t)
     | _ \<Rightarrow> None)
   | Command c args \<Rightarrow> None)"

text \<open>The prefix a list of time points denotes if its timestamps do not decrease.\<close>

lift_definition prefix_of_list :: "('a \<times> nat) list \<Rightarrow> 'a prefix" is
  "\<lambda>xs. if sorted (map snd xs) then xs else []"
  by auto

text \<open>The prefix that a list of items denotes, followed by a last time point with no events at
  timestamp @{text t} if @{text "fin = Some t"}; @{const None} if an item denotes no time point
  or the timestamps decrease. The prefix a log denotes, with the events of the predicates that
  @{text K} accepts, is that of its items (@{const parse_log}).\<close>

definition prefix_of_items :: "(string \<Rightarrow> double option) \<Rightarrow> lsig \<Rightarrow> nat option \<Rightarrow> string item list \<Rightarrow>
    Formula.prefix option" where
  "prefix_of_items pf S fin items = (case those (map (tp_of_item pf S) items) of
     None \<Rightarrow> None
   | Some tps \<Rightarrow> (let tps' = tps @ (case fin of None \<Rightarrow> [] | Some t \<Rightarrow> [({}, t)]) in
       if sorted (map snd tps') then Some (prefix_of_list tps') else None))"

definition log_prefix :: "(string \<Rightarrow> bool) \<Rightarrow> (string \<Rightarrow> double option) \<Rightarrow> lsig \<Rightarrow> nat option \<Rightarrow> string \<Rightarrow>
    Formula.prefix option" where
  "log_prefix K pf S fin s = Option.bind (parse_log s) (\<lambda>items. prefix_of_items pf S fin (map (filter_item K) items))"

subsubsection \<open>The conversion implements the specification\<close>

text \<open>A function on byte strings as one on strings.\<close>

definition sf :: "(bytes \<Rightarrow> 'a) \<Rightarrow> string \<Rightarrow> 'a" where
  "sf f s = f (Abs_bytes s)"

lemma sf_Rep[simp]: "sf f (Rep_bytes x) = f x"
  by (simp add: sf_def Rep_bytes_inverse)

definition opt_of_sum :: "'a + 'b \<Rightarrow> 'b option" where
  "opt_of_sum x = (case x of Inl _ \<Rightarrow> None | Inr y \<Rightarrow> Some y)"

lemma opt_of_sum_simps[simp]: "opt_of_sum (Inl a) = None" "opt_of_sum (Inr b) = Some b"
  "opt_of_sum (map_sum f g x) = map_option g (opt_of_sum x)"
  by (auto simp: opt_of_sum_def split: sum.splits)

abbreviation abs_event :: "bytes \<times> bytes list \<Rightarrow> string \<times> string list" where
  "abs_event \<equiv> map_prod Rep_bytes (map Rep_bytes)"

text \<open>The code converts the events of a time point with an accumulator, so that the depth of the
  recursion does not grow with their number.\<close>

fun conv_events_acc :: "(bytes \<Rightarrow> double option) \<Rightarrow> (Formula.name \<times> nat \<Rightarrow> ty list option) \<Rightarrow>
    Formula.event list \<Rightarrow> (bytes \<times> bytes list) list \<Rightarrow> verror + Formula.event list" where
  "conv_events_acc pf L acc [] = Inr (rev acc)"
| "conv_events_acc pf L acc (e # es) = (case conv_event pf L e of
     Inl err \<Rightarrow> Inl err
   | Inr x \<Rightarrow> conv_events_acc pf L (x # acc) es)"

lemma conv_events_code[code]: "conv_events pf L es = conv_events_acc pf L [] es"
  by (cases "conv_events pf L es") (simp_all add: conv_events_acc)

text \<open>The first event of a predicate whose name the signature does not declare. Which error is
  reported for an entry follows MonPoly's parser, which checks the names of the predicates, then
  the order of the timestamps, and then the arity and the fields of each event in turn.\<close>

fun pred_error :: "lsig \<Rightarrow> (bytes \<times> bytes list) list \<Rightarrow> verror option" where
  "pred_error S [] = None"
| "pred_error S ((p, fs) # es) = (if list_ex (\<lambda>(q, _). str8_eq q (string8_of_bytes p)) S
     then pred_error S es else Some (VE_PREDICATE p (length fs)))"

text \<open>The error of the first event that does not convert, as MonPoly's parser reports it: it
  converts the fields against the types that the signature declares for the name of the predicate
  one after the other, and reports a wrong number of fields only if the fields they have in
  common convert.\<close>

fun conv_error :: "(bytes \<Rightarrow> double option) \<Rightarrow> (Formula.name \<times> nat \<Rightarrow> ty list option) \<Rightarrow> lsig \<Rightarrow>
    (bytes \<times> bytes list) list \<Rightarrow> verror option" where
  "conv_error pf L S [] = None"
| "conv_error pf L S ((p, fs) # es) = (let q = string8_of_bytes p in
     case L (q, length fs) of
       Some tys \<Rightarrow> (case conv_fields pf tys fs 0 of
         Inl (i, t) \<Rightarrow> Some (VE_FIELD p i t)
       | Inr _ \<Rightarrow> conv_error pf L S es)
     | None \<Rightarrow> (case find (\<lambda>(q', _). str8_eq q' q) S of
         None \<Rightarrow> Some (VE_PREDICATE p (length fs))
       | Some (_, tys) \<Rightarrow> (case conv_fields pf tys fs 0 of
           Inl (i, t) \<Rightarrow> Some (VE_FIELD p i t)
         | Inr _ \<Rightarrow> Some (VE_PREDICATE p (length fs)))))"

fun cmerge :: "'a comparator \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "cmerge c [] ys = ys"
| "cmerge c (x # xs) [] = x # xs"
| "cmerge c (x # xs) (y # ys) = (case c x y of
     order.Lt \<Rightarrow> x # cmerge c xs (y # ys)
   | order.Gt \<Rightarrow> y # cmerge c (x # xs) ys
   | order.Eq \<Rightarrow> x # cmerge c xs ys)"

fun cmerge_rev :: "'a comparator \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "cmerge_rev c acc [] ys = fold Cons ys acc"
| "cmerge_rev c acc (x # xs) [] = fold Cons (x # xs) acc"
| "cmerge_rev c acc (x # xs) (y # ys) = (case c x y of
     order.Lt \<Rightarrow> cmerge_rev c (x # acc) xs (y # ys)
   | order.Gt \<Rightarrow> cmerge_rev c (y # acc) (x # xs) ys
   | order.Eq \<Rightarrow> cmerge_rev c (x # acc) xs ys)"

fun cmerge_pairs :: "'a comparator \<Rightarrow> 'a list list \<Rightarrow> 'a list list \<Rightarrow> 'a list list" where
  "cmerge_pairs c acc (a # b # r) = cmerge_pairs c (cmerge_rev c [] a b # acc) r"
| "cmerge_pairs c acc [a] = rev a # acc"
| "cmerge_pairs c acc [] = acc"

function cmerge_all :: "'a comparator \<Rightarrow> bool \<Rightarrow> 'a list list \<Rightarrow> 'a list" where
  "cmerge_all c d [] = []"
| "cmerge_all c d [a] = (if d then rev a else a)"
| "cmerge_all c d (a # b # r) = cmerge_all c (\<not> d) (cmerge_pairs (if d then (\<lambda>x y. c y x) else c) [] (a # b # r))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(c, d, xss). length xss)") (auto simp: length_cmerge_pairs)

text \<open>The runs of increasing elements of the list.\<close>

fun runs_tc :: "'a comparator \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list list \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "runs_tc c x cur acc [] = rev (x # cur) # acc"
| "runs_tc c x cur acc (y # ys) = (if c x y = order.Lt then runs_tc c y (x # cur) acc ys
     else runs_tc c y [] (rev (x # cur) # acc) ys)"

definition csort :: "'a comparator \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "csort c xs = (case xs of [] \<Rightarrow> [] | x # ys \<Rightarrow> cmerge_all c False (runs_tc c x [] [] ys))"

subsection \<open>Databases\<close>

text \<open>The events of a time point, grouped by predicate and arity.\<close>

fun add_ev :: "Formula.event \<Rightarrow> ((Formula.name \<times> nat) \<times> event_data list list) list \<Rightarrow>
    ((Formula.name \<times> nat) \<times> event_data list list) list" where
  "add_ev (p, vs) [] = [((p, length vs), [vs])]"
| "add_ev (p, vs) ((k, xs) # g) = (if k = (p, length vs) then (k, vs # xs) # g else (k, xs) # add_ev (p, vs) g)"

definition group_evs :: "Formula.event list \<Rightarrow> ((Formula.name \<times> nat) \<times> event_data list list) list" where
  "group_evs evs = fold add_ev evs []"

text \<open>The code computes the key of an event once.\<close>

fun add_evk :: "Formula.name \<times> nat \<Rightarrow> event_data list \<Rightarrow> ((Formula.name \<times> nat) \<times> event_data list list) list \<Rightarrow>
    ((Formula.name \<times> nat) \<times> event_data list list) list" where
  "add_evk k vs [] = [(k, [vs])]"
| "add_evk k vs ((k', xs) # g) = (if str8_eq (fst k') (fst k) \<and> snd k' = snd k then (k', vs # xs) # g
     else (k', xs) # add_evk k vs g)"

definition build_db :: "Formula.event list \<Rightarrow> udatabase" where
  "build_db evs = fold (\<lambda>(k, xs) db. uinsert_table_into_db k (utable_of_list xs) db) (group_evs evs) uempty_db"

definition map_t :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "map_t f xs = rev (fold (\<lambda>x acc. f x # acc) xs [])"

lemma map_t[simp]: "map_t f xs = map f xs"
proof -
  have "fold (\<lambda>x acc. f x # acc) xs acc = rev (map f xs) @ acc" for acc
    by (induction xs arbitrary: acc) auto
  then show ?thesis
    by (simp add: map_t_def)
qed

function rbtreeify_fi :: "integer \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a, 'b) rbt \<times> ('a \<times> 'b) list"
  and rbtreeify_gi :: "integer \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a, 'b) rbt \<times> ('a \<times> 'b) list" where
  "rbtreeify_fi n kvs = (if n \<le> 0 then (RBT_Impl.Empty, kvs)
    else if n = 1 then (case kvs of (k, v) # kvs' \<Rightarrow> (RBT_Impl.Branch RBT_Impl.R RBT_Impl.Empty k v RBT_Impl.Empty, kvs'))
    else (case Code_Numeral.divmod_abs n 2 of (n', r) \<Rightarrow>
      if r = 0 then (case rbtreeify_fi n' kvs of (t1, (k, v) # kvs') \<Rightarrow>
        apfst (RBT_Impl.Branch RBT_Impl.B t1 k v) (rbtreeify_gi n' kvs'))
      else (case rbtreeify_fi n' kvs of (t1, (k, v) # kvs') \<Rightarrow>
        apfst (RBT_Impl.Branch RBT_Impl.B t1 k v) (rbtreeify_fi n' kvs'))))"
| "rbtreeify_gi n kvs = (if n \<le> 1 then (RBT_Impl.Empty, kvs)
    else (case Code_Numeral.divmod_abs n 2 of (n', r) \<Rightarrow>
      if r = 0 then (case rbtreeify_gi n' kvs of (t1, (k, v) # kvs') \<Rightarrow>
        apfst (RBT_Impl.Branch RBT_Impl.B t1 k v) (rbtreeify_gi n' kvs'))
      else (case rbtreeify_fi n' kvs of (t1, (k, v) # kvs') \<Rightarrow>
        apfst (RBT_Impl.Branch RBT_Impl.B t1 k v) (rbtreeify_gi n' kvs'))))"
  by pat_completeness auto
termination
  by (relation "measure (case_sum (\<lambda>(n, _). nat_of_integer n) (\<lambda>(n, _). nat_of_integer n))")
    (auto simp: divmod_abs_def nat_of_integer_half)

declare rbtreeify_fi.simps[simp del] rbtreeify_gi.simps[simp del]

fun ilen :: "integer \<Rightarrow> 'a list \<Rightarrow> integer" where
  "ilen acc [] = acc"
| "ilen acc (x # xs) = ilen (acc + 1) xs"

lemma ilen_code[code]: "ilen acc [] = acc" "ilen acc (x # xs) = ilen (idx_succ acc) xs"
  by (simp_all add: idx_succ_def)

definition rbtreeify_i :: "('a \<times> 'b) list \<Rightarrow> ('a, 'b) rbt" where
  "rbtreeify_i kvs = fst (rbtreeify_gi (ilen 1 kvs) kvs)"

definition urbt_sort :: "event_data list list \<Rightarrow> event_data list set_rbt" where
  "urbt_sort xs = rbt_of_sorted_list (csort ed_comparator xs)"

lemma urbt_sort_code[code abstract]:
  "RBT_Mapping2.impl_of (urbt_sort xs) = rbtreeify_i (map_t (\<lambda>x. (x, ())) (csort ed_comparator xs))"
proof -
  have "strict_sorted_by ed_comparator (csort ed_comparator xs)"
    using csort(2)[OF comparator_edl] strict_sorted_by_sorted_wrt[OF comparator_edl] by simp
  then show ?thesis
    by (simp add: urbt_sort_def rbt_of_sorted_list.rep_eq ccomp_etuple rbtreeify_i)
qed

lemma build_db_code_sort[code]: "build_db evs =
  fold (\<lambda>(k, xs) db. uinsert_table_into_db k (RBT_set (urbt_sort (rev xs))) db) (group_evs evs) uempty_db"
proof -
  have "utable_of_list xs = RBT_set (urbt_sort (rev xs))" for xs
    by (simp add: utable_of_list_def urbt_sort_def RBT_set_rbt_of_sorted_list ID_ccompare_etuple
        csort(1)[OF comparator_edl])
  then show ?thesis
    by (simp add: build_db_def)
qed

subsection \<open>Converting events faster\<close>

text \<open>The fields are converted by a tail-recursive loop, which computes the index of a field only
  if it does not convert, and the lengths of lists are counted as integers rather than as natural
  numbers.\<close>

fun conv_fields_a :: "(bytes \<Rightarrow> double option) \<Rightarrow> ty list \<Rightarrow> bytes list \<Rightarrow> event_data list \<Rightarrow>
    (nat \<times> ty) + event_data list" where
  "conv_fields_a pf (t # ts) (f # fs) acc = (case conv_field pf t f of
     None \<Rightarrow> Inl (length acc, t)
   | Some x \<Rightarrow> conv_fields_a pf ts fs (x # acc))"
| "conv_fields_a pf _ _ acc = Inr (rev acc)"

lemma conv_event_fast[code]: "conv_event pf L e = (case e of (p, fs) \<Rightarrow> let q = string8_of_bytes p; m = nat_of_integer (ilen 0 fs) in
     (case L (q, m) of
       None \<Rightarrow> Inl (VE_PREDICATE p m)
     | Some tys \<Rightarrow> map_sum (\<lambda>(i, t). VE_FIELD p i t) (Pair q) (conv_fields_a pf tys fs [])))"
proof -
  have A: "nat_of_integer (ilen 0 fs) = length fs" for fs :: "bytes list"
    by (simp add: ilen)
  have B: "conv_fields_a pf tys fs [] = conv_fields pf tys fs 0" for tys fs
    by (cases "conv_fields pf tys fs 0") (simp_all add: conv_fields_a)
  show ?thesis
    by (auto simp: conv_event_def A B Let_def split: prod.splits option.splits)
qed

lemma lsig_find_fast[code]: "lsig_find [] q n = None"
  "lsig_find ((p, tys) # S) q n = (if str8_eq p q \<and> ilen 0 tys = integer_of_nat n then Some tys else lsig_find S q n)"
  by (simp_all add: ilen integer_of_nat_eq_of_nat)

lemma add_ev_fast[code]: "add_ev (p, vs) g = add_evk (p, nat_of_integer (ilen 0 vs)) vs g"
  by (simp add: add_ev_code ilen)

subsection \<open>The predicates of the formula\<close>

text \<open>The predicates that occur freely in a formula (@{const Rewriting.preds}), as a list.\<close>

fun free_preds :: "'t Formula.formula \<Rightarrow> (Formula.name \<times> nat) list" where
  "free_preds (Formula.Pred e ts) = [(e, length ts)]"
| "free_preds (Formula.Let p \<phi> \<psi>) = free_preds \<phi> @ filter (\<lambda>x. x \<noteq> (p, Formula.nfv \<phi>)) (free_preds \<psi>)"
| "free_preds (Formula.Frz p \<phi> \<psi>) = free_preds \<phi> @ filter (\<lambda>x. x \<noteq> (p, Formula.nfv \<phi>)) (free_preds \<psi>)"
| "free_preds (Formula.LetPast p \<phi> \<psi>) = filter (\<lambda>x. x \<noteq> (p, Formula.nfv \<phi>)) (free_preds \<phi> @ free_preds \<psi>)"
| "free_preds (Formula.Eq t1 t2) = []"
| "free_preds (Formula.Less t1 t2) = []"
| "free_preds (Formula.LessEq t1 t2) = []"
| "free_preds (Formula.Neg \<phi>) = free_preds \<phi>"
| "free_preds (Formula.Or \<phi> \<psi>) = free_preds \<phi> @ free_preds \<psi>"
| "free_preds (Formula.And \<phi> \<psi>) = free_preds \<phi> @ free_preds \<psi>"
| "free_preds (Formula.Ands \<phi>s) = concat (map free_preds \<phi>s)"
| "free_preds (Formula.Exists t \<phi>) = free_preds \<phi>"
| "free_preds (Formula.Agg y \<omega> tys f \<phi>) = free_preds \<phi>"
| "free_preds (Formula.Prev I \<phi>) = free_preds \<phi>"
| "free_preds (Formula.Next I \<phi>) = free_preds \<phi>"
| "free_preds (Formula.Since \<phi> I \<psi>) = free_preds \<phi> @ free_preds \<psi>"
| "free_preds (Formula.Until \<phi> I \<psi>) = free_preds \<phi> @ free_preds \<psi>"
| "free_preds (Formula.Trigger \<phi> I \<psi>) = free_preds \<phi> @ free_preds \<psi>"
| "free_preds (Formula.Release \<phi> I \<psi>) = free_preds \<phi> @ free_preds \<psi>"
| "free_preds (Formula.MatchF I r) = regex_list free_preds r"
| "free_preds (Formula.MatchP I r) = regex_list free_preds r"
| "free_preds (Formula.TP t) = []"
| "free_preds (Formula.TS t) = []"

lemma set_free_preds[simp]: "set (free_preds \<phi>) = Rewriting.preds \<phi>"
  by (induction \<phi> rule: free_preds.induct) (auto simp: fv_regex_alt)

subsection \<open>The monitor on the log\<close>

text \<open>The configuration: which predicates' events to skip, the signature, the lookup of a
  predicate in it, and the reader of floats.\<close>

datatype vconf = VConf (vc_skip: "Formula.name \<Rightarrow> bool") (vc_lsig: lsig)
  (vc_lookup: "Formula.name \<times> nat \<Rightarrow> ty list option") (vc_pf: "bytes \<Rightarrow> double option")

text \<open>The parser keeps the events of the predicates whose names occur freely in the formula,
  and those of the predicates the signature does not declare, which the conversion reports. The
  events of the other predicates are neither converted nor checked.\<close>

definition vkeep :: "vconf \<Rightarrow> bytes \<Rightarrow> bool" where
  "vkeep cf b = (\<not> vc_skip cf (string8_of_bytes b))"

text \<open>The predicates whose events the parser skips: in a list for few predicates, in a set for
  many.\<close>

definition vskip :: "bool \<Rightarrow> tysym Formula.formula \<Rightarrow> lsig \<Rightarrow> Formula.name list" where
  "vskip filt \<phi> S = (if filt then (let F = set (map fst (free_preds \<phi>)) in filter (\<lambda>q. q \<notin> F) (map fst S))
     else [])"

definition vskip_fun :: "Formula.name list \<Rightarrow> Formula.name \<Rightarrow> bool" where
  "vskip_fun xs = (if length xs < 32 then (\<lambda>q. list_ex (str8_eq q) xs) else (let A = set xs in (\<lambda>q. q \<in> A)))"

text \<open>The state of the monitor proper is that of the executable monitor and the last timestamp; that of
  the whole monitor includes the parser's.\<close>

type_synonym vmstate = "emstate \<times> nat"
type_synonym vstate = "estate \<times> vmstate"

text \<open>The output: the verdicts of a time point, or an error at an offset in the input.\<close>

datatype vout = VO_VERDICTS "(nat \<times> ts \<times> utable) list" | VO_ERROR integer verror

definition vtp :: "integer \<Rightarrow> Formula.event list \<Rightarrow> nat \<Rightarrow> vmstate \<Rightarrow> vout \<times> vmstate" where
  "vtp sp xs t z = (if t < snd z then (VO_ERROR sp (VE_ORDER t (snd z)), z)
     else (case emstep (build_db xs, t) (fst z) of (vs, ust) \<Rightarrow> (VO_VERDICTS vs, (ust, t))))"

definition conv_entry :: "vconf \<Rightarrow> bytes \<Rightarrow> (bytes \<times> bytes list) list \<Rightarrow> verror + Formula.event list \<times> nat" where
  "conv_entry cf ts evs = (case bnat_of ts of
     None \<Rightarrow> Inl (VE_TIMESTAMP ts)
   | Some t \<Rightarrow> map_sum id (\<lambda>xs. (xs, t)) (conv_events (vc_pf cf) (vc_lookup cf) evs))"

text \<open>An item that does not denote a time point is reported, and the monitor's state does not
  change. If the events do not convert, the error reported is the first of, in the order of
  MonPoly's parser: an event of an undeclared predicate, a decreasing timestamp, and the first
  event that does not convert (@{const conv_error}).\<close>

definition vitem :: "vconf \<Rightarrow> out \<Rightarrow> vmstate \<Rightarrow> vout \<times> vmstate" where
  "vitem cf x z = (case x of
     O_ERROR pos e \<Rightarrow> (VO_ERROR pos (VE_PARSE e), z)
   | O_ITEM sp (Command c args) \<Rightarrow> (VO_ERROR sp (VE_COMMAND c), z)
   | O_ITEM sp (Entry ts evs) \<Rightarrow> (case bnat_of ts of
       None \<Rightarrow> (VO_ERROR sp (VE_TIMESTAMP ts), z)
     | Some t \<Rightarrow> (case conv_events (vc_pf cf) (vc_lookup cf) evs of
         Inl e \<Rightarrow> (VO_ERROR sp (case pred_error (vc_lsig cf) evs of
             Some e' \<Rightarrow> e'
           | None \<Rightarrow> if t < snd z then VE_ORDER t (snd z)
             else (case conv_error (vc_pf cf) (vc_lookup cf) (vc_lsig cf) evs of Some e' \<Rightarrow> e' | None \<Rightarrow> e)), z)
       | Inr xs \<Rightarrow> vtp sp xs t z)))"

fun vitems :: "vconf \<Rightarrow> out list \<Rightarrow> vmstate \<Rightarrow> vout list \<times> vmstate" where
  "vitems cf [] z = ([], z)"
| "vitems cf (x # xs) z = (case vitem cf x z of (v, st1) \<Rightarrow>
     (case vitems cf xs st1 of (vs, st2) \<Rightarrow> (v # vs, st2)))"

fun vitems_acc :: "vconf \<Rightarrow> out list \<Rightarrow> vmstate \<Rightarrow> vout list \<Rightarrow> vout list \<times> vmstate" where
  "vitems_acc cf [] z acc = (rev acc, z)"
| "vitems_acc cf (x # xs) z acc = (case vitem cf x z of (v, st1) \<Rightarrow> vitems_acc cf xs st1 (v # acc))"

lemma vitems_code[code]: "vitems cf xs z = vitems_acc cf xs z []"
  by (simp add: vitems_acc split: prod.splits)

text \<open>A chunk of the input, the end of the input, with an optional last time point with no events,
  and the initial state, if the formula is well-formed, its preparation succeeds, and the executable
  compiler covers it. Unless @{text filt} is set, the parser keeps all events.\<close>

definition vfeed_chunk :: "vconf \<Rightarrow> bytes \<Rightarrow> vstate \<Rightarrow> vout list \<times> vstate" where
  "vfeed_chunk cf s z = (case efeed_chunk (vkeep cf) s (fst z) of
     (xs, est) \<Rightarrow> (case vitems cf xs (snd z) of (vs, mst) \<Rightarrow> (vs, (est, mst))))"

definition vfinish :: "vconf \<Rightarrow> nat option \<Rightarrow> vstate \<Rightarrow> vout list" where
  "vfinish cf fin z = (case vitems cf (efinish (vkeep cf) (fst z)) (snd z) of
     (vs, mst) \<Rightarrow> vs @ (case fin of None \<Rightarrow> [] | Some t \<Rightarrow> [fst (vtp (fst (fst z)) [] t mst)]))"

datatype vinit_error = VI_WF | VI_PREPARE String.literal | VI_FRAGMENT nat

definition vinit :: "ipolicy \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> lsig \<Rightarrow> (bytes \<Rightarrow> double option) \<Rightarrow> tysym Formula.formula \<Rightarrow>
    vinit_error + vconf \<times> vstate" where
  "vinit ix mw rw filt S pf \<phi> = (if \<not> wf_formula \<phi> then Inl VI_WF else
     (case eminit_verimon ix mw rw (lsig_tsig S) \<phi> of
       Inl e \<Rightarrow> Inl (VI_PREPARE e)
     | Inr ust \<Rightarrow> (let n = efail_nodes (eabs (emstate_m ust)) in
         if n = 0 then Inr (VConf (vskip_fun (vskip filt \<phi> S)) S (lsig_lookup_fun S) pf, (einit, ust, 0))
         else Inl (VI_FRAGMENT n))))"

text \<open>For the theorems: the whole input, in chunks, and the verdicts in the output.\<close>

fun vfeed_chunks :: "vconf \<Rightarrow> bytes list \<Rightarrow> vstate \<Rightarrow> vout list \<times> vstate" where
  "vfeed_chunks cf [] z = ([], z)"
| "vfeed_chunks cf (s # ss) z = (case vfeed_chunk cf s z of (vs1, st1) \<Rightarrow>
     (case vfeed_chunks cf ss st1 of (vs2, st2) \<Rightarrow> (vs1 @ vs2, st2)))"

definition vrun :: "vconf \<Rightarrow> nat option \<Rightarrow> vstate \<Rightarrow> bytes list \<Rightarrow> vout list" where
  "vrun cf fin z ss = (case vfeed_chunks cf ss z of (vs, z') \<Rightarrow> vs @ vfinish cf fin z')"

definition vverdicts :: "vout list \<Rightarrow> (nat \<times> ts \<times> utable) list" where
  "vverdicts xs = concat (map (\<lambda>x. case x of VO_VERDICTS vs \<Rightarrow> vs | VO_ERROR _ _ \<Rightarrow> []) xs)"

definition has_verror :: "vout list \<Rightarrow> bool" where
  "has_verror xs \<longleftrightarrow> (\<exists>pos e. VO_ERROR pos e \<in> set xs)"

lemma vverdicts_simps[simp]:
  "vverdicts [] = []"
  "vverdicts (VO_VERDICTS vs # xs) = vs @ vverdicts xs"
  "vverdicts (VO_ERROR pos e # xs) = vverdicts xs"
  "vverdicts (xs @ ys) = vverdicts xs @ vverdicts ys"
  by (simp_all add: vverdicts_def)

text \<open>For the driver: the least offset in the input that later outputs may report, except that
  of the pending item -- that of the pending lexeme, if any, and otherwise the number of bytes
  read.\<close>

definition vpending :: "vstate \<Rightarrow> integer" where
  "vpending z = (case fst z of (b, l, _) \<Rightarrow> (case l of
     E_SIMPLE xs j t \<Rightarrow> t | E_QUOTED xs j t \<Rightarrow> t | E_ESCAPE xs j t \<Rightarrow> t | _ \<Rightarrow> b))"

lemma has_verror_simps[simp]:
  "\<not> has_verror []"
  "has_verror (x # xs) \<longleftrightarrow> (case x of VO_VERDICTS _ \<Rightarrow> has_verror xs | VO_ERROR _ _ \<Rightarrow> True)"
  "has_verror (xs @ ys) \<longleftrightarrow> has_verror xs \<or> has_verror ys"
  by (auto simp: has_verror_def split: vout.splits)

subsection \<open>Correctness\<close>

subsubsection \<open>The executable monitor on a list of time points\<close>

fun usteps :: "(Formula.event list \<times> nat) list \<Rightarrow> emstate \<Rightarrow> (nat \<times> ts \<times> utable) list \<times> emstate" where
  "usteps [] ust = ([], ust)"
| "usteps ((xs, t) # tps) ust = (case emstep (build_db xs, t) ust of (vs1, ust1) \<Rightarrow>
     (case usteps tps ust1 of (vs2, ust2) \<Rightarrow> (vs1 @ vs2, ust2)))"

subsubsection \<open>Items\<close>

definition conv_item :: "vconf \<Rightarrow> bytes item \<Rightarrow> (Formula.event list \<times> nat) option" where
  "conv_item cf x = (case x of Entry ts evs \<Rightarrow> opt_of_sum (conv_entry cf ts evs) | Command c args \<Rightarrow> None)"

definition fin_tps :: "nat option \<Rightarrow> (Formula.event list \<times> nat) list" where
  "fin_tps fin = (case fin of None \<Rightarrow> [] | Some t \<Rightarrow> [([], t)])"

lemma preds_map_formula[simp]: "Rewriting.preds (Formula.formula.map_formula f \<phi>) = Rewriting.preds \<phi>"
  by (induction \<phi>) (auto simp: fv_regex_alt regex.set_map)

subsection \<open>From the log to the verdicts\<close>

text \<open>The predicates whose events the parser keeps, as the specification states it, and the
  verdicts as the specification states them: tuples over the formula's free variables in the
  order in which @{const Formula.fv_list} lists them.  The executable monitor's tuples are over the
  same variables in ascending order.\<close>

definition keep_spec :: "bool \<Rightarrow> 't Formula.formula \<Rightarrow> lsig \<Rightarrow> string \<Rightarrow> bool" where
  "keep_spec filt \<phi> S p \<longleftrightarrow> \<not> filt \<or> Abs_string8 p \<in> fst ` Rewriting.preds \<phi> \<or> Abs_string8 p \<notin> fst ` set S"

definition vwiden :: "'t Formula.formula \<Rightarrow> (nat \<times> ts \<times> utable) list \<Rightarrow> (nat \<times> ts \<times> event_data table) list" where
  "vwiden \<phi> = map (\<lambda>(i, t, X). (i, t, etabw (Formula.fv_list \<phi>) (ecols (Formula.fv_list \<phi>)) X))"

text \<open>The signature, as the specification of the prepared formula uses it.\<close>

locale verimon_log = verimon_prepare rw "lsig_tsig S" \<phi>
  for rw :: bool and S :: lsig and \<phi> :: "tysym Formula.formula"
begin

context
  fixes mw :: bool
begin

end

end

end
(*>*)
