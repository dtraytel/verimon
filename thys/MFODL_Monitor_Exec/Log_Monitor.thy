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

  The main theorem, @{text verimon_log.vrun_log}, states that for the bytes of a log that
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
  @{theory MFODL_Monitor_Devel.Event_Data} compare strings byte-wise, as the characters' codes
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

lemma lsig_lookup_length: "lsig_lookup S (p, n) = Some tys \<Longrightarrow> length tys = n"
  by (induction S) (auto simp: lsig_lookup_def split: if_splits)

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

lemma ix_list_fold: "ix_list (fold ix_add xs m) p = [(length tys, tys). (q, tys) \<leftarrow> rev xs, q = p] @ ix_list m p"
proof (induction xs arbitrary: m)
  case (Cons x xs)
  obtain q tys where x: "x = (q, tys)"
    by (cases x)
  show ?case
    using Cons[of "ix_add x m"] by (auto simp: x ix_list_def split: if_splits)
qed simp

lemma ix_list_lsig_index: "ix_list (lsig_index S) p = [(length tys, tys). (q, tys) \<leftarrow> S, q = p]"
proof -
  have "ix_list Mapping.empty p = []"
    by (simp add: ix_list_def)
  then show ?thesis
    by (simp add: lsig_index_def ix_list_fold)
qed

lemma index_lookup_lsig_index: "index_lookup (lsig_index S) = lsig_lookup S"
proof (rule ext)
  fix pn :: "Formula.name \<times> nat"
  obtain p n where pn: "pn = (p, n)"
    by (cases pn)
  show "index_lookup (lsig_index S) pn = lsig_lookup S pn"
    unfolding pn index_lookup_def ix_list_lsig_index lsig_lookup_def
    by (induction S) (auto split: if_splits)
qed

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

lemma Rep_prefix_of_list: "sorted (map snd xs) \<Longrightarrow> Rep_prefix (prefix_of_list xs) = xs"
  by (simp add: prefix_of_list.rep_eq)

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

lemma conv_field_string: "conv_field pf t f = field_of_string (sf pf) t (Rep_bytes f)"
  by (cases t) (simp_all add: conv_field_def field_of_string_def bint_of_correct string8_of_bytes_def
    Rep_bytes_inverse)

lemma conv_fields_string: "length tys = length fs \<Longrightarrow>
  opt_of_sum (conv_fields pf tys fs i) = those (map2 (field_of_string (sf pf)) tys (map Rep_bytes fs))"
proof (induction pf tys fs i rule: conv_fields.induct)
  case (1 pf t ts f fs i)
  then show ?case
    by (auto simp: conv_field_string split: option.splits)
qed auto

abbreviation abs_event :: "bytes \<times> bytes list \<Rightarrow> string \<times> string list" where
  "abs_event \<equiv> map_prod Rep_bytes (map Rep_bytes)"

lemma conv_event_string: "opt_of_sum (conv_event pf (lsig_lookup S) e) = event_of_string (sf pf) S (abs_event e)"
proof -
  obtain p fs where e: "e = (p, fs)"
    by (cases e)
  show ?thesis
  proof (cases "lsig_lookup S (string8_of_bytes p, length fs)")
    case (Some tys)
    with conv_fields_string[OF lsig_lookup_length[OF Some], of pf 0] show ?thesis
      by (simp add: e conv_event_def event_of_string_def string8_of_bytes_def)
  qed (simp add: e conv_event_def event_of_string_def string8_of_bytes_def)
qed

lemma conv_events_string:
  "opt_of_sum (conv_events pf (lsig_lookup S) evs) = those (map (\<lambda>e. event_of_string (sf pf) S (abs_event e)) evs)"
proof (induction evs)
  case (Cons e evs)
  show ?case
  proof (cases "conv_event pf (lsig_lookup S) e")
    case (Inl err)
    with conv_event_string[of pf S e] show ?thesis
      by simp
  next
    case (Inr x)
    with conv_event_string[of pf S e, symmetric] Cons.IH[symmetric] show ?thesis
      by (simp add: opt_of_sum_def split: sum.splits)
  qed
qed simp

text \<open>The code converts the events of a time point with an accumulator, so that the depth of the
  recursion does not grow with their number.\<close>

fun conv_events_acc :: "(bytes \<Rightarrow> double option) \<Rightarrow> (Formula.name \<times> nat \<Rightarrow> ty list option) \<Rightarrow>
    Formula.event list \<Rightarrow> (bytes \<times> bytes list) list \<Rightarrow> verror + Formula.event list" where
  "conv_events_acc pf L acc [] = Inr (rev acc)"
| "conv_events_acc pf L acc (e # es) = (case conv_event pf L e of
     Inl err \<Rightarrow> Inl err
   | Inr x \<Rightarrow> conv_events_acc pf L (x # acc) es)"

lemma conv_events_acc: "conv_events_acc pf L acc es = map_sum id ((@) (rev acc)) (conv_events pf L es)"
  by (induction pf L acc es rule: conv_events_acc.induct) (auto simp: map_sum_def split: sum.splits)

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

subsection \<open>Sorting\<close>

text \<open>The tuples of a table are sorted, without duplicates, before the table is built, so that
  the tree is built in one pass. The merge sort below merges the runs of increasing elements of
  the list, so that a sorted list is one run, and is tail recursive, since a time point may hold
  many events: merging onto an accumulator reverses the order, so a round of merges turns lists
  that increase into lists that decrease, and the next round merges those with the comparator
  turned around. It drops duplicates as it merges, and is proved to sort strictly, so that the
  tree can be built without checking that it is.\<close>

lemma comparator_converse:
  assumes "comparator c"
  shows "comparator (\<lambda>x y. c y x)"
proof
  fix x y z
  show "invert_order (c y x) = c x y"
    by (rule comparator.sym[OF assms])
  show "c y x = order.Eq \<Longrightarrow> x = y"
    using comparator.weak_eq[OF assms, of y x] by simp
  show "c y x = order.Lt \<Longrightarrow> c z y = order.Lt \<Longrightarrow> c z x = order.Lt"
    using comparator.comp_trans[OF assms, of z y x] by simp
qed

fun cmerge :: "'a comparator \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "cmerge c [] ys = ys"
| "cmerge c (x # xs) [] = x # xs"
| "cmerge c (x # xs) (y # ys) = (case c x y of
     order.Lt \<Rightarrow> x # cmerge c xs (y # ys)
   | order.Gt \<Rightarrow> y # cmerge c (x # xs) ys
   | order.Eq \<Rightarrow> x # cmerge c xs ys)"

lemma set_cmerge: "comparator c \<Longrightarrow> set (cmerge c xs ys) = set xs \<union> set ys"
  by (induction c xs ys rule: cmerge.induct) (auto split: order.splits dest: comparator.weak_eq)

lemma sorted_cmerge: "comparator c \<Longrightarrow> sorted_wrt (lt_of_comp c) xs \<Longrightarrow> sorted_wrt (lt_of_comp c) ys \<Longrightarrow>
  sorted_wrt (lt_of_comp c) (cmerge c xs ys)"
proof (induction c xs ys rule: cmerge.induct)
  case (3 c x xs y ys)
  have tr: "lt_of_comp c a b \<Longrightarrow> lt_of_comp c b d \<Longrightarrow> lt_of_comp c a d" for a b d
    using comparator.comp_trans[OF 3(4), of a b d] by (simp add: comparator.Lt_lt_conv[OF 3(4)])
  note conv = comparator.Lt_lt_conv[OF 3(4)] comparator.Gt_lt_conv[OF 3(4)] comparator.eq_Eq_conv[OF 3(4)]
  from 3 show ?case
    by (auto simp: set_cmerge conv split: order.splits intro: tr)
qed simp_all

fun cmerge_rev :: "'a comparator \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "cmerge_rev c acc [] ys = fold Cons ys acc"
| "cmerge_rev c acc (x # xs) [] = fold Cons (x # xs) acc"
| "cmerge_rev c acc (x # xs) (y # ys) = (case c x y of
     order.Lt \<Rightarrow> cmerge_rev c (x # acc) xs (y # ys)
   | order.Gt \<Rightarrow> cmerge_rev c (y # acc) (x # xs) ys
   | order.Eq \<Rightarrow> cmerge_rev c (x # acc) xs ys)"

lemma cmerge_rev: "cmerge_rev c acc xs ys = rev (cmerge c xs ys) @ acc"
  by (induction c acc xs ys rule: cmerge_rev.induct) (auto simp: fold_Cons_rev split: order.splits)

fun cmerge_pairs :: "'a comparator \<Rightarrow> 'a list list \<Rightarrow> 'a list list \<Rightarrow> 'a list list" where
  "cmerge_pairs c acc (a # b # r) = cmerge_pairs c (cmerge_rev c [] a b # acc) r"
| "cmerge_pairs c acc [a] = rev a # acc"
| "cmerge_pairs c acc [] = acc"

lemma length_cmerge_pairs: "length (cmerge_pairs c acc xss) = length acc + (length xss + 1) div 2"
  by (induction c acc xss rule: cmerge_pairs.induct) auto

lemma set_cmerge_pairs: "comparator c \<Longrightarrow> \<Union> (set ` set (cmerge_pairs c acc xss)) = \<Union> (set ` set (acc @ xss))"
  by (induction c acc xss rule: cmerge_pairs.induct) (auto simp: cmerge_rev set_cmerge)

lemma sorted_rev_converse:
  "sorted_wrt (lt_of_comp (\<lambda>x y. c y x)) (rev xs) \<longleftrightarrow> sorted_wrt (lt_of_comp c) xs"
  "sorted_wrt (lt_of_comp c) (rev xs) \<longleftrightarrow> sorted_wrt (lt_of_comp (\<lambda>x y. c y x)) xs"
proof -
  have L: "lt_of_comp (\<lambda>x y. c y x) = (\<lambda>a b. lt_of_comp c b a)"
    by (simp add: fun_eq_iff lt_of_comp_def)
  show "sorted_wrt (lt_of_comp (\<lambda>x y. c y x)) (rev xs) \<longleftrightarrow> sorted_wrt (lt_of_comp c) xs"
    unfolding L sorted_wrt_rev by (rule refl)
  show "sorted_wrt (lt_of_comp c) (rev xs) \<longleftrightarrow> sorted_wrt (lt_of_comp (\<lambda>x y. c y x)) xs"
    unfolding L sorted_wrt_rev by (rule refl)
qed

lemma sorted_cmerge_pairs: "comparator c \<Longrightarrow> \<forall>a \<in> set xss. sorted_wrt (lt_of_comp c) a \<Longrightarrow>
    \<forall>a \<in> set acc. sorted_wrt (lt_of_comp (\<lambda>x y. c y x)) a \<Longrightarrow>
    \<forall>a \<in> set (cmerge_pairs c acc xss). sorted_wrt (lt_of_comp (\<lambda>x y. c y x)) a"
proof (induction c acc xss rule: cmerge_pairs.induct)
  case (1 c acc a b r)
  then show ?case
    using sorted_cmerge[of c a b] by (simp add: cmerge_rev sorted_rev_converse)
qed (simp_all add: sorted_rev_converse)

function cmerge_all :: "'a comparator \<Rightarrow> bool \<Rightarrow> 'a list list \<Rightarrow> 'a list" where
  "cmerge_all c d [] = []"
| "cmerge_all c d [a] = (if d then rev a else a)"
| "cmerge_all c d (a # b # r) = cmerge_all c (\<not> d) (cmerge_pairs (if d then (\<lambda>x y. c y x) else c) [] (a # b # r))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(c, d, xss). length xss)") (auto simp: length_cmerge_pairs)

lemma cmerge_all: "comparator c \<Longrightarrow> \<forall>a \<in> set xss. sorted_wrt (lt_of_comp (if d then (\<lambda>x y. c y x) else c)) a \<Longrightarrow>
  set (cmerge_all c d xss) = \<Union> (set ` set xss) \<and> sorted_wrt (lt_of_comp c) (cmerge_all c d xss)"
proof (induction c d xss rule: cmerge_all.induct)
  case (2 c d a)
  then show ?case
    by (cases d) (simp_all add: sorted_rev_converse)
next
  case (3 c d a b r)
  let ?c = "if d then (\<lambda>x y. c y x) else c"
  have comp: "comparator ?c"
    using 3(2) comparator_converse[OF 3(2)] by (cases d) simp_all
  have conv: "(\<lambda>x y. ?c y x) = (if \<not> d then (\<lambda>x y. c y x) else c)"
    by auto
  have "\<forall>a \<in> set (cmerge_pairs ?c [] (a # b # r)). sorted_wrt (lt_of_comp (if \<not> d then (\<lambda>x y. c y x) else c)) a"
    using sorted_cmerge_pairs[OF comp, of "a # b # r" "[]"] 3(3) unfolding conv by simp
  with 3(1)[OF 3(2)] set_cmerge_pairs[OF comp, of "[]" "a # b # r"] show ?case
    by simp
qed simp

lemma sorted_runs_tc: "comparator c \<Longrightarrow> sorted_wrt (lt_of_comp c) (rev (x # cur)) \<Longrightarrow>
  \<forall>a \<in> set acc. sorted_wrt (lt_of_comp c) a \<Longrightarrow> \<forall>a \<in> set (runs_tc c x cur acc ys). sorted_wrt (lt_of_comp c) a"
proof (induction c x cur acc ys rule: runs_tc.induct)
  case (2 c x cur acc y ys)
  show ?case
  proof (cases "c x y = order.Lt")
    case True
    have "lt_of_comp c z y" if "z \<in> set (x # cur)" for z
    proof -
      have "z = x \<or> lt_of_comp c z x"
        using that 2(4) by (auto simp: sorted_wrt_append)
      then show ?thesis
        using True comparator.comp_trans[OF 2(3), of z x y] by (auto simp: comparator.Lt_lt_conv[OF 2(3)])
    qed
    then have "sorted_wrt (lt_of_comp c) (rev (y # x # cur))"
      using 2(4) by (simp add: sorted_wrt_append)
    with True 2 show ?thesis
      by simp
  next
    case False
    have A: "\<forall>a \<in> set (rev (x # cur) # acc). sorted_wrt (lt_of_comp c) a"
      using 2(4,5) by simp
    have S: "sorted_wrt (lt_of_comp c) (rev [y])"
      by simp
    have R: "runs_tc c x cur acc (y # ys) = runs_tc c y [] (rev (x # cur) # acc) ys"
      using False by simp
    show ?thesis
      unfolding R by (rule 2(2)[OF False 2(3) S A])
  qed
qed simp

lemma set_runs_tc: "\<Union> (set ` set (runs_tc c x cur acc ys)) = Set.insert x (set cur \<union> \<Union> (set ` set acc) \<union> set ys)"
  by (induction c x cur acc ys rule: runs_tc.induct) auto

definition csort :: "'a comparator \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "csort c xs = (case xs of [] \<Rightarrow> [] | x # ys \<Rightarrow> cmerge_all c False (runs_tc c x [] [] ys))"

lemma csort:
  assumes "comparator c"
  shows "set (csort c xs) = set xs" and "sorted_wrt (lt_of_comp c) (csort c xs)"
proof -
  have "set (csort c xs) = set xs \<and> sorted_wrt (lt_of_comp c) (csort c xs)"
  proof (cases xs)
    case (Cons x ys)
    have "\<forall>a \<in> set (runs_tc c x [] [] ys). sorted_wrt (lt_of_comp c) a"
      by (rule sorted_runs_tc[OF assms]) simp_all
    then have "set (cmerge_all c False (runs_tc c x [] [] ys)) = \<Union> (set ` set (runs_tc c x [] [] ys)) \<and>
      sorted_wrt (lt_of_comp c) (cmerge_all c False (runs_tc c x [] [] ys))"
      using cmerge_all[OF assms, of "runs_tc c x [] [] ys" False] by simp
    then show ?thesis
      unfolding Cons csort_def set_runs_tc by simp
  qed (simp add: csort_def)
  then show "set (csort c xs) = set xs" and "sorted_wrt (lt_of_comp c) (csort c xs)"
    by simp_all
qed

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

lemma add_ev_code: "add_ev (p, vs) g = add_evk (p, length vs) vs g"
  by (induction "(p, vs)" g rule: add_ev.induct) (auto simp: str8_eq_def prod_eq_iff)

definition build_db :: "Formula.event list \<Rightarrow> udatabase" where
  "build_db evs = fold (\<lambda>(k, xs) db. uinsert_table_into_db k (utable_of_list xs) db) (group_evs evs) uempty_db"

text \<open>The groups have distinct keys, and each holds the tuples of its key.\<close>

lemma map_of_add_ev:
  "map_of (add_ev (p, vs) g) k =
   (if k = (p, length vs) then Some (vs # (case map_of g k of None \<Rightarrow> [] | Some xs \<Rightarrow> xs)) else map_of g k)"
  by (induction "(p, vs)" g rule: add_ev.induct) auto

lemma keys_add_ev: "fst ` set (add_ev (p, vs) g) = Set.insert (p, length vs) (fst ` set g)"
  by (induction "(p, vs)" g rule: add_ev.induct) auto

lemma distinct_add_ev: "distinct (map fst g) \<Longrightarrow> distinct (map fst (add_ev (p, vs) g))"
  by (induction "(p, vs)" g rule: add_ev.induct) (auto simp: keys_add_ev)

lemma map_of_fold_add_ev:
  "map_of (fold add_ev evs g) k = (case filter (\<lambda>e. (fst e, length (snd e)) = k) evs of
     [] \<Rightarrow> map_of g k
   | fs \<Rightarrow> Some (rev (map snd fs) @ (case map_of g k of None \<Rightarrow> [] | Some xs \<Rightarrow> xs)))"
proof (induction evs arbitrary: g)
  case (Cons e evs)
  obtain p vs where e: "e = (p, vs)"
    by (cases e)
  show ?case
    using Cons[of "add_ev (p, vs) g"]
    by (auto simp: e map_of_add_ev split: list.splits option.splits)
qed simp

lemma map_of_group_evs:
  "map_of (group_evs evs) k = (case filter (\<lambda>e. (fst e, length (snd e)) = k) evs of
     [] \<Rightarrow> None | fs \<Rightarrow> Some (rev (map snd fs)))"
  by (simp add: group_evs_def map_of_fold_add_ev split: list.splits)

lemma distinct_group_evs: "distinct (map fst (group_evs evs))"
proof -
  have "distinct (map fst (fold add_ev evs g))" if "distinct (map fst g)" for g
    using that
  proof (induction evs arbitrary: g)
    case (Cons e evs)
    then show ?case
      by (cases e) (simp add: distinct_add_ev)
  qed simp
  then show ?thesis
    by (simp add: group_evs_def)
qed

lemma lookup_fold_uinsert:
  assumes "distinct (map fst g)"
  shows "Mapping.lookup (fold (\<lambda>(k, xs) db. uinsert_table_into_db k (f xs) db) g db) k =
    (case map_of g k of Some xs \<Rightarrow> Some (case Mapping.lookup db k of None \<Rightarrow> [f xs] | Some T \<Rightarrow> map ((\<union>) (f xs)) T)
     | None \<Rightarrow> Mapping.lookup db k)"
  using assms
proof (induction g arbitrary: db)
  case (Cons a g)
  obtain k' xs' where a: "a = (k', xs')"
    by (cases a)
  from Cons.prems a have "k' \<notin> fst ` set g"
    by auto
  then have "map_of g k' = None"
    by (simp add: map_of_eq_None_iff)
  with Cons a show ?case
    by (auto simp: uinsert_table_into_db_def lookup_update_mapping_with split: option.splits)
qed simp

theorem build_db_mk_db: "build_db evs = mk_db (set evs)"
proof (rule mapping_eqI)
  fix k :: "Formula.name \<times> nat"
  obtain p n where k: "k = (p, n)"
    by (cases k)
  have lk: "Mapping.lookup (build_db evs) k = map_option (\<lambda>xs. [set xs]) (map_of (group_evs evs) k)"
    using lookup_fold_uinsert[of "group_evs evs" "\<lambda>xs. utable_of_list xs" uempty_db k] distinct_group_evs
    by (auto simp: build_db_def uempty_db_def utable_of_list_def ID_ccompare_etuple
      split: option.splits)
  have mk: "Mapping.lookup (mk_db (set evs)) (p, n) = (if \<exists>ts. (p, ts) \<in> set evs \<and> n = length ts
    then Some [{ts. (p, ts) \<in> set evs \<and> n = length ts}] else None)"
    by (simp add: Mapping.lookup.rep_eq mk_db.rep_eq)
  have f: "set (map snd (filter (\<lambda>e. (fst e, length (snd e)) = k) evs)) = {ts. (p, ts) \<in> set evs \<and> n = length ts}"
    by (force simp: k)
  have e: "filter (\<lambda>e. (fst e, length (snd e)) = k) evs = [] \<longleftrightarrow> \<not> (\<exists>ts. (p, ts) \<in> set evs \<and> n = length ts)"
    by (force simp: k filter_empty_conv)
  show "Mapping.lookup (build_db evs) k = Mapping.lookup (mk_db (set evs)) k"
  proof (cases "filter (\<lambda>e. (fst e, length (snd e)) = k) evs = []")
    case True
    then show ?thesis
      using lk mk e by (simp add: map_of_group_evs k)
  next
    case False
    then have "map_of (group_evs evs) k = Some (rev (map snd (filter (\<lambda>e. (fst e, length (snd e)) = k) evs)))"
      by (simp add: map_of_group_evs split: list.splits)
    then show ?thesis
      using lk mk e f False by (simp add: k)
  qed
qed

definition map_t :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "map_t f xs = rev (fold (\<lambda>x acc. f x # acc) xs [])"

lemma map_t[simp]: "map_t f xs = map f xs"
proof -
  have "fold (\<lambda>x acc. f x # acc) xs acc = rev (map f xs) @ acc" for acc
    by (induction xs arbitrary: acc) auto
  then show ?thesis
    by (simp add: map_t_def)
qed

subsection \<open>Building the tables faster\<close>

text \<open>The tree of a table is built by @{const rbtreeify}, whose generated code computes with the
  natural numbers of the generated code, which wrap the integers. The copy below computes with the
  integers directly, and is proved to build the same tree.\<close>

lemma nat_of_integer_half: "\<not> n \<le> 0 \<Longrightarrow> n \<noteq> 1 \<Longrightarrow> nat_of_integer (n div 2) < nat_of_integer n"
  "\<not> n \<le> 1 \<Longrightarrow> nat_of_integer (n div 2) < nat_of_integer n"
  including integer.lifting by (transfer, auto)+

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

lemma integer_of_nat_rbt_simps:
  "integer_of_nat n \<le> 0 \<longleftrightarrow> n = 0" "integer_of_nat n \<le> 1 \<longleftrightarrow> n = 0 \<or> n = 1"
  "integer_of_nat n = 1 \<longleftrightarrow> n = 1"
  "Code_Numeral.divmod_abs (integer_of_nat n) 2 = (integer_of_nat (n div 2), integer_of_nat (n mod 2))"
  "integer_of_nat m = 0 \<longleftrightarrow> m = 0"
  by (simp_all add: integer_eq_iff less_eq_integer.rep_eq divmod_abs_def integer_of_nat.rep_eq
      zdiv_int zmod_int le_Suc_eq)

lemma rbtreeify_fi: "rbtreeify_fi (integer_of_nat n) kvs = rbtreeify_f n kvs"
  and rbtreeify_gi: "rbtreeify_gi (integer_of_nat n) kvs = rbtreeify_g n kvs"
proof -
  have fg: "rbtreeify_fi (integer_of_nat n) kvs = rbtreeify_f n kvs \<and>
      rbtreeify_gi (integer_of_nat n) kvs = rbtreeify_g n kvs" for n and kvs :: "('a \<times> 'b) list"
  proof (induction n arbitrary: kvs rule: less_induct)
    case (less n kvs)
    consider "n = 0" | "n = 1" | "1 < n"
      by linarith
    then show ?case
    proof cases
      case 3
      then have ne: "n \<noteq> 0" "n \<noteq> 1" and lt: "n div 2 < n"
        by simp_all
      show ?thesis
      proof
        show "rbtreeify_fi (integer_of_nat n) kvs = rbtreeify_f n kvs"
          by (subst rbtreeify_fi.simps, subst rbtreeify_f.simps)
            (simp only: integer_of_nat_rbt_simps less.IH[OF lt] ne if_False prod.case)
        show "rbtreeify_gi (integer_of_nat n) kvs = rbtreeify_g n kvs"
          by (subst rbtreeify_gi.simps, subst rbtreeify_g.simps)
            (simp only: integer_of_nat_rbt_simps less.IH[OF lt] ne if_False prod.case simp_thms)
      qed
    qed (simp_all add: rbtreeify_fi.simps rbtreeify_gi.simps rbtreeify_f.simps rbtreeify_g.simps
      integer_of_nat_rbt_simps)
  qed
  show "rbtreeify_fi (integer_of_nat n) kvs = rbtreeify_f n kvs"
    using fg by simp
  show "rbtreeify_gi (integer_of_nat n) kvs = rbtreeify_g n kvs"
    using fg by simp
qed

fun ilen :: "integer \<Rightarrow> 'a list \<Rightarrow> integer" where
  "ilen acc [] = acc"
| "ilen acc (x # xs) = ilen (acc + 1) xs"

lemma ilen: "ilen acc xs = acc + integer_of_nat (length xs)"
  by (induction acc xs rule: ilen.induct) (simp_all add: integer_of_nat_eq_of_nat)

lemma ilen_code[code]: "ilen acc [] = acc" "ilen acc (x # xs) = ilen (idx_succ acc) xs"
  by (simp_all add: idx_succ_def)

definition rbtreeify_i :: "('a \<times> 'b) list \<Rightarrow> ('a, 'b) rbt" where
  "rbtreeify_i kvs = fst (rbtreeify_gi (ilen 1 kvs) kvs)"

lemma rbtreeify_i: "rbtreeify_i kvs = rbtreeify kvs"
proof -
  have "ilen 1 kvs = integer_of_nat (Suc (length kvs))"
    by (simp add: ilen integer_of_nat_eq_of_nat)
  then show ?thesis
    by (simp add: rbtreeify_i_def rbtreeify_def rbtreeify_gi)
qed

text \<open>The tables of a time point are built with this sort and tree construction. The groups
  hold their tuples in the reverse order of the log; the code reverses them before sorting them,
  so that tuples that come sorted in the log are sorted in linear time.\<close>

lemma comparator_edl: "comparator ed_comparator"
  by (rule ID_ccompare'[OF ID_ccompare_etuple])

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

lemma conv_fields_a: "conv_fields_a pf tys fs acc = map_sum id ((@) (rev acc)) (conv_fields pf tys fs (length acc))"
  by (induction pf tys fs acc rule: conv_fields_a.induct) (auto simp: sum.map_comp comp_def split: option.splits)

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

lemma vskip_fun: "vskip_fun xs q \<longleftrightarrow> q \<in> set xs"
  by (auto simp: vskip_fun_def str8_eq_def list_ex_iff)

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

lemma vitems_acc: "vitems_acc cf xs z acc = (case vitems cf xs z of (vs, z') \<Rightarrow> (rev acc @ vs, z'))"
  by (induction cf xs z acc rule: vitems_acc.induct) (auto split: prod.splits)

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

definition vinit :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> lsig \<Rightarrow> (bytes \<Rightarrow> double option) \<Rightarrow> tysym Formula.formula \<Rightarrow>
    vinit_error + vconf \<times> vstate" where
  "vinit mw rw filt S pf \<phi> = (if \<not> wf_formula \<phi> then Inl VI_WF else
     (case eminit_verimon mw rw (lsig_tsig S) \<phi> of
       Inl e \<Rightarrow> Inl (VI_PREPARE e)
     | Inr ust \<Rightarrow> (let n = efail_nodes (emstate_m ust) in
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

lemma usteps_append: "usteps (tps1 @ tps2) ust = (case usteps tps1 ust of (vs1, ust1) \<Rightarrow>
  (case usteps tps2 ust1 of (vs2, ust2) \<Rightarrow> (vs1 @ vs2, ust2)))"
  by (induction tps1 ust rule: usteps.induct) (auto split: prod.splits)

lemma usteps_dmsteps0:
  "fst (usteps tps ust) = emsteps0_stateless (map (apfst set) tps) (ust)"
proof (induction tps arbitrary: ust)
  case (Cons tp tps)
  obtain xs t where tp: "tp = (xs, t)"
    by (cases tp)
  obtain vs1 ust1 where u: "emstep (build_db xs, t) ust = (vs1, ust1)"
    by fastforce
  have "emstep (mk_db (set xs), t) ust = (vs1, ust1)"
    using u by (simp add: build_db_mk_db)
  then show ?case
    using Cons.IH[of ust1] u by (cases "usteps tps ust1") (simp add: tp)
qed simp

subsubsection \<open>Items\<close>

definition conv_item :: "vconf \<Rightarrow> bytes item \<Rightarrow> (Formula.event list \<times> nat) option" where
  "conv_item cf x = (case x of Entry ts evs \<Rightarrow> opt_of_sum (conv_entry cf ts evs) | Command c args \<Rightarrow> None)"

lemma conv_item_string:
  assumes "vc_lookup cf = lsig_lookup (vc_lsig cf)"
  shows "map_option (apfst set) (conv_item cf x) = tp_of_item (sf (vc_pf cf)) (vc_lsig cf) (map_item Rep_bytes x)"
proof (cases x)
  case (Entry ts evs)
  have "those (map (event_of_string (sf (vc_pf cf)) (vc_lsig cf)) (map abs_event evs)) =
    opt_of_sum (conv_events (vc_pf cf) (vc_lookup cf) evs)"
    by (simp add: assms conv_events_string comp_def)
  then show ?thesis
    by (auto simp: Entry conv_item_def tp_of_item_def conv_entry_def bnat_of_correct opt_of_sum_def
      split: option.splits sum.splits)
qed (simp add: conv_item_def tp_of_item_def)

lemma vitem_None: "conv_item cf e = None \<Longrightarrow> \<exists>err. vitem cf (O_ITEM sp e) z = (VO_ERROR sp err, z)"
  by (auto simp: vitem_def conv_item_def conv_entry_def opt_of_sum_def split: item.splits sum.splits option.splits)

lemma vitem_Some:
  assumes "conv_item cf e = Some (xs, t)"
  shows "vitem cf (O_ITEM sp e) z = vtp sp xs t z"
proof -
  obtain ts evs where e: "e = Entry ts evs"
    using assms by (cases e) (auto simp: conv_item_def)
  obtain t' where t: "bnat_of ts = Some t'"
    using assms by (cases "bnat_of ts") (auto simp: e conv_item_def conv_entry_def)
  obtain ys where c: "conv_events (vc_pf cf) (vc_lookup cf) evs = Inr ys"
    using assms by (cases "conv_events (vc_pf cf) (vc_lookup cf) evs") (auto simp: e t conv_item_def conv_entry_def)
  have "ys = xs" "t' = t"
    using assms by (simp_all add: e t c conv_item_def conv_entry_def)
  then show ?thesis
    by (simp add: vitem_def e t c)
qed

lemma vitems_append: "vitems cf (xs @ ys) z = (case vitems cf xs z of (vs1, z1) \<Rightarrow>
  (case vitems cf ys z1 of (vs2, z2) \<Rightarrow> (vs1 @ vs2, z2)))"
  by (induction cf xs z rule: vitems.induct) (auto split: prod.splits)

lemma vitems_has_err: "has_err xs \<Longrightarrow> has_verror (fst (vitems cf xs z))"
proof (induction cf xs z rule: vitems.induct)
  case (2 cf x xs z)
  obtain v z1 where v: "vitem cf x z = (v, z1)"
    by (metis prod.exhaust)
  show ?case
  proof (cases x)
    case (O_ITEM sp e)
    with "2.prems" have "has_err xs"
      by simp
    with "2.IH"[OF v[symmetric]] v show ?thesis
      by (auto split: prod.splits vout.splits)
  qed (use v in \<open>auto simp: vitem_def split: prod.splits\<close>)
qed simp

text \<open>Without errors, the items are converted and their timestamps do not decrease, and the
  verdicts are those of the monitor on the time points.\<close>

lemma vitems_ok:
  assumes "oks xs = Some es" "vitems cf xs (ust, lt) = (vs, z')" "\<not> has_verror vs"
  shows "\<exists>tps. those (map (conv_item cf) es) = Some tps \<and> sorted (lt # map snd tps) \<and>
    vverdicts vs = fst (usteps tps ust) \<and> z' = (snd (usteps tps ust), last (lt # map snd tps))"
  using assms
proof (induction xs arbitrary: es ust lt vs z')
  case (Cons x xs)
  from Cons.prems(1) obtain sp e es' where x: "x = O_ITEM sp e" and es: "es = e # es'"
    and oks: "oks xs = Some es'"
    by (cases x) auto
  obtain v z1 where v: "vitem cf x (ust, lt) = (v, z1)"
    by (metis prod.exhaust)
  obtain vs' where vs': "vitems cf xs z1 = (vs', z')" and vs: "vs = v # vs'"
    using Cons.prems(2) v by (auto split: prod.splits)
  have ok: "\<not> has_verror (v # vs')"
    using Cons.prems(3) vs by simp
  obtain ys t where c: "conv_item cf e = Some (ys, t)"
    using vitem_None[of cf e sp "(ust, lt)"] v ok x by (cases "conv_item cf e") auto
  obtain vs1 ust1 where u: "emstep (build_db ys, t) ust = (vs1, ust1)"
    by fastforce
  have t: "\<not> t < lt" and v1: "v = VO_VERDICTS vs1" and z1: "z1 = (ust1, t)"
    using v ok vitem_Some[OF c, of sp "(ust, lt)"] u x by (auto simp: vtp_def split: if_splits)
  have "\<not> has_verror vs'"
    using ok by (auto split: vout.splits)
  then obtain tps where "those (map (conv_item cf) es') = Some tps" "sorted (t # map snd tps)"
    "vverdicts vs' = fst (usteps tps ust1)" "z' = (snd (usteps tps ust1), last (t # map snd tps))"
    using Cons.IH[OF oks vs'[unfolded z1]] by blast
  then show ?case
    using c t u es vs v1
    by (intro exI[of _ "(ys, t) # tps"]) (auto split: prod.splits)
qed simp

lemma vitems_noerr:
  assumes "oks xs = Some es" "those (map (conv_item cf) es) = Some tps" "sorted (lt # map snd tps)"
  shows "\<not> has_verror (fst (vitems cf xs (ust, lt)))"
  using assms
proof (induction xs arbitrary: es tps ust lt)
  case (Cons x xs)
  from Cons.prems(1) obtain sp e es' where x: "x = O_ITEM sp e" and es: "es = e # es'"
    and oks: "oks xs = Some es'"
    by (cases x) auto
  from Cons.prems(2) es obtain ys t tps' where c: "conv_item cf e = Some (ys, t)"
    and tps: "those (map (conv_item cf) es') = Some tps'" "tps = (ys, t) # tps'"
    by (auto split: option.splits)
  obtain vs1 ust1 where u: "emstep (build_db ys, t) ust = (vs1, ust1)"
    by fastforce
  from Cons.prems(3) tps have "lt \<le> t" "sorted (t # map snd tps')"
    by auto
  with Cons.IH[OF oks tps(1), of t ust1] vitem_Some[OF c, of sp "(ust, lt)"] u x show ?case
    by (auto simp: vtp_def split: prod.splits)
qed simp

subsubsection \<open>The prefix a log denotes is well typed and finite\<close>

lemma those_map_option: "those (map (map_option g) xs) = map_option (map g) (those xs)"
  by (induction xs) (simp_all add: option.map_comp comp_def split: option.splits)

lemma those_Some_in: "those (map f xs) = Some ys \<Longrightarrow> y \<in> set ys \<Longrightarrow> \<exists>x\<in>set xs. f x = Some y"
  by (induction xs arbitrary: ys) (auto split: option.splits)

lemma field_of_string_ty: "field_of_string pf t f = Some x \<Longrightarrow> ty_of x = t"
  by (cases t) (auto simp: field_of_string_def)

lemma those_map2_field_of_string:
  "those (map2 (field_of_string pf) tys fs) = Some xs \<Longrightarrow> length tys = length fs \<Longrightarrow> wty_tuple tys xs"
proof (induction tys arbitrary: fs xs)
  case (Cons t tys)
  then obtain f fs' where "fs = f # fs'"
    by (cases fs) auto
  with Cons show ?case
    by (auto simp: wty_tuple_def field_of_string_ty split: option.splits)
qed (simp add: wty_tuple_def)

lemma event_of_string_wty:
  assumes "event_of_string pf S e = Some x"
  shows "wty_event (lsig_lookup S) (fst x) (snd x)"
proof -
  obtain p fs where e: "e = (p, fs)"
    by (cases e)
  with assms obtain tys xs where tys: "lsig_lookup S (Abs_string8 p, length fs) = Some tys"
    and xs: "those (map2 (field_of_string pf) tys fs) = Some xs" and x: "x = (Abs_string8 p, xs)"
    by (auto simp: event_of_string_def split: option.splits)
  have w: "wty_tuple tys xs"
    using those_map2_field_of_string[OF xs lsig_lookup_length[OF tys]] .
  then have "length xs = length fs"
    using lsig_lookup_length[OF tys] by (simp add: wty_tuple_def list_all2_lengthD)
  with tys w x show ?thesis
    by (simp add: wty_event_def)
qed

lemma tp_of_item_wty: "tp_of_item pf S it = Some tp \<Longrightarrow> wty_db (lsig_lookup S) (fst tp) \<and> finite (fst tp)"
  by (fastforce simp: tp_of_item_def wty_db_def dest: those_Some_in event_of_string_wty
    split: item.splits option.splits)

lemma prefix_of_items_Some:
  assumes "prefix_of_items pf S fin items = Some \<pi>"
  obtains tps where "those (map (tp_of_item pf S) items) = Some tps"
    and "sorted (map snd (tps @ (case fin of None \<Rightarrow> [] | Some t \<Rightarrow> [({}, t)])))"
    and "Rep_prefix \<pi> = tps @ (case fin of None \<Rightarrow> [] | Some t \<Rightarrow> [({}, t)])"
  using assms by (auto simp: prefix_of_items_def Let_def Rep_prefix_of_list split: option.splits if_splits)

lemma prefix_of_items_wty:
  assumes "prefix_of_items pf S fin items = Some \<pi>"
  shows "wty_prefix (lsig_lookup S) \<pi>" and "pfinite \<pi>"
proof -
  obtain tps where tps: "those (map (tp_of_item pf S) items) = Some tps"
    and R: "Rep_prefix \<pi> = tps @ (case fin of None \<Rightarrow> [] | Some t \<Rightarrow> [({}, t)])"
    using prefix_of_items_Some[OF assms] by blast
  have H: "wty_db (lsig_lookup S) (fst tp) \<and> finite (fst tp)" if "tp \<in> set (Rep_prefix \<pi>)" for tp
  proof -
    from that R consider "tp \<in> set tps" | "fst tp = {}"
      by (auto split: option.splits)
    then show ?thesis
    proof cases
      case 1
      then obtain it where "tp_of_item pf S it = Some tp"
        using those_Some_in[OF tps] by blast
      then show ?thesis
        by (rule tp_of_item_wty)
    qed (simp add: wty_db_def)
  qed
  then show "wty_prefix (lsig_lookup S) \<pi>" and "pfinite \<pi>"
    by (simp_all add: wty_prefix.rep_eq pfinite.rep_eq)
qed

subsubsection \<open>The monitor on the log implements the kernel on the prefix\<close>

lemma vfeed_chunks_efeed:
  "vfeed_chunks cf ss (est, z) = (case efeed_chunks (vkeep cf) ss est of (xs, est') \<Rightarrow>
     (case vitems cf xs z of (vs, z') \<Rightarrow> (vs, (est', z'))))"
proof (induction ss arbitrary: est z)
  case (Cons s ss)
  then show ?case
    by (auto simp: vfeed_chunk_def vitems_append split: prod.splits)
qed simp

lemma vrun_eparse:
  obtains pos where "vrun cf fin (einit, z) ss = (case vitems cf (eparse (vkeep cf) ss) z of
    (vs, z') \<Rightarrow> vs @ (case fin of None \<Rightarrow> [] | Some t \<Rightarrow> [fst (vtp pos [] t z')]))"
proof -
  obtain xs est' where e: "efeed_chunks (vkeep cf) ss einit = (xs, est')"
    by (metis prod.exhaust)
  show ?thesis
    by (rule that[of "fst est'"])
      (auto simp: vrun_def vfeed_chunks_efeed e eparse_def vfinish_def vitems_append
        split: prod.splits option.splits)
qed

lemma sorted_snoc_last: "sorted ((a :: nat) # ys) \<Longrightarrow> sorted ((a # ys) @ [t]) \<longleftrightarrow> last (a # ys) \<le> t"
proof (induction ys arbitrary: a)
  case (Cons y ys)
  then show ?case
    by auto
qed simp

lemma those_conv_item:
  assumes "vc_lookup cf = lsig_lookup (vc_lsig cf)"
  shows "those (map (tp_of_item (sf (vc_pf cf)) (vc_lsig cf)) (abs_items es)) =
    map_option (map (apfst set)) (those (map (conv_item cf) es))"
  by (simp add: comp_def conv_item_string[OF assms, symmetric] those_map_option[symmetric])

definition fin_tps :: "nat option \<Rightarrow> (Formula.event list \<times> nat) list" where
  "fin_tps fin = (case fin of None \<Rightarrow> [] | Some t \<Rightarrow> [([], t)])"

lemma prefix_of_items_abs:
  assumes "vc_lookup cf = lsig_lookup (vc_lsig cf)"
  shows "prefix_of_items (sf (vc_pf cf)) (vc_lsig cf) fin (abs_items es) =
    (case those (map (conv_item cf) es) of
      None \<Rightarrow> None
    | Some tps \<Rightarrow> (let tps' = map (apfst set) (tps @ fin_tps fin) in
        if sorted (map snd tps') then Some (prefix_of_list tps') else None))"
  unfolding prefix_of_items_def those_conv_item[OF assms]
  by (auto simp: fin_tps_def Let_def split: option.splits)

lemma vitems_cases:
  fixes cf fin pos ust xs
  assumes lk: "vc_lookup cf = lsig_lookup (vc_lsig cf)"
  defines "V \<equiv> (case vitems cf xs (ust, 0) of
      (vs, z') \<Rightarrow> vs @ (case fin of None \<Rightarrow> [] | Some t \<Rightarrow> [fst (vtp pos [] t z')]))"
    and "L \<equiv> Option.bind (oks xs) (\<lambda>es. prefix_of_items (sf (vc_pf cf)) (vc_lsig cf) fin (abs_items es))"
  obtains (err) "has_verror V" "L = None"
  | (ok) \<pi> where "\<not> has_verror V" "L = Some \<pi>" "vverdicts V = emonitor (ust) \<pi>"
proof -
  let ?xs = xs
  obtain vs z' where vs: "vitems cf ?xs (ust, 0) = (vs, z')"
    by (metis prod.exhaust)
  have V: "V = vs @ (case fin of None \<Rightarrow> [] | Some t \<Rightarrow> [fst (vtp pos [] t z')])"
    by (simp add: V_def vs)
  show thesis
  proof (cases "oks ?xs")
    case None
    then have "has_verror V"
      using vitems_has_err[of ?xs cf "(ust, 0)"] vs V by (simp add: oks_None_iff)
    moreover from None have "L = None"
      by (simp add: L_def)
    ultimately show thesis
      by (rule err)
  next
    case (Some es)
    then have L: "L = prefix_of_items (sf (vc_pf cf)) (vc_lsig cf) fin (abs_items es)"
      by (simp add: L_def)
    show thesis
    proof (cases "those (map (conv_item cf) es)")
      case None
      then have "has_verror vs"
        using vitems_ok[OF Some vs] by force
      then have "has_verror V"
        using V vs by simp
      moreover from None have "L = None"
        by (simp add: L prefix_of_items_abs[OF lk])
      ultimately show thesis
        by (rule err)
    next
      case (Some tps)
      note tps = this
      let ?tps = "tps @ fin_tps fin"
      have L': "L = (if sorted (map snd ?tps) then Some (prefix_of_list (map (apfst set) ?tps)) else None)"
        by (simp add: L prefix_of_items_abs[OF lk] tps Let_def comp_def)
      have A: "\<not> has_verror vs \<longleftrightarrow> sorted (0 # map snd tps)"
        using vitems_ok[OF \<open>oks ?xs = Some es\<close> vs] vitems_noerr[OF \<open>oks ?xs = Some es\<close> tps, of 0 ust] vs tps
        by fastforce
      have B: "\<not> has_verror vs \<Longrightarrow> vverdicts vs = fst (usteps tps ust) \<and>
        z' = (snd (usteps tps ust), last (0 # map snd tps))"
        using vitems_ok[OF \<open>oks ?xs = Some es\<close> vs] tps by auto
      have E: "(\<not> has_verror V \<longleftrightarrow> sorted (map snd ?tps)) \<and>
        (\<not> has_verror V \<longrightarrow> vverdicts V = fst (usteps ?tps ust))"
      proof (cases fin)
        case None
        then show ?thesis
          using V vs A B by (auto simp: fin_tps_def)
      next
        case (Some t)
        note fin = this
        obtain vs1 ust1 where u: "emstep (build_db [], t) (snd (usteps tps ust)) = (vs1, ust1)"
          by (metis prod.exhaust)
        have S1: "sorted (0 # map snd tps) \<Longrightarrow> sorted (map snd ?tps) \<longleftrightarrow> \<not> t < last (0 # map snd tps)"
          using sorted_snoc_last[of 0 "map snd tps" t] by (auto simp: fin fin_tps_def not_less)
        have S2: "\<not> sorted (0 # map snd tps) \<Longrightarrow> \<not> sorted (map snd ?tps)"
          by (auto simp: sorted_append)
        show ?thesis
          using V vs fin A B u S1 S2 by (auto simp: vtp_def usteps_append fin_tps_def split: prod.splits)
      qed
      show thesis
      proof (cases "sorted (map snd ?tps)")
        case True
        then have "vverdicts V = emonitor (ust) (prefix_of_list (map (apfst set) ?tps))"
          using E by (simp add: usteps_dmsteps0 emonitor_def emsteps_stateless.rep_eq Rep_prefix_of_list comp_def)
        with True E L' show thesis
          by (intro ok) auto
      next
        case False
        with E L' show thesis
          by (intro err) auto
      qed
    qed
  qed
qed

lemma vrun_cases:
  fixes cf fin ust ss
  assumes lk: "vc_lookup cf = lsig_lookup (vc_lsig cf)"
  defines "L \<equiv> log_prefix (sk (vkeep cf)) (sf (vc_pf cf)) (vc_lsig cf) fin (concat (map Rep_bytes ss))"
    and "V \<equiv> vrun cf fin (einit, (ust, 0)) ss"
  obtains (err) "has_verror V" "L = None"
  | (ok) \<pi> where "\<not> has_verror V" "L = Some \<pi>" "vverdicts V = emonitor (ust) \<pi>"
proof -
  let ?k = "vkeep cf"
  let ?xs = "eparse ?k ss"
  obtain pos where V: "V = (case vitems cf ?xs (ust, 0) of
    (vs, z') \<Rightarrow> vs @ (case fin of None \<Rightarrow> [] | Some t \<Rightarrow> [fst (vtp pos [] t z')]))"
    using vrun_eparse unfolding V_def by blast
  have L: "L = Option.bind (oks ?xs) (\<lambda>es. prefix_of_items (sf (vc_pf cf)) (vc_lsig cf) fin (abs_items es))"
    using eparse_filter[of ?k ss] unfolding L_def log_prefix_def
    by (cases "oks ?xs"; cases "parse_log (concat (map Rep_bytes ss))") auto
  show thesis
  proof (cases rule: vitems_cases[where cf=cf and xs="?xs" and ust=ust and fin=fin and pos=pos, OF lk, case_names err ok])
    case err
    then show thesis
      using that(1) V L by simp
  next
    case (ok \<pi>)
    then show thesis
      using that(2)[of \<pi>] V L by simp
  qed
qed

lemma vfeed_chunks_cases:
  fixes cf ust ss
  assumes lk: "vc_lookup cf = lsig_lookup (vc_lsig cf)"
  defines "V \<equiv> fst (vfeed_chunks cf ss (einit, (ust, 0)))"
    and "L \<equiv> Option.bind (fstream_run (sk (vkeep cf)) (concat (map Rep_bytes ss)) fstream_init)
      (\<lambda>(es, _). prefix_of_items (sf (vc_pf cf)) (vc_lsig cf) None es)"
  obtains (err) "has_verror V" "L = None"
  | (ok) \<pi> where "\<not> has_verror V" "L = Some \<pi>" "vverdicts V = emonitor (ust) \<pi>"
proof -
  let ?k = "vkeep cf"
  let ?xs = "fst (efeed_chunks ?k ss einit)"
  have V: "V = (case vitems cf ?xs (ust, 0) of
    (vs, z') \<Rightarrow> vs @ (case None of None \<Rightarrow> [] | Some t \<Rightarrow> [fst (vtp 0 [] t z')]))"
    by (simp add: V_def vfeed_chunks_efeed split: prod.splits)
  have L: "L = Option.bind (oks ?xs) (\<lambda>es. prefix_of_items (sf (vc_pf cf)) (vc_lsig cf) None (abs_items es))"
    using efeed_chunks_online[of ?k ss] unfolding L_def
    by (cases "oks ?xs"; cases "fstream_run (sk ?k) (concat (map Rep_bytes ss)) fstream_init") auto
  show thesis
  proof (cases rule: vitems_cases[where cf=cf and xs="?xs" and ust=ust and fin=None and pos=0, OF lk, case_names err ok])
    case err
    then show thesis
      using that(1) V L by simp
  next
    case (ok \<pi>)
    then show thesis
      using that(2)[of \<pi>] V L by simp
  qed
qed

subsection \<open>The verdicts depend only on the events of the predicates that occur freely\<close>

text \<open>An event that a formula matches is one of a predicate that occurs freely in it.\<close>

lemma matches_preds: "Safety.matches v \<phi> e \<Longrightarrow> (fst e, length (snd e)) \<in> Rewriting.preds \<phi>"
proof (induction \<phi> arbitrary: v e)
  case (LetPast p \<phi> \<psi>)
  from LetPast.prems have ne: "(fst e, length (snd e)) \<noteq> (p, Formula.nfv \<phi>)"
    by auto
  from LetPast.prems obtain e' where r: "(\<lambda>e' e. Safety.matches (snd e') \<phi> e \<and> fst e' = p \<and>
      length (snd e') = Formula.nfv \<phi>)\<^sup>*\<^sup>* e' e" and m: "Safety.matches v \<psi> e'"
    by auto
  from r show ?case
  proof (cases rule: rtranclp.cases)
    case rtrancl_refl
    with LetPast.IH(2)[OF m] ne show ?thesis
      by simp
  next
    case (rtrancl_into_rtrancl b)
    with LetPast.IH(1)[of "snd b" e] ne show ?thesis
      by simp
  qed
qed (fastforce simp: fv_regex_alt)+

lemma preds_map_formula[simp]: "Rewriting.preds (Formula.formula.map_formula f \<phi>) = Rewriting.preds \<phi>"
  by (induction \<phi>) (auto simp: fv_regex_alt regex.set_map)

lemma pmap_\<Gamma>_pmap_\<Gamma>: "pmap_\<Gamma> f (pmap_\<Gamma> g \<pi>) = pmap_\<Gamma> (f \<circ> g) \<pi>"
  by transfer (auto split: prod.splits)

lemma wty_prefix_pmap_\<Gamma>_Int: "wty_prefix S \<pi> \<Longrightarrow> wty_prefix S (pmap_\<Gamma> (\<lambda>D. D \<inter> E) \<pi>)"
  by (fastforce simp: wty_prefix.rep_eq pmap_\<Gamma>.rep_eq wty_db_def)

text \<open>Restricting a well-typed prefix to a superset of the relevant events does not change the
  verdicts.\<close>

lemma (in future_bounded_mfodl) Mt_restrict:
  assumes wty: "wty_prefix SIG \<pi>" and E: "\<And>v e. Safety.matches v \<phi> e \<Longrightarrow> e \<in> E"
  shows "Mt (pmap_\<Gamma> (\<lambda>D. D \<inter> E) \<pi>) = Mt \<pi>"
proof -
  let ?\<pi>E = "pmap_\<Gamma> (\<lambda>D. D \<inter> E) \<pi>"
  have p: "\<pi> \<in> formula_slicer.prefixes" and pE: "?\<pi>E \<in> formula_slicer.prefixes"
    using wty wty_prefix_pmap_\<Gamma>_Int[OF wty] by (auto simp: prefixes_alt)
  have "(\<lambda>D. D \<inter> E \<inter> relevant_events \<phi> UNIV) = (\<lambda>D. D \<inter> relevant_events \<phi> UNIV)"
    using E by auto
  then have eq: "pmap_\<Gamma> (\<lambda>D. D \<inter> relevant_events \<phi> UNIV) ?\<pi>E =
    pmap_\<Gamma> (\<lambda>D. D \<inter> relevant_events \<phi> UNIV) \<pi>"
    by (simp only: pmap_\<Gamma>_pmap_\<Gamma> comp_def)
  have "(i, v) \<in> M ?\<pi>E \<longleftrightarrow> (i, v) \<in> M \<pi>" for i v
  proof (cases "wf_tuple (Formula.fv_list \<phi>) v")
    case True
    let ?y = "map (tup_get (Formula.fv_list \<phi>) v) [0..<Suc (Max (Set.insert 0 (Formula.fv \<phi>)))]"
    have "mem_restr UNIV (Formula.fv_list \<phi>) v"
      by (rule mem_restrI[where y = ?y]) (auto simp: True less_Suc_eq_le simp del: upt_Suc intro: Max_ge)
    then show ?thesis
      using sliceable_M[OF p, of UNIV v i] sliceable_M[OF pE, of UNIV v i] eq by simp
  qed (simp add: M_def)
  then have "M ?\<pi>E = M \<pi>"
    by auto
  then show ?thesis
    by (simp add: Mt_def)
qed

subsection \<open>From the log to the verdicts\<close>

text \<open>The predicates whose events the parser keeps, as the specification states it, and the
  verdicts as the specification states them: tuples over the formula's free variables in the
  order in which @{const Formula.fv_list} lists them.  The executable monitor's tuples are over the
  same variables in ascending order.\<close>

definition keep_spec :: "bool \<Rightarrow> 't Formula.formula \<Rightarrow> lsig \<Rightarrow> string \<Rightarrow> bool" where
  "keep_spec filt \<phi> S p \<longleftrightarrow> \<not> filt \<or> Abs_string8 p \<in> fst ` Rewriting.preds \<phi> \<or> Abs_string8 p \<notin> fst ` set S"

definition vwiden :: "'t Formula.formula \<Rightarrow> (nat \<times> ts \<times> utable) list \<Rightarrow> (nat \<times> ts \<times> event_data table) list" where
  "vwiden \<phi> = map (\<lambda>(i, t, X). (i, t, etabw (Formula.fv_list \<phi>) (ecols (Formula.fv_list \<phi>)) X))"

lemma vinit_Inr:
  assumes "vinit mw rw filt S pf \<phi> = Inr (cf, z)"
  obtains ust where "cf = VConf (vskip_fun (vskip filt \<phi> S)) S (lsig_lookup_fun S) pf" "z = (einit, ust, 0)"
    "wf_formula \<phi>" "eminit_verimon mw rw (lsig_tsig S) \<phi> = Inr ust" "efail_nodes (emstate_m ust) = 0"
  using assms by (auto simp: vinit_def Let_def split: if_splits sum.splits)

lemma sk_vkeep: "sk (vkeep (VConf (vskip_fun (vskip filt \<phi> S)) S' L pf)) = keep_spec filt \<phi> S"
  by (auto simp: fun_eq_iff sk_def vkeep_def vskip_fun vskip_def Let_def keep_spec_def string8_of_bytes_def
      Abs_bytes_inverse)
text \<open>Filtering the items restricts the prefix they denote to the events kept.\<close>

lemma those_map_cong: "those (map f xs) = Some ys \<Longrightarrow> (\<And>x y. f x = Some y \<Longrightarrow> g x = Some (h y)) \<Longrightarrow>
  those (map g xs) = Some (map h ys)"
  by (induction xs arbitrary: ys) (auto split: option.splits)

lemma those_filter: "those (map f xs) = Some ys \<Longrightarrow> (\<And>x y. f x = Some y \<Longrightarrow> P x \<longleftrightarrow> Q y) \<Longrightarrow>
  those (map f (filter P xs)) = Some (filter Q ys)"
  by (induction xs arbitrary: ys) (auto split: option.splits)

lemma event_of_string_fst: "event_of_string pf S e = Some x \<Longrightarrow> fst x = Abs_string8 (fst e)"
  by (auto simp: event_of_string_def split: option.splits prod.splits)

lemma tp_of_item_filter:
  assumes "tp_of_item pf S it = Some tp"
  shows "tp_of_item pf S (filter_item K it) = Some (apfst (\<lambda>D. D \<inter> {e. K (Rep_string8 (fst e))}) tp)"
proof (cases it)
  case (Entry ts evs)
  with assms obtain t xs where t: "nat_of_string ts = Some t" and xs: "those (map (event_of_string pf S) evs) = Some xs"
    and tp: "tp = (set xs, t)"
    by (auto simp: tp_of_item_def split: option.splits)
  have "those (map (event_of_string pf S) (filter (K \<circ> fst) evs)) = Some (filter (\<lambda>e. K (Rep_string8 (fst e))) xs)"
    by (rule those_filter[OF xs]) (auto dest: event_of_string_fst simp: Abs_string8_inverse)
  then show ?thesis
    by (auto simp: Entry tp_of_item_def t tp)
qed (use assms in \<open>simp add: tp_of_item_def\<close>)

lemma prefix_of_list_map: "sorted (map snd xs) \<Longrightarrow> prefix_of_list (map (apfst f) xs) = pmap_\<Gamma> f (prefix_of_list xs)"
  by transfer (auto simp: comp_def apfst_def map_prod_def split_beta)

lemma prefix_of_items_filter:
  assumes "prefix_of_items pf S fin items = Some \<pi>"
  shows "prefix_of_items pf S fin (map (filter_item K) items) = Some (pmap_\<Gamma> (\<lambda>D. D \<inter> {e. K (Rep_string8 (fst e))}) \<pi>)"
proof -
  let ?g = "\<lambda>D. D \<inter> {e. K (Rep_string8 (fst e))}"
  let ?fin = "case fin of None \<Rightarrow> [] | Some t \<Rightarrow> [({}, t)]"
  obtain tps where tps: "those (map (tp_of_item pf S) items) = Some tps"
    and srt: "sorted (map snd (tps @ ?fin))" and \<pi>: "\<pi> = prefix_of_list (tps @ ?fin)"
    using assms by (auto simp: prefix_of_items_def Let_def split: option.splits if_splits)
  have "those (map (tp_of_item pf S) (map (filter_item K) items)) = Some (map (apfst ?g) tps)"
    using those_map_cong[OF tps, of "tp_of_item pf S \<circ> filter_item K" "apfst ?g"] tp_of_item_filter
    by (simp add: comp_def)
  moreover have "map (apfst ?g) tps @ ?fin = map (apfst ?g) (tps @ ?fin)"
    by (simp split: option.splits)
  ultimately show ?thesis
    using srt prefix_of_list_map[OF srt, of ?g]
    by (simp add: prefix_of_items_def \<pi> comp_def del: map_append split: option.splits)
qed

text \<open>The signature, as the specification of the prepared formula uses it.\<close>

locale verimon_log = verimon_prepare rw "lsig_tsig S" \<phi>
  for rw :: bool and S :: lsig and \<phi> :: "tysym Formula.formula"
begin

lemma map_sig_lsig: "map_sig (convert_tysym o check_subst) (lsig_tsig S) = lsig_lookup S"
proof -
  have "convert_tysym (check_subst (TCst x)) = x" for x
    using wf_f_check_subst unfolding wf_f_def by (metis comp_apply tysym.inject(3))
  then show ?thesis
    by (auto simp: fun_eq_iff map_sig_def lsig_tsig_def option.map_comp comp_def option.map_ident)
qed

context
  fixes mw :: bool
begin

interpretation monitor_\<phi>: future_bounded_mfodl "Formula.formula.map_formula (convert_tysym \<circ> check_subst) \<phi>"
  "map_sig (convert_tysym o check_subst) (lsig_tsig S)" "convert_tysym o check_subst o TAny"
  using future_bounded_\<phi> by (auto simp: future_bounded_mfodl_def future_bounded_mfodl_axioms_def wty_mfodl_def)

text \<open>The verdicts depend only on the events of the predicates that occur freely in the
  formula.\<close>

theorem Mt_preds:
  assumes "wty_prefix (lsig_lookup S) \<pi>" "wty_prefix (lsig_lookup S) \<pi>'"
    and "pmap_\<Gamma> (\<lambda>D. D \<inter> {e. (fst e, length (snd e)) \<in> Rewriting.preds \<phi>}) \<pi> =
      pmap_\<Gamma> (\<lambda>D. D \<inter> {e. (fst e, length (snd e)) \<in> Rewriting.preds \<phi>}) \<pi>'"
  shows "monitor_\<phi>.Mt \<pi> = monitor_\<phi>.Mt \<pi>'"
proof -
  have E: "Safety.matches v (Formula.formula.map_formula (convert_tysym \<circ> check_subst) \<phi>) e \<Longrightarrow>
    e \<in> {e. (fst e, length (snd e)) \<in> Rewriting.preds \<phi>}" for v e
    using matches_preds[of v "Formula.formula.map_formula (convert_tysym \<circ> check_subst) \<phi>" e] by simp
  from assms show ?thesis
    using monitor_\<phi>.Mt_restrict[OF _ E, of \<pi>] monitor_\<phi>.Mt_restrict[OF _ E, of \<pi>']
    by (simp add: map_sig_lsig)
qed

text \<open>The monitor on a log whose events of the predicates whose names occur freely in the
  formula, and of those the signature does not declare, denote a prefix (all events, unless
  @{text filt}): it reports no error, and its verdicts are those the specification prescribes
  for this prefix, and thus for every well-typed prefix with the same events of the predicates
  that occur freely in the formula (@{thm [source] Mt_preds}); otherwise, it reports an
  error.\<close>

theorem vrun_filtered:
  fixes fin ss
  assumes init: "vinit mw rw filt S pf \<phi> = Inr (cf, z)"
  defines "L \<equiv> log_prefix (keep_spec filt \<phi> S) (sf pf) S fin (concat (map Rep_bytes ss))"
  shows "\<not> has_verror (vrun cf fin z ss) \<longleftrightarrow> L \<noteq> None"
    and "L = Some \<pi> \<Longrightarrow> flatten_verdicts (vwiden \<phi> (vverdicts (vrun cf fin z ss))) = monitor_\<phi>.Mt \<pi>"
proof -
  obtain ust where cf: "cf = VConf (vskip_fun (vskip filt \<phi> S)) S (lsig_lookup_fun S) pf" and z: "z = (einit, ust, 0)"
    and u: "eminit_verimon mw rw (lsig_tsig S) \<phi> = Inr ust" and zf: "efail_nodes (emstate_m ust) = 0"
    using vinit_Inr[OF init] by blast
  have lk: "vc_lookup cf = lsig_lookup (vc_lsig cf)"
    by (simp add: cf)
  have L: "L = log_prefix (sk (vkeep cf)) (sf (vc_pf cf)) (vc_lsig cf) fin (concat (map Rep_bytes ss))"
    by (simp add: L_def cf sk_vkeep)
  show "\<not> has_verror (vrun cf fin z ss) \<longleftrightarrow> L \<noteq> None"
    by (cases rule: vrun_cases[where cf=cf and fin=fin and ust=ust and ss=ss, OF lk, case_names err ok]) (auto simp: L z)
  assume "L = Some \<pi>"
  then obtain items where "prefix_of_items (sf pf) S fin (map (filter_item (keep_spec filt \<phi> S)) items) = Some \<pi>"
    by (cases "parse_log (concat (map Rep_bytes ss))") (auto simp: L_def log_prefix_def)
  note w = prefix_of_items_wty[OF this]
  show "flatten_verdicts (vwiden \<phi> (vverdicts (vrun cf fin z ss))) = monitor_\<phi>.Mt \<pi>"
  proof (cases rule: vrun_cases[where cf=cf and fin=fin and ust=ust and ss=ss, OF lk, case_names err ok])
    case err
    with \<open>L = Some \<pi>\<close> show ?thesis
      by (simp add: L)
  next
    case (ok \<pi>')
    with \<open>L = Some \<pi>\<close> have R: "vverdicts (vrun cf fin z ss) = emonitor (ust) \<pi>"
      by (simp add: L z)
    have "wty_prefix (map_sig (convert_tysym o check_subst) (lsig_tsig S)) \<pi>"
      using w(1) by (simp add: map_sig_lsig)
    then show ?thesis
      using eminit_verimon_mverdicts[OF u zf w(2)] by (simp add: vwiden_def R)  qed
qed

text \<open>The monitor on a log that denotes a prefix: it reports no error, and its verdicts are those
  the specification prescribes for the prefix, although, if @{text filt}, it does not convert
  the events of the other predicates.\<close>

theorem vrun_log:
  assumes init: "vinit mw rw filt S pf \<phi> = Inr (cf, z)"
    and log: "log_prefix (\<lambda>_. True) (sf pf) S fin (concat (map Rep_bytes ss)) = Some \<pi>"
  shows "\<not> has_verror (vrun cf fin z ss)"
    and "flatten_verdicts (vwiden \<phi> (vverdicts (vrun cf fin z ss))) = monitor_\<phi>.Mt \<pi>"
proof -
  let ?E = "{e. keep_spec filt \<phi> S (Rep_string8 (fst e))}"
  from log obtain items where items: "parse_log (concat (map Rep_bytes ss)) = Some items"
    and p: "prefix_of_items (sf pf) S fin items = Some \<pi>"
    by (cases "parse_log (concat (map Rep_bytes ss))") (auto simp: log_prefix_def)
  have L: "log_prefix (keep_spec filt \<phi> S) (sf pf) S fin (concat (map Rep_bytes ss)) =
    Some (pmap_\<Gamma> (\<lambda>D. D \<inter> ?E) \<pi>)"
    by (simp add: log_prefix_def items prefix_of_items_filter[OF p])
  then show "\<not> has_verror (vrun cf fin z ss)"
    using vrun_filtered(1)[OF init] by simp
  have E: "Safety.matches v (Formula.formula.map_formula (convert_tysym \<circ> check_subst) \<phi>) e \<Longrightarrow> e \<in> ?E" for v e
    using matches_preds[of v "Formula.formula.map_formula (convert_tysym \<circ> check_subst) \<phi>" e]
    by (force simp: keep_spec_def Rep_string8_inverse)
  have "monitor_\<phi>.Mt (pmap_\<Gamma> (\<lambda>D. D \<inter> ?E) \<pi>) = monitor_\<phi>.Mt \<pi>"
    using monitor_\<phi>.Mt_restrict[OF _ E] prefix_of_items_wty(1)[OF p] by (simp add: map_sig_lsig)
  with vrun_filtered(2)[OF init L] show "flatten_verdicts (vwiden \<phi> (vverdicts (vrun cf fin z ss))) = monitor_\<phi>.Mt \<pi>"
    by simp
qed

text \<open>For an input that is still being read: the verdicts output so far are those of the entries
  the streaming parser has output (@{thm [source] Log_Exec.efeed_chunks_online}).\<close>

theorem vfeed_chunks_online:
  fixes ss
  assumes init: "vinit mw rw filt S pf \<phi> = Inr (cf, z)"
  defines "L \<equiv> Option.bind (fstream_run (keep_spec filt \<phi> S) (concat (map Rep_bytes ss)) fstream_init)
      (\<lambda>(es, _). prefix_of_items (sf pf) S None es)"
  shows "\<not> has_verror (fst (vfeed_chunks cf ss z)) \<longleftrightarrow> L \<noteq> None"
    and "L = Some \<pi> \<Longrightarrow> flatten_verdicts (vwiden \<phi> (vverdicts (fst (vfeed_chunks cf ss z)))) = monitor_\<phi>.Mt \<pi>"
proof -
  obtain ust where cf: "cf = VConf (vskip_fun (vskip filt \<phi> S)) S (lsig_lookup_fun S) pf" and z: "z = (einit, ust, 0)"
    and u: "eminit_verimon mw rw (lsig_tsig S) \<phi> = Inr ust" and zf: "efail_nodes (emstate_m ust) = 0"
    using vinit_Inr[OF init] by blast
  have lk: "vc_lookup cf = lsig_lookup (vc_lsig cf)"
    by (simp add: cf)
  have L: "L = Option.bind (fstream_run (sk (vkeep cf)) (concat (map Rep_bytes ss)) fstream_init)
      (\<lambda>(es, _). prefix_of_items (sf (vc_pf cf)) (vc_lsig cf) None es)"
    by (simp add: L_def cf sk_vkeep)
  show "\<not> has_verror (fst (vfeed_chunks cf ss z)) \<longleftrightarrow> L \<noteq> None"
    by (cases rule: vfeed_chunks_cases[where cf=cf and ust=ust and ss=ss, OF lk, case_names err ok]) (auto simp: L z)
  assume "L = Some \<pi>"
  then obtain es where "prefix_of_items (sf pf) S None es = Some \<pi>"
    by (cases "fstream_run (keep_spec filt \<phi> S) (concat (map Rep_bytes ss)) fstream_init")
      (auto simp: L_def)
  note w = prefix_of_items_wty[OF this]
  show "flatten_verdicts (vwiden \<phi> (vverdicts (fst (vfeed_chunks cf ss z)))) = monitor_\<phi>.Mt \<pi>"
  proof (cases rule: vfeed_chunks_cases[where cf=cf and ust=ust and ss=ss, OF lk, case_names err ok])
    case err
    with \<open>L = Some \<pi>\<close> show ?thesis
      by (simp add: L)
  next
    case (ok \<pi>')
    with \<open>L = Some \<pi>\<close> have R: "vverdicts (fst (vfeed_chunks cf ss z)) = emonitor (ust) \<pi>"
      by (simp add: L z)
    have "wty_prefix (map_sig (convert_tysym o check_subst) (lsig_tsig S)) \<pi>"
      using w(1) by (simp add: map_sig_lsig)
    then show ?thesis
      using eminit_verimon_mverdicts[OF u zf w(2)] by (simp add: vwiden_def R)  qed
qed

text \<open>At the level of the grammar: if the input read so far extends to a log, the verdicts output
  so far are those of a prefix of the log's entries, if there was no error.\<close>

corollary vfeed_chunks_log:
  assumes init: "vinit mw rw filt S pf \<phi> = Inr (cf, z)"
    and log: "log_lang (concat (map Rep_bytes ss) @ s') es'"
    and ok: "\<not> has_verror (fst (vfeed_chunks cf ss z))"
  obtains es es'' \<pi> where "es' = es @ es''"
    and "prefix_of_items (sf pf) S None (map (filter_item (keep_spec filt \<phi> S)) es) = Some \<pi>"
    and "flatten_verdicts (vwiden \<phi> (vverdicts (fst (vfeed_chunks cf ss z)))) = monitor_\<phi>.Mt \<pi>"
proof -
  let ?s = "concat (map Rep_bytes ss)" and ?K = "keep_spec filt \<phi> S"
  have "Option.bind (fstream_run ?K ?s fstream_init) (\<lambda>(es, _). prefix_of_items (sf pf) S None es) \<noteq> None"
    using vfeed_chunks_online(1)[OF init, of ss] ok by simp
  then obtain es1 l1 p1 \<pi> where f: "fstream_run ?K ?s fstream_init = Some (es1, l1, p1)"
    and p: "prefix_of_items (sf pf) S None es1 = Some \<pi>"
    by (cases "fstream_run ?K ?s fstream_init") auto
  from f obtain es st where r: "stream_run ?s stream_init = Some (es, st)"
    and es1: "es1 = map (filter_item ?K) es"
    unfolding fstream_run_init by (cases "stream_run ?s stream_init") (auto split: prod.splits)
  obtain es'' where "es' = es @ es''"
    using stream_run_prefix[OF r log] .
  moreover have "flatten_verdicts (vwiden \<phi> (vverdicts (fst (vfeed_chunks cf ss z)))) = monitor_\<phi>.Mt \<pi>"
    using vfeed_chunks_online(2)[OF init, of ss \<pi>] f p by simp
  ultimately show ?thesis
    using that p es1 by blast
qed

text \<open>In particular, the verdicts of the entries of a log are output as soon as the next item
  begins, if they denote a prefix.\<close>

corollary vfeed_chunks_prompt:
  assumes init: "vinit mw rw filt S pf \<phi> = Inr (cf, z)"
    and "Glex s ts" "G_parser ts es" "c = CHR ''@'' \<or> c = CHR ''>''"
    and "concat (map Rep_bytes ss) = s @ [c]"
    and p: "prefix_of_items (sf pf) S None es = Some \<pi>"
  shows "\<not> has_verror (fst (vfeed_chunks cf ss z))"
    and "flatten_verdicts (vwiden \<phi> (vverdicts (fst (vfeed_chunks cf ss z)))) = monitor_\<phi>.Mt \<pi>"
proof -
  let ?E = "{e. keep_spec filt \<phi> S (Rep_string8 (fst e))}"
  obtain P where "fstream_run (keep_spec filt \<phi> S) (s @ [c]) fstream_init =
    Some (map (filter_item (keep_spec filt \<phi> S)) es, L_INIT, P)"
    using fstream_run_prompt[OF assms(2-4)] .
  then have L: "Option.bind (fstream_run (keep_spec filt \<phi> S) (concat (map Rep_bytes ss)) fstream_init)
      (\<lambda>(es, _). prefix_of_items (sf pf) S None es) = Some (pmap_\<Gamma> (\<lambda>D. D \<inter> ?E) \<pi>)"
    by (simp add: assms(5) prefix_of_items_filter[OF p])
  then show "\<not> has_verror (fst (vfeed_chunks cf ss z))"
    using vfeed_chunks_online(1)[OF init] by simp
  have E: "Safety.matches v (Formula.formula.map_formula (convert_tysym \<circ> check_subst) \<phi>) e \<Longrightarrow> e \<in> ?E" for v e
    using matches_preds[of v "Formula.formula.map_formula (convert_tysym \<circ> check_subst) \<phi>" e]
    by (force simp: keep_spec_def Rep_string8_inverse)
  have "monitor_\<phi>.Mt (pmap_\<Gamma> (\<lambda>D. D \<inter> ?E) \<pi>) = monitor_\<phi>.Mt \<pi>"
    using monitor_\<phi>.Mt_restrict[OF _ E] prefix_of_items_wty(1)[OF p] by (simp add: map_sig_lsig)
  with vfeed_chunks_online(2)[OF init L] show "flatten_verdicts (vwiden \<phi> (vverdicts (fst (vfeed_chunks cf ss z)))) = monitor_\<phi>.Mt \<pi>"
    by simp
qed

end

end

text \<open>The monitor starts only if the assumptions of the locale hold.\<close>

lemma vinit_verimon_log:
  assumes "vinit mw rw filt S pf \<phi> = Inr (cf, z)"
  shows "verimon_log rw S \<phi>"
proof -
  obtain ust where "wf_formula \<phi>" "eminit_verimon mw rw (lsig_tsig S) \<phi> = Inr ust"
    using vinit_Inr[OF assms] by metis
  then show ?thesis
    by (cases "prepare_verimon rw (lsig_tsig S) \<phi>")
      (auto simp: verimon_log_def verimon_prepare_def eminit_verimon_def)
qed

(*<*)
end
(*>*)
