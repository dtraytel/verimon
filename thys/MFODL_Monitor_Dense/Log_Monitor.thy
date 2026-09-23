(*<*)
theory Log_Monitor
  imports Dense_VeriMon Dense_Code_Opt "Log_Parser.Log_Values"
begin
(*>*)

section \<open>From the log to the verdicts\<close>

text \<open>
  This theory composes the verified log parser of session Log_Parser with the verified dense
  monitor: the time points the parser outputs are converted into the monitor's databases, by
  the signature, and fed to @{const udmstep}. The parser drops the events of the predicates the
  formula does not mention (@{theory Log_Parser.Log_Filter}). The final theorem states that the
  verdicts output for a log are those that the specification of the formula prescribes for the
  trace the log denotes.
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

subsection \<open>Signatures\<close>

text \<open>The signature as the front end reads it: the predicates with their argument types.\<close>

type_synonym lsig = "(string8 \<times> ty list) list"

definition lsig_lookup :: "lsig \<Rightarrow> string8 \<times> nat \<Rightarrow> ty list option" where
  "lsig_lookup S pn = map_option snd (find (\<lambda>(p, tys). (p, length tys) = pn) S)"

definition lsig_tsig :: "lsig \<Rightarrow> tyssig" where
  "lsig_tsig S = map_sig TCst (lsig_lookup S)"

lemma lsig_lookup_length: "lsig_lookup S (p, n) = Some tys \<Longrightarrow> length tys = n"
  by (induction S) (auto simp: lsig_lookup_def split: if_splits)

subsection \<open>Converting events\<close>

text \<open>A field of a given type. Integers are read as in @{theory Log_Parser.Log_Values}; floats
  by a parameter @{text pf}, the platform's reader, about which nothing is assumed.\<close>

definition conv_field :: "(bytes \<Rightarrow> double option) \<Rightarrow> ty \<Rightarrow> bytes \<Rightarrow> event_data option" where
  "conv_field pf t f = (case t of
     TInt \<Rightarrow> map_option (EInt \<circ> integer_of_int) (bint_of f)
   | TFloat \<Rightarrow> map_option EFloat (pf f)
   | TString \<Rightarrow> Some (EString (string8_of_bytes f)))"

lemma conv_field_ty: "conv_field pf t f = Some x \<Longrightarrow> ty_of x = t"
  by (cases t) (auto simp: conv_field_def)

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

definition conv_event :: "(bytes \<Rightarrow> double option) \<Rightarrow> lsig \<Rightarrow> bytes \<times> bytes list \<Rightarrow> verror + Formula.event" where
  "conv_event pf S e = (case e of (p, fs) \<Rightarrow> let q = string8_of_bytes p in
     (case lsig_lookup S (q, length fs) of
       None \<Rightarrow> Inl (VE_PREDICATE p (length fs))
     | Some tys \<Rightarrow> map_sum (\<lambda>(i, t). VE_FIELD p i t) (Pair q) (conv_fields pf tys fs 0)))"

fun conv_events :: "(bytes \<Rightarrow> double option) \<Rightarrow> lsig \<Rightarrow> (bytes \<times> bytes list) list \<Rightarrow> verror + Formula.event list" where
  "conv_events pf S [] = Inr []"
| "conv_events pf S (e # es) = (case conv_event pf S e of
     Inl err \<Rightarrow> Inl err
   | Inr x \<Rightarrow> map_sum id (Cons x) (conv_events pf S es))"

text \<open>Converted events are well typed.\<close>

lemma conv_fields_ty:
  "conv_fields pf ts fs i = Inr xs \<Longrightarrow> length ts = length fs \<Longrightarrow> list_all2 (\<lambda>t x. ty_of x = t) ts xs"
proof (induction pf ts fs i arbitrary: xs rule: conv_fields.induct)
  case (1 pf t ts f fs i)
  then show ?case
    by (auto simp: map_sum_def conv_field_ty split: option.splits sum.splits)
qed auto

lemma conv_event_wty:
  assumes "conv_event pf S e = Inr x"
  shows "wty_event (lsig_lookup S) (fst x) (snd x)"
proof -
  obtain p fs where e: "e = (p, fs)"
    by (cases e)
  with assms obtain tys xs where tys: "lsig_lookup S (string8_of_bytes p, length fs) = Some tys"
    and xs: "conv_fields pf tys fs 0 = Inr xs" and x: "x = (string8_of_bytes p, xs)"
    by (auto simp: conv_event_def map_sum_def Let_def split: option.splits sum.splits)
  from xs lsig_lookup_length[OF tys] have "list_all2 (\<lambda>t x. ty_of x = t) tys xs"
    by (rule conv_fields_ty)
  moreover from this lsig_lookup_length[OF tys] have "length xs = length fs"
    by (simp add: list_all2_lengthD)
  ultimately show ?thesis
    using tys x by (simp add: wty_event_def wty_tuple_def)
qed

lemma conv_events_Inr:
  "conv_events pf S es = Inr xs \<Longrightarrow> list_all2 (\<lambda>e x. conv_event pf S e = Inr x) es xs"
proof (induction es arbitrary: xs)
  case (Cons e es)
  then show ?case
    by (auto simp: map_sum_def split: sum.splits)
qed auto

subsection \<open>Databases\<close>

text \<open>The events of a time point, grouped by predicate and arity.\<close>

fun add_ev :: "Formula.event \<Rightarrow> ((Formula.name \<times> nat) \<times> event_data list list) list \<Rightarrow>
    ((Formula.name \<times> nat) \<times> event_data list list) list" where
  "add_ev (p, vs) [] = [((p, length vs), [vs])]"
| "add_ev (p, vs) ((k, xs) # g) = (if k = (p, length vs) then (k, vs # xs) # g else (k, xs) # add_ev (p, vs) g)"

definition group_evs :: "Formula.event list \<Rightarrow> ((Formula.name \<times> nat) \<times> event_data list list) list" where
  "group_evs evs = fold add_ev evs []"

definition build_db :: "Formula.event list \<Rightarrow> udatabase" where
  "build_db evs = fold (\<lambda>(k, xs) db. uinsert_table_into_db k (utable_of_list (sort_c xs)) db) (group_evs evs) uempty_db"

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

theorem rdb_build_db: "rdb (build_db evs) = mk_db (set evs)"
proof (rule mapping_eqI)
  fix k :: "Formula.name \<times> nat"
  obtain p n where k: "k = (p, n)"
    by (cases k)
  have lk: "Mapping.lookup (build_db evs) k = map_option (\<lambda>xs. [set xs]) (map_of (group_evs evs) k)"
    using lookup_fold_uinsert[of "group_evs evs" "\<lambda>xs. utable_of_list (sort_c xs)" uempty_db k] distinct_group_evs
    by (auto simp: build_db_def uempty_db_def utable_of_list_def set_sort_c ID_ccompare_ed
      split: option.splits)
  have mk: "Mapping.lookup (mk_db (set evs)) (p, n) = (if \<exists>ts. (p, ts) \<in> set evs \<and> n = length ts
    then Some [map Some ` {ts. (p, ts) \<in> set evs \<and> n = length ts}] else None)"
    by (simp add: Mapping.lookup.rep_eq mk_db.rep_eq)
  have f: "set (map snd (filter (\<lambda>e. (fst e, length (snd e)) = k) evs)) = {ts. (p, ts) \<in> set evs \<and> n = length ts}"
    by (force simp: k)
  have e: "filter (\<lambda>e. (fst e, length (snd e)) = k) evs = [] \<longleftrightarrow> \<not> (\<exists>ts. (p, ts) \<in> set evs \<and> n = length ts)"
    by (force simp: k filter_empty_conv)
  show "Mapping.lookup (rdb (build_db evs)) k = Mapping.lookup (mk_db (set evs)) k"
  proof (cases "filter (\<lambda>e. (fst e, length (snd e)) = k) evs = []")
    case True
    then show ?thesis
      using lk mk e by (simp add: map_of_group_evs k)
  next
    case False
    then have "map_of (group_evs evs) k = Some (rev (map snd (filter (\<lambda>e. (fst e, length (snd e)) = k) evs)))"
      by (simp add: map_of_group_evs split: list.splits)
    then show ?thesis
      using lk mk e f False by (simp add: reopt_table_def reopt_def k)
  qed
qed

(*<*)
end
(*>*)
