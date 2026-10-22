(*<*)
theory Log_Monitor_Correctness
  imports "Monitor_Exec.Log_Monitor" Exec_Preparation_Correctness "Monitor_Impl_Proof.Monitor_Instance_Valid"
begin
(*>*)

section \<open>Correctness of the log monitor\<close>

text \<open>The reader of floats is a parameter about which nothing is assumed; the front end passes
  OCaml's @{text float_of_string_opt}.\<close>

subsection \<open>Lookup in the signature\<close>

lemma lsig_lookup_length: "lsig_lookup S (p, n) = Some tys \<Longrightarrow> length tys = n"
  by (induction S) (auto simp: lsig_lookup_def split: if_splits)

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

lemma lsig_lookup_fun[simp]: "lsig_lookup_fun S = lsig_lookup S"
  by (simp add: lsig_lookup_fun_def index_lookup_lsig_index)

subsection \<open>Prefix denoted by a log\<close>

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

lift_definition prefix_of_list :: "('a \<times> nat) list \<Rightarrow> 'a prefix" is
  "\<lambda>xs. if sorted (map snd xs) then xs else []"
  by auto

lemma Rep_prefix_of_list: "sorted (map snd xs) \<Longrightarrow> Rep_prefix (prefix_of_list xs) = xs"
  by (simp add: prefix_of_list.rep_eq)

definition prefix_of_items :: "(string \<Rightarrow> double option) \<Rightarrow> lsig \<Rightarrow> nat option \<Rightarrow> string item list \<Rightarrow>
    Formula.prefix option" where
  "prefix_of_items pf S fin items = (case those (map (tp_of_item pf S) items) of
     None \<Rightarrow> None
   | Some tps \<Rightarrow> (let tps' = tps @ (case fin of None \<Rightarrow> [] | Some t \<Rightarrow> [({}, t)]) in
       if sorted (map snd tps') then Some (prefix_of_list tps') else None))"

definition log_prefix :: "(string \<Rightarrow> bool) \<Rightarrow> (string \<Rightarrow> double option) \<Rightarrow> lsig \<Rightarrow> nat option \<Rightarrow> string \<Rightarrow>
    Formula.prefix option" where
  "log_prefix K pf S fin s = Option.bind (parse_log s) (\<lambda>items. prefix_of_items pf S fin (map (filter_item K) items))"

subsection \<open>Conversion of events\<close>

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

subsection \<open>Database of an entry\<close>

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

lemma vskip_fun: "vskip_fun xs q \<longleftrightarrow> q \<in> set xs"
  by (auto simp: vskip_fun_def str8_eq_def list_ex_iff)

subsection \<open>Entries, runs and outputs\<close>

definition conv_entry :: "vconf \<Rightarrow> bytes \<Rightarrow> (bytes \<times> bytes list) list \<Rightarrow> verror + Formula.event list \<times> nat" where
  "conv_entry cf ts evs = (case bnat_of ts of
     None \<Rightarrow> Inl (VE_TIMESTAMP ts)
   | Some t \<Rightarrow> map_sum id (\<lambda>xs. (xs, t)) (conv_events (vc_pf cf) (vc_lookup cf) evs))"

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

lemma has_verror_simps[simp]:
  "\<not> has_verror []"
  "has_verror (x # xs) \<longleftrightarrow> (case x of VO_VERDICTS _ \<Rightarrow> has_verror xs | VO_ERROR _ _ \<Rightarrow> True)"
  "has_verror (xs @ ys) \<longleftrightarrow> has_verror xs \<or> has_verror ys"
  by (auto simp: has_verror_def split: vout.splits)

subsection \<open>Monitor on a list of time points\<close>

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

subsection \<open>Conversion of items\<close>

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

subsection \<open>Well-typed finite prefix of a log\<close>

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

subsection \<open>Independence of irrelevant events\<close>

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

lemma pmap_\<Gamma>_pmap_\<Gamma>: "pmap_\<Gamma> f (pmap_\<Gamma> g \<pi>) = pmap_\<Gamma> (f \<circ> g) \<pi>"
  by transfer (auto split: prod.splits)

lemma wty_prefix_pmap_\<Gamma>_Int: "wty_prefix S \<pi> \<Longrightarrow> wty_prefix S (pmap_\<Gamma> (\<lambda>D. D \<inter> E) \<pi>)"
  by (fastforce simp: wty_prefix.rep_eq pmap_\<Gamma>.rep_eq wty_db_def)

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

subsection \<open>Kept events and widened verdicts\<close>

text \<open>The specification's tuples list the free variables in the order of @{const Formula.fv_list};
  the executable monitor's list them in ascending order.\<close>

definition keep_spec :: "bool \<Rightarrow> 't Formula.formula \<Rightarrow> lsig \<Rightarrow> string \<Rightarrow> bool" where
  "keep_spec filt \<phi> S p \<longleftrightarrow> \<not> filt \<or> Abs_string8 p \<in> fst ` Rewriting.preds \<phi> \<or> Abs_string8 p \<notin> fst ` set S"

definition vwiden :: "'t Formula.formula \<Rightarrow> (nat \<times> ts \<times> utable) list \<Rightarrow> (nat \<times> ts \<times> event_data table) list" where
  "vwiden \<phi> = map (\<lambda>(i, t, X). (i, t, etabw (Formula.fv_list \<phi>) (ecols (Formula.fv_list \<phi>)) X))"

lemma vinit_Inr:
  assumes "vinit ix mw rw filt S pf \<phi> = Inr (cf, z)"
  obtains ust where "cf = VConf (vskip_fun (vskip filt \<phi> S)) S (lsig_lookup_fun S) pf" "z = (einit, ust, 0)"
    "wf_formula \<phi>" "eminit_verimon ix mw rw (lsig_tsig S) \<phi> = Inr ust" "efail_nodes (eabs (emstate_m ust)) = 0"
  using assms by (auto simp: vinit_def Let_def split: if_splits sum.splits)

lemma sk_vkeep: "sk (vkeep (VConf (vskip_fun (vskip filt \<phi> S)) S' L pf)) = keep_spec filt \<phi> S"
  by (auto simp: fun_eq_iff sk_def vkeep_def vskip_fun vskip_def Let_def keep_spec_def string8_of_bytes_def
      Abs_bytes_inverse)

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

subsection \<open>Locale of the log monitor\<close>

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

end

end

lemma vinit_verimon_log:
  assumes "vinit ix mw rw filt S pf \<phi> = Inr (cf, z)"
  shows "verimon_log rw S \<phi>"
proof -
  obtain ust where "wf_formula \<phi>" "eminit_verimon ix mw rw (lsig_tsig S) \<phi> = Inr ust"
    using vinit_Inr[OF assms] by metis
  then show ?thesis
    by (cases "prepare_verimon rw (lsig_tsig S) \<phi>")
      (auto simp: verimon_log_def verimon_prepare_def eminit_verimon_def)
qed

(*<*)
end
(*>*)
