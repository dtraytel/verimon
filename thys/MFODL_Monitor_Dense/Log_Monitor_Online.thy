(*<*)
theory Log_Monitor_Online
  imports Log_Monitor
begin
(*>*)

section \<open>The online interface of the monitor on the log\<close>

text \<open>
  The theorems of @{theory MFODL_Monitor_Dense.Log_Monitor} describe the verdicts output for all
  of the log, or for all of it that has been read, from the initial state. This theory describes
  the monitor's online interface, as VeriMon's correctness theorem describes @{const minit} and
  @{const mstep} (@{thm [source] verimon_rewrite.wf_mstate_mstep},
  @{thm [source] verimon_rewrite.mstep_mverdicts}): an invariant @{text wf_vstate} relates the
  state to the bytes read so far and to the prefix they denote; @{const vinit} establishes it,
  and @{const vfeed_chunk} preserves it as long as the bytes read denote a prefix, reporting no
  error and outputting exactly the verdicts that the specification prescribes for that prefix and
  not for the one before, and reports an error as soon as they denote none; likewise for
  @{const vfinish}. The prefixes are those of the events that the parser keeps; the corollaries
  for logs whose events all denote a prefix, as in @{thm [source] verimon_log.vrun_log}, are at
  the end.
\<close>

subsection \<open>The dense monitor's state after a prefix\<close>

primrec dmsteps0_state :: "(Formula.database \<times> nat) list \<Rightarrow> dmstate \<Rightarrow> dmstate" where
  "dmsteps0_state [] ds = ds"
| "dmsteps0_state (tdb # \<pi>) ds = dmsteps0_state \<pi> (snd (dmstep (apfst mk_db tdb) ds))"

lift_definition dmsteps_state :: "Formula.prefix \<Rightarrow> dmstate \<Rightarrow> dmstate" is dmsteps0_state .

lemma dmsteps0_stateless_append: "dmsteps0_stateless (\<pi> @ \<pi>') ds =
  dmsteps0_stateless \<pi> ds @ dmsteps0_stateless \<pi>' (dmsteps0_state \<pi> ds)"
  by (induction \<pi> arbitrary: ds) (simp_all add: split_beta)

lemma dmsteps0_state_append: "dmsteps0_state (\<pi> @ \<pi>') ds = dmsteps0_state \<pi>' (dmsteps0_state \<pi> ds)"
  by (induction \<pi> arbitrary: ds) simp_all

text \<open>A step outputs the verdicts of time points from the index of the first one whose verdict
  is pending on, which only increases.\<close>

lemma dmstep_indices:
  assumes "dmstep tdb ds = (vs, ds')"
  shows "dmstate_i ds \<le> dmstate_i ds'" and "(k, t, X) \<in> set vs \<Longrightarrow> dmstate_i ds \<le> k \<and> k < dmstate_i ds'"
proof -
  obtain xs m where d: "deval (dmstate_j ds + 1) [snd tdb] (fst tdb) (dmstate_m ds) = (xs, m)"
    by fastforce
  obtain i' tq vs' where a: "dannotate (dmstate_i ds) (dmstate_t ds @@ [snd tdb]) xs [] = (i', tq, vs')"
    by (metis prod.exhaust)
  have "fst (dmstep tdb ds) = vs'" "dmstate_i (snd (dmstep tdb ds)) = i'"
    using d a by (simp_all add: dmstep_def)
  then have vs: "vs = vs'" and i': "dmstate_i ds' = i'"
    by (simp_all add: assms)
  note e = dannotate_eq[OF a]
  show "dmstate_i ds \<le> dmstate_i ds'"
    using e by (simp add: i')
  assume "(k, t, X) \<in> set vs"
  then show "dmstate_i ds \<le> k \<and> k < dmstate_i ds'"
    using e by (auto simp: vs i' List.in_set_enumerate_eq)
qed

lemma dmsteps0_state_mono: "dmstate_i ds \<le> dmstate_i (dmsteps0_state \<pi> ds)"
proof (induction \<pi> arbitrary: ds)
  case (Cons tdb \<pi>)
  obtain vs ds1 where s: "dmstep (apfst mk_db tdb) ds = (vs, ds1)"
    by fastforce
  show ?case
    using Cons.IH[of ds1] dmstep_indices(1)[OF s] by (simp add: s)
qed simp

lemma dmsteps0_indices:
  "(k, t, X) \<in> set (dmsteps0_stateless \<pi> ds) \<Longrightarrow> dmstate_i ds \<le> k \<and> k < dmstate_i (dmsteps0_state \<pi> ds)"
proof (induction \<pi> arbitrary: ds)
  case (Cons tdb \<pi>)
  obtain vs ds1 where s: "dmstep (apfst mk_db tdb) ds = (vs, ds1)"
    by fastforce
  from Cons.prems have "(k, t, X) \<in> set vs \<or> (k, t, X) \<in> set (dmsteps0_stateless \<pi> ds1)"
    by (simp add: s)
  then show ?case
  proof
    assume "(k, t, X) \<in> set vs"
    with dmstep_indices[OF s] dmsteps0_state_mono[of ds1 \<pi>] show ?thesis
      by (fastforce simp: s)
  next
    assume "(k, t, X) \<in> set (dmsteps0_stateless \<pi> ds1)"
    with Cons.IH[of ds1] dmstep_indices(1)[OF s] show ?thesis
      by (fastforce simp: s)
  qed
qed simp

text \<open>So the verdicts output after a prefix are disjoint from those output for it.\<close>

lemma flatten_verdicts_dmsteps0_append:
  fixes f :: "event_data table \<Rightarrow> event_data table"
  defines "W \<equiv> map (\<lambda>(i, t, X). (i, t, f X))"
  shows "flatten_verdicts (W (dmsteps0_stateless \<pi>' (dmsteps0_state \<pi> ds))) =
    flatten_verdicts (W (dmsteps0_stateless (\<pi> @ \<pi>') ds)) - flatten_verdicts (W (dmsteps0_stateless \<pi> ds))"
proof -
  let ?k = "dmstate_i (dmsteps0_state \<pi> ds)"
  let ?A = "flatten_verdicts (W (dmsteps0_stateless \<pi> ds))"
  let ?B = "flatten_verdicts (W (dmsteps0_stateless \<pi>' (dmsteps0_state \<pi> ds)))"
  have A: "x \<in> ?A \<Longrightarrow> fst x < ?k" for x
    using dmsteps0_indices[of _ _ _ \<pi> ds] by (fastforce simp: W_def flatten_verdicts_def)
  have B: "x \<in> ?B \<Longrightarrow> ?k \<le> fst x" for x
    using dmsteps0_indices[of _ _ _ \<pi>' "dmsteps0_state \<pi> ds"] dmsteps0_state_mono[of ds \<pi>]
    by (fastforce simp: W_def flatten_verdicts_def)
  have "flatten_verdicts (W (dmsteps0_stateless (\<pi> @ \<pi>') ds)) = ?A \<union> ?B"
    by (simp add: dmsteps0_stateless_append W_def)
  moreover have "?A \<inter> ?B = {}"
    using A B by fastforce
  ultimately show ?thesis
    by blast
qed

subsection \<open>The executable monitor from any state\<close>

lemma usteps_state:
  "(snd (usteps tps ust)) = dmsteps0_state (map (apfst set) tps) (ust)"
proof (induction tps arbitrary: ust)
  case (Cons tp tps)
  obtain xs t where tp: "tp = (xs, t)"
    by (cases tp)
  obtain vs1 ust1 where u: "dmstep (build_db xs, t) ust = (vs1, ust1)"
    by fastforce
  have "dmstep (mk_db (set xs), t) ust = (vs1, ust1)"
    using u by (simp add: build_db_mk_db)
  then show ?case
    using Cons.IH[of ust1] u by (cases "usteps tps ust1") (simp add: tp)
qed simp

text \<open>The items that the parser outputs are converted, and the time points they denote are fed
  to the monitor, as long as their timestamps do not decrease from the last one fed.\<close>

lemma vitems_from:
  assumes oks: "oks xs = Some es" and v: "vitems cf xs (ust, lt) = (vs, z')"
  shows "those (map (conv_item cf) es) = None \<Longrightarrow> has_verror vs"
    and "those (map (conv_item cf) es) = Some tps \<Longrightarrow> \<not> has_verror vs \<longleftrightarrow> sorted (lt # map snd tps)"
    and "those (map (conv_item cf) es) = Some tps \<Longrightarrow> \<not> has_verror vs \<Longrightarrow>
      vverdicts vs = fst (usteps tps ust) \<and> z' = (snd (usteps tps ust), last (lt # map snd tps))"
proof -
  note ok = vitems_ok[OF oks v]
  show "those (map (conv_item cf) es) = None \<Longrightarrow> has_verror vs"
    using ok by force
  assume tps: "those (map (conv_item cf) es) = Some tps"
  show "\<not> has_verror vs \<longleftrightarrow> sorted (lt # map snd tps)"
    using ok vitems_noerr[OF oks tps, of lt ust] v tps by fastforce
  show "\<not> has_verror vs \<Longrightarrow> vverdicts vs = fst (usteps tps ust) \<and> z' = (snd (usteps tps ust), last (lt # map snd tps))"
    using ok tps by fastforce
qed

subsection \<open>The prefix grows with the items\<close>

lemma those_append: "those (xs @ ys) = Option.bind (those xs) (\<lambda>as. map_option ((@) as) (those ys))"
proof (induction xs)
  case (Cons x xs)
  then show ?case
    by (cases x; cases "those xs") (auto simp: option.map_comp comp_def intro!: option.map_cong0)
qed (simp add: option.map_ident)

lemma sorted_append_last_ts:
  assumes "sorted (map snd (Rep_prefix \<pi>))"
  shows "sorted (map snd (Rep_prefix \<pi> @ xs)) \<longleftrightarrow> sorted (last_ts \<pi> # map snd xs)"
proof (cases "Rep_prefix \<pi>" rule: rev_cases)
  case Nil
  then show ?thesis
    by (simp add: last_ts.rep_eq)
next
  case (snoc ys y)
  have lt: "last_ts \<pi> = snd y"
    by (simp add: last_ts.rep_eq snoc list.case_eq_if)
  from assms show ?thesis
    by (auto simp: snoc lt sorted_append intro: order.trans)
qed

lemma last_ts_append:
  "Rep_prefix \<pi>' = Rep_prefix \<pi> @ xs \<Longrightarrow> last_ts \<pi>' = last (last_ts \<pi> # map snd xs)"
  by (cases xs rule: rev_cases) (auto simp: last_ts.rep_eq list.case_eq_if)

lemma less_eq_prefix_append: "Rep_prefix \<pi>' = Rep_prefix \<pi> @ xs \<Longrightarrow> \<pi> \<le> \<pi>'"
  by transfer auto

text \<open>The prefix that items denote, when they follow items that denote a prefix: the time points
  of the new items, which are converted as by @{const conv_item}, are appended to it if their
  timestamps do not decrease.\<close>

lemma prefix_of_items_append:
  assumes lk: "vc_lookup cf = lsig_lookup (vc_lsig cf)"
    and p: "prefix_of_items (sf (vc_pf cf)) (vc_lsig cf) None es1 = Some \<pi>"
  shows "prefix_of_items (sf (vc_pf cf)) (vc_lsig cf) fin (es1 @ abs_items es2) =
    (case those (map (conv_item cf) es2) of
      None \<Rightarrow> None
    | Some tps \<Rightarrow> (let \<delta> = map (apfst set) (tps @ fin_tps fin) in
        if sorted (last_ts \<pi> # map snd \<delta>) then Some (prefix_of_list (Rep_prefix \<pi> @ \<delta>)) else None))"
proof -
  let ?tp = "tp_of_item (sf (vc_pf cf)) (vc_lsig cf)"
  from p obtain T1 where T1: "those (map ?tp es1) = Some T1" and srt: "sorted (map snd T1)"
    and \<pi>: "\<pi> = prefix_of_list T1"
    by (auto simp: prefix_of_items_def split: option.splits if_splits)
  have R: "Rep_prefix \<pi> = T1"
    using srt by (simp add: \<pi> Rep_prefix_of_list)
  have F: "(case fin of None \<Rightarrow> [] | Some t \<Rightarrow> [({}, t)]) = map (apfst set) (fin_tps fin)"
    by (simp add: fin_tps_def split: option.splits)
  have T2: "those (map ?tp (abs_items es2)) = map_option (map (apfst set)) (those (map (conv_item cf) es2))"
    by (rule those_conv_item[OF lk])
  have T: "those (map ?tp (es1 @ abs_items es2)) =
    map_option ((@) T1) (map_option (map (apfst set)) (those (map (conv_item cf) es2)))"
    by (simp only: map_append those_append T1 T2 bind.simps)
  show ?thesis
  proof (cases "those (map (conv_item cf) es2)")
    case None
    then show ?thesis
      unfolding prefix_of_items_def T by simp
  next
    case (Some tps)
    let ?\<delta> = "map (apfst set) (tps @ fin_tps fin)"
    have S: "sorted (map snd (T1 @ ?\<delta>)) \<longleftrightarrow> sorted (last_ts \<pi> # map snd ?\<delta>)"
      using sorted_append_last_ts[of \<pi> ?\<delta>] srt by (simp only: R)
    have E: "(T1 @ map (apfst set) tps) @ (case fin of None \<Rightarrow> [] | Some t \<Rightarrow> [({}, t)]) = T1 @ ?\<delta>"
      by (simp add: F)
    have "those (map ?tp (es1 @ abs_items es2)) = Some (T1 @ map (apfst set) tps)"
      unfolding T Some by simp
    then show ?thesis
      unfolding prefix_of_items_def Let_def by (simp only: option.case Some E S R)
  qed
qed

text \<open>With the last time point with no events at the end of the input, if any.\<close>

lemma vitems_fin:
  fixes fin :: "nat option" and pos :: integer
  assumes oks: "oks xs = Some es" and v: "vitems cf xs (ust, lt) = (vs, z')"
  defines "V \<equiv> vs @ (case fin of None \<Rightarrow> [] | Some t \<Rightarrow> [fst (vtp pos [] t z')])"
  shows "those (map (conv_item cf) es) = None \<Longrightarrow> has_verror V"
    and "those (map (conv_item cf) es) = Some tps \<Longrightarrow> \<not> has_verror V \<longleftrightarrow> sorted (lt # map snd (tps @ fin_tps fin))"
    and "those (map (conv_item cf) es) = Some tps \<Longrightarrow> \<not> has_verror V \<Longrightarrow>
      vverdicts V = fst (usteps (tps @ fin_tps fin) ust)"
proof -
  note F = vitems_from[OF oks v]
  show "those (map (conv_item cf) es) = None \<Longrightarrow> has_verror V"
    using F(1) by (simp add: V_def)
  assume tps: "those (map (conv_item cf) es) = Some tps"
  have A: "\<not> has_verror vs \<longleftrightarrow> sorted (lt # map snd tps)"
    using F(2)[OF tps] .
  have B: "\<not> has_verror vs \<Longrightarrow> vverdicts vs = fst (usteps tps ust) \<and> z' = (snd (usteps tps ust), last (lt # map snd tps))"
    using F(3)[OF tps] .
  have E: "(\<not> has_verror V \<longleftrightarrow> sorted (lt # map snd (tps @ fin_tps fin))) \<and>
    (\<not> has_verror V \<longrightarrow> vverdicts V = fst (usteps (tps @ fin_tps fin) ust))"
  proof (cases fin)
    case None
    then show ?thesis
      using A B by (auto simp: V_def fin_tps_def)
  next
    case (Some t)
    obtain vs1 ust1 where u: "dmstep (build_db [], t) (snd (usteps tps ust)) = (vs1, ust1)"
      by (metis prod.exhaust)
    have S1: "sorted (lt # map snd tps) \<Longrightarrow> sorted (lt # map snd (tps @ fin_tps fin)) \<longleftrightarrow> \<not> t < last (lt # map snd tps)"
      using sorted_snoc_last[of lt "map snd tps" t] by (auto simp: Some fin_tps_def not_less)
    have S2: "\<not> sorted (lt # map snd tps) \<Longrightarrow> \<not> sorted (lt # map snd (tps @ fin_tps fin))"
      by (auto simp: sorted_append)
    show ?thesis
      using A B u S1 S2 by (auto simp: V_def Some vtp_def usteps_append fin_tps_def split: prod.splits)
  qed
  then show "\<not> has_verror V \<longleftrightarrow> sorted (lt # map snd (tps @ fin_tps fin))"
    and "\<not> has_verror V \<Longrightarrow> vverdicts V = fst (usteps (tps @ fin_tps fin) ust)"
    by auto
qed

subsection \<open>The invariant\<close>

text \<open>The prefix that the bytes read so far denote: that of the items the streaming parser has
  output (@{thm [source] efeed_chunks_online}), if they denote one.\<close>

definition stream_prefix :: "(string \<Rightarrow> bool) \<Rightarrow> (string \<Rightarrow> double option) \<Rightarrow> lsig \<Rightarrow> string \<Rightarrow>
    Formula.prefix option" where
  "stream_prefix K pf S s = Option.bind (fstream_run K s fstream_init) (\<lambda>(es, _). prefix_of_items pf S None es)"

lemma vinit_Inr_state:
  assumes "vinit mw rw filt S pf \<phi> = Inr (cf, (e, ust, n))"
  shows "cf = VConf (vskip_fun (vskip filt \<phi> S)) S (lsig_lookup_fun S) pf" and "e = einit" and "n = 0"
    and "dminit_verimon mw rw (lsig_tsig S) \<phi> = Inr ust" and "vdfail_nodes (dmstate_m ust) = 0"
  using assms by (auto simp: vinit_def Let_def split: if_splits sum.splits)

lemma dmsteps_state_Rep: "dmsteps_state \<pi> ds = dmsteps0_state (Rep_prefix \<pi>) ds"
  by (simp add: dmsteps_state_def)

lemma dmonitor_Rep: "dmonitor ds \<pi> = dmsteps0_stateless (Rep_prefix \<pi>) ds"
  by (simp add: dmonitor_def dmsteps_stateless.rep_eq)

lemma prefix_of_list_Nil: "prefix_of_list [] = pnil"
  by transfer simp

lemma prefix_of_items_Nil: "prefix_of_items pf S None [] = Some pnil"
  by (simp add: prefix_of_items_def prefix_of_list_Nil)

lemma sorted_Rep_prefix: "sorted (map snd (Rep_prefix \<pi>))"
  using Rep_prefix[of \<pi>] by simp

lemma prefix_of_items_append_Some:
  assumes "prefix_of_items pf S None (es @ es') = Some \<pi>'"
  obtains \<pi> where "prefix_of_items pf S None es = Some \<pi>"
proof -
  from assms obtain T where T: "those (map (tp_of_item pf S) (es @ es')) = Some T"
    and srt: "sorted (map snd T)"
    by (auto simp: prefix_of_items_def split: option.splits if_splits)
  then obtain T1 T2 where T1: "those (map (tp_of_item pf S) es) = Some T1" and "T = T1 @ T2"
    by (cases "those (map (tp_of_item pf S) es)"; cases "those (map (tp_of_item pf S) es')")
      (auto simp: those_append)
  with srt have "prefix_of_items pf S None es = Some (prefix_of_list T1)"
    by (simp add: prefix_of_items_def sorted_append)
  then show thesis
    by (rule that)
qed

lemma stream_prefix_append_Some:
  assumes "stream_prefix K pf S (s @ s') = Some \<pi>'"
  obtains \<pi> where "stream_prefix K pf S s = Some \<pi>"
proof -
  from assms obtain es st es2 st2 where r: "fstream_run K s fstream_init = Some (es, st)"
    and "fstream_run K s' st = Some (es2, st2)" and p: "prefix_of_items pf S None (es @ es2) = Some \<pi>'"
    by (cases "fstream_run K s fstream_init"; cases "fstream_run K s' (snd (the (fstream_run K s fstream_init)))")
      (auto simp: stream_prefix_def fstream_run_append)
  from prefix_of_items_append_Some[OF p] obtain \<pi> where "prefix_of_items pf S None es = Some \<pi>" .
  then show thesis
    by (intro that[of \<pi>]) (simp add: stream_prefix_def r)
qed

lemma prefix_of_items_append_mono:
  assumes "prefix_of_items pf S None es = Some \<pi>" and "prefix_of_items pf S None (es @ es') = Some \<pi>'"
  shows "\<pi> \<le> \<pi>'"
proof -
  from assms(1) obtain T1 where T1: "those (map (tp_of_item pf S) es) = Some T1" and s1: "sorted (map snd T1)"
    and \<pi>: "\<pi> = prefix_of_list T1"
    by (auto simp: prefix_of_items_def split: option.splits if_splits)
  from assms(2) obtain T where T: "those (map (tp_of_item pf S) (es @ es')) = Some T" and s: "sorted (map snd T)"
    and \<pi>': "\<pi>' = prefix_of_list T"
    by (auto simp: prefix_of_items_def split: option.splits if_splits)
  from T T1 obtain T2 where "T = T1 @ T2"
    by (cases "those (map (tp_of_item pf S) es')") (auto simp: those_append)
  with s s1 show ?thesis
    by (intro less_eq_prefix_append) (simp add: \<pi> \<pi>' Rep_prefix_of_list)
qed

lemma stream_prefix_mono:
  assumes "stream_prefix K pf S s = Some \<pi>" and "stream_prefix K pf S (s @ s') = Some \<pi>'"
  shows "\<pi> \<le> \<pi>'"
proof -
  from assms(1) obtain es st where r: "fstream_run K s fstream_init = Some (es, st)"
    and p: "prefix_of_items pf S None es = Some \<pi>"
    by (cases "fstream_run K s fstream_init") (auto simp: stream_prefix_def)
  from assms(2) r obtain es2 st2 where "fstream_run K s' st = Some (es2, st2)"
    and p': "prefix_of_items pf S None (es @ es2) = Some \<pi>'"
    by (cases "fstream_run K s' st") (auto simp: stream_prefix_def fstream_run_append)
  from prefix_of_items_append_mono[OF p p'] show ?thesis .
qed

lemma less_eq_prefix_Rep: "\<pi> \<le> \<pi>' \<Longrightarrow> \<exists>xs. Rep_prefix \<pi>' = Rep_prefix \<pi> @ xs"
  by transfer auto

lemma stream_prefix_filter:
  assumes "stream_prefix (\<lambda>_. True) pf S s = Some \<pi>"
  shows "stream_prefix K pf S s = Some (pmap_\<Gamma> (\<lambda>D. D \<inter> {e. K (Rep_string8 (fst e))}) \<pi>)"
proof -
  from assms obtain es st where r: "stream_run s stream_init = Some (es, st)"
    and p: "prefix_of_items pf S None es = Some \<pi>"
    by (cases "stream_run s stream_init") (auto simp: stream_prefix_def fstream_run_init)
  show ?thesis
    using prefix_of_items_filter[OF p, of K] by (cases st) (auto simp: stream_prefix_def fstream_run_init r)
qed

lemma log_prefix_filter:
  assumes "log_prefix (\<lambda>_. True) pf S fin s = Some \<pi>"
  shows "log_prefix K pf S fin s = Some (pmap_\<Gamma> (\<lambda>D. D \<inter> {e. K (Rep_string8 (fst e))}) \<pi>)"
proof -
  from assms obtain items where "parse_log s = Some items" and p: "prefix_of_items pf S fin items = Some \<pi>"
    by (cases "parse_log s") (auto simp: log_prefix_def)
  then show ?thesis
    by (simp add: log_prefix_def prefix_of_items_filter[OF p])
qed

lemma stream_prefix_items: "stream_prefix K pf S s = Some \<pi> \<Longrightarrow> \<exists>es. prefix_of_items pf S None es = Some \<pi>"
  by (cases "fstream_run K s fstream_init") (auto simp: stream_prefix_def)

lemma log_prefix_items: "log_prefix K pf S fin s = Some \<pi> \<Longrightarrow> \<exists>es. prefix_of_items pf S fin es = Some \<pi>"
  by (cases "parse_log s") (auto simp: log_prefix_def)

lemma log_prefix_fparse_log: "log_prefix K pf S fin s = Option.bind (fparse_log K s) (prefix_of_items pf S fin)"
  by (cases "parse_log s") (simp_all add: log_prefix_def fparse_log_correct)

context verimon_log
begin

context
  fixes mw :: bool
begin

interpretation monitor_\<phi>: future_bounded_mfodl "Formula.formula.map_formula (convert_tysym \<circ> check_subst) \<phi>"
  "map_sig (convert_tysym o check_subst) (lsig_tsig S)" "convert_tysym o check_subst o TAny"
  using future_bounded_\<phi> by (auto simp: future_bounded_mfodl_def future_bounded_mfodl_axioms_def wty_mfodl_def)

text \<open>The state @{text z} is the one after the bytes @{text s} are read, whose events that the
  parser keeps denote the prefix @{text \<pi>}, from the state @{const vinit} started with the
  configuration @{text cf}: its parser state is the streaming parser's after @{text s}, and its
  monitor state is the dense monitor's after @{text \<pi>}, with the last timestamp of @{text \<pi>}.\<close>

definition wf_vstate :: "bool \<Rightarrow> (bytes \<Rightarrow> double option) \<Rightarrow> vconf \<Rightarrow> string \<Rightarrow> Formula.prefix \<Rightarrow> vstate \<Rightarrow> bool" where
  "wf_vstate filt pf cf s \<pi> z \<longleftrightarrow> (\<exists>ust0 b l ps sp ust es.
     vinit mw rw filt S pf \<phi> = Inr (cf, (einit, ust0, 0)) \<and>
     z = ((b, l, Some ps, sp), (ust, last_ts \<pi>)) \<and> wf0 l \<and>
     fstream_run (keep_spec filt \<phi> S) s fstream_init = Some (es, abs_l0 l, map_fpstate Rep_bytes ps) \<and>
     prefix_of_items (sf pf) S None es = Some \<pi> \<and>
     ust = dmsteps_state \<pi> (ust0))"

text \<open>The verdicts of the dense monitor on a prefix that items denote are those the
  specification prescribes (@{thm [source] dminit_verimon_mverdicts}).\<close>

lemma dmonitor_Mt:
  assumes init: "vinit mw rw filt S pf \<phi> = Inr (cf, (einit, ust0, 0))"
    and p: "prefix_of_items (sf pf) S fin es = Some \<rho>"
  shows "flatten_verdicts (map (\<lambda>(i, t, X). (i, t, dtabw (Formula.fv_list \<phi>) (dcols (Formula.fv_list \<phi>)) X))
    (dmonitor (ust0) \<rho>)) = monitor_\<phi>.Mt \<rho>"
proof -
  note w = prefix_of_items_wty[OF p]
  have "wty_prefix (map_sig (convert_tysym o check_subst) (lsig_tsig S)) \<rho>"
    using w(1) by (simp add: map_sig_lsig)
  then show ?thesis
    by (rule dminit_verimon_mverdicts[OF vinit_Inr_state(4,5)[OF init] w(2)])
qed

text \<open>The verdicts are monotone in the prefix.\<close>

lemma Mt_mono_items:
  assumes init: "vinit mw rw filt S pf \<phi> = Inr (cf, (einit, ust0, 0))"
    and p: "prefix_of_items (sf pf) S fin es = Some \<pi>" and p': "prefix_of_items (sf pf) S fin' es' = Some \<pi>'"
    and le: "\<pi> \<le> \<pi>'"
  shows "monitor_\<phi>.Mt \<pi> \<subseteq> monitor_\<phi>.Mt \<pi>'"
proof -
  obtain xs where R: "Rep_prefix \<pi>' = Rep_prefix \<pi> @ xs"
    using less_eq_prefix_Rep[OF le] ..
  show ?thesis
    unfolding dmonitor_Mt[OF init p, symmetric] dmonitor_Mt[OF init p', symmetric]
    by (auto simp: dmonitor_Rep R dmsteps0_stateless_append)
qed

text \<open>The verdicts of the time points that follow a prefix are those that the specification
  prescribes for the longer prefix and not for the shorter one.\<close>

lemma usteps_mverdicts:
  assumes init: "vinit mw rw filt S pf \<phi> = Inr (cf, (einit, ust0, 0))"
    and p: "prefix_of_items (sf pf) S None es = Some \<pi>"
    and p': "prefix_of_items (sf pf) S fin es' = Some \<pi>'"
    and R: "Rep_prefix \<pi>' = Rep_prefix \<pi> @ map (apfst set) tps"
    and D: "ust = dmsteps_state \<pi> (ust0)"
  shows "flatten_verdicts (vwiden \<phi> (fst (usteps tps ust))) = monitor_\<phi>.Mt \<pi>' - monitor_\<phi>.Mt \<pi>"
proof -
  let ?W = "map (\<lambda>(i, t, X). (i, t, dtabw (Formula.fv_list \<phi>) (dcols (Formula.fv_list \<phi>)) X))"
  note M = dmonitor_Mt[OF init]
  have V: "vwiden \<phi> (fst (usteps tps ust)) =
    ?W (dmsteps0_stateless (map (apfst set) tps) (dmsteps0_state (Rep_prefix \<pi>) (ust0)))"
    by (simp add: vwiden_def usteps_dmsteps0 D dmsteps_state_Rep)
  have A: "flatten_verdicts (?W (dmsteps0_stateless (Rep_prefix \<pi>) (ust0))) = monitor_\<phi>.Mt \<pi>"
    using M[OF p] by (simp only: dmonitor_Rep)
  have B: "flatten_verdicts (?W (dmsteps0_stateless (Rep_prefix \<pi> @ map (apfst set) tps) (ust0))) =
    monitor_\<phi>.Mt \<pi>'"
    using M[OF p'] by (simp only: dmonitor_Rep R)
  show ?thesis
    unfolding V flatten_verdicts_dmsteps0_append A B ..
qed

text \<open>The initial state is the one after no bytes, which denote the empty prefix.\<close>

theorem wf_vstate_vinit:
  assumes init: "vinit mw rw filt S pf \<phi> = Inr (cf, z)"
  shows "wf_vstate filt pf cf [] pnil z"
proof -
  obtain e ust n where z: "z = (e, ust, n)"
    by (metis prod_cases3)
  have init': "vinit mw rw filt S pf \<phi> = Inr (cf, (einit, ust, 0))"
    using init vinit_Inr_state(2,3)[OF init[unfolded z]] by (simp add: z)
  have Z: "z = ((0, E_INIT, Some F_INIT, 0), (ust, last_ts pnil))"
    using vinit_Inr_state(2,3)[OF init[unfolded z]] by (simp add: z einit_def last_ts.rep_eq pnil.rep_eq)
  show ?thesis
    unfolding wf_vstate_def
    by (rule exI[of _ ust], rule exI[of _ 0], rule exI[of _ E_INIT], rule exI[of _ F_INIT], rule exI[of _ 0],
        rule exI[of _ ust], rule exI[of _ "[]"])
      (simp add: init' Z fstream_init_def abs_l0_def prefix_of_items_Nil dmsteps_state_Rep pnil.rep_eq)
qed

text \<open>A chunk of the input: if the bytes read so far no longer denote a prefix, the monitor
  reports an error; otherwise, it reports none, the invariant holds for the longer prefix, and the
  verdicts are exactly those that the specification prescribes for the longer prefix and not
  for the shorter one.\<close>

theorem vfeed_chunk_online:
  assumes wf: "wf_vstate filt pf cf s \<pi> z" and step: "vfeed_chunk cf c z = (outs, z')"
  shows "stream_prefix (keep_spec filt \<phi> S) (sf pf) S (s @ Rep_bytes c) = None \<Longrightarrow> has_verror outs"
    and "stream_prefix (keep_spec filt \<phi> S) (sf pf) S (s @ Rep_bytes c) = Some \<pi>' \<Longrightarrow>
      \<not> has_verror outs \<and> \<pi> \<le> \<pi>' \<and> wf_vstate filt pf cf (s @ Rep_bytes c) \<pi>' z' \<and>
      flatten_verdicts (vwiden \<phi> (vverdicts outs)) = monitor_\<phi>.Mt \<pi>' - monitor_\<phi>.Mt \<pi>"
proof -
  obtain ust0 b l ps sp ust es where init: "vinit mw rw filt S pf \<phi> = Inr (cf, (einit, ust0, 0))"
    and z: "z = ((b, l, Some ps, sp), (ust, last_ts \<pi>))" and w0: "wf0 l"
    and R: "fstream_run (keep_spec filt \<phi> S) s fstream_init = Some (es, abs_l0 l, map_fpstate Rep_bytes ps)"
    and p: "prefix_of_items (sf pf) S None es = Some \<pi>"
    and D: "ust = dmsteps_state \<pi> (ust0)"
    using wf unfolding wf_vstate_def by blast
  note cf = vinit_Inr_state(1)[OF init]
  let ?K = "keep_spec filt \<phi> S" and ?k = "vkeep cf"
  have K: "sk ?k = ?K"
    by (simp add: cf sk_vkeep)
  have lk: "vc_lookup cf = lsig_lookup (vc_lsig cf)"
    by (simp add: cf)
  have pcf: "vc_pf cf = pf" "vc_lsig cf = S"
    by (simp_all add: cf)
  have p': "prefix_of_items (sf (vc_pf cf)) (vc_lsig cf) None es = Some \<pi>"
    using p by (simp add: pcf)
  obtain xs est where e: "efeed_chunk ?k c (b, l, Some ps, sp) = (xs, est)"
    by (cases "efeed_chunk ?k c (b, l, Some ps, sp)")
  obtain vs mst where v: "vitems cf xs (ust, last_ts \<pi>) = (vs, mst)"
    by (cases "vitems cf xs (ust, last_ts \<pi>)")
  have outs: "outs = vs" and z': "z' = (est, mst)"
    using step by (simp_all add: vfeed_chunk_def z e v)
  note C = efeed_chunk_correct[OF w0, where k = ?k and s = c and ps = ps and b = b and sp = sp, unfolded K e]
  have SP: "stream_prefix ?K (sf pf) S (s @ Rep_bytes c) =
    (case fstream_run ?K (Rep_bytes c) (abs_l0 l, map_fpstate Rep_bytes ps) of
      None \<Rightarrow> None
    | Some (es2, _) \<Rightarrow> prefix_of_items (sf pf) S None (es @ es2))"
    by (simp add: stream_prefix_def fstream_run_append R split: option.splits prod.splits)
  have main: "case stream_prefix ?K (sf pf) S (s @ Rep_bytes c) of
      None \<Rightarrow> has_verror outs
    | Some \<pi>' \<Rightarrow> \<not> has_verror outs \<and> \<pi> \<le> \<pi>' \<and> wf_vstate filt pf cf (s @ Rep_bytes c) \<pi>' z' \<and>
        flatten_verdicts (vwiden \<phi> (vverdicts outs)) = monitor_\<phi>.Mt \<pi>' - monitor_\<phi>.Mt \<pi>"
  proof (cases "fstream_run ?K (Rep_bytes c) (abs_l0 l, map_fpstate Rep_bytes ps)")
    case None
    with C have "has_err xs"
      by simp
    then show ?thesis
      using vitems_has_err[of xs cf "(ust, last_ts \<pi>)"] by (simp add: SP None outs v)
  next
    case (Some r)
    obtain es2 L' P' where r: "r = (es2, L', P')"
      by (cases r)
    with C Some obtain es2' l' ps' sp' where est: "est = (b + bytes_length c, l', Some ps', sp')"
      and oks: "oks xs = Some es2'" and a: "abs_items es2' = es2" and "abs_l0 l' = L'" and w0': "wf0 l'"
      and "map_fpstate Rep_bytes ps' = P'"
      by auto
    then have R': "fstream_run ?K (s @ Rep_bytes c) fstream_init =
      Some (es @ abs_items es2', abs_l0 l', map_fpstate Rep_bytes ps')"
      by (simp add: fstream_run_append R Some r)
    have SP': "stream_prefix ?K (sf pf) S (s @ Rep_bytes c) = prefix_of_items (sf pf) S None (es @ abs_items es2')"
      by (simp add: SP Some r a)
    note PA = prefix_of_items_append[OF lk p', of None es2', unfolded pcf]
    show ?thesis
    proof (cases "those (map (conv_item cf) es2')")
      case None
      then show ?thesis
        using vitems_from(1)[OF oks v] PA by (simp add: SP' outs)
    next
      case (Some tps)
      have fin: "tps @ fin_tps None = tps"
        by (simp add: fin_tps_def)
      show ?thesis
      proof (cases "sorted (last_ts \<pi> # map snd tps)")
        case False
        then have F: "\<not> sorted (last_ts \<pi> # map snd (map (apfst set) tps))"
          by simp
        have "prefix_of_items (sf pf) S None (es @ abs_items es2') = None"
          using PA by (simp only: Some option.case Let_def fin F if_False)
        then show ?thesis
          using vitems_from(2)[OF oks v Some] False by (auto simp: SP' outs)
      next
        case True
        let ?\<pi>' = "prefix_of_list (Rep_prefix \<pi> @ map (apfst set) tps)"
        have T: "sorted (last_ts \<pi> # map snd (map (apfst set) tps))"
          using True by simp
        have P': "prefix_of_items (sf pf) S None (es @ abs_items es2') = Some ?\<pi>'"
          using PA by (simp only: Some option.case Let_def T if_True fin)
        have Rep': "Rep_prefix ?\<pi>' = Rep_prefix \<pi> @ map (apfst set) tps"
          using True sorted_append_last_ts[of \<pi> "map (apfst set) tps"] sorted_Rep_prefix[of \<pi>]
          by (simp add: Rep_prefix_of_list)
        have ok: "\<not> has_verror vs"
          using vitems_from(2)[OF oks v Some] True by simp
        have vv: "vverdicts vs = fst (usteps tps ust)"
          and mst: "mst = (snd (usteps tps ust), last (last_ts \<pi> # map snd tps))"
          using vitems_from(3)[OF oks v Some ok] by auto
        have D': "(snd (usteps tps ust)) = dmsteps_state ?\<pi>' (ust0)"
          by (simp add: usteps_state D dmsteps_state_Rep Rep' dmsteps0_state_append)
        have mst': "mst = (snd (usteps tps ust), last_ts ?\<pi>')"
          using mst last_ts_append[OF Rep'] by simp
        have wf': "wf_vstate filt pf cf (s @ Rep_bytes c) ?\<pi>' z'"
          unfolding wf_vstate_def
          by (rule exI[of _ ust0], rule exI[of _ "b + bytes_length c"], rule exI[of _ l'], rule exI[of _ ps'],
              rule exI[of _ sp'], rule exI[of _ "snd (usteps tps ust)"], rule exI[of _ "es @ abs_items es2'"])
            (simp add: init z' est mst' w0' R' P' D')
        have V: "flatten_verdicts (vwiden \<phi> (vverdicts vs)) = monitor_\<phi>.Mt ?\<pi>' - monitor_\<phi>.Mt \<pi>"
          using usteps_mverdicts[OF init p P' Rep' D] by (simp add: vv)
        show ?thesis
          using ok wf' V less_eq_prefix_append[OF Rep'] by (simp add: SP' P' outs)
      qed
    qed
  qed
  show "stream_prefix ?K (sf pf) S (s @ Rep_bytes c) = None \<Longrightarrow> has_verror outs"
    using main by simp
  show "stream_prefix ?K (sf pf) S (s @ Rep_bytes c) = Some \<pi>' \<Longrightarrow>
      \<not> has_verror outs \<and> \<pi> \<le> \<pi>' \<and> wf_vstate filt pf cf (s @ Rep_bytes c) \<pi>' z' \<and>
      flatten_verdicts (vwiden \<phi> (vverdicts outs)) = monitor_\<phi>.Mt \<pi>' - monitor_\<phi>.Mt \<pi>"
    using main by simp
qed

text \<open>The end of the input, followed by a last time point with no events at timestamp
  @{text t} if @{text "fin = Some t"}: if the bytes read do not denote a prefix, the monitor reports
  an error; otherwise, it reports none, and its verdicts are exactly those that the specification
  prescribes for the prefix and not for the one before.\<close>

theorem vfinish_online:
  assumes wf: "wf_vstate filt pf cf s \<pi> z"
  shows "log_prefix (keep_spec filt \<phi> S) (sf pf) S fin s = None \<Longrightarrow> has_verror (vfinish cf fin z)"
    and "log_prefix (keep_spec filt \<phi> S) (sf pf) S fin s = Some \<pi>' \<Longrightarrow>
      \<not> has_verror (vfinish cf fin z) \<and> \<pi> \<le> \<pi>' \<and>
      flatten_verdicts (vwiden \<phi> (vverdicts (vfinish cf fin z))) = monitor_\<phi>.Mt \<pi>' - monitor_\<phi>.Mt \<pi>"
proof -
  obtain ust0 b l ps sp ust es where init: "vinit mw rw filt S pf \<phi> = Inr (cf, (einit, ust0, 0))"
    and z: "z = ((b, l, Some ps, sp), (ust, last_ts \<pi>))" and w0: "wf0 l"
    and R: "fstream_run (keep_spec filt \<phi> S) s fstream_init = Some (es, abs_l0 l, map_fpstate Rep_bytes ps)"
    and p: "prefix_of_items (sf pf) S None es = Some \<pi>"
    and D: "ust = dmsteps_state \<pi> (ust0)"
    using wf unfolding wf_vstate_def by blast
  note cf = vinit_Inr_state(1)[OF init]
  let ?K = "keep_spec filt \<phi> S" and ?k = "vkeep cf"
  let ?xs = "efinish ?k (b, l, Some ps, sp)"
  have K: "sk ?k = ?K"
    by (simp add: cf sk_vkeep)
  have lk: "vc_lookup cf = lsig_lookup (vc_lsig cf)"
    by (simp add: cf)
  have pcf: "vc_pf cf = pf" "vc_lsig cf = S"
    by (simp_all add: cf)
  have p': "prefix_of_items (sf (vc_pf cf)) (vc_lsig cf) None es = Some \<pi>"
    using p by (simp add: pcf)
  obtain vs mst where v: "vitems cf ?xs (ust, last_ts \<pi>) = (vs, mst)"
    by (cases "vitems cf ?xs (ust, last_ts \<pi>)")
  define V where "V = vs @ (case fin of None \<Rightarrow> [] | Some t \<Rightarrow> [fst (vtp b [] t mst)])"
  have fz: "vfinish cf fin z = V"
    by (simp add: vfinish_def z v V_def split: option.splits)
  note C = efinish_correct[OF w0, where k = ?k and ps = ps and b = b and sp = sp, unfolded K]
  have LP: "log_prefix ?K (sf pf) S fin s =
    (case fstream_finish ?K (abs_l0 l, map_fpstate Rep_bytes ps) of
      None \<Rightarrow> None
    | Some es2 \<Rightarrow> prefix_of_items (sf pf) S fin (es @ es2))"
    by (simp add: log_prefix_fparse_log fparse_log_def R split: option.splits)
  have main: "case log_prefix ?K (sf pf) S fin s of
      None \<Rightarrow> has_verror V
    | Some \<pi>' \<Rightarrow> \<not> has_verror V \<and> \<pi> \<le> \<pi>' \<and>
        flatten_verdicts (vwiden \<phi> (vverdicts V)) = monitor_\<phi>.Mt \<pi>' - monitor_\<phi>.Mt \<pi>"
  proof (cases "fstream_finish ?K (abs_l0 l, map_fpstate Rep_bytes ps)")
    case None
    with C have "has_err ?xs"
      by simp
    then show ?thesis
      using vitems_has_err[of ?xs cf "(ust, last_ts \<pi>)"] by (simp add: LP None v V_def)
  next
    case (Some es2)
    with C obtain es2' where oks: "oks ?xs = Some es2'" and a: "abs_items es2' = es2"
      by auto
    have LP': "log_prefix ?K (sf pf) S fin s = prefix_of_items (sf pf) S fin (es @ abs_items es2')"
      by (simp add: LP Some a)
    note PA = prefix_of_items_append[OF lk p', of fin es2', unfolded pcf]
    note VF = vitems_fin[OF oks v, where fin = fin and pos = b, folded V_def]
    show ?thesis
    proof (cases "those (map (conv_item cf) es2')")
      case None
      then show ?thesis
        using VF(1) PA by (simp add: LP')
    next
      case (Some tps)
      let ?\<delta> = "map (apfst set) (tps @ fin_tps fin)"
      show ?thesis
      proof (cases "sorted (last_ts \<pi> # map snd ?\<delta>)")
        case False
        have "prefix_of_items (sf pf) S fin (es @ abs_items es2') = None"
          using PA by (simp only: Some option.case Let_def False if_False)
        then show ?thesis
          using VF(2)[OF Some] False by (auto simp: LP')
      next
        case True
        let ?\<pi>' = "prefix_of_list (Rep_prefix \<pi> @ ?\<delta>)"
        have P': "prefix_of_items (sf pf) S fin (es @ abs_items es2') = Some ?\<pi>'"
          using PA by (simp only: Some option.case Let_def True if_True)
        have Rep': "Rep_prefix ?\<pi>' = Rep_prefix \<pi> @ ?\<delta>"
          using True sorted_append_last_ts[of \<pi> ?\<delta>] sorted_Rep_prefix[of \<pi>]
          by (simp add: Rep_prefix_of_list)
        have ok: "\<not> has_verror V"
          using VF(2)[OF Some] True by simp
        have vv: "vverdicts V = fst (usteps (tps @ fin_tps fin) ust)"
          using VF(3)[OF Some ok] .
        have "flatten_verdicts (vwiden \<phi> (vverdicts V)) = monitor_\<phi>.Mt ?\<pi>' - monitor_\<phi>.Mt \<pi>"
          using usteps_mverdicts[OF init p P' Rep' D] by (simp add: vv)
        then show ?thesis
          using ok less_eq_prefix_append[OF Rep'] by (simp add: LP' P')
      qed
    qed
  qed
  show "log_prefix ?K (sf pf) S fin s = None \<Longrightarrow> has_verror (vfinish cf fin z)"
    using main by (simp add: fz)
  show "log_prefix ?K (sf pf) S fin s = Some \<pi>' \<Longrightarrow>
      \<not> has_verror (vfinish cf fin z) \<and> \<pi> \<le> \<pi>' \<and>
      flatten_verdicts (vwiden \<phi> (vverdicts (vfinish cf fin z))) = monitor_\<phi>.Mt \<pi>' - monitor_\<phi>.Mt \<pi>"
    using main by (simp add: fz)
qed

lemma wf_vstate_stream_prefix:
  "wf_vstate filt pf cf s \<pi> z \<Longrightarrow> stream_prefix (keep_spec filt \<phi> S) (sf pf) S s = Some \<pi>"
  by (auto simp: wf_vstate_def stream_prefix_def)

lemma wf_vstate_Mt_mono:
  assumes "wf_vstate filt pf cf s \<pi> z" and "wf_vstate filt pf cf s' \<pi>' z'" and "\<pi> \<le> \<pi>'"
  shows "monitor_\<phi>.Mt \<pi> \<subseteq> monitor_\<phi>.Mt \<pi>'"
proof -
  from assms(1) obtain ust0 es where init: "vinit mw rw filt S pf \<phi> = Inr (cf, (einit, ust0, 0))"
    and p: "prefix_of_items (sf pf) S None es = Some \<pi>"
    unfolding wf_vstate_def by blast
  from assms(2) obtain ust0' es' where init': "vinit mw rw filt S pf \<phi> = Inr (cf, (einit, ust0', 0))"
    and p': "prefix_of_items (sf pf) S None es' = Some \<pi>'"
    unfolding wf_vstate_def by blast
  from init init' have "ust0' = ust0"
    by simp
  with Mt_mono_items[OF init p _ assms(3)] p' show ?thesis
    by blast
qed

text \<open>Several chunks at once, as long as the bytes read denote a prefix.\<close>

theorem vfeed_chunks_online_step:
  assumes "wf_vstate filt pf cf s \<pi> z" and "vfeed_chunks cf cs z = (outs, z')"
    and "stream_prefix (keep_spec filt \<phi> S) (sf pf) S (s @ concat (map Rep_bytes cs)) = Some \<pi>'"
  shows "\<not> has_verror outs \<and> \<pi> \<le> \<pi>' \<and> wf_vstate filt pf cf (s @ concat (map Rep_bytes cs)) \<pi>' z' \<and>
    flatten_verdicts (vwiden \<phi> (vverdicts outs)) = monitor_\<phi>.Mt \<pi>' - monitor_\<phi>.Mt \<pi>"
  using assms
proof (induction cs arbitrary: s \<pi> z outs)
  case Nil
  then have "\<pi>' = \<pi>" and "outs = []" and "z' = z"
    using wf_vstate_stream_prefix[OF Nil.prems(1)] by simp_all
  with Nil.prems(1) show ?case
    by (simp add: flatten_verdicts_def vwiden_def)
next
  case (Cons c cs)
  obtain outs1 z1 where s1: "vfeed_chunk cf c z = (outs1, z1)"
    by (cases "vfeed_chunk cf c z")
  obtain outs2 where s2: "vfeed_chunks cf cs z1 = (outs2, z')" and outs: "outs = outs1 @ outs2"
    using Cons.prems(2) s1 by (auto split: prod.splits)
  have "stream_prefix (keep_spec filt \<phi> S) (sf pf) S ((s @ Rep_bytes c) @ concat (map Rep_bytes cs)) = Some \<pi>'"
    using Cons.prems(3) by simp
  then obtain \<pi>1 where sp1: "stream_prefix (keep_spec filt \<phi> S) (sf pf) S (s @ Rep_bytes c) = Some \<pi>1"
    by (rule stream_prefix_append_Some)
  note O1 = vfeed_chunk_online(2)[OF Cons.prems(1) s1 sp1]
  have O2: "\<not> has_verror outs2 \<and> \<pi>1 \<le> \<pi>' \<and> wf_vstate filt pf cf ((s @ Rep_bytes c) @ concat (map Rep_bytes cs)) \<pi>' z' \<and>
    flatten_verdicts (vwiden \<phi> (vverdicts outs2)) = monitor_\<phi>.Mt \<pi>' - monitor_\<phi>.Mt \<pi>1"
    by (rule Cons.IH) (use O1 s2 Cons.prems(3) in simp_all)
  have m1: "monitor_\<phi>.Mt \<pi> \<subseteq> monitor_\<phi>.Mt \<pi>1"
    using wf_vstate_Mt_mono[OF Cons.prems(1)] O1 by blast
  have m2: "monitor_\<phi>.Mt \<pi>1 \<subseteq> monitor_\<phi>.Mt \<pi>'"
    using wf_vstate_Mt_mono O1 O2 by blast
  have V: "flatten_verdicts (vwiden \<phi> (vverdicts outs)) =
    flatten_verdicts (vwiden \<phi> (vverdicts outs1)) \<union> flatten_verdicts (vwiden \<phi> (vverdicts outs2))"
    by (simp add: outs vwiden_def)
  have F1: "flatten_verdicts (vwiden \<phi> (vverdicts outs1)) = monitor_\<phi>.Mt \<pi>1 - monitor_\<phi>.Mt \<pi>"
    using O1 by blast
  have F2: "flatten_verdicts (vwiden \<phi> (vverdicts outs2)) = monitor_\<phi>.Mt \<pi>' - monitor_\<phi>.Mt \<pi>1"
    using O2 by blast
  have "\<not> has_verror outs"
    using O1 O2 by (simp add: outs)
  moreover have "\<pi> \<le> \<pi>'"
    using O1 O2 by (blast intro: order.trans)
  moreover have "wf_vstate filt pf cf (s @ concat (map Rep_bytes (c # cs))) \<pi>' z'"
    using O2 by simp
  moreover have "flatten_verdicts (vwiden \<phi> (vverdicts outs)) = monitor_\<phi>.Mt \<pi>' - monitor_\<phi>.Mt \<pi>"
    unfolding V F1 F2 using m1 m2 by blast
  ultimately show ?case
    by blast
qed

theorem vfeed_chunks_online_error:
  assumes "wf_vstate filt pf cf s \<pi> z" and "vfeed_chunks cf cs z = (outs, z')"
    and "stream_prefix (keep_spec filt \<phi> S) (sf pf) S (s @ concat (map Rep_bytes cs)) = None"
  shows "has_verror outs"
  using assms
proof (induction cs arbitrary: s \<pi> z outs)
  case Nil
  then show ?case
    using wf_vstate_stream_prefix[OF Nil.prems(1)] by simp
next
  case (Cons c cs)
  obtain outs1 z1 where s1: "vfeed_chunk cf c z = (outs1, z1)"
    by (cases "vfeed_chunk cf c z")
  obtain outs2 where s2: "vfeed_chunks cf cs z1 = (outs2, z')" and outs: "outs = outs1 @ outs2"
    using Cons.prems(2) s1 by (auto split: prod.splits)
  show ?case
  proof (cases "stream_prefix (keep_spec filt \<phi> S) (sf pf) S (s @ Rep_bytes c)")
    case None
    then show ?thesis
      using vfeed_chunk_online(1)[OF Cons.prems(1) s1] by (simp add: outs)
  next
    case (Some \<pi>1)
    note O1 = vfeed_chunk_online(2)[OF Cons.prems(1) s1 Some]
    have "has_verror outs2"
      by (rule Cons.IH[where s = "s @ Rep_bytes c" and \<pi> = \<pi>1]) (use O1 s2 Cons.prems(3) in simp_all)
    then show ?thesis
      by (simp add: outs)
  qed
qed

text \<open>The verdicts do not depend on the events that the parser skips.\<close>

lemma Mt_filter:
  assumes "prefix_of_items (sf pf) S fin es = Some \<rho>"
  shows "monitor_\<phi>.Mt (pmap_\<Gamma> (\<lambda>D. D \<inter> {e. keep_spec filt \<phi> S (Rep_string8 (fst e))}) \<rho>) = monitor_\<phi>.Mt \<rho>"
proof -
  let ?E = "{e. keep_spec filt \<phi> S (Rep_string8 (fst e))}"
  have E: "Safety.matches v (Formula.formula.map_formula (convert_tysym \<circ> check_subst) \<phi>) e \<Longrightarrow> e \<in> ?E" for v e
    using matches_preds[of v "Formula.formula.map_formula (convert_tysym \<circ> check_subst) \<phi>" e]
    by (force simp: keep_spec_def Rep_string8_inverse)
  show ?thesis
    using monitor_\<phi>.Mt_restrict[OF _ E] prefix_of_items_wty(1)[OF assms] by (simp add: map_sig_lsig)
qed

text \<open>The online versions of @{thm [source] vrun_log}: for bytes whose events all denote a
  prefix, a chunk and the end of the input report no error, and output exactly the verdicts that
  the specification prescribes for the longer prefix and not for the shorter one, although the
  parser skips the events of the other declared predicates if @{text filt}.\<close>

theorem vfeed_chunk_online_log:
  assumes wf: "wf_vstate filt pf cf s \<pi>0 z" and step: "vfeed_chunk cf c z = (outs, z')"
    and p: "stream_prefix (\<lambda>_. True) (sf pf) S s = Some \<pi>"
    and p': "stream_prefix (\<lambda>_. True) (sf pf) S (s @ Rep_bytes c) = Some \<pi>'"
  shows "\<not> has_verror outs" and "\<pi> \<le> \<pi>'"
    and "wf_vstate filt pf cf (s @ Rep_bytes c) (pmap_\<Gamma> (\<lambda>D. D \<inter> {e. keep_spec filt \<phi> S (Rep_string8 (fst e))}) \<pi>') z'"
    and "flatten_verdicts (vwiden \<phi> (vverdicts outs)) = monitor_\<phi>.Mt \<pi>' - monitor_\<phi>.Mt \<pi>"
proof -
  let ?g = "\<lambda>D. D \<inter> {e. keep_spec filt \<phi> S (Rep_string8 (fst e))}"
  have f: "stream_prefix (keep_spec filt \<phi> S) (sf pf) S s = Some (pmap_\<Gamma> ?g \<pi>)"
    by (rule stream_prefix_filter[OF p])
  have f': "stream_prefix (keep_spec filt \<phi> S) (sf pf) S (s @ Rep_bytes c) = Some (pmap_\<Gamma> ?g \<pi>')"
    by (rule stream_prefix_filter[OF p'])
  have \<pi>0: "\<pi>0 = pmap_\<Gamma> ?g \<pi>"
    using wf_vstate_stream_prefix[OF wf] f by simp
  note O = vfeed_chunk_online(2)[OF wf step f']
  obtain es where "prefix_of_items (sf pf) S None es = Some \<pi>"
    using stream_prefix_items[OF p] by blast
  note M = Mt_filter[OF this]
  obtain es' where "prefix_of_items (sf pf) S None es' = Some \<pi>'"
    using stream_prefix_items[OF p'] by blast
  note M' = Mt_filter[OF this]
  show "\<not> has_verror outs" and "wf_vstate filt pf cf (s @ Rep_bytes c) (pmap_\<Gamma> ?g \<pi>') z'"
    using O by blast+
  show "\<pi> \<le> \<pi>'"
    by (rule stream_prefix_mono[OF p p'])
  have "flatten_verdicts (vwiden \<phi> (vverdicts outs)) = monitor_\<phi>.Mt (pmap_\<Gamma> ?g \<pi>') - monitor_\<phi>.Mt (pmap_\<Gamma> ?g \<pi>)"
    using O unfolding \<pi>0 by blast
  then show "flatten_verdicts (vwiden \<phi> (vverdicts outs)) = monitor_\<phi>.Mt \<pi>' - monitor_\<phi>.Mt \<pi>"
    by (simp only: M M')
qed

theorem vfinish_online_log:
  assumes wf: "wf_vstate filt pf cf s \<pi>0 z"
    and p: "stream_prefix (\<lambda>_. True) (sf pf) S s = Some \<pi>"
    and p': "log_prefix (\<lambda>_. True) (sf pf) S fin s = Some \<pi>'"
  shows "\<not> has_verror (vfinish cf fin z)"
    and "flatten_verdicts (vwiden \<phi> (vverdicts (vfinish cf fin z))) = monitor_\<phi>.Mt \<pi>' - monitor_\<phi>.Mt \<pi>"
proof -
  let ?g = "\<lambda>D. D \<inter> {e. keep_spec filt \<phi> S (Rep_string8 (fst e))}"
  have f: "stream_prefix (keep_spec filt \<phi> S) (sf pf) S s = Some (pmap_\<Gamma> ?g \<pi>)"
    by (rule stream_prefix_filter[OF p])
  have f': "log_prefix (keep_spec filt \<phi> S) (sf pf) S fin s = Some (pmap_\<Gamma> ?g \<pi>')"
    by (rule log_prefix_filter[OF p'])
  have \<pi>0: "\<pi>0 = pmap_\<Gamma> ?g \<pi>"
    using wf_vstate_stream_prefix[OF wf] f by simp
  note O = vfinish_online(2)[OF wf f']
  obtain es where "prefix_of_items (sf pf) S None es = Some \<pi>"
    using stream_prefix_items[OF p] by blast
  note M = Mt_filter[OF this]
  obtain es' where "prefix_of_items (sf pf) S fin es' = Some \<pi>'"
    using log_prefix_items[OF p'] by blast
  note M' = Mt_filter[OF this]
  show "\<not> has_verror (vfinish cf fin z)"
    using O by blast
  have "flatten_verdicts (vwiden \<phi> (vverdicts (vfinish cf fin z))) =
    monitor_\<phi>.Mt (pmap_\<Gamma> ?g \<pi>') - monitor_\<phi>.Mt (pmap_\<Gamma> ?g \<pi>)"
    using O unfolding \<pi>0 by blast
  then show "flatten_verdicts (vwiden \<phi> (vverdicts (vfinish cf fin z))) = monitor_\<phi>.Mt \<pi>' - monitor_\<phi>.Mt \<pi>"
    by (simp only: M M')
qed

theorem vfeed_chunks_online_log:
  assumes wf: "wf_vstate filt pf cf s \<pi>0 z" and steps: "vfeed_chunks cf cs z = (outs, z')"
    and p: "stream_prefix (\<lambda>_. True) (sf pf) S s = Some \<pi>"
    and p': "stream_prefix (\<lambda>_. True) (sf pf) S (s @ concat (map Rep_bytes cs)) = Some \<pi>'"
  shows "\<not> has_verror outs" and "\<pi> \<le> \<pi>'"
    and "wf_vstate filt pf cf (s @ concat (map Rep_bytes cs))
      (pmap_\<Gamma> (\<lambda>D. D \<inter> {e. keep_spec filt \<phi> S (Rep_string8 (fst e))}) \<pi>') z'"
    and "flatten_verdicts (vwiden \<phi> (vverdicts outs)) = monitor_\<phi>.Mt \<pi>' - monitor_\<phi>.Mt \<pi>"
proof -
  let ?g = "\<lambda>D. D \<inter> {e. keep_spec filt \<phi> S (Rep_string8 (fst e))}"
  have f: "stream_prefix (keep_spec filt \<phi> S) (sf pf) S s = Some (pmap_\<Gamma> ?g \<pi>)"
    by (rule stream_prefix_filter[OF p])
  have f': "stream_prefix (keep_spec filt \<phi> S) (sf pf) S (s @ concat (map Rep_bytes cs)) = Some (pmap_\<Gamma> ?g \<pi>')"
    by (rule stream_prefix_filter[OF p'])
  have \<pi>0: "\<pi>0 = pmap_\<Gamma> ?g \<pi>"
    using wf_vstate_stream_prefix[OF wf] f by simp
  note O = vfeed_chunks_online_step[OF wf steps f']
  obtain es where "prefix_of_items (sf pf) S None es = Some \<pi>"
    using stream_prefix_items[OF p] by blast
  note M = Mt_filter[OF this]
  obtain es' where "prefix_of_items (sf pf) S None es' = Some \<pi>'"
    using stream_prefix_items[OF p'] by blast
  note M' = Mt_filter[OF this]
  show "\<not> has_verror outs"
    and "wf_vstate filt pf cf (s @ concat (map Rep_bytes cs)) (pmap_\<Gamma> ?g \<pi>') z'"
    using O by blast+
  show "\<pi> \<le> \<pi>'"
    by (rule stream_prefix_mono[OF p p'])
  have "flatten_verdicts (vwiden \<phi> (vverdicts outs)) = monitor_\<phi>.Mt (pmap_\<Gamma> ?g \<pi>') - monitor_\<phi>.Mt (pmap_\<Gamma> ?g \<pi>)"
    using O unfolding \<pi>0 by blast
  then show "flatten_verdicts (vwiden \<phi> (vverdicts outs)) = monitor_\<phi>.Mt \<pi>' - monitor_\<phi>.Mt \<pi>"
    by (simp only: M M')
qed

text \<open>In summary, for the monitor on the log, as for VeriMon's kernel
  (@{thm [source] verimon_rewrite.wf_mstate_minit}, @{thm [source] verimon_rewrite.wf_mstate_mstep},
  @{thm [source] verimon_rewrite.mstep_mverdicts}):
  \begin{itemize}
  \item @{thm [source] wf_vstate_vinit}: @{thm wf_vstate_vinit[no_vars]}
  \item @{thm [source] vfeed_chunk_online}: @{thm vfeed_chunk_online[no_vars]}
  \item @{thm [source] vfinish_online}: @{thm vfinish_online[no_vars]}
  \item @{thm [source] vfeed_chunks_online_step}: @{thm vfeed_chunks_online_step[no_vars]}
  \item @{thm [source] vfeed_chunk_online_log}: @{thm vfeed_chunk_online_log[no_vars]}
  \item @{thm [source] vfinish_online_log}: @{thm vfinish_online_log[no_vars]}
  \item @{thm [source] vfeed_chunks_online_log}: @{thm vfeed_chunks_online_log[no_vars]}
  \item @{thm [source] vfeed_chunks_online_error}: @{thm vfeed_chunks_online_error[no_vars]}
  \end{itemize}
  The prefixes are those of the events that the parser keeps; by
  @{thm [source] Mt_preds}, the verdicts are those of every well-typed prefix with the same events
  of the predicates that occur freely in the formula.\<close>

end

end

(*<*)
end
(*>*)
