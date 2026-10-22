(*<*)
theory CLI_Proof
  imports "VeriMon_CLI.CLI" "Monitor_Exec_Proof.Log_Monitor_Online"
begin
(*>*)

section \<open>The verified monitor with MonPoly's command line: correctness\<close>

subsection \<open>Correctness\<close>

text \<open>If the monitor starts on the contents of the two files, then they are a formula and a
  signature, and the monitor was started by @{const vinit} on the converted formula and the
  converted signature.\<close>

lemma cli_main_Run:
  assumes "cli_main prog args pf = NeedFile fn k1" "k1 ftext = NeedFile sn k2"
    and "k2 stext = Run msg conf cf z fin n L"
  obtains \<psi>0 S \<phi> f where "parse_formula (Rep_bytes ftext) = Some \<psi>0"
    and "read_sig (Rep_bytes stext) = Inr S"
    and "conv_formula pf (c_rw conf) (input_formula conf \<psi>0) = Inr \<phi>"
    and "lsig_of S \<phi> = Inr L"
    and "check (lsig_tsig L) TAny \<phi> = Inr f"
    and "vinit (c_index conf) (c_mw conf) (c_rw conf) (c_filter conf) L pf \<phi> = Inr (cf, z)"
  using assms unfolding cli_main_def start_monitor_def Let_def
  by (auto split: command.splits if_splits option.splits sum.splits vinit_error.splits prod.splits)

text \<open>The main theorem: the monitor runs on the formula of the input and the signature, which
  satisfy the assumptions of @{locale verimon_log}. So for every log that denotes a prefix, the
  monitor reports no error and outputs the verdicts that the specification of the formula
  prescribes for the prefix (@{thm [source] verimon_log.vrun_log}, theory
  @{theory Monitor_Exec_Proof.Log_Monitor_Online}), and an error on every log whose events of
  the formula's predicates denote no prefix (@{thm [source] verimon_log.vrun_filtered}).\<close>

theorem cli_run:
  assumes "cli_main prog args pf = NeedFile fn k1" "k1 ftext = NeedFile sn k2"
    and "k2 stext = Run msg conf cf z fin n L"
  obtains \<psi>0 S \<phi> where "parse_formula (Rep_bytes ftext) = Some \<psi>0"
    and "read_sig (Rep_bytes stext) = Inr S"
    and "conv_formula pf (c_rw conf) (input_formula conf \<psi>0) = Inr \<phi>"
    and "lsig_of S \<phi> = Inr L"
    and "vinit (c_index conf) (c_mw conf) (c_rw conf) (c_filter conf) L pf \<phi> = Inr (cf, z)"
    and "verimon_log (c_rw conf) L \<phi>"
  using cli_main_Run[OF assms] vinit_verimon_log by metis

subsection \<open>End-to-end correctness\<close>

text \<open>The verdicts that the specification prescribes for a prefix @{text \<pi>}, for the formula
  @{text \<phi>} with the types @{text f} that the type checker infers for it and the signature
  @{text L}: the time points @{text i} up to the progress on @{text \<pi>}, with their timestamps,
  and the tuples @{text v} over the free variables of @{text \<phi>} such that @{text \<phi>} holds at
  @{text i} under @{text v} on every well-typed trace that extends @{text \<pi>}. The type annotations
  matter: an aggregation's decides, for example, whether a sum is an integer or a floating point
  sum.\<close>

definition verdict_spec :: "lsig \<Rightarrow> tysym Formula.formula \<Rightarrow> (tysym \<Rightarrow> tysym) \<Rightarrow> Formula.prefix \<Rightarrow>
    (nat \<times> nat \<times> event_data tuple) set" where
  "verdict_spec L \<phi> f \<pi> = {(i, pts \<pi> ! i, v) | i v. i < pprogress \<phi> \<pi> \<and> wf_tuple (Formula.fv_list \<phi>) v \<and>
     (\<forall>\<sigma>. wty_trace (lsig_lookup L) \<sigma> \<longrightarrow> prefix_of \<pi> \<sigma> \<longrightarrow>
       Formula.sat \<sigma> Map.empty (val (Formula.nfv \<phi>) (Formula.fv_list \<phi>) v) i
         (Formula.formula.map_formula (convert_tysym \<circ> f) \<phi>))}"

text \<open>The verdicts of the monitor's specification (@{text monitor_\<phi>.Mt}, theory
  @{theory Monitor_Exec.Log_Monitor}) are those of @{const verdict_spec}.\<close>

context verimon_log
begin

interpretation monitor_\<phi>: future_bounded_mfodl "Formula.formula.map_formula (convert_tysym \<circ> check_subst) \<phi>"
  "map_sig (convert_tysym o check_subst) (lsig_tsig S)" "convert_tysym o check_subst o TAny"
  using future_bounded_\<phi> by (auto simp: future_bounded_mfodl_def future_bounded_mfodl_axioms_def wty_mfodl_def)

lemma Mt_verdict_spec:
  assumes "check (lsig_tsig S) TAny \<phi> = Inr f"
  shows "monitor_\<phi>.Mt \<pi> = verdict_spec S \<phi> f \<pi>"
proof -
  have cs: "check_subst = f"
    using check_check_subst assms by simp
  have pp: "pprogress (Formula.formula.map_formula g \<phi>) = pprogress \<phi>" for g :: "tysym \<Rightarrow> ty"
    by (simp add: pprogress_def fun_eq_iff)
  show ?thesis
    unfolding monitor_\<phi>.Mt_def
    unfolding monitor_\<phi>.M_def
    unfolding monitor_\<phi>.traces_def
    unfolding map_sig_lsig
    unfolding cs
    by (auto simp: verdict_spec_def pp)
qed

end

text \<open>The correctness of the whole monitor, in terms of the specifications of its parts: if the
  program starts the monitor on the contents of the formula file and of the signature file, then

  \<^item> the formula file is lexed into a token sequence that the grammar of MonPoly's formulas
    derives (@{const mfodl_Formula}), and @{text \<psi>0} is the formula it denotes;
  \<^item> the signature file is lexed into a token sequence that the grammar of signatures derives
    (@{const sig_lang}), and @{text S} is the signature it denotes;
  \<^item> @{text \<phi>} is the conversion of @{text \<psi>0} (negated with @{text "-negate"}), @{text L} the
    signature of the monitor, and @{text f} the types that the type checker infers for
    @{text \<phi>};
  \<^item> the run on a log reports an error exactly when the log's events of the formula's predicates
    and of the predicates the signature does not declare (all events with
    @{text "-nofilterrel"}, @{const keep_spec}) denote no prefix; and
  \<^item> on a log that denotes a prefix @{text \<pi>}, its verdicts are exactly those that
    @{const verdict_spec} prescribes for @{text \<pi>}.

  The verdicts are those of @{const vrun}: the outputs of @{const vfeed_chunk} on the chunks of
  the log, however it is cut into chunks, and of @{const vfinish} at its end, which the driver
  prints with @{const verdict_out}.\<close>

theorem verimon_correct:
  assumes run: "cli_main prog args pf = NeedFile fn k1" "k1 ftext = NeedFile sn k2"
    "k2 stext = Run msg conf cf z fin n L"
  obtains w \<psi> \<psi>0 ds S \<phi> f where
    "lex (Rep_bytes ftext) = Some w" "mfodl_Formula w \<psi>" "postprocess \<psi> = Some \<psi>0"
    and "sig_lang (Rep_bytes stext) ds" "decls_schema ds base_schema = Inr S"
    and "conv_formula pf (c_rw conf) (input_formula conf \<psi>0) = Inr \<phi>"
    and "lsig_of S \<phi> = Inr L"
    and "check (lsig_tsig L) TAny \<phi> = Inr f"
    and "\<And>ss. has_verror (vrun cf fin z ss) \<longleftrightarrow>
      log_prefix (keep_spec (c_filter conf) \<phi> L) (sf pf) L fin (concat (map Rep_bytes ss)) = None"
    and "\<And>ss \<pi>. log_prefix (\<lambda>_. True) (sf pf) L fin (concat (map Rep_bytes ss)) = Some \<pi> \<Longrightarrow>
      \<not> has_verror (vrun cf fin z ss) \<and>
      flatten_verdicts (vwiden \<phi> (vverdicts (vrun cf fin z ss))) = verdict_spec L \<phi> f \<pi>"
proof -
  obtain \<psi>0 S \<phi> f where P: "parse_formula (Rep_bytes ftext) = Some \<psi>0"
    and R: "read_sig (Rep_bytes stext) = Inr S"
    and C: "conv_formula pf (c_rw conf) (input_formula conf \<psi>0) = Inr \<phi>"
    and Ls: "lsig_of S \<phi> = Inr L"
    and ch: "check (lsig_tsig L) TAny \<phi> = Inr f"
    and init: "vinit (c_index conf) (c_mw conf) (c_rw conf) (c_filter conf) L pf \<phi> = Inr (cf, z)"
    using cli_main_Run[OF run] by metis
  obtain w \<psi> where W: "lex (Rep_bytes ftext) = Some w" "mfodl_Formula w \<psi>" "postprocess \<psi> = Some \<psi>0"
    using P unfolding parse_formula_Some_iff by blast
  obtain ds where D: "sig_lang (Rep_bytes stext) ds" "decls_schema ds base_schema = Inr S"
    using R unfolding read_sig_correct by blast
  interpret verimon_log "c_rw conf" L \<phi>
    using vinit_verimon_log[OF init] .
  have E: "has_verror (vrun cf fin z ss) \<longleftrightarrow>
      log_prefix (keep_spec (c_filter conf) \<phi> L) (sf pf) L fin (concat (map Rep_bytes ss)) = None" for ss
    using vrun_filtered(1)[OF init] by blast
  have V: "\<not> has_verror (vrun cf fin z ss) \<and>
      flatten_verdicts (vwiden \<phi> (vverdicts (vrun cf fin z ss))) = verdict_spec L \<phi> f \<pi>"
    if "log_prefix (\<lambda>_. True) (sf pf) L fin (concat (map Rep_bytes ss)) = Some \<pi>" for ss \<pi>
    using vrun_log[OF init that, unfolded Mt_verdict_spec[OF ch]] by blast
  show thesis
    using that[OF W D C Ls ch E V] .
qed

text \<open>The same online, as the driver runs the monitor: after the chunks @{text ss} read so far,

  \<^item> the outputs so far contain an error exactly when the bytes read so far, restricted to the
    events the monitor keeps, denote no prefix (@{const stream_prefix}; the last time point read
    is held back until the next begins);
  \<^item> if the bytes read so far denote a prefix @{text \<pi>}, the outputs so far contain no error, and
    their verdicts are exactly those of @{const verdict_spec} for @{text \<pi>};
  \<^item> the outputs of a further chunk, after which the bytes denote @{text \<pi>'}, contain no error,
    and their verdicts are exactly those of @{text \<pi>'} that are not those of @{text \<pi>}, so that
    every verdict is output once, as soon as the bytes that determine it have been read;
  \<^item> the outputs at the end of the log are those of the prefix that the whole log denotes, with
    the last time point @{text fin}, that are not those of @{text \<pi>}; and
  \<^item> a chunk, or the end of the log, after which the bytes no longer denote a prefix outputs an
    error.\<close>

theorem verimon_correct_online:
  assumes run: "cli_main prog args pf = NeedFile fn k1" "k1 ftext = NeedFile sn k2"
    "k2 stext = Run msg conf cf z fin n L"
  obtains w \<psi> \<psi>0 ds S \<phi> f where
    "lex (Rep_bytes ftext) = Some w" "mfodl_Formula w \<psi>" "postprocess \<psi> = Some \<psi>0"
    and "sig_lang (Rep_bytes stext) ds" "decls_schema ds base_schema = Inr S"
    and "conv_formula pf (c_rw conf) (input_formula conf \<psi>0) = Inr \<phi>"
    and "lsig_of S \<phi> = Inr L"
    and "check (lsig_tsig L) TAny \<phi> = Inr f"
    and "\<And>ss. has_verror (fst (vfeed_chunks cf ss z)) \<longleftrightarrow>
      stream_prefix (keep_spec (c_filter conf) \<phi> L) (sf pf) L (concat (map Rep_bytes ss)) = None"
    and "\<And>ss \<pi>. stream_prefix (\<lambda>_. True) (sf pf) L (concat (map Rep_bytes ss)) = Some \<pi> \<Longrightarrow>
      \<not> has_verror (fst (vfeed_chunks cf ss z)) \<and>
      flatten_verdicts (vwiden \<phi> (vverdicts (fst (vfeed_chunks cf ss z)))) = verdict_spec L \<phi> f \<pi>"
    and "\<And>ss c \<pi> \<pi>'. stream_prefix (\<lambda>_. True) (sf pf) L (concat (map Rep_bytes ss)) = Some \<pi> \<Longrightarrow>
      stream_prefix (\<lambda>_. True) (sf pf) L (concat (map Rep_bytes ss) @ Rep_bytes c) = Some \<pi>' \<Longrightarrow>
      \<pi> \<le> \<pi>' \<and> \<not> has_verror (fst (vfeed_chunk cf c (snd (vfeed_chunks cf ss z)))) \<and>
      flatten_verdicts (vwiden \<phi> (vverdicts (fst (vfeed_chunk cf c (snd (vfeed_chunks cf ss z)))))) =
        verdict_spec L \<phi> f \<pi>' - verdict_spec L \<phi> f \<pi>"
    and "\<And>ss \<pi> \<pi>'. stream_prefix (\<lambda>_. True) (sf pf) L (concat (map Rep_bytes ss)) = Some \<pi> \<Longrightarrow>
      log_prefix (\<lambda>_. True) (sf pf) L fin (concat (map Rep_bytes ss)) = Some \<pi>' \<Longrightarrow>
      \<not> has_verror (vfinish cf fin (snd (vfeed_chunks cf ss z))) \<and>
      flatten_verdicts (vwiden \<phi> (vverdicts (vfinish cf fin (snd (vfeed_chunks cf ss z))))) =
        verdict_spec L \<phi> f \<pi>' - verdict_spec L \<phi> f \<pi>"
    and "\<And>ss c. stream_prefix (keep_spec (c_filter conf) \<phi> L) (sf pf) L (concat (map Rep_bytes ss)) \<noteq> None \<Longrightarrow>
      stream_prefix (keep_spec (c_filter conf) \<phi> L) (sf pf) L (concat (map Rep_bytes ss) @ Rep_bytes c) = None \<Longrightarrow>
      has_verror (fst (vfeed_chunk cf c (snd (vfeed_chunks cf ss z))))"
    and "\<And>ss. stream_prefix (keep_spec (c_filter conf) \<phi> L) (sf pf) L (concat (map Rep_bytes ss)) \<noteq> None \<Longrightarrow>
      log_prefix (keep_spec (c_filter conf) \<phi> L) (sf pf) L fin (concat (map Rep_bytes ss)) = None \<Longrightarrow>
      has_verror (vfinish cf fin (snd (vfeed_chunks cf ss z)))"
proof -
  obtain \<psi>0 S \<phi> f where P: "parse_formula (Rep_bytes ftext) = Some \<psi>0"
    and R: "read_sig (Rep_bytes stext) = Inr S"
    and C: "conv_formula pf (c_rw conf) (input_formula conf \<psi>0) = Inr \<phi>"
    and Ls: "lsig_of S \<phi> = Inr L"
    and ch: "check (lsig_tsig L) TAny \<phi> = Inr f"
    and init: "vinit (c_index conf) (c_mw conf) (c_rw conf) (c_filter conf) L pf \<phi> = Inr (cf, z)"
    using cli_main_Run[OF run] by metis
  obtain w \<psi> where W: "lex (Rep_bytes ftext) = Some w" "mfodl_Formula w \<psi>" "postprocess \<psi> = Some \<psi>0"
    using P unfolding parse_formula_Some_iff by blast
  obtain ds where D: "sig_lang (Rep_bytes stext) ds" "decls_schema ds base_schema = Inr S"
    using R unfolding read_sig_correct by blast
  interpret verimon_log "c_rw conf" L \<phi>
    using vinit_verimon_log[OF init] .
  note M = Mt_verdict_spec[OF ch]
  note wf0 = wf_vstate_vinit[OF init]
  obtain ust0 where init': "vinit (c_index conf) (c_mw conf) (c_rw conf) (c_filter conf) L pf \<phi> = Inr (cf, (einit, ust0, 0))"
    using wf0 unfolding wf_vstate_def by blast
  have p0: "stream_prefix (\<lambda>_. True) (sf pf) L [] = Some pnil"
    by (simp add: stream_prefix_def prefix_of_items_Nil)
  have E: "has_verror (fst (vfeed_chunks cf ss z)) \<longleftrightarrow>
      stream_prefix (keep_spec (c_filter conf) \<phi> L) (sf pf) L (concat (map Rep_bytes ss)) = None" for ss
    using vfeed_chunks_online(1)[OF init, of ss] by (simp add: stream_prefix_def) (metis not_None_eq)
  have V: "\<not> has_verror (fst (vfeed_chunks cf ss z)) \<and>
      flatten_verdicts (vwiden \<phi> (vverdicts (fst (vfeed_chunks cf ss z)))) = verdict_spec L \<phi> f \<pi>"
    if p: "stream_prefix (\<lambda>_. True) (sf pf) L (concat (map Rep_bytes ss)) = Some \<pi>" for ss \<pi>
  proof -
    obtain outs z' where v: "vfeed_chunks cf ss z = (outs, z')"
      by (cases "vfeed_chunks cf ss z")
    have p': "stream_prefix (\<lambda>_. True) (sf pf) L ([] @ concat (map Rep_bytes ss)) = Some \<pi>"
      using p by simp
    note O = vfeed_chunks_online_log[OF wf0 v p0 p']
    show ?thesis
      using O(1,4)[unfolded Mt_pnil[OF init'], unfolded M] by (simp add: v)
  qed
  have wfss: "wf_vstate (c_index conf) (c_mw conf) (c_filter conf) pf cf (concat (map Rep_bytes ss))
      (pmap_\<Gamma> (\<lambda>D. D \<inter> {e. keep_spec (c_filter conf) \<phi> L (Rep_string8 (fst e))}) \<pi>)
      (snd (vfeed_chunks cf ss z))"
    if p: "stream_prefix (\<lambda>_. True) (sf pf) L (concat (map Rep_bytes ss)) = Some \<pi>" for ss \<pi>
  proof -
    obtain outs z' where v: "vfeed_chunks cf ss z = (outs, z')"
      by (cases "vfeed_chunks cf ss z")
    have p': "stream_prefix (\<lambda>_. True) (sf pf) L ([] @ concat (map Rep_bytes ss)) = Some \<pi>"
      using p by simp
    show ?thesis
      using vfeed_chunks_online_log(3)[OF wf0 v p0 p'] by (simp add: v)
  qed
  have Ch: "\<pi> \<le> \<pi>' \<and> \<not> has_verror (fst (vfeed_chunk cf c (snd (vfeed_chunks cf ss z)))) \<and>
      flatten_verdicts (vwiden \<phi> (vverdicts (fst (vfeed_chunk cf c (snd (vfeed_chunks cf ss z)))))) =
        verdict_spec L \<phi> f \<pi>' - verdict_spec L \<phi> f \<pi>"
    if p: "stream_prefix (\<lambda>_. True) (sf pf) L (concat (map Rep_bytes ss)) = Some \<pi>"
      and p': "stream_prefix (\<lambda>_. True) (sf pf) L (concat (map Rep_bytes ss) @ Rep_bytes c) = Some \<pi>'"
    for ss c \<pi> \<pi>'
  proof -
    obtain outs z' where s: "vfeed_chunk cf c (snd (vfeed_chunks cf ss z)) = (outs, z')"
      by (cases "vfeed_chunk cf c (snd (vfeed_chunks cf ss z))")
    note O = vfeed_chunk_online_log[OF wfss[OF p] s p p']
    show ?thesis
      using O(1,2,4)[unfolded M] by (simp add: s)
  qed
  have Fi: "\<not> has_verror (vfinish cf fin (snd (vfeed_chunks cf ss z))) \<and>
      flatten_verdicts (vwiden \<phi> (vverdicts (vfinish cf fin (snd (vfeed_chunks cf ss z))))) =
        verdict_spec L \<phi> f \<pi>' - verdict_spec L \<phi> f \<pi>"
    if p: "stream_prefix (\<lambda>_. True) (sf pf) L (concat (map Rep_bytes ss)) = Some \<pi>"
      and p': "log_prefix (\<lambda>_. True) (sf pf) L fin (concat (map Rep_bytes ss)) = Some \<pi>'"
    for ss \<pi> \<pi>'
    using vfinish_online_log[OF wfss[OF p] p p', unfolded M] by simp
  have wfk: "\<exists>\<pi>. wf_vstate (c_index conf) (c_mw conf) (c_filter conf) pf cf (concat (map Rep_bytes ss)) \<pi>
      (snd (vfeed_chunks cf ss z))"
    if p: "stream_prefix (keep_spec (c_filter conf) \<phi> L) (sf pf) L (concat (map Rep_bytes ss)) \<noteq> None" for ss
  proof -
    obtain \<pi> where p': "stream_prefix (keep_spec (c_filter conf) \<phi> L) (sf pf) L ([] @ concat (map Rep_bytes ss)) = Some \<pi>"
      using p by auto
    obtain outs z' where v: "vfeed_chunks cf ss z = (outs, z')"
      by (cases "vfeed_chunks cf ss z")
    show ?thesis
      using vfeed_chunks_online_step[OF wf0 v p'] by (auto simp: v)
  qed
  have ChE: "has_verror (fst (vfeed_chunk cf c (snd (vfeed_chunks cf ss z))))"
    if p: "stream_prefix (keep_spec (c_filter conf) \<phi> L) (sf pf) L (concat (map Rep_bytes ss)) \<noteq> None"
      and p': "stream_prefix (keep_spec (c_filter conf) \<phi> L) (sf pf) L (concat (map Rep_bytes ss) @ Rep_bytes c) = None"
    for ss c
  proof -
    obtain \<pi> where wf: "wf_vstate (c_index conf) (c_mw conf) (c_filter conf) pf cf (concat (map Rep_bytes ss)) \<pi>
        (snd (vfeed_chunks cf ss z))"
      using wfk[OF p] by blast
    obtain outs z' where s: "vfeed_chunk cf c (snd (vfeed_chunks cf ss z)) = (outs, z')"
      by (cases "vfeed_chunk cf c (snd (vfeed_chunks cf ss z))")
    show ?thesis
      using vfeed_chunk_online(1)[OF wf s p'] by (simp add: s)
  qed
  have FiE: "has_verror (vfinish cf fin (snd (vfeed_chunks cf ss z)))"
    if p: "stream_prefix (keep_spec (c_filter conf) \<phi> L) (sf pf) L (concat (map Rep_bytes ss)) \<noteq> None"
      and p': "log_prefix (keep_spec (c_filter conf) \<phi> L) (sf pf) L fin (concat (map Rep_bytes ss)) = None"
    for ss
    using wfk[OF p] vfinish_online(1)[OF _ p'] by blast
  show thesis
    using that[OF W D C Ls ch E V Ch Fi ChE FiE] .
qed

(*<*)
end
(*>*)
