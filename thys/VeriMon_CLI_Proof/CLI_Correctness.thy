(*<*)
theory CLI_Correctness
  imports "VeriMon_CLI.CLI" "Monitor_Exec_Proof.Log_Monitor_Online"
begin
(*>*)

section \<open>Correctness of the command-line monitor\<close>

subsection \<open>Starting the monitor\<close>

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

text \<open>A started monitor satisfies the assumptions of @{locale verimon_log}, whose theorems state its
  correctness on logs.\<close>

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

text \<open>The verdicts prescribed for a prefix @{text \<pi>}: up to the progress, the tuples under which
  @{text \<phi>}, with the inferred types @{text f}, holds on every well-typed extension of @{text \<pi>}.\<close>

definition verdict_spec :: "lsig \<Rightarrow> tysym Formula.formula \<Rightarrow> (tysym \<Rightarrow> tysym) \<Rightarrow> Formula.prefix \<Rightarrow>
    (nat \<times> nat \<times> event_data tuple) set" where
  "verdict_spec L \<phi> f \<pi> = {(i, pts \<pi> ! i, v) | i v. i < pprogress \<phi> \<pi> \<and> wf_tuple (Formula.fv_list \<phi>) v \<and>
     (\<forall>\<sigma>. wty_trace (lsig_lookup L) \<sigma> \<longrightarrow> prefix_of \<pi> \<sigma> \<longrightarrow>
       Formula.sat \<sigma> Map.empty (val (Formula.nfv \<phi>) (Formula.fv_list \<phi>) v) i
         (Formula.formula.map_formula (convert_tysym \<circ> f) \<phi>))}"

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

text \<open>If the program starts the monitor, the two files derive a formula and a signature. A log
  yields an error iff the events kept denote no prefix, and on a prefix exactly the verdicts of
  @{const verdict_spec}.\<close>

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

subsection \<open>Online correctness\<close>

text \<open>After each chunk, the outputs so far contain an error iff the bytes read denote no prefix, and
  each verdict is output once, as soon as the bytes that determine it have been read.\<close>

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
