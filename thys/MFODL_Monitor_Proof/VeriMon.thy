theory VeriMon
imports Correctness Progress_Rewriting "MFODL_Logic.Preparation"
begin

text \<open>The monitor side of locale @{locale verimon_prepare}, whose logic half is in theory
  Preparation: the progress of the prepared formula @{text \<psi>}, and its verdicts.  The two
  specification locales are interpreted again here, since an interpretation inside a locale block
  ends with the block.\<close>

context verimon_prepare
begin

interpretation verimon_\<psi>: verimon_spec \<psi> "map_sig (convert_tysym o check_subst) sig" "convert_tysym o check_subst o TAny"
  using verimon_spec_\<psi> by (auto simp: verimon_spec_def verimon_spec_axioms_def wty_mfodl_def)

interpretation monitor_\<phi>: future_bounded_mfodl "Formula.formula.map_formula (convert_tysym \<circ> check_subst) \<phi>"
  "map_sig (convert_tysym o check_subst) sig" "convert_tysym o check_subst o TAny"
  using future_bounded_\<phi> by (auto simp: future_bounded_mfodl_def future_bounded_mfodl_axioms_def wty_mfodl_def)

lemma pprogress_\<psi>: "pprogress \<psi> \<pi> = pprogress (Formula.formula.map_formula (convert_tysym \<circ> check_subst) \<phi>) \<pi>"
  using prepare_\<psi>[symmetric] unfolding pprogress_def unfolding prepare_verimon_def
  by (auto split: sum.splits if_splits simp: progress_normalize progress_dual_since progress_rrewrite Let_def type_check_def check_check_subst)

text \<open>The rewriting preserves the free variables, but not necessarily the order in which
  @{const Formula.fv_list} lists them: the kernel's verdicts on @{term \<psi>} are those of the
  specification of the input formula, with their columns reordered.\<close>

lemma M_exchange: "verimon_\<psi>.M \<pi> = (\<lambda>(i, v). (i, restrict (Formula.fv_list \<psi>)
  (Formula.fv_list (Formula.formula.map_formula (convert_tysym \<circ> check_subst) \<phi>)) v)) ` monitor_\<phi>.M \<pi>"
proof -
  let ?ds = "Formula.fv_list \<psi>"
  let ?cs = "Formula.fv_list (Formula.formula.map_formula (convert_tysym \<circ> check_subst) \<phi>)"
  have set_cs: "set ?ds = set ?cs" "set ?cs = set ?ds"
    by (simp_all add: fvi_\<psi>)
  have restrict_back: "restrict ?ds ?cs (restrict ?cs ?ds v) = v"
    if "wf_tuple ?ds v" for v :: "event_data list"
    using that by (subst restrict_restrict) (simp_all add: fvi_\<psi> restrict_idle)
  have val_ds: "val (Formula.nfv \<phi>) ?ds (restrict ?ds ?cs v) = val (Formula.nfv \<phi>) ?cs v"
    for v :: "event_data list"
    by (rule val_restrict_perm) (rule set_cs)
  have val_cs: "val (Formula.nfv \<phi>) ?cs (restrict ?cs ?ds v) = val (Formula.nfv \<phi>) ?ds v"
    for v :: "event_data list"
    by (rule val_restrict_perm) (rule set_cs)
  have to_\<phi>: "wf_tuple ?ds v \<and> (i, restrict ?cs ?ds v) \<in> monitor_\<phi>.M \<pi>"
    if "(i, v) \<in> verimon_\<psi>.M \<pi>" for i v
    using that unfolding verimon_\<psi>.M_def monitor_\<phi>.M_def
    by (simp add: sat_\<psi> nfv_\<psi> pprogress_\<psi> val_cs)
  have to_\<psi>: "(i, restrict ?ds ?cs v) \<in> verimon_\<psi>.M \<pi>" if "(i, v) \<in> monitor_\<phi>.M \<pi>" for i v
    using that unfolding verimon_\<psi>.M_def monitor_\<phi>.M_def
    by (simp add: sat_\<psi> nfv_\<psi> pprogress_\<psi> val_ds)
  show ?thesis
  proof (rule set_eqI, safe)
    fix i v
    assume "(i, v) \<in> verimon_\<psi>.M \<pi>"
    with to_\<phi>[OF this] show "(i, v) \<in> (\<lambda>(i, v). (i, restrict ?ds ?cs v)) ` monitor_\<phi>.M \<pi>"
      by (auto simp: restrict_back intro!: image_eqI[where x = "(i, restrict ?cs ?ds v)"])
  qed (rule to_\<psi>)
qed

lemma Mt_exchange: "verimon_\<psi>.Mt \<pi> = (\<lambda>(i, t, v). (i, t, restrict (Formula.fv_list \<psi>)
  (Formula.fv_list (Formula.formula.map_formula (convert_tysym \<circ> check_subst) \<phi>)) v)) ` monitor_\<phi>.Mt \<pi>"
  unfolding verimon_\<psi>.Mt_def monitor_\<phi>.Mt_def M_exchange image_image
  by (simp add: split_beta)

(* Correctness of specification of the monitor *)
lemmas mono_monitor = monitor_\<phi>.mono_monitor
lemmas sound_monitor = monitor_\<phi>.sound_monitor
lemmas complete_monitor = monitor_\<phi>.complete_monitor
lemmas sliceable_M = monitor_\<phi>.sliceable_M

end

text \<open>The kernel's monitor on the prepared formula.\<close>

locale verimon_rewrite = maux + verimon_prepare
begin

interpretation verimon_\<psi>: verimon \<psi> "map_sig (convert_tysym o check_subst) sig" "convert_tysym o check_subst o TAny"
  by (intro verimon.intro verimon_spec_\<psi>) unfold_locales

lemma verimon_wf_mstate_minit: "wf_mstate (map_sig (convert_tysym o check_subst) sig) (convert_tysym o check_subst o TAny) \<psi> pnil R (minit \<psi>)"
  using prepare_\<psi>[symmetric] safe_\<psi> unfolding prepare_verimon_def
  using check_sound_proven[OF check_check_subst wf, unfolded wty_result_fX_def, THEN conjunct2, THEN spec, of "convert_tysym o check_subst"]
  by (auto split: sum.splits if_splits simp: Let_def type_check_def check_check_subst
    intro!: wf_mstate_minit wty_rrewrite wty_dual_since wty_normalize dest!: spec[of _ "convert_tysym"])

(* Correctness of output of the monitor (verdicts of \phi is the output) *)
lemmas wf_mstate_minit = verimon_wf_mstate_minit
lemmas wf_mstate_mstep = wf_mstate_mstep
lemmas mstep_mverdicts = verimon_\<psi>.mstep_mverdicts[unfolded Mt_exchange]

end

end
