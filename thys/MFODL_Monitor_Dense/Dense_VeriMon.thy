(*<*)
theory Dense_VeriMon
  imports Dense_Push "MFODL_Monitor_Devel.VeriMon" Dense_Maux
begin
(*>*)

section \<open>VeriMon's preparation of the formula, and the monitor on it\<close>

text \<open>
  The monitor runs on the formula that VeriMon prepares (@{const prepare_verimon}): the input
  formula is type checked and, if it is not monitorable and rewriting is requested, normalized
  and rewritten until it becomes monitorable.  Optionally (@{text mw}), the prepared formula is
  converted into multi-way joins.  Then @{const dense_prep} binds frozen predicates with
  @{const Formula.Let} where it can (@{theory MFODL_Monitor_Dense.Dense_Frz}), moves existential
  quantifiers into the windows they commute with (@{theory MFODL_Monitor_Dense.Dense_Push}), and
  binds the right operand of a release so that it is evaluated once
  (@{theory MFODL_Monitor_Dense.Dense_Share}).  The kernel of
  @{theory MFODL_Monitor_Devel.Monitor_Impl}, with the window structures of
  @{theory MFODL_Monitor_Dense.Dense_Maux}, is started on the result.

  Every rewrite preserves the free variables but not necessarily the order in which
  @{const Formula.fv_list} lists them, and the kernel's verdicts are tuples over that list.  So
  the initialization returns the list of the verdicts' columns along with the state, and the
  theorem @{text udminit_verimon_mverdicts} below states that the verdicts, with their columns
  reordered to those of the input formula, are the ones the specification of the input formula
  prescribes.
\<close>

subsection \<open>Reordering the verdicts' columns\<close>

text \<open>Two formulas with the same number and set of free variables, the same satisfaction
  relation and the same progress have the same verdicts, up to the order of their columns.\<close>

context
  fixes \<phi> \<psi> :: "ty Formula.formula" and S :: sig and E :: tyenv
  assumes fb: "future_bounded_mfodl \<phi> S E" "future_bounded_mfodl \<psi> S E"
    and fv: "Formula.fv \<psi> = Formula.fv \<phi>" and nfv: "Formula.nfv \<psi> = Formula.nfv \<phi>"
    and sat: "\<And>\<sigma> v i. Formula.sat \<sigma> Map.empty v i \<psi> = Formula.sat \<sigma> Map.empty v i \<phi>"
    and pp: "pprogress \<psi> = pprogress \<phi>"
begin

interpretation p: future_bounded_mfodl \<phi> S E
  by (rule fb(1))

interpretation q: future_bounded_mfodl \<psi> S E
  by (rule fb(2))

lemma M_perm: "q.M \<pi> = (\<lambda>(i, v). (i, restrict (Formula.fv_list \<psi>) (Formula.fv_list \<phi>) v)) ` p.M \<pi>"
proof -
  let ?ds = "Formula.fv_list \<psi>"
  let ?cs = "Formula.fv_list \<phi>"
  have set_cs: "set ?ds = set ?cs" "set ?cs = set ?ds"
    by (simp_all add: fv)
  have restrict_back: "restrict ?ds ?cs (restrict ?cs ?ds v) = v"
    if "wf_tuple ?ds v" for v :: "event_data list"
    using that by (subst restrict_restrict) (simp_all add: fv restrict_idle)
  have val_ds: "val (Formula.nfv \<phi>) ?ds (restrict ?ds ?cs v) = val (Formula.nfv \<phi>) ?cs v"
    for v :: "event_data list"
    by (rule val_restrict_perm) (rule set_cs)
  have val_cs: "val (Formula.nfv \<phi>) ?cs (restrict ?cs ?ds v) = val (Formula.nfv \<phi>) ?ds v"
    for v :: "event_data list"
    by (rule val_restrict_perm) (rule set_cs)
  have to_\<phi>: "wf_tuple ?ds v \<and> (i, restrict ?cs ?ds v) \<in> p.M \<pi>" if "(i, v) \<in> q.M \<pi>" for i v
    using that unfolding q.M_def p.M_def
    by (simp add: sat nfv pp val_cs)
  have to_\<psi>: "(i, restrict ?ds ?cs v) \<in> q.M \<pi>" if "(i, v) \<in> p.M \<pi>" for i v
    using that unfolding q.M_def p.M_def
    by (simp add: sat nfv pp val_ds)
  show ?thesis
  proof (rule set_eqI, safe)
    fix i v
    assume "(i, v) \<in> q.M \<pi>"
    with to_\<phi>[OF this] show "(i, v) \<in> (\<lambda>(i, v). (i, restrict ?ds ?cs v)) ` p.M \<pi>"
      by (auto simp: restrict_back intro!: image_eqI[where x = "(i, restrict ?cs ?ds v)"])
  qed (rule to_\<psi>)
qed

lemma Mt_perm: "q.Mt \<pi> = (\<lambda>(i, t, v). (i, t, restrict (Formula.fv_list \<psi>) (Formula.fv_list \<phi>) v)) ` p.Mt \<pi>"
  unfolding q.Mt_def p.Mt_def M_perm image_image
  by (simp add: split_beta)

end

lemma flatten_verdicts_map_image:
  "flatten_verdicts (map (\<lambda>(i, t, X). (i, t, f ` X)) Vs) = (\<lambda>(i, t, v). (i, t, f v)) ` flatten_verdicts Vs"
  by (auto simp: flatten_verdicts_def image_UN image_image split_beta)

text \<open>Changing the formula's type annotations changes none of its column lists.\<close>

lemma fvi_list_map_formula[simp]:
  "Formula.fvi_list b (Formula.formula.map_formula g \<phi>) = Formula.fvi_list b \<phi>"
proof (induction b \<phi> rule: Formula.fvi_list.induct)
  case (20 b I r)
  then show ?case
    by (induction r) auto
next
  case (21 b I r)
  then show ?case
    by (induction r) auto
qed (auto simp: fold_map comp_def cong: fold_cong)

subsection \<open>The monitor's state and its initialization\<close>

type_synonym udmstate = dmstate

text \<open>The multiway conversion expands a release into an until over several copies of its right
  operand; @{const share_opt} binds that operand with @{const Formula.Let} first, so that the copies
  are all occurrences of one predicate.\<close>

definition prep_mw :: "bool \<Rightarrow> ty Formula.formula \<Rightarrow> ty Formula.formula" where
  "prep_mw mw \<psi> = dense_prep (if mw then convert_multiway (share_opt \<psi>) else \<psi>)"

definition udminit_verimon where
  "udminit_verimon mw rw sig \<phi> =
     map_sum id (\<lambda>\<psi>. let \<chi> = prep_mw mw \<psi> in (Formula.fv_list \<chi>, dminit_safe \<chi> :: udmstate))
       (prepare_verimon rw sig \<phi>)"

lemma verimon_spec_share_opt: "verimon_spec \<phi> S E \<Longrightarrow> verimon_spec (share_opt \<phi>) S E"
  by (auto simp: verimon_spec_def verimon_spec_axioms_def wty_mfodl_def wty_share_opt
    mmonitorable_share_opt)

lemma verimon_spec_dense_prep: "verimon_spec \<phi> S E \<Longrightarrow> verimon_spec (dense_prep \<phi>) S E"
  by (auto simp: verimon_spec_def verimon_spec_axioms_def wty_mfodl_def wty_dense_prep
    mmonitorable_dense_prep)

context verimon_prepare
begin

definition "\<psi>_mw mw = prep_mw mw \<psi>"

lemma udminit_verimon_\<psi>_mw:
  "udminit_verimon mw rw sig \<phi> = Inr (Formula.fv_list (\<psi>_mw mw), dminit_safe (\<psi>_mw mw))"
  by (simp add: udminit_verimon_def prepare_\<psi> \<psi>_mw_def Let_def)

lemma verimon_spec_\<psi>_mw:
  "verimon_spec (\<psi>_mw mw) (map_sig (convert_tysym o check_subst) sig) (convert_tysym o check_subst o TAny)"
  by (cases mw) (simp_all add: \<psi>_mw_def prep_mw_def verimon_spec_\<psi> verimon_spec_convert_multiway
    verimon_spec_share_opt verimon_spec_dense_prep)

lemma safe_share_opt_\<psi>: "safe_formula (share_opt \<psi>)"
  using verimon_spec.monitorable[OF verimon_spec_share_opt[OF verimon_spec_\<psi>]]
  by (simp add: mmonitorable_def)

lemma fvi_\<psi>_mw: "Formula.fvi b (\<psi>_mw mw) = Formula.fvi b \<phi>"
  by (simp add: \<psi>_mw_def prep_mw_def fv_convert_multiway fvi_\<psi>)

lemma nfv_\<psi>_mw: "Formula.nfv (\<psi>_mw mw) = Formula.nfv \<phi>"
  by (simp add: \<psi>_mw_def prep_mw_def nfv_convert_multiway nfv_\<psi>)

lemma sat_\<psi>_mw: "Formula.sat \<sigma> V v i (\<psi>_mw mw) = Formula.sat \<sigma> V v i \<psi>"
  by (simp add: \<psi>_mw_def prep_mw_def sat_convert_multiway[OF safe_share_opt_\<psi>])

lemma pprogress_\<psi>_mw: "pprogress (\<psi>_mw mw) \<pi> = pprogress \<psi> \<pi>"
  by (simp add: \<psi>_mw_def prep_mw_def pprogress_def progress_convert_multiway[OF safe_share_opt_\<psi>])

context
  fixes mw :: bool
begin

interpretation monitor_\<phi>: future_bounded_mfodl "Formula.formula.map_formula (convert_tysym \<circ> check_subst) \<phi>"
  "map_sig (convert_tysym o check_subst) sig" "convert_tysym o check_subst o TAny"
  using future_bounded_\<phi> by (auto simp: future_bounded_mfodl_def future_bounded_mfodl_axioms_def wty_mfodl_def)

interpretation verimon_mw: verimon "\<psi>_mw mw" "map_sig (convert_tysym o check_subst) sig"
  "convert_tysym o check_subst o TAny"
  valid_dsaux init_dsaux add_new_ts_dsaux join_dsaux add_new_table_dsaux result_dsaux
  valid_muaux_dq "init_muaux_dq :: _ \<Rightarrow> muaux_dq" add_new_muaux_dq length_muaux_dq eval_muaux_dq
  valid_mmtaux init_mmtaux update_mmtaux result_mmtaux
  by (intro verimon.intro verimon_spec_\<psi>_mw) unfold_locales

text \<open>The verdicts of the monitor started from the state @{const udminit_verimon} builds, with
  their columns reordered to those of the input formula, are the verdicts the specification of
  the input formula prescribes.\<close>

theorem udminit_verimon_mverdicts:
  assumes init: "udminit_verimon mw rw sig \<phi> = Inr (cs, ust)"
    and wty: "wty_prefix (map_sig (convert_tysym o check_subst) sig) \<pi>"
  shows "flatten_verdicts (map (\<lambda>(i, t, X). (i, t, restrict
      (Formula.fv_list (Formula.formula.map_formula (convert_tysym \<circ> check_subst) \<phi>)) cs ` X))
      (dmsteps_stateless \<pi> ust)) = monitor_\<phi>.Mt \<pi>"
proof -
  have cs: "cs = Formula.fv_list (\<psi>_mw mw)" and ust: "ust = dminit_safe (\<psi>_mw mw)"
    using init by (simp_all add: udminit_verimon_\<psi>_mw)
  have "flatten_verdicts (dmsteps_stateless \<pi> ust) = verimon_mw.Mt \<pi>"
    using verimon_mw.monitor_mverdicts[OF wty] by (simp add: ust dense_maux.monitor_def)
  moreover have "monitor_\<phi>.Mt \<pi> = (\<lambda>(i, t, v). (i, t, restrict
      (Formula.fv_list (Formula.formula.map_formula (convert_tysym \<circ> check_subst) \<phi>))
      (Formula.fv_list (\<psi>_mw mw)) v)) ` verimon_mw.Mt \<pi>"
    by (rule Mt_perm) (auto simp: fvi_\<psi>_mw nfv_\<psi>_mw sat_\<psi>_mw sat_\<psi> pprogress_\<psi>_mw pprogress_\<psi> fun_eq_iff
      intro: monitor_\<phi>.future_bounded_mfodl_axioms verimon_mw.future_bounded_mfodl_axioms)
  ultimately show ?thesis
    by (simp add: flatten_verdicts_map_image cs)
qed
end

end

(*<*)
end
(*>*)
