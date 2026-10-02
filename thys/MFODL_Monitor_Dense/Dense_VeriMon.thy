(*<*)
theory Dense_VeriMon
  imports Dense_Push "MFODL_Monitor_Devel.VeriMon"
begin
(*>*)

section \<open>VeriMon's preparation of the formula for the verified dense monitor\<close>

text \<open>
  The verified dense monitor runs on the formula that VeriMon prepares (@{const prepare_verimon}):
  the input formula is type checked and, if it is not monitorable and rewriting is requested,
  normalized and rewritten until it becomes monitorable. Optionally (@{text mw}), the prepared
  formula is converted into multi-way joins. The dense state is then built from it by
  @{const udminit_push}, which also binds frozen predicates with @{const Formula.Let} where it
  can (@{theory MFODL_Monitor_Dense.Dense_Frz}), moves existential quantifiers into the
  windows they commute with (@{theory MFODL_Monitor_Dense.Dense_Push}), and binds the right
  operand of a release so that it is evaluated once (@{theory MFODL_Monitor_Dense.Dense_Share}). The
  theorem @{text udminit_verimon_mverdicts} below states that the verdicts of the dense monitor
  started from this state are those of the input formula, provided the dense compiler covered
  the whole formula.

  The dense tuples are over the free variables in ascending order, whatever the formula they
  were compiled from: the rewrites change the order in which @{const Formula.fv_list} lists the
  free variables, and so the kernel's columns, but not the set.
\<close>

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

text \<open>The multiway conversion expands a release into an until over several copies of its right
  operand; @{const share_opt} binds that operand with @{const Formula.Let} first, so that the copies
  are all occurrences of one predicate.\<close>

definition udminit_verimon where
  "udminit_verimon mw rw sig \<phi> =
     map_sum id (\<lambda>\<psi>. udminit_push (if mw then convert_multiway (share_opt \<psi>) else \<psi>))
       (prepare_verimon rw sig \<phi>)"

lemma verimon_spec_share_opt: "verimon_spec \<phi> S E \<Longrightarrow> verimon_spec (share_opt \<phi>) S E"
  by (auto simp: verimon_spec_def verimon_spec_axioms_def wty_mfodl_def wty_share_opt
    mmonitorable_share_opt)

context verimon_prepare
begin

definition "\<psi>_mw mw = (if mw then convert_multiway (share_opt \<psi>) else \<psi>)"

lemma udminit_verimon_\<psi>_mw: "udminit_verimon mw rw sig \<phi> = Inr (udminit_push (\<psi>_mw mw))"
  by (simp add: udminit_verimon_def prepare_\<psi> \<psi>_mw_def)

lemma verimon_spec_\<psi>_mw:
  "verimon_spec (\<psi>_mw mw) (map_sig (convert_tysym o check_subst) sig) (convert_tysym o check_subst o TAny)"
  by (cases mw) (simp_all add: \<psi>_mw_def verimon_spec_\<psi> verimon_spec_convert_multiway
    verimon_spec_share_opt)

lemma safe_share_opt_\<psi>: "safe_formula (share_opt \<psi>)"
  using verimon_spec.monitorable[OF verimon_spec_share_opt[OF verimon_spec_\<psi>]]
  by (simp add: mmonitorable_def)

lemma fvi_\<psi>_mw: "Formula.fvi b (\<psi>_mw mw) = Formula.fvi b \<phi>"
  by (simp add: \<psi>_mw_def fv_convert_multiway fvi_\<psi>)

lemma nfv_\<psi>_mw: "Formula.nfv (\<psi>_mw mw) = Formula.nfv \<phi>"
  by (simp add: \<psi>_mw_def nfv_convert_multiway nfv_\<psi>)

lemma sat_\<psi>_mw: "Formula.sat \<sigma> V v i (\<psi>_mw mw) = Formula.sat \<sigma> V v i \<psi>"
  by (simp add: \<psi>_mw_def sat_convert_multiway[OF safe_share_opt_\<psi>])

lemma pprogress_\<psi>_mw: "pprogress (\<psi>_mw mw) \<pi> = pprogress \<psi> \<pi>"
  by (simp add: \<psi>_mw_def pprogress_def progress_convert_multiway[OF safe_share_opt_\<psi>])

context
  fixes mw :: bool
begin

interpretation verimon_mw: verimon_spec "\<psi>_mw mw" "map_sig (convert_tysym o check_subst) sig"
  "convert_tysym o check_subst o TAny"
  using verimon_spec_\<psi>_mw by (auto simp: verimon_spec_def verimon_spec_axioms_def wty_mfodl_def)

interpretation monitor_\<phi>: future_bounded_mfodl "Formula.formula.map_formula (convert_tysym \<circ> check_subst) \<phi>"
  "map_sig (convert_tysym o check_subst) sig" "convert_tysym o check_subst o TAny"
  using future_bounded_\<phi> by (auto simp: future_bounded_mfodl_def future_bounded_mfodl_axioms_def wty_mfodl_def)

text \<open>The verdicts of the dense monitor started from the state @{const udminit_verimon} builds
  are the verdicts the specification of the input formula prescribes.\<close>

theorem udminit_verimon_mverdicts:
  assumes init: "udminit_verimon mw rw sig \<phi> = Inr ust"
    and zf: "uvdfail_nodes (udmstate_m ust) = 0"
    and f: "pfinite \<pi>" and wty: "wty_prefix (map_sig (convert_tysym o check_subst) sig) \<pi>"
  shows "flatten_verdicts (map (\<lambda>(i, t, X).
      (i, t, dtabw (Formula.fv_list \<phi>) (dcols (Formula.fv_list \<phi>)) X))
      (dmonitor (Rep_udmstate ust) \<pi>)) = monitor_\<phi>.Mt \<pi>"
proof -
  let ?\<psi> = "\<psi>_mw mw"
  let ?\<chi> = "dense_prep ?\<psi>"
  have ust: "ust = udminit_push ?\<psi>"
    using init by (simp add: udminit_verimon_\<psi>_mw)
  have R: "Rep_udmstate ust = dof_state (Formula.nfv ?\<psi>) (Formula.fv_list ?\<chi>)
      (dcols (Formula.fv_list ?\<chi>)) (minit_safe ?\<chi>)"
    unfolding ust by (rule Rep_udminit_push[OF verimon_mw.monitorable])
  have zf': "vdfail_nodes (dmstate_m (dof_state (Formula.nfv ?\<psi>) (Formula.fv_list ?\<chi>)
      (dcols (Formula.fv_list ?\<chi>)) (minit_safe ?\<chi>))) = 0"
    using zf by (simp only: R[symmetric] vdfail_nodes_Rep_udmstate)
  have A: "flatten_verdicts (map (\<lambda>(i, t, X).
      (i, t, dtabw (Formula.fv_list ?\<psi>) (dcols (Formula.fv_list ?\<psi>)) X))
      (dmonitor (Rep_udmstate ust) \<pi>)) = verimon_mw.Mt \<pi>"
    using verimon_mw.dmonitor_mverdicts_push[OF zf' f wty] by (simp only: R)
  have Mt: "monitor_\<phi>.Mt \<pi> = (\<lambda>(i, t, v). (i, t, restrict
      (Formula.fv_list (Formula.formula.map_formula (convert_tysym \<circ> check_subst) \<phi>))
      (Formula.fv_list ?\<psi>) v)) ` verimon_mw.Mt \<pi>"
    by (rule Mt_perm) (auto simp: fvi_\<psi>_mw nfv_\<psi>_mw sat_\<psi>_mw sat_\<psi> pprogress_\<psi>_mw pprogress_\<psi> fun_eq_iff
      intro: monitor_\<phi>.future_bounded_mfodl_axioms verimon_mw.future_bounded_mfodl_axioms)
  have cs: "dcols (Formula.fv_list ?\<psi>) = dcols (Formula.fv_list \<phi>)"
    by (rule dcols_cong) (simp add: fvi_\<psi>_mw)
  have w: "dtabw (Formula.fv_list \<phi>) (dcols (Formula.fv_list \<phi>)) X =
      restrict (Formula.fv_list \<phi>) (Formula.fv_list ?\<psi>) ` dtabw (Formula.fv_list ?\<psi>) (dcols (Formula.fv_list \<phi>)) X"
    for X :: "event_data list set"
    by (simp add: dtabw_def image_image restrict_restrict fvi_\<psi>_mw)
  show ?thesis
    unfolding w flatten_verdicts_map_comp Mt using A by (simp add: cs)
qed

end

end

(*<*)
end
(*>*)
