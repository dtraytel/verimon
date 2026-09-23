(*<*)
theory Dense_VeriMon
  imports Dense_Unbox_Exec "MFODL_Monitor_Devel.VeriMon"
begin
(*>*)

section \<open>VeriMon's preparation of the formula for the verified dense monitor\<close>

text \<open>
  The verified dense monitor runs on the formula that VeriMon prepares (@{const prepare_verimon}):
  the input formula is type checked and, if it is not monitorable and rewriting is requested,
  normalized and rewritten until it becomes monitorable. Optionally (@{text mw}), the prepared
  formula is converted into multi-way joins before the dense state is built from it. The
  theorem @{text udminit_verimon_mverdicts} below states that the verdicts of the dense monitor
  started from this state are those of the input formula, provided the dense compiler covered
  the whole formula.
\<close>

definition udminit_verimon where
  "udminit_verimon mw rw sig \<phi> =
     map_sum id (\<lambda>\<psi>. udminit_safe (if mw then convert_multiway \<psi> else \<psi>)) (prepare_verimon rw sig \<phi>)"

context verimon_prepare
begin

definition "\<psi>_mw mw = (if mw then convert_multiway \<psi> else \<psi>)"

lemma udminit_verimon_\<psi>_mw: "udminit_verimon mw rw sig \<phi> = Inr (udminit_safe (\<psi>_mw mw))"
  by (simp add: udminit_verimon_def prepare_\<psi> \<psi>_mw_def)

lemma verimon_spec_\<psi>_mw:
  "verimon_spec (\<psi>_mw mw) (map_sig (convert_tysym o check_subst) sig) (convert_tysym o check_subst o TAny)"
  by (cases mw) (simp_all add: \<psi>_mw_def verimon_spec_\<psi> verimon_spec_convert_multiway)

lemma fvi_\<psi>_mw: "Formula.fvi b (\<psi>_mw mw) = Formula.fvi b \<phi>"
  by (simp add: \<psi>_mw_def fv_convert_multiway fvi_\<psi>)

lemma nfv_\<psi>_mw: "Formula.nfv (\<psi>_mw mw) = Formula.nfv \<phi>"
  by (simp add: \<psi>_mw_def nfv_convert_multiway nfv_\<psi>)

lemma sat_\<psi>_mw: "Formula.sat \<sigma> V v i (\<psi>_mw mw) = Formula.sat \<sigma> V v i \<psi>"
  by (simp add: \<psi>_mw_def sat_convert_multiway[OF safe_\<psi>])

lemma pprogress_\<psi>_mw: "pprogress (\<psi>_mw mw) \<pi> = pprogress \<psi> \<pi>"
  by (simp add: \<psi>_mw_def pprogress_def progress_convert_multiway[OF safe_\<psi>])

context
  fixes mw :: bool
begin

interpretation verimon_\<psi>: verimon_spec \<psi> "map_sig (convert_tysym o check_subst) sig"
  "convert_tysym o check_subst o TAny"
  using verimon_spec_\<psi> by (auto simp: verimon_spec_def verimon_spec_axioms_def wty_mfodl_def)

interpretation verimon_mw: verimon_spec "\<psi>_mw mw" "map_sig (convert_tysym o check_subst) sig"
  "convert_tysym o check_subst o TAny"
  using verimon_spec_\<psi>_mw by (auto simp: verimon_spec_def verimon_spec_axioms_def wty_mfodl_def)

interpretation monitor_\<phi>: future_bounded_mfodl "Formula.formula.map_formula (convert_tysym \<circ> check_subst) \<phi>"
  "map_sig (convert_tysym o check_subst) sig" "convert_tysym o check_subst o TAny"
  using future_bounded_\<phi> by (auto simp: future_bounded_mfodl_def future_bounded_mfodl_axioms_def wty_mfodl_def)

lemma Mt_\<psi>_mw: "verimon_mw.Mt \<pi> = verimon_\<psi>.Mt \<pi>"
  unfolding verimon_mw.Mt_def verimon_\<psi>.Mt_def verimon_mw.M_def verimon_\<psi>.M_def
  by (auto simp: sat_\<psi>_mw fvi_\<psi>_mw fvi_\<psi> nfv_\<psi>_mw nfv_\<psi> pprogress_\<psi>_mw)

text \<open>The verdicts of the dense monitor started from the state @{const udminit_verimon} builds
  are the verdicts the specification of the input formula prescribes.\<close>

theorem udminit_verimon_mverdicts:
  assumes init: "udminit_verimon mw rw sig \<phi> = Inr ust"
    and zf: "uvdfail_nodes (udmstate_m ust) = 0"
    and f: "pfinite \<pi>" and wty: "wty_prefix (map_sig (convert_tysym o check_subst) sig) \<pi>"
  shows "flatten_verdicts (map (\<lambda>(i, t, X).
      (i, t, dtabw (Formula.nfv \<phi>) (set_cols (Formula.fv \<phi>)) X))
      (dmonitor (Rep_udmstate ust) \<pi>)) = monitor_\<phi>.Mt \<pi>"
proof -
  have ust: "ust = udminit_safe (\<psi>_mw mw)"
    using init by (simp add: udminit_verimon_\<psi>_mw)
  have zf': "vdfail_nodes (dmstate_m (dof_state (Formula.nfv (\<psi>_mw mw))
      (set_cols (Formula.fv (\<psi>_mw mw))) (minit_safe (\<psi>_mw mw)))) = 0"
    using zf unfolding ust by (simp only: Rep_udminit_safe[symmetric] vdfail_nodes_Rep_udmstate)
  from verimon_mw.dmonitor_mverdicts_dof[OF zf' f wty, unfolded Mt_\<psi>_mw Mt_exchange] show ?thesis
    by (simp add: ust Rep_udminit_safe nfv_\<psi>_mw fvi_\<psi>_mw)
qed

end

end

(*<*)
end
(*>*)
