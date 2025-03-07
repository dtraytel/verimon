theory VeriMon
imports Correctness Rewriting
begin

context maux begin

definition "prepare_verimon rw sig \<phi> =
(case type_check sig \<phi> of Inl err \<Rightarrow> Inl err
| Inr \<phi> \<Rightarrow>
(if mmonitorable_exec \<phi> then Inr \<phi> else
(if rw then
let n\<phi> = normalize \<phi> in
if mmonitorable_exec n\<phi> then Inr n\<phi> else
let r\<phi> = rrewrite n\<phi> in
if mmonitorable_exec r\<phi> then Inr r\<phi> else Inl STR ''not monitorable''
else Inl STR ''not monitorable'')))"

definition "minit_verimon rw sig \<phi> = map_sum id minit (prepare_verimon rw sig \<phi>)"

end

lemma wty_normalize: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> normalize \<phi>"
  sorry

lemma "type_check (\<lambda>_. None) (Formula.Exists (TAny 0) (Formula.Eq (Formula.Var 0) (Formula.Var 0))) = XYZ"
  apply (simp add: type_check_def check_comparison_def clash_propagate_def new_type_symbol_def update_env_def)
  oops

locale actually_verimon = maux +
  fixes rw sig \<phi>
  assumes wf: "wf_formula \<phi>" 
  and prepare_Inr: "\<not> sum.isl (prepare_verimon rw sig \<phi>)"
begin

lemma check_Inr: "\<exists>f. check sig TAny \<phi> = Inr f"
  using prepare_Inr unfolding prepare_verimon_def type_check_def
  by (simp add: bind_def split: sum.splits if_splits)

definition "check_subst = (THE f. check sig TAny \<phi> = Inr f)"

lemma check_check_subst: "check sig TAny \<phi> = Inr check_subst"
  unfolding check_subst_def using check_Inr
  by auto

lemma wf_f_TCst_convert_tysym[simp]: "wf_f (TCst o convert_tysym)"
  unfolding wf_f_def
  by (auto simp: numeric_ty_def)

interpretation verimon: verimon "projr (prepare_verimon rw sig \<phi>)" "map_sig (convert_tysym o check_subst) sig" "convert_tysym o check_subst o TAny"
  apply standard
  subgoal using prepare_Inr
    apply (cases "prepare_verimon rw sig \<phi>")
     apply (simp_all add: prepare_verimon_def type_check_def Let_def bind_def split: sum.splits if_splits)
    subgoal
      apply (frule check_sound_proven[OF _ wf])
      apply (auto simp add: check_check_subst wty_result_fX_def wf_f_comp simp flip: comp_assoc
        intro!: exI[of _ "convert_tysym"] dest: spec[of _ "convert_tysym \<circ> check_subst"])
      done
    subgoal
      apply (frule check_sound_proven[OF _ wf])
      apply (auto simp add: check_check_subst wty_result_fX_def wf_f_comp simp flip: comp_assoc
        intro!: exI[of _ "convert_tysym"] wty_normalize dest: spec[of _ "convert_tysym \<circ> check_subst"])
      done
      
      sorry
    subgoal sorry
    done
  subgoal using prepare_Inr
    by (cases "prepare_verimon rw sig \<phi>")
      (simp_all add: prepare_verimon_def monitorable_formula_code Let_def split: sum.splits if_splits)
  done

end

context verimon begin
thm mono_monitor sound_monitor complete_monitor sliceable_M
end
end