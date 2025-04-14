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

lemma wty_trm_st: "E \<turnstile> tm :: ty \<Longrightarrow>  E \<turnstile> st tm :: ty"
  by (induction tm ty rule: wty_trm.induct)
    (auto 0 3 simp: st_def ty_of_eval_trm ty_of_plus ty_of_minus ty_of_mult ty_of_div ty_of_mod elim: wty_trm.cases intro!: wty_trm.intros intro: ty_of_uminus)

inductive_cases wty_formula_PredE[elim!]: "S, E \<turnstile> Formula.Pred p tms"
inductive_cases wty_formula_NegE[elim!]: "S, E \<turnstile> Formula.Neg \<phi>"
inductive_cases wty_formula_AndE[elim!]: "S, E \<turnstile> Formula.And \<phi>1 \<phi>2"
inductive_cases wty_formula_OrE[elim!]: "S, E \<turnstile> Formula.Or \<phi>1 \<phi>2"
inductive_cases wty_formula_LetE[elim!]: "S, E \<turnstile> Formula.Let p \<phi>1 \<phi>2"
inductive_cases wty_formula_AggE[elim!]: "S, E \<turnstile> Formula.Agg y \<omega> tys f \<phi>"

lemma wty_simplify_terms: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> simplify_terms \<phi>"
proof (induction S E \<phi> rule: wty_formula.induct)
  case (Pred S p tms tys E)
  then show ?case sorry
next
  case (Let S E' \<phi> p E \<psi>)
  then show ?case
    by (auto simp del: fun_upd_apply simp: simplify_terms_nfv intro!: wty_formula.Let)
next
  case (LetPast S p \<phi> E' E \<psi>)
  then show ?case
    by (auto simp del: fun_upd_apply simp: simplify_terms_nfv intro!: wty_formula.LetPast)
next
  case (Eq E x t y S)
  then show ?case
    by (auto intro!: wty_formula.Eq wty_trm_st)
next
  case (Less E x t y S)
  then show ?case 
    by (auto intro!: wty_formula.Less wty_trm_st)
next
  case (LessEq E x t y S)
  then show ?case
    by (auto intro!: wty_formula.LessEq wty_trm_st)
next
  case (Neg S E \<phi>)
  then show ?case
    by (auto intro!: wty_formula.Neg)
next
  case (Or S E \<phi> \<psi>)
  then show ?case
    by (auto intro!: wty_formula.Or)
next
  case (And S E \<phi> \<psi>)
  then show ?case 
    by (auto intro!: wty_formula.And)
next
  case (Ands \<phi>s S E)
  then show ?case
    by (auto intro!: wty_formula.Ands)
next
  case (Exists S t E \<phi>)
  then show ?case
    by (auto intro!: wty_formula.Exists)
next
  case (Agg E y agg_type t tys f S \<phi> d)
  then show ?case
    by (auto intro!: wty_formula.Agg)
next
  case (Prev S E \<phi> \<I>)
  then show ?case 
    by (auto intro!: wty_formula.Prev)
next
  case (Next S E \<phi> \<I>)
  then show ?case
    by (auto intro!: wty_formula.Next)
next
  case (Since S E \<phi> \<psi> \<I>)
  then show ?case
    by (auto intro!: wty_formula.Since)
next
  case (Until S E \<phi> \<psi> \<I>)
  then show ?case
    by (auto intro!: wty_formula.Until)
next
  case (Trigger S E \<phi> \<psi> \<I>)
  then show ?case
    by (auto intro!: wty_formula.Trigger)
next
  case (Release S E \<phi> \<psi> \<I>)
  then show ?case
    by (auto intro!: wty_formula.Release)
next
  case (MatchP S E r I)
  then show ?case
    by (auto simp: regex.pred_map comp_def intro!: wty_formula.MatchP elim: regex.pred_mono_strong)
next
  case (MatchF S E r I)
  then show ?case
    by (auto simp: regex.pred_map comp_def intro!: wty_formula.MatchF elim: regex.pred_mono_strong)
next
  case (TP E t S)
  then show ?case
    by (auto intro!: wty_formula.TP wty_formula_TPD wty_trm_st)
next
  case (TS E t S)
  then show ?case
    by (auto intro!: wty_formula.TS wty_formula_TSD wty_trm_st)
qed

lemma wty_push_negation: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> push_negation \<phi>"
proof (induction \<phi> arbitrary: S E rule: push_negation.induct)
  case (1 \<phi> \<psi>)
  then show ?case
    by (auto intro!: wty_formula.Or wty_formula.Neg)
next
  case (2 \<phi> \<psi>)
  then show ?case
    by (auto intro!: wty_formula.And wty_formula.Neg)
next
  case (3 p \<phi> \<psi>)
  then show ?case
    by (force simp: push_negation_nfv intro!: wty_formula.Let)
next
  case (4 p \<phi> \<psi>)
  then show ?case sorry
next
  case ("5_2" v va vb)
  then show ?case sorry
next
  case ("5_3" v va vb)
  then show ?case sorry
next
  case ("5_5" v va)
  then show ?case sorry
next
  case ("5_6" v va)
  then show ?case sorry
next
  case ("5_7" v)
  then show ?case sorry
next
  case ("5_8" v)
  then show ?case sorry
next
  case ("5_9" v va)
  then show ?case sorry
next
  case ("5_10" v va vb vc vd)
  then show ?case sorry
next
  case ("5_11" v va)
  then show ?case sorry
next
  case ("5_12" v va)
  then show ?case sorry
next
  case ("5_13" v va vb)
  then show ?case sorry
next
  case ("5_14" v va vb)
  then show ?case sorry
next
  case ("5_15" v va vb)
  then show ?case sorry
next
  case ("5_16" v va vb)
  then show ?case sorry
next
  case ("5_17" v va)
  then show ?case sorry
next
  case ("5_18" v va)
  then show ?case sorry
next
  case ("5_19" v)
  then show ?case sorry
next
  case ("5_20" v)
  then show ?case sorry
next
  case (6 \<phi> \<psi>)
  then show ?case sorry
next
  case (7 \<phi> \<psi>)
  then show ?case sorry
next
  case (8 l)
  then show ?case sorry
next
  case (9 t \<phi>)
  then show ?case sorry
next
  case (10 y \<omega> tys f \<phi>)
  then show ?case by (auto intro!: wty_formula.Agg)
next
  case (11 I \<phi>)
  then show ?case sorry
next
  case (12 I \<phi>)
  then show ?case sorry
next
  case (13 \<phi> I \<psi>)
  then show ?case sorry
next
  case (14 \<phi> I \<psi>)
  then show ?case sorry
next
  case (15 I r)
  then show ?case sorry
next
  case (16 I r)
  then show ?case sorry
qed auto

lemma wty_elim_double_negation: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> elim_double_negation \<phi>"
  sorry

lemma wty_normalize: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> normalize \<phi>"
  unfolding normalize_def using wty_push_negation wty_simplify_terms wty_elim_double_negation
  by auto

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
  subgoal using prepare_Inr
    by (cases "prepare_verimon rw sig \<phi>")
      (simp_all add: prepare_verimon_def monitorable_formula_code Let_def split: sum.splits if_splits)
  done

end

context verimon begin
thm mono_monitor sound_monitor complete_monitor sliceable_M
end
end