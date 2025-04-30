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
inductive_cases wty_formula_EqE[elim!]: "S, E \<turnstile> Formula.Eq t1 t2"
inductive_cases wty_formula_LessE[elim!]: "S, E \<turnstile> Formula.Less t1 t2"
inductive_cases wty_formula_LessEqE[elim!]: "S, E \<turnstile> Formula.LessEq t1 t2"
inductive_cases wty_formula_LetE[elim!]: "S, E \<turnstile> Formula.Let p \<phi>1 \<phi>2"
inductive_cases wty_formula_LetPastE[elim!]: "S, E \<turnstile> Formula.LetPast p \<phi>1 \<phi>2"
inductive_cases wty_formula_NegE[elim!]: "S, E \<turnstile> Formula.Neg \<phi>"
inductive_cases wty_formula_OrE[elim!]: "S, E \<turnstile> Formula.Or \<phi>1 \<phi>2"
inductive_cases wty_formula_AndE[elim!]: "S, E \<turnstile> Formula.And \<phi>1 \<phi>2"
inductive_cases wty_formula_AndsE[elim!]: "S, E \<turnstile> Formula.Ands \<phi>"
inductive_cases wty_formula_ExistsE[elim!]: "S, E \<turnstile> Formula.Exists t \<phi>"
inductive_cases wty_formula_AggE[elim!]: "S, E \<turnstile> Formula.Agg y \<omega> tys f \<phi>"
inductive_cases wty_formula_PrevE[elim!]: "S, E \<turnstile> Formula.Prev I \<phi>"
inductive_cases wty_formula_NextE[elim!]: "S, E \<turnstile> Formula.Next I \<phi>"
inductive_cases wty_formula_SinceE[elim!]: "S, E \<turnstile> Formula.Since \<phi>1 I \<phi>2"
inductive_cases wty_formula_UntilE[elim!]: "S, E \<turnstile> Formula.Until \<phi>1 I \<phi>2"
inductive_cases wty_formula_TriggerE[elim!]: "S, E \<turnstile> Formula.Trigger \<phi>1 I \<phi>2"
inductive_cases wty_formula_RelaseE[elim!]: "S, E \<turnstile> Formula.Release \<phi>1 I \<phi>2"
inductive_cases wty_formula_MatchFE[elim!]: "S, E \<turnstile> Formula.MatchF I \<phi>"
inductive_cases wty_formula_MatchPE[elim!]: "S, E \<turnstile> Formula.MatchP I \<phi>"
inductive_cases wty_formula_TSE[elim!]: "S, E \<turnstile> Formula.TS t"
inductive_cases wty_formula_TPE[elim!]: "S, E \<turnstile> Formula.TP t"

lemma wty_simplify_terms: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> simplify_terms \<phi>"
proof (induction S E \<phi> rule: wty_formula.induct)
  case (Pred S p tms tys E)
  then show ?case
    by (auto intro!: wty_formula.Pred simp: list.rel_map wty_trm_st elim!: list.rel_mono_strong)
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
qed (*TODO: Change to "(auto intro!: wty_formula.intros)" and remove trivial cases*)

lemma wty_push_negation: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> push_negation \<phi>"
proof (induction \<phi> arbitrary: S E rule: push_negation.induct)
  case (3 p \<phi> \<psi>)
  then show ?case
    by (auto simp: push_negation_nfv intro!: wty_formula.Let)
next
  case (4 p \<phi> \<psi>)
  then show ?case
    by (auto simp: push_negation_nfv intro!: wty_formula.LetPast)
next
  case ("5_2" v va vb)
  then show ?case
    by (fastforce intro!: wty_formula.Let wty_formula.Neg)
next
  case ("5_3" v va vb)
  then show ?case
    by (fastforce intro!: wty_formula.Neg wty_formula.LetPast)
next
  case (15 I r)
  then show ?case 
    by (fastforce simp: regex.pred_map intro!: wty_formula.MatchP elim: regex.pred_mono_strong)
next
  case (16 I r)
  then show ?case
    by (fastforce simp: regex.pred_map intro!: wty_formula.MatchF elim: regex.pred_mono_strong)
qed (auto intro!: wty_formula.intros)

lemma wty_elim_double_negation: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> elim_double_negation \<phi>"
proof (induction \<phi> arbitrary: S E rule: elim_double_negation.induct)
  case (2 p \<phi> \<psi>)
  then show ?case
    by (auto simp: elim_double_negation_nfv intro!: wty_formula.Let)
next
  case (3 p \<phi> \<psi>)
  then show ?case
    by (auto simp: elim_double_negation_nfv intro!: wty_formula.LetPast)
next
  case ("4_2" v va vb)
  then show ?case
    by (fastforce intro!: wty_formula.Let wty_formula.Neg)
next
  case ("4_3" v va vb)
  then show ?case
    by (fastforce intro!: wty_formula.LetPast wty_formula.Neg)
next
  case (14 I r)
  then show ?case
    by (fastforce simp: regex.pred_map intro!: wty_formula.MatchP elim: regex.pred_mono_strong)
next
  case (15 I r)
  then show ?case
    by (fastforce simp: regex.pred_map intro!: wty_formula.MatchF elim: regex.pred_mono_strong)
qed (auto intro!: wty_formula.intros)

lemma wty_normalize: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> normalize \<phi>"
  unfolding normalize_def using wty_push_negation wty_simplify_terms wty_elim_double_negation
  by auto

lemma wty_trm_shiftTI: "E \<turnstile> t :: T \<Longrightarrow> (\<lambda>i. if i < n then E i else if i = n then k else E (i - 1)) \<turnstile> shiftTI n t :: T"
  by (induct t T rule: wty_trm.induct) (auto intro!: wty_trm.intros)

lemma wty_formula_shiftI_r: 
  "S, E \<turnstile> project \<alpha> \<Longrightarrow> S, (\<lambda>i. if i < n then E i else if i = n then k else E (i - 1)) \<turnstile> project (shiftI_r n \<alpha>)"
proof (induction \<alpha> arbitrary: n E S)
  case (Exists T \<alpha>)
  have "(\<lambda>i. if i < Suc n then case i of 0 \<Rightarrow> T | Suc x \<Rightarrow> E x else if i = Suc n then k else case i - 1 of 0 \<Rightarrow> T | Suc x \<Rightarrow> E x) =
        case_nat T (\<lambda>i. if i < n then E i else if i = n then k else E (i - 1))"
    by (auto simp: fun_eq_iff split: nat.splits)
  with Exists(2) Exists(1)[of S "case_nat T E" "Suc n"] show ?case
    by (auto intro!: wty_formula.Exists)
next
  case (Agg y \<omega> tys f \<alpha>)
  have "(\<lambda>i. if i < n + length tys then agg_env E tys i else if i = n + length tys then k else agg_env E tys (i - 1)) =
    agg_env (\<lambda>i. if i < n then E i else if i = n then k else E (i - 1)) tys"
    by (auto simp: fun_eq_iff simp: agg_env_def)
  with Agg(2) Agg(1)[of S "agg_env E tys" "n + length tys"] show ?case
    by (auto intro!: wty_formula.Agg dest!: wty_trm_shiftTI[of "agg_env E tys" f _ "n + length tys" k])
next
  case (MatchF I r)
  then show ?case
    by (auto intro!: wty_formula.MatchF simp: regex.pred_map elim!: regex.pred_mono_strong)
next
  case (MatchP I r)
  then show ?case
    by (auto intro!: wty_formula.MatchP simp: regex.pred_map elim!: regex.pred_mono_strong)
qed (auto 0 4 simp: list.rel_map once_def eventually_def historically_def always_def
    elim!: list.rel_mono_strong intro: wty_formula.intros wty_trm_shiftTI)

lemma wty_rewrite: "S, E \<turnstile> project \<phi> \<Longrightarrow> S, E \<turnstile> project (rewrite \<phi> t)"
proof (induction \<phi> t arbitrary: E rule: rewrite.induct)
  case (2 \<alpha> \<beta> I \<gamma> t)
  then show ?case by (fastforce simp: once_def eventually_def intro!: wty_formula.And wty_formula.Release wty_formula.Since wty_formula.Until)
next
  case (3 \<alpha> \<beta> I \<gamma> t)
  then show ?case  by (fastforce simp: eventually_def intro!: wty_formula.And wty_formula.Trigger wty_formula.Until)
next
  case (4 \<alpha> k \<beta> t)
  have "(\<lambda>i. if i = 0 then k else E (i - 1)) = case_nat k E"
    by (auto simp: fun_eq_iff split: nat.splits)
  with 4(2-4) show ?case
    using wty_formula_shiftI_r[of S E \<alpha> 0 k]
    by (auto intro!: wty_formula.Exists wty_formula.And 4(1))
next
  case (6 \<alpha> \<beta> I \<gamma> t)
  then show ?case(* And (Since) *)
  proof (cases "bounded I")
    case T1:True
    then show ?thesis
    proof (cases "prop_cond \<alpha> \<beta>")
      case T2:True
      with 6(1,3,10) show ?thesis
        by (auto simp: T1 eventually_def intro!: wty_formula.intros 6(2))
    next
      case F2:False
      then show ?thesis
      proof(cases "prop_cond \<alpha> \<gamma>")
        case T3:True
        with 6(4,5,10) show ?thesis
          by (auto simp: T1 F2 eventually_def intro!: wty_formula.intros 6(6))
      next
        case F3:False
        then show ?thesis
          using F2 6 wty_formula.intros by auto
      qed
    qed
  next
    case F1:False
    then show ?thesis
      using 6 wty_formula.intros by auto
  qed
next
  case (7 \<alpha> \<beta> I \<gamma> t)
  then show ?case(* And (Until) *)
    sorry
next
  case (14 \<alpha> \<gamma> I \<beta> t)
  then show ?case(* Since (And) *)
    sorry
next
  case (15 \<alpha> \<gamma> I \<beta> t)
  then show ?case(* Until (And) *)
    sorry
next
  case (34 I r t)
  then show ?case by (force simp: regex.pred_map intro!: wty_formula.MatchF elim: regex.pred_mono_strong)
next
  case (35 I r t)
  then show ?case by (force simp: regex.pred_map intro!: wty_formula.MatchP elim: regex.pred_mono_strong)
qed (auto simp: once_def eventually_def always_def historically_def intro!: wty_formula.intros)

lemma wty_project_embed: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> project (embed \<phi>)"
  proof (induction S E \<phi> rule: wty_formula.induct)
    case (Let S E' \<phi> p E \<psi>)
    then show ?case by (auto simp: nfv_project project_embed intro!: wty_formula.Let)
  next
    case (LetPast S p \<phi> E' E \<psi>)
    then show ?case by (auto simp: nfv_project project_embed intro!: wty_formula.LetPast)
  next
    case (MatchP S E r I)
    then show ?case by (auto simp: regex.pred_map comp_def intro!: wty_formula.MatchP elim: regex.pred_mono_strong)
  next
    case (MatchF S E r I)
    then show ?case by (auto simp: regex.pred_map comp_def intro!: wty_formula.MatchF elim: regex.pred_mono_strong)
  qed (auto intro!: wty_formula.intros)

lemma wty_rrewrite: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> rrewrite \<phi>"
  unfolding rrewrite_def using wty_rewrite wty_project_embed by auto

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
    subgoal
      apply (frule check_sound_proven[OF _ wf])
      apply (auto simp add: check_check_subst wty_result_fX_def wf_f_comp simp flip: comp_assoc
        intro!: exI[of _ "convert_tysym"] wty_normalize wty_rrewrite dest: spec[of _ "convert_tysym \<circ> check_subst"])
      done
    done
  subgoal using prepare_Inr
    by (cases "prepare_verimon rw sig \<phi>")
      (simp_all add: prepare_verimon_def monitorable_formula_code Let_def split: sum.splits if_splits)
  done

lemma wf_f_check_subst[simp]: "wf_f (TCst \<circ> (convert_tysym o check_subst))"
  using wf_f_comp[OF wf_f_TCst_convert_tysym check_sound_proven[OF check_check_subst wf, unfolded wty_result_fX_def, THEN conjunct1]]
  by (auto simp: comp_assoc)

lemma verimon_wf_mstate_minit: "prepare_verimon rw sig \<phi> = Inr \<psi> \<Longrightarrow>
  wf_mstate (map_sig (convert_tysym o check_subst) sig) (convert_tysym o check_subst o TAny) \<psi> pnil R (minit \<psi>)"
  unfolding prepare_verimon_def using check_sound_proven[OF check_check_subst wf, unfolded wty_result_fX_def, THEN conjunct2, THEN spec, of "convert_tysym o check_subst"]
  by (auto split: sum.splits if_splits simp: Let_def mmonitorable_def type_check_def check_check_subst
    simp flip: monitorable_formula_code
    intro!: wf_mstate_minit wty_rrewrite wty_normalize dest!: spec[of _ "convert_tysym"])
 

end

context verimon begin
thm mono_monitor sound_monitor complete_monitor sliceable_M
find_theorems M
thm M_def
thm mstep_mverdicts
thm wf_mstate_minit_safe
find_theorems maux.minit_verimon
end
end