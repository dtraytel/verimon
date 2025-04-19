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

lemma wty_simplify_terms: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> simplify_terms \<phi>"
proof (induction S E \<phi> rule: wty_formula.induct)
  case (Pred S p tms tys E)
  then show ?case
    sorry
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
  case ("5_7" v)
  then show ?case
    by (auto intro!: wty_formula.Neg)
next
  case ("5_8" v)
  then show ?case
    by (auto intro!: wty_formula.Neg wty_formula.Ands)
next
  case ("5_9" v va)
  then show ?case
    by (auto intro!: wty_formula.Neg wty_formula.Exists)
next
  case ("5_10" v va vb vc vd)
  then show ?case
    by (auto intro!: wty_formula.Neg wty_formula.Agg)
next
  case ("5_11" v va)
  then show ?case
    by (auto intro!: wty_formula.Neg wty_formula.Prev)
next
  case ("5_12" v va)
  then show ?case
    by (auto intro!: wty_formula.Neg wty_formula.Next)
next
  case ("5_13" v va vb)
  then show ?case
    by (auto intro!: wty_formula.Neg wty_formula.Since)
next
  case ("5_14" v va vb)
  then show ?case
    by (auto intro!: wty_formula.Neg wty_formula.Until)
next
  case ("5_17" v va)
  then show ?case
    by (auto intro!: wty_formula.Neg wty_formula.MatchF)
next
  case ("5_18" v va)
  then show ?case 
    by (auto intro!: wty_formula.Neg wty_formula.MatchP)
next
  case (6 \<phi> \<psi>)
  then show ?case 
    by (auto intro!: wty_formula.Or)
next
  case (7 \<phi> \<psi>)
  then show ?case
    by (auto intro!: wty_formula.And)
next
  case (8 l)
  then show ?case
    by (auto intro!: wty_formula.Ands)
next
  case (9 t \<phi>)
  then show ?case
    by (auto intro!: wty_formula.Exists)
next
  case (10 y \<omega> tys f \<phi>)
  then show ?case
    by (auto intro!: wty_formula.Agg)
next
  case (11 I \<phi>)
  then show ?case
    by (auto intro!: wty_formula.Prev)
next
  case (12 I \<phi>)
  then show ?case
    by (auto intro!: wty_formula.Next)
next
  case (13 \<phi> I \<psi>)
  then show ?case
    by (auto intro!: wty_formula.Since)
next
  case (14 \<phi> I \<psi>)
  then show ?case
    by (auto intro!: wty_formula.Until)
next
  case (15 I r)
  then show ?case 
    by (force simp: regex.pred_map comp_def intro!: wty_formula.MatchP elim: regex.pred_mono_strong)
next
  case (16 I r)
  then show ?case
    by (force simp: regex.pred_map comp_def intro!: wty_formula.MatchF elim: regex.pred_mono_strong)
qed auto

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
  case ("4_1" v va)
  then show ?case by auto
next
  case ("4_2" v va vb)
  then show ?case by (fastforce intro!: wty_formula.Let wty_formula.Neg)
next
  case ("4_3" v va vb)
  then show ?case by (fastforce intro!: wty_formula.LetPast wty_formula.Neg)
next
  case ("4_7" v va)
  then show ?case
    by (auto intro!: wty_formula.Or wty_formula.Neg)
next
  case ("4_8" v va)
  then show ?case
    by (auto intro!: wty_formula.And wty_formula.Neg)
next
  case ("4_9" v)
  then show ?case
    by (auto intro!: wty_formula.Ands wty_formula.Neg)
next
  case ("4_10" v va)
  then show ?case
    by (auto intro!: wty_formula.Exists wty_formula.Neg)
next
  case ("4_11" v va vb vc vd)
  then show ?case
    by (auto intro!: wty_formula.Agg wty_formula.Neg)
next
  case ("4_12" v va)
  then show ?case
    by (auto intro!: wty_formula.Prev wty_formula.Neg)
next
  case ("4_13" v va)
  then show ?case
    by (auto intro!: wty_formula.Next wty_formula.Neg)
next
  case ("4_14" v va vb)
  then show ?case
    by (auto intro!: wty_formula.Since wty_formula.Neg)
next
  case ("4_15" v va vb)
  then show ?case
    by (auto intro!: wty_formula.Until wty_formula.Neg)
next
  case ("4_18" v va)
  then show ?case
    by (auto intro!: wty_formula.MatchF wty_formula.Neg)
next
  case ("4_19" v va)
  then show ?case
    by (auto intro!: wty_formula.MatchP wty_formula.Neg)
next
  case (5 \<phi> \<psi>)
  then show ?case
    by (auto intro!: wty_formula.Or)
next
  case (6 \<phi> \<psi>)
  then show ?case
    by (auto intro!: wty_formula.And)
next
  case (7 l)
  then show ?case
    by (auto intro!: wty_formula.Ands)
next
  case (8 t \<phi>)
  then show ?case
    by (auto intro!: wty_formula.Exists)
next
  case (9 y \<omega> tys f \<phi>)
  then show ?case
    by (auto intro!: wty_formula.Agg)
next
  case (10 I \<phi>)
  then show ?case
    by (auto intro!: wty_formula.Prev)
next
  case (11 I \<phi>)
  then show ?case
    by (auto intro!: wty_formula.Next)
next
  case (12 \<phi> I \<psi>)
  then show ?case
    by (auto intro!: wty_formula.Since)
next
  case (13 \<phi> I \<psi>)
  then show ?case
    by (auto intro!: wty_formula.Until)
next
  case (14 I r)
  then show ?case
    by (force simp: regex.pred_map comp_def intro!: wty_formula.MatchP elim: regex.pred_mono_strong)
next
  case (15 I r)
  then show ?case
    by (force simp: regex.pred_map comp_def intro!: wty_formula.MatchF elim: regex.pred_mono_strong)
qed auto (*TODO: Change to "(auto intro!: wty_formula.intros)" and remove trivial cases*)

lemma wty_normalize: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> normalize \<phi>"
  unfolding normalize_def using wty_push_negation wty_simplify_terms wty_elim_double_negation
  by auto

lemma wty_rewrite: "S, E \<turnstile> (project \<phi>) \<Longrightarrow> S, E \<turnstile> project (rewrite \<phi> t)"
proof (induction \<phi> t rule: rewrite.induct)
  case (2 \<alpha> \<beta> I \<gamma> t)
  then show ?case by (fastforce simp: once_def eventually_def intro!: wty_formula.And wty_formula.Release wty_formula.Since wty_formula.Until)
next
  case (3 \<alpha> \<beta> I \<gamma> t)
  then show ?case by (fastforce simp: eventually_def intro!: wty_formula.And wty_formula.Trigger wty_formula.Until)
next
  case (4 \<alpha> k \<beta> t)
  then show ?case(* needing Shift_I_r 0 by (auto intro!: wty_formula.And wty_formula.Exists)*) sorry
next
  case (6 \<alpha> \<beta> I \<gamma> t)
  then show ?case(* by (auto simp: eventually_def intro!: wty_formula.And wty_formula.Since wty_formula.Until)*) sorry
next
  case (7 \<alpha> \<beta> I \<gamma> t)
  then show ?case(* by (auto simp: once_def intro!: wty_formula.And wty_formula.Until wty_formula.Since)*) sorry
next(*
  case (8 \<alpha> I \<beta> t)
  then show ?case by (auto simp: once_def eventually_def intro!: wty_formula.And wty_formula.Since wty_formula.Until)
next
  case (9 \<alpha> I \<beta> t)
  then show ?case by (auto simp: eventually_def once_def intro!: wty_formula.And wty_formula.Until wty_formula.Since)
next
  case (10 \<alpha> I \<beta> t)
  then show ?case by (auto simp: historically_def once_def eventually_def intro!: wty_formula.And wty_formula.Since wty_formula.Until wty_formula.Neg)
next
  case (11 \<alpha> I \<beta> t)
  then show ?case by (auto simp: always_def eventually_def once_def intro!: wty_formula.And wty_formula.Until wty_formula.Since wty_formula.Neg)
next*)
  case (14 \<alpha> \<gamma> I \<beta> t)
  then show ?case(* Since ( And)  by (auto simp: once_def eventually_def intro!: wty_formula.Since wty_formula.And wty_formula.Until)*) sorry
next
  case (15 \<alpha> \<gamma> I \<beta> t)
  then show ?case(* Until (And) fix_r? by (auto simp: eventually_def intro!: wty_formula.And wty_formula.Until)*) sorry
next
  case (23 k \<phi> t)
  then show ?case (*Exists case_nat*)  sorry
next
  case (24 y \<omega> b' f \<phi> t)
  then show ?case (*by (auto intro!: wty_formula.Agg agg_env)*) sorry
next(*
  case (30 I \<alpha> t)
  then show ?case by (auto simp: eventually_def intro!: wty_formula.Until)
next
  case (31 I \<alpha> t)
  then show ?case by (auto simp: once_def intro!: wty_formula.Since)
next
  case (32 I \<alpha> t)
  then show ?case by (auto simp: always_def eventually_def intro!: wty_formula.Neg wty_formula.Until)
next
  case (33 I \<alpha> t)
  then show ?case by (auto simp: historically_def once_def intro!: wty_formula.Neg wty_formula.Since)
next*)
  case (34 I r t)
  then show ?case by (force simp: regex.pred_map intro!: wty_formula.MatchF elim: regex.pred_mono_strong)
next
  case (35 I r t)
  then show ?case by (force simp: regex.pred_map intro!: wty_formula.MatchP elim: regex.pred_mono_strong)
qed (auto simp: once_def eventually_def always_def historically_def intro!: wty_formula.intros)

lemma wty_project_embed: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> (project (embed \<phi>))"
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