theory VeriMon
imports Correctness Rewriting
begin

lemma map_formula_release_safe_bounded[simp]: "Formula.formula.map_formula f (release_safe_bounded \<phi> I \<psi>) =
  release_safe_bounded (Formula.formula.map_formula f \<phi>) I (Formula.formula.map_formula f \<psi>)"
  by (auto simp: release_safe_bounded_def eventually_def Formula.TT_def always_safe_bounded_def once_def)

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

lemma normalize_fvi:
  "Formula.fvi b (normalize \<phi>) = Formula.fvi b \<phi>"
  unfolding normalize_def by (auto simp: elim_double_negation_fvi push_negation_fvi simplify_terms_fvi)

lemma normalize_nfv:
  "Formula.nfv (normalize \<phi>) = Formula.nfv \<phi>"
  unfolding normalize_def by (auto simp: elim_double_negation_nfv push_negation_nfv simplify_terms_nfv)

lemma rrewrite_fvi:
  "Formula.fvi b (rrewrite \<phi>) = Formula.fvi b \<phi>"
  unfolding rrewrite_def by (auto simp: rewrite_fv[symmetric] project_embed)

lemma rrewrite_nfv:
  "Formula.nfv (rrewrite \<phi>) = Formula.nfv \<phi>"
  unfolding Formula.nfv_def rrewrite_fvi ..

(* Elimination rules for well-typed formulas*)
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

(* Proofs that normalize preserves well-typedness*)

lemma wty_trm_st: "E \<turnstile> tm :: ty \<Longrightarrow>  E \<turnstile> st tm :: ty"
  by (induction tm ty rule: wty_trm.induct)
    (auto 0 3 simp: st_def ty_of_eval_trm ty_of_plus ty_of_minus ty_of_mult ty_of_div ty_of_mod elim: wty_trm.cases intro!: wty_trm.intros intro: ty_of_uminus)

lemma wty_simplify_terms: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> simplify_terms \<phi>"
proof (induction S E \<phi> rule: wty_formula.induct)
  case (Pred S p tms tys E)
  then show ?case
    by (auto simp: list.rel_map wty_trm_st intro!: wty_formula.Pred elim!: list.rel_mono_strong)
next
  case (Let S E' \<phi> p E \<psi>)
  then show ?case
    by (auto simp del: fun_upd_apply simp: simplify_terms_nfv intro!: wty_formula.Let)
next
  case (LetPast S p \<phi> E' E \<psi>)
  then show ?case
    by (auto simp del: fun_upd_apply simp: simplify_terms_nfv intro!: wty_formula.LetPast)
next
  case (MatchP S E r I)
  then show ?case
    by (auto simp: regex.pred_map comp_def intro!: wty_formula.MatchP elim: regex.pred_mono_strong)
next
  case (MatchF S E r I)
  then show ?case
    by (auto simp: regex.pred_map comp_def intro!: wty_formula.MatchF elim: regex.pred_mono_strong)
qed  (auto intro!: wty_formula.intros wty_trm_st)

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

(* Proofs that rrewrite preserves well-typedness*)

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
  then show ?case
    by (fastforce simp: once_def eventually_def intro!: wty_formula.And wty_formula.Release wty_formula.Since wty_formula.Until)
next
  case (3 \<alpha> \<beta> I \<gamma> t)
  then show ?case
    by (fastforce simp: eventually_def intro!: wty_formula.And wty_formula.Trigger wty_formula.Until)
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
        by (auto simp: T1 eventually_def intro!: wty_formula.And wty_formula.Since wty_formula.Until 6(2))
    next
      case F2:False
      then show ?thesis
      proof(cases "prop_cond \<alpha> \<gamma>")
        case T3:True
        with 6(4,5,10) show ?thesis
          by (auto simp: T1 F2 eventually_def intro!: wty_formula.And wty_formula.Since wty_formula.Until 6(6))
      next
        case F3:False
        with 6(7,8,9,10) show ?thesis
          by (auto simp: F2 intro!: wty_formula.And wty_formula.Since)
      qed
    qed
  next
    case F1:False
    with 6(7,8,9,10) show ?thesis
      by (auto intro!: wty_formula.And wty_formula.Since)
  qed
next
  case (7 \<alpha> \<beta> I \<gamma> t)
  then show ?case(* And (Until) *)
  proof (cases "bounded I")
    case T1:True
    then show ?thesis
    proof (cases "prop_cond \<alpha> \<beta>")
      case T2:True
      with 7(1,3,10) show ?thesis
        by (auto simp: T1 once_def
            intro!: wty_formula.And wty_formula.Until wty_formula.Since 7(2))
    next
      case F2:False
      then show ?thesis
      proof(cases "prop_cond \<alpha> \<gamma>")
        case T3:True
        with 7(4,5,10) show ?thesis
          by (auto simp: T1 F2 once_def
              intro!: wty_formula.And wty_formula.Until wty_formula.Since 7(6))
      next
        case F3:False
        with 7(7,8,9,10) show ?thesis
          by (auto simp: F2 intro!: wty_formula.And wty_formula.Until)
      qed
    qed
  next
    case F1:False
    with 7(7,8,9,10) show ?thesis
      by (auto intro!: wty_formula.And wty_formula.Until)
  qed
next
  case (14 \<alpha> \<gamma> I \<beta> t)
  then show ?case(* Since (And) *)
  proof (cases "prop_cond \<alpha> \<beta>")
    case T1:True
    then show ?thesis
    proof (cases t)
      case Same
      with 14(1,6,7) show ?thesis
        by (auto simp: eventually_def
            intro!: wty_formula.Since wty_formula.And wty_formula.Until 14(2,3))
    next
      case Swapped
      with 14(1,6,7) show ?thesis
        by (auto simp: once_def intro!: wty_formula.Since wty_formula.And 14(4,5))
    qed
   next
    case F1:False
    then show ?thesis
    proof (cases "prop_cond \<alpha> \<gamma>")
      case T2:True
      then show ?thesis
      proof (cases t)
        case Same
        with 14(1,6,7) show ?thesis
          by (auto simp: F1 eventually_def
              intro!: wty_formula.Since wty_formula.And wty_formula.Until 14(3))
      next
        case Swapped
        with 14(1,6,7) show ?thesis
          by (auto simp: F1 once_def intro!: wty_formula.Since wty_formula.And 14(5))
      qed
    next
      case F2:False
      then show ?thesis
      proof (cases t)
        case Same
        with 14(1,6,7) show ?thesis
          by (auto simp: eventually_def
              intro!: wty_formula.Since wty_formula.And wty_formula.Until 14(2,3))
      next
        case Swapped
        with 14(1,6,7) show ?thesis
          by (auto simp: once_def intro!: wty_formula.Since wty_formula.And 14(4,5))
      qed
    qed
  qed
next
  case (15 \<alpha> \<gamma> I \<beta> t)
  then show ?case(* Until (And) *)
  proof (cases "prop_cond \<alpha> \<beta>")
    case T1:True
    then show ?thesis
    proof (cases t)
      case Same
      with 15(1,6,7) show ?thesis
        by (auto simp: once_def
            intro!: wty_formula.Until wty_formula.And wty_formula.Since 15(2,3))
    next
      case Swapped
      with 15(1,6,7) show ?thesis
        by (auto simp: eventually_def intro!: wty_formula.Until wty_formula.And 15(4,5))
    qed
  next
    case F1:False
    then show ?thesis
    proof (cases "prop_cond \<alpha> \<gamma>")
      case T2:True
      then show ?thesis
      proof (cases t)
        case Same
        with 15(1,6,7) show ?thesis
          by (auto simp: once_def F1
              intro!: wty_formula.Until wty_formula.And wty_formula.Since 15(3))
      next
        case Swapped
        with 15(1,6,7) show ?thesis
          by (auto simp: eventually_def F1 intro!: wty_formula.Until wty_formula.And 15(5))
      qed
    next
      case F2:False
      with 15 show ?thesis
      proof (cases t)
        case Same
        with 15(1,6,7) show ?thesis
          by (auto simp: once_def
              intro!: wty_formula.Until wty_formula.And wty_formula.Since 15(2,3))
      next
        case Swapped
        with 15(1,6,7) show ?thesis
          by (auto simp: eventually_def intro!: wty_formula.Until wty_formula.And 15(4,5))
      qed
    qed
  qed
next
  case (34 I r t)
  then show ?case
    by (force simp: regex.pred_map intro!: wty_formula.MatchF elim: regex.pred_mono_strong)
next
  case (35 I r t)
  then show ?case
    by (force simp: regex.pred_map intro!: wty_formula.MatchP elim: regex.pred_mono_strong)
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

(* Proofs that if a normalized formula is future-boundedness, then so is the original formula *)
lemma safe_letpast_simplify_terms: "safe_letpast (p, n) (simplify_terms \<phi>) = safe_letpast (p, n) \<phi>"
  by (induct \<phi> arbitrary: p n rule: simplify_terms.induct)
    (auto simp: simplify_terms_nfv image_image regex.set_map)

lemma future_bounded_simplify_terms: "Safety.future_bounded (simplify_terms \<phi>) \<Longrightarrow> Safety.future_bounded \<phi>"
  by (induction \<phi> rule: simplify_terms.induct)
    (auto simp: simplify_terms_nfv list.pred_map regex.pred_map safe_letpast_simplify_terms elim: list.pred_mono_strong regex.pred_mono_strong)

lemma safe_letpast_push_negation: "safe_letpast (p, n) (push_negation \<phi>) = safe_letpast (p, n) \<phi>"
  by (induct \<phi> arbitrary: p n rule: push_negation.induct)
    (auto simp: push_negation_nfv image_image regex.set_map)

lemma future_bounded_push_negation: "Safety.future_bounded (push_negation \<phi>) \<Longrightarrow> Safety.future_bounded \<phi>"
  by (induct \<phi> rule: push_negation.induct)
    (auto simp: push_negation_nfv list.pred_map regex.pred_map safe_letpast_push_negation elim: list.pred_mono_strong regex.pred_mono_strong)

lemma safe_letpast_elim_double_negation: "safe_letpast (p, n) (elim_double_negation \<phi>) = safe_letpast (p, n) \<phi>"
  by (induct \<phi> arbitrary: p n rule: elim_double_negation.induct)
    (auto simp: elim_double_negation_nfv image_image regex.set_map)

lemma future_bounded_elim_double_negation: "Safety.future_bounded (elim_double_negation \<phi>) \<Longrightarrow> Safety.future_bounded \<phi>"
  by (induction \<phi> rule: elim_double_negation.induct)
    (auto simp: elim_double_negation_nfv list.pred_map regex.pred_map safe_letpast_elim_double_negation elim: list.pred_mono_strong regex.pred_mono_strong)

lemma future_bounded_normalize: "Safety.future_bounded (normalize \<phi>) \<Longrightarrow> Safety.future_bounded \<phi>"
  unfolding normalize_def using future_bounded_simplify_terms future_bounded_push_negation future_bounded_elim_double_negation by auto

(* Proofs that if a rewritten formula is future-boundedness, then so is the original formula *)
lemma future_bounded_historically[simp]: "Safety.future_bounded (historically I \<phi>) = Safety.future_bounded \<phi>"
  by (auto simp: historically_def)

lemma future_bounded_always[simp]: "Safety.future_bounded (always I \<phi>) = (bounded I \<and> Safety.future_bounded \<phi>)"
  by (auto simp: always_def)

lemma future_bounded_shiftI_r[simp]: "Safety.future_bounded (project (shiftI_r i \<phi>)) = Safety.future_bounded (project \<phi>)"
  by (induct \<phi> arbitrary: i)
   (auto simp: list.pred_map regex.pred_map elim: list.pred_mono_strong regex.pred_mono_strong)

lemma future_bounded_fix_r[simp]: "Safety.future_bounded (project (fix_r \<phi> t)) = Safety.future_bounded (project \<phi>)"
  by (induct \<phi> t rule: fix_r.induct) auto

lemma future_bounded_rewrite: "Safety.future_bounded (project (rewrite \<phi> t)) \<Longrightarrow> Safety.future_bounded (project \<phi>)"
proof (induct \<phi> t rule: rewrite.induct)
  case (3 \<alpha> \<beta> I \<gamma> t)
  from 3(1-4,7) 3(5)[OF _ refl] 3(6)[OF _ refl refl] show ?case
    by (cases "prop_cond \<alpha> \<beta>"; cases "prop_cond \<beta> \<alpha>"; cases "prop_cond \<gamma> \<alpha>")
      (auto simp: Let_def split: if_splits)
next
  case (14 \<alpha> \<gamma> I \<beta> t)
  from 14(1,7) 14(2-6)[OF refl] show ?case
    by (cases "prop_cond \<alpha> \<beta>"; cases "prop_cond \<gamma> \<beta>") (auto simp: Let_def split: if_splits)
qed (auto simp: list.pred_map regex.pred_map elim: list.pred_mono_strong regex.pred_mono_strong split: if_splits)

lemma future_bounded_project_embed: "Safety.future_bounded (project (embed \<phi>)) \<Longrightarrow> Safety.future_bounded \<phi>"
  by (auto simp: project_embed)

lemma future_bounded_rrewrite: "Safety.future_bounded (rrewrite \<phi>) \<Longrightarrow> Safety.future_bounded \<phi>"
  unfolding rrewrite_def using future_bounded_rewrite future_bounded_project_embed by auto

(* Proofs that rewriting does not change the progress of the monitor *)
lemma progress_map_formula[simp]: "progress \<sigma> P (Formula.formula.map_formula f \<phi>) j = progress \<sigma> P \<phi> j"
  by (induct \<phi> arbitrary: P j rule: progress_custom_induct)
    (auto simp: letpast_progress_def progress_regex_def regex.set_map image_image)

lemma progress_simplify_terms[simp]: "progress \<sigma> P (simplify_terms \<phi>) j = progress \<sigma> P \<phi> j"
  apply (induction \<phi> arbitrary: P j rule: simplify_terms.induct)
  apply (auto simp: simplify_terms_nfv letpast_progress_def progress_regex_def regex.set_map image_image)
    (* TODO: release_safe_bounded *)
  sorry

lemma progress_push_negation[simp]: "progress \<sigma> P (push_negation \<phi>) j = progress \<sigma> P \<phi> j"
  by (induction \<phi> arbitrary: P j rule: push_negation.induct)
    (auto simp: push_negation_nfv letpast_progress_def progress_regex_def regex.set_map image_image)

lemma progress_elim_double_negation[simp]: "progress \<sigma> P (elim_double_negation \<phi>) j = progress \<sigma> P \<phi> j"
  by (induction \<phi> arbitrary: P j rule: elim_double_negation.induct)
    (auto simp: elim_double_negation_nfv letpast_progress_def progress_regex_def regex.set_map image_image)

lemma progress_normalize[simp]: "progress \<sigma> P (normalize \<phi>) j = progress \<sigma> P \<phi> j"
  unfolding normalize_def by auto

lemma progress_shiftI_r[simp]: "progress \<sigma> P (project (shiftI_r i \<phi>)) j = progress \<sigma> P (project \<phi>) j"
  apply (induct \<phi> arbitrary: i P j)
   apply (auto simp: progress_regex_def regex.set_map image_image always_def eventually_def historically_def)
  (* TODO: release_safe_bounded *)
  sorry

lemma progress_fix_r[simp]: "progress \<sigma> P (project (fix_r \<phi> t)) j = progress \<sigma> P (project \<phi>) j"
proof (induct \<phi> t arbitrary: P j rule: fix_r.induct)
  case (1 l I r)
  then show ?case
    sorry
qed (auto simp: conj_commute)

(*
find_theorems progress "Suc _"
find_theorems memL "min _ _"
find_theorems memL 
find_theorems "\<not> memL _ 0"
find_theorems "min _ _" "Suc _" *)

definition "conterex = Formula.And (Formula.Pred (STR ''a'') [Formula.Var 0, Formula.Var 1])
  (Formula.Since (Formula.Or (Formula.Neg (Formula.Pred (STR ''b'') [Formula.Var 0])) (Formula.Pred (STR ''b'') [Formula.Var 1])) (interval 0 10) (Formula.Pred (STR ''c'') [Formula.Var 0, Formula.Var 1]))"
lemma "progress \<sigma> Map.empty conterex j = j"
  by (auto simp add: conterex_def)
thm prop_cond_def[of "Rewriting.Pred (STR ''a'') [Formula.Var 0]" "Rewriting.Neg (Rewriting.Pred (STR ''b'') [Formula.Var 0])"]
lemma "progress \<sigma> Map.empty (rrewrite conterex) j < j"
  using interval_bounds[of 0 10]
  apply (auto simp add: rrewrite_def prop_cond_def conterex_def eventually_def enat_0 min_less_iff_disj)
  apply (subst cInf_less_iff)
    apply (auto simp: enat_0 intro!: exI[of _ "j"]) []
   apply auto []
  apply auto
  find_theorems "Inf _ < _"
  sorry

lemma bounded_init_ivl[simp]: "bounded I \<Longrightarrow> bounded (init_ivl I)"
  by transfer auto

lemma "\<not> mmonitorable conterex"
  using interval_bounds[of 0 10, OF _ refl]
  by (auto simp: rrewrite_def prop_cond_def conterex_def eventually_def mmonitorable_def safe_assignment_def enat_0)

lemma "mmonitorable (rrewrite conterex)"
  using interval_bounds[of 0 10, OF _ refl]
  by (auto simp: rrewrite_def prop_cond_def conterex_def eventually_def mmonitorable_def safe_assignment_def enat_0)

lemma progress_rewrite[simp]: "progress \<sigma> P (project (rewrite \<phi> t)) j = progress \<sigma> P (project (fix_r \<phi> t)) j"
proof (induction \<phi> t arbitrary: P j rule: rewrite.induct)
  case (2 \<alpha> \<beta> I \<gamma> t)
  then show ?case
    apply simp
    sorry
next
  case (3 \<alpha> \<beta> I \<gamma> t)
  then show ?case
    sorry
next
  case (6 \<alpha> \<beta> I \<gamma> t)
  then show ?case
    apply simp
    sorry
next
  case (7 \<alpha> \<beta> I \<gamma> t)
  then show ?case
    sorry
next
  case (8 \<alpha> I \<beta> t)
  then show ?case
    apply (auto simp: once_def eventually_def)
    sorry
next
  case (9 \<alpha> I \<beta> t)
  then show ?case
    apply (auto simp: eventually_def)
    sorry
next
  case (10 \<alpha> I \<beta> t)
  then show ?case
    apply (auto simp: historically_def eventually_def)
    sorry
next
  case (11 \<alpha> I \<beta> t)
  then show ?case
    apply (auto simp: once_def always_def eventually_def)
    sorry
next
  case (12 \<alpha> I \<beta> t)
  from 12(1-4) 12(5)[OF _ refl] show ?case
    by (cases "prop_cond \<alpha> \<beta>") auto
next
  case (13 \<alpha> I \<beta> t) (* And \<alpha> (Next I \<beta>)) *)
  then show ?case
    sorry
next
  case (14 \<alpha> \<gamma> I \<beta> t) (* Since (And \<alpha> \<gamma>) I \<beta>) *)
  then show ?case
    sorry
next
  case (15 \<alpha> \<gamma> I \<beta> t) (* Until (And \<alpha> \<gamma>) I \<beta>) *)
  then show ?case
    sorry
next
  case (27 \<phi> I \<psi> t) (* release_safe_bounded *)
  then show ?case sorry
qed (auto simp: conj_commute once_def always_def eventually_def historically_def
    progress_regex_def regex.set_map image_image)

lemma progress_rrewrite[simp]: "progress \<sigma> P (rrewrite \<phi> ) j = progress \<sigma> P \<phi> j"
  by (auto simp: rrewrite_def project_embed)

locale actually_verimon = maux +
  fixes rw sig \<phi>
  assumes wf: "wf_formula \<phi>" 
  and prepare_Inr: "\<not> sum.isl (prepare_verimon rw sig \<phi>)"
begin

lemma check_Inr: "\<exists>f. check sig TAny \<phi> = Inr f"
  using prepare_Inr unfolding prepare_verimon_def type_check_def
  by (simp add: bind_def split: sum.splits if_splits)

definition "check_subst = (THE f. check sig TAny \<phi> = Inr f)"
definition "\<psi> = (THE \<psi>. prepare_verimon rw sig \<phi> = Inr \<psi>)"

lemma check_check_subst: "check sig TAny \<phi> = Inr check_subst"
  unfolding check_subst_def using check_Inr
  by auto

lemma prepare_\<psi>: "prepare_verimon rw sig \<phi> = Inr \<psi>"
  unfolding \<psi>_def using prepare_Inr
  by (cases "prepare_verimon rw sig \<phi>") auto

lemma safe_\<psi>: "safe_formula \<psi>"
  using prepare_\<psi> unfolding prepare_verimon_def
  by (auto split: sum.splits if_splits simp: Let_def mmonitorable_def
    simp flip: monitorable_formula_code)

lemma wf_f_TCst_convert_tysym[simp]: "wf_f (TCst o convert_tysym)"
  unfolding wf_f_def
  by (auto simp: numeric_ty_def)

lemma wf_f_check_subst[simp]: "wf_f (TCst \<circ> (convert_tysym o check_subst))"
  using wf_f_comp[OF wf_f_TCst_convert_tysym check_sound_proven[OF check_check_subst wf, unfolded wty_result_fX_def, THEN conjunct1]]
  by (auto simp: comp_assoc)

interpretation verimon_\<psi>: verimon \<psi> "map_sig (convert_tysym o check_subst) sig" "convert_tysym o check_subst o TAny"
  unfolding \<psi>_def
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

interpretation monitor_\<phi>: future_bounded_mfodl "Formula.formula.map_formula (convert_tysym \<circ> check_subst) \<phi>"
  "map_sig (convert_tysym o check_subst) sig" "convert_tysym o check_subst o TAny"
  apply standard
  subgoal
    using prepare_\<psi>
    apply (simp_all add: prepare_verimon_def type_check_def Let_def bind_def split: sum.splits if_splits)
    subgoal
      apply (frule check_sound_proven[OF _ wf])
      apply (auto simp add: check_check_subst wty_result_fX_def
        intro!: exI[of _ "convert_tysym"] dest: spec[of _ "convert_tysym o check_subst"])
      done
    subgoal
      apply (frule check_sound_proven[OF _ wf])
      apply (auto simp add: check_check_subst wty_result_fX_def intro!: exI[of _ "convert_tysym"])
      done
    subgoal
      apply (frule check_sound_proven[OF _ wf])
      apply (auto simp add: check_check_subst wty_result_fX_def intro!: exI[of _ "convert_tysym"])
      done
    done
  subgoal
    using prepare_\<psi>[symmetric] check_check_subst[symmetric] unfolding prepare_verimon_def
    apply (auto simp add: prepare_verimon_def type_check_def Let_def bind_def mmonitorable_def
        simp flip: monitorable_formula_code 
        split: sum.splits if_splits intro: future_bounded_rrewrite future_bounded_normalize)
    done
  done

thm monitor_\<phi>.mono_monitor

lemma sat_the_\<psi>:
  "sat_the \<sigma> V v i \<psi> = sat_the \<sigma> V v i (Formula.formula.map_formula (convert_tysym \<circ> check_subst) \<phi>)"
  using prepare_\<psi>[symmetric] safe_\<psi> unfolding prepare_verimon_def
  by (auto split: sum.splits if_splits simp: Let_def final_sat normalize_sat type_check_def check_check_subst)

lemma fvi_\<psi>: "Formula.fvi b \<psi> = Formula.fvi b \<phi>"
  using prepare_\<psi>[symmetric] unfolding prepare_verimon_def
  by (auto split: sum.splits if_splits simp: Let_def normalize_fvi rrewrite_fvi type_check_def check_check_subst)

lemma nfv_\<psi>: "Formula.nfv \<psi> = Formula.nfv \<phi>"
  using prepare_\<psi>[symmetric] unfolding prepare_verimon_def
  by (auto split: sum.splits if_splits simp: Let_def normalize_nfv rrewrite_nfv type_check_def check_check_subst)

lemma pprogress_\<psi>: "pprogress \<psi> \<pi> = pprogress (Formula.formula.map_formula (convert_tysym \<circ> check_subst) \<phi>) \<pi>"
  using prepare_\<psi>[symmetric] unfolding pprogress_def unfolding prepare_verimon_def
  by (auto split: sum.splits if_splits simp: Let_def type_check_def check_check_subst)

lemma Mt_exchange: "verimon_\<psi>.Mt \<pi> = monitor_\<phi>.Mt \<pi>"
  unfolding verimon_\<psi>.Mt_def monitor_\<phi>.Mt_def verimon_\<psi>.M_def monitor_\<phi>.M_def
  by (auto simp: sat_the_\<psi> fvi_\<psi> nfv_\<psi> pprogress_\<psi>)

thm verimon_\<psi>.mono_monitor[unfolded verimon_\<psi>.M_def, folded sat_the_\<psi>]
thm verimon_\<psi>.sound_monitor

lemma verimon_wf_mstate_minit: "wf_mstate (map_sig (convert_tysym o check_subst) sig) (convert_tysym o check_subst o TAny) \<psi> pnil R (minit \<psi>)"
  using prepare_\<psi>[symmetric] safe_\<psi> unfolding prepare_verimon_def
  using check_sound_proven[OF check_check_subst wf, unfolded wty_result_fX_def, THEN conjunct2, THEN spec, of "convert_tysym o check_subst"]
  by (auto split: sum.splits if_splits simp: Let_def type_check_def check_check_subst
    intro!: wf_mstate_minit wty_rrewrite wty_normalize dest!: spec[of _ "convert_tysym"])

lemmas mono_monitor = monitor_\<phi>.mono_monitor
lemmas sound_monitor = monitor_\<phi>.sound_monitor
lemmas complete_monitor = monitor_\<phi>.complete_monitor
lemmas sliceable_M = monitor_\<phi>.sliceable_M
lemmas wf_mstate_minit = verimon_wf_mstate_minit
lemmas wf_mstate_mstep = wf_mstate_mstep
lemmas mstep_mverdicts = verimon_\<psi>.mstep_mverdicts[unfolded Mt_exchange]

end

context verimon begin
thm mono_monitor sound_monitor complete_monitor sliceable_M
thm wf_mstate_minit_safe wf_mstate_mstep mstep_mverdicts
find_theorems M
thm Mt_def
thm M_def
find_theorems maux.minit_verimon
end
end