theory VeriMon
imports Correctness Rewriting Safety_Proofs
begin

lemma map_formula_release_safe_bounded[simp]: "Formula.formula.map_formula f (release_safe_bounded \<phi> I \<psi>) =
  release_safe_bounded (Formula.formula.map_formula f \<phi>) I (Formula.formula.map_formula f \<psi>)"
  by (auto simp: release_safe_bounded_def eventually_def Formula.TT_def always_safe_bounded_def once_def)

lemma progress_map_formula[simp]: "progress \<sigma> P (Formula.formula.map_formula f \<phi>) j = progress \<sigma> P \<phi> j"
  by (induct \<phi> arbitrary: P j rule: progress_custom_induct)
    (auto simp: letpast_progress_def frz_progress_def progress_regex_def regex.set_map image_image)

text \<open>VeriMon's preparation of an input formula: type checking and, if the formula is not
  monitorable and rewriting is requested (@{text rw}), normalization and then rewriting, until
  the formula becomes monitorable. It does not depend on the auxiliary data structures of the
  monitor, so all monitors (the kernel and the dense one) share it.\<close>

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

context maux begin

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

lemma val_restrict_perm: "set ds = set cs \<Longrightarrow> val n ds (restrict ds cs x) = val n cs x"
proof (rule nth_equalityI)
  fix i
  assume set: "set ds = set cs" and "i < length (val n ds (restrict ds cs x))"
  have none: "map_of (zip xs ys) i = None" if "i \<notin> set xs" for xs :: "nat list" and ys :: "'a list"
    using that by (auto simp: map_of_eq_None_iff dest: set_zip_leftD)
  from set show "val n ds (restrict ds cs x) ! i = val n cs x ! i"
    using \<open>i < length _\<close> by (cases "i \<in> set ds") (simp add: tup_get_restrict, simp add: tup_get_def none)
qed simp

(* Elimination rules for well-typed formulas*)
inductive_cases wty_formula_PredE[elim!]: "S, E \<turnstile> Formula.Pred p tms"
inductive_cases wty_formula_EqE[elim!]: "S, E \<turnstile> Formula.Eq t1 t2"
inductive_cases wty_formula_LessE[elim!]: "S, E \<turnstile> Formula.Less t1 t2"
inductive_cases wty_formula_LessEqE[elim!]: "S, E \<turnstile> Formula.LessEq t1 t2"
inductive_cases wty_formula_LetE[elim!]: "S, E \<turnstile> Formula.Let p \<phi>1 \<phi>2"
inductive_cases wty_formula_FrzE[elim!]: "S, E \<turnstile> Formula.Frz p \<phi>1 \<phi>2"
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
  case (Frz S E' \<phi> p E \<psi>)
  then show ?case
    by (auto simp del: fun_upd_apply simp: simplify_terms_nfv intro!: wty_formula.Frz)
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
    by (auto simp: push_negation_nfv intro!: wty_formula.Frz)
next
  case (5 p \<phi> \<psi>)
  then show ?case
    by (auto simp: push_negation_nfv intro!: wty_formula.LetPast)
next
  case ("6_2" v va vb)
  then show ?case
    by (fastforce intro!: wty_formula.Let wty_formula.Neg)
next
  case ("6_3" v va vb)
  then show ?case
    by (fastforce intro!: wty_formula.Frz wty_formula.Neg)
next
  case ("6_4" v va vb)
  then show ?case
    by (fastforce intro!: wty_formula.Neg wty_formula.LetPast)
next
  case (16 I r)
  then show ?case 
    by (fastforce simp: regex.pred_map intro!: wty_formula.MatchP elim: regex.pred_mono_strong)
next
  case (17 I r)
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
    by (auto simp: elim_double_negation_nfv intro!: wty_formula.Frz)
next
  case (4 p \<phi> \<psi>)
  then show ?case
    by (auto simp: elim_double_negation_nfv intro!: wty_formula.LetPast)
next
  case ("5_2" v va vb)
  then show ?case
    by (fastforce intro!: wty_formula.Let wty_formula.Neg)
next
  case ("5_3" v va vb)
  then show ?case
    by (fastforce intro!: wty_formula.Frz wty_formula.Neg)
next
  case ("5_4" v va vb)
  then show ?case
    by (fastforce intro!: wty_formula.LetPast wty_formula.Neg)
next
  case (15 I r)
  then show ?case
    by (fastforce simp: regex.pred_map intro!: wty_formula.MatchP elim: regex.pred_mono_strong)
next
  case (16 I r)
  then show ?case
    by (fastforce simp: regex.pred_map intro!: wty_formula.MatchF elim: regex.pred_mono_strong)
qed (auto intro!: wty_formula.intros)

lemma wty_normalize: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> normalize \<phi>"
  unfolding normalize_def using wty_push_negation wty_simplify_terms wty_elim_double_negation
  by auto


(* Proofs that rrewrite preserves well-typedness*)

lemma wty_trm_shiftTI:
  "E \<turnstile> t :: T \<Longrightarrow> (\<lambda>i. if i < n then E i else if i = n then k else E (i - 1)) \<turnstile> shiftTI n t :: T"
  by (induct t T rule: wty_trm.induct) (auto intro!: wty_trm.intros)

lemma wty_formula_shiftI_r: 
  "S, E \<turnstile> project \<phi> \<Longrightarrow>
     S, (\<lambda>i. if i < n then E i else if i = n then k else E (i - 1)) \<turnstile> project (shiftI_r n \<phi>)"
proof (induction \<phi> arbitrary: n E S rule: Rewriting.formula.induct)
  case (Exists T \<alpha>)
    have "(\<lambda>i. if i < Suc n then case i of 0 \<Rightarrow> T | Suc x \<Rightarrow> E x 
            else if i = Suc n then k else case i - 1 of 0 \<Rightarrow> T | Suc x \<Rightarrow> E x) =
           case_nat T (\<lambda>i. if i < n then E i else if i = n then k else E (i - 1))"
    by (auto simp: fun_eq_iff split: nat.splits)
  with Exists(2) Exists(1)[of S "case_nat T E" "Suc n"] show ?case
    by (auto intro!: wty_formula.Exists)
next
  case (Agg y \<omega> tys f \<alpha>)
  have "(\<lambda>i. if i < n + length tys then agg_env E tys i
 else if i = n + length tys then k else agg_env E tys (i - 1)) =
    agg_env (\<lambda>i. if i < n then E i else if i = n then k else E (i - 1)) tys"
    by (auto simp: fun_eq_iff simp: agg_env_def)
  with Agg(2) Agg(1)[of S "agg_env E tys" "n + length tys"] show ?case
    by (auto intro!: wty_formula.Agg dest!: wty_trm_shiftTI[of "agg_env E tys" f _ "n + length tys" k])
next
  case (Frz p \<alpha> \<beta>)
  then show ?case
    by (auto intro!: wty_formula.Frz)
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

text \<open> Typing is not affected by updating the signature for predicates that do not occur. \<close>

lemma wty_formula_fun_upd_fresh: "S, E \<turnstile> \<phi> \<Longrightarrow> p \<notin> preds \<phi> \<Longrightarrow> S(p \<mapsto> x), E \<turnstile> \<phi>"
proof (induction S E \<phi> rule: wty_formula.induct)
  case (Pred S q tms tys E)
  then show ?case
    by (auto intro!: wty_formula.Pred)
next
  case (Let S E' \<phi> q E \<psi>)
  let ?q = "(q, Formula.nfv \<phi>)"
  let ?t = "tabulate E' 0 (Formula.nfv \<phi>)"
  from Let.prems have p: "p \<notin> preds \<phi>" "p \<noteq> ?q \<Longrightarrow> p \<notin> preds \<psi>"
    by auto
  have "S(p \<mapsto> x, ?q \<mapsto> ?t), E \<turnstile> \<psi>"
  proof (cases "p = ?q")
    case True
    then have "S(p \<mapsto> x, ?q \<mapsto> ?t) = S(?q \<mapsto> ?t)"
      by simp
    then show ?thesis
      using Let.hyps(2) by (simp only:)
  next
    case False
    then have "S(p \<mapsto> x, ?q \<mapsto> ?t) = S(?q \<mapsto> ?t, p \<mapsto> x)"
      by (rule fun_upd_twist)
    then show ?thesis
      using Let.IH(2)[OF p(2)[OF False]] by (simp only:)
  qed
  then show ?case
    by (rule wty_formula.Let[OF Let.IH(1)[OF p(1)]])
next
  case (Frz S E' \<phi> q E \<psi>)
  let ?q = "(q, Formula.nfv \<phi>)"
  let ?t = "tabulate E' 0 (Formula.nfv \<phi>)"
  from Frz.prems have p: "p \<notin> preds \<phi>" "p \<noteq> ?q \<Longrightarrow> p \<notin> preds \<psi>"
    by auto
  have "S(p \<mapsto> x, ?q \<mapsto> ?t), E \<turnstile> \<psi>"
  proof (cases "p = ?q")
    case True
    then have "S(p \<mapsto> x, ?q \<mapsto> ?t) = S(?q \<mapsto> ?t)"
      by simp
    then show ?thesis
      using Frz.hyps(2) by (simp only:)
  next
    case False
    then have "S(p \<mapsto> x, ?q \<mapsto> ?t) = S(?q \<mapsto> ?t, p \<mapsto> x)"
      by (rule fun_upd_twist)
    then show ?thesis
      using Frz.IH(2)[OF p(2)[OF False]] by (simp only:)
  qed
  then show ?case
    by (rule wty_formula.Frz[OF Frz.IH(1)[OF p(1)]])
next
  case (LetPast S q \<phi> E' E \<psi>)
  let ?q = "(q, Formula.nfv \<phi>)"
  let ?t = "tabulate E' 0 (Formula.nfv \<phi>)"
  have "S(p \<mapsto> x, ?q \<mapsto> ?t), E' \<turnstile> \<phi> \<and> S(p \<mapsto> x, ?q \<mapsto> ?t), E \<turnstile> \<psi>"
  proof (cases "p = ?q")
    case True
    then have "S(p \<mapsto> x, ?q \<mapsto> ?t) = S(?q \<mapsto> ?t)"
      by simp
    then show ?thesis
      using LetPast.hyps by (simp only: simp_thms)
  next
    case False
    with LetPast.prems have "p \<notin> preds \<phi>" "p \<notin> preds \<psi>"
      by auto
    moreover from False have "S(p \<mapsto> x, ?q \<mapsto> ?t) = S(?q \<mapsto> ?t, p \<mapsto> x)"
      by (rule fun_upd_twist)
    ultimately show ?thesis
      using LetPast.IH by (simp only: simp_thms)
  qed
  then show ?case
    by (blast intro: wty_formula.LetPast[where E'=E'])
next
  case (MatchP S E r I)
  then show ?case
    by (auto simp: fv_regex_alt regex.pred_set intro!: wty_formula.MatchP)
next
  case (MatchF S E r I)
  then show ?case
    by (auto simp: fv_regex_alt regex.pred_set intro!: wty_formula.MatchF)
qed (auto intro!: wty_formula.intros)

lemma wty_frz_atom: "S (q, n) = Some (tabulate E 0 n) \<Longrightarrow> S, E \<turnstile> project (frz_atom q n)"
  by (auto simp: frz_atom_def tabulate_alt list.rel_map intro!: wty_formula.Pred wty_trm.Var list.rel_refl)

text \<open> Typing of a frozen conjunct: @{term "Frz q \<alpha>' (And \<alpha>' \<psi>)"}. \<close>

lemma wty_frz_and:
  assumes "S, E \<turnstile> project \<alpha>'" "(q, nfv \<alpha>') \<notin> preds (project \<alpha>')"
    and "S((q, nfv \<alpha>') \<mapsto> tabulate E 0 (nfv \<alpha>')), E \<turnstile> project \<psi>"
  shows "S, E \<turnstile> project (Frz q \<alpha>' (And \<alpha>' \<psi>))"
  unfolding project.simps
  by (rule wty_formula.Frz[where E'=E, OF assms(1)], rule wty_formula.And)
    (use assms in \<open>simp_all add: nfv_project wty_formula_fun_upd_fresh\<close>)

lemma wty_frz_atom_and:
  assumes "S, E \<turnstile> project \<beta>" "(q, n) \<notin> preds (project \<beta>)"
  shows "S((q, n) \<mapsto> tabulate E 0 n), E \<turnstile> project (And (frz_atom q n) \<beta>)"
  unfolding project.simps
  by (rule wty_formula.And[OF wty_frz_atom wty_formula_fun_upd_fresh[OF assms]]) simp

lemma wty_fresh_rewrite:
  "S, E \<turnstile> project (rewrite \<gamma> t) \<Longrightarrow> (q, n) \<notin> preds (project \<gamma>) \<Longrightarrow>
   S((q, n) \<mapsto> x), E \<turnstile> project (rewrite \<gamma> t)"
  by (simp add: wty_formula_fun_upd_fresh)

lemma wty_frz_conj_rw:
  assumes "S, E \<turnstile> project (rewrite \<alpha> Same)" "(q, nfv \<alpha>) \<notin> preds (project \<alpha>)"
    "S((q, nfv \<alpha>) \<mapsto> tabulate E 0 (nfv \<alpha>)), E \<turnstile> project X"
  shows "S, E \<turnstile> project (Frz q (rewrite \<alpha> Same) (And (rewrite \<alpha> Same) X))"
  using wty_frz_and[of S E "rewrite \<alpha> Same" q X] assms by simp

lemma wty_rewrite: "S, E \<turnstile> project \<phi> \<Longrightarrow> S, E \<turnstile> project (rewrite \<phi> t)"
proof (induction \<phi> t arbitrary: S E rule: rewrite.induct)
  case (1 \<alpha> \<beta> \<gamma> t)
  then show ?case
    by (auto intro!: wty_formula.intros)
next
  case (2 \<alpha> \<beta> I \<gamma> t)
  from "2.prems" have w\<alpha>: "S, E \<turnstile> project \<alpha>" and w\<beta>: "S, E \<turnstile> project \<beta>"
    and w\<gamma>: "S, E \<turnstile> project \<gamma>"
    by auto
  show ?case
  proof (cases "prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>")
    case True
    let ?q = "frz_name [\<alpha>, \<beta>, \<gamma>]"
    let ?S = "S((?q, nfv \<alpha>) \<mapsto> tabulate E 0 (nfv \<alpha>))"
    have w1: "?S, E \<turnstile> project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)"
      by (rule "2.IH"(2)[OF True refl refl refl wty_frz_atom_and[OF w\<beta>]]) (simp add: frz_name_fresh)
    have w2: "?S, E \<turnstile> project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<gamma>) Same)"
      by (rule "2.IH"(3)[OF True refl refl refl wty_frz_atom_and[OF w\<gamma>]]) (simp add: frz_name_fresh)
    from w1 w2 have body: "?S, E \<turnstile> project (Release (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same) I
      (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<gamma>) Same))"
      by (auto intro!: wty_formula.intros)
    have eq: "rewrite (And \<alpha> (Release \<beta> I \<gamma>)) t = Frz ?q (rewrite \<alpha> Same) (And (rewrite \<alpha> Same) (Release (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same) I
      (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<gamma>) Same)))"
      using True by (simp add: Let_def)
    show ?thesis
      unfolding eq by (rule wty_frz_conj_rw[OF "2.IH"(1)[OF True w\<alpha>] _ body]) (simp add: frz_name_fresh)
  next
    case False
    with 2 w\<alpha> w\<beta> w\<gamma> show ?thesis
      by (auto intro!: wty_formula.intros)
  qed
next
  case (3 \<alpha> \<beta> I \<gamma> t)
  from "3.prems" have w\<alpha>: "S, E \<turnstile> project \<alpha>" and w\<beta>: "S, E \<turnstile> project \<beta>"
    and w\<gamma>: "S, E \<turnstile> project \<gamma>"
    by auto
  show ?case
  proof (cases "prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>")
    case True
    let ?q = "frz_name [\<alpha>, \<beta>, \<gamma>]"
    let ?S = "S((?q, nfv \<alpha>) \<mapsto> tabulate E 0 (nfv \<alpha>))"
    have w1: "?S, E \<turnstile> project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)"
      by (rule "3.IH"(2)[OF True refl refl refl wty_frz_atom_and[OF w\<beta>]]) (simp add: frz_name_fresh)
    have w2: "?S, E \<turnstile> project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<gamma>) Same)"
      by (rule "3.IH"(3)[OF True refl refl refl wty_frz_atom_and[OF w\<gamma>]]) (simp add: frz_name_fresh)
    from w1 w2 have body: "?S, E \<turnstile> project (Trigger (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same) I
      (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<gamma>) Same))"
      by (auto intro!: wty_formula.intros)
    have eq: "rewrite (And \<alpha> (Trigger \<beta> I \<gamma>)) t = Frz ?q (rewrite \<alpha> Same) (And (rewrite \<alpha> Same) (Trigger (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same) I
      (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<gamma>) Same)))"
      using True by (simp add: Let_def)
    show ?thesis
      unfolding eq by (rule wty_frz_conj_rw[OF "3.IH"(1)[OF True w\<alpha>] _ body]) (simp add: frz_name_fresh)
  next
    case False
    with 3 w\<alpha> w\<beta> w\<gamma> show ?thesis
      by (auto intro!: wty_formula.intros)
  qed
next
  case (4 \<alpha> k \<beta> t)
  have "(\<lambda>i. if i = 0 then k else E (i - 1)) = case_nat k E"
    by (auto simp: fun_eq_iff split: nat.splits)
  with 4(2-4) show ?case
    using wty_formula_shiftI_r[of S E \<alpha> 0 k]
    by (auto intro!: wty_formula.Exists wty_formula.And 4(1))
next
  case (6 \<alpha> \<beta> I \<gamma> t)
  from "6.prems" have w\<alpha>: "S, E \<turnstile> project \<alpha>" and w\<beta>: "S, E \<turnstile> project \<beta>"
    and w\<gamma>: "S, E \<turnstile> project \<gamma>"
    by auto
  let ?q = "frz_name [\<alpha>, \<beta>, \<gamma>]"
  let ?S = "S((?q, nfv \<alpha>) \<mapsto> tabulate E 0 (nfv \<alpha>))"
  consider (a) "prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>"
    | (b) "\<not> (prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>)" "prop_cond \<alpha> \<gamma> \<and> frz_ok \<alpha>"
    | (c) "\<not> (prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>)" "\<not> (prop_cond \<alpha> \<gamma> \<and> frz_ok \<alpha>)"
    by blast
  then show ?case
  proof cases
    case a
    have w1: "?S, E \<turnstile> project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)"
      by (rule "6.IH"(2)[OF a refl refl refl wty_frz_atom_and[OF w\<beta>]]) (simp add: frz_name_fresh)
    have w2: "?S, E \<turnstile> project (rewrite \<gamma> Same)"
      by (rule wty_fresh_rewrite[OF "6.IH"(3)[OF a refl refl refl w\<gamma>]]) (simp add: frz_name_fresh)
    from w1 w2 have body: "?S, E \<turnstile> project (Since (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same) I (rewrite \<gamma> Same))"
      by (auto intro!: wty_formula.intros)
    have eq: "rewrite (And \<alpha> (Since \<beta> I \<gamma>)) t = Frz ?q (rewrite \<alpha> Same) (And (rewrite \<alpha> Same) (Since (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same) I (rewrite \<gamma> Same)))"
      using a by (simp add: Let_def)
    show ?thesis
      unfolding eq by (rule wty_frz_conj_rw[OF "6.IH"(1)[OF a w\<alpha>] _ body]) (simp add: frz_name_fresh)
  next
    case b
    have w1: "?S, E \<turnstile> project (rewrite \<beta> Same)"
      by (rule wty_fresh_rewrite[OF "6.IH"(5)[OF b refl refl refl w\<beta>]]) (simp add: frz_name_fresh)
    have w2: "?S, E \<turnstile> project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<gamma>) Same)"
      by (rule "6.IH"(6)[OF b refl refl refl wty_frz_atom_and[OF w\<gamma>]]) (simp add: frz_name_fresh)
    from w1 w2 have body: "?S, E \<turnstile> project (Since (rewrite \<beta> Same) I (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<gamma>) Same))"
      by (auto intro!: wty_formula.intros)
    have eq: "rewrite (And \<alpha> (Since \<beta> I \<gamma>)) t = Frz ?q (rewrite \<alpha> Same) (And (rewrite \<alpha> Same) (Since (rewrite \<beta> Same) I (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<gamma>) Same)))"
      using b by (simp add: Let_def)
    show ?thesis
      unfolding eq by (rule wty_frz_conj_rw[OF "6.IH"(4)[OF b w\<alpha>] _ body]) (simp add: frz_name_fresh)
  next
    case c
    with 6 w\<alpha> w\<beta> w\<gamma> show ?thesis
      by (auto intro!: wty_formula.intros)
  qed
next
  case (7 \<alpha> \<beta> I \<gamma> t)
  from "7.prems" have w\<alpha>: "S, E \<turnstile> project \<alpha>" and w\<beta>: "S, E \<turnstile> project \<beta>"
    and w\<gamma>: "S, E \<turnstile> project \<gamma>"
    by auto
  let ?q = "frz_name [\<alpha>, \<beta>, \<gamma>]"
  let ?S = "S((?q, nfv \<alpha>) \<mapsto> tabulate E 0 (nfv \<alpha>))"
  consider (a) "prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>"
    | (b) "\<not> (prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>)" "prop_cond \<alpha> \<gamma> \<and> frz_ok \<alpha>"
    | (c) "\<not> (prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>)" "\<not> (prop_cond \<alpha> \<gamma> \<and> frz_ok \<alpha>)"
    by blast
  then show ?case
  proof cases
    case a
    have w1: "?S, E \<turnstile> project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)"
      by (rule "7.IH"(2)[OF a refl refl refl wty_frz_atom_and[OF w\<beta>]]) (simp add: frz_name_fresh)
    have w2: "?S, E \<turnstile> project (rewrite \<gamma> Same)"
      by (rule wty_fresh_rewrite[OF "7.IH"(3)[OF a refl refl refl w\<gamma>]]) (simp add: frz_name_fresh)
    from w1 w2 have body: "?S, E \<turnstile> project (Until (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same) I (rewrite \<gamma> Same))"
      by (auto intro!: wty_formula.intros)
    have eq: "rewrite (And \<alpha> (Until \<beta> I \<gamma>)) t = Frz ?q (rewrite \<alpha> Same) (And (rewrite \<alpha> Same) (Until (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same) I (rewrite \<gamma> Same)))"
      using a by (simp add: Let_def)
    show ?thesis
      unfolding eq by (rule wty_frz_conj_rw[OF "7.IH"(1)[OF a w\<alpha>] _ body]) (simp add: frz_name_fresh)
  next
    case b
    have w1: "?S, E \<turnstile> project (rewrite \<beta> Same)"
      by (rule wty_fresh_rewrite[OF "7.IH"(5)[OF b refl refl refl w\<beta>]]) (simp add: frz_name_fresh)
    have w2: "?S, E \<turnstile> project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<gamma>) Same)"
      by (rule "7.IH"(6)[OF b refl refl refl wty_frz_atom_and[OF w\<gamma>]]) (simp add: frz_name_fresh)
    from w1 w2 have body: "?S, E \<turnstile> project (Until (rewrite \<beta> Same) I (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<gamma>) Same))"
      by (auto intro!: wty_formula.intros)
    have eq: "rewrite (And \<alpha> (Until \<beta> I \<gamma>)) t = Frz ?q (rewrite \<alpha> Same) (And (rewrite \<alpha> Same) (Until (rewrite \<beta> Same) I (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<gamma>) Same)))"
      using b by (simp add: Let_def)
    show ?thesis
      unfolding eq by (rule wty_frz_conj_rw[OF "7.IH"(4)[OF b w\<alpha>] _ body]) (simp add: frz_name_fresh)
  next
    case c
    with 7 w\<alpha> w\<beta> w\<gamma> show ?thesis
      by (auto intro!: wty_formula.intros)
  qed
next
  case (8 \<alpha> I \<beta> t)
  show ?case
  proof (cases "prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>")
    case True
    let ?q = "frz_name [\<alpha>, \<beta>]"
    let ?S = "S((?q, nfv \<alpha>) \<mapsto> tabulate E 0 (nfv \<alpha>))"
    from "8.prems" have w\<alpha>: "S, E \<turnstile> project \<alpha>" and w\<beta>: "S, E \<turnstile> project \<beta>"
      by (auto simp: once_def)
    have w1: "?S, E \<turnstile> project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)"
      by (rule "8.IH"(2)[OF True refl refl refl wty_frz_atom_and[OF w\<beta>]]) (simp add: frz_name_fresh)
    have body: "?S, E \<turnstile> project (Once I (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same))"
      using w1 by (auto simp: once_def intro!: wty_formula.intros)
    have eq: "rewrite (And \<alpha> (Once I \<beta>)) t = Frz ?q (rewrite \<alpha> Same) (And (rewrite \<alpha> Same) (Once I (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)))"
      using True by (simp add: Let_def)
    show ?thesis
      unfolding eq by (rule wty_frz_conj_rw[OF "8.IH"(1)[OF True w\<alpha>] _ body]) (simp add: frz_name_fresh)
  next
    case False
    with 8 show ?thesis
      by (auto simp: once_def intro!: wty_formula.intros)
  qed
next
  case (9 \<alpha> I \<beta> t)
  show ?case
  proof (cases "prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>")
    case True
    let ?q = "frz_name [\<alpha>, \<beta>]"
    let ?S = "S((?q, nfv \<alpha>) \<mapsto> tabulate E 0 (nfv \<alpha>))"
    from "9.prems" have w\<alpha>: "S, E \<turnstile> project \<alpha>" and w\<beta>: "S, E \<turnstile> project \<beta>"
      by (auto simp: eventually_def)
    have w1: "?S, E \<turnstile> project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)"
      by (rule "9.IH"(2)[OF True refl refl refl wty_frz_atom_and[OF w\<beta>]]) (simp add: frz_name_fresh)
    have body: "?S, E \<turnstile> project (Eventually I (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same))"
      using w1 by (auto simp: eventually_def intro!: wty_formula.intros)
    have eq: "rewrite (And \<alpha> (Eventually I \<beta>)) t = Frz ?q (rewrite \<alpha> Same) (And (rewrite \<alpha> Same) (Eventually I (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)))"
      using True by (simp add: Let_def)
    show ?thesis
      unfolding eq by (rule wty_frz_conj_rw[OF "9.IH"(1)[OF True w\<alpha>] _ body]) (simp add: frz_name_fresh)
  next
    case False
    with 9 show ?thesis
      by (auto simp: eventually_def intro!: wty_formula.intros)
  qed
next
  case (10 \<alpha> I \<beta> t)
  show ?case
  proof (cases "prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>")
    case True
    let ?q = "frz_name [\<alpha>, \<beta>]"
    let ?S = "S((?q, nfv \<alpha>) \<mapsto> tabulate E 0 (nfv \<alpha>))"
    from "10.prems" have w\<alpha>: "S, E \<turnstile> project \<alpha>" and w\<beta>: "S, E \<turnstile> project \<beta>"
      by (auto simp: historically_def once_def)
    have w1: "?S, E \<turnstile> project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)"
      by (rule "10.IH"(2)[OF True refl refl refl wty_frz_atom_and[OF w\<beta>]]) (simp add: frz_name_fresh)
    have body: "?S, E \<turnstile> project (Historically I (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same))"
      using w1 by (auto simp: historically_def once_def intro!: wty_formula.intros)
    have eq: "rewrite (And \<alpha> (Historically I \<beta>)) t = Frz ?q (rewrite \<alpha> Same) (And (rewrite \<alpha> Same) (Historically I (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)))"
      using True by (simp add: Let_def)
    show ?thesis
      unfolding eq by (rule wty_frz_conj_rw[OF "10.IH"(1)[OF True w\<alpha>] _ body]) (simp add: frz_name_fresh)
  next
    case False
    with 10 show ?thesis
      by (auto simp: historically_def once_def intro!: wty_formula.intros)
  qed
next
  case (11 \<alpha> I \<beta> t)
  show ?case
  proof (cases "prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>")
    case True
    let ?q = "frz_name [\<alpha>, \<beta>]"
    let ?S = "S((?q, nfv \<alpha>) \<mapsto> tabulate E 0 (nfv \<alpha>))"
    from "11.prems" have w\<alpha>: "S, E \<turnstile> project \<alpha>" and w\<beta>: "S, E \<turnstile> project \<beta>"
      by (auto simp: always_def eventually_def)
    have w1: "?S, E \<turnstile> project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)"
      by (rule "11.IH"(2)[OF True refl refl refl wty_frz_atom_and[OF w\<beta>]]) (simp add: frz_name_fresh)
    have body: "?S, E \<turnstile> project (Always I (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same))"
      using w1 by (auto simp: always_def eventually_def intro!: wty_formula.intros)
    have eq: "rewrite (And \<alpha> (Always I \<beta>)) t = Frz ?q (rewrite \<alpha> Same) (And (rewrite \<alpha> Same) (Always I (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)))"
      using True by (simp add: Let_def)
    show ?thesis
      unfolding eq by (rule wty_frz_conj_rw[OF "11.IH"(1)[OF True w\<alpha>] _ body]) (simp add: frz_name_fresh)
  next
    case False
    with 11 show ?thesis
      by (auto simp: always_def eventually_def intro!: wty_formula.intros)
  qed
next
  case (14 \<alpha> \<gamma> I \<beta> t)
  from "14.prems" have w\<alpha>: "S, E \<turnstile> project \<alpha>" and w\<beta>: "S, E \<turnstile> project \<beta>"
    and w\<gamma>: "S, E \<turnstile> project \<gamma>"
    by auto
  have wl: "S, E \<turnstile> project (rewrite (And \<alpha> \<gamma>) Same)"
    using "14.IH"(1) w\<alpha> w\<gamma> by (auto intro!: wty_formula.intros)
  let ?q = "frz_name [\<alpha>, \<gamma>, \<beta>]"
  consider (a) "t = Same \<and> \<not> mem I 0 \<and> prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>"
    | (b) "\<not> (t = Same \<and> \<not> mem I 0 \<and> prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>)"
      "t = Same \<and> \<not> mem I 0 \<and> prop_cond \<gamma> \<beta> \<and> frz_ok \<gamma>"
    | (c) "\<not> (t = Same \<and> \<not> mem I 0 \<and> prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>)"
      "\<not> (t = Same \<and> \<not> mem I 0 \<and> prop_cond \<gamma> \<beta> \<and> frz_ok \<gamma>)"
    by blast
  then show ?case
  proof cases
    case a
    let ?S = "S((?q, nfv \<alpha>) \<mapsto> tabulate E 0 (nfv \<alpha>))"
    have w1: "?S, E \<turnstile> project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)"
      by (rule "14.IH"(3)[OF refl a refl refl wty_frz_atom_and[OF w\<beta>]]) (simp add: frz_name_fresh)
    have w2: "?S, E \<turnstile> project (rewrite (And \<alpha> \<gamma>) Same)"
      by (rule wty_fresh_rewrite[OF wl]) (simp add: frz_name_fresh)
    from a w1 w2 show ?thesis
      using "14.IH"(2)[OF refl a refl refl w\<alpha>]
      by (auto simp: Let_def nfv_project intro!: wty_formula.Frz[where E'=E] wty_formula.Since)
  next
    case b
    let ?S = "S((?q, nfv \<gamma>) \<mapsto> tabulate E 0 (nfv \<gamma>))"
    have w1: "?S, E \<turnstile> project (rewrite (And (frz_atom ?q (nfv \<gamma>)) \<beta>) Same)"
      by (rule "14.IH"(5)[OF refl b refl refl wty_frz_atom_and[OF w\<beta>]]) (simp add: frz_name_fresh)
    have w2: "?S, E \<turnstile> project (rewrite (And \<alpha> \<gamma>) Same)"
      by (rule wty_fresh_rewrite[OF wl]) (simp add: frz_name_fresh)
    from b w1 w2 show ?thesis
      using "14.IH"(4)[OF refl b refl refl w\<gamma>]
      by (auto simp: Let_def nfv_project intro!: wty_formula.Frz[where E'=E] wty_formula.Since)
  next
    case c
    with 14 wl w\<alpha> w\<beta> w\<gamma> show ?thesis
      by (cases t) (auto simp: Let_def once_def intro!: wty_formula.intros "14.IH"(6-8))
  qed
next
  case (5 \<alpha> \<beta> t)
  from "5.prems" have w\<alpha>: "S, E \<turnstile> project \<alpha>" and w\<beta>: "S, E \<turnstile> project \<beta>"
    by auto
  show ?case
  proof (cases "prop_cond \<alpha> \<beta>")
    case True
    then show ?thesis
      using "5.IH"(1)[OF True w\<alpha>] "5.IH"(2)[OF True, unfolded project.simps, OF wty_formula.And[OF w\<alpha> w\<beta>]]
      by (auto intro!: wty_formula.intros)
  next
    case False
    then show ?thesis
      using "5.IH"(3)[OF False w\<alpha>] "5.IH"(4)[OF False refl w\<beta>]
      by (auto intro!: wty_formula.intros)
  qed
next
  case (12 \<alpha> I \<beta> t)
  from "12.prems" have w\<alpha>: "S, E \<turnstile> project \<alpha>" and w\<beta>: "S, E \<turnstile> project \<beta>"
    by auto
  show ?case
  proof (cases "prop_cond \<alpha> \<beta>")
    case True
    then show ?thesis
      using "12.IH"(1)[OF True w\<alpha>] "12.IH"(3)[OF True w\<beta>]
      by (auto intro!: wty_formula.intros)
  next
    case False
    then show ?thesis
      using "12.IH"(4)[OF False w\<alpha>] "12.IH"(5)[OF False refl w\<beta>]
      by (auto intro!: wty_formula.intros)
  qed
next
  case (13 \<alpha> I \<beta> t)
  from "13.prems" have w\<alpha>: "S, E \<turnstile> project \<alpha>" and w\<beta>: "S, E \<turnstile> project \<beta>"
    by auto
  show ?case
  proof (cases "prop_cond \<alpha> \<beta>")
    case True
    then show ?thesis
      using "13.IH"(1)[OF True w\<alpha>] "13.IH"(3)[OF True w\<beta>]
      by (auto intro!: wty_formula.intros)
  next
    case False
    then show ?thesis
      using "13.IH"(4)[OF False w\<alpha>] "13.IH"(5)[OF False refl w\<beta>]
      by (auto intro!: wty_formula.intros)
  qed
next
  case (15 \<alpha> \<gamma> I \<beta> t)
  from "15.prems" have w\<alpha>: "S, E \<turnstile> project \<alpha>" and w\<beta>: "S, E \<turnstile> project \<beta>"
    and w\<gamma>: "S, E \<turnstile> project \<gamma>"
    by (cases t; auto)+
  have wl: "S, E \<turnstile> project (rewrite (And \<alpha> \<gamma>) Same)"
    using "15.IH"(1) w\<alpha> w\<gamma> by (auto intro!: wty_formula.intros)
  show ?case
    using wl w\<alpha> w\<beta> w\<gamma>
    by (cases t) (auto simp: Let_def once_def intro!: wty_formula.intros "15.IH"(2-4))
next
  case (34 I r t)
  then show ?case
    by (force simp: regex.pred_map intro!: wty_formula.MatchF elim: regex.pred_mono_strong)
next
  case (35 I r t)
  then show ?case
    by (force simp: regex.pred_map intro!: wty_formula.MatchP elim: regex.pred_mono_strong)
next
  case (36 \<phi>s t)
  then show ?case
    by (auto intro!: wty_formula.Ands)
next
  case ("19_10" \<phi>s I r)
  from "19_10.prems" have wr: "S, E \<turnstile> project r" and w\<phi>s: "\<forall>\<phi>\<in>set \<phi>s. S, E \<turnstile> project \<phi>"
    by auto
  have "S, E \<turnstile> project (rewrite (Ands \<phi>s) Same)"
    by (rule "19_10.IH"(2)) (use w\<phi>s in \<open>auto intro!: wty_formula.Ands\<close>)
  then show ?case
    using "19_10.IH"(1)[OF wr] by (auto intro!: wty_formula.intros)
next
  case ("20_10" \<phi>s I r)
  from "20_10.prems" have wr: "S, E \<turnstile> project r" and w\<phi>s: "\<forall>\<phi>\<in>set \<phi>s. S, E \<turnstile> project \<phi>"
    by auto
  have "S, E \<turnstile> project (rewrite (Ands \<phi>s) Same)"
    by (rule "20_10.IH"(2)) (use w\<phi>s in \<open>auto intro!: wty_formula.Ands\<close>)
  then show ?case
    using "20_10.IH"(1)[OF wr] by (auto intro!: wty_formula.intros)
qed (auto simp: once_def eventually_def always_def historically_def intro!: wty_formula.intros)

lemma wty_project_embed: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> project (embed \<phi>)"
  by (simp add: project_embed)

lemma wty_rrewrite: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> rrewrite \<phi>"
  unfolding rrewrite_def using wty_rewrite wty_project_embed by auto


(* Proofs that if a normalized formula is future-bounded, then so is the original formula *)

lemma safe_letpast_simplify_terms[simp]: "safe_letpast (p, n) (simplify_terms \<phi>) = safe_letpast (p, n) \<phi>"
  by (induction \<phi> arbitrary: p n rule: simplify_terms.induct)
    (auto simp: simplify_terms_nfv image_image regex.set_map)

lemma future_bounded_simplify_terms: "Safety.future_bounded (simplify_terms \<phi>) \<Longrightarrow> Safety.future_bounded \<phi>"
  by (induction \<phi> rule: simplify_terms.induct)
    (auto simp: simplify_terms_nfv list.pred_map regex.pred_map elim: list.pred_mono_strong regex.pred_mono_strong)

lemma safe_letpast_push_negation[simp]: "safe_letpast (p, n) (push_negation \<phi>) = safe_letpast (p, n) \<phi>"
  by (induction \<phi> arbitrary: p n rule: push_negation.induct)
    (auto simp: push_negation_nfv image_image regex.set_map)

lemma future_bounded_push_negation: "Safety.future_bounded (push_negation \<phi>) \<Longrightarrow> Safety.future_bounded \<phi>"
  by (induction \<phi> rule: push_negation.induct)
    (auto simp: push_negation_nfv list.pred_map regex.pred_map elim: list.pred_mono_strong regex.pred_mono_strong)

lemma safe_letpast_elim_double_negation[simp]: "safe_letpast (p, n) (elim_double_negation \<phi>) = safe_letpast (p, n) \<phi>"
  by (induction \<phi> arbitrary: p n rule: elim_double_negation.induct)
    (auto simp: elim_double_negation_nfv image_image regex.set_map)

lemma future_bounded_elim_double_negation: "Safety.future_bounded (elim_double_negation \<phi>) \<Longrightarrow> Safety.future_bounded \<phi>"
  by (induction \<phi> rule: elim_double_negation.induct)
    (auto simp: elim_double_negation_nfv list.pred_map regex.pred_map elim: list.pred_mono_strong regex.pred_mono_strong)

lemma future_bounded_normalize: "Safety.future_bounded (normalize \<phi>) \<Longrightarrow> Safety.future_bounded \<phi>"
  unfolding normalize_def using future_bounded_simplify_terms future_bounded_push_negation future_bounded_elim_double_negation by auto


(* Proofs that if a rewritten formula is future-bounded, then so is the original formula *)

lemma future_bounded_shiftI_r[simp]: "Safety.future_bounded (project (shiftI_r i \<phi>)) = Safety.future_bounded (project \<phi>)"
  by (induction \<phi> arbitrary: i rule: Rewriting.formula.induct)
   (auto simp: historically_def always_def list.pred_map regex.pred_map
     elim: list.pred_mono_strong regex.pred_mono_strong)

lemma future_bounded_fix_r[simp]: "Safety.future_bounded (project (fix_r \<phi> t)) = Safety.future_bounded (project \<phi>)"
  by (induction \<phi> t rule: fix_r.induct) auto

lemma future_bounded_frz_atom[simp]: "Safety.future_bounded (project (frz_atom q n))"
  by (simp add: frz_atom_def)

lemma future_bounded_rewrite: "Safety.future_bounded (project (rewrite \<phi> t)) \<Longrightarrow> Safety.future_bounded (project \<phi>)"
proof (induction \<phi> t rule: rewrite.induct)
  case (14 \<alpha> \<gamma> I \<beta> t)
  then show ?case
    by (cases t) (auto simp: Let_def split: if_splits)
next
  case (15 \<alpha> \<gamma> I \<beta> t)
  then show ?case
    by (cases t) (auto simp: Let_def split: if_splits)
qed (auto simp: Let_def always_def historically_def list.pred_map regex.pred_map
      elim: list.pred_mono_strong regex.pred_mono_strong split: if_splits)

lemma future_bounded_project_embed: "Safety.future_bounded (project (embed \<phi>)) \<Longrightarrow> Safety.future_bounded \<phi>"
  by (auto simp: project_embed)

lemma future_bounded_rrewrite: "Safety.future_bounded (rrewrite \<phi>) \<Longrightarrow> Safety.future_bounded \<phi>"
  unfolding rrewrite_def using future_bounded_rewrite future_bounded_project_embed by auto


(* Proofs that normalize does not change the progress of the monitor *)

lemma progress_simplify_terms[simp]: "progress \<sigma> P (simplify_terms \<phi>) j = progress \<sigma> P \<phi> j"
  using [[linarith_split_limit = 17]]
  by (induction \<phi> arbitrary: P j rule: simplify_terms.induct)
    (auto simp: simplify_terms_nfv letpast_progress_def frz_progress_def progress_regex_def regex.set_map image_image
     release_safe_bounded_def Formula.eventually_def always_safe_bounded_def)

lemma progress_push_negation[simp]: "progress \<sigma> P (push_negation \<phi>) j = progress \<sigma> P \<phi> j"
  by (induction \<phi> arbitrary: P j rule: push_negation.induct)
    (auto simp: push_negation_nfv letpast_progress_def frz_progress_def progress_regex_def regex.set_map image_image)

lemma progress_elim_double_negation[simp]: "progress \<sigma> P (elim_double_negation \<phi>) j = progress \<sigma> P \<phi> j"
  by (induction \<phi> arbitrary: P j rule: elim_double_negation.induct)
    (auto simp: elim_double_negation_nfv letpast_progress_def frz_progress_def progress_regex_def regex.set_map image_image)

lemma progress_normalize: "progress \<sigma> P (normalize \<phi>) j = progress \<sigma> P \<phi> j"
  unfolding normalize_def by auto

(* Proofs that rewrite does not change the progress of the monitor.
   The rules that propagate a range restriction \<alpha> into the scope of a temporal operator bind
   \<alpha>'s current satisfactions to a fresh predicate with the freeze operator (Frz q \<alpha> (\<alpha> \<and> OP (q \<and> \<beta>))).
   Since \<alpha> is conjoined at the outer level, the frozen predicate q is available whenever the outer
   conjunction can make progress (lemma progress_Frz_And); hence the progress of the rewritten formula
   coincides with the original one (lemma progress_rewrite). *)
lemma progress_shift[simp]: "progress \<sigma> P (project (shiftI_r i \<phi>)) j = progress \<sigma> P (project \<phi>) j"
proof (induction \<phi> arbitrary: i P j rule: Rewriting.formula.induct)
  case (Ands \<phi>s)
  then show ?case
    by (simp add: image_image cong: image_cong)
next
  case (Release \<phi> I \<psi>)
  then show ?case
    by (simp only: project.simps shiftI_r.simps progress.simps release_safe_bounded_def
      always_safe_bounded_def Formula.eventually_def once_def Formula.TT_def)
next
  case (MatchF I r)
  then show ?case
    by (simp add: progress_regex_def regex.set_map image_image cong: image_cong)
next
  case (MatchP I r)
  then show ?case
    by (simp add: progress_regex_def regex.set_map image_image cong: image_cong)
qed (simp_all add: eventually_def historically_def always_def frz_progress_def)

text \<open> The progress of a freeze operator whose body is not ahead of the frozen formula. \<close>

lemma progress_Frz_eq:
  assumes P: "pred_mapping (\<lambda>x. x \<le> j) P"
    and le1: "progress \<sigma> (P((q, Formula.nfv \<alpha>) \<mapsto> j)) \<psi> j \<le> progress \<sigma> P \<alpha> j"
    and le0: "progress \<sigma> (P((q, Formula.nfv \<alpha>) \<mapsto> 0)) \<psi> j \<le> progress \<sigma> P \<alpha> j"
  shows "progress \<sigma> P (Formula.Frz q \<alpha> \<psi>) j = progress \<sigma> (P((q, Formula.nfv \<alpha>) \<mapsto> j)) \<psi> j"
proof -
  let ?pn = "(q, Formula.nfv \<alpha>)"
  let ?a = "progress \<sigma> P \<alpha> j" and ?m = "progress \<sigma> (P(?pn \<mapsto> j)) \<psi> j"
  have a_le: "?a \<le> j"
    by (rule progress_le_gen[OF P])
  have "(LEAST i. i \<le> j \<and> progress \<sigma> (P(?pn \<mapsto> (if i < ?a then j else 0))) \<psi> j \<le> i) = ?m"
  proof (rule Least_equality)
    show "?m \<le> j \<and> progress \<sigma> (P(?pn \<mapsto> if ?m < ?a then j else 0)) \<psi> j \<le> ?m"
      using le1 le0 a_le by auto
  next
    fix y
    assume "y \<le> j \<and> progress \<sigma> (P(?pn \<mapsto> if y < ?a then j else 0)) \<psi> j \<le> y"
    then show "?m \<le> y"
      using le1 by (cases "y < ?a") auto
  qed
  then show ?thesis
    by (simp add: frz_progress_def)
qed

lemma progress_fresh[simp]: "p \<notin> preds \<phi> \<Longrightarrow> progress \<sigma> (P(p \<mapsto> x)) \<phi> j = progress \<sigma> P \<phi> j"
  by (rule not_contains_pred_progress) (auto dest: contains_pred_preds)

lemma progress_Frz_And:
  assumes P: "pred_mapping (\<lambda>x. x \<le> j) P" and fresh: "(q, Formula.nfv \<alpha>) \<notin> preds \<alpha>"
  shows "progress \<sigma> P (Formula.Frz q \<alpha> (Formula.And \<alpha> \<psi>)) j =
    min (progress \<sigma> P \<alpha> j) (progress \<sigma> (P((q, Formula.nfv \<alpha>) \<mapsto> j)) \<psi> j)"
  using fresh by (subst progress_Frz_eq[OF P]) auto

lemma progress_frz_and_rw:
  assumes P: "pred_mapping (\<lambda>x. x \<le> j) P" and fresh: "(q, nfv \<alpha>) \<notin> preds (project \<alpha>)"
  shows "progress \<sigma> P (project (Frz q (rewrite \<alpha> Same) (And (rewrite \<alpha> Same) X))) j =
    min (progress \<sigma> P (project (rewrite \<alpha> Same)) j) (progress \<sigma> (P((q, nfv \<alpha>) \<mapsto> j)) (project X) j)"
  using progress_Frz_And[OF P, where q=q and \<alpha>="project (rewrite \<alpha> Same)" and \<psi>="project X" and \<sigma>=\<sigma>] fresh
  by (simp add: nfv_project)

lemma progress_frz_atom_and:
  assumes P: "pred_mapping (\<lambda>x. x \<le> j) P" and fresh: "(q, n) \<notin> preds (project \<beta>)"
  shows "progress \<sigma> (P((q, n) \<mapsto> j)) (project (And (frz_atom q n) \<beta>)) j = progress \<sigma> P (project \<beta>) j"
  using fresh progress_le_gen[OF P, of \<sigma> "project \<beta>"] by (simp add: frz_atom_def)

lemma progress_frz_ih:
  assumes P: "pred_mapping (\<lambda>x. x \<le> j) P" and fresh: "(q, n) \<notin> preds (project \<beta>)"
    and IH: "pred_mapping (\<lambda>x. x \<le> j) (P((q, n) \<mapsto> j)) \<Longrightarrow>
      progress \<sigma> (P((q, n) \<mapsto> j)) (project (rewrite (And (frz_atom q n) \<beta>) Same)) j =
      progress \<sigma> (P((q, n) \<mapsto> j)) (project (fix_r (And (frz_atom q n) \<beta>) Same)) j"
  shows "progress \<sigma> (P((q, n) \<mapsto> j)) (project (rewrite (And (frz_atom q n) \<beta>) Same)) j = progress \<sigma> P (project \<beta>) j"
  using IH P progress_frz_atom_and[OF P fresh] by simp

lemma progress_release_safe_bounded_cong:
  assumes "progress \<sigma> P \<phi> j = progress \<sigma> P' \<phi>' j" "progress \<sigma> P \<psi> j = progress \<sigma> P' \<psi>' j"
  shows "progress \<sigma> P (release_safe_bounded \<phi> I \<psi>) j = progress \<sigma> P' (release_safe_bounded \<phi>' I \<psi>') j"
  using assms
  by (simp only: progress.simps release_safe_bounded_def always_safe_bounded_def Formula.eventually_def once_def Formula.TT_def)

lemma progress_Release_cong:
  assumes "progress \<sigma> P \<phi> j = progress \<sigma> P' \<phi>' j" "progress \<sigma> P \<psi> j = progress \<sigma> P' \<psi>' j"
  shows "progress \<sigma> P (Formula.Release \<phi> I \<psi>) j = progress \<sigma> P' (Formula.Release \<phi>' I \<psi>') j"
  using assms
  by (simp only: progress.simps release_safe_bounded_def always_safe_bounded_def Formula.eventually_def once_def Formula.TT_def)

lemma progress_Until_cong:
  assumes "min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j) = min (progress \<sigma> P' \<phi>' j) (progress \<sigma> P' \<psi>' j)"
  shows "progress \<sigma> P (Formula.Until \<phi> I \<psi>) j = progress \<sigma> P' (Formula.Until \<phi>' I \<psi>') j"
  using assms by (simp only: progress.simps)

lemma progress_rewrite:
  "pred_mapping (\<lambda>x. x \<le> j) P \<Longrightarrow>
   progress \<sigma> P (project (rewrite \<phi> t)) j = progress \<sigma> P (project (fix_r \<phi> t)) j"
proof (induction \<phi> t arbitrary: P rule: rewrite.induct)
  case (2 \<alpha> \<beta> I \<gamma> t)
  note P = "2.prems"
  show ?case
  proof (cases "prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>")
    case True
    let ?q = "frz_name [\<alpha>, \<beta>, \<gamma>]"
    let ?P = "P((?q, nfv \<alpha>) \<mapsto> j)"
    have h1: "progress \<sigma> ?P (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)) j = progress \<sigma> P (project \<beta>) j"
      by (rule progress_frz_ih[OF P _ "2.IH"(2)[OF True refl refl refl]]) (simp add: frz_name_fresh)
    have h2: "progress \<sigma> ?P (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<gamma>) Same)) j = progress \<sigma> P (project \<gamma>) j"
      by (rule progress_frz_ih[OF P _ "2.IH"(3)[OF True refl refl refl]]) (simp add: frz_name_fresh)
    have eq: "rewrite (And \<alpha> (Release \<beta> I \<gamma>)) t = Frz ?q (rewrite \<alpha> Same) (And (rewrite \<alpha> Same)
      (Release (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same) I (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<gamma>) Same)))"
      using True by (simp add: Let_def)
    have "progress \<sigma> P (project (rewrite (And \<alpha> (Release \<beta> I \<gamma>)) t)) j =
      min (progress \<sigma> P (project (rewrite \<alpha> Same)) j) (progress \<sigma> ?P (Formula.Release
        (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)) I (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<gamma>) Same))) j)"
      unfolding eq by (subst progress_frz_and_rw[OF P]) (simp_all add: frz_name_fresh)
    also have "\<dots> = progress \<sigma> P (project (fix_r (And \<alpha> (Release \<beta> I \<gamma>)) t)) j"
      using progress_Release_cong[OF h1 h2, of I] "2.IH"(1)[OF True P] by simp
    finally show ?thesis .
  next
    case False
    then have eq: "rewrite (And \<alpha> (Release \<beta> I \<gamma>)) t =
      And (rewrite \<alpha> Same) (Release (rewrite \<beta> Same) I (rewrite \<gamma> Same))"
      by (simp add: Let_def)
    show ?thesis
      unfolding eq using "2.IH"(4)[OF False P] "2.IH"(5)[OF False refl P] "2.IH"(6)[OF False refl refl P]
        progress_release_safe_bounded_cong[OF "2.IH"(5)[OF False refl P] "2.IH"(6)[OF False refl refl P], of I]
      by simp
  qed
next
  case (3 \<alpha> \<beta> I \<gamma> t)
  note P = "3.prems"
  show ?case
  proof (cases "prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>")
    case True
    let ?q = "frz_name [\<alpha>, \<beta>, \<gamma>]"
    let ?P = "P((?q, nfv \<alpha>) \<mapsto> j)"
    have h1: "progress \<sigma> ?P (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)) j = progress \<sigma> P (project \<beta>) j"
      by (rule progress_frz_ih[OF P _ "3.IH"(2)[OF True refl refl refl]]) (simp add: frz_name_fresh)
    have h2: "progress \<sigma> ?P (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<gamma>) Same)) j = progress \<sigma> P (project \<gamma>) j"
      by (rule progress_frz_ih[OF P _ "3.IH"(3)[OF True refl refl refl]]) (simp add: frz_name_fresh)
    have eq: "rewrite (And \<alpha> (Trigger \<beta> I \<gamma>)) t = Frz ?q (rewrite \<alpha> Same) (And (rewrite \<alpha> Same)
      (Trigger (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same) I (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<gamma>) Same)))"
      using True by (simp add: Let_def)
    have "progress \<sigma> P (project (rewrite (And \<alpha> (Trigger \<beta> I \<gamma>)) t)) j =
      min (progress \<sigma> P (project (rewrite \<alpha> Same)) j) (progress \<sigma> ?P (Formula.Trigger
        (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)) I (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<gamma>) Same))) j)"
      unfolding eq by (subst progress_frz_and_rw[OF P]) (simp_all add: frz_name_fresh)
    also have "\<dots> = progress \<sigma> P (project (fix_r (And \<alpha> (Trigger \<beta> I \<gamma>)) t)) j"
      using h1 h2 "3.IH"(1)[OF True P] by simp
    finally show ?thesis .
  next
    case False
    then have eq: "rewrite (And \<alpha> (Trigger \<beta> I \<gamma>)) t =
      And (rewrite \<alpha> Same) (Trigger (rewrite \<beta> Same) I (rewrite \<gamma> Same))"
      by (simp add: Let_def)
    show ?thesis
      unfolding eq using "3.IH"(4)[OF False P] "3.IH"(5)[OF False refl P] "3.IH"(6)[OF False refl refl P]
      by simp
  qed
next
  case (4 \<alpha> k \<beta> t)
  then show ?case
    by (cases "prop_cond \<alpha> \<beta>") (auto simp: project_shift[symmetric])
next
  case (6 \<alpha> \<beta> I \<gamma> t)
  note P = "6.prems"
  let ?q = "frz_name [\<alpha>, \<beta>, \<gamma>]"
  let ?P = "P((?q, nfv \<alpha>) \<mapsto> j)"
  consider (a) "prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>"
    | (b) "\<not> (prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>)" "prop_cond \<alpha> \<gamma> \<and> frz_ok \<alpha>"
    | (c) "\<not> (prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>)" "\<not> (prop_cond \<alpha> \<gamma> \<and> frz_ok \<alpha>)"
    by blast
  then show ?case
  proof cases
    case a
    have h1: "progress \<sigma> ?P (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)) j = progress \<sigma> P (project \<beta>) j"
      by (rule progress_frz_ih[OF P _ "6.IH"(2)[OF a refl refl refl]]) (simp add: frz_name_fresh)
    have h2: "progress \<sigma> ?P (project (rewrite \<gamma> Same)) j = progress \<sigma> P (project \<gamma>) j"
      using "6.IH"(3)[OF a refl refl refl P] by (simp add: frz_name_fresh)
    have eq: "rewrite (And \<alpha> (Since \<beta> I \<gamma>)) t = Frz ?q (rewrite \<alpha> Same) (And (rewrite \<alpha> Same)
      (Since (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same) I (rewrite \<gamma> Same)))"
      using a by (simp add: Let_def)
    have "progress \<sigma> P (project (rewrite (And \<alpha> (Since \<beta> I \<gamma>)) t)) j =
      min (progress \<sigma> P (project (rewrite \<alpha> Same)) j) (progress \<sigma> ?P (Formula.Since
        (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)) I (project (rewrite \<gamma> Same))) j)"
      unfolding eq by (subst progress_frz_and_rw[OF P]) (simp_all add: frz_name_fresh)
    also have "\<dots> = progress \<sigma> P (project (fix_r (And \<alpha> (Since \<beta> I \<gamma>)) t)) j"
      using h1 h2 "6.IH"(1)[OF a P] by simp
    finally show ?thesis .
  next
    case b
    have h1: "progress \<sigma> ?P (project (rewrite \<beta> Same)) j = progress \<sigma> P (project \<beta>) j"
      using "6.IH"(5)[OF b refl refl refl P] by (simp add: frz_name_fresh)
    have h2: "progress \<sigma> ?P (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<gamma>) Same)) j = progress \<sigma> P (project \<gamma>) j"
      by (rule progress_frz_ih[OF P _ "6.IH"(6)[OF b refl refl refl]]) (simp add: frz_name_fresh)
    have eq: "rewrite (And \<alpha> (Since \<beta> I \<gamma>)) t = Frz ?q (rewrite \<alpha> Same) (And (rewrite \<alpha> Same)
      (Since (rewrite \<beta> Same) I (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<gamma>) Same)))"
      using b by (simp add: Let_def)
    have "progress \<sigma> P (project (rewrite (And \<alpha> (Since \<beta> I \<gamma>)) t)) j =
      min (progress \<sigma> P (project (rewrite \<alpha> Same)) j) (progress \<sigma> ?P (Formula.Since
        (project (rewrite \<beta> Same)) I (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<gamma>) Same))) j)"
      unfolding eq by (subst progress_frz_and_rw[OF P]) (simp_all add: frz_name_fresh)
    also have "\<dots> = progress \<sigma> P (project (fix_r (And \<alpha> (Since \<beta> I \<gamma>)) t)) j"
      using h1 h2 "6.IH"(4)[OF b P] by simp
    finally show ?thesis .
  next
    case c
    then have eq: "rewrite (And \<alpha> (Since \<beta> I \<gamma>)) t =
      And (rewrite \<alpha> Same) (Since (rewrite \<beta> Same) I (rewrite \<gamma> Same))"
      by (simp add: Let_def)
    show ?thesis
      unfolding eq using "6.IH"(7)[OF c P] "6.IH"(8)[OF c refl P] "6.IH"(9)[OF c refl refl P]
      by simp
  qed
next
  case (7 \<alpha> \<beta> I \<gamma> t)
  note P = "7.prems"
  let ?q = "frz_name [\<alpha>, \<beta>, \<gamma>]"
  let ?P = "P((?q, nfv \<alpha>) \<mapsto> j)"
  consider (a) "prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>"
    | (b) "\<not> (prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>)" "prop_cond \<alpha> \<gamma> \<and> frz_ok \<alpha>"
    | (c) "\<not> (prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>)" "\<not> (prop_cond \<alpha> \<gamma> \<and> frz_ok \<alpha>)"
    by blast
  then show ?case
  proof cases
    case a
    have h1: "progress \<sigma> ?P (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)) j = progress \<sigma> P (project \<beta>) j"
      by (rule progress_frz_ih[OF P _ "7.IH"(2)[OF a refl refl refl]]) (simp add: frz_name_fresh)
    have h2: "progress \<sigma> ?P (project (rewrite \<gamma> Same)) j = progress \<sigma> P (project \<gamma>) j"
      using "7.IH"(3)[OF a refl refl refl P] by (simp add: frz_name_fresh)
    have eq: "rewrite (And \<alpha> (Until \<beta> I \<gamma>)) t = Frz ?q (rewrite \<alpha> Same) (And (rewrite \<alpha> Same)
      (Until (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same) I (rewrite \<gamma> Same)))"
      using a by (simp add: Let_def)
    have "progress \<sigma> P (project (rewrite (And \<alpha> (Until \<beta> I \<gamma>)) t)) j =
      min (progress \<sigma> P (project (rewrite \<alpha> Same)) j) (progress \<sigma> ?P (Formula.Until
        (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)) I (project (rewrite \<gamma> Same))) j)"
      unfolding eq by (subst progress_frz_and_rw[OF P]) (simp_all add: frz_name_fresh)
    also have "\<dots> = progress \<sigma> P (project (fix_r (And \<alpha> (Until \<beta> I \<gamma>)) t)) j"
      using h1 h2 "7.IH"(1)[OF a P] by simp
    finally show ?thesis .
  next
    case b
    have h1: "progress \<sigma> ?P (project (rewrite \<beta> Same)) j = progress \<sigma> P (project \<beta>) j"
      using "7.IH"(5)[OF b refl refl refl P] by (simp add: frz_name_fresh)
    have h2: "progress \<sigma> ?P (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<gamma>) Same)) j = progress \<sigma> P (project \<gamma>) j"
      by (rule progress_frz_ih[OF P _ "7.IH"(6)[OF b refl refl refl]]) (simp add: frz_name_fresh)
    have eq: "rewrite (And \<alpha> (Until \<beta> I \<gamma>)) t = Frz ?q (rewrite \<alpha> Same) (And (rewrite \<alpha> Same)
      (Until (rewrite \<beta> Same) I (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<gamma>) Same)))"
      using b by (simp add: Let_def)
    have "progress \<sigma> P (project (rewrite (And \<alpha> (Until \<beta> I \<gamma>)) t)) j =
      min (progress \<sigma> P (project (rewrite \<alpha> Same)) j) (progress \<sigma> ?P (Formula.Until
        (project (rewrite \<beta> Same)) I (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<gamma>) Same))) j)"
      unfolding eq by (subst progress_frz_and_rw[OF P]) (simp_all add: frz_name_fresh)
    also have "\<dots> = progress \<sigma> P (project (fix_r (And \<alpha> (Until \<beta> I \<gamma>)) t)) j"
      using h1 h2 "7.IH"(4)[OF b P] by simp
    finally show ?thesis .
  next
    case c
    then have eq: "rewrite (And \<alpha> (Until \<beta> I \<gamma>)) t =
      And (rewrite \<alpha> Same) (Until (rewrite \<beta> Same) I (rewrite \<gamma> Same))"
      by (simp add: Let_def)
    show ?thesis
      unfolding eq using "7.IH"(7)[OF c P] "7.IH"(8)[OF c refl P] "7.IH"(9)[OF c refl refl P]
      by simp
  qed
next
  case (8 \<alpha> I \<beta> t)
  note P = "8.prems"
  show ?case
  proof (cases "prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>")
    case True
    let ?q = "frz_name [\<alpha>, \<beta>]"
    let ?P = "P((?q, nfv \<alpha>) \<mapsto> j)"
    have h1: "progress \<sigma> ?P (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)) j = progress \<sigma> P (project \<beta>) j"
      by (rule progress_frz_ih[OF P _ "8.IH"(2)[OF True refl refl refl]]) (simp add: frz_name_fresh)
    have eq: "rewrite (And \<alpha> (Once I \<beta>)) t = Frz ?q (rewrite \<alpha> Same) (And (rewrite \<alpha> Same)
      (Once I (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)))"
      using True by (simp add: Let_def)
    have "progress \<sigma> P (project (rewrite (And \<alpha> (Once I \<beta>)) t)) j =
      min (progress \<sigma> P (project (rewrite \<alpha> Same)) j) (progress \<sigma> ?P (once I
        (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same))) j)"
      unfolding eq by (subst progress_frz_and_rw[OF P]) (simp_all add: frz_name_fresh)
    also have "\<dots> = progress \<sigma> P (project (fix_r (And \<alpha> (Once I \<beta>)) t)) j"
      using h1 "8.IH"(1)[OF True P] by (simp add: once_def)
    finally show ?thesis .
  next
    case False
    then have eq: "rewrite (And \<alpha> (Once I \<beta>)) t = And (rewrite \<alpha> Same) (Once I (rewrite \<beta> Same))"
      by (simp add: Let_def)
    show ?thesis
      unfolding eq using "8.IH"(3)[OF False P] "8.IH"(4)[OF False refl P]
      by (simp add: once_def)
  qed
next
  case (9 \<alpha> I \<beta> t)
  note P = "9.prems"
  show ?case
  proof (cases "prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>")
    case True
    let ?q = "frz_name [\<alpha>, \<beta>]"
    let ?P = "P((?q, nfv \<alpha>) \<mapsto> j)"
    have h1: "progress \<sigma> ?P (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)) j = progress \<sigma> P (project \<beta>) j"
      by (rule progress_frz_ih[OF P _ "9.IH"(2)[OF True refl refl refl]]) (simp add: frz_name_fresh)
    have eq: "rewrite (And \<alpha> (Eventually I \<beta>)) t = Frz ?q (rewrite \<alpha> Same) (And (rewrite \<alpha> Same)
      (Eventually I (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)))"
      using True by (simp add: Let_def)
    have "progress \<sigma> P (project (rewrite (And \<alpha> (Eventually I \<beta>)) t)) j =
      min (progress \<sigma> P (project (rewrite \<alpha> Same)) j) (progress \<sigma> ?P (Formula.eventually I
        (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same))) j)"
      unfolding eq by (subst progress_frz_and_rw[OF P]) (simp_all add: frz_name_fresh)
    also have "\<dots> = progress \<sigma> P (project (fix_r (And \<alpha> (Eventually I \<beta>)) t)) j"
      using h1 "9.IH"(1)[OF True P] by (simp add: eventually_def)
    finally show ?thesis .
  next
    case False
    then have eq: "rewrite (And \<alpha> (Eventually I \<beta>)) t = And (rewrite \<alpha> Same) (Eventually I (rewrite \<beta> Same))"
      by (simp add: Let_def)
    show ?thesis
      unfolding eq using "9.IH"(3)[OF False P] "9.IH"(4)[OF False refl P]
      by (simp add: eventually_def)
  qed
next
  case (10 \<alpha> I \<beta> t)
  note P = "10.prems"
  show ?case
  proof (cases "prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>")
    case True
    let ?q = "frz_name [\<alpha>, \<beta>]"
    let ?P = "P((?q, nfv \<alpha>) \<mapsto> j)"
    have h1: "progress \<sigma> ?P (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)) j = progress \<sigma> P (project \<beta>) j"
      by (rule progress_frz_ih[OF P _ "10.IH"(2)[OF True refl refl refl]]) (simp add: frz_name_fresh)
    have eq: "rewrite (And \<alpha> (Historically I \<beta>)) t = Frz ?q (rewrite \<alpha> Same) (And (rewrite \<alpha> Same)
      (Historically I (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)))"
      using True by (simp add: Let_def)
    have "progress \<sigma> P (project (rewrite (And \<alpha> (Historically I \<beta>)) t)) j =
      min (progress \<sigma> P (project (rewrite \<alpha> Same)) j) (progress \<sigma> ?P (historically I
        (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same))) j)"
      unfolding eq by (subst progress_frz_and_rw[OF P]) (simp_all add: frz_name_fresh)
    also have "\<dots> = progress \<sigma> P (project (fix_r (And \<alpha> (Historically I \<beta>)) t)) j"
      using h1 "10.IH"(1)[OF True P] by (simp add: historically_def once_def)
    finally show ?thesis .
  next
    case False
    then have eq: "rewrite (And \<alpha> (Historically I \<beta>)) t = And (rewrite \<alpha> Same) (Historically I (rewrite \<beta> Same))"
      by (simp add: Let_def)
    show ?thesis
      unfolding eq using "10.IH"(3)[OF False P] "10.IH"(4)[OF False refl P]
      by (simp add: historically_def once_def)
  qed
next
  case (11 \<alpha> I \<beta> t)
  note P = "11.prems"
  show ?case
  proof (cases "prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>")
    case True
    let ?q = "frz_name [\<alpha>, \<beta>]"
    let ?P = "P((?q, nfv \<alpha>) \<mapsto> j)"
    have h1: "progress \<sigma> ?P (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)) j = progress \<sigma> P (project \<beta>) j"
      by (rule progress_frz_ih[OF P _ "11.IH"(2)[OF True refl refl refl]]) (simp add: frz_name_fresh)
    have eq: "rewrite (And \<alpha> (Always I \<beta>)) t = Frz ?q (rewrite \<alpha> Same) (And (rewrite \<alpha> Same)
      (Always I (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)))"
      using True by (simp add: Let_def)
    have "progress \<sigma> P (project (rewrite (And \<alpha> (Always I \<beta>)) t)) j =
      min (progress \<sigma> P (project (rewrite \<alpha> Same)) j) (progress \<sigma> ?P (always I
        (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same))) j)"
      unfolding eq by (subst progress_frz_and_rw[OF P]) (simp_all add: frz_name_fresh)
    also have "\<dots> = progress \<sigma> P (project (fix_r (And \<alpha> (Always I \<beta>)) t)) j"
      using h1 "11.IH"(1)[OF True P] by (simp add: always_def eventually_def)
    finally show ?thesis .
  next
    case False
    then have eq: "rewrite (And \<alpha> (Always I \<beta>)) t = And (rewrite \<alpha> Same) (Always I (rewrite \<beta> Same))"
      by (simp add: Let_def)
    show ?thesis
      unfolding eq using "11.IH"(3)[OF False P] "11.IH"(4)[OF False refl P]
      by (simp add: always_def eventually_def)
  qed
next
  case (12 \<alpha> I \<beta> t)
  from "12.IH"(1-4)[OF _ "12.prems"] "12.IH"(5)[OF _ refl "12.prems"] show ?case
    by (cases "prop_cond \<alpha> \<beta>") auto
next
  case (13 \<alpha> I \<beta> t)
  from "13.IH"(1-4)[OF _ "13.prems"] "13.IH"(5)[OF _ refl "13.prems"] show ?case
    using progress_le_gen[OF "13.prems", of \<sigma> "project \<alpha>"] progress_le_gen[OF "13.prems", of \<sigma> "project \<beta>"]
    by (cases "prop_cond \<alpha> \<beta>") (auto simp: min_def not_le less_Suc_eq)
next
  case (14 \<alpha> \<gamma> I \<beta> t)
  note P = "14.prems"
  let ?q = "frz_name [\<alpha>, \<gamma>, \<beta>]"
  have L: "progress \<sigma> (P((?q, n) \<mapsto> x)) (project (rewrite (And \<alpha> \<gamma>) Same)) j =
    min (progress \<sigma> P (project \<alpha>) j) (progress \<sigma> P (project \<gamma>) j)" for n x
    using "14.IH"(1)[OF P] by (simp add: frz_name_fresh)
  consider (a) "t = Same \<and> \<not> mem I 0 \<and> prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>"
    | (b) "\<not> (t = Same \<and> \<not> mem I 0 \<and> prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>)"
      "t = Same \<and> \<not> mem I 0 \<and> prop_cond \<gamma> \<beta> \<and> frz_ok \<gamma>"
    | (c) "\<not> (t = Same \<and> \<not> mem I 0 \<and> prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>)"
      "\<not> (t = Same \<and> \<not> mem I 0 \<and> prop_cond \<gamma> \<beta> \<and> frz_ok \<gamma>)"
    by blast
  then show ?case
  proof cases
    case a
    let ?P = "P((?q, nfv \<alpha>) \<mapsto> j)"
    have h1: "progress \<sigma> ?P (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)) j = progress \<sigma> P (project \<beta>) j"
      by (rule progress_frz_ih[OF P _ "14.IH"(3)[OF refl a refl refl]]) (simp add: frz_name_fresh)
    have h\<alpha>: "progress \<sigma> P (project (rewrite \<alpha> Same)) j = progress \<sigma> P (project \<alpha>) j"
      using "14.IH"(2)[OF refl a refl refl P] by simp
    have eq: "rewrite (Since (And \<alpha> \<gamma>) I \<beta>) t = Frz ?q (rewrite \<alpha> Same)
      (Since (rewrite (And \<alpha> \<gamma>) Same) I (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same))"
      using a by (simp add: Let_def)
    have "progress \<sigma> P (project (rewrite (Since (And \<alpha> \<gamma>) I \<beta>) t)) j =
      progress \<sigma> ?P (Formula.Since (project (rewrite (And \<alpha> \<gamma>) Same)) I
        (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same))) j"
      unfolding eq project.simps
      by (rule progress_Frz_eq[OF P, where \<alpha>="project (rewrite \<alpha> Same)", unfolded nfv_project nfv_rewrite]) (simp_all add: L h\<alpha>)
    also have "\<dots> = progress \<sigma> P (project (fix_r (Since (And \<alpha> \<gamma>) I \<beta>) t)) j"
      using a L h1 by simp
    finally show ?thesis .
  next
    case b
    let ?P = "P((?q, nfv \<gamma>) \<mapsto> j)"
    have h1: "progress \<sigma> ?P (project (rewrite (And (frz_atom ?q (nfv \<gamma>)) \<beta>) Same)) j = progress \<sigma> P (project \<beta>) j"
      by (rule progress_frz_ih[OF P _ "14.IH"(5)[OF refl b refl refl]]) (simp add: frz_name_fresh)
    have h\<gamma>: "progress \<sigma> P (project (rewrite \<gamma> Same)) j = progress \<sigma> P (project \<gamma>) j"
      using "14.IH"(4)[OF refl b refl refl P] by simp
    have eq: "rewrite (Since (And \<alpha> \<gamma>) I \<beta>) t = Frz ?q (rewrite \<gamma> Same)
      (Since (rewrite (And \<alpha> \<gamma>) Same) I (rewrite (And (frz_atom ?q (nfv \<gamma>)) \<beta>) Same))"
      using b by (auto simp: Let_def)
    have "progress \<sigma> P (project (rewrite (Since (And \<alpha> \<gamma>) I \<beta>) t)) j =
      progress \<sigma> ?P (Formula.Since (project (rewrite (And \<alpha> \<gamma>) Same)) I
        (project (rewrite (And (frz_atom ?q (nfv \<gamma>)) \<beta>) Same))) j"
      unfolding eq project.simps
      by (rule progress_Frz_eq[OF P, where \<alpha>="project (rewrite \<gamma> Same)", unfolded nfv_project nfv_rewrite]) (simp_all add: L h\<gamma>)
    also have "\<dots> = progress \<sigma> P (project (fix_r (Since (And \<alpha> \<gamma>) I \<beta>) t)) j"
      using b L h1 by simp
    finally show ?thesis .
  next
    case c
    have le: "progress \<sigma> P (project \<alpha>) j \<le> j" "progress \<sigma> P (project \<gamma>) j \<le> j"
      by (rule progress_le_gen[OF P])+
    show ?thesis
      using c "14.IH"(1)[OF P] "14.IH"(6)[OF refl c _ P] "14.IH"(7)[OF refl c _ _ P] "14.IH"(8)[OF refl c _ _ P] le
      by (cases t) (auto simp: Let_def once_def min_def split: if_splits)
  qed
next
  case (15 \<alpha> \<gamma> I \<beta> t)
  note P = "15.prems"
  have le: "progress \<sigma> P (project \<alpha>) j \<le> j" "progress \<sigma> P (project \<gamma>) j \<le> j"
    by (rule progress_le_gen[OF P])+
  let ?a = "progress \<sigma> P (project \<alpha>) j" and ?b = "progress \<sigma> P (project \<beta>) j"
    and ?c = "progress \<sigma> P (project \<gamma>) j"
  define r where "r = (if t = Same \<and> \<not> mem I 0 \<and> prop_cond \<alpha> \<beta> then rewrite (And (Once I \<alpha>) \<beta>) Same
    else if t = Same \<and> \<not> mem I 0 \<and> prop_cond \<gamma> \<beta> then rewrite (And (Once I \<gamma>) \<beta>) Same
    else rewrite \<beta> Same)"
  have eq: "rewrite (Until (And \<alpha> \<gamma>) I \<beta>) t = fix_r (Until (rewrite (And \<alpha> \<gamma>) Same) I r) t"
    by (simp add: r_def Let_def)
  have L: "progress \<sigma> P (project (rewrite (And \<alpha> \<gamma>) Same)) j = min ?a ?c"
    using "15.IH"(1)[OF P] by simp
  have R: "min (min ?a ?c) (progress \<sigma> P (project r) j) = min (min ?a ?c) ?b"
  proof (cases "t = Same \<and> \<not> mem I 0 \<and> prop_cond \<alpha> \<beta>")
    case True
    then show ?thesis
      using "15.IH"(2)[OF refl True P] le by (simp add: r_def once_def min_def)
  next
    case False
    show ?thesis
    proof (cases "t = Same \<and> \<not> mem I 0 \<and> prop_cond \<gamma> \<beta>")
      case True
      then show ?thesis
        using "15.IH"(3)[OF refl False True P] False le by (simp add: r_def once_def min_def)
    next
      case False': False
      have "r = rewrite \<beta> Same"
        by (simp only: r_def if_not_P[OF False] if_not_P[OF False'])
      then show ?thesis
        using "15.IH"(4)[OF refl False False' P] by simp
    qed
  qed
  show ?case
  proof (cases t)
    case Same
    show ?thesis
      unfolding eq unfolding Same fix_r.simps project.simps
      by (rule progress_Until_cong) (simp add: L R)
  next
    case Swapped
    show ?thesis
      unfolding eq unfolding Swapped fix_r.simps project.simps
      by (rule progress_Until_cong) (use R in \<open>simp add: L min.commute min.left_commute min.assoc\<close>)
  qed
next
  case (27 \<phi> I \<psi> t)
  then show ?case
    using "27.IH"(1)[OF "27.prems"] "27.IH"(2)[OF "27.prems"]
      progress_release_safe_bounded_cong[OF "27.IH"(1)[OF "27.prems"] "27.IH"(2)[OF "27.prems"], of I]
    by simp
qed (auto simp: once_def always_def eventually_def historically_def
    progress_regex_def regex.set_map image_image)

lemma progress_rrewrite: "pred_mapping (\<lambda>x. x \<le> j) P \<Longrightarrow> progress \<sigma> P (rrewrite \<phi>) j = progress \<sigma> P \<phi> j"
  by (simp add: rrewrite_def progress_rewrite project_embed)

(* Proofs that the conversion into multi-way joins preserves well-typedness and the specification *)

lemma wty_get_and_list: "S, E \<turnstile> \<phi> \<Longrightarrow> \<psi> \<in> set (get_and_list \<phi>) \<Longrightarrow> S, E \<turnstile> \<psi>"
  by (induction \<phi> rule: get_and_list.induct) (auto split: if_splits)

lemma wty_Ands_get_and_list:
  "S, E \<turnstile> \<alpha> \<Longrightarrow> S, E \<turnstile> \<beta> \<Longrightarrow> S, E \<turnstile> Formula.Ands (get_and_list \<alpha> @ get_and_list \<beta>)"
  by (auto intro!: wty_formula.Ands dest: wty_get_and_list)

lemma wty_Ands_Cons_get_and_list:
  "S, E \<turnstile> \<alpha> \<Longrightarrow> S, E \<turnstile> \<beta> \<Longrightarrow> S, E \<turnstile> Formula.Ands (\<alpha> # get_and_list \<beta>)"
  by (auto intro!: wty_formula.Ands dest: wty_get_and_list)

lemma wty_release_safe_0: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> \<psi> \<Longrightarrow> S, E \<turnstile> release_safe_0 \<phi> I \<psi>"
  by (auto simp: release_safe_0_def always_safe_0_def intro!: wty_formula.intros)

lemma wty_release_safe_bounded: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> \<psi> \<Longrightarrow> S, E \<turnstile> release_safe_bounded \<phi> I \<psi>"
  by (auto simp: release_safe_bounded_def always_safe_bounded_def Formula.eventually_def once_def
      intro!: wty_formula.intros)

lemma wty_and_release_safe_bounded:
  "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> \<phi>' \<Longrightarrow> S, E \<turnstile> \<psi>' \<Longrightarrow> S, E \<turnstile> and_release_safe_bounded \<phi> \<phi>' I \<psi>'"
  by (auto simp: and_release_safe_bounded_def Formula.eventually_def
      intro!: wty_formula.intros wty_release_safe_bounded)

lemma wty_convert_multiway: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> convert_multiway \<phi>"
proof (induction \<phi> arbitrary: S E rule: measure_induct_rule[of size'])
  case (less \<phi>)
  note IH = less.IH
  show ?case
    using less.prems
  proof (cases \<phi>)
    case (And \<alpha> \<beta>)
    from less.prems have w\<alpha>: "S, E \<turnstile> \<alpha>" and w\<beta>: "S, E \<turnstile> \<beta>"
      by (auto simp: And)
    have c\<alpha>: "S, E \<turnstile> convert_multiway \<alpha>"
      by (rule IH[OF _ w\<alpha>]) (unfold And, rule size'_Or(1))
    have c\<beta>: "S, E \<turnstile> convert_multiway \<beta>"
      by (rule IH[OF _ w\<beta>]) (unfold And, rule size'_Or(2))
    have cr: "S, E \<turnstile> convert_multiway (and_release_safe_bounded \<alpha> \<phi>' I \<psi>')"
      if \<beta>: "\<beta> = Formula.Release \<phi>' I \<psi>'" for \<phi>' I \<psi>'
    proof (rule IH)
      show "size' (and_release_safe_bounded \<alpha> \<phi>' I \<psi>') < size' \<phi>"
        using size'_and_release[of \<alpha> \<phi>' I \<psi>'] by (simp add: And \<beta>)
      show "S, E \<turnstile> and_release_safe_bounded \<alpha> \<phi>' I \<psi>'"
        using w\<alpha> w\<beta> by (auto simp: \<beta> intro!: wty_and_release_safe_bounded)
    qed
    show ?thesis
    proof (cases "\<exists>\<phi>' I \<psi>'. \<beta> = Formula.Release \<phi>' I \<psi>'")
      case True
      then obtain \<phi>' I \<psi>' where \<beta>: "\<beta> = Formula.Release \<phi>' I \<psi>'"
        by blast
      show ?thesis
        using c\<alpha> c\<beta> cr[OF \<beta>] w\<beta> unfolding And \<beta>
        by (auto intro!: wty_formula.And wty_formula.Release wty_Ands_get_and_list
            wty_Ands_Cons_get_and_list)
    next
      case False
      then have nr: "(case \<beta> of Formula.Release \<phi>' I \<psi>' \<Rightarrow> True | _ \<Rightarrow> False) = False"
        by (cases \<beta>) auto
      show ?thesis
        using c\<alpha> c\<beta> w\<beta> unfolding And
        by (auto simp: nr intro!: wty_formula.And wty_Ands_get_and_list wty_Ands_Cons_get_and_list)
    qed
  next
    case (Release \<alpha> I \<beta>)
    from less.prems have w\<alpha>: "S, E \<turnstile> \<alpha>" and w\<beta>: "S, E \<turnstile> \<beta>"
      by (auto simp: Release)
    have "S, E \<turnstile> convert_multiway (release_safe_0 \<alpha> I \<beta>)"
      by (rule IH[OF _ wty_release_safe_0[OF w\<alpha> w\<beta>]])
        (use size'_Release[of \<alpha> I \<beta>] in \<open>simp add: Release\<close>)
    moreover have "S, E \<turnstile> convert_multiway (release_safe_bounded \<alpha> I \<beta>)"
      by (rule IH[OF _ wty_release_safe_bounded[OF w\<alpha> w\<beta>]])
        (use size'_Release[of \<alpha> I \<beta>] in \<open>simp add: Release\<close>)
    ultimately show ?thesis
      by (simp add: Release)
  next
    case (Ands \<phi>s)
    have "S, E \<turnstile> convert_multiway \<chi>" if "\<chi> \<in> set \<phi>s" for \<chi>
    proof (rule IH)
      show "size' \<chi> < size' \<phi>"
        using sum_list_mem_leq[OF that, of size'] by (simp add: Ands)
      show "S, E \<turnstile> \<chi>"
        using less.prems that by (auto simp: Ands)
    qed
    then show ?thesis
      by (auto simp: Ands intro!: wty_formula.Ands)
  next
    case (MatchP I r)
    have sz: "size' \<chi> < size' \<phi>" if "\<chi> \<in> regex.atms r" for \<chi>
      using regex_atms_size'[OF that] by (simp add: MatchP)
    have "Regex.pred_regex (\<lambda>\<chi>. S, E \<turnstile> convert_multiway \<chi>) r"
      using less.prems by (auto simp: MatchP elim!: regex.pred_mono_strong intro: IH[OF sz])
    then show ?thesis
      by (auto simp: MatchP regex.pred_map comp_def intro!: wty_formula.MatchP)
  next
    case (MatchF I r)
    have sz: "size' \<chi> < size' \<phi>" if "\<chi> \<in> regex.atms r" for \<chi>
      using regex_atms_size'[OF that] by (simp add: MatchF)
    have "Regex.pred_regex (\<lambda>\<chi>. S, E \<turnstile> convert_multiway \<chi>) r"
      using less.prems by (auto simp: MatchF elim!: regex.pred_mono_strong intro: IH[OF sz])
    then show ?thesis
      by (auto simp: MatchF regex.pred_map comp_def intro!: wty_formula.MatchF)
  next
    case (Let p \<alpha> \<beta>)
    from less.prems obtain E' where w\<alpha>: "S, E' \<turnstile> \<alpha>"
      and w\<beta>: "S((p, Formula.nfv \<alpha>) \<mapsto> tabulate E' 0 (Formula.nfv \<alpha>)), E \<turnstile> \<beta>"
      by (auto simp: Let)
    have c\<alpha>: "S, E' \<turnstile> convert_multiway \<alpha>"
      by (rule IH[OF _ w\<alpha>]) (simp add: Let)
    have c\<beta>: "S((p, Formula.nfv \<alpha>) \<mapsto> tabulate E' 0 (Formula.nfv \<alpha>)), E \<turnstile> convert_multiway \<beta>"
      by (rule IH[OF _ w\<beta>]) (simp add: Let)
    show ?thesis
      unfolding Let convert_multiway.simps
      by (rule wty_formula.Let[where E'=E', OF c\<alpha>]) (simp add: nfv_convert_multiway c\<beta>)
  next
    case (Frz p \<alpha> \<beta>)
    from less.prems obtain E' where w\<alpha>: "S, E' \<turnstile> \<alpha>"
      and w\<beta>: "S((p, Formula.nfv \<alpha>) \<mapsto> tabulate E' 0 (Formula.nfv \<alpha>)), E \<turnstile> \<beta>"
      by (auto simp: Frz)
    have c\<alpha>: "S, E' \<turnstile> convert_multiway \<alpha>"
      by (rule IH[OF _ w\<alpha>]) (simp add: Frz)
    have c\<beta>: "S((p, Formula.nfv \<alpha>) \<mapsto> tabulate E' 0 (Formula.nfv \<alpha>)), E \<turnstile> convert_multiway \<beta>"
      by (rule IH[OF _ w\<beta>]) (simp add: Frz)
    show ?thesis
      unfolding Frz convert_multiway.simps
      by (rule wty_formula.Frz[where E'=E', OF c\<alpha>]) (simp add: nfv_convert_multiway c\<beta>)
  next
    case (LetPast p \<alpha> \<beta>)
    from less.prems obtain E' where
      w\<alpha>: "S((p, Formula.nfv \<alpha>) \<mapsto> tabulate E' 0 (Formula.nfv \<alpha>)), E' \<turnstile> \<alpha>"
      and w\<beta>: "S((p, Formula.nfv \<alpha>) \<mapsto> tabulate E' 0 (Formula.nfv \<alpha>)), E \<turnstile> \<beta>"
      by (auto simp: LetPast)
    have c\<alpha>: "S((p, Formula.nfv \<alpha>) \<mapsto> tabulate E' 0 (Formula.nfv \<alpha>)), E' \<turnstile> convert_multiway \<alpha>"
      by (rule IH[OF _ w\<alpha>]) (simp add: LetPast)
    have c\<beta>: "S((p, Formula.nfv \<alpha>) \<mapsto> tabulate E' 0 (Formula.nfv \<alpha>)), E \<turnstile> convert_multiway \<beta>"
      by (rule IH[OF _ w\<beta>]) (simp add: LetPast)
    show ?thesis
      unfolding LetPast convert_multiway.simps
      by (rule wty_formula.LetPast[where E'=E']) (simp_all add: nfv_convert_multiway c\<alpha> c\<beta>)
  qed (auto simp: nfv_convert_multiway intro!: wty_formula.intros intro: IH)
qed

lemma mmonitorable_convert_multiway: "mmonitorable \<phi> \<Longrightarrow> mmonitorable (convert_multiway \<phi>)"
  by (simp add: mmonitorable_def safe_convert_multiway future_bounded_convert_multiway)

lemma verimon_spec_convert_multiway:
  assumes "verimon_spec \<phi> S E"
  shows "verimon_spec (convert_multiway \<phi>) S E"
proof -
  interpret verimon_spec \<phi> S E by (fact assms)
  show ?thesis
    by unfold_locales (auto intro: wty_convert_multiway[OF well_typed] mmonitorable_convert_multiway[OF monitorable])
qed

(* Locales for correctness proofs *)

text \<open>The correctness of the preparation: whatever monitor evaluates the prepared formula
  @{text \<psi>}, it satisfies the specification of @{text \<psi>}, which coincides with that of the
  input formula. The locale does not depend on the auxiliary data structures of any monitor.\<close>

locale verimon_prepare =
  fixes rw sig \<phi>
  assumes wf: "wf_formula \<phi>" 
  and prepare_Inr: "\<not> sum.isl (prepare_verimon rw sig \<phi>)"
begin

definition "\<psi> = (THE \<psi>. prepare_verimon rw sig \<phi> = Inr \<psi>)"
definition "check_subst = (THE f. check sig TAny \<phi> = Inr f)"

lemma check_Inr: "\<exists>f. check sig TAny \<phi> = Inr f"
  using prepare_Inr unfolding prepare_verimon_def type_check_def
  by (simp add: bind_def split: sum.splits if_splits)

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

lemma verimon_spec_\<psi>:
  "verimon_spec \<psi> (map_sig (convert_tysym o check_subst) sig) (convert_tysym o check_subst o TAny)"
proof -
  let ?f = "convert_tysym o check_subst"
  let ?\<phi> = "Formula.formula.map_formula ?f \<phi>"
  have type_check: "type_check sig \<phi> = Inr ?\<phi>"
    using prepare_Inr check_check_subst
    by (auto simp: prepare_verimon_def type_check_def bind_def split: if_splits)
  have wty: "map_sig ?f sig, ?f o TAny \<turnstile> ?\<phi>"
    using check_sound_proven[OF check_check_subst wf] wf_f_check_subst wf_f_TCst_convert_tysym
    unfolding wty_result_fX_def by blast
  have \<psi>_cases: "\<psi> = ?\<phi> \<or> \<psi> = normalize ?\<phi> \<or> \<psi> = rrewrite (normalize ?\<phi>)"
    using prepare_\<psi> by (auto simp: prepare_verimon_def type_check Let_def split: if_splits)
  have "mmonitorable \<psi>"
    using prepare_\<psi> by (auto simp: prepare_verimon_def type_check Let_def monitorable_formula_code
      split: if_splits)
  moreover have "map_sig ?f sig, ?f o TAny \<turnstile> \<psi>"
    using \<psi>_cases by (elim disjE) (simp_all add: wty wty_normalize wty_rrewrite)
  ultimately show ?thesis
    by (intro verimon_spec.intro wty_mfodl.intro verimon_spec_axioms.intro)
qed

lemma future_bounded_\<phi>:
  "future_bounded_mfodl (Formula.formula.map_formula (convert_tysym \<circ> check_subst) \<phi>)
    (map_sig (convert_tysym o check_subst) sig) (convert_tysym o check_subst o TAny)"
proof -
  let ?f = "convert_tysym o check_subst"
  let ?\<phi> = "Formula.formula.map_formula ?f \<phi>"
  have type_check: "type_check sig \<phi> = Inr ?\<phi>"
    using prepare_Inr check_check_subst
    by (auto simp: prepare_verimon_def type_check_def bind_def split: if_splits)
  have "map_sig ?f sig, ?f o TAny \<turnstile> ?\<phi>"
    using check_sound_proven[OF check_check_subst wf] wf_f_check_subst wf_f_TCst_convert_tysym
    unfolding wty_result_fX_def by blast
  moreover have "Safety.future_bounded ?\<phi>"
  proof -
    have \<psi>_cases: "\<psi> = ?\<phi> \<or> \<psi> = normalize ?\<phi> \<or> \<psi> = rrewrite (normalize ?\<phi>)"
      using prepare_\<psi> by (auto simp: prepare_verimon_def type_check Let_def split: if_splits)
    have "mmonitorable \<psi>"
      using verimon_spec_\<psi> by (rule verimon_spec.monitorable)
    then have "Safety.future_bounded \<psi>"
      by (simp add: mmonitorable_def)
    with \<psi>_cases show ?thesis
      using future_bounded_normalize[OF future_bounded_rrewrite] future_bounded_normalize
      by auto
  qed
  ultimately show ?thesis
    by (intro future_bounded_mfodl.intro wty_mfodl.intro future_bounded_mfodl_axioms.intro)
qed

interpretation verimon_\<psi>: verimon_spec \<psi> "map_sig (convert_tysym o check_subst) sig" "convert_tysym o check_subst o TAny"
  using verimon_spec_\<psi> by (auto simp: verimon_spec_def verimon_spec_axioms_def wty_mfodl_def)

interpretation monitor_\<phi>: future_bounded_mfodl "Formula.formula.map_formula (convert_tysym \<circ> check_subst) \<phi>"
  "map_sig (convert_tysym o check_subst) sig" "convert_tysym o check_subst o TAny"
  using future_bounded_\<phi> by (auto simp: future_bounded_mfodl_def future_bounded_mfodl_axioms_def wty_mfodl_def)

lemma fvi_\<psi>: "Formula.fvi b \<psi> = Formula.fvi b \<phi>"
  using prepare_\<psi>[symmetric] unfolding prepare_verimon_def
  by (auto split: sum.splits if_splits simp: Let_def normalize_fvi rrewrite_fvi type_check_def check_check_subst)

lemma nfv_\<psi>: "Formula.nfv \<psi> = Formula.nfv \<phi>"
  using prepare_\<psi>[symmetric] unfolding prepare_verimon_def
  by (auto split: sum.splits if_splits simp: Let_def normalize_nfv rrewrite_nfv type_check_def check_check_subst)

lemma sat_\<psi>:
  "Formula.sat \<sigma> V v i \<psi> = Formula.sat \<sigma> V v i (Formula.formula.map_formula (convert_tysym \<circ> check_subst) \<phi>)"
  using prepare_\<psi>[symmetric] safe_\<psi> unfolding prepare_verimon_def
  by (auto split: sum.splits if_splits simp: Let_def final_sat normalize_sat type_check_def check_check_subst)

lemma pprogress_\<psi>: "pprogress \<psi> \<pi> = pprogress (Formula.formula.map_formula (convert_tysym \<circ> check_subst) \<phi>) \<pi>"
  using prepare_\<psi>[symmetric] unfolding pprogress_def unfolding prepare_verimon_def
  by (auto split: sum.splits if_splits simp: progress_normalize progress_rrewrite Let_def type_check_def check_check_subst)

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
    intro!: wf_mstate_minit wty_rrewrite wty_normalize dest!: spec[of _ "convert_tysym"])

(* Correctness of output of the monitor (verdicts of \phi is the output) *)
lemmas wf_mstate_minit = verimon_wf_mstate_minit
lemmas wf_mstate_mstep = wf_mstate_mstep
lemmas mstep_mverdicts = verimon_\<psi>.mstep_mverdicts[unfolded Mt_exchange]

end

end
