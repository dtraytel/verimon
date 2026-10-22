(*<*)
theory Frz_Rewrite
  imports "MFODL_Monitor.Monitor" "MFODL_Logic.Typing"
begin
(*>*)



section \<open>A frozen predicate lifted out of the temporal operators\<close>

text \<open>
  @{term "Formula.Frz p \<phi> \<psi>"} holds at a time point @{term i} if @{term \<psi>} does there with
  @{term p} interpreted, at every time point, as @{term \<phi>} is at @{term i}.  The monitor
  evaluates it by replaying @{term \<psi>} over the whole prefix once per time point, which is
  quadratic in the prefix.  Two rewrites avoid the replay in the common case.

  A frozen predicate does not change over time, so a conjunct of it under a temporal operator
  can be taken out: @{text "\<phi> S\<^sub>I (\<alpha> \<and> q)"} is @{text "q \<and> \<phi> S\<^sub>I \<alpha>"}, and likewise for
  Until and Next (@{text hoist}).  For a Since whose interval does not contain 0, and for Prev,
  the rewritten formula can have a smaller progress than the original, whose verdict at the
  first time point does not depend on the frozen predicate, when the frozen formula lags behind
  the prefix.  They are rewritten only when it cannot (@{text full_now}): a formula over the
  past operators and free predicates is known at every time point as soon as it arrives.  And once the
  frozen predicate occurs only at the current time point -- under no temporal operator --
  freezing it is the same as binding it with @{term Formula.Let} (@{text now_only}), which the
  monitor evaluates incrementally.  Both keep the satisfaction relation and the progress.
\<close>

subsection \<open>The rewrites\<close>

fun is_frz_pred :: "Formula.name \<times> nat \<Rightarrow> 't Formula.formula \<Rightarrow> bool" where
  "is_frz_pred pn (Formula.Pred e ts) = ((e, length ts) = pn)"
| "is_frz_pred pn _ = False"

text \<open>A conjunction with the frozen predicate as a conjunct, split into that conjunct and the rest;
  the front end makes a conjunction of more than two formulas a list.  Formulas have no
  executable equality -- their intervals have none -- so the conjunct is taken out of a list by
  its position rather than with @{const remove1}.  The conjunct is also found under an
  existential quantifier whose variable it does not mention; taken out of the quantifier, its
  variables are renumbered (@{text dec_trm}).\<close>

fun dec_trm :: "Formula.trm \<Rightarrow> Formula.trm" where
  "dec_trm (Formula.Var x) = Formula.Var (x - 1)"
| "dec_trm (Formula.Const c) = Formula.Const c"
| "dec_trm (Formula.Plus x y) = Formula.Plus (dec_trm x) (dec_trm y)"
| "dec_trm (Formula.Minus x y) = Formula.Minus (dec_trm x) (dec_trm y)"
| "dec_trm (Formula.UMinus x) = Formula.UMinus (dec_trm x)"
| "dec_trm (Formula.Mult x y) = Formula.Mult (dec_trm x) (dec_trm y)"
| "dec_trm (Formula.Div x y) = Formula.Div (dec_trm x) (dec_trm y)"
| "dec_trm (Formula.Mod x y) = Formula.Mod (dec_trm x) (dec_trm y)"
| "dec_trm (Formula.F2i x) = Formula.F2i (dec_trm x)"
| "dec_trm (Formula.I2f x) = Formula.I2f (dec_trm x)"

fun frz_find :: "Formula.name \<times> nat \<Rightarrow> 't Formula.formula list \<Rightarrow>
    ('t Formula.formula \<times> 't Formula.formula list) option" where
  "frz_find pn [] = None"
| "frz_find pn (x # xs) = (if is_frz_pred pn x then Some (x, xs) else
     (case frz_find pn xs of Some (q, ys) \<Rightarrow> Some (q, x # ys) | None \<Rightarrow> None))"

fun frz_split :: "Formula.name \<times> nat \<Rightarrow> 't Formula.formula \<Rightarrow>
    ('t Formula.formula \<times> 't Formula.formula) option" where
  "frz_split pn (Formula.And \<alpha> \<beta>) =
     (if is_frz_pred pn \<beta> then Some (\<beta>, \<alpha>) else if is_frz_pred pn \<alpha> then Some (\<alpha>, \<beta>) else None)"
| "frz_split pn (Formula.Ands l) = (case frz_find pn l of
     Some (q, r) \<Rightarrow> Some (q, Formula.Ands r) | None \<Rightarrow> None)"
| "frz_split pn (Formula.Exists t \<alpha>) = (case frz_split pn \<alpha> of
     Some (Formula.Pred e ts, \<beta>) \<Rightarrow> (if list_all (\<lambda>s. 0 \<notin> Formula.fv_trm s) ts
       then Some (Formula.Pred e (map dec_trm ts), Formula.Exists t \<beta>) else None)
   | _ \<Rightarrow> None)"
| "frz_split pn _ = None"

text \<open>The flag @{text fl} says that the frozen predicate is known at every time point of the
  prefix, i.e., that the frozen formula never lags behind (@{text full_now} below).  Then the
  conjunct is also taken out of a Since whose interval does not contain 0 and out of a Prev.\<close>

fun hoist :: "bool \<Rightarrow> Formula.name \<times> nat \<Rightarrow> 't Formula.formula \<Rightarrow> 't Formula.formula" where
  "hoist fl pn (Formula.Since \<phi> I \<psi>) = (let \<psi>' = hoist fl pn \<psi> in
     case (if memL I 0 \<or> fl then frz_split pn \<psi>' else None) of
       Some (q, \<alpha>) \<Rightarrow> Formula.And q (Formula.Since (hoist fl pn \<phi>) I \<alpha>)
     | None \<Rightarrow> Formula.Since (hoist fl pn \<phi>) I \<psi>')"
| "hoist fl pn (Formula.Until \<phi> I \<psi>) = (let \<psi>' = hoist fl pn \<psi> in
     case frz_split pn \<psi>' of
       Some (q, \<alpha>) \<Rightarrow> Formula.And q (Formula.Until (hoist fl pn \<phi>) I \<alpha>)
     | None \<Rightarrow> Formula.Until (hoist fl pn \<phi>) I \<psi>')"
| "hoist fl pn (Formula.Next I \<psi>) = (let \<psi>' = hoist fl pn \<psi> in
     case frz_split pn \<psi>' of
       Some (q, \<alpha>) \<Rightarrow> Formula.And q (Formula.Next I \<alpha>)
     | None \<Rightarrow> Formula.Next I \<psi>')"
| "hoist fl pn (Formula.Neg \<phi>) = Formula.Neg (hoist fl pn \<phi>)"
| "hoist fl pn (Formula.And \<phi> \<psi>) = Formula.And (hoist fl pn \<phi>) (hoist fl pn \<psi>)"
| "hoist fl pn (Formula.Or \<phi> \<psi>) = Formula.Or (hoist fl pn \<phi>) (hoist fl pn \<psi>)"
| "hoist fl pn (Formula.Ands l) = Formula.Ands (map (hoist fl pn) l)"
| "hoist fl pn (Formula.Exists t \<phi>) = (let \<phi>' = hoist fl pn \<phi> in
     case frz_split pn (Formula.Exists t \<phi>') of
       Some (q, \<alpha>) \<Rightarrow> Formula.And q \<alpha>
     | None \<Rightarrow> Formula.Exists t \<phi>')"
| "hoist fl pn (Formula.Agg y \<omega> tys f \<phi>) = Formula.Agg y \<omega> tys f (hoist fl pn \<phi>)"
| "hoist fl pn (Formula.Let e \<phi> \<psi>) =
     (if (e, Formula.nfv \<phi>) = pn then Formula.Let e \<phi> \<psi> else Formula.Let e \<phi> (hoist fl pn \<psi>))"
| "hoist fl pn (Formula.Prev I \<psi>) = (let \<psi>' = hoist fl pn \<psi> in
     case (if fl then frz_split pn \<psi>' else None) of
       Some (q, \<alpha>) \<Rightarrow> Formula.And q (Formula.Prev I \<alpha>)
     | None \<Rightarrow> Formula.Prev I \<psi>')"
| "hoist fl pn \<phi> = \<phi>"

fun now_only :: "Formula.name \<times> nat \<Rightarrow> 't Formula.formula \<Rightarrow> bool" where
  "now_only pn (Formula.Pred e ts) = True"
| "now_only pn (Formula.Neg \<phi>) = now_only pn \<phi>"
| "now_only pn (Formula.And \<phi> \<psi>) = (now_only pn \<phi> \<and> now_only pn \<psi>)"
| "now_only pn (Formula.Or \<phi> \<psi>) = (now_only pn \<phi> \<and> now_only pn \<psi>)"
| "now_only pn (Formula.Ands l) = (\<forall>\<phi> \<in> set l. now_only pn \<phi>)"
| "now_only pn (Formula.Exists t \<phi>) = now_only pn \<phi>"
| "now_only pn (Formula.Agg y \<omega> tys f \<phi>) = now_only pn \<phi>"
| "now_only pn (Formula.Let e \<phi> \<psi>) = (\<not> contains_pred pn (Formula.Let e \<phi> \<psi>) \<or>
     ((e, Formula.nfv \<phi>) \<noteq> pn \<and> \<not> contains_pred pn \<phi> \<and> now_only pn \<psi>))"
| "now_only pn \<phi> = (\<not> contains_pred pn \<phi>)"

text \<open>A formula that never lags: built from the past operators and the connectives over
  predicates none of which is bound by an enclosing @{const Formula.Let} or
  @{const Formula.Frz} (the list @{text B}), whose progress may lag.  Its progress is the whole
  prefix (@{text progress_full_now} below).\<close>

fun full_now :: "(Formula.name \<times> nat) list \<Rightarrow> 't Formula.formula \<Rightarrow> bool" where
  "full_now B (Formula.Pred e ts) = ((e, length ts) \<notin> set B)"
| "full_now B (Formula.Eq t1 t2) = True"
| "full_now B (Formula.Less t1 t2) = True"
| "full_now B (Formula.LessEq t1 t2) = True"
| "full_now B (Formula.Neg \<phi>) = full_now B \<phi>"
| "full_now B (Formula.And \<phi> \<psi>) = (full_now B \<phi> \<and> full_now B \<psi>)"
| "full_now B (Formula.Or \<phi> \<psi>) = (full_now B \<phi> \<and> full_now B \<psi>)"
| "full_now B (Formula.Ands l) = list_all (full_now B) l"
| "full_now B (Formula.Exists t \<phi>) = full_now B \<phi>"
| "full_now B (Formula.Agg y \<omega> tys f \<phi>) = full_now B \<phi>"
| "full_now B (Formula.Prev I \<phi>) = full_now B \<phi>"
| "full_now B (Formula.Since \<phi> I \<psi>) = (full_now B \<phi> \<and> full_now B \<psi>)"
| "full_now B _ = False"

fun frz_rw :: "(Formula.name \<times> nat) list \<Rightarrow> 't Formula.formula \<Rightarrow> 't Formula.formula" where
  "frz_rw B (Formula.Frz p \<phi> \<psi>) = (let pn = (p, Formula.nfv \<phi>); \<phi>' = frz_rw B \<phi>;
       \<psi>' = hoist (full_now B \<phi>') pn (frz_rw (pn # B) \<psi>) in
     if now_only pn \<psi>' then Formula.Let p \<phi>' \<psi>' else Formula.Frz p \<phi>' \<psi>')"
| "frz_rw B (Formula.Let p \<phi> \<psi>) =
     Formula.Let p (frz_rw B \<phi>) (frz_rw ((p, Formula.nfv \<phi>) # B) \<psi>)"
| "frz_rw B (Formula.Neg \<phi>) = Formula.Neg (frz_rw B \<phi>)"
| "frz_rw B (Formula.And \<phi> \<psi>) = Formula.And (frz_rw B \<phi>) (frz_rw B \<psi>)"
| "frz_rw B (Formula.Or \<phi> \<psi>) = Formula.Or (frz_rw B \<phi>) (frz_rw B \<psi>)"
| "frz_rw B (Formula.Ands l) = Formula.Ands (map (frz_rw B) l)"
| "frz_rw B (Formula.Exists t \<phi>) = Formula.Exists t (frz_rw B \<phi>)"
| "frz_rw B (Formula.Agg y \<omega> tys f \<phi>) = Formula.Agg y \<omega> tys f (frz_rw B \<phi>)"
| "frz_rw B (Formula.Prev I \<phi>) = Formula.Prev I (frz_rw B \<phi>)"
| "frz_rw B (Formula.Next I \<phi>) = Formula.Next I (frz_rw B \<phi>)"
| "frz_rw B (Formula.Since \<phi> I \<psi>) = Formula.Since (frz_rw B \<phi>) I (frz_rw B \<psi>)"
| "frz_rw B (Formula.Until \<phi> I \<psi>) = Formula.Until (frz_rw B \<phi>) I (frz_rw B \<psi>)"
| "frz_rw B \<phi> = \<phi>"
text \<open>The rewrite is applied only when its result is monitorable, so that safety need not be
  shown to be preserved: taking a conjunct out of a temporal operator can make its other operand
  unsafe.\<close>

definition frz_opt :: "ty Formula.formula \<Rightarrow> ty Formula.formula" where
  "frz_opt \<phi> = (let \<phi>' = frz_rw [] \<phi> in if mmonitorable_exec \<phi>' then \<phi>' else \<phi>)"

lemma frz_find_Some:
  "frz_find pn l = Some (q, r) \<Longrightarrow> is_frz_pred pn q \<and> set l = insert q (set r)"
  by (induct l arbitrary: r) (auto split: if_splits option.splits)

lemma wty_dec_trm: "case_nat t E \<turnstile> s :: ty \<Longrightarrow> 0 \<notin> Formula.fv_trm s \<Longrightarrow> E \<turnstile> dec_trm s :: ty"
proof (induct rule: wty_trm.induct)
  case (Var x ty)
  then show ?case
    by (cases x) (auto intro: wty_trm.Var)
qed (auto intro: wty_trm.intros)

lemma frz_split_Exists_Some:
  assumes "frz_split pn (Formula.Exists t \<alpha>) = Some (q, \<alpha>')"
  obtains e ts \<beta> where "frz_split pn \<alpha> = Some (Formula.Pred e ts, \<beta>)"
    "list_all (\<lambda>s. 0 \<notin> Formula.fv_trm s) ts" "q = Formula.Pred e (map dec_trm ts)"
    "\<alpha>' = Formula.Exists t \<beta>"
  using assms by (auto split: option.splits prod.splits formula.splits if_splits)

lemma frz_split_wty:
  "frz_split pn \<psi> = Some (q, r) \<Longrightarrow> S, E \<turnstile> \<psi> \<Longrightarrow> S, E \<turnstile> q \<and> S, E \<turnstile> r"
proof (induct pn \<psi> arbitrary: q r E rule: frz_split.induct)
  case (3 pn t \<alpha>)
  from 3(2) obtain e ts \<beta> where s: "frz_split pn \<alpha> = Some (Formula.Pred e ts, \<beta>)"
    "list_all (\<lambda>s. 0 \<notin> Formula.fv_trm s) ts" "q = Formula.Pred e (map dec_trm ts)"
    "r = Formula.Exists t \<beta>"
    by (rule frz_split_Exists_Some)
  from 3(3) have "S, case_nat t E \<turnstile> \<alpha>"
    by (rule wty_formula_ExistsD)
  with 3(1)[OF s(1)] have p: "S, case_nat t E \<turnstile> Formula.Pred e ts" and b: "S, case_nat t E \<turnstile> \<beta>"
    by blast+
  from p obtain tys where "S (e, length ts) = Some tys"
    "list_all2 (\<lambda>tm ty. case_nat t E \<turnstile> tm :: ty) ts tys"
    by (cases rule: wty_formula.cases) auto
  moreover have "E \<turnstile> dec_trm tm :: ty" if "tm \<in> set ts" "case_nat t E \<turnstile> tm :: ty" for tm ty
    using wty_dec_trm[OF that(2)] s(2) that(1) by (simp add: list_all_iff)
  ultimately have "S, E \<turnstile> q"
    using s(3) by (auto intro!: wty_formula.Pred simp: list.rel_map elim!: list.rel_mono_strong)
  then show ?case
    using b s(4) by (auto intro: wty_formula.Exists)
qed (auto split: if_splits option.splits dest!: frz_find_Some elim!: wty_formula.cases
  intro!: wty_formula.intros)

text \<open>Out of an existential quantifier the conjunct is taken whether or not a temporal operator
  follows: that is first-order reasoning, and the split already renumbers its variables.  The
  equation is not a simplification rule, so that the lemmas below see the two outcomes of the
  split rather than the split's own equations.\<close>

declare hoist.simps(8)[simp del]

lemma hoist_Exists_cases:
  obtains (None) "frz_split pn (Formula.Exists t (hoist fl pn \<phi>)) = None"
    "hoist fl pn (Formula.Exists t \<phi>) = Formula.Exists t (hoist fl pn \<phi>)"
  | (Some) q \<alpha> where "frz_split pn (Formula.Exists t (hoist fl pn \<phi>)) = Some (q, \<alpha>)"
    "hoist fl pn (Formula.Exists t \<phi>) = Formula.And q \<alpha>"
proof (cases "frz_split pn (Formula.Exists t (hoist fl pn \<phi>))")
  case None
  then show thesis
    by (intro that(1)) (simp_all only: hoist.simps(8) Let_def option.case)
next
  case (Some x)
  then obtain q \<alpha> where "frz_split pn (Formula.Exists t (hoist fl pn \<phi>)) = Some (q, \<alpha>)"
    by (cases x) simp
  then show thesis
    by (intro that(2)) (simp_all only: hoist.simps(8) Let_def option.case prod.case)
qed

lemma wty_frz_split_And:
  assumes "frz_split pn \<psi> = Some (q, \<alpha>)" "S, E \<turnstile> \<psi>" "S, E \<turnstile> \<alpha> \<Longrightarrow> S, E \<turnstile> \<beta>"
  shows "S, E \<turnstile> Formula.And q \<beta>"
  using frz_split_wty[OF assms(1,2)] assms(3) by (auto intro: wty_formula.And)

lemma wty_hoist: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> hoist fl pn \<phi>"
proof (induct fl pn \<phi> arbitrary: S E rule: hoist.induct)
  case (1 fl pn \<phi> I \<psi>)
  then have \<phi>: "S, E \<turnstile> \<phi>" and \<psi>: "S, E \<turnstile> hoist fl pn \<psi>"
    by (auto dest: wty_formulaD)
  then have "S, E \<turnstile> hoist fl pn \<phi>"
    using 1(2)[OF refl _ \<phi>] 1(3)[OF refl _ refl \<phi>]
    by (cases "if memL I 0 \<or> fl then frz_split pn (hoist fl pn \<psi>) else None") auto
  with \<psi> show ?case
    by (auto split: option.splits simp: Let_def intro: wty_formula.Since
      intro!: wty_frz_split_And dest: frz_split_wty)
next
  case (2 fl pn \<phi> I \<psi>)
  then have \<phi>: "S, E \<turnstile> \<phi>" and \<psi>: "S, E \<turnstile> hoist fl pn \<psi>"
    by (auto dest: wty_formulaD)
  then have "S, E \<turnstile> hoist fl pn \<phi>"
    using 2(2)[OF refl _ \<phi>] 2(3)[OF refl _ refl \<phi>]
    by (cases "frz_split pn (hoist fl pn \<psi>)") auto
  with \<psi> show ?case
    by (auto split: option.splits simp: Let_def intro: wty_formula.Until
      intro!: wty_frz_split_And dest: frz_split_wty)
next
  case (3 fl pn I \<psi>)
  then have "S, E \<turnstile> hoist fl pn \<psi>"
    by (auto dest: wty_formulaD)
  then show ?case
    by (auto split: option.splits simp: Let_def intro: wty_formula.Next
      intro!: wty_frz_split_And dest: frz_split_wty)
next
  case (7 fl pn l)
  show ?case
    using 7(1) wty_formula_AndsD[OF 7(2)] by (auto intro!: wty_formula.Ands)
next
  case (8 fl pn t \<phi>)
  have "S, E \<turnstile> Formula.Exists t (hoist fl pn \<phi>)"
    using 8(1)[OF wty_formula_ExistsD[OF 8(2)]] by (rule wty_formula.Exists)
  then show ?case
  proof (cases rule: hoist_Exists_cases[of pn t fl \<phi>])
    case (Some q \<alpha>)
    then show ?thesis
      using frz_split_wty[OF Some(1) \<open>S, E \<turnstile> Formula.Exists t (hoist fl pn \<phi>)\<close>]
      by (auto intro: wty_formula.And)
  qed simp
next
  case (11 fl pn I \<psi>)
  then have "S, E \<turnstile> hoist fl pn \<psi>"
    by (auto dest: wty_formulaD)
  then show ?case
    by (auto split: option.splits if_splits simp: Let_def intro: wty_formula.Prev
      intro!: wty_frz_split_And dest: frz_split_wty)
qed (erule wty_formula.cases; auto intro: wty_formula.intros)+

lemma wty_frz_rw: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> frz_rw B \<phi>"
proof (induct B \<phi> arbitrary: S E rule: frz_rw.induct)
  case (1 B p \<phi> \<psi>)
  let ?pn = "(p, Formula.nfv \<phi>)"
  from 1(3) obtain E' where \<phi>: "S, E' \<turnstile> \<phi>" and \<psi>: "S(?pn \<mapsto> tabulate E' 0 (Formula.nfv \<phi>)), E \<turnstile> \<psi>"
    by (cases rule: wty_formula.cases) auto
  have \<phi>': "S, E' \<turnstile> frz_rw B \<phi>"
    by (rule 1(1)[OF refl \<phi>])
  have \<psi>': "S(?pn \<mapsto> tabulate E' 0 (Formula.nfv \<phi>)), E \<turnstile>
      hoist (full_now B (frz_rw B \<phi>)) ?pn (frz_rw (?pn # B) \<psi>)"
    by (rule wty_hoist[OF 1(2)[OF refl refl \<psi>]])
  show ?case
    using wty_formula.Let[OF \<phi>'] wty_formula.Frz[OF \<phi>'] \<psi>' by (simp add: Let_def)
next
  case (2 B p \<phi> \<psi>)
  from 2(3) obtain E' where \<phi>: "S, E' \<turnstile> \<phi>" and \<psi>: "S((p, Formula.nfv \<phi>) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>)), E \<turnstile> \<psi>"
    by (cases rule: wty_formula.cases) auto
  show ?case
    using wty_formula.Let[OF 2(1)[OF \<phi>]] 2(2)[OF \<psi>] by (simp add: fun_upd_def)
next
  case (6 B l)
  show ?case
    using 6(1) wty_formula_AndsD[OF 6(2)] by (auto intro!: wty_formula.Ands)
qed (erule wty_formula.cases; auto intro: wty_formula.intros)+

lemma wty_frz_opt: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> frz_opt \<phi>"
  by (simp add: frz_opt_def Let_def wty_frz_rw)

lemma mmonitorable_frz_opt: "mmonitorable \<phi> \<Longrightarrow> mmonitorable (frz_opt \<phi>)"
  by (simp add: frz_opt_def Let_def mmonitorable_exec_mmonitorable)

(*<*)
end
(*>*)
