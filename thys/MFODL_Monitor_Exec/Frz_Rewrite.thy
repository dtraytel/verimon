(*<*)
theory Frz_Rewrite
  imports "MFODL_Monitor_Devel.Monitor" "MFODL_Monitor_Devel.Progress" "MFODL_Logic.Typing"
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

subsection \<open>The split of a conjunction\<close>

lemma is_frz_predD: "is_frz_pred pn q \<Longrightarrow> \<exists>e ts. q = Formula.Pred e ts \<and> (e, length ts) = pn"
  by (cases q) auto

lemma frz_find_Some:
  "frz_find pn l = Some (q, r) \<Longrightarrow> is_frz_pred pn q \<and> set l = insert q (set r)"
  by (induct l arbitrary: r) (auto split: if_splits option.splits)

lemma Min_insert_image:
  assumes "set l = insert q (set r)" "r \<noteq> []"
  shows "Min (f ` set l) = min (f q) (Min (f ` set r))"
  using assms by simp

lemma eval_dec_trm: "0 \<notin> Formula.fv_trm s \<Longrightarrow> Formula.eval_trm v (dec_trm s) = Formula.eval_trm (z # v) s"
  by (induct s) (auto simp: nth_Cons')

lemma fvi_dec_trm: "0 \<notin> Formula.fv_trm s \<Longrightarrow> Formula.fvi_trm b (dec_trm s) = Formula.fvi_trm (Suc b) s"
  by (induct s) auto

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

lemma frz_split_pred: "frz_split pn \<psi> = Some (q, r) \<Longrightarrow> is_frz_pred pn q"
proof (induct pn \<psi> arbitrary: q r rule: frz_split.induct)
  case (3 pn t \<alpha>)
  from 3(2) obtain e ts \<beta> where s: "frz_split pn \<alpha> = Some (Formula.Pred e ts, \<beta>)"
    "q = Formula.Pred e (map dec_trm ts)"
    by (rule frz_split_Exists_Some)
  with 3(1)[OF s(1)] show ?case
    by simp
qed (auto split: if_splits option.splits dest: frz_find_Some)

lemma sat_Pred_dec_trm:
  "list_all (\<lambda>s. 0 \<notin> Formula.fv_trm s) ts \<Longrightarrow>
    Formula.sat \<sigma> V v i (Formula.Pred e (map dec_trm ts)) = Formula.sat \<sigma> V (z # v) i (Formula.Pred e ts)"
proof -
  assume "list_all (\<lambda>s. 0 \<notin> Formula.fv_trm s) ts"
  then have eq: "map (Formula.eval_trm v) (map dec_trm ts) = map (Formula.eval_trm (z # v)) ts"
    by (auto simp: eval_dec_trm list_all_iff)
  show ?thesis
    by (simp only: Formula.sat.simps length_map eq)
qed

lemma frz_split_sat:
  "frz_split pn \<psi> = Some (q, r) \<Longrightarrow>
    Formula.sat \<sigma> V v i \<psi> \<longleftrightarrow> Formula.sat \<sigma> V v i q \<and> Formula.sat \<sigma> V v i r"
proof (induct pn \<psi> arbitrary: q r v rule: frz_split.induct)
  case (3 pn t \<alpha>)
  from 3(2) obtain e ts \<beta> where s: "frz_split pn \<alpha> = Some (Formula.Pred e ts, \<beta>)"
    "list_all (\<lambda>s. 0 \<notin> Formula.fv_trm s) ts" "q = Formula.Pred e (map dec_trm ts)"
    "r = Formula.Exists t \<beta>"
    by (rule frz_split_Exists_Some)
  show ?case
    using 3(1)[OF s(1)] sat_Pred_dec_trm[OF s(2)] s(3,4) by auto
qed (auto split: if_splits option.splits dest!: frz_find_Some)

lemma frz_split_fvi:
  "frz_split pn \<psi> = Some (q, r) \<Longrightarrow> Formula.fvi b \<psi> = Formula.fvi b q \<union> Formula.fvi b r"
proof (induct pn \<psi> arbitrary: q r b rule: frz_split.induct)
  case (3 pn t \<alpha>)
  from 3(2) obtain e ts \<beta> where s: "frz_split pn \<alpha> = Some (Formula.Pred e ts, \<beta>)"
    "list_all (\<lambda>s. 0 \<notin> Formula.fv_trm s) ts" "q = Formula.Pred e (map dec_trm ts)"
    "r = Formula.Exists t \<beta>"
    by (rule frz_split_Exists_Some)
  have "Formula.fvi b q = Formula.fvi (Suc b) (Formula.Pred e ts)"
    using s(2,3) by (auto simp: fvi_dec_trm list_all_iff)
  then show ?case
    using 3(1)[OF s(1)] s(4) by simp
qed (auto split: if_splits option.splits dest!: frz_find_Some)

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

lemma frz_split_progress:
  "frz_split pn \<psi> = Some (q, r) \<Longrightarrow> pred_mapping (\<lambda>x. x \<le> j) P \<Longrightarrow>
    progress \<sigma> P \<psi> j = min (progress \<sigma> P q j) (progress \<sigma> P r j)"
proof (induct pn \<psi> arbitrary: q r rule: frz_split.induct)
  case (2 pn l)
  from 2(1) obtain r' where f: "frz_find pn l = Some (q, r')" "r = Formula.Ands r'"
    by (auto split: option.splits)
  have l: "set l = insert q (set r')"
    using frz_find_Some[OF f(1)] by blast
  have le: "progress \<sigma> P q j \<le> j"
    by (rule progress_le_gen[OF 2(2)])
  show ?case
  proof (cases "r' = []")
    case True
    with l f(2) le show ?thesis
      by (auto simp: min_absorb1)
  next
    case False
    with l f(2) show ?thesis
      by (auto simp: Min_insert_image)
  qed
next
  case (3 pn t \<alpha>)
  from 3(2) obtain e ts \<beta> where s: "frz_split pn \<alpha> = Some (Formula.Pred e ts, \<beta>)"
    "list_all (\<lambda>s. 0 \<notin> Formula.fv_trm s) ts" "q = Formula.Pred e (map dec_trm ts)"
    "r = Formula.Exists t \<beta>"
    by (rule frz_split_Exists_Some)
  show ?case
    using 3(1)[OF s(1) 3(3)] s(3,4) by simp
qed (auto split: if_splits)

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

lemma fvi_hoist[simp]: "Formula.fvi b (hoist fl pn \<phi>) = Formula.fvi b \<phi>"
proof (induct fl pn \<phi> arbitrary: b rule: hoist.induct)
  case (1 fl pn \<phi> I \<psi>)
  have \<phi>: "Formula.fvi b' (hoist fl pn \<phi>) = Formula.fvi b' \<phi>" for b'
    using 1(2)[OF refl] 1(3)[OF refl _ refl]
    by (cases "if memL I 0 \<or> fl then frz_split pn (hoist fl pn \<psi>) else None") auto
  show ?case
    using 1(1) \<phi> by (auto simp: Let_def split: option.splits if_splits dest!: frz_split_fvi)
next
  case (2 fl pn \<phi> I \<psi>)
  have \<phi>: "Formula.fvi b' (hoist fl pn \<phi>) = Formula.fvi b' \<phi>" for b'
    using 2(2)[OF refl] 2(3)[OF refl _ refl]
    by (cases "frz_split pn (hoist fl pn \<psi>)") auto
  show ?case
    using 2(1) \<phi> by (auto simp: Let_def split: option.splits dest!: frz_split_fvi)
next
  case (8 fl pn t \<phi>)
  show ?case
  proof (cases rule: hoist_Exists_cases[of pn t fl \<phi>])
    case (Some q \<alpha>)
    have "Formula.fvi b (Formula.Exists t (hoist fl pn \<phi>)) = Formula.fvi b q \<union> Formula.fvi b \<alpha>"
      by (rule frz_split_fvi[OF Some(1)])
    then show ?thesis
      using 8 by (simp only: Some(2) Formula.fvi.simps)
  qed (use 8 in simp)
qed (auto simp: Let_def split: option.splits if_splits dest!: frz_split_fvi)

lemma nfv_hoist[simp]: "Formula.nfv (hoist fl pn \<phi>) = Formula.nfv \<phi>"
  by (simp add: Formula.nfv_def)

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

lemma sat_frz_pred_const:
  assumes "is_frz_pred pn q" "V pn = Some X" "\<forall>w j j'. X w j = X w j'"
  shows "Formula.sat \<sigma> V v j q = Formula.sat \<sigma> V v i q"
proof -
  obtain e ts where "q = Formula.Pred e ts" "(e, length ts) = pn"
    using is_frz_predD[OF assms(1)] by blast
  then show ?thesis
    using assms(2) assms(3)[rule_format, of _ j i] by simp
qed

lemma frz_split_sat_const:
  assumes "frz_split pn \<psi> = Some (q, \<alpha>)" "V pn = Some X" "\<forall>w j j'. X w j = X w j'"
  shows "Formula.sat \<sigma> V v j \<psi> \<longleftrightarrow> Formula.sat \<sigma> V v i q \<and> Formula.sat \<sigma> V v j \<alpha>"
proof -
  have "is_frz_pred pn q"
    by (rule frz_split_pred[OF assms(1)])
  then show ?thesis
    using frz_split_sat[OF assms(1)] sat_frz_pred_const[of pn q V X \<sigma> v j i] assms(2,3)
    by blast
qed

lemma sat_hoist:
  assumes "V pn = Some X" "\<forall>w j j'. X w j = X w j'"
  shows "Formula.sat \<sigma> V v i (hoist fl pn \<phi>) = Formula.sat \<sigma> V v i \<phi>"
  using assms
proof (induct fl pn \<phi> arbitrary: V v i rule: hoist.induct)
  case (1 fl pn \<phi> I \<psi>)
  have \<psi>: "Formula.sat \<sigma> V v' j (hoist fl pn \<psi>) = Formula.sat \<sigma> V v' j \<psi>" for v' j
    using 1(1)[where V=V] 1(4,5) by blast
  have \<phi>: "Formula.sat \<sigma> V v' j (hoist fl pn \<phi>) = Formula.sat \<sigma> V v' j \<phi>" for v' j
    using 1(2)[OF refl, where V=V] 1(3)[OF refl _ refl, where V=V] 1(4,5)
    by (cases "if memL I 0 \<or> fl then frz_split pn (hoist fl pn \<psi>) else None") auto
  show ?case
    using \<psi> \<phi> frz_split_sat_const[where V=V and pn=pn and \<psi>="hoist fl pn \<psi>" and \<sigma>=\<sigma> and v=v and i=i] 1(4,5)
    by (auto simp: Let_def split: option.splits)
next
  case (2 fl pn \<phi> I \<psi>)
  have \<psi>: "Formula.sat \<sigma> V v' j (hoist fl pn \<psi>) = Formula.sat \<sigma> V v' j \<psi>" for v' j
    using 2(1)[where V=V] 2(4,5) by blast
  have \<phi>: "Formula.sat \<sigma> V v' j (hoist fl pn \<phi>) = Formula.sat \<sigma> V v' j \<phi>" for v' j
    using 2(2)[OF refl, where V=V] 2(3)[OF refl _ refl, where V=V] 2(4,5)
    by (cases "frz_split pn (hoist fl pn \<psi>)") auto
  show ?case
    using \<psi> \<phi> frz_split_sat_const[where V=V and pn=pn and \<psi>="hoist fl pn \<psi>" and \<sigma>=\<sigma> and v=v and i=i] 2(4,5)
    by (auto simp: Let_def split: option.splits)
next
  case (3 fl pn I \<psi>)
  have \<psi>: "Formula.sat \<sigma> V v' j (hoist fl pn \<psi>) = Formula.sat \<sigma> V v' j \<psi>" for v' j
    using 3(1)[where V=V] 3(2,3) by blast
  show ?case
    using \<psi> frz_split_sat_const[where V=V and pn=pn and \<psi>="hoist fl pn \<psi>" and \<sigma>=\<sigma> and v=v and i=i] 3(2,3)
    by (auto simp: Let_def split: option.splits)
next
  case (8 fl pn t \<phi>)
  have \<phi>: "Formula.sat \<sigma> V v i (Formula.Exists t (hoist fl pn \<phi>)) = Formula.sat \<sigma> V v i (Formula.Exists t \<phi>)"
    using 8 by simp
  show ?case
  proof (cases rule: hoist_Exists_cases[of pn t fl \<phi>])
    case (Some q \<alpha>)
    then show ?thesis
      using frz_split_sat[OF Some(1), of \<sigma> V v i] \<phi> by simp
  qed (use \<phi> in simp)
next
  case (11 fl pn I \<psi>)
  have \<psi>: "Formula.sat \<sigma> V v' j (hoist fl pn \<psi>) = Formula.sat \<sigma> V v' j \<psi>" for v' j
    using 11(1)[where V=V] 11(2,3) by blast
  show ?case
    using \<psi> frz_split_sat_const[where V=V and pn=pn and \<psi>="hoist fl pn \<psi>" and \<sigma>=\<sigma> and v=v and i=i] 11(2,3)
    by (auto simp: Let_def split: option.splits if_splits nat.splits)
qed auto
lemma progress_frz_pred: "is_frz_pred pn q \<Longrightarrow> P pn = Some k \<Longrightarrow> progress \<sigma> P q j = k"
  by (cases q) auto

lemma frz_split_progress_const:
  assumes "frz_split pn \<psi> = Some (q, \<alpha>)" "pred_mapping (\<lambda>x. x \<le> j) P" "P pn = Some k"
  shows "progress \<sigma> P \<psi> j = min k (progress \<sigma> P \<alpha> j)" "progress \<sigma> P q j = k"
  using frz_split_progress[OF assms(1,2)] progress_frz_pred[of pn q P k \<sigma> j] assms(3) frz_split_pred[OF assms(1)]
  by auto

text \<open>The frozen predicate's progress is either the whole prefix or none of it, and the whole
  prefix when the flag is set.\<close>

lemma progress_hoist:
  assumes "pred_mapping (\<lambda>x. x \<le> j) P" "P pn = Some k" "k = 0 \<or> k = j" "fl \<Longrightarrow> k = j"
  shows "progress \<sigma> P (hoist fl pn \<phi>) j = progress \<sigma> P \<phi> j"
  using assms
proof (induct fl pn \<phi> arbitrary: P rule: hoist.induct)
  case (1 fl pn \<phi> I \<psi>)
  have \<psi>: "progress \<sigma> P (hoist fl pn \<psi>) j = progress \<sigma> P \<psi> j"
    using 1(1)[where P=P] 1(4-7) by blast
  have \<phi>: "progress \<sigma> P (hoist fl pn \<phi>) j = progress \<sigma> P \<phi> j"
    using 1(2)[OF refl, where P=P] 1(3)[OF refl _ refl, where P=P] 1(4-7)
    by (cases "if memL I 0 \<or> fl then frz_split pn (hoist fl pn \<psi>) else None") auto
  show ?case
  proof (cases "if memL I 0 \<or> fl then frz_split pn (hoist fl pn \<psi>) else None")
    case None
    then show ?thesis
      using \<psi> \<phi> by (simp add: Let_def)
  next
    case (Some q\<alpha>)
    then obtain q \<alpha> where s: "frz_split pn (hoist fl pn \<psi>) = Some (q, \<alpha>)" "memL I 0 \<or> fl"
      by (cases q\<alpha>) (auto split: if_splits)
    note c = frz_split_progress_const[OF s(1) 1(4,5), where \<sigma>=\<sigma>]
    have \<psi>\<alpha>: "progress \<sigma> P \<psi> j = min k (progress \<sigma> P \<alpha> j)"
      using c(1) \<psi> by simp
    have le: "progress \<sigma> P \<alpha> j \<le> j" "progress \<sigma> P \<phi> j \<le> j"
      using progress_le_gen[OF 1(4)] by blast+
    show ?thesis
    proof (cases "memL I 0")
      case True
      then show ?thesis
        using \<phi> s c(2) \<psi>\<alpha> by (simp add: Let_def min.left_commute)
    next
      case False
      then have "k = j"
        using s(2) 1(7) by blast
      then show ?thesis
        using \<phi> s c(2) \<psi>\<alpha> le False by (auto simp: Let_def min_def)
    qed
  qed
next
  case (2 fl pn \<phi> I \<psi>)
  have \<psi>: "progress \<sigma> P (hoist fl pn \<psi>) j = progress \<sigma> P \<psi> j"
    using 2(1)[where P=P] 2(4-7) by blast
  have \<phi>: "progress \<sigma> P (hoist fl pn \<phi>) j = progress \<sigma> P \<phi> j"
    using 2(2)[OF refl, where P=P] 2(3)[OF refl _ refl, where P=P] 2(4-7)
    by (cases "frz_split pn (hoist fl pn \<psi>)") auto
  show ?case
  proof (cases "frz_split pn (hoist fl pn \<psi>)")
    case (Some q\<alpha>)
    then obtain q \<alpha> where s: "frz_split pn (hoist fl pn \<psi>) = Some (q, \<alpha>)"
      by (cases q\<alpha>) auto
    note c = frz_split_progress_const[OF s 2(4,5), where \<sigma>=\<sigma>]
    have \<psi>\<alpha>: "progress \<sigma> P \<psi> j = min k (progress \<sigma> P \<alpha> j)"
      using c(1) \<psi> by simp
    have le: "progress \<sigma> P \<alpha> j \<le> j" "progress \<sigma> P (Formula.Until \<phi> I \<alpha>) j \<le> j"
      using progress_le_gen[OF 2(4)] by blast+
    have eq: "progress \<sigma> P (hoist fl pn (Formula.Until \<phi> I \<psi>)) j =
      min k (progress \<sigma> P (Formula.Until \<phi> I \<alpha>) j)"
      using s \<phi> c(2) by (simp add: Let_def)
    from 2(6) show ?thesis
    proof
      assume "k = 0"
      then show ?thesis
        using eq \<psi>\<alpha> progress_Until_le[of \<sigma> P \<phi> I \<psi> j] by simp
    next
      assume "k = j"
      then show ?thesis
        using eq \<psi>\<alpha> le by (simp add: min_absorb2)
    qed
  qed (use \<psi> \<phi> in \<open>simp add: Let_def\<close>)
next
  case (3 fl pn I \<psi>)
  have \<psi>: "progress \<sigma> P (hoist fl pn \<psi>) j = progress \<sigma> P \<psi> j"
    using 3(1)[where P=P] 3(2-5) by blast
  show ?case
  proof (cases "frz_split pn (hoist fl pn \<psi>)")
    case (Some q\<alpha>)
    then obtain q \<alpha> where s: "frz_split pn (hoist fl pn \<psi>) = Some (q, \<alpha>)"
      by (cases q\<alpha>) auto
    note c = frz_split_progress_const[OF s 3(2,3), where \<sigma>=\<sigma>]
    have \<psi>\<alpha>: "progress \<sigma> P \<psi> j = min k (progress \<sigma> P \<alpha> j)"
      using c(1) \<psi> by simp
    have le: "progress \<sigma> P \<alpha> j \<le> j"
      using progress_le_gen[OF 3(2)] by blast
    from 3(4) show ?thesis
      using s c(2) \<psi>\<alpha> le by (auto simp: Let_def min_absorb2)
  qed (use \<psi> in \<open>simp add: Let_def\<close>)
next
  case (8 fl pn t \<phi>)
  have \<phi>: "progress \<sigma> P (Formula.Exists t (hoist fl pn \<phi>)) j = progress \<sigma> P \<phi> j"
    using 8 by simp
  show ?case
  proof (cases rule: hoist_Exists_cases[of pn t fl \<phi>])
    case (Some q \<alpha>)
    then show ?thesis
      using frz_split_progress[OF Some(1) 8(2), of \<sigma>] \<phi> by simp
  qed (use \<phi> in simp)
next
  case (10 fl pn e \<phi> \<psi>)
  show ?case
  proof (cases "(e, Formula.nfv \<phi>) = pn")
    case False
    let ?P = "P((e, Formula.nfv \<phi>) \<mapsto> progress \<sigma> P \<phi> j)"
    have "progress \<sigma> P \<phi> j \<le> j"
      by (rule progress_le_gen[OF 10(2)])
    then have "pred_mapping (\<lambda>x. x \<le> j) ?P" "?P pn = Some k"
      using 10(2,3) False by auto
    from 10(1)[OF False this 10(4,5)] show ?thesis
      using False by (simp add: fun_upd_def)
  qed simp
next
  case (11 fl pn I \<psi>)
  have \<psi>: "progress \<sigma> P (hoist fl pn \<psi>) j = progress \<sigma> P \<psi> j"
    using 11(1)[where P=P] 11(2-5) by blast
  show ?case
  proof (cases "if fl then frz_split pn (hoist fl pn \<psi>) else None")
    case (Some q\<alpha>)
    then obtain q \<alpha> where s: "frz_split pn (hoist fl pn \<psi>) = Some (q, \<alpha>)" "fl"
      by (cases q\<alpha>) (auto split: if_splits)
    note c = frz_split_progress_const[OF s(1) 11(2,3), where \<sigma>=\<sigma>]
    have k: "k = j"
      using s(2) 11(5) by blast
    have le: "progress \<sigma> P \<alpha> j \<le> j"
      using progress_le_gen[OF 11(2)] by blast
    show ?thesis
      using s c \<psi> le k by (auto simp: Let_def min_def)
  qed (use \<psi> in \<open>simp add: Let_def\<close>)
qed auto
subsection \<open>A frozen predicate at the current time point only\<close>

lemma not_contains_pred_sat_upd:
  "\<not> contains_pred pn \<psi> \<Longrightarrow> Formula.sat \<sigma> (V(pn \<mapsto> X)) v i \<psi> = Formula.sat \<sigma> (V(pn \<mapsto> Y)) v i \<psi>"
  by simp

lemma sat_now_only:
  assumes "now_only pn \<psi>" "\<forall>w. X w i = Y w i"
  shows "Formula.sat \<sigma> (V(pn \<mapsto> X)) v i \<psi> = Formula.sat \<sigma> (V(pn \<mapsto> Y)) v i \<psi>"
  using assms
proof (induct pn \<psi> arbitrary: V v rule: now_only.induct)
  case 1
  then show ?case
    by (auto split: option.splits)
next
  case 2
  then show ?case
    by auto
next
  case 3
  then show ?case
    by auto
next
  case 4
  then show ?case
    by auto
next
  case 5
  then show ?case
    by auto
next
  case 6
  then show ?case
    by auto
next
  case 7
  then show ?case
    by auto
next
  case (8 pn e \<phi> \<psi>)
  show ?case
  proof (cases "contains_pred pn (Formula.Let e \<phi> \<psi>)")
    case True
    with 8(2) have ne: "(e, Formula.nfv \<phi>) \<noteq> pn" and \<phi>: "\<not> contains_pred pn \<phi>" and \<psi>: "now_only pn \<psi>"
      by auto
    define Z where "Z = (\<lambda>w j. Formula.sat \<sigma> V w j \<phi>)"
    have eq: "V(pn \<mapsto> W, (e, Formula.nfv \<phi>) \<mapsto> \<lambda>w j. Formula.sat \<sigma> (V(pn \<mapsto> W)) w j \<phi>) =
      V((e, Formula.nfv \<phi>) \<mapsto> Z, pn \<mapsto> W)" for W
      using ne \<phi> by (simp add: Z_def fun_upd_twist)
    show ?thesis
      using 8(1)[OF ne \<phi> \<psi> 8(3), where V="V((e, Formula.nfv \<phi>) \<mapsto> Z)"] by (simp only: Formula.sat.simps eq)
  next
    case False
    then show ?thesis
      by (metis not_contains_pred_sat)
  qed
qed (rule not_contains_pred_sat_upd, simp)+
lemma Min_min_image:
  "finite S \<Longrightarrow> S \<noteq> {} \<Longrightarrow> Min ((\<lambda>x. min (f x) (g x)) ` S) = min (Min (f ` S)) (Min (g ` S))"
  by (induct rule: finite_ne_induct) (auto simp: ac_simps)

lemma Min_if_image:
  fixes k j :: nat
  assumes "finite S" "S \<noteq> {}" "k \<le> j"
  shows "Min ((\<lambda>x. if Q x then k else j) ` S) = (if \<exists>x\<in>S. Q x then k else j)"
  using assms by (cases "\<exists>x\<in>S. Q x") (auto intro!: Min_eqI intro: rev_image_eqI)

lemma progress_upd_le: "pred_mapping (\<lambda>x. x \<le> j) P \<Longrightarrow> progress \<sigma> (P(pn \<mapsto> j)) \<psi> j \<le> j"
  by (rule progress_le_gen) simp

lemma progress_not_contains_upd:
  assumes "\<not> contains_pred pn \<psi>" "pred_mapping (\<lambda>x. x \<le> j) P"
  shows "progress \<sigma> (P(pn \<mapsto> k)) \<psi> j =
    min (if contains_pred pn \<psi> then k else j) (progress \<sigma> (P(pn \<mapsto> j)) \<psi> j)"
proof -
  have "progress \<sigma> P \<psi> j \<le> j"
    by (rule progress_le_gen[OF assms(2)])
  then show ?thesis
    using assms(1) by (simp add: min_absorb2)
qed

lemma progress_now_only:
  assumes "now_only pn \<psi>" "pred_mapping (\<lambda>x. x \<le> j) P" "k \<le> j"
  shows "progress \<sigma> (P(pn \<mapsto> k)) \<psi> j =
    min (if contains_pred pn \<psi> then k else j) (progress \<sigma> (P(pn \<mapsto> j)) \<psi> j)"
  using assms
proof (induct pn \<psi> arbitrary: P rule: now_only.induct)
  case (1 pn e ts)
  show ?case
  proof (cases "pn = (e, length ts)")
    case True
    with 1(3) show ?thesis
      by (simp add: min_absorb1)
  next
    case False
    then show ?thesis
      by (intro progress_not_contains_upd 1(2)) simp
  qed
next
  case 2
  then show ?case
    by simp
next
  case (3 pn \<phi> \<psi>)
  from 3(3) have no: "now_only pn \<phi>" "now_only pn \<psi>"
    by simp_all
  note IH = 3(1)[OF no(1) 3(4,5)] 3(2)[OF no 3(4,5)]
  have "progress \<sigma> (P(pn \<mapsto> j)) \<phi> j \<le> j" "progress \<sigma> (P(pn \<mapsto> j)) \<psi> j \<le> j"
    by (rule progress_upd_le[OF 3(4)])+
  then show ?case
    using IH 3(5) by (auto simp: min_def)
next
  case (4 pn \<phi> \<psi>)
  from 4(3) have no: "now_only pn \<phi>" "now_only pn \<psi>"
    by simp_all
  note IH = 4(1)[OF no(1) 4(4,5)] 4(2)[OF no 4(4,5)]
  have "progress \<sigma> (P(pn \<mapsto> j)) \<phi> j \<le> j" "progress \<sigma> (P(pn \<mapsto> j)) \<psi> j \<le> j"
    by (rule progress_upd_le[OF 4(4)])+
  then show ?case
    using IH 4(5) by (auto simp: min_def)
next
  case (5 pn l)
  show ?case
  proof (cases "l = []")
    case False
    from 5(2) have no: "\<forall>\<phi>\<in>set l. now_only pn \<phi>"
      by simp
    have "progress \<sigma> (P(pn \<mapsto> k)) \<phi> j =
      min (if contains_pred pn \<phi> then k else j) (progress \<sigma> (P(pn \<mapsto> j)) \<phi> j)"
      if "\<phi> \<in> set l" for \<phi>
      by (rule 5(1)[OF that bspec[OF no that] 5(3,4)])
    then have "(\<lambda>\<phi>. progress \<sigma> (P(pn \<mapsto> k)) \<phi> j) ` set l =
      (\<lambda>\<phi>. min (if contains_pred pn \<phi> then k else j) (progress \<sigma> (P(pn \<mapsto> j)) \<phi> j)) ` set l"
      by (rule image_cong[OF refl])
    then have "Min ((\<lambda>\<phi>. progress \<sigma> (P(pn \<mapsto> k)) \<phi> j) ` set l) =
      Min ((\<lambda>\<phi>. min (if contains_pred pn \<phi> then k else j) (progress \<sigma> (P(pn \<mapsto> j)) \<phi> j)) ` set l)"
      by simp
    also have "\<dots> = min (Min ((\<lambda>\<phi>. if contains_pred pn \<phi> then k else j) ` set l))
      (Min ((\<lambda>\<phi>. progress \<sigma> (P(pn \<mapsto> j)) \<phi> j) ` set l))"
      using False by (intro Min_min_image) auto
    also have "\<dots> = min (if \<exists>\<phi>\<in>set l. contains_pred pn \<phi> then k else j)
      (Min ((\<lambda>\<phi>. progress \<sigma> (P(pn \<mapsto> j)) \<phi> j) ` set l))"
      using False 5(4) by (subst Min_if_image) auto
    finally have calc: "Min ((\<lambda>\<phi>. progress \<sigma> (P(pn \<mapsto> k)) \<phi> j) ` set l) =
      min (if \<exists>\<phi>\<in>set l. contains_pred pn \<phi> then k else j)
      (Min ((\<lambda>\<phi>. progress \<sigma> (P(pn \<mapsto> j)) \<phi> j) ` set l))" .
    have pa: "progress \<sigma> Q (Formula.Ands l) j = Min ((\<lambda>\<phi>. progress \<sigma> Q \<phi> j) ` set l)" for Q
      using False by simp
    show ?thesis
      unfolding pa contains_pred.simps by (rule calc)  qed simp
next
  case 6
  then show ?case
    by simp
next
  case 7
  then show ?case
    by simp
next
  case (8 pn e \<phi> \<psi>)
  show ?case
  proof (cases "contains_pred pn (Formula.Let e \<phi> \<psi>)")
    case True
    with 8(2) have ne: "(e, Formula.nfv \<phi>) \<noteq> pn" and \<phi>: "\<not> contains_pred pn \<phi>" and \<psi>: "now_only pn \<psi>"
      by auto
    let ?P = "P((e, Formula.nfv \<phi>) \<mapsto> progress \<sigma> P \<phi> j)"
    have "progress \<sigma> P \<phi> j \<le> j"
      by (rule progress_le_gen[OF 8(3)])
    then have pm: "pred_mapping (\<lambda>x. x \<le> j) ?P"
      using 8(3) by simp
    have eq: "P(pn \<mapsto> x, (e, Formula.nfv \<phi>) \<mapsto> progress \<sigma> (P(pn \<mapsto> x)) \<phi> j) = ?P(pn \<mapsto> x)" for x
      using ne \<phi> by (simp add: fun_upd_twist)
    have l: "progress \<sigma> (P(pn \<mapsto> x)) (Formula.Let e \<phi> \<psi>) j = progress \<sigma> (?P(pn \<mapsto> x)) \<psi> j" for x
      by (simp only: progress.simps eq)
    have c: "contains_pred pn (Formula.Let e \<phi> \<psi>) = contains_pred pn \<psi>"
      using ne \<phi> by auto
    show ?thesis
      unfolding l c by (rule 8(1)[OF ne \<phi> \<psi> pm 8(4)])
  next
    case False
    then show ?thesis
      by (rule progress_not_contains_upd[OF _ 8(3)])
  qed
qed (rule progress_not_contains_upd; simp)+
lemma sat_Frz_now_only:
  assumes "now_only (p, Formula.nfv \<phi>) \<psi>"
  shows "Formula.sat \<sigma> V v i (Formula.Frz p \<phi> \<psi>) = Formula.sat \<sigma> V v i (Formula.Let p \<phi> \<psi>)"
  using sat_now_only[OF assms, where X="\<lambda>w j. Formula.sat \<sigma> V w i \<phi>" and Y="\<lambda>w j. Formula.sat \<sigma> V w j \<phi>"]
  by simp

lemma progress_Frz_now_only:
  assumes "now_only (p, Formula.nfv \<phi>) \<psi>" "pred_mapping (\<lambda>x. x \<le> j) P"
  shows "progress \<sigma> P (Formula.Frz p \<phi> \<psi>) j = progress \<sigma> P (Formula.Let p \<phi> \<psi>) j"
proof -
  define pn where "pn = (p, Formula.nfv \<phi>)"
  define a where "a = progress \<sigma> P \<phi> j"
  define F where "F = progress \<sigma> (P(pn \<mapsto> j)) \<psi> j"
  define c where "c = contains_pred pn \<psi>"
  have a: "a \<le> j"
    unfolding a_def by (rule progress_le_gen[OF assms(2)])
  have F: "F \<le> j"
    unfolding F_def by (rule progress_upd_le[OF assms(2)])
  have f: "progress \<sigma> (P(pn \<mapsto> x)) \<psi> j = min (if c then x else j) F" if "x \<le> j" for x
    unfolding c_def F_def by (rule progress_now_only[OF assms(1)[folded pn_def] assms(2) that])
  have "progress \<sigma> P (Formula.Frz p \<phi> \<psi>) j =
    (LEAST i. i \<le> j \<and> min (if c then (if i < a then j else 0) else j) F \<le> i)"
    by (simp add: frz_progress_def Let_def f pn_def[symmetric] a_def[symmetric])
  also have "\<dots> = min (if c then a else j) F"
  proof (rule Least_equality)
    show "min (if c then a else j) F \<le> j \<and>
      min (if c then (if min (if c then a else j) F < a then j else 0) else j) F \<le> min (if c then a else j) F"
      using a F by (auto simp: min_def)
  next
    fix y
    assume "y \<le> j \<and> min (if c then (if y < a then j else 0) else j) F \<le> y"
    then show "min (if c then a else j) F \<le> y"
      using a F by (auto simp: min_def split: if_splits)
  qed
  also have "\<dots> = progress \<sigma> P (Formula.Let p \<phi> \<psi>) j"
    using f[OF a] by (simp add: pn_def a_def)
  finally show ?thesis .
qed

subsection \<open>The rewrite of the whole formula\<close>

lemma fvi_frz_rw[simp]: "Formula.fvi b (frz_rw B \<phi>) = Formula.fvi b \<phi>"
  by (induct B \<phi> arbitrary: b rule: frz_rw.induct) (auto simp: Let_def)

lemma nfv_frz_rw[simp]: "Formula.nfv (frz_rw B \<phi>) = Formula.nfv \<phi>"
  by (simp add: Formula.nfv_def)

lemma sat_frz_rw[simp]: "Formula.sat \<sigma> V v i (frz_rw B \<phi>) = Formula.sat \<sigma> V v i \<phi>"
proof (induct B \<phi> arbitrary: V v i rule: frz_rw.induct)
  case (1 B p \<phi> \<psi>)
  let ?pn = "(p, Formula.nfv \<phi>)"
  let ?\<phi>' = "frz_rw B \<phi>"
  let ?\<psi>' = "hoist (full_now B ?\<phi>') ?pn (frz_rw (?pn # B) \<psi>)"
  have \<phi>: "Formula.sat \<sigma> V' v' i' ?\<phi>' = Formula.sat \<sigma> V' v' i' \<phi>" for V' v' i'
    by (rule 1(1)[OF refl])
  have \<psi>: "Formula.sat \<sigma> V' v' i' (frz_rw (?pn # B) \<psi>) = Formula.sat \<sigma> V' v' i' \<psi>" for V' v' i'
    by (rule 1(2)[OF refl refl])
  have h: "Formula.sat \<sigma> (V(?pn \<mapsto> \<lambda>w j. Formula.sat \<sigma> V w i \<phi>)) v i ?\<psi>' =
    Formula.sat \<sigma> (V(?pn \<mapsto> \<lambda>w j. Formula.sat \<sigma> V w i \<phi>)) v i (frz_rw (?pn # B) \<psi>)"
    by (rule sat_hoist) auto
  have "Formula.sat \<sigma> V v i (Formula.Frz p ?\<phi>' ?\<psi>') = Formula.sat \<sigma> V v i (Formula.Frz p \<phi> \<psi>)"
    using h by (simp add: \<phi> \<psi>)
  moreover have "Formula.sat \<sigma> V v i (Formula.Let p ?\<phi>' ?\<psi>') =
    Formula.sat \<sigma> V v i (Formula.Frz p ?\<phi>' ?\<psi>')" if "now_only ?pn ?\<psi>'"
    using sat_Frz_now_only[of p ?\<phi>' ?\<psi>'] that by simp
  ultimately show ?case
    by (simp add: Let_def)
qed (auto split: nat.splits)

text \<open>Outside the bound predicates, every predicate is known at every time point of the
  prefix or at none of them; a formula that never lags then has the whole prefix as its
  progress.\<close>

definition full_env :: "(Formula.name \<times> nat) list \<Rightarrow> (Formula.name \<times> nat \<rightharpoonup> nat) \<Rightarrow> nat \<Rightarrow> bool" where
  "full_env B P j \<longleftrightarrow> (\<forall>pn. pn \<notin> set B \<longrightarrow> P pn = None \<or> P pn = Some j)"

lemma full_env_Cons_upd: "full_env B P j \<Longrightarrow> full_env (pn # B) (P(pn \<mapsto> x)) j"
  by (auto simp: full_env_def)

lemma progress_full_now:
  "pred_mapping (\<lambda>x. x \<le> j) P \<Longrightarrow> full_env B P j \<Longrightarrow> full_now B \<phi> \<Longrightarrow> progress \<sigma> P \<phi> j = j"
proof (induct B \<phi> rule: full_now.induct)
  case (1 B e ts)
  then have "P (e, length ts) = None \<or> P (e, length ts) = Some j"
    by (auto simp: full_env_def)
  then show ?case
    by auto
next
  case (8 B l)
  have "\<forall>\<phi> \<in> set l. progress \<sigma> P \<phi> j = j"
    using 8 by (auto simp: list_all_iff)
  then show ?case
    by (cases l) (auto intro!: Min_eqI)
qed auto

lemma progress_frz_rw:
  "pred_mapping (\<lambda>x. x \<le> j) P \<Longrightarrow> full_env B P j \<Longrightarrow> progress \<sigma> P (frz_rw B \<phi>) j = progress \<sigma> P \<phi> j"
proof (induct B \<phi> arbitrary: P rule: frz_rw.induct)
  case (1 B p \<phi> \<psi>)
  let ?pn = "(p, Formula.nfv \<phi>)"
  let ?\<phi>' = "frz_rw B \<phi>"
  let ?fl = "full_now B ?\<phi>'"
  let ?\<psi>' = "hoist ?fl ?pn (frz_rw (?pn # B) \<psi>)"
  have \<phi>: "progress \<sigma> P ?\<phi>' j = progress \<sigma> P \<phi> j"
    by (rule 1(1)[OF refl 1(3,4)])
  have \<psi>: "progress \<sigma> (P(?pn \<mapsto> x)) ?\<psi>' j = progress \<sigma> (P(?pn \<mapsto> x)) \<psi> j"
    if "x = 0 \<or> x = j" "?fl \<Longrightarrow> x = j" for x
  proof -
    have pm: "pred_mapping (\<lambda>x. x \<le> j) (P(?pn \<mapsto> x))"
      using 1(3) that(1) by auto
    have "progress \<sigma> (P(?pn \<mapsto> x)) ?\<psi>' j = progress \<sigma> (P(?pn \<mapsto> x)) (frz_rw (?pn # B) \<psi>) j"
      by (rule progress_hoist[OF pm _ that]) simp
    also have "\<dots> = progress \<sigma> (P(?pn \<mapsto> x)) \<psi> j"
      by (rule 1(2)[OF refl refl pm full_env_Cons_upd[OF 1(4)]])
    finally show ?thesis .
  qed
  have le: "progress \<sigma> (P(?pn \<mapsto> 0)) ?\<psi>' j \<le> j" "progress \<sigma> (P(?pn \<mapsto> 0)) \<psi> j \<le> j"
    by (rule progress_le_gen; use 1(3) in simp)+
  have "progress \<sigma> P (Formula.Frz p ?\<phi>' ?\<psi>') j = progress \<sigma> P (Formula.Frz p \<phi> \<psi>) j"
  proof (cases ?fl)
    case False
    then show ?thesis
      using \<psi> by (simp add: frz_progress_def Let_def \<phi>)
  next
    case True
    have a: "progress \<sigma> P \<phi> j = j"
      using progress_full_now[OF 1(3,4) True, of \<sigma>] \<phi> by simp
    have \<psi>j: "progress \<sigma> (P(?pn \<mapsto> j)) ?\<psi>' j = progress \<sigma> (P(?pn \<mapsto> j)) \<psi> j"
      by (rule \<psi>) simp_all
    have "(\<lambda>i. i \<le> j \<and> progress \<sigma> (P(?pn \<mapsto> (if i < j then j else 0))) ?\<psi>' j \<le> i) =
      (\<lambda>i. i \<le> j \<and> progress \<sigma> (P(?pn \<mapsto> (if i < j then j else 0))) \<psi> j \<le> i)"
    proof
      fix i
      show "(i \<le> j \<and> progress \<sigma> (P(?pn \<mapsto> (if i < j then j else 0))) ?\<psi>' j \<le> i) =
        (i \<le> j \<and> progress \<sigma> (P(?pn \<mapsto> (if i < j then j else 0))) \<psi> j \<le> i)"
        using \<psi>j le by (cases "i < j") auto
    qed    then show ?thesis
      by (simp add: frz_progress_def Let_def \<phi> a)
  qed
  moreover have "progress \<sigma> P (Formula.Let p ?\<phi>' ?\<psi>') j =
    progress \<sigma> P (Formula.Frz p ?\<phi>' ?\<psi>') j" if "now_only ?pn ?\<psi>'"
    using progress_Frz_now_only[of p ?\<phi>' ?\<psi>' j P \<sigma>] that 1(3) by simp
  ultimately show ?case
    by (simp add: Let_def)
next
  case (2 B p \<phi> \<psi>)
  have "progress \<sigma> P \<phi> j \<le> j"
    by (rule progress_le_gen[OF 2(3)])
  then have pm: "pred_mapping (\<lambda>x. x \<le> j) (P((p, Formula.nfv \<phi>) \<mapsto> progress \<sigma> P \<phi> j))"
    using 2(3) by simp
  show ?case
    using 2(1)[OF 2(3,4)] 2(2)[OF pm full_env_Cons_upd[OF 2(4)]] by (simp add: fun_upd_def)
qed (auto simp: o_def cong: map_cong)

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

lemma fvi_frz_opt[simp]: "Formula.fvi b (frz_opt \<phi>) = Formula.fvi b \<phi>"
  by (simp add: frz_opt_def Let_def)

lemma nfv_frz_opt[simp]: "Formula.nfv (frz_opt \<phi>) = Formula.nfv \<phi>"
  by (simp add: frz_opt_def Let_def)

lemma sat_frz_opt[simp]: "Formula.sat \<sigma> V v i (frz_opt \<phi>) = Formula.sat \<sigma> V v i \<phi>"
  by (simp add: frz_opt_def Let_def)

lemma progress_frz_opt:
  "pred_mapping (\<lambda>x. x \<le> j) P \<Longrightarrow> full_env [] P j \<Longrightarrow> progress \<sigma> P (frz_opt \<phi>) j = progress \<sigma> P \<phi> j"
  by (simp add: frz_opt_def Let_def progress_frz_rw)

lemma progress_frz_opt_empty[simp]: "progress \<sigma> Map.empty (frz_opt \<phi>) j = progress \<sigma> Map.empty \<phi> j"
  by (simp add: progress_frz_opt full_env_def)

lemma wty_frz_opt: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> frz_opt \<phi>"
  by (simp add: frz_opt_def Let_def wty_frz_rw)

lemma mmonitorable_frz_opt: "mmonitorable \<phi> \<Longrightarrow> mmonitorable (frz_opt \<phi>)"
  by (simp add: frz_opt_def Let_def mmonitorable_exec_mmonitorable)

(*<*)
end
(*>*)
