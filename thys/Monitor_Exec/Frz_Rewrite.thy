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

lemma is_frz_predD: "is_frz_pred pn q \<Longrightarrow> \<exists>e ts. q = Formula.Pred e ts \<and> (e, length ts) = pn"
  by (cases q) auto

lemma frz_find_Some:
  "frz_find pn l = Some (q, r) \<Longrightarrow> is_frz_pred pn q \<and> set l = insert q (set r)"
  by (induct l arbitrary: r) (auto split: if_splits option.splits)

lemma eval_dec_trm: "0 \<notin> Formula.fv_trm s \<Longrightarrow> Formula.eval_trm v (dec_trm s) = Formula.eval_trm (z # v) s"
  by (induct s) (auto simp: nth_Cons')

lemma fvi_dec_trm: "0 \<notin> Formula.fv_trm s \<Longrightarrow> Formula.fvi_trm b (dec_trm s) = Formula.fvi_trm (Suc b) s"
  by (induct s) auto

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
lemma sat_Frz_now_only:
  assumes "now_only (p, Formula.nfv \<phi>) \<psi>"
  shows "Formula.sat \<sigma> V v i (Formula.Frz p \<phi> \<psi>) = Formula.sat \<sigma> V v i (Formula.Let p \<phi> \<psi>)"
  using sat_now_only[OF assms, where X="\<lambda>w j. Formula.sat \<sigma> V w i \<phi>" and Y="\<lambda>w j. Formula.sat \<sigma> V w j \<phi>"]
  by simp

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

lemma fvi_frz_opt[simp]: "Formula.fvi b (frz_opt \<phi>) = Formula.fvi b \<phi>"
  by (simp add: frz_opt_def Let_def)

lemma nfv_frz_opt[simp]: "Formula.nfv (frz_opt \<phi>) = Formula.nfv \<phi>"
  by (simp add: frz_opt_def Let_def)

lemma sat_frz_opt[simp]: "Formula.sat \<sigma> V v i (frz_opt \<phi>) = Formula.sat \<sigma> V v i \<phi>"
  by (simp add: frz_opt_def Let_def)

end
(*>*)
