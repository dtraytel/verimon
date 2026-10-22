(*<*)
theory Freeze_Hoisting
  imports "Monitor_Algorithm.Monitor" "MFODL_Logic.Typing"
begin
(*>*)



section \<open>Hoisting of frozen predicates\<close>

text \<open>A frozen conjunct is taken out of temporal operators (@{text hoist}); once it occurs only
  at the current time point, the freeze becomes a @{term Formula.Let} (@{text now_only}).\<close>

subsection \<open>Splitting off the frozen conjunct\<close>

fun is_frz_pred :: "Formula.name \<times> nat \<Rightarrow> 't Formula.formula \<Rightarrow> bool" where
  "is_frz_pred pn (Formula.Pred e ts) = ((e, length ts) = pn)"
| "is_frz_pred pn _ = False"

text \<open>Formulas have no executable equality, so the conjunct is found by position; out of a
  quantifier its variables are renumbered (@{text dec_trm}).\<close>

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

subsection \<open>The rewrite\<close>

text \<open>If the frozen formula never lags (@{text fl}), the conjunct is also taken out of Prev and
  of a Since whose interval excludes 0; otherwise this could lower the progress.\<close>

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

text \<open>A formula that never lags: past operators over predicates not bound by an enclosing
  @{const Formula.Let} or @{const Formula.Frz} (the list @{text B}).\<close>

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

text \<open>Hoisting can make an operand unsafe, so the rewrite applies only if its result is
  monitorable.\<close>

definition frz_opt :: "ty Formula.formula \<Rightarrow> ty Formula.formula" where
  "frz_opt \<phi> = (let \<phi>' = frz_rw [] \<phi> in if mmonitorable_exec \<phi>' then \<phi>' else \<phi>)"

text \<open>The quantifier's equation is not a simp rule, so that proofs see the two outcomes of the
  split.\<close>

declare hoist.simps(8)[simp del]

end
(*>*)
