(*<*)
theory Exec_Preparation
  imports Exec_Compiler Freeze_Hoisting Release_Sharing "MFODL_Logic.Preparation"
begin
(*>*)



section \<open>Preparation of the formula\<close>

subsection \<open>Quantifiers and comparisons moved inward\<close>

text \<open>@{text "\<exists>y. ONCE[I] \<phi>"} equals @{text "ONCE[I] (\<exists>y. \<phi>)"}, and likewise for
  @{text EVENTUALLY}; inside the window the projection happens once, on the entering tuples.\<close>

text \<open>Equality on formulas is not executable, so @{const Formula.TT} is recognised by its shape.\<close>

definition is_TT :: "'t Formula.formula \<Rightarrow> bool" where
  [simp]: "is_TT \<phi> \<longleftrightarrow> \<phi> = Formula.TT"

lemma is_TT_code[code]:
  "is_TT \<phi> = (case \<phi> of Formula.Eq (Formula.Const (EInt i)) (Formula.Const (EInt j)) \<Rightarrow>
      i = 0 \<and> j = 0 | _ \<Rightarrow> False)"
proof (cases \<phi>)
  case (Eq t1 t2)
  then show ?thesis
    by (cases t1; cases t2) (auto simp: Formula.TT_def split: event_data.split)
qed (simp_all add: Formula.TT_def)

fun ex_into :: "'t \<Rightarrow> 't Formula.formula \<Rightarrow> 't Formula.formula" where
  "ex_into t (Formula.Since \<phi> I \<psi>) =
     (if is_TT \<phi> then Formula.Since Formula.TT I (ex_into t \<psi>)
      else Formula.Exists t (Formula.Since \<phi> I \<psi>))"
| "ex_into t (Formula.Until \<phi> I \<psi>) =
     (if is_TT \<phi> then Formula.Until Formula.TT I (ex_into t \<psi>)
      else Formula.Exists t (Formula.Until \<phi> I \<psi>))"
| "ex_into t \<phi> = Formula.Exists t \<phi>"

text \<open>A comparison conjoined to a multiway conjunction moves onto the first safe window
  aggregation binding its variables, where it filters the groups before they are built.\<close>

definition is_cmp :: "'t Formula.formula \<Rightarrow> bool" where
  "is_cmp c = (case c of Formula.Less _ _ \<Rightarrow> True | Formula.LessEq _ _ \<Rightarrow> True | _ \<Rightarrow> False)"

definition is_wagg :: "'t Formula.formula \<Rightarrow> bool" where
  "is_wagg e = (case e of Formula.Agg _ _ _ _ (Formula.Since _ _ _) \<Rightarrow> True
     | Formula.Agg _ _ _ _ (Formula.Until _ _ _) \<Rightarrow> True | _ \<Rightarrow> False)"

fun ands_cstr :: "'t Formula.formula \<Rightarrow> 't Formula.formula list \<Rightarrow> 't Formula.formula list option" where
  "ands_cstr c [] = None"
| "ands_cstr c (e # es) = (if is_wagg e \<and> safe_formula e \<and> Formula.fv c \<subseteq> Formula.fv e
     then Some (Formula.And e c # es) else map_option ((#) e) (ands_cstr c es))"

definition and_cstr :: "'t Formula.formula \<Rightarrow> 't Formula.formula \<Rightarrow> 't Formula.formula" where
  "and_cstr X c = (case X of
      Formula.Ands l \<Rightarrow> (if is_cmp c then (case ands_cstr c l of
          Some l' \<Rightarrow> Formula.Ands l' | None \<Rightarrow> Formula.And X c) else Formula.And X c)
    | _ \<Rightarrow> Formula.And X c)"

fun push_ex :: "'t Formula.formula \<Rightarrow> 't Formula.formula" where
  "push_ex (Formula.Exists t \<phi>) = ex_into t (push_ex \<phi>)"
| "push_ex (Formula.Neg \<phi>) = Formula.Neg (push_ex \<phi>)"
| "push_ex (Formula.Or \<phi> \<psi>) = Formula.Or (push_ex \<phi>) (push_ex \<psi>)"
| "push_ex (Formula.And \<phi> \<psi>) = (case \<psi> of
      Formula.Trigger _ _ _ \<Rightarrow> Formula.And \<phi> \<psi>
    | Formula.Release _ _ _ \<Rightarrow> Formula.And \<phi> \<psi>
    | _ \<Rightarrow> and_cstr (push_ex \<phi>) (push_ex \<psi>))"
| "push_ex (Formula.Ands l) = Formula.Ands (map push_ex l)"
| "push_ex (Formula.Let p \<phi> \<psi>) = Formula.Let p (push_ex \<phi>) (push_ex \<psi>)"
| "push_ex (Formula.Agg y \<omega> tys f \<phi>) = Formula.Agg y \<omega> tys f (push_ex \<phi>)"
| "push_ex (Formula.Prev I \<phi>) = Formula.Prev I (push_ex \<phi>)"
| "push_ex (Formula.Next I \<phi>) = Formula.Next I (push_ex \<phi>)"
| "push_ex (Formula.Since \<phi> I \<psi>) = Formula.Since (push_ex \<phi>) I (push_ex \<psi>)"
| "push_ex (Formula.Until \<phi> I \<psi>) = Formula.Until (push_ex \<phi>) I (push_ex \<psi>)"
| "push_ex \<phi> = \<phi>"

text \<open>The conjunction's case distinction, folded into a test for structural induction.\<close>

lemma push_ex_And:
  "push_ex (Formula.And \<phi> \<psi>) = (if Formula.is_Trigger \<psi> \<or> Formula.is_Release \<psi>
     then Formula.And \<phi> \<psi> else and_cstr (push_ex \<phi>) (push_ex \<psi>))"
  by (cases \<psi>) simp_all

declare push_ex.simps(4)[simp del]

lemma fvi_ex_into[simp]: "Formula.fvi b (ex_into t \<phi>) = Formula.fvi (Suc b) \<phi>"
  by (induct t \<phi> arbitrary: b rule: ex_into.induct) auto

lemma sat_ex_into[simp]:
  "Formula.sat \<sigma> V v i (ex_into t \<phi>) = (\<exists>z. Formula.sat \<sigma> V (z # v) i \<phi>)"
  by (induct t \<phi> arbitrary: v i rule: ex_into.induct) auto

lemma safe_ex_into[simp]: "safe_formula (ex_into t \<phi>) = (safe_formula \<phi> \<and> 0 \<in> Formula.fv \<phi>)"
  by (induct t \<phi> rule: ex_into.induct) auto

lemma future_bounded_ex_into[simp]:
  "Safety.future_bounded (ex_into t \<phi>) = Safety.future_bounded \<phi>"
  by (induct t \<phi> rule: ex_into.induct) auto

lemma matches_ex_into[simp]:
  "Safety.matches v (ex_into t \<phi>) e = (\<exists>z. Safety.matches (z # v) \<phi> e)"
  by (induct t \<phi> arbitrary: v rule: ex_into.induct) (auto simp: Formula.TT_def)

subsection \<open>Prepared formula and initial state\<close>

text \<open>The monitor starts on @{term "eprep \<phi>"}, which hoists frozen predicates, moves
  quantifiers into windows and shares the right operands of releases.\<close>

definition eprep :: "ty Formula.formula \<Rightarrow> ty Formula.formula" where
  "eprep \<phi> = share_opt (push_ex (frz_opt \<phi>))"

context verimon_spec
begin

end

definition eminit_push :: "ty Formula.formula \<Rightarrow> emstate" where
  "eminit_push \<phi> = eminit_safe (eprep \<phi>)"

lemma fvi_list_map_formula[simp]:
  "Formula.fvi_list b (Formula.formula.map_formula g \<phi>) = Formula.fvi_list b \<phi>"
proof (induction b \<phi> rule: Formula.fvi_list.induct)
  case (20 b I r)
  then show ?case
    by (induction r) auto
next
  case (21 b I r)
  then show ?case
    by (induction r) auto
qed (auto simp: fold_map comp_def cong: fold_cong)

text \<open>@{const share_opt} precedes the multiway conversion, which copies a release's right
  operand.\<close>

definition eminit_verimon where
  "eminit_verimon ix mw rw sig \<phi> =
     map_sum id (\<lambda>\<psi>. eindex ix (eminit_push (if mw then convert_multiway (share_opt \<psi>) else \<psi>)))
       (prepare_verimon rw sig \<phi>)"

(*<*)
end
(*>*)
