(*<*)
theory Push_Rewrite
  imports Compile Frz_Rewrite Share_Rewrite "MFODL_Logic.Preparation"
begin
(*>*)



section \<open>An existential quantifier moved into a window\<close>

text \<open>
  Over a window whose left operand is @{const Formula.TT} -- the past and future diamonds
  @{text "ONCE"} and @{text "EVENTUALLY"} -- an existential quantifier commutes with the window:
  @{text "\<exists>y. ONCE[I] \<phi>"} holds exactly when @{text "ONCE[I] (\<exists>y. \<phi>)"} does.  The two monitor
  very differently.  With the quantifier outside, the window keeps every tuple of @{text \<phi>} over
  the whole interval and the quantifier projects that whole result at every time point; with it
  inside, the projection happens once, on the tuples entering the window, and the window keeps
  only the projected tuples.  On @{text "C(x) AND (EXISTS y. ONCE[0,50] A(x,y))"} the first holds
  about 2000 pairs where the second holds about 200 values of @{text x}.

  @{text push_ex} makes that move everywhere it applies, and the lemmas below show that it
  changes nothing the monitor's specification depends on: the free variables, the satisfaction
  relation, the progress, the relevant events, safety, future-boundedness and typing.  It goes
  into both operands of a @{text Let}: the rewrite of @{theory Monitor_Exec.Frz_Rewrite}
  turns most freezes into one, and its body is where their windows are.  It leaves alone the
  subformulas whose treatment builds new formulas from their operands (@{text LetPast},
  @{text Frz}, the regular expressions, the trigger and release operators, and a conjunction
  with a trigger or release on the right), which keeps those lemmas structural.
\<close>

text \<open>Equality on formulas is not executable -- the intervals have no equality in the generated
  code -- so the test for @{const Formula.TT} gets a code equation that reads its shape.\<close>

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

text \<open>A comparison conjoined to a multiway conjunction is moved onto the first of its safe
  operands that binds the comparison's variables and is an aggregation over a window:
  @{text "(\<psi>\<^sub>1 AND \<dots> AND \<phi> AND \<dots>) AND c"} becomes the conjunction with @{text \<phi>} replaced by
  @{text "\<phi> AND c"}.  There the comparison can filter the aggregate's groups before they are
  built, where above the conjunction it filters the join's and the anti-joins' result.  Onto other operands the move is not made: filtering an operand instead of
  the join's result pays off only when the operand is the smaller of the two, which the rewrite
  cannot know.  The multiway conjunction is what the front end's @{const convert_multiway} makes of
  @{text "\<phi> AND NOT \<psi> AND c"}.\<close>

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

text \<open>The conjunction's equation with its case distinction folded into a test, so that the
  lemmas below can go by structural induction without splitting over every constructor.\<close>

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

subsection \<open>The rewritten formula\<close>

text \<open>
  The monitor is started on @{term "eprep \<phi>"}: the frozen predicates are taken out of
  the temporal operators and bound with @{const Formula.Let} where they can be
  (@{theory Monitor_Exec.Frz_Rewrite}), the existential quantifiers are moved into the
  windows, and the right operand of a release is bound with @{const Formula.Let} so that it is
  evaluated once (@{theory Monitor_Exec.Share_Rewrite}).  Everything the specification of
  the monitor for @{term \<phi>} depends on -- the number and set of free variables, the traces
  (through the signature), the satisfaction relation and the progress -- is the same for the
  rewritten formula, which is monitorable and well typed whenever @{term \<phi>} is.  Only the order
  in which @{const Formula.fv_list} lists the free variables may change.
\<close>

definition eprep :: "ty Formula.formula \<Rightarrow> ty Formula.formula" where
  "eprep \<phi> = share_opt (push_ex (frz_opt \<phi>))"

context verimon_spec
begin

end

definition eminit_push :: "ty Formula.formula \<Rightarrow> emstate" where
  "eminit_push \<phi> = eminit_safe (eprep \<phi>)"

end
(*>*)
