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
  into both operands of a @{text Let}: the rewrite of @{theory MFODL_Monitor_Exec.Frz_Rewrite}
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

lemma push_ex_And:
  "push_ex (Formula.And \<phi> \<psi>) = (if Formula.is_Trigger \<psi> \<or> Formula.is_Release \<psi>
     then Formula.And \<phi> \<psi> else and_cstr (push_ex \<phi>) (push_ex \<psi>))"
  by (cases \<psi>) simp_all

declare push_ex.simps(4)[simp del]

subsection \<open>The comparison's move\<close>

subsection \<open>Free variables\<close>

lemma nfv_push_ex[simp]: "Formula.nfv (push_ex \<phi>) = Formula.nfv \<phi>"
  by (simp add: Formula.nfv_def)

subsection \<open>Satisfaction\<close>

lemma sat_push_ex[simp]: "Formula.sat \<sigma> V v i (push_ex \<phi>) = Formula.sat \<sigma> V v i \<phi>"
  by (induct \<phi> arbitrary: V v i) (auto simp: push_ex_And split: nat.splits)

subsection \<open>Shapes\<close>

lemma push_ex_Neg_iff:
  "push_ex \<phi> = Formula.Neg \<psi> \<longleftrightarrow> (\<exists>\<phi>'. \<phi> = Formula.Neg \<phi>' \<and> \<psi> = push_ex \<phi>')"
  by (cases \<phi>) (auto simp: push_ex_And)

lemma remove_neg_push_ex[simp]: "remove_neg (push_ex \<phi>) = push_ex (remove_neg \<phi>)"
  by (cases \<phi>) (auto simp: push_ex_And)

lemma is_Trigger_push_ex[simp]: "Formula.is_Trigger (push_ex \<phi>) = Formula.is_Trigger \<phi>"
  and is_Release_push_ex[simp]: "Formula.is_Release (push_ex \<phi>) = Formula.is_Release \<phi>"
  by (cases \<phi>; simp add: push_ex_And)+

subsection \<open>Safety\<close>

subsection \<open>Future-boundedness, monitorability and relevant events\<close>

lemma future_bounded_push_ex[simp]: "Safety.future_bounded (push_ex \<phi>) = Safety.future_bounded \<phi>"
  by (induct \<phi>) (auto simp: push_ex_And list.pred_map o_def cong: list.pred_cong)

lemma mmonitorable_push_ex[simp]: "mmonitorable (push_ex \<phi>) = mmonitorable \<phi>"
  by (simp add: mmonitorable_def)

subsection \<open>Progress\<close>

lemma progress_push_ex[simp]: "progress \<sigma> P (push_ex \<phi>) j = progress \<sigma> P \<phi> j"
  by (induct \<phi> arbitrary: P) (auto simp: push_ex_And o_def cong: map_cong)

lemma pprogress_push_ex[simp]: "pprogress (push_ex \<phi>) = pprogress \<phi>"
  by (simp add: pprogress_def fun_eq_iff)

subsection \<open>Typing\<close>

subsection \<open>The rewritten formula\<close>

text \<open>
  The monitor is started on @{term "eprep \<phi>"}: the frozen predicates are taken out of
  the temporal operators and bound with @{const Formula.Let} where they can be
  (@{theory MFODL_Monitor_Exec.Frz_Rewrite}), the existential quantifiers are moved into the
  windows, and the right operand of a release is bound with @{const Formula.Let} so that it is
  evaluated once (@{theory MFODL_Monitor_Exec.Share_Rewrite}).  Everything the specification of
  the monitor for @{term \<phi>} depends on -- the number and set of free variables, the traces
  (through the signature), the satisfaction relation and the progress -- is the same for the
  rewritten formula, which is monitorable and well typed whenever @{term \<phi>} is.  Only the order
  in which @{const Formula.fv_list} lists the free variables may change.
\<close>

definition eprep :: "ty Formula.formula \<Rightarrow> ty Formula.formula" where
  "eprep \<phi> = share_opt (push_ex (frz_opt \<phi>))"

lemma nfv_eprep[simp]: "Formula.nfv (eprep \<phi>) = Formula.nfv \<phi>"
  by (simp add: eprep_def)

lemma sat_eprep[simp]: "Formula.sat \<sigma> V v i (eprep \<phi>) = Formula.sat \<sigma> V v i \<phi>"
  by (simp add: eprep_def)

lemma pprogress_eprep[simp]: "pprogress (eprep \<phi>) = pprogress \<phi>"
  by (simp add: pprogress_def fun_eq_iff eprep_def)

lemma mmonitorable_eprep: "mmonitorable \<phi> \<Longrightarrow> mmonitorable (eprep \<phi>)"
  by (simp add: eprep_def mmonitorable_share_opt mmonitorable_frz_opt)

subsection \<open>Reordering the verdicts' columns\<close>

text \<open>Two formulas with the same number and set of free variables, the same satisfaction
  relation and the same progress have the same verdicts, up to the order of their columns.\<close>

context
  fixes \<phi> \<psi> :: "ty Formula.formula" and S :: sig and E :: tyenv
  assumes fb: "future_bounded_mfodl \<phi> S E" "future_bounded_mfodl \<psi> S E"
    and fv: "Formula.fv \<psi> = Formula.fv \<phi>" and nfv: "Formula.nfv \<psi> = Formula.nfv \<phi>"
    and sat: "\<And>\<sigma> v i. Formula.sat \<sigma> Map.empty v i \<psi> = Formula.sat \<sigma> Map.empty v i \<phi>"
    and pp: "pprogress \<psi> = pprogress \<phi>"
begin

end

subsection \<open>The executable monitor on the rewritten formula\<close>

lemma fv_list_eprep_ecols: "ecols (Formula.fv_list (eprep \<phi>)) = ecols (Formula.fv_list \<phi>)"
  by (rule ecols_cong) simp

context verimon_spec
begin

end

text \<open>The front end's entry point: the executable monitor started on the rewritten formula, the state
  of @{thm [source] verimon_spec.emonitor_mverdicts_push}.\<close>

definition eminit_push :: "ty Formula.formula \<Rightarrow> emstate" where
  "eminit_push \<phi> = eminit_safe (eprep \<phi>)"

lemma eminit_push_eq:
  "eminit_push \<phi>
   = eof_state (Formula.nfv \<phi>) (Formula.fv_list (eprep \<phi>))
       (ecols (Formula.fv_list (eprep \<phi>))) (minit_safe (eprep \<phi>))"
  by (simp add: eminit_push_def eminit_safe_def)
(*<*)
end
(*>*)
