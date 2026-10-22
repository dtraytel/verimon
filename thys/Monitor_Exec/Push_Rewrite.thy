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

lemma ands_cstr_Some:
  "ands_cstr c l = Some l' \<Longrightarrow> \<exists>xs e ys. l = xs @ e # ys \<and> l' = xs @ Formula.And e c # ys \<and>
     safe_formula e \<and> Formula.fv c \<subseteq> Formula.fv e"
proof (induct l arbitrary: l')
  case (Cons e es)
  show ?case
  proof (cases "is_wagg e \<and> safe_formula e \<and> Formula.fv c \<subseteq> Formula.fv e")
    case True
    with Cons.prems show ?thesis by (intro exI[of _ "[]"]) auto
  next
    case False
    with Cons.prems obtain l'' where l'': "ands_cstr c es = Some l''" "l' = e # l''" by auto
    from Cons.hyps[OF l''(1)] obtain xs e' ys where
      "es = xs @ e' # ys" "l'' = xs @ Formula.And e' c # ys" "safe_formula e'" "Formula.fv c \<subseteq> Formula.fv e'"
      by blast
    with l''(2) show ?thesis by (intro exI[of _ "e # xs"]) auto
  qed
qed simp

lemma and_cstr_cases:
  obtains "and_cstr X c = Formula.And X c"
  | xs e ys where "X = Formula.Ands (xs @ e # ys)" "is_cmp c" "safe_formula e"
    "Formula.fv c \<subseteq> Formula.fv e" "and_cstr X c = Formula.Ands (xs @ Formula.And e c # ys)"
proof (cases "\<exists>l l'. X = Formula.Ands l \<and> is_cmp c \<and> ands_cstr c l = Some l'")
  case True
  then obtain l l' where s: "X = Formula.Ands l" "is_cmp c" "ands_cstr c l = Some l'" by blast
  from ands_cstr_Some[OF s(3)] obtain xs e ys where
    t: "l = xs @ e # ys" "l' = xs @ Formula.And e c # ys" "safe_formula e" "Formula.fv c \<subseteq> Formula.fv e"
    by blast
  show thesis by (rule that(2)[of xs e ys]) (simp_all add: and_cstr_def s(1,2) t s(3)[unfolded t])
next
  case False
  then have "and_cstr X c = Formula.And X c"
    unfolding and_cstr_def by (auto split: Formula.formula.split option.split)
  then show thesis by (rule that(1))
qed

lemma and_cstr_shape: "(\<exists>a b. and_cstr X c = Formula.And a b) \<or> (\<exists>l. and_cstr X c = Formula.Ands l)"
  by (cases rule: and_cstr_cases[of X c]) auto

lemma and_cstr_shapes[simp]:
  "\<not> is_constraint (and_cstr X c)"
  "\<not> safe_assignment Y (and_cstr X c)"
  "and_cstr X c \<noteq> Formula.Neg \<psi>"
  "remove_neg (and_cstr X c) = and_cstr X c"
  "\<not> Formula.is_Trigger (and_cstr X c)"
  "\<not> Formula.is_Release (and_cstr X c)"
  "and_cstr X c \<noteq> Formula.Eq t1 t2"
  "and_cstr X c \<noteq> Formula.Less t1 t2"
  "and_cstr X c \<noteq> Formula.LessEq t1 t2"
  using and_cstr_shape[of X c] by (elim disjE exE; simp add: safe_assignment_def)+

lemma fvi_and_cstr[simp]: "Formula.fvi b (and_cstr X c) = Formula.fvi b (Formula.And X c)"
  by (cases rule: and_cstr_cases[of X c]) auto

lemma sat_and_cstr[simp]:
  "Formula.sat \<sigma> V v i (and_cstr X c) = Formula.sat \<sigma> V v i (Formula.And X c)"
  by (cases rule: and_cstr_cases[of X c]) auto

lemma matches_and_cstr[simp]: "Safety.matches v (and_cstr X c) e = Safety.matches v (Formula.And X c) e"
  by (cases rule: and_cstr_cases[of X c]) auto

subsection \<open>Free variables\<close>

lemma fvi_ex_into[simp]: "Formula.fvi b (ex_into t \<phi>) = Formula.fvi (Suc b) \<phi>"
  by (induct t \<phi> arbitrary: b rule: ex_into.induct) auto

lemma fvi_push_ex[simp]: "Formula.fvi b (push_ex \<phi>) = Formula.fvi b \<phi>"
  by (induct \<phi> arbitrary: b) (auto simp: push_ex_And)

lemma nfv_push_ex[simp]: "Formula.nfv (push_ex \<phi>) = Formula.nfv \<phi>"
  by (simp add: Formula.nfv_def)

subsection \<open>Satisfaction\<close>

lemma sat_ex_into[simp]:
  "Formula.sat \<sigma> V v i (ex_into t \<phi>) = (\<exists>z. Formula.sat \<sigma> V (z # v) i \<phi>)"
  by (induct t \<phi> arbitrary: v i rule: ex_into.induct) auto

lemma is_constraint_push_ex[simp]: "is_constraint (push_ex \<phi>) = is_constraint \<phi>"
proof (cases \<phi>)
  case (Neg \<psi>)
  then show ?thesis by (auto simp: is_constraint_Neg_iff push_ex_comparison)
qed (auto simp: push_ex_And)

lemma safe_assignment_push_ex[simp]: "safe_assignment X (push_ex \<phi>) = safe_assignment X \<phi>"
proof (cases \<phi>)
  case (Exists t \<psi>)
  then show ?thesis
    using ex_into_shapes(2)[of X t "push_ex \<psi>"] by (simp add: safe_assignment_def)
next
  case (And \<phi>1 \<psi>)
  then show ?thesis
    using and_cstr_shapes(2)[of X "push_ex \<phi>1" "push_ex \<psi>"] by (simp add: push_ex_And safe_assignment_def)
qed (simp_all add: push_ex_And safe_assignment_def)

lemma remove_neg_push_ex[simp]: "remove_neg (push_ex \<phi>) = push_ex (remove_neg \<phi>)"
  by (cases \<phi>) (auto simp: push_ex_And)

lemma is_Trigger_push_ex[simp]: "Formula.is_Trigger (push_ex \<phi>) = Formula.is_Trigger \<phi>"
  and is_Release_push_ex[simp]: "Formula.is_Release (push_ex \<phi>) = Formula.is_Release \<phi>"
  by (cases \<phi>; simp add: push_ex_And)+

subsection \<open>Safety\<close>

lemma safe_ex_into[simp]: "safe_formula (ex_into t \<phi>) = (safe_formula \<phi> \<and> 0 \<in> Formula.fv \<phi>)"
  by (induct t \<phi> rule: ex_into.induct) auto

lemma safe_push_ex[simp]: "safe_formula (push_ex \<phi>) = safe_formula \<phi>"
proof (induct \<phi> rule: measure_induct_rule[where f = size])
  case (less \<phi>)
  show ?case
  proof (cases \<phi>)
    case (And \<phi>1 \<psi>)
    show ?thesis
    proof (cases "Formula.is_Trigger \<psi> \<or> Formula.is_Release \<psi>")
      case True
      then show ?thesis by (simp add: And push_ex_And)
    next
      case False
      then have nt: "\<not> Formula.is_Trigger \<psi>" "\<not> Formula.is_Release \<psi>" by simp_all
      have i1: "safe_formula (push_ex \<phi>1) = safe_formula \<phi>1"
        and i2: "safe_formula (push_ex \<psi>) = safe_formula \<psi>"
        by (rule less; simp add: And)+
      have i3: "(case \<psi> of Formula.Neg \<psi>' \<Rightarrow> safe_formula (push_ex \<psi>') | _ \<Rightarrow> False)
          = (case \<psi> of Formula.Neg \<psi>' \<Rightarrow> safe_formula \<psi>' | _ \<Rightarrow> False)"
        by (cases \<psi>) (simp_all add: And less)
      show ?thesis
        unfolding And push_ex_And
        by (simp del: safe_formula.simps(10) add: nt safe_And_not_TR case_Neg_push_ex i1 i2 i3)
    qed
  next
    case (Ands l)
    have s1: "size x < size \<phi>" if "x \<in> set l" for x
      using size_list_estimation'[of x l "size x" size] that by (simp add: Ands)
    have s2: "size (remove_neg x) < size \<phi>" if "x \<in> set l" for x
      using size_list_estimation'[of x l "size (remove_neg x)" size] that size_remove_neg[of x]
      by (simp add: Ands)
    have i: "\<And>x. x \<in> set l \<Longrightarrow> safe_formula (push_ex x) = safe_formula x"
      by (rule less, rule s1)
    have j: "\<And>x. x \<in> set l \<Longrightarrow> safe_formula (push_ex (remove_neg x)) = safe_formula (remove_neg x)"
      by (rule less, rule s2)
    have p: "partition safe_formula (map push_ex l)
        = (map push_ex (filter safe_formula l), map push_ex (filter (Not \<circ> safe_formula) l))"
      by (auto simp: filter_map o_def i cong: filter_cong)
    show ?thesis
      unfolding Ands push_ex.simps safe_formula.simps p
      by (auto simp: list.pred_map list_all_iff o_def j)
  next
    case (Since \<phi>1 I \<psi>)
    have "(case \<phi>1 of Formula.Neg \<psi>' \<Rightarrow> safe_formula (push_ex \<psi>') | _ \<Rightarrow> False)
        = (case \<phi>1 of Formula.Neg \<psi>' \<Rightarrow> safe_formula \<psi>' | _ \<Rightarrow> False)"
      by (cases \<phi>1) (simp_all add: Since less)
    then show ?thesis by (simp add: Since case_Neg_push_ex less)
  next
    case (Until \<phi>1 I \<psi>)
    have "(case \<phi>1 of Formula.Neg \<psi>' \<Rightarrow> safe_formula (push_ex \<psi>') | _ \<Rightarrow> False)
        = (case \<phi>1 of Formula.Neg \<psi>' \<Rightarrow> safe_formula \<psi>' | _ \<Rightarrow> False)"
      by (cases \<phi>1) (simp_all add: Until less)
    then show ?thesis by (simp add: Until case_Neg_push_ex less)
  qed (simp_all add: less)
qed

subsection \<open>Future-boundedness, monitorability and relevant events\<close>

lemma future_bounded_ex_into[simp]:
  "Safety.future_bounded (ex_into t \<phi>) = Safety.future_bounded \<phi>"
  by (induct t \<phi> rule: ex_into.induct) auto

lemma future_bounded_push_ex[simp]: "Safety.future_bounded (push_ex \<phi>) = Safety.future_bounded \<phi>"
  by (induct \<phi>) (auto simp: push_ex_And list.pred_map o_def cong: list.pred_cong)

lemma mmonitorable_push_ex[simp]: "mmonitorable (push_ex \<phi>) = mmonitorable \<phi>"
  by (simp add: mmonitorable_def)

lemma matches_ex_into[simp]:
  "Safety.matches v (ex_into t \<phi>) e = (\<exists>z. Safety.matches (z # v) \<phi> e)"
  by (induct t \<phi> arbitrary: v rule: ex_into.induct) (auto simp: Formula.TT_def)

lemma matches_push_ex[simp]: "Safety.matches v (push_ex \<phi>) e = Safety.matches v \<phi> e"
  by (induct \<phi> arbitrary: v e) (auto simp: push_ex_And)

subsection \<open>Progress\<close>

lemma pprogress_push_ex[simp]: "pprogress (push_ex \<phi>) = pprogress \<phi>"
  by (simp add: pprogress_def fun_eq_iff)

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

lemma fvi_eprep[simp]: "Formula.fvi b (eprep \<phi>) = Formula.fvi b \<phi>"
  by (simp add: eprep_def)

lemma nfv_eprep[simp]: "Formula.nfv (eprep \<phi>) = Formula.nfv \<phi>"
  by (simp add: eprep_def)

lemma sat_eprep[simp]: "Formula.sat \<sigma> V v i (eprep \<phi>) = Formula.sat \<sigma> V v i \<phi>"
  by (simp add: eprep_def)

lemma pprogress_eprep[simp]: "pprogress (eprep \<phi>) = pprogress \<phi>"
  by (simp add: pprogress_def fun_eq_iff eprep_def)

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

context verimon_spec
begin

end

text \<open>The front end's entry point: the executable monitor started on the rewritten formula, the state
  of @{thm [source] verimon_spec.emonitor_mverdicts_push}.\<close>

definition eminit_push :: "ty Formula.formula \<Rightarrow> emstate" where
  "eminit_push \<phi> = eminit_safe (eprep \<phi>)"

end
(*>*)
