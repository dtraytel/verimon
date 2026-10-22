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

lemma wty_and_cstr:
  assumes "S, E \<turnstile> Formula.And X c"
  shows "S, E \<turnstile> and_cstr X c"
proof (cases rule: and_cstr_cases[of X c])
  case (2 xs e ys)
  from assms have a: "S, E \<turnstile> Formula.Ands (xs @ e # ys)" "S, E \<turnstile> c"
    unfolding 2(1) by (auto dest: wty_formula_AndD)
  have "\<forall>\<phi> \<in> set (xs @ Formula.And e c # ys). S, E \<turnstile> \<phi>"
    using wty_formula_AndsD[OF a(1)] a(2) by (auto intro: wty_formula.And)
  then show ?thesis
    unfolding 2(5) by (rule wty_formula.Ands)
qed (use assms in simp)

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

lemma wty_ex_into: "S, case_nat t E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> ex_into t \<phi>"
proof (induct t \<phi> arbitrary: E rule: ex_into.induct)
  case (1 t \<phi> I \<psi>)
  then show ?case
    by (auto intro!: wty_formula.intros elim: wty_formula.cases)
next
  case (2 t \<phi> I \<psi>)
  then show ?case
    by (auto intro!: wty_formula.intros elim: wty_formula.cases)
qed (simp only: ex_into.simps, rule wty_formula.Exists, assumption)+

lemma wty_push_ex: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> push_ex \<phi>"
  by (induct rule: wty_formula.induct)
    (auto simp: push_ex_And fun_upd_def intro!: wty_formula.intros wty_ex_into wty_and_cstr elim: regex.pred_mono_strong)

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

lemma wty_eprep: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> eprep \<phi>"
  by (simp add: eprep_def wty_share_opt wty_push_ex wty_frz_opt)

lemma mmonitorable_eprep: "mmonitorable \<phi> \<Longrightarrow> mmonitorable (eprep \<phi>)"
  by (simp add: eprep_def mmonitorable_share_opt mmonitorable_frz_opt)

lemma M_perm: "q.M \<pi> = (\<lambda>(i, v). (i, restrict (Formula.fv_list \<psi>) (Formula.fv_list \<phi>) v)) ` p.M \<pi>"
proof -
  let ?ds = "Formula.fv_list \<psi>"
  let ?cs = "Formula.fv_list \<phi>"
  have set_cs: "set ?ds = set ?cs" "set ?cs = set ?ds"
    by (simp_all add: fv)
  have restrict_back: "restrict ?ds ?cs (restrict ?cs ?ds v) = v"
    if "wf_tuple ?ds v" for v :: "event_data list"
    using that by (subst restrict_restrict) (simp_all add: fv restrict_idle)
  have val_ds: "val (Formula.nfv \<phi>) ?ds (restrict ?ds ?cs v) = val (Formula.nfv \<phi>) ?cs v"
    for v :: "event_data list"
    by (rule val_restrict_perm) (rule set_cs)
  have val_cs: "val (Formula.nfv \<phi>) ?cs (restrict ?cs ?ds v) = val (Formula.nfv \<phi>) ?ds v"
    for v :: "event_data list"
    by (rule val_restrict_perm) (rule set_cs)
  have to_\<phi>: "wf_tuple ?ds v \<and> (i, restrict ?cs ?ds v) \<in> p.M \<pi>" if "(i, v) \<in> q.M \<pi>" for i v
    using that unfolding q.M_def p.M_def
    by (simp add: sat nfv pp val_cs)
  have to_\<psi>: "(i, restrict ?ds ?cs v) \<in> q.M \<pi>" if "(i, v) \<in> p.M \<pi>" for i v
    using that unfolding q.M_def p.M_def
    by (simp add: sat nfv pp val_ds)
  show ?thesis
  proof (rule set_eqI, safe)
    fix i v
    assume "(i, v) \<in> q.M \<pi>"
    with to_\<phi>[OF this] show "(i, v) \<in> (\<lambda>(i, v). (i, restrict ?ds ?cs v)) ` p.M \<pi>"
      by (auto simp: restrict_back intro!: image_eqI[where x = "(i, restrict ?cs ?ds v)"])
  qed (rule to_\<psi>)
qed

lemma Mt_perm: "q.Mt \<pi> = (\<lambda>(i, t, v). (i, t, restrict (Formula.fv_list \<psi>) (Formula.fv_list \<phi>) v)) ` p.Mt \<pi>"
  unfolding q.Mt_def p.Mt_def M_perm image_image
  by (simp add: split_beta)

lemma flatten_verdicts_map_comp:
  "flatten_verdicts (map (\<lambda>(i, t, X). (i, t, f ` g X)) Vs) =
    (\<lambda>(i, t, v). (i, t, f v)) ` flatten_verdicts (map (\<lambda>(i, t, X). (i, t, g X)) Vs)"
  by (auto simp: flatten_verdicts_def image_UN image_image split_beta)

lemma fv_list_eprep_ecols: "ecols (Formula.fv_list (eprep \<phi>)) = ecols (Formula.fv_list \<phi>)"
  by (rule ecols_cong) simp

context verimon_spec
begin

theorem emonitor_mverdicts_push:
  assumes zf: "efail_nodes (eabs (emstate_m (eof_state (Formula.nfv \<phi>) (Formula.fv_list (eprep \<phi>))
      (ecols (Formula.fv_list (eprep \<phi>))) (minit_safe (eprep \<phi>))))) = 0"
    and f: "pfinite \<pi>" and wty: "wty_prefix SIG \<pi>"
  shows "flatten_verdicts (map (\<lambda>(i, t, X).
      (i, t, etabw (Formula.fv_list \<phi>) (ecols (Formula.fv_list \<phi>)) X))
      (emonitor (eof_state (Formula.nfv \<phi>) (Formula.fv_list (eprep \<phi>))
         (ecols (Formula.fv_list (eprep \<phi>))) (minit_safe (eprep \<phi>))) \<pi>)) = Mt \<pi>"
proof -
  let ?\<chi> = "eprep \<phi>"
  interpret p: verimon_spec ?\<chi> SIG ENV
    by unfold_locales
      (simp_all add: wty_eprep[OF well_typed] mmonitorable_eprep[OF monitorable])
  let ?ks = "Formula.fv_list ?\<chi>" and ?ls = "Formula.fv_list \<phi>" and ?cs = "ecols (Formula.fv_list \<phi>)"
  have cs: "ecols ?ks = ?cs"
    by (rule fv_list_eprep_ecols)
  have v: "flatten_verdicts (map (\<lambda>(i, t, X). (i, t, etabw ?ks ?cs X))
      (emonitor (eof_state (Formula.nfv \<phi>) ?ks ?cs (minit_safe ?\<chi>)) \<pi>)) = p.Mt \<pi>"
    using p.emonitor_mverdicts_dof[OF _ f wty] zf by (simp add: cs)
  have Mt: "Mt \<pi> = (\<lambda>(i, t, v). (i, t, restrict ?ls ?ks v)) ` p.Mt \<pi>"
    by (rule Mt_perm[where S = SIG and E = ENV])
      (simp_all add: future_bounded_mfodl_axioms p.future_bounded_mfodl_axioms fun_eq_iff)
  have r: "restrict ?ls ?ks (restrict ?ks ?cs d) = restrict ?ls ?cs d" for d :: "event_data list"
    by (rule restrict_restrict) simp
  have w: "etabw ?ls ?cs X = restrict ?ls ?ks ` etabw ?ks ?cs X" for X :: "event_data list set"
    by (simp add: etabw_def image_image r)
  show ?thesis
    unfolding cs w flatten_verdicts_map_comp v Mt ..
qed

end

text \<open>The front end's entry point: the executable monitor started on the rewritten formula, the state
  of @{thm [source] verimon_spec.emonitor_mverdicts_push}.\<close>

definition eminit_push :: "ty Formula.formula \<Rightarrow> emstate" where
  "eminit_push \<phi> = eminit_safe (eprep \<phi>)"

end
(*>*)
