(*<*)
theory Push_Rewrite_Proof
  imports "Monitor_Exec.Push_Rewrite" Compile_Proof Frz_Rewrite_Proof Share_Rewrite_Proof "MFODL_Monitor_Proof.VeriMon" "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



text \<open>The conjunction's equation with its case distinction folded into a test, so that the
  lemmas below can go by structural induction without splitting over every constructor.\<close>

lemma push_ex_And:
  "push_ex (Formula.And \<phi> \<psi>) = (if Formula.is_Trigger \<psi> \<or> Formula.is_Release \<psi>
     then Formula.And \<phi> \<psi> else and_cstr (push_ex \<phi>) (push_ex \<psi>))"
  by (cases \<psi>) simp_all

subsection \<open>The comparison's move\<close>

text \<open>The move keeps the conjunction's operands and only regroups them; its result is a
  conjunction or a multiway conjunction.\<close>

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

lemma is_cmp_cases:
  assumes "is_cmp c"
  obtains t1 t2 where "c = Formula.Less t1 t2" | t1 t2 where "c = Formula.LessEq t1 t2"
  using assms by (cases c) (simp_all add: is_cmp_def)

lemma fvi_and_cstr[simp]: "Formula.fvi b (and_cstr X c) = Formula.fvi b (Formula.And X c)"
  by (cases rule: and_cstr_cases[of X c]) auto

lemma sat_and_cstr[simp]:
  "Formula.sat \<sigma> V v i (and_cstr X c) = Formula.sat \<sigma> V v i (Formula.And X c)"
  by (cases rule: and_cstr_cases[of X c]) auto

lemma future_bounded_and_cstr[simp]:
  "Safety.future_bounded (and_cstr X c) = Safety.future_bounded (Formula.And X c)"
  by (cases rule: and_cstr_cases[of X c]) auto

lemma matches_and_cstr[simp]: "Safety.matches v (and_cstr X c) e = Safety.matches v (Formula.And X c) e"
  by (cases rule: and_cstr_cases[of X c]) auto

lemma progress_and_cstr[simp]: "progress \<sigma> P (and_cstr X c) j = progress \<sigma> P (Formula.And X c) j"
proof (cases rule: and_cstr_cases[of X c])
  case (2 xs e ys)
  from 2(2) have pc: "progress \<sigma> P c j = j" by (cases rule: is_cmp_cases) simp_all
  show ?thesis
    using 2 pc
    by (cases "set (map (\<lambda>\<phi>. progress \<sigma> P \<phi> j) xs) \<union> set (map (\<lambda>\<phi>. progress \<sigma> P \<phi> j) ys) = {}")
      (auto simp: min.assoc min.commute min.left_commute)
qed simp

lemma safe_And_cmp: "is_cmp c \<Longrightarrow> safe_formula (Formula.And X c) = (safe_formula X \<and> Formula.fv c \<subseteq> Formula.fv X)"
  by (erule is_cmp_cases) (simp_all add: safe_assignment_def)

lemma safe_Ands_replace:
  assumes "safe_formula e" "safe_formula e'" "Formula.fv e' = Formula.fv e"
  shows "safe_formula (Formula.Ands (xs @ e' # ys)) = safe_formula (Formula.Ands (xs @ e # ys))"
  using assms by simp

lemma safe_and_cstr[simp]: "safe_formula (and_cstr X c) = safe_formula (Formula.And X c)"
proof (cases rule: and_cstr_cases[of X c])
  case (2 xs e ys)
  have l: "safe_formula (Formula.Ands (xs @ Formula.And e c # ys)) = safe_formula (Formula.Ands (xs @ e # ys))"
    by (rule safe_Ands_replace) (use 2 safe_And_cmp[OF 2(2)] in auto)
  have "Formula.fv c \<subseteq> Formula.fv (Formula.Ands (xs @ e # ys))"
    using 2(4) by auto
  then have r: "safe_formula (Formula.And X c) = safe_formula (Formula.Ands (xs @ e # ys))"
    unfolding safe_And_cmp[OF 2(2)] 2(1) by blast
  show ?thesis
    by (simp only: 2(5) l r)
qed simp

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

subsection \<open>Free variables\<close>

lemma fvi_push_ex[simp]: "Formula.fvi b (push_ex \<phi>) = Formula.fvi b \<phi>"
  by (induct \<phi> arbitrary: b) (auto simp: push_ex_And)

subsection \<open>Satisfaction\<close>

lemma sat_push_ex[simp]: "Formula.sat \<sigma> V v i (push_ex \<phi>) = Formula.sat \<sigma> V v i \<phi>"
  by (induct \<phi> arbitrary: V v i) (auto simp: push_ex_And split: nat.splits)

subsection \<open>Shapes\<close>

text \<open>The safety conditions look at a few syntactic shapes of their operands: comparisons,
  assignments and negations.  The quantifier's step never produces one of them, and the rest of
  the traversal keeps each of them as it is.\<close>

lemma ex_into_shape: "(\<exists>\<psi>. ex_into t \<phi> = Formula.Exists t \<psi>) \<or>
  (\<exists>I \<psi>. ex_into t \<phi> = Formula.Since Formula.TT I \<psi>) \<or> (\<exists>I \<psi>. ex_into t \<phi> = Formula.Until Formula.TT I \<psi>)"
  by (cases "(t, \<phi>)" rule: ex_into.cases) simp_all

lemma ex_into_shapes[simp]:
  "\<not> is_constraint (ex_into t \<phi>)"
  "\<not> safe_assignment X (ex_into t \<phi>)"
  "ex_into t \<phi> \<noteq> Formula.Neg \<psi>"
  "remove_neg (ex_into t \<phi>) = ex_into t \<phi>"
  "\<not> Formula.is_Trigger (ex_into t \<phi>)"
  "\<not> Formula.is_Release (ex_into t \<phi>)"
  "ex_into t \<phi> \<noteq> Formula.Eq t1 t2"
  "ex_into t \<phi> \<noteq> Formula.Less t1 t2"
  "ex_into t \<phi> \<noteq> Formula.LessEq t1 t2"
  using ex_into_shape[of t \<phi>] by (elim disjE exE; simp add: safe_assignment_def)+

lemma push_ex_Neg_iff:
  "push_ex \<phi> = Formula.Neg \<psi> \<longleftrightarrow> (\<exists>\<phi>'. \<phi> = Formula.Neg \<phi>' \<and> \<psi> = push_ex \<phi>')"
  by (cases \<phi>) (auto simp: push_ex_And)

lemma push_ex_comparison:
  "push_ex \<phi> = Formula.Eq t1 t2 \<longleftrightarrow> \<phi> = Formula.Eq t1 t2"
  "push_ex \<phi> = Formula.Less t1 t2 \<longleftrightarrow> \<phi> = Formula.Less t1 t2"
  "push_ex \<phi> = Formula.LessEq t1 t2 \<longleftrightarrow> \<phi> = Formula.LessEq t1 t2"
  by (cases \<phi>; simp add: push_ex_And)+

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

lemma safe_And_not_TR:
  "\<not> Formula.is_Trigger \<psi> \<Longrightarrow> \<not> Formula.is_Release \<psi> \<Longrightarrow>
   safe_formula (Formula.And \<phi> \<psi>) = (safe_formula \<phi> \<and>
     (safe_assignment (Formula.fv \<phi>) \<psi> \<or> safe_formula \<psi> \<or> Formula.fv \<psi> \<subseteq> Formula.fv \<phi> \<and>
       (is_constraint \<psi> \<or> (case \<psi> of Formula.Neg \<psi>' \<Rightarrow> safe_formula \<psi>' | _ \<Rightarrow> False))))"
  by (cases \<psi>) simp_all

lemma case_Neg_push_ex:
  "(case push_ex \<phi> of Formula.Neg \<psi> \<Rightarrow> f \<psi> | _ \<Rightarrow> False)
   = (case \<phi> of Formula.Neg \<psi> \<Rightarrow> f (push_ex \<psi>) | _ \<Rightarrow> False)"
  by (simp add: case_Neg_iff push_ex_Neg_iff) blast

subsection \<open>Safety\<close>

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

lemma future_bounded_push_ex[simp]: "Safety.future_bounded (push_ex \<phi>) = Safety.future_bounded \<phi>"
  by (induct \<phi>) (auto simp: push_ex_And list.pred_map o_def cong: list.pred_cong)

lemma matches_push_ex[simp]: "Safety.matches v (push_ex \<phi>) e = Safety.matches v \<phi> e"
  by (induct \<phi> arbitrary: v e) (auto simp: push_ex_And)

subsection \<open>Progress\<close>

lemma progress_push_ex[simp]: "progress \<sigma> P (push_ex \<phi>) j = progress \<sigma> P \<phi> j"
  by (induct \<phi> arbitrary: P) (auto simp: push_ex_And o_def cong: map_cong)

lemma pprogress_push_ex[simp]: "pprogress (push_ex \<phi>) = pprogress \<phi>"
  by (simp add: pprogress_def fun_eq_iff)

subsection \<open>Typing\<close>

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

lemma pprogress_eprep[simp]: "pprogress (eprep \<phi>) = pprogress \<phi>"
  by (simp add: pprogress_def fun_eq_iff eprep_def)

lemma wty_eprep: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> eprep \<phi>"
  by (simp add: eprep_def wty_share_opt wty_push_ex wty_frz_opt)

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

interpretation p: future_bounded_mfodl \<phi> S E
  by (rule fb(1))

interpretation q: future_bounded_mfodl \<psi> S E
  by (rule fb(2))

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

end

lemma flatten_verdicts_map_comp:
  "flatten_verdicts (map (\<lambda>(i, t, X). (i, t, f ` g X)) Vs) =
    (\<lambda>(i, t, v). (i, t, f v)) ` flatten_verdicts (map (\<lambda>(i, t, X). (i, t, g X)) Vs)"
  by (auto simp: flatten_verdicts_def image_UN image_image split_beta)

subsection \<open>The executable monitor on the rewritten formula\<close>

text \<open>The executable state is compiled from the rewritten formula at its own column list, but the
  ascending columns are the free variables in ascending order, which the rewriting does not change.
  So the executable verdicts, read at the columns of @{term \<phi>}, are those of @{term \<phi>}.\<close>

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

lemma eminit_push_eq:
  "eminit_push \<phi>
   = eof_state (Formula.nfv \<phi>) (Formula.fv_list (eprep \<phi>))
       (ecols (Formula.fv_list (eprep \<phi>))) (minit_safe (eprep \<phi>))"
  by (simp add: eminit_push_def eminit_safe_def)
(*<*)
end
(*>*)
