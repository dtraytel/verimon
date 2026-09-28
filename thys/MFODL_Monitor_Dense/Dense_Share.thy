(*<*)
theory Dense_Share
  imports "MFODL_Monitor_Devel.Monitor" "MFODL_Monitor_Devel.Progress" "MFODL_Monitor_Devel.Typing"
begin
(*>*)

section \<open>The right operand of a release, evaluated once\<close>

text \<open>
  The monitor evaluates a release by the formula that defines it in terms of the past and
  future operators (@{const release_safe_0}, @{const and_release_safe_bounded}), which
  contains the right operand four or five times; each copy is a subformula of its own, and
  the monitor evaluates each.  On @{text "C(x) AND ALWAYS[0,5] (EXISTS y. A(x,y) OR B(x,y))"},
  which VeriMon's rewriting turns into a release, that is five evaluations of the
  quantified disjunction per time point.  Binding the right operand with
  @{const Formula.Let} to a predicate that occurs nowhere else, and releasing that predicate,
  has it evaluated once.  VeriMon's multiway conversion (@{const convert_multiway}) expands a
  release in the same way, so the theory @{text Dense_VeriMon} applies the rewrite
  before that conversion as well.
\<close>

subsection \<open>The rewrite\<close>

text \<open>Whether a formula mentions a predicate, bound or not.\<close>

fun occurs :: "Formula.name \<times> nat \<Rightarrow> 't Formula.formula \<Rightarrow> bool" where
  "occurs pn (Formula.Pred e ts) = ((e, length ts) = pn)"
| "occurs pn (Formula.Let e \<phi> \<psi>) = (occurs pn \<phi> \<or> occurs pn \<psi>)"
| "occurs pn (Formula.Frz e \<phi> \<psi>) = (occurs pn \<phi> \<or> occurs pn \<psi>)"
| "occurs pn (Formula.LetPast e \<phi> \<psi>) = (occurs pn \<phi> \<or> occurs pn \<psi>)"
| "occurs pn (Formula.Neg \<phi>) = occurs pn \<phi>"
| "occurs pn (Formula.Or \<phi> \<psi>) = (occurs pn \<phi> \<or> occurs pn \<psi>)"
| "occurs pn (Formula.And \<phi> \<psi>) = (occurs pn \<phi> \<or> occurs pn \<psi>)"
| "occurs pn (Formula.Ands l) = (\<exists>\<phi>\<in>set l. occurs pn \<phi>)"
| "occurs pn (Formula.Exists t \<phi>) = occurs pn \<phi>"
| "occurs pn (Formula.Agg y \<omega> tys f \<phi>) = occurs pn \<phi>"
| "occurs pn (Formula.Prev I \<phi>) = occurs pn \<phi>"
| "occurs pn (Formula.Next I \<phi>) = occurs pn \<phi>"
| "occurs pn (Formula.Since \<phi> I \<psi>) = (occurs pn \<phi> \<or> occurs pn \<psi>)"
| "occurs pn (Formula.Until \<phi> I \<psi>) = (occurs pn \<phi> \<or> occurs pn \<psi>)"
| "occurs pn (Formula.Trigger \<phi> I \<psi>) = (occurs pn \<phi> \<or> occurs pn \<psi>)"
| "occurs pn (Formula.Release \<phi> I \<psi>) = (occurs pn \<phi> \<or> occurs pn \<psi>)"
| "occurs pn (Formula.MatchP I r) = (\<exists>\<phi>\<in>Regex.atms r. occurs pn \<phi>)"
| "occurs pn (Formula.MatchF I r) = (\<exists>\<phi>\<in>Regex.atms r. occurs pn \<phi>)"
| "occurs pn _ = False"

definition shr :: Formula.name where
  "shr = string8_literal STR ''__release''"

definition share_ok :: "'t Formula.formula \<Rightarrow> 't Formula.formula \<Rightarrow> bool" where
  "share_ok \<alpha> \<psi> = ((\<forall>x\<in>{0..<Formula.nfv \<psi>}. x \<in> Formula.fv \<psi>) \<and> \<not> occurs (shr, Formula.nfv \<psi>) \<alpha> \<and>
     (case \<psi> of Formula.Pred _ _ \<Rightarrow> False | _ \<Rightarrow> True))"

definition shr_pred :: "'t Formula.formula \<Rightarrow> 't Formula.formula" where
  "shr_pred \<psi> = Formula.Pred shr (map Formula.Var [0..<Formula.nfv \<psi>])"

text \<open>The front end turns @{text "ALWAYS[I] \<psi>"} into a release whose left operand is false,
  @{text "(NOT ''x'' = ''x'') R[I] \<psi>"}.  With @{text "0 \<in> I"}, the multiway conversion expands a
  release into @{text "(\<psi> U[I] (\<psi> \<and> \<phi>)) \<or> always_safe_0 I \<psi>"}, whose first disjunct cannot hold
  when @{text \<phi>} is false, but whose until node keeps every tuple of @{text \<psi>} over the
  interval all the same.  So such a release is replaced by @{const always_safe_0} directly
  (@{text rel_op}); its progress is the release's (@{text progress_rel_op}), because the first
  disjunct never has less progress than the second.\<close>

fun str_eq_trm :: "Formula.trm \<Rightarrow> Formula.trm \<Rightarrow> bool" where
  "str_eq_trm (Formula.Const (EString s)) (Formula.Const (EString s')) = (s = s')"
| "str_eq_trm _ _ = False"

fun int_neq_trm :: "Formula.trm \<Rightarrow> Formula.trm \<Rightarrow> bool" where
  "int_neq_trm (Formula.Const (EInt i)) (Formula.Const (EInt i')) = (i \<noteq> i')"
| "int_neq_trm _ _ = False"

fun is_ff :: "'t Formula.formula \<Rightarrow> bool" where
  "is_ff (Formula.Neg (Formula.Eq t u)) = str_eq_trm t u"
| "is_ff (Formula.Eq t u) = int_neq_trm t u"
| "is_ff _ = False"

lemma str_eq_trmD: "str_eq_trm t u \<Longrightarrow> \<exists>s. t = Formula.Const (EString s) \<and> u = t"
  by (induct t u rule: str_eq_trm.induct) auto

lemma int_neq_trmD: "int_neq_trm t u \<Longrightarrow> \<exists>i i'. t = Formula.Const (EInt i) \<and> u = Formula.Const (EInt i') \<and> i \<noteq> i'"
  by (induct t u rule: int_neq_trm.induct) auto

lemma is_ffE:
  assumes "is_ff \<phi>"
  obtains s where "\<phi> = Formula.Neg (Formula.Eq (Formula.Const (EString s)) (Formula.Const (EString s)))"
  | i i' where "\<phi> = Formula.Eq (Formula.Const (EInt i)) (Formula.Const (EInt i'))" "i \<noteq> i'"
  using assms by (cases \<phi> rule: is_ff.cases) (auto dest!: str_eq_trmD int_neq_trmD)

lemma is_ff_sat: "is_ff \<phi> \<Longrightarrow> \<not> Formula.sat \<sigma> V v i \<phi>"
  by (erule is_ffE) auto

lemma is_ff_fvi: "is_ff \<phi> \<Longrightarrow> Formula.fvi b \<phi> = {}"
  by (erule is_ffE) auto

lemma is_ff_progress: "is_ff \<phi> \<Longrightarrow> progress \<sigma> P \<phi> j = j"
  by (erule is_ffE) auto

definition rel_op :: "'t Formula.formula \<Rightarrow> \<I> \<Rightarrow> 't Formula.formula \<Rightarrow> 't Formula.formula" where
  "rel_op \<phi> I \<psi> = (if is_ff \<phi> \<and> mem I 0 \<and> bounded I then always_safe_0 I \<psi> else Formula.Release \<phi> I \<psi>)"

lemma fvi_rel_op[simp]: "Formula.fvi b (rel_op \<phi> I \<psi>) = Formula.fvi b (Formula.Release \<phi> I \<psi>)"
  by (auto simp: rel_op_def always_safe_0_def is_ff_fvi)

lemma sat_rel_op[simp]: "Formula.sat \<sigma> V v i (rel_op \<phi> I \<psi>) = Formula.sat \<sigma> V v i (Formula.Release \<phi> I \<psi>)"
  using always_rewrite_0[of I \<sigma> V v i \<psi>] is_ff_sat[of \<phi> \<sigma> V v] by (auto simp: rel_op_def)

lemma progress_rel_op[simp]: "progress \<sigma> P (rel_op \<phi> I \<psi>) j = progress \<sigma> P (Formula.Release \<phi> I \<psi>) j"
proof (cases "is_ff \<phi> \<and> mem I 0 \<and> bounded I")
  case True
  let ?A = "{i. \<forall>k. k < j \<and> k \<le> min (progress \<sigma> P \<psi> j) (progress \<sigma> P \<phi> j) \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
  let ?B = "{i. \<forall>k. k < j \<and> k \<le> progress \<sigma> P \<psi> j \<longrightarrow> memR (flip_int_double_upper I) (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
  have "?A \<subseteq> ?B"
    using True is_ff_progress[of \<phi> \<sigma> P j] by (auto intro: memR_flip_int_double_upper)
  then have "?A \<union> ?B = ?B"
    by blast
  then show ?thesis
    using True by (simp add: rel_op_def)
qed (simp only: rel_op_def if_not_P if_False)

lemma wty_rel_op: "S, E \<turnstile> Formula.Release \<phi> I \<psi> \<Longrightarrow> S, E \<turnstile> rel_op \<phi> I \<psi>"
  by (auto simp: rel_op_def always_safe_0_def intro!: wty_formula.intros dest: wty_formulaD)

fun share_rw :: "'t Formula.formula \<Rightarrow> 't Formula.formula" where
  "share_rw (Formula.And \<alpha> (Formula.Release \<phi> I \<psi>)) = (let \<alpha>' = share_rw \<alpha>; \<phi>' = share_rw \<phi>; \<psi>' = share_rw \<psi> in
     if share_ok (Formula.And \<alpha>' \<phi>') \<psi>'
     then Formula.Let shr \<psi>' (Formula.And \<alpha>' (rel_op \<phi>' I (shr_pred \<psi>')))
     else Formula.And \<alpha>' (rel_op \<phi>' I \<psi>'))"
| "share_rw (Formula.Release \<phi> I \<psi>) = (let \<phi>' = share_rw \<phi>; \<psi>' = share_rw \<psi> in
     if share_ok \<phi>' \<psi>' then Formula.Let shr \<psi>' (rel_op \<phi>' I (shr_pred \<psi>'))
     else rel_op \<phi>' I \<psi>')"
| "share_rw (Formula.Let p \<phi> \<psi>) = Formula.Let p (share_rw \<phi>) (share_rw \<psi>)"
| "share_rw (Formula.Neg \<phi>) = Formula.Neg (share_rw \<phi>)"
| "share_rw (Formula.And \<phi> \<psi>) = Formula.And (share_rw \<phi>) (share_rw \<psi>)"
| "share_rw (Formula.Or \<phi> \<psi>) = Formula.Or (share_rw \<phi>) (share_rw \<psi>)"
| "share_rw (Formula.Ands l) = Formula.Ands (map share_rw l)"
| "share_rw (Formula.Exists t \<phi>) = Formula.Exists t (share_rw \<phi>)"
| "share_rw (Formula.Agg y \<omega> tys f \<phi>) = Formula.Agg y \<omega> tys f (share_rw \<phi>)"
| "share_rw (Formula.Prev I \<phi>) = Formula.Prev I (share_rw \<phi>)"
| "share_rw (Formula.Next I \<phi>) = Formula.Next I (share_rw \<phi>)"
| "share_rw (Formula.Since \<phi> I \<psi>) = Formula.Since (share_rw \<phi>) I (share_rw \<psi>)"
| "share_rw (Formula.Until \<phi> I \<psi>) = Formula.Until (share_rw \<phi>) I (share_rw \<psi>)"
| "share_rw \<phi> = \<phi>"

text \<open>As for the frozen predicates, the rewrite is applied only when its result is monitorable.\<close>

definition share_opt :: "ty Formula.formula \<Rightarrow> ty Formula.formula" where
  "share_opt \<phi> = (let \<phi>' = share_rw \<phi> in if mmonitorable_exec \<phi>' then \<phi>' else \<phi>)"

subsection \<open>The shared predicate\<close>

lemma not_contains_pred_preds: "\<not> occurs pn \<phi> \<Longrightarrow> \<not> contains_pred pn \<phi>"
  by (induct pn \<phi> rule: contains_pred.induct) auto

lemma tabulate_map_upt: "tabulate f x n = map f [x..<x + n]"
  by (induct n arbitrary: x) (auto simp: upt_rec)

lemma fvi_shr_pred:
  assumes "\<forall>x\<in>{0..<Formula.nfv \<psi>}. x \<in> Formula.fv \<psi>"
  shows "Formula.fvi b (shr_pred \<psi>) = Formula.fvi b \<psi>"
proof (rule set_eqI)
  fix y
  have "y \<in> Formula.fvi b (shr_pred \<psi>) \<longleftrightarrow> y + b < Formula.nfv \<psi>"
  proof
    assume "y \<in> Formula.fvi b (shr_pred \<psi>)"
    then show "y + b < Formula.nfv \<psi>"
      by (auto simp: shr_pred_def split: if_splits)
  next
    assume "y + b < Formula.nfv \<psi>"
    then show "y \<in> Formula.fvi b (shr_pred \<psi>)"
      by (auto simp: shr_pred_def intro!: bexI[of _ "y + b"])
  qed
  also have "\<dots> \<longleftrightarrow> y + b \<in> Formula.fv \<psi>"
    using assms fvi_less_nfv[of \<psi>] by auto
  also have "\<dots> \<longleftrightarrow> y \<in> Formula.fvi b \<psi>"
    by (rule fvi_iff_fv[symmetric])
  finally show "y \<in> Formula.fvi b (shr_pred \<psi>) \<longleftrightarrow> y \<in> Formula.fvi b \<psi>" .
qed

lemma sat_shr_pred:
  assumes "share_ok \<alpha> \<psi>"
  shows "Formula.sat \<sigma> (V((shr, Formula.nfv \<psi>) \<mapsto> \<lambda>w j. Formula.sat \<sigma> V w j \<psi>)) v i (shr_pred \<psi>) =
    Formula.sat \<sigma> V v i \<psi>"
proof -
  have "Formula.sat \<sigma> V (map ((!) v) [0..<Formula.nfv \<psi>]) i \<psi> = Formula.sat \<sigma> V v i \<psi>"
    using fvi_less_nfv[of \<psi>] by (intro sat_fv_cong) auto
  then show ?thesis
    by (simp add: shr_pred_def o_def)
qed

lemma progress_shr_pred:
  "progress \<sigma> (P((shr, Formula.nfv \<psi>) \<mapsto> k)) (shr_pred \<psi>) j = k"
  by (simp add: shr_pred_def)

lemma wty_shr_pred:
  "S((shr, Formula.nfv \<psi>) \<mapsto> tabulate E 0 (Formula.nfv \<psi>)), E \<turnstile> shr_pred \<psi>"
  by (auto simp: shr_pred_def tabulate_map_upt list.rel_map intro!: wty_formula.Pred
    list.rel_refl_strong wty_trm.Var)

lemma wty_fresh_upd:
  assumes "S(q \<mapsto> y), E \<turnstile> \<psi>" "q \<noteq> pn \<Longrightarrow> S(q \<mapsto> y, pn \<mapsto> x), E \<turnstile> \<psi>"
  shows "S(pn \<mapsto> x, q \<mapsto> y), E \<turnstile> \<psi>"
proof (cases "q = pn")
  case True
  then show ?thesis
    using assms(1) by simp
next
  case False
  then show ?thesis
    using assms(2) unfolding fun_upd_twist[OF not_sym[OF False]] by blast
qed

lemma wty_fresh': "S, E \<turnstile> \<phi> \<Longrightarrow> \<not> occurs pn \<phi> \<Longrightarrow> S' = S(pn \<mapsto> x) \<Longrightarrow> S', E \<turnstile> \<phi>"
proof (induct arbitrary: S' rule: wty_formula.induct)
  case (Let S E' \<phi> p E \<psi>)
  let ?q = "(p, Formula.nfv \<phi>)" and ?y = "tabulate E' 0 (Formula.nfv \<phi>)"
  show ?case
    unfolding Let(6)
  proof (rule wty_formula.Let)
    show "S(pn \<mapsto> x), E' \<turnstile> \<phi>"
      by (rule Let(2)[where S'="S(pn \<mapsto> x)", OF _ refl]) (use Let(5) in simp)
    show "S(pn \<mapsto> x, ?q \<mapsto> ?y), E \<turnstile> \<psi>"
    proof (rule wty_fresh_upd)
      show "S(?q \<mapsto> ?y), E \<turnstile> \<psi>"
        by (rule Let(3))
      show "S(?q \<mapsto> ?y, pn \<mapsto> x), E \<turnstile> \<psi>"
        by (rule Let(4)[where S'="S(?q \<mapsto> ?y, pn \<mapsto> x)", OF _ refl]) (use Let(5) in simp)
    qed
  qed
next
  case (Frz S E' \<phi> p E \<psi>)
  let ?q = "(p, Formula.nfv \<phi>)" and ?y = "tabulate E' 0 (Formula.nfv \<phi>)"
  show ?case
    unfolding Frz(6)
  proof (rule wty_formula.Frz)
    show "S(pn \<mapsto> x), E' \<turnstile> \<phi>"
      by (rule Frz(2)[where S'="S(pn \<mapsto> x)", OF _ refl]) (use Frz(5) in simp)
    show "S(pn \<mapsto> x, ?q \<mapsto> ?y), E \<turnstile> \<psi>"
    proof (rule wty_fresh_upd)
      show "S(?q \<mapsto> ?y), E \<turnstile> \<psi>"
        by (rule Frz(3))
      show "S(?q \<mapsto> ?y, pn \<mapsto> x), E \<turnstile> \<psi>"
        by (rule Frz(4)[where S'="S(?q \<mapsto> ?y, pn \<mapsto> x)", OF _ refl]) (use Frz(5) in simp)
    qed
  qed
next
  case (LetPast S p \<phi> E' E \<psi>)
  let ?q = "(p, Formula.nfv \<phi>)" and ?y = "tabulate E' 0 (Formula.nfv \<phi>)"
  show ?case
    unfolding LetPast(6)
  proof (rule wty_formula.LetPast)
    show "S(pn \<mapsto> x, ?q \<mapsto> ?y), E' \<turnstile> \<phi>"
    proof (rule wty_fresh_upd)
      show "S(?q \<mapsto> ?y), E' \<turnstile> \<phi>"
        by (rule LetPast(1))
      show "S(?q \<mapsto> ?y, pn \<mapsto> x), E' \<turnstile> \<phi>"
        by (rule LetPast(2)[where S'="S(?q \<mapsto> ?y, pn \<mapsto> x)", OF _ refl]) (use LetPast(5) in simp)
    qed
    show "S(pn \<mapsto> x, ?q \<mapsto> ?y), E \<turnstile> \<psi>"
    proof (rule wty_fresh_upd)
      show "S(?q \<mapsto> ?y), E \<turnstile> \<psi>"
        by (rule LetPast(3))
      show "S(?q \<mapsto> ?y, pn \<mapsto> x), E \<turnstile> \<psi>"
        by (rule LetPast(4)[where S'="S(?q \<mapsto> ?y, pn \<mapsto> x)", OF _ refl]) (use LetPast(5) in simp)
    qed
  qed
next
  case (MatchP S E r I)
  show ?case
    unfolding MatchP(3) using MatchP(1,2)
    by (auto intro!: wty_formula.MatchP elim!: regex.pred_mono_strong)
next
  case (MatchF S E r I)
  show ?case
    unfolding MatchF(3) using MatchF(1,2)
    by (auto intro!: wty_formula.MatchF elim!: regex.pred_mono_strong)
qed (auto intro: wty_formula.intros)

lemma wty_fresh: "S, E \<turnstile> \<phi> \<Longrightarrow> \<not> occurs pn \<phi> \<Longrightarrow> S(pn \<mapsto> x), E \<turnstile> \<phi>"
  by (rule wty_fresh'[OF _ _ refl])

lemma sat_Release_cong:
  assumes "\<And>v j. Formula.sat \<sigma> V v j \<phi> = Formula.sat \<sigma> V' v j \<phi>'"
    "\<And>v j. Formula.sat \<sigma> V v j \<psi> = Formula.sat \<sigma> V' v j \<psi>'"
  shows "Formula.sat \<sigma> V v i (Formula.Release \<phi> I \<psi>) = Formula.sat \<sigma> V' v i (Formula.Release \<phi>' I \<psi>')"
  using assms by simp

lemma progress_Release_cong:
  assumes "progress \<sigma> P \<phi> j = progress \<sigma> P' \<phi>' j" "progress \<sigma> P \<psi> j = progress \<sigma> P' \<psi>' j"
  shows "progress \<sigma> P (Formula.Release \<phi> I \<psi>) j = progress \<sigma> P' (Formula.Release \<phi>' I \<psi>') j"
  using assms by (simp add: release_safe_bounded_def always_safe_bounded_def Formula.eventually_def
    Formula.once_def)

subsection \<open>The rewrite of the whole formula\<close>

lemma fvi_share_rw[simp]: "Formula.fvi b (share_rw \<phi>) = Formula.fvi b \<phi>"
  by (induct \<phi> arbitrary: b rule: share_rw.induct)
    (auto simp: Let_def share_ok_def fvi_shr_pred split: if_splits)

lemma nfv_share_rw[simp]: "Formula.nfv (share_rw \<phi>) = Formula.nfv \<phi>"
  by (simp add: Formula.nfv_def)

lemma sat_share_rw[simp]: "Formula.sat \<sigma> V v i (share_rw \<phi>) = Formula.sat \<sigma> V v i \<phi>"
proof (induct \<phi> arbitrary: V v i rule: share_rw.induct)
  case (1 \<alpha> \<phi> I \<psi>)
  note IH\<alpha> = 1(1) and IH\<phi> = 1(2)[OF refl] and IH\<psi> = 1(3)[OF refl refl]
  let ?\<alpha> = "share_rw \<alpha>" and ?\<phi> = "share_rw \<phi>" and ?\<psi> = "share_rw \<psi>"
  let ?V = "V((shr, Formula.nfv ?\<psi>) \<mapsto> \<lambda>w j. Formula.sat \<sigma> V w j ?\<psi>)"
  show ?case
  proof (cases "share_ok (Formula.And ?\<alpha> ?\<phi>) ?\<psi>")
    case True
    then have n\<alpha>: "\<not> contains_pred (shr, Formula.nfv ?\<psi>) ?\<alpha>" and n\<phi>: "\<not> contains_pred (shr, Formula.nfv ?\<psi>) ?\<phi>"
      by (auto simp: share_ok_def intro!: not_contains_pred_preds)
    have p: "Formula.sat \<sigma> ?V v' j (shr_pred ?\<psi>) = Formula.sat \<sigma> V v' j \<psi>" for v' j
      by (rule trans[OF sat_shr_pred[OF True] IH\<psi>])
    have f: "Formula.sat \<sigma> ?V v' j ?\<phi> = Formula.sat \<sigma> V v' j \<phi>" for v' j
      by (rule trans[OF not_contains_pred_sat[OF n\<phi>] IH\<phi>])
    have a: "Formula.sat \<sigma> ?V v i ?\<alpha> = Formula.sat \<sigma> V v i \<alpha>"
      by (rule trans[OF not_contains_pred_sat[OF n\<alpha>] IH\<alpha>])
    show ?thesis
      using True a sat_Release_cong[of \<sigma> ?V ?\<phi> V \<phi> "shr_pred ?\<psi>" \<psi>, OF f p] by (simp add: Let_def)
  next
    case False
    then show ?thesis
      using IH\<alpha> IH\<phi> IH\<psi> sat_Release_cong[of \<sigma> V ?\<phi> V \<phi> ?\<psi> \<psi>] by (simp add: Let_def)
  qed
next
  case (2 \<phi> I \<psi>)
  note IH\<phi> = 2(1) and IH\<psi> = 2(2)[OF refl]
  let ?\<phi> = "share_rw \<phi>" and ?\<psi> = "share_rw \<psi>"
  let ?V = "V((shr, Formula.nfv ?\<psi>) \<mapsto> \<lambda>w j. Formula.sat \<sigma> V w j ?\<psi>)"
  show ?case
  proof (cases "share_ok ?\<phi> ?\<psi>")
    case True
    then have n\<phi>: "\<not> contains_pred (shr, Formula.nfv ?\<psi>) ?\<phi>"
      by (auto simp: share_ok_def intro!: not_contains_pred_preds)
    have p: "Formula.sat \<sigma> ?V v' j (shr_pred ?\<psi>) = Formula.sat \<sigma> V v' j \<psi>" for v' j
      by (rule trans[OF sat_shr_pred[OF True] IH\<psi>])
    have f: "Formula.sat \<sigma> ?V v' j ?\<phi> = Formula.sat \<sigma> V v' j \<phi>" for v' j
      by (rule trans[OF not_contains_pred_sat[OF n\<phi>] IH\<phi>])
    show ?thesis
      using True sat_Release_cong[of \<sigma> ?V ?\<phi> V \<phi> "shr_pred ?\<psi>" \<psi>, OF f p] by (simp add: Let_def)
  next
    case False
    then show ?thesis
      using IH\<phi> IH\<psi> sat_Release_cong[of \<sigma> V ?\<phi> V \<phi> ?\<psi> \<psi>] by (simp add: Let_def)
  qed
qed (auto split: nat.splits)

lemma progress_share_rw:
  "pred_mapping (\<lambda>x. x \<le> j) P \<Longrightarrow> progress \<sigma> P (share_rw \<phi>) j = progress \<sigma> P \<phi> j"
proof (induct \<phi> arbitrary: P rule: share_rw.induct)
  case (1 \<alpha> \<phi> I \<psi>)
  note IH\<alpha> = 1(1)[OF 1(4)] and IH\<phi> = 1(2)[OF refl 1(4)] and IH\<psi> = 1(3)[OF refl refl 1(4)]
  let ?\<alpha> = "share_rw \<alpha>" and ?\<phi> = "share_rw \<phi>" and ?\<psi> = "share_rw \<psi>"
  let ?P = "P((shr, Formula.nfv ?\<psi>) \<mapsto> progress \<sigma> P ?\<psi> j)"
  show ?case
  proof (cases "share_ok (Formula.And ?\<alpha> ?\<phi>) ?\<psi>")
    case True
    then have n\<alpha>: "\<not> contains_pred (shr, Formula.nfv ?\<psi>) ?\<alpha>" and n\<phi>: "\<not> contains_pred (shr, Formula.nfv ?\<psi>) ?\<phi>"
      by (auto simp: share_ok_def intro!: not_contains_pred_preds)
    have a: "progress \<sigma> ?P ?\<alpha> j = progress \<sigma> P \<alpha> j"
      by (rule trans[OF not_contains_pred_progress[OF n\<alpha>] IH\<alpha>])
    have f: "progress \<sigma> ?P ?\<phi> j = progress \<sigma> P \<phi> j"
      by (rule trans[OF not_contains_pred_progress[OF n\<phi>] IH\<phi>])
    have p: "progress \<sigma> ?P (shr_pred ?\<psi>) j = progress \<sigma> P \<psi> j"
      by (rule trans[OF progress_shr_pred IH\<psi>])
    show ?thesis
      using True a progress_Release_cong[OF f p, of I] by (simp add: Let_def)
  next
    case False
    then show ?thesis
      using IH\<alpha> progress_Release_cong[OF IH\<phi> IH\<psi>, of I] by (simp add: Let_def)
  qed
next
  case (2 \<phi> I \<psi>)
  note IH\<phi> = 2(1)[OF 2(3)] and IH\<psi> = 2(2)[OF refl 2(3)]
  let ?\<phi> = "share_rw \<phi>" and ?\<psi> = "share_rw \<psi>"
  let ?P = "P((shr, Formula.nfv ?\<psi>) \<mapsto> progress \<sigma> P ?\<psi> j)"
  show ?case
  proof (cases "share_ok ?\<phi> ?\<psi>")
    case True
    then have n\<phi>: "\<not> contains_pred (shr, Formula.nfv ?\<psi>) ?\<phi>"
      by (auto simp: share_ok_def intro!: not_contains_pred_preds)
    have f: "progress \<sigma> ?P ?\<phi> j = progress \<sigma> P \<phi> j"
      by (rule trans[OF not_contains_pred_progress[OF n\<phi>] IH\<phi>])
    have p: "progress \<sigma> ?P (shr_pred ?\<psi>) j = progress \<sigma> P \<psi> j"
      by (rule trans[OF progress_shr_pred IH\<psi>])
    show ?thesis
      using True progress_Release_cong[OF f p, of I] by (simp add: Let_def)
  next
    case False
    then show ?thesis
      using progress_Release_cong[OF IH\<phi> IH\<psi>, of I] by (simp add: Let_def)
  qed
next
  case (3 p \<phi> \<psi>)
  have "progress \<sigma> P \<phi> j \<le> j"
    by (rule progress_le_gen[OF 3(3)])
  then have pm: "pred_mapping (\<lambda>x. x \<le> j) (P((p, Formula.nfv \<phi>) \<mapsto> progress \<sigma> P \<phi> j))"
    using 3(3) by simp
  show ?case
    using 3(1)[OF 3(3)] 3(2)[OF pm] by (simp add: fun_upd_def)
qed (auto simp: o_def cong: map_cong)

lemma wty_share_rw: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> share_rw \<phi>"
proof (induct \<phi> arbitrary: S E rule: share_rw.induct)
  case (1 \<alpha> \<phi> I \<psi>)
  let ?\<alpha> = "share_rw \<alpha>" and ?\<phi> = "share_rw \<phi>" and ?\<psi> = "share_rw \<psi>"
  let ?S = "S((shr, Formula.nfv ?\<psi>) \<mapsto> tabulate E 0 (Formula.nfv ?\<psi>))"
  from 1(4) have "S, E \<turnstile> \<alpha>" "S, E \<turnstile> \<phi>" "S, E \<turnstile> \<psi>"
    by (auto dest: wty_formulaD)
  then have \<alpha>: "S, E \<turnstile> ?\<alpha>" and \<phi>: "S, E \<turnstile> ?\<phi>" and \<psi>: "S, E \<turnstile> ?\<psi>"
    using 1(1) 1(2)[OF refl] 1(3)[OF refl refl] by blast+
  show ?case
  proof (cases "share_ok (Formula.And ?\<alpha> ?\<phi>) ?\<psi>")
    case True
    then have "\<not> occurs (shr, Formula.nfv ?\<psi>) ?\<alpha>" "\<not> occurs (shr, Formula.nfv ?\<psi>) ?\<phi>"
      by (auto simp: share_ok_def)
    then have "?S, E \<turnstile> Formula.And ?\<alpha> (rel_op ?\<phi> I (shr_pred ?\<psi>))"
      by (intro wty_formula.And wty_rel_op wty_formula.Release wty_fresh[OF \<alpha>] wty_fresh[OF \<phi>] wty_shr_pred)
    then show ?thesis
      using True \<psi> by (auto simp: Let_def intro!: wty_formula.Let[where E'=E])
  next
    case False
    then show ?thesis
      using \<alpha> \<phi> \<psi> by (auto simp: Let_def intro!: wty_formula.And wty_rel_op wty_formula.Release)
  qed
next
  case (2 \<phi> I \<psi>)
  let ?\<phi> = "share_rw \<phi>" and ?\<psi> = "share_rw \<psi>"
  let ?S = "S((shr, Formula.nfv ?\<psi>) \<mapsto> tabulate E 0 (Formula.nfv ?\<psi>))"
  from 2(3) have "S, E \<turnstile> \<phi>" "S, E \<turnstile> \<psi>"
    by (auto dest: wty_formulaD)
  then have \<phi>: "S, E \<turnstile> ?\<phi>" and \<psi>: "S, E \<turnstile> ?\<psi>"
    using 2(1) 2(2)[OF refl] by blast+
  show ?case
  proof (cases "share_ok ?\<phi> ?\<psi>")
    case True
    then have "\<not> occurs (shr, Formula.nfv ?\<psi>) ?\<phi>"
      by (auto simp: share_ok_def)
    then have "?S, E \<turnstile> rel_op ?\<phi> I (shr_pred ?\<psi>)"
      by (intro wty_rel_op wty_formula.Release wty_fresh[OF \<phi>] wty_shr_pred)
    then show ?thesis
      using True \<psi> by (auto simp: Let_def intro!: wty_formula.Let[where E'=E])
  next
    case False
    then show ?thesis
      using \<phi> \<psi> by (auto simp: Let_def intro!: wty_rel_op wty_formula.Release)
  qed
next
  case (3 p \<phi> \<psi>)
  from 3(3) obtain E' where \<phi>: "S, E' \<turnstile> \<phi>" and \<psi>: "S((p, Formula.nfv \<phi>) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>)), E \<turnstile> \<psi>"
    by (cases rule: wty_formula.cases) auto
  show ?case
    using wty_formula.Let[OF 3(1)[OF \<phi>]] 3(2)[OF \<psi>] by (simp add: fun_upd_def)
next
  case (7 l)
  show ?case
    using 7(1) wty_formula_AndsD[OF 7(2)] by (auto intro!: wty_formula.Ands)
qed (erule wty_formula.cases; auto intro: wty_formula.intros)+

lemma fvi_share_opt[simp]: "Formula.fvi b (share_opt \<phi>) = Formula.fvi b \<phi>"
  by (simp add: share_opt_def Let_def)

lemma nfv_share_opt[simp]: "Formula.nfv (share_opt \<phi>) = Formula.nfv \<phi>"
  by (simp add: share_opt_def Let_def)

lemma sat_share_opt[simp]: "Formula.sat \<sigma> V v i (share_opt \<phi>) = Formula.sat \<sigma> V v i \<phi>"
  by (simp add: share_opt_def Let_def)

lemma progress_share_opt_empty[simp]:
  "progress \<sigma> Map.empty (share_opt \<phi>) j = progress \<sigma> Map.empty \<phi> j"
  by (simp add: share_opt_def Let_def progress_share_rw)

lemma wty_share_opt: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> share_opt \<phi>"
  by (simp add: share_opt_def Let_def wty_share_rw)

lemma mmonitorable_share_opt: "mmonitorable \<phi> \<Longrightarrow> mmonitorable (share_opt \<phi>)"
  by (simp add: share_opt_def Let_def mmonitorable_exec_mmonitorable)

(*<*)
end
(*>*)