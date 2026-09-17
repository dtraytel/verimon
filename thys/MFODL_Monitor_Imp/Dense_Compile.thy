(*<*)
theory Dense_Compile
  imports Dense_Correct
begin
(*>*)

section \<open>One criterion for the whole formula\<close>

text \<open>
  The twenty-five node lemmas of the three preceding theories each say: if the operands produce
  finite tables over their columns, so does this node.  They compose by structural induction, and
  the predicate \<open>mok\<close> below is what they compose into -- one rule per node, carrying
  exactly that node's lemma's hypotheses, with the operands' @{const produces} replaced by
  \<open>mok\<close> itself.  So \<open>mok\<close> is a structural criterion on the kernel's
  formula, and the theorem \<open>mok_produces\<close> that follows it discharges the
  simulation's remaining input hypothesis in one step.

  Two rules cannot be read off the kernel's formula alone: the match nodes carry a marked regular
  expression whose safety is a property of the source regex, so their rules quantify over the
  atom list the expression was compiled from.  That is why \<open>mok\<close> is inductive
  rather than a recursive function.
\<close>

inductive mok :: "nat \<Rightarrow> nat set \<Rightarrow> ts \<Rightarrow>
    (mmasaux, muaux_dq, event_data mmtaux) mformula \<Rightarrow> bool" where
  MokRel: "table n A rel \<Longrightarrow> finite rel \<Longrightarrow> mok n A tw (mformula.MRel rel)"
| MokNeg: "mok n {} tw (mformula.MNeg \<phi>)"
| MokAndRel: "mok n A tw \<phi> \<Longrightarrow> mok n A tw (mformula.MAndRel \<phi> conf)"
| MokAndAssign: "fst conf < n \<Longrightarrow> mok n B tw \<phi> \<Longrightarrow> A = Set.insert (fst conf) B \<Longrightarrow>
    mok n A tw (mformula.MAndAssign \<phi> conf)"
| MokExists: "mok (Suc n) B tw \<phi> \<Longrightarrow> A = (\<lambda>x. x - Suc 0) ` (B - {0}) \<Longrightarrow>
    mok n A tw (mformula.MExists \<phi>)"
| MokPredC: "length tms = n \<Longrightarrow> A = {0..<n} \<Longrightarrow>
    mok n A tw (mformula.MPred e tms Copy)"
| MokPredS: "is_simple_pattern tms 0 \<Longrightarrow>
    (\<forall>t \<in> set tms. \<forall>x \<in> Formula.fv_trm t. x < n) \<Longrightarrow>
    A = (\<Union>t \<in> set tms. Formula.fv_trm t) \<Longrightarrow>
    mok n A tw (mformula.MPred e tms Simple)"
| MokPredM: "A = (\<Union>t \<in> set tms. Formula.fv_trm t) \<Longrightarrow>
    mok n A tw (mformula.MPred e tms Match)"
| MokTP: "A = mtrm_cols mt \<Longrightarrow> mok n A tw (mformula.MTP mt i)"
| MokTS: "A = mtrm_cols mt \<Longrightarrow> mok n A tw (mformula.MTS mt)"
| MokOr: "mok n A tw \<phi> \<Longrightarrow> mok n A tw \<psi> \<Longrightarrow>
    list_all (ftable n A) (fst buf) \<Longrightarrow> list_all (ftable n A) (snd buf) \<Longrightarrow>
    mok n A tw (mformula.MOr \<phi> \<psi> buf)"
| MokAnd: "mok n A1 tw \<phi> \<Longrightarrow> mok n A2 tw \<psi> \<Longrightarrow>
    list_all (ftable n A1) (fst buf) \<Longrightarrow> list_all (ftable n A2) (snd buf) \<Longrightarrow>
    (\<not> pos \<Longrightarrow> A2 \<subseteq> A1) \<Longrightarrow> A = (if pos then A1 \<union> A2 else A1) \<Longrightarrow>
    mok n A tw (mformula.MAnd A1 \<phi> pos A2 \<psi> buf)"
| MokPrev: "mok n A tw \<phi> \<Longrightarrow> list_all (ftable n A) buf \<Longrightarrow>
    mok n A tw (mformula.MPrev I \<phi> first buf nts)"
| MokNext: "mok n A tw \<phi> \<Longrightarrow> mok n A tw (mformula.MNext I \<phi> first nts)"
| MokAgg: "mok (length (aggargs_tys args) + n) G tw \<phi> \<Longrightarrow>
    aggargs_n args = n \<Longrightarrow> aggargs_y args < n \<Longrightarrow>
    (\<forall>i \<in> G. length (aggargs_tys args) \<le> i) \<Longrightarrow>
    (aggargs_g0 args \<Longrightarrow> G = {}) \<Longrightarrow>
    A = Set.insert (aggargs_y args) ((\<lambda>i. i - length (aggargs_tys args)) ` G) \<Longrightarrow>
    mok n A tw (mformula.MAgg args \<phi>)"
| MokAnds: "length L = length ((A0 # As) @ A_neg) \<Longrightarrow>
    length buf = length ((A0 # As) @ A_neg) \<Longrightarrow>
    (\<forall>i < length ((A0 # As) @ A_neg).
       mok n (((A0 # As) @ A_neg) ! i) tw (L ! i)) \<Longrightarrow>
    (\<forall>i < length ((A0 # As) @ A_neg).
       list_all (ftable n (((A0 # As) @ A_neg) ! i)) (buf ! i)) \<Longrightarrow>
    (\<forall>C \<in> set ((A0 # As) @ A_neg). wf_set n C) \<Longrightarrow>
    (\<forall>B \<in> set A_neg. B \<subseteq> A0 \<union> \<Union>(set As)) \<Longrightarrow> A = A0 \<union> \<Union>(set As) \<Longrightarrow>
    mok n A tw (mformula.MAnds (A0 # As) A_neg L buf)"
| MokSince: "mok n L tw \<phi> \<Longrightarrow> mok n R tw \<psi> \<Longrightarrow>
    saux_inv args n L R tw buf aux \<Longrightarrow> args_agg args = None \<Longrightarrow> args_n args = n \<Longrightarrow>
    args_L args = L \<Longrightarrow> args_R args = R \<Longrightarrow> L \<subseteq> R \<Longrightarrow>
    mok n R tw (mformula.MSince args \<phi> \<psi> buf aux)"
| MokUntil: "mok n L tw \<phi> \<Longrightarrow> mok n R tw \<psi> \<Longrightarrow>
    until_inv args n L R tw t aux buf nts \<Longrightarrow> args_agg args = None \<Longrightarrow>
    args_n args = n \<Longrightarrow> args_L args = L \<Longrightarrow> args_R args = R \<Longrightarrow> L \<subseteq> R \<Longrightarrow>
    mok n R tw (mformula.MUntil args \<phi> \<psi> buf nts t aux)"
| MokTrigger: "mok n L tw \<phi> \<Longrightarrow> mok n R tw \<psi> \<Longrightarrow>
    trigger_inv args n L R tw aux buf nts \<Longrightarrow> args_n args = n \<Longrightarrow>
    args_L args = L \<Longrightarrow> args_R args = R \<Longrightarrow> mem (args_ivl args) 0 \<Longrightarrow>
    mok n R tw (mformula.MTrigger args \<phi> \<psi> buf nts aux)"
| MokAndTrigger: "mok n A tw \<alpha> \<Longrightarrow> mok n L tw \<phi> \<Longrightarrow> mok n R tw \<psi> \<Longrightarrow>
    trigger_inv args n L R tw aux buf2 nts \<Longrightarrow>
    list_all (ftable n A) (fst buf1) \<Longrightarrow>
    list_all (\<lambda>p. fst p = R \<and> ftable n R (snd p)) (snd buf1) \<Longrightarrow>
    args_n args = n \<Longrightarrow> args_L args = L \<Longrightarrow> args_R args = R \<Longrightarrow>
    mem (args_ivl args) 0 \<Longrightarrow> R \<subseteq> A \<Longrightarrow>
    mok n A tw (mformula.MAndTrigger A \<alpha> buf1 args \<phi> \<psi> buf2 nts aux)"
| MokLet: "mok m {0..<m} tw \<phi> \<Longrightarrow> mok n A tw \<psi> \<Longrightarrow>
    mok n A tw (mformula.MLet p m \<phi> \<psi>)"
| MokLetPast: "mok m {0..<m} tw \<phi> \<Longrightarrow> mok n A tw \<psi> \<Longrightarrow>
    (\<forall>y. buf = Some y \<longrightarrow> ftable m {0..<m} y) \<Longrightarrow>
    mok n A tw (mformula.MLetPast p m \<phi> \<psi> i buf)"
| MokFrz: "mok m {0..<m} tw \<phi> \<Longrightarrow> mok n A tw \<psi> \<Longrightarrow>
    list_all (ftable m {0..<m}) \<alpha>s \<Longrightarrow>
    mok n A tw (mformula.MFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s)"
| MokMatchP: "Regex.safe_regex fv rgx_safe_pred Past Strict
      (from_mregex mr (\<psi>s :: ty Formula.formula list)) \<Longrightarrow>
    ok (length \<psi>s) mr \<Longrightarrow> A = fv_regex (from_mregex mr \<psi>s) \<Longrightarrow>
    distinct mrs \<Longrightarrow> set mrs = RPDs mr \<Longrightarrow>
    (\<forall>i < length \<psi>s. Formula.fv (\<psi>s ! i) \<subseteq> A) \<Longrightarrow>
    length L = length \<psi>s \<Longrightarrow>
    (\<forall>i < length \<psi>s. mok n (Formula.fv (\<psi>s ! i)) tw (L ! i)) \<Longrightarrow>
    length buf = length \<psi>s \<Longrightarrow>
    (\<forall>i < length \<psi>s. list_all (ftable n (Formula.fv (\<psi>s ! i))) (buf ! i)) \<Longrightarrow>
    maux_inv n A aux \<Longrightarrow>
    mok n A tw (mformula.MMatchP I mr mrs L buf nts aux)"
| MokMatchF: "Regex.safe_regex fv rgx_safe_pred Futu Strict
      (from_mregex mr (\<psi>s :: ty Formula.formula list)) \<Longrightarrow>
    ok (length \<psi>s) mr \<Longrightarrow> A = fv_regex (from_mregex mr \<psi>s) \<Longrightarrow>
    distinct mrs \<Longrightarrow> set mrs = LPDs mr \<Longrightarrow>
    (\<forall>i < length \<psi>s. Formula.fv (\<psi>s ! i) \<subseteq> A) \<Longrightarrow>
    length L = length \<psi>s \<Longrightarrow>
    (\<forall>i < length \<psi>s. mok n (Formula.fv (\<psi>s ! i)) tw (L ! i)) \<Longrightarrow>
    length buf = length \<psi>s \<Longrightarrow>
    (\<forall>i < length \<psi>s. list_all (ftable n (Formula.fv (\<psi>s ! i))) (buf ! i)) \<Longrightarrow>
    mfaux_inv n A \<psi>s aux \<Longrightarrow>
    mok n A tw (mformula.MMatchF I mr mrs L buf nts t aux)"

text \<open>
  Every rule is discharged by the node lemma it was read off, applied to the induction
  hypotheses of its operands.
\<close>

theorem mok_produces: "mok n A tw \<phi> \<Longrightarrow> produces n A tw \<phi>"
proof (induct rule: mok.induct)
  case MokRel then show ?case by (auto intro: produces_MRel)
next
  case MokNeg then show ?case by (rule produces_MNeg)
next
  case MokAndRel then show ?case by (auto intro: produces_MAndRel)
next
  case MokAndAssign then show ?case by (auto intro: produces_MAndAssign)
next
  case MokExists then show ?case by (auto intro: produces_MExists)
next
  case MokPredC then show ?case by (auto intro: produces_MPred_Copy)
next
  case MokPredS then show ?case by (auto intro: produces_MPred_Simple)
next
  case MokPredM then show ?case by (auto intro: produces_MPred_Match)
next
  case MokTP then show ?case by (auto intro: produces_MTP)
next
  case MokTS then show ?case by (auto intro: produces_MTS)
next
  case MokOr then show ?case by (auto intro: produces_MOr)
next
  case (MokAnd n A1 tw \<phi> A2 \<psi> buf pos A)
  show ?case
    by (rule produces_MAnd[OF MokAnd(2) MokAnd(4) MokAnd(5) MokAnd(6) MokAnd(7) MokAnd(8)])
next
  case MokPrev then show ?case by (auto intro: produces_MPrev)
next
  case MokNext then show ?case by (auto intro: produces_MNext)
next
  case MokAgg then show ?case by (auto intro: produces_MAgg)
next
  case (MokAnds L A0 As A_neg buf n tw A)
  have pL: "\<forall>i < length ((A0 # As) @ A_neg).
      produces n (((A0 # As) @ A_neg) ! i) tw (L ! i)"
    using MokAnds(3) by blast
  show ?case
    by (rule produces_MAnds[OF MokAnds(1) MokAnds(2) pL MokAnds(4) MokAnds(5)
        MokAnds(6) MokAnds(7)])
next
  case MokSince
  show ?case
    by (rule produces_MSince[OF MokSince(2) MokSince(4) MokSince(5) MokSince(6)
        MokSince(7) MokSince(8) MokSince(9) MokSince(10)])
next
  case MokUntil
  show ?case
    by (rule produces_MUntil[OF MokUntil(2) MokUntil(4) MokUntil(5) MokUntil(6)
        MokUntil(7) MokUntil(8) MokUntil(9) MokUntil(10)])
next
  case MokTrigger
  show ?case
    by (rule produces_MTrigger[OF MokTrigger(2) MokTrigger(4) MokTrigger(5)
        MokTrigger(6) MokTrigger(7) MokTrigger(8) MokTrigger(9)])
next
  case MokAndTrigger
  show ?case
    by (rule produces_MAndTrigger[OF MokAndTrigger(2) MokAndTrigger(4) MokAndTrigger(6)
        MokAndTrigger(7) MokAndTrigger(8) MokAndTrigger(9) MokAndTrigger(10)
        MokAndTrigger(11) MokAndTrigger(12) MokAndTrigger(13) MokAndTrigger(14)])
next
  case MokLet
  show ?case by (rule produces_MLet[OF MokLet(2) MokLet(4)])
next
  case MokLetPast
  show ?case by (rule produces_MLetPast[OF MokLetPast(2) MokLetPast(4) MokLetPast(5)])
next
  case MokFrz
  show ?case by (rule produces_MFrz[OF MokFrz(2) MokFrz(4) MokFrz(5)])
next
  case (MokMatchP mr \<psi>s A mrs L n tw buf aux I nts)
  have pL: "\<forall>i < length \<psi>s. produces n (Formula.fv (\<psi>s ! i)) tw (L ! i)"
    using MokMatchP(8) by blast
  show ?case
    by (rule produces_MMatchP[OF MokMatchP(1) MokMatchP(2) MokMatchP(3) MokMatchP(4)
        MokMatchP(5) MokMatchP(6) MokMatchP(7) pL MokMatchP(9) MokMatchP(10) MokMatchP(11)])
next
  case (MokMatchF mr \<psi>s A mrs L n tw buf aux I nts t)
  have pL: "\<forall>i < length \<psi>s. produces n (Formula.fv (\<psi>s ! i)) tw (L ! i)"
    using MokMatchF(8) by blast
  show ?case
    by (rule produces_MMatchF[OF MokMatchF(1) MokMatchF(2) MokMatchF(3) MokMatchF(4)
        MokMatchF(5) MokMatchF(6) MokMatchF(7) pL MokMatchF(9) MokMatchF(10) MokMatchF(11)])
qed

section \<open>Closing the chain\<close>

text \<open>
  The transferred correctness theorems of @{theory MFODL_Monitor_Imp.Dense_Correct} all ask the
  caller for a related initial state, @{term "dmsim_state n cs 0 (minit_safe \<phi>) dst"}, and
  until one is produced they say nothing about any concrete monitor.  @{thm [source] DsPure} is the
  cheapest way to produce one: it relates @{term "DPure \<phi> n (wide_mask n cs)"} to
  @{term \<phi>} for any kernel state that @{const produces} finite tables over @{term "set cs"}.
  The dense monitor built this way runs the kernel's own evaluator and narrows its output, so it
  is the bottom of the refinement rather than the interesting point of it; what it settles is
  that the theorems are about something.  Everything the criterion of the previous section buys
  is the hypothesis @{const produces}, which @{thm [source] mok_produces} now supplies from a
  structural check.
\<close>

definition dpure_state :: "nat \<Rightarrow> cols \<Rightarrow>
    (mmasaux, muaux_dq, event_data mmtaux) mstate \<Rightarrow> dmstate" where
  "dpure_state n cs st =
     \<lparr> dmstate_i = mstate_i st, dmstate_j = mstate_j st,
       dmstate_m = DPure (mstate_m st) n (wide_mask n cs),
       dmstate_n = n, dmstate_cs = cs, dmstate_t = mstate_t st \<rparr>"

lemma dmsim_state_dpure_state:
  assumes w: "wf_cols n cs" and n: "mstate_n st = n"
    and p: "produces n (set cs) tw (mstate_m st)"
  shows "dmsim_state n cs tw st (dpure_state n cs st)"
  by (simp add: dmsim_state_def dpure_state_def n DsPure[OF w p])

lemma dmsim_state_dpure_state_mok:
  assumes w: "wf_cols n cs" and n: "mstate_n st = n"
    and p: "mok n (set cs) tw (mstate_m st)"
  shows "dmsim_state n cs tw st (dpure_state n cs st)"
  by (rule dmsim_state_dpure_state[OF w n mok_produces[OF p]])

context verimon_spec
begin

theorem dmonitor_mverdicts_pure:
  assumes w: "wf_cols n cs" and ni: "mstate_n (minit_safe \<phi>) = n"
    and p: "mok n (set cs) 0 (mstate_m (minit_safe \<phi>))"
    and f: "pfinite \<pi>" and wty: "wty_prefix SIG \<pi>"
  shows "flatten_verdicts (map (\<lambda>(i, t, X). (i, t, dtabw n cs X))
      (dmonitor (dpure_state n cs (minit_safe \<phi>)) \<pi>)) = Mt \<pi>"
  using w by (intro dmonitor_mverdicts[OF dmsim_state_dpure_state_mok[OF w ni p] _ f wty]) simp

end

(*<*)
end
(*>*)
