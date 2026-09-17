(*<*)
theory Dense_Init
  imports Dense_Compile
begin
(*>*)

section \<open>Work in progress: the criterion for the kernel's initial state\<close>

text \<open>
  This theory is NOT part of the session (it is deliberately absent from \<open>ROOT\<close>): five
  of the thirty-two cases of @{text mok_minit0} are still \<open>sorry\<close>.  It is kept in the
  repository so that the twenty-seven finished ones are not lost.

  @{text mok_minit0} is the last open hypothesis of
  @{text dmonitor_mverdicts_pure}: with it, the dense monitor's transferred correctness
  theorems hold outright for every safe formula.  The cases that remain are \<open>Agg\<close>,
  \<open>Trigger_0\<close>, \<open>And_Trigger\<close>, \<open>MatchP\<close> and \<open>MatchF\<close>.
  \<open>And_Trigger\<close> additionally needs a node lemma the theory does not have yet: its
  interval need not contain \<open>0\<close>, and @{thm [source] produces_MAndTrigger} assumes it
  does, because the trigger structure's result carries its own column set, which is the
  operand's only when the window is nonempty.  Joining that pair back against the left operand
  gives a table over the left operand's columns either way, so the node lemma can be weakened --
  that is the next step.
\<close>

lemma ftable_eval_agg':
  assumes t: "table (length tys + n) G rel" and fin: "finite rel"
    and y: "y < n" and g0: "g0 \<Longrightarrow> G \<subseteq> {0..<length tys}"
  shows "ftable n (Set.insert y ((\<lambda>i. i - length tys) ` (G - {0..<length tys})))
      (eval_agg n g0 y \<omega> tys trm rel)"
proof (cases "g0 \<and> rel = empty_table")
  case True
  then have G: "G - {0..<length tys} = {}" using g0 by auto
  have "table n {y} (singleton_table n y (eval_agg_op \<omega> {}))" by simp
  moreover have "finite (singleton_table n y (eval_agg_op \<omega> {}))"
    by (simp add: singleton_table_def)
  ultimately show ?thesis using True by (simp add: eval_agg_def G)
next
  case False
  have w: "\<And>x. x \<in> rel \<Longrightarrow>
      wf_tuple n ((\<lambda>i. i - length tys) ` (G - {0..<length tys})) (drop (length tys) x)"
  proof -
    fix x assume x: "x \<in> rel"
    then have wx: "wf_tuple (length tys + n) G x" using t by (simp add: table_def)
    show "wf_tuple n ((\<lambda>i. i - length tys) ` (G - {0..<length tys})) (drop (length tys) x)"
      unfolding wf_tuple_def
    proof (intro conjI allI impI)
      show "length (drop (length tys) x) = n" using wx by (simp add: wf_tuple_def)
    next
      fix i assume i: "i < n"
      have d: "drop (length tys) x ! i = x ! (length tys + i)"
        using wx i by (simp add: wf_tuple_def)
      have g: "(x ! (length tys + i) = None) = (length tys + i \<notin> G)"
        using wx i by (simp add: wf_tuple_def)
      have s: "(length tys + i \<in> G)
          = (i \<in> (\<lambda>j. j - length tys) ` (G - {0..<length tys}))"
        by (force simp: image_iff)
      show "(drop (length tys) x ! i = None)
          = (i \<notin> (\<lambda>j. j - length tys) ` (G - {0..<length tys}))"
        unfolding d g using s by blast
    qed
  qed
  show ?thesis
    unfolding eval_agg_def if_not_P[OF False]
    using fin w y by (auto simp: table_def Let_def intro!: wf_tuple_insert_upd)
qed

lemma fv_Exists_image:
  "Formula.fv (Formula.Exists t \<phi>) = (\<lambda>x. x - Suc 0) ` (Formula.fv \<phi> - {0})"
proof (intro set_eqI iffI)
  fix x assume "x \<in> Formula.fv (Formula.Exists t \<phi>)"
  then have "Suc x \<in> Formula.fv \<phi>" by (simp add: fvi_Suc)
  then show "x \<in> (\<lambda>x. x - Suc 0) ` (Formula.fv \<phi> - {0})"
    by (intro rev_image_eqI[of "Suc x"]) auto
next
  fix x assume "x \<in> (\<lambda>x. x - Suc 0) ` (Formula.fv \<phi> - {0})"
  then obtain y where y: "y \<in> Formula.fv \<phi>" "y \<noteq> 0" "x = y - Suc 0" by auto
  then have "Suc x \<in> Formula.fv \<phi>" by auto
  then show "x \<in> Formula.fv (Formula.Exists t \<phi>)" by (simp add: fvi_Suc)
qed

lemma saux_inv_init:
  assumes sub: "L \<subseteq> R"
  shows "saux_inv (init_args I n L R b agg) n L R tw init_mbuf2S
     (init_mmasaux (init_args I n L R b agg))"
  by (rule saux_invI[OF valid_init_mmasaux[OF sub]]) auto

lemma until_inv_init:
  assumes sub: "L \<subseteq> R"
  shows "until_inv (init_args I n L R b agg) n L R tw 0
     (init_muaux_dq (init_args I n L R b agg)) ([], []) []"
proof -
  have v: "valid_muaux_dq (init_args I n L R b agg) 0
      (init_muaux_dq (init_args I n L R b agg)) []"
    by (rule valid_init_muaux_dq[OF sub])
  show ?thesis unfolding until_inv_def uaux_inv_def using v by auto
qed

lemma trigger_inv_init:
  assumes m: "mem I 0" and sub: "L \<subseteq> R"
  shows "trigger_inv (init_args I n L R b agg) n L R tw
     (init_mmtaux (init_args I n L R b agg)) ([], []) []"
proof -
  have v: "valid_mmtaux (init_args I n L R b agg) 0
      (init_mmtaux (init_args I n L R b agg)) []"
    using valid_init_mmtaux[where I = I and L = L and R = R and pos = b and n = n and agg = agg]
      m sub by (simp add: Let_def)
  have t: "taux_inv (init_args I n L R b agg) n L R 0
      (init_mmtaux (init_args I n L R b agg))"
    unfolding taux_inv_def using v by (intro exI[of _ "[]"]) simp
  show ?thesis unfolding trigger_inv_def using t by (auto intro!: exI[of _ 0])
qed

lemma mok_minit0:
  "safe_formula \<phi> \<Longrightarrow> \<forall>x \<in> Formula.fv \<phi>. x < n \<Longrightarrow>
   mok n (Formula.fv \<phi>) tw (minit0 n \<phi>)"
proof (induction arbitrary: n rule: safe_formula_induct)
  case (Eq_Const c d)
  show ?case
    by (auto simp: table_def unit_table_def empty_table_def wf_tuple_def intro!: MokRel)
next
  case (Eq_Var1 c x)
  then show ?case
    by (auto simp: table_def singleton_table_def wf_tuple_def intro!: MokRel)
next
  case (Eq_Var2 c x)
  then show ?case
    by (auto simp: table_def singleton_table_def wf_tuple_def intro!: MokRel)
next
  case (Pred e ts)
  have m: "minit0 n (Formula.Pred e ts) = mformula.MPred e ts (pred_mode_of n ts)" by simp
  have A: "Formula.fv (Formula.Pred e ts) = (\<Union>t \<in> set ts. Formula.fv_trm t)" by simp
  show ?case
  proof (cases "pred_mode_of n ts")
    case Copy
    then have c: "ts = map Formula.Var [0..<n]" by (simp add: is_copy_pattern_def)
    show ?thesis unfolding m Copy A
      by (rule MokPredC) (use c in \<open>auto simp: image_iff\<close>)
  next
    case Simple
    then have s: "is_simple_pattern ts 0" by simp
    show ?thesis unfolding m Simple A
      by (rule MokPredS[OF s]) (use Pred in auto)
  next
    case Match
    show ?thesis unfolding m Match A by (rule MokPredM) simp
  qed
next
  case (Let p \<phi> \<psi>)
  have nf: "\<forall>x \<in> Formula.fv \<phi>. x < Formula.nfv \<phi>" by (simp add: fvi_less_nfv)
  have e: "Formula.fv \<phi> = {0..<Formula.nfv \<phi>}" using Let.hyps(1) nf by auto
  have p1: "mok (Formula.nfv \<phi>) {0..<Formula.nfv \<phi>} tw (minit0 (Formula.nfv \<phi>) \<phi>)"
    using Let.IH(1)[OF nf] unfolding e .
  have p2: "mok n (Formula.fv \<psi>) tw (minit0 n \<psi>)"
    using Let.prems by (intro Let.IH(2)) simp
  show ?case by (simp add: MokLet[OF p1 p2])
next
  case (Frz p \<phi> \<psi>)
  have nf: "\<forall>x \<in> Formula.fv \<phi>. x < Formula.nfv \<phi>" by (simp add: fvi_less_nfv)
  have e: "Formula.fv \<phi> = {0..<Formula.nfv \<phi>}" using Frz.hyps(1) nf by auto
  have p1: "mok (Formula.nfv \<phi>) {0..<Formula.nfv \<phi>} tw (minit0 (Formula.nfv \<phi>) \<phi>)"
    using Frz.IH(1)[OF nf] unfolding e .
  have p2: "mok n (Formula.fv \<psi>) tw (minit0 n \<psi>)"
    using Frz.prems by (intro Frz.IH(2)) simp
  show ?case by (simp add: MokFrz[OF p1 p2])
next
  case (LetPast p \<phi> \<psi>)
  have nf: "\<forall>x \<in> Formula.fv \<phi>. x < Formula.nfv \<phi>" by (simp add: fvi_less_nfv)
  have e: "Formula.fv \<phi> = {0..<Formula.nfv \<phi>}" using LetPast.hyps(2) nf by auto
  have p1: "mok (Formula.nfv \<phi>) {0..<Formula.nfv \<phi>} tw (minit0 (Formula.nfv \<phi>) \<phi>)"
    using LetPast.IH(1)[OF nf] unfolding e .
  have p2: "mok n (Formula.fv \<psi>) tw (minit0 n \<psi>)"
    using LetPast.prems by (intro LetPast.IH(2)) simp
  show ?case by (simp add: MokLetPast[OF p1 p2])
next
  case (And_assign \<phi> \<psi>)
  then have 1: "\<forall>x \<in> Formula.fv \<psi>. x < n" by simp
  from 1 \<open>safe_assignment (Formula.fv \<phi>) \<psi>\<close> obtain x t where
    xn: "x < n" and xf: "x \<notin> Formula.fv \<phi>" and tf: "Formula.fv_trm t \<subseteq> Formula.fv \<phi>"
    and eq: "\<psi> = Formula.Eq (Formula.Var x) t \<or> \<psi> = Formula.Eq t (Formula.Var x)"
    unfolding safe_assignment_def by (force split: formula.splits trm.splits)
  have p: "mok n (Formula.fv \<phi>) tw (minit0 n \<phi>)" using And_assign by simp
  show ?case using xn xf tf eq p \<open>safe_assignment (Formula.fv \<phi>) \<psi>\<close>
    by (auto intro!: MokAndAssign split: trm.splits)
next
  case (And_safe \<phi> \<psi>)
  have p1: "mok n (Formula.fv \<phi>) tw (minit0 n \<phi>)" using And_safe by simp
  have p2: "mok n (Formula.fv \<psi>) tw (minit0 n \<psi>)" using And_safe by simp
  have m: "minit0 n (Formula.And \<phi> \<psi>) = mformula.MAnd (Formula.fv \<phi>)
      (minit0 n \<phi>) True (Formula.fv \<psi>) (minit0 n \<psi>) ([], [])"
    using And_safe.hyps by simp
  show ?case unfolding m by (rule MokAnd[OF p1 p2]) auto
next
  case (And_constraint \<phi> \<psi>)
  have p: "mok n (Formula.fv \<phi>) tw (minit0 n \<phi>)" using And_constraint by simp
  have m: "minit0 n (Formula.And \<phi> \<psi>) = mformula.MAndRel (minit0 n \<phi>) (split_constraint \<psi>)"
    using And_constraint.hyps by simp
  have e: "Formula.fv (Formula.And \<phi> \<psi>) = Formula.fv \<phi>"
    using And_constraint.hyps(4) by auto
  show ?case unfolding m e by (rule MokAndRel[OF p])
next
  case (And_Not \<phi> \<psi>)
  have p1: "mok n (Formula.fv \<phi>) tw (minit0 n \<phi>)" using And_Not by simp
  have p2: "mok n (Formula.fv \<psi>) tw (minit0 n \<psi>)" using And_Not by simp
  have sub: "Formula.fv \<psi> \<subseteq> Formula.fv \<phi>" using And_Not.hyps(4) by simp
  have m: "minit0 n (Formula.And \<phi> (Formula.Neg \<psi>)) = mformula.MAnd (Formula.fv \<phi>)
      (minit0 n \<phi>) False (Formula.fv \<psi>) (minit0 n \<psi>) ([], [])"
    using And_Not.hyps by simp
  have e: "Formula.fv (Formula.And \<phi> (Formula.Neg \<psi>)) = Formula.fv \<phi>"
    using sub by auto
  show ?case unfolding m e by (rule MokAnd[OF p1 p2]) (use sub in auto)
next
  case (And_Trigger \<phi> \<phi>' I \<psi>') then show ?case sorry
next
  case (And_Release \<phi> \<phi>' I \<psi>')
  show ?case
    using And_Release.IH(1)[OF And_Release.prems[unfolded release_fvi(3)]]
      And_Release.hyps(5,6)
    by (simp add: release_fvi(3) safe_assignment_def)
next
  case (Ands l pos neg)
  have part: "pos = filter safe_formula l" and negd: "neg = filter (\<lambda>a. \<not> safe_formula a) l"
    using Ands.hyps(1) by (auto simp: o_def)
  have setl: "set l = set pos \<union> set neg" using part negd by auto
  have lenl: "length l = length pos + length neg" using part negd
    by (simp add: sum_length_filter_compl)
  obtain p ps where pl: "pos = p # ps" using Ands.hyps(2) by (cases pos) auto
  have e: "Formula.fv (Formula.Ands l) = \<Union> (Formula.fv ` set pos)"
    using setl Ands.hyps(5) by auto
  have b: "\<forall>x \<in> \<Union> (Formula.fv ` set pos). x < n"
    using Ands.prems setl by auto
  have bn: "\<forall>x \<in> \<Union> (Formula.fv ` set neg). x < n" using b Ands.hyps(5) by blast
  let ?css = "map Formula.fv pos @ map Formula.fv neg"
  let ?L = "map (minit0 n) pos @ map (minit0 n) (map remove_neg neg)"
  have cs: "(Formula.fv p # map Formula.fv ps) @ map Formula.fv neg = ?css"
    by (simp add: pl)
  have lL: "length ?L = length ?css" by simp
  have lb: "length (replicate (length l) []) = length ?css" using lenl by simp
  have pL: "\<forall>i < length ?css. mok n (?css ! i) tw (?L ! i)"
  proof (intro allI impI)
    fix i assume i: "i < length ?css"
    show "mok n (?css ! i) tw (?L ! i)"
    proof (cases "i < length pos")
      case True
      then have c: "?css ! i = Formula.fv (pos ! i)" and l': "?L ! i = minit0 n (pos ! i)"
        by (simp_all add: nth_append)
      have ip: "pos ! i \<in> set pos" using True by simp
      have bi: "\<forall>x \<in> Formula.fv (pos ! i). x < n" using b ip by auto
      show ?thesis unfolding c l'
        using Ands.IH(1)[unfolded list_all_iff] ip bi by blast
    next
      case False
      let ?j = "i - length pos"
      have j: "?j < length neg" using i False by simp
      have c: "?css ! i = Formula.fv (neg ! ?j)" using False j by (simp add: nth_append)
      have l': "?L ! i = minit0 n (remove_neg (neg ! ?j))"
        using False j by (simp add: nth_append)
      have ip: "remove_neg (neg ! ?j) \<in> set (map remove_neg neg)" using j by simp
      have bi: "\<forall>x \<in> Formula.fv (remove_neg (neg ! ?j)). x < n"
        using bn j by (auto simp: fv_remove_neg[symmetric])
      have "mok n (Formula.fv (remove_neg (neg ! ?j))) tw (minit0 n (remove_neg (neg ! ?j)))"
        using Ands.IH(2)[unfolded list_all_iff] ip bi by blast
      then show ?thesis unfolding c l' by (simp add: fv_remove_neg[symmetric])
    qed
  qed
  have pb: "\<forall>i < length ?css.
      list_all (ftable n (?css ! i)) (replicate (length l) [] ! i)"
    using lenl by simp
  have wf: "\<forall>C \<in> set ?css. wf_set n C" using b bn by (auto simp: wf_set_def)
  have sn: "\<forall>B \<in> set (map Formula.fv neg).
      B \<subseteq> Formula.fv p \<union> \<Union> (set (map Formula.fv ps))"
    using Ands.hyps(5) pl by auto
  have m: "minit0 n (Formula.Ands l) = mformula.MAnds (Formula.fv p # map Formula.fv ps)
      (map Formula.fv neg) ?L (replicate (length l) [])"
    using Ands.hyps(1)[symmetric] pl by (simp add: Let_def)
  have A: "Formula.fv (Formula.Ands l)
      = Formula.fv p \<union> \<Union> (set (map Formula.fv ps))" using e pl by simp
  show ?case unfolding m A
    by (rule MokAnds[OF lL[unfolded cs[symmetric]] lb[unfolded cs[symmetric]]
        pL[unfolded cs[symmetric]] pb[unfolded cs[symmetric]]
        wf[unfolded cs[symmetric]] sn refl])
next
  case (Neg \<phi>)
  show ?case using Neg.hyps(1) by (simp add: MokNeg)
next
  case (Or \<phi> \<psi>)
  have p1: "mok n (Formula.fv \<phi>) tw (minit0 n \<phi>)"
    using Or.prems by (intro Or.IH(1)) simp
  have p2: "mok n (Formula.fv \<psi>) tw (minit0 n \<psi>)"
    using Or.prems by (intro Or.IH(2)) (simp add: Or.hyps(1))
  have m: "minit0 n (Formula.Or \<phi> \<psi>) = mformula.MOr (minit0 n \<phi>) (minit0 n \<psi>) ([], [])"
    by simp
  have e: "Formula.fv (Formula.Or \<phi> \<psi>) = Formula.fv \<phi>" using Or.hyps(1) by simp
  show ?case unfolding m e
    by (rule MokOr[OF p1 p2[unfolded Or.hyps(1)]]) auto
next
  case (Exists t \<phi>)
  have b: "\<forall>x \<in> Formula.fv \<phi>. x < Suc n"
    using fvi_Suc_bound[where b = 0 and \<phi> = \<phi> and n = n] Exists.prems by simp
  have p: "mok (Suc n) (Formula.fv \<phi>) tw (minit0 (Suc n) \<phi>)" by (rule Exists.IH[OF b])
  have m: "minit0 n (Formula.Exists t \<phi>) = mformula.MExists (minit0 (Suc n) \<phi>)" by simp
  have e: "Formula.fv (Formula.Exists t \<phi>)
      = (\<lambda>x. x - Suc 0) ` (Formula.fv \<phi> - {0})"
    by (rule fv_Exists_image)
  show ?case unfolding m by (rule MokExists[OF p e])
next
  case (Agg y \<omega> tys f \<phi>) then show ?case sorry
next
  case (Prev I \<phi>)
  have p: "mok n (Formula.fv \<phi>) tw (minit0 n \<phi>)"
    using Prev.prems by (intro Prev.IH) simp
  have m: "minit0 n (Formula.Prev I \<phi>) = mformula.MPrev I (minit0 n \<phi>) True [] []" by simp
  have e: "Formula.fv (Formula.Prev I \<phi>) = Formula.fv \<phi>" by simp
  show ?case unfolding m e by (rule MokPrev[OF p]) simp
next
  case (Next I \<phi>)
  have p: "mok n (Formula.fv \<phi>) tw (minit0 n \<phi>)"
    using Next.prems by (intro Next.IH) simp
  have m: "minit0 n (Formula.Next I \<phi>) = mformula.MNext I (minit0 n \<phi>) True []" by simp
  have e: "Formula.fv (Formula.Next I \<phi>) = Formula.fv \<phi>" by simp
  show ?case unfolding m e by (rule MokNext[OF p])
next
  case (Since \<phi> I \<psi>)
  note sub = \<open>Formula.fv \<phi> \<subseteq> Formula.fv \<psi>\<close>
  have b: "\<forall>x \<in> Formula.fv \<psi>. x < n" using Since.prems by simp
  have p1: "mok n (Formula.fv \<phi>) tw (minit0 n \<phi>)"
    using b sub by (intro Since.IH(1)) auto
  have p2: "mok n (Formula.fv \<psi>) tw (minit0 n \<psi>)" by (rule Since.IH(2)[OF b])
  let ?args = "init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) True None"
  have m: "minit0 n (Formula.Since \<phi> I \<psi>) =
      mformula.MSince ?args (minit0 n \<phi>) (minit0 n \<psi>) init_mbuf2S (init_mmasaux ?args)"
    using Since.hyps(2) by (simp add: default_mmasaux.init_since_def)
  have e: "Formula.fv (Formula.Since \<phi> I \<psi>) = Formula.fv \<psi>" using sub by auto
  show ?case unfolding m e
    by (rule MokSince[OF p1 p2 saux_inv_init[OF sub]]) (simp_all add: init_args_def sub)
next
  case (Not_Since \<phi> I \<psi>)
  have sub: "Formula.fv \<phi> \<subseteq> Formula.fv \<psi>" using Not_Since.hyps(1) by simp
  have b: "\<forall>x \<in> Formula.fv \<psi>. x < n" using Not_Since.prems by simp
  have p1: "mok n (Formula.fv \<phi>) tw (minit0 n \<phi>)"
    using b sub by (intro Not_Since.IH(1)) auto
  have p2: "mok n (Formula.fv \<psi>) tw (minit0 n \<psi>)" by (rule Not_Since.IH(2)[OF b])
  let ?args = "init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) False None"
  have m: "minit0 n (Formula.Since (Formula.Neg \<phi>) I \<psi>) =
      mformula.MSince ?args (minit0 n \<phi>) (minit0 n \<psi>) init_mbuf2S (init_mmasaux ?args)"
    using Not_Since.hyps(3) by (simp add: default_mmasaux.init_since_def)
  have e: "Formula.fv (Formula.Since (Formula.Neg \<phi>) I \<psi>) = Formula.fv \<psi>"
    using sub by auto
  show ?case unfolding m e
    by (rule MokSince[OF p1 p2 saux_inv_init[OF sub]]) (simp_all add: init_args_def sub)
next
  case (Until \<phi> I \<psi>)
  note sub = \<open>Formula.fv \<phi> \<subseteq> Formula.fv \<psi>\<close>
  have b: "\<forall>x \<in> Formula.fv \<psi>. x < n" using Until.prems by simp
  have p1: "mok n (Formula.fv \<phi>) tw (minit0 n \<phi>)"
    using b sub by (intro Until.IH(1)) auto
  have p2: "mok n (Formula.fv \<psi>) tw (minit0 n \<psi>)" by (rule Until.IH(2)[OF b])
  let ?args = "init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) True None"
  have m: "minit0 n (Formula.Until \<phi> I \<psi>) =
      mformula.MUntil ?args (minit0 n \<phi>) (minit0 n \<psi>) ([], []) [] 0 (init_muaux_dq ?args)"
    using Until.hyps(2) by (simp add: dq_muaux.init_until_def)
  have e: "Formula.fv (Formula.Until \<phi> I \<psi>) = Formula.fv \<psi>" using sub by auto
  show ?case unfolding m e
    by (rule MokUntil[OF p1 p2 until_inv_init[OF sub]]) (simp_all add: init_args_def sub)
next
  case (Not_Until \<phi> I \<psi>)
  have sub: "Formula.fv \<phi> \<subseteq> Formula.fv \<psi>" using Not_Until.hyps(1) by simp
  have b: "\<forall>x \<in> Formula.fv \<psi>. x < n" using Not_Until.prems by simp
  have p1: "mok n (Formula.fv \<phi>) tw (minit0 n \<phi>)"
    using b sub by (intro Not_Until.IH(1)) auto
  have p2: "mok n (Formula.fv \<psi>) tw (minit0 n \<psi>)" by (rule Not_Until.IH(2)[OF b])
  let ?args = "init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) False None"
  have m: "minit0 n (Formula.Until (Formula.Neg \<phi>) I \<psi>) =
      mformula.MUntil ?args (minit0 n \<phi>) (minit0 n \<psi>) ([], []) [] 0 (init_muaux_dq ?args)"
    using Not_Until.hyps(3) by (simp add: dq_muaux.init_until_def)
  have e: "Formula.fv (Formula.Until (Formula.Neg \<phi>) I \<psi>) = Formula.fv \<psi>"
    using sub by auto
  show ?case unfolding m e
    by (rule MokUntil[OF p1 p2 until_inv_init[OF sub]]) (simp_all add: init_args_def sub)
next
  case (Trigger_0 \<phi> I \<psi>) then show ?case sorry
next
  case (Trigger \<phi> I \<psi>) then show ?case by simp
next
  case (Release_0 \<phi> I \<psi>)
  show ?case
    using Release_0.IH[OF Release_0.prems[unfolded release_fvi(1)]] Release_0.hyps(1)
    by (simp add: release_fvi(1))
next
  case (Release \<phi> I \<psi>) then show ?case by simp
next
  case (MatchP I r) then show ?case sorry
next
  case (MatchF I r) then show ?case sorry
next
  case (TP t)
  then show ?case by (cases t) (auto intro!: MokTP)
next
  case (TS t)
  then show ?case by (cases t) (auto intro!: MokTS)
qed

(*<*)
end
(*>*)
