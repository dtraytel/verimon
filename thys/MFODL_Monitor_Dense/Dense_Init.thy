(*<*)
theory Dense_Init
  imports Dense_Compile
begin
(*>*)

section \<open>The criterion for the kernel's initial state\<close>

text \<open>
  @{text mok_minit0} says that the kernel's initial state for a safe formula satisfies the
  structural criterion \<open>mok\<close> of the preceding theory, with the formula's free
  variables as its column set.  It is the last open hypothesis of
  @{text dmonitor_mverdicts_dof}, so with it the dense monitor's transferred
  correctness theorems hold for every monitorable formula the compiler covers.

  The proof is by @{thm [source] safe_formula_induct}, one case per constructor.  What each case
  has to supply beyond the induction hypotheses is the initial auxiliary structure's invariant,
  and that comes from the kernel's own \<open>valid_init\<close> lemmas at time \<open>0\<close>:
  the three lemmas @{text saux_inv_init}, @{text until_inv_init} and
  @{text trigger_inv_init} below package them.  The two remaining wrinkles are the column
  arithmetic of the binders -- the existential and the aggregation shift the free variables, so
  their cases go through @{text fvi_image} and @{text fv_Agg_image} -- and the fused conjunction
  with a trigger, which splits on whether the interval contains \<open>0\<close>: when it does,
  the trigger itself is safe and the kernel builds an ordinary conjunction node; when it does
  not, the kernel builds the fused node and the weakened trigger lemmas of
  @{theory MFODL_Monitor_Dense.Dense_Agg} apply.
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

lemma trigger_inv_init_weak:
  assumes wkc: "mem I 0 \<or> (b \<and> L = R)" and sub: "L \<subseteq> R"
  shows "trigger_inv (init_args I n L R b agg) n L R tw
     (init_mmtaux (init_args I n L R b agg)) ([], []) []"
proof -
  have v: "valid_mmtaux (init_args I n L R b agg) 0
      (init_mmtaux (init_args I n L R b agg)) []"
    using valid_init_mmtaux[where I = I and L = L and R = R and pos = b and n = n and agg = agg]
      wkc sub by (auto simp: Let_def)
  have t: "taux_inv (init_args I n L R b agg) n L R 0
      (init_mmtaux (init_args I n L R b agg))"
    unfolding taux_inv_def using v by (intro exI[of _ "[]"]) simp
  show ?thesis unfolding trigger_inv_def using t by (auto intro!: exI[of _ 0])
qed

lemma fvi_image: "Formula.fvi b \<phi> = (\<lambda>i. i - b) ` (Formula.fv \<phi> - {0..<b})"
proof (intro set_eqI iffI)
  fix x assume "x \<in> Formula.fvi b \<phi>"
  then have "x + b \<in> Formula.fv \<phi>" by (rule fvi_iff_fv[THEN iffD1])
  then show "x \<in> (\<lambda>i. i - b) ` (Formula.fv \<phi> - {0..<b})"
    by (intro rev_image_eqI[of "x + b"]) auto
next
  fix x assume "x \<in> (\<lambda>i. i - b) ` (Formula.fv \<phi> - {0..<b})"
  then obtain j where j: "j \<in> Formula.fv \<phi>" "b \<le> j" "x = j - b" by auto
  then have "x + b \<in> Formula.fv \<phi>" by simp
  then show "x \<in> Formula.fvi b \<phi>" by (rule fvi_iff_fv[THEN iffD2])
qed

lemma fvi_trm_mono:
  assumes s: "Formula.fv_trm f \<subseteq> Formula.fv \<phi>"
  shows "Formula.fvi_trm b f \<subseteq> Formula.fvi b \<phi>"
proof
  fix x assume "x \<in> Formula.fvi_trm b f"
  then have "x + b \<in> Formula.fv_trm f" by (rule fvi_trm_iff_fv_trm[THEN iffD1])
  then have "x + b \<in> Formula.fv \<phi>" using s by blast
  then show "x \<in> Formula.fvi b \<phi>" by (rule fvi_iff_fv[THEN iffD2])
qed

lemma fv_Agg_image:
  assumes t: "Formula.fvi_trm (length tys) f \<subseteq> Formula.fvi (length tys) \<phi>"
  shows "Formula.fv (Formula.Agg y \<omega> tys f \<phi>)
     = Set.insert y ((\<lambda>i. i - length tys) ` (Formula.fv \<phi> - {0..<length tys}))"
  using t by (auto simp: fvi_image[symmetric])

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
  case (And_Trigger \<phi> \<phi>' I \<psi>')
  note sp = \<open>safe_formula \<phi>\<close> and sp' = \<open>safe_formula \<phi>'\<close>
  note sd = \<open>safe_dual True safe_formula \<phi>' I \<psi>'\<close>
  note subf = \<open>Formula.fv (Formula.Trigger \<phi>' I \<psi>') \<subseteq> Formula.fv \<phi>\<close>
  have sub: "Formula.fv \<phi>' \<subseteq> Formula.fv \<psi>'"
    using sd sp' by (auto simp: safe_dual_def split: if_splits)
  have subR: "Formula.fv \<psi>' \<subseteq> Formula.fv \<phi>" using subf by auto
  have bA: "\<forall>x \<in> Formula.fv \<phi>. x < n" using And_Trigger.prems by simp
  have bR: "\<forall>x \<in> Formula.fv \<psi>'. x < n" using bA subR by auto
  have bL: "\<forall>x \<in> Formula.fv \<phi>'. x < n" using bR sub by auto
  have pa: "mok n (Formula.fv \<phi>) tw (minit0 n \<phi>)" by (rule And_Trigger(5)[OF bA])
  have p1: "mok n (Formula.fv \<phi>') tw (minit0 n \<phi>')" by (rule And_Trigger(6)[OF bL])
  have p2: "mok n (Formula.fv \<psi>') tw (minit0 n \<psi>')" by (rule And_Trigger(7)[OF bR])
  have fvt: "Formula.fv \<phi>' \<union> Formula.fv \<psi>' = Formula.fv \<psi>'" using sub by auto
  have et: "Formula.fv (Formula.Trigger \<phi>' I \<psi>') = Formula.fv \<psi>'" using sub by auto
  have e: "Formula.fv (Formula.And \<phi> (Formula.Trigger \<phi>' I \<psi>')) = Formula.fv \<phi>"
    using subf by auto
  let ?args = "\<lambda>b. init_args I n (Formula.fv \<phi>') (Formula.fv \<psi>') b None"
  show ?case
  proof (cases "mem I 0")
    case True
    have st: "safe_formula (Formula.Trigger \<phi>' I \<psi>')"
      using sd sp' True by (simp add: safe_dual_def)
    have mt: "minit0 n (Formula.Trigger \<phi>' I \<psi>') = mformula.MTrigger (?args True)
        (minit0 n \<phi>') (minit0 n \<psi>') ([], []) [] (init_mmtaux (?args True))"
      using sp' by (simp add: verimon_maux.init_trigger_def)
    have pt: "mok n (Formula.fv \<psi>') tw (minit0 n (Formula.Trigger \<phi>' I \<psi>'))"
      unfolding mt
      by (rule MokTrigger[OF p1 p2 trigger_inv_init[OF True sub]])
        (simp_all add: init_args_def True)
    have m: "minit0 n (Formula.And \<phi> (Formula.Trigger \<phi>' I \<psi>')) =
        mformula.MAnd (Formula.fv \<phi>) (minit0 n \<phi>) True (Formula.fv \<psi>')
          (minit0 n (Formula.Trigger \<phi>' I \<psi>')) ([], [])"
      using st fvt by (simp add: no_safe_assign_trigger)
    show ?thesis unfolding m e
      by (rule MokAnd[OF pa pt]) (use subR in auto)
  next
    case False
    have LR: "Formula.fv \<phi>' = Formula.fv \<psi>'"
      using sd False by (simp add: safe_dual_def)
    have nst: "\<not> safe_formula (Formula.Trigger \<phi>' I \<psi>')"
      using False by (simp add: safe_dual_def)
    have m: "minit0 n (Formula.And \<phi> (Formula.Trigger \<phi>' I \<psi>')) =
        mformula.MAndTrigger (Formula.fv \<phi>) (minit0 n \<phi>) ([], []) (?args True)
          (minit0 n \<phi>') (minit0 n \<psi>') ([], []) [] (init_mmtaux (?args True))"
      using nst sp' by (simp add: no_safe_assign_trigger verimon_maux.init_and_trigger_def)
    have wkc: "mem (args_ivl (?args True)) 0 \<or>
        (args_pos (?args True) \<and> Formula.fv \<phi>' = Formula.fv \<psi>')"
      using LR by (simp add: init_args_def)
    show ?thesis unfolding m e
      by (rule MokAndTrigger[OF pa p1 p2
          trigger_inv_init_weak[OF _ sub] _ _ _ _ _ wkc])
        (use subR LR in \<open>simp_all add: init_args_def\<close>)
  qed
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
  case (Agg y \<omega> tys f \<phi>)
  note tsub = \<open>{0..<length tys} \<subseteq> Formula.fv \<phi>\<close>
  note fsub = \<open>Formula.fv_trm f \<subseteq> Formula.fv \<phi>\<close>
  note sf = \<open>safe_formula \<phi>\<close>
  have A: "Formula.fv (Formula.Agg y \<omega> tys f \<phi>)
      = Set.insert y ((\<lambda>i. i - length tys) ` (Formula.fv \<phi> - {0..<length tys}))"
    by (rule fv_Agg_image[OF fvi_trm_mono[OF fsub]])
  have yn: "y < n" using Agg.prems A by simp
  have bp: "\<forall>x \<in> Formula.fv \<phi>. x < length tys + n"
  proof
    fix x assume x: "x \<in> Formula.fv \<phi>"
    show "x < length tys + n"
    proof (cases "x < length tys")
      case True then show ?thesis by simp
    next
      case False
      then have "x - length tys
          \<in> (\<lambda>i. i - length tys) ` (Formula.fv \<phi> - {0..<length tys})" using x by auto
      then have "x - length tys < n" using Agg.prems A by auto
      then show ?thesis using False by simp
    qed
  qed
  let ?ag = "init_aggargs (Formula.fv \<phi>) n (Formula.fv \<phi> \<subseteq> {0..<length tys}) y \<omega> tys f"
  have ag: "\<And>c g. aggargs_n (init_aggargs c n g y \<omega> tys f) = n"
      "\<And>c g. aggargs_y (init_aggargs c n g y \<omega> tys f) = y"
      "\<And>c g. aggargs_tys (init_aggargs c n g y \<omega> tys f) = tys"
      "\<And>c g. aggargs_g0 (init_aggargs c n g y \<omega> tys f) = g"
    by (simp_all add: init_aggargs_def)
  have p: "mok (length tys + n) (Formula.fv \<phi>) tw (minit0 (length tys + n) \<phi>)"
    by (rule Agg.IH[OF order_refl sf bp])
  have D: "mok n (Formula.fv (Formula.Agg y \<omega> tys f \<phi>)) tw
      (mformula.MAgg ?ag (minit0 (length tys + n) \<phi>))"
    unfolding A
  proof (rule MokAgg[where args = "?ag" and G = "Formula.fv \<phi>"])
    show "mok (length (aggargs_tys ?ag) + n) (Formula.fv \<phi>) tw
        (minit0 (length tys + n) \<phi>)" using p by (simp add: init_aggargs_def)
  qed (simp_all add: init_aggargs_def yn)
  show ?case
  proof (cases \<phi>)
    case (Since \<chi> I \<eta>)
    have s: "Formula.fv \<chi> \<subseteq> Formula.fv \<eta>" and se: "safe_formula \<eta>"
      and sc: "safe_formula \<chi> \<or>
        (case \<chi> of Formula.Neg \<chi>' \<Rightarrow> safe_formula \<chi>' | _ \<Rightarrow> False)"
      using sf unfolding Since by auto
    have R: "Formula.fv \<eta> = Formula.fv \<phi>" using s unfolding Since by auto
    have bR: "\<forall>x \<in> Formula.fv \<eta>. x < length tys + n" using bp R by simp
    have bL: "\<forall>x \<in> Formula.fv \<chi>. x < length tys + n" using bR s by auto
    have p2: "mok (length tys + n) (Formula.fv \<eta>) tw (minit0 (length tys + n) \<eta>)"
      by (rule Agg.IH[OF _ se bR]) (simp add: Since)
    have Ag: "Formula.fv (Formula.Agg y \<omega> tys f \<phi>)
        = Set.insert y ((\<lambda>i. i - length tys) ` (Formula.fv \<eta> - {0..<length tys}))"
      unfolding A R ..
    show ?thesis
    proof (cases "safe_formula \<chi>")
      case True
      have p1: "mok (length tys + n) (Formula.fv \<chi>) tw (minit0 (length tys + n) \<chi>)"
        by (rule Agg.IH[OF _ True bL]) (simp add: Since)
      let ?args = "init_args I (length tys + n) (Formula.fv \<chi>) (Formula.fv \<eta>)
          True (Some ?ag)"
      have m: "minit0 n (Formula.Agg y \<omega> tys f \<phi>) = mformula.MSince ?args
          (minit0 (length tys + n) \<chi>) (minit0 (length tys + n) \<eta>) init_mbuf2S
          (init_mmasaux ?args)"
        using True unfolding Since
        by (simp add: Let_def default_mmasaux.init_since_def)
      have aggeq: "args_agg ?args = Some ?ag" by (simp add: init_args_def)
      show ?thesis unfolding m Ag
        by (rule MokSinceAgg[OF p1 p2 saux_inv_init[OF s] aggeq])
          (simp_all add: init_args_def ag s[unfolded R] yn R)
    next
      case False
      have "case \<chi> of Formula.Neg \<chi>' \<Rightarrow> safe_formula \<chi>' | _ \<Rightarrow> False"
        using sc False by simp
      then obtain \<chi>' where chi: "\<chi> = Formula.Neg \<chi>'" and sc': "safe_formula \<chi>'"
        by (cases \<chi>) auto
      have fvc: "Formula.fv \<chi>' = Formula.fv \<chi>" using chi by simp
      have bL': "\<forall>x \<in> Formula.fv \<chi>'. x < length tys + n"
        using bL unfolding fvc[symmetric] .
      have p1: "mok (length tys + n) (Formula.fv \<chi>) tw (minit0 (length tys + n) \<chi>')"
        unfolding fvc[symmetric]
        by (rule Agg.IH[OF _ sc' bL']) (simp add: Since chi)
      let ?args = "init_args I (length tys + n) (Formula.fv \<chi>) (Formula.fv \<eta>)
          False (Some ?ag)"
      have m: "minit0 n (Formula.Agg y \<omega> tys f \<phi>) = mformula.MSince ?args
          (minit0 (length tys + n) \<chi>') (minit0 (length tys + n) \<eta>) init_mbuf2S
          (init_mmasaux ?args)"
        using False chi unfolding Since
        by (simp add: Let_def default_mmasaux.init_since_def)
      have aggeq: "args_agg ?args = Some ?ag" by (simp add: init_args_def)
      show ?thesis unfolding m Ag
        by (rule MokSinceAgg[OF p1 p2 saux_inv_init[OF s] aggeq])
          (simp_all add: init_args_def ag s[unfolded R] yn R)
    qed
  next
    case (Until \<chi> I \<eta>)
    have s: "Formula.fv \<chi> \<subseteq> Formula.fv \<eta>" and se: "safe_formula \<eta>"
      and sc: "safe_formula \<chi> \<or>
        (case \<chi> of Formula.Neg \<chi>' \<Rightarrow> safe_formula \<chi>' | _ \<Rightarrow> False)"
      using sf unfolding Until by auto
    have R: "Formula.fv \<eta> = Formula.fv \<phi>" using s unfolding Until by auto
    have bR: "\<forall>x \<in> Formula.fv \<eta>. x < length tys + n" using bp R by simp
    have bL: "\<forall>x \<in> Formula.fv \<chi>. x < length tys + n" using bR s by auto
    have p2: "mok (length tys + n) (Formula.fv \<eta>) tw (minit0 (length tys + n) \<eta>)"
      by (rule Agg.IH[OF _ se bR]) (simp add: Until)
    have Ag: "Formula.fv (Formula.Agg y \<omega> tys f \<phi>)
        = Set.insert y ((\<lambda>i. i - length tys) ` (Formula.fv \<eta> - {0..<length tys}))"
      unfolding A R ..
    show ?thesis
    proof (cases "safe_formula \<chi>")
      case True
      have p1: "mok (length tys + n) (Formula.fv \<chi>) tw (minit0 (length tys + n) \<chi>)"
        by (rule Agg.IH[OF _ True bL]) (simp add: Until)
      let ?args = "init_args I (length tys + n) (Formula.fv \<chi>) (Formula.fv \<eta>)
          True (Some ?ag)"
      have m: "minit0 n (Formula.Agg y \<omega> tys f \<phi>) = mformula.MUntil ?args
          (minit0 (length tys + n) \<chi>) (minit0 (length tys + n) \<eta>) ([], []) [] 0
          (init_muaux_dq ?args)"
        using True unfolding Until by (simp add: Let_def dq_muaux.init_until_def)
      have aggeq: "args_agg ?args = Some ?ag" by (simp add: init_args_def)
      show ?thesis unfolding m Ag
        by (rule MokUntilAgg[OF p1 p2 until_inv_init[OF s] aggeq])
          (simp_all add: init_args_def ag s[unfolded R] yn R)
    next
      case False
      have "case \<chi> of Formula.Neg \<chi>' \<Rightarrow> safe_formula \<chi>' | _ \<Rightarrow> False"
        using sc False by simp
      then obtain \<chi>' where chi: "\<chi> = Formula.Neg \<chi>'" and sc': "safe_formula \<chi>'"
        by (cases \<chi>) auto
      have fvc: "Formula.fv \<chi>' = Formula.fv \<chi>" using chi by simp
      have bL': "\<forall>x \<in> Formula.fv \<chi>'. x < length tys + n"
        using bL unfolding fvc[symmetric] .
      have p1: "mok (length tys + n) (Formula.fv \<chi>) tw (minit0 (length tys + n) \<chi>')"
        unfolding fvc[symmetric]
        by (rule Agg.IH[OF _ sc' bL']) (simp add: Until chi)
      let ?args = "init_args I (length tys + n) (Formula.fv \<chi>) (Formula.fv \<eta>)
          False (Some ?ag)"
      have m: "minit0 n (Formula.Agg y \<omega> tys f \<phi>) = mformula.MUntil ?args
          (minit0 (length tys + n) \<chi>') (minit0 (length tys + n) \<eta>) ([], []) [] 0
          (init_muaux_dq ?args)"
        using False chi unfolding Until by (simp add: Let_def dq_muaux.init_until_def)
      have aggeq: "args_agg ?args = Some ?ag" by (simp add: init_args_def)
      show ?thesis unfolding m Ag
        by (rule MokUntilAgg[OF p1 p2 until_inv_init[OF s] aggeq])
          (simp_all add: init_args_def ag s[unfolded R] yn R)
    qed
  qed (use D in \<open>simp_all add: Let_def\<close>)
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
  case (Trigger_0 \<phi> I \<psi>)
  note m0 = \<open>mem I 0\<close>
  have sub: "Formula.fv \<phi> \<subseteq> Formula.fv \<psi>" using Trigger_0(3) .
  have b: "\<forall>x \<in> Formula.fv \<psi>. x < n" using Trigger_0.prems by simp
  have bp: "\<forall>x \<in> Formula.fv \<phi>. x < n" using b sub by auto
  have p2: "mok n (Formula.fv \<psi>) tw (minit0 n \<psi>)" by (rule Trigger_0(5)[OF b])
  have e: "Formula.fv (Formula.Trigger \<phi> I \<psi>) = Formula.fv \<psi>" using sub by auto
  show ?case
  proof (cases "safe_formula \<phi>")
    case True
    have p1: "mok n (Formula.fv \<phi>) tw (minit0 n \<phi>)"
    proof (cases "\<forall>x. (\<forall>xa \<in> Formula.fv \<phi>. xa < x)
        \<longrightarrow> mok x (Formula.fv \<phi>) tw (minit0 x \<phi>)")
      case True then show ?thesis using bp by blast
    next
      case False
      then have "case \<phi> of Formula.Neg \<chi> \<Rightarrow> safe_formula \<chi> \<and>
          (\<forall>x. (\<forall>xa \<in> Formula.fv \<chi>. xa < x) \<longrightarrow>
            mok x (Formula.fv \<chi>) tw (minit0 x \<chi>)) | _ \<Rightarrow> False"
        using Trigger_0(4) by blast
      then obtain \<chi> where phi: "\<phi> = Formula.Neg \<chi>" by (cases \<phi>) auto
      have "Formula.fv \<chi> = {}" using \<open>safe_formula \<phi>\<close> phi by simp
      then show ?thesis using phi by (simp add: MokNeg)
    qed
    let ?args = "init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) True None"
    have m: "minit0 n (Formula.Trigger \<phi> I \<psi>) = mformula.MTrigger ?args
        (minit0 n \<phi>) (minit0 n \<psi>) ([], []) [] (init_mmtaux ?args)"
      using True by (simp add: verimon_maux.init_trigger_def)
    show ?thesis unfolding m e
      by (rule MokTrigger[OF p1 p2 trigger_inv_init[OF m0 sub]])
        (simp_all add: init_args_def m0)
  next
    case False
    have "case \<phi> of Formula.Neg \<chi> \<Rightarrow> safe_formula \<chi> \<and>
        (\<forall>x. (\<forall>xa \<in> Formula.fv \<chi>. xa < x) \<longrightarrow>
          mok x (Formula.fv \<chi>) tw (minit0 x \<chi>)) | _ \<Rightarrow> False"
      using Trigger_0(4) False by auto
    then obtain \<chi> where phi: "\<phi> = Formula.Neg \<chi>"
      and ih: "\<forall>x. (\<forall>xa \<in> Formula.fv \<chi>. xa < x) \<longrightarrow>
          mok x (Formula.fv \<chi>) tw (minit0 x \<chi>)"
      by (cases \<phi>) auto
    have fvc: "Formula.fv \<chi> = Formula.fv \<phi>" using phi by simp
    have p1: "mok n (Formula.fv \<phi>) tw (minit0 n \<chi>)"
      using ih bp unfolding fvc by blast
    let ?args = "init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) False None"
    have m: "minit0 n (Formula.Trigger \<phi> I \<psi>) = mformula.MTrigger ?args
        (minit0 n \<chi>) (minit0 n \<psi>) ([], []) [] (init_mmtaux ?args)"
      using False phi by (simp add: verimon_maux.init_trigger_def)
    show ?thesis unfolding m e
      by (rule MokTrigger[OF p1 p2 trigger_inv_init[OF m0 sub]])
        (simp_all add: init_args_def m0)
  qed
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
  case (MatchP I r)
  note sr = \<open>Regex.safe_regex fv rgx_safe_pred Past Strict r\<close>
  obtain mr \<phi>s where tm: "to_mregex r = (mr, \<phi>s)" by (cases "to_mregex r")
  have ok: "ok (length \<phi>s) mr" and at: "set \<phi>s = safe_atms r"
    using to_mregex_ok[OF tm] by auto
  have fm: "from_mregex mr \<phi>s = r" by (rule from_mregex_eq[OF sr tm])
  have fr: "Formula.fv_regex r = (\<Union>\<psi> \<in> set \<phi>s. Formula.fv \<psi>)"
    unfolding at by (rule fv_regex_alt2[OF sr])
  have sub: "\<forall>i < length \<phi>s. Formula.fv (\<phi>s ! i) \<subseteq> Formula.fv_regex r"
  proof (intro allI impI subsetI)
    fix i x assume i: "i < length \<phi>s" and x: "x \<in> Formula.fv (\<phi>s ! i)"
    show "x \<in> Formula.fv_regex r" unfolding fr using i x by auto
  qed
  have b: "\<forall>x \<in> Formula.fv_regex r. x < n" using MatchP.prems by simp
  have pL: "\<forall>i < length \<phi>s. mok n (Formula.fv (\<phi>s ! i)) tw (minit0 n (\<phi>s ! i))"
  proof (intro allI impI)
    fix i assume i: "i < length \<phi>s"
    have mem: "\<phi>s ! i \<in> safe_atms r" using nth_mem[OF i] at by blast
    have bi: "\<forall>x \<in> Formula.fv (\<phi>s ! i). x < n" using b sub i by auto
    show "mok n (Formula.fv (\<phi>s ! i)) tw (minit0 n (\<phi>s ! i))"
      using MatchP.IH mem bi by blast
  qed
  have m: "minit0 n (Formula.MatchP I r) = mformula.MMatchP I mr
      (sorted_list_of_set (RPDs mr)) (map (minit0 n) \<phi>s) (replicate (length \<phi>s) []) [] []"
    using tm by simp
  have A: "Formula.fv (Formula.MatchP I r) = Formula.fv_regex r" by simp
  show ?case unfolding m A
    by (rule MokMatchP[OF sr[folded fm] ok])
      (simp_all add: fm finite_RPDs sub pL maux_inv_def)
next
  case (MatchF I r)
  note sr = \<open>Regex.safe_regex fv rgx_safe_pred Futu Strict r\<close>
  obtain mr \<phi>s where tm: "to_mregex r = (mr, \<phi>s)" by (cases "to_mregex r")
  have ok: "ok (length \<phi>s) mr" and at: "set \<phi>s = safe_atms r"
    using to_mregex_ok[OF tm] by auto
  have fm: "from_mregex mr \<phi>s = r" by (rule from_mregex_eq[OF sr tm])
  have fr: "Formula.fv_regex r = (\<Union>\<psi> \<in> set \<phi>s. Formula.fv \<psi>)"
    unfolding at by (rule fv_regex_alt2[OF sr])
  have sub: "\<forall>i < length \<phi>s. Formula.fv (\<phi>s ! i) \<subseteq> Formula.fv_regex r"
  proof (intro allI impI subsetI)
    fix i x assume i: "i < length \<phi>s" and x: "x \<in> Formula.fv (\<phi>s ! i)"
    show "x \<in> Formula.fv_regex r" unfolding fr using i x by auto
  qed
  have b: "\<forall>x \<in> Formula.fv_regex r. x < n" using MatchF.prems by simp
  have pL: "\<forall>i < length \<phi>s. mok n (Formula.fv (\<phi>s ! i)) tw (minit0 n (\<phi>s ! i))"
  proof (intro allI impI)
    fix i assume i: "i < length \<phi>s"
    have mem: "\<phi>s ! i \<in> safe_atms r" using nth_mem[OF i] at by blast
    have bi: "\<forall>x \<in> Formula.fv (\<phi>s ! i). x < n" using b sub i by auto
    show "mok n (Formula.fv (\<phi>s ! i)) tw (minit0 n (\<phi>s ! i))"
      using MatchF.IH mem bi by blast
  qed
  have m: "minit0 n (Formula.MatchF I r) = mformula.MMatchF I mr
      (sorted_list_of_set (LPDs mr)) (map (minit0 n) \<phi>s) (replicate (length \<phi>s) []) [] 0 []"
    using tm by simp
  have A: "Formula.fv (Formula.MatchF I r) = Formula.fv_regex r" by simp
  show ?case unfolding m A
    by (rule MokMatchF[OF sr[folded fm] ok])
      (simp_all add: fm finite_LPDs sub pL mfaux_inv_def)
next
  case (TP t)
  then show ?case by (cases t) (auto intro!: MokTP)
next
  case (TS t)
  then show ?case by (cases t) (auto intro!: MokTS)
qed

section \<open>The kernel's initial state, read off\<close>

text \<open>
  @{text mok_minit0} discharges the criterion for the state the kernel itself starts from; what
  remains for the theory that follows is to read that state's two fields off @{const minit_safe}.
\<close>

lemma minit_safe_state:
  assumes "mmonitorable \<phi>"
  shows "mstate_n (minit_safe \<phi>) = Formula.nfv \<phi>"
    and "mstate_m (minit_safe \<phi>) = minit0 (Formula.nfv \<phi>) \<phi>"
  using assms[unfolded monitorable_formula_code]
  by (simp_all add: default_maux.minit_safe_def default_maux.minit_def Let_def)

(*<*)
end
(*>*)
