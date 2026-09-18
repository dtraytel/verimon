(*<*)
theory Dense_Descend
  imports Dense_Init
begin
(*>*)

section \<open>The descending compiler\<close>

text \<open>
  The state built in the preceding theory relates to the kernel's through one \<open>DPure\<close>
  node at the root: honest, but it runs the kernel's evaluator and narrows its output, so nothing
  of the dense representation is used.  This theory replaces it by a compiler that descends into
  the formula and emits a dense node wherever the simulation has a rule for one, falling back to
  \<open>DPure\<close> only at the constructors the dense fragment does not cover.

  The compiler is a plain function of the kernel's formula and the column list its result is to
  have.  It needs no separate pass computing a node's columns: at every recursive call the column
  list of the operand is read off the node itself -- the two variable sets a conjunction stores,
  the argument record a temporal node stores, the operand columns an aggregation stores -- or, for
  the existential, is reconstructed from the node's own columns, because a safe existential binds
  a variable that does occur, so the operand's columns are the node's shifted up with a zero in
  front.
\<close>

subsection \<open>The compiler\<close>

definition dagg_gcols :: "aggargs \<Rightarrow> cols" where
  "dagg_gcols args = map (\<lambda>c. c - length (aggargs_tys args))
     (drop (length (aggargs_tys args)) (set_cols (aggargs_cols args)))"

fun dof :: "nat \<Rightarrow> cols \<Rightarrow> (mmasaux, muaux_dq, event_data mmtaux) mformula \<Rightarrow> dformula"
and dof_list :: "nat \<Rightarrow> cols list \<Rightarrow>
    (mmasaux, muaux_dq, event_data mmtaux) mformula list \<Rightarrow> dformula list" where
  "dof_list n css [] = []"
| "dof_list n css (\<phi> # L) =
     dof n (case css of [] \<Rightarrow> [] | c # _ \<Rightarrow> c) \<phi> #
     dof_list n (case css of [] \<Rightarrow> [] | _ # r \<Rightarrow> r) L"
| "dof n cs (mformula.MRel rel) = DRel (dtabc n cs rel)"
| "dof n cs (mformula.MPred e tms mode) =
     (if mode = Match then DPredM e (length tms) tms cs
      else if (mode = Copy \<and> tms = map Formula.Var [0..<n] \<and> cs = [0..<n])
           \<or> (mode = Simple \<and> is_simple_pattern tms 0 \<and> cs = smp_cols tms)
      then DPredS e (length tms)
      else DPure (mformula.MPred e tms mode) n (wide_mask n cs))"
| "dof n cs (mformula.MAndRel \<phi> conf) =
     (if Formula.fv_trm (fst conf) \<subseteq> set cs \<and> Formula.fv_trm (snd (snd (snd conf))) \<subseteq> set cs
      then DAndRel (dof n cs \<phi>) (reindex_constraint cs conf)
      else DPure (mformula.MAndRel \<phi> conf) n (wide_mask n cs))"
| "dof n cs (mformula.MNeg \<phi>) =
     (if cs = [] then DNeg (dof n [] \<phi>)
      else DPure (mformula.MNeg \<phi>) n (wide_mask n cs))"
| "dof n cs (mformula.MExists \<phi>) = DExists (dof (Suc n) (0 # map Suc cs) \<phi>) True"
| "dof n cs (mformula.MOr \<phi> \<psi> buf) =
     DOr (dof n cs \<phi>) (dof n cs \<psi>)
       (map (dtabc n cs) (fst buf), map (dtabc n cs) (snd buf))"
| "dof n cs (mformula.MAnd A \<phi> pos B \<psi> buf) =
     (let cs1 = set_cols A; cs2 = set_cols B in
      if cs = merge_cols cs1 cs2 \<and> (pos \<or> B \<subseteq> A)
      then DAnd (mk_djoin cs1 cs2) (dof n cs1 \<phi>) pos (dof n cs2 \<psi>)
             (map (dtabc n cs1) (fst buf), map (dtabc n cs2) (snd buf))
      else DPure (mformula.MAnd A \<phi> pos B \<psi> buf) n (wide_mask n cs))"
| "dof n cs (mformula.MPrev I \<phi> first buf nts) =
     DPrev I (dof n cs \<phi>) first (map (dtabc n cs) buf) nts"
| "dof n cs (mformula.MNext I \<phi> first nts) = DNext I (dof n cs \<phi>) first nts"
| "dof n cs (mformula.MAnds A_pos A_neg L buf) =
     (case A_pos of [] \<Rightarrow> DPure (mformula.MAnds A_pos A_neg L buf) n (wide_mask n cs)
      | A # As \<Rightarrow>
        (let c0 = set_cols A; css = map set_cols As; nss = map set_cols A_neg in
         if cs = dands_cols c0 css \<and> length L = length A_pos + length A_neg
         then DAnds (dands_plans c0 css) (dands_plans (dands_cols c0 css) nss)
                (dof_list n (c0 # css @ nss) L)
                (map2 map (map (dtabc n) (c0 # css @ nss)) buf)
         else DPure (mformula.MAnds A_pos A_neg L buf) n (wide_mask n cs)))"
| "dof n cs (mformula.MAgg args \<phi>) =
     (let m = length (aggargs_tys args); g = dagg_gcols args; y = aggargs_y args in
      if cs = merge_cols g [y] \<and> set_cols (aggargs_cols args) = agg_cols m g
      then DAgg (aggargs_g0 args) (aggargs_\<omega> args)
             (reindex_trm (agg_cols m g) (aggargs_f args)) m (ins_pos g y)
             (dof (m + n) (agg_cols m g) \<phi>)
      else DPure (mformula.MAgg args \<phi>) n (wide_mask n cs))"
| "dof n cs (mformula.MSince args \<phi> \<psi> buf aux) =
     (let cs_L = set_cols (args_L args) in
      if args_agg args = None \<and> args_n args = n \<and> args_R args = set cs \<and>
         set cs_L \<subseteq> set cs \<and> buf = init_mbuf2S
      then DSince (dargs cs cs_L args) (emb_plan cs cs_L)
             (dof n cs_L \<phi>) (dof n cs \<psi>) init_mbuf2S
             (init_mmasaux (dargs cs cs_L args))
      else DPure (mformula.MSince args \<phi> \<psi> buf aux) n (wide_mask n cs))"
| "dof n cs (mformula.MUntil args \<phi> \<psi> buf nts t aux) =
     (let cs_L = set_cols (args_L args) in
      if args_agg args = None \<and> args_n args = n \<and> args_R args = set cs \<and>
         set cs_L \<subseteq> set cs \<and> buf = ([], []) \<and> nts = [] \<and> t = 0
      then DUntil (dargs cs cs_L args) (emb_plan cs cs_L)
             (dof n cs_L \<phi>) (dof n cs \<psi>) ([], []) [] 0
             (init_muaux_dq (dargs cs cs_L args))
      else DPure (mformula.MUntil args \<phi> \<psi> buf nts t aux) n (wide_mask n cs))"
| "dof n cs \<phi> = DPure \<phi> n (wide_mask n cs)"

subsection \<open>Column lists from column sets\<close>

lemma set_set_cols[simp]: "finite A \<Longrightarrow> set (set_cols A) = A"
  by (rule set_cols(2))

lemma sorted_set_cols[simp]: "finite A \<Longrightarrow> sorted_wrt (<) (set_cols A)"
  by (rule set_cols(1))

lemma set_cols_fv[simp]: "set (set_cols (Formula.fv \<phi>)) = Formula.fv \<phi>"
  by simp

lemma wf_cols_set_cols:
  assumes "finite A" and "\<forall>x \<in> A. x < n"
  shows "wf_cols n (set_cols A)"
  using assms by simp

lemma set_cols_eq:
  assumes "finite A" and "sorted_wrt (<) cs" and "set cs = A"
  shows "set_cols A = cs"
proof -
  have "sorted_wrt (<) (set_cols A)" and "set (set_cols A) = A" using assms by simp_all
  then show ?thesis using assms
    by (intro sorted_distinct_set_unique) (auto simp: strict_sorted_iff)
qed

lemma set_cols_merge:
  assumes "finite A" and "finite B"
  shows "set_cols (A \<union> B) = merge_cols (set_cols A) (set_cols B)"
  by (rule set_cols_eq)
    (use assms in \<open>auto simp: sorted_merge_cols set_merge_cols\<close>)

subsection \<open>The escape hatch, as a step of the compiler\<close>

lemma dsim_dof_pure:
  assumes w: "wf_cols n cs" and p: "produces n (set cs) tw \<phi>"
    and d: "dof n cs \<phi> = DPure \<phi> n (wide_mask n cs)"
  shows "dsim n cs tw (dof n cs \<phi>) \<phi>"
  unfolding d by (rule dsim.DsPure[OF w p])

lemma produces_minit0:
  assumes "safe_formula \<phi>" and "\<forall>x \<in> Formula.fv \<phi>. x < n"
  shows "produces n (Formula.fv \<phi>) tw (minit0 n \<phi>)"
  by (rule mok_produces[OF mok_minit0[OF assms]])

lemma dsim_dof_minit0_pure:
  assumes s: "safe_formula \<phi>" and b: "\<forall>x \<in> Formula.fv \<phi>. x < n"
    and d: "dof n (set_cols (Formula.fv \<phi>)) (minit0 n \<phi>)
        = DPure (minit0 n \<phi>) n (wide_mask n (set_cols (Formula.fv \<phi>)))"
  shows "dsim n (set_cols (Formula.fv \<phi>)) tw
     (dof n (set_cols (Formula.fv \<phi>)) (minit0 n \<phi>)) (minit0 n \<phi>)"
  by (rule dsim_dof_pure[OF wf_cols_set_cols[OF finite_fvi b] _ d])
    (use produces_minit0[OF s b] in simp)

subsection \<open>One lemma per constructor\<close>

text \<open>
  The induction that follows has thirty-two cases, so each is proved on its own first, with the
  induction hypotheses as assumptions.  A case whose constructor the dense fragment does not
  cover needs no lemma: it is @{thm [source] dsim_dof_minit0_pure} with the equation that the
  compiler falls back at that node.
\<close>

abbreviation (input) dofc :: "nat \<Rightarrow> ts \<Rightarrow> ty Formula.formula \<Rightarrow> bool" where
  "dofc n tw \<phi> \<equiv> dsim n (set_cols (Formula.fv \<phi>)) tw
     (dof n (set_cols (Formula.fv \<phi>)) (minit0 n \<phi>)) (minit0 n \<phi>)"

lemma dsim_dof_minit0_rel:
  assumes s: "safe_formula \<phi>" and b: "\<forall>x \<in> Formula.fv \<phi>. x < n"
    and m: "minit0 n \<phi> = mformula.MRel rel" and t: "table n (Formula.fv \<phi>) rel"
  shows "dofc n tw \<phi>"
proof -
  let ?cs = "set_cols (Formula.fv \<phi>)"
  have w: "wf_cols n ?cs" by (rule wf_cols_set_cols[OF finite_fvi b])
  have sc: "set ?cs = Formula.fv \<phi>" by simp
  have p: "produces n (set ?cs) tw (mformula.MRel rel)"
    using produces_minit0[OF s b] unfolding m sc .
  have d: "dof n ?cs (mformula.MRel rel) = DRel (dtabc n ?cs rel)" by simp
  show ?thesis unfolding m d by (rule dsim.DsRel[OF w p]) (use t sc in simp)
qed

lemma set_cols_empty[simp]: "set_cols {} = []"
  by (rule set_cols_eq) auto

lemma set_cols_set[simp]: "wf_cols n cs \<Longrightarrow> set_cols (set cs) = cs"
  by (rule set_cols_eq) auto

lemma ex_cols_Suc[simp]: "ex_cols (0 # map Suc cs) = cs"
  by (simp add: ex_cols_def ex_drop0_def o_def)

lemma ex_drop0_Suc[simp]: "ex_drop0 (0 # map Suc cs)"
  by (simp add: ex_drop0_def)

lemma set_cols_fvi_Suc:
  assumes z: "0 \<in> Formula.fv \<phi>"
  shows "set_cols (Formula.fv \<phi>) = 0 # map Suc (set_cols (Formula.fvi (Suc 0) \<phi>))"
proof (rule set_cols_eq)
  show "finite (Formula.fv \<phi>)" by simp
  show "sorted_wrt (<) (0 # map Suc (set_cols (Formula.fvi (Suc 0) \<phi>)))"
    by (auto simp: sorted_wrt_map)
  have "set (map Suc (set_cols (Formula.fvi (Suc 0) \<phi>))) = Suc ` Formula.fvi (Suc 0) \<phi>"
    by simp
  also have "\<dots> = Formula.fv \<phi> - {0}"
  proof (intro set_eqI iffI)
    fix x assume "x \<in> Suc ` Formula.fvi (Suc 0) \<phi>"
    then obtain y where y: "y \<in> Formula.fvi (Suc 0) \<phi>" and x: "x = Suc y" by auto
    have "y + Suc 0 \<in> Formula.fv \<phi>" using y by (rule fvi_iff_fv[THEN iffD1])
    then show "x \<in> Formula.fv \<phi> - {0}" using x by simp
  next
    fix x assume x: "x \<in> Formula.fv \<phi> - {0}"
    then obtain y where y: "x = Suc y" by (cases x) auto
    have "y + Suc 0 \<in> Formula.fv \<phi>" using x y by simp
    then have "y \<in> Formula.fvi (Suc 0) \<phi>" by (rule fvi_iff_fv[THEN iffD2])
    then show "x \<in> Suc ` Formula.fvi (Suc 0) \<phi>" using y by auto
  qed
  finally show "set (0 # map Suc (set_cols (Formula.fvi (Suc 0) \<phi>))) = Formula.fv \<phi>"
    using z by auto
qed

lemma dsim_dof_minit0_Pred:
  assumes sf: "safe_formula \<phi>" and b: "\<forall>x \<in> Formula.fv \<phi>. x < n"
    and e: "\<phi> = Formula.Pred pn ts"
  shows "dofc n tw \<phi>"
proof -
  let ?cs = "set_cols (Formula.fv \<phi>)"
  have w: "wf_cols n ?cs" by (rule wf_cols_set_cols[OF finite_fvi b])
  have pr: "produces n (set ?cs) tw (minit0 n \<phi>)" using produces_minit0[OF sf b] by simp
  have m: "minit0 n \<phi> = mformula.MPred pn ts (pred_mode_of n ts)" unfolding e by simp
  show ?thesis
  proof (cases "pred_mode_of n ts")
    case Copy
    then have c: "ts = map Formula.Var [0..<n]" by (simp add: is_copy_pattern_def)
    have A: "Formula.fv \<phi> = {0..<n}" unfolding e using c by (auto simp: image_iff)
    have cs: "?cs = [0..<n]" unfolding A by (rule set_cols_eq) auto
    have d: "dof n ?cs (mformula.MPred pn ts Copy) = DPredS pn n" using c cs by simp
    have pr': "produces n (set ?cs) tw (mformula.MPred pn ts Copy)"
      using pr unfolding m Copy .
    show ?thesis unfolding m Copy d by (rule dsim.DsPredC[OF w pr' c cs])
  next
    case Simple
    then have sp: "is_simple_pattern ts 0" by simp
    show ?thesis
    proof (cases "?cs = smp_cols ts")
      case True
      have d: "dof n ?cs (mformula.MPred pn ts Simple) = DPredS pn (length ts)"
        using sp True by simp
      have pr': "produces n (set ?cs) tw (mformula.MPred pn ts Simple)"
        using pr unfolding m Simple .
      show ?thesis unfolding m Simple d by (rule dsim.DsPredS[OF w pr' sp True])
    next
      case False
      have d: "dof n ?cs (minit0 n \<phi>) = DPure (minit0 n \<phi>) n (wide_mask n ?cs)"
        unfolding m Simple using False by simp
      show ?thesis by (rule dsim_dof_pure[OF w pr d])
    qed
  next
    case Match
    have d: "dof n ?cs (mformula.MPred pn ts Match) = DPredM pn (length ts) ts ?cs" by simp
    have pr': "produces n (set ?cs) tw (mformula.MPred pn ts Match)"
      using pr unfolding m Match .
    show ?thesis unfolding m Match d by (rule dsim.DsPredM[OF w pr'])
  qed
qed

lemma dsim_dof_minit0_Or:
  assumes sf: "safe_formula \<phi>" and b: "\<forall>x \<in> Formula.fv \<phi>. x < n"
    and m: "minit0 n \<phi> = mformula.MOr (minit0 n \<chi>) (minit0 n \<psi>) ([], [])"
    and A: "Formula.fv \<phi> = Formula.fv \<chi>" and A': "Formula.fv \<phi> = Formula.fv \<psi>"
    and i1: "dofc n tw \<chi>" and i2: "dofc n tw \<psi>"
  shows "dofc n tw \<phi>"
proof -
  let ?cs = "set_cols (Formula.fv \<phi>)"
  have w: "wf_cols n ?cs" by (rule wf_cols_set_cols[OF finite_fvi b])
  have pr: "produces n (set ?cs) tw (mformula.MOr (minit0 n \<chi>) (minit0 n \<psi>) ([], []))"
    using produces_minit0[OF sf b] unfolding m by simp
  have d: "dof n ?cs (mformula.MOr (minit0 n \<chi>) (minit0 n \<psi>) ([], []))
      = DOr (dof n ?cs (minit0 n \<chi>)) (dof n ?cs (minit0 n \<psi>)) ([], [])" by simp
  have s1: "dsim n ?cs tw (dof n ?cs (minit0 n \<chi>)) (minit0 n \<chi>)"
    using i1 unfolding A[symmetric] .
  have s2: "dsim n ?cs tw (dof n ?cs (minit0 n \<psi>)) (minit0 n \<psi>)"
    using i2 unfolding A'[symmetric] .
  have bf: "dbuf2 n ?cs ?cs ([], []) ([], [])" by (simp add: dbuf2_def)
  show ?thesis unfolding m d by (rule dsim.DsOr[OF w pr s1 s2 bf])
qed

lemma dsim_dof_minit0_Neg:
  assumes sf: "safe_formula \<phi>" and b: "\<forall>x \<in> Formula.fv \<phi>. x < n"
    and m: "minit0 n \<phi> = mformula.MNeg (minit0 n \<chi>)"
    and A: "Formula.fv \<phi> = {}" and A': "Formula.fv \<chi> = {}"
    and i1: "dofc n tw \<chi>"
  shows "dofc n tw \<phi>"
proof -
  have cs: "set_cols (Formula.fv \<phi>) = []" unfolding A by simp
  have pr: "produces n {} tw (mformula.MNeg (minit0 n \<chi>))"
    using produces_minit0[OF sf b] unfolding m A .
  have d: "dof n [] (mformula.MNeg (minit0 n \<chi>)) = DNeg (dof n [] (minit0 n \<chi>))" by simp
  have s1: "dsim n [] tw (dof n [] (minit0 n \<chi>)) (minit0 n \<chi>)"
    using i1 unfolding A' by simp
  show ?thesis unfolding cs m d by (rule dsim.DsNeg[OF pr s1])
qed

lemma dsim_dof_minit0_Prev:
  assumes sf: "safe_formula \<phi>" and b: "\<forall>x \<in> Formula.fv \<phi>. x < n"
    and m: "minit0 n \<phi> = mformula.MPrev I (minit0 n \<chi>) True [] []"
    and A: "Formula.fv \<phi> = Formula.fv \<chi>" and i1: "dofc n tw \<chi>"
  shows "dofc n tw \<phi>"
proof -
  let ?cs = "set_cols (Formula.fv \<phi>)"
  have w: "wf_cols n ?cs" by (rule wf_cols_set_cols[OF finite_fvi b])
  have pr: "produces n (set ?cs) tw (mformula.MPrev I (minit0 n \<chi>) True [] [])"
    using produces_minit0[OF sf b] unfolding m by simp
  have d: "dof n ?cs (mformula.MPrev I (minit0 n \<chi>) True [] [])
      = DPrev I (dof n ?cs (minit0 n \<chi>)) True [] []" by simp
  have s1: "dsim n ?cs tw (dof n ?cs (minit0 n \<chi>)) (minit0 n \<chi>)"
    using i1 unfolding A[symmetric] .
  show ?thesis unfolding m d by (rule dsim.DsPrev[OF w pr s1]) simp_all
qed

lemma dsim_dof_minit0_Next:
  assumes sf: "safe_formula \<phi>" and b: "\<forall>x \<in> Formula.fv \<phi>. x < n"
    and m: "minit0 n \<phi> = mformula.MNext I (minit0 n \<chi>) True []"
    and A: "Formula.fv \<phi> = Formula.fv \<chi>" and i1: "dofc n tw \<chi>"
  shows "dofc n tw \<phi>"
proof -
  let ?cs = "set_cols (Formula.fv \<phi>)"
  have w: "wf_cols n ?cs" by (rule wf_cols_set_cols[OF finite_fvi b])
  have pr: "produces n (set ?cs) tw (mformula.MNext I (minit0 n \<chi>) True [])"
    using produces_minit0[OF sf b] unfolding m by simp
  have d: "dof n ?cs (mformula.MNext I (minit0 n \<chi>) True [])
      = DNext I (dof n ?cs (minit0 n \<chi>)) True []" by simp
  have s1: "dsim n ?cs tw (dof n ?cs (minit0 n \<chi>)) (minit0 n \<chi>)"
    using i1 unfolding A[symmetric] .
  show ?thesis unfolding m d by (rule dsim.DsNext[OF w pr s1])
qed

lemma dsim_dof_minit0_Exists:
  assumes sf: "safe_formula \<phi>" and b: "\<forall>x \<in> Formula.fv \<phi>. x < n"
    and m: "minit0 n \<phi> = mformula.MExists (minit0 (Suc n) \<chi>)"
    and A: "Formula.fv \<phi> = Formula.fvi (Suc 0) \<chi>" and z: "0 \<in> Formula.fv \<chi>"
    and i1: "dofc (Suc n) tw \<chi>"
  shows "dofc n tw \<phi>"
proof -
  let ?cs = "set_cols (Formula.fv \<phi>)"
  let ?ccs = "set_cols (Formula.fv \<chi>)"
  have w: "wf_cols n ?cs" by (rule wf_cols_set_cols[OF finite_fvi b])
  have pr: "produces n (set ?cs) tw (mformula.MExists (minit0 (Suc n) \<chi>))"
    using produces_minit0[OF sf b] unfolding m by simp
  have cc: "?ccs = 0 # map Suc ?cs" unfolding A by (rule set_cols_fvi_Suc[OF z])
  have d: "dof n ?cs (mformula.MExists (minit0 (Suc n) \<chi>))
      = DExists (dof (Suc n) ?ccs (minit0 (Suc n) \<chi>)) True" unfolding cc by simp
  show ?thesis unfolding m d
    by (rule dsim.DsExists[OF w pr i1]) (simp_all add: cc)
qed

lemma dsim_dof_minit0_MAnd:
  assumes sf: "safe_formula \<phi>" and b: "\<forall>x \<in> Formula.fv \<phi>. x < n"
    and m: "minit0 n \<phi>
        = mformula.MAnd (set c1) (minit0 n \<chi>) pos (set c2) (minit0 n \<psi>) ([], [])"
    and c1: "c1 = set_cols (Formula.fv \<chi>)" and c2: "c2 = set_cols (Formula.fv \<psi>)"
    and A: "Formula.fv \<phi> = Formula.fv \<chi> \<union> Formula.fv \<psi>"
    and np: "\<not> pos \<Longrightarrow> Formula.fv \<psi> \<subseteq> Formula.fv \<chi>"
    and i1: "dofc n tw \<chi>" and i2: "dofc n tw \<psi>"
  shows "dofc n tw \<phi>"
proof -
  let ?cs = "set_cols (Formula.fv \<phi>)"
  have w: "wf_cols n ?cs" by (rule wf_cols_set_cols[OF finite_fvi b])
  have pr: "produces n (set ?cs) tw
      (mformula.MAnd (set c1) (minit0 n \<chi>) pos (set c2) (minit0 n \<psi>) ([], []))"
    using produces_minit0[OF sf b] unfolding m by simp
  have mc: "?cs = merge_cols c1 c2" unfolding A c1 c2 by (rule set_cols_merge) simp_all
  have sc1: "set c1 = Formula.fv \<chi>" unfolding c1 by simp
  have sc2: "set c2 = Formula.fv \<psi>" unfolding c2 by simp
  have sc1': "set_cols (set c1) = c1" unfolding c1 by simp
  have sc2': "set_cols (set c2) = c2" unfolding c2 by simp
  have g2: "\<not> pos \<Longrightarrow> set c2 \<subseteq> set c1" using np unfolding sc1 sc2 .
  have g: "pos \<or> set c2 \<subseteq> set c1" using g2 by (cases pos) auto
  have d: "dof n ?cs (mformula.MAnd (set c1) (minit0 n \<chi>) pos (set c2) (minit0 n \<psi>) ([], []))
      = DAnd (mk_djoin c1 c2) (dof n c1 (minit0 n \<chi>)) pos (dof n c2 (minit0 n \<psi>)) ([], [])"
    using g by (simp add: Let_def sc1' sc2' mc)
  have bf: "dbuf2 n c1 c2 ([], []) ([], [])" by (simp add: dbuf2_def)
  show ?thesis unfolding m d
    by (rule dsim.DsAnd[OF w pr i1[folded c1] i2[folded c2] mc refl g2 bf])
qed

lemma dsim_dof_minit0_MAndRel:
  assumes sf: "safe_formula \<phi>" and b: "\<forall>x \<in> Formula.fv \<phi>. x < n"
    and m: "minit0 n \<phi> = mformula.MAndRel (minit0 n \<chi>) (t1, pp, c, t2)"
    and A: "Formula.fv \<phi> = Formula.fv \<chi>" and i1: "dofc n tw \<chi>"
  shows "dofc n tw \<phi>"
proof -
  let ?cs = "set_cols (Formula.fv \<phi>)"
  have w: "wf_cols n ?cs" by (rule wf_cols_set_cols[OF finite_fvi b])
  have pr: "produces n (set ?cs) tw (mformula.MAndRel (minit0 n \<chi>) (t1, pp, c, t2))"
    using produces_minit0[OF sf b] unfolding m by simp
  have s1: "dsim n ?cs tw (dof n ?cs (minit0 n \<chi>)) (minit0 n \<chi>)"
    using i1 unfolding A[symmetric] .
  show ?thesis
  proof (cases "Formula.fv_trm t1 \<subseteq> set ?cs \<and> Formula.fv_trm t2 \<subseteq> set ?cs")
    case True
    have d: "dof n ?cs (mformula.MAndRel (minit0 n \<chi>) (t1, pp, c, t2))
        = DAndRel (dof n ?cs (minit0 n \<chi>)) (reindex_constraint ?cs (t1, pp, c, t2))"
      using True by simp
    show ?thesis unfolding m d
      by (rule dsim.DsAndRel[OF w pr s1]) (use True in simp_all)
  next
    case False
    have d: "dof n ?cs (minit0 n \<phi>) = DPure (minit0 n \<phi>) n (wide_mask n ?cs)"
      unfolding m using False by simp
    show ?thesis by (rule dsim_dof_pure[OF w pr[folded m] d])
  qed
qed

lemma strict_sorted_nth_ge:
  assumes s: "sorted_wrt (<) (L :: nat list)" and i: "i < length L"
  shows "i \<le> L ! i"
  using i
proof (induct i)
  case 0 show ?case by simp
next
  case (Suc i)
  then have ih: "i \<le> L ! i" by simp
  have "L ! i < L ! Suc i" using s Suc.prems by (auto simp: sorted_wrt_iff_nth_less)
  then show ?case using ih by simp
qed

lemma strict_sorted_upt_nth:
  assumes s: "sorted_wrt (<) (L :: nat list)" and sub: "{0..<m} \<subseteq> set L" and i: "i < m"
  shows "i < length L \<and> L ! i = i"
  using i
proof (induct i rule: less_induct)
  case (less i)
  have iL: "i \<in> set L" using sub less.prems by auto
  then obtain k where k: "k < length L" and Lk: "L ! k = i" by (auto simp: in_set_conv_nth)
  have ki: "k \<le> i" using strict_sorted_nth_ge[OF s k] Lk by simp
  have "\<not> k < i"
  proof
    assume ki': "k < i"
    then have "L ! k = k" using less.hyps[of k] less.prems by simp
    then show False using Lk ki' by simp
  qed
  then have "k = i" using ki by simp
  then show ?case using k Lk by simp
qed

lemma strict_sorted_take_upt:
  assumes s: "sorted_wrt (<) (L :: nat list)" and sub: "{0..<m} \<subseteq> set L"
  shows "take m L = [0..<m]"
proof -
  have lm: "m \<le> length L"
  proof (cases m)
    case 0 then show ?thesis by simp
  next
    case (Suc k)
    then have "k < length L" using strict_sorted_upt_nth[OF s sub, of k] by simp
    then show ?thesis using Suc by simp
  qed
  show ?thesis
  proof (rule nth_equalityI)
    show "length (take m L) = length [0..<m]" using lm by simp
  next
    fix i assume "i < length (take m L)"
    then have i: "i < m" using lm by simp
    then show "take m L ! i = [0..<m] ! i"
      using strict_sorted_upt_nth[OF s sub i] lm by simp
  qed
qed

lemma set_cols_agg_cols:
  assumes fin: "finite A" and sub: "{0..<m} \<subseteq> A"
  shows "set_cols A = agg_cols m (map (\<lambda>c. c - m) (drop m (set_cols A)))"
    and "set (map (\<lambda>c. c - m) (drop m (set_cols A))) = (\<lambda>c. c - m) ` (A - {0..<m})"
    and "sorted_wrt (<) (map (\<lambda>c. c - m) (drop m (set_cols A)))"
proof -
  let ?L = "set_cols A"
  have s: "sorted_wrt (<) ?L" and sa: "set ?L = A" using fin by simp_all
  have tk: "take m ?L = [0..<m]" by (rule strict_sorted_take_upt[OF s]) (use sub sa in simp)
  have ge: "\<forall>c \<in> set (drop m ?L). m \<le> c"
  proof
    fix c assume "c \<in> set (drop m ?L)"
    then obtain j where j: "j < length (drop m ?L)" and c: "drop m ?L ! j = c"
      by (auto simp: in_set_conv_nth)
    have "?L ! (m + j) = c" using j c by simp
    moreover have "m + j \<le> ?L ! (m + j)"
      by (rule strict_sorted_nth_ge[OF s]) (use j in simp)
    ultimately show "m \<le> c" by simp
  qed
  have mp: "map (\<lambda>c. c + m) (map (\<lambda>c. c - m) (drop m ?L)) = drop m ?L"
    using ge by (simp add: o_def map_idI)
  show "set_cols A = agg_cols m (map (\<lambda>c. c - m) (drop m ?L))"
    using tk mp by (metis append_take_drop_id)
  have dd: "set (drop m ?L) = A - {0..<m}"
  proof -
    have d: "distinct ?L" using s by (simp add: strict_sorted_iff)
    have "set ?L = set (take m ?L) \<union> set (drop m ?L)"
      by (metis append_take_drop_id set_append)
    moreover have "set (take m ?L) \<inter> set (drop m ?L) = {}"
      using d by (metis append_take_drop_id distinct_append)
    ultimately show ?thesis using sa tk by auto
  qed
  show "set (map (\<lambda>c. c - m) (drop m ?L)) = (\<lambda>c. c - m) ` (A - {0..<m})"
    using dd by simp
  show "sorted_wrt (<) (map (\<lambda>c. c - m) (drop m ?L))"
  proof -
    have sd: "sorted_wrt (<) (drop m ?L)" using s by (simp add: sorted_wrt_drop)
    show ?thesis unfolding sorted_wrt_map
      by (rule sorted_wrt_mono_rel[OF _ sd]) (use ge in auto)
  qed
qed

lemma dsince_rel_init:
  assumes a: "args = init_args I n L R pos None"
    and sub: "L \<subseteq> R" and cL: "set cs_L = L" and cR: "set cs_R = R"
  shows "dsince_rel n cs_R cs_L args tw (init_mmasaux args)
     (init_mmasaux (dargs cs_R cs_L args)) init_mbuf2S init_mbuf2S"
proof -
  have v: "valid_mmasaux args 0 (init_mmasaux args) []"
    unfolding a by (rule valid_init_mmasaux[OF sub])
  have s: "dsaux n cs_R cs_L args 0 (init_mmasaux (dargs cs_R cs_L args)) []"
    by (rule dsaux_init) (use sub cL cR in simp)
  have "dsince_rel n cs_R cs_L args tw (init_mmasaux args)
      (init_mmasaux (dargs cs_R cs_L args)) ([], [], [], False)
      (map (dtabc n cs_R) [], map (dtabc n cs_R) [], [], False)"
    by (rule dsince_relI[OF v s]) simp_all
  then show ?thesis by simp
qed

lemma duntil_rel_init:
  assumes a: "args = init_args I n L R pos None"
    and sub: "L \<subseteq> R" and cL: "set cs_L = L" and cR: "set cs_R = R"
  shows "duntil_rel n cs_R cs_L args tw 0 (init_muaux_dq args)
     (init_muaux_dq (dargs cs_R cs_L args)) ([], []) ([], []) []"
proof -
  have v: "valid_muaux_dq args 0 (init_muaux_dq args) []"
    unfolding a by (rule valid_init_muaux_dq[OF sub])
  have s: "duaux n cs_R cs_L args 0 (init_muaux_dq (dargs cs_R cs_L args)) []"
    by (rule duaux_init) (use sub cL cR in simp)
  have r: "duaux_rel n cs_R cs_L args 0 (init_muaux_dq args)
      (init_muaux_dq (dargs cs_R cs_L args))"
    unfolding duaux_rel_def using v s by blast
  show ?thesis unfolding duntil_rel_def using r by auto
qed

lemma dsim_dof_minit0_MSince:
  assumes sf: "safe_formula \<phi>" and b: "\<forall>x \<in> Formula.fv \<phi>. x < n"
    and m: "minit0 n \<phi>
        = mformula.MSince args (minit0 n \<chi>) (minit0 n \<psi>) init_mbuf2S (init_mmasaux args)"
    and a: "args = init_args I n (Formula.fv \<chi>) (Formula.fv \<psi>) pos None"
    and A: "Formula.fv \<phi> = Formula.fv \<psi>" and sub: "Formula.fv \<chi> \<subseteq> Formula.fv \<psi>"
    and i1: "dofc n tw \<chi>" and i2: "dofc n tw \<psi>"
  shows "dofc n tw \<phi>"
proof -
  let ?cs = "set_cols (Formula.fv \<phi>)"
  let ?cL = "set_cols (Formula.fv \<chi>)"
  have w: "wf_cols n ?cs" by (rule wf_cols_set_cols[OF finite_fvi b])
  have bL: "\<forall>x \<in> Formula.fv \<chi>. x < n" using b sub unfolding A by auto
  have wL: "wf_cols n ?cL" by (rule wf_cols_set_cols[OF finite_fvi bL])
  have pr: "produces n (set ?cs) tw
      (mformula.MSince args (minit0 n \<chi>) (minit0 n \<psi>) init_mbuf2S (init_mmasaux args))"
    using produces_minit0[OF sf b] unfolding m by simp
  have aL: "args_L args = set ?cL" unfolding a by (simp add: init_args_def)
  have aR: "args_R args = set ?cs" unfolding a A by (simp add: init_args_def)
  have an: "args_n args = n" unfolding a by (simp add: init_args_def)
  have ag: "args_agg args = None" unfolding a by (simp add: init_args_def)
  have sb: "set ?cL \<subseteq> set ?cs" using sub unfolding A by simp
  have cLa: "set_cols (args_L args) = ?cL" unfolding aL using wL by simp
  have d: "dof n ?cs
        (mformula.MSince args (minit0 n \<chi>) (minit0 n \<psi>) init_mbuf2S (init_mmasaux args))
      = DSince (dargs ?cs ?cL args) (emb_plan ?cs ?cL)
          (dof n ?cL (minit0 n \<chi>)) (dof n ?cs (minit0 n \<psi>)) init_mbuf2S
          (init_mmasaux (dargs ?cs ?cL args))"
    using ag an aR sb by (simp add: Let_def cLa)
  have rl: "dsince_rel n ?cs ?cL args tw (init_mmasaux args)
      (init_mmasaux (dargs ?cs ?cL args)) init_mbuf2S init_mbuf2S"
    by (rule dsince_rel_init[OF a]) (use sub A in auto)
  have s2: "dsim n ?cs tw (dof n ?cs (minit0 n \<psi>)) (minit0 n \<psi>)"
    using i2 unfolding A[symmetric] .
  show ?thesis unfolding m d
    by (rule dsim.DsSince[OF w pr i1 s2 wL sb ag an aL aR refl refl rl])
qed

lemma dsim_dof_minit0_MUntil:
  assumes sf: "safe_formula \<phi>" and b: "\<forall>x \<in> Formula.fv \<phi>. x < n"
    and m: "minit0 n \<phi>
        = mformula.MUntil args (minit0 n \<chi>) (minit0 n \<psi>) ([], []) [] 0 (init_muaux_dq args)"
    and a: "args = init_args I n (Formula.fv \<chi>) (Formula.fv \<psi>) pos None"
    and A: "Formula.fv \<phi> = Formula.fv \<psi>" and sub: "Formula.fv \<chi> \<subseteq> Formula.fv \<psi>"
    and i1: "dofc n tw \<chi>" and i2: "dofc n tw \<psi>"
  shows "dofc n tw \<phi>"
proof -
  let ?cs = "set_cols (Formula.fv \<phi>)"
  let ?cL = "set_cols (Formula.fv \<chi>)"
  have w: "wf_cols n ?cs" by (rule wf_cols_set_cols[OF finite_fvi b])
  have bL: "\<forall>x \<in> Formula.fv \<chi>. x < n" using b sub unfolding A by auto
  have wL: "wf_cols n ?cL" by (rule wf_cols_set_cols[OF finite_fvi bL])
  have pr: "produces n (set ?cs) tw
      (mformula.MUntil args (minit0 n \<chi>) (minit0 n \<psi>) ([], []) [] 0 (init_muaux_dq args))"
    using produces_minit0[OF sf b] unfolding m by simp
  have aL: "args_L args = set ?cL" unfolding a by (simp add: init_args_def)
  have aR: "args_R args = set ?cs" unfolding a A by (simp add: init_args_def)
  have an: "args_n args = n" unfolding a by (simp add: init_args_def)
  have ag: "args_agg args = None" unfolding a by (simp add: init_args_def)
  have sb: "set ?cL \<subseteq> set ?cs" using sub unfolding A by simp
  have cLa: "set_cols (args_L args) = ?cL" unfolding aL using wL by simp
  have d: "dof n ?cs
        (mformula.MUntil args (minit0 n \<chi>) (minit0 n \<psi>) ([], []) [] 0 (init_muaux_dq args))
      = DUntil (dargs ?cs ?cL args) (emb_plan ?cs ?cL)
          (dof n ?cL (minit0 n \<chi>)) (dof n ?cs (minit0 n \<psi>)) ([], []) [] 0
          (init_muaux_dq (dargs ?cs ?cL args))"
    using ag an aR sb by (simp add: Let_def cLa)
  have rl: "duntil_rel n ?cs ?cL args tw 0 (init_muaux_dq args)
      (init_muaux_dq (dargs ?cs ?cL args)) ([], []) ([], []) []"
    by (rule duntil_rel_init[OF a]) (use sub A in auto)
  have s2: "dsim n ?cs tw (dof n ?cs (minit0 n \<psi>)) (minit0 n \<psi>)"
    using i2 unfolding A[symmetric] .
  show ?thesis unfolding m d
    by (rule dsim.DsUntil[OF w pr i1 s2 wL sb ag an aL aR refl refl rl])
qed

lemma dsim_dof_minit0_MAgg:
  assumes sf: "safe_formula \<phi>" and b: "\<forall>x \<in> Formula.fv \<phi>. x < n"
    and m: "minit0 n \<phi> = mformula.MAgg args (minit0 (length tys + n) \<chi>)"
    and a: "args = init_aggargs (Formula.fv \<chi>) n (Formula.fv \<chi> \<subseteq> {0..<length tys}) y \<omega> tys f"
    and ynot: "y + length tys \<notin> Formula.fv \<chi>"
    and tsub: "{0..<length tys} \<subseteq> Formula.fv \<chi>"
    and fsub: "Formula.fv_trm f \<subseteq> Formula.fv \<chi>"
    and A: "Formula.fv \<phi>
        = Set.insert y ((\<lambda>i. i - length tys) ` (Formula.fv \<chi> - {0..<length tys}))"
    and bc: "\<forall>x \<in> Formula.fv \<chi>. x < length tys + n"
    and i1: "dofc (length tys + n) tw \<chi>"
  shows "dofc n tw \<phi>"
proof -
  let ?k = "length (aggargs_tys args)"
  let ?cs = "set_cols (Formula.fv \<phi>)"
  let ?g = "map (\<lambda>c. c - ?k) (drop ?k (set_cols (Formula.fv \<chi>)))"
  have ac: "aggargs_cols args = Formula.fv \<chi>" and an: "aggargs_n args = n"
    and ay: "aggargs_y args = y" and aty: "aggargs_tys args = tys"
    and ag0: "aggargs_g0 args = (Formula.fv \<chi> \<subseteq> {0..<length tys})" and af: "aggargs_f args = f"
    unfolding a by (simp_all add: init_aggargs_def)
  have kt: "?k = length tys" unfolding aty ..
  have w: "wf_cols n ?cs" by (rule wf_cols_set_cols[OF finite_fvi b])
  have m': "minit0 n \<phi> = mformula.MAgg args (minit0 (?k + n) \<chi>)" unfolding kt by (rule m)
  have pr: "produces n (set ?cs) tw (mformula.MAgg args (minit0 (?k + n) \<chi>))"
    using produces_minit0[OF sf b] unfolding m' by simp
  have tsub': "{0..<?k} \<subseteq> Formula.fv \<chi>" unfolding kt by (rule tsub)
  note sc = set_cols_agg_cols[OF finite_fvi tsub']
  have cc: "set_cols (Formula.fv \<chi>) = agg_cols ?k ?g" by (rule sc(1))
  have gs: "set ?g = (\<lambda>c. c - ?k) ` (Formula.fv \<chi> - {0..<?k})" by (rule sc(2))
  have gsort: "sorted_wrt (<) ?g" by (rule sc(3))
  have gb: "\<forall>c \<in> set ?g. c < n" using gs bc unfolding kt by auto
  have wg: "wf_cols n ?g" using gsort gb by simp
  have ynotg: "y \<notin> set ?g"
  proof
    assume "y \<in> set ?g"
    then obtain c where c: "c \<in> Formula.fv \<chi> - {0..<?k}" and yc: "y = c - ?k" using gs by auto
    then have "c = y + ?k" by auto
    then show False using c ynot unfolding kt by auto
  qed
  have dg: "dagg_gcols args = ?g" unfolding dagg_gcols_def ac ..
  have A': "Formula.fv \<phi> = Set.insert y (set ?g)" unfolding A kt[symmetric] gs[symmetric] ..
  have cse: "?cs = merge_cols ?g [y]" unfolding A'
    by (rule set_cols_eq) (use gsort ynotg in \<open>auto simp: sorted_merge_cols set_merge_cols\<close>)
  have g0: "aggargs_g0 args \<Longrightarrow> ?g = []"
  proof -
    assume "aggargs_g0 args"
    then have "Formula.fv \<chi> \<subseteq> {0..<?k}" using ag0 unfolding kt by simp
    then have "set ?g = {}" using gs by auto
    then show "?g = []" by simp
  qed
  have fs: "Formula.fv_trm (aggargs_f args) \<subseteq> set (agg_cols ?k ?g)"
    unfolding af cc[symmetric] using fsub by simp
  have yn: "y < n" using A b by auto
  have gd2: "set_cols (aggargs_cols args) = agg_cols ?k ?g" unfolding ac by (rule cc)
  have d: "dof n ?cs (mformula.MAgg args (minit0 (?k + n) \<chi>))
      = DAgg (aggargs_g0 args) (aggargs_\<omega> args) (reindex_trm (agg_cols ?k ?g) (aggargs_f args))
          ?k (ins_pos ?g y) (dof (?k + n) (agg_cols ?k ?g) (minit0 (?k + n) \<chi>))"
    using cse gd2 by (simp add: Let_def dg ay)
  have s1: "dsim (?k + n) (agg_cols ?k ?g) tw
      (dof (?k + n) (agg_cols ?k ?g) (minit0 (?k + n) \<chi>)) (minit0 (?k + n) \<chi>)"
    using i1 unfolding kt[symmetric] cc[symmetric] .
  show ?thesis unfolding m' d
    by (rule dsim.DsAgg[OF w pr s1 wg an ay yn ynotg g0 fs cse])
qed

lemma length_dof_list[simp]: "length (dof_list n css L) = length L"
  by (induct L arbitrary: css) auto

lemma dof_list_nth:
  "i < length L \<Longrightarrow> i < length css \<Longrightarrow> dof_list n css L ! i = dof n (css ! i) (L ! i)"
proof (induct L arbitrary: css i)
  case Nil then show ?case by simp
next
  case (Cons a L)
  then obtain c cs' where css: "css = c # cs'" by (cases css) auto
  show ?case
  proof (cases i)
    case 0 then show ?thesis using css by simp
  next
    case (Suc j)
    then show ?thesis using Cons css by simp
  qed
qed

lemma map_set_cols_set:
  assumes "\<forall>c \<in> set css. wf_cols n c"
  shows "map (set_cols \<circ> set) css = css"
  by (rule map_idI) (use assms in auto)

lemma dsim_dof_minit0_MAnds:
  assumes sf: "safe_formula \<phi>" and b: "\<forall>x \<in> Formula.fv \<phi>. x < n"
    and m: "minit0 n \<phi> = mformula.MAnds (set c0 # map set css) (map set nss) L
        (replicate (length L) [])"
    and lenL: "length (c0 # css @ nss) = length L"
    and wfc: "\<forall>c \<in> set (c0 # css @ nss). wf_cols n c"
    and A: "Formula.fv \<phi> = set c0 \<union> (\<Union>c \<in> set css. set c)"
    and sub: "\<forall>c \<in> set nss. set c \<subseteq> Formula.fv \<phi>"
    and ih: "\<forall>i < length L. dsim n ((c0 # css @ nss) ! i) tw
        (dof n ((c0 # css @ nss) ! i) (L ! i)) (L ! i)"
  shows "dofc n tw \<phi>"
proof -
  let ?cs = "set_cols (Formula.fv \<phi>)"
  let ?css = "c0 # css @ nss"
  have w: "wf_cols n ?cs" by (rule wf_cols_set_cols[OF finite_fvi b])
  have pr: "produces n (set ?cs) tw
      (mformula.MAnds (set c0 # map set css) (map set nss) L (replicate (length L) []))"
    using produces_minit0[OF sf b] unfolding m by simp
  have s0: "sorted_wrt (<) c0" and sall: "\<forall>c \<in> set css. sorted_wrt (<) c" using wfc by auto
  have dc: "?cs = dands_cols c0 css"
    unfolding A by (rule set_cols_eq)
      (use s0 sall in \<open>auto simp: sorted_dands_cols set_dands_cols\<close>)
  have sb: "\<forall>c \<in> set nss. set c \<subseteq> set (dands_cols c0 css)"
    using sub unfolding A by (simp add: set_dands_cols)
  have w0: "wf_cols n c0" using wfc by simp
  have sc0: "set_cols (set c0) = c0" by (rule set_cols_set[OF w0])
  have scss: "map (set_cols \<circ> set) css = css" using wfc by (intro map_set_cols_set) auto
  have scnss: "map (set_cols \<circ> set) nss = nss" using wfc by (intro map_set_cols_set) auto
  have d: "dof n ?cs (mformula.MAnds (set c0 # map set css) (map set nss) L
        (replicate (length L) []))
      = DAnds (dands_plans c0 css) (dands_plans (dands_cols c0 css) nss)
          (dof_list n ?css L) (map2 map (map (dtabc n) ?css) (replicate (length L) []))"
    using dc lenL by (simp add: Let_def sc0 scss scnss)
  have ld: "\<forall>i < length L. dsim n (?css ! i) tw (dof_list n ?css L ! i) (L ! i)"
  proof (intro allI impI)
    fix i assume i: "i < length L"
    then have i': "i < length ?css" using lenL by simp
    have "dof_list n ?css L ! i = dof n (?css ! i) (L ! i)" by (rule dof_list_nth[OF i i'])
    then show "dsim n (?css ! i) tw (dof_list n ?css L ! i) (L ! i)" using ih i by simp
  qed
  have bf: "dbufn n ?css (replicate (length L) [])
      (map2 map (map (dtabc n) ?css) (replicate (length L) []))"
    using lenL by (auto simp: dbufn_def)
  show ?thesis unfolding m d
    by (rule dsim.DsAnds[OF w pr ld _ lenL wfc sb dc refl refl bf]) simp
qed

text \<open>
  A fused aggregation compiles to the escape hatch, because the structure it builds carries the
  aggregation in its arguments and the dense Since and Until do not.  All the induction needs of
  it is the node's shape, and that is read off the kernel's two initialisers once, here, rather
  than inside the induction, where the case distinction over the operand would be paid for again
  at every use.
\<close>

lemma formula_not_Neg_case:
  "\<forall>x. \<phi> \<noteq> Formula.Neg x \<Longrightarrow> (case \<phi> of Formula.Neg x \<Rightarrow> f x | _ \<Rightarrow> c) = c"
  by (cases \<phi>) simp_all

lemma init_since_shape:
  "(\<exists>args \<xi> \<eta> bf aux. args_agg args = agg \<and>
      default_mmasaux.init_since minit0 m agg \<alpha> J \<beta> = mformula.MSince args \<xi> \<eta> bf aux)
   \<or> default_mmasaux.init_since minit0 m agg \<alpha> J \<beta> = mformula.MRel empty_table"
proof (cases "safe_formula \<alpha>")
  case True
  let ?args = "init_args J m (Formula.fv \<alpha>) (Formula.fv \<beta>) True agg"
  have ag: "args_agg ?args = agg" by (simp add: init_args_def)
  have eq: "default_mmasaux.init_since minit0 m agg \<alpha> J \<beta>
      = mformula.MSince ?args (minit0 m \<alpha>) (minit0 m \<beta>) init_mbuf2S (init_mmasaux ?args)"
    using True by (simp add: default_mmasaux.init_since_def)
  show ?thesis using ag eq by blast
next
  case ns: False
  show ?thesis
  proof (cases "\<exists>x. \<alpha> = Formula.Neg x")
    case True
    then obtain x where ax: "\<alpha> = Formula.Neg x" by blast
    let ?args = "init_args J m (Formula.fv \<alpha>) (Formula.fv \<beta>) False agg"
    have ag: "args_agg ?args = agg" by (simp add: init_args_def)
    have eq: "default_mmasaux.init_since minit0 m agg \<alpha> J \<beta>
        = mformula.MSince ?args (minit0 m x) (minit0 m \<beta>) init_mbuf2S (init_mmasaux ?args)"
      using ns ax by (simp add: default_mmasaux.init_since_def)
    show ?thesis using ag eq by blast
  next
    case False
    then have "default_mmasaux.init_since minit0 m agg \<alpha> J \<beta> = mformula.MRel empty_table"
      using ns by (simp add: default_mmasaux.init_since_def formula_not_Neg_case)
    then show ?thesis by blast
  qed
qed

lemma init_until_shape:
  "(\<exists>args \<xi> \<eta> bf ns t aux. args_agg args = agg \<and>
      dq_muaux.init_until minit0 m agg \<alpha> J \<beta> = mformula.MUntil args \<xi> \<eta> bf ns t aux)
   \<or> dq_muaux.init_until minit0 m agg \<alpha> J \<beta> = mformula.MRel empty_table"
proof (cases "safe_formula \<alpha>")
  case True
  let ?args = "init_args J m (Formula.fv \<alpha>) (Formula.fv \<beta>) True agg"
  have ag: "args_agg ?args = agg" by (simp add: init_args_def)
  have eq: "dq_muaux.init_until minit0 m agg \<alpha> J \<beta>
      = mformula.MUntil ?args (minit0 m \<alpha>) (minit0 m \<beta>) ([], []) [] 0 (init_muaux_dq ?args)"
    using True by (simp add: dq_muaux.init_until_def)
  show ?thesis using ag eq by blast
next
  case ns: False
  show ?thesis
  proof (cases "\<exists>x. \<alpha> = Formula.Neg x")
    case True
    then obtain x where ax: "\<alpha> = Formula.Neg x" by blast
    let ?args = "init_args J m (Formula.fv \<alpha>) (Formula.fv \<beta>) False agg"
    have ag: "args_agg ?args = agg" by (simp add: init_args_def)
    have eq: "dq_muaux.init_until minit0 m agg \<alpha> J \<beta>
        = mformula.MUntil ?args (minit0 m x) (minit0 m \<beta>) ([], []) [] 0 (init_muaux_dq ?args)"
      using ns ax by (simp add: dq_muaux.init_until_def)
    show ?thesis using ag eq by blast
  next
    case False
    then have "dq_muaux.init_until minit0 m agg \<alpha> J \<beta> = mformula.MRel empty_table"
      using ns by (simp add: dq_muaux.init_until_def formula_not_Neg_case)
    then show ?thesis by blast
  qed
qed

subsection \<open>The compiler produces a simulation\<close>

theorem dsim_dof_minit0:
  "safe_formula \<phi> \<Longrightarrow> \<forall>x \<in> Formula.fv \<phi>. x < n \<Longrightarrow> dofc n tw \<phi>"
proof (induction arbitrary: n rule: safe_formula_induct)
  case (Eq_Const c d)
  show ?case by (rule dsim_dof_minit0_rel)
      (auto simp: table_def unit_table_def empty_table_def wf_tuple_def split: if_splits)
next
  case (Eq_Var1 c x)
  show ?case by (rule dsim_dof_minit0_rel)
      (use Eq_Var1.prems in \<open>auto simp: table_def singleton_table_def wf_tuple_def\<close>)
next
  case (Eq_Var2 c x)
  show ?case by (rule dsim_dof_minit0_rel)
      (use Eq_Var2.prems in \<open>auto simp: table_def singleton_table_def wf_tuple_def\<close>)
next
  case (Pred e ts)
  show ?case by (rule dsim_dof_minit0_Pred[where pn = e and ts = ts])
      (use Pred.hyps Pred.prems in simp_all)
next
  case (Let p \<phi> \<psi>)
  show ?case by (rule dsim_dof_minit0_pure) (use Let.hyps Let.prems in simp_all)
next
  case (Frz p \<phi> \<psi>)
  show ?case by (rule dsim_dof_minit0_pure) (use Frz.hyps Frz.prems in simp_all)
next
  case (LetPast p \<phi> \<psi>)
  show ?case by (rule dsim_dof_minit0_pure) (use LetPast.hyps LetPast.prems in simp_all)
next
  case (And_assign \<phi> \<psi>)
  show ?case by (rule dsim_dof_minit0_pure) (use And_assign.hyps And_assign.prems in simp_all)
next
  case (And_safe \<phi> \<psi>)
  have sfa: "safe_formula (Formula.And \<phi> \<psi>)" using And_safe.hyps by simp
  have b1: "\<forall>x \<in> Formula.fv \<phi>. x < n" using And_safe.prems by simp
  have b2: "\<forall>x \<in> Formula.fv \<psi>. x < n" using And_safe.prems by simp
  have m: "minit0 n (Formula.And \<phi> \<psi>)
      = mformula.MAnd (set (set_cols (Formula.fv \<phi>))) (minit0 n \<phi>) True
          (set (set_cols (Formula.fv \<psi>))) (minit0 n \<psi>) ([], [])"
    using And_safe.hyps by simp
  show ?case
    by (rule dsim_dof_minit0_MAnd[OF sfa And_safe.prems m refl refl])
      (use And_safe.IH(1)[OF b1] And_safe.IH(2)[OF b2] in simp_all)
next
  case (And_constraint \<phi> \<psi>)
  have sfa: "safe_formula (Formula.And \<phi> \<psi>)" using And_constraint.hyps by simp
  have b1: "\<forall>x \<in> Formula.fv \<phi>. x < n" using And_constraint.prems by simp
  have A: "Formula.fv (Formula.And \<phi> \<psi>) = Formula.fv \<phi>" using And_constraint.hyps(4) by auto
  obtain t1 pp c t2 where cf: "split_constraint \<psi> = (t1, pp, c, t2)"
    by (cases "split_constraint \<psi>")
  have m: "minit0 n (Formula.And \<phi> \<psi>) = mformula.MAndRel (minit0 n \<phi>) (t1, pp, c, t2)"
    using And_constraint.hyps cf by simp
  show ?case
    by (rule dsim_dof_minit0_MAndRel[OF sfa And_constraint.prems m A
        And_constraint.IH[OF b1]])
next
  case (And_Not \<phi> \<psi>)
  have sfa: "safe_formula (Formula.And \<phi> (Formula.Neg \<psi>))" using And_Not.hyps by simp
  have sub: "Formula.fv \<psi> \<subseteq> Formula.fv \<phi>" using And_Not.hyps(4) by simp
  have b1: "\<forall>x \<in> Formula.fv \<phi>. x < n" using And_Not.prems by simp
  have b2: "\<forall>x \<in> Formula.fv \<psi>. x < n" using b1 sub by auto
  have m: "minit0 n (Formula.And \<phi> (Formula.Neg \<psi>))
      = mformula.MAnd (set (set_cols (Formula.fv \<phi>))) (minit0 n \<phi>) False
          (set (set_cols (Formula.fv \<psi>))) (minit0 n \<psi>) ([], [])"
    using And_Not.hyps by simp
  show ?case
    by (rule dsim_dof_minit0_MAnd[OF sfa And_Not.prems m refl refl])
      (use sub And_Not.IH(1)[OF b1] And_Not.IH(2)[OF b2] in \<open>simp_all add: Un_absorb2\<close>)
next
  case (And_Trigger \<phi> \<phi>' I \<psi>')
  note sp' = \<open>safe_formula \<phi>'\<close> and sd = \<open>safe_dual True safe_formula \<phi>' I \<psi>'\<close>
  note subf = \<open>Formula.fv (Formula.Trigger \<phi>' I \<psi>') \<subseteq> Formula.fv \<phi>\<close>
  have sub: "Formula.fv \<phi>' \<subseteq> Formula.fv \<psi>'"
    using sd sp' by (auto simp: safe_dual_def split: if_splits)
  have fvt: "Formula.fv (Formula.Trigger \<phi>' I \<psi>') = Formula.fv \<psi>'" using sub by auto
  have bA: "\<forall>x \<in> Formula.fv \<phi>. x < n" using And_Trigger.prems by simp
  have bR: "\<forall>x \<in> Formula.fv \<psi>'. x < n" using bA subf fvt by auto
  have bL: "\<forall>x \<in> Formula.fv \<phi>'. x < n" using bR sub by auto
  show ?case
  proof (cases "mem I 0")
    case True
    have st: "safe_formula (Formula.Trigger \<phi>' I \<psi>')"
      using sd sp' True by (simp add: safe_dual_def)
    have sfa: "safe_formula (Formula.And \<phi> (Formula.Trigger \<phi>' I \<psi>'))"
      using And_Trigger.hyps st by simp
    have bt: "\<forall>x \<in> Formula.fv (Formula.Trigger \<phi>' I \<psi>'). x < n" using bR fvt by simp
    have mt: "dof n (set_cols (Formula.fv (Formula.Trigger \<phi>' I \<psi>')))
          (minit0 n (Formula.Trigger \<phi>' I \<psi>'))
        = DPure (minit0 n (Formula.Trigger \<phi>' I \<psi>')) n
          (wide_mask n (set_cols (Formula.fv (Formula.Trigger \<phi>' I \<psi>'))))"
      using sp' by (simp add: verimon_maux.init_trigger_def)
    have i2: "dofc n tw (Formula.Trigger \<phi>' I \<psi>')"
      by (rule dsim_dof_minit0_pure[OF st bt mt])
    have m: "minit0 n (Formula.And \<phi> (Formula.Trigger \<phi>' I \<psi>'))
        = mformula.MAnd (set (set_cols (Formula.fv \<phi>))) (minit0 n \<phi>) True
            (set (set_cols (Formula.fv (Formula.Trigger \<phi>' I \<psi>'))))
            (minit0 n (Formula.Trigger \<phi>' I \<psi>')) ([], [])"
      using st by (simp add: no_safe_assign_trigger)
    show ?thesis
      by (rule dsim_dof_minit0_MAnd[OF sfa And_Trigger.prems m refl refl])
        (use subf i2 And_Trigger.IH(1)[OF bA] in \<open>simp_all add: Un_absorb2\<close>)
  next
    case False
    have nst: "\<not> safe_formula (Formula.Trigger \<phi>' I \<psi>')"
      using False by (simp add: safe_dual_def)
    have sfa: "safe_formula (Formula.And \<phi> (Formula.Trigger \<phi>' I \<psi>'))"
      using And_Trigger.hyps subf by simp
    have m: "dof n (set_cols (Formula.fv (Formula.And \<phi> (Formula.Trigger \<phi>' I \<psi>'))))
          (minit0 n (Formula.And \<phi> (Formula.Trigger \<phi>' I \<psi>')))
        = DPure (minit0 n (Formula.And \<phi> (Formula.Trigger \<phi>' I \<psi>'))) n
          (wide_mask n (set_cols (Formula.fv (Formula.And \<phi> (Formula.Trigger \<phi>' I \<psi>')))))"
      using nst sp' by (simp add: no_safe_assign_trigger verimon_maux.init_and_trigger_def)
    show ?thesis by (rule dsim_dof_minit0_pure[OF sfa And_Trigger.prems m])
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
  have bb: "\<forall>x \<in> \<Union> (Formula.fv ` set pos). x < n" using Ands.prems setl by auto
  have bn: "\<forall>x \<in> \<Union> (Formula.fv ` set neg). x < n" using bb Ands.hyps(5) by blast
  have sfa: "safe_formula (Formula.Ands l)"
    using Ands.hyps(1,2,3,4,5) by (simp add: Let_def)
  let ?c0 = "set_cols (Formula.fv p)"
  let ?css = "map (\<lambda>a. set_cols (Formula.fv a)) ps"
  let ?nss = "map (\<lambda>a. set_cols (Formula.fv a)) neg"
  let ?L = "map (minit0 n) pos @ map (minit0 n) (map remove_neg neg)"
  have m: "minit0 n (Formula.Ands l)
      = mformula.MAnds (set ?c0 # map set ?css) (map set ?nss) ?L
          (replicate (length ?L) [])"
    using Ands.hyps(1)[symmetric] pl lenl by (simp add: Let_def o_def)
  have cssall: "?c0 # ?css @ ?nss
      = map (\<lambda>a. set_cols (Formula.fv a)) pos @ map (\<lambda>a. set_cols (Formula.fv a)) neg"
    using pl by simp
  have lenL: "length (?c0 # ?css @ ?nss) = length ?L" using pl lenl by simp
  have wfc: "\<forall>c \<in> set (?c0 # ?css @ ?nss). wf_cols n c"
    using bb bn pl by (auto simp: wf_cols_set_cols)
  have A: "Formula.fv (Formula.Ands l) = set ?c0 \<union> (\<Union>c \<in> set ?css. set c)"
    unfolding e using pl by auto
  have sub: "\<forall>c \<in> set ?nss. set c \<subseteq> Formula.fv (Formula.Ands l)"
    unfolding e using Ands.hyps(5) by auto
  have ih: "\<forall>i < length ?L. dsim n ((?c0 # ?css @ ?nss) ! i) tw
      (dof n ((?c0 # ?css @ ?nss) ! i) (?L ! i)) (?L ! i)"
  proof (intro allI impI)
    fix i assume i: "i < length ?L"
    show "dsim n ((?c0 # ?css @ ?nss) ! i) tw
        (dof n ((?c0 # ?css @ ?nss) ! i) (?L ! i)) (?L ! i)"
    proof (cases "i < length pos")
      case True
      then have c: "(?c0 # ?css @ ?nss) ! i = set_cols (Formula.fv (pos ! i))"
        and l': "?L ! i = minit0 n (pos ! i)"
        unfolding cssall by (simp_all add: nth_append)
      have ip: "pos ! i \<in> set pos" using True by simp
      have bi: "\<forall>x \<in> Formula.fv (pos ! i). x < n" using bb ip by auto
      show ?thesis unfolding c l'
        using Ands.IH(1)[unfolded list_all_iff] ip bi by blast
    next
      case False
      let ?j = "i - length pos"
      have j: "?j < length neg" using i False lenl by simp
      have c: "(?c0 # ?css @ ?nss) ! i = set_cols (Formula.fv (neg ! ?j))"
        using False j unfolding cssall by (simp add: nth_append)
      have l': "?L ! i = minit0 n (remove_neg (neg ! ?j))"
        using False j by (simp add: nth_append)
      have ip: "remove_neg (neg ! ?j) \<in> set (map remove_neg neg)" using j by simp
      have bi: "\<forall>x \<in> Formula.fv (remove_neg (neg ! ?j)). x < n"
        using bn j by (auto simp: fv_remove_neg[symmetric])
      have "dofc n tw (remove_neg (neg ! ?j))"
        using Ands.IH(2)[unfolded list_all_iff] ip bi by blast
      then show ?thesis unfolding c l' by (simp add: fv_remove_neg[symmetric])
    qed
  qed
  show ?case
    by (rule dsim_dof_minit0_MAnds[OF sfa Ands.prems m lenL wfc A sub ih])
next
  case (Neg \<phi>)
  have sfa: "safe_formula (Formula.Neg \<phi>)" using Neg.hyps by simp
  have b1: "\<forall>x \<in> Formula.fv \<phi>. x < n" using Neg.hyps(1) by simp
  have m: "minit0 n (Formula.Neg \<phi>) = mformula.MNeg (minit0 n \<phi>)" using Neg.hyps(1) by simp
  show ?case
    by (rule dsim_dof_minit0_Neg[OF sfa Neg.prems m _ Neg.hyps(1) Neg.IH[OF b1]])
      (use Neg.hyps(1) in simp)
next
  case (Or \<phi> \<psi>)
  have sfa: "safe_formula (Formula.Or \<phi> \<psi>)" using Or.hyps by simp
  have b1: "\<forall>x \<in> Formula.fv \<phi>. x < n" using Or.prems by simp
  have b2: "\<forall>x \<in> Formula.fv \<psi>. x < n" using Or.prems Or.hyps(1) by simp
  have m: "minit0 n (Formula.Or \<phi> \<psi>) = mformula.MOr (minit0 n \<phi>) (minit0 n \<psi>) ([], [])"
    by simp
  show ?case
    by (rule dsim_dof_minit0_Or[OF sfa Or.prems m _ _ Or.IH(1)[OF b1] Or.IH(2)[OF b2]])
      (use Or.hyps(1) in simp_all)
next
  case (Exists t \<phi>)
  have sfa: "safe_formula (Formula.Exists t \<phi>)" using Exists.hyps by simp
  have b1: "\<forall>x \<in> Formula.fv \<phi>. x < Suc n"
    using fvi_Suc_bound[where b = 0 and \<phi> = \<phi> and n = n] Exists.prems by simp
  have m: "minit0 n (Formula.Exists t \<phi>) = mformula.MExists (minit0 (Suc n) \<phi>)" by simp
  show ?case
    by (rule dsim_dof_minit0_Exists[OF sfa Exists.prems m _ Exists.hyps(2)
        Exists.IH[OF b1]]) simp
next
  case (Agg y \<omega> tys f \<chi>)
  note tsub = \<open>{0..<length tys} \<subseteq> Formula.fv \<chi>\<close> and fsub = \<open>Formula.fv_trm f \<subseteq> Formula.fv \<chi>\<close>
  note ynot = \<open>y + length tys \<notin> Formula.fv \<chi>\<close> and sc = \<open>safe_formula \<chi>\<close>
  have sfa: "safe_formula (Formula.Agg y \<omega> tys f \<chi>)" using sc ynot tsub fsub by simp
  have A: "Formula.fv (Formula.Agg y \<omega> tys f \<chi>)
      = Set.insert y ((\<lambda>i. i - length tys) ` (Formula.fv \<chi> - {0..<length tys}))"
    by (rule fv_Agg_image[OF fvi_trm_mono[OF fsub]])
  have bp: "\<forall>x \<in> Formula.fv \<chi>. x < length tys + n"
  proof
    fix x assume x: "x \<in> Formula.fv \<chi>"
    show "x < length tys + n"
    proof (cases "x < length tys")
      case True then show ?thesis by simp
    next
      case False
      then have "x - length tys
          \<in> (\<lambda>i. i - length tys) ` (Formula.fv \<chi> - {0..<length tys})" using x by auto
      then have "x - length tys < n" using Agg.prems A by auto
      then show ?thesis using False by simp
    qed
  qed
  let ?ag = "init_aggargs (Formula.fv \<chi>) n (Formula.fv \<chi> \<subseteq> {0..<length tys}) y \<omega> tys f"
  let ?cs = "set_cols (Formula.fv (Formula.Agg y \<omega> tys f \<chi>))"
  have D: "dofc n tw (Formula.Agg y \<omega> tys f \<chi>)"
    if mm: "minit0 n (Formula.Agg y \<omega> tys f \<chi>)
        = mformula.MAgg ?ag (minit0 (length tys + n) \<chi>)"
  proof -
    have i1: "dofc (length tys + n) tw \<chi>" by (rule Agg.IH[OF order_refl sc bp])
    show ?thesis
      by (rule dsim_dof_minit0_MAgg[OF sfa Agg.prems mm refl ynot tsub fsub A bp i1])
  qed
  have shape: "(\<exists>args \<xi> \<eta> bf aux. args_agg args \<noteq> None \<and>
          minit0 n (Formula.Agg y \<omega> tys f \<chi>) = mformula.MSince args \<xi> \<eta> bf aux)
      \<or> (\<exists>args \<xi> \<eta> bf ns t aux. args_agg args \<noteq> None \<and>
          minit0 n (Formula.Agg y \<omega> tys f \<chi>) = mformula.MUntil args \<xi> \<eta> bf ns t aux)
      \<or> minit0 n (Formula.Agg y \<omega> tys f \<chi>) = mformula.MRel empty_table"
    if dj: "\<chi> = Formula.Since \<chi>1 J \<chi>2 \<or> \<chi> = Formula.Until \<chi>1 J \<chi>2" for \<chi>1 J \<chi>2
  proof -
    note S = init_since_shape[where agg = "Some ?ag" and m = "length tys + n"
        and \<alpha> = \<chi>1 and J = J and \<beta> = \<chi>2]
    note U = init_until_shape[where agg = "Some ?ag" and m = "length tys + n"
        and \<alpha> = \<chi>1 and J = J and \<beta> = \<chi>2]
    show ?thesis using dj S U by (auto simp: Let_def)
  qed
  have E: "dofc n tw (Formula.Agg y \<omega> tys f \<chi>)"
    if dj: "\<chi> = Formula.Since \<chi>1 J \<chi>2 \<or> \<chi> = Formula.Until \<chi>1 J \<chi>2" for \<chi>1 J \<chi>2
    using shape[OF dj]
  proof (elim disjE exE conjE)
    fix args \<xi> \<eta> bf aux
    assume ag: "args_agg args \<noteq> None"
      and mm: "minit0 n (Formula.Agg y \<omega> tys f \<chi>) = mformula.MSince args \<xi> \<eta> bf aux"
    have m: "dof n ?cs (minit0 n (Formula.Agg y \<omega> tys f \<chi>))
        = DPure (minit0 n (Formula.Agg y \<omega> tys f \<chi>)) n (wide_mask n ?cs)"
      unfolding mm using ag by (simp add: Let_def)
    show ?thesis by (rule dsim_dof_minit0_pure[OF sfa Agg.prems m])
  next
    fix args \<xi> \<eta> bf ns t aux
    assume ag: "args_agg args \<noteq> None"
      and mm: "minit0 n (Formula.Agg y \<omega> tys f \<chi>) = mformula.MUntil args \<xi> \<eta> bf ns t aux"
    have m: "dof n ?cs (minit0 n (Formula.Agg y \<omega> tys f \<chi>))
        = DPure (minit0 n (Formula.Agg y \<omega> tys f \<chi>)) n (wide_mask n ?cs)"
      unfolding mm using ag by (simp add: Let_def)
    show ?thesis by (rule dsim_dof_minit0_pure[OF sfa Agg.prems m])
  next
    assume mm: "minit0 n (Formula.Agg y \<omega> tys f \<chi>) = mformula.MRel empty_table"
    show ?thesis
      by (rule dsim_dof_minit0_rel[OF sfa Agg.prems mm]) (simp add: table_def empty_table_def)
  qed
  show ?case
  proof (cases \<chi>)
    case (Since \<chi>1 J \<chi>2) show ?thesis by (rule E[of \<chi>1 J \<chi>2]) (use Since in blast)
  next
    case (Until \<chi>1 J \<chi>2) show ?thesis by (rule E[of \<chi>1 J \<chi>2]) (use Until in blast)
  qed (use D in \<open>simp_all add: Let_def\<close>)
next
  case (Prev I \<phi>)
  have sfa: "safe_formula (Formula.Prev I \<phi>)" using Prev.hyps by simp
  have b1: "\<forall>x \<in> Formula.fv \<phi>. x < n" using Prev.prems by simp
  have m: "minit0 n (Formula.Prev I \<phi>) = mformula.MPrev I (minit0 n \<phi>) True [] []" by simp
  show ?case by (rule dsim_dof_minit0_Prev[OF sfa Prev.prems m _ Prev.IH[OF b1]]) simp
next
  case (Next I \<phi>)
  have sfa: "safe_formula (Formula.Next I \<phi>)" using Next.hyps by simp
  have b1: "\<forall>x \<in> Formula.fv \<phi>. x < n" using Next.prems by simp
  have m: "minit0 n (Formula.Next I \<phi>) = mformula.MNext I (minit0 n \<phi>) True []" by simp
  show ?case by (rule dsim_dof_minit0_Next[OF sfa Next.prems m _ Next.IH[OF b1]]) simp
next
  case (Since \<phi> I \<psi>)
  note sub = \<open>Formula.fv \<phi> \<subseteq> Formula.fv \<psi>\<close> and s1 = \<open>safe_formula \<phi>\<close> and s2 = \<open>safe_formula \<psi>\<close>
  have sfa: "safe_formula (Formula.Since \<phi> I \<psi>)" using sub s1 s2 by simp
  have A: "Formula.fv (Formula.Since \<phi> I \<psi>) = Formula.fv \<psi>" using sub by auto
  have b2: "\<forall>x \<in> Formula.fv \<psi>. x < n" using Since.prems A by simp
  have b1: "\<forall>x \<in> Formula.fv \<phi>. x < n" using b2 sub by auto
  have m: "minit0 n (Formula.Since \<phi> I \<psi>)
      = mformula.MSince (init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) True None)
          (minit0 n \<phi>) (minit0 n \<psi>) init_mbuf2S
          (init_mmasaux (init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) True None))"
    using s1 by (simp add: default_mmasaux.init_since_def)
  show ?case
    by (rule dsim_dof_minit0_MSince[OF sfa Since.prems m refl A sub
        Since.IH(1)[OF b1] Since.IH(2)[OF b2]])
next
  case (Not_Since \<phi> I \<psi>)
  note sub = \<open>Formula.fv (Formula.Neg \<phi>) \<subseteq> Formula.fv \<psi>\<close> and s1 = \<open>safe_formula \<phi>\<close>
  note ns = \<open>\<not> safe_formula (Formula.Neg \<phi>)\<close> and s2 = \<open>safe_formula \<psi>\<close>
  have sfa: "safe_formula (Formula.Since (Formula.Neg \<phi>) I \<psi>)" using sub s1 s2 by simp
  have A: "Formula.fv (Formula.Since (Formula.Neg \<phi>) I \<psi>) = Formula.fv \<psi>" using sub by auto
  have b2: "\<forall>x \<in> Formula.fv \<psi>. x < n" using Not_Since.prems A by simp
  have b1: "\<forall>x \<in> Formula.fv \<phi>. x < n" using b2 sub by auto
  have m: "minit0 n (Formula.Since (Formula.Neg \<phi>) I \<psi>)
      = mformula.MSince (init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) False None)
          (minit0 n \<phi>) (minit0 n \<psi>) init_mbuf2S
          (init_mmasaux (init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) False None))"
    using ns by (simp add: default_mmasaux.init_since_def)
  show ?case
    by (rule dsim_dof_minit0_MSince[OF sfa Not_Since.prems m refl A _
        Not_Since.IH(1)[OF b1] Not_Since.IH(2)[OF b2]]) (use sub in simp)
next
  case (Until \<phi> I \<psi>)
  note sub = \<open>Formula.fv \<phi> \<subseteq> Formula.fv \<psi>\<close> and s1 = \<open>safe_formula \<phi>\<close> and s2 = \<open>safe_formula \<psi>\<close>
  have sfa: "safe_formula (Formula.Until \<phi> I \<psi>)" using sub s1 s2 by simp
  have A: "Formula.fv (Formula.Until \<phi> I \<psi>) = Formula.fv \<psi>" using sub by auto
  have b2: "\<forall>x \<in> Formula.fv \<psi>. x < n" using Until.prems A by simp
  have b1: "\<forall>x \<in> Formula.fv \<phi>. x < n" using b2 sub by auto
  have m: "minit0 n (Formula.Until \<phi> I \<psi>)
      = mformula.MUntil (init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) True None)
          (minit0 n \<phi>) (minit0 n \<psi>) ([], []) [] 0
          (init_muaux_dq (init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) True None))"
    using s1 by (simp add: dq_muaux.init_until_def)
  show ?case
    by (rule dsim_dof_minit0_MUntil[OF sfa Until.prems m refl A sub
        Until.IH(1)[OF b1] Until.IH(2)[OF b2]])
next
  case (Not_Until \<phi> I \<psi>)
  note sub = \<open>Formula.fv (Formula.Neg \<phi>) \<subseteq> Formula.fv \<psi>\<close> and s1 = \<open>safe_formula \<phi>\<close>
  note ns = \<open>\<not> safe_formula (Formula.Neg \<phi>)\<close> and s2 = \<open>safe_formula \<psi>\<close>
  have sfa: "safe_formula (Formula.Until (Formula.Neg \<phi>) I \<psi>)" using sub s1 s2 by simp
  have A: "Formula.fv (Formula.Until (Formula.Neg \<phi>) I \<psi>) = Formula.fv \<psi>" using sub by auto
  have b2: "\<forall>x \<in> Formula.fv \<psi>. x < n" using Not_Until.prems A by simp
  have b1: "\<forall>x \<in> Formula.fv \<phi>. x < n" using b2 sub by auto
  have m: "minit0 n (Formula.Until (Formula.Neg \<phi>) I \<psi>)
      = mformula.MUntil (init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) False None)
          (minit0 n \<phi>) (minit0 n \<psi>) ([], []) [] 0
          (init_muaux_dq (init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) False None))"
    using ns by (simp add: dq_muaux.init_until_def)
  show ?case
    by (rule dsim_dof_minit0_MUntil[OF sfa Not_Until.prems m refl A _
        Not_Until.IH(1)[OF b1] Not_Until.IH(2)[OF b2]]) (use sub in simp)
next
  case (Trigger_0 \<phi> I \<psi>)
  have dj: "safe_formula \<phi> \<or> (case \<phi> of Formula.Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False)"
    using Trigger_0(4) by (cases \<phi>) auto
  have st: "safe_formula (Formula.Trigger \<phi> I \<psi>)"
    using Trigger_0.hyps dj by (simp add: safe_dual_def)
  have m: "dof n (set_cols (Formula.fv (Formula.Trigger \<phi> I \<psi>)))
        (minit0 n (Formula.Trigger \<phi> I \<psi>))
      = DPure (minit0 n (Formula.Trigger \<phi> I \<psi>)) n
        (wide_mask n (set_cols (Formula.fv (Formula.Trigger \<phi> I \<psi>))))"
  proof (cases "safe_formula \<phi>")
    case True then show ?thesis by (simp add: verimon_maux.init_trigger_def)
  next
    case False
    then obtain \<chi> where "\<phi> = Formula.Neg \<chi>" using dj by (cases \<phi>) auto
    then show ?thesis by (simp add: verimon_maux.init_trigger_def)
  qed
  show ?case by (rule dsim_dof_minit0_pure[OF st Trigger_0.prems m])
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
  show ?case by (rule dsim_dof_minit0_pure)
      (use MatchP.hyps MatchP.prems in \<open>simp_all split: prod.split\<close>)
next
  case (MatchF I r)
  show ?case by (rule dsim_dof_minit0_pure)
      (use MatchF.hyps MatchF.prems in \<open>simp_all split: prod.split\<close>)
next
  case (TP t)
  show ?case by (rule dsim_dof_minit0_pure)
      (use TP.hyps TP.prems in \<open>simp_all split: trm.splits\<close>)
next
  case (TS t)
  show ?case by (rule dsim_dof_minit0_pure)
      (use TS.hyps TS.prems in \<open>simp_all split: trm.splits\<close>)
qed

section \<open>The dense monitor's correctness theorem, on the compiled state\<close>

text \<open>
  The state the compiler produces relates to the kernel's the same way the escape hatch's did,
  so the transferred theorems of the preceding theories apply to it unchanged -- but now every
  node the dense fragment covers is a dense node, and the kernel's evaluator runs only under the
  constructors it does not.
\<close>

definition dof_state :: "nat \<Rightarrow> cols \<Rightarrow>
    (mmasaux, muaux_dq, event_data mmtaux) mstate \<Rightarrow> dmstate" where
  "dof_state n cs st =
     \<lparr> dmstate_i = mstate_i st, dmstate_j = mstate_j st,
       dmstate_m = dof n cs (mstate_m st),
       dmstate_n = n, dmstate_cs = cs, dmstate_t = mstate_t st \<rparr>"

lemma dmsim_state_dof_state:
  assumes n: "mstate_n st = n" and p: "dsim n cs tw (dof n cs (mstate_m st)) (mstate_m st)"
  shows "dmsim_state n cs tw st (dof_state n cs st)"
  by (simp add: dmsim_state_def dof_state_def n p)

context verimon_spec
begin

theorem dmonitor_mverdicts_dof:
  assumes f: "pfinite \<pi>" and wty: "wty_prefix SIG \<pi>"
  shows "flatten_verdicts (map (\<lambda>(i, t, X).
      (i, t, dtabw (Formula.nfv \<phi>) (set_cols (Formula.fv \<phi>)) X))
      (dmonitor (dof_state (Formula.nfv \<phi>) (set_cols (Formula.fv \<phi>))
         (minit_safe \<phi>)) \<pi>)) = Mt \<pi>"
proof -
  have mm: "mmonitorable \<phi>" by (rule monitorable)
  then have s: "safe_formula \<phi>" by (simp add: mmonitorable_def)
  have fin: "finite (Formula.fv \<phi>)" by simp
  have b: "\<forall>x \<in> Formula.fv \<phi>. x < Formula.nfv \<phi>" by (rule fvi_less_nfv)
  have w: "wf_cols (Formula.nfv \<phi>) (set_cols (Formula.fv \<phi>))"
    using set_cols[OF fin] b by auto
  have ni: "mstate_n (minit_safe \<phi>) = Formula.nfv \<phi>" by (rule minit_safe_state(1)[OF mm])
  have mm0: "mstate_m (minit_safe \<phi>) = minit0 (Formula.nfv \<phi>) \<phi>"
    by (rule minit_safe_state(2)[OF mm])
  have p: "dsim (Formula.nfv \<phi>) (set_cols (Formula.fv \<phi>)) 0
      (dof (Formula.nfv \<phi>) (set_cols (Formula.fv \<phi>)) (mstate_m (minit_safe \<phi>)))
      (mstate_m (minit_safe \<phi>))"
    unfolding mm0 by (rule dsim_dof_minit0[OF s b])
  have r: "dmsim_state (Formula.nfv \<phi>) (set_cols (Formula.fv \<phi>)) 0 (minit_safe \<phi>)
      (dof_state (Formula.nfv \<phi>) (set_cols (Formula.fv \<phi>)) (minit_safe \<phi>))"
    by (rule dmsim_state_dof_state[OF ni p])
  show ?thesis using w by (intro dmonitor_mverdicts[OF r _ f wty]) simp
qed

end

(*<*)
end
(*>*)
