(*<*)
theory Init
  imports Compile_Check
begin
(*>*)

section \<open>The criterion for the kernel's initial state\<close>

text \<open>
  \<open>mok_minit0\<close> says that the kernel's initial state for a safe formula satisfies the structural
  criterion \<open>mok\<close> of the preceding theory, with the formula's free-variable list as its column
  list.  The proof is by @{thm [source] safe_formula_induct}, one case per constructor.  What
  each case has to supply beyond the induction hypotheses is the initial auxiliary structure's
  invariant, and that comes from the kernel's own \<open>valid_init\<close> lemmas at time \<open>0\<close>: the three
  lemmas \<open>saux_inv_init\<close>, \<open>until_inv_init\<close> and \<open>trigger_inv_init\<close> below package them.  The
  remaining work is the column arithmetic of @{const Formula.fvi_list}: the kernel's node for a
  compound formula carries its operands' column lists, and the node lemmas say which list the
  node's output is over, which has to be the compound formula's own.
\<close>

lemma saux_inv_init:
  assumes sub: "set kL \<subseteq> set kR" and dL: "distinct kL" and dR: "distinct kR"
  shows "saux_inv (init_args I n kL kR b agg) kL kR tw init_mbuf2S
     (init_mmasaux (init_args I n kL kR b agg))"
  by (rule saux_invI[OF valid_init_mmasaux[OF sub dL dR]]) auto

lemma until_inv_init:
  assumes sub: "set kL \<subseteq> set kR" and dL: "distinct kL" and dR: "distinct kR"
  shows "until_inv (init_args I n kL kR b agg) kL kR tw 0
     (init_muaux_dq (init_args I n kL kR b agg)) ([], []) []"
proof -
  have v: "valid_muaux_dq (init_args I n kL kR b agg) 0 (init_muaux_dq (init_args I n kL kR b agg)) []"
    by (rule valid_init_muaux_dq[OF sub dL dR])
  show ?thesis unfolding until_inv_def uaux_inv_def using v by auto
qed

lemma trigger_inv_init:
  assumes wkc: "if mem I 0 then set kL \<subseteq> set kR else set kL = set kR"
    and dL: "distinct kL" and dR: "distinct kR" and pos: "\<not> mem I 0 \<longrightarrow> b"
  shows "trigger_inv (init_args I n kL kR b agg) kL kR tw
     (init_mmtaux (init_args I n kL kR b agg)) ([], []) []"
proof -
  have v: "valid_mmtaux (init_args I n kL kR b agg) 0 (init_mmtaux (init_args I n kL kR b agg)) []"
    using valid_init_mmtaux[OF wkc dL dR pos] by (simp add: Let_def)
  have t: "taux_inv (init_args I n kL kR b agg) kL kR 0 (init_mmtaux (init_args I n kL kR b agg))"
    unfolding taux_inv_def using v by (intro exI[of _ "[]"]) simp
  show ?thesis unfolding trigger_inv_def using t by (auto intro!: exI[of _ 0])
qed

lemma simple_pattern_upt: "is_simple_pattern (map Formula.Var [k..<k + m]) k"
proof (induct m arbitrary: k)
  case (Suc m)
  have "[k..<k + Suc m] = k # [Suc k..<Suc k + m]" by (simp add: upt_conv_Cons)
  then show ?case using Suc[of "Suc k"] by simp
qed simp

text \<open>The kernel compiles a release by rewriting it; the rewritten formula has the same
  free-variable list as the original.\<close>

lemma fv_list_release_safe_0:
  "Formula.fv \<phi> \<subseteq> Formula.fv \<psi> \<Longrightarrow>
   Formula.fv_list (release_safe_0 \<phi> I \<psi>) = Formula.fv_list (Formula.Release \<phi> I \<psi>)"
  by (simp add: release_safe_0_def always_safe_0_def cols_union_subset)

lemma fv_list_and_release_safe_bounded:
  "Formula.fv (Formula.Release \<phi>' I \<psi>') \<subseteq> Formula.fv \<phi> \<Longrightarrow>
   Formula.fv_list (and_release_safe_bounded \<phi> \<phi>' I \<psi>')
     = Formula.fv_list (Formula.And \<phi> (Formula.Release \<phi>' I \<psi>'))"
  by (simp add: and_release_safe_bounded_def release_safe_bounded_def always_safe_bounded_def
      cols_union_subset)

text \<open>An assignment appends the assigned variable's column.\<close>

lemma cols_union_assign:
  "set ys \<subseteq> set xs \<Longrightarrow> x \<notin> set xs \<Longrightarrow> cols_union xs (cols_union [x] ys) = xs @ [x]"
  "set ys \<subseteq> set xs \<Longrightarrow> x \<notin> set xs \<Longrightarrow> cols_union xs (cols_union ys [x]) = xs @ [x]"
  "x \<notin> set xs \<Longrightarrow> cols_union xs [x] = xs @ [x]"
  by (auto simp: cols_union_def filter_empty_conv)

lemma fv_list_And_assign:
  assumes sa: "safe_assignment (Formula.fv \<phi>) \<psi>"
  shows "Formula.fv_list (Formula.And \<phi> \<psi>) = Formula.fv_list \<phi> @ [fst (split_assignment (Formula.fv \<phi>) \<psi>)]"
proof -
  from sa consider (a) x t where "x \<notin> Formula.fv \<phi>" "Formula.fv_trm t \<subseteq> Formula.fv \<phi>"
      "\<psi> = Formula.Eq (Formula.Var x) t"
    | (b) x t where "x \<notin> Formula.fv \<phi>" "Formula.fv_trm t \<subseteq> Formula.fv \<phi>"
      "\<psi> = Formula.Eq t (Formula.Var x)"
    | (c) x y where "x \<notin> Formula.fv \<phi> \<longleftrightarrow> y \<in> Formula.fv \<phi>" "\<psi> = Formula.Eq (Formula.Var x) (Formula.Var y)"
    unfolding safe_assignment_iff2 by blast
  then show ?thesis
  proof cases
    case a
    then show ?thesis by (cases t) (simp_all add: cols_union_assign)
  next
    case b
    then show ?thesis by (cases t) (simp_all add: cols_union_assign)
  next
    case c
    then show ?thesis by (cases "x \<in> Formula.fv \<phi>") (simp_all add: cols_union_assign)
  qed
qed

text \<open>An aggregation's columns are the result column followed by its operand's group columns,
  shifted down past the bound variables.\<close>

lemma fv_list_Agg:
  assumes y: "y + length tys \<notin> Formula.fv \<phi>" and f: "Formula.fv_trm f \<subseteq> Formula.fv \<phi>"
  shows "Formula.fv_list (Formula.Agg y \<omega> tys f \<phi>) = y # shift_cols (length tys) (Formula.fv_list \<phi>)"
proof -
  have s: "set (Formula.fvi_trm_list (length tys) f) \<subseteq> set (Formula.fvi_list (length tys) \<phi>)"
    using f by (auto simp: fvi_trm_iff_fv_trm[where b = "length tys"] fvi_iff_fv[where b = "length tys"])
  have yn: "y \<notin> set (Formula.fvi_list (length tys) \<phi>)"
    using y by (simp add: fvi_iff_fv[where b = "length tys"])
  have sh: "Formula.fvi_list (length tys) \<phi> = shift_cols (length tys) (Formula.fv_list \<phi>)"
    using fvi_list_plus[of 0 "length tys" \<phi>] by simp
  have c1: "cols_union (Formula.fvi_list (length tys) \<phi>) (Formula.fvi_trm_list (length tys) f)
      = Formula.fvi_list (length tys) \<phi>" by (rule cols_union_subset[OF s])
  have c2: "cols_union [y] (Formula.fvi_list (length tys) \<phi>) = y # Formula.fvi_list (length tys) \<phi>"
    using yn by (auto simp: cols_union_def intro!: filter_True)
  have "Formula.fv_list (Formula.Agg y \<omega> tys f \<phi>) = cols_union [y]
      (cols_union (Formula.fvi_list (length tys) \<phi>) (Formula.fvi_trm_list (length tys) f))"
    by simp
  also have "\<dots> = y # shift_cols (length tys) (Formula.fv_list \<phi>)"
    unfolding c1 unfolding c2 unfolding sh ..
  finally show ?thesis .
qed

lemma shift_cols_Nil_iff: "shift_cols k cs = [] \<longleftrightarrow> (\<forall>x \<in> set cs. x < k)"
  by (auto simp: shift_cols_def filter_empty_conv)

lemma mok_minit0:
  "safe_formula \<phi> \<Longrightarrow> \<forall>x \<in> Formula.fv \<phi>. x < n \<Longrightarrow>
   mok n (Formula.fv_list \<phi>) tw (minit0 n \<phi>)"
proof (induction arbitrary: n rule: safe_formula_induct)
  case (Eq_Const c d)
  show ?case
    by (auto simp: table_def unit_table_def empty_table_def intro!: MokRel)
next
  case (Eq_Var1 c x)
  show ?case
    by (auto simp: table_def singleton_table_def wf_tuple_def intro!: MokRel)
next
  case (Eq_Var2 c x)
  show ?case
    by (auto simp: table_def singleton_table_def wf_tuple_def intro!: MokRel)
next
  case (Pred e ts)
  have m: "minit0 n (Formula.Pred e ts) = MPred e ts (pred_mode_of n ts)" by simp
  have A: "Formula.fv_list (Formula.Pred e ts) = pred_cols ts" by (rule fv_list_Pred)
  show ?case
  proof (cases "pred_mode_of n ts")
    case Copy
    then have c: "ts = map Formula.Var [0..<n]" by (simp add: pred_mode_of_def is_copy_pattern_def split: if_splits)
    have s: "is_simple_pattern ts 0" unfolding c using simple_pattern_upt[of 0 n] by simp
    show ?thesis unfolding m Copy A
      by (rule MokPredDb) (simp_all add: pred_cols_simple[OF s] length_smp_cols[OF s])
  next
    case Simple
    then have s: "is_simple_pattern ts 0" by (simp add: pred_mode_of_def split: if_splits)
    show ?thesis unfolding m Simple A
      by (rule MokPredDb) (simp_all add: pred_cols_simple[OF s] length_smp_cols[OF s])
  next
    case Match
    show ?thesis unfolding m Match A by (rule MokPredM) simp
  qed
next
  case (Let p \<phi> \<psi>)
  have p1: "mok (Formula.nfv \<phi>) (Formula.fv_list \<phi>) tw (minit0 (Formula.nfv \<phi>) \<phi>)"
    by (rule Let.IH(1)) (simp add: fvi_less_nfv)
  have p2: "mok n (Formula.fv_list \<psi>) tw (minit0 n \<psi>)"
    using Let.prems by (intro Let.IH(2)) simp
  show ?case by (simp add: MokLet[OF p1 p2])
next
  case (Frz p \<phi> \<psi>)
  have p1: "mok (Formula.nfv \<phi>) (Formula.fv_list \<phi>) tw (minit0 (Formula.nfv \<phi>) \<phi>)"
    by (rule Frz.IH(1)) (simp add: fvi_less_nfv)
  have p2: "mok n (Formula.fv_list \<psi>) tw (minit0 n \<psi>)"
    using Frz.prems by (intro Frz.IH(2)) simp
  show ?case by (simp add: MokFrz[OF p1 p2 _ p2])
next
  case (LetPast p \<phi> \<psi>)
  have p1: "mok (Formula.nfv \<phi>) (Formula.fv_list \<phi>) tw (minit0 (Formula.nfv \<phi>) \<phi>)"
    by (rule LetPast.IH(1)) (simp add: fvi_less_nfv)
  have p2: "mok n (Formula.fv_list \<psi>) tw (minit0 n \<psi>)"
    using LetPast.prems by (intro LetPast.IH(2)) simp
  show ?case by (simp add: MokLetPast[OF p1 p2])
next
  case (And_assign \<phi> \<psi>)
  have p: "mok n (Formula.fv_list \<phi>) tw (minit0 n \<phi>)" using And_assign by simp
  have m: "minit0 n (Formula.And \<phi> \<psi>) =
      MAndAssign (Formula.fv_list \<phi>) (minit0 n \<phi>) (split_assignment (Formula.fv \<phi>) \<psi>)"
    using And_assign.hyps(2) by simp
  show ?case unfolding m fv_list_And_assign[OF And_assign.hyps(2)]
    by (rule MokAndAssign[OF p refl])
next
  case (And_safe \<phi> \<psi>)
  have p1: "mok n (Formula.fv_list \<phi>) tw (minit0 n \<phi>)" using And_safe by simp
  have p2: "mok n (Formula.fv_list \<psi>) tw (minit0 n \<psi>)" using And_safe by simp
  have m: "minit0 n (Formula.And \<phi> \<psi>) = MAnd (Formula.fv_list \<phi>)
      (minit0 n \<phi>) True (Formula.fv_list \<psi>) (minit0 n \<psi>) ([], [])"
    using And_safe.hyps by simp
  show ?case unfolding m by (rule MokAnd[OF p1 p2]) simp_all
next
  case (And_constraint \<phi> \<psi>)
  have p: "mok n (Formula.fv_list \<phi>) tw (minit0 n \<phi>)" using And_constraint by simp
  have m: "minit0 n (Formula.And \<phi> \<psi>) =
      MAndRel (Formula.fv_list \<phi>) (minit0 n \<phi>) (split_constraint \<psi>)"
    using And_constraint.hyps by simp
  have e: "Formula.fv_list (Formula.And \<phi> \<psi>) = Formula.fv_list \<phi>"
    using And_constraint.hyps(4) by (simp add: cols_union_subset)
  show ?case unfolding m e by (rule MokAndRel[OF p])
next
  case (And_Not \<phi> \<psi>)
  have p1: "mok n (Formula.fv_list \<phi>) tw (minit0 n \<phi>)" using And_Not by simp
  have p2: "mok n (Formula.fv_list \<psi>) tw (minit0 n \<psi>)" using And_Not by simp
  have sub: "Formula.fv \<psi> \<subseteq> Formula.fv \<phi>" using And_Not.hyps(4) by simp
  have m: "minit0 n (Formula.And \<phi> (Formula.Neg \<psi>)) = MAnd (Formula.fv_list \<phi>)
      (minit0 n \<phi>) False (Formula.fv_list \<psi>) (minit0 n \<psi>) ([], [])"
    using And_Not.hyps by simp
  show ?case unfolding m by (rule MokAnd[OF p1 p2]) (simp_all add: sub)
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
  have pa: "mok n (Formula.fv_list \<phi>) tw (minit0 n \<phi>)" by (rule And_Trigger(5)[OF bA])
  have p1: "mok n (Formula.fv_list \<phi>') tw (minit0 n \<phi>')" by (rule And_Trigger(6)[OF bL])
  have p2: "mok n (Formula.fv_list \<psi>') tw (minit0 n \<psi>')" by (rule And_Trigger(7)[OF bR])
  have et: "Formula.fv_list (Formula.Trigger \<phi>' I \<psi>') = Formula.fv_list \<psi>'"
    using sub by (simp add: cols_union_subset)
  have e: "Formula.fv_list (Formula.And \<phi> (Formula.Trigger \<phi>' I \<psi>')) = Formula.fv_list \<phi>"
    using subf by (simp add: cols_union_subset)
  let ?args = "\<lambda>b. init_args I n (Formula.fv_list \<phi>') (Formula.fv_list \<psi>') b None"
  show ?case
  proof (cases "mem I 0")
    case True
    have st: "safe_formula (Formula.Trigger \<phi>' I \<psi>')"
      using sd sp' True by (simp add: safe_dual_def)
    have mt: "minit0 n (Formula.Trigger \<phi>' I \<psi>') = MTrigger (?args True)
        (minit0 n \<phi>') (minit0 n \<psi>') ([], []) [] (init_mmtaux (?args True))"
      using sp' by (simp add: verimon_maux.init_trigger_def)
    have pt: "mok n (Formula.fv_list (Formula.Trigger \<phi>' I \<psi>')) tw (minit0 n (Formula.Trigger \<phi>' I \<psi>'))"
      unfolding mt et
      by (rule MokTrigger[OF p1 p2 trigger_inv_init]) (simp_all add: init_args_def True sub)
    have m: "minit0 n (Formula.And \<phi> (Formula.Trigger \<phi>' I \<psi>')) =
        MAnd (Formula.fv_list \<phi>) (minit0 n \<phi>) True (Formula.fv_list (Formula.Trigger \<phi>' I \<psi>'))
          (minit0 n (Formula.Trigger \<phi>' I \<psi>')) ([], [])"
      using st by (simp add: no_safe_assign_trigger)
    show ?thesis unfolding m
      by (rule MokAnd[OF pa pt]) simp_all
  next
    case False
    have LR: "Formula.fv \<phi>' = Formula.fv \<psi>'"
      using sd False by (simp add: safe_dual_def)
    have nst: "\<not> safe_formula (Formula.Trigger \<phi>' I \<psi>')"
      using False by (simp add: safe_dual_def)
    have m: "minit0 n (Formula.And \<phi> (Formula.Trigger \<phi>' I \<psi>')) =
        MAndTrigger (Formula.fv_list \<phi>) (minit0 n \<phi>) ([], []) (?args True)
          (minit0 n \<phi>') (minit0 n \<psi>') ([], []) [] (init_mmtaux (?args True))"
      using nst sp' by (simp add: no_safe_assign_trigger verimon_maux.init_and_trigger_def)
    show ?thesis unfolding m e
      by (rule MokAndTrigger[OF pa p1 p2 trigger_inv_init])
        (use subR LR False in \<open>simp_all add: init_args_def\<close>)
  qed
next
  case (And_Release \<phi> \<phi>' I \<psi>')
  have b: "\<forall>x \<in> Formula.fv (and_release_safe_bounded \<phi> \<phi>' I \<psi>'). x < n"
    using And_Release.prems by (auto simp: release_fvi(3))
  have m: "minit0 n (Formula.And \<phi> (Formula.Release \<phi>' I \<psi>')) =
      minit0 n (and_release_safe_bounded \<phi> \<phi>' I \<psi>')"
    using And_Release.hyps(6) by (simp add: safe_assignment_def safe_dual_def)
  show ?case unfolding m fv_list_and_release_safe_bounded[OF And_Release.hyps(7), symmetric]
    by (rule And_Release.IH(1)[OF b])
next
  case (Ands l pos neg)
  have part: "pos = filter safe_formula l" and negd: "neg = filter (\<lambda>a. \<not> safe_formula a) l"
    using Ands.hyps(1) by (auto simp: o_def)
  have setl: "set l = set pos \<union> set neg" using part negd by auto
  have lenl: "length l = length pos + length neg" using part negd
    by (simp add: sum_length_filter_compl)
  obtain p ps where pl: "pos = p # ps" using Ands.hyps(2) by (cases pos) auto
  have b: "\<forall>x \<in> \<Union> (Formula.fv ` set pos). x < n"
    using Ands.prems setl by auto
  have bn: "\<forall>x \<in> \<Union> (Formula.fv ` set neg). x < n" using b Ands.hyps(5) by blast
  let ?kss = "map Formula.fv_list pos @ map Formula.fv_list neg"
  let ?L = "map (minit0 n) pos @ map (minit0 n) (map remove_neg neg)"
  have cs: "(Formula.fv_list p # map Formula.fv_list ps) @ map Formula.fv_list neg = ?kss"
    by (simp add: pl)
  have lL: "length ?L = length ?kss" by simp
  have lb: "length (replicate (length l) ([] :: event_data table list)) = length ?kss"
    using lenl by simp
  have fvrn: "\<And>\<chi>. Formula.fv_list (remove_neg \<chi>) = Formula.fv_list \<chi>"
    by (case_tac \<chi>) simp_all
  have pL: "\<forall>i < length ?kss. mok n (?kss ! i) tw (?L ! i)"
  proof (intro allI impI)
    fix i assume i: "i < length ?kss"
    show "mok n (?kss ! i) tw (?L ! i)"
    proof (cases "i < length pos")
      case True
      then have c: "?kss ! i = Formula.fv_list (pos ! i)" and l': "?L ! i = minit0 n (pos ! i)"
        by (simp_all add: nth_append)
      have ip: "pos ! i \<in> set pos" using True by simp
      have bi: "\<forall>x \<in> Formula.fv (pos ! i). x < n" using b ip by auto
      show ?thesis unfolding c l'
        using Ands.IH(1)[unfolded list_all_iff] ip bi by blast
    next
      case False
      let ?j = "i - length pos"
      have j: "?j < length neg" using i False by simp
      have c: "?kss ! i = Formula.fv_list (neg ! ?j)" using False j by (simp add: nth_append)
      have l': "?L ! i = minit0 n (remove_neg (neg ! ?j))"
        using False j by (simp add: nth_append)
      have ip: "remove_neg (neg ! ?j) \<in> set (map remove_neg neg)" using j by simp
      have bi: "\<forall>x \<in> Formula.fv (remove_neg (neg ! ?j)). x < n"
        using bn j by (auto simp: fv_remove_neg[symmetric])
      have "mok n (Formula.fv_list (remove_neg (neg ! ?j))) tw (minit0 n (remove_neg (neg ! ?j)))"
        using Ands.IH(2)[unfolded list_all_iff] ip bi by blast
      then show ?thesis unfolding c l' fvrn .
    qed
  qed
  have pb: "\<forall>i < length ?kss. list_all (ftable (?kss ! i)) (replicate (length l) [] ! i)"
    using lenl by simp
  have sn: "\<forall>k \<in> set (map Formula.fv_list neg). set k \<subseteq> set (kands_cols (Formula.fv_list p) (map Formula.fv_list ps))"
    using Ands.hyps(5) pl by (auto simp: set_kands_cols)
  have m: "minit0 n (Formula.Ands l) = MAnds (Formula.fv_list (Formula.Ands l))
      (Formula.fv_list p # map Formula.fv_list ps) (map Formula.fv_list neg) ?L
      (replicate (length l) [])"
    using Ands.hyps(1)[symmetric] pl by (simp add: Let_def)
  have A: "set (Formula.fv_list (Formula.Ands l))
      = set (kands_cols (Formula.fv_list p) (map Formula.fv_list ps))"
    unfolding Formula.set_fvi_list using setl Ands.hyps(5) pl by (auto simp: set_kands_cols)
  show ?case unfolding m
    by (rule MokAnds[OF lL[unfolded cs[symmetric]] lb[unfolded cs[symmetric]]
        pL[unfolded cs[symmetric]] pb[unfolded cs[symmetric]] _ sn distinct_fvi_list A]) auto
next
  case (Neg \<phi>)
  have "Formula.fv_list \<phi> = []" using Neg.hyps(1) by (metis List.set_empty Formula.set_fvi_list)
  then show ?case using Neg.hyps(1) by (simp add: MokNeg)
next
  case (Or \<phi> \<psi>)
  have p1: "mok n (Formula.fv_list \<phi>) tw (minit0 n \<phi>)"
    using Or.prems by (intro Or.IH(1)) simp
  have p2: "mok n (Formula.fv_list \<psi>) tw (minit0 n \<psi>)"
    using Or.prems by (intro Or.IH(2)) (simp add: Or.hyps(1))
  have e: "Formula.fv_list (Formula.Or \<phi> \<psi>) = Formula.fv_list \<phi>"
    using Or.hyps(1) by (simp add: cols_union_subset)
  show ?case unfolding e by (simp add: MokOr[OF p1 p2])
next
  case (Exists t \<phi>)
  have b: "\<forall>x \<in> Formula.fv \<phi>. x < Suc n"
    using fvi_Suc_bound[where b = 0 and \<phi> = \<phi> and n = n] Exists.prems by simp
  have p: "mok (Suc n) (Formula.fv_list \<phi>) tw (minit0 (Suc n) \<phi>)" by (rule Exists.IH[OF b])
  have e: "Formula.fv_list (Formula.Exists t \<phi>) = ex_cols (Formula.fv_list \<phi>)"
    by (simp add: fvi_list_Suc)
  show ?case unfolding e by (simp add: MokExists[OF p])
next
  case (Agg y \<omega> tys f \<phi>)
  note ynf = \<open>y + length tys \<notin> Formula.fv \<phi>\<close>
  note fsub = \<open>Formula.fv_trm f \<subseteq> Formula.fv \<phi>\<close>
  note sf = \<open>safe_formula \<phi>\<close>
  have A: "Formula.fv_list (Formula.Agg y \<omega> tys f \<phi>) = y # shift_cols (length tys) (Formula.fv_list \<phi>)"
    by (rule fv_list_Agg[OF ynf fsub])
  have bp: "\<forall>x \<in> Formula.fv \<phi>. x < length tys + n"
  proof
    fix x assume x: "x \<in> Formula.fv \<phi>"
    show "x < length tys + n"
    proof (cases "x < length tys")
      case True then show ?thesis by simp
    next
      case False
      then have "x - length tys \<in> Formula.fv (Formula.Agg y \<omega> tys f \<phi>)"
        using x by (simp add: fvi_iff_fv[where b = "length tys"])
      then have "x - length tys < n" using Agg.prems by blast
      then show ?thesis using False by simp
    qed
  qed
  let ?ag = "init_aggargs (Formula.fv_list \<phi>) n (Formula.fv \<phi> \<subseteq> {0..<length tys}) y \<omega> tys f"
  have ag: "aggargs_cols ?ag = Formula.fv_list \<phi>" "aggargs_y ?ag = y" "aggargs_tys ?ag = tys"
      "aggargs_g0 ?ag = (Formula.fv \<phi> \<subseteq> {0..<length tys})"
    by (simp_all add: init_aggargs_def)
  have g0: "aggargs_g0 ?ag \<Longrightarrow> shift_cols (length (aggargs_tys ?ag)) (aggargs_cols ?ag) = []"
    unfolding ag by (auto simp: shift_cols_Nil_iff)
  have ks: "y # shift_cols (length tys) (Formula.fv_list \<phi>)
      = aggargs_y ?ag # shift_cols (length (aggargs_tys ?ag)) (aggargs_cols ?ag)"
    unfolding ag ..
  have p: "mok (length (aggargs_tys ?ag) + n) (Formula.fv_list \<phi>) tw (minit0 (length tys + n) \<phi>)"
    unfolding ag by (rule Agg.IH[OF order_refl sf bp])
  have D: "mok n (y # shift_cols (length tys) (Formula.fv_list \<phi>)) tw
      (MAgg ?ag (minit0 (length tys + n) \<phi>))"
    by (rule MokAgg[OF p g0 ks])
  show ?case
  proof (cases \<phi>)
    case (Since \<chi> I \<eta>)
    have s: "Formula.fv \<chi> \<subseteq> Formula.fv \<eta>" and se: "safe_formula \<eta>"
      and sc: "safe_formula \<chi> \<or> (case \<chi> of Formula.Neg \<chi>' \<Rightarrow> safe_formula \<chi>' | _ \<Rightarrow> False)"
      using sf unfolding Since by auto
    have R: "Formula.fv_list \<phi> = Formula.fv_list \<eta>"
      using s unfolding Since by (simp add: cols_union_subset)
    have bR: "\<forall>x \<in> Formula.fv \<eta>. x < length tys + n" using bp Since by simp
    have bL: "\<forall>x \<in> Formula.fv \<chi>. x < length tys + n" using bR s by auto
    have p2: "mok (length tys + n) (Formula.fv_list \<eta>) tw (minit0 (length tys + n) \<eta>)"
      by (rule Agg.IH[OF _ se bR]) (simp add: Since)
    show ?thesis
    proof (cases "safe_formula \<chi>")
      case True
      have p1: "mok (length tys + n) (Formula.fv_list \<chi>) tw (minit0 (length tys + n) \<chi>)"
        by (rule Agg.IH[OF _ True bL]) (simp add: Since)
      let ?args = "init_args I (length tys + n) (Formula.fv_list \<chi>) (Formula.fv_list \<eta>) True (Some ?ag)"
      have m: "minit0 n (Formula.Agg y \<omega> tys f \<phi>) = MSince ?args
          (minit0 (length tys + n) \<chi>) (minit0 (length tys + n) \<eta>) init_mbuf2S (init_mmasaux ?args)"
        using True unfolding Since by (simp add: Let_def default_mmasaux.init_since_def)
      show ?thesis unfolding m A
        by (rule MokSinceAgg[OF p1 p2 saux_inv_init _ _ _ _ _ g0 ks]) (simp_all add: init_args_def s)
    next
      case False
      then obtain \<chi>' where chi: "\<chi> = Formula.Neg \<chi>'" and sc': "safe_formula \<chi>'"
        using sc by (cases \<chi>) auto
      have fvc: "Formula.fv_list \<chi>' = Formula.fv_list \<chi>" using chi by simp
      have bL': "\<forall>x \<in> Formula.fv \<chi>'. x < length tys + n" using bL chi by simp
      have p1: "mok (length tys + n) (Formula.fv_list \<chi>) tw (minit0 (length tys + n) \<chi>')"
        unfolding fvc[symmetric] by (rule Agg.IH[OF _ sc' bL']) (simp add: Since chi)
      let ?args = "init_args I (length tys + n) (Formula.fv_list \<chi>') (Formula.fv_list \<eta>) False (Some ?ag)"
      have m: "minit0 n (Formula.Agg y \<omega> tys f \<phi>) = MSince ?args
          (minit0 (length tys + n) \<chi>') (minit0 (length tys + n) \<eta>) init_mbuf2S (init_mmasaux ?args)"
        using False chi unfolding Since by (simp add: Let_def default_mmasaux.init_since_def)
      show ?thesis unfolding m A fvc
        by (rule MokSinceAgg[OF p1 p2 saux_inv_init _ _ _ _ _ g0 ks]) (simp_all add: init_args_def s)
    qed
  next
    case (Until \<chi> I \<eta>)
    have s: "Formula.fv \<chi> \<subseteq> Formula.fv \<eta>" and se: "safe_formula \<eta>"
      and sc: "safe_formula \<chi> \<or> (case \<chi> of Formula.Neg \<chi>' \<Rightarrow> safe_formula \<chi>' | _ \<Rightarrow> False)"
      using sf unfolding Until by auto
    have R: "Formula.fv_list \<phi> = Formula.fv_list \<eta>"
      using s unfolding Until by (simp add: cols_union_subset)
    have bR: "\<forall>x \<in> Formula.fv \<eta>. x < length tys + n" using bp Until by simp
    have bL: "\<forall>x \<in> Formula.fv \<chi>. x < length tys + n" using bR s by auto
    have p2: "mok (length tys + n) (Formula.fv_list \<eta>) tw (minit0 (length tys + n) \<eta>)"
      by (rule Agg.IH[OF _ se bR]) (simp add: Until)
    show ?thesis
    proof (cases "safe_formula \<chi>")
      case True
      have p1: "mok (length tys + n) (Formula.fv_list \<chi>) tw (minit0 (length tys + n) \<chi>)"
        by (rule Agg.IH[OF _ True bL]) (simp add: Until)
      let ?args = "init_args I (length tys + n) (Formula.fv_list \<chi>) (Formula.fv_list \<eta>) True (Some ?ag)"
      have m: "minit0 n (Formula.Agg y \<omega> tys f \<phi>) = MUntil ?args
          (minit0 (length tys + n) \<chi>) (minit0 (length tys + n) \<eta>) ([], []) [] 0
          (init_muaux_dq ?args)"
        using True unfolding Until by (simp add: Let_def dq_muaux.init_until_def)
      show ?thesis unfolding m A
        by (rule MokUntilAgg[OF p1 p2 until_inv_init _ _ _ _ _ g0 ks]) (simp_all add: init_args_def s)
    next
      case False
      then obtain \<chi>' where chi: "\<chi> = Formula.Neg \<chi>'" and sc': "safe_formula \<chi>'"
        using sc by (cases \<chi>) auto
      have fvc: "Formula.fv_list \<chi>' = Formula.fv_list \<chi>" using chi by simp
      have bL': "\<forall>x \<in> Formula.fv \<chi>'. x < length tys + n" using bL chi by simp
      have p1: "mok (length tys + n) (Formula.fv_list \<chi>) tw (minit0 (length tys + n) \<chi>')"
        unfolding fvc[symmetric] by (rule Agg.IH[OF _ sc' bL']) (simp add: Until chi)
      let ?args = "init_args I (length tys + n) (Formula.fv_list \<chi>') (Formula.fv_list \<eta>) False (Some ?ag)"
      have m: "minit0 n (Formula.Agg y \<omega> tys f \<phi>) = MUntil ?args
          (minit0 (length tys + n) \<chi>') (minit0 (length tys + n) \<eta>) ([], []) [] 0
          (init_muaux_dq ?args)"
        using False chi unfolding Until by (simp add: Let_def dq_muaux.init_until_def)
      show ?thesis unfolding m A fvc
        by (rule MokUntilAgg[OF p1 p2 until_inv_init _ _ _ _ _ g0 ks]) (simp_all add: init_args_def s)
    qed
  qed (use D A in \<open>simp_all add: Let_def\<close>)
next
  case (Prev I \<phi>)
  have p: "mok n (Formula.fv_list \<phi>) tw (minit0 n \<phi>)"
    using Prev.prems by (intro Prev.IH) simp
  show ?case by (simp add: MokPrev[OF p])
next
  case (Next I \<phi>)
  have p: "mok n (Formula.fv_list \<phi>) tw (minit0 n \<phi>)"
    using Next.prems by (intro Next.IH) simp
  show ?case by (simp add: MokNext[OF p])
next
  case (Since \<phi> I \<psi>)
  note sub = \<open>Formula.fv \<phi> \<subseteq> Formula.fv \<psi>\<close>
  have b: "\<forall>x \<in> Formula.fv \<psi>. x < n" using Since.prems by simp
  have p1: "mok n (Formula.fv_list \<phi>) tw (minit0 n \<phi>)"
    using b sub by (intro Since.IH(1)) auto
  have p2: "mok n (Formula.fv_list \<psi>) tw (minit0 n \<psi>)" by (rule Since.IH(2)[OF b])
  let ?args = "init_args I n (Formula.fv_list \<phi>) (Formula.fv_list \<psi>) True None"
  have m: "minit0 n (Formula.Since \<phi> I \<psi>) =
      MSince ?args (minit0 n \<phi>) (minit0 n \<psi>) init_mbuf2S (init_mmasaux ?args)"
    using Since.hyps(2) by (simp add: default_mmasaux.init_since_def)
  have e: "Formula.fv_list (Formula.Since \<phi> I \<psi>) = Formula.fv_list \<psi>"
    using sub by (simp add: cols_union_subset)
  show ?case unfolding m e
    by (rule MokSince[OF p1 p2 saux_inv_init]) (simp_all add: init_args_def sub)
next
  case (Not_Since \<phi> I \<psi>)
  have sub: "Formula.fv \<phi> \<subseteq> Formula.fv \<psi>" using Not_Since.hyps(1) by simp
  have b: "\<forall>x \<in> Formula.fv \<psi>. x < n" using Not_Since.prems by simp
  have p1: "mok n (Formula.fv_list \<phi>) tw (minit0 n \<phi>)"
    using b sub by (intro Not_Since.IH(1)) auto
  have p2: "mok n (Formula.fv_list \<psi>) tw (minit0 n \<psi>)" by (rule Not_Since.IH(2)[OF b])
  let ?args = "init_args I n (Formula.fv_list \<phi>) (Formula.fv_list \<psi>) False None"
  have m: "minit0 n (Formula.Since (Formula.Neg \<phi>) I \<psi>) =
      MSince ?args (minit0 n \<phi>) (minit0 n \<psi>) init_mbuf2S (init_mmasaux ?args)"
    using Not_Since.hyps(3) by (simp add: default_mmasaux.init_since_def)
  have e: "Formula.fv_list (Formula.Since (Formula.Neg \<phi>) I \<psi>) = Formula.fv_list \<psi>"
    using sub by (simp add: cols_union_subset)
  show ?case unfolding m e
    by (rule MokSince[OF p1 p2 saux_inv_init]) (simp_all add: init_args_def sub)
next
  case (Until \<phi> I \<psi>)
  note sub = \<open>Formula.fv \<phi> \<subseteq> Formula.fv \<psi>\<close>
  have b: "\<forall>x \<in> Formula.fv \<psi>. x < n" using Until.prems by simp
  have p1: "mok n (Formula.fv_list \<phi>) tw (minit0 n \<phi>)"
    using b sub by (intro Until.IH(1)) auto
  have p2: "mok n (Formula.fv_list \<psi>) tw (minit0 n \<psi>)" by (rule Until.IH(2)[OF b])
  let ?args = "init_args I n (Formula.fv_list \<phi>) (Formula.fv_list \<psi>) True None"
  have m: "minit0 n (Formula.Until \<phi> I \<psi>) =
      MUntil ?args (minit0 n \<phi>) (minit0 n \<psi>) ([], []) [] 0 (init_muaux_dq ?args)"
    using Until.hyps(2) by (simp add: dq_muaux.init_until_def)
  have e: "Formula.fv_list (Formula.Until \<phi> I \<psi>) = Formula.fv_list \<psi>"
    using sub by (simp add: cols_union_subset)
  show ?case unfolding m e
    by (rule MokUntil[OF p1 p2 until_inv_init]) (simp_all add: init_args_def sub)
next
  case (Not_Until \<phi> I \<psi>)
  have sub: "Formula.fv \<phi> \<subseteq> Formula.fv \<psi>" using Not_Until.hyps(1) by simp
  have b: "\<forall>x \<in> Formula.fv \<psi>. x < n" using Not_Until.prems by simp
  have p1: "mok n (Formula.fv_list \<phi>) tw (minit0 n \<phi>)"
    using b sub by (intro Not_Until.IH(1)) auto
  have p2: "mok n (Formula.fv_list \<psi>) tw (minit0 n \<psi>)" by (rule Not_Until.IH(2)[OF b])
  let ?args = "init_args I n (Formula.fv_list \<phi>) (Formula.fv_list \<psi>) False None"
  have m: "minit0 n (Formula.Until (Formula.Neg \<phi>) I \<psi>) =
      MUntil ?args (minit0 n \<phi>) (minit0 n \<psi>) ([], []) [] 0 (init_muaux_dq ?args)"
    using Not_Until.hyps(3) by (simp add: dq_muaux.init_until_def)
  have e: "Formula.fv_list (Formula.Until (Formula.Neg \<phi>) I \<psi>) = Formula.fv_list \<psi>"
    using sub by (simp add: cols_union_subset)
  show ?case unfolding m e
    by (rule MokUntil[OF p1 p2 until_inv_init]) (simp_all add: init_args_def sub)
next
  case (Trigger_0 \<phi> I \<psi>)
  note m0 = \<open>mem I 0\<close>
  have sub: "Formula.fv \<phi> \<subseteq> Formula.fv \<psi>" using Trigger_0(3) .
  have b: "\<forall>x \<in> Formula.fv \<psi>. x < n" using Trigger_0.prems by simp
  have bp: "\<forall>x \<in> Formula.fv \<phi>. x < n" using b sub by auto
  have p2: "mok n (Formula.fv_list \<psi>) tw (minit0 n \<psi>)" by (rule Trigger_0(5)[OF b])
  have e: "Formula.fv_list (Formula.Trigger \<phi> I \<psi>) = Formula.fv_list \<psi>"
    using sub by (simp add: cols_union_subset)
  show ?case
  proof (cases "safe_formula \<phi>")
    case True
    have p1: "mok n (Formula.fv_list \<phi>) tw (minit0 n \<phi>)"
    proof (cases "\<forall>x. (\<forall>xa \<in> Formula.fv \<phi>. xa < x) \<longrightarrow> mok x (Formula.fv_list \<phi>) tw (minit0 x \<phi>)")
      case True then show ?thesis using bp by blast
    next
      case False
      then have "case \<phi> of Formula.Neg \<chi> \<Rightarrow> safe_formula \<chi> \<and>
          (\<forall>x. (\<forall>xa \<in> Formula.fv \<chi>. xa < x) \<longrightarrow> mok x (Formula.fv_list \<chi>) tw (minit0 x \<chi>))
        | _ \<Rightarrow> False"
        using Trigger_0(4) by blast
      then obtain \<chi> where phi: "\<phi> = Formula.Neg \<chi>" by (cases \<phi>) auto
      have "Formula.fv \<chi> = {}" using \<open>safe_formula \<phi>\<close> phi by simp
      then have "Formula.fv_list \<chi> = []" by (metis List.set_empty Formula.set_fvi_list)
      then show ?thesis using phi \<open>Formula.fv \<chi> = {}\<close> by (simp add: MokNeg)
    qed
    let ?args = "init_args I n (Formula.fv_list \<phi>) (Formula.fv_list \<psi>) True None"
    have m: "minit0 n (Formula.Trigger \<phi> I \<psi>) = MTrigger ?args
        (minit0 n \<phi>) (minit0 n \<psi>) ([], []) [] (init_mmtaux ?args)"
      using True by (simp add: verimon_maux.init_trigger_def)
    show ?thesis unfolding m e
      by (rule MokTrigger[OF p1 p2 trigger_inv_init]) (simp_all add: init_args_def m0 sub)
  next
    case False
    have "case \<phi> of Formula.Neg \<chi> \<Rightarrow> safe_formula \<chi> \<and>
        (\<forall>x. (\<forall>xa \<in> Formula.fv \<chi>. xa < x) \<longrightarrow> mok x (Formula.fv_list \<chi>) tw (minit0 x \<chi>))
      | _ \<Rightarrow> False"
      using Trigger_0(4) False by auto
    then obtain \<chi> where phi: "\<phi> = Formula.Neg \<chi>"
      and ih: "\<forall>x. (\<forall>xa \<in> Formula.fv \<chi>. xa < x) \<longrightarrow> mok x (Formula.fv_list \<chi>) tw (minit0 x \<chi>)"
      by (cases \<phi>) auto
    have fvc: "Formula.fv_list \<chi> = Formula.fv_list \<phi>" using phi by simp
    have p1: "mok n (Formula.fv_list \<phi>) tw (minit0 n \<chi>)"
      using ih bp phi unfolding fvc[symmetric] by simp
    let ?args = "init_args I n (Formula.fv_list \<chi>) (Formula.fv_list \<psi>) False None"
    have m: "minit0 n (Formula.Trigger \<phi> I \<psi>) = MTrigger ?args
        (minit0 n \<chi>) (minit0 n \<psi>) ([], []) [] (init_mmtaux ?args)"
      using False phi by (simp add: verimon_maux.init_trigger_def)
    show ?thesis unfolding m e fvc
      by (rule MokTrigger[OF p1 p2 trigger_inv_init])
        (use sub phi in \<open>simp_all add: init_args_def m0\<close>)
  qed
next
  case (Trigger \<phi> I \<psi>) then show ?case by simp
next
  case (Release_0 \<phi> I \<psi>)
  have sub: "Formula.fv \<phi> \<subseteq> Formula.fv \<psi>" using Release_0.hyps(4) .
  show ?case
    using Release_0.IH[OF Release_0.prems[unfolded release_fvi(1)]] Release_0.hyps(1)
    by (simp add: fv_list_release_safe_0[OF sub])
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
    unfolding fr using nth_mem by blast
  have b: "\<forall>x \<in> Formula.fv_regex r. x < n" using MatchP.prems by simp
  have pL: "\<forall>i < length \<phi>s. mok n (map Formula.fv_list \<phi>s ! i) tw (map (minit0 n) \<phi>s ! i)"
  proof (intro allI impI)
    fix i assume i: "i < length \<phi>s"
    have mem: "\<phi>s ! i \<in> safe_atms r" using nth_mem[OF i] at by blast
    have bi: "\<forall>x \<in> Formula.fv (\<phi>s ! i). x < n" using b sub i by auto
    show "mok n (map Formula.fv_list \<phi>s ! i) tw (map (minit0 n) \<phi>s ! i)"
      using MatchP.IH mem bi i by auto
  qed
  have m: "minit0 n (Formula.MatchP I r) = MMatchP I (Formula.fv_list (Formula.MatchP I r))
      (map Formula.fv_list \<phi>s) mr (sorted_list_of_set (RPDs mr)) (map (minit0 n) \<phi>s)
      (replicate (length \<phi>s) []) [] []"
    using tm by simp
  have A: "set (Formula.fv_list (Formula.MatchP I r)) = Formula.fv_regex (from_mregex mr \<phi>s)"
    unfolding Formula.set_fvi_list fm by simp
  show ?case unfolding m
    by (rule MokMatchP[OF sr[folded fm] ok A distinct_fvi_list])
      (use sub fm pL in \<open>simp_all add: finite_RPDs maux_inv_def\<close>)
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
    unfolding fr using nth_mem by blast
  have b: "\<forall>x \<in> Formula.fv_regex r. x < n" using MatchF.prems by simp
  have pL: "\<forall>i < length \<phi>s. mok n (map Formula.fv_list \<phi>s ! i) tw (map (minit0 n) \<phi>s ! i)"
  proof (intro allI impI)
    fix i assume i: "i < length \<phi>s"
    have mem: "\<phi>s ! i \<in> safe_atms r" using nth_mem[OF i] at by blast
    have bi: "\<forall>x \<in> Formula.fv (\<phi>s ! i). x < n" using b sub i by auto
    show "mok n (map Formula.fv_list \<phi>s ! i) tw (map (minit0 n) \<phi>s ! i)"
      using MatchF.IH mem bi i by auto
  qed
  have m: "minit0 n (Formula.MatchF I r) = MMatchF I (Formula.fv_list (Formula.MatchF I r))
      (map Formula.fv_list \<phi>s) mr (sorted_list_of_set (LPDs mr)) (map (minit0 n) \<phi>s)
      (replicate (length \<phi>s) []) [] 0 []"
    using tm by simp
  have A: "set (Formula.fv_list (Formula.MatchF I r)) = Formula.fv_regex (from_mregex mr \<phi>s)"
    unfolding Formula.set_fvi_list fm by simp
  show ?case unfolding m
    by (rule MokMatchF[OF sr[folded fm] ok A distinct_fvi_list])
      (use sub fm pL in \<open>simp_all add: finite_LPDs mfaux_inv_def\<close>)
next
  case (TP t)
  then show ?case by (cases t) (auto simp: mtrm_ecols_def intro!: MokTP)
next
  case (TS t)
  then show ?case by (cases t) (auto simp: mtrm_ecols_def intro!: MokTS)
qed

section \<open>The kernel's initial state, read off\<close>

text \<open>
  \<open>mok_minit0\<close> discharges the criterion for the state the kernel itself starts from; what
  remains for the theory that follows is to read that state's fields off @{const minit_safe}.
\<close>

lemma minit_safe_state:
  assumes "mmonitorable \<phi>"
  shows "mstate_n (minit_safe \<phi>) = Formula.nfv \<phi>"
    and "mstate_m (minit_safe \<phi>) = minit0 (Formula.nfv \<phi>) \<phi>"
    and "mstate_i (minit_safe \<phi>) = 0" and "mstate_j (minit_safe \<phi>) = 0"
    and "mstate_t (minit_safe \<phi>) = []"
  using assms[unfolded monitorable_formula_code]
  by (simp_all add: default_maux.minit_safe_def default_maux.minit_def Let_def)

(*<*)
end
(*>*)
