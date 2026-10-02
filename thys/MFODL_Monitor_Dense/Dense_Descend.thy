(*<*)
theory Dense_Descend
  imports Dense_Init
begin
(*>*)

section \<open>The descending compiler\<close>

text \<open>
  The dense evaluator's formula has a node for most, but not all, of the kernel's.  This theory
  builds the compiler that descends into a kernel formula and emits a dense node wherever the
  simulation has a rule for one, answering \<open>DFail\<close> at the constructors the dense fragment does
  not cover.  Nothing relates \<open>DFail\<close> to a kernel formula, so the theorems below hold of a
  compiled formula that has none -- which the caller checks with @{const vdfail_nodes}.

  The compiler is a plain function of the kernel's formula and the two column lists its result
  is to have: the kernel's, @{term ks}, and the dense one, @{term cs}, which is the ascending
  order of the same columns.  At every recursive call the kernel column list of the operand is
  read off the node itself -- the kernel's nodes store their operands' column lists -- and the
  dense one is its ascending order, @{term dcols}.  Wherever a node's own columns are determined
  by its operands', the compiler checks that they are the ones it was asked for.
\<close>

subsection \<open>The compiler\<close>

definition dcols :: "cols \<Rightarrow> cols" where
  "dcols k = set_cols (set k)"

text \<open>The positions in @{term cs} of the columns in @{term L}.  The compiler fuses an aggregation
  into the temporal operator below it only when the left operand's columns occupy none of the
  right operand's positions.\<close>

definition cpos :: "cols \<Rightarrow> nat set \<Rightarrow> nat set" where
  "cpos cs L = {i. i < length cs \<and> cs ! i \<in> L}"

lemma cpos_code[code]: "cpos cs L = set (filter (\<lambda>i. cs ! i \<in> L) [0..<length cs])"
  by (auto simp: cpos_def)

definition dagg_gcols :: "aggargs \<Rightarrow> cols" where
  "dagg_gcols args = map (\<lambda>c. c - length (aggargs_tys args))
     (drop (length (aggargs_tys args)) (dcols (aggargs_cols args)))"

text \<open>The width a temporal structure runs at: its own, or -- with an aggregation fused into it --
  the operand's, which is wider by the bound variables the aggregation ranges over.\<close>

definition dnode_n :: "nat \<Rightarrow> args \<Rightarrow> nat" where
  "dnode_n n args = (case args_agg args of None \<Rightarrow> n
     | Some ag \<Rightarrow> length (aggargs_tys ag) + aggargs_n ag)"

function (sequential) dof ::
    "nat \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> (mmasaux, muaux_dq, event_data mmtaux) mformula \<Rightarrow> dformula" where
  "dof n ks cs (MRel rel) = DRel (dtabc ks cs rel)"
| "dof n ks cs (MPred e tms mode) =
     (if mode = Match then (if ks = pred_cols tms then DPredM e (length tms) tms cs else DFail)
      else if (mode = Copy \<and> tms = map Formula.Var [0..<length tms] \<and> ks = [0..<length tms] \<and> cs = ks)
           \<or> (mode = Simple \<and> is_simple_pattern tms 0 \<and> cs = smp_cols tms \<and> ks = cs)
      then DPredS e (length tms)
      else DFail)"
| "dof n ks cs (MAndRel k \<phi> conf) =
     (if k = ks \<and> Formula.fv_trm (fst conf) \<subseteq> set cs \<and> Formula.fv_trm (snd (snd (snd conf))) \<subseteq> set cs
      then DAndRel (dof n ks cs \<phi>) (reindex_constraint cs conf)
      else DFail)"
| "dof n ks cs (MNeg \<phi>) =
     (if ks = [] \<and> cs = [] then DNeg (dof n [] [] \<phi>) else DFail)"
| "dof n ks cs (MExists kks \<phi>) =
     (let ccs = dcols kks in
      if ks = ex_cols kks \<and> cs = dex_cols ccs
      then DExists (dof (Suc n) kks ccs \<phi>) (ex_drop0 ccs) else DFail)"
| "dof n ks cs (MOr k1 \<phi> k2 \<psi> buf) =
     (if k1 = ks \<and> set k2 = set ks \<and> buf = ([], [])
      then DOr (dof n ks cs \<phi>) (dof n k2 cs \<psi>) ([], []) else DFail)"
| "dof n ks cs (MAnd k1 \<phi> pos k2 \<psi> buf) =
     (let c1 = dcols k1; c2 = dcols k2 in
      if ks = cols_union k1 k2 \<and> cs = merge_cols c1 c2 \<and> (pos \<or> set k2 \<subseteq> set k1) \<and> buf = ([], [])
      then DAnd (mk_djoin c1 c2) (dof n k1 c1 \<phi>) pos (dof n k2 c2 \<psi>) ([], [])
      else DFail)"
| "dof n ks cs (MPrev I \<phi> first buf nts) =
     (if buf = [] then DPrev I (dof n ks cs \<phi>) first [] nts else DFail)"
| "dof n ks cs (MNext I \<phi> first nts) = DNext I (dof n ks cs \<phi>) first nts"
| "dof n ks cs (MAnds k kpos kneg L buf) =
     (case kpos of [] \<Rightarrow> DFail
      | k0 # kss \<Rightarrow>
        (let c0 = dcols k0; css = map dcols kss; nss = map dcols kneg in
         if k = ks \<and> cs = dands_cols c0 css \<and> length L = length kpos + length kneg \<and>
            length buf = length L \<and> (\<forall>b \<in> set buf. b = []) \<and>
            (\<forall>c \<in> set nss. set c \<subseteq> set (dands_cols c0 css))
         then DAnds (dands_plans c0 css) (dands_plans (dands_cols c0 css) nss)
                (map (\<lambda>(k, \<phi>). dof n k (dcols k) \<phi>) (zip (kpos @ kneg) L)) (map (\<lambda>_. []) L)
         else DFail))"
| "dof n ks cs (MAgg args \<phi>) =
     (let m = length (aggargs_tys args); k0 = aggargs_cols args; g = dagg_gcols args;
          y = aggargs_y args in
      if ks = y # shift_cols m k0 \<and> cs = merge_cols g [y] \<and> dcols k0 = agg_cols m g \<and>
         y \<notin> set g \<and> (aggargs_g0 args \<longrightarrow> g = []) \<and> Formula.fv_trm (aggargs_f args) \<subseteq> set k0
      then DAgg (aggargs_g0 args) (aggargs_\<omega> args)
             (reindex_trm (agg_cols m g) (aggargs_f args)) m (ins_pos g y)
             (dof (m + n) k0 (agg_cols m g) \<phi>)
      else DFail)"
| "dof n ks cs (MSince args \<phi> \<psi> buf aux) =
     (let kL = args_L args; kR = args_R args; cL = dcols kL; cR = dcols kR;
          \<phi>d = dof (args_n args) kL cL \<phi>; \<psi>d = dof (args_n args) kR cR \<psi> in
      case args_agg args of
        None \<Rightarrow>
          (if args_n args = n \<and> ks = kR \<and> cs = cR \<and> set kL \<subseteq> set kR \<and> buf = init_mbuf2S
           then DSince (dargs cR cL args) \<phi>d \<psi>d init_mbuf2S
                  (dsx_init (dargs cR cL args) (dmsk cR cL))
           else DFail)
      | Some ag \<Rightarrow>
          (let m = length (aggargs_tys ag); g = dagg_gcols ag; y = aggargs_y ag in
           if aggargs_cols ag = kR \<and> set kL \<subseteq> set kR \<and> buf = init_mbuf2S \<and>
              agg_cols m g = cR \<and> ks = y # shift_cols m kR \<and> cs = merge_cols g [y] \<and>
              y \<notin> set g \<and> (aggargs_g0 ag \<longrightarrow> g = []) \<and> Formula.fv_trm (aggargs_f ag) \<subseteq> set kR
           then (if cpos cR (set cL) = {}
                 then DSince (dargs cR cL args) \<phi>d \<psi>d init_mbuf2S
                        (dsx_init_agg (dargs cR cL args)
                          (aggargs_g0 ag, aggargs_\<omega> ag, reindex_trm cR (aggargs_f ag),
                           m, ins_pos g y))
                 else DAgg (aggargs_g0 ag) (aggargs_\<omega> ag) (reindex_trm cR (aggargs_f ag))
                        m (ins_pos g y)
                        (DSince (dargs cR cL args) \<phi>d \<psi>d init_mbuf2S
                          (dsx_init (dargs cR cL args) (dmsk cR cL))))
           else DFail))"
| "dof n ks cs (MUntil args \<phi> \<psi> buf nts t aux) =
     (let kL = args_L args; kR = args_R args; cL = dcols kL; cR = dcols kR;
          \<phi>d = dof (args_n args) kL cL \<phi>; \<psi>d = dof (args_n args) kR cR \<psi> in
      case args_agg args of
        None \<Rightarrow>
          (if args_n args = n \<and> ks = kR \<and> cs = cR \<and> set kL \<subseteq> set kR \<and>
              buf = ([], []) \<and> nts = [] \<and> t = 0
           then DUntil (dargs cR cL args) (dmsk cR cL) \<phi>d \<psi>d ([], []) [] 0
                  (dux_init (dargs cR cL args))
           else DFail)
      | Some ag \<Rightarrow>
          (let m = length (aggargs_tys ag); g = dagg_gcols ag; y = aggargs_y ag in
           if aggargs_cols ag = kR \<and> set kL \<subseteq> set kR \<and> buf = ([], []) \<and> nts = [] \<and> t = 0 \<and>
              agg_cols m g = cR \<and> ks = y # shift_cols m kR \<and> cs = merge_cols g [y] \<and>
              y \<notin> set g \<and> (aggargs_g0 ag \<longrightarrow> g = []) \<and> Formula.fv_trm (aggargs_f ag) \<subseteq> set kR
           then (if cpos cR (set cL) = {} \<and> memL (args_ivl args) 0
                 then DUntil (dargs cR cL args) (dmsk cR cL) \<phi>d \<psi>d ([], []) [] 0
                        (dux_init_agg (dargs cR cL args)
                          (aggargs_g0 ag, aggargs_\<omega> ag, reindex_trm cR (aggargs_f ag),
                           m, ins_pos g y))
                 else DAgg (aggargs_g0 ag) (aggargs_\<omega> ag) (reindex_trm cR (aggargs_f ag))
                  m (ins_pos g y)
                  (DUntil (dargs cR cL args) (dmsk cR cL) \<phi>d \<psi>d ([], []) [] 0
                    (dux_init (dargs cR cL args))))
           else DFail))"
| "dof n ks cs (MAndAssign k0 \<phi> conf) =
     (let y = fst conf; t = snd conf; c0 = dcols k0 in
      if ks = k0 @ [y] \<and> y \<notin> set k0 \<and> Formula.fv_trm t \<subseteq> set c0 \<and> cs = merge_cols c0 [y]
      then DAndAssign (ins_pos c0 y) (reindex_trm c0 t) (dof n k0 c0 \<phi>)
      else DFail)"
| "dof n ks cs (MLet p m kks \<phi> \<psi>) =
     (if dcols kks = [0..<m] then DLet p m (dof m kks [0..<m] \<phi>) (dof n ks cs \<psi>) else DFail)"
| "dof n ks cs (MFrz p m kks \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L) =
     (if dcols kks = [0..<m] \<and> \<alpha>s = [] \<and> rb = []
      then DFrz p m (dof m kks [0..<m] \<phi>) (dof n ks cs \<psi>) jfrz jpsi0 jphi []
        (dof n ks cs \<rho>) w pR tq [] d po ng lv (dof n ks cs \<rho>L) else DFail)"
| "dof n ks cs (MLetPast p m kks \<phi> \<psi> i buf) =
     (if dcols kks = [0..<m] \<and> buf = None
      then DLetPast p m (dof m kks [0..<m] \<phi>) (dof n ks cs \<psi>) i None else DFail)"
| "dof n ks cs (MTrigger args \<phi> \<psi> buf nts aux) =
     (let kL = args_L args; kR = args_R args; cL = dcols kL in
      if ks = kR \<and> cs = dcols kR \<and> set kL \<subseteq> set kR \<and> mem (args_ivl args) 0 \<and>
         buf = ([], []) \<and> nts = []
      then DTrigger (dargs cs cL args) (emb_plan cs cL)
             (dof n kL cL \<phi>) (dof n kR cs \<psi>) ([], []) []
             (ginit_mmtaux (dargs cs cL args) (dmsk cs cL))
      else DFail)"
| "dof n ks cs (MAndTrigger k \<alpha> buf1 args \<phi> \<psi> buf2 nts aux) =
     (let kL = args_L args; kR = args_R args; cR = dcols kR; cL = dcols kL in
      if k = ks \<and> set kR \<subseteq> set ks \<and> set kL \<subseteq> set kR \<and>
         tok cR cL args \<and> buf1 = ([], []) \<and> buf2 = ([], []) \<and> nts = []
      then DAndTrigger (mk_djoin cs cR) (dof n ks cs \<alpha>) ([], []) (dargs cR cL args)
             (dof n kL cL \<phi>) (dof n kR cR \<psi>) ([], []) []
             (ginit_mmtaux (dargs cR cL args) (dmsk cR cL))
      else DFail)"
| "dof n ks cs (MMatchP I k dss mr mrs L buf nts aux) =
     (let css = map dcols dss in
      if k = ks \<and> length dss = length L \<and> length buf = length L \<and> (\<forall>b \<in> set buf. b = []) \<and>
         aux = [] \<and> (\<forall>c \<in> set css. set c \<subseteq> set cs)
      then DMatchP (length cs) I mr mrs (map (emb_plan cs) css)
             (map (\<lambda>(k, \<phi>). dof n k (dcols k) \<phi>) (zip dss L)) (map (\<lambda>_. []) L) nts []
      else DFail)"
| "dof n ks cs (MMatchF I k dss mr mrs L buf nts t aux) =
     (let css = map dcols dss in
      if k = ks \<and> length dss = length L \<and> length buf = length L \<and> (\<forall>b \<in> set buf. b = []) \<and>
         aux = [] \<and> (\<forall>c \<in> set css. set c \<subseteq> set cs)
      then DMatchF (length cs) I mr mrs (map (emb_plan cs) css)
             (map (\<lambda>(k, \<phi>). dof n k (dcols k) \<phi>) (zip dss L)) (map (\<lambda>_. []) L) nts t []
      else DFail)"
| "dof n ks cs (MTP mt i) = (if ks = mtrm_dcols mt \<and> cs = ks then DTP mt i else DFail)"
| "dof n ks cs (MTS mt) = (if ks = mtrm_dcols mt \<and> cs = ks then DTS mt else DFail)"
  by pat_completeness (simp_all only: prod.inject mformula.inject mformula.distinct simp_thms)

termination dof
  by (relation "measure (\<lambda>(n, ks, cs, \<phi>). size \<phi>)")
    (auto simp: termination_simp dest!: set_zip_rightD)

subsection \<open>Column lists in ascending order\<close>

lemma set_dcols[simp]: "set (dcols k) = set k"
  by (simp add: dcols_def set_cols)

lemma sorted_dcols: "sorted_wrt (<) (dcols k)"
  by (simp add: dcols_def set_cols)

lemma dcols_Nil[simp]: "dcols [] = []"
  by (simp add: dcols_def set_cols_empty)

lemma dframe_dcols: "distinct k \<Longrightarrow> dframe k (dcols k)"
  by (simp add: dcols_def dframe_set_cols)

lemma dcols_cong: "set k = set k' \<Longrightarrow> dcols k = dcols k'"
  by (simp add: dcols_def)

lemma dcols_eqI: "sorted_wrt (<) c \<Longrightarrow> set c = set k \<Longrightarrow> dcols k = c"
  unfolding dcols_def by (rule set_cols_eqI[symmetric]) simp_all

lemma dcols_upt: "set k = {0..<m} \<Longrightarrow> dcols k = [0..<m]"
  by (simp add: dcols_def set_cols_upt)

lemma dframe_fv_list: "dframe (Formula.fv_list \<phi>) (dcols (Formula.fv_list \<phi>))"
  by (rule dframe_dcols[OF distinct_fvi_list])

subsection \<open>The nodes the dense fragment does not cover\<close>

lemma produces_minit0:
  assumes "safe_formula \<phi>" and "\<forall>x \<in> Formula.fv \<phi>. x < n"
  shows "produces n (Formula.fv_list \<phi>) tw (minit0 n \<phi>)"
  by (rule mok_produces[OF mok_minit0[OF assms]])

text \<open>
  @{const dof} is total, and answers @{const DFail} where it has no dense node or where a check
  fails.  Nothing relates @{const DFail} to a kernel formula, so every statement below is
  conditional on the compiled formula containing none of them -- @{term "dofz n \<phi>"} -- and each
  check of the compiler is then available as a fact.
\<close>

abbreviation (input) dofc :: "nat \<Rightarrow> ts \<Rightarrow> ty Formula.formula \<Rightarrow> bool" where
  "dofc n tw \<phi> \<equiv> dsim n (Formula.fv_list \<phi>) (dcols (Formula.fv_list \<phi>)) tw
     (dof n (Formula.fv_list \<phi>) (dcols (Formula.fv_list \<phi>)) (minit0 n \<phi>)) (minit0 n \<phi>)"

abbreviation (input) dofz :: "nat \<Rightarrow> ty Formula.formula \<Rightarrow> bool" where
  "dofz n \<phi> \<equiv> vdfail_nodes (dof n (Formula.fv_list \<phi>) (dcols (Formula.fv_list \<phi>)) (minit0 n \<phi>)) = 0"

lemma dof_check:
  assumes "vdfail_nodes (dof n ks cs \<phi>) = 0" and "\<not> P \<Longrightarrow> dof n ks cs \<phi> = DFail"
  shows P
  using assms by (cases P) auto

lemma mok_MRelD: "mok n ks tw (mformula.MRel rel) \<Longrightarrow> ftable ks rel"
  by (cases rule: mok.cases) auto

lemma dsim_dof_minit0_rel:
  assumes s: "safe_formula \<phi>" and b: "\<forall>x \<in> Formula.fv \<phi>. x < n"
    and m: "minit0 n \<phi> = mformula.MRel rel"
  shows "dofc n tw \<phi>"
proof -
  have mk: "mok n (Formula.fv_list \<phi>) tw (mformula.MRel rel)"
    using mok_minit0[OF s b] unfolding m .
  show ?thesis unfolding m dof.simps
    by (rule DsRel[OF dframe_fv_list mok_produces[OF mk]])
      (use mok_MRelD[OF mk] in simp)
qed

subsection \<open>The temporal structures' initial states\<close>

lemma dsince_rel_init:
  assumes a: "args = init_args I n kL kR pos agg"
    and fR: "dframe kR cR" and fL: "dframe kL cL" and sub: "set kL \<subseteq> set kR"
  shows "dsince_rel kR cR kL cL args tw (init_mmasaux args)
     (dsx_init (dargs cR cL args) (dmsk cR cL)) init_mbuf2S init_mbuf2S"
proof -
  have v: "valid_mmasaux args 0 (init_mmasaux args) []"
    unfolding a by (rule valid_init_mmasaux[OF sub dframeD(1)[OF fL] dframeD(1)[OF fR]])
  have s: "dsxaux' kR cR cL args 0 (dsx_init (dargs cR cL args) (dmsk cR cL)) []"
    by (rule dsxaux'_init[OF fR fL sub])
  show ?thesis using dsince_relI[OF v s, where tw = tw and kL = kL and xs = "[]" and ys = "[]" and tss = "[]"
      and sk = False] by (simp only: list.map list.pred_inject sorted0 list.set(1) empty_iff ball_empty le0
        simp_thms)
qed

lemma dsince_rel_init_agg:
  assumes a: "args = init_args I n kL kR pos agg"
    and fR: "dframe kR cR" and fL: "dframe kL cL" and sub: "set kL \<subseteq> set kR"
    and c: "cL = []" and ok: "dagg_ok p (length cR)"
  shows "dsince_rel kR cR kL cL args tw (init_mmasaux args)
     (dsx_init_agg (dargs cR cL args) p) init_mbuf2S init_mbuf2S"
proof -
  have v: "valid_mmasaux args 0 (init_mmasaux args) []"
    unfolding a by (rule valid_init_mmasaux[OF sub dframeD(1)[OF fL] dframeD(1)[OF fR]])
  have s: "dsxaux' kR cR cL args 0 (dsx_init_agg (dargs cR cL args) p) []"
    by (rule dsxaux'_init_agg[OF c ok])
  show ?thesis using dsince_relI[OF v s, where tw = tw and kL = kL and xs = "[]" and ys = "[]" and tss = "[]"
      and sk = False] by (simp only: list.map list.pred_inject sorted0 list.set(1) empty_iff ball_empty le0
        simp_thms)
qed

lemma duntil_rel_init:
  assumes a: "args = init_args I n kL kR pos agg"
    and fR: "dframe kR cR" and fL: "dframe kL cL" and sub: "set kL \<subseteq> set kR"
  shows "duntil_rel kR cR kL cL args tw 0 (init_muaux_dq args)
     (dux_init (dargs cR cL args)) ([], []) ([], []) []"
proof -
  have v: "valid_muaux_dq args 0 (init_muaux_dq args) []"
    unfolding a by (rule valid_init_muaux_dq[OF sub dframeD(1)[OF fL] dframeD(1)[OF fR]])
  have s: "duxaux' kL cL kR cR args 0 (dux_init (dargs cR cL args)) []"
    by (rule duxaux'_init[OF fR fL sub])
  show ?thesis unfolding duntil_rel_def duaux_rel_def using v s by auto
qed

lemma duntil_rel_init_agg:
  assumes a: "args = init_args I n kL kR pos agg"
    and fR: "dframe kR cR" and fL: "dframe kL cL" and sub: "set kL \<subseteq> set kR"
    and c: "cL = []" and inz: "memL (args_ivl args) 0" and ok: "dagg_ok p (length cR)"
  shows "duntil_rel kR cR kL cL args tw 0 (init_muaux_dq args)
     (dux_init_agg (dargs cR cL args) p) ([], []) ([], []) []"
proof -
  have v: "valid_muaux_dq args 0 (init_muaux_dq args) []"
    unfolding a by (rule valid_init_muaux_dq[OF sub dframeD(1)[OF fL] dframeD(1)[OF fR]])
  have s: "duxaux' kL cL kR cR args 0 (dux_init_agg (dargs cR cL args) p) []"
    by (rule duxaux'_init_agg[OF c inz ok])
  show ?thesis unfolding duntil_rel_def duaux_rel_def using v s by auto
qed

lemma dtrigger_rel_init:
  assumes a: "args = init_args I n kL kR pos agg"
    and fR: "dframe kR cR" and fL: "dframe kL cL" and sub: "set kL \<subseteq> set kR"
    and ok: "tok cR cL args"
  shows "dtrigger_rel kR cR kL cL args tw (init_mmtaux args)
     (ginit_mmtaux (dargs cR cL args) (dmsk cR cL)) ([], []) ([], []) []"
proof -
  have i: "args_ivl args = I" and p: "args_pos args = pos" unfolding a by (simp_all add: init_args_def)
  have e: "cL = cR \<Longrightarrow> set kL = set kR" using dframeD(3)[OF fR] dframeD(3)[OF fL] by auto
  have v: "valid_mmtaux args 0 (init_mmtaux args) []"
    using valid_init_mmtaux[of I kL kR pos n agg] ok sub e dframeD(1)[OF fL] dframeD(1)[OF fR]
    unfolding a by (auto simp: tok_def init_args_def Let_def split: if_splits)
  have d: "dtaux kL cL kR cR args 0 (ginit_mmtaux (dargs cR cL args) (dmsk cR cL)) []"
    by (rule dtaux_init[OF fR fL sub ok])
  have "dtrigger_rel kR cR kL cL args tw (init_mmtaux args)
      (ginit_mmtaux (dargs cR cL args) (dmsk cR cL)) ([], [])
      (map (dtabc kL cL) [], map (dtabc kR cR) []) []"
    by (rule dtrigger_relI[OF v _ d]) simp_all
  then show ?thesis by (simp only: list.map)
qed

lemma dof_since_z:
  assumes "vdfail_nodes (dof n ks cs (MSince args \<phi> \<psi> buf aux)) = 0"
  shows "vdfail_nodes (dof (args_n args) (args_L args) (dcols (args_L args)) \<phi>) = 0"
    and "vdfail_nodes (dof (args_n args) (args_R args) (dcols (args_R args)) \<psi>) = 0"
  using assms by (cases "args_agg args"; auto simp: Let_def split: if_splits)+

lemma dof_until_z:
  assumes "vdfail_nodes (dof n ks cs (MUntil args \<phi> \<psi> buf nts t aux)) = 0"
  shows "vdfail_nodes (dof (args_n args) (args_L args) (dcols (args_L args)) \<phi>) = 0"
    and "vdfail_nodes (dof (args_n args) (args_R args) (dcols (args_R args)) \<psi>) = 0"
  using assms by (cases "args_agg args"; auto simp: Let_def split: if_splits)+

lemma dsim_dof_since:
  assumes a: "args = init_args I n kL kR pos None"
    and pr: "produces n kR tw (MSince args \<phi> \<psi> init_mbuf2S (init_mmasaux args))"
    and s1: "dsim n kL (dcols kL) tw (dof n kL (dcols kL) \<phi>) \<phi>"
    and s2: "dsim n kR (dcols kR) tw (dof n kR (dcols kR) \<psi>) \<psi>"
    and dL: "distinct kL" and dR: "distinct kR" and sub: "set kL \<subseteq> set kR"
  shows "dsim n kR (dcols kR) tw (dof n kR (dcols kR) (MSince args \<phi> \<psi> init_mbuf2S (init_mmasaux args)))
     (MSince args \<phi> \<psi> init_mbuf2S (init_mmasaux args))"
proof -
  have ag: "args_agg args = None" "args_n args = n" "args_L args = kL" "args_R args = kR"
    unfolding a by (simp_all add: init_args_def)
  have rl: "dsince_rel kR (dcols kR) kL (dcols kL) args tw (init_mmasaux args)
      (dsx_init (dargs (dcols kR) (dcols kL) args) (dmsk (dcols kR) (dcols kL)))
      init_mbuf2S init_mbuf2S"
    by (rule dsince_rel_init[OF a dframe_dcols[OF dR] dframe_dcols[OF dL] sub])
  show ?thesis
    by (simp add: ag sub Let_def del: init_mmasaux.simps)
      (rule DsSince[OF dframe_dcols[OF dR] pr _ _ sub ag(1,3,4) refl rl], use s1 s2 in \<open>simp_all add: ag\<close>)
qed

lemma dsim_dof_until:
  assumes a: "args = init_args I n kL kR pos None"
    and pr: "produces n kR tw (MUntil args \<phi> \<psi> ([], []) [] 0 (init_muaux_dq args))"
    and s1: "dsim n kL (dcols kL) tw (dof n kL (dcols kL) \<phi>) \<phi>"
    and s2: "dsim n kR (dcols kR) tw (dof n kR (dcols kR) \<psi>) \<psi>"
    and dL: "distinct kL" and dR: "distinct kR" and sub: "set kL \<subseteq> set kR"
  shows "dsim n kR (dcols kR) tw (dof n kR (dcols kR) (MUntil args \<phi> \<psi> ([], []) [] 0 (init_muaux_dq args)))
     (MUntil args \<phi> \<psi> ([], []) [] 0 (init_muaux_dq args))"
proof -
  have ag: "args_agg args = None" "args_n args = n" "args_L args = kL" "args_R args = kR"
    unfolding a by (simp_all add: init_args_def)
  have rl: "duntil_rel kR (dcols kR) kL (dcols kL) args tw 0 (init_muaux_dq args)
      (dux_init (dargs (dcols kR) (dcols kL) args)) ([], []) ([], []) []"
    by (rule duntil_rel_init[OF a dframe_dcols[OF dR] dframe_dcols[OF dL] sub])
  show ?thesis
    by (simp add: ag sub Let_def)
      (rule DsUntil[OF dframe_dcols[OF dR] pr _ _ sub ag(1,3,4) refl refl rl], use s1 s2 in \<open>simp_all add: ag\<close>)
qed

lemma dsim_dof_neg:
  assumes fv: "Formula.fv \<phi> = {}" and sf: "safe_formula \<phi>"
    and b: "\<forall>x \<in> Formula.fv (Formula.Neg \<phi>). x < n" and z: "dofz n (Formula.Neg \<phi>)"
    and ih: "dofz n \<phi> \<Longrightarrow> dofc n tw \<phi>"
  shows "dofc n tw (Formula.Neg \<phi>)"
proof -
  have e: "Formula.fv_list \<phi> = []" using fv by (metis List.set_empty Formula.set_fvi_list)
  have s: "dofc n tw \<phi>" using z fv e by (intro ih) simp
  have pr: "produces n (Formula.fv_list (Formula.Neg \<phi>)) tw (minit0 n (Formula.Neg \<phi>))"
    using produces_minit0[of "Formula.Neg \<phi>" n tw] b sf fv by simp
  show ?thesis using s pr fv e by (auto intro!: DsNeg)
qed

lemma dof_trigger_z:
  assumes "vdfail_nodes (dof n ks cs (MTrigger args \<phi> \<psi> buf nts aux)) = 0"
  shows "vdfail_nodes (dof n (args_L args) (dcols (args_L args)) \<phi>) = 0"
    and "vdfail_nodes (dof n (args_R args) (dcols (args_R args)) \<psi>) = 0"
  using assms by (auto simp: Let_def split: if_splits)

lemma dsim_dof_trigger:
  assumes a: "args = init_args I n kL kR pos None" and m0: "mem I 0"
    and pr: "produces n kR tw (MTrigger args \<phi> \<psi> ([], []) [] (init_mmtaux args))"
    and s1: "dsim n kL (dcols kL) tw (dof n kL (dcols kL) \<phi>) \<phi>"
    and s2: "dsim n kR (dcols kR) tw (dof n kR (dcols kR) \<psi>) \<psi>"
    and dL: "distinct kL" and dR: "distinct kR" and sub: "set kL \<subseteq> set kR"
  shows "dsim n kR (dcols kR) tw (dof n kR (dcols kR) (MTrigger args \<phi> \<psi> ([], []) [] (init_mmtaux args)))
     (MTrigger args \<phi> \<psi> ([], []) [] (init_mmtaux args))"
proof -
  have ag: "args_L args = kL" "args_R args = kR" "args_ivl args = I"
    unfolding a by (simp_all add: init_args_def)
  have ok: "tok (dcols kR) (dcols kL) args" by (rule tok_mem0) (simp add: ag m0)
  have rl: "dtrigger_rel kR (dcols kR) kL (dcols kL) args tw (init_mmtaux args)
      (ginit_mmtaux (dargs (dcols kR) (dcols kL) args) (dmsk (dcols kR) (dcols kL)))
      ([], []) ([], []) []"
    by (rule dtrigger_rel_init[OF a dframe_dcols[OF dR] dframe_dcols[OF dL] sub ok])
  show ?thesis
    by (simp add: ag sub m0 Let_def)
      (rule DsTrigger[OF dframe_dcols[OF dR] pr s1 s2 sub ag(1,2) _ refl refl rl], simp add: ag m0)
qed

lemma dsim_dof_minit0_trigger:
  assumes m0: "mem I 0" and sp: "safe_formula \<phi>" and sub: "Formula.fv \<phi> \<subseteq> Formula.fv \<psi>"
    and sft: "safe_formula (Formula.Trigger \<phi> I \<psi>)"
    and b: "\<forall>x \<in> Formula.fv (Formula.Trigger \<phi> I \<psi>). x < n" and z: "dofz n (Formula.Trigger \<phi> I \<psi>)"
    and i1: "dofz n \<phi> \<Longrightarrow> dofc n tw \<phi>" and i2: "dofz n \<psi> \<Longrightarrow> dofc n tw \<psi>"
  shows "dofc n tw (Formula.Trigger \<phi> I \<psi>)"
proof -
  let ?args = "init_args I n (Formula.fv_list \<phi>) (Formula.fv_list \<psi>) True None"
  have e: "Formula.fv_list (Formula.Trigger \<phi> I \<psi>) = Formula.fv_list \<psi>"
    using sub by (simp add: cols_union_subset)
  have m: "minit0 n (Formula.Trigger \<phi> I \<psi>) = MTrigger ?args
      (minit0 n \<phi>) (minit0 n \<psi>) ([], []) [] (init_mmtaux ?args)"
    using sp by (simp add: verimon_maux.init_trigger_def)
  note zz = dof_trigger_z[OF z[unfolded m e]]
  have s1: "dofc n tw \<phi>" using zz(1) by (intro i1) (simp add: init_args_def)
  have s2: "dofc n tw \<psi>" using zz(2) by (intro i2) (simp add: init_args_def)
  have pr: "produces n (Formula.fv_list \<psi>) tw
      (MTrigger ?args (minit0 n \<phi>) (minit0 n \<psi>) ([], []) [] (init_mmtaux ?args))"
    using produces_minit0[OF sft b, of tw] unfolding m e .
  show ?thesis unfolding m e
    by (rule dsim_dof_trigger[OF refl m0 pr s1 s2 distinct_fvi_list distinct_fvi_list])
      (simp add: sub)
qed

subsection \<open>The compiler produces a simulation\<close>

theorem dsim_dof_minit0:
  "safe_formula \<phi> \<Longrightarrow> \<forall>x \<in> Formula.fv \<phi>. x < n \<Longrightarrow> dofz n \<phi> \<Longrightarrow> dofc n tw \<phi>"
proof (induction arbitrary: n rule: safe_formula_induct)
  case (Eq_Const c d)
  show ?case by (rule dsim_dof_minit0_rel[OF _ Eq_Const.prems(1)]) simp_all
next
  case (Eq_Var1 c x)
  show ?case by (rule dsim_dof_minit0_rel[OF _ Eq_Var1.prems(1)]) simp_all
next
  case (Eq_Var2 c x)
  show ?case by (rule dsim_dof_minit0_rel[OF _ Eq_Var2.prems(1)]) simp_all
next
  case (Pred e ts)
  have pr: "produces n (Formula.fv_list (Formula.Pred e ts)) tw (minit0 n (Formula.Pred e ts))"
    using produces_minit0[of "Formula.Pred e ts" n tw] Pred by simp
  show ?case using Pred.prems(2) pr dframe_fv_list[of "Formula.Pred e ts"]
    by (cases "pred_mode_of n ts") (auto split: if_splits intro: dsim.intros)
next
  case (Let p \<phi> \<psi>)
  have c: "dcols (Formula.fv_list \<phi>) = [0..<Formula.nfv \<phi>]"
    by (rule dcols_upt) (use Let.hyps(1) fvi_less_nfv[of \<phi>] in auto)
  have z1: "dofz (Formula.nfv \<phi>) \<phi>" and z2: "dofz n \<psi>"
    using Let.prems(2) unfolding c by (simp_all split: if_splits)
  have s1: "dofc (Formula.nfv \<phi>) tw \<phi>" by (rule Let.IH(1)[OF fvi_less_nfv z1])
  have s2: "dofc n tw \<psi>" using Let.prems(1) z2 by (intro Let.IH(2)) simp_all
  have pr: "produces n (Formula.fv_list (Formula.Let p \<phi> \<psi>)) tw (minit0 n (Formula.Let p \<phi> \<psi>))"
    using produces_minit0[of "Formula.Let p \<phi> \<psi>" n tw] Let by simp
  show ?case using s1[unfolded c] s2 pr dframe_fv_list[of \<psi>] c by (auto intro!: DsLet)
next
  case (Frz p \<phi> \<psi>)
  have c: "dcols (Formula.fv_list \<phi>) = [0..<Formula.nfv \<phi>]"
    by (rule dcols_upt) (use Frz.hyps(1) fvi_less_nfv[of \<phi>] in auto)
  have z1: "dofz (Formula.nfv \<phi>) \<phi>" and z2: "dofz n \<psi>"
    using Frz.prems(2) unfolding c by (simp_all split: if_splits)
  have s1: "dofc (Formula.nfv \<phi>) tw \<phi>" by (rule Frz.IH(1)[OF fvi_less_nfv z1])
  have s2: "dofc n tw \<psi>" using Frz.prems(1) z2 by (intro Frz.IH(2)) simp_all
  have pr: "produces n (Formula.fv_list (Formula.Frz p \<phi> \<psi>)) tw (minit0 n (Formula.Frz p \<phi> \<psi>))"
    using produces_minit0[of "Formula.Frz p \<phi> \<psi>" n tw] Frz by simp
  show ?case using s1[unfolded c] s2 pr dframe_fv_list[of \<psi>] c
    by (auto intro!: DsFrz[where rb = "[]", unfolded list.map(1)])
next
  case (LetPast p \<phi> \<psi>)
  have c: "dcols (Formula.fv_list \<phi>) = [0..<Formula.nfv \<phi>]"
    by (rule dcols_upt) (use LetPast.hyps(2) fvi_less_nfv[of \<phi>] in auto)
  have z1: "dofz (Formula.nfv \<phi>) \<phi>" and z2: "dofz n \<psi>"
    using LetPast.prems(2) unfolding c by (simp_all split: if_splits)
  have s1: "dofc (Formula.nfv \<phi>) tw \<phi>" by (rule LetPast.IH(1)[OF fvi_less_nfv z1])
  have s2: "dofc n tw \<psi>" using LetPast.prems(1) z2 by (intro LetPast.IH(2)) simp_all
  have pr: "produces n (Formula.fv_list (Formula.LetPast p \<phi> \<psi>)) tw
      (minit0 n (Formula.LetPast p \<phi> \<psi>))"
    using produces_minit0[of "Formula.LetPast p \<phi> \<psi>" n tw] LetPast by simp
  show ?case using s1[unfolded c] s2 pr dframe_fv_list[of \<psi>] c by (auto intro!: DsLetPast)
next
  case (And_assign \<phi> \<psi>)
  obtain y t where sp: "split_assignment (Formula.fv \<phi>) \<psi> = (y, t)"
    by (cases "split_assignment (Formula.fv \<phi>) \<psi>") auto
  have m: "minit0 n (Formula.And \<phi> \<psi>) = MAndAssign (Formula.fv_list \<phi>) (minit0 n \<phi>) (y, t)"
    using And_assign.hyps(2) sp by simp
  have pr: "produces n (Formula.fv_list (Formula.And \<phi> \<psi>)) tw (minit0 n (Formula.And \<phi> \<psi>))"
    using produces_minit0[of "Formula.And \<phi> \<psi>" n tw] And_assign by simp
  have z: "dofz n \<phi>" using And_assign.prems(2) unfolding m by (simp add: Let_def split: if_splits)
  have s: "dofc n tw \<phi>" using And_assign.prems(1) z by (intro And_assign.IH) simp_all
  show ?case using And_assign.prems(2) s pr dframe_fv_list[of "Formula.And \<phi> \<psi>"] unfolding m
    by (auto simp: Let_def split: if_splits intro!: DsAndAssign)
next
  case (And_safe \<phi> \<psi>)
  have m: "minit0 n (Formula.And \<phi> \<psi>) = MAnd (Formula.fv_list \<phi>)
      (minit0 n \<phi>) True (Formula.fv_list \<psi>) (minit0 n \<psi>) ([], [])"
    using And_safe.hyps by simp
  have pr: "produces n (Formula.fv_list (Formula.And \<phi> \<psi>)) tw (minit0 n (Formula.And \<phi> \<psi>))"
    using produces_minit0[of "Formula.And \<phi> \<psi>" n tw] And_safe by simp
  have z1: "dofz n \<phi>" and z2: "dofz n \<psi>"
    using And_safe.prems(2) unfolding m by (simp_all add: Let_def split: if_splits)
  have s1: "dofc n tw \<phi>" using And_safe.prems(1) z1 by (intro And_safe.IH(1)) simp_all
  have s2: "dofc n tw \<psi>" using And_safe.prems(1) z2 by (intro And_safe.IH(2)) simp_all
  show ?case using And_safe.prems(2) s1 s2 pr dframe_fv_list[of "Formula.And \<phi> \<psi>"] unfolding m
    by (auto simp: Let_def dbuf2_def split: if_splits intro!: DsAnd)
next
  case (And_constraint \<phi> \<psi>)
  obtain t1 p c t2 where sc: "split_constraint \<psi> = (t1, p, c, t2)"
    by (cases "split_constraint \<psi>") auto
  have m: "minit0 n (Formula.And \<phi> \<psi>) = MAndRel (Formula.fv_list \<phi>) (minit0 n \<phi>) (t1, p, c, t2)"
    using And_constraint.hyps sc by simp
  have e: "Formula.fv_list (Formula.And \<phi> \<psi>) = Formula.fv_list \<phi>"
    using And_constraint.hyps(4) by (simp add: cols_union_subset)
  have pr: "produces n (Formula.fv_list (Formula.And \<phi> \<psi>)) tw (minit0 n (Formula.And \<phi> \<psi>))"
    using produces_minit0[of "Formula.And \<phi> \<psi>" n tw] And_constraint by simp
  have z: "dofz n \<phi>" using And_constraint.prems(2) unfolding m e by (simp split: if_splits)
  have s: "dofc n tw \<phi>" using And_constraint.prems(1) z by (intro And_constraint.IH) simp_all
  show ?case using And_constraint.prems(2) s pr dframe_fv_list[of \<phi>] unfolding m e
    by (auto split: if_splits intro!: DsAndRel)
next
  case (And_Not \<phi> \<psi>)
  have m: "minit0 n (Formula.And \<phi> (Formula.Neg \<psi>)) = MAnd (Formula.fv_list \<phi>)
      (minit0 n \<phi>) False (Formula.fv_list \<psi>) (minit0 n \<psi>) ([], [])"
    using And_Not.hyps by simp
  have pr: "produces n (Formula.fv_list (Formula.And \<phi> (Formula.Neg \<psi>))) tw
      (minit0 n (Formula.And \<phi> (Formula.Neg \<psi>)))"
    using produces_minit0[of "Formula.And \<phi> (Formula.Neg \<psi>)" n tw] And_Not by simp
  have z1: "dofz n \<phi>" and z2: "dofz n \<psi>"
    using And_Not.prems(2) unfolding m by (simp_all add: Let_def split: if_splits)
  have s1: "dofc n tw \<phi>" using And_Not.prems(1) z1 by (intro And_Not.IH(1)) simp_all
  have s2: "dofc n tw \<psi>" using And_Not.prems(1) z2 by (intro And_Not.IH(2)) simp_all
  show ?case using And_Not.prems(2) s1 s2 pr dframe_fv_list[of "Formula.And \<phi> (Formula.Neg \<psi>)"]
    unfolding m by (auto simp: Let_def dbuf2_def split: if_splits intro!: DsAnd)
next
  case (And_Trigger \<phi> \<phi>' I \<psi>')
  note sp = \<open>safe_formula \<phi>\<close> and sp' = \<open>safe_formula \<phi>'\<close>
  note sd = \<open>safe_dual True safe_formula \<phi>' I \<psi>'\<close>
  note subf = \<open>Formula.fv (Formula.Trigger \<phi>' I \<psi>') \<subseteq> Formula.fv \<phi>\<close>
  have sub: "Formula.fv \<phi>' \<subseteq> Formula.fv \<psi>'"
    using sd sp' by (auto simp: safe_dual_def split: if_splits)
  have sp2: "safe_formula \<psi>'" using sd by (auto simp: safe_dual_def split: if_splits)
  have subR: "Formula.fv \<psi>' \<subseteq> Formula.fv \<phi>" using subf by auto
  have bA: "\<forall>x \<in> Formula.fv \<phi>. x < n" using And_Trigger.prems by simp
  have bR: "\<forall>x \<in> Formula.fv \<psi>'. x < n" using bA subR by auto
  have bL: "\<forall>x \<in> Formula.fv \<phi>'. x < n" using bR sub by auto
  have e: "Formula.fv_list (Formula.And \<phi> (Formula.Trigger \<phi>' I \<psi>')) = Formula.fv_list \<phi>"
    using subf by (simp add: cols_union_subset)
  have sfa: "safe_formula (Formula.And \<phi> (Formula.Trigger \<phi>' I \<psi>'))" using And_Trigger.hyps by simp
  let ?args = "init_args I n (Formula.fv_list \<phi>') (Formula.fv_list \<psi>') True None"
  show ?case
  proof (cases "mem I 0")
    case True
    have st: "safe_formula (Formula.Trigger \<phi>' I \<psi>')"
      using sd sp' True by (simp add: safe_dual_def)
    have m: "minit0 n (Formula.And \<phi> (Formula.Trigger \<phi>' I \<psi>')) =
        MAnd (Formula.fv_list \<phi>) (minit0 n \<phi>) True (Formula.fv_list (Formula.Trigger \<phi>' I \<psi>'))
          (minit0 n (Formula.Trigger \<phi>' I \<psi>')) ([], [])"
      using st by (simp add: no_safe_assign_trigger)
    have z1: "dofz n \<phi>" and z2: "dofz n (Formula.Trigger \<phi>' I \<psi>')"
      using And_Trigger.prems(2) unfolding m by (simp_all add: Let_def split: if_splits)
    have s1: "dofc n tw \<phi>" by (rule And_Trigger.IH(1)[OF bA z1])
    have s2: "dofc n tw (Formula.Trigger \<phi>' I \<psi>')"
      by (rule dsim_dof_minit0_trigger[OF True sp' sub st _ z2])
        (use bR sub And_Trigger.IH(2,3) bL in auto)
    have pr: "produces n (Formula.fv_list (Formula.And \<phi> (Formula.Trigger \<phi>' I \<psi>'))) tw
        (minit0 n (Formula.And \<phi> (Formula.Trigger \<phi>' I \<psi>')))"
      by (rule produces_minit0[OF sfa And_Trigger.prems(1)])
    show ?thesis
      using And_Trigger.prems(2) s1 s2 pr dframe_fv_list[of "Formula.And \<phi> (Formula.Trigger \<phi>' I \<psi>')"]
      unfolding m by (auto simp: Let_def dbuf2_def split: if_splits intro!: DsAnd)
  next
    case False
    have LR: "Formula.fv \<phi>' = Formula.fv \<psi>'" using sd False by (simp add: safe_dual_def)
    have nst: "\<not> safe_formula (Formula.Trigger \<phi>' I \<psi>')"
      using False by (simp add: safe_dual_def)
    have m: "minit0 n (Formula.And \<phi> (Formula.Trigger \<phi>' I \<psi>')) =
        MAndTrigger (Formula.fv_list \<phi>) (minit0 n \<phi>) ([], []) ?args
          (minit0 n \<phi>') (minit0 n \<psi>') ([], []) [] (init_mmtaux ?args)"
      using nst sp' by (simp add: no_safe_assign_trigger verimon_maux.init_and_trigger_def)
    have ag: "args_L ?args = Formula.fv_list \<phi>'" "args_R ?args = Formula.fv_list \<psi>'"
      "args_ivl ?args = I" "args_pos ?args = True"
      by (simp_all add: init_args_def)
    have zz: "vdfail_nodes (dof n (Formula.fv_list \<phi>) (dcols (Formula.fv_list \<phi>))
        (MAndTrigger (Formula.fv_list \<phi>) (minit0 n \<phi>) ([], []) ?args
          (minit0 n \<phi>') (minit0 n \<psi>') ([], []) [] (init_mmtaux ?args))) = 0"
      using And_Trigger.prems(2) unfolding m e .
    have ok: "tok (dcols (Formula.fv_list \<psi>')) (dcols (Formula.fv_list \<phi>')) ?args"
      using zz by (simp add: Let_def ag split: if_splits)
    have z1: "dofz n \<phi>" and z2: "dofz n \<phi>'" and z3: "dofz n \<psi>'"
      using zz by (simp_all add: Let_def ag split: if_splits)
    have s1: "dofc n tw \<phi>" by (rule And_Trigger.IH(1)[OF bA z1])
    have s2: "dofc n tw \<phi>'" by (rule And_Trigger.IH(2)[OF bL z2])
    have s3: "dofc n tw \<psi>'" by (rule And_Trigger.IH(3)[OF bR z3])
    have pr: "produces n (Formula.fv_list \<phi>) tw
        (MAndTrigger (Formula.fv_list \<phi>) (minit0 n \<phi>) ([], []) ?args
          (minit0 n \<phi>') (minit0 n \<psi>') ([], []) [] (init_mmtaux ?args))"
      using produces_minit0[OF sfa And_Trigger.prems(1), of tw] unfolding m e .
    have rl: "dtrigger_rel (Formula.fv_list \<psi>') (dcols (Formula.fv_list \<psi>'))
        (Formula.fv_list \<phi>') (dcols (Formula.fv_list \<phi>')) ?args tw (init_mmtaux ?args)
        (ginit_mmtaux (dargs (dcols (Formula.fv_list \<psi>')) (dcols (Formula.fv_list \<phi>')) ?args)
          (dmsk (dcols (Formula.fv_list \<psi>')) (dcols (Formula.fv_list \<phi>'))))
        ([], []) ([], []) []"
      by (rule dtrigger_rel_init[OF refl dframe_fv_list dframe_fv_list _ ok]) (simp add: sub)
    show ?thesis unfolding m e
      by (simp add: Let_def ag sub subR ok)
        (rule DsAndTrigger[OF dframe_fv_list pr s1 s2 s3 _ _ ag(1,2) ok refl refl _ rl],
          simp_all add: sub subR dandbuf_def)
  qed
next
  case (And_Release \<phi> \<phi>' I \<psi>')
  have m: "minit0 n (Formula.And \<phi> (Formula.Release \<phi>' I \<psi>')) =
      minit0 n (and_release_safe_bounded \<phi> \<phi>' I \<psi>')"
    using And_Release.hyps(6) by (simp add: safe_assignment_def safe_dual_def)
  have e: "Formula.fv_list (Formula.And \<phi> (Formula.Release \<phi>' I \<psi>'))
      = Formula.fv_list (and_release_safe_bounded \<phi> \<phi>' I \<psi>')"
    by (rule fv_list_and_release_safe_bounded[OF And_Release.hyps(7), symmetric])
  show ?case unfolding m e
    by (rule And_Release.IH(1)[OF _ And_Release.prems(2)[unfolded m e]])
      (use And_Release.prems(1) in \<open>simp add: release_fvi(3)\<close>)
next
  case (Ands l pos neg)
  show ?case sorry
next
  case (Neg \<phi>)
  show ?case by (rule dsim_dof_neg[OF Neg.hyps(1,2) Neg.prems]) (use Neg.IH Neg.hyps(1) in simp)
next
  case (Or \<phi> \<psi>)
  have e: "Formula.fv_list (Formula.Or \<phi> \<psi>) = Formula.fv_list \<phi>"
    using Or.hyps(1) by (simp add: cols_union_subset)
  have c: "dcols (Formula.fv_list \<psi>) = dcols (Formula.fv_list \<phi>)"
    using Or.hyps(1) by (intro dcols_cong) simp
  have z1: "dofz n \<phi>" and z2: "dofz n \<psi>" using Or.prems(2) Or.hyps(1) unfolding e c by simp_all
  have s1: "dofc n tw \<phi>" using Or.prems(1) z1 by (intro Or.IH(1)) simp_all
  have s2: "dofc n tw \<psi>" using Or.prems(1) z2 Or.hyps(1) by (intro Or.IH(2)) simp_all
  have pr: "produces n (Formula.fv_list (Formula.Or \<phi> \<psi>)) tw (minit0 n (Formula.Or \<phi> \<psi>))"
    using produces_minit0[of "Formula.Or \<phi> \<psi>" n tw] Or by simp
  show ?case unfolding e using s1 s2[unfolded c] pr[unfolded e] dframe_fv_list[of \<phi>] Or.hyps(1)
    by (auto simp: dbuf2_def intro!: DsOr)
next
  case (Exists t \<phi>)
  have b: "\<forall>x \<in> Formula.fv \<phi>. x < Suc n"
    using fvi_Suc_bound[where b = 0 and \<phi> = \<phi> and n = n] Exists.prems by simp
  have e: "Formula.fv_list (Formula.Exists t \<phi>) = ex_cols (Formula.fv_list \<phi>)"
    by (simp add: fvi_list_Suc)
  have pr: "produces n (Formula.fv_list (Formula.Exists t \<phi>)) tw (minit0 n (Formula.Exists t \<phi>))"
    using produces_minit0[of "Formula.Exists t \<phi>" n tw] Exists by simp
  have z: "dofz (Suc n) \<phi>" using Exists.prems(2) by (simp add: Let_def split: if_splits)
  have s: "dofc (Suc n) tw \<phi>" by (rule Exists.IH[OF b z])
  show ?case using Exists.prems(2) s pr dframe_fv_list[of "Formula.Exists t \<phi>"]
    by (auto simp: Let_def split: if_splits intro!: DsExists)
next
  case (Agg y \<omega> tys f \<phi>)
  show ?case sorry
next
  case (Prev I \<phi>)
  have z: "dofz n \<phi>" using Prev.prems(2) by simp
  have s: "dofc n tw \<phi>" using Prev.prems(1) z by (intro Prev.IH) simp_all
  have pr: "produces n (Formula.fv_list (Formula.Prev I \<phi>)) tw (minit0 n (Formula.Prev I \<phi>))"
    using produces_minit0[of "Formula.Prev I \<phi>" n tw] Prev by simp
  show ?case using s pr dframe_fv_list[of "Formula.Prev I \<phi>"] by (auto intro!: DsPrev)
next
  case (Next I \<phi>)
  have z: "dofz n \<phi>" using Next.prems(2) by simp
  have s: "dofc n tw \<phi>" using Next.prems(1) z by (intro Next.IH) simp_all
  have pr: "produces n (Formula.fv_list (Formula.Next I \<phi>)) tw (minit0 n (Formula.Next I \<phi>))"
    using produces_minit0[of "Formula.Next I \<phi>" n tw] Next by simp
  show ?case using s pr dframe_fv_list[of "Formula.Next I \<phi>"] by (auto intro!: DsNext)
next
  case (Since \<phi> I \<psi>)
  note sub = \<open>Formula.fv \<phi> \<subseteq> Formula.fv \<psi>\<close>
  have b: "\<forall>x \<in> Formula.fv \<psi>. x < n" using Since.prems by simp
  let ?args = "init_args I n (Formula.fv_list \<phi>) (Formula.fv_list \<psi>) True None"
  have m: "minit0 n (Formula.Since \<phi> I \<psi>) =
      MSince ?args (minit0 n \<phi>) (minit0 n \<psi>) init_mbuf2S (init_mmasaux ?args)"
    using Since.hyps(2) by (simp add: default_mmasaux.init_since_def)
  have e: "Formula.fv_list (Formula.Since \<phi> I \<psi>) = Formula.fv_list \<psi>"
    using sub by (simp add: cols_union_subset)
  have pr: "produces n (Formula.fv_list \<psi>) tw
      (MSince ?args (minit0 n \<phi>) (minit0 n \<psi>) init_mbuf2S (init_mmasaux ?args))"
    using produces_minit0[of "Formula.Since \<phi> I \<psi>" n tw] Since unfolding m e by simp
  note z = dof_since_z[OF Since.prems(2)[unfolded m e]]
  have s1: "dofc n tw \<phi>" using b sub z(1) by (intro Since.IH(1)) (auto simp: init_args_def)
  have s2: "dofc n tw \<psi>" using b z(2) by (intro Since.IH(2)) (auto simp: init_args_def)
  show ?case unfolding m e
    by (rule dsim_dof_since[OF refl pr s1 s2 distinct_fvi_list distinct_fvi_list]) (simp add: sub)
next
  case (Not_Since \<phi> I \<psi>)
  have sub: "Formula.fv \<phi> \<subseteq> Formula.fv \<psi>" using Not_Since.hyps(1) by simp
  have b: "\<forall>x \<in> Formula.fv \<psi>. x < n" using Not_Since.prems by simp
  let ?args = "init_args I n (Formula.fv_list \<phi>) (Formula.fv_list \<psi>) False None"
  have m: "minit0 n (Formula.Since (Formula.Neg \<phi>) I \<psi>) =
      MSince ?args (minit0 n \<phi>) (minit0 n \<psi>) init_mbuf2S (init_mmasaux ?args)"
    using Not_Since.hyps(3) by (simp add: default_mmasaux.init_since_def)
  have e: "Formula.fv_list (Formula.Since (Formula.Neg \<phi>) I \<psi>) = Formula.fv_list \<psi>"
    using sub by (simp add: cols_union_subset)
  have pr: "produces n (Formula.fv_list \<psi>) tw
      (MSince ?args (minit0 n \<phi>) (minit0 n \<psi>) init_mbuf2S (init_mmasaux ?args))"
    using produces_minit0[of "Formula.Since (Formula.Neg \<phi>) I \<psi>" n tw] Not_Since unfolding m e
    by simp
  note z = dof_since_z[OF Not_Since.prems(2)[unfolded m e]]
  have s1: "dofc n tw \<phi>" using b sub z(1) by (intro Not_Since.IH(1)) (auto simp: init_args_def)
  have s2: "dofc n tw \<psi>" using b z(2) by (intro Not_Since.IH(2)) (auto simp: init_args_def)
  show ?case unfolding m e
    by (rule dsim_dof_since[OF refl pr s1 s2 distinct_fvi_list distinct_fvi_list]) (simp add: sub)
next
  case (Until \<phi> I \<psi>)
  note sub = \<open>Formula.fv \<phi> \<subseteq> Formula.fv \<psi>\<close>
  have b: "\<forall>x \<in> Formula.fv \<psi>. x < n" using Until.prems by simp
  let ?args = "init_args I n (Formula.fv_list \<phi>) (Formula.fv_list \<psi>) True None"
  have m: "minit0 n (Formula.Until \<phi> I \<psi>) =
      MUntil ?args (minit0 n \<phi>) (minit0 n \<psi>) ([], []) [] 0 (init_muaux_dq ?args)"
    using Until.hyps(2) by (simp add: dq_muaux.init_until_def)
  have e: "Formula.fv_list (Formula.Until \<phi> I \<psi>) = Formula.fv_list \<psi>"
    using sub by (simp add: cols_union_subset)
  have pr: "produces n (Formula.fv_list \<psi>) tw
      (MUntil ?args (minit0 n \<phi>) (minit0 n \<psi>) ([], []) [] 0 (init_muaux_dq ?args))"
    using produces_minit0[of "Formula.Until \<phi> I \<psi>" n tw] Until unfolding m e by simp
  note z = dof_until_z[OF Until.prems(2)[unfolded m e]]
  have s1: "dofc n tw \<phi>" using b sub z(1) by (intro Until.IH(1)) (auto simp: init_args_def)
  have s2: "dofc n tw \<psi>" using b z(2) by (intro Until.IH(2)) (auto simp: init_args_def)
  show ?case unfolding m e
    by (rule dsim_dof_until[OF refl pr s1 s2 distinct_fvi_list distinct_fvi_list]) (simp add: sub)
next
  case (Not_Until \<phi> I \<psi>)
  have sub: "Formula.fv \<phi> \<subseteq> Formula.fv \<psi>" using Not_Until.hyps(1) by simp
  have b: "\<forall>x \<in> Formula.fv \<psi>. x < n" using Not_Until.prems by simp
  let ?args = "init_args I n (Formula.fv_list \<phi>) (Formula.fv_list \<psi>) False None"
  have m: "minit0 n (Formula.Until (Formula.Neg \<phi>) I \<psi>) =
      MUntil ?args (minit0 n \<phi>) (minit0 n \<psi>) ([], []) [] 0 (init_muaux_dq ?args)"
    using Not_Until.hyps(3) by (simp add: dq_muaux.init_until_def)
  have e: "Formula.fv_list (Formula.Until (Formula.Neg \<phi>) I \<psi>) = Formula.fv_list \<psi>"
    using sub by (simp add: cols_union_subset)
  have pr: "produces n (Formula.fv_list \<psi>) tw
      (MUntil ?args (minit0 n \<phi>) (minit0 n \<psi>) ([], []) [] 0 (init_muaux_dq ?args))"
    using produces_minit0[of "Formula.Until (Formula.Neg \<phi>) I \<psi>" n tw] Not_Until unfolding m e
    by simp
  note z = dof_until_z[OF Not_Until.prems(2)[unfolded m e]]
  have s1: "dofc n tw \<phi>" using b sub z(1) by (intro Not_Until.IH(1)) (auto simp: init_args_def)
  have s2: "dofc n tw \<psi>" using b z(2) by (intro Not_Until.IH(2)) (auto simp: init_args_def)
  show ?case unfolding m e
    by (rule dsim_dof_until[OF refl pr s1 s2 distinct_fvi_list distinct_fvi_list]) (simp add: sub)
next
  case (Trigger_0 \<phi> I \<psi>)
  note m0 = \<open>mem I 0\<close>
  have sub: "Formula.fv \<phi> \<subseteq> Formula.fv \<psi>" using Trigger_0(3) .
  have b: "\<forall>x \<in> Formula.fv \<psi>. x < n" using Trigger_0.prems by simp
  have bp: "\<forall>x \<in> Formula.fv \<phi>. x < n" using b sub by auto
  have e: "Formula.fv_list (Formula.Trigger \<phi> I \<psi>) = Formula.fv_list \<psi>"
    using sub by (simp add: cols_union_subset)
  show ?case
  proof (cases "safe_formula \<phi>")
    case True
    let ?args = "init_args I n (Formula.fv_list \<phi>) (Formula.fv_list \<psi>) True None"
    have m: "minit0 n (Formula.Trigger \<phi> I \<psi>) = MTrigger ?args
        (minit0 n \<phi>) (minit0 n \<psi>) ([], []) [] (init_mmtaux ?args)"
      using True by (simp add: verimon_maux.init_trigger_def)
    note z = dof_trigger_z[OF Trigger_0.prems(2)[unfolded m e]]
    have z1: "dofz n \<phi>" and z2: "dofz n \<psi>" using z by (simp_all add: init_args_def)
    have s2: "dofc n tw \<psi>" by (rule Trigger_0(5)[OF _ z2]) (use b in auto)
    have sft: "safe_formula (Formula.Trigger \<phi> I \<psi>)"
      using m0 sub Trigger_0(2) True by (simp add: safe_dual_def)
    have s1: "dofc n tw \<phi>"
    proof (cases "\<forall>n. (\<forall>x \<in> Formula.fv \<phi>. x < n) \<longrightarrow> dofz n \<phi> \<longrightarrow> dofc n tw \<phi>")
      case True then show ?thesis using bp z1 by blast
    next
      case False
      then obtain \<chi> where phi: "\<phi> = Formula.Neg \<chi>" and sc: "safe_formula \<chi>"
        and ih: "\<forall>n. (\<forall>x \<in> Formula.fv \<chi>. x < n) \<longrightarrow> dofz n \<chi> \<longrightarrow> dofc n tw \<chi>"
        using Trigger_0(4) by (cases \<phi>) auto
      have fc: "Formula.fv \<chi> = {}" using \<open>safe_formula \<phi>\<close> phi by simp
      show ?thesis unfolding phi
        by (rule dsim_dof_neg[OF fc sc]) (use bp z1 ih fc phi in auto)
    qed
    have pr: "produces n (Formula.fv_list \<psi>) tw
        (MTrigger ?args (minit0 n \<phi>) (minit0 n \<psi>) ([], []) [] (init_mmtaux ?args))"
      using produces_minit0[OF sft Trigger_0.prems(1), of tw] unfolding m e .
    show ?thesis unfolding m e
      by (rule dsim_dof_trigger[OF refl m0 pr s1 s2 distinct_fvi_list distinct_fvi_list])
        (simp add: sub)
  next
    case False
    obtain \<chi> where phi: "\<phi> = Formula.Neg \<chi>" and sc: "safe_formula \<chi>"
      and ih: "\<forall>n. (\<forall>x \<in> Formula.fv \<chi>. x < n) \<longrightarrow> dofz n \<chi> \<longrightarrow> dofc n tw \<chi>"
      using Trigger_0(4) False by (cases \<phi>) auto
    let ?args = "init_args I n (Formula.fv_list \<chi>) (Formula.fv_list \<psi>) False None"
    have m: "minit0 n (Formula.Trigger \<phi> I \<psi>) = MTrigger ?args
        (minit0 n \<chi>) (minit0 n \<psi>) ([], []) [] (init_mmtaux ?args)"
      using False phi by (simp add: verimon_maux.init_trigger_def)
    note z = dof_trigger_z[OF Trigger_0.prems(2)[unfolded m e]]
    have z1: "dofz n \<chi>" and z2: "dofz n \<psi>" using z by (simp_all add: init_args_def)
    have s2: "dofc n tw \<psi>" by (rule Trigger_0(5)[OF _ z2]) (use b in auto)
    have s1: "dofc n tw \<chi>" using ih bp z1 phi by simp
    have sft: "safe_formula (Formula.Trigger \<phi> I \<psi>)"
      using m0 sub Trigger_0(2) sc phi by (simp add: safe_dual_def)
    have pr: "produces n (Formula.fv_list \<psi>) tw
        (MTrigger ?args (minit0 n \<chi>) (minit0 n \<psi>) ([], []) [] (init_mmtaux ?args))"
      using produces_minit0[OF sft Trigger_0.prems(1), of tw] unfolding m e .
    show ?thesis unfolding m e
      by (rule dsim_dof_trigger[OF refl m0 pr s1 s2 distinct_fvi_list distinct_fvi_list])
        (use sub phi in simp)
  qed
next
  case (Trigger \<phi> I \<psi>) then show ?case by simp
next
  case (Release_0 \<phi> I \<psi>)
  have sub: "Formula.fv \<phi> \<subseteq> Formula.fv \<psi>" using Release_0.hyps(4) .
  have m: "minit0 n (Formula.Release \<phi> I \<psi>) = minit0 n (release_safe_0 \<phi> I \<psi>)"
    using Release_0.hyps(1) by simp
  have e: "Formula.fv_list (Formula.Release \<phi> I \<psi>) = Formula.fv_list (release_safe_0 \<phi> I \<psi>)"
    by (rule fv_list_release_safe_0[OF sub, symmetric])
  show ?case unfolding m e
    by (rule Release_0.IH[OF _ Release_0.prems(2)[unfolded m e]])
      (use Release_0.prems(1) in \<open>simp add: release_fvi(1)\<close>)
next
  case (Release \<phi> I \<psi>) then show ?case by simp
next
  case (MatchP I r)
  show ?case sorry
next
  case (MatchF I r)
  show ?case sorry
next
  case (TP t)
  have pr: "produces n (Formula.fv_list (Formula.TP t)) tw (minit0 n (Formula.TP t))"
    using produces_minit0[of "Formula.TP t" n tw] TP by simp
  show ?case using TP.prems(2) pr dframe_fv_list[of "Formula.TP t"]
    by (auto split: if_splits intro!: DsTP)
next
  case (TS t)
  have pr: "produces n (Formula.fv_list (Formula.TS t)) tw (minit0 n (Formula.TS t))"
    using produces_minit0[of "Formula.TS t" n tw] TS by simp
  show ?case using TS.prems(2) pr dframe_fv_list[of "Formula.TS t"]
    by (auto split: if_splits intro!: DsTS)
qed

end
