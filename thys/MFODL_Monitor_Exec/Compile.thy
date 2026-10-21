(*<*)
theory Compile
  imports Correct
begin
(*>*)

section \<open>The descending compiler\<close>

text \<open>
  The executable evaluator's formula has a node for most, but not all, of the kernel's.  This theory
  builds the compiler that descends into a kernel formula and emits a executable node wherever the
  simulation has a rule for one, answering \<open>EFail\<close> at the constructors the executable fragment does
  not cover.  Nothing relates \<open>EFail\<close> to a kernel formula, so the theorems below hold of a
  compiled formula that has none -- which the caller checks with @{const efail_nodes}.

  The compiler is a plain function of the kernel's formula and the two column lists its result
  is to have: the kernel's, @{term ks}, and the executable one, @{term cs}, which is the ascending
  order of the same columns.  At every recursive call the kernel column list of the operand is
  read off the node itself -- the kernel's nodes store their operands' column lists -- and the
  executable one is its ascending order, @{term ecols}.  Wherever a node's own columns are determined
  by its operands', the compiler checks that they are the ones it was asked for.
\<close>

subsection \<open>The compiler\<close>

definition ecols :: "cols \<Rightarrow> cols" where
  "ecols k = set_cols (set k)"

text \<open>The positions in @{term cs} of the columns in @{term L}.  The compiler fuses an aggregation
  into the temporal operator below it only when the left operand's columns occupy none of the
  right operand's positions.\<close>

definition cpos :: "cols \<Rightarrow> nat set \<Rightarrow> nat set" where
  "cpos cs L = {i. i < length cs \<and> cs ! i \<in> L}"

lemma cpos_code[code]: "cpos cs L = set (filter (\<lambda>i. cs ! i \<in> L) [0..<length cs])"
  by (auto simp: cpos_def)

definition eagg_gcols :: "aggargs \<Rightarrow> cols" where
  "eagg_gcols args = map (\<lambda>c. c - length (aggargs_tys args))
     (drop (length (aggargs_tys args)) (ecols (aggargs_cols args)))"

text \<open>The width a temporal structure runs at: its own, or -- with an aggregation fused into it --
  the operand's, which is wider by the bound variables the aggregation ranges over.\<close>

text \<open>A constraint over a fused aggregating Since becomes the node's guard rather than a filter
  above it: the constraint is on the node's own columns, which are exactly the aggregation's, so
  the groups that fail it never have to be built.  Nothing else takes a guard.\<close>

fun eset_q :: "uconstr \<Rightarrow> eformula \<Rightarrow> eformula option" where
  "eset_q c (ESince args \<phi> \<psi> buf aux) =
     (case aux of UDSX_wagg p None a \<Rightarrow> Some (ESince args \<phi> \<psi> buf (UDSX_wagg p (Some c) a))
      | _ \<Rightarrow> None)"
| "eset_q c \<phi> = None"

lemma efail_nodes_eset_q: "eset_q c d = Some d' \<Longrightarrow> efail_nodes d' = efail_nodes d"
  by (cases d) (auto split: udsaux_x.splits option.splits)

function (sequential) eof ::
    "nat \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> (mmasaux, muaux_dq, event_data mmtaux) mformula \<Rightarrow> eformula" where
  "eof n ks cs (MRel rel) = ERel (etabc ks cs rel)"
| "eof n ks cs (MPred e tms mode) =
     (if mode = Match then (if ks = pred_cols tms then EPredM e (length tms) tms cs else EFail)
      else if (mode = Copy \<and> tms = map Formula.Var [0..<length tms] \<and> ks = [0..<length tms] \<and> cs = ks)
           \<or> (mode = Simple \<and> is_simple_pattern tms 0 \<and> cs = smp_cols tms \<and> ks = cs)
      then EPredS e (length tms)
      else EFail)"
| "eof n ks cs (MAndRel k \<phi> conf) =
     (if k = ks \<and> Formula.fv_trm (fst conf) \<subseteq> set cs \<and> Formula.fv_trm (snd (snd (snd conf))) \<subseteq> set cs
      then (let d = eof n ks cs \<phi>; c = reindex_constraint cs conf in
        case eset_q c d of Some d' \<Rightarrow> d' | None \<Rightarrow> EAndRel d c)
      else EFail)"
| "eof n ks cs (MNeg \<phi>) =
     (if ks = [] \<and> cs = [] then ENeg (eof n [] [] \<phi>) else EFail)"
| "eof n ks cs (MExists kks \<phi>) =
     (let ccs = ecols kks in
      if ks = ex_cols kks \<and> cs = eex_cols ccs
      then EExists (eof (Suc n) kks ccs \<phi>) (ex_drop0 ccs) else EFail)"
| "eof n ks cs (MOr k1 \<phi> k2 \<psi> buf) =
     (if k1 = ks \<and> set k2 = set ks \<and> buf = ([], [])
      then EOr (eof n ks cs \<phi>) (eof n k2 cs \<psi>) (mbuf_t_empty, mbuf_t_empty) else EFail)"
| "eof n ks cs (MAnd k1 \<phi> pos k2 \<psi> buf) =
     (let c1 = ecols k1; c2 = ecols k2 in
      if ks = cols_union k1 k2 \<and> cs = merge_cols c1 c2 \<and> (pos \<or> set k2 \<subseteq> set k1) \<and> buf = ([], [])
      then EAnd (mk_djoin c1 c2) (eof n k1 c1 \<phi>) pos (eof n k2 c2 \<psi>) (mbuf_t_empty, mbuf_t_empty)
      else EFail)"
| "eof n ks cs (MPrev I \<phi> first buf nts) =
     (if buf = [] then EPrev I (eof n ks cs \<phi>) first mbuf_t_empty (mbuf_t_empty @@ nts) else EFail)"
| "eof n ks cs (MNext I \<phi> first nts) = ENext I (eof n ks cs \<phi>) first (mbuf_t_empty @@ nts)"
| "eof n ks cs (MAnds k kpos kneg L buf) =
     (case kpos of [] \<Rightarrow> EFail
      | k0 # kss \<Rightarrow>
        (let c0 = ecols k0; css = map ecols kss; nss = map ecols kneg in
         if k = ks \<and> cs = eands_cols c0 css \<and> length L = length kpos + length kneg \<and>
            length buf = length L \<and> (\<forall>b \<in> set buf. b = []) \<and>
            (\<forall>c \<in> set nss. set c \<subseteq> set (eands_cols c0 css))
         then EAnds (eands_plans c0 css) (eands_plans (eands_cols c0 css) nss)
                (map (\<lambda>(k, \<phi>). eof n k (ecols k) \<phi>) (zip (kpos @ kneg) L)) (map (\<lambda>_. mbuf_t_empty) L)
         else EFail))"
| "eof n ks cs (MAgg args \<phi>) =
     (let m = length (aggargs_tys args); k0 = aggargs_cols args; g = eagg_gcols args;
          y = aggargs_y args in
      if ks = y # shift_cols m k0 \<and> cs = merge_cols g [y] \<and> ecols k0 = agg_cols m g \<and>
         y \<notin> set g \<and> (aggargs_g0 args \<longrightarrow> g = []) \<and> Formula.fv_trm (aggargs_f args) \<subseteq> set k0
      then EAgg (aggargs_g0 args) (aggargs_\<omega> args)
             (reindex_trm (agg_cols m g) (aggargs_f args)) m (ins_pos g y)
             (eof (m + n) k0 (agg_cols m g) \<phi>)
      else EFail)"
| "eof n ks cs (MSince args \<phi> \<psi> buf aux) =
     (let kL = args_L args; kR = args_R args; cL = ecols kL; cR = ecols kR;
          \<phi>d = eof (args_n args) kL cL \<phi>; \<psi>d = eof (args_n args) kR cR \<psi> in
      case args_agg args of
        None \<Rightarrow>
          (if args_n args = n \<and> ks = kR \<and> cs = cR \<and> set kL \<subseteq> set kR \<and> buf = init_mbuf2S
           then ESince (eargs cR cL args) \<phi>d \<psi>d init_mebuf2S
                  (udsx_init (eargs cR cL args) (emsk cR cL))
           else EFail)
      | Some ag \<Rightarrow>
          (let m = length (aggargs_tys ag); g = eagg_gcols ag; y = aggargs_y ag in
           if aggargs_cols ag = kR \<and> set kL \<subseteq> set kR \<and> buf = init_mbuf2S \<and>
              agg_cols m g = cR \<and> ks = y # shift_cols m kR \<and> cs = merge_cols g [y] \<and>
              y \<notin> set g \<and> (aggargs_g0 ag \<longrightarrow> g = []) \<and> Formula.fv_trm (aggargs_f ag) \<subseteq> set kR
           then (if cpos cR (set cL) = {}
                 then ESince (eargs cR cL args) \<phi>d \<psi>d init_mebuf2S
                        (udsx_init_agg (eargs cR cL args)
                          (aggargs_g0 ag, aggargs_\<omega> ag, reindex_trm cR (aggargs_f ag),
                           m, ins_pos g y) None)
                 else EAgg (aggargs_g0 ag) (aggargs_\<omega> ag) (reindex_trm cR (aggargs_f ag))
                        m (ins_pos g y)
                        (ESince (eargs cR cL args) \<phi>d \<psi>d init_mebuf2S
                          (udsx_init (eargs cR cL args) (emsk cR cL))))
           else EFail))"
| "eof n ks cs (MUntil args \<phi> \<psi> buf nts t aux) =
     (let kL = args_L args; kR = args_R args; cL = ecols kL; cR = ecols kR;
          \<phi>d = eof (args_n args) kL cL \<phi>; \<psi>d = eof (args_n args) kR cR \<psi> in
      case args_agg args of
        None \<Rightarrow>
          (if args_n args = n \<and> ks = kR \<and> cs = cR \<and> set kL \<subseteq> set kR \<and>
              buf = ([], []) \<and> nts = [] \<and> t = 0
           then EUntil (eargs cR cL args) (emsk cR cL) \<phi>d \<psi>d (mbuf_t_empty, mbuf_t_empty) mbuf_t_empty 0
                  (udux_init (eargs cR cL args))
           else EFail)
      | Some ag \<Rightarrow>
          (let m = length (aggargs_tys ag); g = eagg_gcols ag; y = aggargs_y ag in
           if aggargs_cols ag = kR \<and> set kL \<subseteq> set kR \<and> buf = ([], []) \<and> nts = [] \<and> t = 0 \<and>
              agg_cols m g = cR \<and> ks = y # shift_cols m kR \<and> cs = merge_cols g [y] \<and>
              y \<notin> set g \<and> (aggargs_g0 ag \<longrightarrow> g = []) \<and> Formula.fv_trm (aggargs_f ag) \<subseteq> set kR
           then (if cpos cR (set cL) = {} \<and> memL (args_ivl args) 0
                 then EUntil (eargs cR cL args) (emsk cR cL) \<phi>d \<psi>d (mbuf_t_empty, mbuf_t_empty)
                        mbuf_t_empty 0
                        (udux_init_agg (eargs cR cL args)
                          (aggargs_g0 ag, aggargs_\<omega> ag, reindex_trm cR (aggargs_f ag),
                           m, ins_pos g y))
                 else EAgg (aggargs_g0 ag) (aggargs_\<omega> ag) (reindex_trm cR (aggargs_f ag))
                  m (ins_pos g y)
                  (EUntil (eargs cR cL args) (emsk cR cL) \<phi>d \<psi>d (mbuf_t_empty, mbuf_t_empty)
                    mbuf_t_empty 0 (udux_init (eargs cR cL args))))
           else EFail))"
| "eof n ks cs (MAndAssign k0 \<phi> conf) =
     (let y = fst conf; t = snd conf; c0 = ecols k0 in
      if ks = k0 @ [y] \<and> y \<notin> set k0 \<and> Formula.fv_trm t \<subseteq> set c0 \<and> cs = merge_cols c0 [y]
      then EAndAssign (ins_pos c0 y) (reindex_trm c0 t) (eof n k0 c0 \<phi>)
      else EFail)"
| "eof n ks cs (MLet p m kks \<phi> \<psi>) =
     (if ecols kks = [0..<m] then ELet p m (eof m kks [0..<m] \<phi>) (eof n ks cs \<psi>) else EFail)"
| "eof n ks cs (MFrz p m kks \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L sx cS \<rho>S \<rho>E) =
     (if ecols kks = [0..<m] \<and> \<alpha>s = [] \<and> rb = [] \<and> cS = ks \<and>
         (case sx of FSSep _ _ _ _ _ _ _ _ \<Rightarrow> False | _ \<Rightarrow> True)
      then EFrz p m (eof m kks [0..<m] \<phi>) (eof n ks cs \<psi>) jfrz jpsi0 jphi []
        (eof n ks cs \<rho>) w pR tq [] d po ng lv (eof n ks cs \<rho>L) sx cs (eof n ks cs \<rho>S) (eof n ks cs \<rho>E)
      else EFail)"
| "eof n ks cs (MLetPast p m kks \<phi> \<psi> i buf) =
     (if ecols kks = [0..<m] \<and> buf = None
      then ELetPast p m (eof m kks [0..<m] \<phi>) (eof n ks cs \<psi>) i None else EFail)"
| "eof n ks cs (MTrigger args \<phi> \<psi> buf nts aux) =
     (let kL = args_L args; kR = args_R args; cL = ecols kL in
      if ks = kR \<and> cs = ecols kR \<and> set kL \<subseteq> set kR \<and> mem (args_ivl args) 0 \<and>
         buf = ([], []) \<and> nts = []
      then ETrigger (eargs cs cL args) (emb_plan cs cL)
             (eof n kL cL \<phi>) (eof n kR cs \<psi>) (mbuf_t_empty, mbuf_t_empty) mbuf_t_empty
             (tw_init (eargs cs cL args) (emsk cs cL))
      else EFail)"
| "eof n ks cs (MRelease args \<phi> \<psi> buf nts t aux) =
     (let kL = args_L args; kR = args_R args; cL = ecols kL in
      if ks = kR \<and> cs = ecols kR \<and> set kL \<subseteq> set kR \<and> buf = ([], []) \<and> nts = [] \<and> aux = []
      then ERelease (eargs cs cL args) (emsk cs cL)
             (eof n kL cL \<phi>) (eof n kR cs \<psi>) (mbuf_t_empty, mbuf_t_empty) mbuf_t_empty t
             eraux_init
      else EFail)"
| "eof n ks cs (MAndTrigger k \<alpha> buf1 args \<phi> \<psi> buf2 nts aux) =
     (let kL = args_L args; kR = args_R args; cR = ecols kR; cL = ecols kL in
      if k = ks \<and> set kR \<subseteq> set ks \<and> set kL \<subseteq> set kR \<and>
         tok cR cL args \<and> buf1 = ([], []) \<and> buf2 = ([], []) \<and> nts = []
      then EAndTrigger (mk_djoin cs cR) (eof n ks cs \<alpha>) (mbuf_t_empty, mbuf_t_empty) (eargs cR cL args)
             (eof n kL cL \<phi>) (eof n kR cR \<psi>) (mbuf_t_empty, mbuf_t_empty) mbuf_t_empty
             (tw_init (eargs cR cL args) (emsk cR cL))
      else EFail)"
| "eof n ks cs (MMatchP I k dss mr mrs L buf nts aux) =
     (let css = map ecols dss in
      if k = ks \<and> length dss = length L \<and> length buf = length L \<and> (\<forall>b \<in> set buf. b = []) \<and>
         aux = [] \<and> (\<forall>c \<in> set css. set c \<subseteq> set cs)
      then EMatchP (length cs) I mr mrs (map (emb_plan cs) css)
             (map (\<lambda>(k, \<phi>). eof n k (ecols k) \<phi>) (zip dss L)) (map (\<lambda>_. mbuf_t_empty) L)
             (mbuf_t_empty @@ nts) []
      else EFail)"
| "eof n ks cs (MMatchF I k dss mr mrs L buf nts t aux) =
     (let css = map ecols dss in
      if k = ks \<and> length dss = length L \<and> length buf = length L \<and> (\<forall>b \<in> set buf. b = []) \<and>
         aux = [] \<and> (\<forall>c \<in> set css. set c \<subseteq> set cs)
      then EMatchF (length cs) I mr mrs (map (emb_plan cs) css)
             (map (\<lambda>(k, \<phi>). eof n k (ecols k) \<phi>) (zip dss L)) (map (\<lambda>_. mbuf_t_empty) L)
             (mbuf_t_empty @@ nts) t []
      else EFail)"
| "eof n ks cs (MTP mt i) = (if ks = mtrm_ecols mt \<and> cs = ks then ETP mt i else EFail)"
| "eof n ks cs (MTS mt) = (if ks = mtrm_ecols mt \<and> cs = ks then ETS mt else EFail)"
  by pat_completeness (simp_all only: prod.inject mformula.inject mformula.distinct simp_thms)

termination eof
  by (relation "measure (\<lambda>(n, ks, cs, \<phi>). size \<phi>)")
    (auto simp: termination_simp dest!: set_zip_rightD)

text \<open>The structures the compiler starts the nodes with, read through their representations.\<close>

lemma Rep_mbuf_t_empty[simp]: "Rep_mbuf_t mbuf_t_empty = []"
  by (rule mbuf_t_empty.rep_eq)

lemma Rep_mbuf_t_empty_append[simp]: "Rep_mbuf_t (mbuf_t_empty @@ xs) = xs"
  by (simp add: mbuf_t_append.rep_eq)

lemma rbufS_init[simp]: "rbufS init_mebuf2S = init_mbuf2S"
  by simp

lemma rdsx_udsx_init[simp]: "rdsx (udsx_init args msk) = esx_init args msk"
  by (rule esx_init_rdsx[symmetric])

lemma rdux_udux_init[simp]: "rdux (udux_init args) = eux_init args"
  by (rule eux_init_rdux[symmetric])

lemma rdux_udux_init_agg[simp]: "rdux (udux_init_agg args p) = eux_init_agg args p"
  by (rule eux_init_agg_rdux[symmetric])

subsection \<open>Column lists in ascending order\<close>

lemma set_ecols[simp]: "set (ecols k) = set k"
  by (simp add: ecols_def set_cols)

lemma ecols_Nil[simp]: "ecols [] = []"
  by (simp add: ecols_def set_cols_empty)

lemma eframe_dcols: "distinct k \<Longrightarrow> eframe k (ecols k)"
  by (simp add: ecols_def eframe_set_cols)

lemma ecols_cong: "set k = set k' \<Longrightarrow> ecols k = ecols k'"
  by (simp add: ecols_def)

lemma ecols_upt: "set k = {0..<m} \<Longrightarrow> ecols k = [0..<m]"
  by (simp add: ecols_def set_cols_upt)

lemma eframe_fv_list: "eframe (Formula.fv_list \<phi>) (ecols (Formula.fv_list \<phi>))"
  by (rule eframe_dcols[OF distinct_fvi_list])

subsection \<open>The kernel's initial state\<close>

lemma fv_list_and_release_safe_bounded:
  "Formula.fv (Formula.Release \<phi>' I \<psi>') \<subseteq> Formula.fv \<phi> \<Longrightarrow>
   Formula.fv_list (and_release_safe_bounded \<phi> \<phi>' I \<psi>')
     = Formula.fv_list (Formula.And \<phi> (Formula.Release \<phi>' I \<psi>'))"
  by (simp add: and_release_safe_bounded_def release_safe_bounded_def always_safe_bounded_def
      cols_union_subset)

text \<open>The fields of the kernel's initial state, read off @{const minit_safe}.\<close>

lemma minit_safe_state:
  assumes "mmonitorable \<phi>"
  shows "mstate_n (minit_safe \<phi>) = Formula.nfv \<phi>"
    and "mstate_m (minit_safe \<phi>) = minit0 (Formula.nfv \<phi>) \<phi>"
    and "mstate_i (minit_safe \<phi>) = 0" and "mstate_j (minit_safe \<phi>) = 0"
    and "mstate_t (minit_safe \<phi>) = []"
  using assms[unfolded monitorable_formula_code]
  by (simp_all add: default_maux.minit_safe_def default_maux.minit_def Let_def)

subsection \<open>The nodes the executable fragment does not cover\<close>

text \<open>
  @{const eof} is total, and answers @{const EFail} where it has no executable node or where a check
  fails.  Nothing relates @{const EFail} to a kernel formula, so every statement below is
  conditional on the compiled formula containing none of them -- @{term "eofz n \<phi>"} -- and each
  check of the compiler is then available as a fact.
\<close>

abbreviation (input) eofc :: "nat \<Rightarrow> ts \<Rightarrow> ty Formula.formula \<Rightarrow> bool" where
  "eofc n tw \<phi> \<equiv> esim n (Formula.fv_list \<phi>) (ecols (Formula.fv_list \<phi>)) tw
     (eof n (Formula.fv_list \<phi>) (ecols (Formula.fv_list \<phi>)) (minit0 n \<phi>)) (minit0 n \<phi>)"

abbreviation (input) eofz :: "nat \<Rightarrow> ty Formula.formula \<Rightarrow> bool" where
  "eofz n \<phi> \<equiv> efail_nodes (eof n (Formula.fv_list \<phi>) (ecols (Formula.fv_list \<phi>)) (minit0 n \<phi>)) = 0"

text \<open>A safe formula's initial state is a constant table only for an equality, whose table the
  kernel's correctness proof describes.\<close>

lemma esim_dof_minit0_rel:
  assumes s: "safe_formula \<phi>" and b: "\<forall>x \<in> Formula.fv \<phi>. x < n"
    and m: "minit0 n \<phi> = mformula.MRel rel"
  shows "eofc n tw \<phi>"
proof -
  have "kwf_mformula \<sigma> 0 Map.empty Map.empty n UNIV (mformula.MRel rel) \<phi>" for \<sigma>
    using kmaux_wf_minit0[OF s b, of Map.empty \<sigma> Map.empty UNIV] unfolding m by simp
  then obtain t1 t2 where \<phi>: "\<phi> = Formula.Eq t1 t2" and rel: "rel = eq_rel t1 t2"
    and simple: "is_simple_eq t1 t2" and fv1: "\<forall>x\<in>Formula.fv_trm t1. x < n" and fv2: "\<forall>x\<in>Formula.fv_trm t2. x < n"
    by (cases rule: kmaux_wf_mformula_cases) auto
  have "table (Formula.fv_list \<phi>) rel"
    using qtableD(1)[OF qtable_eq_relI[OF fv1 fv2 simple refl, of UNIV]] by (simp add: \<phi> rel)
  then show ?thesis
    unfolding m eof.simps by (rule EsRel[OF eframe_fv_list])
qed

subsection \<open>The temporal structures' initial states\<close>

lemma esince_rel_init:
  assumes a: "args = init_args I n kL kR pos agg"
    and fR: "eframe kR cR" and fL: "eframe kL cL" and sub: "set kL \<subseteq> set kR"
  shows "esince_rel kR cR kL cL args tw (init_mmasaux args)
     (esx_init (eargs cR cL args) (emsk cR cL)) init_mbuf2S init_mbuf2S"
proof -
  have v: "valid_mmasaux args 0 (init_mmasaux args) []"
    unfolding a by (rule valid_init_mmasaux[OF sub eframeD(1)[OF fL] eframeD(1)[OF fR]])
  have s: "esxaux' kR cR cL args 0 (esx_init (eargs cR cL args) (emsk cR cL)) []"
    by (rule esxaux'_init[OF fR fL sub])
  show ?thesis using esince_relI[OF v s, where tw = tw and kL = kL and xs = "[]" and ys = "[]" and tss = "[]"
      and sk = False] by (simp only: list.map list.pred_inject sorted0 list.set(1) empty_iff ball_empty le0
        simp_thms)
qed

lemma esince_rel_init_agg:
  assumes a: "args = init_args I n kL kR pos agg"
    and fR: "eframe kR cR" and fL: "eframe kL cL" and sub: "set kL \<subseteq> set kR"
    and c: "cL = []" and ok: "eagg_ok p (length cR)"
  shows "esince_rel kR cR kL cL args tw (init_mmasaux args)
     (esx_init_agg (eargs cR cL args) p) init_mbuf2S init_mbuf2S"
proof -
  have v: "valid_mmasaux args 0 (init_mmasaux args) []"
    unfolding a by (rule valid_init_mmasaux[OF sub eframeD(1)[OF fL] eframeD(1)[OF fR]])
  have s: "esxaux' kR cR cL args 0 (esx_init_agg (eargs cR cL args) p) []"
    by (rule esxaux'_init_agg[OF c ok])
  show ?thesis using esince_relI[OF v s, where tw = tw and kL = kL and xs = "[]" and ys = "[]" and tss = "[]"
      and sk = False] by (simp only: list.map list.pred_inject sorted0 list.set(1) empty_iff ball_empty le0
        simp_thms)
qed

lemma euntil_rel_init:
  assumes a: "args = init_args I n kL kR pos agg"
    and fR: "eframe kR cR" and fL: "eframe kL cL" and sub: "set kL \<subseteq> set kR"
  shows "euntil_rel kR cR kL cL args tw 0 (init_muaux_dq args)
     (eux_init (eargs cR cL args)) ([], []) ([], []) []"
proof -
  have v: "valid_muaux_dq args 0 (init_muaux_dq args) []"
    unfolding a by (rule valid_init_muaux_dq[OF sub eframeD(1)[OF fL] eframeD(1)[OF fR]])
  have s: "euxaux' kL cL kR cR args 0 (eux_init (eargs cR cL args)) []"
    by (rule euxaux'_init[OF fR fL sub])
  show ?thesis unfolding euntil_rel_def euaux_rel_def using v s by auto
qed

lemma euntil_rel_init_agg:
  assumes a: "args = init_args I n kL kR pos agg"
    and fR: "eframe kR cR" and fL: "eframe kL cL" and sub: "set kL \<subseteq> set kR"
    and c: "cL = []" and inz: "memL (args_ivl args) 0" and ok: "eagg_ok p (length cR)"
  shows "euntil_rel kR cR kL cL args tw 0 (init_muaux_dq args)
     (eux_init_agg (eargs cR cL args) p) ([], []) ([], []) []"
proof -
  have v: "valid_muaux_dq args 0 (init_muaux_dq args) []"
    unfolding a by (rule valid_init_muaux_dq[OF sub eframeD(1)[OF fL] eframeD(1)[OF fR]])
  have s: "euxaux' kL cL kR cR args 0 (eux_init_agg (eargs cR cL args) p) []"
    by (rule euxaux'_init_agg[OF c inz ok])
  show ?thesis unfolding euntil_rel_def euaux_rel_def using v s by auto
qed

lemma etrigger_rel_init:
  assumes a: "args = init_args I n kL kR pos agg"
    and fR: "eframe kR cR" and fL: "eframe kL cL" and sub: "set kL \<subseteq> set kR"
    and ok: "tok cR cL args"
  shows "etrigger_rel kR cR kL cL args tw (init_mmtaux args)
     (tw_init (eargs cR cL args) (emsk cR cL)) ([], []) ([], []) []"
proof -
  have i: "args_ivl args = I" and p: "args_pos args = pos" unfolding a by (simp_all add: init_args_def)
  have e: "cL = cR \<Longrightarrow> set kL = set kR" using eframeD(3)[OF fR] eframeD(3)[OF fL] by auto
  have v: "valid_mmtaux args 0 (init_mmtaux args) []"
    using valid_init_mmtaux[of I kL kR pos n agg] ok sub e eframeD(1)[OF fL] eframeD(1)[OF fR]
    unfolding a by (auto simp: tok_def init_args_def Let_def split: if_splits)
  have d: "etw kL cL kR cR args 0 (tw_init (eargs cR cL args) (emsk cR cL)) []"
    by (rule etw_init[OF ok])
  have "etrigger_rel kR cR kL cL args tw (init_mmtaux args)
      (tw_init (eargs cR cL args) (emsk cR cL)) ([], [])
      (map (etabc kL cL) [], map (etabc kR cR) []) []"
    by (rule etrigger_relI[OF v _ d]) simp_all
  then show ?thesis by (simp only: list.map)
qed

lemma eof_since_z:
  assumes "efail_nodes (eof n ks cs (MSince args \<phi> \<psi> buf aux)) = 0"
  shows "efail_nodes (eof (args_n args) (args_L args) (ecols (args_L args)) \<phi>) = 0"
    and "efail_nodes (eof (args_n args) (args_R args) (ecols (args_R args)) \<psi>) = 0"
  using assms by (cases "args_agg args"; auto simp: Let_def split: if_splits)+

lemma eof_until_z:
  assumes "efail_nodes (eof n ks cs (MUntil args \<phi> \<psi> buf nts t aux)) = 0"
  shows "efail_nodes (eof (args_n args) (args_L args) (ecols (args_L args)) \<phi>) = 0"
    and "efail_nodes (eof (args_n args) (args_R args) (ecols (args_R args)) \<psi>) = 0"
  using assms by (cases "args_agg args"; auto simp: Let_def split: if_splits)+

lemma esim_dof_since:
  assumes a: "args = init_args I n kL kR pos None"
    and s1: "esim n kL (ecols kL) tw (eof n kL (ecols kL) \<phi>) \<phi>"
    and s2: "esim n kR (ecols kR) tw (eof n kR (ecols kR) \<psi>) \<psi>"
    and dL: "distinct kL" and dR: "distinct kR" and sub: "set kL \<subseteq> set kR"
  shows "esim n kR (ecols kR) tw (eof n kR (ecols kR) (MSince args \<phi> \<psi> init_mbuf2S (init_mmasaux args)))
     (MSince args \<phi> \<psi> init_mbuf2S (init_mmasaux args))"
proof -
  have ag: "args_agg args = None" "args_n args = n" "args_L args = kL" "args_R args = kR"
    unfolding a by (simp_all add: init_args_def)
  have rl: "esince_rel kR (ecols kR) kL (ecols kL) args tw (init_mmasaux args)
      (esx_init (eargs (ecols kR) (ecols kL) args) (emsk (ecols kR) (ecols kL)))
      init_mbuf2S init_mbuf2S"
    by (rule esince_rel_init[OF a eframe_dcols[OF dR] eframe_dcols[OF dL] sub])
  show ?thesis
    by (simp add: ag sub Let_def del: init_mmasaux.simps)
      (rule EsSince[OF eframe_dcols[OF dR] _ _ sub ag(1,3,4) refl], use s1 s2 rl in \<open>simp_all add: ag\<close>)
qed

lemma esim_dof_until:
  assumes a: "args = init_args I n kL kR pos None"
    and s1: "esim n kL (ecols kL) tw (eof n kL (ecols kL) \<phi>) \<phi>"
    and s2: "esim n kR (ecols kR) tw (eof n kR (ecols kR) \<psi>) \<psi>"
    and dL: "distinct kL" and dR: "distinct kR" and sub: "set kL \<subseteq> set kR"
  shows "esim n kR (ecols kR) tw (eof n kR (ecols kR) (MUntil args \<phi> \<psi> ([], []) [] 0 (init_muaux_dq args)))
     (MUntil args \<phi> \<psi> ([], []) [] 0 (init_muaux_dq args))"
proof -
  have ag: "args_agg args = None" "args_n args = n" "args_L args = kL" "args_R args = kR"
    unfolding a by (simp_all add: init_args_def)
  have rl: "euntil_rel kR (ecols kR) kL (ecols kL) args tw 0 (init_muaux_dq args)
      (eux_init (eargs (ecols kR) (ecols kL) args)) ([], []) ([], []) []"
    by (rule euntil_rel_init[OF a eframe_dcols[OF dR] eframe_dcols[OF dL] sub])
  show ?thesis
    by (simp add: ag sub Let_def)
      (rule EsUntil[OF eframe_dcols[OF dR] _ _ sub ag(1,3,4) refl refl], use s1 s2 rl in \<open>simp_all add: ag\<close>)
qed

lemma esim_dof_neg:
  assumes fv: "Formula.fv \<phi> = {}" and sf: "safe_formula \<phi>"
    and b: "\<forall>x \<in> Formula.fv (Formula.Neg \<phi>). x < n" and z: "eofz n (Formula.Neg \<phi>)"
    and ih: "eofz n \<phi> \<Longrightarrow> eofc n tw \<phi>"
  shows "eofc n tw (Formula.Neg \<phi>)"
proof -
  have e: "Formula.fv_list \<phi> = []" using fv by (metis List.set_empty Formula.set_fvi_list)
  have s: "eofc n tw \<phi>" using z fv e by (intro ih) simp
  show ?thesis using s fv e by (auto intro!: EsNeg)
qed

lemma eof_trigger_z:
  assumes "efail_nodes (eof n ks cs (MTrigger args \<phi> \<psi> buf nts aux)) = 0"
  shows "efail_nodes (eof n (args_L args) (ecols (args_L args)) \<phi>) = 0"
    and "efail_nodes (eof n (args_R args) (ecols (args_R args)) \<psi>) = 0"
  using assms by (auto simp: Let_def split: if_splits)

lemma esim_dof_trigger:
  assumes a: "args = init_args I n kL kR pos None" and m0: "mem I 0"
    and s1: "esim n kL (ecols kL) tw (eof n kL (ecols kL) \<phi>) \<phi>"
    and s2: "esim n kR (ecols kR) tw (eof n kR (ecols kR) \<psi>) \<psi>"
    and dL: "distinct kL" and dR: "distinct kR" and sub: "set kL \<subseteq> set kR"
  shows "esim n kR (ecols kR) tw (eof n kR (ecols kR) (MTrigger args \<phi> \<psi> ([], []) [] (init_mmtaux args)))
     (MTrigger args \<phi> \<psi> ([], []) [] (init_mmtaux args))"
proof -
  have ag: "args_L args = kL" "args_R args = kR" "args_ivl args = I"
    unfolding a by (simp_all add: init_args_def)
  have ok: "tok (ecols kR) (ecols kL) args" by (rule tok_mem0) (simp add: ag m0)
  have rl: "etrigger_rel kR (ecols kR) kL (ecols kL) args tw (init_mmtaux args)
      (tw_init (eargs (ecols kR) (ecols kL) args) (emsk (ecols kR) (ecols kL)))
      ([], []) ([], []) []"
    by (rule etrigger_rel_init[OF a eframe_dcols[OF dR] eframe_dcols[OF dL] sub ok])
  show ?thesis
    by (simp add: ag sub m0 Let_def)
      (rule EsTrigger[OF eframe_dcols[OF dR] s1 s2 sub ag(1,2) _ refl refl], use rl in \<open>simp_all add: ag m0\<close>)
qed

lemma eof_release_z:
  assumes "efail_nodes (eof n ks cs (MRelease args \<phi> \<psi> buf nts t aux)) = 0"
  shows "efail_nodes (eof n (args_L args) (ecols (args_L args)) \<phi>) = 0"
    and "efail_nodes (eof n (args_R args) (ecols (args_R args)) \<psi>) = 0"
  using assms by (auto simp: Let_def split: if_splits)

lemma esim_dof_release:
  assumes a: "args = init_args I n kL kR pos None"
    and s1: "esim n kL (ecols kL) tw (eof n kL (ecols kL) \<phi>) \<phi>"
    and s2: "esim n kR (ecols kR) tw (eof n kR (ecols kR) \<psi>) \<psi>"
    and dL: "distinct kL" and dR: "distinct kR" and sub: "set kL \<subseteq> set kR"
  shows "esim n kR (ecols kR) tw (eof n kR (ecols kR) (MRelease args \<phi> \<psi> ([], []) [] 0 []))
     (MRelease args \<phi> \<psi> ([], []) [] 0 [])"
proof -
  have ag: "args_L args = kL" "args_R args = kR"
    unfolding a by (simp_all add: init_args_def)
  show ?thesis
    by (simp add: ag sub Let_def)
      (rule EsRelease[OF eframe_dcols[OF dR] s1 s2 sub ag refl refl],
        simp_all add: ebuf2_def erelease_rel_init)
qed

lemma esim_dof_minit0_trigger:
  assumes m0: "mem I 0" and sp: "safe_formula \<phi>" and sub: "Formula.fv \<phi> \<subseteq> Formula.fv \<psi>"
    and sft: "safe_formula (Formula.Trigger \<phi> I \<psi>)"
    and b: "\<forall>x \<in> Formula.fv (Formula.Trigger \<phi> I \<psi>). x < n" and z: "eofz n (Formula.Trigger \<phi> I \<psi>)"
    and i1: "eofz n \<phi> \<Longrightarrow> eofc n tw \<phi>" and i2: "eofz n \<psi> \<Longrightarrow> eofc n tw \<psi>"
  shows "eofc n tw (Formula.Trigger \<phi> I \<psi>)"
proof -
  let ?args = "init_args I n (Formula.fv_list \<phi>) (Formula.fv_list \<psi>) True None"
  have e: "Formula.fv_list (Formula.Trigger \<phi> I \<psi>) = Formula.fv_list \<psi>"
    using sub by (simp add: cols_union_subset)
  have m: "minit0 n (Formula.Trigger \<phi> I \<psi>) = MTrigger ?args
      (minit0 n \<phi>) (minit0 n \<psi>) ([], []) [] (init_mmtaux ?args)"
    using sp by (simp add: verimon_maux.init_trigger_def)
  note zz = eof_trigger_z[OF z[unfolded m e]]
  have s1: "eofc n tw \<phi>" using zz(1) by (intro i1) (simp add: init_args_def)
  have s2: "eofc n tw \<psi>" using zz(2) by (intro i2) (simp add: init_args_def)
  show ?thesis unfolding m e
    by (rule esim_dof_trigger[OF refl m0 s1 s2 distinct_fvi_list distinct_fvi_list])
      (simp add: sub)
qed

subsection \<open>Aggregations\<close>

lemma cpos_empty_Nil: "set c \<subseteq> set c' \<Longrightarrow> cpos c' (set c) = {} \<Longrightarrow> c = []"
  by (cases c) (auto simp: cpos_def in_set_conv_nth)

lemma esim_dof_agg:
  assumes z: "efail_nodes (eof n ks (ecols ks) (MAgg ag \<phi>)) = 0" and ek: "distinct ks"
    and s: "efail_nodes (eof (length (aggargs_tys ag) + n) (aggargs_cols ag)
        (ecols (aggargs_cols ag)) \<phi>) = 0 \<Longrightarrow>
      esim (length (aggargs_tys ag) + n) (aggargs_cols ag) (ecols (aggargs_cols ag)) tw
        (eof (length (aggargs_tys ag) + n) (aggargs_cols ag) (ecols (aggargs_cols ag)) \<phi>) \<phi>"
  shows "esim n ks (ecols ks) tw (eof n ks (ecols ks) (MAgg ag \<phi>)) (MAgg ag \<phi>)"
proof -
  let ?m = "length (aggargs_tys ag)" and ?g = "eagg_gcols ag" and ?y = "aggargs_y ag"
    and ?k0 = "aggargs_cols ag"
  have c: "ks = ?y # shift_cols ?m ?k0" "ecols ks = merge_cols ?g [?y]"
    "ecols ?k0 = agg_cols ?m ?g" "?y \<notin> set ?g" "aggargs_g0 ag \<longrightarrow> ?g = []"
    "Formula.fv_trm (aggargs_f ag) \<subseteq> set ?k0"
    using z by (simp_all add: Let_def split: if_splits)
  have d: "eof n ks (ecols ks) (MAgg ag \<phi>) = EAgg (aggargs_g0 ag) (aggargs_\<omega> ag)
      (reindex_trm (agg_cols ?m ?g) (aggargs_f ag)) ?m (ins_pos ?g ?y)
      (eof (?m + n) ?k0 (agg_cols ?m ?g) \<phi>)"
    using c by (simp add: Let_def)
  have zc: "efail_nodes (eof (?m + n) ?k0 (ecols ?k0) \<phi>) = 0" using z unfolding d c(3) by simp
  show ?thesis unfolding d
    by (rule EsAgg[OF eframe_dcols[OF ek] s[OF zc, unfolded c(3)] refl refl c(4) _ c(6) c(1,2)])
      (use c(5) in simp)
qed

lemma esim_dof_since_agg:
  assumes a: "args = init_args I nn kL kR pos (Some ag)"
    and s1: "esim nn kL (ecols kL) tw (eof nn kL (ecols kL) \<phi>) \<phi>"
    and s2: "esim nn kR (ecols kR) tw (eof nn kR (ecols kR) \<psi>) \<psi>"
    and dL: "distinct kL" and dR: "distinct kR" and ek: "distinct ks" and sub: "set kL \<subseteq> set kR"
    and z: "efail_nodes (eof n ks (ecols ks) (MSince args \<phi> \<psi> init_mbuf2S (init_mmasaux args))) = 0"
  shows "esim n ks (ecols ks) tw (eof n ks (ecols ks) (MSince args \<phi> \<psi> init_mbuf2S (init_mmasaux args)))
     (MSince args \<phi> \<psi> init_mbuf2S (init_mmasaux args))"
proof -
  let ?m = "length (aggargs_tys ag)" and ?g = "eagg_gcols ag" and ?y = "aggargs_y ag"
  let ?cL = "ecols kL" and ?cR = "ecols kR"
  let ?p = "(aggargs_g0 ag, aggargs_\<omega> ag, reindex_trm ?cR (aggargs_f ag), ?m, ins_pos ?g ?y)"
  have ag: "args_agg args = Some ag" "args_n args = nn" "args_L args = kL" "args_R args = kR"
    unfolding a by (simp_all add: init_args_def)
  have c: "aggargs_cols ag = kR" "agg_cols ?m ?g = ?cR" "ks = ?y # shift_cols ?m kR"
    "ecols ks = merge_cols ?g [?y]" "?y \<notin> set ?g" "aggargs_g0 ag \<longrightarrow> ?g = []"
    "Formula.fv_trm (aggargs_f ag) \<subseteq> set kR"
    using z by (simp_all add: ag Let_def sub split: if_splits)
  have rl: "esince_rel kR ?cR kL ?cL args tw (init_mmasaux args)
      (esx_init (eargs ?cR ?cL args) (emsk ?cR ?cL)) init_mbuf2S init_mbuf2S"
    by (rule esince_rel_init[OF a eframe_dcols[OF dR] eframe_dcols[OF dL] sub])
  show ?thesis
  proof (cases "cpos ?cR (set ?cL) = {}")
    case True
    have cL: "?cL = []" by (rule cpos_empty_Nil[OF _ True]) (simp add: sub)
    have ok: "eagg_ok ?p (length ?cR)"
      using eagg_ok_agg[of "aggargs_f ag" ?m ?g "aggargs_g0 ag" "aggargs_\<omega> ag" ?y] c(2,6,7)
      by simp
    have rla: "esince_rel kR ?cR kL ?cL args tw (init_mmasaux args)
        (esx_init_agg (eargs ?cR ?cL args) ?p) init_mbuf2S init_mbuf2S"
      by (rule esince_rel_init_agg[OF a eframe_dcols[OF dR] eframe_dcols[OF dL] sub cL ok])
    have d: "eof n ks (ecols ks) (MSince args \<phi> \<psi> init_mbuf2S (init_mmasaux args)) =
        ESince (eargs ?cR ?cL args) (eof nn kL ?cL \<phi>) (eof nn kR ?cR \<psi>) init_mebuf2S
          (udsx_init_agg (eargs ?cR ?cL args) ?p None)"
      using True c by (simp add: ag sub Let_def del: init_mmasaux.simps)
    show ?thesis unfolding d
      by (rule EsSinceFused[OF eframe_dcols[OF ek] _ _ sub ag(1,3,4) refl _ c(1) refl c(5) _ c(7)
            c(2)[symmetric] c(3,4)], use s1 s2 c(6) rla in \<open>simp_all add: ag\<close>)
  next
    case False
    have d: "eof n ks (ecols ks) (MSince args \<phi> \<psi> init_mbuf2S (init_mmasaux args)) =
        EAgg (aggargs_g0 ag) (aggargs_\<omega> ag) (reindex_trm ?cR (aggargs_f ag)) ?m (ins_pos ?g ?y)
          (ESince (eargs ?cR ?cL args) (eof nn kL ?cL \<phi>) (eof nn kR ?cR \<psi>) init_mebuf2S
            (udsx_init (eargs ?cR ?cL args) (emsk ?cR ?cL)))"
      using False c by (simp add: ag sub Let_def del: init_mmasaux.simps)
    show ?thesis unfolding d
      by (rule EsSinceAgg[OF eframe_dcols[OF ek] _ _ sub ag(1,3,4) refl _ c(1) refl c(5) _ c(7)
            c(2)[symmetric] c(3,4)], use s1 s2 c(6) rl in \<open>simp_all add: ag\<close>)
  qed
qed

lemma esim_dof_until_agg:
  assumes a: "args = init_args I nn kL kR pos (Some ag)"
    and s1: "esim nn kL (ecols kL) tw (eof nn kL (ecols kL) \<phi>) \<phi>"
    and s2: "esim nn kR (ecols kR) tw (eof nn kR (ecols kR) \<psi>) \<psi>"
    and dL: "distinct kL" and dR: "distinct kR" and ek: "distinct ks" and sub: "set kL \<subseteq> set kR"
    and z: "efail_nodes (eof n ks (ecols ks) (MUntil args \<phi> \<psi> ([], []) [] 0 (init_muaux_dq args))) = 0"
  shows "esim n ks (ecols ks) tw (eof n ks (ecols ks) (MUntil args \<phi> \<psi> ([], []) [] 0 (init_muaux_dq args)))
     (MUntil args \<phi> \<psi> ([], []) [] 0 (init_muaux_dq args))"
proof -
  let ?m = "length (aggargs_tys ag)" and ?g = "eagg_gcols ag" and ?y = "aggargs_y ag"
  let ?cL = "ecols kL" and ?cR = "ecols kR"
  let ?p = "(aggargs_g0 ag, aggargs_\<omega> ag, reindex_trm ?cR (aggargs_f ag), ?m, ins_pos ?g ?y)"
  have ag: "args_agg args = Some ag" "args_n args = nn" "args_L args = kL" "args_R args = kR"
    unfolding a by (simp_all add: init_args_def)
  have c: "aggargs_cols ag = kR" "agg_cols ?m ?g = ?cR" "ks = ?y # shift_cols ?m kR"
    "ecols ks = merge_cols ?g [?y]" "?y \<notin> set ?g" "aggargs_g0 ag \<longrightarrow> ?g = []"
    "Formula.fv_trm (aggargs_f ag) \<subseteq> set kR"
    using z by (simp_all add: ag Let_def sub split: if_splits)
  have rl: "euntil_rel kR ?cR kL ?cL args tw 0 (init_muaux_dq args)
      (eux_init (eargs ?cR ?cL args)) ([], []) ([], []) []"
    by (rule euntil_rel_init[OF a eframe_dcols[OF dR] eframe_dcols[OF dL] sub])
  show ?thesis
  proof (cases "cpos ?cR (set ?cL) = {} \<and> memL (args_ivl args) 0")
    case True
    have cL: "?cL = []" by (rule cpos_empty_Nil[OF _ conjunct1[OF True]]) (simp add: sub)
    have ok: "eagg_ok ?p (length ?cR)"
      using eagg_ok_agg[of "aggargs_f ag" ?m ?g "aggargs_g0 ag" "aggargs_\<omega> ag" ?y] c(2,6,7)
      by simp
    have rla: "euntil_rel kR ?cR kL ?cL args tw 0 (init_muaux_dq args)
        (eux_init_agg (eargs ?cR ?cL args) ?p) ([], []) ([], []) []"
      by (rule euntil_rel_init_agg[OF a eframe_dcols[OF dR] eframe_dcols[OF dL] sub cL
            conjunct2[OF True] ok])
    have d: "eof n ks (ecols ks) (MUntil args \<phi> \<psi> ([], []) [] 0 (init_muaux_dq args)) =
        EUntil (eargs ?cR ?cL args) (emsk ?cR ?cL) (eof nn kL ?cL \<phi>) (eof nn kR ?cR \<psi>)
          (mbuf_t_empty, mbuf_t_empty) mbuf_t_empty 0 (udux_init_agg (eargs ?cR ?cL args) ?p)"
      using True c by (simp add: ag sub Let_def)
    show ?thesis unfolding d
      by (rule EsUntilFused[OF eframe_dcols[OF ek] _ _ sub ag(1,3,4) refl refl _ _ c(1) refl c(5) _
            c(7) c(2)[symmetric] c(3,4)], use s1 s2 c(6) rla in \<open>simp_all add: ag\<close>)
  next
    case False
    have d: "eof n ks (ecols ks) (MUntil args \<phi> \<psi> ([], []) [] 0 (init_muaux_dq args)) =
        EAgg (aggargs_g0 ag) (aggargs_\<omega> ag) (reindex_trm ?cR (aggargs_f ag)) ?m (ins_pos ?g ?y)
          (EUntil (eargs ?cR ?cL args) (emsk ?cR ?cL) (eof nn kL ?cL \<phi>) (eof nn kR ?cR \<psi>)
            (mbuf_t_empty, mbuf_t_empty) mbuf_t_empty 0 (udux_init (eargs ?cR ?cL args)))"
      using False c by (simp add: ag sub Let_def)
    show ?thesis unfolding d
      by (rule EsUntilAgg[OF eframe_dcols[OF ek] _ _ sub ag(1,3,4) refl refl _ _ c(1) refl c(5) _
            c(7) c(2)[symmetric] c(3,4)], use s1 s2 c(6) rl in \<open>simp_all add: ag\<close>)
  qed
qed

subsection \<open>The guard\<close>

text \<open>A constraint over a node goes into the node as its guard exactly when the node is a fused
  aggregating Since without one; the node is then related to the kernel's constraint over the
  kernel's node by the rule for the guarded Since, and otherwise the constraint stays above it.\<close>

lemma esim_eset_q:
  assumes s: "esim n ks cs tw d \<phi>"
    and wf: "eframe ks cs"
    and fv1: "Formula.fv_trm t1 \<subseteq> set cs" and fv2: "Formula.fv_trm t2 \<subseteq> set cs"
  shows "esim n ks cs tw (case eset_q (reindex_constraint cs (t1, p, c, t2)) d of
      Some d' \<Rightarrow> d' | None \<Rightarrow> EAndRel d (reindex_constraint cs (t1, p, c, t2)))
    (MAndRel ks \<phi> (t1, p, c, t2))"
proof (cases "eset_q (reindex_constraint cs (t1, p, c, t2)) d")
  case None
  then show ?thesis using EsAndRel[OF wf s fv1 fv2] by simp
next
  case (Some d')
  then obtain dags \<phi>d \<psi>d dbuf ap a where d: "d = ESince dags \<phi>d \<psi>d dbuf (UDSX_wagg ap None a)"
    and d': "d' = ESince dags \<phi>d \<psi>d dbuf (UDSX_wagg ap (Some (reindex_constraint cs (t1, p, c, t2))) a)"
    using Some by (cases d) (auto split: udsaux_x.splits option.splits)
  have "esim n ks cs tw d' (MAndRel ks \<phi> (t1, p, c, t2))"
    using s[unfolded d]
  proof (cases rule: esim.cases)
    case EsSince
    then show ?thesis by simp
  next
    case (EsSinceFused args \<phi>' \<psi> buf aux kL cL kR cR ag y gcols)
    show ?thesis unfolding d' EsSinceFused(1)
      by (rule esim.EsSinceGuard[OF wf]) (use EsSinceFused fv1 fv2 in simp_all)
  next
    case EsSinceGuard
    then show ?thesis by simp
  qed
  then show ?thesis using Some by simp
qed

subsection \<open>The compiler produces a simulation\<close>

theorem esim_dof_minit0:
  "safe_formula \<phi> \<Longrightarrow> \<forall>x \<in> Formula.fv \<phi>. x < n \<Longrightarrow> eofz n \<phi> \<Longrightarrow> eofc n tw \<phi>"
proof (induction arbitrary: n rule: safe_formula_induct)
  case (Eq_Const c d)
  show ?case by (rule esim_dof_minit0_rel[OF _ Eq_Const.prems(1)]) simp_all
next
  case (Eq_Var1 c x)
  show ?case by (rule esim_dof_minit0_rel[OF _ Eq_Var1.prems(1)]) simp_all
next
  case (Eq_Var2 c x)
  show ?case by (rule esim_dof_minit0_rel[OF _ Eq_Var2.prems(1)]) simp_all
next
  case (Pred e ts)
  show ?case using Pred.prems(2) eframe_fv_list[of "Formula.Pred e ts"]
    by (cases "pred_mode_of n ts") (auto split: if_splits intro: esim.intros)
next
  case (Let p \<phi> \<psi>)
  have c: "ecols (Formula.fv_list \<phi>) = [0..<Formula.nfv \<phi>]"
    by (rule ecols_upt) (use Let.hyps(1) fvi_less_nfv[of \<phi>] in auto)
  have z1: "eofz (Formula.nfv \<phi>) \<phi>" and z2: "eofz n \<psi>"
    using Let.prems(2) unfolding c by (simp_all split: if_splits)
  have s1: "eofc (Formula.nfv \<phi>) tw \<phi>" by (rule Let.IH(1)[OF fvi_less_nfv z1])
  have s2: "eofc n tw \<psi>" using Let.prems(1) z2 by (intro Let.IH(2)) simp_all
  show ?case using s1[unfolded c] s2 eframe_fv_list[of \<psi>] c by (auto intro!: EsLet)
next
  case (Frz p \<phi> \<psi>)
  have c: "ecols (Formula.fv_list \<phi>) = [0..<Formula.nfv \<phi>]"
    by (rule ecols_upt) (use Frz.hyps(1) fvi_less_nfv[of \<phi>] in auto)
  have z1: "eofz (Formula.nfv \<phi>) \<phi>" and z2: "eofz n \<psi>"
    using Frz.prems(2) unfolding c by (simp_all split: if_splits)
  have s1: "eofc (Formula.nfv \<phi>) tw \<phi>" by (rule Frz.IH(1)[OF fvi_less_nfv z1])
  have s2: "eofc n tw \<psi>" using Frz.prems(1) z2 by (intro Frz.IH(2)) simp_all
  have sx: "map_frz_sep id (etabc (Formula.fv_list \<psi>) (ecols (Formula.fv_list \<psi>)))
      (frz_sep_init (p, Formula.nfv \<phi>) \<psi> :: (event_data list set, event_data table) frz_sep) =
    frz_sep_init (p, Formula.nfv \<phi>) \<psi>"
    by (simp add: frz_sep_init_def)
  have nsep: "(frz_sep_init (p, Formula.nfv \<phi>) \<psi> :: (event_data list set, event_data table) frz_sep) \<noteq>
      FSSep L nL pX buf rg bo tk Lr" for L nL pX buf rg bo tk Lr
    by (simp add: frz_sep_init_def)
  have ncase: "(case frz_sep_init (p, Formula.nfv \<phi>) \<psi> :: (event_data list set, event_data table) frz_sep of
      FSSep _ _ _ _ _ _ _ _ \<Rightarrow> False | _ \<Rightarrow> True)"
    by (simp add: frz_sep_init_def)
  show ?case using s1[unfolded c] s2 eframe_fv_list[of \<psi>] c nsep ncase
    by (auto intro!: EsFrz[where rb = "[]" and sx = "frz_sep_init (p, Formula.nfv \<phi>) \<psi>"
      and ks = "Formula.fv_list \<psi>" and cs = "ecols (Formula.fv_list \<psi>)", unfolded list.map(1) sx])
next
  case (LetPast p \<phi> \<psi>)
  have c: "ecols (Formula.fv_list \<phi>) = [0..<Formula.nfv \<phi>]"
    by (rule ecols_upt) (use LetPast.hyps(2) fvi_less_nfv[of \<phi>] in auto)
  have z1: "eofz (Formula.nfv \<phi>) \<phi>" and z2: "eofz n \<psi>"
    using LetPast.prems(2) unfolding c by (simp_all split: if_splits)
  have s1: "eofc (Formula.nfv \<phi>) tw \<phi>" by (rule LetPast.IH(1)[OF fvi_less_nfv z1])
  have s2: "eofc n tw \<psi>" using LetPast.prems(1) z2 by (intro LetPast.IH(2)) simp_all
  show ?case using s1[unfolded c] s2 eframe_fv_list[of \<psi>] c by (auto intro!: EsLetPast)
next
  case (And_assign \<phi> \<psi>)
  obtain y t where sp: "split_assignment (Formula.fv \<phi>) \<psi> = (y, t)"
    by (cases "split_assignment (Formula.fv \<phi>) \<psi>") auto
  have m: "minit0 n (Formula.And \<phi> \<psi>) = MAndAssign (Formula.fv_list \<phi>) (minit0 n \<phi>) (y, t)"
    using And_assign.hyps(2) sp by simp
  have z: "eofz n \<phi>" using And_assign.prems(2) unfolding m by (simp add: Let_def split: if_splits)
  have s: "eofc n tw \<phi>" using And_assign.prems(1) z by (intro And_assign.IH) simp_all
  show ?case using And_assign.prems(2) s eframe_fv_list[of "Formula.And \<phi> \<psi>"] unfolding m
    by (auto simp: Let_def split: if_splits intro!: EsAndAssign)
next
  case (And_safe \<phi> \<psi>)
  have m: "minit0 n (Formula.And \<phi> \<psi>) = MAnd (Formula.fv_list \<phi>)
      (minit0 n \<phi>) True (Formula.fv_list \<psi>) (minit0 n \<psi>) ([], [])"
    using And_safe.hyps by simp
  have z1: "eofz n \<phi>" and z2: "eofz n \<psi>"
    using And_safe.prems(2) unfolding m by (simp_all add: Let_def split: if_splits)
  have s1: "eofc n tw \<phi>" using And_safe.prems(1) z1 by (intro And_safe.IH(1)) simp_all
  have s2: "eofc n tw \<psi>" using And_safe.prems(1) z2 by (intro And_safe.IH(2)) simp_all
  show ?case using And_safe.prems(2) s1 s2 eframe_fv_list[of "Formula.And \<phi> \<psi>"] unfolding m
    by (auto simp: Let_def ebuf2_def split: if_splits intro!: EsAnd)
next
  case (And_constraint \<phi> \<psi>)
  obtain t1 p c t2 where sc: "split_constraint \<psi> = (t1, p, c, t2)"
    by (cases "split_constraint \<psi>") auto
  have m: "minit0 n (Formula.And \<phi> \<psi>) = MAndRel (Formula.fv_list \<phi>) (minit0 n \<phi>) (t1, p, c, t2)"
    using And_constraint.hyps sc by simp
  have e: "Formula.fv_list (Formula.And \<phi> \<psi>) = Formula.fv_list \<phi>"
    using And_constraint.hyps(4) by (simp add: cols_union_subset)
  have z: "eofz n \<phi>" using And_constraint.prems(2) unfolding m e
    by (auto simp: Let_def efail_nodes_eset_q split: if_splits option.splits)
  have s: "eofc n tw \<phi>" using And_constraint.prems(1) z by (intro And_constraint.IH) simp_all
  have fv: "Formula.fv_trm t1 \<subseteq> set (ecols (Formula.fv_list \<phi>))"
    "Formula.fv_trm t2 \<subseteq> set (ecols (Formula.fv_list \<phi>))"
    using And_constraint.prems(2) unfolding m e by (simp_all split: if_splits)
  show ?case unfolding m e using fv
    by (simp add: Let_def esim_eset_q[OF s eframe_fv_list])
next
  case (And_Not \<phi> \<psi>)
  have m: "minit0 n (Formula.And \<phi> (Formula.Neg \<psi>)) = MAnd (Formula.fv_list \<phi>)
      (minit0 n \<phi>) False (Formula.fv_list \<psi>) (minit0 n \<psi>) ([], [])"
    using And_Not.hyps by simp
  have z1: "eofz n \<phi>" and z2: "eofz n \<psi>"
    using And_Not.prems(2) unfolding m by (simp_all add: Let_def split: if_splits)
  have s1: "eofc n tw \<phi>" using And_Not.prems(1) z1 by (intro And_Not.IH(1)) simp_all
  have s2: "eofc n tw \<psi>" using And_Not.prems(1) z2 by (intro And_Not.IH(2)) simp_all
  show ?case using And_Not.prems(2) s1 s2 eframe_fv_list[of "Formula.And \<phi> (Formula.Neg \<psi>)"]
    unfolding m by (auto simp: Let_def ebuf2_def split: if_splits intro!: EsAnd)
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
    have z1: "eofz n \<phi>" and z2: "eofz n (Formula.Trigger \<phi>' I \<psi>')"
      using And_Trigger.prems(2) unfolding m by (simp_all add: Let_def split: if_splits)
    have s1: "eofc n tw \<phi>" by (rule And_Trigger.IH(1)[OF bA z1])
    have s2: "eofc n tw (Formula.Trigger \<phi>' I \<psi>')"
      by (rule esim_dof_minit0_trigger[OF True sp' sub st _ z2])
        (use bR sub And_Trigger.IH(2,3) bL in auto)
    show ?thesis
      using And_Trigger.prems(2) s1 s2 eframe_fv_list[of "Formula.And \<phi> (Formula.Trigger \<phi>' I \<psi>')"]
      unfolding m by (auto simp: Let_def ebuf2_def split: if_splits intro!: EsAnd)
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
    have zz: "efail_nodes (eof n (Formula.fv_list \<phi>) (ecols (Formula.fv_list \<phi>))
        (MAndTrigger (Formula.fv_list \<phi>) (minit0 n \<phi>) ([], []) ?args
          (minit0 n \<phi>') (minit0 n \<psi>') ([], []) [] (init_mmtaux ?args))) = 0"
      using And_Trigger.prems(2) unfolding m e .
    have ok: "tok (ecols (Formula.fv_list \<psi>')) (ecols (Formula.fv_list \<phi>')) ?args"
      using zz by (simp add: Let_def ag split: if_splits)
    have z1: "eofz n \<phi>" and z2: "eofz n \<phi>'" and z3: "eofz n \<psi>'"
      using zz by (simp_all add: Let_def ag split: if_splits)
    have s1: "eofc n tw \<phi>" by (rule And_Trigger.IH(1)[OF bA z1])
    have s2: "eofc n tw \<phi>'" by (rule And_Trigger.IH(2)[OF bL z2])
    have s3: "eofc n tw \<psi>'" by (rule And_Trigger.IH(3)[OF bR z3])
    have rl: "etrigger_rel (Formula.fv_list \<psi>') (ecols (Formula.fv_list \<psi>'))
        (Formula.fv_list \<phi>') (ecols (Formula.fv_list \<phi>')) ?args tw (init_mmtaux ?args)
        (tw_init (eargs (ecols (Formula.fv_list \<psi>')) (ecols (Formula.fv_list \<phi>')) ?args)
          (emsk (ecols (Formula.fv_list \<psi>')) (ecols (Formula.fv_list \<phi>'))))
        ([], []) ([], []) []"
      by (rule etrigger_rel_init[OF refl eframe_fv_list eframe_fv_list _ ok]) (simp add: sub)
    show ?thesis unfolding m e
      by (simp add: Let_def ag sub subR ok)
        (rule EsAndTrigger[OF eframe_fv_list s1 s2 s3 _ _ ag(1,2) ok refl refl],
          use rl in \<open>simp_all add: sub subR eandbuf_def\<close>)
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
  have part: "pos = filter safe_formula l" and negd: "neg = filter (\<lambda>a. \<not> safe_formula a) l"
    using Ands.hyps(1) by (auto simp: o_def)
  have setl: "set l = set pos \<union> set neg" using part negd by auto
  have lenl: "length l = length pos + length neg" using part negd
    by (simp add: sum_length_filter_compl)
  obtain p ps where pl: "pos = p # ps" using Ands.hyps(2) by (cases pos) auto
  have b: "\<forall>x \<in> \<Union> (Formula.fv ` set pos). x < n" using Ands.prems setl by auto
  have bn: "\<forall>x \<in> \<Union> (Formula.fv ` set neg). x < n" using b Ands.hyps(5) by blast
  define Ks where "Ks = map Formula.fv_list pos @ map Formula.fv_list neg"
  define L where "L = map (minit0 n) pos @ map (minit0 n) (map remove_neg neg)"
  define Ld where "Ld = map (\<lambda>(k, \<phi>). eof n k (ecols k) \<phi>) (zip Ks L)"
  let ?c0 = "ecols (Formula.fv_list p)"
  let ?css = "map ecols (map Formula.fv_list ps)"
  let ?nss = "map ecols (map Formula.fv_list neg)"
  have e1: "Formula.fv_list p # map Formula.fv_list ps @ map Formula.fv_list neg = Ks"
    by (simp add: Ks_def pl)
  have e2: "?c0 # ?css @ ?nss = map ecols Ks" unfolding e1[symmetric] by simp
  have lK: "length Ks = length L" by (simp add: Ks_def L_def)
  have lLd: "length Ld = length L" by (simp add: Ld_def lK)
  have Ldi: "\<And>i. i < length L \<Longrightarrow> Ld ! i = eof n (Ks ! i) (ecols (Ks ! i)) (L ! i)"
    by (simp add: Ld_def lK)
  have fvrn: "\<And>\<chi>. Formula.fv_list (remove_neg \<chi>) = Formula.fv_list \<chi>"
    by (case_tac \<chi>) simp_all
  have m: "minit0 n (Formula.Ands l) = MAnds (Formula.fv_list (Formula.Ands l))
      (Formula.fv_list p # map Formula.fv_list ps) (map Formula.fv_list neg) L
      (replicate (length l) [])"
    using Ands.hyps(1)[symmetric] pl by (simp add: Let_def L_def)
  have zz: "efail_nodes (eof n (Formula.fv_list (Formula.Ands l)) (ecols (Formula.fv_list (Formula.Ands l)))
      (MAnds (Formula.fv_list (Formula.Ands l)) (Formula.fv_list p # map Formula.fv_list ps)
        (map Formula.fv_list neg) L (replicate (length l) []))) = 0"
    using Ands.prems(2) unfolding m .
  have lenL: "length L = length l" by (simp add: L_def lenl)
  have chk: "ecols (Formula.fv_list (Formula.Ands l)) = eands_cols ?c0 ?css \<and>
      (\<forall>c \<in> set ?nss. set c \<subseteq> set (eands_cols ?c0 ?css))"
    using zz lenL pl by (auto simp: Let_def split: if_splits)
  have d: "eof n (Formula.fv_list (Formula.Ands l)) (ecols (Formula.fv_list (Formula.Ands l)))
      (MAnds (Formula.fv_list (Formula.Ands l)) (Formula.fv_list p # map Formula.fv_list ps)
        (map Formula.fv_list neg) L (replicate (length l) []))
    = EAnds (eands_plans ?c0 ?css) (eands_plans (eands_cols ?c0 ?css) ?nss) Ld (map (\<lambda>_. mbuf_t_empty) L)"
    using chk lenL lenl pl unfolding Ld_def e1[symmetric] by (simp add: Let_def)
  have zall: "\<forall>x \<in> set Ld. efail_nodes x = 0" using zz unfolding d by simp
  have zi: "\<And>i. i < length L \<Longrightarrow> efail_nodes (eof n (Ks ! i) (ecols (Ks ! i)) (L ! i)) = 0"
    using zall Ldi lLd by (metis nth_mem)
  have pL: "\<forall>i < length L. esim n (Ks ! i) (ecols (Ks ! i)) tw (Ld ! i) (L ! i)"
  proof (intro allI impI)
    fix i assume i: "i < length L"
    show "esim n (Ks ! i) (ecols (Ks ! i)) tw (Ld ! i) (L ! i)"
      unfolding Ldi[OF i]
    proof (cases "i < length pos")
      case True
      then have c: "Ks ! i = Formula.fv_list (pos ! i)" and l': "L ! i = minit0 n (pos ! i)"
        by (simp_all add: Ks_def L_def nth_append)
      have ip: "pos ! i \<in> set pos" using True by simp
      have bi: "\<forall>x \<in> Formula.fv (pos ! i). x < n" using b ip by auto
      show "esim n (Ks ! i) (ecols (Ks ! i)) tw (eof n (Ks ! i) (ecols (Ks ! i)) (L ! i)) (L ! i)"
        using Ands.IH(1)[unfolded list_all_iff] ip bi zi[OF i] unfolding c l' by blast
    next
      case False
      let ?j = "i - length pos"
      have j: "?j < length neg" using i False by (simp add: L_def)
      have c: "Ks ! i = Formula.fv_list (remove_neg (neg ! ?j))"
        using False j by (simp add: Ks_def nth_append fvrn)
      have l': "L ! i = minit0 n (remove_neg (neg ! ?j))"
        using False j by (simp add: L_def nth_append)
      have ip: "remove_neg (neg ! ?j) \<in> set (map remove_neg neg)" using j by simp
      have bi: "\<forall>x \<in> Formula.fv (remove_neg (neg ! ?j)). x < n"
        using bn j by (auto simp: fv_remove_neg[symmetric])
      show "esim n (Ks ! i) (ecols (Ks ! i)) tw (eof n (Ks ! i) (ecols (Ks ! i)) (L ! i)) (L ! i)"
        using Ands.IH(2)[unfolded list_all_iff] ip bi zi[OF i] unfolding c l' by blast
    qed
  qed
  have pL': "\<forall>i < length L. esim n ((Formula.fv_list p # map Formula.fv_list ps @ map Formula.fv_list neg) ! i)
      ((?c0 # ?css @ ?nss) ! i) tw (Ld ! i) (L ! i)"
    unfolding e1 e2 using pL lK by simp
  have sfa: "safe_formula (Formula.Ands l)" using Ands.hyps by (auto simp: list_all_iff)
  have bf: "ebufn (Formula.fv_list p # map Formula.fv_list ps @ map Formula.fv_list neg)
      (?c0 # ?css @ ?nss) (replicate (length l) []) (map Rep_mbuf_t (map (\<lambda>_. mbuf_t_empty) L))"
    unfolding e1 e2 using lK lenL by (auto simp: ebufn_def intro!: nth_equalityI)
  show ?case unfolding m d
    by (rule EsAnds[OF eframe_fv_list pL' _ _ _ _ _ _ refl refl bf])
      (use chk lK lLd lenL pl in \<open>simp_all add: Ks_def\<close>)
next
  case (Neg \<phi>)
  show ?case by (rule esim_dof_neg[OF Neg.hyps(1,2) Neg.prems]) (use Neg.IH Neg.hyps(1) in simp)
next
  case (Or \<phi> \<psi>)
  have e: "Formula.fv_list (Formula.Or \<phi> \<psi>) = Formula.fv_list \<phi>"
    using Or.hyps(1) by (simp add: cols_union_subset)
  have c: "ecols (Formula.fv_list \<psi>) = ecols (Formula.fv_list \<phi>)"
    using Or.hyps(1) by (intro ecols_cong) simp
  have z1: "eofz n \<phi>" and z2: "eofz n \<psi>" using Or.prems(2) Or.hyps(1) unfolding e c by simp_all
  have s1: "eofc n tw \<phi>" using Or.prems(1) z1 by (intro Or.IH(1)) simp_all
  have s2: "eofc n tw \<psi>" using Or.prems(1) z2 Or.hyps(1) by (intro Or.IH(2)) simp_all
  show ?case unfolding e using s1 s2[unfolded c] eframe_fv_list[of \<phi>] Or.hyps(1)
    by (auto simp: ebuf2_def intro!: EsOr)
next
  case (Exists t \<phi>)
  have b: "\<forall>x \<in> Formula.fv \<phi>. x < Suc n"
    using fvi_Suc_bound[where b = 0 and \<phi> = \<phi> and n = n] Exists.prems by simp
  have e: "Formula.fv_list (Formula.Exists t \<phi>) = ex_cols (Formula.fv_list \<phi>)"
    by (simp add: fvi_list_Suc)
  have z: "eofz (Suc n) \<phi>" using Exists.prems(2) by (simp add: Let_def split: if_splits)
  have s: "eofc (Suc n) tw \<phi>" by (rule Exists.IH[OF b z])
  show ?case using Exists.prems(2) s eframe_fv_list[of "Formula.Exists t \<phi>"]
    by (auto simp: Let_def split: if_splits intro!: EsExists)
next
  case (Agg y \<omega> tys f \<phi>)
  note sf = \<open>safe_formula \<phi>\<close>
  have sfa: "safe_formula (Formula.Agg y \<omega> tys f \<phi>)" using Agg.hyps by simp
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
      then have "x - length tys < n" using Agg.prems(1) by blast
      then show ?thesis using False by simp
    qed
  qed
  let ?ag = "init_aggargs (Formula.fv_list \<phi>) n (Formula.fv \<phi> \<subseteq> {0..<length tys}) y \<omega> tys f"
  have ag: "aggargs_cols ?ag = Formula.fv_list \<phi>" "aggargs_tys ?ag = tys"
    by (simp_all add: init_aggargs_def)
  have D: "minit0 n (Formula.Agg y \<omega> tys f \<phi>) = MAgg ?ag (minit0 (length tys + n) \<phi>) \<Longrightarrow>
      eofc n tw (Formula.Agg y \<omega> tys f \<phi>)"
  proof -
    assume m: "minit0 n (Formula.Agg y \<omega> tys f \<phi>) = MAgg ?ag (minit0 (length tys + n) \<phi>)"
    show ?thesis unfolding m
      by (rule esim_dof_agg[OF Agg.prems(2)[unfolded m] distinct_fvi_list])
        (unfold ag, rule Agg.IH[OF order_refl sf bp])
  qed
  show ?case
  proof (cases \<phi>)
    case (Since \<chi> I \<eta>)
    have s: "Formula.fv \<chi> \<subseteq> Formula.fv \<eta>" and se: "safe_formula \<eta>"
      and sc: "safe_formula \<chi> \<or> (case \<chi> of Formula.Neg \<chi>' \<Rightarrow> safe_formula \<chi>' | _ \<Rightarrow> False)"
      using sf unfolding Since by auto
    have bR: "\<forall>x \<in> Formula.fv \<eta>. x < length tys + n" using bp Since by simp
    have bL: "\<forall>x \<in> Formula.fv \<chi>. x < length tys + n" using bR s by auto
    show ?thesis
    proof (cases "safe_formula \<chi>")
      case True
      let ?args = "init_args I (length tys + n) (Formula.fv_list \<chi>) (Formula.fv_list \<eta>) True (Some ?ag)"
      have m: "minit0 n (Formula.Agg y \<omega> tys f \<phi>) = MSince ?args
          (minit0 (length tys + n) \<chi>) (minit0 (length tys + n) \<eta>) init_mbuf2S (init_mmasaux ?args)"
        using True unfolding Since by (simp add: Let_def default_mmasaux.init_since_def)
      note zz = Agg.prems(2)[unfolded m]
      note z = eof_since_z[OF zz]
      have s1: "eofc (length tys + n) tw \<chi>"
        by (rule Agg.IH[OF _ True bL]) (use z(1) in \<open>simp_all add: Since init_args_def\<close>)
      have s2: "eofc (length tys + n) tw \<eta>"
        by (rule Agg.IH[OF _ se bR]) (use z(2) in \<open>simp_all add: Since init_args_def\<close>)
      show ?thesis unfolding m
        by (rule esim_dof_since_agg[OF refl s1 s2 distinct_fvi_list distinct_fvi_list
              distinct_fvi_list _ zz]) (simp add: s)
    next
      case False
      then obtain \<chi>' where chi: "\<chi> = Formula.Neg \<chi>'" and sc': "safe_formula \<chi>'"
        using sc by (cases \<chi>) auto
      have fvc: "Formula.fv_list \<chi>' = Formula.fv_list \<chi>" using chi by simp
      have bL': "\<forall>x \<in> Formula.fv \<chi>'. x < length tys + n" using bL chi by simp
      let ?args = "init_args I (length tys + n) (Formula.fv_list \<chi>') (Formula.fv_list \<eta>) False (Some ?ag)"
      have m: "minit0 n (Formula.Agg y \<omega> tys f \<phi>) = MSince ?args
          (minit0 (length tys + n) \<chi>') (minit0 (length tys + n) \<eta>) init_mbuf2S (init_mmasaux ?args)"
        using False chi unfolding Since by (simp add: Let_def default_mmasaux.init_since_def)
      note zz = Agg.prems(2)[unfolded m]
      note z = eof_since_z[OF zz]
      have s1: "eofc (length tys + n) tw \<chi>'"
        by (rule Agg.IH[OF _ sc' bL']) (use z(1) in \<open>simp_all add: Since chi init_args_def\<close>)
      have s2: "eofc (length tys + n) tw \<eta>"
        by (rule Agg.IH[OF _ se bR]) (use z(2) in \<open>simp_all add: Since init_args_def\<close>)
      show ?thesis unfolding m
        by (rule esim_dof_since_agg[OF refl s1 s2 distinct_fvi_list distinct_fvi_list
              distinct_fvi_list _ zz]) (use s chi in simp)
    qed
  next
    case (Until \<chi> I \<eta>)
    have s: "Formula.fv \<chi> \<subseteq> Formula.fv \<eta>" and se: "safe_formula \<eta>"
      and sc: "safe_formula \<chi> \<or> (case \<chi> of Formula.Neg \<chi>' \<Rightarrow> safe_formula \<chi>' | _ \<Rightarrow> False)"
      using sf unfolding Until by auto
    have bR: "\<forall>x \<in> Formula.fv \<eta>. x < length tys + n" using bp Until by simp
    have bL: "\<forall>x \<in> Formula.fv \<chi>. x < length tys + n" using bR s by auto
    show ?thesis
    proof (cases "safe_formula \<chi>")
      case True
      let ?args = "init_args I (length tys + n) (Formula.fv_list \<chi>) (Formula.fv_list \<eta>) True (Some ?ag)"
      have m: "minit0 n (Formula.Agg y \<omega> tys f \<phi>) = MUntil ?args
          (minit0 (length tys + n) \<chi>) (minit0 (length tys + n) \<eta>) ([], []) [] 0 (init_muaux_dq ?args)"
        using True unfolding Until by (simp add: Let_def dq_muaux.init_until_def)
      note zz = Agg.prems(2)[unfolded m]
      note z = eof_until_z[OF zz]
      have s1: "eofc (length tys + n) tw \<chi>"
        by (rule Agg.IH[OF _ True bL]) (use z(1) in \<open>simp_all add: Until init_args_def\<close>)
      have s2: "eofc (length tys + n) tw \<eta>"
        by (rule Agg.IH[OF _ se bR]) (use z(2) in \<open>simp_all add: Until init_args_def\<close>)
      show ?thesis unfolding m
        by (rule esim_dof_until_agg[OF refl s1 s2 distinct_fvi_list distinct_fvi_list
              distinct_fvi_list _ zz]) (simp add: s)
    next
      case False
      then obtain \<chi>' where chi: "\<chi> = Formula.Neg \<chi>'" and sc': "safe_formula \<chi>'"
        using sc by (cases \<chi>) auto
      have bL': "\<forall>x \<in> Formula.fv \<chi>'. x < length tys + n" using bL chi by simp
      let ?args = "init_args I (length tys + n) (Formula.fv_list \<chi>') (Formula.fv_list \<eta>) False (Some ?ag)"
      have m: "minit0 n (Formula.Agg y \<omega> tys f \<phi>) = MUntil ?args
          (minit0 (length tys + n) \<chi>') (minit0 (length tys + n) \<eta>) ([], []) [] 0 (init_muaux_dq ?args)"
        using False chi unfolding Until by (simp add: Let_def dq_muaux.init_until_def)
      note zz = Agg.prems(2)[unfolded m]
      note z = eof_until_z[OF zz]
      have s1: "eofc (length tys + n) tw \<chi>'"
        by (rule Agg.IH[OF _ sc' bL']) (use z(1) in \<open>simp_all add: Until chi init_args_def\<close>)
      have s2: "eofc (length tys + n) tw \<eta>"
        by (rule Agg.IH[OF _ se bR]) (use z(2) in \<open>simp_all add: Until init_args_def\<close>)
      show ?thesis unfolding m
        by (rule esim_dof_until_agg[OF refl s1 s2 distinct_fvi_list distinct_fvi_list
              distinct_fvi_list _ zz]) (use s chi in simp)
    qed
  qed (rule D; simp add: Let_def)+
next
  case (Prev I \<phi>)
  have z: "eofz n \<phi>" using Prev.prems(2) by simp
  have s: "eofc n tw \<phi>" using Prev.prems(1) z by (intro Prev.IH) simp_all
  show ?case using s eframe_fv_list[of "Formula.Prev I \<phi>"] by (auto intro!: EsPrev)
next
  case (Next I \<phi>)
  have z: "eofz n \<phi>" using Next.prems(2) by simp
  have s: "eofc n tw \<phi>" using Next.prems(1) z by (intro Next.IH) simp_all
  show ?case using s eframe_fv_list[of "Formula.Next I \<phi>"] by (auto intro!: EsNext)
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
  note z = eof_since_z[OF Since.prems(2)[unfolded m e]]
  have s1: "eofc n tw \<phi>" using b sub z(1) by (intro Since.IH(1)) (auto simp: init_args_def)
  have s2: "eofc n tw \<psi>" using b z(2) by (intro Since.IH(2)) (auto simp: init_args_def)
  show ?case unfolding m e
    by (rule esim_dof_since[OF refl s1 s2 distinct_fvi_list distinct_fvi_list]) (simp add: sub)
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
  note z = eof_since_z[OF Not_Since.prems(2)[unfolded m e]]
  have s1: "eofc n tw \<phi>" using b sub z(1) by (intro Not_Since.IH(1)) (auto simp: init_args_def)
  have s2: "eofc n tw \<psi>" using b z(2) by (intro Not_Since.IH(2)) (auto simp: init_args_def)
  show ?case unfolding m e
    by (rule esim_dof_since[OF refl s1 s2 distinct_fvi_list distinct_fvi_list]) (simp add: sub)
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
  note z = eof_until_z[OF Until.prems(2)[unfolded m e]]
  have s1: "eofc n tw \<phi>" using b sub z(1) by (intro Until.IH(1)) (auto simp: init_args_def)
  have s2: "eofc n tw \<psi>" using b z(2) by (intro Until.IH(2)) (auto simp: init_args_def)
  show ?case unfolding m e
    by (rule esim_dof_until[OF refl s1 s2 distinct_fvi_list distinct_fvi_list]) (simp add: sub)
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
  note z = eof_until_z[OF Not_Until.prems(2)[unfolded m e]]
  have s1: "eofc n tw \<phi>" using b sub z(1) by (intro Not_Until.IH(1)) (auto simp: init_args_def)
  have s2: "eofc n tw \<psi>" using b z(2) by (intro Not_Until.IH(2)) (auto simp: init_args_def)
  show ?case unfolding m e
    by (rule esim_dof_until[OF refl s1 s2 distinct_fvi_list distinct_fvi_list]) (simp add: sub)
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
    note z = eof_trigger_z[OF Trigger_0.prems(2)[unfolded m e]]
    have z1: "eofz n \<phi>" and z2: "eofz n \<psi>" using z by (simp_all add: init_args_def)
    have s2: "eofc n tw \<psi>" by (rule Trigger_0(5)[OF _ z2]) (use b in auto)
    have sft: "safe_formula (Formula.Trigger \<phi> I \<psi>)"
      using m0 sub Trigger_0(2) True by (simp add: safe_dual_def)
    have s1: "eofc n tw \<phi>"
    proof (cases "\<forall>n. (\<forall>x \<in> Formula.fv \<phi>. x < n) \<longrightarrow> eofz n \<phi> \<longrightarrow> eofc n tw \<phi>")
      case True then show ?thesis using bp z1 by blast
    next
      case False
      then obtain \<chi> where phi: "\<phi> = Formula.Neg \<chi>" and sc: "safe_formula \<chi>"
        and ih: "\<forall>n. (\<forall>x \<in> Formula.fv \<chi>. x < n) \<longrightarrow> eofz n \<chi> \<longrightarrow> eofc n tw \<chi>"
        using Trigger_0(4) by (cases \<phi>) auto
      have fc: "Formula.fv \<chi> = {}" using \<open>safe_formula \<phi>\<close> phi by simp
      show ?thesis unfolding phi
        by (rule esim_dof_neg[OF fc sc]) (use bp z1 ih fc phi in auto)
    qed
    show ?thesis unfolding m e
      by (rule esim_dof_trigger[OF refl m0 s1 s2 distinct_fvi_list distinct_fvi_list])
        (simp add: sub)
  next
    case False
    obtain \<chi> where phi: "\<phi> = Formula.Neg \<chi>" and sc: "safe_formula \<chi>"
      and ih: "\<forall>n. (\<forall>x \<in> Formula.fv \<chi>. x < n) \<longrightarrow> eofz n \<chi> \<longrightarrow> eofc n tw \<chi>"
      using Trigger_0(4) False by (cases \<phi>) auto
    let ?args = "init_args I n (Formula.fv_list \<chi>) (Formula.fv_list \<psi>) False None"
    have m: "minit0 n (Formula.Trigger \<phi> I \<psi>) = MTrigger ?args
        (minit0 n \<chi>) (minit0 n \<psi>) ([], []) [] (init_mmtaux ?args)"
      using False phi by (simp add: verimon_maux.init_trigger_def)
    note z = eof_trigger_z[OF Trigger_0.prems(2)[unfolded m e]]
    have z1: "eofz n \<chi>" and z2: "eofz n \<psi>" using z by (simp_all add: init_args_def)
    have s2: "eofc n tw \<psi>" by (rule Trigger_0(5)[OF _ z2]) (use b in auto)
    have s1: "eofc n tw \<chi>" using ih bp z1 phi by simp
    have sft: "safe_formula (Formula.Trigger \<phi> I \<psi>)"
      using m0 sub Trigger_0(2) sc phi by (simp add: safe_dual_def)
    show ?thesis unfolding m e
      by (rule esim_dof_trigger[OF refl m0 s1 s2 distinct_fvi_list distinct_fvi_list])
        (use sub phi in simp)
  qed
next
  case (Trigger \<phi> I \<psi>) then show ?case by simp
next
  case (Release_0 \<phi> I \<psi>)
  have sub: "Formula.fv \<phi> \<subseteq> Formula.fv \<psi>" using Release_0.hyps(4) .
  obtain \<phi>'' pos where rl: "release_left \<phi> \<psi> = (\<phi>'', pos)"
    by (cases "release_left \<phi> \<psi>")
  have sub'': "Formula.fv \<phi>'' \<subseteq> Formula.fv \<psi>"
    by (rule fv_release_left[OF rl sub])
  have b: "\<forall>x \<in> Formula.fv \<psi>. x < n" using Release_0.prems(1) by simp
  have b'': "\<forall>x \<in> Formula.fv \<phi>''. x < n" using b sub'' by auto
  have e: "Formula.fv_list (Formula.Release \<phi> I \<psi>) = Formula.fv_list \<psi>"
    using sub by (simp add: cols_union_subset)
  let ?args = "init_args I n (Formula.fv_list \<phi>'') (Formula.fv_list \<psi>) pos None"
  have m: "minit0 n (Formula.Release \<phi> I \<psi>) = MRelease ?args
      (minit0 n \<phi>'') (minit0 n \<psi>) ([], []) [] 0 []"
    using Release_0.hyps(1) rl by simp
  note z = eof_release_z[OF Release_0.prems(2)[unfolded m e]]
  have z1: "eofz n \<phi>''" and z2: "eofz n \<psi>" using z by (simp_all add: init_args_def)
  have s2: "eofc n tw \<psi>" by (rule Release_0(6)[OF b z2])
  have s1: "eofc n tw \<phi>''"
    using release_left_cases[OF rl]
  proof (elim disjE conjE)
    assume "\<phi>'' = \<phi>" "safe_formula \<phi>"
    then show ?thesis
      using Release_0(8) b'' z1 by auto
  next
    assume "\<phi> = Formula.Neg \<phi>''" "safe_formula \<phi>''"
    then show ?thesis
      using Release_0(9) b'' z1 by auto
  next
    assume "\<phi>'' = Formula.And \<psi> \<phi>"
    then show ?thesis
      using Release_0(7) b'' z1 by auto
  qed
  show ?case unfolding m e
    by (rule esim_dof_release[OF refl s1 s2 distinct_fvi_list distinct_fvi_list]) (simp add: sub'')
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
  define ks where "ks = Formula.fv_list (Formula.MatchP I r)"
  define dss where "dss = map Formula.fv_list \<phi>s"
  define L where "L = map (minit0 n) \<phi>s"
  define Ld where "Ld = map (\<lambda>(k, \<phi>). eof n k (ecols k) \<phi>) (zip dss L)"
  have lL: "length L = length \<phi>s" and ld: "length dss = length \<phi>s" and lLd: "length Ld = length \<phi>s"
    by (simp_all add: L_def dss_def Ld_def)
  have Ldi: "\<And>i. i < length \<phi>s \<Longrightarrow> Ld ! i = eof n (dss ! i) (ecols (dss ! i)) (L ! i)"
    by (simp add: Ld_def L_def dss_def)
  have m: "minit0 n (Formula.MatchP I r) = MMatchP I ks dss mr (sorted_list_of_set (RPDs mr)) L
      (replicate (length \<phi>s) []) [] []"
    using tm by (simp add: ks_def dss_def L_def)
  have zz: "efail_nodes (eof n ks (ecols ks)
      (MMatchP I ks dss mr (sorted_list_of_set (RPDs mr)) L (replicate (length \<phi>s) []) [] [])) = 0"
    using MatchP.prems(2) unfolding m ks_def[symmetric] .
  have chk: "\<forall>c \<in> set (map ecols dss). set c \<subseteq> set (ecols ks)"
    using zz lL ld by (auto simp: Let_def split: if_splits)
  have d: "eof n ks (ecols ks)
      (MMatchP I ks dss mr (sorted_list_of_set (RPDs mr)) L (replicate (length \<phi>s) []) [] [])
    = EMatchP (length (ecols ks)) I mr (sorted_list_of_set (RPDs mr))
        (map (emb_plan (ecols ks)) (map ecols dss)) Ld (map (\<lambda>_. mbuf_t_empty) L) (mbuf_t_empty @@ []) []"
    using chk lL ld unfolding Ld_def by (simp add: Let_def)
  have zall: "\<forall>x \<in> set Ld. efail_nodes x = 0" using zz unfolding d by simp
  have pL: "\<forall>i < length L. esim n (dss ! i) (map ecols dss ! i) tw (Ld ! i) (L ! i)"
  proof (intro allI impI)
    fix i assume i: "i < length L"
    then have i': "i < length \<phi>s" by (simp add: lL)
    have mem: "\<phi>s ! i \<in> safe_atms r" using nth_mem[OF i'] at by blast
    have bi: "\<forall>x \<in> Formula.fv (\<phi>s ! i). x < n" using b sub i' by auto
    have zi: "eofz n (\<phi>s ! i)"
      using zall nth_mem[of i Ld] Ldi[OF i'] lLd i' by (simp add: dss_def L_def)
    have "eofc n tw (\<phi>s ! i)" using MatchP.IH mem bi zi by blast
    then show "esim n (dss ! i) (map ecols dss ! i) tw (Ld ! i) (L ! i)"
      using Ldi[OF i'] i' by (simp add: dss_def L_def)
  qed
  have A: "set ks = Formula.fv_regex (from_mregex mr \<phi>s)"
    unfolding ks_def Formula.set_fvi_list fm by simp
  have bf: "ebufn dss (map ecols dss) (replicate (length \<phi>s) []) (map Rep_mbuf_t (map (\<lambda>_. mbuf_t_empty) L))"
    using lL ld by (auto simp: ebufn_def intro!: nth_equalityI)
  show ?case unfolding m ks_def[symmetric] d
    by (rule EsMatchP[OF eframe_dcols[OF distinct_fvi_list[of 0 "Formula.MatchP I r", folded ks_def]]
          sr[folded fm] ok A _ _ dss_def _ lL lLd[folded lL] _ _ pL refl bf])
      (use sub fm A in \<open>auto simp: finite_RPDs dss_def intro!: eframe_fv_list\<close>)
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
  define ks where "ks = Formula.fv_list (Formula.MatchF I r)"
  define dss where "dss = map Formula.fv_list \<phi>s"
  define L where "L = map (minit0 n) \<phi>s"
  define Ld where "Ld = map (\<lambda>(k, \<phi>). eof n k (ecols k) \<phi>) (zip dss L)"
  have lL: "length L = length \<phi>s" and ld: "length dss = length \<phi>s" and lLd: "length Ld = length \<phi>s"
    by (simp_all add: L_def dss_def Ld_def)
  have Ldi: "\<And>i. i < length \<phi>s \<Longrightarrow> Ld ! i = eof n (dss ! i) (ecols (dss ! i)) (L ! i)"
    by (simp add: Ld_def L_def dss_def)
  have m: "minit0 n (Formula.MatchF I r) = MMatchF I ks dss mr (sorted_list_of_set (LPDs mr)) L
      (replicate (length \<phi>s) []) [] 0 []"
    using tm by (simp add: ks_def dss_def L_def)
  have zz: "efail_nodes (eof n ks (ecols ks)
      (MMatchF I ks dss mr (sorted_list_of_set (LPDs mr)) L (replicate (length \<phi>s) []) [] 0 [])) = 0"
    using MatchF.prems(2) unfolding m ks_def[symmetric] .
  have chk: "\<forall>c \<in> set (map ecols dss). set c \<subseteq> set (ecols ks)"
    using zz lL ld by (auto simp: Let_def split: if_splits)
  have d: "eof n ks (ecols ks)
      (MMatchF I ks dss mr (sorted_list_of_set (LPDs mr)) L (replicate (length \<phi>s) []) [] 0 [])
    = EMatchF (length (ecols ks)) I mr (sorted_list_of_set (LPDs mr))
        (map (emb_plan (ecols ks)) (map ecols dss)) Ld (map (\<lambda>_. mbuf_t_empty) L) (mbuf_t_empty @@ []) 0 []"
    using chk lL ld unfolding Ld_def by (simp add: Let_def)
  have zall: "\<forall>x \<in> set Ld. efail_nodes x = 0" using zz unfolding d by simp
  have pL: "\<forall>i < length L. esim n (dss ! i) (map ecols dss ! i) tw (Ld ! i) (L ! i)"
  proof (intro allI impI)
    fix i assume i: "i < length L"
    then have i': "i < length \<phi>s" by (simp add: lL)
    have mem: "\<phi>s ! i \<in> safe_atms r" using nth_mem[OF i'] at by blast
    have bi: "\<forall>x \<in> Formula.fv (\<phi>s ! i). x < n" using b sub i' by auto
    have zi: "eofz n (\<phi>s ! i)"
      using zall nth_mem[of i Ld] Ldi[OF i'] lLd i' by (simp add: dss_def L_def)
    have "eofc n tw (\<phi>s ! i)" using MatchF.IH mem bi zi by blast
    then show "esim n (dss ! i) (map ecols dss ! i) tw (Ld ! i) (L ! i)"
      using Ldi[OF i'] i' by (simp add: dss_def L_def)
  qed
  have A: "set ks = Formula.fv_regex (from_mregex mr \<phi>s)"
    unfolding ks_def Formula.set_fvi_list fm by simp
  have bf: "ebufn dss (map ecols dss) (replicate (length \<phi>s) []) (map Rep_mbuf_t (map (\<lambda>_. mbuf_t_empty) L))"
    using lL ld by (auto simp: ebufn_def intro!: nth_equalityI)
  show ?case unfolding m ks_def[symmetric] d
    by (rule EsMatchF[OF eframe_dcols[OF distinct_fvi_list[of 0 "Formula.MatchF I r", folded ks_def]]
          sr[folded fm] ok A _ _ dss_def _ lL lLd[folded lL] _ _ pL refl bf])
      (use sub fm A in \<open>auto simp: finite_LPDs dss_def intro!: eframe_fv_list\<close>)
next
  case (TP t)
  show ?case using TP.prems(2) eframe_fv_list[of "Formula.TP t"]
    by (auto split: if_splits intro!: EsTP)
next
  case (TS t)
  show ?case using TS.prems(2) eframe_fv_list[of "Formula.TS t"]
    by (auto split: if_splits intro!: EsTS)
qed

section \<open>The executable monitor's correctness theorem, on the compiled state\<close>

text \<open>
  The state the compiler produces relates to the kernel's whenever the compilation covered every
  node, so the transferred theorems of the preceding theories apply to it under that one check.
  It is a check on the formula alone, made once, before the monitor runs.
\<close>

definition eof_state :: "nat \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow>
    (mmasaux, muaux_dq, event_data mmtaux) mstate \<Rightarrow> emstate" where
  "eof_state n ks cs st =
     \<lparr> emstate_i = mstate_i st, emstate_j = mstate_j st,
       emstate_m = eemb IxNone [] (eof n ks cs (mstate_m st)),
       emstate_n = n, emstate_cs = cs, emstate_t = mbuf_t_empty @@ mstate_t st \<rparr>"

lemma emsim_state_eof_state:
  assumes n: "mstate_n st = n" and p: "esim n ks cs tw (eof n ks cs (mstate_m st)) (mstate_m st)"
  shows "emsim_state n ks cs tw st (eof_state n ks cs st)"
  by (simp add: emsim_state_def eof_state_def n p mbuf_t_append.rep_eq)

context verimon_spec
begin

theorem emonitor_mverdicts_dof:
  assumes zf: "efail_nodes (eabs (emstate_m (eof_state (Formula.nfv \<phi>) (Formula.fv_list \<phi>)
      (ecols (Formula.fv_list \<phi>)) (minit_safe \<phi>)))) = 0"
    and f: "pfinite \<pi>" and wty: "wty_prefix SIG \<pi>"
  shows "flatten_verdicts (map (\<lambda>(i, t, X).
      (i, t, etabw (Formula.fv_list \<phi>) (ecols (Formula.fv_list \<phi>)) X))
      (emonitor (eof_state (Formula.nfv \<phi>) (Formula.fv_list \<phi>) (ecols (Formula.fv_list \<phi>))
         (minit_safe \<phi>)) \<pi>)) = Mt \<pi>"
proof -
  have mm: "mmonitorable \<phi>" by (rule monitorable)
  then have s: "safe_formula \<phi>" by (simp add: mmonitorable_def)
  have b: "\<forall>x \<in> Formula.fv \<phi>. x < Formula.nfv \<phi>" by (rule fvi_less_nfv)
  have ni: "mstate_n (minit_safe \<phi>) = Formula.nfv \<phi>" by (rule minit_safe_state(1)[OF mm])
  have mm0: "mstate_m (minit_safe \<phi>) = minit0 (Formula.nfv \<phi>) \<phi>"
    by (rule minit_safe_state(2)[OF mm])
  have zf': "eofz (Formula.nfv \<phi>) \<phi>"
    using zf unfolding eof_state_def mm0 by simp
  have p: "esim (Formula.nfv \<phi>) (Formula.fv_list \<phi>) (ecols (Formula.fv_list \<phi>)) 0
      (eof (Formula.nfv \<phi>) (Formula.fv_list \<phi>) (ecols (Formula.fv_list \<phi>)) (mstate_m (minit_safe \<phi>)))
      (mstate_m (minit_safe \<phi>))"
    unfolding mm0 by (rule esim_dof_minit0[OF s b zf'])
  show ?thesis
    by (rule emonitor_mverdicts[OF emsim_state_eof_state[OF ni p] f wty])
qed

end

text \<open>The executable monitor's initial state: the compiled kernel state.  The kernel's
  initialization is executed for it.  Its window initializations are locale definitions, so they
  are given code through constants for the interpretation the kernel state uses.\<close>

definition "kinit_since = msaux_ops.init_since (init_mmasaux :: _ \<Rightarrow> mmasaux)"
definition "kinit_until = muaux_ops.init_until (init_muaux_dq :: _ \<Rightarrow> muaux_dq)"
definition "kinit_trigger = mtaux_ops.init_trigger (init_mmtaux :: _ \<Rightarrow> event_data mmtaux)"
definition "kinit_and_trigger = mtaux_ops.init_and_trigger (init_mmtaux :: _ \<Rightarrow> event_data mmtaux)"

lemmas [code] = msaux_ops.init_since_def[where init_msaux = "init_mmasaux :: _ \<Rightarrow> mmasaux", folded kinit_since_def]
  muaux_ops.init_until_def[where init_muaux = "init_muaux_dq :: _ \<Rightarrow> muaux_dq", folded kinit_until_def]
  mtaux_ops.init_trigger_def[where init_mtaux = "init_mmtaux :: _ \<Rightarrow> event_data mmtaux", folded kinit_trigger_def]
  mtaux_ops.init_and_trigger_def[where init_mtaux = "init_mmtaux :: _ \<Rightarrow> event_data mmtaux", folded kinit_and_trigger_def]
lemmas [code_unfold] = kinit_since_def[symmetric] kinit_until_def[symmetric]
  kinit_trigger_def[symmetric] kinit_and_trigger_def[symmetric]

definition eminit_safe :: "ty Formula.formula \<Rightarrow> emstate" where
  "eminit_safe \<phi> = eof_state (Formula.nfv \<phi>) (Formula.fv_list \<phi>) (ecols (Formula.fv_list \<phi>))
     (minit_safe \<phi>)"

end
