(*<*)
theory Exec_Compiler
  imports Exec_Monitor
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

lemma Rep_mbuf_t_empty[simp]: "Rep_mbuf_t mbuf_t_empty = []"
  by (rule mbuf_t_empty.rep_eq)

lemma Rep_mbuf_t_empty_append[simp]: "Rep_mbuf_t (mbuf_t_empty @@ xs) = xs"
  by (simp add: mbuf_t_append.rep_eq)

lemma rbufS_init[simp]: "rbufS init_mebuf2S = init_mbuf2S"
  by simp

abbreviation (input) eofc :: "nat \<Rightarrow> ts \<Rightarrow> ty Formula.formula \<Rightarrow> bool" where
  "eofc n tw \<phi> \<equiv> esim n (Formula.fv_list \<phi>) (ecols (Formula.fv_list \<phi>)) tw
     (eof n (Formula.fv_list \<phi>) (ecols (Formula.fv_list \<phi>)) (minit0 n \<phi>)) (minit0 n \<phi>)"

abbreviation (input) eofz :: "nat \<Rightarrow> ty Formula.formula \<Rightarrow> bool" where
  "eofz n \<phi> \<equiv> efail_nodes (eof n (Formula.fv_list \<phi>) (ecols (Formula.fv_list \<phi>)) (minit0 n \<phi>)) = 0"

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

context verimon_spec
begin

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
