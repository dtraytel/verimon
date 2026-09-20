(*<*)
theory Dense_Descend_Code
  imports Dense_Exec
begin
(*>*)

section \<open>The descending compiler, executable\<close>

text \<open>
  @{const dof} descends the kernel's @{typ "(mmasaux, muaux_dq, event_data mmtaux) mformula"},
  which is the specification type: its code representation is @{const Rep_meformula} of an
  @{typ "(mmasaux, muaux_dq, event_data mmtaux) meformula"}, so the code generator cannot match
  on its constructors and @{const dof} is not executable as it stands.  Its result is a
  @{typ dformula}, whose code representation is in turn @{const Rep_edformula} of an
  @{typ edformula}, so the result must be built from the executable constructors as well.

  The transcription below descends the implementation type and builds the implementation
  type.  It is @{const dof} clause for clause, with the buffers read through
  @{const Rep_mbuf_t} where @{const dof} reads them directly and rebuilt with
  @{const mbuf_t_append} where @{const dof} writes lists, and the lemma after it says the two
  agree -- which is the code equation the generator needs.  Nothing new is decided here; every
  guard and every node is the one above.
\<close>

abbreviation (input) "dbuf_of n cs b \<equiv> mbuf_t_empty @@ map (dtabc n cs) (Rep_mbuf_t b)"

function (sequential) edof ::
    "nat \<Rightarrow> cols \<Rightarrow> (mmasaux, muaux_dq, event_data mmtaux) meformula \<Rightarrow> edformula" where
  "edof n cs (meformula.MRel rel) = EDRel (dtabc n cs rel)"
| "edof n cs (meformula.MPred e tms mode) =
     (if mode = Match then EDPredM e (length tms) tms cs
      else if (mode = Copy \<and> tms = map Formula.Var [0..<n] \<and> cs = [0..<n])
           \<or> (mode = Simple \<and> is_simple_pattern tms 0 \<and> cs = smp_cols tms)
      then EDPredS e (length tms)
      else EDFail)"
| "edof n cs (meformula.MAndRel \<phi> conf) =
     (if Formula.fv_trm (fst conf) \<subseteq> set cs \<and> Formula.fv_trm (snd (snd (snd conf))) \<subseteq> set cs
      then EDAndRel (edof n cs \<phi>) (reindex_constraint cs conf)
      else EDFail)"
| "edof n cs (meformula.MNeg \<phi>) =
     (if cs = [] then EDNeg (edof n [] \<phi>)
      else EDFail)"
| "edof n cs (meformula.MExists \<phi>) = EDExists (edof (Suc n) (0 # map Suc cs) \<phi>) True"
| "edof n cs (meformula.MOr \<phi> \<psi> buf) =
     EDOr (edof n cs \<phi>) (edof n cs \<psi>) (dbuf_of n cs (fst buf), dbuf_of n cs (snd buf))"
| "edof n cs (meformula.MAnd A \<phi> pos B \<psi> buf) =
     (let cs1 = set_cols A; cs2 = set_cols B in
      if cs = merge_cols cs1 cs2 \<and> (pos \<or> B \<subseteq> A)
      then EDAnd (mk_djoin cs1 cs2) (edof n cs1 \<phi>) pos (edof n cs2 \<psi>)
             (dbuf_of n cs1 (fst buf), dbuf_of n cs2 (snd buf))
      else EDFail)"
| "edof n cs (meformula.MPrev I \<phi> first buf nts) =
     EDPrev I (edof n cs \<phi>) first (dbuf_of n cs buf) nts"
| "edof n cs (meformula.MNext I \<phi> first nts) =
     EDNext I (edof n cs \<phi>) first nts"
| "edof n cs (meformula.MAnds A_pos A_neg L buf) =
     (case A_pos of [] \<Rightarrow> EDFail
      | A # As \<Rightarrow>
        (let c0 = set_cols A; css = map set_cols As; nss = map set_cols A_neg in
         if cs = dands_cols c0 css \<and> length L = length A_pos + length A_neg
         then EDAnds (dands_plans c0 css) (dands_plans (dands_cols c0 css) nss)
                (map2 (edof n) (c0 # css @ nss) L)
                (map (\<lambda>b. mbuf_t_empty @@ b)
                  (map2 map (map (dtabc n) (c0 # css @ nss)) (map Rep_mbuf_t buf)))
         else EDFail))"
| "edof n cs (meformula.MAgg args \<phi>) =
     (let m = length (aggargs_tys args); g = dagg_gcols args; y = aggargs_y args in
      if cs = merge_cols g [y] \<and> set_cols (aggargs_cols args) = agg_cols m g
      then EDAgg (aggargs_g0 args) (aggargs_\<omega> args)
             (reindex_trm (agg_cols m g) (aggargs_f args)) m (ins_pos g y)
             (edof (m + n) (agg_cols m g) \<phi>)
      else EDFail)"
| "edof n cs (meformula.MSince args \<phi> \<psi> buf aux) =
     (let cs_L = set_cols (args_L args); cs_R = set_cols (args_R args);
          \<phi>d = edof (dnode_n n args) cs_L \<phi>; \<psi>d = edof (dnode_n n args) cs_R \<psi>;
          bf = (case buf of (a, b, c, d) \<Rightarrow> (Rep_mbuf_t a, Rep_mbuf_t b, Rep_mbuf_t c, d)) in
      case args_agg args of
        None \<Rightarrow>
          (if args_n args = n \<and> cs = cs_R \<and> set cs_L \<subseteq> set cs_R \<and> bf = init_mbuf2S
           then EDSince (dargs cs cs_L args) \<phi>d \<psi>d init_mebuf2S
                  (dsx_init (dargs cs cs_L args) (dmsk cs cs_L))
           else EDFail)
      | Some ag \<Rightarrow>
          (let m = length (aggargs_tys ag); g = dagg_gcols ag; y = aggargs_y ag in
           if args_n args = m + aggargs_n ag \<and> aggargs_n ag = n \<and> set cs_L \<subseteq> set cs_R \<and>
              bf = init_mbuf2S \<and> agg_cols m g = cs_R \<and> cs = merge_cols g [y] \<and>
              wf_cols n g \<and> y < n \<and> y \<notin> set g \<and> (aggargs_g0 ag \<longrightarrow> g = []) \<and>
              Formula.fv_trm (aggargs_f ag) \<subseteq> set cs_R
           then (if cpos cs_R (set cs_L) = {}
                 then EDSince (dargs cs_R cs_L args) \<phi>d \<psi>d init_mebuf2S
                        (dsx_init_agg (dargs cs_R cs_L args)
                          (aggargs_g0 ag, aggargs_\<omega> ag, reindex_trm cs_R (aggargs_f ag),
                           m, ins_pos g y))
                 else EDAgg (aggargs_g0 ag) (aggargs_\<omega> ag) (reindex_trm cs_R (aggargs_f ag))
                        m (ins_pos g y)
                        (EDSince (dargs cs_R cs_L args) \<phi>d \<psi>d init_mebuf2S
                          (dsx_init (dargs cs_R cs_L args) (dmsk cs_R cs_L))))
           else EDFail))"
| "edof n cs (meformula.MUntil args \<phi> \<psi> buf nts t aux) =
     (let cs_L = set_cols (args_L args); cs_R = set_cols (args_R args);
          \<phi>d = edof (dnode_n n args) cs_L \<phi>; \<psi>d = edof (dnode_n n args) cs_R \<psi> in
      case args_agg args of
        None \<Rightarrow>
          (if args_n args = n \<and> cs = cs_R \<and> set cs_L \<subseteq> set cs_R \<and>
              map_prod Rep_mbuf_t Rep_mbuf_t buf = ([], []) \<and> Rep_mbuf_t nts = [] \<and> t = 0
           then EDUntil (dargs cs cs_L args) (dmsk cs cs_L) \<phi>d \<psi>d (mbuf_t_empty, mbuf_t_empty)
                  mbuf_t_empty 0 (dux_init (dargs cs cs_L args))
           else EDFail)
      | Some ag \<Rightarrow>
          (let m = length (aggargs_tys ag); g = dagg_gcols ag; y = aggargs_y ag in
           if args_n args = m + aggargs_n ag \<and> aggargs_n ag = n \<and> set cs_L \<subseteq> set cs_R \<and>
              map_prod Rep_mbuf_t Rep_mbuf_t buf = ([], []) \<and> Rep_mbuf_t nts = [] \<and> t = 0 \<and>
              agg_cols m g = cs_R \<and> cs = merge_cols g [y] \<and>
              wf_cols n g \<and> y < n \<and> y \<notin> set g \<and> (aggargs_g0 ag \<longrightarrow> g = []) \<and>
              Formula.fv_trm (aggargs_f ag) \<subseteq> set cs_R
           then EDAgg (aggargs_g0 ag) (aggargs_\<omega> ag) (reindex_trm cs_R (aggargs_f ag))
                  m (ins_pos g y)
                  (EDUntil (dargs cs_R cs_L args) (dmsk cs_R cs_L) \<phi>d \<psi>d
                    (mbuf_t_empty, mbuf_t_empty) mbuf_t_empty 0
                    (dux_init (dargs cs_R cs_L args)))
           else EDFail))"
| "edof n cs (meformula.MAndAssign \<phi> conf) =
     (let y = fst conf; t = snd conf; cs0 = rem_col cs y in
      if y \<in> set cs \<and> Formula.fv_trm t \<subseteq> set cs0
      then EDAndAssign (ins_pos cs0 y) (reindex_trm cs0 t) (edof n cs0 \<phi>)
      else EDFail)"
| "edof n cs (meformula.MLet p m \<phi> \<psi>) = EDLet p m (edof m [0..<m] \<phi>) (edof n cs \<psi>)"
| "edof n cs (meformula.MFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s) =
     EDFrz p m (edof m [0..<m] \<phi>) (edof n cs \<psi>) jfrz jpsi0 jphi \<alpha>s"
| "edof n cs (meformula.MLetPast p m \<phi> \<psi> i buf) =
     EDLetPast p m (edof m [0..<m] \<phi>) (edof n cs \<psi>) i buf"
| "edof n cs (meformula.MTrigger args \<phi> \<psi> buf nts aux) =
     (let cs_L = set_cols (args_L args) in
      if args_n args = n \<and> args_R args = set cs \<and> set cs_L \<subseteq> set cs \<and>
         mem (args_ivl args) 0 \<and> map_prod Rep_mbuf_t Rep_mbuf_t buf = ([], []) \<and>
         Rep_mbuf_t nts = []
      then EDTrigger (dargs cs cs_L args) (emb_plan cs cs_L)
             (edof n cs_L \<phi>) (edof n cs \<psi>) (mbuf_t_empty, mbuf_t_empty) mbuf_t_empty
             (init_mmtaux (dargs cs cs_L args))
      else EDFail)"
| "edof n cs (meformula.MTP mt i) =
     (if cs = mtrm_dcols mt then EDTP mt i
      else EDFail)"
| "edof n cs (meformula.MTS mt) =
     (if cs = mtrm_dcols mt then EDTS mt
      else EDFail)"
| "edof n cs \<phi> = EDFail"
  by pat_completeness auto

termination edof
  by (relation "measure (\<lambda>(n, cs, \<phi>). size \<phi>)")
    (auto simp: termination_simp dest!: set_zip_rightD)

lemma edof_dof: "Rep_edformula (edof n cs e) = dof n cs (Rep_meformula e)"
proof (induct n cs e rule: edof.induct)
  case (12 n cs args \<phi> \<psi> buf aux)
  then show ?case
    by (cases "args_agg args") (simp_all add: Let_def mbuf_t_empty.rep_eq mbuf_t_append.rep_eq)
next
  case (13 n cs args \<phi> \<psi> buf nts t aux)
  then show ?case
    by (cases "args_agg args") (simp_all add: Let_def mbuf_t_empty.rep_eq mbuf_t_append.rep_eq)
qed (simp_all add: Let_def zip_map2 o_def mbuf_t_empty.rep_eq mbuf_t_append.rep_eq
      split: list.splits prod.splits cong: map_cong)

lemma dof_code[code]: "dof n cs (Rep_meformula e) = Rep_edformula (edof n cs e)"
  by (simp add: edof_dof)

(*<*)
end
(*>*)
