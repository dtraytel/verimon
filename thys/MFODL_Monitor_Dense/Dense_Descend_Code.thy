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

text \<open>
  The match nodes recover their operands' frames with @{const mfcols}, which descends the
  specification type for the same reason @{const dof} does.  Here is its transcription to the
  implementation type; nothing about it changes but the constructors it matches on.
\<close>

function (sequential) emfcols ::
    "nat \<Rightarrow> (mmasaux, muaux_dq, event_data mmtaux) meformula \<Rightarrow> cols option" where
  "emfcols n (meformula.MRel rel) = None"
| "emfcols n (meformula.MPred e tms mode) =
     (case mode of Copy \<Rightarrow> Some [0..<n]
      | _ \<Rightarrow> Some (set_cols (\<Union>t \<in> set tms. Formula.fv_trm t)))"
| "emfcols n (meformula.MLet p m \<phi> \<psi>) = emfcols n \<psi>"
| "emfcols n (meformula.MFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po) = emfcols n \<psi>"
| "emfcols n (meformula.MLetPast p m \<phi> \<psi> i buf) = emfcols n \<psi>"
| "emfcols n (meformula.MAnd A1 \<phi> pos A2 \<psi> buf) =
     (case (emfcols n \<phi>, emfcols n \<psi>) of
        (Some c1, Some c2) \<Rightarrow> Some (if pos then merge_cols c1 c2 else c1)
      | _ \<Rightarrow> None)"
| "emfcols n (meformula.MAndAssign \<phi> conf) =
     map_option (\<lambda>c. merge_cols c [fst conf]) (emfcols n \<phi>)"
| "emfcols n (meformula.MAndRel \<phi> conf) = emfcols n \<phi>"
| "emfcols n (meformula.MAndTrigger A \<alpha> buf1 args \<phi> \<psi> buf2 nts aux) = emfcols n \<alpha>"
| "emfcols n (meformula.MAnds A_pos A_neg L buf) =
     (case those (map (emfcols n) (take (length A_pos) L)) of
        Some (c0 # cs') \<Rightarrow> Some (dands_cols c0 cs')
      | _ \<Rightarrow> None)"
| "emfcols n (meformula.MOr \<phi> \<psi> buf) = emfcols n \<phi>"
| "emfcols n (meformula.MNeg \<phi>) = Some []"
| "emfcols n (meformula.MExists \<phi>) = map_option (ungroup_cols (Suc 0)) (emfcols (Suc n) \<phi>)"
| "emfcols n (meformula.MAgg args \<phi>) =
     map_option (\<lambda>g. merge_cols (ungroup_cols (length (aggargs_tys args)) g)
         [aggargs_y args])
       (emfcols (length (aggargs_tys args) + n) \<phi>)"
| "emfcols n (meformula.MPrev I \<phi> first buf nts) = emfcols n \<phi>"
| "emfcols n (meformula.MNext I \<phi> first nts) = emfcols n \<phi>"
| "emfcols n (meformula.MSince args \<phi> \<psi> buf aux) =
     (case args_agg args of None \<Rightarrow> emfcols n \<psi>
      | Some ag \<Rightarrow> map_option (\<lambda>r. merge_cols (ungroup_cols (length (aggargs_tys ag)) r)
            [aggargs_y ag])
          (emfcols (dnode_n n args) \<psi>))"
| "emfcols n (meformula.MUntil args \<phi> \<psi> buf nts t aux) =
     (case args_agg args of None \<Rightarrow> emfcols n \<psi>
      | Some ag \<Rightarrow> map_option (\<lambda>r. merge_cols (ungroup_cols (length (aggargs_tys ag)) r)
            [aggargs_y ag])
          (emfcols (dnode_n n args) \<psi>))"
| "emfcols n (meformula.MTrigger args \<phi> \<psi> buf nts aux) = emfcols n \<psi>"
| "emfcols n (meformula.MMatchP I mr mrs L buf nts aux) = None"
| "emfcols n (meformula.MMatchF I mr mrs L buf nts t aux) = None"
| "emfcols n (meformula.MTP mt i) = Some (mtrm_dcols mt)"
| "emfcols n (meformula.MTS mt) = Some (mtrm_dcols mt)"
  by pat_completeness auto

termination
  by (relation "measure (\<lambda>(n, \<phi>). size \<phi>)")
    (auto dest!: in_set_takeD intro!: le_imp_less_Suc size_list_estimation')

lemma emfcols_mfcols: "emfcols n e = mfcols n (Rep_meformula e)"
  by (induct n e rule: emfcols.induct)
    (auto simp: take_map o_def split: option.splits list.splits pred_mode.splits
      cong: map_cong)

function (sequential) edof ::
    "nat \<Rightarrow> cols \<Rightarrow> (mmasaux, muaux_dq, event_data mmtaux) meformula \<Rightarrow> edformula" where
  "edof n cs (meformula.MRel rel) = EDRel (dsan (dtabc n cs rel))"
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
     (if mbuf_t_is_empty (fst buf) \<and> mbuf_t_is_empty (snd buf)
      then EDOr (edof n cs \<phi>) (edof n cs \<psi>) (mbuf_t_empty, mbuf_t_empty) else EDFail)"
| "edof n cs (meformula.MAnd A \<phi> pos B \<psi> buf) =
     (let cs1 = set_cols A; cs2 = set_cols B in
      if cs = merge_cols cs1 cs2 \<and> (pos \<or> B \<subseteq> A) \<and>
         mbuf_t_is_empty (fst buf) \<and> mbuf_t_is_empty (snd buf)
      then EDAnd (mk_djoin cs1 cs2) (edof n cs1 \<phi>) pos (edof n cs2 \<psi>)
             (mbuf_t_empty, mbuf_t_empty)
      else EDFail)"
| "edof n cs (meformula.MPrev I \<phi> first buf nts) =
     (if mbuf_t_is_empty buf then EDPrev I (edof n cs \<phi>) first mbuf_t_empty nts else EDFail)"
| "edof n cs (meformula.MNext I \<phi> first nts) =
     EDNext I (edof n cs \<phi>) first nts"
| "edof n cs (meformula.MAnds A_pos A_neg L buf) =
     (case A_pos of [] \<Rightarrow> EDFail
      | A # As \<Rightarrow>
        (let c0 = set_cols A; css = map set_cols As; nss = map set_cols A_neg in
         if cs = dands_cols c0 css \<and> length L = length A_pos + length A_neg \<and>
            list_all mbuf_t_is_empty buf
         then EDAnds (dands_plans c0 css) (dands_plans (dands_cols c0 css) nss)
                (map2 (edof n) (c0 # css @ nss) L) (map (\<lambda>_. mbuf_t_empty) L)
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
           then (if cpos cs_R (set cs_L) = {} \<and> memL (args_ivl args) 0
                 then EDUntil (dargs cs_R cs_L args) (dmsk cs_R cs_L) \<phi>d \<psi>d (mbuf_t_empty, mbuf_t_empty) mbuf_t_empty 0
                        (dux_init_agg (dargs cs_R cs_L args)
                          (aggargs_g0 ag, aggargs_\<omega> ag, reindex_trm cs_R (aggargs_f ag),
                           m, ins_pos g y))
                 else EDAgg (aggargs_g0 ag) (aggargs_\<omega> ag) (reindex_trm cs_R (aggargs_f ag))
                  m (ins_pos g y)
                  (EDUntil (dargs cs_R cs_L args) (dmsk cs_R cs_L) \<phi>d \<psi>d
                    (mbuf_t_empty, mbuf_t_empty) mbuf_t_empty 0
                    (dux_init (dargs cs_R cs_L args))))
           else EDFail))"
| "edof n cs (meformula.MAndAssign \<phi> conf) =
     (let y = fst conf; t = snd conf; cs0 = rem_col cs y in
      if y \<in> set cs \<and> Formula.fv_trm t \<subseteq> set cs0
      then EDAndAssign (ins_pos cs0 y) (reindex_trm cs0 t) (edof n cs0 \<phi>)
      else EDFail)"
| "edof n cs (meformula.MLet p m \<phi> \<psi>) = EDLet p m (edof m [0..<m] \<phi>) (edof n cs \<psi>)"
| "edof n cs (meformula.MFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po) =
     (if \<alpha>s = [] \<and> rb = [] then EDFrz p m (edof m [0..<m] \<phi>) (edof n cs \<psi>) jfrz jpsi0 jphi []
        (edof n cs \<rho>) w pR tq [] d po else EDFail)"
| "edof n cs (meformula.MLetPast p m \<phi> \<psi> i buf) =
     (if buf = None then EDLetPast p m (edof m [0..<m] \<phi>) (edof n cs \<psi>) i None else EDFail)"
| "edof n cs (meformula.MTrigger args \<phi> \<psi> buf nts aux) =
     (let cs_L = set_cols (args_L args) in
      if args_n args = n \<and> args_R args = set cs \<and> set cs_L \<subseteq> set cs \<and>
         mem (args_ivl args) 0 \<and> map_prod Rep_mbuf_t Rep_mbuf_t buf = ([], []) \<and>
         Rep_mbuf_t nts = []
      then EDTrigger (dargs cs cs_L args) (emb_plan cs cs_L)
             (edof n cs_L \<phi>) (edof n cs \<psi>) (mbuf_t_empty, mbuf_t_empty) mbuf_t_empty
             (ginit_mmtaux (dargs cs cs_L args) (dmsk cs cs_L))
      else EDFail)"
| "edof n cs (meformula.MAndTrigger A \<alpha> buf1 args \<phi> \<psi> buf2 nts aux) =
     (let cs_R = set_cols (args_R args); cs_L = set_cols (args_L args) in
      if args_n args = n \<and> cs = set_cols A \<and> set cs_R \<subseteq> set cs \<and> set cs_L \<subseteq> set cs_R \<and>
         tok cs_R cs_L args \<and> mbuf_t_is_empty (fst buf1) \<and> mbuf_t_is_empty (snd buf1) \<and>
         mbuf_t_is_empty (fst buf2) \<and> mbuf_t_is_empty (snd buf2) \<and> mbuf_t_is_empty nts
      then EDAndTrigger (mk_djoin cs cs_R) (edof n cs \<alpha>) (mbuf_t_empty, mbuf_t_empty)
             (dargs cs_R cs_L args) (edof n cs_L \<phi>) (edof n cs_R \<psi>)
             (mbuf_t_empty, mbuf_t_empty) mbuf_t_empty
             (ginit_mmtaux (dargs cs_R cs_L args) (dmsk cs_R cs_L))
      else EDFail)"
| "edof n cs (meformula.MTP mt i) =
     (if cs = mtrm_dcols mt then EDTP mt i
      else EDFail)"
| "edof n cs (meformula.MTS mt) =
     (if cs = mtrm_dcols mt then EDTS mt
      else EDFail)"
| "edof n cs (meformula.MMatchP I mr mrs L buf nts aux) =
     (case those (map (emfcols n) L) of None \<Rightarrow> EDFail
      | Some css \<Rightarrow>
        (if length buf = length L \<and> list_all mbuf_t_is_empty buf \<and> aux = [] \<and>
            (\<forall>c \<in> set css. set c \<subseteq> set cs)
         then EDMatchP (length cs) I mr mrs (map (emb_plan cs) css) (map2 (edof n) css L)
                (map (\<lambda>_. mbuf_t_empty) L) nts []
         else EDFail))"
| "edof n cs (meformula.MMatchF I mr mrs L buf nts t aux) =
     (case those (map (emfcols n) L) of None \<Rightarrow> EDFail
      | Some css \<Rightarrow>
        (if length buf = length L \<and> list_all mbuf_t_is_empty buf \<and> aux = [] \<and>
            (\<forall>c \<in> set css. set c \<subseteq> set cs)
         then EDMatchF (length cs) I mr mrs (map (emb_plan cs) css) (map2 (edof n) css L)
                (map (\<lambda>_. mbuf_t_empty) L) nts t []
         else EDFail))"
  by pat_completeness (simp_all only: prod.inject meformula.inject meformula.distinct simp_thms)

termination edof
  by (relation "measure (\<lambda>(n, cs, \<phi>). size \<phi>)")
    (auto simp: termination_simp dest!: set_zip_rightD)

lemma edof_dof: "Rep_edformula (edof n cs e) = dof n cs (Rep_meformula e)"
proof (induct n cs e rule: edof.induct)
  case (12 n cs args \<phi> \<psi> buf aux)
  show ?case
    by (simp only: edof.simps dof.simps Rep_meformula.simps Let_def
        12(1)[OF refl refl] 12(2)[OF refl refl refl] if_distrib[of Rep_edformula]
        option.case_distrib[of Rep_edformula] Rep_edformula.simps prod.case mbuf_t_empty.rep_eq)
next
  case (13 n cs args \<phi> \<psi> buf nts t aux)
  show ?case
    by (simp only: edof.simps dof.simps Rep_meformula.simps Let_def
        13(1)[OF refl refl] 13(2)[OF refl refl refl] if_distrib[of Rep_edformula]
        option.case_distrib[of Rep_edformula] Rep_edformula.simps map_prod_simp mbuf_t_empty.rep_eq)
next
  case (6 n cs \<phi> \<psi> buf)
  then show ?case by (cases buf) (simp add: mbuf_t_empty.rep_eq mbuf_t_is_empty.rep_eq)
next
  case (7 n cs A \<phi> pos B \<psi> buf)
  then show ?case by (cases buf) (simp add: Let_def mbuf_t_empty.rep_eq mbuf_t_is_empty.rep_eq)
next
  case (19 n cs A \<alpha> buf1 args \<phi> \<psi> buf2 nts aux)
  have e: "(mbuf_t_is_empty (fst buf1) \<and> mbuf_t_is_empty (snd buf1) \<and>
      mbuf_t_is_empty (fst buf2) \<and> mbuf_t_is_empty (snd buf2) \<and> mbuf_t_is_empty nts) =
    (map_prod Rep_mbuf_t Rep_mbuf_t buf1 = ([], []) \<and> map_prod Rep_mbuf_t Rep_mbuf_t buf2 = ([], []) \<and>
      Rep_mbuf_t nts = [])"
    by (cases buf1; cases buf2) (simp add: mbuf_t_is_empty.rep_eq)
  show ?case
    unfolding edof.simps dof.simps Rep_meformula.simps Let_def e if_distrib[of Rep_edformula]
  proof (rule if_cong[OF refl], goal_cases)
    case 1
    show ?case
      by (simp only: Rep_edformula.simps map_prod_simp mbuf_t_empty.rep_eq
          19(1-3)[OF refl refl 1[folded e]])
  qed (simp only: Rep_edformula.simps)
qed (simp_all add: Let_def zip_map2 o_def mbuf_t_empty.rep_eq mbuf_t_append.rep_eq
      mbuf_t_is_empty.rep_eq list_all_iff emfcols_mfcols
      split: list.splits option.splits prod.splits cong: map_cong)

lemma dof_code[code]: "dof n cs (Rep_meformula e) = Rep_edformula (edof n cs e)"
  by (simp add: edof_dof)

(*<*)
end
(*>*)
