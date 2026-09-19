(*<*)
theory Dense_Descend_Code
  imports Dense_Descend
begin
(*>*)

section \<open>The descending compiler, executable\<close>

text \<open>
  @{const dof} descends the kernel's @{typ "(mmasaux, muaux_dq, event_data mmtaux) mformula"},
  which is the specification type: its code representation is @{const Rep_meformula} of an
  @{typ "(mmasaux, muaux_dq, event_data mmtaux) meformula"}, so the code generator cannot match
  on its constructors and @{const dof} is not executable as it stands.

  The transcription below descends the implementation type instead.  It is @{const dof} clause
  for clause, with the buffers read through @{const Rep_mbuf_t} where @{const dof} reads them
  directly, and the lemma after it says the two agree -- which is the code equation the generator
  needs.  Nothing new is decided here; every guard and every node is the one above.
\<close>

fun edof :: "nat \<Rightarrow> cols \<Rightarrow> (mmasaux, muaux_dq, event_data mmtaux) meformula \<Rightarrow>
    dformula" where
  "edof n cs (meformula.MRel rel) = DRel (dtabc n cs rel)"
| "edof n cs (meformula.MPred e tms mode) =
     (if mode = Match then DPredM e (length tms) tms cs
      else if (mode = Copy \<and> tms = map Formula.Var [0..<n] \<and> cs = [0..<n])
           \<or> (mode = Simple \<and> is_simple_pattern tms 0 \<and> cs = smp_cols tms)
      then DPredS e (length tms)
      else DFail)"
| "edof n cs (meformula.MAndRel \<phi> conf) =
     (if Formula.fv_trm (fst conf) \<subseteq> set cs \<and> Formula.fv_trm (snd (snd (snd conf))) \<subseteq> set cs
      then DAndRel (edof n cs \<phi>) (reindex_constraint cs conf)
      else DFail)"
| "edof n cs (meformula.MNeg \<phi>) =
     (if cs = [] then DNeg (edof n [] \<phi>)
      else DFail)"
| "edof n cs (meformula.MExists \<phi>) = DExists (edof (Suc n) (0 # map Suc cs) \<phi>) True"
| "edof n cs (meformula.MOr \<phi> \<psi> buf) =
     DOr (edof n cs \<phi>) (edof n cs \<psi>)
       (map (dtabc n cs) (Rep_mbuf_t (fst buf)), map (dtabc n cs) (Rep_mbuf_t (snd buf)))"
| "edof n cs (meformula.MAnd A \<phi> pos B \<psi> buf) =
     (let cs1 = set_cols A; cs2 = set_cols B in
      if cs = merge_cols cs1 cs2 \<and> (pos \<or> B \<subseteq> A)
      then DAnd (mk_djoin cs1 cs2) (edof n cs1 \<phi>) pos (edof n cs2 \<psi>)
             (map (dtabc n cs1) (Rep_mbuf_t (fst buf)),
              map (dtabc n cs2) (Rep_mbuf_t (snd buf)))
      else DFail)"
| "edof n cs (meformula.MPrev I \<phi> first buf nts) =
     DPrev I (edof n cs \<phi>) first (map (dtabc n cs) (Rep_mbuf_t buf)) (Rep_mbuf_t nts)"
| "edof n cs (meformula.MNext I \<phi> first nts) =
     DNext I (edof n cs \<phi>) first (Rep_mbuf_t nts)"
| "edof n cs (meformula.MAnds A_pos A_neg L buf) =
     (case A_pos of [] \<Rightarrow> DFail
      | A # As \<Rightarrow>
        (let c0 = set_cols A; css = map set_cols As; nss = map set_cols A_neg in
         if cs = dands_cols c0 css \<and> length L = length A_pos + length A_neg
         then DAnds (dands_plans c0 css) (dands_plans (dands_cols c0 css) nss)
                (map2 (edof n) (c0 # css @ nss) L)
                (map2 map (map (dtabc n) (c0 # css @ nss)) (map Rep_mbuf_t buf))
         else DFail))"
| "edof n cs (meformula.MAgg args \<phi>) =
     (let m = length (aggargs_tys args); g = dagg_gcols args; y = aggargs_y args in
      if cs = merge_cols g [y] \<and> set_cols (aggargs_cols args) = agg_cols m g
      then DAgg (aggargs_g0 args) (aggargs_\<omega> args)
             (reindex_trm (agg_cols m g) (aggargs_f args)) m (ins_pos g y)
             (edof (m + n) (agg_cols m g) \<phi>)
      else DFail)"
| "edof n cs (meformula.MSince args \<phi> \<psi> buf aux) =
     (let cs_L = set_cols (args_L args) in
      if args_agg args = None \<and> args_n args = n \<and> args_R args = set cs \<and>
         set cs_L \<subseteq> set cs \<and>
         (case buf of (a, b, c, d) \<Rightarrow> (Rep_mbuf_t a, Rep_mbuf_t b, Rep_mbuf_t c, d)) = init_mbuf2S
      then DSince (dargs cs cs_L args)
             (edof n cs_L \<phi>) (edof n cs \<psi>) init_mbuf2S
             (dinit_msaux (dargs cs cs_L args) (dmsk cs cs_L))
      else DFail)"
| "edof n cs (meformula.MUntil args \<phi> \<psi> buf nts t aux) =
     (let cs_L = set_cols (args_L args) in
      if args_agg args = None \<and> args_n args = n \<and> args_R args = set cs \<and>
         set cs_L \<subseteq> set cs \<and> map_prod Rep_mbuf_t Rep_mbuf_t buf = ([], []) \<and>
         Rep_mbuf_t nts = [] \<and> t = 0
      then DUntil (dargs cs cs_L args) (dmsk cs cs_L)
             (edof n cs_L \<phi>) (edof n cs \<psi>) ([], []) [] 0
             (init_dq (dargs cs cs_L args))
      else DFail)"
| "edof n cs (meformula.MAndAssign \<phi> conf) =
     (let y = fst conf; t = snd conf; cs0 = rem_col cs y in
      if y \<in> set cs \<and> Formula.fv_trm t \<subseteq> set cs0
      then DAndAssign (ins_pos cs0 y) (reindex_trm cs0 t) (edof n cs0 \<phi>)
      else DFail)"
| "edof n cs (meformula.MLet p m \<phi> \<psi>) = DLet p m (edof m [0..<m] \<phi>) (edof n cs \<psi>)"
| "edof n cs (meformula.MFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s) =
     DFrz p m (edof m [0..<m] \<phi>) (edof n cs \<psi>) jfrz jpsi0 jphi \<alpha>s"
| "edof n cs (meformula.MLetPast p m \<phi> \<psi> i buf) =
     DLetPast p m (edof m [0..<m] \<phi>) (edof n cs \<psi>) i buf"
| "edof n cs (meformula.MTrigger args \<phi> \<psi> buf nts aux) =
     (let cs_L = set_cols (args_L args) in
      if args_n args = n \<and> args_R args = set cs \<and> set cs_L \<subseteq> set cs \<and>
         mem (args_ivl args) 0 \<and> map_prod Rep_mbuf_t Rep_mbuf_t buf = ([], []) \<and>
         Rep_mbuf_t nts = []
      then DTrigger (dargs cs cs_L args) (emb_plan cs cs_L)
             (edof n cs_L \<phi>) (edof n cs \<psi>) ([], []) [] (init_mmtaux (dargs cs cs_L args))
      else DFail)"
| "edof n cs (meformula.MTP mt i) =
     (if cs = mtrm_dcols mt then DTP mt i
      else DFail)"
| "edof n cs (meformula.MTS mt) =
     (if cs = mtrm_dcols mt then DTS mt
      else DFail)"
| "edof n cs \<phi> = DFail"

lemma edof_dof: "edof n cs e = dof n cs (Rep_meformula e)"
  by (induct n cs e rule: edof.induct)
    (simp_all add: Let_def split: list.splits prod.splits)

lemma dof_code[code]: "dof n cs (Rep_meformula e) = edof n cs e"
  by (simp add: edof_dof)

(*<*)
end
(*>*)
