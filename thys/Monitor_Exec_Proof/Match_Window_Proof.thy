(*<*)
theory Match_Window_Proof
  imports "Monitor_Exec.Match_Window" Frame_Aux_Proof Until_Gen_Proof "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



lemma gnth_nth[simp]: "i < length xs \<Longrightarrow> gnth xs i = xs ! i"
  by (simp add: gnth_def)

lemma mrg_left_key_map:
  "sorted_wrt (<) cs1 \<Longrightarrow> sorted_wrt (<) cs2 \<Longrightarrow> set cs2 \<subseteq> set cs1 \<Longrightarrow>
     mrg_left_key (mrg_plan cs1 cs2) = map (\<lambda>c. c \<in> set cs2) cs1"
proof (induct cs1 cs2 rule: mrg_plan.induct)
  case (1 ds)
  then show ?case by (simp add: mrg_left_key_MRgt)
next
  case (2 c cs)
  then show ?case by simp
next
  case (3 c cs d ds)
  note cc = mrg_plan_Cons_cases[OF 3(4,5,6)]
  show ?case
  proof (cases "c < d")
    case True
    have "c \<notin> set (d # ds)" using True 3(5) by auto
    moreover have "c \<noteq> d" using True by simp
    ultimately show ?thesis using 3(1)[OF True] 3(4,5) cc(2)[OF True] by simp
  next
    case False
    then have e: "c = d" using cc(1) by simp
    have "map (\<lambda>x. x \<in> set (c # ds)) cs = map (\<lambda>x. x \<in> set ds) cs" using 3(4) by auto
    then show ?thesis using 3(3)[OF False cc(1)] 3(4,5) cc(3)[OF e] False e by simp
  qed
qed

lemma emb_msk_emb_plan:
  assumes s1: "sorted_wrt (<) cs" and s2: "sorted_wrt (<) c" and sub: "set c \<subseteq> set cs"
  shows "emb_msk (emb_plan cs c) = emsk cs c"
  by (simp add: emb_msk_def emb_plan_def emsk_def mrg_left_key_map[OF s1 s2 sub] comp_def)

lemma eproj_dmsk:
  assumes s1: "sorted_wrt (<) cs" and s2: "sorted_wrt (<) ds" and sub: "set ds \<subseteq> set cs"
    and l: "length a = length cs"
  shows "eproj (emsk cs ds) a = restrict ds cs a"
  using emsk_args_dproj[OF emsk_args_dargs[OF s1 s2 sub, of undefined], of a] l
  by (simp add: emsk_def)

text \<open>The window's lookup and tabulation are the kernel's.\<close>

lemma glookup_lookup: "glookup = lookup"
  by (simp add: glookup_def Monitor.lookup_def empty_table_def)

lemma gmrtabulate_mrtabulate: "gmrtabulate xs f = mrtabulate xs f"
  by transfer (simp add: empty_table_def)

lemma mrtabulate_cong:
  assumes "\<And>k. k \<in> set ks \<Longrightarrow> f k = g k"
  shows "mrtabulate ks f = mrtabulate ks g"
proof -
  have "List.map_filter (\<lambda>k. let fk = f k in if fk = empty_table then None else Some (k, fk)) ks
      = List.map_filter (\<lambda>k. let fk = g k in if fk = empty_table then None else Some (k, fk)) ks"
    using assms
  proof (induct ks)
    case (Cons a ks)
    then have "f a = g a" by simp
    with Cons show ?case by (simp add: Let_def)
  qed simp
  then show ?thesis unfolding mrtabulate.abs_eq by simp
qed

subsection \<open>The lax epsilon\<close>

lemma join_same:
  assumes d: "distinct cs" and tA: "table cs A" and tB: "table cs B"
  shows "join cs A True cs B = A \<inter> B"
  using join_sub_eq[OF d d tA tB subset_refl, of True] tA
  by (auto simp: table_def restrict_idle[OF d])

lemma geps_lax_eq:
  assumes s: "sorted_wrt (<) cs" and wf: "wf_atoms cs css css \<phi>s"
  shows "ok (length \<phi>s) mr \<Longrightarrow> table cs guard \<Longrightarrow>
     geps_lax (map (emsk cs) css) guard \<phi>s mr = \<epsilon>_lax cs css guard \<phi>s mr"
proof (induct mr arbitrary: guard)
  case (MSkip m)
  then show ?case by (simp add: empty_table_def)
next
  case (MTestPos i)
  then have i: "i < length \<phi>s" by simp
  have lc: "length css = length \<phi>s" using wf by (simp add: wf_atoms_def)
  have fi: "eframe (css ! i) (css ! i)" and si: "set (css ! i) \<subseteq> set cs"
    and ti: "table (css ! i) (\<phi>s ! i)" using wf_atomsD[OF wf i] by simp_all
  have dc: "distinct cs" using s by (simp add: strict_sorted_iff)
  have p: "\<And>a. a \<in> guard \<Longrightarrow> eproj (emsk cs (css ! i)) a = restrict (css ! i) cs a"
    using MTestPos(2) eproj_dmsk[OF s eframeD(2)[OF fi] si] by (auto simp: table_def wf_tuple_def)
  show ?case using i lc join_sub_eq[OF dc eframeD(1)[OF fi] MTestPos(2) ti si, of True] p
    by (auto simp: esemi_def)
next
  case (MTestNeg i)
  then have i: "i < length \<phi>s" by simp
  have lc: "length css = length \<phi>s" using wf by (simp add: wf_atoms_def)
  have fi: "eframe (css ! i) (css ! i)" and si: "set (css ! i) \<subseteq> set cs"
    and ti: "table (css ! i) (\<phi>s ! i)" using wf_atomsD[OF wf i] by simp_all
  have dc: "distinct cs" using s by (simp add: strict_sorted_iff)
  have p: "\<And>a. a \<in> guard \<Longrightarrow> eproj (emsk cs (css ! i)) a = restrict (css ! i) cs a"
    using MTestNeg(2) eproj_dmsk[OF s eframeD(2)[OF fi] si] by (auto simp: table_def wf_tuple_def)
  show ?case using i lc join_sub_eq[OF dc eframeD(1)[OF fi] MTestNeg(2) ti si, of False] p
    by (auto simp: esemi_def)
next
  case (MPlus r t)
  then show ?case by simp
next
  case (MTimes r t)
  have o1: "ok (length \<phi>s) r" and o2: "ok (length \<phi>s) t" using MTimes(3) by simp_all
  have dc: "distinct cs" using s by (simp add: strict_sorted_iff)
  have t1: "table cs (\<epsilon>_lax cs css guard \<phi>s r)" by (rule table_eps_lax[OF wf o1 MTimes(4)])
  have t2: "table cs (\<epsilon>_lax cs css guard \<phi>s t)" by (rule table_eps_lax[OF wf o2 MTimes(4)])
  show ?case using MTimes(1)[OF o1 MTimes(4)] MTimes(2)[OF o2 MTimes(4)]
    by (simp add: join_same[OF dc t1 t2])
qed simp

lemma grdelta_eq:
  assumes s: "sorted_wrt (<) cs" and wf: "wf_atoms cs css css \<phi>s"
    and X: "\<And>ms. table cs (lookup X ms)"
  shows "ok (length \<phi>s) mr \<Longrightarrow> grdelta (map (emsk cs) css) \<kappa> X \<phi>s mr = r\<delta> cs css \<kappa> X \<phi>s mr"
proof (induct mr arbitrary: \<kappa>)
  case (MSkip m)
  then show ?case by (cases m) (simp_all add: glookup_lookup empty_table_def)
next
  case (MTimes r t)
  have o1: "ok (length \<phi>s) r" and o2: "ok (length \<phi>s) t" using MTimes(3) by simp_all
  have tg: "table cs (r\<delta> cs css \<kappa> X \<phi>s r)" by (rule table_rdelta[OF wf X o1])
  show ?case using MTimes(1)[OF o1] MTimes(2)[OF o2] by (simp add: geps_lax_eq[OF s wf o2 tg])
qed (simp_all add: empty_table_def)

lemma gldelta_eq:
  assumes s: "sorted_wrt (<) cs" and wf: "wf_atoms cs css css \<phi>s"
    and X: "\<And>ms. table cs (lookup X ms)"
  shows "ok (length \<phi>s) mr \<Longrightarrow> gldelta (map (emsk cs) css) \<kappa> X \<phi>s mr = l\<delta> cs css \<kappa> X \<phi>s mr"
proof (induct mr arbitrary: \<kappa>)
  case (MSkip m)
  then show ?case by (cases m) (simp_all add: glookup_lookup empty_table_def)
next
  case (MTimes r t)
  have o1: "ok (length \<phi>s) r" and o2: "ok (length \<phi>s) t" using MTimes(3) by simp_all
  have tg: "table cs (l\<delta> cs css \<kappa> X \<phi>s t)" by (rule table_ldelta[OF wf X o2])
  show ?case using MTimes(1)[OF o1] MTimes(2)[OF o2] by (simp add: geps_lax_eq[OF s wf o1 tg])
qed (simp_all add: empty_table_def)

context eregex_frame
begin

lemma ewf_atoms: "wfrels rels \<Longrightarrow> wf_atoms cs css css (erels rels)"
  using lc fa sub eframeD(3)[OF fK]
  by (auto simp: wf_atoms_def list_all2_conv_all_nth eframe_def table_etabc strict_sorted_iff)

lemma css_eq:
  assumes i: "i < length \<psi>s" and e: "Formula.fv (\<psi>s ! i) = set ks"
  shows "css ! i = cs"
  using eframeD(2,3)[OF fK] eframeD(2,3)[OF fa[OF i]] e by (intro strict_sorted_equal) auto

lemma greps_strict_eq:
  assumes ops: "wfrels rels"
  shows "Regex.safe_regex fv rgx_safe_pred Past Strict (from_mregex mr \<psi>s) \<Longrightarrow>
     ok (length \<psi>s) mr \<Longrightarrow> set ks = fv_regex (from_mregex mr \<psi>s) \<Longrightarrow>
     greps_strict gmsks (erels rels) mr = r\<epsilon>_strict cs css (erels rels) mr"
proof (induct mr)
  case (MSkip m)
  then show ?case by (simp add: unit_table_def empty_table_def)
next
  case (MTestPos i)
  then have i: "i < length \<psi>s" by simp
  have "css ! i = cs" using css_eq[OF i] MTestPos(3) by simp
  then show ?case using i lr[OF ops] by (simp add: reorder_def)
next
  case (MTestNeg i)
  then show ?case using lr[OF ops] by (simp add: unit_table_def empty_table_def)
next
  case (MPlus r t)
  have fvr: "set ks = fv_regex (from_mregex r \<psi>s)"
    and fvt: "set ks = fv_regex (from_mregex t \<psi>s)" using MPlus(3,5) by auto
  show ?case using MPlus(1)[OF _ _ fvr] MPlus(2)[OF _ _ fvt] MPlus(3,4) by simp
next
  case (MTimes r t)
  have o1: "ok (length \<psi>s) r" and o2: "ok (length \<psi>s) t" using MTimes(4) by simp_all
  have sr1: "Regex.safe_regex fv rgx_safe_pred Past Strict (from_mregex r \<psi>s)"
    using MTimes(3) by simp
  have fvr: "set ks = fv_regex (from_mregex r \<psi>s)" using MTimes(3,5) by auto
  have tg: "table cs (r\<epsilon>_strict cs css (erels rels) r)"
    using table_etabc etabc_reps_strict[OF ops sr1 o1 fvr] by metis
  show ?case using MTimes(1)[OF sr1 o1 fvr] o2 lr[OF ops]
    by (simp add: geps_lax_eq[OF eframeD(2)[OF fK] ewf_atoms[OF ops] _ tg])
next
  case (MStar r)
  then show ?case by (simp add: unit_table_def)
qed

lemma gleps_strict_eq:
  assumes ops: "wfrels rels"
  shows "Regex.safe_regex fv rgx_safe_pred Futu Strict (from_mregex mr \<psi>s) \<Longrightarrow>
     ok (length \<psi>s) mr \<Longrightarrow> set ks = fv_regex (from_mregex mr \<psi>s) \<Longrightarrow>
     gleps_strict gmsks (erels rels) mr = l\<epsilon>_strict cs css (erels rels) mr"
proof (induct mr)
  case (MSkip m)
  then show ?case by (simp add: unit_table_def empty_table_def)
next
  case (MTestPos i)
  then have i: "i < length \<psi>s" by simp
  have "css ! i = cs" using css_eq[OF i] MTestPos(3) by simp
  then show ?case using i lr[OF ops] by (simp add: reorder_def)
next
  case (MTestNeg i)
  then show ?case using lr[OF ops] by (simp add: unit_table_def empty_table_def)
next
  case (MPlus r t)
  have fvr: "set ks = fv_regex (from_mregex r \<psi>s)"
    and fvt: "set ks = fv_regex (from_mregex t \<psi>s)" using MPlus(3,5) by auto
  show ?case using MPlus(1)[OF _ _ fvr] MPlus(2)[OF _ _ fvt] MPlus(3,4) by simp
next
  case (MTimes r t)
  have o1: "ok (length \<psi>s) r" and o2: "ok (length \<psi>s) t" using MTimes(4) by simp_all
  have sr2: "Regex.safe_regex fv rgx_safe_pred Futu Strict (from_mregex t \<psi>s)"
    using MTimes(3) by simp
  have fvt: "set ks = fv_regex (from_mregex t \<psi>s)" using MTimes(3,5) by auto
  have tg: "table cs (l\<epsilon>_strict cs css (erels rels) t)"
    using table_etabc etabc_leps_strict[OF ops sr2 o2 fvt] by metis
  show ?case using MTimes(2)[OF sr2 o2 fvt] o1 lr[OF ops]
    by (simp add: geps_lax_eq[OF eframeD(2)[OF fK] ewf_atoms[OF ops] _ tg])
next
  case (MStar r)
  then show ?case by (simp add: unit_table_def)
qed

end

subsection \<open>The past-match window\<close>

lemma emrd_rel_table:
  "emrd_rel ks cs aux daux \<Longrightarrow> (t, X) \<in> set daux \<Longrightarrow> table cs (lookup X ms)"
  by (induct rule: emrd_rel_induct) (auto simp: table_etabc)

context ematchP_frame
begin

lemma ldrels: "length (erels rels) = length \<psi>s"
  using lr[OF ops] by simp

lemma gtab_head:
  "mrtabulate mrs (greps_strict gmsks (erels rels)) = mrtabulate mrs (r\<epsilon>_strict cs css (erels rels))"
  using mrsok by (intro mrtabulate_cong greps_strict_eq[OF ops]) auto

lemma gtab_step:
  assumes X: "\<And>ms. table cs (lookup X ms)"
  shows "mrtabulate mrs (\<lambda>ms. grdelta gmsks id X (erels rels) ms
       \<union> (if t = nt then greps_strict gmsks (erels rels) ms else {}))
     = mrtabulate mrs (\<lambda>ms. r\<delta> cs css id X (erels rels) ms
       \<union> (if t = nt then r\<epsilon>_strict cs css (erels rels) ms else {}))"
proof (rule mrtabulate_cong)
  fix ms
  assume ms: "ms \<in> set mrs"
  have o: "ok (length (erels rels)) ms" using mrsok[OF ms] ldrels by simp
  show "grdelta gmsks id X (erels rels) ms \<union> (if t = nt then greps_strict gmsks (erels rels) ms else {})
      = r\<delta> cs css id X (erels rels) ms \<union> (if t = nt then r\<epsilon>_strict cs css (erels rels) ms else {})"
    using mrsok[OF ms]
    by (simp add: grdelta_eq[OF eframeD(2)[OF fK] ewf_atoms[OF ops] X o] greps_strict_eq[OF ops])
qed

lemma gtab_window:
  "(\<And>t X ms. (t, X) \<in> set D \<Longrightarrow> table cs (lookup X ms)) \<Longrightarrow>
   [(t, mrtabulate mrs (\<lambda>ms. grdelta gmsks id X (erels rels) ms
       \<union> (if t = nt then greps_strict gmsks (erels rels) ms else {}))). (t, X) \<leftarrow> D, memR I (nt - t)]
   = [(t, mrtabulate mrs (\<lambda>ms. r\<delta> cs css id X (erels rels) ms
       \<union> (if t = nt then r\<epsilon>_strict cs css (erels rels) ms else {}))). (t, X) \<leftarrow> D, memR I (nt - t)]"
proof (induct D)
  case (Cons x D)
  obtain t X where x: "x = (t, X)" by (cases x)
  have "\<And>ms. table cs (lookup X ms)" using Cons(2)[of t X] x by simp
  moreover have "\<And>t X ms. (t, X) \<in> set D \<Longrightarrow> table cs (lookup X ms)"
    using Cons(2) by (metis list.set_intros(2))
  ultimately show ?case using Cons(1) x by (simp add: gtab_step)
qed simp

lemma gupdate_matchP_eq:
  assumes rel: "emrd_rel ks cs aux daux"
  shows "gupdate_matchP gmsks I mr mrs (erels rels) nt daux
     = update_matchP cs css I mr mrs (erels rels) nt daux"
proof -
  have w: "[(t, mrtabulate mrs (\<lambda>ms. grdelta gmsks id X (erels rels) ms
       \<union> (if t = nt then greps_strict gmsks (erels rels) ms else {}))). (t, X) \<leftarrow> daux, memR I (nt - t)]
   = [(t, mrtabulate mrs (\<lambda>ms. r\<delta> cs css id X (erels rels) ms
       \<union> (if t = nt then r\<epsilon>_strict cs css (erels rels) ms else {}))). (t, X) \<leftarrow> daux, memR I (nt - t)]"
    by (rule gtab_window[OF emrd_rel_table[OF rel]])
  show ?thesis
    unfolding gupdate_matchP_def update_matchP_def glookup_lookup gmrtabulate_mrtabulate gtab_head w ..
qed

lemma etabc_gupdate_matchP:
  assumes rel: "emrd_rel ks cs aux daux"
  shows "etabc ks cs (fst (update_matchP ks kss I mr mrs rels nt aux))
       = fst (gupdate_matchP gmsks I mr mrs (erels rels) nt daux) \<and>
     emrd_rel ks cs (snd (update_matchP ks kss I mr mrs rels nt aux))
       (snd (gupdate_matchP gmsks I mr mrs (erels rels) nt daux))"
  unfolding gupdate_matchP_eq[OF rel] by (rule etabc_update_matchP[OF rel])

end

subsection \<open>The future-match window\<close>

lemma geval_matchF_eval_matchF: "geval_matchF I mr nt aux = eval_matchF I mr nt aux"
  by (induct aux rule: eval_matchF.induct) simp_all

context ematchF_frame
begin

lemma table_lookup_dbase:
  assumes rels: "wfrels rels"
  shows "table cs (lookup (mrtabulate mrs (l\<epsilon>_strict cs css (erels rels))) ms)"
  using etabL[OF rels] by (simp add: lookup_tabulate[OF d] table_etabc flip: etabL[OF rels])

lemma gupdate_matchF_base_eq:
  assumes rels: "wfrels rels"
  shows "gupdate_matchF_base gmsks I mr mrs (erels rels) nt
     = update_matchF_base cs css I mr mrs (erels rels) nt"
proof -
  have "mrtabulate mrs (gleps_strict gmsks (erels rels)) = mrtabulate mrs (l\<epsilon>_strict cs css (erels rels))"
    using mrsok by (intro mrtabulate_cong gleps_strict_eq[OF rels]) auto
  then show ?thesis
    by (simp add: gupdate_matchF_base_def update_matchF_base_def glookup_lookup gmrtabulate_mrtabulate
        Let_def empty_table_def)
qed

lemma gupdate_matchF_step_eq:
  assumes rls: "wfrels rls" and X: "\<And>ms. table cs (lookup X ms)"
  shows "gupdate_matchF_step gmsks I mr mrs nt (t, erels rls, drel) (A, X)
       = update_matchF_step cs css I mr mrs nt (t, erels rls, drel) (A, X)"
    and "table cs (lookup (mrtabulate mrs (l\<delta> cs css id X (erels rls))) ms)"
proof -
  have o: "\<And>ms. ms \<in> set mrs \<Longrightarrow> ok (length (erels rls)) ms" using okms[OF _ rls] by simp
  have "mrtabulate mrs (gldelta gmsks id X (erels rls)) = mrtabulate mrs (l\<delta> cs css id X (erels rls))"
    by (intro mrtabulate_cong gldelta_eq[OF eframeD(2)[OF fK] ewf_atoms[OF rls] X o])
  then show "gupdate_matchF_step gmsks I mr mrs nt (t, erels rls, drel) (A, X)
       = update_matchF_step cs css I mr mrs nt (t, erels rls, drel) (A, X)"
    by (simp add: gupdate_matchF_step_def update_matchF_step_def glookup_lookup gmrtabulate_mrtabulate
        Let_def)
  show "table cs (lookup (mrtabulate mrs (l\<delta> cs css id X (erels rls))) ms)"
    using table_ldelta[OF ewf_atoms[OF rls] X o]
    by (simp add: lookup_tabulate[OF d])
qed

lemma gmatchF_foldr_eq:
  assumes rels: "wfrels rels" and rel: "emld_rel ks cs \<psi>s css aux daux"
  shows "foldr (gupdate_matchF_step gmsks I mr mrs nt) daux (gupdate_matchF_base gmsks I mr mrs (erels rels) nt)
       = foldr (update_matchF_step cs css I mr mrs nt) daux (update_matchF_base cs css I mr mrs (erels rels) nt)
     \<and> (\<forall>ms. table cs (lookup (snd (foldr (update_matchF_step cs css I mr mrs nt) daux
          (update_matchF_base cs css I mr mrs (erels rels) nt))) ms))"
  using rel
proof (induct rule: emld_rel_induct)
  case Nil
  show ?case using table_lookup_dbase[OF rels]
    by (simp add: gupdate_matchF_base_eq[OF rels] update_matchF_base_def Let_def)
next
  case (Cons t rls rel aux daux)
  obtain A X where W: "foldr (update_matchF_step cs css I mr mrs nt) daux
      (update_matchF_base cs css I mr mrs (erels rels) nt) = (A, X)"
    by (cases "foldr (update_matchF_step cs css I mr mrs nt) daux
      (update_matchF_base cs css I mr mrs (erels rels) nt)")
  have IH: "foldr (gupdate_matchF_step gmsks I mr mrs nt) daux
      (gupdate_matchF_base gmsks I mr mrs (erels rels) nt) = (A, X)"
    and tX: "\<And>ms. table cs (lookup X ms)" using Cons(3) unfolding W by simp_all
  have E: "foldr (update_matchF_step cs css I mr mrs nt) ((t, erels rls, etabc ks cs rel) # daux)
      (update_matchF_base cs css I mr mrs (erels rels) nt)
      = update_matchF_step cs css I mr mrs nt (t, erels rls, etabc ks cs rel) (A, X)"
    unfolding W[symmetric] by simp
  have GE: "foldr (gupdate_matchF_step gmsks I mr mrs nt) ((t, erels rls, etabc ks cs rel) # daux)
      (gupdate_matchF_base gmsks I mr mrs (erels rels) nt)
      = gupdate_matchF_step gmsks I mr mrs nt (t, erels rls, etabc ks cs rel) (A, X)"
    unfolding IH[symmetric] by simp
  show ?case unfolding E GE gupdate_matchF_step_eq(1)[OF Cons(1) tX]
    using gupdate_matchF_step_eq(2)[OF Cons(1) tX]
    by (simp add: update_matchF_step_def Let_def)
qed

lemma gupdate_matchF_eq:
  assumes rels: "wfrels rels" and rel: "emld_rel ks cs \<psi>s css aux daux"
  shows "gupdate_matchF gmsks I mr mrs (erels rels) nt daux
     = update_matchF cs css I mr mrs (erels rels) nt daux"
  using gmatchF_foldr_eq[OF rels rel] by (simp add: gupdate_matchF_def update_matchF_def)

lemma etabc_gupdate_matchF:
  assumes rels: "wfrels rels" and rel: "emld_rel ks cs \<psi>s css aux daux"
  shows "emld_rel ks cs \<psi>s css (update_matchF ks kss I mr mrs rels nt aux)
     (gupdate_matchF gmsks I mr mrs (erels rels) nt daux)"
  unfolding gupdate_matchF_eq[OF rels rel] by (rule etabc_update_matchF[OF rels rel])

lemma etabc_geval_matchF:
  assumes "emld_rel ks cs \<psi>s css aux daux"
  shows "fst (geval_matchF I mr nt daux) = map (etabc ks cs) (fst (eval_matchF I mr nt aux)) \<and>
     emld_rel ks cs \<psi>s css (snd (eval_matchF I mr nt aux)) (snd (geval_matchF I mr nt daux))"
  unfolding geval_matchF_eval_matchF by (rule etabc_eval_matchF[OF assms])

end

(*<*)
end
(*>*)
