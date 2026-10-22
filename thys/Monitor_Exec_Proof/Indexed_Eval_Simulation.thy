(*<*)
theory Indexed_Eval_Simulation
  imports "Monitor_Exec.Indexed_Eval" Exec_Eval_Simulation Indexed_Windows_Simulation "Monitor_Impl_Proof.Monitor_Instance_Valid"
begin
(*>*)

section \<open>Correctness of indexed evaluation\<close>

subsection \<open>Forgetting the indices\<close>

lemma iset_igands_pos: "iset (igands_pos ps t us) = gands_pos ps (iset t) (map iset us)"
  by (induct ps t us rule: igands_pos.induct) (simp_all add: ijoin_eq)

lemma igmulti_join_eq: "igmulti_join ps ns us = gmulti_join ps ns (map iset us)"
  by (cases us) (simp_all add: igmulti_join_def gmulti_join_def iset_igands_pos take_map drop_map)

lemma lookup_dabs: "Mapping.lookup (dabs db) k = map_option (map iset) (Mapping.lookup db k)"
  by (simp add: dabs_def Mapping.lookup_map_values)

lemma dabs_update[simp]: "dabs (Mapping.update k xs db) = Mapping.update k (map iset xs) (dabs db)"
  by (rule mapping_eqI) (simp add: lookup_dabs Mapping.lookup_update')

lemma dabs_demb[simp]: "dabs (demb db) = db"
  by (rule mapping_eqI) (simp add: lookup_dabs demb_def Mapping.lookup_map_values option.map_comp
      comp_def option.map_ident)

lemma map_zip_inv:
  "length Q = length L \<Longrightarrow> (\<And>q x. (q, x) \<in> set (zip Q L) \<Longrightarrow> g (f q x) = x) \<Longrightarrow>
    map g (map (\<lambda>(q, x). f q x) (zip Q L)) = L"
  by (induct Q L rule: list_induct2) auto

lemma eabs_eemb[simp]: "eabs (eemb ix rq \<phi>) = \<phi>"
proof (induct ix rq \<phi> rule: eemb.induct)
  case (13 ix rq ps ns Ld dbuf)
  have "map eabs (map (\<lambda>(q, \<phi>). eemb ix q \<phi>) (zip (eands_req ps (length Ld)) Ld)) = Ld"
    by (rule map_zip_inv) (auto intro: 13)
  then show ?case by simp
qed (auto simp: comp_def intro!: map_idI)

subsection \<open>Buffers\<close>

lemma mbuf_t_cases_map: "mbuf_t_cases (mbuf_t_map f b) = map_prod (map_option f) (mbuf_t_map f) (mbuf_t_cases b)"
  by transfer (auto split: list.splits)

lemma imebufn_take_ibn:
  "imebufn_take g z buf = (z', buf') \<Longrightarrow> (\<forall>xs z. g xs z = f (map iset xs) z) \<Longrightarrow>
     mebufn_take f z (ibn buf) = (z', ibn buf')"
proof (induction g z buf arbitrary: z' buf' rule: imebufn_take.induct)
  case (1 g z buf)
  have e: "ibn buf = [] \<longleftrightarrow> buf = []" "(\<exists>x \<in> set (ibn buf). mbuf_t_is_empty x) \<longleftrightarrow> (\<exists>x \<in> set buf. mbuf_t_is_empty x)"
    by (auto simp: ibn_def)
  have ne: "\<And>x. \<not> mbuf_t_is_empty x \<Longrightarrow> fst (mbuf_t_cases x) \<noteq> None"
    by transfer (auto split: list.splits)
  show ?case
  proof (cases "buf = [] \<or> (\<exists>x \<in> set buf. mbuf_t_is_empty x)")
    case True
    then show ?thesis using 1(2) e
      by (subst mebufn_take.simps) (simp add: imebufn_take.simps[of g z buf] del: mebufn_take.simps)
  next
    case False
    have h: "map (the \<circ> fst \<circ> mbuf_t_cases) (ibn buf) = map iset (map (the \<circ> fst \<circ> mbuf_t_cases) buf)"
      unfolding ibn_def map_map
    proof (rule map_cong[OF refl])
      fix x
      assume "x \<in> set buf"
      then have "fst (mbuf_t_cases x) \<noteq> None" using False ne by blast
      then show "(the \<circ> fst \<circ> mbuf_t_cases \<circ> mbuf_t_map iset) x = (iset \<circ> (the \<circ> fst \<circ> mbuf_t_cases)) x"
        by (simp add: mbuf_t_cases_map option.map_sel)
    qed
    have t: "map (snd \<circ> mbuf_t_cases) (ibn buf) = ibn (map (snd \<circ> mbuf_t_cases) buf)"
      by (auto simp: ibn_def mbuf_t_cases_map split: prod.splits)
    have u: "imebufn_take g (g (map (the \<circ> fst \<circ> mbuf_t_cases) buf) z) (map (snd \<circ> mbuf_t_cases) buf)
        = (z', buf')"
      using 1(2) False by (simp add: imebufn_take.simps[of g z buf])
    have g: "g (map (the \<circ> fst \<circ> mbuf_t_cases) buf) z = f (map iset (map (the \<circ> fst \<circ> mbuf_t_cases) buf)) z"
      using 1(3) by blast
    have IH: "mebufn_take f (f (map iset (map (the \<circ> fst \<circ> mbuf_t_cases) buf)) z)
        (ibn (map (snd \<circ> mbuf_t_cases) buf)) = (z', ibn buf')"
      using 1(1)[OF False u 1(3)] unfolding g .
    have ne2: "\<not> (ibn buf = [] \<or> (\<exists>x \<in> set (ibn buf). mbuf_t_is_empty x))"
      using False e by blast
    show ?thesis
      by (subst mebufn_take.simps) (simp only: if_not_P[OF ne2] h t IH)
  qed
qed

lemma ibn_add: "ibn (List.map2 (@@) dbuf xss) = mebufn_add (map (map iset) xss) (ibn dbuf)"
  unfolding ibn_def mebufn_add.simps
  by (induct dbuf xss rule: list_induct2') simp_all

lemma mebuf2_take_ib2:
  "mebuf2_take g b = (zs, b') \<Longrightarrow> (\<forall>x y. iset (g x y) = f (iset x) (iset y)) \<Longrightarrow>
   mebuf2_take f (ib2 b) = (map iset zs, ib2 b')"
proof (induction g b arbitrary: zs b' rule: mebuf2_take.induct)
  case (1 g xs ys)
  show ?case
  proof (cases "mbuf_t_cases xs")
    case (Pair xo xs')
    show ?thesis
    proof (cases xo)
      case None
      then show ?thesis using 1(2) Pair by (auto simp: ib2_def mbuf_t_cases_map)
    next
      case (Some x)
      show ?thesis
      proof (cases "mbuf_t_cases ys")
        case (Pair yo ys')
        then show ?thesis
          using 1 \<open>mbuf_t_cases xs = (xo, xs')\<close> Some
          by (cases yo) (auto simp: ib2_def mbuf_t_cases_map split: prod.splits)
      qed
    qed
  qed
qed

subsection \<open>Evaluator\<close>

text \<open>Evaluation over indexed tables computes what @{const eeval} computes once the indices are
  forgotten.\<close>

lemma map_eeval_eabs:
  assumes "\<And>x xs \<phi>'. x \<in> set Ld \<Longrightarrow> ieval [] j ts db x = (xs, \<phi>') \<Longrightarrow>
    eeval j ts (dabs db) (eabs x) = (map iset xs, eabs \<phi>')"
  shows "map (\<lambda>x. eeval j ts (dabs db) (eabs x)) Ld = map (\<lambda>x. map_prod (map iset) eabs (ieval [] j ts db x)) Ld"
proof (rule map_cong[OF refl])
  fix x
  assume x: "x \<in> set Ld"
  obtain xs \<phi>' where "ieval [] j ts db x = (xs, \<phi>')"
    by (cases "ieval [] j ts db x")
  then show "eeval j ts (dabs db) (eabs x) = map_prod (map iset) eabs (ieval [] j ts db x)"
    using assms[OF x] by simp
qed

lemma map_eeval_eabs_zip:
  assumes "length Q = length Ld"
    and "\<And>q x xs \<phi>'. (q, x) \<in> set (zip Q Ld) \<Longrightarrow> ieval q j ts db x = (xs, \<phi>') \<Longrightarrow>
    eeval j ts (dabs db) (eabs x) = (map iset xs, eabs \<phi>')"
  shows "map (\<lambda>x. eeval j ts (dabs db) (eabs x)) Ld =
    map (\<lambda>(q, x). map_prod (map iset) eabs (ieval q j ts db x)) (zip Q Ld)"
proof -
  have L: "Ld = map snd (zip Q Ld)" using assms(1) by simp
  have "map (\<lambda>x. eeval j ts (dabs db) (eabs x)) Ld =
      map (\<lambda>(q, x). eeval j ts (dabs db) (eabs x)) (zip Q Ld)"
    by (subst (1) L) (simp add: case_prod_beta)
  also have "\<dots> = map (\<lambda>(q, x). map_prod (map iset) eabs (ieval q j ts db x)) (zip Q Ld)"
  proof (rule map_cong[OF refl])
    fix e
    assume e: "e \<in> set (zip Q Ld)"
    obtain q x where qx: "e = (q, x)" by (cases e)
    obtain xs \<phi>' where "ieval q j ts db x = (xs, \<phi>')" by (cases "ieval q j ts db x")
    then show "(\<lambda>(q, x). eeval j ts (dabs db) (eabs x)) e = (\<lambda>(q, x). map_prod (map iset) eabs (ieval q j ts db x)) e"
      using assms(2)[of q x] e qx by simp
  qed
  finally show ?thesis .
qed

lemma ieval_fallback: "map_prod (map itab) (eemb IxNone []) E = (xs, \<phi>') \<Longrightarrow> E = (map iset xs, eabs \<phi>')"
  by (cases E) (auto simp: comp_def)

theorem ieval_eeval:
  "ieval rq j ts db \<phi> = (xs, \<phi>') \<Longrightarrow> eeval j ts (dabs db) (eabs \<phi>) = (map iset xs, eabs \<phi>')"
proof (induction rq j ts db \<phi> arbitrary: xs \<phi>' rule: ieval.induct)
  case (9 rq j ts db \<phi> \<psi> buf)
  obtain xs1 \<phi>1 where 1: "ieval [] j ts db \<phi> = (xs1, \<phi>1)" by fastforce
  obtain ys1 \<psi>1 where 2: "ieval [] j ts db \<psi> = (ys1, \<psi>1)" by fastforce
  obtain zs buf' where 3: "mebuf2_take iunion (mebuf2_add xs1 ys1 buf) = (zs, buf')"
    by (cases "mebuf2_take iunion (mebuf2_add xs1 ys1 buf)") auto
  have t: "mebuf2_take (\<union>) (ib2 (mebuf2_add xs1 ys1 buf)) = (map iset zs, ib2 buf')"
    by (rule mebuf2_take_ib2[OF 3]) simp
  show ?case
    using 9(3) 9(1)[OF 1] 9(2)[OF refl 1[symmetric] 2] t by (auto simp: 1 2 3)
next
  case (10 rq j ts db pl \<phi> pos \<psi> buf)
  obtain xs1 \<phi>1 where 1: "ieval (jreq_l pl pos) j ts db \<phi> = (xs1, \<phi>1)" by fastforce
  obtain ys1 \<psi>1 where 2: "ieval (jreq_r pl pos) j ts db \<psi> = (ys1, \<psi>1)" by fastforce
  obtain zs buf' where 3: "mebuf2_take (\<lambda>r1 r2. itab (ijoin pl r1 pos r2)) (mebuf2_add xs1 ys1 buf) = (zs, buf')"
    by (cases "mebuf2_take (\<lambda>r1 r2. itab (ijoin pl r1 pos r2)) (mebuf2_add xs1 ys1 buf)") auto
  have t: "mebuf2_take (\<lambda>r1 r2. gbin_join pl r1 pos r2) (ib2 (mebuf2_add xs1 ys1 buf)) = (map iset zs, ib2 buf')"
    by (rule mebuf2_take_ib2[OF 3]) (simp add: ijoin_eq)
  show ?case
    using 10(3) 10(1)[OF 1] 10(2)[OF refl 1[symmetric] 2] t by (auto simp: 1 2 3)
next
  case (14 rq j ts db dags \<phi> \<psi> buf aux)
  obtain xs1 \<phi>1 where 1: "ieval [] j ts db \<phi> = (xs1, \<phi>1)" by fastforce
  obtain ys1 \<psi>1 where 2: "ieval [] j ts db \<psi> = (ys1, \<psi>1)" by fastforce
  obtain zs buf' aux' where 3: "iuedsx_eval_since dags [] (mebuf2S_add (map iset xs1) (map iset ys1) ts buf)
      (iudsx_ensure rq aux) = (zs, buf', aux')"
    by (metis prod_cases3)
  have t: "uedsx_eval_since dags [] (mebuf2S_add (map iset xs1) (map iset ys1) ts buf) (riu aux)
      = (map iset zs, buf', riu aux')"
    using iuedsx_eval_since_abs[of dags "[]" "mebuf2S_add (map iset xs1) (map iset ys1) ts buf"
      "iudsx_ensure rq aux"] 3 by simp
  show ?case
    using 14(3) 14(1)[OF 1] 14(2)[OF refl 1[symmetric] 2] t by (auto simp: 1 2 3)
next
  case (15 rq j ts db dags msk \<phi> \<psi> buf nts t aux)
  obtain xs1 \<phi>1 where 1: "ieval [] j ts db \<phi> = (xs1, \<phi>1)" by fastforce
  obtain ys1 \<psi>1 where 2: "ieval [] j ts db \<psi> = (ys1, \<psi>1)" by fastforce
  let ?B = "mebuf2_add (map iset xs1) (map iset ys1) buf"
  obtain ua ub nt un where 3: "mebuf2t_take (iudux_add_new dags msk) (iudux_ensure rq aux) ?B t (nts @@ ts)
      = (ua, ub, nt, un)"
    by (cases "mebuf2t_take (iudux_add_new dags msk) (iudux_ensure rq aux) ?B t (nts @@ ts)") auto
  obtain zs ua2 where 4: "iudux_eval dags nt ua = (zs, ua2)" by fastforce
  have t: "mebuf2t_take (udux_add_new dags msk) (riud aux) ?B t (nts @@ ts) = (riud ua, ub, nt, un)"
    using mebuf2t_take_nat[of "udux_add_new dags msk" riud "iudux_add_new dags msk" "iudux_ensure rq aux"
        ?B t "nts @@ ts", OF riud_add_new] 3 by simp
  have u: "udux_eval dags nt (riud ua) = (map iset zs, riud ua2)"
    using riud_eval[of dags nt ua] 4 by simp
  show ?case
    using 15(3) 15(1)[OF 1] 15(2)[OF refl 1[symmetric] 2] t u by (auto simp: 1 2 3 4)
next
  case (13 rq j ts db ps ns Ld dbuf)
  let ?Q = "eands_req ps (length Ld)"
  let ?R = "map (\<lambda>(q, \<phi>). ieval q j ts db \<phi>) (zip ?Q Ld)"
  let ?F = "\<lambda>as zs. zs @@ [gmulti_join ps ns as]"
  let ?G = "\<lambda>as zs. zs @@ [igmulti_join ps ns as]"
  have R: "map (\<lambda>x. eeval j ts (dabs db) (eabs x)) Ld =
      map (\<lambda>(q, x). map_prod (map iset) eabs (ieval q j ts db x)) (zip ?Q Ld)"
    by (rule map_eeval_eabs_zip) (auto intro: 13(1))
  obtain zs dbuf' where 3: "imebufn_take ?G mbuf_t_empty (List.map2 (@@) dbuf (map fst ?R)) = (zs, dbuf')"
    by fastforce
  have t: "mebufn_take ?F mbuf_t_empty (mebufn_add (map (map iset \<circ> fst) ?R) (ibn dbuf)) = (zs, ibn dbuf')"
    using imebufn_take_ibn[OF 3, of ?F] by (simp add: igmulti_join_eq ibn_add comp_def)
  have i: "ieval rq j ts db (EAnds ps ns Ld dbuf) = (map itab (Rep_mbuf_t zs), EAnds ps ns (map snd ?R) dbuf')"
    using 3 by (simp add: Let_def)
  have e: "eeval j ts (dabs db) (eabs (EAnds ps ns Ld dbuf)) =
      (Rep_mbuf_t zs, EAnds ps ns (map (eabs \<circ> snd) ?R) (ibn dbuf'))"
    using t by (simp add: Let_def R comp_def case_prod_beta del: mebufn_take.simps mebufn_add.simps)
  from 13(2) i have xs: "xs = map itab (Rep_mbuf_t zs)" and \<phi>': "\<phi>' = EAnds ps ns (map snd ?R) dbuf'"
    by simp_all
  show ?case
    unfolding e xs \<phi>' by (simp add: comp_def)
next
  case (27 rq j ts db x)
  then show ?case by (cases "eeval j ts (dabs db) x") (auto simp: comp_def)
next
  case 20
  then show ?case by (intro ieval_fallback) (simp only: ieval.simps)
next
  case 21
  then show ?case by (intro ieval_fallback) (simp only: ieval.simps)
next
  case (24 rq j ts db m I mr mrs pls Ld dbuf nts daux)
  have R: "map (\<lambda>x. eeval j ts (dabs db) (eabs x)) Ld = map (\<lambda>x. map_prod (map iset) eabs (ieval [] j ts db x)) Ld"
    by (rule map_eeval_eabs) (rule 24(1))
  show ?case
    using 24(2) by (auto simp add: Let_def comp_def R case_prod_beta simp del: mebufnt_take.simps)
next
  case (25 rq j ts db m I mr mrs pls Ld dbuf nts t daux)
  have R: "map (\<lambda>x. eeval j ts (dabs db) (eabs x)) Ld = map (\<lambda>x. map_prod (map iset) eabs (ieval [] j ts db x)) Ld"
    by (rule map_eeval_eabs) (rule 25(1))
  show ?case
    using 25(2) by (auto simp add: Let_def comp_def R case_prod_beta simp del: mebufnt_take.simps)
qed (auto simp: Let_def lookup_dabs split: prod.splits option.splits
  simp del: mebuf2_take.simps mebuf2t_take.simps mebuf2T_take.simps mebufn_take.simps
    mebufnt_take.simps meprev_next.simps mebuf2S_add.simps)
end
