(*<*)
theory IEval_Proof
  imports "Monitor_Exec.IEval" Eval_Proof IWindow_Proof "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



lemma iset_igands_pos: "iset (igands_pos ps t us) = gands_pos ps (iset t) (map iset us)"
  by (induct ps t us rule: igands_pos.induct) (simp_all add: ijoin_eq)

lemma igmulti_join_eq: "igmulti_join ps ns us = gmulti_join ps ns (map iset us)"
  by (cases us) (simp_all add: igmulti_join_def gmulti_join_def iset_igands_pos take_map drop_map)

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

end
