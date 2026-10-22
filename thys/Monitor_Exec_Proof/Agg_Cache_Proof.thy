(*<*)
theory Agg_Cache_Proof
  imports "Monitor_Exec.Agg_Cache" Until_Agg_Proof "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



lemma gmr_mkr: "gmr p (\<lambda>x. x) f m = {mkr p g v | g v. map_option f (Mapping.lookup m g) = Some v}"
  unfolding gmr_def mkr_def[symmetric]
proof (intro set_eqI iffI)
  fix x
  assume "x \<in> (\<lambda>g. case Mapping.lookup m g of Some i \<Rightarrow> mkr p g (f i) | None \<Rightarrow> g) ` Mapping.keys m"
  then obtain g i where "Mapping.lookup m g = Some i" "x = mkr p g (f i)"
    by (auto simp: Mapping.keys_dom_lookup)
  then show "x \<in> {mkr p g v |g v. map_option f (Mapping.lookup m g) = Some v}" by auto
next
  fix x
  assume "x \<in> {mkr p g v |g v. map_option f (Mapping.lookup m g) = Some v}"
  then obtain g i where g: "Mapping.lookup m g = Some i" "x = mkr p g (f i)" by auto
  then have "g \<in> Mapping.keys m" by (simp add: Mapping.keys_dom_lookup domI)
  with g show "x \<in> (\<lambda>g. case Mapping.lookup m g of Some i \<Rightarrow> mkr p g (f i) | None \<Rightarrow> g) ` Mapping.keys m"
    by (auto intro!: rev_image_eqI[of g])
qed

lemma gres_gvset: "gres g0 \<omega> p (\<lambda>x. x) a =
    (if g0 \<and> gkeys a = {} then {[eval_agg_op \<omega> {}]} else gvset \<omega> p a)"
  by (cases a) (auto simp: gvset_def gmr_mkr split: Formula.agg_type.splits)

lemma gcache_ugres: "gcache q p a = (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> ugres (uqok q) False \<omega> pos a)"
  by (simp add: gcache_def ugres_def gres_gvset split: prod.splits)

lemma uc_set_gcache: "cachedp (snd (uc_key x)) \<Longrightarrow> uc_ax x = Some a \<Longrightarrow>
    uc_set x = gcache (fst (uc_key x)) (snd (uc_key x)) a"
  by transfer auto

text \<open>The window's two steps on the counts, the aggregate and its result, in one pass each.  A
  structure built for another node (its key differs) is rebuilt instead.\<close>

lemma gempty_gkeys: "gempty a \<longleftrightarrow> gkeys a = {}"
  by (cases a) (simp_all add: Mapping.is_empty_def)

lemma uc_res: "uc_res q p w x = uag_res q p w (uc_cnt x) (uc_ax x)"
  by (auto simp: uc_res_def uag_res_code ugres_def gres_gvset ufilt_def uc_set_gcache gcache_def
      gempty_gkeys split: option.splits prod.splits)

lemma sa_move_rsc: "sa_move args p nt pend win (ucc (uc_cnt x)) (uc_ax x) =
    (case usc_move args p q nt pend win x of (pend', win', x') \<Rightarrow> (pend', win', ucc (uc_cnt x'), uc_ax x'))"
proof (induct args p q nt pend win x rule: usc_move.induct)
  case (1 args p q nt pend win x)
  obtain h pend' where hd: "safe_hd pend = (h, pend')" by (cases "safe_hd pend")
  show ?case
  proof (cases h)
    case None
    then show ?thesis by (subst sa_move.simps, subst usc_move.simps) (simp add: hd)
  next
    case (Some e)
    note IH = 1[OF hd[symmetric] Some]
    show ?thesis
      using IH by (subst sa_move.simps, subst usc_move.simps) (simp add: hd Some)
  qed
qed

lemma sa_expire_rsc: "sa_expire args p nt win (ucc (uc_cnt x)) (uc_ax x) =
    (case usc_expire args p q nt win x of (win', x') \<Rightarrow> (win', ucc (uc_cnt x'), uc_ax x'))"
proof (induct args p q nt win x rule: usc_expire.induct)
  case (1 args p q nt win x)
  obtain h win' where hd: "safe_hd win = (h, win')" by (cases "safe_hd win")
  show ?case
  proof (cases h)
    case None
    then show ?thesis by (subst sa_expire.simps, subst usc_expire.simps) (simp add: hd)
  next
    case (Some e)
    note IH = 1[OF hd[symmetric] Some]
    show ?thesis
      using IH by (subst sa_expire.simps, subst usc_expire.simps) (simp add: hd Some)
  qed
qed

lemma sa_add_new_ts_rsc: "sa_add_new_ts args p nt (rsc aux) = rsc (usc_add_new_ts args p q nt aux)"
proof -
  obtain t pend win x where aux: "aux = ((t, pend, win), x)" by (cases aux) auto
  obtain pend' win' x' where m: "usc_move args p q nt pend win x = (pend', win', x')"
    by (cases "usc_move args p q nt pend win x") auto
  obtain win'' x'' where e: "usc_expire args p q nt win' x' = (win'', x'')"
    by (cases "usc_expire args p q nt win' x'") auto
  show ?thesis
    using sa_move_rsc[of args p nt pend win x q] sa_expire_rsc[of args p nt win' x' q]
    by (simp add: aux m e sa_add_new_ts_def usc_add_new_ts_def)
qed

lemma sa_join_rsc: "sa_join args p X (rsc aux) = rsc (usc_join args p q X aux)"
  by (cases aux) (auto simp: sa_join_def sw_join_def usc_join_def ucc.simps)

lemma sa_add_new_table_rsc: "sa_add_new_table args p X (rsc aux) = rsc (usc_add_new_table args p q X aux)"
  by (cases aux) (auto simp: sa_add_new_table_def usc_add_new_table_def)

lemma sa_result_rsc: "ufilt q (sa_result args p (rsc aux)) = usc_result q args p aux"
  by (cases aux) (auto simp: sa_result_def usc_result_def uc_res ag_res_ucc simp del: ag_res_ucc_None)

(*<*)
end
(*>*)
